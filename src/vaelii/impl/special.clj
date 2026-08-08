;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.special
  "The special-predicate dispatch table: what each functor the engine interprets
  *means* to the derived state around the store, stated once, with both halves of
  every meaning side by side.

  A special predicate needs behaviour in four places — reflecting a stored sentex
  into the caches, the removal mirror, `recover`'s cache-only replay, and `wff`'s
  per-functor well-formedness check — and the compiler cross-checks none of them, so
  the enumeration lives once here: `entries` maps each functor to its arms,

    :integrate    (fn [kb sentex handle])  reflect a newly stored sentex into the caches
    :disintegrate (fn [kb sentex])         the mirror, reference-counted on (:id sentex)
    :rebuild      (fn [tax sentex])        recover's cache-only replay — no re-check
                                           posting, no migration, no universal lifting,
                                           because the store already holds what those
                                           side effects produced
    :wff          (fn [tax sentence])      structural well-formedness (vaelii.impl.wff
                                           keeps the check fns; the table points at them)
    :derived?     bool                     the :integrate arm also runs on the
                                           derivation path (see `integrate-transitive`)

  and `check-entries` refuses an asymmetric entry **at namespace load**, so an
  add-side arm without its removal and rebuild halves is a build failure rather
  than a cache that drifts on the first retraction or restart.

  Because the arms are where a special predicate's whole behaviour lives, the
  machinery those behaviours need lives here too: the exception re-check queue the
  taxonomy arms post to, the universal-predicate lifting, and the equality
  migration.  Third layer of the engine stack (kb <- checks <- special <-
  integrate <- chain <- settle): everything here reads kb and checks, and the
  store-mutation choke points in `vaelii.impl.integrate` sit directly above."
  (:require [clojure.string :as str]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rewrite :as rewrite]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.wff :as wff]))

;; ## The exception re-check queue
;;
;; Nothing about an `exceptWhen` exception is stored (docs/exceptions.md, "The
;; exception is never stored"), so belief in an excepted conclusion cannot be read
;; back — it has to be *re-evaluated*.  The functions below decide **when**, and
;; they are deliberately coarse: a spurious re-check costs one level-6 query, while a
;; missed one is a conclusion that should have been swept and wasn't.
;;
;; They queue **rule handles**, never justifications.  That is what makes the index
;; affordable: a rule handle is an antecedent of every justification it licenses, so
;; every firing is reachable from the rule through links the TMS already maintains,
;; and the index stays at the scale of the rule index rather than of the fact store.
;;
;; The queue is a **map** `{rule-handle -> triggers}` rather than a set, because rule
;; granularity is right for deciding *whether* to look at a rule and far too coarse
;; for deciding *which of its firings* to re-evaluate.  `triggers` is the set of
;; sentences that arrived or left — what `exception-blocked-set` narrows the rule's
;; firings by before paying for a single level-6 query — or `:all` where no such
;; sentence exists (a taxonomy edge moved, a rule was just indexed) and every firing
;; must be re-checked.

(defn- mark-recheck
  "Queue `rule-handles` for exception re-evaluation at the next `settle`, recording
  `trigger` — the sentence whose arrival or departure could have flipped the exception
  — or `:all` when there is no such sentence and every firing must be re-checked.

  `:all` is absorbing: once a rule is queued unconditionally, adding a narrower
  trigger to it must not narrow it back."
  [kb rule-handles trigger]
  (when (seq rule-handles)
    (swap! (:recheck kb)
           (fn [m]
             (reduce (fn [m rh]
                       (let [cur (get m rh)]
                         (assoc m rh (if (or (= :all cur) (= :all trigger))
                                       :all
                                       (conj (or cur #{}) trigger)))))
                     m rule-handles)))))

(defn- recheck-preserving-along
  "`rel` is the relation of some `(argPreserving P n rel)` declaration and its extent
  just moved — a fact on it arrived or left, or it is `genl` / `genlContext` and an
  edge moved.  Queue every rule whose exception mentions a declaring `P`.

  This is the argument-side twin of the predicate keying below.  An exception on
  `largerThan` is answered by `ArgPreservingProver` walking the *arguments'* reach, so
  `(genl chihuahua dog)` can flip it with neither `chihuahua` nor `dog` appearing
  anywhere near `largerThan` — the genls walk cannot see that, and the firings that
  predate the edge would keep a block the firings after it correctly drop.

  `:all`, never a narrowing trigger: the sentence that moved is on `rel`, and the
  exception is stated over `P`, so it could not narrow the right firings anyway."
  [kb rel]
  (let [idx (:index kb)]
    (doseq [[pred r] (inherit/declared kb)
            :when (= r rel)]
      (mark-recheck kb (p/rules-with-exception-on idx pred) :all))))

(def ^:private declaration-subjects
  "Declaration functors, mapped to the argument positions naming a predicate the
  declaration licenses an inference **about**.

  These sentences move what a level-6 query answers about a predicate without being
  *on* that predicate, and without touching its extent.  `(symmetric sibOf)` makes a
  stored `(sibOf Ann Bob)` answer `(sibOf Bob Ann)`; `(inverse childOf parentOf)`
  makes it answer a goal on the partner predicate; `(asymmetric typL)` is what gives
  the converse the standing to deny a claim, so it decides whether
  `ArgPreservingProver` finds anything against one.  The re-check index is keyed on
  the exception's own predicate and none of these functors is that predicate, so
  without this the firings that predate the declaration keep a conclusion the firings
  after it correctly drop — an order dependence, and the same one
  `recheck-preserving-along` closes on the argument side.

  Which position: the subject is argument 1 throughout, and `inverse` names two
  predicates because either one's goals are answered from the other's facts.
  `functional` is absent because it is read by the definitional checks and answers no
  goal; `arity` and the decontextualization marks likewise.  `argIsa` / `argGenl` are
  absent for the opposite reason — a membership they infer is *stored*, so it arrives
  through the ordinary fact trigger."
  '{transitive           [1]
    symmetric            [1]
    asymmetric           [1]
    reflexive            [1]
    inverse              [1 2]
    argPreserving        [1]
    argPreservingInverse [1]})

(defn- recheck-declaration
  "A declaration licensing an inference about some predicate arrived or left: queue
  every rule whose exception that predicate could newly answer, or newly fail to.

  The fan is `genls(subject)`, the same walk `recheck-on-predicate` does and for the
  same reason — an exception stated at a supertype predicate is satisfied by an answer
  at a subtype, and that generality is the point of stating a taxonomy.  `:all` rather
  than a narrowing trigger: a declaration's arguments are a predicate and a position,
  which agree with an exception conjunct's arguments on nothing.

  `(transitive R)` gets a second posting, because it is two claims at once.  Beside
  `TransitivePredicateProver` reading it, it is the **licence** `inherit/usable-relation?`
  reads at use for every `(argPreserving P n R)` — so withdrawing it withdraws the
  inheritance for a `P` this sentence never names, and `recheck-preserving-along` is
  exactly the walk from a relation to those predicates.

  Gated on some rule carrying an `exceptWhen` at all, so a KB using neither feature
  pays one map lookup on the functor and a set-cardinality read."
  [kb sentence]
  (when-let [poss (get declaration-subjects (nm/functor sentence))]
    (let [idx (:index kb)]
      (when (seq (p/exception-rules idx))
        (doseq [i    poss
                :let [pred (nth sentence i nil)]
                :when (symbol? pred)]
          ;; the global closure on purpose, as everywhere here: an over-selected
          ;; re-check re-evaluates and changes nothing, an under-selected one is a
          ;; wrong belief
          (doseq [p (tax/genls (:taxonomy kb) pred)]
            (mark-recheck kb (p/rules-with-exception-on idx p) :all))
          (when (= 'transitive (nm/functor sentence))
            (recheck-preserving-along kb pred)))))))

(defn- argisa-declared-types
  "The types some `(argIsa pred n T)` declares of `pred`'s argument positions — read off
  the roots rather than through `matches-visible`, and globally rather than per context,
  because a trigger has to be conservative in the direction the answer is and a
  declaration this context cannot see still qualifies a rule in one that can."
  [kb pred]
  (let [idx (:index kb)]
    (when (pos? (p/count-with-functor idx 'argIsa))
      (into #{}
            (comp (keep #(p/get-sentex (:records kb) %))
                  (map :sentence)
                  (filter #(and (= 'argIsa (nm/functor %)) (= 4 (count %))))
                  (map #(nth % 3))
                  (filter symbol?))
            (p/sentexes-with-args idx 'argIsa {1 pred})))))

(defn- recheck-argisa-inferred
  "`argIsa` read as an **inference** rather than as a constraint: a believed `(P … x@n …)`
  beside `(argIsa P n T)` makes `x` a `T`, and every supertype of `T`
  (`provers/inferred-types`, behind `ArgTypeProver`).  So a fact on `P` flips an
  exception stated on `T` with nothing on `T` having been written and no relationship
  between the two predicates for the genls walk below to follow — the same shape of blind
  channel `recheck-preserving-along` closes on the argument side, and blind in the same
  way: without this the firings that predate the fact keep a conclusion the firings after
  it correctly drop, so which you get depends on when the fact arrived.

  Both arrival orders come here, and `sen` says which: a fact on `P`, whose declared
  argument types are read; or the `(argIsa P n T)` declaration itself, which does the
  same to every fact of `P` already stored.

  `:all`, for `recheck-preserving-along`'s reason: what moved is a fact about `P` (or a
  declaration about `P`'s argument positions), and the exception is about `T`, so the
  sentence could not narrow the right firings anyway.

  Free for a KB that declares no `argIsa` — one cardinality read — and free for one that
  declares plenty but states no exception over a declared type, which is the ordinary
  case: the roster probe per supertype answers empty."
  [kb pred sen]
  (let [idx (:index kb)]
    (when-let [ts (seq (if (= 'argIsa pred)
                         (when (= 4 (count sen)) (filter symbol? [(nth sen 3)]))
                         (argisa-declared-types kb pred)))]
      (doseq [t  ts
              t' (tax/genls (:taxonomy kb) t)]
        (mark-recheck kb (p/rules-with-exception-on idx t') :all)))))

(defn- recheck-on-predicate
  "A fact with predicate `pred` arrived or left: queue every rule whose exception
  mentions `pred` **or any supertype of it**.  Both directions matter — an arriving
  fact can make an exception hold, a leaving one can release it.

  The genl fan-out is not over-caution, it is the same fan-out matching does.  An
  exception `(flightless ?b)` is answered by a stored `(penguin Opus)` through the
  spec walk, so the arrival of a `penguin` fact must reach a rule that only ever
  mentions `flightless`.  Keying the trigger on the literal predicate alone would miss
  every exception stated at a more general type than the fact that satisfies it —
  which is most of them, since that generality is the point of stating a taxonomy.

  `trigger` is the sentence this predicate came from; it rides along so the re-check
  can be narrowed to the firings that sentence could actually reach.

  A fact can also move an exception's answer without being on the exception's
  predicate at all, and along two channels the genls walk cannot see: `pred` is the
  relation some `argPreserving` declaration inherits along
  (`recheck-preserving-along`), or `pred` has an `argIsa`-declared argument type, which
  makes the fact evidence of a membership nobody wrote (`recheck-argisa-inferred`)."
  [kb pred trigger]
  (when (symbol? pred)
    ;; No excepted rule anywhere ⇒ nothing to re-check, and walking `genls(pred)` just
    ;; to probe an empty exception set costs an up-closure per assert — quadratic over a
    ;; deep taxonomy load, and dead weight on every plain bulk load.  Guard on the global
    ;; exception-rule set (empty for any KB with no `exceptWhen`), exactly as its edge-side
    ;; twin `recheck-genl-edge` does.
    (let [idx (:index kb)]
      (when (seq (p/exception-rules idx))
        ;; the global closure on purpose: an over-selected re-check re-evaluates and
        ;; changes nothing, an under-selected one is a missed withdrawal
        (doseq [p (tax/genls (:taxonomy kb) pred)]
          (mark-recheck kb (p/rules-with-exception-on idx p) trigger))
        (recheck-preserving-along kb pred)
        (recheck-argisa-inferred kb pred trigger)))))

(defn- recheck-on-qualitative
  "A fact of a registered calculus arrived or left, so the **whole network** moved:
  queue every forward rule joining on any predicate of that calculus.

  Queued as `:all` rather than with the sentence as a narrowing trigger, and that is the
  honest shape — a constraint anywhere can change what is entailed anywhere else, which
  is what path consistency *is*.  Narrowing by the arriving sentence would keep only the
  firings mentioning the very regions it named, and miss exactly the propagation the
  calculus exists for.

  Why any of this is needed: a firing that joined on an entailed relation lists the facts
  behind it as antecedents, so the JTMS withdraws it when one of those goes.  What the
  antecedents cannot express is the network turning *unsatisfiable* — the supporting
  facts are all still believed, and some other fact made the theory impossible.  That is
  decided per firing by `chain/entailment-withdrawn?`, and this is what puts the firing
  in front of it.

  It takes the sentence's **underlying body**, so a believed `(not (ntpp A B))` arrives
  at the calculus its own functor (`not`) names nothing about.  A negative fact is read
  into the network as the complement of the predicate's denotation, so it moves the
  network exactly as a positive one does and can make it impossible outright — and then
  a firing the network licensed has to be put in front of `entailment-withdrawn?` on
  precisely the same trigger.

  Bounded by the rules mentioning the calculus at all, which is zero for every KB that
  registered no prover — `calculus-for` answers nil and this costs one deref."
  [kb body]
  (when-let [calc (qkb/calculus-for kb (nm/functor body))]
    (let [idx (:index kb)]
      (mark-recheck kb
                    (into #{} (mapcat #(p/rules-by-antecedent idx %)) (:predicates calc))
                    :all))))

(defn- recheck-preserving-firings
  "A sentence moved what a preserved predicate licenses: queue every forward rule
  carrying an antecedent on one, so the firings that joined on an **inherited** claim
  are put in front of `chain/inheritance-withdrawn?` at the next settle.

  The argument-side twin of `recheck-on-qualitative`, and needed for the same reason.
  A firing that joined on an inherited claim names the claim, the declaration and the
  reach edges as its antecedents, so the JTMS withdraws it when one of those goes.
  What the antecedents cannot express is a **more specific contrary claim arriving**:
  every one of them is still stored and believed, and some other sentence has undercut
  what they licensed — a general default does not fire for a pair a specific claim
  speaks about (docs/inherit.md), and nothing about that is stored either.

  Queued as `:all` rather than with the sentence as a narrowing trigger, for
  `recheck-preserving-along`'s reason: the sentence that moved is on the relation, or
  on a tuple below the one the firing joined at, so it agrees with the firing's
  literals on nothing a shape comparison could use.

  `inherit/rejoin-rules` is the same read the chainer's own re-join makes, and behind
  the same O(1) gate — a KB that declares no preservation pays two cardinality reads
  per sentence."
  [kb sentence]
  (when-let [rs (inherit/rejoin-rules kb sentence)]
    (mark-recheck kb rs :all)))

(defn recheck-on-sentence
  "The re-check trigger for a whole sentence: its functor, and — for a negation — the
  functor of the positive body underneath, since `(not (penguin X))` is content about
  `penguin` and an exception on `penguin` must see it come and go.

  Both postings carry the **whole sentence** as the trigger, not the predicate they
  were keyed on: what narrows a firing is the arguments as well, and the negation is
  content about the same arguments as its body.

  `underlying-body`, not `positive-body`: a *genuinely negative* sentence is exactly
  the interesting case here.  `(not (penguin X))` arriving is what defeats a believed
  `(penguin X)`, and a re-check condition reading belief — an `unknown`, an aggregate's
  census — moves on the defeat with no fact having been stored or removed.

  The body is read once and serves all four consumers: the predicate-keyed posting
  above, the declaration posting, the qualitative trigger and the preservation trigger
  — each for the same reason, that a calculus, a declaration's subject and a predicate
  are named by what is under the `not`, never by the `not`."
  [kb sentence]
  (let [b (sx/underlying-body sentence)]
    (recheck-on-predicate kb (nm/functor sentence) sentence)
    (when (and b (not= b sentence))
      (recheck-on-predicate kb (nm/functor b) sentence))
    (recheck-declaration kb (or b sentence))
    (recheck-on-qualitative kb (or b sentence))
    (recheck-preserving-firings kb (or b sentence))))

(defn recheck-every-exception
  "Re-check **every** rule carrying an exception — the blanket trigger.  Two channels
  take it: `recover`, where nothing about blocking survives a restart so every exception
  must be re-decided from scratch and there is no edge or fact to narrow by, and
  `recheck-equality-edge` on the sides where its own narrowing is blind — a class
  splitting, and a schematic rewrite arriving.

  (A `genlContext` edge change does not come here: `recheck-genlContext-edge` narrows it
  to the excepted rules whose firings live in the moved visibility cone, the context-keyed
  twin of `recheck-genl-edge`'s predicate keying.)

  There is no triggering *sentence* here — the whole blocking state is being rebuilt —
  so this queues `:all` and every firing of every queued rule is re-evaluated."
  [kb]
  (mark-recheck kb (p/exception-rules (:index kb)) :all))

(def ^:private closure-answered-exception-functors
  "Exception functors a `genl` edge can flip **without** the edge's endpoints
  appearing anywhere near the registered predicate, so the genls-of-the-supertype
  walk in `recheck-genl-edge` cannot see them and they are waved through instead:

    genl      the transitivity prover answers a `(genl x y)` conjunct from the very
              closure the edge just moved
    disjoint  disjointness is closed under genl (both up-closures are walked), so
              any edge can connect a pair a declaration separates
    not       a negated conjunct registers under `not` (its functor).  Today a
              ground negation is answered from stored negative sentexes with no
              genl fan-out, so no edge can flip it — this is defensive, priced at
              one set-read on a rare path, against contravariant negative matching
              ever arriving.

  Everything else the level-6 stack can reach a `genl` edge reaches *through the
  spec closure of the registered predicate* — the fact fan-out, the argIsa type
  inference, a declared-transitive relation's own facts — and those are exactly
  what the genls walk covers.  With one exception, and it is why this set is not the
  whole story: argument-position preservation reads the closure of the **arguments**,
  so `(genl chihuahua dog)` flips an exception on `largerThan` with neither endpoint
  anywhere near it.  Which predicates those are is a property of the KB rather than
  of the code, so they cannot be listed here — `recheck-preserving-along` reads them
  per KB and this set is unioned with what it finds."
  '#{genl disjoint not})

(defn- recheck-genl-edge
  "A `genl` edge under `super` was added or removed: queue the rules whose exception
  the moved closure can actually reach, instead of every excepted rule.

  The edge is `[sub super]`; only `super`'s up-closure matters.  Every reachability
  pair the edge adds or removes runs `x -> … -> sub -> super -> … -> y`, so the spec
  closure `specs(pe)` of an exception predicate `pe` changes **iff `pe` is `super`
  or a supertype of it** — a predicate above `sub` but not above `super` already
  reached everything below `sub`, and one unrelated to both is untouched.  That is
  the same genls walk `recheck-on-predicate` does for an arriving fact, keyed at the
  edge's supertype: the facts at or below `sub` are, from the closure's point of
  view, arriving at (or leaving) every predicate at or above `super` at once.
  `genls(super)` itself is the same before and after the change — an edge that would
  put `sub` above `super` is a cycle, refused by wff on the assert path and dropped
  as a violation on the derivation path — so reading it after the mutation is safe.

  The waved-through functors above cover the provers that read the closure across
  arguments, and `recheck-preserving-along` covers the one set of them the code
  cannot name in advance.  Sound by construction: every channel a genl edge can reach
  a level-6 answer through is either predicate-addressed here or waved through; when
  a future channel is in doubt, the answer is to queue, not to skip — the sin this
  replaces was queueing everything always, not queueing conservatively."
  [kb super]
  (let [tx (:taxonomy kb) idx (:index kb)]
    ;; No excepted rule anywhere ⇒ nothing to re-check, and computing `genls(super)`
    ;; just to iterate an empty rule set would make a deep `genl` load quadratic —
    ;; the up-closure grows with depth and this runs on every edge.  Guard on the
    ;; global exception-rule set, which is empty for a KB (like a bulk taxonomy load)
    ;; that uses no `exceptWhen`.
    (when (seq (p/exception-rules idx))
      ;; the global closure on purpose, as in recheck-on-predicate: a re-check
      ;; trigger that under-selects is a missed withdrawal
      (doseq [pe (into (tax/genls tx super) closure-answered-exception-functors)]
        (mark-recheck kb (p/rules-with-exception-on idx pe) :all))
      (recheck-preserving-along kb 'genl))))

(defn- aggregate-rule?
  "Does the rule at `rh` carry an aggregate antecedent?  The two edge triggers below
  exempt one from their firing-side narrowing, because an aggregate binds a value and a
  census that rises licenses a firing there is no justification to find."
  [kb rh]
  (when-let [rsx (p/get-sentex (:records kb) rh)]
    (and (rules/rule? rsx) (rules/has-aggregate? rsx))))

(defn- refusals-reach?
  "Does rule `rh` have a refused firing `hit?` accepts — or a refusal record too full to
  hold entries at all, which is waved through?

  Both edge triggers below narrow on what a rule's **firings** look like, and a refused
  firing is a firing with no justification to read (`chain`'s \"a refused firing is
  remembered as bindings\"): without this they see a rule blocked on every firing as a
  rule that never fired, and skip it.  An `:overflow` record keeps no entries, so there
  is nothing to test and the only sound answer is yes.

  The record is read as a bare KB field rather than through `chain`, which writes it and
  sits three layers above here."
  [kb rh hit?]
  (let [r (get @(:refused kb) rh)]
    (if (set? r) (boolean (some hit? r)) (= :overflow r))))

(defn- recheck-genlContext-edge
  "A `genlContext` edge `(genlContext sub super)` was added or removed: queue only the
  excepted rules the visibility change can actually reach, instead of *every* excepted
  rule wholesale.

  An exception is evaluated in its conclusion's placement context and reads the facts
  visible from there.  The edge changes `sub`'s up-closure, so what any context *sees*
  changes exactly for the contexts that see `sub` — `context-down(sub)`, stable across
  the edge itself (the edge moves what `sub` sees, not who sees `sub`).  So an
  exception is affected iff one of its rule's firings is placed in `context-down(sub)`.

  Dependency narrowing, keyed on contexts (the twin of `recheck-genl-edge`'s predicate
  keying): iterate each excepted rule's firings — a cheap context lookup per firing, no
  query — and queue the rule only when one lands in the affected cone.  The level-6
  re-check queries in `settle` are then paid for the affected excepted rules alone, not
  all of them.  Guarded on the global exception-rule set, so a KB with no `exceptWhen`
  pays one set read and stops.

  Keyed on where a firing was **placed**, and a firing refused at derive time was never
  placed — so the same cone test is asked of the rule's **recorded refusals**, whose
  entries name the placement context the refused conclusion would have had.  Without
  that half, a rule blocked every time it fired has no context to read here and a
  widened cone that releases it reaches nothing.

  **An aggregate rule is exempt from that narrowing**, because for it the reasoning
  above is false in one direction.  Every other re-check condition is a block, so the
  thing a widened cone can change always has a firing to be found; an aggregate binds a
  **value**, and a census that rises licenses a firing that never existed.  There is no
  placed conclusion to read a context off, so the cone test finds nothing and the rule
  is silently skipped — a count taken in `SubContext` before it inherited `UpContext`
  stays taken.  The same asymmetry `settle/aggregate-recheck-rules` exists for, met the
  same way: queue it and let the re-join decide.  One record fetch per excepted rule, on
  a `genlContext` edge."
  [kb sub]
  (let [idx (:index kb) tms (:tms kb)
        excepted (p/exception-rules idx)]
    (when (seq excepted)
      (let [affected (tax/context-down (:taxonomy kb) sub)
            in-cone? (fn [jid]
                       (when-let [j (jtms/justification tms jid)]
                         (when-let [csx (p/get-sentex (:records kb) (:consequence j))]
                           (contains? affected (:context csx)))))]
        (doseq [rh excepted]
          (when (or (aggregate-rule? kb rh)
                    (some in-cone? (jtms/dependents tms rh))
                    (refusals-reach? kb rh #(contains? affected (:pctx %))))
            (mark-recheck kb [rh] :all)))
        ;; A predicate preserved along `genlContext` reads that closure across its
        ;; arguments, so the cone test above — which is about where a firing was
        ;; *placed* — cannot see it.
        (recheck-preserving-along kb 'genlContext)))))

(defn- binds-any?
  "Does the firing behind justification `jid` bind one of `terms` — at any depth, since
  a binding may be a compound whose argument merged?

  The **record**, not the network's graph entry: `jtms/graph-just` drops the bindings on
  the way into the JTMS (belief never reads them), so the store is the only place a
  firing's variable map survives.  Same read `settle` makes to re-run an exception."
  [kb terms jid]
  (when-let [j (p/get-justification (:records kb) jid)]
    (boolean (some (fn [v] (some terms (tree-seq sequential? seq v)))
                   (vals (:bindings j))))))

(defn- recheck-equality-edge
  "The equality closure moved — an equality was asserted, derived or retracted, or a
  schematic rewrite rule arrived or left.  Queue the rules carrying a re-check condition
  the move can reach.

  The third edge trigger beside `recheck-genl-edge` and `recheck-genlContext-edge`, and
  it is keyed like neither.  A merge moves what a belief-reading condition sees — an
  `exceptWhen` query, an `unknown`, an aggregate's census — in two ways nothing else
  does:

  * it **retires a spelling** rather than removing a fact.  The superseded sentex is
    still stored and still holds its handle, so no arm reports a fact arriving or
    leaving on its predicate — and yet it is gone from every belief-filtered read.
  * it **rewrites the condition's own goal**.  `(unknown (flies Tweety))` is answered
    under Tweety's representative, so merging Tweety with a Birdy that flies makes the
    condition false with nothing on `flies` having moved at all.

  The second rules out keying on a predicate, which is what `recheck-genl-edge` has:
  nothing on the condition's own predicate moved.  What is left is the **merged class**,
  and it keys the firings rather than the rules — the twin of `recheck-genlContext-edge`
  testing where a firing was placed, a set membership per firing and no query.  A firing
  is reached when it **binds** a term of the class, which is exactly the case
  `chain/settled-bindings` then has something to rewrite; a firing binding nothing that
  moved is asking the same question it asked before, and every other way the merge can
  reach it already has a trigger of its own.  A fact restated under the representative
  is a fact arriving on its own predicate; an `exceptWhen` meta-sentex naming a merged
  term migrates and re-registers itself.

  **Except an aggregate**, which takes `:all` and no test.  It binds a *value*, so the
  census can move with no term the firing names appearing in the merge at all — the
  firing that counted `(childOf Ann C3)` binds `Ann`, and the class is `{C2 C3}` — and
  a census that *rises* licenses a firing there is no justification for yet.  The same
  exemption `recheck-genlContext-edge` makes, for the same reason.

  A **schematic rewrite** takes `:all` too, and has no choice: it normalizes terms
  rather than merging symbols, so there is no class to test a binding against.  They
  are rare, and one arriving is a global change to the KB's normal forms.

  **And so does the removal side** — `terms` nil — where the narrowing is not merely
  imprecise but blind.  Splitting a class *releases* conditions, and what a release owes
  a re-derivation to is exactly the firings the block already swept: they hold no
  justification, so there are no bindings to test and the test would find nothing every
  time.  Adding an equality can only make a condition start holding, so there the
  surviving firings are the whole question; a retraction is rare beside the asserts, and
  pays the blanket.

  Gated on there being a re-check condition at all, so a KB that merges and uses none
  pays one set read per merge."
  ([kb] (recheck-equality-edge kb nil))
  ([kb terms]
   (let [tms (:tms kb)]
     (when-let [rules (seq (p/exception-rules (:index kb)))]
       (doseq [rh rules]
         (when (or (nil? terms)
                   (aggregate-rule? kb rh)
                   (some #(binds-any? kb terms %) (jtms/dependents tms rh))
                   ;; ...and the same question of a firing that was refused before it
                   ;; could hold a justification: its bindings are recorded, so the
                   ;; class-membership test reaches it exactly as it reaches a placed one
                   (refusals-reach? kb rh
                                    (fn [e] (some (fn [v] (some terms (tree-seq sequential? seq v)))
                                                  (vals (:bindings e))))))
           (mark-recheck kb [rh] :all)))))))

(defn- bump-roster!
  "Reference-count `ks` into the roster atom `a`, by `f` (`inc` or `dec`).

  Counted rather than a set, because two rules sharing an antecedent predicate — or a
  context — must not have the first retraction retire what the second still reads.  The
  same discipline the taxonomy's support counts keep.  A count reaching zero drops the
  key, so a roster stays the *live* vocabulary rather than everything a rule ever
  mentioned."
  [a ks f]
  (when (seq ks)
    (swap! a (fn [m] (reduce (fn [m k]
                               (let [n (f (get m k 0))]
                                 (if (pos? n) (assoc m k n) (dissoc m k))))
                             m ks)))))

(defn note-rule!
  "Add (`inc`) or drop (`dec`) a rule in the two rosters `visibility-seeds` reads: the
  predicates it takes as antecedents, and the context it is stated in.

  Both are kept here rather than derived on demand because both answer a question a
  `genlContext` edge asks and the index cannot: *which predicates could a seed usefully
  have*, and *does this cone hold a rule at all*.  Maintained at the rule index/unindex
  choke points, beside `:opposed` at the store's, and rebuilt by `recover` because
  recovery replays rule indexing."
  [kb rule-sentex preds f]
  (bump-roster! (:rule-antecedents kb) preds f)
  (bump-roster! (:rule-contexts kb) [(:context rule-sentex)] f))

(defn index-rule-sentex
  "Index a rule handle by **all** of its predicates — both sets are complete, so
  `rules-by-consequent` answers \"what could conclude P?\" for a forward-only rule
  too.

  Only the *predicates* are indexed.  The **record is the source of truth** for what
  a rule may do: a `set/*Rule` wrapper canonicalizes into the sentex (see
  `vaelii.impl.sentex`), and `:direction` / `:defeasible` are read off it by every
  consumer.  Nothing enumerates rules by defeasibility any more — defaults fire from
  the same agenda as strict rules — so there is no default-rule index to maintain.

  A rule is not a table entry: its trigger is the *shape* of the sentence (any
  functor can head an implication), so it is the structural arm of the
  `integrate-sentex` walk below, and this is its add half."
  [kb handle rule-sentex]
  (let [s (:sentence rule-sentex)]
    (p/index-rule (:index kb) handle
                  (rules/antecedent-predicates s)
                  (rules/consequent-predicate s))
    (note-rule! kb rule-sentex (rules/antecedent-predicates s) inc)
    ;; ...and, if it carries an `(unknown S)` antecedent, by the predicates that NAF
    ;; query mentions (`recheck-predicates`).  It must not make the rule term-indexed,
    ;; or `find-sentexes` on `penguin` would return a rule merely because it reasons
    ;; about penguins (docs/naf.md).  An `exceptWhen` exception rides a separate
    ;; meta-sentex, registered under this rule by `index-exceptWhen-meta` below.
    (when (rules/rechecked? rule-sentex)
      (p/index-exception (:index kb) handle (rules/recheck-predicates rule-sentex))
      ;; `:all`: a freshly indexed rule has no triggering sentence to narrow by, and by
      ;; the time settle drains the queue it may already have fired
      (mark-recheck kb [handle] :all))))

;; ---- exceptWhen meta-sentexes: the re-check posting for an exception ------
;; An exceptWhen exception is `(exceptWhen <query> (sentexHandle H))` — a meta-sentex
;; naming the rule H it qualifies.  The rule's exceptions are read from these
;; meta-sentexes (`provers/rule-exceptions`), so what the meta-sentex has to do on
;; arrival/departure is keep the re-check index in step: post/withdraw the rule H under
;; the query's predicates (so a matching fact re-checks H) and queue H for re-evaluation.

(defn index-exceptWhen-meta
  "Register the exceptWhen meta-sentex `meta-sentex` in the re-check index: post the
  rule it names under each predicate its query mentions and into the `:rules` roster,
  and queue the rule for a blanket re-check (a fact may already have arrived that its
  new exception blocks)."
  [kb meta-sentex]
  (let [rh    (sx/exceptWhen-rule-handle (:sentence meta-sentex))
        preds (keep nm/functor (sx/exception-query-conjuncts (:sentence meta-sentex)))]
    (when rh
      (p/index-exception (:index kb) rh preds)
      (mark-recheck kb [rh] :all))
    nil))

(defn- rule-remaining-recheck-preds
  "The predicates the rule `rh` must stay registered under after the exceptWhen
  meta-sentex `dropping-id` leaves: those of its *other* believed exceptWhen
  meta-sentexes' queries, plus its own `unknown` antecedents' — so a predicate two
  exceptions share, or one shared with a NAF antecedent, is not wrongly dropped."
  [kb rh dropping-id]
  (let [others (into #{}
                     (comp (map #(p/get-sentex (:records kb) %))
                           (filter some?)
                           (filter #(and (sx/exceptWhen-meta? (:sentence %))
                                         (= rh (sx/exceptWhen-rule-handle (:sentence %)))
                                         (not= dropping-id (:id %))))
                           (mapcat #(keep nm/functor (sx/exception-query-conjuncts (:sentence %)))))
                     (p/sentexes-with-term (:index kb) (sx/sentex-handle rh)))
        rsx    (p/get-sentex (:records kb) rh)]
    (into others (when rsx (rules/recheck-predicates rsx)))))

(defn unindex-exceptWhen-meta
  "The mirror of `index-exceptWhen-meta`: withdraw the departing exceptWhen
  meta-sentex's postings, then re-post the rule from the predicates its *remaining*
  exceptions and NAF antecedents still need — a set re-add restores any shared
  predicate the blanket withdraw over-removed, and leaves the rule off the `:rules`
  roster exactly when nothing watches it any more.  Queues the rule for re-check, since
  losing an exception may revive what it was blocking."
  [kb meta-sentex]
  (let [rh        (sx/exceptWhen-rule-handle (:sentence meta-sentex))
        this-preds (keep nm/functor (sx/exception-query-conjuncts (:sentence meta-sentex)))]
    (when rh
      (p/unindex-exception! (:index kb) rh this-preds)
      (when-let [remaining (seq (rule-remaining-recheck-preds kb rh (:id meta-sentex)))]
        (p/index-exception (:index kb) rh remaining))
      (mark-recheck kb [rh] :all))))

;; ---- except: visibility removal blocks derivations too -------------------
;; A believed `(except (sentexHandle H))` in context C hides H from C and its
;; descendants — for reads *and* for derivation: a rule firing that used H as an
;; antecedent and placed its conclusion in the cone rests on a fact that context can no
;; longer see, so the conclusion is swept (`chain/justification-excepted?` reads the
;; hidden set).  The trigger below queues the rules of every firing that uses H, so a
;; late `except` arriving (or leaving) re-checks and sweeps (or revives) them.  It is
;; the derivation-side twin of `recheck-on-sentence`, keyed on the *handle* the except
;; names rather than a predicate.

(defn recheck-except
  "An `(except (sentexHandle H))` fact arrived or left: queue every rule the visibility
  change touches, so `settle` (on arrival) sweeps a conclusion now resting on an
  invisible antecedent and `retract!` (on departure) re-derives one the fact can be seen
  for again.  Two rule sets, because the two directions need different rules:

    * the rules of firings that **use H** (`jtms/dependents`) — the conclusions to
      sweep when the except arrives; and
    * the rules that could **fire on H** (`rules-by-antecedent` over H's predicate and
      its supertypes, the same fan matching does) — the conclusions to re-derive when
      the except leaves, since by then the firing that used H has been swept away and
      `dependents` no longer names it.

  Queuing both on both directions over-approximates (the per-placement hidden-set test
  in `chain/justification-excepted?` and `derive-conclusion`'s block narrow it), which is
  the safe direction — a spurious re-check costs one query, a missed one leaves a
  conclusion resting on an invisible fact or fails to bring one back.

  Returns the rule handles it marked — the settle loop re-chains them when the
  trigger was a belief flip, which moves no blocked justification for the drain to
  notice on its own."
  [kb except-sentex]
  (when-let [h (sx/handle-id (second (:sentence except-sentex)))]
    (let [tms      (:tms kb)
          users    (keep (fn [jid]
                           (let [inf (:informant (jtms/justification tms jid))]
                             (when (integer? inf) inf)))
                         (jtms/dependents tms h))
          target   (p/get-sentex (:records kb) h)
          pred     (some-> target :sentence nm/functor)
          ;; the global closure on purpose: an under-selected re-check trigger is a
          ;; missed sweep or a missed revival
          firers   (when (symbol? pred)
                     (mapcat #(p/rules-by-antecedent (:index kb) %)
                             (tax/genls (:taxonomy kb) pred)))
          marked   (vec (into (set users) firers))]
      (mark-recheck kb marked :all)
      marked)))

(defn recheck-except-cone
  "A `genlContext` edge moved visibility for the contexts in `context-down(sub)`, which
  changes not only what an exceptWhen query sees (`recheck-genlContext-edge`) but also
  which handles a believed `except` hides from a context in the cone — so a derivation
  it blocks or releases must be re-checked too.  Re-queues every `except`'s affected
  firings (`recheck-except`).  Gated on the `except` root, so a KB using no `except`
  pays one count and stops; excepts are rare, so re-queuing all of them on a rare edge
  change is the cheap over-approximation."
  [kb]
  (let [idx (:index kb)]
    (when (pos? (p/count-with-functor idx sx/except-functor))
      (doseq [eh (p/sentexes-with-functor idx sx/except-functor)
              :let [esx (p/get-sentex (:records kb) eh)]
              :when esx]
        (recheck-except kb esx)))))

;; ---- the decontextualized predicate ---------------------------------------
;; `(decontextualizedPredicate P)` lifts every `(P ...)` out of the context it was
;; stated in and into UniverseContext, which every context sees — so the fact
;; stops being a claim of one theory and becomes a claim of the KB.
;;
;; The lift is a *deduction*: the original stays where it was stated and a copy is
;; derived in UniverseContext, justified by the placement sentex AND the declaration —
;; so retracting or defeating either withdraws the copy.  The KB documents the
;; mechanism in its own representation as the inert rule
;; `(implies (?pred . ?args) (ist UniverseContext (?pred . ?args)))`; it is implemented
;; in code because that dotted rule would match every fact in the store.
;;
;; **UniverseContext, and not a target the declaration names.**  The definitional
;; checks — disjointness, functionality, argIsa — are context-scoped: they run where
;; the fact is stated, against what is visible from there.  Lifting into a context the
;; stating context cannot see moves the fact somewhere those checks never looked, so
;; two facts that are each admissible where they were stated can meet in the target as
;; a disjointness violation nothing reports.  UniverseContext is the one target every
;; context sees, so the copy is visible to the next assert and the ordinary check
;; catches the clash at its source.  `unchecked-target?` below covers the one case that
;; leaves: a context wired outside the spindle, which does not see UniverseContext
;; either.

;; Genuine in-file cycle, threaded through the table.  Three derivation sites live
;; above the table and must reach the choke point below it: the lift's copy, the
;; equality arms' migrated twin and the argument-constraint entailment are all derived
;; sentexes, so all three go through `derived-sentex-added`, and equality and the
;; entailment additionally check `wff-problems` / `wff-violation` — and each of those
;; walks the very table these arms sit in.  The cycle is data-shaped (the table's
;; values are the arm fns), so four declares close it.
(declare derived-sentex-added integrate-twin wff-problems wff-violation)

(def universal-context 'UniverseContext)

(defn- unchecked-target?
  "Could the definitional checks have missed what this lift is about to create?

  They run at `src-context` against what is visible from there, so they have already
  considered everything in UniverseContext whenever `src-context` sees it — which is
  every context in a spindle-shaped KB.  When it does not, the copy lands where the
  stating context cannot look, and the check has to be re-run on the copy itself."
  [kb src-context]
  (not (tax/sees? (:taxonomy kb) src-context universal-context)))

(defn- deduce-lift
  "Deduce `sentence` (stored at `src-handle` in `src-context`) into UniverseContext,
  justified by `[src-handle, the declaration]` for each declaring sentex in `dhs` —
  one witness per declaration, as a migrated twin gets one per equality, so retracting
  one of two declarations leaves the copy standing on the other.

  Returns `{:new [handle] :violations [v]}` — the handle when the copy was newly
  created (the caller seeds chaining with it), the violation when the copy could not be
  admitted.  Reported rather than thrown, like every check off the assert path: a lift
  runs inside a fixpoint and inside `settle`, neither of which may abort halfway."
  [kb sentence src-handle src-context dhs]
  (if (or (empty? dhs) (= src-context universal-context))
    {:new [] :violations []}
    ;; the check the stating context could not run, run here — and only here, so a KB
    ;; whose contexts all see UniverseContext (the ordinary spindle) pays one `sees?`
    (if-let [v (and (unchecked-target? kb src-context)
                    (checks/constraint-violation kb sentence universal-context))]
      {:new [] :violations [(-> v
                                (assoc :sentence sentence :context universal-context)
                                (assoc-in [:detail :lifted-from] src-context))]}
      (let [[h2 s2 new?] (kb/find-or-create-sentex kb sentence universal-context)]
        (if (= h2 src-handle)
          {:new [] :violations []}
          (do
            ;; the copy is a derived sentex in a context that did not have it: it
            ;; reaches the closures and posts its exception re-check trigger exactly as
            ;; a rule conclusion does
            (when new? (derived-sentex-added kb s2 h2))
            (doseq [dh dhs]
              (let [depth (inc (max (jtms/depth (:tms kb) src-handle) (jtms/depth (:tms kb) dh)))
                    antes [src-handle dh]]
                (jtms/ensure-node (:tms kb) h2 depth)
                (when-not (jtms/has-justification? (:tms kb) 'decontextualizedPredicate antes h2)
                  (let [jid  (p/next-id (:records kb))
                        ;; The lift adds no defeasibility of its own, so it confers
                        ;; :monotonic and `conferred-class` caps it at the weaker of the
                        ;; source fact and the declaration.
                        just (jtms/->just jid 'decontextualizedPredicate antes h2 {} :monotonic)]
                    (p/put-justification (:records kb) just)
                    (jtms/add-justification (:tms kb) just)))))
            {:new (if new? [h2] []) :violations []}))))))

(defn deduce-lifts
  "Deduce `sentence` (stored at `handle` in `context`) into UniverseContext if its
  predicate is decontextualized — `{:new [handles] :violations [v]}`, nil when the
  predicate carries no declaration.

  Called from both stores of new content — `assert` and forward chaining's
  `place-conclusion` — because a decontextualized predicate is a claim about the
  predicate, not about how a particular sentence arrived.  Lifting only what a caller
  asserted would make belief depend on arrival order: declare-then-derive would leave
  the conclusion unlifted while derive-then-declare lifted it through `lift-existing`,
  and the two orders are the same knowledge.

  The gate is a single in-memory cache read, because every assert and every placed rule
  conclusion pays it to find out there is nothing to do."
  [kb sentence handle context]
  (let [tax  (:taxonomy kb)
        pred (nm/functor sentence)]
    ;; the global property read on purpose: the lift decides the *storage* context,
    ;; and scoping it by what could see the declaration would be circular
    (when (and pred (tax/has-prop? tax :decontextualized pred))
      (deduce-lift kb sentence handle context
                   (tax/prop-supporters tax :decontextualized pred)))))

(defn- lift-existing
  "When a declaration arrives, retroactively deduce every `(pred ...)` sentex outside
  UniverseContext into it — so a declaration arriving after the facts reaches them,
  exactly as one arriving before reaches the facts that follow.  Same
  `{:new :violations}` result, so the copies it makes are chaining seeds like any
  other new content and a rule keyed on the predicate fires on them.

  Sweeps what is **stored**, not what is believed.  A copy of a defeated fact is
  justified by that fact and so is defeated too — the JTMS already says what a
  disbelieved antecedent means — whereas skipping it would leave the copy missing when
  the fact revives, which is belief depending on the order the defeat and the
  declaration arrived in.

  The extent is **snapshotted** before the first copy is made.  Every copy carries
  `pred` too, so it posts to the very term-index entry this is walking; `find-sentexes`
  is lazy, which would leave the walk reading a posting list the walk itself is
  extending.  The copies are all in UniverseContext and so would be filtered out
  anyway — this is not about which sentexes get lifted, but about not depending on
  whether a given index backend hands back a snapshot or a live view."
  [kb pred dh]
  (reduce (fn [acc s]
            (if-not (and (= pred (nm/functor (:sentence s)))
                         (not= universal-context (:context s)))
              acc
              (merge-with into acc (deduce-lift kb (:sentence s) (:id s) (:context s) #{dh}))))
          {:new [] :violations []}
          (vec (kb/find-sentexes kb pred))))

;; ---- the argument constraints, drawn as entailments ----------------------
;; `checks/constraint-entailments` reads what the visible `argIsa` / `argGenl`
;; declarations *say* about a sentence's arguments; this materializes it, and does so
;; the way the lift above does — as a derived sentex justified by `[the triggering
;; fact, the declaration]`.  That is the whole point: the type is **held** by its
;; supporters rather than merely produced, so retracting either one takes it back and
;; defeating the fact takes it out.
;;
;; Both directions, for the reason the lift has both: a declaration reaching back over
;; facts already stored must reach the same KB as one the facts arrive under, or belief
;; depends on which came first.  `deduce-arg-types` is fact-meets-declaration,
;; `entail-existing` is declaration-meets-facts.

(defn inadmissible
  "The violation that stops `sentence` from being stored in `context`, or nil — naming,
  the definitional constraints, well-formedness, and edge stratification, as one value.

  This is the triple `place-conclusion` runs over a rule's conclusion, and it holds of
  any content the engine mints on its own behalf: a `(T x)` can clash with a disjoint
  membership, a `(genl X T)` edge can close a taxonomy cycle or a cycle through
  negation, and a type used at the wrong arity is not a type membership at all.  Three
  callers ask it — the argument-type entailment below, forward chaining, and abduction,
  which asks it *before* minting a hypothesis so that a sentence no assertion could
  legally make is never one the search assumes.

  A **value**, never a throw.  Two of its callers run after their triggering sentex is
  stored (that is what gives them a handle to be justified by) and inside a fixpoint,
  neither of which may abort halfway; the third would rather refuse a hypothesis than
  fail the query that wanted it."
  [kb sentence context]
  (or (when-let [ps (nm/blocking-problems (:naming kb) sentence context)]
        {:violation :naming
         :detail    {:message (str "naming invariant: " (str/join "; " ps))}})
      (checks/constraint-violation kb sentence context)
      (wff-violation kb sentence)
      (checks/edge-stratification-violation kb sentence)))

(def ^:private empty-entailment-result {:new [] :violations []})

;; Genuine in-file cycle: a minted type draws its own entailments, so `entail-arg-type`
;; calls back into `deduce-arg-types`, which is the fold over it.  Reordering cannot
;; break it — the recursion is the cascade, and its termination argument is in
;; `entail-arg-type`'s docstring.
(declare deduce-arg-types)

(defn- entail-arg-type
  "Materialize one entailment: store `(:assert ent)` in `context` and justify it by
  `[src-handle, the declaration]`.  `{:new [handle] :violations [v]}` — the handle when
  the sentex was newly created (the caller seeds chaining with it), the violation when
  it could not be admitted.

  Depth and strength are the lift's: one past the deeper of its two supporters, and
  `:monotonic` conferred, because the entailment adds no defeasibility of its own —
  `conferred-class` caps it at the weaker of the fact and the declaration, so a default
  fact yields a default type.  The informant is the declaring predicate, so `why` names
  `argIsa` beside the two sentexes rather than an anonymous derivation.

  **A minted type draws its own entailments**, and must: the retroactive direction
  cascades whether or not this one does — a declaration arriving over a stored `(t1 x)`
  reaches it through `entail-existing` — so a forward direction that stopped at one
  level would make the two orders disagree.  It recurses only on *progress* (a sentex
  created, or a justification added), which is what bounds it: both are content-keyed
  and monotone within a pass — `find-or-create-sentex` returns the existing handle and
  `has-justification?` refuses a second copy — and the sentences that can be minted are
  a subset of the finite `{(type, term)}` product the KB's own vocabulary spans.  Each
  recursive step therefore consumes one element of a finite set that never shrinks, so
  the cascade closes; the cycle test in `argtype_entail_test` is the check on that."
  [kb ent src-handle context]
  (let [sentence (:assert ent)
        dh       (first (:because ent))]
    (if-let [v (inadmissible kb sentence context)]
      {:new [] :violations [(assoc v :sentence sentence :context context
                                   :entailed-from src-handle)]}
      (let [[h2 s2 new?] (kb/find-or-create-sentex kb sentence context)]
        (if (= h2 src-handle)
          empty-entailment-result
          (do
            ;; a derived sentex in a context that did not have it: it reaches the
            ;; closures and posts its exception re-check trigger exactly as a rule
            ;; conclusion does
            (when new? (derived-sentex-added kb s2 h2))
            (let [depth  (inc (max (jtms/depth (:tms kb) src-handle)
                                   (jtms/depth (:tms kb) dh)))
                  antes  [src-handle dh]
                  _      (jtms/ensure-node (:tms kb) h2 depth)
                  fresh? (not (jtms/has-justification? (:tms kb) (:kind ent) antes h2))]
              (when fresh?
                (let [jid  (p/next-id (:records kb))
                      just (jtms/->just jid (:kind ent) antes h2 {} :monotonic)]
                  (p/put-justification (:records kb) just)
                  (jtms/add-justification (:tms kb) just)))
              (merge-with into
                          {:new (if new? [h2] []) :violations []}
                          (if (or new? fresh?)
                            (deduce-arg-types
                             kb (checks/constraint-entailments kb sentence context)
                             h2 context)
                            empty-entailment-result)))))))))

(defn deduce-arg-types
  "Materialize the entailments `checks/constraint-entailments` drew over a sentence
  stored at `handle` in `context` — `{:new [handles] :violations [v]}`.

  Called from both stores of new content — `assert` and forward chaining's
  `place-conclusion` — because what a declaration says about an argument is a claim
  about the predicate, not about how a particular sentence arrived.  Entailing only
  what a caller asserted would make belief depend on arrival order, exactly as lifting
  only asserted content would."
  [kb entailments handle context]
  (reduce (fn [acc e] (merge-with into acc (entail-arg-type kb e handle context)))
          empty-entailment-result
          entailments))

(defn- retroactive-mints
  "The entailments a newly stored declaration `dh` draws over one already-stored sentex
  `sx`, materialized in `sx`'s **own** context.

  The stored sentex is put back through `checks/constraint-entailments` and the answers
  narrowed to this declaration, rather than the conditions being re-decided here: the
  two directions must agree about what a declaration entails, and the only way to be
  sure of that is for them to ask the same function.  What that buys is the whole
  local-vs-inherited rule for free — a declaration written in an ancestor context does
  not draw an entailment in a descendant when the facts arrive first either.

  A genuine negation is not argument-checked, so it entails nothing; nor does a rule,
  whose stored sentence is an implication."
  [kb sx dh]
  (if-not (and (= :true (:truth sx)) (nil? (:antecedent sx)))
    empty-entailment-result
    (let [sctx (:context sx)]
      (deduce-arg-types kb
                        (filter #(= [dh] (:because %))
                                (checks/constraint-entailments kb (:sentence sx) sctx))
                        (:id sx) sctx))))

(def ^:private entailing-declarations
  "The argument-constraint declarations that entail, with the arity each is written at —
  the roster `entail-existing` dispatches on, so a fourth kind is one line rather than a
  widened `and`."
  '{argIsa 3, argGenl 3, interArgIsa 5})

(defn entail-existing
  "When an `(argIsa P n T)` / `(argGenl P n T)` / `(interArgIsa P n T m U)` declaration
  arrives, draw what it now says about the `(P …)` sentexes **already stored** — so a
  declaration arriving after the facts reaches them exactly as one arriving before
  reaches the facts that follow.  Same `{:new :violations}` result, so the types it mints
  are chaining seeds like any other new content.  nil when `sentence` is not an argument
  constraint.

  Two of `interArgIsa`'s three arrival orders are covered here and at the door; the third
  — the *trigger's* type arriving after both the fact and the declaration — is the
  family's documented open-world non-reach (docs/taxonomy.md, \"What each constraint does
  in each arrival order\"), and `argIsa` has it too from the other side.

  Sweeps what is **stored**, not what is believed, for `lift-existing`'s reason: a type
  minted off a defeated fact is justified by that fact and so is defeated too — the
  JTMS already says what a disbelieved antecedent means — whereas skipping it would
  leave the type missing when the fact revives, which is belief depending on the order
  the defeat and the declaration arrived in.

  The extent is read off the **functor root**, which is the precise answer to \"every
  stored `(P …)`\", and snapshotted before the first mint: a minted `(T x)` posts to
  the roots the walk is reading, and no index backend promises whether a posting read
  is a snapshot or a live view."
  [kb sentence dh]
  (when checks/*assertive-arg-types?*
    (let [[f pred] sentence]
      (when (and (= (entailing-declarations f) (nm/arity sentence)) (symbol? pred))
        (reduce (fn [acc sx] (merge-with into acc (retroactive-mints kb sx dh)))
                empty-entailment-result
                (vec (keep #(p/get-sentex (:records kb) %)
                           (p/sentexes-with-functor (:index kb) pred))))))))

(defn subsumption-seeds
  "The stored facts a new `(genl sub super)` edge newly makes matchable, as chaining
  seeds — the taxonomy twin of `lift-existing`, and there for exactly the same reason.

  Matching fans an antecedent's functor over its `genl` **spec** closure, so an edge
  arriving after the facts changes which antecedents they satisfy: `(dog Muffet)` stored,
  then `(genl dog animal)`, and a rule on `(animal ?x)` should fire.  The semi-naive
  agenda never sees it — the arriving datum is the *edge*, and firing the rules keyed on
  `genl` is not the same thing as re-firing the rules the edge just connected.  Without
  this the same three sentences derive a conclusion in one order and not the other,
  which is the one thing belief may not depend on (docs/nmtms.md).

  The seeds are `sub`'s whole spec subtree, because subsumption is transitive: an edge
  at the top of a hierarchy makes every fact below it matchable at the new supertype.
  Believed only — a disbelieved fact matches nothing, and it will seed the agenda itself
  when it revives.  Cost is the subtree's extent, paid once per edge, and it is nothing
  on the ordinary load order (a hierarchy arrives before the facts under it, when the
  extent is empty).

  The *removal* side is `resubsumption-seeds` below: a firing names the `genl` edges it
  subsumed through, so dropping one withdraws what it licensed — and the facts have to
  go back on the agenda when the reachability outlives the supporter that left."
  [kb sentence]
  (when (= 'genl (nm/functor sentence))
    (let [[_ sub] sentence
          idx (:index kb)
          tms (:tms kb)]
      (when (symbol? sub)
        (into [] (comp (mapcat #(p/sentexes-with-functor idx %))
                       (distinct)
                       (filter #(jtms/in? tms %)))
              (tax/specs (:taxonomy kb) sub))))))

(defn visibility-seeds
  "The stored facts a new `(genlContext sub super)` edge newly makes matchable, as
  chaining seeds — the **context** twin of `subsumption-seeds`, and there for exactly
  the same reason.

  Matching fans an antecedent up the visibility cone, so an edge arriving after both the
  rule and the facts changes which facts the rule can see: `(cFactP CA)` in
  `MidContext`, a rule in `LowContext`, then `(genlContext LowContext MidContext)`, and
  the rule should fire.  The semi-naive agenda never sees it — the arriving datum is the
  *edge*, and firing the rules keyed on `genlContext` is not the same thing as re-joining
  the rules the edge just gave a wider view.  Without this the same four sentences derive
  a conclusion in the orders that put the edge first and nothing in the others, which is
  the one thing belief may not depend on (docs/nmtms.md).

  **Both cones, because an edge pairs rules and facts in two directions.**  It is not
  only that a rule below can now see facts above: a rule stated *above* applies in every
  context that sees it, so the edge equally hands the general rule the specialized
  context's own facts, and places its conclusion there.  Seeding is by fact, so the seeds
  are the believed sentexes of `super`'s **up**-cone — seeing `super` means seeing
  everything `super` sees — together with those of `sub`'s **down**-cone, the contexts a
  rule above is now inherited into.  Taking one and not the other fixes half the orders
  and leaves the rest, which is worse than either: the shape that still fails is the
  narrower one, and so the easier to mistake for correct.

  **Enumerated from the rules, not from the cone**, and the difference is asymptotic
  rather than a constant.  Walking the cone and keeping the facts some rule could match
  costs one record fetch per sentex *in the cone* — so wiring N contexts under a
  `UniverseContext` holding K facts is O(N·K) where the KB without this is O(N+K), and
  building a spindle D deep is O(D²) because each edge's up-cone is the whole chain
  above it.  Measured: 3.9x on the first shape, 5x and climbing with depth on the
  second, and 1.8x on the starter load, which does wire contexts after filling them.

  So it goes the other way.  `:rule-antecedents` is the live roster of predicates some
  rule takes as an antecedent, kept O(1) at the rule index/unindex choke points beside
  `:opposed`; this walks *those* predicates' extents and keeps the facts whose context
  is in the cone.  Cost is then proportional to the rule-relevant facts and independent
  of how much ontology the cone holds — a KB with no rules pays one map read, and the
  upper ontology sitting in `UniverseContext` is not walked because almost none of it is
  a rule antecedent.  The cone is a set membership per candidate, so it costs nothing to
  ask about both cones.

  **And each half is gated on the other holding a rule**, which is what makes the
  ordinary case free rather than merely cheap.  Seeding `super`'s facts is worth nothing
  unless some rule sits in `sub`'s down-cone to newly see them, and seeding `sub`'s facts
  nothing unless a rule sits in `super`'s up-cone to be inherited into it.  Wiring an
  empty context under a full one — the commonest edge there is — holds no rule on the
  new side, so it seeds nothing at all, where without the gate it re-seeds the whole
  ontology above and re-joins rules that already fired on every fact of it.  That is the
  difference between 3.9x on the shape and 1.0x, and it is not the enumeration but the
  chaining the seeds provoke.  `:rule-contexts` answers it as a map read per context in
  the cone, and contexts are few.

  The removal side needs no twin — dropping an edge *narrows* what a rule sees, and the
  ordinary dependency-directed sweep already withdraws a firing whose antecedent stopped
  being visible."
  [kb sentence]
  (when (= 'genlContext (nm/functor sentence))
    (let [[_ sub super] sentence
          preds (keys @(:rule-antecedents kb))]
      (when (seq preds)
        (let [idx  (:index kb)
              recs (:records kb)
              tms  (:tms kb)
              tx   (:taxonomy kb)
              ruled? @(:rule-contexts kb)
              up    (when (symbol? super) (tax/context-up tx super))
              down  (when (symbol? sub)   (tax/context-down tx sub))
              cone (cond-> #{}
                     (some ruled? down) (into up)
                     (some ruled? up)   (into down))]
          (when (seq cone)
            (into [] (comp (mapcat #(p/sentexes-with-functor idx %))
                           (distinct)
                           (filter #(jtms/in? tms %))
                           (filter (fn [h]
                                     (when-let [s (p/get-sentex recs h)]
                                       (contains? cone (:context s))))))
                  preds)))))))

(defn resubsumption-seeds
  "The chaining seeds a teardown owes, given the `removed` sentexes its sweep collected
  — `subsumption-seeds` in the retraction direction.

  A firing that matched by subsumption names **one** witness for the `genl` path it
  used (`taxonomy/reach-support`), so removing an edge on that path invalidates the
  justification and the dependency-directed sweep collects the conclusion.  That is the
  point.  But a reachability can outlive one of its supporters — the same edge asserted
  from a second context, or a second path around the one that went — and then the
  conclusion is still licensed and must come back.  So the spec subtree under every
  removed edge goes back on the agenda and the rules fire again over it.

  Revival is a **re-derivation**, at a fresh handle, exactly as it is under
  `exceptWhen`: the sweep deleted the conclusion, so there is no label to flip back.
  That is the price of naming a witness rather than every witness, and it is the same
  price the qualitative support pays for the same reason (docs/qcn.md) — carrying every
  route would be one justification per path through a hierarchy where paths multiply.

  Two things make the reading exact.

  It is taken **before** the teardown, while the taxonomy still holds the departing
  edge: `specs` is what decides which facts could have subsumed through it, and reading
  it afterwards asks the shrunken hierarchy a question about the whole one — with
  `(genl dog mammal)` gone, `specs(mammal)` no longer names `dog`, whose facts are
  exactly the ones that need re-joining.

  And it is gated on the sweep having taken **something besides the records asked
  for**: a justification naming the departing edge is deleted with it, so a conclusion
  that survived kept another one and needs no re-derivation, and a conclusion that did
  not is in `removed`.  So retracting an edge that licensed nothing — the common case —
  costs one functor read per removed record and no chaining at all."
  [kb removed]
  (when (next removed)
    (into []
          (comp (map :sentence)
                (filter #(= 'genl (nm/functor %)))
                (distinct)
                (mapcat #(subsumption-seeds kb %))
                (distinct))
          removed)))

;; ---- equality: rewriteOf / sameAs / equals ------------------------------
;;
;; Three assertable relations feed one equivalence closure in the taxonomy
;; (docs/equality.md).  The closure itself is `vaelii.impl.taxonomy`'s and the
;; read/rewrite half (`rewrite-term`, `rewrite-goal`, `displaced-terms`,
;; `rewritable-sentex?`) lives in `vaelii.impl.kb` beside `query`; what lives here
;; is everything that happens *because* two names turned out to denote one thing:
;;
;;   the equality table arm   the edge reaches the closure, like a genl edge
;;   migrate-class            every sentex naming a non-representative gets a rewritten
;;                            twin under the representative, derived and justified by
;;                            [the original, the equality]
;;   refresh-supersessions    the stale spellings stop being believed — and start again
;;                            when the merge goes away
;;
;; The three relations differ only in what they say *about* their members: only
;; `rewriteOf` names a preferred term, and that one argument is the whole of the
;; difference as far as the closure is concerned — which is why the table holds one
;; entry-shape for all three.

(defn- wff-violation*
  "`wff-problems` as a **value** in the shape `checks/constraint-violation` returns —
  the derivation-path form of the well-formedness check.  Public as `wff-violation`
  below the table; declared-through here because migration needs it before the
  table exists."
  [kb sentence]
  (when-let [ps (seq (wff-problems (:taxonomy kb) sentence))]
    {:violation :not-well-formed
     :detail    {:problems (vec ps)
                 :message  (str "not well-formed: " (str/join "; " ps))}}))

(defn- justify-twin!
  "Justify a migrated twin `twin-handle` by `[orig-handle, equality]` for each equality
  supporter in `eqs` — one independent witness per
  incident edge, so dropping any single equality leaves the rest and the ordinary
  sweep collects the twin when the last goes.  The restatement adds no defeasibility
  of its own, so each justification confers `:monotonic` and `conferred-class` caps it at
  the weaker of the original and the equality.  Idempotent (`has-justification?`)."
  [kb orig-handle twin-handle eqs]
  (doseq [eh (distinct eqs)]
    (let [depth (inc (max (jtms/depth (:tms kb) orig-handle) (jtms/depth (:tms kb) eh)))
          antes [orig-handle eh]]
      (jtms/ensure-node (:tms kb) twin-handle depth)
      (when-not (jtms/has-justification? (:tms kb) 'rewriteOf antes twin-handle)
        (let [jid  (p/next-id (:records kb))
              just (jtms/->just jid 'rewriteOf antes twin-handle {} :monotonic)]
          (p/put-justification (:records kb) just)
          (jtms/add-justification (:tms kb) just))))))

(defn- varmap-realign
  "The substitution mapping the *original* rule's canonical variables to the `twin`'s.

  A migrated exception's query is stored in the original rule's canonical variables
  (`assert-exceptWhen-meta!`), and the twin is built from the original's **canonical**
  sentence — so `(:varmap twin)` maps `{twin-canonical -> original-canonical}` and its
  inverse is exactly the realignment.  The identity when the merge did not reorder the
  antecedents (the common case), non-trivial only when a renamed predicate sorts to a
  different position and so renumbers the variables."
  [twin]
  (into {} (keep (fn [[tv ov]] (when (not= tv ov) [ov tv]))) (:varmap twin)))

(defn- rename-vars
  "Single-pass variable rename: replace each variable by its `m` mapping (identity when
  absent), **without** chasing the result.  `res/substitute` recurses into the value
  it substitutes (safe for the acyclic bindings unification produces), which loops on a
  variable *permutation* like `varmap-realign` returns; this does not."
  [m form]
  (cond
    (sx/variable? form) (get m form form)
    (sequential? form)  (apply list (map #(rename-vars m %) form))
    :else               form))

(defn- migrate-rule-exceptions
  "Carry rule `orig`'s `exceptWhen` exceptions onto its migrated twin `twin`.

  A rule and its exceptions are **separate** sentexes linked by the rule's handle —
  `(exceptWhen <query> (sentexHandle H))` names the rule H it qualifies — so migrating
  the rule to a new handle would strand its exceptions on the superseded original and
  the twin would fire *unguarded*.  So each believed exception meta-sentex naming
  `orig` gets a twin naming `twin` (its query rewritten to the representatives too, a
  no-op when the exception mentions no merged term), derived and justified by `[the
  meta, the equality]` — the same belief-following discipline the rule twin itself
  rides.  Retracting the merge collects the exception twins with the rule twin and the
  originals revive.  Registered through `integrate-twin`, so the twin meta re-posts in
  the exception re-check index under `twin`.

  `eqs` are the equality supporters that migrated the rule — the exception twin exists
  *because* the rule did, so it rests on the same merge."
  [kb orig twin eqs]
  (let [realign (varmap-realign (p/get-sentex (:records kb) twin))]
    (doseq [mh   (p/sentexes-with-term (:index kb) (sx/sentex-handle orig))
            :let  [msx (p/get-sentex (:records kb) mh)]
            :when (and msx
                       (sx/exceptWhen-meta? (:sentence msx))
                       (= orig (sx/exceptWhen-rule-handle (:sentence msx)))
                       (jtms/in? (:tms kb) mh))]
      ;; rewrite the query's terms to the representatives (a no-op when the exception
      ;; mentions no merged term) and realign its variables to the twin's canonical
      ;; numbering (a no-op when the merge did not reorder the antecedents)
      (let [q'  (mapv #(sx/canon (rename-vars realign (kb/rewrite-term kb %)))
                      (sx/exception-query-conjuncts (:sentence msx)))
            m'  (sx/exceptWhen-meta q' twin)
            ctx (:context msx)
            [h s new?] (kb/find-or-create-sentex kb m' ctx)]
        (when new? (integrate-twin kb s h))
        (justify-twin! kb mh h eqs)))))

(defn- equality-contexts
  "The contexts of every equality edge and schematic rewrite rule that could bear on
  `sentence` — the whole **class** of each symbol it names, not merely the edges
  incident on that symbol.

  The class is the unit because election is: `(rewriteOf B C)` and `(rewriteOf A B)`
  make `A` the head for `C` too, so an edge that touches nothing in the sentence still
  decides what the sentence's terms rewrite to.  Reading only the incident edges would
  enumerate one reader and miss the one whose extra edge moves the answer.

  Unbelieved supporters are kept.  This picks *candidate readers*, and each candidate
  re-reads belief and visibility for itself; over-approximating costs a rewrite that
  comes back unchanged, and under-approximating costs a reader.

  **Empty means the sentence cannot be restated at all**, since a rewrite comes from an
  equality edge or a schematic rule and this enumerates both.  That is the gate on the
  assert path — every asserted sentex is offered to migration — so it is written to
  answer *empty* before it allocates anything: which of the sentence's own symbols have
  merged, and which rules reach it, are both cheap set questions, and a sentence no
  merge touches never walks a class or reads a record."
  [kb sentence]
  (let [tx      (:taxonomy kb)
        merged? (tax/merged-term-pred tx)
        terms   (when merged? (sx/symbols-where merged? sentence))
        rules   (filterv #(rewrite/rule-applies? % sentence) (tax/rewrite-rules tx))]
    (if (and (empty? terms) (empty? rules))
      #{}
      (into #{}
            (keep (fn [h] (:context (p/get-sentex (:records kb) h))))
            (concat (for [t terms, m (tax/equiv-class tx t), eh (tax/equality-supporters tx m)]
                      eh)
                    (map :handle rules))))))

(defn- reader-contexts-for
  "The contexts whose election could restate `sentex` differently: its own, and every
  context where it meets an equality that bears on it.

  **The reader is not the fact's own context.**  A merge holds where it is visible, and
  who reads the fact is any context below it — each electing a representative over a
  different set of visible edges (`tax/scoped-class`).  A single normal form computed
  at the fact's context serves only that one reader; one computed globally serves none
  reliably, since it can be elected by an edge no reader of the fact inherits.  So the
  parties are `tax/meet-closure` of the fact's context with the equalities' — the same
  enumeration a qualitative network takes (docs/qcn.md) and for the same reason.

  Filtered to contexts that **see** the fact: a context the fact is invisible from has
  no view of it to restate.  Ordered most-general first, by the size of the context's
  own up-closure and then by name — a content-keyed order, so which twin a duplicate
  form collapses into cannot depend on arrival.  The fact's own context leads
  explicitly rather than by that key: it is the only reader that supersedes, and two
  mutually-visible contexts have up-closures of a size that would otherwise let a name
  decide which of them is the fact's.

  **No equality bearing on the sentence means no reader**, and that is the gate: nothing
  can restate it, so migration reads no closure and runs no rewrite.  One equality
  context closes almost as fast — `meet-closure` of a comparable pair is the pair, and
  the filter leaves the fact's own context alone."
  [kb sentex]
  (let [tx    (:taxonomy kb)
        pctx  (:context sentex)
        ectxs (equality-contexts kb (:sentence sentex))]
    (when (seq ectxs)
      (->> (tax/meet-closure tx (conj ectxs pctx))
           (filter #(tax/sees? tx % pctx))
           (sort-by (juxt #(if (= % pctx) 0 1) #(count (tax/context-up tx %)) str))))))

(defn- migrate-into
  "Restate `sentex` as `reader` sees it, and store the result there.  Returns
  `{:form <normal form> :new [h] :superseded [[datum reason]] :violations [v]}`, or nil
  when `reader`'s election leaves the sentence alone, rests on nothing it believes, or
  reproduces a form `placed` already holds somewhere `reader` can see — that twin is
  already this reader's answer and a second copy would report the fact twice."
  [kb sentex reader placed]
  (let [handle    (:id sentex)
        sentence  (:sentence sentex)
        tx        (:taxonomy kb)
        rewritten (sx/canon (kb/rewrite-term kb sentence reader))]
    (when-not (or (= rewritten (sx/canon sentence))
                  (some (fn [[c f]] (and (= f rewritten) (tax/sees? tx reader c))) placed))
      ;; every witness that justifies the twin, each an independent support so dropping
      ;; any one leaves the rest.  Two kinds, both belief-following and both applying
      ;; only where **visible** from the reader whose restatement this is:
      (let [eqs (concat
                 ;; symbol equalities incident on a term of the sentence
                 (filter (fn [eh]
                           (when-let [esx (p/get-sentex (:records kb) eh)]
                             (and (jtms/in? (:tms kb) eh)
                                  (tax/sees? tx reader (:context esx)))))
                         (mapcat #(tax/equality-supporters tx %)
                                 (filter symbol? (tree-seq sequential? seq sentence))))
                 ;; schematic rewrite rules that normalize a subterm of the sentence —
                 ;; the oriented equational rewriting of docs/equality.md.  A rule that
                 ;; rewrites nothing here contributed nothing to the normal form and
                 ;; must not appear as a support.
                 (for [{:keys [handle context] :as rule} (tax/rewrite-rules tx)
                       :when (and (rewrite/rule-applies? rule sentence)
                                  (jtms/in? (:tms kb) handle)
                                  (tax/sees? tx reader context))]
                   handle))]
        (when (seq eqs)
          (let [existing (kb/find-sentex-handle kb rewritten reader)
                v        (when-not existing
                           (or (checks/constraint-violation kb rewritten reader)
                               (wff-violation* kb rewritten)))]
            (if v
              {:form rewritten :violations [(assoc v :sentence rewritten :context reader
                                                   :rule handle)]}
              ;; A rule stores its wrappers on the record, not in the sentence, so the
              ;; rewritten form is a *bare* implication — re-wrap it with the original's
              ;; direction / defeasibility (`rules/rewrap`) before find-or-create, or a
              ;; forward-only or defeasible rule's twin would default to a plain two-way
              ;; `implies`.  The path drops the wrapper either way, so dedup and the
              ;; `existing` probe above are unaffected.
              (let [twin-sentence (if (rules/rule-sentence? rewritten)
                                    (rules/rewrap rewritten (:direction sentex) (:defeasible sentex)
                                                  (:assumption sentex) (:constraint sentex))
                                    rewritten)
                    [h s new?]    (kb/find-or-create-sentex kb twin-sentence reader)]
                ;; `integrate-twin`, not `derived-sentex-added`: a twin is a restated
                ;; **declaration** and must reach every cache/index arm an asserted one
                ;; does (the disjoint / metadata caches, the rule index), not merely the
                ;; genl closure edges the forward-chaining conclusion path narrows to.
                (when new? (integrate-twin kb s h))
                (justify-twin! kb handle h eqs)
                ;; A migrated rule's `exceptWhen` exceptions ride separate meta-sentexes
                ;; keyed by the rule's handle, so they must be re-pointed onto the twin
                ;; or it fires unguarded (docs/equality.md, round two).
                (when (rules/rule-sentence? rewritten)
                  (migrate-rule-exceptions kb handle h eqs))
                (cond-> {:form rewritten :new (if new? [h] [])}
                  ;; only the fact's own context supersedes: a reader below it restates
                  ;; the fact for itself and leaves the original believed where it lives
                  (= reader (:context sentex))
                  (assoc :superseded [[handle (kb/displaced-terms kb sentence reader)]]))))))))))

(defn migrate-sentex
  "Restate one stored sentex under its terms' representatives — **once per reader whose
  election differs**, not once per sentex.

  Returns `{:new [handles] :superseded [[datum reason]] :violations [v]}`.  Five things
  are load-bearing:

  * **Re-canonicalized, not substituted.**  The twin is built by find-or-create from
    the rewritten *sentence*, so it goes back through the `sentex` constructor.  A
    merge changes what a symmetric predicate's sorted argument order should be —
    `(siblingOf lo mid)` with `lo` retired in favour of a term sorting after `mid`
    has to come back as `(siblingOf mid hi)`, not `(siblingOf hi mid)` — and a
    textual substitution would quietly store one fact under two handles.
  * **Justified, not asserted.**  The twin is a derivation from `[the original, the
    equality]`, one justification per incident equality edge, so each merge is an
    independent witness and dropping the equality collects the twin through the
    ordinary dependency-directed sweep.  Dedup falls out: when the rewritten form is
    already stored, find-or-create returns that handle and it simply gains a support.
  * **One twin per election, placed where the reader that elected it lives.**  A merge
    applies where it is visible, so a fact above one is read by contexts that inherit
    different sets of edges and elect different representatives (`reader-contexts-for`).
    The fact's own context is always a reader and takes the twin that supersedes the
    original; a reader *below* it that elects something else gets its own twin, placed
    in that reader's context — the restatement is the reader's, not the fact's, and
    putting it where the fact lives would publish it to contexts whose election it is
    not.  Two readers electing the same form share one twin, at the more general of
    them.
  * **Checked, and dropped rather than thrown on failure.**  A merge can *create* a
    disjointness violation — `(dog Rex)` + `(cat Fluffy)` + a merge makes one
    individual both — so the same definitional checks `place-conclusion` runs guard
    this, and a failure is reported through `violations`.  The original is then left
    believed: superseding a spelling whose restatement was refused would lose the
    caller's knowledge outright.
  * **A reader that changes nothing costs one rewrite.**  The overwhelming case is a
    single reader — the fact's own context — because it takes two contexts stating
    equalities for a second election to exist at all."
  [kb sentex]
  (-> (reduce (fn [acc reader]
                (if-let [r (migrate-into kb sentex reader (:placed acc))]
                  (-> acc
                      (update :placed conj [reader (:form r)])
                      (update :new into (:new r))
                      (update :superseded into (:superseded r))
                      (update :violations into (:violations r)))
                  acc))
              {:placed [] :new [] :superseded [] :violations []}
              (reader-contexts-for kb sentex))
      (dissoc :placed)))

(defn- migrate-class
  "Restate every stored sentex naming a term the equality closure has displaced.

  `find-sentexes` answers \"every sentex containing this term, at any nesting depth\"
  in one index lookup, which is what makes migration affordable and what makes
  congruence free.  The whole class is walked rather than just the arriving edge's
  endpoints, because **a late `rewriteOf` can move the representative**: `(sameAs A
  B)` elects a term lexicographically and a later `(rewriteOf B A)` re-elects `B`, so
  everything already migrated to `A` has to migrate again.  Walking the class covers
  re-migration with no separate path — it is the expensive case, not a special one.

  A sentex is migrated whether it is currently believed or merely superseded: the
  superseded ones are exactly the twins of a previous election, and re-election has
  to be able to reach them."
  [kb terms]
  (let [tms (:tms kb)]
    (reduce
     (fn [acc t]
       (reduce (fn [acc sx] (merge-with into acc (migrate-sentex kb sx)))
               acc
               (filter #(and (kb/rewritable-sentex? kb %)
                             (or (jtms/in? tms (:id %)) (jtms/superseded? tms (:id %))))
                       (kb/find-sentexes kb t))))
     {:new [] :superseded [] :violations []}
     (remove #(= % (tax/representative (:taxonomy kb) %)) terms))))

(defn- integrate-equality
  "The equality relations' add arm: reflect the sentex into the closure and migrate
  what it displaces.  Also exactly what a *derived* equality — the one `functional`
  now infers instead of throwing — needs, which is why `derive-equality` below calls
  it rather than the full table walk."
  [kb sentex handle]
  (let [sentence (:sentence sentex)
        [_ a b]  sentence]
    (tax/add-equality (:taxonomy kb) a b handle (kb/preferred-term sentence))
    (let [class (tax/equiv-class (:taxonomy kb) a)]
      (recheck-equality-edge kb (set class))
      (migrate-class kb class))))

(defn- migrate-matching
  "Migrate every rewritable stored sentex naming symbol `head` — the candidate set for
  a schematic rewrite rule whose LHS is headed by `head`.  The head is present in
  every occurrence of the redex, so the term index gives a superset in one lookup;
  `migrate-sentex` recomputes each sentence's normal form and twins only the ones that
  actually change.  Same shape as `migrate-class`, keyed by the rule's LHS head rather
  than by a merged term's class."
  [kb head]
  (let [tms (:tms kb)]
    (reduce (fn [acc sx] (merge-with into acc (migrate-sentex kb sx)))
            {:new [] :superseded [] :violations []}
            (filter #(and (kb/rewritable-sentex? kb %)
                          (or (jtms/in? tms (:id %)) (jtms/superseded? tms (:id %))))
                    (kb/find-sentexes kb head)))))

(defn- confluence-violations
  "Non-confluent conflicts the just-cached rule `handle` forms with the other active
  rewrite rules, as violation entries for the ledger — **detection, not completion**
  (docs/equational.md).  A `:non-confluent` entry names the two rules and the two
  forms a shared term normalizes to, so the author sees that two schematic equations
  disagree; the engine still gives a deterministic normal form, so nothing is dropped."
  [kb sentex handle lhs rhs]
  (let [new-rule {:handle handle :lhs lhs :rhs rhs}]
    (for [nj (rewrite/non-joining-pairs new-rule (tax/rewrite-rules (:taxonomy kb)))]
      {:violation :non-confluent
       :rule      handle
       :with      (:with nj)
       :sentence  (:sentence sentex)
       :message   (str "non-confluent schematic rewrite rules " handle " and " (:with nj)
                       ": a shared term normalizes to both " (pr-str (:form-a nj))
                       " and " (pr-str (:form-b nj)))})))

(defn- integrate-rewrite-rule
  "A schematic equation's add arm (docs/equational.md): orient `(equals a b)` into a
  terminating rewrite, cache it belief-following in the taxonomy, migrate every stored
  sentex it normalizes to a justified twin — exactly the shape `integrate-equality`
  has for a symbol merge — and **surface** any non-confluent conflict with an existing
  rule into the migration result's `:violations` (filed by `assert` through
  `violations/report`, and logged).  Returns the migration result so the twins seed
  chaining.  Orientability was already enforced by `wff/equality-problems`, so `orient`
  never returns nil here."
  [kb sentex handle]
  (let [[_ a b]   (:sentence sentex)
        [lhs rhs] (rewrite/orient a b)]
    (tax/add-rewrite-rule (:taxonomy kb) handle lhs rhs (:context sentex))
    (recheck-equality-edge kb)
    (update (migrate-matching kb (first lhs))
            :violations into (confluence-violations kb sentex handle lhs rhs))))

(defn- supersession-map
  "The `datum -> representative` map of spellings the equality closure currently
  displaces, recomputed from the taxonomy.

  Derived state, like `defeated` and `blocked`: it is recomputed rather than
  accumulated, so a supersession cannot outlive the merge that caused it and a
  retracted equality gives the caller's premise back with no un-supersede path of its
  own.  Only the *current* entries are re-examined (plus whatever migration just
  added), which keeps this proportional to what has actually merged rather than to
  the KB.

  **Read from the sentex's own context**, the way migration writes it.  A datum lives in
  one context, and the question a supersession answers is whether *that* context has
  retired the spelling — so an equality it cannot see must not displace it, and a
  restatement elected below it is that reader's twin rather than a replacement for this
  one (`migrate-sentex`).  Asking globally instead would take a premise away from the
  context that asserted it on the strength of a merge stated somewhere it cannot see.

  **One visibility predicate per context, not per entry.**  Scoping the read costs a
  record fetch per equality supporter, and this walks every displaced datum on each
  merging assert — so a fresh predicate per entry would re-fetch the same supporter
  records once per entry, which is the whole reconcile squared.  The entries cluster
  hard by context (they are the sentexes one merge displaced), so memoizing across the
  walk collapses that to one fetch per supporter."
  [kb extra]
  (let [tms (:tms kb)
        vis (memoize #(res/visible-supporter-fn kb %))]
    (into {}
          (keep (fn [[d _]]
                  (when-let [sx (p/get-sentex (:records kb) d)]
                    (let [ctx       (:context sx)
                          visible?  (vis ctx)
                          rewritten (sx/canon (kb/rewrite-term* kb (:sentence sx) visible?))]
                      ;; still displaced only if its own terms still rewrite to
                      ;; something else *and* the restatement is actually stored
                      (when (and (not= rewritten (sx/canon (:sentence sx)))
                                 (kb/find-sentex-handle kb rewritten ctx))
                        [d (kb/displaced-terms* kb (:sentence sx) visible?)])))))
          (into (jtms/superseded tms) extra))))

(defn refresh-supersessions
  "Reconcile the superseded set with the equality closure — the equality analogue of
  `tax/refresh-beliefs`, and called from the same place for the same reason."
  ([kb] (refresh-supersessions kb nil))
  ([kb extra] (jtms/supersede (:tms kb) (supersession-map kb extra))))

(defn- derive-equality
  "Store `(equals x y)` in `context` as a **derivation** from `antes` and merge with
  it.  Returns the migration result, so the caller can seed chaining with the twins.

  The arguments are ordered by content, never by arrival: the sentence is a key, and
  a key that depended on which value the caller happened to assert second would make
  one merge store as two sentexes."
  [kb x y context informant antes]
  (let [[lo hi]    (sort [x y])
        sentence   (list 'equals lo hi)
        [h s new?] (kb/find-or-create-sentex kb sentence context)
        depth      (inc (reduce max 0 (map #(jtms/depth (:tms kb) %) antes)))]
    (jtms/ensure-node (:tms kb) h depth)
    (when-not (jtms/has-justification? (:tms kb) informant antes h)
      (let [jid  (p/next-id (:records kb))
            just (jtms/->just jid informant (vec antes) h {} :monotonic)]
        (p/put-justification (:records kb) just)
        (jtms/add-justification (:tms kb) just)))
    (when new? (derived-sentex-added kb s h))
    (integrate-equality kb s h)))

(defn derive-functional-equalities
  "`(functional P)` plus two symbol values for the same first argument **derives**
  `(equals V1 V2)` rather than throwing (docs/equality.md).

  `equals` specifically, not `sameAs`: the value of a functional role need not be an
  individual — a birthplace, a measurement — and OWL's `sameAs` is individuals-only.
  `equals` is the one of the three that always type-checks here.

  Making it a real justification is what makes it safe.  The risk of auto-inference is
  that one wrong `functional` declaration silently merges two real individuals across
  the whole KB — so the merge is justified by **[both facts, the declaration]**, `why`
  names exactly which declaration and which two facts caused it, and retracting any
  one of them runs the ordinary sweep and un-merges.  An opaque merge would be
  dangerous; an inspectable, reversible one is knowledge.

  Gated on the taxonomy's `:functional` mark before it reads the store.  This runs on
  **every** asserted fact and the store read is a `sentexes-matching` over an unscoped
  context, so on a KB that declares nothing functional — the common case, and every bulk
  load — the mark is what stands between an assert and an index query per fact to learn
  what an O(1) set lookup answers.  The mark is maintained by the same table entry that
  stores the declaration and replayed by `recover`, so it holds exactly when the query
  finds something; the unscoped arity is what keeps that equivalence, since the query
  under it names no context either.  The handle comes from the store, because a
  justification needs the declaring sentex itself, and only the true branch pays for it."
  [kb sentence context handle]
  (let [pred (nm/functor sentence)
        b    (second (nm/args sentence))
        fh   (when (tax/has-prop? (:taxonomy kb) :functional pred)
               (:id (first (kb/sentexes-matching kb (list 'functional pred) '?ctx))))]
    (when fh
      (reduce (fn [acc [oh v]]
                (if-not (and (checks/mergeable-values? v b)
                             (not (tax/same-class? (:taxonomy kb) v b)))
                  acc
                  (merge-with into acc
                              (derive-equality kb v b context 'functional [handle oh fh]))))
              {:new [] :superseded [] :violations []}
              (checks/functional-clashes kb sentence context)))))

(defn equate-existing
  "When a `(functional P)` declaration arrives, derive the equalities P's **already
  stored** facts license — the other direction of `derive-functional-equalities`, which
  is a fact meeting the declaration.  nil when `sentence` declares nothing functional.

  A declaration has to reach the facts already stored exactly as it reaches the facts
  that follow, which is the rule `entail-existing` states for the argument constraints
  and holds here for the same reason: whether two spellings denote one woman is a
  question about the KB's content, and an answer that depended on whether the schema or
  the facts were loaded first would be an answer about the file.  Written the ordinary
  way — declaration first, then the facts — this finds an empty extent and costs one
  functor-root read.

  Each fact is handed to `derive-functional-equalities`, which asks the same question
  from the other side, so the two directions cannot drift about what a functional slot
  licenses or what justifies the merge: the equality names both facts and this
  declaration whichever way round it was reached, and retracting any of the three
  un-merges.  Re-deriving is idempotent — `same-class?` skips a pair the closure already
  holds and `has-justification?` skips an argument it already has — so a slot filled by
  three values collapses to one class rather than to the first pair walked.

  Sweeps what is **stored** rather than what is believed, for `entail-existing`'s
  reason: an equality derived off a defeated fact rests on that fact and is defeated
  with it, where skipping it would leave the merge missing when the fact revives — belief
  depending on the order the defeat and the declaration arrived in.  The extent is read
  off the functor root and snapshotted before the first merge, since migration writes
  twins to the roots the walk is reading."
  [kb sentence]
  (when (and (= 'functional (nm/functor sentence)) (= 1 (nm/arity sentence)))
    (let [pred (first (nm/args sentence))]
      (when (symbol? pred)
        (reduce (fn [acc sx]
                  (merge-with into acc
                              (derive-functional-equalities
                               kb (:sentence sx) (:context sx) (:id sx))))
                {:new [] :superseded [] :violations []}
                (vec (keep #(p/get-sentex (:records kb) %)
                           (p/sentexes-with-functor (:index kb) pred))))))))

;; ---- the table -----------------------------------------------------------

(defn- prop-entry
  "The entry for a predicate-metadata mark — `(transitive P)`, `(symmetric P)`, … —
  which differ only in the `:props` key they maintain.

  `:derived?`, so a mark that arrives by *derivation* installs like an asserted one:
  a rule concluding `(symmetric P)`, and — the case that actually happens on every
  KB — the UniverseContext copy a `decontextualizedPredicate` lift makes of one.  The
  copy carries its own context, which is what a scoped `has-prop?` reads, so without
  this the mark is recorded only under the context the declaration was stated in while
  the *sentex* is visible everywhere.  `:rebuild` replays every stored sentex of the
  functor either way, so the live KB and the recovered one disagreed about the same
  store — a restart changed the answer."
  [kind]
  {:integrate    (fn [kb sx h] (tax/mark-prop (:taxonomy kb) kind (second (:sentence sx)) h (:context sx)))
   :disintegrate (fn [kb sx] (tax/unmark-prop! (:taxonomy kb) kind (second (:sentence sx)) (:id sx)))
   :rebuild      (fn [tax {[_ pred] :sentence id :id ctx :context}] (tax/mark-prop tax kind pred id ctx))
   :wff          wff/prop-problems
   :derived?     true})

(def ^:private equality-entry
  "One entry-shape for all three equality relations: they produce the same class,
  and the whole of their difference — whether a preferred term is named — is read
  off the sentence by `kb/preferred-term` inside the arms.

  Two compound shapes are **not** a symbol merge, and each arm dispatches on them:

  * `(rewriteOf T E)` with a compound `E` is a NAT reify-to-term declaration
    (docs/nat.md) — a quoted NAT expression the partition (over symbols) can hold no
    part of.  Skipped by every arm: stored as an ordinary quoting fact, findable by
    the term index, never in the partition.

  * `(equals L R)` with a variable-bearing compound side is a **schematic equational
    rule** — an oriented rewrite, cached in the taxonomy's rewrite-rule set rather
    than the partition (docs/equality.md, symbolic equational reasoning).  Its add arm
    orients and migrates; its removal drops the rule (the sweep collects the twins and
    `refresh-supersessions` revives the originals); its rebuild re-orients on recover.

  `wff/equality-problems` waves both compound shapes through the same way."
  {:integrate    (fn [kb sx h]
                   (let [s (:sentence sx) [_ _ b] s]
                     (cond
                       (rewrite/schematic-equation? s) (integrate-rewrite-rule kb sx h)
                       (sequential? b)                 nil   ; NAT rewriteOf-to-compound
                       :else                           (integrate-equality kb sx h))))
   ;; the merge (or rule) survives while any other sentex still asserts it; when the
   ;; last supporter goes the class splits (or the rule leaves) and
   ;; `refresh-supersessions` (at the next settle) gives the displaced spellings back —
   ;; which moves a census and a NAF judgement exactly as the merge moved them, so the
   ;; re-check trigger is owed on this side too
   :disintegrate (fn [kb sx]
                   (let [s (:sentence sx) [_ a b] s]
                     (cond
                       (rewrite/schematic-equation? s)
                       (do (tax/del-rewrite-rule! (:taxonomy kb) (:id sx))
                           (recheck-equality-edge kb))
                       (sequential? b) nil
                       :else
                       (do (tax/del-equality! (:taxonomy kb) a b (:id sx))
                           ;; no class to narrow by on this side: what a released
                           ;; condition owes a re-derivation to is the firings the block
                           ;; swept, which hold no bindings to test
                           (recheck-equality-edge kb)))))
   ;; no migration is replayed on rebuild: the twins and their justifications are
   ;; already in the durable store, so recovery restores the *closure* / *rule set* and
   ;; lets the caller's `refresh-supersessions` decide which spellings it displaces
   :rebuild      (fn [tax {s :sentence id :id ctx :context}]
                   (let [[_ a b] s]
                     (cond
                       (rewrite/schematic-equation? s)
                       (when-let [[lhs rhs] (rewrite/orient a b)]
                         (tax/add-rewrite-rule tax id lhs rhs ctx))
                       (sequential? b) nil
                       :else (tax/add-equality tax a b id (kb/preferred-term s)))))
   :wff          wff/equality-problems})

(defn check-entries
  "Refuse an ill-formed table at namespace load, so add/remove symmetry is a
  structural property rather than a review item.

  Two shapes are refused.  An entry with *some* of the cache arms — an `:integrate`
  whose `:disintegrate` or `:rebuild` is missing (or any other partial triple) is
  exactly the mirrored-cond drift this table exists to end: the cache would fill on
  assert and leak on retract, or come back wrong after `recover`.  And an entry with
  no arm at all, which is a typo.  Returns `entries` unchanged so it can wrap the
  def."
  [entries]
  (doseq [[f spec] entries]
    (let [cache-arms [:integrate :disintegrate :rebuild]
          present    (filterv #(get spec %) cache-arms)]
      (when (and (seq present) (not= (count present) (count cache-arms)))
        (throw (ex-info (str "special-predicate table entry for " f " is asymmetric: has "
                             (str/join ", " (map name present)) " but not "
                             (str/join ", " (map name (remove (set present) cache-arms)))
                             " — an add arm without its removal and rebuild halves leaks")
                        {:type    :bad-table-entry
                         :functor f
                         :present (set present)
                         :missing (vec (remove (set present) cache-arms))})))
      (when-not (or (:wff spec) (seq present))
        (throw (ex-info (str "special-predicate table entry for " f " has no arm at all")
                        {:type :bad-table-entry :functor f})))))
  entries)

(def entries
  "The special-predicate dispatch table, as an **ordered** vector of
  `[functor spec]` pairs — ordered because `rebuild-taxonomy` replays it top to
  bottom and a rebuild arm may read what an earlier one wrote (metatype membership
  reads the marks; nothing else is order-sensitive today, and keeping the assert
  path's traditional order costs nothing).  `table` below is the lookup view.

  This vector is *the* functor enumeration: integrate, disintegrate, rebuild and
  wff all walk it, so a predicate added here is added to all four at once and
  `check-entries` refuses it half-done."
  (check-entries
   (vec
    (concat
     [;; the two transitive relations: closure edges, belief-tracked in the
      ;; taxonomy.  Their arms post the exception re-check *edge* trigger —
      ;; on the derivation path as well as the assert path (`:derived?`), so a
      ;; rule-concluded edge re-checks the exceptions too.
      ['genl {:integrate    (fn [kb sx h]
                              (let [[_ a b] (:sentence sx)]
                                (tax/add-genl (:taxonomy kb) a b h (:context sx))
                                (recheck-genl-edge kb b)))
              :disintegrate (fn [kb sx]
                              (let [[_ a b] (:sentence sx)]
                                (tax/del-genl! (:taxonomy kb) a b (:id sx))
                                (recheck-genl-edge kb b)))
              :rebuild      (fn [tax {[_ a b] :sentence id :id ctx :context}]
                              (tax/add-genl tax a b id ctx))
              :wff          wff/genl-problems
              :derived?     true}]
      ['genlContext {:integrate    (fn [kb sx h]
                                     (let [[_ a b] (:sentence sx)]
                                       (tax/add-genlContext (:taxonomy kb) a b h (:context sx))
                                       ;; visibility moved: re-check the excepted rules
                                       ;; whose firings live in the affected context cone
                                       ;; (`context-down` of the edge's sub) — the
                                       ;; context-keyed twin of recheck-genl-edge — and
                                       ;; the `except`-blocked derivations the same move
                                       ;; may have released or newly blocked
                                       (recheck-genlContext-edge kb a)
                                       (recheck-except-cone kb)))
                     :disintegrate (fn [kb sx]
                                     (let [[_ a b] (:sentence sx)]
                                       (tax/del-genlContext! (:taxonomy kb) a b (:id sx))
                                       (recheck-genlContext-edge kb a)
                                       (recheck-except-cone kb)))
                     :rebuild      (fn [tax {[_ a b] :sentence id :id ctx :context}]
                                     (tax/add-genlContext tax a b id ctx))
                     :wff          wff/genlContext-problems
                     :derived?     true}]
      ;; `:derived?` for the same reason the props carry it: a separation a rule
      ;; concluded must constrain the moment it is believed, not only after a restart
      ;; replays it — and its own context is what a scoped `disjoint?` reads
      ['disjoint {:integrate    (fn [kb sx h]
                                  (let [[_ a b] (:sentence sx)]
                                    (tax/add-disjoint (:taxonomy kb) a b h (:context sx))))
                  :disintegrate (fn [kb sx]
                                  (let [[_ a b] (:sentence sx)]
                                    (tax/del-disjoint! (:taxonomy kb) a b (:id sx))))
                  :rebuild      (fn [tax {[_ a b] :sentence id :id ctx :context}]
                                  (tax/add-disjoint tax a b id ctx))
                  :wff          wff/disjoint-problems
                  :derived?     true}]
      ['disjointMetatype
       {:integrate    (fn [kb sx h]
                        (let [[_ m] (:sentence sx)]
                          (tax/mark-disjoint-metatype (:taxonomy kb) m h (:context sx))
                          ;; Members already asserted are *recorded*, not turned
                          ;; into a clique of `(disjoint a b)` sentexes;
                          ;; `tax/disjoint?` consults the membership directly.  A
                          ;; member asserted later is picked up by the structural
                          ;; member arm in `integrate-sentex`.
                          (doseq [{[_ t] :sentence id :id mctx :context}
                                  (kb/sentexes-matching kb (list m '?t) '?ctx)]
                            (tax/add-metatype-member (:taxonomy kb) m t id mctx))))
        :disintegrate (fn [kb sx]
                        (let [[_ m] (:sentence sx)]
                          (tax/unmark-disjoint-metatype! (:taxonomy kb) m (:id sx))))
        ;; marks only: membership is replayed by rebuild-taxonomy's second pass,
        ;; once every metatype is known — the member functors are the metatypes
        ;; themselves, which no static table key can name
        :rebuild      (fn [tax {[_ m] :sentence id :id ctx :context}]
                        (tax/mark-disjoint-metatype tax m id ctx))
        :wff          wff/disjointMetatype-problems}]]
     (map (fn [kind] [(symbol (name kind)) (prop-entry kind)])
          [:transitive :symmetric :asymmetric :reflexive :functional])
     [['arity
       ;; `(arity P n)` is read by the per-assert arity check, so it is cached like the
       ;; other declarations the engine interprets rather than re-queried per
       ;; assertion.  `:derived?` for the same reason the prop marks are: a
       ;; decontextualizedPredicate lift makes a UniverseContext copy carrying its own
       ;; context, and a scoped read wants that context recorded.
       {:integrate    (fn [kb sx h]
                        (let [[_ pred n] (:sentence sx)]
                          (when (and (symbol? pred) (integer? n))
                            (tax/add-arity (:taxonomy kb) pred n h (:context sx)))))
        :disintegrate (fn [kb sx]
                        (let [[_ pred n] (:sentence sx)]
                          (when (and (symbol? pred) (integer? n))
                            (tax/del-arity! (:taxonomy kb) pred n (:id sx)))))
        :rebuild      (fn [tax {[_ pred n] :sentence id :id ctx :context}]
                        (when (and (symbol? pred) (integer? n))
                          (tax/add-arity tax pred n id ctx)))
        :derived?     true}]
      ['inverse {:integrate    (fn [kb sx h]
                                 (let [[_ p q] (:sentence sx)]
                                   (tax/add-inverse (:taxonomy kb) p q h (:context sx))))
                 :disintegrate (fn [kb sx]
                                 (let [[_ p q] (:sentence sx)]
                                   (tax/del-inverse! (:taxonomy kb) p q (:id sx))))
                 :rebuild      (fn [tax {[_ p q] :sentence id :id ctx :context}]
                                 (tax/add-inverse tax p q id ctx))
                 :wff          wff/inverse-problems
                 :derived?     true}]
      ['decontextualizedPredicate
       ;; the mark plus the retroactive lift; the lift's justifications need no
       ;; removal arm of their own — each is justified by this sentex, so the
       ;; ordinary dependency-directed sweep withdraws them when it goes.  The
       ;; rebuild replays the mark only: the lifted copies are already stored.
       ;; The integrate arm returns the `{:new :violations}` the equality arms return,
       ;; so a retroactively lifted copy is a chaining seed like any other new content.
       ;; NOT `:derived?`, unlike the marks it is built from: its integrate arm runs an
       ;; O(extent) retroactive lift whose copies are chaining seeds, and the derivation
       ;; path (`integrate-transitive`) discards an arm's return value — so a derived
       ;; declaration would lift silently and leave the copies off the agenda.  A rule
       ;; concluding this declaration is exotic; a half-run lift is not worth having.
       (-> (prop-entry :decontextualized)
           (dissoc :derived?)
           (assoc :integrate (fn [kb sx h]
                               (let [pred (second (:sentence sx))]
                                 (tax/mark-prop (:taxonomy kb) :decontextualized pred h (:context sx))
                                 (lift-existing kb pred h)))))]
      ['forcedDecontextualizedPredicate (prop-entry :forced-decontextualized)]
      ;; `(abduciblePredicate P)` is what lets abduction hypothesize a `(P …)` when a
      ;; proof dead-ends on one (docs/abduction.md).  Deliberately **not**
      ;; decontextualized, unlike the marks above it: `transitive` / `symmetric` are
      ;; claims about a predicate that hold wherever it is mentioned, while this is a
      ;; *policy* of the context that grants it — one theory may be willing to
      ;; assume `wasWashed` and another, reading the same predicate, may not.  The
      ;; scoped `has-prop?` arity is what reads it, so the grant reaches exactly the
      ;; contexts that see the grantor.
      ['abduciblePredicate (prop-entry :abducible)]
      ;; a NAT function's kind is predicate metadata like the marks above —
      ;; `(reifiableFunction F)` marks `:reifiable`, `(unreifiableFunction F)`
      ;; `:unreifiable`, belief-following through the same prop cache.  The reify
      ;; gate (`vaelii.impl.nat`) reads `:reifiable` in memory, so declaring a
      ;; function reifiable is what turns the reify pass on.  Their argument is a
      ;; function name (a `FruitFn`-shaped constant), so `prop-problems` — which
      ;; refuses an individual — is replaced by `function-decl-problems`.
      ['reifiableFunction   (assoc (prop-entry :reifiable)   :wff wff/function-decl-problems)]
      ['unreifiableFunction (assoc (prop-entry :unreifiable) :wff wff/function-decl-problems)]
      ;; `(functionCorrespondingPredicate F P N)` is read by the reify (both ways —
      ;; docs/nat.md), which reaches it through the index rather than a cache: the
      ;; declaration is consulted once per NAT, where the reify is already probing for
      ;; a `rewriteOf` target and a dedup, and the *gate* a KB declaring none pays is
      ;; an O(1) functor count.  So there is nothing to integrate, and the wff arm is
      ;; the whole entry.
      ['functionCorrespondingPredicate {:wff wff/correspondence-problems}]]
     ;; the three equality relations share one entry-shape; sorted so the table
     ;; is a pure function of the set, not of set iteration order
     (map (fn [f] [f equality-entry]) (sort kb/equality-predicates))
     ;; wff-only entries: argIsa / argGenl are constraints consumed at match time (no
     ;; cache to maintain), and so are the two preservation declarations — read back
     ;; through `matches-visible` per query, with the transitivity of the relation
     ;; they name checked here because `argIsa`'s open-world reading cannot
     ;; (docs/inherit.md).  `different` is never stored at all — its wff arm *is* the
     ;; refusal
     ;; ...and the query operators, never stored either — their wff arm is the
     ;; refusal: negation as failure (docs/naf.md) and the five aggregates, which are
     ;; the same family and take the same arm (docs/aggregate.md)
     (into [['argIsa               {:wff wff/arg-constraint-problems}]
            ['argGenl              {:wff wff/arg-constraint-problems}]
            ['interArgIsa          {:wff wff/inter-arg-constraint-problems}]
            ['argPreserving        {:wff wff/arg-preserving-problems}]
            ['argPreservingInverse {:wff wff/arg-preserving-problems}]
            ['different            {:wff wff/different-problems}]
            ['unknown              {:wff wff/naf-problems}]
            ['thereExists          {:wff wff/naf-problems}]]
           (map (fn [f] [f {:wff wff/naf-problems}]))
           (keys sx/aggregate-functors))))))

(def table
  "`entries` as the lookup map the walks below dispatch through."
  (into {} entries))

;; ---- the table walks -----------------------------------------------------

(defn wff-problems
  "Structural well-formedness problems for `sentence` (empty if OK) — the `:wff`
  column of the table, walked.  A sentence whose functor has no entry (or no `:wff`
  arm) is structurally unconstrained here; its argument *types* are still checked
  by the argIsa constraints."
  [tax sentence]
  (if-let [wf (:wff (get table (and (sequential? sentence) (first sentence))))]
    (wf tax sentence)
    []))

(defn wff-violation
  "The same check as a **value**, for content a rule *derived* rather than one a
  caller asserted: nil when `sentence` is well-formed, else a violation map in the
  shape `checks/constraint-violation` returns.

  `assert` checks this on the way in, but a rule may conclude a special predicate —
  `(implies (relates ?x ?y) (genl ?x ?y))` derives taxonomy edges — and the
  derivation path had no such check.  A derived edge reaches the closure through
  `integrate-transitive`, so a rule could close a `genl` cycle that the same edge
  asserted directly would have been refused for, leaving `genls`/`specs` cyclic —
  and those are what matching, placement and stratification all read.

  Dropped and reported rather than thrown, like every check on that path: chaining
  is a fixpoint and must not abort halfway through one."
  [kb sentence]
  (wff-violation* kb sentence))

(defn- structural-integrate
  "The **structural** integrate arms — the ones no functor can key, dispatched on the
  sentence's *shape* instead: a rule (any functor can head an implication), an
  exceptWhen meta-sentex (its second argument is a `(sentexHandle H)`), a visibility
  `except`, and a disjoint metatype's member (the functor is the metatype itself,
  known only at runtime).  Shared by `integrate-sentex` (the assert path) and
  `integrate-twin` (migration), so a migrated rule / meta twin reaches exactly the
  indexing an asserted one does."
  [kb sentex handle]
  (let [sentence (:sentence sentex)
        f        (nm/functor sentence)]
    (cond
      ;; an exceptWhen meta-sentex names a rule it qualifies — register it in the
      ;; re-check index under that rule
      (sx/exceptWhen-meta? sentence)  (index-exceptWhen-meta kb sentex)
      ;; a visibility `(except (sentexHandle H))` fact: queue the firings that use H
      ;; so settle sweeps any conclusion now resting on an invisible antecedent
      (= sx/except-functor f)         (recheck-except kb sentex)
      ;; a rule reaching the general path (e.g. rebuilt by recover, or a migrated
      ;; twin) is indexed from its own record, so it keeps the direction its wrapper
      ;; gave it
      (rules/rule-sentence? sentence) (index-rule-sentex kb handle sentex)
      ;; a member (M T) of a disjoint metatype: record T's membership, which is what
      ;; makes it disjoint from every other member.  Recording is O(1) and reversible;
      ;; asserting a `(disjoint t o)` per existing member was O(n) sentexes per member
      ;; — quadratic overall — and left premises no retraction could reach.
      (and (= 1 (nm/arity sentence)) (tax/disjoint-metatype? (:taxonomy kb) f))
      (tax/add-metatype-member (:taxonomy kb) f (first (nm/args sentence)) handle
                               (:context sentex)))))

(defn- run-integrate-arms
  "Run the one integrate arm that fits `sentex`: the table `:integrate` arm for a
  special functor, else the structural arm.  Shared by `integrate-sentex` (assert
  path) and `integrate-twin` (migration), so the dispatch lives in one place."
  [kb sentex handle]
  (if-let [e (get table (nm/functor (:sentence sentex)))]
    (when-let [g (:integrate e)] (g kb sentex handle))
    (structural-integrate kb sentex handle)))

(defn integrate-sentex
  "Reflect a newly stored sentex into the taxonomy / rule index / disjointness —
  the `:integrate` column of the table, walked, plus the structural arms above.

  Returns `{:new [handles] :superseded [[datum reason]] :violations [v]}` for an
  equality sentex — the twins it created are chaining seeds and the violations are
  the caller's to report — and nil for everything else.  (Only the equality arm
  has anything to say; every other arm mutates a cache and its return value is
  whatever that mutator handed back, so the result is normalized here rather than
  left for the caller to sort out.)"
  [kb sentex handle]
  (let [result (run-integrate-arms kb sentex handle)]
    (when (map? result) result)))

(defn integrate-twin
  "Full integration for a **migrated twin** — a restated declaration or fact the
  equality migration derives (`migrate-sentex`).  A twin must reach the same caches
  an asserted declaration would, or its class-representative spelling is stored and
  believed while the taxonomy never learns what it *declares*: a merged `(disjoint
  dog cat)` twin `(disjoint canine cat)` must reach `add-disjoint`, a `(transitive
  containedBy)` twin must reach `mark-prop`, and a migrated rule twin must reach the
  rule index or it never fires.  So this runs the same arms `integrate-sentex` does —
  the fuller integration `derived-sentex-added` (the forward-chaining conclusion path)
  deliberately narrows to the genl closure edges.

  The **equality arm is skipped**: a twin is never an equality sentex (those are held
  back from migration, `kb/rewritable-sentex?`), and running `migrate-class` from
  inside a migration would recurse.  Then the same re-check post every derived
  sentex gets — a migrated fact / declaration arriving is a trigger like an asserted
  one.

  Migration can run inside a forward-chaining pass (`derive-functional-equalities`
  infers an equality from a derived fact), so the table/structural arms can fire
  mid-fixpoint.  That is safe: none of them re-enter `assert` or `chain` — they add
  cache entries, justifications, and re-check queue items — and the common functional
  merge is of two individual *values*, whose twins are facts that match no
  declaration arm at all."
  [kb sentex handle]
  (let [sentence (:sentence sentex)]
    (when-not (kb/equality-sentence? sentence)
      (run-integrate-arms kb sentex handle))
    (recheck-on-sentence kb sentence)))

(defn disintegrate-sentex!
  "The mirror walk: reverse a departing sentex's cache effects through the
  `:disintegrate` column, or the matching structural arm.  Every cache below is
  reference-counted on the departing sentex's id, so an entry survives while
  another sentex still asserts the same claim."
  [kb sentex]
  (let [sentence (:sentence sentex)
        f        (nm/functor sentence)]
    (cond
      (contains? table f)
      (when-let [g (:disintegrate (get table f))] (g kb sentex))
      (sx/exceptWhen-meta? sentence)
      (unindex-exceptWhen-meta kb sentex)
      ;; a visibility `except` leaving: queue the firings that use its target so settle
      ;; revives the conclusions it was hiding — the mirror of the integrate arm
      (= sx/except-functor f)
      (recheck-except kb sentex)
      (rules/rule-sentence? sentence)
      (do (p/unindex-rule! (:index kb) (:id sentex)
                           (rules/antecedent-predicates sentence)
                           (rules/consequent-predicate sentence))
          (note-rule! kb sentex (rules/antecedent-predicates sentence) dec)
          ;; Deregistration **recomputes** the re-check predicates from the stored
          ;; sentex rather than trusting anything a caller has in hand.  The index
          ;; holds no derived state, so a mismatched deregistration only leaks a stale
          ;; posting — harmless, but recomputing is the rule that cannot drift.  The
          ;; rule's `unknown` antecedents' predicates come back out here; an exceptWhen
          ;; exception's are withdrawn by its own meta-sentex leaving (above).
          (when (rules/rechecked? sentex)
            (p/unindex-exception! (:index kb) (:id sentex)
                                  (rules/recheck-predicates sentex)))
          ;; ...and the firings it refused before they could become justifications.  A
          ;; refusal is dead when its rule goes, and this is the event that says so —
          ;; entries are otherwise dropped lazily, when a queued rule's record is
          ;; walked, and a departed rule is never queued again.
          (swap! (:refused kb) dissoc (:id sentex)))
      ;; a member leaving a disjoint metatype: it stops being disjoint from the rest.
      ;; With the clique materialized this was unreachable — the `(disjoint t o)`
      ;; sentexes were premises in their own right and outlived the membership.
      (and (= 1 (nm/arity sentence)) (tax/disjoint-metatype? (:taxonomy kb) f))
      (tax/del-metatype-member! (:taxonomy kb) f (first (nm/args sentence)) (:id sentex)))))

(defn integrate-transitive
  "The **derivation-path** subset of `integrate-sentex`: only the arms flagged
  `:derived?` — the genl / genlContext closure edges — run for a rule-derived
  conclusion, because the rest of integration either does not apply to a derived
  sentex or would re-enter `assert` from inside forward chaining.  Without this on
  the derivation path, a rule concluding `(genl a b)` stored and believed the sentex
  while the taxonomy never learned the edge — and `recover`, which reads the store,
  then disagreed with the running KB about what the KB entailed.  (A derived
  *equality* takes its own arm through `derive-functional-equalities`, which is the
  one derivation that concludes one.)"
  [kb sentex handle]
  (let [e (get table (nm/functor (:sentence sentex)))]
    (when (:derived? e)
      ((:integrate e) kb sentex handle))))

(defn derived-sentex-added
  "The derivation-path add choke point: everything that must happen because a
  **derived** sentex landed in the store — the closure-reaching integration above,
  and the exception re-check post, since a derived fact is a re-check trigger like
  an asserted one (an exception may be stated over a predicate that only ever
  arrives by inference — the cried-wolf case, where `liar` is concluded by another
  rule).

  Lives here rather than beside `sentex-added` in `vaelii.impl.integrate` because
  the equality arms are themselves derivation sites: a migrated twin and a
  functional-inferred `equals` are derived sentexes, and hand-rolling this pair at
  those sites is exactly the copy-paste the choke points exist to end.  Callers:
  forward chaining's `place-conclusion`, `migrate-sentex`, `derive-equality`."
  [kb sentex handle]
  (integrate-transitive kb sentex handle)
  (recheck-on-sentence kb (:sentence sentex)))

;; ---- rebuild: recover's replay of the table ------------------------------

(defn- stored-declarations
  "Every **stored** sentex whose functor is `f`, believed or not.

  Rebuilding from a belief-filtered read would quietly change what recovery means.
  Every cache follows the same discipline now: `:support` (genl/genlContext/equality)
  and `:cache-support` (disjoint, metatypes + members, props, inverse) are meant to
  record *every* asserting sentex, with `refresh-beliefs` deciding which entries are
  active.  Omit a disbelieved supporter and its handle is gone from the count, so
  clearing its defeat could never revive the entry — a defeated `(disjoint dog cat)`
  would then answer differently either side of a restart, and a disbelieved genl
  supporter's edge would be lost for good.

  So the taxonomy is rebuilt from what is stored, and belief is applied afterwards
  by the `settle` at the end of `recover`, exactly as it is during normal operation.

  Stored, not believed — but **positive**: `sentexes-with-functor` returns both
  polarities, and a `(not (genl a b))` *opposes* the edge rather than asserting it.
  The rebuild arms read the positive shape positionally, so a negation would bind
  its inner sentence as a taxonomy node and nil as the other — and the assert path
  never routes one here either, since its dispatch reads the functor `not`."
  [kb f]
  (->> (p/sentexes-with-functor (:index kb) f)
       (keep #(p/get-sentex (:records kb) %))
       (filter #(and (= :true (:truth %)) (nil? (:antecedent %))))))

(defn rebuild-taxonomy
  "Rebuild the in-memory taxonomy from the durable store: the `:rebuild` column of
  the table, replayed in entry order over the stored declarations of each functor.

  Drops every cache first: a rebuild that merged into the existing one could only
  ever *add*, so an entry whose sentex is gone would survive the recovery that was
  supposed to re-derive it."
  [kb]
  (let [tax (:taxonomy kb)]
    (tax/clear-relations! tax)
    (doseq [[f {:keys [rebuild]}] entries
            :when rebuild
            sx (stored-declarations kb f)]
      (rebuild tax sx))
    ;; Members second, once the metatypes are known — membership is what separates
    ;; them, and nothing about it is stored beyond the `(M T)` sentexes themselves.
    ;; A second pass rather than a table entry, because the member functors are the
    ;; metatypes: data, not vocabulary.
    (doseq [m (tax/disjoint-metatypes tax)
            {[_ t] :sentence id :id ctx :context} (stored-declarations kb m)]
      (tax/add-metatype-member tax m t id ctx))))
