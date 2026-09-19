;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.special
  "The special-predicate dispatch table: what each functor the engine interprets
  *does* to the derived state around the store, stated once, with every half of every
  behaviour side by side.

  A special predicate needs behaviour in four places — reflecting a stored sentex
  into the caches, the removal mirror, `recover`'s cache-only replay, and `wff`'s
  per-functor well-formedness check — and the compiler cross-checks none of them, so
  the arms live once here, in `arms`, keyed by functor:

    :integrate    (fn [kb sentex handle])  reflect a newly stored sentex into the caches
    :disintegrate (fn [kb sentex])         the mirror, reference-counted on (:id sentex)
    :rebuild      (fn [tax sentex])        recover's cache-only replay — no re-check
                                           posting, no migration, no universal lifting,
                                           because the store already holds what those
                                           side effects produced
    :wff          (fn [tax sentence context]) structural well-formedness (vaelii.impl.wff
                                           keeps the check fns; the table points at them.
                                           `context` scopes the arms that read it — today
                                           only `disjoint-problems`)

  and `check-entries` refuses an asymmetric entry **at namespace load**, so an
  add-side arm without its removal and rebuild halves is a build failure rather
  than a cache that drifts on the first retraction or restart.

  **The enumeration is not here.**  Which functors the engine interprets, in what
  order, what each one *says* — its sentence shape, the `:props` kind it maintains,
  whether its arms run on the derivation path — is one entry per term in
  `vaelii.impl.predicates`, which requires nothing and so can be read by `taxonomy`,
  `wff` and `provers`, none of which can read this namespace.  That split is what
  lifts the four-place ceiling above: the arms need functions from four layers and
  can only ever live at layer three, while what a predicate *says* is needed at every
  layer there is.  `entries` joins the two, `check-declarations` refuses a
  disagreement, and `predicates_test` pins the join against the live rosters.

  `structural-integrate` stays outside that framework permanently and no declaration
  can name its arms: they dispatch on a sentence's *shape* rather than on its functor
  — a rule, an `exceptWhen` meta, a visibility `except`, and a disjoint metatype's
  member, whose functor is the metatype and so is data rather than vocabulary.

  What this namespace still owns is everything the arms are and everything they need:
  all four arm columns, the five walks over them, the exception re-check queue the
  taxonomy arms post to, the universal-predicate lifting, and the equality migration.
  Third layer of the engine stack (kb <- checks <- special <- integrate <- chain <-
  settle): everything here reads kb and checks, and the store-mutation choke points in
  `vaelii.impl.integrate` sit directly above."
  (:require [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.predicates :as pr]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rewrite :as rewrite]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
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
;; affordable: the TMS lists every justification a rule licenses under the rule's node,
;; so every firing is reachable from the rule through links the TMS already maintains,
;; and the index stays at the scale of the rule index rather than of the fact store.
;;
;; The queue is a **map** `{rule-handle -> triggers}` rather than a set, because rule
;; granularity is right for deciding *whether* to look at a rule and far too coarse
;; for deciding *which of its firings* to re-evaluate.  `triggers` is the set of
;; sentences that arrived or left — what `exception-blocked-set` narrows the rule's
;; firings by before paying for a single level-6 query — or `:all` where no such
;; sentence exists (a taxonomy edge moved, a rule was just indexed) and every firing
;; must be re-checked. `:all-rejoin` is the stronger form used when the move can create
;; a firing without changing any existing blocked justification; settle must then run
;; the rule join even if the ordinary exception pass otherwise looks unproductive.

(defn- mark-recheck
  "Queue `rule-handles` for exception re-evaluation at the next `settle`, recording
  `trigger` — the sentence whose arrival or departure could have flipped the exception
  — `:all` when there is no such sentence and every firing must be re-checked, or
  `:all-rejoin` when that unconditional check must also force a fresh join.

  The unconditional markers are absorbing, and `:all-rejoin` is the stronger one:
  once queued, adding a narrower trigger must not narrow it back."
  [kb rule-handles trigger]
  (when (seq rule-handles)
    (swap! (reasoning/recheck kb)
           (fn [m]
             (reduce (fn [m rh]
                       (let [cur (get m rh)]
                         (assoc m rh
                                (cond
                                  (or (= :all-rejoin cur) (= :all-rejoin trigger))
                                  :all-rejoin

                                  (or (= :all cur) (= :all trigger))
                                  :all

                                  :else (conj (or cur #{}) trigger)))))
                     m rule-handles)))))

(defn- recheck-preserving-along
  "`rel` is the relation of some `(transitiveInArg P n rel)` declaration and its extent
  just moved — a fact on it arrived or left, or it is `genl` / `genlCx` and an
  edge moved.  Queue every rule whose exception mentions a declaring `P`.

  This is the argument-side twin of the predicate keying below.  An exception on
  `largerThan` is answered by `TransitiveInArgProver` walking the *arguments'* reach, so
  `(genl chihuahua dog)` can flip it with neither `chihuahua` nor `dog` appearing
  anywhere near `largerThan` — the genls walk cannot see that, and the firings that
  predate the edge would keep a block the firings after it correctly drop.

  `:all`, never a narrowing trigger: the sentence that moved is on `rel`, and the
  exception is stated over `P`, so it could not narrow the right firings anyway."
  [kb rel]
  (let [idx (:index kb)]
    (doseq [[pred r] (inherit/declared kb)
            :when (= r rel)]
      (mark-recheck kb (reads/watched-rules-on idx pred) :all))))

(def ^:private declaration-subjects
  "Declaration functors, mapped to the argument positions naming a predicate the
  declaration licenses an inference **about**.

  These sentences move what a level-6 query answers about a predicate without being
  *on* that predicate, and without touching its extent.  `(symmetric sibOf)` makes a
  stored `(sibOf Ann Bob)` answer `(sibOf Bob Ann)`, and the three commutativity marks
  do the same at any arity — a stored `(covering W A B C)` answers a goal naming the
  parts in any order; `(inverse childOf parentOf)`
  makes it answer a goal on the partner predicate; `(asymmetric typL)` is what gives
  the converse the standing to deny a claim, so it decides whether
  `TransitiveInArgProver` finds anything against one.  The re-check index is keyed on
  the exception's own predicate and none of these functors is that predicate, so
  without this the firings that predate the declaration keep a conclusion the firings
  after it correctly drop — an order dependence, and the same one
  `recheck-preserving-along` closes on the argument side.

  Which position: the subject is argument 1 throughout, and `inverse` names two
  predicates because either one's goals are answered from the other's facts.

  Who is **absent**, in the three groups `predicates/check-facets` reads this roster
  against — a declaration answering goals about the predicate at argument 1 posts by one
  of the three routes or the rule refuses it at load:

  * **Answers no goal**, so the rule never asks: `functional` is read by the definitional
    checks and moves nothing a query says; `arity` and the decontextualization marks
    likewise.  They carry no `:answers` facet.
  * **Posts from its own arms** rather than through this shared path, which the
    `:retriggers` facet says: `arg`, whose arms post the arg-type re-check, and
    `closed_extent_predicate`.
  * **Reaches an exception through an ordinary fact trigger**, so there is nothing left
    for either route to post: `genlArg`, `quotedArg` and `interArg` — the rest of the
    argument-constraint family — each licensing inferences that are themselves stored
    sentexes.  Each records that in `:stops-short`, with its own version of the reason."
  '{transitive           [1]
    symmetric            [1]
    asymmetric           [1]
    reflexive            [1]
    commutative              [1]
    commutativeInArgs        [1]
    commutativeInArgAndRest  [1]
    inverse              [1 2]
    transitiveInArg        [1]
    transitiveInArgInverse [1]})

(def recheck-subjects
  "`declaration-subjects`' functors as a set — which declarations post to the exception
  re-check queue through the shared path rather than from arms of their own.

  Public because `predicates/check-facets` holds every declaration that answers goals
  about a predicate to posting by one route or the other, and the two routes live in
  different namespaces: a `:retriggers` facet says the arms do it, this says
  `recheck-declaration` does.  A declaration in neither decides by arrival order, which
  is what that rule refuses at load."
  (set (keys declaration-subjects)))

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
  reads at use for every `(transitiveInArg P n R)` — so withdrawing it withdraws the
  inheritance for a `P` this sentence never names, and `recheck-preserving-along` is
  exactly the walk from a relation to those predicates.

  Gated on some rule carrying an `exceptWhen` at all, so a KB using neither feature
  pays one map lookup on the functor and a set-cardinality read."
  [kb sentence]
  (when-let [poss (get declaration-subjects (nm/functor sentence))]
    (let [idx (:index kb)]
      (when (seq (reads/watched-rules idx))
        (doseq [i    poss
                :let [pred (nth sentence i nil)]
                :when (symbol? pred)]
          ;; the global closure on purpose, as everywhere here: an over-selected
          ;; re-check re-evaluates and changes nothing, an under-selected one is a
          ;; wrong belief
          (doseq [p (tax/genls-global (reasoning/taxonomy kb) pred)]
            (mark-recheck kb (reads/watched-rules-on idx p) :all))
          (when (= 'transitive (nm/functor sentence))
            (recheck-preserving-along kb pred)))))))

(defn- arg-declared-types
  "The types some `(arg pred n T)` declares of `pred`'s argument positions — read off
  the roots rather than through `matches-visible`, and globally rather than per context,
  because a trigger has to be conservative in the direction the answer is and a
  declaration this context cannot see still qualifies a rule in one that can.

  `pred`'s **super-predicates** are read too, and globally for the same reason: a
  declaration on `parentOf` types the arguments of a `fatherOf` fact
  (`res/constraining-predicates`), so a trigger keyed on the exact functor would miss
  exactly the channel the descension opened."
  [kb pred]
  (let [idx (:index kb)]
    (when (pos? (reads/stored-count-with-functor idx 'arg))
      (into #{}
            (comp (mapcat #(reads/as-stored-with-args idx 'arg {1 %}))
                  (keep #(p/get-sentex (:records kb) %))
                  (map :sentence)
                  (filter #(and (= 'arg (nm/functor %)) (= 4 (count %))))
                  (map #(nth % 3))
                  (filter symbol?))
            (tax/genls-global (reasoning/taxonomy kb) pred)))))

(defn- recheck-arg-inferred
  "`arg` read as an **inference** rather than as a constraint: a believed `(P … x@n …)`
  beside `(arg P n T)` makes `x` a `T`, and every supertype of `T`
  (`provers/inferred-types`, behind `ArgTypeProver`).  So a fact on `P` flips an
  exception stated on `T` with nothing on `T` having been written and no relationship
  between the two predicates for the genls walk below to follow — the same shape of blind
  channel `recheck-preserving-along` closes on the argument side, and blind in the same
  way: without this the firings that predate the fact keep a conclusion the firings after
  it correctly drop, so which you get depends on when the fact arrived.

  Both arrival orders come here, and `sen` says which: a fact on `P`, whose declared
  argument types are read; or the `(arg P n T)` declaration itself, which does the
  same to every fact of `P` already stored.

  `:all`, for `recheck-preserving-along`'s reason: what moved is a fact about `P` (or a
  declaration about `P`'s argument positions), and the exception is about `T`, so the
  sentence could not narrow the right firings anyway.

  Free for a KB that declares no `arg` — one cardinality read, and
  `arg-declared-types` stops there.  A KB that declares plenty pays before the roster
  is probed at all: the seed walks `genls(pred)`, reads the `arg` postings on each and
  fetches a record per posting.  What a KB stating no exception over a declared type saves
  is only the tail — the probe per supertype answers empty and nothing is queued."
  [kb pred sen]
  (let [idx (:index kb)]
    (when-let [ts (seq (if (= 'arg pred)
                         (when (= 4 (count sen)) (filter symbol? [(nth sen 3)]))
                         (arg-declared-types kb pred)))]
      (doseq [t  ts
              t' (tax/genls-global (reasoning/taxonomy kb) t)]
        (mark-recheck kb (reads/watched-rules-on idx t') :all)))))

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
  relation some `transitiveInArg` declaration inherits along
  (`recheck-preserving-along`), or `pred` has an `arg`-declared argument type, which
  makes the fact evidence of a membership nobody wrote (`recheck-arg-inferred`)."
  [kb pred trigger]
  (when (symbol? pred)
    ;; No excepted rule anywhere ⇒ nothing to re-check, and walking `genls(pred)` just
    ;; to probe an empty exception set costs an up-closure per assert — quadratic over a
    ;; deep taxonomy load, and dead weight on every plain bulk load.  Guard on the global
    ;; exception-rule set (empty for any KB with no `exceptWhen`), exactly as its edge-side
    ;; twin `recheck-genl-edge` does.
    (let [idx (:index kb)]
      (when (seq (reads/watched-rules idx))
        ;; the global closure on purpose: an over-selected re-check re-evaluates and
        ;; changes nothing, an under-selected one is a missed withdrawal
        (doseq [p (tax/genls-global (reasoning/taxonomy kb) pred)]
          (mark-recheck kb (reads/watched-rules-on idx p) trigger))
        (recheck-preserving-along kb pred)
        (recheck-arg-inferred kb pred trigger)))))

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

  `calculus-triggered-by` rather than `calculus-for`, because what moves a network is
  wider than what one answers: the interval algebra reads a metric **narrowing** beside
  its stored facts, so a `temporalDistance` or a `startOf` arriving changes what is
  entailed between two intervals while being a predicate no interval rule mentions.  The
  rules queued are still keyed on the calculus's own predicates — those are the antecedents
  a rule joins on.

  Bounded by the rules mentioning the calculus at all, which is zero for every KB that
  registered no prover.  Nil is close to free there: `qkb/calculus-for` memoizes the
  registered-calculus list against the registry vector, so a KB that opted into nothing
  pays a registry deref, a volatile read and an identity compare per asserted sentence,
  and the per-prover `instance?` scan only when the registry itself changed."
  [kb body]
  (when-let [calc (qkb/calculus-triggered-by kb (nm/functor body))]
    (let [idx (:index kb)]
      (mark-recheck kb
                    (into #{} (mapcat #(reads/as-stored-rules-by-antecedent idx %)) (:predicates calc))
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

(defn rules-watching
  "The watched rules — an `unknown` antecedent or an `exceptWhen` exception among their
  re-check conditions — that a change to `sentence` could move, keyed as
  `recheck-on-sentence` keys an arrival: the sentence's functor and, for a negation, its
  body's functor, each over its global supertype closure.  Empty for a KB with no watched
  rule.  `settle/released-by-defeat` reads it for a datum a resolution defeated, which
  moves belief without passing the store or removal chokepoints.

  The closure is the **global** one, as in `recheck-on-predicate`, and not scoped to a
  context: the two select the same rules for the same datum, and a rule selected here
  that the datum's contexts cannot reach costs one re-join that derives nothing, where a
  rule a scoped read missed would be a release never re-derived."
  [kb sentence]
  (let [idx (:index kb)]
    (if-not (seq (reads/watched-rules idx))
      #{}
      (let [b     (sx/underlying-body sentence)
            preds (cond-> [(nm/functor sentence)]
                    (and b (not= b sentence)) (conj (nm/functor b)))]
        (into #{}
              (comp (filter symbol?)
                    (mapcat #(tax/genls-global (reasoning/taxonomy kb) %))
                    (mapcat #(reads/watched-rules-on idx %)))
              preds)))))

(defn recheck-every-exception
  "Re-check **every** rule carrying an exception — the blanket trigger.  Two channels
  take it: `recover`, where nothing about blocking survives a restart so every exception
  must be re-decided from scratch and there is no edge or fact to narrow by, and
  `recheck-equality-edge` on the sides where its own narrowing is blind — a class
  splitting, and a schematic rewrite arriving.

  (A `genlCx` edge change does not come here: `recheck-genlCx-edge` narrows it
  to the excepted rules whose firings live in the moved visibility ancestor set, the context-keyed
  twin of `recheck-genl-edge`'s predicate keying.)

  There is no triggering *sentence* here — the whole blocking state is being rebuilt —
  so this queues `:all` and every firing of every queued rule is re-evaluated."
  [kb]
  (mark-recheck kb (reads/watched-rules (:index kb)) :all))

(def ^:private closure-answered-exception-functors
  "Exception functors a `genl` edge can flip **without** the edge's endpoints
  appearing anywhere near the registered predicate, so the genls-of-the-supertype
  walk in `recheck-genl-edge` cannot see them and they are waved through instead:

    genl      the transitivity prover answers a `(genl x y)` conjunct from the very
              closure the edge just moved
    disjoint  disjointness is closed under genl (both up-closures are walked), so
              any edge can connect a pair a declaration separates

  Both are answered across *arguments* — the conjunct's own arguments say nothing
  about which edge can move it — so neither can be keyed on a predicate and neither
  can be narrowed to a subset of the rule's firings.  They are queued `:all`.

  A negated conjunct registers under `not` (its functor) and is **not** here: it is
  keyed on the closure the edge actually moved, by `recheck-negated-exceptions`
  below.

  Everything else the level-6 stack can reach a `genl` edge reaches *through the
  spec closure of the registered predicate* — the fact fan-out, the arg type
  inference, a declared-transitive relation's own facts — and those are exactly
  what the genls walk covers.  With one exception, and it is why this set is not the
  whole story: argument-position preservation reads the closure of the **arguments**,
  so `(genl chihuahua dog)` flips an exception on `largerThan` with neither endpoint
  anywhere near it.  Which predicates those are is a property of the KB rather than
  of the code, so they cannot be listed here — `recheck-preserving-along` reads them
  per KB and this set is unioned with what it finds."
  '#{genl disjoint})

(def ^:private opaque-negated-body-functors
  "Functors under a `not` that `recheck-negated-exceptions` cannot key on, because the
  negation is over a *frame* rather than over a literal and the predicates that decide
  it are the frame's, at whatever depth.  A rule carrying one is queued rather than
  reasoned about."
  '#{and or implies exceptWhen thereExists forAll ist unknown})

(defn- negated-block-literals
  "The `not`-headed literals among rule `rh`'s re-check conditions — its believed
  `exceptWhen` conjuncts, its `unknown` antecedents' queries and its aggregate bodies.

  The same three sources `settle/exception-candidates` narrows a firing by, for the
  same reason: all three are read at firing time rather than named by the
  justification, and all three register the rule in the exception index under the
  functor of what they mention.  A negation registers under `not`, which is what makes
  this list the whole of what a rule is queued for on that key.

  The census bodies are peeled with `rules/watched-literals` first, because a joined body
  is a conjunction and a `(not …)` conjunct of one is exactly the literal this looks for:
  the conjunction's own functor is `and`, which reads as no negation at all."
  [kb rh]
  (let [rsx (p/get-sentex (:records kb) rh)]
    (filterv #(and (sequential? %) (= 'not (nm/functor %)))
             (concat (apply concat (provers/rule-exceptions kb rh))
                     (when rsx (rules/naf-queries rsx))
                     (when rsx (mapcat rules/watched-literals (rules/aggregate-queries rsx)))))))

(defn- negation-under-moved-closure?
  "Could a `genl` edge whose subtype's spec closure is `below` flip one of rule `rh`'s
  negated re-check conditions?

  A ground negation is answered from stored negative sentexes with no genl fan-out, so
  today no edge flips one at all and the honest answer is always false.  The wave-through
  is kept anyway, against contravariant negative matching: reading `(not (dog X))` off a
  stored `(not (animal X))` walks the **up**-closure of the conjunct's own predicate, and
  an edge `[sub super]` moves `genls(P)` for exactly the predicates `P` at or below
  `sub`.  So that is the keying — the contravariant twin of the covariant
  `genls(super)` walk beside it, on the one functor whose registration hides the
  predicate it is about.

  `below` is read after the mutation for `genls(super)`'s reason: an edge putting `sub`
  above `super` is a cycle, refused, so `specs(sub)` is the same set on both sides of
  the change.

  Answers **keep** wherever it cannot read the conjunct: a body whose functor is a
  variable or a compound, a connective frame (`opaque-negated-body-functors`), or a
  rule registered under `not` whose conditions this cannot find at all."
  [kb rh below]
  (let [lits (negated-block-literals kb rh)]
    (or (empty? lits)
        (boolean (some (fn [lit]
                         (let [f (nm/functor (sx/underlying-body lit))]
                           (or (not (symbol? f))
                               (contains? opaque-negated-body-functors f)
                               (contains? below f))))
                       lits)))))

(defn- recheck-negated-exceptions
  "Queue the rules whose **negated** re-check condition the moved `genl` edge can reach,
  where `sub` is the edge's subtype.

  Its own price is what makes it a separate walk from the wave-through above.  Queueing
  a rule is `:all`, and `:all` is the arm of `settle/exception-candidates` that skips
  the firing narrowing and re-evaluates every firing the rule ever made — one level-6
  query apiece.  A negated exception conjunct is ordinary common-sense content
  (`(exceptWhen (not (has_wings ?x)) …)`), so keying it on the functor alone puts the
  whole firing history of every such rule in front of the prover on every `genl` edge
  written anywhere, which is a cost proportional to the rule's history rather than to
  the edge.

  One record read per rule carrying a negated condition, and none at all for a KB that
  has none — the same shape and the same gate `recheck-genlCx-edge` uses on its
  own ancestor set test."
  [kb sub]
  (let [idx (:index kb)]
    (when-let [rules (seq (reads/watched-rules-on idx 'not))]
      (let [below (tax/specs-global (reasoning/taxonomy kb) sub)]
        (doseq [rh rules
                :when (negation-under-moved-closure? kb rh below)]
          (mark-recheck kb [rh] :all))))))

(defn- recheck-genl-edge
  "A `genl` edge `(genl sub super)` was added or removed: queue the rules whose exception
  the moved closure can actually reach, instead of every excepted rule.

  Only `super`'s up-closure matters for the predicate keying.  Every reachability
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

  Three channels the predicate keying cannot see are covered beside it: the two
  waved-through functors above, whose provers read the closure across arguments;
  `recheck-preserving-along`, for the declared preserved positions the code cannot name
  in advance; and `recheck-negated-exceptions`, keyed at the edge's **subtype** because
  a negation is the one condition read against its own predicate's up-closure.

  Sound by construction: every channel a genl edge can reach a level-6 answer through is
  either predicate-addressed here or covered by one of those three; where a channel is in
  doubt, the answer is to queue, not to skip — queueing conservatively is the fallback,
  never queueing everything always."
  [kb sub super]
  (let [tx (reasoning/taxonomy kb) idx (:index kb)]
    ;; No excepted rule anywhere ⇒ nothing to re-check, and computing `genls(super)`
    ;; just to iterate an empty rule set would make a deep `genl` load quadratic —
    ;; the up-closure grows with depth and this runs on every edge.  Guard on the
    ;; global exception-rule set, which is empty for a KB (like a bulk taxonomy load)
    ;; that uses no `exceptWhen`.
    (when (seq (reads/watched-rules idx))
      ;; the global closure on purpose, as in recheck-on-predicate: a re-check
      ;; trigger that under-selects is a missed withdrawal
      (doseq [pe (into (tax/genls-global tx super) closure-answered-exception-functors)]
        (mark-recheck kb (reads/watched-rules-on idx pe) :all))
      (recheck-negated-exceptions kb sub)
      (recheck-preserving-along kb 'genl))))

(defn- aggregate-rule?
  "Can an arriving fact *release* one of the rule at `rh`'s re-check conditions
  (`rules/arrival-releasable?`) — an aggregate whose census rises, or a nested NAF whose
  witness leaves?  The two edge triggers below exempt one from their firing-side
  narrowing, because such a condition licenses a firing there is no justification to
  find."
  [kb rh]
  (when-let [rsx (p/get-sentex (:records kb) rh)]
    (and (rules/rule? rsx) (rules/arrival-releasable? rsx))))

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
  (let [r (get @(reasoning/refused kb) rh)]
    (if (set? r) (boolean (some hit? r)) (= :overflow r))))

(defn- recheck-genlCx-edge
  "A `genlCx` edge `(genlCx sub super)` was added or removed: queue only the
  excepted rules the visibility change can actually reach, instead of *every* excepted
  rule wholesale.

  An exception is evaluated in its conclusion's placement context and reads the facts
  visible from there.  The edge changes `sub`'s up-closure, so what any context *sees*
  changes exactly for the contexts that see `sub` — `context-down(sub)`, stable across
  the edge itself (the edge moves what `sub` sees, not who sees `sub`).  So an
  exception is affected iff one of its rule's firings is placed in `context-down(sub)`.

  Dependency narrowing, keyed on contexts (the twin of `recheck-genl-edge`'s predicate
  keying): iterate each excepted rule's firings — a cheap context lookup per firing, no
  query — and queue the rule only when one lands in the affected ancestor set.  The level-6
  re-check queries in `settle` are then paid for the affected excepted rules alone, not
  all of them.  Guarded on the global exception-rule set, so a KB with no `exceptWhen`
  pays one set read and stops.

  Keyed on where a firing was **placed**, and a firing refused at derive time was never
  placed — so the same ancestor set test is asked of the rule's **recorded refusals**, whose
  entries name the placement context the refused conclusion would have had.  Without
  that half, a rule blocked every time it fired has no context to read here and a
  widened ancestor set that releases it reaches nothing.

  **An aggregate rule is exempt from that narrowing**, because for it the reasoning
  above is false in one direction.  Every other re-check condition is a block, so the
  thing a widened ancestor set can change always has a firing to be found; an aggregate binds a
  **value**, and a census that rises licenses a firing that never existed.  There is no
  placed conclusion to read a context off, so the ancestor set test finds nothing and the rule
  is silently skipped — a count taken in `CxSub` before it inherited `CxUp`
  stays taken.  The same asymmetry `settle/aggregate-recheck-rules` exists for, met the
  same way: queue it and let the re-join decide.

  One record fetch per excepted rule for that exemption test, and then one per **firing**
  for the ancestor set test — `some` short-circuits on a hit, so a rule the edge does reach costs
  the firings up to the first one in the ancestor set, and a rule it reaches through none costs
  every firing the rule ever made.  That is the price of narrowing on placement rather
  than queueing wholesale, and it is paid on a `genlCx` edge alone."
  [kb sub]
  (let [idx (:index kb) tms (reasoning/tms kb)
        excepted (reads/watched-rules idx)]
    (when (seq excepted)
      (let [affected (tax/context-down (reasoning/taxonomy kb) sub)
            in-ancestor-set? (fn [jid]
                               (when-let [j (jtms/justification tms jid)]
                                 (when-let [csx (p/get-sentex (:records kb) (:consequence j))]
                                   (contains? affected (:context csx)))))]
        (doseq [rh excepted]
          (when (or (aggregate-rule? kb rh)
                    (some in-ancestor-set? (jtms/dependents tms rh))
                    (refusals-reach? kb rh #(contains? affected (:pctx %))))
            (mark-recheck kb [rh] :all)))
        ;; A predicate preserved along `genlCx` reads that closure across its
        ;; arguments, so the ancestor set test above — which is about where a firing was
        ;; *placed* — cannot see it.
        (recheck-preserving-along kb 'genlCx)))))

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

  The third edge trigger beside `recheck-genl-edge` and `recheck-genlCx-edge`, and
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
  and it keys the firings rather than the rules — the twin of `recheck-genlCx-edge`
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
  exemption `recheck-genlCx-edge` makes, for the same reason.

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
   (let [tms (reasoning/tms kb)]
     (when-let [rules (seq (reads/watched-rules (:index kb)))]
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
  `genlCx` edge asks and the index cannot: *which predicates could a seed usefully
  have*, and *does this ancestor set hold a rule at all*.  Maintained at the rule index/unindex
  choke points, beside `:opposed` at the store's, and rebuilt by `recover` because
  recovery replays rule indexing."
  [kb rule-sentex preds f]
  (bump-roster! (reasoning/rule-antecedents kb) preds f)
  (bump-roster! (reasoning/rule-contexts kb) [(:context rule-sentex)] f))

(defn index-rule-sentex
  "Index a rule handle by **all** of its predicates — both sets are complete, so
  `rules-by-consequent` answers \"what could conclude P?\" for a forward-only rule
  too.  A rule whose consequent functor is a variable is filed under the
  `p/var-consequent-key` catch-all instead of a canonical `?var0` (see
  `rules/consequent-index-pred`); completeness of the consequent read is then the
  concrete bucket unioned with that catch-all, which `resolution/concluding-rule-handles`
  does.

  Only the *predicates* are indexed.  The **record is the source of truth** for what
  a rule may do: a `set/*Rule` wrapper canonicalizes into the sentex (see
  `vaelii.impl.sentex`), and `:direction` / `:defeasible` are read off it by every
  consumer.  Nothing enumerates rules by defeasibility — defaults fire from the same
  agenda as strict rules — so there is no default-rule index to maintain.

  A rule is not a table entry: its trigger is the *shape* of the sentence (any
  functor can head an implication), so it is the structural arm of the
  `integrate-sentex` walk below, and this is its add half."
  [kb handle rule-sentex]
  (let [antes (:antecedent rule-sentex)]
    (p/index-rule (:index kb) handle
                  (rules/antecedent-keys antes)
                  (rules/consequent-index-pred rule-sentex))
    (note-rule! kb rule-sentex (rules/antecedent-keys antes) inc)
    ;; ...and, if it carries an `(unknown S)` antecedent, by the predicates that NAF
    ;; query mentions (`recheck-predicates`).  It must not make the rule term-indexed,
    ;; or `find-sentexes` on `penguin` would return a rule merely because it reasons
    ;; about penguins (docs/naf.md).  An `exceptWhen` exception rides a separate
    ;; meta-sentex, registered under this rule by `index-exceptWhen-meta` below.
    ;; ...and by the predicates a **closed extent** turns into NAF, which is a taxonomy
    ;; read rather than a property of the sentence, so it is asked here where the kb is
    ;; (`rules/closed-extent-predicates-of`).  A grant asserted *after* the rule reaches
    ;; it through `index-closed-extent-rules` below.
    (let [ce (rules/closed-extent-predicates-of (reasoning/taxonomy kb) (sx/sentence-of rule-sentex))]
      (when (or (rules/rechecked? rule-sentex) (seq ce))
        (p/index-exception (:index kb) handle
                           (distinct (concat (rules/recheck-predicates rule-sentex) ce)))
        ;; `:all`: a freshly indexed rule has no triggering sentence to narrow by, and by
        ;; the time settle drains the queue it may already have fired
        (mark-recheck kb [handle] :all)))))

(defn index-closed-extent-rules
  "A `(closed_extent_predicate P)` grant arrived or left: post every stored rule with a
  **closed** `(not (P …))` antecedent in the re-check index under `P`, and queue it for a
  blanket re-check.

  The grant is what turns such an antecedent from a lookup into negation as failure, so
  a rule asserted before the grant carries no posting and no fact on `P` would ever bring
  its firings back.  Reached through the antecedent index on `[:not P]`, which is the key
  `rules/antecedent-key` files a negation under, so this is one lookup and no scan.

  Queued with **`:all-rejoin`**: what the grant moved is a whole reading, not a sentence,
  so there is nothing to narrow the firings by — and the rule owes a fresh **join** as
  well as a re-check, since the grant blocked nothing for the blocked set to notice and
  the firings it licenses are ones no justification exists for yet.  That is the same
  asymmetry a widened `genlCx` ancestor set takes `:all-rejoin` for.  The posting is left in place
  when the grant leaves: a spurious re-check costs one query, and a missing one is a
  conclusion that should have been swept and wasn't."
  [kb pred]
  (doseq [rh (reads/as-stored-rules-by-antecedent (:index kb) [:not pred])]
    (when-let [rsx (p/get-sentex (:records kb) rh)]
      (when (and (rules/rule? rsx)
                 (seq (rules/closed-negative-antecedents (:antecedent rsx))))
        (p/index-exception (:index kb) rh [pred])
        (mark-recheck kb [rh] :all-rejoin))))
  nil)

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
        preds (rules/watched-predicates
               (sx/exception-query-conjuncts (:sentence meta-sentex)))]
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
                           (mapcat #(rules/watched-predicates
                                     (sx/exception-query-conjuncts (:sentence %)))))
                     (reads/as-stored-with-term (:index kb) (sx/sentex-handle rh)))
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
        this-preds (rules/watched-predicates
                    (sx/exception-query-conjuncts (:sentence meta-sentex)))]
    (when rh
      (p/unindex-exception! (:index kb) rh this-preds)
      (when-let [remaining (seq (rule-remaining-recheck-preds kb rh (:id meta-sentex)))]
        (p/index-exception (:index kb) rh remaining))
      (mark-recheck kb [rh] :all))))

;; ---- except: visibility removal blocks derivations too -------------------
;; A believed `(except (sentexHandle H))` in context C hides H from C and its
;; descendants — for reads *and* for derivation: a rule firing that used H as an
;; antecedent and placed its conclusion in the ancestor set rests on a fact that context can no
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
      `dependents` no longer names it; and

    * **H itself, when H is a rule.**  A firing rests on its rule as it rests on its
      antecedents — the rule handle is in the stored justification, which is what
      sweeps its conclusions when the except arrives — but on departure the swept
      firing is gone from `dependents`, and the predicate fan above is keyed on a
      *fact's* functor, which a rule sentence never matches.  Re-chaining the rule is
      the departure-side twin the fact arm has in `rules-by-antecedent`: without it,
      retracting a rule-targeting except revives the rule's visibility and none of
      its conclusions.

  Queuing both on both directions over-approximates (the per-placement hidden-set test
  in `chain/justification-excepted?` and `derive-conclusion`'s block narrow it), which is
  the safe direction — a spurious re-check costs one query, a missed one leaves a
  conclusion resting on an invisible fact or fails to bring one back.

  Returns the rule handles it marked — the settle loop re-chains them when the
  trigger was a belief flip, which moves no blocked justification for the drain to
  notice on its own."
  ([kb except-sentex] (recheck-except kb except-sentex :all))
  ([kb except-sentex trigger]
   (when-let [h (sx/handle-id (second (:sentence except-sentex)))]
     (let [tms      (reasoning/tms kb)
           users    (keep (fn [jid]
                            (let [inf (:informant (jtms/justification tms jid))]
                              (when (integer? inf) inf)))
                          (jtms/dependents tms h))
           target   (p/get-sentex (:records kb) h)
           pred     (some-> target sx/sentence-of nm/functor)
           ;; the global closure on purpose: an under-selected re-check trigger is a
           ;; missed sweep or a missed revival
           firers   (when (symbol? pred)
                      (mapcat #(reads/as-stored-rules-by-antecedent (:index kb) %)
                              (rules/trigger-keys (reasoning/taxonomy kb) (:sentence target)
                                                  @(reasoning/rule-antecedents kb))))
           marked   (vec (cond-> (into (set users) firers)
                           (and target (rules/rule? target)) (conj h)))]
       (mark-recheck kb marked trigger)
       marked))))

(defn recheck-except-ancestors
  "A `genlCx` edge moved visibility for the contexts in `context-down(sub)`, which
  changes not only what an exceptWhen query sees (`recheck-genlCx-edge`) but also
  which handles a believed `except` hides from a context in the ancestor set — so a derivation
  it blocks or releases must be re-checked too.  Re-queues every `except`'s affected
  firings (`recheck-except`).  Gated on the `except` root, so a KB using no `except`
  pays one count and stops; excepts are rare, so re-queuing all of them on a rare edge
  change is the cheap over-approximation."
  [kb]
  (let [idx (:index kb)]
    (when (pos? (reads/stored-count-with-functor idx sx/except-functor))
      (doseq [eh (reads/as-stored-with-functor idx sx/except-functor)
              :let [esx (p/get-sentex (:records kb) eh)]
              :when esx]
        ;; A context edge can make two independently restored antecedents meet at a
        ;; reader without releasing any already-blocked justification.  Preserve that
        ;; distinction through the queue so settle forces the missing join exactly for
        ;; this visibility-transition shape.
        (recheck-except kb esx :all-rejoin)))))

(defn- belief-change-region
  "`moved` plus the targets of any visibility-excepts it names.

  A relabel reports the except handle because that is the TMS datum whose belief
  changed, while the derived cache is indexed by the declaration handle the except
  hides. Expanding at this boundary lets callers report the event they observed
  without knowing which cache supporter it invalidates.

  Gated on the `:excepted` roster, as the scan in `reconcile-belief-change` is: the
  roster holds every stored visibility except (`kb/note-excepted!`, at the store and
  removal choke points), so while it is empty no handle in `moved` can name one and the
  region is `moved` itself — without a record fetch per member, on a set that is the
  whole KB when a rebuild's settle reads it."
  [kb moved]
  (if (empty? @(reasoning/excepted kb))
    (set moved)
    (into (set moved)
          (keep (fn [h]
                  (some-> (p/get-sentex (:records kb) h)
                          :sentence
                          kb/except-target)))
          moved)))

(defn reconcile-belief-change
  "Reconcile every belief-derived taxonomy cache after `moved` may have changed truth.

  Bare, like `recover` and every other recompute: it rebuilds caches from what the KB
  currently believes and stores nothing of its own, so re-running it is the whole of
  taking it back.

  This is the engine-level choke point above `tax/refresh-beliefs`: ordinary JTMS
  defeat/revival/supersession and visibility `except` both change whether a stored
  declaration currently has force. `moved` may name either declaration handles or
  except handles; the latter are expanded to their targets before the scoped refresh.

  The three-argument form lets a removal path report a visibility change explicitly:
  once the exception record has been deleted, its target alone cannot prove why the
  effective-supporter generation changed.

  The two-argument form decides `visibility-moved?` by reading `moved`'s records for an
  except — behind the `:excepted` roster, so a KB storing no visibility except pays no
  fetch per moved handle (`belief-change-region` says why the gate is exact)."
  ([kb] (reconcile-belief-change kb nil))
  ([kb moved]
   (reconcile-belief-change
    kb
    moved
    (or (nil? moved)
        (and (seq @(reasoning/excepted kb))
             (some (fn [h]
                     (some-> (p/get-sentex (:records kb) h)
                             :sentence
                             kb/except-target))
                   moved)))))
  ([kb moved visibility-moved?]
   (let [region (when (some? moved) (belief-change-region kb moved))
         tms    (reasoning/tms kb)]
     (when visibility-moved?
       (tax/note-supporter-visibility-change! (reasoning/taxonomy kb)))
     (tax/refresh-beliefs
      (reasoning/taxonomy kb)
      #(jtms/in? tms %)
      region))))

;; ---- the decontextualized predicate ---------------------------------------
;; `(decontextualized_predicate P)` lifts every `(P ...)` out of the context it was
;; stated in and into CxUniverse, which every context sees — so the fact
;; stops being a claim of one theory and becomes a claim of the KB.
;;
;; The lift is a *deduction*: the original stays where it was stated and a copy is
;; derived in CxUniverse, justified by the placement sentex AND the declaration —
;; so retracting or defeating either withdraws the copy.  CxCore documents the
;; mechanism in the `comment` on `decontextualized_predicate`; it is implemented in
;; code because a rule stating it would match every fact in the store.
;;
;; **CxUniverse, and not a target the declaration names.**  The definitional
;; checks — disjointness, functionality, arg — are context-scoped: they run where
;; the fact is stated, against what is visible from there.  Lifting into a context the
;; stating context cannot see moves the fact somewhere those checks never looked, so
;; two facts that are each admissible where they were stated can meet in the target as
;; a disjointness violation nothing reports.  CxUniverse is the one target every
;; context sees, so the copy is visible to the next assert and the ordinary check
;; catches the clash at its source.  `unchecked-target?` below covers the one case that
;; leaves: a context wired outside the spindle, which does not see CxUniverse
;; either.

;; Genuine in-file cycle, threaded through the table.  Three derivation sites live
;; above the table and must reach the choke point below it: the lift's copy, the
;; equality arms' migrated twin and the argument-constraint entailment are all derived
;; sentexes, so all three go through `derived-sentex-added`, and equality and the
;; entailment additionally check `wff-problems` / `wff-violation` — and each of those
;; walks the very table these arms sit in.  The cycle is data-shaped (the table's
;; values are the arm fns), so four declares close it.
(declare derived-sentex-added integrate-twin wff-problems wff-violation)

(def universal-context 'CxUniverse)

(defn- unchecked-target?
  "Could the definitional checks have missed what this lift is about to create?

  They run at `src-context` against what is visible from there, so they have already
  considered everything in CxUniverse whenever `src-context` sees it — which is
  every context in a spindle-shaped KB.  When it does not, the copy lands where the
  stating context cannot look, and the check has to be re-run on the copy itself."
  [kb src-context]
  (not (tax/sees? (reasoning/taxonomy kb) src-context universal-context)))

(defn- deduce-lift
  "Deduce `sentence` (stored at `src-handle` in `src-context`) into CxUniverse,
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
    ;; whose contexts all see CxUniverse (the ordinary spindle) pays one `sees?`
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
              (let [depth (inc (max (jtms/depth (reasoning/tms kb) src-handle) (jtms/depth (reasoning/tms kb) dh)))
                    antes [src-handle dh]]
                (jtms/ensure-node (reasoning/tms kb) h2 depth)
                (when-not (jtms/has-justification? (reasoning/tms kb) 'decontextualized_predicate antes h2)
                  (let [jid  (p/next-id (:records kb))
                        ;; The lift adds no defeasibility of its own, so it confers
                        ;; :monotonic and `conferred-class` caps it at the weaker of the
                        ;; source fact and the declaration.
                        just (jtms/->just jid 'decontextualized_predicate antes h2 {} :monotonic)]
                    (p/put-justification (:records kb) just)
                    (jtms/add-justification (reasoning/tms kb) just)))))
            {:new (if new? [h2] []) :violations []}))))))

(defn deduce-lifts
  "Deduce `sentence` (stored at `handle` in `context`) into CxUniverse if its
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
  (let [tax  (reasoning/taxonomy kb)
        pred (nm/functor sentence)]
    ;; the global property read on purpose: the lift decides the *storage* context,
    ;; and scoping it by what could see the declaration would be circular
    (when (and pred (tax/has-prop? tax :decontextualized pred))
      (deduce-lift kb sentence handle context
                   (tax/prop-supporters tax :decontextualized pred)))))

(defn- lift-existing
  "When a declaration arrives, retroactively deduce every `(pred ...)` sentex outside
  CxUniverse into it — so a declaration arriving after the facts reaches them,
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
  extending.  The copies are all in CxUniverse and so would be filtered out
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
;; `checks/constraint-entailments` reads what the visible `arg` / `genlArg`
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

  These are the four `place-conclusion` runs over a rule's conclusion, and they hold of
  any content the engine mints on its own behalf: a `(T x)` can clash with a disjoint
  membership, a `(genl X T)` edge can close a taxonomy cycle or a cycle through
  negation, and a type used at the wrong arity is not a type membership at all.  Three
  callers ask it — the argument-type entailment below, forward chaining, and abduction,
  which asks it *before* minting a hypothesis so that a sentence no assertion could
  legally make is never one the search assumes.

  A **value**, never a throw.  Two of its callers run after their triggering sentex is
  stored (that is what gives them a handle to be justified by) and inside a fixpoint,
  neither of which may abort halfway; the third would rather refuse a hypothesis than
  fail the query that wanted it.

  `pre-checked?` omits `constraint-violation`, the definitional-constraint arm, for a
  caller that has already run it against this exact content.  The assert path's
  first-level argument-type mints are the one such caller: `checks/entailment-check`
  runs `constraint-problem` (and `cascade-clash`, which reads the source's own
  membership) over every mint of the cascade **before** the trigger is stored, and
  refuses the trigger if any mint fails — so a first-level mint reaching the materializer
  has passed the constraint check already, and storing the trigger and the mints beside
  it only adds memberships, which cannot turn a passing `args`/`disjoint`/`arity` check
  into a failing one (each convicts on an absent type, never a present one).  Naming,
  well-formedness and edge stratification are **not** what `entailment-check` runs, so
  they are asked here whichever way `pre-checked?` reads.  Every other caller — forward
  chaining, the retroactive sweeps, and the cascade's own deeper levels, none of which
  `entailment-check` pre-validates — leaves it false and pays the full check."
  ([kb sentence context] (inadmissible kb sentence context false))
  ([kb sentence context pre-checked?]
   (or (when-let [ps (nm/blocking-problems (:naming kb) sentence context)]
         {:violation :naming
          :detail    {:message (str "naming invariant: " (str/join "; " ps))}})
       (when-not pre-checked? (checks/constraint-violation kb sentence context))
       (wff-violation kb sentence context)
       (checks/edge-stratification-violation kb sentence))))

(def ^:private empty-entailment-result {:new [] :violations []})

;; Genuine in-file cycle: a minted type draws its own entailments, so `entail-arg-type`
;; calls back into `deduce-arg-types`, which is the fold over it.  Reordering cannot
;; break it — the recursion is the cascade, and its termination argument is in
;; `entail-arg-type`'s docstring.
(declare deduce-arg-types)

(defn- entail-arg-type
  "Materialize one entailment: store `(:assert ent)` in `context` and justify it by
  `[src-handle, the declaration, the genl edges it descended through]`.
  `{:new [handle] :violations [v]}` — the handle when the sentex was newly created (the
  caller seeds chaining with it), the violation when it could not be admitted.

  **Every member of `:because`, not just the declaration.**  A declaration on a
  super-predicate reaches this fact through `genl` edges (`checks/edge-support`), and a
  type minted through one is entailed only while that edge holds — so the edges are
  antecedents like the declaration is, and retracting one takes the type back.

  Depth and strength are the lift's: one past the deepest of its supporters, and
  `:monotonic` conferred, because the entailment adds no defeasibility of its own —
  `conferred-class` caps it at the weaker of the fact and the declaration, so a default
  fact yields a default type.  The informant is the declaring predicate, so `why` names
  `arg` beside the two sentexes rather than an anonymous derivation.

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
  [kb ent src-handle context pre-checked?]
  (let [sentence (:assert ent)
        because  (vec (:because ent))]
    (if-let [v (inadmissible kb sentence context pre-checked?)]
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
            (let [antes  (into [src-handle] because)
                  depth  (inc (long (reduce max (map #(jtms/depth (reasoning/tms kb) %) antes))))
                  _      (jtms/ensure-node (reasoning/tms kb) h2 depth)
                  fresh? (not (jtms/has-justification? (reasoning/tms kb) (:kind ent) antes h2))
                  ;; `was-in?` records whether `h2` is already believed by another support,
                  ;; read before this justification is added.  It is an O(1) fixpoint read
                  ;; (`jtms/in?`), not an index read, and it gates the cascade below.
                  was-in? (jtms/in? (reasoning/tms kb) h2)]
              (when fresh?
                (let [jid  (p/next-id (:records kb))
                      just (jtms/->just jid (:kind ent) antes h2 {} :monotonic)]
                  (p/put-justification (:records kb) just)
                  (jtms/add-justification (reasoning/tms kb) just)))
              (merge-with into
                          {:new (if new? [h2] []) :violations []}
                          ;; A minted sentence materializes its own entailments when it first
                          ;; becomes believed, and re-materializing them adds nothing:
                          ;; `find-or-create-sentex` dedups the sentence and `has-justification?`
                          ;; refuses a duplicate justification.  The cascade therefore recurs only
                          ;; on a transition to believed — a newly created sentex, or a fresh
                          ;; justification that brings an out node in.  An already-believed dedup
                          ;; target (`fresh?` yet `was-in?`) takes the new support without
                          ;; re-querying its own declarations.  The condition is order-independent:
                          ;; whichever arrival first made the type believed ran the cascade once, so
                          ;; the KB holds the same sentexes and justifications either way.
                          (if (or new? (and fresh? (not was-in?)))
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
  only asserted content would.

  `pre-checked?` says these entailments already passed the definitional constraint
  check, so each mint's admissibility test skips it (`inadmissible`).  Only the assert
  path passes true, and only for its first level: `checks/entailment-check` validated
  those before the trigger was stored.  The default is false, which every other caller
  takes and which the cascade the materializer walks itself takes — a mint drawn one
  level down was not on `entailment-check`'s pre-store list, so it is checked in full."
  ([kb entailments handle context] (deduce-arg-types kb entailments handle context false))
  ([kb entailments handle context pre-checked?]
   (reduce (fn [acc e] (merge-with into acc (entail-arg-type kb e handle context pre-checked?)))
           empty-entailment-result
           entailments)))

(defn- retroactive-mints
  "The entailments a newly stored declaration `dh` draws over one already-stored sentex
  `sx`, materialized in `sx`'s **own** context.

  The stored sentex is put back through `checks/constraint-entailments` and the answers
  narrowed to this declaration, rather than the conditions being re-decided here: the
  two directions must agree about what a declaration entails, and the only way to be
  sure of that is for them to ask the same function.  What that buys is the whole
  local-vs-inherited rule for free — a declaration written in an ancestor context does
  not draw an entailment in a descendant when the facts arrive first either.

  Narrowed on the **first** member of `:because`, which is the declaration; the rest are
  the `genl` edges a declaration on a super-predicate descended through, and they vary
  with the fact rather than with the declaration this call is about.

  A genuine negation is not argument-checked, so it entails nothing; nor does a rule,
  whose stored sentence is an implication."
  [kb sx dh]
  (if-not (and (nil? (:antecedent sx)) (not (sx/negative? sx)))
    empty-entailment-result
    (let [sctx (:context sx)]
      (deduce-arg-types kb
                        (filter #(= dh (first (:because %)))
                                (checks/constraint-entailments kb (:sentence sx) sctx))
                        (:id sx) sctx))))

(def ^:private entailing-declarations
  "The argument-constraint declarations that entail, with the arity each is written at —
  the roster `entail-existing` dispatches on, so a fourth kind is one line rather than a
  widened `and`."
  '{arg 3, genlArg 3, interArg 5})

(defn- subtree-sentexes
  "Every **stored** sentex whose functor is `pred` or any spec of it — the extent a
  declaration or a mark written of `pred` binds, since a `genl` edge between predicates
  says the sub's tuples *are* the super's.  The four retroactive arms read it: a
  declaration meeting the facts, a mark meeting them, and each of those met by an edge
  instead.

  Stored rather than believed, for `lift-existing`'s reason, which every caller repeats:
  content derived off a defeated fact is defeated with it, where skipping the fact would
  leave the derivation missing when it revives — belief depending on the order the defeat
  and the declaration arrived in.

  **Filtered by index cardinality before anything is read.**  `genl` is the commonest
  edge in an ontology, so a spec subtree is routinely most of the vocabulary while only a
  little of it holds facts — and the walk without the filter costs a posting-list read
  and a record fetch per handle for every predicate in the subtree, whether or not it has
  one.  A predicate with nothing stored has nothing to constrain, and asking is one
  count.  What is left to pay per edge is that count per spec, against the whole
  subtree's extent without it.

  A vector, snapshotted before the caller's first write: a mint or a merge posts to the
  roots this walk reads, and no index backend promises whether a posting read is a
  snapshot or a live view."
  [kb pred]
  (let [idx  (:index kb)
        recs (:records kb)]
    (into [] (comp (filter #(pos? (reads/stored-count-with-functor idx %)))
                   (mapcat #(reads/as-stored-with-functor idx %))
                   (distinct)
                   (keep #(p/get-sentex recs %)))
          (tax/specs-global (reasoning/taxonomy kb) pred))))

(defn- any-stored?
  "Is any sentex stored under any of `functors`?  One index cardinality read each, which
  is what lets an arm gated on it cost O(1) for a KB using none of the feature."
  [kb functors]
  (let [idx (:index kb)]
    (boolean (some #(pos? (reads/stored-count-with-functor idx %)) functors))))

(defn entail-existing
  "When an `(arg P n T)` / `(genlArg P n T)` / `(interArg P n T m U)` declaration
  arrives, draw what it now says about the `(P …)` sentexes **already stored** — so a
  declaration arriving after the facts reaches them exactly as one arriving before
  reaches the facts that follow.  Same `{:new :violations}` result, so the types it mints
  are chaining seeds like any other new content.  nil when `sentence` is not an argument
  constraint.

  Two of `interArg`'s three arrival orders are covered here and at the entry point; the third
  — the *trigger's* type arriving after both the fact and the declaration — is the
  family's documented open-world non-reach (docs/taxonomy.md, \"What each constraint does
  in each arrival order\"), and `arg` has it too from the other side.

  Sweeps what is **stored**, not what is believed, for `lift-existing`'s reason: a type
  minted off a defeated fact is justified by that fact and so is defeated too — the
  JTMS already says what a disbelieved antecedent means — whereas skipping it would
  leave the type missing when the fact revives, which is belief depending on the order
  the defeat and the declaration arrived in.

  The extent is read off the **functor roots of `P`'s whole spec subtree**, which is the
  precise answer to \"every stored tuple this declaration constrains\": a declaration on
  `P` binds every predicate beneath it (`res/constraining-predicates`), so an extent read
  off `P`'s own root alone would mint over `(parentOf …)` and not over `(fatherOf …)` —
  a type the same three sentences produce in one arrival order and not the other.
  `subtree-sentexes` reads it, and snapshots it before the first mint."
  [kb sentence dh]
  (when checks/*assertive-arg-types?*
    (let [[f pred] sentence]
      (when (and (= (entailing-declarations f) (nm/arity sentence)) (symbol? pred))
        (reduce (fn [acc sx] (merge-with into acc (retroactive-mints kb sx dh)))
                empty-entailment-result
                (subtree-sentexes kb pred))))))

(defn- super-reaches-declaration?
  "Does `super`, or a genl-ancestor of it, carry an entailing argument declaration?
  `entail-under-edge` reads this before it walks a subtree.

  A `(genl sub super)` edge draws a new type over `sub`'s facts only through a
  declaration the edge is itself a support of: `checks/edge-support` cites the arriving
  edge in the mint's `:because`, so a route that does not run through the edge
  deduplicates against one that already held and adds nothing (`has-justification?`).  A
  route that does run through it reaches its declaring predicate `D` as
  `fact-functor →* sub → super →* D`, so `D` is a genl-ancestor of `super`.  When no
  ancestor of `super` declares, the edge mints and justifies nothing, and the subtree
  read is skipped.

  **`genls-global`, not the scoped `genls`** (E17): `entail-under-edge` sweeps stored
  sentexes across every context the subtree spans, so there is no one vantage to scope
  to, and the gate must over-approximate in the direction the answer is — a declaration
  this edge cannot see from one context still mints a required justification in another
  that can, so a scoped gate that returned false there would drop it, where a spare true
  only reads a subtree that yields nothing.  Read through the same global roster
  (`tax/arg-declaration-props`) `res/constraining-predicates` filters against, so the
  gate and the reader it guards cannot disagree about which predicates declare."
  [kb super]
  (and (symbol? super)
       (let [tax       (reasoning/taxonomy kb)
             declaring (reduce (fn [acc k]
                                 (into acc (tax/props tax (tax/arg-declaration-props k))))
                               #{}
                               (keys entailing-declarations))]
         (boolean (some declaring (tax/genls-global tax super))))))

(defn entail-under-edge
  "When a `(genl sub super)` edge arrives, draw what the declarations on `super` now say
  about the `(sub …)` sentexes **already stored** — the third arrival order of the same
  three ingredients, and there for the reason `subsumption-seeds` beside it is.

  A constraint descends the predicate hierarchy, so the fact, the declaration and the
  **edge** are all ingredients of one entailment.  `deduce-arg-types` covers the fact
  arriving last and `entail-existing` the declaration arriving last; without this, the
  edge arriving last mints nothing and the same three sentences leave the KB holding a
  type in two orders out of three.  nil when `sentence` is not a `genl` edge.

  The whole **spec subtree** of `sub`, because subsumption is transitive: an edge at the
  top of a predicate hierarchy brings every predicate below it under the declarations
  above it.  Each stored sentex is put back through `checks/constraint-entailments` in
  its own context — the same function the other two directions ask, so the three cannot
  disagree — and the mints deduplicate on content, so a fact whose type was already
  entailed by a route that survives contributes a justification and no second record.

  **Three gates in front of the subtree, because this arm fires on a `genl` edge** — the
  commonest thing an ontology says, where the other two fire on a declaration.  Off
  unless `*assertive-arg-types?*`, since with the entailment off there is nothing to mint
  and the edge's other consequences are `subsumption-seeds`'; off unless the KB stores an
  argument constraint at all (`any-stored?`, one index count per kind); and off unless a
  genl-ancestor of `super` carries one (`super-reaches-declaration?`).  The first two
  keep an edge under a predicate nobody constrained from reading a subtree's extent to
  discover there was nothing to draw; the third keeps an edge whose `sub` is constrained
  but whose `super` reaches no declaration from reading it, since every mint this arm
  draws cites the arriving edge and so reaches its declaring predicate through `super`.
  The extent itself is `subtree-sentexes`, filtered by cardinality for the same reason
  one step further in."
  [kb sentence]
  (when (and checks/*assertive-arg-types?*
             (= 'genl (nm/functor sentence))
             (any-stored? kb (keys entailing-declarations))
             (super-reaches-declaration? kb (nth sentence 2)))
    (let [[_ sub] sentence]
      (when (symbol? sub)
        (reduce (fn [acc sx]
                  (if-not (and (nil? (:antecedent sx)) (not (sx/negative? sx)))
                    acc
                    (let [sctx (:context sx)]
                      (merge-with into acc
                                  (deduce-arg-types
                                   kb (checks/constraint-entailments kb (:sentence sx) sctx)
                                   (:id sx) sctx)))))
                empty-entailment-result
                (subtree-sentexes kb sub))))))

;; ---- definitional collection relations, expanded into forward rules -------
;; `(defnNecessary Coll C)` / `(defnSufficient Coll C)` / `(defnIff Coll C)` tie a
;; collection's membership to a condition on the member `?x` (docs/defns.md).  The
;; `defn*` fact is stored like any other; what it *means* is materialized here the way
;; `deduce-lift` materializes a decontextualized copy — as derived content justified by
;; the fact, so it inherits belief, retraction and placement for free.  The derived
;; content is a **rule** rather than a fact, so this is the mint path `chain/mint-rule`
;; takes for a generator, minus the join bindings: index it, node it, justify it once.
;;
;; Open-world only.  `defnSufficient` concludes membership from the condition and
;; `defnNecessary` the condition from membership; neither expands the collection's
;; *complement* — nothing concludes a non-member from the condition's failure, which is
;; closed-world membership completion and stated as an absence in docs/defns.md.

(defn- materialize-defn-rule
  "Store one companion rule `r` (polycanonicalized into one rule per conjunct of a
  conjunctive necessary consequent, and per alternative of a disjunctive condition, by
  `rules/expand-rule`) as a derived rule sentex in `context`,
  justified by `[defn-handle]` under `informant`.

  The mint a generator makes, minus the bindings: index the rule
  (`index-rule-sentex`), give it a node one past the `defn*` fact's, and add the
  justification once (`has-justification?` keeps a re-assert of the same `defn*` from
  duplicating it).  `{:new [handles] :violations [v]}` — the new handles the caller
  seeds chaining with, and a rule that could not be admitted, reported rather than
  thrown for the derivation path's reason."
  [kb r defn-handle context informant]
  (let [minted (rules/expand-rule r)]
    (if-let [v (some #(checks/rule-violation kb % context) minted)]
      {:new [] :violations [(assoc v :sentence r :context context)]}
      (reduce
       (fn [acc one]
         (let [[h s new?] (kb/find-or-create-sentex kb one context)]
           (when new? (index-rule-sentex kb h s))
           (let [depth (inc (long (jtms/depth (reasoning/tms kb) defn-handle)))]
             (jtms/ensure-node (reasoning/tms kb) h depth)
             (when-not (jtms/has-justification? (reasoning/tms kb) informant [defn-handle] h)
               (let [jid  (p/next-id (:records kb))
                     ;; :monotonic conferred, capped by the `defn*` fact's own class in
                     ;; `conferred-class` — the rule adds no defeasibility of its own, so
                     ;; a default `defn*` makes a default rule, exactly as the lift does
                     just (jtms/->just jid informant [defn-handle] h {} :monotonic)]
                 (p/put-justification (:records kb) just)
                 (jtms/add-justification (reasoning/tms kb) just))))
           (if new? (update acc :new conj h) acc)))
       {:new [] :violations []}
       minted))))

(defn materialize-defn-rules
  "Materialize the forward rule(s) a `defn*` fact stored at `defn-handle` in `context`
  expands into (`sx/defn-companion-rules`), each a derived rule sentex justified by the
  `defn*` fact alone.  `{:new [handles] :violations [v]}` — the new rule handles the
  caller seeds chaining with (so a rule fires over the facts already stored), and any
  rule that could not be admitted.

  Called from `assert-one` once the `defn*` fact has a handle to be justified by.  A
  non-`defn*` sentence returns the empty result, so the caller pays one `defn-sentence?`
  read and stops — the gate that keeps every ordinary assert free of it."
  [kb sentence defn-handle context]
  (if-not (sx/defn-sentence? sentence)
    empty-entailment-result
    (let [informant (nm/functor sentence)]
      (reduce (fn [acc r]
                (merge-with into acc
                            (materialize-defn-rule kb r defn-handle context informant)))
              {:new [] :violations []}
              (sx/defn-companion-rules sentence)))))

(defn- negative-subsumption-seeds
  "The half of `subsumption-seeds` that a **negated** antecedent is owed, read up
  `super`'s `genl` closure where the positive half reads down `sub`'s `spec` one.

  Subsumption is contravariant under a negation (docs/inference.md, \"Under a negation
  the fan reverses\"), so an arriving `(genl dog animal)` does not connect `dog`'s facts
  to an `(animal ?x)` antecedent here — it connects `animal`'s *negative* facts to a
  `(not (dog ?x))` one.  `(not (animal A))` stored, then the edge, and a rule negated on
  `dog` should fire; without this seed the same three sentences derive a conclusion in
  one order and not the other, which is what the positive half exists to prevent.

  **Gated on some rule reading a negated antecedent under `sub`**, off the live
  `:rule-antecedents` roster — the same roster `rules/trigger-keys` reads, and for the
  same reason.  Sound in both directions this is reached from: for an arriving edge
  nothing can newly match except through it, and for a departing one an edge no negated
  antecedent could ever have climbed licensed nothing to revive.  A KB whose rules read
  no negation, which is nearly every KB, pays one pass over the roster's keys.

  Negative sentexes only, decided by the stored sentence's head `not`: a *positive* fact on a
  genl of `super` newly matches nothing, since a positive antecedent fans downward and
  the edge moved nothing above `super`."
  [kb sub super]
  (let [specs (tax/specs-global (reasoning/taxonomy kb) sub)]
    (when (some (fn [k] (and (vector? k) (contains? specs (second k))))
                (keys @(reasoning/rule-antecedents kb)))
      (let [idx  (:index kb)
            recs (:records kb)
            tms  (reasoning/tms kb)]
        (into [] (comp (mapcat #(reads/as-stored-with-functor idx %))
                       (distinct)
                       (filter #(jtms/in? tms %))
                       (filter (fn [h]
                                 (when-let [s (p/get-sentex recs h)]
                                   (sx/negative? s)))))
              (tax/genls-global (reasoning/taxonomy kb) super))))))

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

  A **negated** antecedent is answered contravariantly, so the facts an edge newly
  offers *it* sit on the other side of the edge entirely: `negative-subsumption-seeds`
  above reads them up `super`'s genl closure.

  The *removal* side is `resubsumption-seeds` below: a firing names the `genl` edges it
  subsumed through, so dropping one withdraws what it licensed — and the facts have to
  go back on the agenda when the reachability outlives the supporter that left."
  [kb sentence]
  (when (= 'genl (nm/functor sentence))
    (let [[_ sub super] sentence
          idx (:index kb)
          tms (reasoning/tms kb)]
      (when (symbol? sub)
        (into (into [] (comp (mapcat #(reads/as-stored-with-functor idx %))
                             (distinct)
                             (filter #(jtms/in? tms %)))
                    (tax/specs-global (reasoning/taxonomy kb) sub))
              (when (symbol? super) (negative-subsumption-seeds kb sub super)))))))

(defn- transitive-left-ends
  "`a`, and every term that already reached it through believed stored `pred` links — the
  terms whose reach an arriving `(pred a b)` just extended.

  A stored walk rather than `provers/preds-of`, and context-free on purpose: these are
  CANDIDATES for the agenda, and the join that fires re-decides context, belief and
  placement for every one of them.  Bounded by the believed extent of `pred` reachable
  backwards from `a`, which on the ordinary load order — a chain arriving in its own
  direction — is the chain behind the new link and nothing else."
  [kb pred a]
  (let [idx  (:index kb)
        recs (:records kb)
        tms  (reasoning/tms kb)
        left (fn [h]
               (when-let [sx (p/get-sentex recs h)]
                 (let [sent (:sentence sx)]
                   (when (and (not (sx/negative? sx))
                              (nil? (:antecedent sx))
                              (= 3 (count sent))
                              (= pred (nm/functor sent)))
                     (second sent)))))]
    (loop [seen #{a} frontier [a]]
      (if-let [t (peek frontier)]
        (let [ups (into #{}
                        (comp (filter #(jtms/in? tms %))
                              (keep left)
                              (remove seen))
                        (reads/as-stored-with-arg idx 2 t))]
          (recur (into seen ups) (into (pop frontier) ups)))
        seen))))

(defn- transitive-partner-functors
  "The functors some rule is indistinguishable from an antecedent BESIDE a `pred` one — the triggers a
  grown `pred` closure could newly join to.  Empty when no rule takes a `pred`
  antecedent at all, which is the gate that keeps an ordinary assert free."
  [kb pred]
  (let [idx  (:index kb)
        recs (:records kb)]
    (into #{}
          (comp (keep #(p/get-sentex recs %))
                (mapcat :antecedent)
                (keep nm/functor)
                (remove #{pred}))
          (reads/as-stored-rules-by-antecedent idx pred))))

(defn- believed-facts-with-functors
  "The believed stored FACT handles among `handles` whose functor is one of `functors`."
  [kb functors handles]
  (let [recs (:records kb)
        tms  (reasoning/tms kb)]
    (into []
          (comp (distinct)
                (filter #(jtms/in? tms %))
                (filter (fn [h]
                          (when-let [sx (p/get-sentex recs h)]
                            (and (nil? (:antecedent sx))
                                 (contains? functors (nm/functor (:sentence sx))))))))
          handles)))

(defn transitive-seeds
  "The stored facts a declared-transitive predicate's closure makes newly matchable, as
  chaining seeds — the `TransitivePredicateProver`'s twin of `subsumption-seeds` above,
  and there for exactly the same reason.

  **A declared-transitive predicate's closure is answered, never stored.**  `(causes E0
  E2)` is provable the moment both links are in and is never a record — so it is never a
  datum, never on the agenda, and never a trigger.  A rule joined to that predicate,
  `[(does ?a ?act) (causes ?act ?e)]`, can reach a closure pair only from its OTHER
  antecedent's trigger; and when the closure grows, nothing puts that trigger back.
  Assert the `does` before the second link and the firing has already run against a
  shorter closure; assert it after and the join reaches the whole of it.  Same four
  sentences, two answer sets, which is the one thing belief may not depend on
  (docs/nmtms.md).  `subsumption-seeds` states the principle for the taxonomy: firing the
  rules keyed on the arriving predicate is not the same thing as re-firing the rules the
  arrival just connected.  This is that, one closure over.

  **Two arrival orders, because the closure has two ingredients** — the links and the
  declaration — and either can come last.  `deduce-arg-types` / `entail-existing` /
  `entail-under-edge` are the same three-cornered shape for an argument type:

  - a **link** `(pred a b)`, with `pred` already transitive: the reach that grew is `a`'s
    and that of everything behind it (`transitive-left-ends`), so the seeds are the
    believed facts mentioning one of those.
  - the **declaration** `(transitive pred)`, over links already stored: every pair of the
    closure appears at once, so every believed fact on a partner functor goes back.  This
    is the arm a `(transitive …)` asserted after its links needs, and without it a KB that
    declares its properties at the end of a file answers differently from one that
    declares them at the start.

  **The seeds are the partner triggers, not the links.**  Re-seeding the `pred` facts
  themselves buys nothing: their own trigger position joins the other antecedent at the
  term the link already names, which is the pair the run made anyway.

  **The gates are what keep an ordinary assert free.**  Both arms are off unless some rule
  takes a `pred` antecedent — with no such rule there is no join to re-drive — and the
  link arm reads the inverted index's posting per left end rather than any functor extent,
  so a KB whose transitive facts feed no rule pays two lookups and reads nothing.

  The **removal** side needs no twin: a retracted link withdraws the closure pairs that
  rested on it through the justifications the firings recorded, which is the TMS's
  ordinary business and not a reachability question."
  [kb sentence]
  (let [functor (nm/functor sentence)]
    (cond
      ;; the declaration arriving last, over links already stored
      (and (= 'transitive functor) (sequential? sentence) (= 2 (count sentence)))
      (let [pred (second sentence)]
        (when (and (symbol? pred) (not (contains? tax/closure-relations pred)))
          (let [partners (transitive-partner-functors kb pred)]
            (when (seq partners)
              (believed-facts-with-functors
               kb partners
               (mapcat #(reads/as-stored-with-functor (:index kb) %) partners))))))

      ;; a link arriving under a declaration already in force
      (and (symbol? functor)
           (sequential? sentence)
           (= 3 (count sentence))
           (not (contains? tax/closure-relations functor))
           (tax/has-prop? (reasoning/taxonomy kb) :transitive functor))
      (let [partners (transitive-partner-functors kb functor)]
        (when (seq partners)
          (believed-facts-with-functors
           kb partners
           (mapcat #(reads/as-stored-with-term (:index kb) %)
                   (transitive-left-ends kb functor (second sentence)))))))))

(defn transitive-rule-seeds
  "The stored facts a newly forward-capable RULE needs back on the agenda when one of its
  antecedents reads a declared-transitive predicate — the third arrival order of
  `transitive-seeds`' three ingredients, and there for the reason the other two are.

  A rule seeded on its own handle is joined over the stored facts, and that join reaches
  the closure only from whichever side it leads: led from the transitive antecedent it
  enumerates the STORED links and nothing else, since the closure is answered rather than
  stored and an open goal on it yields no record to lead from.  So a rule arriving after
  its facts derives the direct pairs and stops, where the same rule arriving before them
  derives the closure — the same sentences, two answer sets, decided by which came last.

  Seeding the partner facts fixes it the way it fixes the other two arms: each becomes a
  trigger, and a trigger binds the shared variable before the transitive antecedent is
  asked, which is the direction that reaches the closure.

  Off unless an antecedent is actually declared transitive, so an ordinary rule assert
  pays one property lookup per antecedent and reads nothing."
  [kb rule-sentex]
  (let [antes (:antecedent rule-sentex)]
    (when (seq antes)
      (let [functors (into #{} (keep nm/functor) antes)
            trans    (into #{} (filter #(and (symbol? %)
                                             (not (contains? tax/closure-relations %))
                                             (tax/has-prop? (reasoning/taxonomy kb) :transitive %)))
                           functors)]
        (when (seq trans)
          (let [partners (into #{} (remove trans) functors)]
            (when (seq partners)
              (believed-facts-with-functors
               kb partners
               (mapcat #(reads/as-stored-with-functor (:index kb) %) partners)))))))))

(defn- roster-antecedent-functors
  "The index functors the facts matchable by a `:rule-antecedents` roster key root under.

  A positive key IS a functor symbol; a **negated** key `[:not g]` roots its facts under
  `g` — a `(not (g A))` record indexes by its positive body's functor (`impl.kv`) — so a
  lookup goes there, not to the `[:not g]` key nothing is ever written to.  Without that
  a genlCx edge arriving after a negative fact never re-joins a rule with a negated
  antecedent, and the same three sentences derive a conclusion in one order and not the
  other — the arrival-order dependence `subsumption-seeds` has a negated half to prevent.

  **And one functor per key is not enough, because matching fans.**  An antecedent
  `(dog ?x)` is answered by a stored `(terrier Rex)` down `dog`'s `genl` spec closure,
  and a negation reverses the fan (docs/inference.md, \"Under a negation the fan
  reverses\"), so `(not (dog ?x))` is answered by a stored `(not (animal A))` up `dog`'s
  genl closure instead.  Reading the key's own functor alone finds the facts a rule
  *names* and not the facts it *matches*, so an edge re-joins the rule over half of what
  it newly sees, and a type hierarchy standing between the rule and the fact is enough
  to leave the conclusion in the orders that wired the contexts first and nowhere else.
  `subsumption-seeds` reads these same two closures, for the same reason from the other
  side of the pair.

  The closures are **global**, and that is `subsumption-seeds`' argument too: these are
  candidates for a re-join and the firing's placement narrows them afterwards, so fanning
  from one context would drop a fact that a context seeing both would match."
  [tx k]
  (if (vector? k)
    (tax/genls-global tx (second k))
    (tax/specs-global tx k)))

(defn visibility-seeds
  "The stored facts a new `(genlCx sub super)` edge newly makes matchable, as
  chaining seeds — the **context** twin of `subsumption-seeds`, and there for exactly
  the same reason.

  Matching fans an antecedent up the visibility ancestor set, so an edge arriving after both the
  rule and the facts changes which facts the rule can see: `(cFactP CA)` in
  `CxMid`, a rule in `CxLow`, then `(genlCx CxLow CxMid)`, and
  the rule should fire.  The semi-naive agenda never sees it — the arriving datum is the
  *edge*, and firing the rules keyed on `genlCx` is not the same thing as re-joining
  the rules the edge just gave a wider view.  Without this the same four sentences derive
  a conclusion in the orders that put the edge first and nothing in the others, which is
  the one thing belief may not depend on (docs/nmtms.md).

  **Both ancestor sets, because an edge pairs rules and facts in two directions.**  It is not
  only that a rule below can now see facts above: a rule stated *above* applies in every
  context that sees it, so the edge equally hands the general rule the specialized
  context's own facts, and places its conclusion there.  Seeding is by fact, so the seeds
  are the believed sentexes of `super`'s **up**-ancestor set — seeing `super` means seeing
  everything `super` sees — together with those of `sub`'s **down**-ancestor set, the contexts a
  rule above is now inherited into.  Taking one and not the other fixes half the orders
  and leaves the rest, which is worse than either: the structure that still fails is the
  narrower one, and so the easier to mistake for correct.

  **Enumerated from the rules, not from the ancestor set**, and the difference is asymptotic
  rather than a constant.  Walking the ancestor set and keeping the facts some rule could match
  costs one record fetch per sentex *in the ancestor set* — so wiring N contexts under a
  `CxUniverse` holding K facts is O(N·K) where the KB without this is O(N+K), and
  building a spindle D deep is O(D²) because each edge's ancestor set is the whole chain
  above it.  Measured: 3.9x on the first shape, 5x and climbing with depth on the
  second, and 1.8x on the starter load, which does wire contexts after filling them.

  So it goes the other way.  `:rule-antecedents` is the live roster of predicates some
  rule takes as an antecedent, kept O(1) at the rule index/unindex choke points beside
  `:opposed`; this walks *those* predicates' extents — each fanned by `genl` the way the
  matcher fans it, `roster-antecedent-functors` — and keeps the facts whose context
  is in the ancestor set.  Cost is then proportional to the rule-relevant facts and independent
  of how much ontology the ancestor set holds — a KB with no rules pays one map read, a KB whose
  rule antecedents name no type with subtypes pays one extent read each (a closure over a
  predicate outside the hierarchy is the predicate), and the upper ontology sitting in
  `CxUniverse` is not walked because almost none of it is a rule antecedent.  The ancestor set is
  a set membership per candidate, so it adds no work to ask about both ancestor sets.

  **And each half is gated on the other holding a rule**, which is what makes the
  ordinary case free rather than merely cheap.  Seeding `super`'s facts is worth nothing
  unless some rule sits in `sub`'s descendant set to newly see them, and seeding `sub`'s facts
  nothing unless a rule sits in `super`'s ancestor set to be inherited into it.  Wiring an
  empty context under a full one — the commonest edge there is — holds no rule on the
  new side, so it seeds nothing at all, where without the gate it re-seeds the whole
  ontology above and re-joins rules that already fired on every fact of it.  That is the
  difference between 3.9x on the shape and 1.0x, and it is not the enumeration but the
  chaining the seeds provoke.  `:rule-contexts` answers it as a map read per context in
  the ancestor set, and contexts are few.

  **Withdrawal needs no twin of this**, because dropping an edge *narrows* what a rule
  sees and a firing names the `genlCx` edges its placement saw its ingredients over
  (`chain/visibility-support`) — so the ordinary dependency-directed sweep already
  withdraws one whose antecedent stopped being visible.  What the removal side does owe
  is the other half, *revival*, and this is called for that too: `resubsumption-seeds`
  puts these same seeds back when a sighting outlives the edge that witnessed it.

  **And on that path the gate does not apply**, which is the two-arity form.  The gate is
  sound for an arriving edge because an arriving edge is the *only* new reachability:
  nothing can newly match except through it, so an ancestor set holding no rule newly matches
  nothing.  A departing edge says nothing of the kind.  The firing being revived was
  placed where it could see the rule and the facts by whatever route it liked, and the
  route that went need not be the route either of them lay on — a placement seeing the
  rule down one branch and the facts down another loses an edge whose two ancestor sets hold
  neither.  Asking the gate there answers a question about the departed edge's own line
  and calls it a question about the firing, which is `resubsumption-seeds`'s stated
  reason for re-joining unconditionally: a missed revival is exactly the arrival-order
  dependence the witnesses exist to remove, and the KB that never held the edge derives
  the conclusion.  The cost is bounded by the same thing that bounds the pass around it
  — it runs only where a sweep already took a record the caller did not ask for."
  ([kb sentence] (visibility-seeds kb sentence true))
  ([kb sentence gated?]
   (when (= 'genlCx (nm/functor sentence))
     (let [[_ sub super] sentence
           preds (keys @(reasoning/rule-antecedents kb))]
       (when (seq preds)
         (let [idx  (:index kb)
               recs (:records kb)
               tms  (reasoning/tms kb)
               tx   (reasoning/taxonomy kb)
               ruled? @(reasoning/rule-contexts kb)
               up    (when (symbol? super) (tax/context-up tx super))
               down  (when (symbol? sub)   (tax/context-down tx sub))
               ancestor-set (if gated?
                              (cond-> #{}
                                (some ruled? down) (into up)
                                (some ruled? up)   (into down))
                              (into (set up) down))]
           (when (seq ancestor-set)
             (into [] (comp (mapcat #(roster-antecedent-functors tx %))
                            (distinct)
                            (mapcat #(reads/as-stored-with-functor idx %))
                            (distinct)
                            (filter #(jtms/in? tms %))
                            (filter (fn [h]
                                      (when-let [s (p/get-sentex recs h)]
                                        (contains? ancestor-set (:context s))))))
                   preds))))))))

(def ^:private edge-functors
  "The two relations a firing can name a witness for, and so the two whose removal owes
  a re-chain.  The same set the taxonomy names `closure-relations`, aliased for the
  local reading the way `provers/transitive-predicates` and `inherit/virtual-relations`
  are: a firing rests on a *reachability* rather than on a stored link precisely because
  these two answer from a cached closure, so the two readings are one fact."
  tax/closure-relations)

(defn resubsumption-seeds
  "The chaining seeds a teardown owes, given the `removed` sentexes its sweep collected
  — `subsumption-seeds` and `visibility-seeds` in the retraction direction.

  A firing names **one** witness for each reachability it rests on: the `genl` path a
  subsumed match climbed, and the `genlCx` path its placement saw each ingredient
  context over (`taxonomy/reach-support`, `chain/visibility-support`).  So removing an
  edge on one of those paths invalidates the justification and the dependency-directed
  sweep collects the conclusion.  That is the point.  But a reachability can outlive one
  of its supporters — the same edge asserted from a second context, or a second path
  around the one that went — and then the conclusion is still licensed and must come
  back.  So the facts the departed edge could have carried go back on the agenda and the
  rules fire again over them: a `genl` edge's spec subtree, a `genlCx` edge's two ancestor sets.

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
  exactly the ones that need re-joining.  The context ancestor sets are read at the same moment
  and are not sensitive to it, since removing `(genlCx sub super)` changes neither who
  reaches `sub` nor what `super` reaches; reading them early is the same answer, from
  the one place that has the records in hand.

  And it is gated on the sweep having taken **something besides the records asked
  for**: a justification naming the departing edge is deleted with it, so a conclusion
  that survived kept another one and needs no re-derivation, and a conclusion that did
  not is in `removed`.  So retracting an edge that licensed nothing — the common case —
  costs one functor read per removed record and no chaining at all.

  **The re-join is unconditional where it happens, and asking it any other way would be
  a bug.**  Whether the reachability really survived is `place-conseq`'s question, decided
  from the taxonomy as it now stands; a gate here guessing the answer from the departing
  edge alone would be wrong wherever the surviving route runs somewhere other than
  between that edge's own endpoints, and a missed revival is the arrival-order dependence
  the witnesses exist to remove.  That is why `visibility-seeds` is called in its
  **ungated** arity: its own gate is the one this paragraph forbids, sound for an
  arriving edge and not for a departing one.  So most of what this seeds finds nothing to place, and
  that pass is deliberately silent: `chain/*report-no-placement?*` is bound off around
  it, since a firing the caller's own retraction just killed is the retraction restated
  rather than a diagnosis of the KB."
  [kb removed]
  (when (next removed)
    (into []
          (comp (map :sentence)
                (filter #(contains? edge-functors (nm/functor %)))
                (distinct)
                (mapcat (fn [s] (into (vec (subsumption-seeds kb s))
                                      (visibility-seeds kb s false))))
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
  [kb sentence context]
  (when-let [ps (seq (wff-problems (reasoning/taxonomy kb) sentence context))]
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
    (let [depth (inc (max (jtms/depth (reasoning/tms kb) orig-handle) (jtms/depth (reasoning/tms kb) eh)))
          antes [orig-handle eh]]
      (jtms/ensure-node (reasoning/tms kb) twin-handle depth)
      (when-not (jtms/has-justification? (reasoning/tms kb) 'rewriteOf antes twin-handle)
        (let [jid  (p/next-id (:records kb))
              just (jtms/->just jid 'rewriteOf antes twin-handle {} :monotonic)]
          (p/put-justification (:records kb) just)
          (jtms/add-justification (reasoning/tms kb) just))))))

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

(defn- retarget-handle
  "Replace every `(sentexHandle orig)` in `form` with `(sentexHandle twin)`, recursively —
  the handle-swap that re-points a meta from a superseded sentex onto its twin.  Any other
  handle and every non-handle term is untouched."
  [form orig twin]
  (cond
    (and (sx/sentex-handle? form) (= orig (sx/handle-id form))) (sx/sentex-handle twin)
    (sequential? form) (apply list (map #(retarget-handle % orig twin) form))
    :else form))

(defn- meta-target
  "The handle a **handle-naming meta-sentex** `s` names, or nil for any other sentence.
  Three kinds name a sentex by handle and so must follow it through a merge: an
  `exceptWhen` names the rule it guards, an `except` names the sentex it hides, and any
  `target_following_predicate` meta (koinii's reply acts) names the claim it hangs on.  A
  target-following meta carries exactly one `(sentexHandle H)` argument, and that is its
  target."
  [kb s]
  (or (sx/exceptWhen-rule-handle s)
      (kb/except-target s)
      (when (and (sequential? s) (symbol? (first s))
                 (tax/has-prop? (reasoning/taxonomy kb) :target-following (first s)))
        (some #(when (sx/sentex-handle? %) (sx/handle-id %)) s))))

(defn- rebuild-handle-meta
  "The twin meta naming `twin` where `s` named `orig`.  An `exceptWhen` re-points and
  realigns its query — the terms to `reader`'s representatives, the variables to the twin's
  canonical numbering — and rebuilds through `exceptWhen-meta` so the conjuncts sort
  canonically.  Every other handle-naming meta (`except`, a target-following reply) is
  ground: rewrite its terms to `reader`'s representatives (a no-op when it mentions no
  merged term) and retarget the handle."
  [kb s orig twin realign reader]
  (if (sx/exceptWhen-meta? s)
    (sx/exceptWhen-meta
     (mapv #(sx/canon (rename-vars realign (kb/rewrite-term kb % reader)))
           (sx/exception-query-conjuncts s))
     twin)
    (sx/canon (retarget-handle (kb/rewrite-term kb s reader) orig twin))))

(defn migrate-handle-metas
  "Carry every believed handle-naming meta of sentex `orig` onto its migrated twin `twin`.

  A meta and the sentex it names are **separate** sentexes linked by the handle —
  `(exceptWhen … (sentexHandle H))`, `(except (sentexHandle H))`, a target-following
  `(P … (sentexHandle H) …)` — so migrating the named sentex to a new handle would strand
  its metas on the superseded original: an `exceptWhen` twin would fire *unguarded*, an
  `except`ed twin would become visible, a reply would name a claim no longer believed.  So
  each such meta gets a twin naming `twin` (its terms rewritten to the representatives too,
  a no-op when it mentions no merged term), derived and justified by `[the meta, the
  equality]` — the same belief-following discipline the sentex twin itself rides.
  Retracting the merge collects the meta twins with it and the originals revive.  Registered
  through `integrate-twin`, so the twin reaches every index arm the original did — the
  exception re-check, the `except` roster, the reply cascade.

  `eqs` are the witnesses that migrated the sentex — the meta twin exists *because* the
  sentex did, so it rests on the same merge.  Public because a `(symmetric P)` mark folding
  two mirrored rows into one owes its doomed row's metas the same carry, and hands the
  declaration itself as the single witness (`integrate/commute-existing`): what raises a
  twin differs between the two callers, what a stranded meta costs does not.

  Rewrites read from `reader`, the vantage the twin's own form was elected from
  (`migrate-into`), so a meta elects the spellings its target does; the unscoped rewrite
  used the global election, which a merge `reader` cannot see would diverge from — a twin
  mis-guarded, mis-hidden or mis-aimed."
  [kb orig twin eqs reader]
  (let [realign (varmap-realign (p/get-sentex (:records kb) twin))]
    (doseq [mh   (reads/as-stored-with-term (:index kb) (sx/sentex-handle orig))
            :let  [msx (p/get-sentex (:records kb) mh)
                   s   (and msx (:sentence msx))]
            :when (and msx (jtms/in? (reasoning/tms kb) mh) (= orig (meta-target kb s)))]
      (let [m'  (rebuild-handle-meta kb s orig twin realign reader)
            ctx (:context msx)
            [h sx2 new?] (kb/find-or-create-sentex kb m' ctx)]
        (when new? (integrate-twin kb sx2 h))
        (justify-twin! kb mh h eqs)))))

(defn- handle-twins
  "The live twins a merge has already made of sentex `orig`: `[{:twin :eqs :reader}]`.  A
  twin is the `:consequence` of a `rewriteOf`-informant justification whose antecedents are
  `[orig, equality]` (`justify-twin!`); `jtms/dependents` names those from the original's
  side.  Grouping by consequence recovers each twin, the equality supporters that raised it,
  and its context — the same `reader` its form was elected from — exactly the arguments the
  first migration took.  Empty when `orig` has no twin, the common path.  A forward-chaining
  or defeat use of `orig` carries a different informant and is filtered out."
  [kb orig]
  (let [tms (reasoning/tms kb)]
    (->> (jtms/dependents tms orig)
         (map #(jtms/justification tms %))
         (filter #(and (= 'rewriteOf (:informant %)) (some #{orig} (:antecedents %))))
         (group-by :consequence)
         (keep (fn [[twin justs]]
                 (when-let [tsx (p/get-sentex (:records kb) twin)]
                   {:twin   twin
                    :eqs    (into [] (comp (mapcat :antecedents) (remove #{orig}) (distinct)) justs)
                    :reader (:context tsx)}))))))

(defn migrate-meta-onto-twins
  "A handle-naming meta `s` was just asserted.  If the sentex it names already migrated to
  twins, the merge ran before this meta existed, so migration never saw it — the meta lands
  on the superseded original and the live twin is unguarded / visible / unendorsed
  (docs/equality.md, the meta-after-merge case).  For each twin, replay `migrate-handle-metas`
  — it re-points **every** believed meta of the target (this new one included) and is
  idempotent for those already carried.  A no-op when `s` names nothing or its target has no
  twin, the common path; returns nil either way, and the twins settle with the caller's
  settle.  Takes the stored sentex (like `migrate-sentex`), not the bare sentence."
  [kb sentex]
  (when-let [target (meta-target kb (:sentence sentex))]
    (doseq [{:keys [twin eqs reader]} (handle-twins kb target)]
      (migrate-handle-metas kb target twin eqs reader))))

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
  (let [tx      (reasoning/taxonomy kb)
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
  (let [tx    (reasoning/taxonomy kb)
        pctx  (:context sentex)
        ectxs (equality-contexts kb (sx/sentence-of sentex))]
    (when (seq ectxs)
      (->> (tax/meet-closure tx (conj ectxs pctx))
           (filter #(tax/sees? tx % pctx))
           ;; the middle key is a taxonomy-closure read — built once per context, not
           ;; ~2·n·log n times; the tuple is `[0/1 long string]`, ordered by `compare`
           (nm/sort-by-content-key
            (juxt #(if (= % pctx) 0 1) #(count (tax/context-up tx %)) nm/print-key)
            compare)))))

(defn- migrate-into
  "Restate `sentex` as `reader` sees it, and store the result there.  Returns
  `{:form <normal form> :new [h] :superseded [[datum reason]] :violations [v]}`, or nil
  when `reader`'s election leaves the sentence alone, rests on nothing it believes, or
  reproduces a form `placed` already holds somewhere `reader` can see — that twin is
  already this reader's answer and a second copy would report the fact twice."
  [kb sentex reader placed]
  (let [handle    (:id sentex)
        sentence  (sx/sentence-of sentex)
        tx        (reasoning/taxonomy kb)
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
                             (and (jtms/in? (reasoning/tms kb) eh)
                                  (tax/sees? tx reader (:context esx)))))
                         (mapcat #(tax/equality-supporters tx %)
                                 (filter symbol? (tree-seq sequential? seq sentence))))
                 ;; schematic rewrite rules that normalize a subterm of the sentence —
                 ;; the oriented equational rewriting of docs/equality.md.  A rule that
                 ;; rewrites nothing here contributed nothing to the normal form and
                 ;; must not appear as a support.
                 (for [{:keys [handle context] :as rule} (tax/rewrite-rules tx)
                       :when (and (rewrite/rule-applies? rule sentence)
                                  (jtms/in? (reasoning/tms kb) handle)
                                  (tax/sees? tx reader context))]
                   handle))]
        (when (seq eqs)
          (let [existing (kb/find-sentex-handle kb rewritten reader)
                v        (when-not existing
                           (or (checks/constraint-violation kb rewritten reader)
                               (wff-violation* kb rewritten reader)))]
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
                ;; A migrated sentex's handle-naming meta-sentexes — `exceptWhen`
                ;; exceptions, an `except` hiding it, a target-following reply naming it —
                ;; ride separate sentexes keyed by its handle, so they must be re-pointed
                ;; onto the twin or the twin fires unguarded / becomes visible / loses its
                ;; reply (docs/equality.md, round two).  Any sentex can bear one, not only a
                ;; rule, so this is unconditional; a sentex with no meta enumerates nothing.
                (migrate-handle-metas kb handle h eqs reader)
                (cond-> {:form rewritten :new (if new? [h] [])}
                  ;; only the fact's own context supersedes: a reader below it restates
                  ;; the fact for itself and leaves the original believed where it lives
                  (= reader (:context sentex))
                  (assoc :superseded [[handle (kb/displaced-terms kb sentence reader)]]))))))))))

(defn migrate-sentex
  "Restate one stored sentex under its terms' representatives — **once per reader whose
  election differs**, not once per sentex.

  Returns `{:new [handles] :superseded [[datum reason]] :violations [v]}`.  Five things
  are required:

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
  (let [tms (reasoning/tms kb)]
    (reduce
     (fn [acc t]
       (reduce (fn [acc sx] (merge-with into acc (migrate-sentex kb sx)))
               acc
               (filter #(and (kb/rewritable-sentex? kb %)
                             (or (jtms/in? tms (:id %)) (jtms/superseded? tms (:id %))))
                       (kb/find-sentexes kb t))))
     {:new [] :superseded [] :violations []}
     (remove #(= % (tax/representative (reasoning/taxonomy kb) %)) terms))))

(defn- integrate-equality
  "The equality relations' add arm: reflect the sentex into the closure and migrate
  what it displaces.  Also exactly what a *derived* equality — the one `functional`
  now infers instead of throwing — needs, which is why `derive-equality` below calls
  it rather than the full table walk."
  [kb sentex handle]
  (let [sentence (:sentence sentex)
        [_ a b]  sentence]
    (tax/add-equality (reasoning/taxonomy kb) a b handle (kb/preferred-term sentence))
    (let [class (tax/equiv-class (reasoning/taxonomy kb) a)]
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
  (let [tms (reasoning/tms kb)]
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
    (for [nj (rewrite/non-joining-pairs new-rule (tax/rewrite-rules (reasoning/taxonomy kb)))]
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
    (tax/add-rewrite-rule (reasoning/taxonomy kb) handle lhs rhs (:context sentex))
    (recheck-equality-edge kb)
    (update (migrate-matching kb (first lhs))
            :violations into (confluence-violations kb sentex handle lhs rhs))))

(defn integrate-equality-sentex
  "The three equality relations' add arm, whichever entry point the sentex came through, and
  the whole of what one of them *means* to the derived state: the closure learns the
  edge and migration restates what the edge displaces.  Returns the migration result —
  `{:new :superseded :violations}` — which is why this is a named function rather than
  the table's anonymous arm.

  Two compound shapes are not a symbol merge and each is dispatched here (the reasons
  are `equality-entry`'s, beside the removal and rebuild halves that mirror this one):
  a schematic `(equals L R)` is an oriented rewrite rule, and `(rewriteOf T E)` with a
  compound `E` is a NAT reify-to-term declaration the partition holds no part of.

  The **derivation** path reaches it here too — a rule concluding one of the three
  merges exactly as an asserted one does — and it has to be by this function rather
  than by flagging the entry `:derived?`: `integrate-transitive` discards what an arm
  returns, and here the return value *is* the work, since the twins are chaining seeds
  and a migration a definitional check refused is a violation somebody must report."
  [kb sentex handle]
  (let [s (:sentence sentex) [_ _ b] s]
    (cond
      (rewrite/schematic-equation? s) (integrate-rewrite-rule kb sentex handle)
      (sequential? b)                 nil   ; NAT rewriteOf-to-compound
      :else                           (integrate-equality kb sentex handle))))

(defn- believed-restatements
  "Every believed equality sentex and schematic rewrite rule in the KB, as
  `{:context :terms}` — the restatements a reader can consult, each with the terms it
  puts in play.

  An equality edge contributes the whole **class** of its symbol arguments, minus the
  terms already standing for their class, which is `migrate-class`'s candidate set and
  is the unit for `equality-contexts`' reason: chain composition means an edge touching
  neither of a sentence's own terms still decides what they rewrite to.  A schematic
  rule contributes its LHS head, which is `migrate-matching`'s: the head is present in
  every occurrence of the redex, so the term index gives a superset in one lookup.

  Read off the three equality functor roots and the taxonomy's rule cache, so the cost
  is proportional to the **standing merges** and not to the store — a KB holding a
  hundred million facts and no merge enumerates nothing."
  [kb]
  (let [tx   (reasoning/taxonomy kb)
        idx  (:index kb)
        recs (:records kb)
        tms  (reasoning/tms kb)]
    (into (into []
                (comp (mapcat #(reads/as-stored-with-functor idx %))
                      (distinct)
                      (filter #(jtms/in? tms %))
                      (keep #(p/get-sentex recs %))
                      (map (fn [sx]
                             {:context (:context sx)
                              :terms   (into #{}
                                             (comp (filter symbol?)
                                                   (mapcat #(tax/equiv-class tx %))
                                                   (remove #(= % (tax/representative tx %))))
                                             (rest (:sentence sx)))})))
                (sort kb/equality-predicates))
          (comp (filter #(and (sequential? (:lhs %)) (symbol? (first (:lhs %)))))
                (map (fn [r] {:context (:context r) :terms #{(first (:lhs r))}})))
          (tax/rewrite-rules tx))))

(defn- restated-terms-in
  "The terms the `restatements` stored in one of `ctxs` put in play."
  [restatements ctxs]
  (into #{} (comp (filter #(contains? ctxs (:context %))) (mapcat :terms)) restatements))

(defn- ancestor-migration-candidates
  "The stored sentexes naming one of `terms` whose context is in `ctxs` and which
  migration may restate — rewritable, and either believed or merely superseded, the
  same pair `migrate-class` admits and for its reason.  Keyed by handle, so a sentex
  reached through two of its terms is migrated once."
  [kb terms ctxs]
  (let [tms (reasoning/tms kb)]
    (into {}
          (comp (mapcat #(kb/find-sentexes kb %))
                (filter #(and (contains? ctxs (:context %))
                              (kb/rewritable-sentex? kb %)
                              (or (jtms/in? tms (:id %)) (jtms/superseded? tms (:id %)))))
                (map (juxt :id identity)))
          terms)))

(defn migrate-under-context-edge
  "When a `(genlCx sub super)` edge arrives, restate the sentexes the widened ancestor set newly
  exposes to a merge — the third arrival order of the same three ingredients, and the
  equality twin of `visibility-seeds`.

  An equality applies **where it is visible**, so which sentexes it restates is as much
  a question about the `genlCx` ancestor set as about the closure.  `migrate-class` covers the
  merge arriving last and `migrate-sentex` on the assert path covers the fact arriving
  last; without this the *edge* arriving last leaves the record spelled the way a context
  that could not see the merge stored it, while every read from a context that now can
  asks after the representative and misses it — a sentex believed and answering no query,
  in exactly the orderings that wire the contexts last.  `supersession-stamp` carries
  `:ctx-gen`, so the reconcile beside this re-derives which spellings are displaced on
  the same edge; what it cannot do is *write* the restatement, since an entry there is
  only ever dropped or restated and a spelling starts being displaced when migration
  says so.

  **Both ancestor sets, because an edge pairs facts and merges in two directions.**  The whole of
  the new reachability is that a reader in `context-down(sub)` now sees
  `context-up(super)`, so a triple of reader, fact and merge is new only if the reader
  newly reached one of the two — which puts that one in `super`'s ancestor set and the reader
  in `sub`'s descendant set, whichever it was.  So there are two halves: a merge above meeting
  the facts the widened readers already saw, and a fact above meeting the merges they
  already saw.  Taking one and not the other fixes half the orders and leaves the rest.

  **Enumerated from the merges, not from the ancestor set**, for `visibility-seeds`' reason: the
  candidates are the stored sentexes naming a term one of those merges displaces, and
  the inverted term index answers that in one lookup per term.  Cost is then proportional
  to the standing merges and to what they reach, and independent of how much ontology the
  ancestor set holds — a KB that has merged nothing pays one set-empty test, and each half is
  gated on the other side holding a merge the reader can see, so wiring a context under
  one whose merges it already inherits enumerates nothing.

  **The removal side needs no twin of this.**  Dropping an edge narrows what a reader
  sees, and a twin names the equality edges it was elected over
  (`justify-twin!`), so the ordinary dependency-directed sweep collects one whose merge
  the reader can no longer see, and `refresh-supersessions` hands the spelling back."
  [kb sentence]
  (when (= 'genlCx (nm/functor sentence))
    (let [tx           (reasoning/taxonomy kb)
          [_ sub super] sentence]
      (when (and (symbol? sub) (symbol? super)
                 (or (seq (tax/equality-edges tx)) (seq (tax/rewrite-rules tx))))
        (let [above   (set (tax/context-up tx super))
              ;; every context a newly-widened reader can see: the readers are
              ;; `context-down(sub)`, and each reads the merges and the facts of its own
              ;; ancestor set.  Contexts are few, so this is a memoized closure read apiece.
              readers (into #{} (mapcat #(tax/context-up tx %)) (tax/context-down tx sub))
              rs      (believed-restatements kb)
              near    (restated-terms-in rs above)
              far     (restated-terms-in rs readers)
              cands   (merge (when (seq near) (ancestor-migration-candidates kb near readers))
                             (when (seq far)  (ancestor-migration-candidates kb far above)))]
          (reduce (fn [acc sx] (merge-with into acc (migrate-sentex kb sx)))
                  {:new [] :superseded [] :violations []}
                  (vals cands)))))))

(defn- displacement
  "The supersession entry for datum `d` — `[d {displaced-term representative}]` — or nil
  when `d`'s spelling is not displaced, or `d` is no longer stored at all.

  **Read from the sentex's own context**, the way migration writes it.  A datum lives in
  one context, and the question a supersession answers is whether *that* context has
  retired the spelling — so an equality it cannot see must not displace it, and a
  restatement elected below it is that reader's twin rather than a replacement for this
  one (`migrate-sentex`).  Asking globally instead would take a premise away from the
  context that asserted it on the strength of a merge stated somewhere it cannot see.

  `visible-for` is the caller's memo from context to visibility predicate.  **One
  visibility predicate per context, not per entry**: scoping the read costs a record
  fetch per equality supporter, and a merging assert examines every entry the migration
  produced — so a fresh predicate per entry would re-fetch the same supporter records
  once per entry, which is the whole reconcile squared.  The entries cluster hard by
  context (they are the sentexes one merge displaced), so memoizing across the walk
  collapses that to one fetch per supporter."
  [kb visible-for d]
  (when-let [sx (p/get-sentex (:records kb) d)]
    (let [ctx       (:context sx)
          visible?  (visible-for ctx)
          sentence  (sx/sentence-of sx)
          rewritten (sx/canon (kb/rewrite-term* kb sentence visible?))]
      ;; still displaced only if its own terms still rewrite to something else *and*
      ;; the restatement is actually stored
      (when (and (not= rewritten (sx/canon sentence))
                 (kb/find-sentex-handle kb rewritten ctx))
        [d (kb/displaced-terms* kb sentence visible?)]))))

(defn- supersession-stamp
  "Everything a supersession answer reads besides the datum's own record: the active
  equality edges and the `rewriteOf` preference claims they carry — which between them
  decide every class and every representative — the believed schematic rewrite rules,
  which decide the rest of a normal form, and the `genlCx` generation, which
  decides which merges a sentex's own context can see.

  Cheap to take and cheap to compare, with one of the four the exception on both counts.
  `equality-edges` and `rewrite-rules` are handed back as the *same object* while nothing
  has moved, so their comparison stops on identity, and `:ctx-gen` is a counter.
  `equality-prefs` flattens the per-edge preference sets into a fresh set on every call,
  so `:prefs` is rebuilt per stamp and always compared by value — proportional to the
  standing `rewriteOf` claims, which is none at all for a KB that states no preference.
  It is a stamp of the derived state, not of the KB: a store holding a hundred million
  facts and no merge stamps as the empty set."
  [kb]
  (let [tax (reasoning/taxonomy kb)]
    {:equality (tax/equality-edges tax)
     :prefs    (tax/equality-prefs tax)
     :rewrites (tax/rewrite-rules tax)
     :ctx-gen  (tax/relation-gen tax :genlCx)}))

(defn- region-suffices?
  "Can this reconcile be narrowed to the moved region, or must every standing entry be
  re-examined?

  An entry's answer reads four things: the datum's own record, the class its terms
  belong to, the rewrite rules, and whether the restatement is still stored.  Hold the
  last three still and the only entries that can have moved are the ones the region
  names — so the question here is whether the stamp says they held.

  * **The rewrite rules and the `genlCx` generation must be unchanged.**  Neither
    leaves a trace on the entries: a schematic rule leaving re-normalizes every sentence
    it reached, and a context edge changes which merges a reader can see, and in both
    cases the entry that stops holding is one nothing relabelled.

  * **The equality edges and preferences must be unchanged, *or* `extra` must be
    non-empty.**  `extra` is migration's own output, and migration walks the whole class
    a merge moved (`migrate-class`) — every stored sentex naming any member, superseded
    ones included, and every entry already in the set is one `kb/rewritable-sentex?`
    admits and goes on admitting while the merge that displaced it stands.  So a class
    move that arrived with a migration is described by what the migration handed over,
    and a class move that arrived without one (an equality retracted, defeated or
    revived) is described by nothing and takes the full pass.

    The one thing that escape does not carry is a restatement migration **refused** —
    a rewritten form the constraint or `wff` checks reject, which is filed as a violation
    and leaves the sentex out of `extra`.  A spelling already displaced by an earlier
    merge then keeps that supersession rather than being handed back, and the KB is one
    with a reported violation in it either way.

  Answers **no** when there is no previous stamp at all, which is a freshly opened KB, a
  recovered one, and anything that wiped the derived state: a stamp that cannot be
  compared costs one full reconcile and never a wrong answer."
  [stamp prev extra]
  (and (some? prev)
       (= (:rewrites stamp) (:rewrites prev))
       (= (:ctx-gen stamp) (:ctx-gen prev))
       (or (and (= (:equality stamp) (:equality prev))
                (= (:prefs stamp) (:prefs prev)))
           (boolean (seq extra)))))

(defn- supersession-map
  "The `datum -> displaced-terms` map of spellings the equality closure currently
  displaces, reconciled against the taxonomy.

  Derived state, like `defeated` and `blocked`: it is recomputed rather than
  accumulated, so a supersession cannot outlive the merge that caused it and a
  retracted equality gives the caller's premise back with no un-supersede path of its
  own.  Entries are only ever dropped or restated here — a spelling *starts* being
  displaced when migration says so, and arrives as `extra`.

  **Narrowed to the region, the way every other reconcile in `settle-finish` is.**  A
  standing merge is not small: `sameAs` is one of three relations feeding the closure,
  `owl:sameAs` is what an RDF import emits in quantity, and re-examining every displaced
  datum on every settle would make loading n merges quadratic in n.  So the walk is over
  `extra` plus the entries the moved region names, and `region-suffices?` decides
  whether that is the whole answer.  Each examined entry costs a record fetch, a rewrite
  through the closure and a store probe; each carried one costs a set membership test.

  `region` is `jtms/touched`, a superset of every datum whose belief moved — which is
  also a superset of every datum *removed*, since a removal relabels what rested on it.
  That is what covers the two ways an entry can stop holding while the closure stands
  still: the displaced datum itself leaving, and its restatement leaving with it.  Pass
  nil to force the full pass."
  [kb extra region]
  (let [tms   (reasoning/tms kb)
        held  (jtms/superseded tms)
        stamp (supersession-stamp kb)
        prev  (some-> (reasoning/supersessions kb) deref)
        vis   (memoize #(res/visible-supporter-fn kb %))]
    (some-> (reasoning/supersessions kb) (reset! stamp))
    (if (and (some? region) (region-suffices? stamp prev extra))
      (reduce (fn [m d] (if-let [e (displacement kb vis d)] (conj m e) (dissoc m d)))
              (into held extra)
              (into (mapv first extra) (filter #(contains? held %)) region))
      (into {} (keep #(displacement kb vis (first %))) (into held extra)))))

(defn refresh-supersessions
  "Reconcile the superseded set with the equality closure — the equality analogue of
  `tax/refresh-beliefs`, and called from the same place for the same reason.

  The window is the same for all three callers (an assert that merged, the end of a
  settle, and `recover`): everything the TMS has relabelled since the last settle
  finished.  Two of them let it read that window itself; **`settle-finish` hands over
  the value it already holds**, because there the read is not free — the dense network
  materializes the whole bitmap into a boxed set per read, which on a rebuild is the KB,
  and the finish reads it once into a delay precisely so its consumers do not each pay
  for it.  Taking the value rather than re-reading is safe for the same reason that
  delay is: nothing between the finish's read and `reset-touched!` relabels, so the
  region cannot grow underneath it."
  ([kb] (refresh-supersessions kb nil))
  ([kb extra] (refresh-supersessions kb extra (jtms/touched (reasoning/tms kb))))
  ([kb extra region]
   (jtms/supersede (reasoning/tms kb) (supersession-map kb extra region))))

(defn- derive-equality
  "Store `(equals x y)` in `context` as a **derivation** from `antes` and merge with
  it.  Returns the migration result, so the caller can seed chaining with the twins.

  The arguments are ordered by content, never by arrival: the sentence is a key, and
  a key that depended on which value the caller happened to assert second would make
  one merge store as two sentexes.  **The antecedents are ordered the same way**
  (`kb/antecedent-order`), for the reading rather than for the key: the caller hands them
  over with the arriving fact ahead of the standing one, so an unordered vector would
  make `why` print the two facts behind one merge in whichever order they were written."
  [kb x y context informant antes]
  (let [[lo hi]    (sort [x y])
        sentence   (list 'equals lo hi)
        antes      (kb/antecedent-order kb antes)
        [h s new?] (kb/find-or-create-sentex kb sentence context)
        depth      (inc (reduce max 0 (map #(jtms/depth (reasoning/tms kb) %) antes)))]
    (jtms/ensure-node (reasoning/tms kb) h depth)
    (when-not (jtms/has-justification? (reasoning/tms kb) informant antes h)
      (let [jid  (p/next-id (:records kb))
            just (jtms/->just jid informant antes h {} :monotonic)]
        (p/put-justification (:records kb) just)
        (jtms/add-justification (reasoning/tms kb) just)))
    (when new? (derived-sentex-added kb s h))
    (integrate-equality kb s h)))

(defn- derive-functional-equalities-in
  "`derive-functional-equalities`, scoped to exactly `context` and no reader below it —
  the single-context mechanics `derive-functional-equalities` sweeps over every reader
  that can see `context`.  Read this one for how the merge is found and justified;
  read the public wrapper for why one call becomes several.

  `(functional P)` plus two symbol values for the same first argument **derives**
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
  justification needs the declaring sentex itself, and only the true branch pays for it.

  **One justification per declaring sentex, not one off an arbitrary declaration.**  A
  KB may state `(functional P)` in two contexts, which is two sentexes and two handles
  and is refused by nothing; taking `first` of them put an assertion-ordered handle into
  the justification's antecedents, so retracting *that* declaration withdrew the merge
  while the other still stood — and which of the two it was depended on the order they
  arrived in.  `tax/prop-supporters` is the whole set, defeated members included (its
  docstring says why: a derivation revives by itself when its supporter does), **and
  unfiltered by what `context` sees** — the whole set on the visibility axis too, and
  deliberately: filtering to visible supporters would make the surviving merge depend
  on which declaration was retracted first, and
  `a-merge-rests-on-every-functional-declaration-not-on-one-of-them` pins both
  directions on independent predicates so no arbitrary choice can pass as this.  The
  equality takes a justification from each — the shape `deduce-lift` already uses for
  the same reason, so retracting one of two declarations leaves the merge standing on
  the other.  Sorted only to make each antecedent list stable to read; the *set* of
  justifications is what carries the meaning, and a set has no order to depend on.

  **A mark on a super-predicate counts, and brings its `genl` edges with it.**
  `(functional parentOf)` says a child has one mother however the tuple is spelled, so
  two `fatherOf` fillers merge under it (`tax/props-over`) — and the merge then rests on
  the subsumption as much as on the declaration, so `checks/edge-support` puts the edge
  handles into the same antecedent list.  Without them, retracting the edge would leave
  two names merged on a declaration that no longer reaches either of them.

  **Both spellings' edges, and only the mark that convicted.**  Two things follow from
  the clash being a *pair*, and the earlier reading of it got both wrong.

  The pair has two sides and each reached the marked predicate its own way.  Naming the
  arriving sentence's descent and not the stored filler's left the merge standing after
  the filler's own `genl` edge was retracted — at which point that fact is not a tuple of
  the marked predicate at all, and nothing licenses the merge.  That is verbatim the
  failure `edge-support` exists to prevent, avoided on one side and not the other, so
  both descents are named.

  And `functional-clashes` reports **which** mark convicted, as the `via` of its triple,
  computed for exactly this.  Justifying the merge with every marked predicate above the
  functor instead let a mark that never covered the pair hold it up: with
  `(functional guardianOf)` over a hierarchy where only one of the two spellings is a
  `guardianOf`, the merge survived retracting the only declaration that ever reached
  both.  One clash, one convicting mark, its declaring sentexes — which is still every
  *sentex* of that mark, since a predicate declared functional in two contexts is two
  handles and the merge may not depend on which arrived first.

  Scoped to the reader, matching the clash it is drawn from: `props-over` is read
  through `functional-clashes`' own scoped call and the descent through `context`, so a
  mark or an edge in a sibling context cannot support a merge that context cannot see.
  `prop-supporters` stays unfiltered, deliberately and for the reason its own docstring
  gives.

  **The two descents are a set, not a concatenation.**  They overlap whenever the two
  sides share any of the path up to the mark, which is the ordinary case rather than the
  odd one: two `fatherOf` fillers under `(functional parentOf)` descend the *same* edge,
  and a `dad_of` filler beside a `fatherOf` one shares the `fatherOf → parentOf` hop.
  Appending them left the shared handles twice over in the record `derive-equality`
  stores, so `core/why`'s `:because`, `why-not`'s `:missing` and `preview`'s
  `:antecedents` each listed one edge two or three times.  Belief never moved — `valid?`
  is an `every?` and `has-justification?` keys on a set — which is why it reads as
  cosmetic and is not: an antecedent list is the explanation a caller is given, and one
  that counts a single edge twice describes a justification the KB does not hold.
  `distinct` rather than a set literal, so the list keeps the order the descent produced
  and stays stable to read."
  [kb sentence context handle]
  (let [tax     (reasoning/taxonomy kb)
        recs    (:records kb)
        pred    (nm/functor sentence)
        ;; content-ordered, so which pair gets the explicit equality is a function of
        ;; what the KB says rather than of which filler was written first — it shows when
        ;; a standing merge among the fillers is later retracted.  **The whole triple is
        ;; in the key**, the form the antisymmetric twin below uses and for the same
        ;; reason: `first-per-slot` dedups on `[handle value]`, so two handles can fill
        ;; the slot with one value, and a key holding the value alone would leave them
        ;; tied — the tie falling to `functional-clashes`' own order, which is a `for`
        ;; over `res/matches-visible`, an answer *set*.  `oh` goes into the derived
        ;; equality's antecedent vector, so that is not cosmetic.  Structural, so nothing
        ;; is printed and no ambient `*print-length*` can collapse it.
        clashes (nm/sort-by-content-key
                 (fn [[oh v via n]] (let [s (p/get-sentex recs oh)]
                                      [v (:sentence s) (:context s) via n]))
                 (checks/functional-clashes kb sentence context))]
    (when (seq clashes)
      (reduce (fn [acc [oh v via n :as clash]]
                ;; the incoming filler is argument `n`, read off the clash rather than
                ;; assumed to be argument 2 — with `functionalInArg` the constrained
                ;; position moves, and two clashes on one sentence may be about two
                ;; different arguments of it.
                (let [b (checks/functional-filler sentence clash)]
                  ;; the idempotence guard is **scoped to `context`**: skip a pair only
                  ;; when the merge that reconciles them is one `context` can already see.
                  ;; Read globally it skipped a pair merged behind an edge `context` cannot
                  ;; see, so a context could not derive a functional equality it is owed
                  ;; because some other context happened to hold one — belief drifting with
                  ;; a merge the reader never heard of.
                  (if-not (and (checks/mergeable-values? v b)
                               (not (res/same-class-in? kb v b context)))
                    acc
                    ;; the edges *both* sides of the pair descended to reach the mark —
                    ;; deduped, since the two descents share every hop they have in common
                    ;; and the same functor on both sides shares all of them
                    (let [other (some-> (p/get-sentex recs oh) :sentence nm/functor)
                          edges (into [] (distinct)
                                      (cond-> (vec (checks/edge-support kb pred via context))
                                        (and (symbol? other) (not= other pred))
                                        (into (checks/edge-support kb other via context))))
                          ;; every declaration constraining `via` at this position — the
                          ;; `(functional via)` sentexes at position 2 and the
                          ;; `(functionalInArg via n)` sentexes always, so a merge holding
                          ;; under both spellings survives retracting either.
                          antes (map #(into [%] edges)
                                     (sort (checks/functional-declaration-supporters
                                            tax via n)))]
                      (reduce (fn [acc a]
                                (merge-with into acc
                                            (derive-equality kb v b context 'functional
                                                             (into [handle oh] a))))
                              acc antes)))))
              {:new [] :superseded [] :violations []}
              clashes))))

(defn- functional-mark-relevant?
  "Could `sentence`'s own functor, or something it descends from, carry a `functional`
  or `functionalInArg` mark — the cheap pre-gate `derive-functional-equalities` reads
  before paying for a reader sweep, so a fact of a predicate no mark reaches never pays
  for one.  Two unscoped, over-approximating `genl`-walk reads (`tax/props-over`,
  `tax/functional-in-arg-over`), the same reads `checks/functional-clashes` already
  makes internally to answer the single-context question — this asks it once more,
  early, purely to decide whether `context-down` is worth reading at all."
  [tax sentence]
  (let [f (nm/functor sentence)]
    (and (symbol? f)
         (or (seq (tax/props-over tax :functional f))
             (seq (tax/functional-in-arg-over tax f))))))

(defn derive-functional-equalities
  "`derive-functional-equalities-in`, run from `context` **and from every reader that
  can see it** — `(tax/context-down tax context)`, which already includes `context`
  itself.

  A functional clash is a property of what a vantage sees, not of where the arriving
  fact happens to be stored.  Scoping to `context` alone was fine while nothing could
  see `context` but `context` — the ordinary KB, one flat namespace — but a fact
  arriving into a context that some *other*, already-connected reader below it can see
  is exactly the shape two mutually-blind siblings joined from below present: neither
  `CxLeft` nor `CxRight` can see the other's filler when its own fact lands, so a
  derivation scoped only to the arriving fact's own context finds nothing, and the
  reader below — `CxBottom`, which was told about both edges before either fact
  arrived — is never asked at all.  `functional-clashes` is itself already
  context-scoped and answers a different, generally *wider*, set of clashes for a
  reader below than for `context` alone (that is the whole point of asking it again
  per reader rather than reusing one answer), so this cannot be phrased as `context`'s
  own result handed down to its readers — each reader gets its own call.

  **Gated before `context-down` is read, on the same global roster
  `equate-under-edge`/`equate-under-context-edge` gate on** — a KB that declares
  nothing `functional` and nothing `functionalInArg` gets one map read here and never
  the closure walk, whatever context topology it has, matching the docstring's own
  standing claim that a KB using none of the feature pays an O(1) set lookup per fact
  and no more.  On the common single-context KB `context-down` answers `#{context}`,
  so the sweep runs its one iteration and reduces to exactly today's behaviour.

  **Idempotent for the reason `equate-existing` gives**, applied once per reader
  instead of once per direction: `derive-functional-equalities-in` itself skips a pair
  `same-class-in?` already holds from that reader's own view, so a reader whose ancestor set
  overlaps another's — which every reader below `context` overlaps `context` on, since
  `context-down` always includes it — pays a repeated no-op read rather than a repeated
  merge.

  **`readers`, when given, is the only reader set this sweeps** — the intersection with
  `context-down(context)`, not a replacement for it.  One caller passes it:
  `equate-under-context-edge-via`, which hands down the contexts a `genlCx` edge actually
  changed the ancestor set of.  A reader outside that set sees exactly what it saw before
  the edge, so no pair can have newly become jointly visible to it; whichever of the other
  three arrival orders applies had already run there, each with its full fan.  Which set
  that is comes straight out of `context-down`, which filters its raw candidates by
  `(sees? tax % c)` — every candidate's own forward walk — and so is the exact inverse of
  `context-up`, `except` holes included: `context-up(R)` gains `super`'s side exactly when
  `sub` is in it, which is exactly when `R` is in `context-down(sub)`.

  nil is the default and the every-other-caller case: a fact, a declaration or a `genl`
  edge arriving last changes no context's ancestor set, so there is no smaller set to
  narrow to and all of `context-down` is swept.  `genlcx_sweep_test` pins both the pairs
  the narrowing must keep deriving and the readers it must not visit, and
  `genlcx_sweep_cost_test` pins that the count does not grow with readers the edge did
  not reach.

  **This is what lets `equate-under-context-edge` and `equate-under-edge` stay the same
  shape**: each already calls this function once per stored fact, using that fact's own
  storage context, exactly as it always has — the sweep this wrapper adds is what
  reaches the readers a fact's own context cannot, so neither caller needs a reader
  computation of its own any more.  `derive-antisymmetric-equalities` is the twin, over
  `derive-antisymmetric-equalities-in`.

  **A second, per-fact gate stands in front of the reader sweep**
  (`functional-mark-relevant?`), and it is not redundant with the KB-wide one above it.
  The KB-wide gate answers *does this feature exist at all*; a KB that declares
  `(functional birthYear)` and nothing else still asserts every other predicate it has,
  and without the per-fact gate every one of those unrelated facts pays a full
  `context-down` closure read regardless — a plain, unrelated fact landing in a context
  with thousands of readers below it costs a thousands-of-contexts sweep for a
  `functional-clashes` call that is always going to answer empty.  The per-fact gate is
  what `functional-clashes` is always going to check anyway (`tax/props-over`,
  `tax/functional-in-arg-over`), asked once, early, before the expensive part rather
  than N times inside it."
  ([kb sentence context handle] (derive-functional-equalities kb sentence context handle nil))
  ([kb sentence context handle readers]
   (let [tax (reasoning/taxonomy kb)]
     (when (tax/functional-family-declared? tax)
       (if (functional-mark-relevant? tax sentence)
         (reduce (fn [acc r]
                   (merge-with into acc (derive-functional-equalities-in kb sentence r handle)))
                 {:new [] :superseded [] :violations []}
                 (cond->> (tax/context-down tax context)
                   readers (filter readers)))
         (derive-functional-equalities-in kb sentence context handle))))))

(defn- functional-family-declaration
  "The predicate `sentence` marks, when it is a functional-family declaration —
  `(functional P)` or `(functionalInArg P n)` — else nil.  The one entry point the
  declaration-arriving-last merge path opens through.

  **The lane map, because this entry point has eaten a fix before.**  A mark family
  lives in two lanes:

  * **Merges (this namespace):** fact-last → `derive-functional-equalities`;
    declaration-last → `equate-existing`, through this entry point; `genl`-edge-last →
    `equate-under-edge`; `genlCx`-edge-last → `equate-under-context-edge`.
  * **Clash exposure (`settle.clj`):** `clash-declaration-functors`, the
    discovery arms, the trigger case — reported via
    `checks/arbitrable-violations`.

  The 2026-08 `functionalInArg` gap sat exactly here: settle's lane was swept
  thoroughly while an exact-functor test in `equate-existing` quietly excluded
  the generalized declaration, and nothing named the exclusion.  So the spellings
  are no longer written in each lane: `tax/functional-family-marks` is this entry point's
  read of the declaration's `:family`, settle's rosters are that same entry's
  `:sweeps` and `:shape` read back, and `predicates/check-families` refuses at load
  a family whose spellings disagree about the sweep — so a new spelling reaches this
  entry point and settle's rosters together rather than separately.  What stays here is the
  arity, since this entry point is downstream of well-formedness and settle's triggers,
  coming off a moved region, are not."
  [sentence]
  (when (case (tax/functional-family-marks (nm/functor sentence))
          :mark        (= 1 (nm/arity sentence))
          :mark-in-arg (= 2 (nm/arity sentence))
          false)
    (first (nm/args sentence))))

(defn- equate-declared-subtree
  "The body `equate-existing` and `antisym-equate-existing` share: every **stored** fact
  of `pred`'s spec subtree handed back to the family's `derive` in its own context, for
  the declaration-arriving-last direction.

  Stored rather than believed, and unfiltered where `equate-under-edge-via` filters — an
  equality derived off a defeated fact rests on that fact and is defeated with it, where
  skipping it would leave the merge missing when the fact revives.  The two entry points state
  that reasoning once between them because they are one rule about one arrival order.

  nil for a `pred` that is not a symbol, so a caller's entry point can hand over whatever its
  declaration named without checking first."
  [kb pred derive]
  (when (symbol? pred)
    (reduce (fn [acc sx]
              (merge-with into acc
                          (derive kb (:sentence sx) (:context sx) (:id sx))))
            {:new [] :superseded [] :violations []}
            (subtree-sentexes kb pred))))

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
  un-merges.  Re-deriving is idempotent — the scoped `same-class-in?` skips a pair the reader's
  visible closure already holds and `has-justification?` skips an argument it already
  has — so a slot filled by three values collapses to one class rather than to the first
  pair walked.

  Sweeps what is **stored** rather than what is believed, for `entail-existing`'s
  reason: an equality derived off a defeated fact rests on that fact and is defeated
  with it, where skipping it would leave the merge missing when the fact revives — belief
  depending on the order the defeat and the declaration arrived in.  The extent is read
  off the functor roots of `P`'s whole `genl` **spec** subtree, because the mark binds
  every predicate beneath the one it names (`tax/props-over`) — an extent read off `P`'s
  own root alone would merge two `parentOf` fillers and leave two `fatherOf` ones apart.
  `subtree-sentexes` reads it, snapshotted before the first merge, since migration writes
  twins to the roots the walk is reading."
  [kb sentence]
  (when-let [pred (functional-family-declaration sentence)]
    (equate-declared-subtree kb pred derive-functional-equalities)))

(defn- equate-under-edge-via
  "The body `equate-under-edge` and `antisym-equate-under-edge` share: a `(genl sub
  super)` edge arriving over facts already stored, with every believed premise of `sub`'s
  spec subtree handed back to the family's `derive` in its own context.

  `declares?` is the family's cheap pre-gate, asked of the taxonomy before the subtree is
  read — so a `genl` write into a KB declaring nothing of the family costs one map lookup
  and no traversal.

  **Shared rather than written twice, because the two entry points differ in nothing else.**
  They answer one arrival order — the edge arriving last — for two mark families, and a
  fix to that order has to reach both or reach neither: vaelii#43 was exactly such a fix,
  applied to two copies by hand.  A family joins by passing its gate and its derive, which
  is the same reading `tax/functional-family-marks` gives the spellings one lane up."
  [kb sentence declares? derive]
  (when (and (= 'genl (nm/functor sentence))
             (= 2 (nm/arity sentence))
             (declares? (reasoning/taxonomy kb)))
    (let [[_ sub] sentence]
      (when (symbol? sub)
        (reduce (fn [acc sx]
                  (if-not (and (nil? (:antecedent sx)) (not (sx/negative? sx)))
                    acc
                    (merge-with into acc
                                (derive kb (:sentence sx) (:context sx) (:id sx)))))
                {:new [] :superseded [] :violations []}
                (subtree-sentexes kb sub))))))

(defn equate-under-edge
  "When a `(genl sub super)` edge arrives, derive the equalities a `(functional …)` mark
  above `super` now licenses over the `(sub …)` facts already stored — the third arrival
  order of the same three ingredients, and the equality twin of `entail-under-edge`.

  A `functional` mark descends the predicate hierarchy, so the two facts, the declaration
  and the **edge** are all ingredients of one merge.  `derive-functional-equalities`
  covers the fact arriving last and `equate-existing` the declaration arriving last;
  without this, the edge arriving last merges nothing and whether two names denote one
  woman would depend on which of the three was written first.  nil when `sentence` is not
  a `genl` edge.

  The whole **spec subtree** of `sub`, because subsumption is transitive, and each stored
  fact is put back through `derive-functional-equalities` in its own context — the same
  function the other two directions ask, so the three cannot disagree about what a slot
  licenses or what justifies the merge.  Re-deriving is idempotent for the reason
  `equate-existing` gives.

  **Free for a KB that declares nothing of the functional family**, and that is decided
  *before* the subtree is read rather than per fact inside the fold.  This arm fires on a
  `genl` edge — the commonest thing an ontology says — where the other two fire on a
  declaration and are gated by their own trigger, so it is the one that reaches for an
  extent on an ordinary write.  `tax/functional-family-declared?` answers it in two map
  reads; `subtree-sentexes` filters what survives by index cardinality.

  **The family, not the arity-2 spelling alone**, and it is the gate rather than the body
  that had to learn this: the fold below asks `derive-functional-equalities`, which reads
  both spellings, so a gate on `props :functional` alone shut the whole arm for a KB whose
  only mark was `(functionalInArg P n)` — the `genl` edge arriving last merged nothing
  where `(functional P)` in the same order merged, which is the arity-2 behaviour
  `functional_in_arg_test` exists to hold still.  Reading the shared predicate is what
  keeps this entry point and `equate-under-context-edge` asking one question.

  **What that does not buy is a smaller edge.**  `subsumption-seeds` walks the same spec
  subtree on the same edge and must — those facts really do become matchable — so a
  `genl` write is Ω(subtree extent) whatever this arm does, and the gate removes a
  redundant traversal rather than an order of growth.  Measured on a 16x subtree the two
  read alike, which is why no `lein perf` check states this: the gate is worth having
  because repeated work and a false docstring are both worth removing, not because it
  moves a curve."
  [kb sentence]
  (equate-under-edge-via kb sentence
                         tax/functional-family-declared?
                         derive-functional-equalities))

(defn- derive-antisymmetric-equalities-in
  "`derive-antisymmetric-equalities`, scoped to exactly `context` and no reader below
  it — see the public wrapper for why one call becomes several.

  `(anti_symmetric P)` plus a believed converse `(P b a)` for `(P a b)` **derives**
  `(equals a b)` and merges — the antisymmetric twin of `derive-functional-equalities`,
  and the same machinery.

  Making it a real justification is what makes it safe.  The merge is justified by
  **[this fact, the converse, the declaration]** — plus the `genl` edges either spelling
  descended through to reach the mark (`checks/edge-support`), for `derive-functional-
  equalities`' reason — so `why` names exactly what caused it and retracting any one
  un-merges.  One justification per declaring sentex (`tax/prop-supporters`), so a
  predicate declared antisymmetric in two contexts leaves the merge standing on the other
  when one is retracted.

  Gated on the `:anti-symmetric` roster before the store is read, so a KB declaring
  nothing antisymmetric — the common case — pays one O(1) set lookup per asserted fact and
  no more.  Both arguments must be plain symbols the partition can hold
  (`checks/mergeable-values?`); a self tuple, or a pair some visible merge already
  reconciles, is skipped.  A non-mergeable converse is the hard contradiction
  `checks/antisymmetry-problems` refuses at the entry point instead."
  [kb sentence context handle]
  (let [tax (reasoning/taxonomy kb)]
    (when (seq (tax/props tax :anti-symmetric))
      (let [pred (nm/functor sentence)
            args (vec (nm/args sentence))]
        (when (= 2 (count args))
          (let [[a b] args]
            (when (checks/mergeable-values? a b)
              (let [recs      (:records kb)
                    ;; on content, never the handle: order the converses by the sentence
                    ;; the handle names, its context, and the marked predicate read
                    ;; through — so which merge is derived first is a function of what the
                    ;; KB says, not of which converse was asserted first.  Belief is the
                    ;; same either way (every converse derives the one `(equals a b)`), but
                    ;; a handle key would have decided the derivation order on arrival.
                    converses (nm/sort-by-content-key
                               (fn [[h via]] (let [s (p/get-sentex recs h)]
                                               [(:sentence s) (:context s) via]))
                               (checks/antisymmetric-converses kb sentence context))]
                (reduce
                 (fn [acc [oh via]]
                   ;; a self tuple probes itself, and a pair a visible merge already holds
                   ;; is done — both scoped to `context`, matching the clash it is drawn from
                   (if (or (= oh handle) (res/same-class-in? kb a b context))
                     acc
                     (let [other (some-> (p/get-sentex (:records kb) oh) :sentence nm/functor)
                           edges (into [] (distinct)
                                       (cond-> (vec (checks/edge-support kb pred via context))
                                         (and (symbol? other) (not= other pred))
                                         (into (checks/edge-support kb other via context))))
                           antes (map #(into [%] edges)
                                      (sort (tax/prop-supporters tax :anti-symmetric via)))]
                       (reduce (fn [acc a-list]
                                 (merge-with into acc
                                             (derive-equality kb a b context 'anti_symmetric
                                                              (into [handle oh] a-list))))
                               acc antes))))
                 {:new [] :superseded [] :violations []}
                 converses)))))))))

(defn- anti-symmetric-mark-relevant?
  "The antisymmetric twin of `functional-mark-relevant?`: could `sentence`'s own
  functor, or something it descends from, carry an `anti_symmetric` mark?  One unscoped
  `tax/props-over` read — no `functionalInArg` twin exists for this mark, so this is
  the whole of the check."
  [tax sentence]
  (let [f (nm/functor sentence)]
    (and (symbol? f) (seq (tax/props-over tax :anti-symmetric f)))))

(defn derive-antisymmetric-equalities
  "`derive-antisymmetric-equalities-in`, run from `context` and from every reader that
  can see it — the antisymmetric twin of `derive-functional-equalities`'s own wrapper,
  same reachability (`tax/context-down`), same two-gate shape (KB-wide, then
  `anti-symmetric-mark-relevant?` per fact before the closure read), same reason: two
  mutually-blind contexts each holding one direction of a converse pair merge only from
  a reader below both, and a context edge alone (`antisym-equate-under-context-edge`) is
  not the only way that reader comes to exist — the *facts* can just as well be the last
  of the three to arrive, into a topology the edges already connect.

  `readers` narrows the sweep exactly as it does in the functional twin, is passed by the
  same one caller, and rests on the same argument — read that docstring for it.  The two
  take the argument together because `equate-under-context-edge-via` hands it to whichever
  `derive` it was given: one twin narrowing and the other not would be the drift the
  shared body exists to prevent."
  ([kb sentence context handle] (derive-antisymmetric-equalities kb sentence context handle nil))
  ([kb sentence context handle readers]
   (let [tax (reasoning/taxonomy kb)]
     (when (seq (tax/props tax :anti-symmetric))
       (if (anti-symmetric-mark-relevant? tax sentence)
         (reduce (fn [acc r]
                   (merge-with into acc (derive-antisymmetric-equalities-in kb sentence r handle)))
                 {:new [] :superseded [] :violations []}
                 (cond->> (tax/context-down tax context)
                   readers (filter readers)))
         (derive-antisymmetric-equalities-in kb sentence context handle))))))

(defn antisym-equate-existing
  "When an `(anti_symmetric P)` declaration arrives, derive the equalities P's **already
  stored** facts license — the twin of `equate-existing`, over the antisymmetric merge.
  Sweeps the whole spec subtree beneath `P` (the mark descends), and hands each stored
  fact back to `derive-antisymmetric-equalities`, so the two arrival directions cannot
  drift about what a converse licenses or what justifies the merge.  nil when `sentence`
  declares nothing antisymmetric."
  [kb sentence]
  (when (and (= 'anti_symmetric (nm/functor sentence)) (= 1 (nm/arity sentence)))
    (equate-declared-subtree kb (first (nm/args sentence))
                             derive-antisymmetric-equalities)))

(defn antisym-equate-under-edge
  "When a `(genl sub super)` edge arrives, derive the equalities an `(anti_symmetric …)`
  mark above `super` now licenses over the `(sub …)` facts already stored — the twin of
  `equate-under-edge`.  Free for a KB declaring nothing antisymmetric, decided before the
  subtree is read.  nil when `sentence` is not a `genl` edge."
  [kb sentence]
  (equate-under-edge-via kb sentence
                         #(seq (tax/props % :anti-symmetric))
                         derive-antisymmetric-equalities))

(defn- context-edge-reader-ancestors
  "Every context a `(genlCx sub super)` edge's widened readers can see, once the edge
  has integrated — `context-down(sub)`'s own members' ancestor sets, unioned.  The exact
  reachability `migrate-under-context-edge` computes for the same trigger (above): a
  merge's restatement and a functional/anti_symmetric clash are the same kind of event —
  a fact becoming newly visible to a reader — so the two share the reachability rule.

  `context-up(super)` alone would be a strict subset and not enough on its own: `sub`
  is a member of `context-down(sub)` (that closure always includes its own root), so
  `context-up(sub)` is one of the sets this unions — and after the edge integrates it
  already reaches everything `context-up(super)` does, by transitivity.  What it adds
  beyond that subset is every *other* reader whose ancestor set also runs through `sub` — a
  context wired under `sub` before this edge arrived gained the same new visibility
  the edge gives `sub` itself, and a candidate fact stored in *its* own pre-existing
  ancestor set can newly clash with something in `super`'s ancestor set exactly as one stored in
  `sub`'s own ancestor set can."
  [tax sub]
  (into #{} (mapcat #(tax/context-up tax %)) (tax/context-down tax sub)))

(defn- stored-facts-in-ancestors
  "Stored, positive, non-rule sentexes across `contexts`, kept when `marked?` admits
  them — the ancestor-set-scoped analogue of `subtree-sentexes`' spec-subtree walk, over
  contexts instead of predicates, and lazy for the same reason: a budgeted caller
  realizes only its prefix, and a context cycle can make an ancestor set the whole graph.

  Reimplemented here rather than sharing `vaelii.impl.settle`'s own ancestor set walkers
  (`believed-in-ancestors`, `constraint-facts-in-ancestors`), for two reasons.  `settle` already
  requires `special`, so the reverse would be a namespace cycle.  And those are
  **belief**-filtered, where this deliberately is not, for `equate-existing`'s reason:
  an equality derived off a defeated fact rests on that fact and is defeated with it,
  so skipping a defeated candidate here would leave a revival's merge missing —
  `derive-functional-equalities`/`-in` read the store, never the belief filter, and
  this feeds them, so it has to agree."
  [kb contexts marked?]
  (let [tax (reasoning/taxonomy kb)]
    (for [c     (filter symbol? contexts)
          h     (reads/as-stored-in-context (:index kb) c)
          :let  [s (p/get-sentex (:records kb) h)]
          :when (and s (nil? (:antecedent s)) (not (sx/negative? s))
                     (sequential? (:sentence s))
                     (marked? tax (:sentence s)))]
      s)))

(defn- budgeted-context-edge-candidates
  "Up to `tax/*exposure-instance-budget*` stored, positive, non-rule sentexes drawn from
  the ancestor set `(genlCx sub super)` widens, kept when `marked?` admits them — the shared
  shape `equate-under-context-edge` and `antisym-equate-under-context-edge` fold
  `derive-functional-equalities` / `derive-antisymmetric-equalities` over — as
  `[candidates cut-budget-or-nil]`.

  **Scoped to the edge, not to the whole KB's marked-predicate roster.**  An earlier
  draft of this walk read every stored fact under every functional/functionalInArg-
  marked predicate anywhere in the KB, capped only by the budget — which meant the cap
  was reached by 'does *any* marked predicate anywhere exceed the budget', not by
  anything about the arriving edge, so on a KB past that size *every* subsequent
  `genlCx` edge paid the capped walk and risked a cut, including edges with nothing to
  do with the predicate that put the KB over the line.
  `context-edge-reader-ancestors` fixes that: the candidate set is what this edge actually
  makes newly relevant, so an edge between two small, unrelated contexts costs what it
  actually touches, and an unrelated predicate's extent can no longer spend this edge's
  budget.

  **What it does not fix is the cut's own order-dependence, and that is stated here
  rather than claimed away.**  `stored-facts-in-ancestors` enumerates
  `reads/as-stored-in-context` per ancestor set member, which is handle order, which is
  assertion order; `take` selects a *prefix* of that.  So once an ancestor set holds more
  candidates than the budget, which merges this edge derives is still a function of when
  the facts arrived — the same content in a different order merging in one ordering and
  not the other, which is an order-independence residual and not merely a completeness
  gap.  Sorting the ancestor set to content order would remove it and is refused for the reason
  `tax/*exposure-instance-budget*` measures: the sort forces the whole extent, which is
  the cost the cap exists to refuse, and a context cycle makes the ancestor set the graph.  So
  the residual is left, and it is left **named** — the caller files
  `:context-edge-exposure-truncated` whenever the cut happens, so no reader has to infer
  from silence that the sweep was complete.  Below the cap, which is every KB that has
  not put >`*exposure-instance-budget*` marked facts in one ancestor set, the sweep is exact and
  the invariant holds outright.

  **The cap still bounds the derive calls, not the enumeration itself.**  Unlike the
  eager `subtree-sentexes` an unscoped walk would have to accept in full,
  `stored-facts-in-ancestors` is lazy, so `take` here genuinely stops the read early rather
  than merely capping what gets handed to `derive-functional-equalities` afterward —
  what remains bounded-but-real is `derive-functional-equalities` itself, since that
  function now sweeps every reader below its context, a closure read per candidate.  `constraint-exposure-context-edge` measures exactly this — 8x the facts
  the ancestor set holds must cost the same past the cap.

  Sharing `*exposure-instance-budget*` with `vaelii.impl.settle`'s exposure passes
  rather than inventing a second knob: both are 'how much work will one genlCx edge's
  cross-context sweep spend', and a KB operator wants one dial for that, not two that
  can drift apart.

  **The residual this leaves is narrower than `settle`'s own, and stated here
  plainly.**  A pair `settle`'s exposure pass cuts short goes undecided *this settle*
  and is remembered in `:clashes` for the next one to re-examine — this cap has a
  narrower second chance than that, not none: because the candidate set is now scoped
  to *this* edge's own ancestor set, a merge it misses is not automatically retried by an
  unrelated later edge the way the unscoped draft accidentally allowed, but a *later*
  `genlCx` edge widening the *same* ancestor set further would re-walk it and could still
  reach the pair.  That is why the caller files a violation naming the cut rather than
  treating it as routine — it is closer to `:exposure-truncated`'s honesty than to a
  bound with a guaranteed safety net behind it."
  [kb sub marked?]
  (let [tax    (reasoning/taxonomy kb)
        budget (max 0 (long tax/*exposure-instance-budget*))
        xs     (into [] (take (inc budget))
                     (stored-facts-in-ancestors kb (context-edge-reader-ancestors tax sub) marked?))]
    (if (> (count xs) budget)
      [(subvec xs 0 budget) budget]
      [xs nil])))

(defn- context-edge-exposure-truncation
  "The violation entry `equate-under-context-edge`/`antisym-equate-under-context-edge`
  file when `budgeted-context-edge-candidates` cuts short — never silently, matching
  every other bounded sweep in this KB."
  [sub mark budget]
  {:violation :context-edge-exposure-truncated
   :detail    {:context sub :mark mark :budget budget
               :message (str "genlCx edge into " sub " bounded its " (name mark)
                             " merge sweep at " budget " instances; some pairs the"
                             " widened ancestor set newly makes jointly visible may go"
                             " unmerged for this edge")}})

(defn- equate-under-context-edge-via
  "The body `equate-under-context-edge` and `antisym-equate-under-context-edge` share: a
  `(genlCx sub super)` edge arriving over facts a widened ancestor set newly makes jointly
  visible, with each candidate handed back to the family's `derive` in its own context,
  and the budget's cut reported as `prop`'s truncation rather than swallowed.

  `declares?` gates on the family being declared at all and `relevant?` narrows the ancestor set
  sweep to the facts a mark of it could actually reach — the two places the families
  differ, beside the derive and the truncation key.

  **`derive` is called with a fifth argument here and with four everywhere else**: the
  contexts `context-down(sub)` names, which are the readers whose ancestor set this edge
  changed.  Both twins take it and both narrow on it, since this body chooses neither.
  The candidate set is what the *budget* bounds and the reader set is what this bounds,
  and the two do not interact: `budgeted-context-edge-candidates` cuts a prefix of the
  facts, this cuts the contexts each surviving fact is re-derived at, and
  `genlcx_sweep_test` pins a forced truncation deriving the same pairs and filing the same
  notice either way.

  **Shared for `equate-under-edge-via`'s reason**, and more sharply: this is the budgeted
  entry point, so a copy that drifted would not merely miss merges but report a different
  coverage story for the same cut."
  [kb sentence declares? relevant? derive prop]
  (when (= 'genlCx (nm/functor sentence))
    (let [tax (reasoning/taxonomy kb)
          [_ sub super] sentence]
      (when (and (symbol? sub) (symbol? super) (declares? tax))
        (let [[candidates cut] (budgeted-context-edge-candidates kb sub relevant?)
              ;; the readers this edge actually changed the ancestor set of, computed once
              ;; and handed to every `derive` below rather than each one re-deriving the
              ;; whole reader fan of its candidate's own context
              widened (set (tax/context-down tax sub))
              result (reduce (fn [acc sx]
                               (merge-with into acc
                                           (derive kb (:sentence sx) (:context sx) (:id sx)
                                                   widened)))
                             {:new [] :superseded [] :violations []}
                             candidates)]
          (cond-> result
            cut (update :violations conj
                        (context-edge-exposure-truncation sub prop cut))))))))

(defn equate-under-context-edge
  "When a `(genlCx sub super)` edge arrives, derive the equalities a `(functional …)`
  mark already licenses over facts the widened ancestor set newly makes jointly visible — the
  fourth arrival order of the same three ingredients, and the context twin of
  `equate-under-edge`.

  **The context twin of `equate-under-edge`'s shape, over an ancestor set instead of a
  subtree**: sweep the stored facts `context-edge-reader-ancestors` says this edge newly
  makes relevant, kept when `functional-mark-relevant?` admits their functor, and hand
  each back to `derive-functional-equalities` **at its own storage context**, exactly
  as `equate-under-edge` already does.  What makes that correct here is that
  `derive-functional-equalities` no longer answers only for the context it is handed —
  it sweeps every reader below that context too (`tax/context-down`), which is what
  reaches a joining context this edge just connected without this arm needing a second,
  independent reachability computation of its own.  Before that wrapper existed, this
  function *was* that computation, reading each candidate's visibility here instead of
  leaving it to the callee — one caller's worth of correctness-sensitive logic that a
  second caller (the plain fact-arrival trigger, which has exactly the same problem
  when the topology is wired *before* the facts arrive rather than after) could not
  share.  Centralizing it is what let both shrink back to this shape.

  **Still `genlCx`-triggered and still necessary**, not redundant with the wrapper's own
  sweep: a `genlCx` edge arriving *after* both facts are already stored changes no
  fact and fires no ordinary assert, so nothing else re-invokes `derive-functional-
  equalities` for either of them — this arm is what does, over the extent
  `context-edge-reader-ancestors` names.  Gated identically to `equate-under-edge` at the
  top: free for a KB that declares nothing functional and nothing functionalInArg,
  decided before the ancestor set is read.

  **Budgeted, unlike `equate-under-edge`.**  A `genl` edge's own subtree is bounded by
  real vocabulary growth — the edge names the very predicate whose subtree is swept, so
  a big walk means a big subtree the edge itself accounts for.  A `genlCx` edge names
  two *contexts*: `context-edge-reader-ancestors` scopes the walk to what this specific edge
  makes relevant, so an edge between two small, unrelated contexts no longer costs a
  KB-wide predicate's whole extent — but the ancestor set itself can still be large (a small
  edge into a context whose readers reach a genuinely huge, genuinely relevant store),
  so `budgeted-context-edge-candidates` still caps what reaches
  `derive-functional-equalities` at `tax/*exposure-instance-budget*` — the same knob
  `vaelii.impl.settle`'s exposure passes spend, so a cut here and a cut there answer to
  one dial — and files a `:context-edge-exposure-truncated` violation when it cuts,
  since a pair past the cap is not derived by anything else afterward this same edge
  (docs/equality.md).

  **Idempotent** for the reason every other direction is: `derive-functional-
  equalities` skips a pair `same-class-in?` already holds from a reader's own view, so
  reprocessing the same candidate on a later edge, or reaching the same reader through
  two different marked predicates, costs a repeated no-op read rather than a repeated
  merge.

  **Retracting the edge does not un-merge, and that is a pre-existing limitation of
  `derive-functional-equalities` rather than something owed here.**  Its antecedents
  name the declaration, the two facts, and any `genl` edges either spelling descended
  (`checks/edge-support`) — never a `genlCx` edge, because no arrival order needs a
  context edge in that list.  An equality this arm derives therefore rests on nothing
  that names the `genlCx` edge that made the pair jointly visible, and the same is
  already true of every other arrival order whenever a fact or a declaration arrives
  last under a `genlCx` edge asserted earlier: the merge outlives a later retraction of
  that edge exactly as it would here.  Closing it is a `genlCx`-support addition to
  `edge-support` and to the antecedent list `derive-functional-equalities` builds, not a
  gap this arrival order introduces or one its own addition should paper over."
  [kb sentence]
  (equate-under-context-edge-via
   kb sentence
   tax/functional-family-declared?
   functional-mark-relevant?
   derive-functional-equalities
   :functional))

(defn antisym-equate-under-context-edge
  "When a `(genlCx sub super)` edge arrives, derive the equalities an
  `(anti_symmetric …)` mark already licenses over facts the widened ancestor set newly makes
  jointly visible — the twin of `equate-under-context-edge`, over the antisymmetric
  merge and `anti-symmetric-mark-relevant?` in place of the functional one.  Same
  shape, same reasoning throughout — see `equate-under-context-edge`, including for why
  a later retraction of this edge does not un-merge what it derives."
  [kb sentence]
  (equate-under-context-edge-via
   kb sentence
   #(seq (tax/props % :anti-symmetric))
   anti-symmetric-mark-relevant?
   derive-antisymmetric-equalities
   :anti-symmetric))

(defn reconcile-context-edge
  "Everything a `(genlCx sub super)` edge means for the **equality** closure, in one
  call: the sentexes the widened ancestor set newly exposes to a standing merge
  (`migrate-under-context-edge`), and the two merges the same widening newly licenses
  (`equate-under-context-edge` for the functional family,
  `antisym-equate-under-context-edge` for the antisymmetric one).  Returns the usual
  `{:new :superseded :violations}`.  Safe on any sentence: each arm gates on the
  `genlCx` functor itself, so a non-edge costs three functor reads and returns the
  empty result.

  **One function because a `genlCx` edge arrives by three entry points, and only two of them
  remembered the list.**  An edge can be *asserted* (`core/assert-one`), *concluded* by
  a rule (`chain/place-fact-conclusion`), or **computed** — materialized by the
  structural producer off a `contextArgSubrelation` declaration with nobody asserting
  anything (`context-nat/materialize-edge`).  The first two spelled the trio out
  side by side and the third spelled none of it, so a calendar month→year edge posted
  the exception re-checks and ran no merge at all: two fillers of one functional slot,
  made jointly visible for the first time by that edge, stayed unmerged and
  uncontradicted, and asserting a single *irrelevant* stated edge afterwards repaired
  it (vaelii#56).  An entry point that has to remember a list is an entry point that forgets it — this
  is the list, and it is the only thing a fourth entry point has to call.

  **Not merged into the `genlCx` `:integrate` arm**, which would be the one place every
  entry point already passes through, for a timing reason that is not incidental: the arm runs
  from `integrate/sentex-added` and `derived-sentex-added` *before* the edge is
  justified, so the edge is a node nothing supports, `tax/context-up` and
  `tax/context-down` — belief-filtered like every closure here — have not widened yet,
  and all three sweeps would enumerate the pre-edge ancestor set and find nothing.  Chaining
  learned this first and says so at its own call site; the rule is the same one:
  reconcile *after* the justification, never beside the integrate arm.

  **nil when no arm did anything**, which is the shape each of them already returns and
  the one the fixpoint's `mig` gate reads: a conclusion re-derived on every round of
  every defaults pass must added no work rather than a little, so this collapses to nil
  rather than to an empty accumulator."
  [kb sentence]
  (let [cme (migrate-under-context-edge kb sentence)
        cfn (equate-under-context-edge kb sentence)
        cax (antisym-equate-under-context-edge kb sentence)]
    (when (or cme cfn cax)
      (merge-with into {:new [] :superseded [] :violations []} cme cfn cax))))

(defn- stored-declarations
  "Every **stored** sentex whose functor is `f`, believed or not.

  Read by the two passes that sweep what is *already there* — `rebuild-taxonomy`'s
  replay, and the `disjoint_metatype` arm picking up memberships asserted before the
  declaration — because both are recording supporters rather than deciding belief, and
  a supporter omitted here is one no later reconcile can find.

  Reading a belief-filtered store would quietly change what recovery means.
  Every cache follows the same discipline now: `:support` (genl/genlCx/equality)
  and `:cache-support` (disjoint, metatypes + members, props, inverse) are meant to
  record *every* asserting sentex, with `refresh-beliefs` deciding which entries are
  active.  Omit a disbelieved supporter and its handle is gone from the count, so
  clearing its defeat could never revive the entry — a defeated `(disjoint dog cat)`
  would then answer differently either side of a restart, and a disbelieved genl
  supporter's edge would be lost for good.

  So the taxonomy is rebuilt from what is stored, and `recover` applies belief to the
  replay afterwards (`tax/refresh-beliefs`), exactly as a settle applies it during normal
  operation.

  Stored, not believed — but **positive**: `sentexes-with-functor` returns both
  polarities, and a `(not (genl a b))` *opposes* the edge rather than asserting it.
  The rebuild arms read the positive shape positionally, so a negation would bind
  its inner sentence as a taxonomy node and nil as the other — and the assert path
  never routes one here either, since its dispatch reads the functor `not`."
  [kb f]
  (->> (reads/as-stored-with-functor (:index kb) f)
       (keep #(p/get-sentex (:records kb) %))
       (filter #(and (nil? (:antecedent %)) (not (sx/negative? %))))))

;; ---- the table -----------------------------------------------------------

(defn- commuting-args-group
  "The runtime group descriptor a `(commutativeInArgs P p1 p2 …)` sentence names, or nil
  when it names none.  **Sorted and deduped**, so the three arms below key on one value
  however the author wrote the positions: `(commutativeInArgs P 2 1)` installs and
  uninstalls the same entry `(commutativeInArgs P 1 2)` does, and a rebuild of either
  finds it.  Nil for a declaration naming fewer than two distinct positions, which
  `wff/commutative-in-args-problems` refuses at the entry point and `recover` may still
  replay from an older or foreign store."
  [sentence]
  (let [ps (vec (sort (distinct (drop 2 sentence))))]
    (when (and (symbol? (second sentence))
               (> (count ps) 1)
               (every? #(and (integer? %) (pos? %)) ps))
      [:args ps])))

(defn- prop-entry
  "The arms for a predicate-metadata mark — `(transitive P)`, `(symmetric P)`, … —
  which differ only in the `:props` key they maintain, and which they now read off
  `functor`'s declaration (`pr/prop-kind`) rather than take as a parameter.  Reading
  it is what lets `spec/::prop-kind` be derived from the declarations rather than from
  this table: a kind exists because a term declares it, not because an arm was written
  with it.

  `skip` is the set of predicates whose property is the engine's own to compute — the
  `closure-relations` genl / genlCx, whose transitivity comes off the cached closures.
  A `(transitive genl)` fact stays stored and queryable, but its prop is **not** marked,
  so `has-prop? :transitive genl` stays false and genl is never handed to the generic
  closure prover.  The skip is applied identically on integrate, disintegrate and
  rebuild, so the live and recovered stores agree.

  Why a mark that arrives by *derivation* must install like an asserted one is the
  `:derived` facet's argument, and it lives with the facet on `predicates/prop`."
  ([functor] (prop-entry functor nil))
  ([functor skip]
   (let [kind    (pr/prop-kind functor)
         marked? (fn [pred] (not (contains? skip pred)))]
     {:integrate    (fn [kb sx h] (let [pred (second (:sentence sx))]
                                    (when (marked? pred)
                                      (tax/mark-prop (reasoning/taxonomy kb) kind pred h (:context sx)))))
      :disintegrate (fn [kb sx] (let [pred (second (:sentence sx))]
                                  (when (marked? pred)
                                    (tax/unmark-prop! (reasoning/taxonomy kb) kind pred (:id sx)))))
      :rebuild      (fn [tax {[_ pred] :sentence id :id ctx :context}]
                      (when (marked? pred) (tax/mark-prop tax kind pred id ctx)))
      :wff          wff/prop-problems})))

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

  `wff/equality-problems` waves both compound shapes through the same way.

  The add arm is `integrate-equality-sentex`, named rather than written out here
  because the derivation path calls it too: a rule concluding one of the three merges
  like an asserted one, and it reaches the arm by that name for the reason stated
  there."
  {:integrate    integrate-equality-sentex
   ;; the merge (or rule) survives while any other sentex still asserts it; when the
   ;; last supporter goes the class splits (or the rule leaves) and
   ;; `refresh-supersessions` (at the next settle) gives the displaced spellings back —
   ;; which moves a census and a NAF judgement exactly as the merge moved them, so the
   ;; re-check trigger is owed on this side too
   :disintegrate (fn [kb sx]
                   (let [s (:sentence sx) [_ a b] s]
                     (cond
                       (rewrite/schematic-equation? s)
                       (do (tax/del-rewrite-rule! (reasoning/taxonomy kb) (:id sx))
                           (recheck-equality-edge kb))
                       (sequential? b) nil
                       :else
                       (do (tax/del-equality! (reasoning/taxonomy kb) a b (:id sx))
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
  no arm at all, which is a typo.  `:mismatch` says which — `:partial-cache-triple`
  or `:no-arm` — the same discriminant every other `:bad-table-entry` in the tree
  carries, so a caller reads one key rather than guessing from the message.  Returns
  `entries` unchanged so it can wrap the def."
  [entries]
  (doseq [[f spec] entries]
    (let [cache-arms [:integrate :disintegrate :rebuild]
          present    (filterv #(get spec %) cache-arms)]
      (when (and (seq present) (not= (count present) (count cache-arms)))
        (throw (ex-info (str "special-predicate table entry for " f " is asymmetric: has "
                             (str/join ", " (map name present)) " but not "
                             (str/join ", " (map name (remove (set present) cache-arms)))
                             " — an add arm without its removal and rebuild halves leaks")
                        {:type     :bad-table-entry
                         :mismatch :partial-cache-triple
                         :functor  f
                         :present  (set present)
                         :missing  (vec (remove (set present) cache-arms))})))
      (when-not (or (:wff spec) (seq present))
        (throw (ex-info (str "special-predicate table entry for " f " has no arm at all"
                             " — an entry carries a :wff arm, the cache triple"
                             " :integrate / :disintegrate / :rebuild, or both; it holds "
                             (pr-str (vec (sort (keys spec)))))
                        {:type :bad-table-entry :mismatch :no-arm :functor f})))))
  entries)

(defn- defn-wff-problems
  "The `:wff` arm for the three `defn*` collection definitions — the member-variable
  check (`sx/defn-condition-problems`), read in the table's `[tax sentence context]` shape."
  [_tax sentence _context]
  (sx/defn-condition-problems sentence))

(def ^:private ^:dynamic *edge-replay-skips*
  "Bound by `rebuild-taxonomy` to a volatile the genl / genlCx `:rebuild` arms bump each
  time `replay-edge` drops a stored declaration that is not a well-formed edge.  Nil off
  the replay path, where `replay-edge` still guards but counts nothing."
  nil)

(defn- replay-edge
  "Replay one stored `genl` / `genlCx` declaration through `add` (`tax/add-genl` or
  `tax/add-genlCx`), but only when the stored sentence's **complete shape** is exactly
  `(expected-f <symbol> <symbol>)` — a valid two-endpoint taxonomy edge.

  `recover` replays the **stored** sentexes rather than the checked ones, and
  `stored-declarations` is a candidate read over the durable functor root, not proof that
  every returned sentence has the requested functor or the current WFF shape.  So a store
  an older, foreign, or stale writer left reaches here as a malformed edge, and reading it
  positionally (`[_ a b]`) reads three distinct malformations as a spurious edge:

    - a 2-element declaration (`(genl foo)`, a metatype membership, an `arity` / `arg`
      row) binds the member as `a` and nil as `b` — the nil enters the closure's node set,
      and `strong-components` throws on it (`java.util.ArrayDeque` rejects a null element)
      the moment `restore-depths` walks a loose relation (the `recover` crash of #80);
    - an **over-arity** row (`(genl a b surplus)`) binds `a` and `b` and silently discards
      the surplus, fabricating `(genl a b)` from a sentence that never was one;
    - a **wrong-functor** row (`(disjoint a b)` handed up under the genl root by a foreign
      or stale index) has symbols in both positions and would replay as `(genl a b)`.

  The last two both satisfy `(symbol? a) (symbol? b)`, so the endpoint-only guard passed
  them; requiring the whole shape — arity three, the literal expected functor, both
  endpoints symbols — is the producer boundary #80 drew, applied to the whole sentence.

  Dropping the malformed declaration is `rebuild-tms`'s discipline for a justification the
  store cannot root: the bad sentex is skipped and counted, never a spurious edge added.
  Returns tax."
  [add tax sentence expected-f id ctx]
  (if (and (= 3 (count sentence))
           (= expected-f (first sentence))
           (symbol? (second sentence))
           (symbol? (nth sentence 2)))
    (add tax (second sentence) (nth sentence 2) id ctx)
    (do (when-let [v *edge-replay-skips*] (vswap! v inc)) tax)))

(defn- cover-parts
  "The `[whole parts]` one `(covering W P …)`, `(separating W P …)` or `(partition W P
  …)` sentence declares, or nil when the stored sentence is not one.

  `recover` replays **stored** sentexes rather than checked ones, so a foreign or stale
  store reaches the rebuild arm with a two-element row or a non-symbol part, and reading
  it positionally would record a cover over nil.  The guard `replay-edge` applies to a
  taxonomy edge, applied to a roster: at least three elements, every one of them a
  symbol, and at least two distinct parts."
  [sentence]
  (let [[_ whole & parts] sentence]
    (when (and (>= (count sentence) 3)
               (symbol? whole)
               (every? symbol? parts)
               (> (count (distinct parts)) 1))
      [whole (distinct parts)])))

(defn- cover-arms
  "The integrate / disintegrate / rebuild triple the three whole-and-parts declarations
  share, differing only in `kind` — which of the two claims the roster makes
  (`tax/cover-kinds`).

  Each arm does two things, because the declaration says two things. The roster goes
  into the taxonomy under one key (`tax/add-cover`), which is what `disjointness-test`
  reads for a partition and what `CoveringProver` reads for either. And a `genl` edge
  per part goes in **against the covering sentex's own handle**, so the specialization
  the cover rests on is one the closure holds rather than one every reader has to
  re-derive: belief follows the declaration through the same supporter map an asserted
  edge uses, and retracting the cover drops the edges with it. The edges post the
  exception re-check the `genl` arm posts, for the reason that arm posts it.

  A part equal to the whole installs no edge — `wff/covering-problems` refuses the
  declaration, and the rebuild arm replays a store that never passed it."
  [kind]
  (letfn [(edges! [kb tax h ctx whole parts]
            (doseq [p parts :when (not= p whole)]
              (tax/add-genl tax p whole h ctx)
              (recheck-genl-edge kb p whole)))]
    {:integrate    (fn [kb sx h]
                     (when-let [[whole parts] (cover-parts (:sentence sx))]
                       (let [tax (reasoning/taxonomy kb) ctx (:context sx)]
                         (tax/add-cover tax whole parts kind h ctx)
                         (edges! kb tax h ctx whole parts))))
     :disintegrate (fn [kb sx]
                     (when-let [[whole parts] (cover-parts (:sentence sx))]
                       (let [tax (reasoning/taxonomy kb)]
                         (tax/del-cover! tax whole parts kind (:id sx))
                         (doseq [p parts :when (not= p whole)]
                           (tax/del-genl! tax p whole (:id sx))
                           (recheck-genl-edge kb p whole)))))
     ;; The rebuild arm takes `tax` alone, so it replays both halves and posts no
     ;; re-check — `recover` re-evaluates every exception after the replay rather than
     ;; per edge.
     :rebuild      (fn [tax {sentence :sentence id :id ctx :context}]
                     (if-let [[whole parts] (cover-parts sentence)]
                       (do (tax/add-cover tax whole parts kind id ctx)
                           (doseq [p parts :when (not= p whole)]
                             (tax/add-genl tax p whole id ctx))
                           tax)
                       (do (when-let [v *edge-replay-skips*] (vswap! v inc)) tax)))
     :wff          wff/covering-problems}))

(def ^:private arms
  "What the engine *does* about each functor it interprets, keyed by functor: the
  integrate / disintegrate / rebuild triple and the structural `:wff` check.

  A **map**, deliberately, where the table it feeds is an ordered vector: the order is
  the declaration's (`predicates/entries`), because it is a statement about the
  predicates rather than about the arms, and `rebuild-taxonomy` replays it.  Writing
  the arms in an order of their own would give the table two orders that had to agree
  and no way to notice when they stopped.

  What each functor *says* — its sentence shape, the `:props` kind it maintains,
  whether it runs on the derivation path — is not here; it is one entry in
  `vaelii.impl.predicates`, which sits below `taxonomy` and `wff` and so can be read
  by the layers this namespace cannot reach.  `entries` below joins the two and
  refuses a disagreement."
  (merge
   {;; the two transitive relations: closure edges, belief-tracked in the taxonomy.
    ;; Their arms post the exception re-check *edge* trigger — on the derivation path
    ;; as well as the assert path, so a rule-concluded edge re-checks the exceptions
    ;; too.
    'genl {:integrate    (fn [kb sx h]
                           (let [[_ a b] (:sentence sx)]
                             (tax/add-genl (reasoning/taxonomy kb) a b h (:context sx))
                             (recheck-genl-edge kb a b)))
           :disintegrate (fn [kb sx]
                           (let [[_ a b] (:sentence sx)]
                             (tax/del-genl! (reasoning/taxonomy kb) a b (:id sx))
                             (recheck-genl-edge kb a b)))
           :rebuild      (fn [tax {sentence :sentence id :id ctx :context}]
                           (replay-edge tax/add-genl tax sentence 'genl id ctx))
           :wff          wff/genl-problems}
    'genlCx {:integrate    (fn [kb sx h]
                             (let [[_ a b] (:sentence sx)]
                               (tax/add-genlCx (reasoning/taxonomy kb) a b h (:context sx))
                               ;; visibility moved: re-check the excepted rules whose
                               ;; firings live in the affected context ancestor set
                               ;; (`context-down` of the edge's sub) — the context-keyed
                               ;; twin of recheck-genl-edge — and the `except`-blocked
                               ;; derivations the same move may have released or newly
                               ;; blocked
                               (recheck-genlCx-edge kb a)
                               (recheck-except-ancestors kb)))
             :disintegrate (fn [kb sx]
                             (let [[_ a b] (:sentence sx)]
                               (tax/del-genlCx! (reasoning/taxonomy kb) a b (:id sx))
                               (recheck-genlCx-edge kb a)
                               (recheck-except-ancestors kb)))
             :rebuild      (fn [tax {sentence :sentence id :id ctx :context}]
                             (replay-edge tax/add-genlCx tax sentence 'genlCx id ctx))
             :wff          wff/genlCx-problems}
    'covering   (cover-arms :covering)
    'separating (cover-arms :separating)
    'partition  (cover-arms :partition)
    'disjoint {:integrate    (fn [kb sx h]
                               (let [[_ a b] (:sentence sx)]
                                 (tax/add-disjoint (reasoning/taxonomy kb) a b h (:context sx))))
               :disintegrate (fn [kb sx]
                               (let [[_ a b] (:sentence sx)]
                                 (tax/del-disjoint! (reasoning/taxonomy kb) a b (:id sx))))
               :rebuild      (fn [tax {[_ a b] :sentence id :id ctx :context}]
                               (tax/add-disjoint tax a b id ctx))
               :wff          wff/disjoint-problems}
    'disjoint_metatype
    {:integrate    (fn [kb sx h]
                     (let [[_ m] (:sentence sx)]
                       (tax/mark-disjoint-metatype (reasoning/taxonomy kb) m h (:context sx))
                       ;; Members already asserted are *recorded*, not turned into a
                       ;; clique of `(disjoint a b)` sentexes; `tax/disjoint?` consults
                       ;; the membership directly.  A member asserted later is picked up
                       ;; by the structural member arm in `integrate-sentex`.
                       ;;
                       ;; **Stored, not believed**, which is the discipline every other
                       ;; retroactive sweep here follows (`lift-existing`,
                       ;; `equate-existing`, `entail-existing`) and for a sharper reason:
                       ;; this one records a *supporter*.  The structural member arm is
                       ;; belief-blind, so a membership asserted after the declaration is
                       ;; counted whatever its label — and a belief-filtered sweep here
                       ;; would skip a defeated membership asserted *before* it, leaving
                       ;; that handle out of `:cache-handle-keys` entirely.  Clearing the
                       ;; defeat could then never revive the entry, since
                       ;; `moved-cache-keys` has no key to find: belief depending on the
                       ;; order the defeat and the declaration arrived in, and
                       ;; permanently.  It would also put the live KB and the recovered
                       ;; one at odds over one store, `rebuild-taxonomy`'s second pass
                       ;; reading what is stored through this very function.
                       (doseq [{[_ t] :sentence id :id mctx :context}
                               (stored-declarations kb m)]
                         (tax/add-metatype-member (reasoning/taxonomy kb) m t id mctx))))
     :disintegrate (fn [kb sx]
                     (let [[_ m] (:sentence sx)]
                       (tax/unmark-disjoint-metatype! (reasoning/taxonomy kb) m (:id sx))))
     ;; marks only: membership is replayed by rebuild-taxonomy's second pass, once every
     ;; metatype is known — the member functors are the metatypes themselves, which no
     ;; static table key can name
     :rebuild      (fn [tax {[_ m] :sentence id :id ctx :context}]
                     (tax/mark-disjoint-metatype tax m id ctx))
     :wff          wff/disjoint-metatype-problems}
    ;; `(sibling_disjoint C)` is the metatype clique keyed off the genl closure: only the
    ;; mark is stored, and `tax/disjoint?` reads C's specializations off `specs`.  So
    ;; there is no member sweep to run on integrate — unlike `disjoint_metatype`, nothing
    ;; was recorded to pick up — and the three arms are the plain mark/unmark, the shape
    ;; `disjoint` itself has.
    'sibling_disjoint
    {:integrate    (fn [kb sx h]
                     (let [[_ c] (:sentence sx)]
                       (tax/mark-sibling-disjoint (reasoning/taxonomy kb) c h (:context sx))))
     :disintegrate (fn [kb sx]
                     (let [[_ c] (:sentence sx)]
                       (tax/unmark-sibling-disjoint! (reasoning/taxonomy kb) c (:id sx))))
     :rebuild      (fn [tax {[_ c] :sentence id :id ctx :context}]
                     (tax/mark-sibling-disjoint tax c id ctx))
     :wff          wff/sibling-disjoint-problems}
    ;; `(siblingDisjointException x y)` exempts one pair the sibling clique or a
    ;; `disjoint_metatype` would separate — the plain add/drop `disjoint` has, keyed as
    ;; the same unordered pair.  Its **retract** is the one thing the generic belief
    ;; reconcile does not cover: if the exception was present ab initio, the pair it
    ;; exempted was admitted and never entered the clash set, so its departure has no
    ;; stored clash to re-derive.  The disintegrate arm posts the pair to
    ;; `:sib-exc-dirty`, and the settle's re-arm sweep (`settle/clash-candidates` /
    ;; `exposure-candidates`) drives `two-sided-reach` over it to convict the
    ;; memberships it now separates.
    'siblingDisjointException
    {:integrate    (fn [kb sx h]
                     (let [[_ a b] (:sentence sx)]
                       (tax/add-sib-exception (reasoning/taxonomy kb) a b h (:context sx))))
     :disintegrate (fn [kb sx]
                     (let [[_ a b] (:sentence sx)]
                       (tax/del-sib-exception! (reasoning/taxonomy kb) a b (:id sx))
                       (when-let [d (reasoning/sib-exc-dirty kb)] (swap! d conj #{a b}))))
     :rebuild      (fn [tax {[_ a b] :sentence id :id ctx :context}]
                     (tax/add-sib-exception tax a b id ctx))
     :wff          wff/siblingDisjointException-problems}
    ;; `(arity P n)` is read by the per-assert arity check, so it is cached like the
    ;; other declarations the engine interprets rather than re-queried per assertion.
    ;; No `:wff` arm: `wff/arity-problems` does not exist, because the arity of `arity`
    ;; is what would check it.
    'arity
    {:integrate    (fn [kb sx h]
                     (let [[_ pred n] (:sentence sx)]
                       (when (and (symbol? pred) (integer? n))
                         (tax/add-arity (reasoning/taxonomy kb) pred n h (:context sx)))))
     :disintegrate (fn [kb sx]
                     (let [[_ pred n] (:sentence sx)]
                       (when (and (symbol? pred) (integer? n))
                         (tax/del-arity! (reasoning/taxonomy kb) pred n (:id sx)))))
     :rebuild      (fn [tax {[_ pred n] :sentence id :id ctx :context}]
                     (when (and (symbol? pred) (integer? n))
                       (tax/add-arity tax pred n id ctx)))}
    ;; `(functionalInArg P n)` says the other arguments of `P` determine argument `n` —
    ;; `functional` generalized off its fixed arg-2 slot.  Cached exactly as `arity` is
    ;; and for the same reason: the definitional checks read it on every assert, and a
    ;; declaration is not something to re-derive per write.
    ;;
    ;; Registered here beside `arity` rather than through `prop-entry`, which cannot
    ;; carry the integer, and deliberately NOT the way `transitiveInArg` is: that one
    ;; licenses tuples and is read for the goal's own predicate, this one refuses them
    ;; and is read up the hierarchy (`tax/functional-in-arg-over`).  The two share a name
    ;; shape and sit on opposite sides of the prover/checker divide — the same line
    ;; `props-over`'s docstring draws, and the reason `functional` is absent from the
    ;; recheck table above.
    'functionalInArg
    {:integrate    (fn [kb sx h]
                     (let [[_ pred n] (:sentence sx)]
                       (when (and (symbol? pred) (integer? n) (pos? n))
                         (tax/add-functional-in-arg (reasoning/taxonomy kb) pred n h (:context sx)))))
     :disintegrate (fn [kb sx]
                     (let [[_ pred n] (:sentence sx)]
                       (when (and (symbol? pred) (integer? n) (pos? n))
                         (tax/del-functional-in-arg! (reasoning/taxonomy kb) pred n (:id sx)))))
     :rebuild      (fn [tax {[_ pred n] :sentence id :id ctx :context}]
                     (when (and (symbol? pred) (integer? n) (pos? n))
                       (tax/add-functional-in-arg tax pred n id ctx)))
     :wff          wff/functional-in-arg-problems}
    ;; The three commutativity relations.  `(commutativeInArgAndRest P f)` licences every
    ;; position from `f` to the literal's own arity to permute; `(commutativeInArgs P p …)`
    ;; licences exactly the positions named; `(commutative P)` licences every position,
    ;; which is the tail from position 1.  All three are cached for `arity`'s reason twice
    ;; over: the canonicalizer reads them on **every** assert, not only on a declaration,
    ;; so a re-query per write would be a read on the hottest path the engine has.
    ;;
    ;; One table between them, since the three written shapes are one runtime group
    ;; descriptor (`sentex/commuting-components`).  Registered here rather than through
    ;; `prop-entry`, which carries no position, and unlike `functionalInArg` these read
    ;; **down** to nothing: the mark is read off the literal's exact functor, because a
    ;; sentex has one key and a `genl` edge below a commutative predicate does not make
    ;; the sub-predicate commutative (`res/kb-sentex`, `tax/commuting-groups`).
    ;;
    ;; `commutative` installs its group **here**, beside the `:commutative` prop the mark
    ;; is queried by, rather than through a CxCore rule deriving `(commutativeInArgAndRest
    ;; P 1)`.  The two spellings state one licence, and a derivation between them is a
    ;; rule whose conclusion re-derives its own premise: the pair was written as a cycle
    ;; and the backward engine has no ancestor-goal guard to stop on it
    ;; (`provers/candidate-rules`).  Installing both marks at their own arms leaves the
    ;; canonicalizer one table to read and the resolution prover no cycle to walk, and the
    ;; equivalence stays in CxCore as two `set/inertRule`s that document it.
    'commutative
    {:integrate    (fn [kb sx h]
                     (let [pred (second (:sentence sx))
                           tax  (reasoning/taxonomy kb)]
                       (when (symbol? pred)
                         (tax/mark-prop tax (pr/prop-kind 'commutative) pred h (:context sx))
                         (tax/add-commuting tax pred [:rest 1] h (:context sx)))))
     :disintegrate (fn [kb sx]
                     (let [pred (second (:sentence sx))
                           tax  (reasoning/taxonomy kb)]
                       (when (symbol? pred)
                         (tax/unmark-prop! tax (pr/prop-kind 'commutative) pred (:id sx))
                         (tax/del-commuting! tax pred [:rest 1] (:id sx)))))
     :rebuild      (fn [tax {[_ pred] :sentence id :id ctx :context}]
                     (when (symbol? pred)
                       (tax/mark-prop tax (pr/prop-kind 'commutative) pred id ctx)
                       (tax/add-commuting tax pred [:rest 1] id ctx)))
     :wff          wff/prop-problems}
    'commutativeInArgAndRest
    {:integrate    (fn [kb sx h]
                     (let [[_ pred n] (:sentence sx)]
                       (when (and (symbol? pred) (integer? n) (pos? n))
                         (tax/add-commuting (reasoning/taxonomy kb) pred [:rest n] h (:context sx)))))
     :disintegrate (fn [kb sx]
                     (let [[_ pred n] (:sentence sx)]
                       (when (and (symbol? pred) (integer? n) (pos? n))
                         (tax/del-commuting! (reasoning/taxonomy kb) pred [:rest n] (:id sx)))))
     :rebuild      (fn [tax {[_ pred n] :sentence id :id ctx :context}]
                     (when (and (symbol? pred) (integer? n) (pos? n))
                       (tax/add-commuting tax pred [:rest n] id ctx)))
     :wff          wff/commutative-in-arg-and-rest-problems}
    'commutativeInArgs
    {:integrate    (fn [kb sx h]
                     (when-let [g (commuting-args-group (:sentence sx))]
                       (tax/add-commuting (reasoning/taxonomy kb) (second (:sentence sx))
                                          g h (:context sx))))
     :disintegrate (fn [kb sx]
                     (when-let [g (commuting-args-group (:sentence sx))]
                       (tax/del-commuting! (reasoning/taxonomy kb) (second (:sentence sx))
                                           g (:id sx))))
     :rebuild      (fn [tax {sentence :sentence id :id ctx :context}]
                     (when-let [g (commuting-args-group sentence)]
                       (tax/add-commuting tax (second sentence) g id ctx)))
     :wff          wff/commutative-in-args-problems}
    'inverse {:integrate    (fn [kb sx h]
                              (let [[_ p q] (:sentence sx)]
                                (tax/add-inverse (reasoning/taxonomy kb) p q h (:context sx))))
              :disintegrate (fn [kb sx]
                              (let [[_ p q] (:sentence sx)]
                                (tax/del-inverse! (reasoning/taxonomy kb) p q (:id sx))))
              :rebuild      (fn [tax {[_ p q] :sentence id :id ctx :context}]
                              (tax/add-inverse tax p q id ctx))
              :wff          wff/inverse-problems}
    ;; the mark plus the retroactive lift; the lift's justifications need no removal arm
    ;; of their own — each is justified by this sentex, so the ordinary
    ;; dependency-directed sweep withdraws them when it goes.  The rebuild replays the
    ;; mark only: the lifted copies are already stored.  The integrate arm returns the
    ;; `{:new :violations}` the equality arms return, so a retroactively lifted copy is a
    ;; chaining seed like any other new content.  This is the one mark the declaration
    ;; withholds `:derived` from, and the reason is stated there.
    'decontextualized_predicate
    (assoc (prop-entry 'decontextualized_predicate)
           :integrate (fn [kb sx h]
                        (let [pred (second (:sentence sx))]
                          (tax/mark-prop (reasoning/taxonomy kb) :decontextualized pred h (:context sx))
                          (lift-existing kb pred h))))
    'forced_decontextualized_predicate (prop-entry 'forced_decontextualized_predicate)
    ;; `(target_following_predicate P)` marks P as forming a **target-following
    ;; meta-sentex**: a `(P … (sentexHandle H) …)` names sentex H and must not outlive it,
    ;; so a teardown that removes H removes the meta with it
    ;; (`core/retract-following-metas!`).  Belief-following and recover-safe like the
    ;; marks above.  koinii's reply acts (`answers` / `disputes` / `endorses` /
    ;; `justifies`) declare it, so retracting a claim cascades to the replies about it —
    ;; the property a message bus cannot give.  The engine's own meta-sentexes (`except`
    ;; / `exceptWhen`) deliberately do **not** carry it: a rule's exception orphans
    ;; harmlessly when the rule is retracted (`meta_sentex_test`), is roster-managed at
    ;; the removal choke point, and that amend-in-place behavior is correct as is — the
    ;; mark is opt-in precisely to leave it untouched.
    'target_following_predicate (prop-entry 'target_following_predicate)
    ;; `(abducible_predicate P)` is what lets abduction hypothesize a `(P …)` when a proof
    ;; dead-ends on one (docs/abduction.md).  Deliberately **not** decontextualized,
    ;; unlike the marks above it: `transitive` / `symmetric` are claims about a predicate
    ;; that hold wherever it is mentioned, while this is a *policy* of the context that
    ;; grants it — one theory may be willing to assume `was_washed` and another, reading
    ;; the same predicate, may not.  The scoped `has-prop?` arity is what reads it, so the
    ;; grant reaches exactly the contexts that see the grantor.
    'abducible_predicate (prop-entry 'abducible_predicate)
    ;; `(closed_extent_predicate P)` says P's **believed** extent is complete: where the
    ;; grant is visible, nothing answering `(P a)` at level 6 is what answers
    ;; `(not (P a))` (docs/naf.md).  Not decontextualized, and for `abducible_predicate`'s
    ;; reason — closing a vocabulary's extent is a *policy* of the theory that closes it,
    ;; so the scoped `has-prop?` arity reaches exactly the contexts that see the grant,
    ;; and a sibling theory reading the same predicate answers open-world as before.
    ;;
    ;; The arms are the mark plus the re-check postings the rules it newly governs need.
    ;; A rule asserted before the grant carries no posting for `P`, so nothing on `P`
    ;; would ever bring its firings back; the arms below close that from both arrival
    ;; orders, the way `recheck-arg-inferred` closes the same asymmetry for `arg`.
    'closed_extent_predicate
    (-> (prop-entry 'closed_extent_predicate)
        (assoc :integrate
               (fn [kb sx h]
                 (let [pred (second (:sentence sx))]
                   (tax/mark-prop (reasoning/taxonomy kb) :closed-extent pred h (:context sx))
                   (index-closed-extent-rules kb pred))))
        (assoc :disintegrate
               (fn [kb sx]
                 (let [pred (second (:sentence sx))]
                   (tax/unmark-prop! (reasoning/taxonomy kb) :closed-extent pred (:id sx))
                   (index-closed-extent-rules kb pred)))))
    ;; `(modal_predicate P)` is what makes `(P agent sentence)` project into the agent's
    ;; context (docs/belief.md) — `BeliefProjectionProver` reads it.  Not
    ;; decontextualized, and for `abducible_predicate`'s reason: which predicates a theory
    ;; reads modally is a *policy* of the context that grants it, so the scoped
    ;; `has-prop?` arity reaches exactly the contexts that see the grant.  `believes`
    ;; ships granted in CxCore; `knows` / `desires` / `intends` are one assertion away.
    'modal_predicate (prop-entry 'modal_predicate)
    ;; a NAT function's kind is predicate metadata like the marks above —
    ;; `(reifiable_function F)` marks `:reifiable`, `(unreifiable_function F)`
    ;; `:unreifiable`, belief-following through the same prop cache.  The reify gate
    ;; (`vaelii.impl.nat`) reads `:reifiable` in memory, so declaring a function reifiable
    ;; is what turns the reify pass on.  Their argument is a function name (a
    ;; `FruitFn`-shaped constant), so `prop-problems` — which refuses an individual — is
    ;; replaced by `function-decl-problems`.
    'reifiable_function   (assoc (prop-entry 'reifiable_function)   :wff wff/function-decl-problems)
    'unreifiable_function (assoc (prop-entry 'unreifiable_function) :wff wff/function-decl-problems)
    ;; `(quoting_function F)` marks `:quoting`: F's arguments are a **mention**, held
    ;; opaque to *identity* congruence — `res/representative-term` rewrites them by
    ;; spelling (`rewriteOf`) only, never by a `sameAs`/`equals` merge — so a quoted term
    ;; does not fold onto its referent's class.  Orthogonal to `:reifiable` /
    ;; `:unreifiable` (it governs argument opacity, not whether the application is
    ;; minted): `Quote` is reifiable + quoting, `Quasiquote` is unreifiable + quoting.
    'quoting_function     (assoc (prop-entry 'quoting_function)     :wff wff/function-decl-problems)
    ;; `(context_denoting_function F)` marks `:context-denoting`: a `Cx*Fn` whose ground
    ;; applications reify to a `cx/` **context** constant (rather than a `nat/` object
    ;; constant), so `(CxTimeFn CxMonad (DatetimeFn "2000"))` becomes a context a sentex
    ;; can be stored in and a `genlCx` node (docs/context-nat.md).  A reify-kind like
    ;; `:reifiable` — the nat gate turns on for it and the mint picks `cx/` by it — with
    ;; the same `function-decl-problems` wff, its argument being a function name.
    'context_denoting_function
    (assoc (prop-entry 'context_denoting_function) :wff wff/function-decl-problems)
    ;; `(contextArgSubrelation F pos R)` declares the structural genlCx ordering: two
    ;; `F`-contexts identical except at argument `pos` are ordered by sub-relation `R` on
    ;; that arg, so the producer materializes `(genlCx sub super)` when `R` holds
    ;; (docs/context-nat.md).  Read back through the index per producer run like the
    ;; correspondence declaration, so the entry is the wff arm alone.
    'contextArgSubrelation {:wff wff/context-arg-subrelation-problems}
    ;; `(functionCorrespondingPredicate F P N)` is read by the reify (both ways —
    ;; docs/nat.md), which reaches it through the index rather than a cache: the
    ;; declaration is consulted once per NAT, where the reify is already probing for a
    ;; `rewriteOf` target and a dedup, and the *gate* a KB declaring none pays is an O(1)
    ;; functor count.  So there is nothing to integrate, and the wff arm is the whole
    ;; entry.
    'functionCorrespondingPredicate {:wff wff/correspondence-problems}
    ;; The four argument constraints are consumed at match time — the declarations
    ;; themselves are read back through `matches-visible` per check, not cached — but
    ;; **which predicates are the subject of one** is marked, because a constraint binds
    ;; the tuples of every predicate beneath the one it names and the check therefore asks
    ;; that question per super-predicate on every assert (`tax/arg-declaration-props`,
    ;; `res/constraining-predicates`).
    'arg       (assoc (prop-entry 'arg)       :wff wff/arg-constraint-problems)
    'genlArg   (assoc (prop-entry 'genlArg)   :wff wff/arg-constraint-problems)
    'quotedArg (assoc (prop-entry 'quotedArg) :wff wff/arg-constraint-problems)
    'interArg  (assoc (prop-entry 'interArg)  :wff wff/inter-arg-constraint-problems)
    ;; the covering constraints type a whole tail at once — each marks its subject
    ;; predicate as declaring one, exactly as the four above, and validates its own form
    ;; through one arm reading both the two- and three-argument shapes
    'args           (assoc (prop-entry 'args)           :wff wff/covering-constraint-problems)
    'argsGenl       (assoc (prop-entry 'argsGenl)       :wff wff/covering-constraint-problems)
    'argAndRest     (assoc (prop-entry 'argAndRest)     :wff wff/covering-constraint-problems)
    'argAndRestGenl (assoc (prop-entry 'argAndRestGenl) :wff wff/covering-constraint-problems)
    ;; The two preservation declarations really are wff-only — read back per query, with
    ;; the transitivity of the relation they name checked here because `arg`'s open-world
    ;; reading cannot (docs/inherit.md).
    'transitiveInArg        {:wff wff/arg-preserving-problems}
    'transitiveInArgInverse {:wff wff/arg-preserving-problems}
    ;; the three definitional collection relations: stored as ordinary facts and expanded
    ;; into forward rules at assert (docs/defns.md), so the wff arm — the member-variable
    ;; check — is the whole table entry, exactly as it is for `transitiveInArg`, which is
    ;; likewise read back rather than integrated
    'defnNecessary  {:wff defn-wff-problems}
    'defnSufficient {:wff defn-wff-problems}
    'defnIff        {:wff defn-wff-problems}
    ;; `different` is never stored at all — its wff arm *is* the refusal
    'different      {:wff wff/different-problems}
    ;; ...and the query operators, never stored either, for the same reason: negation as
    ;; failure (docs/naf.md) and the five aggregates below, which are the same family and
    ;; take the same arm (docs/aggregate.md).  `forall` is sugar for a nested `unknown`
    ;; and is desugared at the rule entry point, so nothing ever stores one either.
    'unknown        {:wff wff/naf-problems}
    'thereExists    {:wff wff/naf-problems}
    'forall         {:wff wff/naf-problems}
    ;; `bravely` / `cautiously` read the current dilemmas (in every optimal labeling, in
    ;; some) and are answered by the opt-in :brave-cautious prover — never stored, for the
    ;; same reason the aggregates are not: a stored one is a computed value nothing keeps
    ;; current (docs/labeling.md).
    'bravely        {:wff wff/brave-cautious-problems}
    'cautiously     {:wff wff/brave-cautious-problems}}
   ;; the eight predicate-metadata marks, each differing only in the `:props` kind its
   ;; declaration names.  `commutative` is the ninth mark and is **not** here: it
   ;; maintains a `:props` kind like these and a commuting group besides, so its arms are
   ;; written out above rather than built by `prop-entry`.
   ;;
   ;; `anti_symmetric` and `anti_transitive` sit in the same list as
   ;; the six below them because the kind is read off the declaration: theirs are the two
   ;; functors whose keyword is not their own spelling (`anti_transitive` stores under
   ;; `:anti-transitive`), so converting the functor would put them somewhere else
   ;; (`pr/prop-kind`, and the pairing at `predicates/prop-marks`).
   ;; `(anti_symmetric P)` derives `(equals a b)` from a believed converse
   ;; (`derive-antisymmetric-equalities`); `(anti_transitive P)` convicts the two-step
   ;; chain and the direct step together (`checks/antitransitivity-problems`).  The mark
   ;; is what both of those read, and reading it up the predicate hierarchy
   ;; (`tax/props-over`) is what makes a `parentOf` mark convict a `fatherOf` chain.
   (into {} (map (fn [f] [f (prop-entry f tax/closure-relations)]))
         '[transitive symmetric asymmetric reflexive functional irreflexive
           anti_symmetric anti_transitive])
   ;; the three equality relations share one entry-shape
   (into {} (map (fn [f] [f equality-entry])) kb/equality-predicates)
   (into {} (map (fn [f] [f {:wff wff/naf-problems}])) (keys sx/aggregate-functors))))

(defn- declared-half
  "The half of a table entry `vaelii.impl.predicates` owns: the `:props` kind a mark
  maintains, and whether the entry's arms run on the derivation path as well as the
  assert path.

  Both are statements about the *predicate* — a mark that arrives by derivation must
  install like an asserted one; a kind exists because something declares it — rather
  than about the functions, which is why they are read off the declaration rather than
  written beside the arms.  The whole argument for each sits on the facet in
  `predicates`."
  [term]
  (cond-> {}
    (pr/prop-kind term)         (assoc :prop (pr/prop-kind term))
    (contains? pr/derived term) (assoc :derived? true)))

(defn check-declarations
  "Refuse a table whose arms and declarations disagree — the cross-layer half of
  `check-entries`, which sees only the arms and so can only check that they mirror each
  other.  Three disagreements are refused, all at namespace load:

  * a functor with arms and no declaration, or a declaration and no arms.  The two are
    one enumeration now, and a functor in only one of them is a predicate the engine
    either interprets without saying so or says something about and does nothing with.
    `arm-functors` is the set of functors the `arms` map keys, read **before** `entries`
    filters to `pr/in-special-table` — so an arm keyed on a functor no declaration places
    in the table is refused here rather than left out of the join unreported.  The
    one-argument arity reads the functors off `entries` itself, for a caller driving the
    validator over a hand-built table.
  * a `:cached` declaration whose arms have no cache triple, or the reverse.
  * a `:checked` declaration whose arms have no `:wff`, or the reverse.

  `check-entries` catches a *missing* arm; neither validator can catch an arm attached
  to the wrong functor, which is what `special_table_test` and `predicates_test` are
  for.  Two validators at two layers, each checking what it can see: they are not to be
  merged.

  One `:type` between them — `:bad-table-entry`, discriminated by `:mismatch` — for the
  reason `check-entries` already gives itself two shapes under one word: whichever way
  the table is bad, the caller catching it is the namespace load, and there is nothing
  a second keyword would let that caller do."
  ([entries] (check-declarations entries (set (map first entries))))
  ([entries arm-functors]
   (let [unarmed    (vec (sort (remove arm-functors pr/in-special-table)))
         undeclared (vec (sort (remove pr/in-special-table arm-functors)))]
     (when (or (seq unarmed) (seq undeclared))
       (throw (ex-info (str "the special-predicate arms and the declarations in"
                            " vaelii.impl.predicates enumerate different functors —"
                            " declared with no arms: " (pr-str unarmed)
                            "; armed with no declaration: " (pr-str undeclared))
                       {:type       :bad-table-entry
                        :mismatch    :enumeration
                        :unarmed     unarmed
                        :undeclared  undeclared})))
     (doseq [[f spec] entries]
       (let [cached?  (contains? pr/cached f)
             checked? (contains? pr/checked f)]
         (when (not= cached? (boolean (:integrate spec)))
           (throw (ex-info (str "special-predicate " f " is declared "
                                (if cached? "" "un") "cached but its arms "
                                (if cached? "have no" "have a") " cache triple")
                           {:type :bad-table-entry :mismatch :cached :functor f})))
         (when (not= checked? (boolean (:wff spec)))
           (throw (ex-info (str "special-predicate " f " is declared "
                                (if checked? "" "un") "checked but its arms "
                                (if checked? "have no" "have a") " :wff arm")
                           {:type :bad-table-entry :mismatch :checked :functor f})))))
     entries)))

(def entries
  "The special-predicate dispatch table: an **ordered** vector of `[functor spec]`
  pairs, joined from the arms above and the declarations in `vaelii.impl.predicates`.

  **The order is the declaration's** — `predicates/entries` filtered to the functors
  this table holds an entry for.  `rebuild-taxonomy` replays it top to bottom and a
  rebuild arm may read what an earlier one wrote (metatype membership reads the marks;
  nothing else is order-sensitive today, and keeping the assert path's traditional
  order adds no work), so the order is content and belongs with the other content.

  This vector is *the* functor enumeration the four walks use: integrate,
  disintegrate, rebuild and wff all walk it, so a predicate declared and armed is added
  to all four at once, `check-entries` refuses it half-armed and `check-declarations`
  refuses it armed without being declared — the latter reading the `arms` map keys, which
  hold every armed functor, not this filtered vector, which by construction holds only the
  declared ones.  `table` below is the lookup view."
  (-> (into [] (comp (map first)
                     (filter pr/in-special-table)
                     (map (fn [f] [f (merge (declared-half f) (arms f))])))
            pr/entries)
      check-entries
      (check-declarations (set (keys arms)))))

(def table
  "`entries` as the lookup map the walks below dispatch through."
  (into {} entries))

;; ---- the table walks -----------------------------------------------------

(defn wff-problems
  "Structural well-formedness problems for `sentence` (empty if OK) — the `:wff`
  column of the table, walked.  A sentence whose functor has no entry (or no `:wff`
  arm) is structurally unconstrained here; its argument *types* are still checked
  by the arg constraints.

  `context` is the asserting (or, on the derivation path, the landing) context, passed
  to every arm.  Today only `wff/disjoint-problems` reads it — to scope its
  genl-relatedness check to the edges that context sees (#92); the rest are
  context-free structural checks and ignore it."
  [tax sentence context]
  (if-let [wf (:wff (get table (and (sequential? sentence) (first sentence))))]
    (wf tax sentence context)
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
  is a fixpoint and must not abort halfway through one.

  `context` is the context the derived sentence lands in, scoping the same
  genl-relatedness read the assert path scopes (#92)."
  [kb sentence context]
  (wff-violation* kb sentence context))

(defn- structural-integrate
  "The **structural** integrate arms — the ones no functor can key, dispatched on the
  sentence's *shape* instead: a rule (any functor can head an implication), an
  exceptWhen meta-sentex (its second argument is a `(sentexHandle H)`), a visibility
  `except`, and a disjoint metatype's member (the functor is the metatype itself,
  known only at runtime).  Shared by `integrate-sentex` (the assert path),
  `integrate-twin` (migration) and `derived-sentex-added` (the derivation path), so a
  migrated rule / meta twin and a rule-derived except reach exactly the indexing an
  asserted one does.

  `derived?` drops the **rule** arm and nothing else.  The derivation path's own caller
  posts a stamped rule by name and before it justifies it (`chain/mint-rule` ->
  `index-rule-sentex`), because a mint is dispatched as a rule rather than as a fact and
  never reaches here; running the arm again would post the same rule twice and mark it
  for a second blanket re-check.  Every other arm is content the derivation path can
  reach only through this walk."
  ([kb sentex handle] (structural-integrate kb sentex handle false))
  ([kb sentex handle derived?]
   (let [sentence (sx/sentence-of sentex)
         f        (nm/functor sentence)]
     (cond
       ;; an exceptWhen meta-sentex names a rule it qualifies — register it in the
       ;; re-check index under that rule
       (sx/exceptWhen-meta? sentence)  (index-exceptWhen-meta kb sentex)
       ;; a visibility `(except (sentexHandle H))` fact: queue the firings that use H
       ;; so settle sweeps any conclusion now resting on an invisible antecedent
       (= sx/except-functor f)         (do (recheck-except kb sentex)
                                           (reconcile-belief-change kb #{handle}))
       ;; a rule reaching the general path (e.g. rebuilt by recover, or a migrated
       ;; twin) is indexed from its own record, so it keeps the direction its wrapper
       ;; gave it
       (and (not derived?)
            (rules/rule-sentence? sentence)) (index-rule-sentex kb handle sentex)
       ;; a member (M T) of a disjoint metatype: record T's membership, which is what
       ;; makes it disjoint from every other member.  Recording is O(1) and reversible;
       ;; asserting a `(disjoint t o)` per existing member would be O(n) sentexes per
       ;; member — quadratic overall — and premises no retraction could reach.
       ;; Gated on the mark being **stored**, not believed: the membership is a
       ;; supporter, and belief follows it through `refresh-cache-support` — a member
       ;; stated while the mark is defeated is recorded now and separates the moment
       ;; the mark revives, in either order of arrival.
       (and (= 1 (nm/arity sentence)) (tax/stored-disjoint-metatype? (reasoning/taxonomy kb) f))
       (tax/add-metatype-member (reasoning/taxonomy kb) f (first (nm/args sentence)) handle
                                (:context sentex))))))

(defn- run-integrate-arms
  "Run the one integrate arm that fits `sentex`: the table `:integrate` arm for a
  special functor, else the structural arm.  Shared by `integrate-sentex` (assert
  path) and `integrate-twin` (migration), so the dispatch lives in one place."
  [kb sentex handle]
  (if-let [e (get table (nm/functor (sx/sentence-of sentex)))]
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
  rule index or it never fires.  So this runs the same arms `integrate-sentex` does,
  where `derived-sentex-added` (the forward-chaining conclusion path) narrows the table
  half to the `:derived?` entries and drops the rule arm its own caller posts by name.

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
  (let [sentence (sx/sentence-of sentex)]
    (when-not (kb/equality-sentence? sentence)
      (run-integrate-arms kb sentex handle))
    (recheck-on-sentence kb sentence)))

(defn disintegrate-sentex!
  "The mirror walk: reverse a departing sentex's cache effects through the
  `:disintegrate` column, or the matching structural arm.  Every cache below is
  reference-counted on the departing sentex's id, so an entry survives while
  another sentex still asserts the same claim."
  [kb sentex]
  (let [sentence (sx/sentence-of sentex)
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
                           (rules/consequent-index-pred sentex))
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
          (swap! (reasoning/refused kb) dissoc (:id sentex)))
      ;; a member leaving a disjoint metatype: it stops being disjoint from the rest.
      ;; Gated on storage like the integrate arm, so a member retracted while the mark
      ;; is defeated drops its support entry rather than leaving it behind for good.
      (and (= 1 (nm/arity sentence)) (tax/stored-disjoint-metatype? (reasoning/taxonomy kb) f))
      (tax/del-metatype-member! (reasoning/taxonomy kb) f (first (nm/args sentence)) (:id sentex)))))

(defn integrate-transitive
  "The **table** half of `derived-sentex-added`: for a functor the table keys, only the
  arms flagged `:derived?` — the genl / genlCx closure edges, and the marks that carry
  the flag for their own reasons — run for a rule-derived conclusion, because the rest
  of integration either does not apply to a derived sentex or would re-enter `assert`
  from inside forward chaining.  Without this on the derivation path, a rule concluding
  `(genl a b)` stored and believed the sentex while the taxonomy never learned the edge
  — and `recover`, which reads the store, then disagreed with the running KB about what
  the KB entailed.  (A derived *equality* is not reached from here:
  `chain/place-fact-conclusion` calls `integrate-equality-sentex` by name, because this
  fn discards what an arm returns and there the return value is the work — the twins and
  the violations.)  A functor the table does **not** key is the structural walk's, not
  this one's."
  [kb sentex handle]
  (let [e (get table (nm/functor (:sentence sentex)))]
    (when (:derived? e)
      ((:integrate e) kb sentex handle))))

(defn derived-sentex-added
  "The derivation-path add choke point: everything that must happen because a
  **derived** sentex landed in the store — the integration arms a derived sentex may
  reach, and the exception re-check post, since a derived fact is a re-check trigger
  like an asserted one (an exception may be stated over a predicate that only ever
  arrives by inference — the cried-wolf case, where `liar` is concluded by another
  rule).

  **The dispatch is `run-integrate-arms`'s, narrowed.**  A functor the table keys runs
  its `:integrate` arm iff the entry is flagged `:derived?` (`integrate-transitive`);
  a functor it does not key runs the structural walk, minus the rule arm the caller
  posts by name (`structural-integrate`'s `derived?`).  Both halves have to be here or
  the derivation path reaches a strictly smaller set of caches than `recover`'s rebuild
  does, and the running KB and the restarted one then disagree about one store: a rule
  concluding a disjoint metatype's member separated nothing until a restart replayed it,
  and a rule-derived `(except (sentexHandle H))` hid its target from the *reads* — the
  roster is written at the store primitive (`kb/note-excepted!`) — while no firing that
  used H was ever queued for the sweep.

  **The except arm's `reconcile-belief-change` is called inline, mid-fixpoint, and
  that is safe.**  Neither half of it re-enters chaining or settling:
  `tax/note-supporter-visibility-change!` is one `swap!` bumping a generation, and
  `tax/refresh-beliefs` is a `swap!` over the taxonomy that reads `jtms/in?` and writes
  cache entries — no assert, no chain, no settle, and no relabel.  It is scoped to the
  arriving except and the handle it hides, so it costs two handles' worth of edge
  lookups rather than the vocabulary's.  `recheck-except` beside it only pushes rule
  handles onto the re-check queue, which is what the settle around this drains; that is
  exactly what the assert path does from inside its own `integrate-sentex`.

  The one ordering difference from the assert path is that `mark-premise` runs *before*
  `integrate/sentex-added`, where two of this fn's four callers run it before the
  justification — so the except is stored, rostered and generation-bumped a few lines
  ahead of being believed.  Nothing reads a scoped taxonomy answer in that window (the
  callers write a justification and nothing else), and the JTMS labels the region as the
  justification lands, so the first read after it recomputes against settled belief.

  Lives here rather than beside `sentex-added` in `vaelii.impl.integrate` because
  the equality arms are themselves derivation sites: a migrated twin and a
  functional-inferred `equals` are derived sentexes, and hand-rolling this pair at
  those sites is exactly the copy-paste the choke points exist to end.  Callers:
  forward chaining's `place-conclusion`, the `decontextualized_predicate` lift, the
  argument-constraint entailment, and `derive-equality`."
  [kb sentex handle]
  (let [sentence (sx/sentence-of sentex)]
    (if (contains? table (nm/functor sentence))
      (integrate-transitive kb sentex handle)
      (structural-integrate kb sentex handle true))
    (recheck-on-sentence kb sentence)))

;; ---- rebuild: recover's replay of the table ------------------------------

(defn rebuild-taxonomy
  "Rebuild the in-memory taxonomy from the durable store: the `:rebuild` column of
  the table, replayed in entry order over the stored declarations of each functor.

  Drops every cache first: a rebuild that merged into the existing one could only
  ever *add*, so an entry whose sentex is gone would survive the recovery that was
  supposed to re-derive it.

  A stored `genl` / `genlCx` declaration whose positional read is not a well-formed edge
  is dropped rather than replayed (`replay-edge`), and the count is warned once — the same
  discipline `rebuild-tms` follows for a justification the store cannot root.  A well-formed
  store never has one; a store an older or foreign writer left a non-edge sentex under the
  genl / genlCx functor root does, and replaying it would seed a null closure node that
  crashes `restore-depths`."
  [kb]
  (let [tax   (reasoning/taxonomy kb)
        skips (volatile! 0)]
    (tax/clear-relations! tax)
    (binding [*edge-replay-skips* skips]
      (doseq [[f {:keys [rebuild]}] entries
              :when rebuild
              sx (stored-declarations kb f)]
        (rebuild tax sx)))
    ;; Members second, once the metatypes are known — membership is what separates
    ;; them, and nothing about it is stored beyond the `(M T)` sentexes themselves.
    ;; A second pass rather than a table entry, because the member functors are the
    ;; metatypes: data, not vocabulary.  Every *stored* mark, as the live member arm
    ;; reads it, so the recovered members are the live KB's whatever the marks' labels.
    (doseq [m (tax/stored-disjoint-metatypes tax)
            {[_ t] :sentence id :id ctx :context} (stored-declarations kb m)]
      (tax/add-metatype-member tax m t id ctx))
    (when (pos? (long @skips))
      (trove/log! {:level :warn :id ::edges-malformed
                   :msg  (str @skips " stored genl/genlCx declarations are not well-formed"
                              " edges and are left out of the taxonomy")
                   :data {:skipped @skips}}))))
