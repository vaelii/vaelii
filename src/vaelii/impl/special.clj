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
            [vaelii.impl.caches :as caches]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.tuple :as tuple]
            [vaelii.impl.except :as exc]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.kv :as kv]
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
            [vaelii.impl.violations :as violations]
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
;; Beside the sentences the set may hold a **withdrawal marker**, for a withdrawal the
;; rule's firings carry rather than its exception: `::entailment` (a calculus network
;; moved) and `{::preserving s}` (`s` moved what a preserved predicate licenses).  Each
;; is narrowed by its own test (`recheck/exception-candidates`), never by the shape one.

(def ^:private ^:dynamic *recheck-probe*
  "A volatile, or nil: while bound, `mark-recheck` adds the rule handles to it and queues
  nothing (`posts-recheck?`)."
  nil)

(defn- mark-recheck
  "Queue `rule-handles` for exception re-evaluation at the next `settle`, recording
  `trigger` — the sentence whose arrival or departure could have flipped the exception,
  or a withdrawal marker — `:all` when there is no such sentence and every firing must
  be re-checked, or `:all-rejoin` when that unconditional check must also force a fresh
  join.

  The unconditional markers are absorbing, and `:all-rejoin` is the stronger one:
  once queued, adding a narrower trigger must not narrow it back."
  [kb rule-handles trigger]
  (if-let [probe *recheck-probe*]
    (vswap! probe into rule-handles)
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
                       m rule-handles))))))

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
    transitiveInArgInverse [1]
    transitiveInArg        [1]})

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

(defn- composed-exception-rules
  "The watched rules a block literal of which a calculus moved by a predicate in `preds`
  answers: a literal on a predicate the calculus claims or on a super-predicate of one,
  `chain/answered-by-calculus?` read from the calculus's end.  `preds` are a fact's
  predicates or an edge's supertype, each of which `qkb/calculi-triggered-by` reads over
  its `genls` closure; empty when none moves a network.  The closure is the global one,
  as in `recheck-on-predicate`: a super-predicate any context sees can be answered there,
  and a rule over-selected costs a re-check that changes nothing.

  A calculus answers such a literal by composition, so the answer moves with the whole
  network: `(spatiallyDisconnected Canary Room)` follows from a `dc` fact on the cage and
  an `ntpp` fact placing the canary in it, and neither names the canary and the room
  together.  The predicate keying reaches the rule from neither fact's predicate but the
  `dc` one, and that fact's arguments agree with the firing's literal on nothing.  So the
  caller queues these rules with the `::entailment` marker, which keeps every firing of
  a rule whose block literal a calculus answers (`recheck/entailment-candidates`) and
  re-asks every refusal (docs/exceptions.md, \"Five channels\")."
  [kb preds]
  (let [cs (into #{} (mapcat #(qkb/calculi-triggered-by kb %)) preds)]
    (if (empty? cs)
      #{}
      (let [tx (reasoning/taxonomy kb) idx (:index kb)]
        (into #{}
              (comp (mapcat :predicates)
                    (mapcat #(tax/genls-global tx %))
                    (distinct)
                    (mapcat #(reads/watched-rules-on idx %)))
              cs)))))

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
  predicate at all, and along three channels the genls walk cannot see: `pred` is the
  relation some `transitiveInArg` declaration inherits along
  (`recheck-preserving-along`), `pred` has an `arg`-declared argument type, which
  makes the fact evidence of a membership nobody wrote (`recheck-arg-inferred`), or
  the fact moves a calculus network that answers the exception by composition
  (`composed-exception-rules`)."
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
        (let [ups (tax/genls-global (reasoning/taxonomy kb) pred)]
          (doseq [p ups]
            (mark-recheck kb (reads/watched-rules-on idx p) trigger))
          (mark-recheck kb (composed-exception-rules kb [pred]) ::entailment))
        (recheck-preserving-along kb pred)
        (recheck-arg-inferred kb pred trigger)))))

(defn- recheck-on-qualitative
  "A sentence on `pred` arrived or left and moved a registered calculus, so the **whole
  network** moved: queue every forward rule joining on any predicate of that calculus.
  `pred` is a fact's predicate, which moves the network from below a calculus predicate
  too, or a `genl` edge's supertype (`qkb/calculi-triggered-by`).

  Queued with the `::entailment` marker rather than with the sentence as a narrowing
  trigger — a constraint anywhere can change what is entailed anywhere else, which is
  what path consistency *is*, so narrowing by the arriving sentence would miss exactly
  the propagation the calculus exists for.  What the marker narrows by is what
  `entailment-withdrawn?` reads, the networks' satisfiability
  (`chain/entailment-withdrawable?`).

  Why any of this is needed: a firing that joined on an entailed relation lists the facts
  behind it as antecedents, so the JTMS withdraws it when one of those goes.  What the
  antecedents cannot express is the network turning *unsatisfiable* — the supporting
  facts are all still believed, and some other fact made the theory impossible.  That is
  decided per firing by `chain/entailment-withdrawn?`, and this is what puts the firing
  in front of it.

  A fact's caller passes its **underlying body**'s functor, so a believed `(not (ntpp A
  B))` arrives at the calculus its own functor (`not`) names nothing about.  A negative
  fact is read into the network as the complement of the predicate's denotation, so it
  moves the network exactly as a positive one does and can make it impossible outright —
  and then a firing the network licensed has to be put in front of
  `entailment-withdrawn?` on precisely the same trigger.

  `calculi-triggered-by` rather than `calculus-for`, because what moves a network is
  wider than what one answers: the interval algebra reads a metric **narrowing** beside
  its stored facts, so a `temporalDistance` or a `startOf` arriving changes what is
  entailed between two intervals while being a predicate no interval rule mentions.  The
  rules queued are still keyed on each calculus's own predicates — those are the
  antecedents a rule joins on.  Every calculus the predicate moves is queued, since an
  instant fact moves both the point network and the Allen one read off it.

  Bounded by the rules mentioning the calculus at all, which is zero for every KB that
  registered no prover.  Nil is close to free there: `qkb/calculus-for` memoizes the
  registered-calculus list against the registry vector, so a KB that opted into nothing
  pays a registry deref, a volatile read and an identity compare per asserted sentence,
  and the per-prover `instance?` scan only when the registry itself changed."
  [kb pred]
  (when-let [calcs (qkb/calculi-triggered-by kb pred)]
    (let [idx (:index kb)]
      (mark-recheck kb
                    (into #{} (comp (mapcat :predicates)
                                    (mapcat #(reads/as-stored-rules-by-antecedent idx %)))
                          calcs)
                    ::entailment))))

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

  Queued with the `{::preserving sentence}` marker rather than with the sentence as a
  narrowing trigger, for `recheck-preserving-along`'s reason: the sentence that moved is
  on the relation, or on a tuple below the one the firing joined at, so it agrees with
  the firing's literals on nothing a shape comparison could use.  The marker narrows by
  the goals the sentence can move instead (`inherit/moved-goal-test`).

  `inherit/rejoin-rules` is the same read the chainer's own re-join makes, and behind
  the same gate — a KB that declares no preservation pays two predicate-extent counts per
  sentence (`inherit/declarations-exist?`)."
  [kb sentence]
  (when-let [rs (inherit/rejoin-rules kb sentence)]
    (mark-recheck kb rs {::preserving sentence})))

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
    (recheck-on-qualitative kb (nm/functor (or b sentence)))
    (recheck-preserving-firings kb (or b sentence))))

(defn posts-recheck?
  "Would `sentence` arriving or leaving queue a watched rule (`recheck-on-sentence`)?
  Queues nothing."
  [kb sentence]
  (let [probe (volatile! #{})]
    (binding [*recheck-probe* probe] (recheck-on-sentence kb sentence))
    (boolean (seq @probe))))

(defn- note-mark-reach!
  "Queue on `:respell` each predicate a statement of whose permuting mark rests on
  `target`, and `[:reifiable f]` each function a statement of whose `reifiable_function`
  mark does: a `defeat` or an `except` of `target` moves which readers believe the mark
  with no label moving, and so which spellings the facts under it are read in
  (`chain/reconcile-spellings!`, `chain/reconcile-reified!`).  Reads the supports of the
  marks' statements, so it costs the marks stored and not the facts under them."
  [kb target]
  (let [t      @(reasoning/taxonomy kb)
        tms    (reasoning/tms kb)
        rests? (fn [k] (some #(contains? (exc/support tms % (constantly false)) target)
                             (keys (tax/supporters (reasoning/taxonomy kb) k))))
        moved  (-> #{}
                   (into (filter #(rests? [:prop :symmetric %])) (get-in t [:props :symmetric]))
                   (into (keep (fn [[p gs]] (when (some #(rests? [:commuting p %]) gs) p)))
                         (:commuting t))
                   (into (comp (filter #(rests? [:prop :reifiable %])) (map #(vector :reifiable %)))
                         (get-in t [:props :reifiable])))]
    (when (seq moved)
      (swap! (reasoning/respell kb) into moved))))

(defn- note-split-marks!
  "Queue on `:respell` each predicate whose permuting marks, and `[:reifiable f]` each
  function whose `reifiable_function` mark, some reader does not believe
  (`res/uniform-marks?`): a `genlCx` edge moves which readers see which defeats and
  excepts, and so which spellings a fact's readers read.  Reads nothing while no
  `defeat` or `except` is stored, since every reader then believes every mark."
  [kb]
  (when (or (reads/stores-any? (:index kb) sx/defeat-functor)
            (reads/stores-any? (:index kb) sx/except-functor))
    (let [t      @(reasoning/taxonomy kb)
          split? (fn [k] (let [sup (tax/supporters (reasoning/taxonomy kb) k)]
                           (and (seq sup) (not (res/uniform-marks? kb {k sup})))))
          moved  (-> #{}
                     (into (filter #(split? [:prop :symmetric %])) (get-in t [:props :symmetric]))
                     (into (keep (fn [[p gs]] (when (some #(split? [:commuting p %]) gs) p)))
                           (:commuting t))
                     (into (comp (filter #(split? [:prop :reifiable %])) (map #(vector :reifiable %)))
                           (get-in t [:props :reifiable])))]
      (when (seq moved)
        (swap! (reasoning/respell kb) into moved)))))

(defn recheck-defeat-target
  "Post the re-check a `(defeat (sentexHandle H))` sentex `sx` owes H's watchers when it is
  stored, removed or relabelled: the defeat moves H's belief at the contexts that see it
  with no relabel of H, so H's sentence posts what its own arrival posts
  (`recheck-on-sentence`), and a permuting mark resting on H re-spells its facts
  (`note-mark-reach!`).  A no-op for any other sentex, and for an H no longer stored."
  [kb sx]
  (when-let [t (kb/defeat-target (:sentence sx))]
    (note-mark-reach! kb t)
    (when-let [ts (p/get-sentex (:records kb) t)]
      (recheck-on-sentence kb (:sentence ts)))))

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

  The same three sources `recheck/exception-candidates` narrows a firing by, for the
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
  today no edge flips one at all and the answer is always false.  The wave-through
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
  a rule is `:all`, and `:all` is the arm of `recheck/exception-candidates` that skips
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

  Four channels the predicate keying cannot see are covered beside it: the two
  waved-through functors above, whose provers read the closure across arguments;
  `recheck-preserving-along`, for the declared preserved positions the code cannot name
  in advance; `recheck-negated-exceptions`, keyed at the edge's **subtype** because
  a negation is the one condition read against its own predicate's up-closure; and
  `composed-exception-rules`, since an edge under a calculus predicate moves the
  network, which reads the sub-predicate's facts through the matcher's fan.  The same
  move puts the rules joining on the calculus in front of `chain/entailment-withdrawn?`
  (`recheck-on-qualitative`), outside the watched-rule guard, since those rules need
  carry no exception.

  Sound by construction: every channel a genl edge can reach a level-6 answer through is
  either predicate-addressed here or covered by one of those four; where a channel is in
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
      (let [ups (tax/genls-global tx super)]
        (doseq [pe (into ups closure-answered-exception-functors)]
          (mark-recheck kb (reads/watched-rules-on idx pe) :all))
        (mark-recheck kb (composed-exception-rules kb [super]) :all))
      (recheck-negated-exceptions kb sub)
      (recheck-preserving-along kb 'genl))
    (recheck-on-qualitative kb super)))

(defn arrival-releasable-rule?
  "Can an arriving fact release a block on the rule stored at `rh`?  True when
  `rules/arrival-releasable?` holds of it, or `rules/exception-arrival-releasable?` of
  its exceptions.  The settle loop owes such a rule a re-join, and the two edge triggers
  below exempt it from their firing-side narrowing."
  [kb rh]
  (when-let [rsx (p/get-sentex (:records kb) rh)]
    (and (rules/rule? rsx)
         (or (rules/arrival-releasable? rsx)
             (rules/exception-arrival-releasable? (provers/rule-exceptions kb rh))))))

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
  exception is affected iff one of its rule's firings is placed in `context-down(sub)`,
  and a guard defeat iff one is placed in a context one of those sees: the firings are
  tested against the second, larger set.

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

  A rule an arrival can release (`arrival-releasable-rule?`) is exempt from that
  narrowing and queued outright (docs/exceptions.md, \"Taxonomy changes are keyed on
  what the closure moved\").

  One record fetch per excepted rule for that exemption test, and then one per **firing**
  for the ancestor set test — `some` short-circuits on a hit, so a rule the edge does reach costs
  the firings up to the first one in the ancestor set, and a rule it reaches through none costs
  every firing the rule ever made.  That is the price of narrowing on placement rather
  than queueing wholesale, and it is paid on a `genlCx` edge alone."
  [kb sub]
  (let [idx (:index kb) tms (reasoning/tms kb)
        excepted (reads/watched-rules idx)]
    (when (seq excepted)
      (let [tax      (reasoning/taxonomy kb)
            affected (tax/context-down tax sub)
            ;; a firing placed where a context under `sub` sees it can gain or lose a
            ;; guard defeat there (`chain/place-guard-defeats!`)
            seen     (into #{} (mapcat #(tax/context-up-global tax %)) affected)
            in-ancestor-set? (fn [jid]
                               (when-let [j (jtms/justification tms jid)]
                                 (when-let [csx (p/get-sentex (:records kb) (:consequence j))]
                                   (contains? seen (:context csx)))))]
        (doseq [rh excepted]
          (when (or (arrival-releasable-rule? kb rh)
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

  **Except an aggregate or a nested NAF** (`arrival-releasable-rule?`), which takes
  `:all` and no test: such a condition can move with no term the firing binds in the
  merged class (docs/exceptions.md, \"Five channels\").

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
                   (arrival-releasable-rule? kb rh)
                   (some #(binds-any? kb terms %) (jtms/dependents tms rh))
                   ;; ...and the same question of a firing that was refused before it
                   ;; could hold a justification: its bindings are recorded, so the
                   ;; class-membership test reaches it exactly as it reaches a placed one
                   (refusals-reach? kb rh
                                    (fn [e] (some (fn [v] (some terms (tree-seq sequential? seq v)))
                                                  (vals (:bindings e))))))
           (mark-recheck kb [rh] :all)))))))

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
  `vaelii.impl.sentex`), and `:engines` / `:defeasible` are read off it by every
  consumer.  Nothing enumerates rules by defeasibility — defaults fire from the same
  agenda as strict rules — so there is no default-rule index to maintain.

  A rule is not a table entry: its trigger is the *shape* of the sentence (any
  functor can head an implication), so it is the structural arm of the
  `integrate-sentex` walk below, and this is its add half."
  [kb handle rule-sentex]
  (let [antes (:antecedent rule-sentex)]
    (p/index-rule (:index kb) handle
                  (rules/antecedent-keys antes)
                  (rules/consequent-index-pred rule-sentex)
                  (:context rule-sentex))
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

(defn restrength-firings!
  "Set the strength of every justification rule `rh` informs to the rule's current
  `provers/firing-strength`, in both copies: the record store's justification records
  (what `supporting-justifications` shows and what `recover` rebuilds the network from)
  and the network's (`jtms/restrength-informant`, which relabels the region).  A rule's
  firing strength moves when its defeasibility resolves or an `exceptWhen` arrives or
  leaves; `dropping-id` is the exception meta-sentex leaving, if any."
  ([kb rh] (restrength-firings! kb rh nil))
  ([kb rh dropping-id]
   (when-let [rsx (p/get-sentex (:records kb) rh)]
     (when (rules/rule? rsx)
       (let [strength (provers/firing-strength kb rh rsx (reads/watched-rule? (:index kb) rh)
                                               dropping-id)
             tms      (reasoning/tms kb)]
         (doseq [jid (jtms/dependents tms rh)
                 :let [j (p/get-justification (:records kb) jid)]
                 :when (and j (= rh (:informant j)) (not= strength (:strength j)))]
           (p/put-justification (:records kb) (assoc j :strength strength)))
         (jtms/restrength-informant tms rh strength))))))

(defn- force-rule!
  "Rewrite the forced memberships of the stored rule at `rh` and of its firings
  (`checks/force-sentexes!`): an `exceptWhen` arriving on a roster rule convicts its
  firings, and the last one leaving releases them."
  [kb rh]
  (when-let [rsx (p/get-sentex (:records kb) rh)]
    (when (rules/rule? rsx)
      (checks/force-sentexes! kb [rsx]))))

(defn index-exceptWhen-meta
  "Register the exceptWhen meta-sentex `meta-sentex` in the re-check index: post the
  rule it names under each predicate its query mentions and into the `:rules` roster,
  queue the rule for a blanket re-check (a fact may already have arrived that its
  new exception blocks), lower the rule's firings to `:default`
  (`restrength-firings!`), and hold void the firings of a roster rule it convicts
  (`checks/force-sentexes!`)."
  [kb meta-sentex]
  (let [rh    (sx/exceptWhen-rule-handle (:sentence meta-sentex))
        preds (rules/watched-predicates
               (sx/exception-query-conjuncts (:sentence meta-sentex)))]
    (when rh
      (p/index-exception (:index kb) rh preds)
      (mark-recheck kb [rh] :all)
      (restrength-firings! kb rh)
      (force-rule! kb rh))
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
  losing an exception may revive what it was blocking, restores the rule's firing
  strength when no guard remains (`restrength-firings!`), and releases the firings of a
  roster rule no exception convicts any more (`checks/force-sentexes!`)."
  [kb meta-sentex]
  (let [rh        (sx/exceptWhen-rule-handle (:sentence meta-sentex))
        this-preds (rules/watched-predicates
                    (sx/exception-query-conjuncts (:sentence meta-sentex)))]
    (when rh
      (p/unindex-exception! (:index kb) rh this-preds)
      (when-let [remaining (seq (rule-remaining-recheck-preds kb rh (:id meta-sentex)))]
        (p/index-exception (:index kb) rh remaining))
      (mark-recheck kb [rh] :all)
      (restrength-firings! kb rh (:id meta-sentex))
      (force-rule! kb rh))))

;; ---- except: visibility removal blocks derivations too -------------------
;; A believed `(except (sentexHandle H))` in context C hides H from C and its
;; descendants — for reads *and* for derivation: a rule firing that used H as an
;; antecedent and placed its conclusion in the ancestor set rests on a fact that context can no
;; longer see, so the conclusion is swept (`chain/justification-excepted?` reads the
;; hidden set).  The trigger below queues the rules of every firing that uses H, so a
;; late `except` arriving (or leaving) re-checks and sweeps (or revives) them.  It is
;; the derivation-side twin of `recheck-on-sentence`, keyed on the *handle* the except
;; names rather than a predicate.

(defn note-except-move!
  "Queue handle `h` on `:except-moves`: an `except` of it stated in `context` arrived,
  left or flipped, so what `h` restates or merges is visible to a different set of
  readers there and below.  `edge`, a `(genlCx sub super)` edge's `[sub super]`, says the
  move is that edge's and reaches the contexts under `sub` alone (`:scoped`); nil says the
  `except` itself moved (`:whole`).  The settle drains the queue (`drain-except-moves!`,
  `take-except-moves!`)."
  [kb h context edge]
  (swap! (reasoning/except-moves kb)
         #(cond-> (update-in % [:pending h] (fnil conj #{}) context)
            edge       (update-in [:scoped h] (fnil conj #{}) edge)
            (nil? edge) (update :whole (fnil conj #{}) h))))

(defn- recheck-defeats-reached
  "Post the re-check of the target of each placed `defeat` an `except` of `h` can take in
  or out of force (`recheck-defeat-target`): each defeat in `closure`, `h`'s consequence
  closure with `h` in it, and each defeat of `h`.  A defeat in the closure rests on `h`
  through a member or a ground of its nogood, and an except of `h` can lower that member's
  class at a reader (docs/nmtms.md, \"A conflict a reader's excepts lower\").  An except
  moves a defeat's force with no relabel of its target."
  [kb h closure]
  (when (reads/stores-any? (:index kb) sx/defeat-functor)
    (let [tms  (reasoning/tms kb)
          recs (:records kb)
          ;; only the engine derives a defeat, under one of two informants
          placed? (fn [d] (some #(contains? #{exc/nogood-informant exc/guard-informant}
                                            (:informant (jtms/justification tms %)))
                                (jtms/supports tms d)))]
      (doseq [d (into (filterv placed? closure) (reads/as-stored-naming (:index kb) sx/defeat-functor h))
              :let [sx (p/get-sentex recs d)]
              :when sx]
        (recheck-defeat-target kb sx)))))

(defn recheck-except
  "An `(except (sentexHandle H))` fact arrived or left: queue every rule the visibility
  change touches, so `settle` (on arrival) sweeps a conclusion now resting on an
  invisible antecedent and `retract!` (on departure) re-derives one the fact can be seen
  for again.  Two rule sets, because the two directions need different rules:

    * the rules of firings that **rest on H** through any chain (the justifications
      of H's consequence closure, `jtms/consequence-closure`) — the conclusions to sweep
      when the except arrives, and the blocked ones to release when it leaves; and
    * the rules that could **fire on H or on what rests on it** (`rules-by-antecedent`
      over each predicate of the closure and its supertypes, the same fan matching does)
      — the conclusions to re-derive when the except leaves, since by then the firing
      that used one has been swept or refused and `dependents` no longer names it; and

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

  H goes on `:except-moves` as well (`note-except-move!`), for the restatements the
  visibility change moves: an equality or a merge mark H restates facts only where it is
  visible, so the settle re-runs H's arrival sweep and reconciles every supersession.

  Returns the rule handles it marked — the settle loop re-chains them when the
  trigger was a belief flip, which moves no blocked justification for the drain to
  notice on its own."
  ([kb except-sentex] (recheck-except kb except-sentex :all nil))
  ([kb except-sentex trigger edge]
   (when-let [h (sx/handle-id (second (:sentence except-sentex)))]
     (note-mark-reach! kb h)
     (let [tms      (reasoning/tms kb)
           ;; what rests on H through any chain, H included: bounded by H's consequences
           closure  (jtms/consequence-closure tms [h])
           users    (into #{}
                          (comp (mapcat #(jtms/dependents tms %))
                                (keep (fn [jid]
                                        (let [inf (:informant (jtms/justification tms jid))]
                                          (when (integer? inf) inf)))))
                          closure)
           target   (p/get-sentex (:records kb) h)
           rule?    (and target (rules/rule? target))
           ;; the rules that could fire on a handle of the closure, for a move that is not
           ;; the except's own; the global closure on purpose: an under-selected re-check
           ;; trigger is a missed sweep or a missed revival
           firers   (when-not (= :all trigger)
                      (into #{}
                            (comp (keep #(p/get-sentex (:records kb) %))
                                  (remove rules/rule?)
                                  (filter #(symbol? (nm/functor (sx/sentence-of %))))
                                  (mapcat #(rules/trigger-keys (reasoning/taxonomy kb) (:sentence %)
                                                               (reads/as-stored-rule-keys (:index kb))))
                                  (mapcat #(reads/as-stored-rules-by-antecedent (:index kb) %)))
                            closure))
           marked   (vec (cond-> (into users firers) rule? (conj h)))]
       (if (= :all trigger)
         ;; the except itself arrived or left: re-decide the firings resting on the
         ;; closure (`recheck/except-candidates`), and chain from the closure for the
         ;; firings it refused (`drain-except-moves!`)
         (do (mark-recheck kb users {::except-closure closure})
             (when rule? (mark-recheck kb [h] :all)))
         (mark-recheck kb marked trigger))
       (note-except-move! kb h (:context except-sentex) edge)
       (recheck-defeats-reached kb h closure)
       ;; the except moves the visibility of H, or through the cascade that of the first
       ;; non-except H's excepts name, with no relabel, so that sentence posts what its
       ;; removal posts: a guard reading it is re-decided, and a firing the guard refused
       ;; or swept is released from the refusal record
       (when-let [fact (loop [s target, seen #{}]
                         (let [t (some-> s :sentence kb/except-target)]
                           (if (and t (not (seen t)))
                             (recur (p/get-sentex (:records kb) t) (conj seen t))
                             s)))]
         (when-not (rules/rule? fact)
           (recheck-on-sentence kb (:sentence fact))))
       (decide/note-except-target! kb h)
       marked))))

(defn recheck-except-ancestors
  "A `(genlCx sub super)` edge moved visibility for the contexts in `context-down(sub)`,
  which changes not only what an exceptWhen query sees (`recheck-genlCx-edge`) but also
  which handles a believed `except` hides from a context in the ancestor set — so a
  derivation it blocks or releases must be re-checked too.  Re-queues the affected
  firings of each `except` the edge moves (`recheck-except`): one stated in a context
  `super` sees, since an `except` hides its target from the contexts that see its own,
  and the edge changes what a context under `sub` sees only by `super`'s ancestor set.
  An `except` naming one of those adds the `except` it names, whose cascade moves with it.
  Read off the `except` extent in `super`'s ancestor set, so an edge whose `super` sees no
  context stating an `except` re-queues none (`lein perf`'s
  `genlcx-edge-beside-excepted-declarations`)."
  [kb sub super]
  (let [idx (:index kb)]
    (when (reads/stores-any? idx sx/except-functor)
      (let [tx   (reasoning/taxonomy kb)
            recs (:records kb)
            seen (into (sorted-set)
                       (reads/as-stored-with-functor-in idx sx/except-functor
                                                        (into #{super} (tax/context-up tx super))))]
        (loop [todo (vec seen) done #{}]
          (when-let [eh (peek todo)]
            (let [todo (pop todo)]
              (if (contains? done eh)
                (recur todo done)
                (let [esx   (p/get-sentex recs eh)
                      inner (some->> esx :sentence kb/except-target)
                      esx   (when inner esx)
                      inner (when (some->> inner (p/get-sentex recs) :sentence kb/except-target)
                              inner)]
                  ;; A context edge can make two independently restored antecedents meet
                  ;; at a reader without releasing any already-blocked justification.
                  ;; Preserve that distinction through the queue so settle forces the
                  ;; missing join exactly for this visibility-transition shape.
                  (when esx (recheck-except kb esx :all-rejoin [sub super]))
                  (recur (cond-> todo inner (conj inner)) (conj done eh)))))))))))

(defn- belief-change-region
  "`moved` plus the targets of any visibility-excepts it names.

  A relabel reports the except handle because that is the TMS datum whose belief
  changed, while the derived cache is indexed by the declaration handle the except
  hides. Expanding at this boundary lets callers report the event they observed
  without knowing which cache supporter it invalidates.

  Gated on a stored `except` (`reads/stores-any?`), as the scan in
  `reconcile-belief-change` is: while none is stored no handle in `moved` can name one and
  the region is `moved` itself — without a record fetch per member, on a set that is the
  whole KB when a rebuild's settle reads it."
  [kb moved]
  (if-not (reads/stores-any? (:index kb) sx/except-functor)
    (set moved)
    (into (set moved)
          (keep (fn [h]
                  (some-> (p/get-sentex (:records kb) h)
                          :sentence
                          kb/except-target)))
          moved)))

(defn- permuting-marks
  "What the store spells sentences by: the `symmetric` predicates, the commuting-group
  table and the `reifiable_function` functions.  Three persistent values, compared by
  identity first."
  [tax]
  [(tax/props tax :symmetric) (get @tax :commuting {}) (tax/props tax :reifiable)])

(defn- note-permuting-moves!
  "Queue on `:respell` every predicate whose permuting marks differ between `before`
  (a `permuting-marks` reading) and now, and `[:reifiable f]` for every function whose
  `reifiable_function` mark does.  A mark that stops holding leaves rows spelled by it,
  and one that starts holding again leaves rows it would have folded; neither is a sentex
  arriving, so `chain/reconcile-spellings!` and `chain/reconcile-reified!` are told here,
  at the places a mark can stop or start holding without a declaration being written — its
  record leaving, and a relabel — and, for the reifiable mark, its record arriving
  (`reifiable-entry`).  Nearly always three `identical?` tests and nothing else."
  [kb [sym0 com0 rf0]]
  (let [[sym1 com1 rf1] (permuting-marks (reasoning/taxonomy kb))]
    (when-not (and (identical? sym0 sym1) (identical? com0 com1) (identical? rf0 rf1))
      (let [moved (-> #{}
                      (into (remove #(contains? sym1 %)) sym0)
                      (into (remove #(contains? sym0 %)) sym1)
                      (into (filter #(not= (get com0 %) (get com1 %)))
                            (concat (keys com0) (keys com1)))
                      (into (comp (remove #(contains? rf1 %)) (map #(vector :reifiable %))) rf0)
                      (into (comp (remove #(contains? rf0 %)) (map #(vector :reifiable %))) rf1))]
        (when (seq moved)
          (swap! (reasoning/respell kb) into moved))))))

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

  The caches read the network (`jtms/in?`); a scoped read filters a supporter through
  the read walk (`res/supporter-believed?`).  The two-argument form decides
  `visibility-moved?` by reading `moved`'s records for an except, whose relabel moves
  what the scoped reads see, and evicts the scoped closures each relabelled `defeat` can
  move (`kb/retire-defeated-reads!`) — each behind a stored `except` or `defeat`
  (`reads/stores-any?`), so a KB storing neither pays no fetch per moved handle
  (`belief-change-region` says why the gate is exact)."
  ([kb] (reconcile-belief-change kb nil))
  ([kb moved]
   (reconcile-belief-change
    kb
    moved
    (or (nil? moved)
        (let [ex?  (reads/stores-any? (:index kb) sx/except-functor)
              def? (and (reads/stores-any? (:index kb) sx/defeat-functor)
                        (tax/defeat-moves-scoped? (reasoning/taxonomy kb)))]
          (when (or ex? def?)
            (reduce (fn [ex-moved? h]
                      (if-let [sx (p/get-sentex (:records kb) h)]
                        (let [s (:sentence sx)]
                          (when (and def? (kb/defeat-target s)) (kb/retire-defeated-reads! kb sx))
                          (let [m (or ex-moved? (boolean (and ex? (kb/except-target s))))]
                            (if (and m (not def?)) (reduced m) m)))
                        ex-moved?))
                    false moved))))))
  ([kb moved visibility-moved?]
   (let [region (when (some? moved) (belief-change-region kb moved))]
     (when visibility-moved?
       (tax/note-supporter-visibility-change! (reasoning/taxonomy kb)))
     (let [before (permuting-marks (reasoning/taxonomy kb))]
       (tax/refresh-beliefs (reasoning/taxonomy kb) (partial jtms/in? (reasoning/tms kb)) region
                            (partial jtms/premise? (reasoning/tms kb)))
       (note-permuting-moves! kb before)))))

;; Genuine in-file cycle, threaded through the table.  Three derivation sites live
;; above the table and must reach the choke point below it: the lift's copy, the
;; equality arms' migrated twin and the argument-constraint entailment are all derived
;; sentexes, so all three go through `derived-sentex-added`, and equality and the
;; entailment additionally check `wff-problems` / `wff-violation` — and each of those
;; walks the very table these arms sit in.  The cycle is data-shaped (the table's
;; values are the arm fns), so four declares close it.
(declare derived-sentex-added integrate-twin wff-problems wff-violation)

(defn taxonomy-generations
  "The `genl` and `genlCx` generations with the rebuild epoch (`tax/relation-epoch`), the
  stamp a waiting entry is decided under: a refused mint, a refused lift, and (as
  `chain/constraint-generations`) an argument conviction.  `settle` re-asks an entry only
  when this moves from its stamp, so the stamp and the comparison are this one function.
  The epoch moves at every `recover`, which restarts the generations at 0."
  [kb]
  (let [tax (reasoning/taxonomy kb)]
    [(tax/relation-epoch tax) (tax/relation-gen tax :genl) (tax/relation-gen tax :genlCx)]))

;; ---- the refusal record's kind roster ---------------------------------------
;; `:kinds` in the refusal record names, per kind, the handles holding an entry of it, and
;; is absent while none does (docs/exceptions.md, "A refused firing is remembered as
;; bindings").

(def ^:private refusal-kinds [:constraint :lift :mint])

(defn- refusal-kind
  "The kind roster key refusal entry `e` is named under, or nil for a rule's refused firing."
  [e]
  (some #(when (get e %) %) refusal-kinds))

(defn- update-kind [m kind f k]
  (let [s  (f (get-in m [:kinds kind] #{}) k)
        ks (if (empty? s) (dissoc (:kinds m) kind) (assoc (:kinds m) kind s))]
    (if (empty? ks) (dissoc m :kinds) (assoc m :kinds ks))))

(defn note-kind
  "Refusal record `m` with handle `k` named under entry `e`'s kind."
  [m k e]
  (if-let [kind (refusal-kind e)] (update-kind m kind conj k) m))

(defn drop-kinds
  "Refusal record `m`, from which the entries `gone` have left handle `k`, with `k` no
  longer named under a kind of `gone` that no entry still under `k` holds."
  [m k gone]
  (let [cur (get m k)]
    (reduce (fn [m kind]
              (if (and (set? cur) (some #(get % kind) cur)) m (update-kind m kind disj k)))
            m
            (into #{} (keep refusal-kind) gone))))

(defn forget-kinds
  "Refusal record `m` with handle `k` named under no kind: its entries left together."
  [m k]
  (reduce #(update-kind %1 %2 disj k) m (keys (:kinds m))))

(defn kind-entries
  "Every entry of `kind` in refusal record `m`, as `[handle entry]` pairs, read off the
  sets of the handles the roster names under `kind`."
  [m kind]
  (for [k (get-in m [:kinds kind])
        :let [cur (get m k)]
        :when (set? cur)
        e cur
        :when (get e kind)]
    [k e]))

(defn- note-pending!
  "Keep `entry` under `k` in the refusal record, in place of any entry `same?` matches.
  The record keeps, beside the rules' refused firings, the engine's own derivations that
  an absence refused — a lift, a declaration's mints — each under the handle whose
  arrival would otherwise have been their only chance (docs/exceptions.md)."
  [kb k entry same?]
  (swap! (reasoning/refused kb)
         (fn [m]
           (let [cur (get m k)]
             (if (= :overflow cur)
               m
               (let [cur (when (set? cur) cur)]
                 (-> (assoc m k (conj (into #{} (remove same?) cur) entry))
                     (drop-kinds k (filter same? cur))
                     (note-kind k entry))))))))

(defn- drop-pending!
  "Retire the entries under `k` that `same?` matches."
  [kb k same?]
  (swap! (reasoning/refused kb)
         (fn [m]
           (let [cur (get m k)]
             (if (set? cur)
               (let [cur' (into #{} (remove same?) cur)]
                 (-> (if (empty? cur') (dissoc m k) (assoc m k cur'))
                     (drop-kinds k (filter same? cur))))
               m)))))

;; ---- the argument constraints, drawn as entailments ----------------------
;; `checks/constraint-entailments` reads what the visible `arg` / `genlArg`
;; declarations *say* about a sentence's arguments; this materializes it, and does so
;; the way the lift below does — as a derived sentex justified by `[the triggering
;; fact, the declaration]`.  That is the whole point: the type is **held** by its
;; supporters rather than merely produced, so retracting either one takes it back and
;; defeating the fact takes it out.
;;
;; Both directions, for the reason the lift has both: a declaration reaching back over
;; facts already stored must reach the same KB as one the facts arrive under, or belief
;; depends on which came first.  `deduce-arg-types` is fact-meets-declaration,
;; `entail-existing` is declaration-meets-facts.

(defn naming-violation
  "The `:naming` violation `sentence` in `context` carries under `kb`'s naming policy, or
  nil: `nm/blocking-problems` as the value a caller that may not throw drops a sentence
  for.  Nil under `:warn` and `:off`."
  [kb sentence context]
  (when-let [ps (nm/blocking-problems (:naming kb) sentence context)]
    {:violation :naming
     :detail    {:message (str "naming invariant: " (str/join "; " ps))}}))

(defn inadmissible
  "The violation that stops `sentence` from being stored in `context`, or nil — naming,
  the definitional constraints, well-formedness, and edge stratification, as one value.

  These hold of any content the engine mints on its own behalf: a `(T x)` can clash with
  a disjoint membership, a `(genl X T)` edge can close a taxonomy cycle or a cycle
  through negation, and a type used at the wrong arity is not a type membership at all.
  Three callers ask it — the argument-type entailment below, the computed `genlCx` edge
  of a context-valued function (`context-nat`), and abduction, which asks it *before*
  minting a hypothesis so that a sentence no assertion could legally make is never one
  the search assumes.  Forward chaining runs the same four over a rule's conclusion in
  `chain/place-conclusion`, the naming arm only where a consequent literal's functor is
  a variable.

  A **value**, never a throw.  Two of its callers run after their triggering sentex is
  stored (that is what gives them a handle to be justified by), and neither may abort
  halfway; the third would rather refuse a hypothesis than fail the query that wanted
  it.

  `constraint-arm` is the definitional-constraint check, `checks/constraint-violation`
  by default, which refuses every violation.  The argument-type mint passes
  `checks/derivation-violation` instead: a mint that clashes with a believed membership is
  placed, and `settle` weighs the pair as it weighs a rule's conclusion that clashes
  (docs/argtypes.md).

  A nil `constraint-arm` omits the arm, for a
  caller that has already run it against this exact content.  The assert path's
  first-level argument-type mints are the one such caller: `checks/entailment-check`
  runs `constraint-problem` (and `cascade-clash`, which reads the source's own
  membership) over every mint of the cascade **before** the trigger is stored, and
  refuses the trigger if any mint fails — so a first-level mint reaching the materializer
  has passed the constraint check already, and storing the trigger and the mints beside
  it only adds memberships, which cannot turn a passing `args`/`disjoint`/`arity` check
  into a failing one (each convicts on an absent type, never a present one).  Naming,
  well-formedness and edge stratification are **not** what `entailment-check` runs, so
  they are asked here whether or not the arm is.  Every other caller — forward
  chaining, the retroactive sweeps, and the cascade's own deeper levels, none of which
  `entailment-check` pre-validates — leaves it false and pays the full check."
  ([kb sentence context] (inadmissible kb sentence context checks/constraint-violation))
  ([kb sentence context constraint-arm]
   (or (naming-violation kb sentence context)
       (when constraint-arm (constraint-arm kb sentence context))
       (wff-violation kb sentence context)
       (checks/edge-stratification-violation kb sentence))))

(def ^:private empty-entailment-result
  "What an entailment step that minted nothing returns, and the seed of every reduce that
  `merge-with into`s step results, so the accumulator and the steps have one shape."
  {:new [] :violations []})

(defn- edge-functor
  "`genl` or `genlCx` for a sentex at `h` that is one of the two edges a route names, and
  nil for anything else."
  [kb h]
  (let [s (:sentence (p/get-sentex (:records kb) h))]
    (when (sequential? s) ('#{genl genlCx} (first s)))))

(defn- route-edge?
  "Is the sentex at `h` a `genl` or `genlCx` edge, the two relations a route names?"
  [kb h]
  (some? (edge-functor kb h)))

(defn- firing-bindings
  "A justification's bindings less the join's context variable `?ctx`, which one join
  binds and a re-join under an arriving edge does not, for the same firing."
  [j]
  (dissoc (:bindings j) '?ctx))

(defn- same-pairing?
  "Do `just` and `j` pair their facts with the same literals: equal subsumptions?  A `j`
  with none whose `extra` antecedents name a `genl` edge was written before subsumptions
  were recorded, and pairs as `just` does (docs/nmtms.md, \"Where the layer stops\")."
  [kb just j extra]
  (or (= (:subsumptions just) (:subsumptions j))
      (and (nil? (:subsumptions j)) (some #(= 'genl (edge-functor kb %)) extra))))

(defn drop-replaced-routes!
  "Drop the justifications the one just added as `just` replaces: the same firing over a
  route the witness rule no longer names.  Returns the merged `jtms/drop-justification!`
  results, for the caller to apply to its stores; the dropped records are deleted here.

  A justification is replaced when it has `just`'s informant, consequence, bindings and
  subsumptions (`same-pairing?`), holds every antecedent of `just` outside `route`, and
  differs from it only in `genl` / `genlCx` edges that are all believed.  `route` is
  `just`'s own route handles; nil reads them off the antecedents by shape.  The
  consequence keeps `just`, whose antecedents are groundable, so the sweep collects
  nothing `just` does not hold up.

  An edge of the older route that is OUT keeps its justification: a route a defeat took
  away comes back when the defeat lifts, and the store then holds both
  (docs/nmtms.md, \"Where the layer stops\")."
  ([kb just] (drop-replaced-routes! kb just nil))
  ([kb just route]
   (let [tms  (reasoning/tms kb)
         recs (:records kb)
         h    (:consequence just)
         sups (jtms/supports tms h)]
     (when (< 1 (count sups))
       (let [antes    (set (:antecedents just))
             core     (reduce disj antes (or route (filter #(route-edge? kb %) antes)))
             replaced (fn [jid]
                        (let [j     (jtms/justification tms jid)
                              a     (set (:antecedents j))
                              extra (reduce disj a core)]
                          (and (not= jid (:id just))
                               (= (:informant just) (:informant j))
                               (seq extra)
                               (= (count core) (- (count a) (count extra)))
                               (every? #(and (jtms/in? tms %) (route-edge? kb %)) extra)
                               (same-pairing? kb just j extra)
                               (= (firing-bindings just)
                                  (firing-bindings (p/get-justification recs jid))))))
             gone     (filterv replaced sups)]
         (reduce (fn [acc jid]
                   (let [r (jtms/drop-justification! tms jid)]
                     (p/delete-justification! recs jid)
                     (merge-with into acc r)))
                 nil gone))))))

;; ---- the mint family (docs/indexing.md, "The mint family") ----------------------

(def ^:private entailing-declarations
  "The argument-constraint declarations that entail, with the arity each is written at —
  the roster `entail-existing` dispatches on, so another kind is one line rather than a
  widened `and`.  Every kind of the `:argument-constraint` family but `quotedArg`, which
  types the term as written and has nothing to derive (docs/argtypes.md)."
  '{arg 3, genlArg 3, interArg 5, args 2, argAndRest 3, argsGenl 2, argAndRestGenl 3,
    interArgs 2, interArgAndRest 3})

(def ^:private mint-informants
  "The informants an argument declaration's mint is justified under: the kinds
  `entailing-declarations` names."
  (set (keys entailing-declarations)))

(defn mint-informant?
  "Is `informant` one an argument declaration's mint is justified under?"
  [informant]
  (contains? mint-informants informant))

(defn- membership-shaped?
  "Is `sentence` a membership `(t x)` of one symbol in another?  A membership subsumes a
  mint of any supertype over the same term, and this test reads no index, so
  `subsumed-mint-blocks` runs it on every sentex a settle moved."
  [sentence]
  (and (= 1 (nm/arity sentence)) (symbol? (nm/functor sentence))
       (symbol? (first (nm/args sentence)))))

(defn- edge-shaped?
  "Is `sentence` a `genl` edge `(genl x S)`: a minted edge, or the one record that
  subsumes a mint out of `x` by itself (`says-more-than?`)?"
  [sentence]
  (and (= 'genl (nm/functor sentence)) (= 3 (count sentence)) (symbol? (nth sentence 1))))

(defn- context-edge-shaped?
  "Is `sentence` a `genlCx` edge, which shows the contexts under `sub` memberships and
  edges they could not see?"
  [sentence]
  (and (= 'genlCx (nm/functor sentence)) (= 3 (count sentence)) (symbol? (nth sentence 1))))

(defn- subsumer-shaped?
  "Can `sentence` subsume a mint?  A membership can, and so can a record that gives terms
  a route they did not have: a `genl` edge or a cover (`tax/installed-edges`), or a `genlCx`
  edge."
  [sentence]
  (or (membership-shaped? sentence) (seq (tax/installed-edges sentence))
      (context-edge-shaped? sentence)))

(defn- roster-term
  "The term the mint family files `sentence` under — `x` of a membership `(t x)` or of an
  edge `(genl x t)` — or nil for a shape no membership or edge can make redundant."
  [sentence]
  (when (or (membership-shaped? sentence) (edge-shaped? sentence))
    (second sentence)))

(defn post-mint!
  "File record `h`, holding `sentence` in `context` and concluded by a stored justification
  `mint-informant?` accepts, in `index`'s mint family, when the sentence has a
  `roster-term`.  Posted from the sentence in hand: `entail-arg-type` as it stores the
  justification, and `reindex` from the record it is indexing."
  [index sentence context h]
  (when-let [x (roster-term sentence)]
    (kv/post-mint! index x context h)))

(defn retire-mint!
  "Take the departing `sentex` out of the mint family, when it is filed there."
  [kb sentex]
  (when-let [x (roster-term (sx/sentence-of sentex))]
    (kv/retire-mint! (:index kb) x (:context sentex) (:id sentex))))

(defn refile-mint!
  "Bring record `h`'s entry in the mint family to its stored spelling: out from under the
  roster term of `old`, the record `h` held before (nil when its spelling did not move),
  and under the current one while a mint justification concludes it.  The callers are the
  store mutations that move a record's spelling (`integrate/respell!`) or the
  justifications concluding it (`integrate/fold-row!`)."
  [kb old h]
  (some->> old (retire-mint! kb))
  (let [tms (reasoning/tms kb)]
    (when (some #(mint-informant? (:informant (jtms/justification tms %))) (jtms/supports tms h))
      (when-let [sx (p/get-sentex (:records kb) h)]
        (post-mint! (:index kb) (sx/sentence-of sx) (:context sx) h)))))

(defn retire-unjustified-mints!
  "Take out of the mint family each record a mint justification removed in `removals`
  concluded, once no other mint justification concludes it.  `removals` is a
  `jtms/retract!`-shaped result, whose `:removed-supports` names each removed
  justification's consequence and informant, read off the network before the removal.  A
  consequence the removal swept leaves through `retire-mint!`; one still in the network
  is retired here, and its record is the one fetch."
  [kb removals]
  (let [tms (reasoning/tms kb)]
    (doseq [h (into (sorted-set)
                    (keep (fn [[c informant]] (when (mint-informant? informant) c)))
                    (:removed-supports removals))
            :when (and (jtms/known-datum? tms h)
                       (not-any? #(mint-informant? (:informant (jtms/justification tms %)))
                                 (jtms/supports tms h)))
            :let [sx (p/get-sentex (:records kb) h)]
            :when sx]
      (retire-mint! kb sx))))

;; Genuine in-file cycle: a minted type draws its own entailments, so `entail-arg-type`
;; calls back into `deduce-placed`, which folds `deduce-arg-types` over it.  Reordering
;; cannot break it — the recursion is the cascade, and its termination argument is in
;; `entail-arg-type`'s docstring.
(declare deduce-placed)

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
    (if-let [v (inadmissible kb sentence context
                             (when-not pre-checked? checks/derivation-violation))]
      {:new [] :violations [(assoc v :sentence sentence :context context
                                   :entailed-from src-handle)]}
      ;; A type the KB already holds more specifically is not written down: the record
      ;; would say what `(dog Fred)` says, one step less precisely, and subsumption
      ;; answers `(animal Fred)` without it.  Withheld only where there is no record yet
      ;; — an existing one takes the justification whatever else holds it up, or
      ;; retracting the specific membership would leave belief depending on which
      ;; arrived first — and the withdrawal half, for the orders where the specific
      ;; membership arrives last, is `settle`'s (`subsumed-mint-blocks`).
      ;;
      ;; The stored handle is read **once** and both branches share it, where
      ;; `find-or-create-sentex` would look it up a second time: this runs per mint per
      ;; assert, and a mint that dedups to a record already stored is the common case on
      ;; a declared ontology (`assert_cost_test`'s `declared` workload counts the lookup).
      (let [stored (kb/find-sentex-handle kb sentence context)]
        (if (or (and (not stored) (checks/subsumed-mint kb sentence context))
                ;; an ingredient an `except` hides from `context`, as a rule firing is
                ;; not placed there (`except-move-sweeps` drops one the except meets)
                (when-let [hidden? (exc/except-hidden-fn kb context)]
                  (or (hidden? src-handle) (some hidden? because))))
          empty-entailment-result
          (let [[h2 s2 new?] (if stored
                               [stored (p/get-sentex (:records kb) stored) false]
                               (let [[h sx] (kb/create-sentex kb sentence context nil)]
                                 [h sx true]))]
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
                      (jtms/add-justification (reasoning/tms kb) just)
                      (post-mint! (:index kb) sentence context h2)
                      ;; the route this pair named before is replaced; `just` holds the
                      ;; mint up, so the drop sweeps nothing and only the records go
                      ;; a trigger membership is an ingredient, not a route
                      (when-not new?
                        (drop-replaced-routes! kb just
                                               (cond->> (rest because)
                                                 (:trigger ent) (remove #{(:trigger ent)}))))))
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
                                (deduce-placed kb sentence h2 context)
                                empty-entailment-result)))))))))))

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

(defn pair-placements
  "The contexts a mint drawn over a fact stated in `fact-cx` through a declaration stated
  in `decl-cx` is placed in, in content order: `fact-cx` when it sees `decl-cx`, else the
  maximal common descendants of the two (`tax/maximal-common-descendant-contexts`, the
  placement of a forward firing and of a placed nogood), and empty when no context sees
  both (docs/argtypes.md, \"Where a mint is placed\")."
  [kb fact-cx decl-cx]
  (let [tax (reasoning/taxonomy kb)]
    (if (or (nil? decl-cx) (tax/sees? tax fact-cx decl-cx))
      [fact-cx]
      (nm/sort-by-content-key nm/name-key compare
                              (tax/maximal-common-descendant-contexts tax [fact-cx decl-cx])))))

(defn- placements-of
  "`pair-placements` of the declaration stored at `dh` against a fact's context, as a fn of
  that context, memoized for one sweep over a lattice that does not move under it."
  [kb dh]
  (let [dc (:context (p/get-sentex (:records kb) dh))]
    (memoize #(pair-placements kb % dc))))

(defn- declarations-below
  "The stored entailing declarations binding `pred`'s tuples that `context` does not see
  and shares a descendant with, as `[handle placements]` pairs (`pair-placements`), in
  content order: the declarations a fact stated in `context` meets below it.

  Read off each declaring kind's argument root at `pred` and at each super-predicate the
  kind's roster names (`tax/props-over`), so the read is bounded by the declarations
  written of `pred`'s ancestors.  The super-predicates are read over every `genl` edge,
  since an edge stated below `context` binds `pred` there; each candidate is asked again
  from its placement (`checks/declaration-entailments`).  Empty, with no index read, when
  no `genlCx` edge comes up to `context` (`tax/context-children-global`)."
  [kb pred context]
  (let [tax (reasoning/taxonomy kb)]
    (if-not (and (symbol? pred) (seq (tax/context-children-global tax context)))
      []
      (let [idx  (:index kb)
            recs (:records kb)]
        (into []
              (for [k     (nm/sort-by-content-key nm/name-key compare (keys entailing-declarations))
                    s     (nm/sort-by-content-key
                           nm/name-key compare
                           (tax/props-over tax (tax/arg-declaration-props k) pred))
                    h     (sort (reads/as-stored-with-args idx k {1 s}))
                    :let  [dsx (p/get-sentex recs h)]
                    :when (and dsx (= (entailing-declarations k) (nm/arity (:sentence dsx)))
                               (= s (second (:sentence dsx))))
                    :let  [pl (pair-placements kb context (:context dsx))]
                    :when (and (seq pl) (not= [context] pl))]
                [h pl]))))))

(defn deduce-below
  "Materialize what the declarations `declarations-below` finds say about the fact
  `sentence` stored at `handle` in `context`, at each of their placements:
  `{:new [handles] :violations [v]}`.  Each mint names the fact, the declaration and the
  `genlCx` edges its placement sees both through (`checks/declaration-entailments`).  The
  assert path and `chain/place-conclusion` call it beside `deduce-arg-types`.  `keep?`,
  when given, takes an entailment and its placement."
  ([kb sentence handle context] (deduce-below kb sentence handle context nil))
  ([kb sentence handle context keep?]
   (if-not checks/*assertive-arg-types?*
     empty-entailment-result
     (reduce (fn [acc [dh pl]]
               (reduce (fn [acc pctx]
                         (let [es (checks/declaration-entailments kb sentence pctx dh handle)]
                           (merge-with into acc
                                       (deduce-arg-types
                                        kb (cond->> es keep? (filterv #(keep? % pctx)))
                                        handle pctx))))
                       acc pl))
             empty-entailment-result
             (declarations-below kb (nm/functor sentence) context)))))

(defn- deduce-placed
  "Materialize every entailment of the stored literal fact `sentence` at `handle` in
  `context`: those of the declarations `context` sees, there (`deduce-arg-types`), and
  those of the declarations below it, at their placements (`deduce-below`).  `keep?`,
  when given, takes an entailment and its placement."
  ([kb sentence handle context] (deduce-placed kb sentence handle context nil))
  ([kb sentence handle context keep?]
   (merge-with into
               (deduce-arg-types
                kb (cond->> (checks/constraint-entailments kb sentence context)
                     keep? (filterv #(keep? % context)))
                handle context)
               (deduce-below kb sentence handle context keep?))))

(defn- retroactive-mints
  "The entailments a newly stored declaration `dh` draws over one already-stored sentex
  `sx`, materialized at each placement of the pair (`placements`, a fn of `sx`'s context;
  `placements-of` by default).

  The stored sentex is put back through `checks/declaration-entailments`, which is
  `checks/constraint-entailments` narrowed to this declaration, rather than the
  conditions being re-decided here: the two directions must agree about what a
  declaration entails, and the only way to be sure of that is for them to ask the same
  function.

  A genuine negation is not argument-checked, so it entails nothing; nor does a rule,
  whose stored sentence is an implication."
  ([kb sx dh] (retroactive-mints kb sx dh (placements-of kb dh)))
  ([kb sx dh placements]
   (if-not (and (nil? (:antecedent sx)) (not (sx/negative? sx)))
     empty-entailment-result
     (let [sctx (:context sx)
           h    (:id sx)]
       (reduce (fn [acc pctx]
                 (merge-with into acc
                             (deduce-arg-types
                              kb (checks/declaration-entailments kb (:sentence sx) pctx dh
                                                                 (when (not= pctx sctx) h))
                              h pctx)))
               empty-entailment-result
               (placements sctx))))))

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
  snapshot or a live view.

  With `limit`, the walk stops after `limit` sentexes, visiting the predicates in content
  order and each posting in the index's own order, so a budgeted caller reads a prefix
  and no more of the extent.  With `contexts`, a set, only the sentexes stated in one of
  them are read (`reads/as-stored-with-functor-in`)."
  ([kb pred] (subtree-sentexes kb pred nil))
  ([kb pred limit] (subtree-sentexes kb pred limit nil))
  ([kb pred limit contexts]
   (let [idx   (:index kb)
         recs  (:records kb)
         preds (filter #(pos? (reads/stored-count-with-functor idx %))
                       (tax/specs-global (reasoning/taxonomy kb) pred))
         read  (if contexts
                 #(reads/as-stored-with-functor-in idx % contexts)
                 #(reads/as-stored-with-functor idx %))]
     (into [] (cond-> (comp (mapcat read)
                            (distinct)
                            (keep #(p/get-sentex recs %)))
                limit (comp (take limit)))
           (cond->> preds limit (sort-by nm/name-key))))))

(defn- declared-types
  "The types an entailing declaration mints memberships in: the last argument of every
  kind but `interArg`, whose target type `U` of `(interArg P n T m U)` is its fifth."
  [sentence]
  (case (nm/functor sentence)
    interArg [(nth sentence 5)]
    (when (contains? entailing-declarations (nm/functor sentence))
      [(last sentence)])))

(defn- mintable-fn
  "`checks/mintable-type?` over `kb`'s genl hierarchy as it stands, as a fn of one type."
  [kb]
  (partial checks/mintable-type? (reasoning/taxonomy kb)))

(defn- unmintable-declaration?
  "Does the declaration `sentence` name a type `mintable?` refuses?  `mintable?` is
  `mintable-fn`'s, or `checks/mintable-types` over a walk the hierarchy does not move
  under."
  [mintable? sentence]
  (boolean (some #(not (mintable? %)) (declared-types sentence))))

(defn- note-unmintable!
  "Remember declaration `dh` in the refusal record when its type is not yet one a
  membership can be minted in, stamped with the taxonomy generations that answer was
  read under.

  `mintable-type?` reads the hierarchy as it stands, so a declaration whose type gains
  its path to `thing` after the declaration and its facts are stored minted nothing in
  that order and everything in the other.  The entry is what `settle` re-asks when a
  generation moves (`released-mints`), and once the type is mintable the declaration's
  whole sweep runs again (`entail-existing`), reaching every fact stored meanwhile.  Kept
  under the declaration's handle, where a rule's refusals are kept under the rule's.
  True when it noted the entry."
  [kb mintable? sentence dh]
  (when (unmintable-declaration? mintable? sentence)
    (note-pending! kb dh {:mint true :gens (taxonomy-generations kb)} :mint)
    true))

(defn mint-refusals
  "The declarations waiting on a type to become mintable, as `[decl-handle entry]`
  pairs in handle order — empty on nearly every KB.  With `gens`, only the entries
  stamped under other generations, compared before the sort, so a settle pass under
  unmoved generations sorts nothing."
  ([kb] (mint-refusals kb nil))
  ([kb gens]
   (into [] (sort-by first (cond->> (kind-entries @(reasoning/refused kb) :mint)
                             gens (remove #(= gens (:gens (second %)))))))))

(defn entail-existing
  "When an `(arg P n T)` / `(genlArg P n T)` / `(interArg P n T m U)` declaration
  arrives, draw what it now says about the `(P …)` sentexes **already stored** — so a
  declaration arriving after the facts reaches them exactly as one arriving before
  reaches the facts that follow.  Same `{:new :violations}` result, so the types it mints
  are chaining seeds like any other new content.  nil when `sentence` is not an argument
  constraint.

  `triggered-mints` reaches a conditional form's trigger arriving after both the fact
  and the declaration, in the settle.

  Sweeps what is **stored**, not what is believed, for `lift-existing`'s reason: a type
  minted off a defeated fact is justified by that fact and so is defeated too — the
  JTMS already says what a disbelieved antecedent means — whereas skipping it would
  leave the type missing when the fact revives, which is belief depending on the order
  the defeat and the declaration arrived in.

  The extent is read off the **predicate extents of `P`'s whole spec subtree**, which is the
  precise answer to \"every stored tuple this declaration constrains\": a declaration on
  `P` binds every predicate beneath it (`res/constraining-predicates`), so an extent read
  off `P` alone would mint over `(parentOf …)` and not over `(fatherOf …)` —
  a type the same three sentences produce in one arrival order and not the other.
  `subtree-sentexes` reads it, and snapshots it before the first mint.

  A declaration whose type is not mintable reads no extent: every arm asks
  `checks/mintable-type?` of that type before it draws, so no fact would yield an
  entailment, and the entry `note-unmintable!` leaves runs the sweep once it is."
  [kb sentence dh]
  (when checks/*assertive-arg-types?*
    (let [[f pred] sentence]
      (when (and (= (entailing-declarations f) (nm/arity sentence)) (symbol? pred))
        (if (note-unmintable! kb (mintable-fn kb) sentence dh)
          empty-entailment-result
          (let [placements (placements-of kb dh)]
            (reduce (fn [acc sx] (merge-with into acc (retroactive-mints kb sx dh placements)))
                    empty-entailment-result
                    (subtree-sentexes kb pred))))))))

(defn release-mint!
  "Re-ask declaration `dh`'s waiting entry under generations `gens`, with `mintable?`
  answering for its types (`unmintable-declaration?`): `{:new [handle …]}` with the types
  its sweep minted once the type is mintable, the entry restamped when it still is not
  (`:waits` then names the types `mintable?` refuses), and the entry retired when the
  declaration has left the store.

  `entail-existing` is the sweep a declaration arriving after its facts runs, so the
  mints are the ones the other arrival order made, deduplicated on content."
  [kb dh gens mintable?]
  (let [sx (p/get-sentex (:records kb) dh)]
    (cond
      (nil? sx)
      (do (drop-pending! kb dh :mint) empty-entailment-result)

      (unmintable-declaration? mintable? (:sentence sx))
      (do (note-pending! kb dh {:mint true :gens gens} :mint)
          (assoc empty-entailment-result
                 :waits (into [] (remove mintable?) (declared-types (:sentence sx)))))

      :else
      (do (drop-pending! kb dh :mint)
          (or (entail-existing kb (:sentence sx) dh) empty-entailment-result)))))

;; ---- a mint the KB holds more specifically ---------------------------------
;; `checks/subsumed-mint` reads whether a minted type is one a believed record already
;; says more precisely.  The mint path above withholds a record it answers for; the
;; settle takes care of the other two directions, which are the functions below:
;;
;; - **withdrawal** — the specific membership, or the edge that makes it specific or
;;   visible, lands after the mint is stored, so the record has to *leave*
;;   (`subsumed-mint-blocks`);
;; - **release** — a record that could have been what subsumed a mint leaves belief or
;;   the store, so the mints about its term are drawn again (`withheld-releases`).
;;
;; A withdrawal is a **block**, not a retraction: the mint's supporters are all still
;; there and still entail it, so a dependency-directed retraction finds it groundable
;; and keeps it (`jtms/retract!`).  Blocking the justification is what `exceptWhen`
;; does to a firing it excepts, and the sweep that follows collects the record exactly
;; as it collects an excepted conclusion (docs/exceptions.md).
;;
;; Nothing remembers a withheld mint.  The release re-derives it from the facts about the
;; departing record's term, which is what the store says, so a KB rebuilt from its store
;; releases what the KB that withheld it releases (docs/argtypes.md).

(defn- mint-only?
  "Is `h` a record the argument entailment alone holds up — no premise support, at least
  one justification, and every one of them an argument declaration's?

  A record an author asserted, or a rule concluded, is not this feature's to withdraw:
  the mint may be redundant, but the record is somebody else's claim.

  Read off the **network**, which keeps each justification's informant, rather than off
  the store: this is asked of every candidate the trigger turns up, and fetching a record
  per justification to read one field of it is the cost `record_fetch_cost_test` counts."
  [kb h]
  (let [tms (reasoning/tms kb)]
    (and (not (jtms/premise? tms h))
         (let [js (keep #(jtms/justification tms %) (jtms/supports tms h))]
           (and (seq js) (every? #(mint-informants (:informant %)) js))))))

(defn- rests-on?
  "Does the support of `h` reach `mint` — is the membership that would make `mint`
  redundant itself derived from it?

  The one shape a block cannot take: withdrawing the mint would take the membership with
  it, which would release the mint, which would derive the membership again.  The walk is
  the support closure, each node visited once; the shipped ontology has no such pair, and
  a KB that writes one keeps both records."
  [kb h mint]
  (let [tms (reasoning/tms kb)]
    (loop [seen #{} frontier [h]]
      (if-let [x (peek frontier)]
        (let [antes (into [] (comp (keep #(jtms/justification tms %))
                                   (mapcat :antecedents)
                                   (remove seen))
                          (jtms/supports tms x))]
          (if (some #(= mint %) antes)
            true
            (recur (into seen antes) (into (pop frontier) antes))))
        false))))

(defn- says-more-than?
  "Does the record `by` say, in `context`, what `sentence` says and more precisely?

  The subsumption test `checks/subsumed-mint` makes, asked of **one** candidate rather
  than searched for: the trigger is already holding the record that moved, so running that
  search — the term's slot roster, then a fetch per predicate above the type — would be
  looking up what the caller has in hand.  `context` is the mint's, since that is the
  vantage its record is read from, and `by` counts only where that context sees it."
  [kb sentence context by]
  (let [tax (reasoning/taxonomy kb)
        s   (:sentence by)]
    (boolean
     (and (tax/sees? tax context (:context by))
          (cond
            (and (membership-shaped? sentence) (membership-shaped? s))
            (and (= (first (nm/args sentence)) (first (nm/args s)))
                 (not= (nm/functor s) (nm/functor sentence))
                 (tax/genl? tax (nm/functor s) (nm/functor sentence) context))

            (and (edge-shaped? sentence) (edge-shaped? s))
            (and (= (nth sentence 1) (nth s 1))
                 (not= (nth s 2) (nth sentence 2))
                 (tax/genl? tax (nth s 2) (nth sentence 2) context)))))))

(defn- withdrawable-mint
  "The handle of the record that makes the mint at `h` redundant, or nil when the mint
  stays.  `by` is the moved record the trigger holds when that record is the only one that
  can be the subsumer (a membership, or an edge out of the mint's own term), and nil when
  the subsumer is some other record the move made reach further, which
  `checks/subsumed-mint` then finds.

  Four conditions, cheapest first: the candidate is not `by` itself; it is the
  entailment's own record (`mint-only?`, network reads); a believed record says it more
  specifically in its own context (the taxonomy, or the index behind `subsumed-mint`); and
  that record does not rest on it (a support walk, asked of the few that get this far)."
  [kb h by]
  (when (and (not= h (:id by)) (mint-only? kb h))
    (let [sx (p/get-sentex (:records kb) h)]
      (when (and sx (nil? (:antecedent sx)))
        (when-let [s (if by
                       (when (says-more-than? kb (:sentence sx) (:context sx) by) (:id by))
                       (checks/subsumed-mint kb (:sentence sx) (:context sx)))]
          (when-not (rests-on? kb s h) s))))))

(defn- roster-members-in
  "The terms some mint is about that hold a stored membership `(z x)` with `z` in `below`,
  a spec closure — the members `subtree-sentexes` would name, narrowed to the mint family.

  Read from the smaller side.  The extent below a type the ontology states an edge out of
  can be most of a corpus while the terms holding a mint are few, and walking the extent
  pages one record per membership to learn its term; walking the mint terms pages only each
  term's own unary facts (`unary-sentexes-with-arg`), so the choice is made by comparing
  the two counts, both index cardinality reads.  Stored rather than believed, as
  `subtree-sentexes` is."
  [kb below]
  (let [idx    (:index kb)
        recs   (:records kb)
        specs  (into #{} (filter #(pos? (reads/stored-count-with-functor idx %))) below)
        extent (transduce (map #(reads/stored-count-with-functor idx %)) + 0 specs)]
    (if (< (reads/stored-mint-term-count idx) extent)
      (filter (fn [x]
                (some (fn [h]
                        (when-let [sx (p/get-sentex recs h)]
                          (let [sen (:sentence sx)]
                            (and (membership-shaped? sen)
                                 (= x (first (nm/args sen)))
                                 (contains? specs (nm/functor sen))))))
                      (p/unary-sentexes-with-arg idx x)))
              (reads/as-stored-mint-terms idx))
      (into [] (comp (mapcat #(reads/as-stored-with-functor idx %))
                     (distinct)
                     (keep #(p/get-sentex recs %))
                     (map :sentence)
                     (filter membership-shaped?)
                     (map #(first (nm/args %)))
                     (distinct)
                     (filter #(reads/stored-mint-term? idx %)))
            specs))))

(defn- withdrawal-candidates
  "The minted records that `sx` — a sentex this settle moved — can have made redundant, as
  `[handle by]` pairs for `withdrawable-mint`, read off the mint family.

  - A **membership** `(T x)` subsumes the mints about `x`.
  - A **`genl` edge** `(genl sub super)` subsumes the edges minted out of `sub` itself.
    The route it gives the types and members under `sub` is `edge-route-candidates`',
    asked once for every edge the settle moved.
  - A **`genlCx` edge** shows every context under `sub` what `super` holds, so the mints
    stated in those contexts are asked the whole question.  The contexts are read off
    whichever of the mints' contexts and `sub`'s descendants is fewer: each mint context
    that sees `sub`, or `tax/context-down` of `sub`, which filters every descendant by
    what it sees.  A `recover` moves every `genlCx` edge, and a lattice
    where most contexts sit under a few holds far more descendants than mint contexts.
    The unscoped `tax/context-down-global` is read for its size alone, to pick the
    side; it is not scoped because it answers nothing, and both sides are.

  A fact of any other shape moves no subsumption and reads nothing."
  [kb sx]
  (let [s   (:sentence sx)
        idx (:index kb)]
    (cond
      (membership-shaped? s)
      (for [h (reads/as-stored-mints-about idx (first (nm/args s)))] [h sx])

      (edge-shaped? s)
      (for [h (reads/as-stored-mints-about idx (nth s 1))] [h sx])

      (context-edge-shaped? s)
      (let [tax (reasoning/taxonomy kb)
            sub (nth s 1)]
        (for [c (if (< (reads/stored-mint-context-count idx)
                       (count (tax/context-down-global tax sub)))
                  (filter #(and (some? %) (tax/sees? tax % sub))
                          (reads/as-stored-mint-contexts idx))
                  (tax/context-down tax sub))
              h (reads/as-stored-mints-in idx c)]
          [h nil])))))

(defn- edge-route-candidates
  "The mints the `genl` edges the records in `edges` install (`tax/installed-edges`: a `genl`
  edge, or a cover's edge per part) gave a route they did not have, as `[handle nil]`
  pairs: the mints about every type strictly under an edge's `sub`, and about every
  member of a type under one.  Each is asked the whole
  question, since the record that subsumes it is the membership or edge below, not the
  edge that moved.

  **One walk for all the edges.**  Asked per edge, the types under each `sub` are a
  closure of their own, and a settle that moves every edge at once — a `recover`, where
  every record comes IN — pays the sum of those closures, which counts a subtree once per
  edge above it rather than once.  The union is `tax/specs-of-all`, one traversal, and the
  members below it one read from whichever of the mint terms and the extent is smaller.  A
  single edge keeps `tax/specs-global` and its memo.

  \"Strictly\" is per edge: a `sub` counts when it sits under another edge's `sub`, which
  its own ancestors (`tax/genls-global`) answer, and only a `sub` holding a mint is asked.

  Unscoped (E17) for `checks/subsumed-mint`'s reason: the mints sit in contexts other than
  the edges', and each candidate is asked in its own context, so the unscoped walk only
  asks more candidates than a scoped one."
  [kb edges]
  (let [idx  (:index kb)
        subs (into #{} (comp (mapcat #(tax/installed-edges (:sentence %))) (map first)) edges)]
    (when (and (seq subs) (pos? (reads/stored-mint-count idx)))
      (let [tax     (reasoning/taxonomy kb)
            below   (if (= 1 (count subs))
                      (tax/specs-global tax (first subs))
                      (tax/specs-of-all tax subs))
            strict? (fn [z]
                      (or (not (contains? subs z))
                          (some #(and (not= z %) (contains? subs %)) (tax/genls-global tax z))))
            types   (if (< (reads/stored-mint-term-count idx) (count below))
                      (filter #(contains? below %) (reads/as-stored-mint-terms idx))
                      (filter #(reads/stored-mint-term? idx %) below))]
        (distinct
         (for [x (concat (filter strict? types) (roster-members-in kb below))
               h (reads/as-stored-mints-about idx x)]
           [h nil]))))))

(defn surplus-placements
  "The mint justifications, in id order, that a `genlCx` edge among `edges` (sentexes)
  left at a context that is no longer a placement of their fact and declaration
  (`pair-placements`).  An edge arriving can give the two a more general common
  descendant, and the placement under it then goes, so the store holds the same mints in
  every arrival order.  Every placement an edge can displace lies under its `sub`, and the
  mints stated there are read off the mint family (`withdrawal-candidates`).  A
  justification at its fact's own context is not asked: that context sees the
  declaration while the `genlCx` edges the justification names hold.  The caller reads
  the gate: the entailment on and the mint family holding a record."
  [kb edges]
  (when (seq edges)
    (let [tms (reasoning/tms kb)
          cx  (fn [h] (:context (p/get-sentex (:records kb) h)))]
      (into (sorted-set)
            (for [e     edges
                  [h _] (withdrawal-candidates kb e)
                  :let  [c (cx h)]
                  jid   (jtms/supports tms h)
                  :let  [j (jtms/justification tms jid)]
                  :when (and j (mint-informant? (:informant j)))
                  :let  [[f d] (:antecedents j)
                         fc    (cx f)]
                  :when (and fc (not= c fc)
                             (not-any? #{c} (pair-placements kb fc (cx d))))]
              jid)))))

(defn note-unpremised!
  "Queue the record at `h`, whose premise mark a retraction removed while a derivation
  still holds it up, for the settle's withdrawal question: a record an author stated
  beside a mint of the same sentence is not the entailment's to withdraw, and once the
  statement goes it is (`mint-only?`), so a believed record that says it more
  specifically withdraws it as it withdraws a mint it meets on arrival."
  [kb h]
  (when (and checks/*assertive-arg-types?* checks/*prune-subsumed-mints?*)
    (swap! (reasoning/mint-queues kb) update :unpremised (fnil conj []) h)))

(defn- drain-unpremised!
  "The handles `note-unpremised!` queued since the last drain, and the queue emptied."
  [kb]
  (let [[old] (swap-vals! (reasoning/mint-queues kb) dissoc :unpremised)]
    (:unpremised old)))

(defn subsumed-mint-blocks
  "The justifications to block because the records they hold up are redundant, and the
  records — `{:blocked #{jid} :withdrawn #{handle}}` over the records the sentexes in
  `moved` can have displaced.

  Every justification of a withdrawn record, because a record survives on any one of
  them: two facts can entail the same type, and blocking one would leave the record
  standing on the other, so how many facts happened to entail it would decide whether it
  stayed.

  `moved` is a **delay** over the region's records, and the gates in front of it decide
  whether it is ever forced: off unless the entailment is on, off unless the mint is
  prunable, and off while the mint family is empty.  A KB holding no mint therefore
  fetches no record here however much it asserts, which is what `record_fetch_cost_test`
  counts.  Forced, the region is filtered by **shape** (`subsumer-shaped?`) and the
  candidates are the mint family's (`withdrawal-candidates` per record,
  `edge-route-candidates` once for all the `genl` edges the records install), so a
  membership about a term holding no mint reads nothing.

  Only a record that **became** believed is asked, which is what keeps this off the price
  of a settle that relabels a large region without moving much of it — a qualitative
  network relabels its whole network per fact and moves a handful of nodes.

  The records a retraction left standing on a derivation alone (`note-unpremised!`) are
  asked too, each the whole question.

  A `genlCx` edge among the moved records is also asked which mint placements it
  displaced (`surplus-placements`), with pruning on or off; those justifications are
  returned under `:surplus`, for the settle to drop.

  `asked` is the settle's own record of which of them it has already put this question to,
  and a record is asked **once per settle** however many passes relabel it.  Nothing is
  missed by that: a mint stored *after* a pass examined its subsumer never reaches the
  store, since `entail-arg-type` asks the same question of every mint it is about to
  write.  `believed?` is belief now, `jtms/in?` or own-context belief."
  [kb moved was-in asked believed?]
  (let [tms    (reasoning/tms kb)
        lost   (drain-unpremised! kb)
        prune? (and checks/*assertive-arg-types?* checks/*prune-subsumed-mints?*)
        moved  (when (and checks/*assertive-arg-types?*
                          (pos? (reads/stored-mint-count (:index kb))))
                 (seq (filter #(let [s (:sentence %)
                                     h (:id %)]
                                 (and (nil? (:antecedent %))
                                      (not (contains? @asked h))
                                      ;; the transition, not the region: a record the
                                      ;; settle relabelled without moving subsumes exactly
                                      ;; what it subsumed before, and most of a relabelled
                                      ;; region does not move (`jtms/touched-in`)
                                      (believed? h)
                                      (not (contains? was-in h))
                                      (subsumer-shaped? s)))
                              @moved)))
        surplus (surplus-placements kb (filter #(context-edge-shaped? (:sentence %)) moved))]
    (vswap! asked into (map :id) moved)
    (cond->
     (when (and prune? (or moved (seq lost)))
       (reduce
        ;; `:withdrawn` keeps a mint two moved records displace from being withdrawn twice;
        ;; a mint one of them does not displace is still asked of the next
        (fn [acc [h by]]
          (if (or (contains? (:withdrawn acc) h) (not (withdrawable-mint kb h by)))
            acc
            (-> acc
                (update :withdrawn conj h)
                (update :blocked into
                        (comp (keep #(jtms/justification tms %)) (map :id))
                        (jtms/supports tms h)))))
        {:blocked #{} :withdrawn #{}}
        (concat (mapcat #(distinct (withdrawal-candidates kb %)) moved)
                (edge-route-candidates kb (filter #(seq (tax/installed-edges (:sentence %))) moved))
                (map (fn [h] [h nil]) lost))))
      ;; a placement an edge displaced leaves by a drop of its own justification, so
      ;; another support of the record keeps it; a dropped one is not also blocked
      (seq surplus) (-> (or {:blocked #{} :withdrawn #{}})
                        (update :blocked #(reduce disj % surplus))
                        (assoc :surplus surplus)))))

(defn note-departure!
  "Queue `sentex`, leaving the store, for `withheld-releases` when it is a record that can
  have subsumed a mint (`subsumer-shaped?`) and pruning is on, or a `genlCx` edge, whose
  departure can give a mint pair a placement back (`departed-context-edge-mints`).  Called
  from `integrate/sentex-removed!`, the one place a record leaves."
  [kb sentex]
  (when checks/*assertive-arg-types?*
    (let [s (sx/sentence-of sentex)]
      (when (if checks/*prune-subsumed-mints?*
              (subsumer-shaped? s)
              (context-edge-shaped? s))
        (swap! (reasoning/mint-queues kb) update :departed (fnil conj [])
               (assoc (select-keys sentex [:id :context]) :sentence s))))))

(defn drain-departures!
  "The records `note-departure!` queued since the last drain, and the queue emptied."
  [kb]
  (let [[old] (swap-vals! (reasoning/mint-queues kb) dissoc :departed)]
    (:departed old)))

(defn- any-declaring?
  "Does any predicate carry an entailing argument declaration?  Read off the taxonomy's
  global roster (`tax/arg-declaration-props`), so the gate every settle passes reads no
  index."
  [kb]
  (let [tax (reasoning/taxonomy kb)]
    (boolean (some #(seq (tax/props tax (tax/arg-declaration-props %)))
                   (keys entailing-declarations)))))

(defn- rederive-mints
  "Draw again the mints of each stored fact in `facts` that `keep?` accepts, as
  `deduce-placed` draws them for the fact arriving now: `{:new [handle …]}`.
  `keep?` takes the minted sentence and its placement.

  A mint already stored with this justification adds nothing (`has-justification?`), one
  a believed record still subsumes is withheld again, and the rest are written — so the
  call is idempotent and decides on current belief alone.  The violations are dropped:
  each was reported when the fact arrived, and a re-derivation exposes nothing new."
  [kb facts keep?]
  (reduce (fn [acc sx]
            (if-not (and (nil? (:antecedent sx)) (not (sx/negative? sx)))
              acc
              (update acc :new into
                      (:new (deduce-placed kb (:sentence sx) (:id sx) (:context sx)
                                           (fn [e c] (keep? (:assert e) c)))))))
          {:new []}
          facts))

(defn- facts-naming
  "The stored facts holding the symbol `x` as an argument, snapshotted before any mint
  is written."
  [kb x]
  (let [recs (:records kb)]
    (into []
          (comp (keep #(p/get-sentex recs %))
                (filter #(some #{x} (rest (:sentence %)))))
          (reads/as-stored-with-term (:index kb) x))))

(defn- released-terms
  "The terms whose withheld mints the departure of `sx` can release, for `mints-about`:
  a membership `(T x)` or an edge `(genl x S)` subsumed the mints about `x`, and each
  edge `(genl sub super)` a record installs (`tax/installed-edges`, so a cover's per part) was
  also a route from every type under `sub` and every member of one — the terms
  `edge-route-candidates` asks about when the same record arrives."
  [kb sx]
  (let [s (:sentence sx)]
    (cond
      (membership-shaped? s) [(first (nm/args s))]

      (seq (tax/installed-edges s))
      (into []
            (comp (map first)
                  (mapcat (fn [sub]
                            (into (vec (tax/specs-global (reasoning/taxonomy kb) sub))
                                  (comp (map :sentence) (filter membership-shaped?)
                                        (map #(first (nm/args %))))
                                  (subtree-sentexes kb sub))))
                  (distinct))
            (tax/installed-edges s)))))

(defn- lost-contexts
  "The contexts a context under `sub` can have seen through the edge `(genlCx sub super)`
  and no longer sees, read after the edge left: `super`'s ancestor set less `sub`'s, in
  content order."
  [tax [_ sub super]]
  (let [kept (set (tax/context-up tax sub))]
    (into [] (remove kept)
          (nm/sort-by-content-key nm/name-key compare (tax/context-up tax super)))))

(defn- departed-context-edge-mints
  "Draw again, at the placements the taxonomy now gives (`pair-placements`), every mint
  pair an edge among `edges` (`genlCx` sentences that left) can have kept from a placement
  under its `sub`: `{:new [handle …] :violations [v …]}`.

  The edge's arrival left such a placement below a more general one, which the settle
  dropped (`surplus-placements`), and that general placement lies in a context `sub` saw
  only through the edge (`lost-contexts`).  So the pairs are read off the mint family in
  those contexts, each mint justification placed below its fact's context naming its fact
  and declaration, and the cost is the mints the edge reaches.  With subsumed mints
  pruned, a placement there can be withheld instead: the believed records stored there
  that can subsume a mint release the terms they name, as their departure would
  (`released-terms`)."
  [kb edges]
  (let [tax  (reasoning/taxonomy kb)
        tms  (reasoning/tms kb)
        idx  (:index kb)
        recs (:records kb)
        cx   #(:context (p/get-sentex recs %))
        lost (into [] (comp (mapcat #(lost-contexts tax %)) (distinct)) edges)
        pairs (into (sorted-set)
                    (for [c     lost
                          h     (reads/as-stored-mints-in idx c)
                          jid   (jtms/supports tms h)
                          :let  [j (jtms/justification tms jid)]
                          :when (and j (mint-informant? (:informant j)))
                          :let  [[f d] (:antecedents j)]
                          :when (not= c (cx f))]
                      [f d]))
        mints (reduce (fn [acc [d fs]]
                        (let [pl (placements-of kb d)]
                          (reduce (fn [acc f]
                                    (if-let [sx (p/get-sentex recs f)]
                                      (merge-with into acc (retroactive-mints kb sx d pl))
                                      acc))
                                  acc (map second fs))))
                      empty-entailment-result
                      (group-by first (map (fn [[f d]] [d f]) pairs)))]
    (if-not checks/*prune-subsumed-mints?*
      mints
      (let [terms (->> lost
                       (into [] (comp (mapcat #(reads/as-stored-in-context idx %))
                                      (keep #(p/get-sentex recs %))
                                      (filter #(and (subsumer-shaped? (:sentence %))
                                                    (not (context-edge-shaped? (:sentence %)))
                                                    (jtms/in? tms (:id %))))
                                      (mapcat #(released-terms kb %))
                                      (filter symbol?)
                                      (distinct)))
                       (sort-by nm/name-key))]
        (reduce (fn [acc x]
                  (merge-with into acc
                              (rederive-mints kb (facts-naming kb x)
                                              (fn [s _] (= x (roster-term s))))))
                mints
                terms)))))

(defn withheld-releases
  "The mints no longer withheld because a record that subsumed them left, and the
  justifications a withheld mint owes a record of its sentence that arrived: `{:new
  [handle …]}`, drawn by `rederive-mints` (docs/argtypes.md, \"Nothing records a withheld
  mint\").

  The departures are the records `note-departure!` queued as they left the store, and the
  records in `moved` (a delay over the settle's region) that went IN ⇒ OUT against
  `was-in`; the arrivals are the ones that came IN.  `believed?` is belief now.
  `withdrawn` holds the mints this settle withdrew, which release nothing.  `asked` holds
  what this settle has already asked, so each record is asked once per settle however
  many passes relabel it.  The queue is drained whether or not the gates pass.

  A `genlCx` edge among the departures also draws again the mint pairs it can have kept
  from a placement (`departed-context-edge-mints`), with pruning on or off."
  [kb moved was-in asked withdrawn believed?]
  (let [queued (drain-departures! kb)
        prune? checks/*prune-subsumed-mints?*
        idx    (:index kb)]
    (when (and checks/*assertive-arg-types?* (any-declaring? kb)
               (or prune? (pos? (reads/stored-mint-count idx))))
      (let [;; the transition, not the region, as `subsumed-mint-blocks` reads it
            moves  (into []
                         (filter #(let [s (:sentence %) h (:id %)]
                                    (and (nil? (:antecedent %))
                                         (not (contains? @asked h))
                                         (not (contains? withdrawn h))
                                         (not= (contains? was-in h) (believed? h))
                                         (if prune? (subsumer-shaped? s) (context-edge-shaped? s)))))
                         @moved)
            out    (into (into [] (remove #(contains? withdrawn (:id %))) queued)
                         (remove #(believed? (:id %)))
                         moves)
            placed (departed-context-edge-mints
                    kb (into [] (comp (map :sentence) (filter context-edge-shaped?)) out))]
        (vswap! asked into (map :id) moves)
        (if-not prune?
          (select-keys placed [:new])
          (let [twins (filter #(let [s (:sentence %)]
                                 (and (believed? (:id %))
                                      (not (context-edge-shaped? s))
                                      (not (when-let [x (roster-term s)]
                                             (reads/stored-mint? idx x (:context %) (:id %))))
                                      (checks/subsumed-mint kb s (:context %))))
                              moves)
                terms (->> (remove #(context-edge-shaped? (:sentence %)) out)
                           (mapcat #(released-terms kb %))
                           (filter symbol?)
                           distinct
                           (sort-by nm/name-key))
                tax   (reasoning/taxonomy kb)]
            (merge-with
             into
             (select-keys placed [:new])
             (reduce (fn [acc x]
                       (merge-with into acc (rederive-mints kb (facts-naming kb x)
                                                            (fn [s _] (= x (roster-term s))))))
                     {:new []}
                     terms)
             (reduce (fn [acc sx]
                       (let [s (:sentence sx) c (:context sx)]
                         (merge-with into acc (rederive-mints kb (facts-naming kb (roster-term s))
                                                              (fn [s' c'] (and (= s s') (= c c')))))))
                     {:new []}
                     twins)
             (rederive-mints kb
                             (into []
                                   (comp (filter #(context-edge-shaped? (:sentence %)))
                                         (mapcat #(sort-by nm/name-key
                                                           (tax/context-down tax (nth (:sentence %) 1))))
                                         (distinct)
                                         (mapcat #(reads/as-stored-in-context idx %))
                                         (keep #(p/get-sentex (:records kb) %)))
                                   out)
                             (fn [s _] (some? (roster-term s)))))))))))

(defn- declaring-predicates
  "The predicates an entailing argument declaration is written of, off the taxonomy's
  global roster (`tax/arg-declaration-props`) — no index read.  With `kinds`, only the
  declarations of those functors."
  ([kb] (declaring-predicates kb (keys entailing-declarations)))
  ([kb kinds]
   (let [tax (reasoning/taxonomy kb)]
     (reduce (fn [acc k] (into acc (tax/props tax (tax/arg-declaration-props k))))
             #{}
             kinds))))

(defn- entail-over
  "Draw the entailments of each stored literal fact in `facts` at their placements, as
  `deduce-placed` draws them for a fact arriving now: `{:new :violations}`.  With
  `kinds`, only the entailments of those declaring functors."
  ([kb facts] (entail-over kb facts nil))
  ([kb facts kinds]
   (reduce (fn [acc sx]
             (if-not (and (nil? (:antecedent sx)) (not (sx/negative? sx)))
               acc
               (merge-with into acc
                           (deduce-placed kb (:sentence sx) (:id sx) (:context sx)
                                          (when kinds (fn [e _] (contains? kinds (:kind e))))))))
           empty-entailment-result
           facts)))

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
       (boolean (some (declaring-predicates kb)
                      (tax/genls-global (reasoning/taxonomy kb) super)))))

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
  and the edge's other consequences are `subsumption-seeds`'; off unless some predicate
  carries an entailing declaration (`declaring-predicates`, the taxonomy's roster, no
  index read); and off unless a genl-ancestor of `super` carries one
  (`super-reaches-declaration?`).  The first two
  keep an edge under a predicate nobody constrained from reading a subtree's extent to
  discover there was nothing to draw; the third keeps an edge whose `sub` is constrained
  but whose `super` reaches no declaration from reading it, since every mint this arm
  draws cites the arriving edge and so reaches its declaring predicate through `super`.
  The extent itself is `subtree-sentexes`, filtered by cardinality for the same reason
  one step further in."
  [kb sentence]
  (when (and checks/*assertive-arg-types?*
             (= 'genl (nm/functor sentence))
             (seq (declaring-predicates kb))
             (super-reaches-declaration? kb (nth sentence 2)))
    (let [[_ sub] sentence]
      (when (symbol? sub)
        (reduce (fn [acc sx]
                  (if-not (and (nil? (:antecedent sx)) (not (sx/negative? sx)))
                    acc
                    (merge-with into acc
                                (deduce-placed kb (:sentence sx) (:id sx) (:context sx)))))
                empty-entailment-result
                (subtree-sentexes kb sub))))))

(defn- declared-functors
  "Every functor holding a stored sentex that an entailing declaration reaches — the specs
  of each declaring predicate (`declaring-predicates`, of `kinds` when given), in content
  order.  Unscoped (`tax/specs-global`, E17): the callers read facts across every context
  they are stored in, and each fact is put back through `checks/constraint-entailments`
  in its own context, so the unscoped walk only reads more facts than a scoped one."
  ([kb] (declared-functors kb (keys entailing-declarations)))
  ([kb kinds]
   (let [tax (reasoning/taxonomy kb)
         idx (:index kb)]
     (into []
           (comp (mapcat #(tax/specs-global tax %))
                 (distinct)
                 (filter #(pos? (reads/stored-count-with-functor idx %))))
           (nm/sort-by-content-key nm/name-key compare (declaring-predicates kb kinds))))))

(defn- declarations-meeting
  "Draw what each entailing declaration stated in a context of `below` says about the
  facts of its extent stated in a context of `seen` (`subtree-sentexes`), at the
  placements of each pair (`retroactive-mints`): `{:new :violations}`.  The declarations
  are read per kind off the predicate extent ending in `below`'s contexts
  (`reads/as-stored-with-functor-in`)."
  [kb below seen]
  (let [idx  (:index kb)
        recs (:records kb)]
    (reduce (fn [acc dsx]
              (let [dh (:id dsx)
                    pl (placements-of kb dh)]
                (reduce (fn [acc sx] (merge-with into acc (retroactive-mints kb sx dh pl)))
                        acc
                        (subtree-sentexes kb (second (:sentence dsx)) nil seen))))
            empty-entailment-result
            (for [k     (nm/sort-by-content-key nm/name-key compare (keys entailing-declarations))
                  h     (sort (reads/as-stored-with-functor-in idx k below))
                  :let  [dsx (p/get-sentex recs h)]
                  :when (and dsx (nil? (:antecedent dsx)) (not (sx/negative? dsx))
                             (= (entailing-declarations k) (nm/arity (:sentence dsx)))
                             (symbol? (second (:sentence dsx))))]
              dsx))))

(defn entail-under-context-edge
  "When a `(genlCx sub super)` edge arrives, draw what the declarations it makes visible
  say about the facts **already stored** in `sub` and every context under it — the fourth
  arrival order of an entailment through an inherited declaration, beside the fact, the
  declaration and the `genl` edge.  Each derivation names the `genlCx` edges it sees its
  declaration through (`checks/entailment-support`), so retracting this edge takes back
  what rests on it, and `rederive-descended` draws again what a second route still
  reaches.  nil when `sentence` is not a `genlCx` edge.

  The edge also gives a fact and a declaration a new common descendant, under `sub`, when
  one of them is stated where `super` sees it and the other in a context a context under
  `sub` sees and `super` does not (`below`, which holds the contexts under `sub`).  The
  facts are read from every context of `below`, and each draws at its placements
  (`deduce-placed`); the declarations stated in `below` draw over the facts stated where
  `super` sees them (`declarations-meeting`).  A placement the edge leaves below a more
  general one is dropped by the settle (`surplus-placements`).

  Off unless `*assertive-arg-types?*` and some predicate declares.  The facts are read
  from the smaller of two sides, compared by index counts: the facts stored in the
  contexts of `below`, kept when a declaration reaches their functor, or the facts of
  the functors a declaration reaches, kept when stored in `below`.  So the arm costs
  the lesser of the edge's extent and the declared extent, and a context holding many
  undeclared facts or a KB holding many declared ones elsewhere costs only the other.
  Snapshotted before the first mint."
  [kb sentence]
  (when (and checks/*assertive-arg-types?*
             (= 'genlCx (nm/functor sentence)) (= 3 (count sentence))
             (symbol? (nth sentence 1))
             (seq (declaring-predicates kb)))
    (let [recs  (:records kb)
          idx   (:index kb)
          tax   (reasoning/taxonomy kb)
          down  (tax/context-down tax (nth sentence 1))
          seen  (set (tax/context-up tax (nth sentence 2)))
          below (into (set down) (comp (mapcat #(tax/context-up tax %)) (remove seen)) down)
          ctxs  (nm/sort-by-content-key nm/name-key compare below)
          by-cx (reduce + 0 (map #(reads/stored-count-in-context idx %) ctxs))
          ;; a `sub` storing nothing below it reads no declared functor
          fs    (if (zero? by-cx) [] (declared-functors kb))
          by-fn (reduce + 0 (map #(reads/stored-count-with-functor idx %) fs))
          facts (if (<= by-cx by-fn)
                  (let [fset (set fs)]
                    (into []
                          (comp (mapcat #(reads/as-stored-in-context idx %))
                                (keep #(p/get-sentex recs %))
                                (filter #(contains? fset (nm/functor (:sentence %)))))
                          ctxs))
                  (let [cset (set ctxs)]
                    (into []
                          (comp (mapcat #(reads/as-stored-with-functor idx %))
                                (distinct)
                                (keep #(p/get-sentex recs %))
                                (filter #(contains? cset (:context %))))
                          fs)))]
      (merge-with into (entail-over kb facts) (declarations-meeting kb below seen)))))

(def ^:private trigger-declarations
  "The entailing declarations whose derivation waits on a trigger membership: `interArg`
  and the homogeneity forms (`checks/trigger-supports`)."
  '#{interArg interArgs interArgAndRest})

(defn- trigger-types
  "The types the stored `interArg` and homogeneity declarations read a trigger at: `T` of
  `(interArg P n T m U)`, `(interArgs R T)` and `(interArgAndRest R n T)`."
  [kb]
  (let [idx (:index kb) recs (:records kb)]
    (into #{}
          (comp (mapcat (fn [k] (map #(vector k %) (reads/as-stored-with-functor idx k))))
                (keep (fn [[k h]]
                        (let [s (:sentence (p/get-sentex recs h))]
                          (when (and (seq? s) (= k (nm/functor s)))
                            (case k
                              interArg        (when (= 6 (count s)) (nth s 3))
                              interArgs       (when (= 3 (count s)) (nth s 2))
                              interArgAndRest (when (= 4 (count s)) (nth s 3)))))))
                (filter symbol?))
          (sort trigger-declarations))))

(defn- trigger-shaped?
  "Is `sx` a stored literal that can be a trigger: a membership, or a record that
  installs `genl` edges?"
  [sx]
  (let [s (:sentence sx)]
    (and (nil? (:antecedent sx))
         (or (membership-shaped? s) (seq (tax/installed-edges s))))))

(defn- trigger-entailments
  "Draw what the trigger records `ins` (`trigger-shaped?`, believed) trigger over the
  stored facts naming the terms they type: `{:new [handle …] :violations [v …]}`, or nil
  when none reaches a trigger type.  A membership `(T x)` reaches the facts naming `x`; an
  edge `(genl sub super)` whose `super` reaches a trigger type reaches every member of a
  type under `sub` (`released-terms`).  Each such fact is put back through
  `checks/constraint-entailments` in its own context, narrowed to the trigger kinds, so
  the derivation names the membership and its route as the fact's own arrival would.

  The facts are read from the smaller of two sides, compared by index counts: the
  postings naming a term, kept when a trigger declaration reaches their functor, or the
  facts of those functors, kept when they name one of the terms, read once for every term
  whose postings outnumber them.  So a membership beside many declared facts that do not
  name its term reads only the term's postings.

  The trigger types are reached through `tax/genls-global` (E17): the facts are read
  across every context they are stored in, and each is asked its own context's
  declarations and memberships, so the unscoped gate only reads more facts."
  [kb ins]
  (when (seq ins)
    (let [tax    (reasoning/taxonomy kb)
          tts    (delay (trigger-types kb))
          ;; a membership or an edge triggers only through a trigger type it reaches
          reach? (fn [t] (or (contains? @tts t) (some @tts (tax/genls-global tax t))))
          terms  (->> ins
                      (mapcat (fn [sx]
                                (let [s (:sentence sx)]
                                  (if (membership-shaped? s)
                                    (when (reach? (nm/functor s)) [(first (nm/args s))])
                                    (when (some (fn [[_ super]] (reach? super))
                                                (tax/installed-edges s))
                                      (released-terms kb sx))))))
                      (filter symbol?)
                      distinct
                      (sort-by nm/name-key))]
      (when (seq terms)
        (let [idx    (:index kb)
              recs   (:records kb)
              fs     (declared-functors kb trigger-declarations)
              fset   (set fs)
              by-fn  (reduce + 0 (map #(reads/stored-count-with-functor idx %) fs))
              names  (fn [xs sx] (some xs (rest (:sentence sx))))
              ;; the declared extent, read once for every term whose postings outnumber it
              extent (fn [xs]
                       (into []
                             (comp (mapcat #(reads/as-stored-with-functor idx %))
                                   (distinct)
                                   (keep #(p/get-sentex recs %))
                                   (filter #(names xs %)))
                             fs))
              posted (fn [[x posting]]
                       (into []
                             (comp (keep #(p/get-sentex recs %))
                                   (filter #(and (contains? fset (nm/functor (:sentence %)))
                                                 (names #{x} %))))
                             posting))
              facts  (if (< by-fn (count terms))
                       (extent (set terms))
                       (let [{small true large false}
                             (group-by (fn [[_ posting]]
                                         (<= (bounded-count (inc by-fn) posting) by-fn))
                                       (map (fn [x] [x (reads/as-stored-with-term idx x)]) terms))]
                         (cond-> (into [] (mapcat posted) small)
                           (seq large) (into (extent (into #{} (map first) large))))))]
          (entail-over kb (into [] (distinct) facts)
                       trigger-declarations))))))

(defn triggered-mints
  "Draw what the memberships and `genl` edges among `moved` that came IN this settle
  trigger (`trigger-entailments`): `{:new [handle …] :violations [v …]}`.  A membership
  `(T x)` arriving after a fact and an `interArg` or homogeneity declaration over it is
  the trigger's arrival order, which the fact and the declaration cannot reach because
  the trigger did not hold when each arrived.  `was-in` and `believed?` are belief before
  the settle and now; `asked` holds the records this settle has asked."
  [kb moved was-in asked believed?]
  (when (and checks/*assertive-arg-types?*
             (seq (declaring-predicates kb trigger-declarations)))
    (let [ins (into []
                    (filter #(let [h (:id %)]
                               (and (not (contains? @asked h))
                                    (not (contains? was-in h))
                                    (believed? h)
                                    (trigger-shaped? %))))
                    @moved)]
      (vswap! asked into (map :id) ins)
      (trigger-entailments kb ins))))

(defn record-arg-types
  "Record the argument-type entailments every stored fact draws, over a store whose facts
  were written without them: `{:facts n :new [handle …] :violations [v …]}`.

  `assert` draws them as each fact arrives.  A store loaded around that path — a dump
  import, `*bulk-load?*`, `bulk-assert-facts!` — holds the facts and none of their
  derived memberships and edges, and `recover` rebuilds belief from the stored
  justifications without drawing any.  This is the one pass that records them, so the
  store then holds what a per-fact load of the same facts holds.  Run it once, after the
  load and after the store is recovered or reindexed, since the declarations and the
  hierarchy they name are read from the taxonomy.

  Facts are read per declared functor, every predicate under an entailing declaration
  in content order, and each fact is asked once whatever number of declarations reach
  it.  Idempotent: a derivation already recorded adds nothing (`has-justification?`)."
  [kb]
  (if-not checks/*assertive-arg-types?*
    (assoc empty-entailment-result :facts 0)
    (let [idx   (:index kb)
          recs  (:records kb)
          facts (into []
                      (comp (mapcat #(reads/as-stored-with-functor idx %))
                            (distinct)
                            (keep #(p/get-sentex recs %)))
                      (declared-functors kb))]
      (assoc (entail-over kb facts) :facts (count facts)))))

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
       empty-entailment-result
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
              empty-entailment-result
              (sx/defn-companion-rules sentence)))))

(defn- licensing-functors
  "The functors besides a rule antecedent's own whose facts move what that antecedent
  answers, for the antecedent keys of `roster` (`reads/as-stored-rule-keys`) — each
  re-join family of `chain/fire-rules-for` named by the facts it reacts to.

  - The predicates a `SupportingProver` reads, when some antecedent is one such a prover
    answers: a unit table decides a `quantityGreaterThan`.
  - A registered calculus's trigger predicates, when some antecedent is on a predicate
    the calculus answers: two `nonTangentialProperPart` facts entail a `partOfRegion`.
  - `transitive`, and the partners an `inverse` records hops on, when some antecedent is
    on a declared-transitive predicate: the declaration turns the walk on, and a
    partner's fact is a hop of it.
  - The declarations and relations a preservation reads (`inherit/licensing-functors`).

  Each family is read against `roster` by membership, so the cost is the families' size
  and not the roster's."
  [kb tx roster]
  (let [ruled? #(contains? roster %)
        walked (filter ruled? (tax/props tx :transitive))]
    (-> #{}
        (cond-> (some ruled? (provers/support-answered-preds kb))
          (into (provers/support-source-preds kb)))
        (into (comp (filter #(some ruled? (:predicates %))) (mapcat :trigger-predicates))
              (qkb/registered-calculi kb))
        (cond-> (seq walked)
          (-> (conj 'transitive)
              (into (mapcat #(tax/inverses-under tx %)) walked)))
        (into (inherit/licensing-functors kb roster)))))

(defn- rule-reads-above?
  "Does a stored rule read a term at or above `super`: an antecedent on one, off the
  antecedent keys (`reads/as-stored-rule-keys`), or an antecedent a re-join family moves
  when a fact on one arrives (`licensing-functors`)?  These are the readers whose answer a
  fact below a `(genl sub super)` edge changes.  False off one set read on a KB with no
  rule.  The
  closure is global, as the seeds it gates are: a context seeing more edges reaches more
  of `super`'s supertypes."
  [kb tax super]
  (let [roster (reads/as-stored-rule-keys (:index kb))]
    (when (seq roster)
      (let [ups (tax/genls-global tax super)]
        (boolean (or (some #(contains? roster %) ups)
                     (some (licensing-functors kb tax roster) ups)))))))

(defn- negative-subsumption-seeds
  "The half of `subsumption-seeds` that a **negated** antecedent is owed, read up
  `super`'s `genl` closure where the positive half reads down `sub`'s `spec` one.

  Subsumption is contravariant under a negation (docs/inference.md, \"Under a negation
  the fan reverses\"), so an arriving `(genl dog animal)` does not connect `dog`'s facts
  to an `(animal ?x)` antecedent here — it connects `animal`'s *negative* facts to a
  `(not (dog ?x))` one.  `(not (animal A))` stored, then the edge, and a rule negated on
  `dog` should fire; without this seed the same three sentences derive a conclusion in
  one order and not the other, which is what the positive half exists to prevent.

  **Gated on some rule reading a negated antecedent under `sub`**, off the stored
  antecedent keys — the same keys `rules/trigger-keys` reads, and for the
  same reason.  Sound in both directions this is reached from: for an arriving edge
  nothing can newly match except through it, and for a departing one an edge no negated
  antecedent could ever have climbed licensed nothing to revive.  A KB whose rules read
  no negation, which is nearly every KB, pays one pass over the keys.

  Negative sentexes only, decided by the stored sentence's head `not`: a *positive* fact on a
  genl of `super` newly matches nothing, since a positive antecedent fans downward and
  the edge moved nothing above `super`."
  [kb sub super]
  (let [specs (tax/specs-global (reasoning/taxonomy kb) sub)]
    (when (some (fn [k] (and (vector? k) (contains? specs (second k))))
                (reads/as-stored-rule-keys (:index kb)))
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
  "The stored facts the `genl` edges `sentence` installs newly make matchable, as
  chaining seeds — the taxonomy twin of `lift-existing`, and there for exactly the same
  reason.  The edges are `tax/installed-edges`': a `(genl sub super)` edge, or one per part of
  a cover, whose edges subsume exactly as a stated one does.

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
  when it revives.  **Gated per edge on `rule-reads-above?`**: a fact below the edge
  newly reaches the terms at or above `super` and no other, so where no rule reads one
  the subtree is not read.  Every functor of the subtree reaches the same terms, so the
  gate decides for all of its facts at once.  Sound on a departing edge for
  `negative-subsumption-seeds`' reason: a firing that climbed it read a term at or above
  `super`.

  A **negated** antecedent is answered contravariantly, so the facts an edge newly
  offers *it* sit on the other side of the edge entirely: `negative-subsumption-seeds`
  above reads them up `super`'s genl closure.

  The *removal* side is `resubsumption-seeds` below: a firing names the `genl` edges it
  subsumed through, so dropping one withdraws what it licensed — and the facts have to
  go back on the agenda when the reachability outlives the supporter that left."
  [kb sentence]
  (when-let [edges (seq (tax/installed-edges sentence))]
    (let [idx (:index kb)
          tms (reasoning/tms kb)
          tax (reasoning/taxonomy kb)]
      (into (into [] (comp (filter (fn [[_ super]] (rule-reads-above? kb tax super)))
                           (mapcat (fn [[sub _]] (tax/specs-global tax sub)))
                           (distinct)
                           (mapcat #(reads/as-stored-with-functor idx %))
                           (distinct)
                           (filter #(jtms/in? tms %)))
                  edges)
            (mapcat (fn [[sub super]]
                      (when (symbol? super) (negative-subsumption-seeds kb sub super))))
            edges))))

(defn minted-seeds
  "`handles` — sentexes an entailment minted — as chaining seeds, followed by the
  `subsumption-seeds` of each one that is a `genl` edge.  A `genlArg` mint is an edge
  like an asserted one, and the facts under it become matchable at the new supertype
  whichever of the two stored it: seeding the handle alone fires the rules keyed on
  `genl`, not the rules the edge connected, so `(wolf Rex)` and a rule on `(animal ?x)`
  stored before a minted `(genl wolf animal)` would derive nothing in that order only."
  [kb handles]
  (if (empty? handles)
    []
    (into (vec handles)
          (mapcat #(some->> (p/get-sentex (:records kb) %) :sentence (subsumption-seeds kb)))
          handles)))

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
  "The functors of the antecedents some rule has BESIDE a `pred` one — the triggers a
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
  "The index functors the facts matchable by a stored rule's antecedent key root under.

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

(defn- context-edge-reader-ancestors
  "Every context a `(genlCx sub super)` edge's widened readers can see, once the edge
  has integrated — `context-down(sub)`'s own members' ancestor sets, unioned.  The one
  reachability rule for the three things an arriving edge re-joins: a rule and a fact
  (`visibility-seeds`), a merge and the fact it restates (`migrate-under-context-edge`),
  and a functional/anti_symmetric clash (`equate-under-context-edge`).  Each is a fact becoming
  newly visible to a reader, so the three read one set.

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

(defn- seed-counts
  "`[by-functor by-context]`: the postings `seeds-in` would read under `functors`, and
  in `ctxs`, one count per functor and per context."
  [idx ctxs functors]
  [(transduce (map #(reads/stored-count-with-functor idx %)) + functors)
   (transduce (map #(reads/stored-count-in-context idx %)) + ctxs)])

(defn- seed-cost
  "The postings `seeds-in` reads for `ctxs` and `functors`: the smaller of the two sides."
  [kb ctxs functors]
  (apply min (seed-counts (:index kb) ctxs functors)))

(defn- seeds-in
  "The believed fact handles stored in one of `ctxs` under one of `functors`, a negation
  counted under its body's functor as the index roots it.

  Read from whichever side holds fewer postings, which is one count per functor and one
  per context to decide.  The functor extents are the smaller side when the contexts hold
  the ontology, and the contexts are when they hold a context just wired in — empty, the
  commonest edge there is — where reading the extents would cost every rule-relevant fact
  in the KB to find none."
  [kb ctxs functors]
  (let [idx  (:index kb)
        recs (:records kb)
        tms  (reasoning/tms kb)
        [by-f by-c] (seed-counts idx ctxs functors)
        root (fn [s] (let [f (nm/functor s)]
                       (if (= sx/not-functor f) (nm/functor (second s)) f)))]
    (if (< by-c by-f)
      (into [] (comp (mapcat #(reads/as-stored-in-context idx %))
                     (distinct)
                     (filter #(jtms/in? tms %))
                     (filter (fn [h]
                               (when-let [s (p/get-sentex recs h)]
                                 (and (nil? (:antecedent s))
                                      (sequential? (:sentence s))
                                      (contains? functors (root (:sentence s))))))))
            ctxs)
      (into [] (comp (mapcat #(reads/as-stored-with-functor idx %))
                     (distinct)
                     (filter #(jtms/in? tms %))
                     (filter (fn [h]
                               (when-let [s (p/get-sentex recs h)]
                                 (contains? ctxs (:context s))))))
            functors))))

(defn- under-seen-edges
  "The believed facts stored in `up` that a `genl` edge stated in `seen` newly brings
  under a rule, as chaining seeds, read from the cheaper of two sides.  `n-edges` is how
  many such edges `seen` states (the census, `tax/supporter-count-in`).  When reading
  `up`'s facts under `functors`, the roster's fan, costs no more postings
  (`seed-cost`), those facts are the seeds, so a `seen` that holds a large taxonomy is
  never walked.  Otherwise each edge is read as `subsumption-seeds` reads one arriving:
  `sub`'s spec closure when a rule reads at or above `super` (`rule-reads-above?`), and
  `super`'s genl closure when a rule reads a negated antecedent under `sub`.  The
  closures are global, as `subsumption-seeds`' are: the seeds are candidates for a
  re-join, and the firing's placement narrows them."
  [kb tx roster seen up functors n-edges]
  (if (<= (seed-cost kb up functors) n-edges)
    (seeds-in kb up functors)
    (let [edges (into [] (comp (keep #(:sentence (p/get-sentex (:records kb) %)))
                               (mapcat tax/installed-edges))
                      (seeds-in kb seen tax/edge-installing-functors))
          fs    (into #{} (mapcat (fn [[sub super]]
                                    (let [specs (tax/specs-global tx sub)]
                                      (concat (when (rule-reads-above? kb tx super) specs)
                                              (when (and (symbol? super)
                                                         (some #(and (vector? %) (contains? specs (second %)))
                                                               roster))
                                                (tax/genls-global tx super))))))
                      edges)]
      (if (seq fs) (seeds-in kb up fs) []))))

(defn visibility-seeds
  "The stored facts a new `(genlCx sub super)` edge newly makes matchable, as
  chaining seeds: the context twin of `subsumption-seeds`.  `up` is `super`'s ancestor
  set, `seen` what the contexts below `sub` see beside it, and `fresh` the part of `up`
  `sub` did not see before.  The facts of `fresh` are seeded when `seen` states a rule,
  the facts of `seen` when `fresh` states a rule or a `genl` edge, the facts of `up` when
  `seen` states a rule and `fresh` a `genl` edge, the smaller side when only the rest of
  `up` states a rule, and the facts of `up` under a `genl` edge `seen` states
  (`under-seen-edges`).  A fact is read under a roster antecedent fanned by `genl` or a
  licensing functor (`seeds-in`).  The ungated arity, `resubsumption-seeds`' revival,
  seeds every such fact of `up` and `seen`.  See docs/contexts.md, \"A `genlCx` edge owes
  the same debt\"."
  ([kb sentence] (visibility-seeds kb sentence true))
  ([kb sentence gated?]
   (when (= 'genlCx (nm/functor sentence))
     (let [[_ sub super] sentence
           idx    (:index kb)
           roster (reads/as-stored-rule-keys idx)]
       (when (seq roster)
         (let [tx     (reasoning/taxonomy kb)
               ruled? (fn [cs] (reads/stores-rule-in? idx (set cs)))
               up     (if (symbol? super) (set (tax/context-up tx super)) #{})
               seen   (if (symbol? sub)
                        (into #{} (remove up) (context-edge-reader-ancestors tx sub))
                        #{})
               fresh  (when gated?
                        (let [usable? (fn [a b] (not (reads/stored-opposed? idx (list 'genlCx a b))))]
                          (if (symbol? sub)
                            (into #{} (remove (tax/context-up-besides tx sub super usable?)) up)
                            up)))
               counts (memoize (fn [cs] (tax/supporter-count-in tx :genl cs)))
               edged? (fn [cs] (pos? (counts cs)))
               fs     (delay (into (into #{} (mapcat #(roster-antecedent-functors tx %)) roster)
                                   (licensing-functors kb tx roster)))
               ancestor-set
               (if gated?
                 (let [sides (cond-> []
                               (ruled? seen)                       (conj fresh)
                               (or (ruled? fresh) (edged? fresh)) (conj seen)
                               (and (ruled? seen) (edged? fresh))  (conj up))]
                   (cond
                     (seq sides) (into #{} cat sides)
                     (ruled? (remove fresh up))
                     (min-key #(transduce (map (fn [c] (reads/stored-count-in-context idx c))) + %)
                              seen fresh)
                     :else #{}))
                 (into up seen))]
           ;; distinct: `under-seen-edges` reads `up`, which a side above may hold too
           (into [] (distinct)
                 (concat (when (seq ancestor-set) (seeds-in kb ancestor-set @fs))
                         (when (and gated? (edged? seen))
                           (under-seen-edges kb tx roster seen up @fs (counts seen)))))))))))

(def ^:private edge-functors
  "The two relations a firing can name a witness for, and so the two whose removal owes
  a re-chain.  The same set the taxonomy names `closure-relations`, aliased for the
  local reading the way `provers/transitive-predicates` and `inherit/virtual-relations`
  are: a firing rests on a *reachability* rather than on a stored link precisely because
  these two answer from a cached closure, so the two readings are one fact."
  tax/closure-relations)

(defn- closure-reader-rules
  "The rules carrying a positive antecedent on the closure relation `rel` (`genl` or
  `genlCx`), as chaining seeds: the rules a forward join answers from that closure
  (`chain/solve-closure`).  A firing of one names a single path between two terms, so
  the edge that leaves took a conclusion a second path may still license, and the facts
  under the edge are not what the rule joins over.  A rule handle on the agenda re-joins
  that rule in full.

  Nil off one membership test on a KB whose rules read neither relation."
  [kb rel]
  (when (reads/stored-rule-key? (:index kb) rel)
    (reads/as-stored-rules-by-antecedent (:index kb) rel)))

(defn closure-edge-relation
  "The closure relation `sentence` puts edges into: its functor for a binary `genl` or
  `genlCx` edge, `genl` for a cover (`tax/installed-edges`), and nil for any other sentence."
  [sentence]
  (when (seq? sentence)
    (let [f (nm/functor sentence)]
      (cond (and (contains? edge-functors f) (= 3 (count sentence))) f
            (seq (tax/installed-edges sentence))                        'genl))))

(defn- departed-edge-rejoin
  "The chaining seeds the edges `sentence` held in a closure owe on leaving it: the facts
  under its `genl` edges, the contexts its `genlCx` edge showed each other, and the rules
  that join over the closure it moved.  `closure-edge-relation` must name one."
  [kb sentence]
  (-> (vec (subsumption-seeds kb sentence))
      (into (visibility-seeds kb sentence false))
      (into (closure-reader-rules kb (closure-edge-relation sentence)))))

(defn- edge-own-mints
  "The records among `removed` whose every justification in `removed-jids` is an
  argument-type mint (`mint-informant?`) of a removed closure edge: the edge is the first
  antecedent, the fact the declaration typed.  Empty, and no justification record read,
  unless `removed` holds a closure edge and something besides it."
  [kb removed removed-jids]
  (let [edges (into #{} (comp (filter #(closure-edge-relation (:sentence %))) (map :id)) removed)]
    (if (or (empty? edges) (not (next removed)))
      #{}
      (let [by-conclusion (group-by :consequence
                                    (keep #(p/get-justification (:records kb) %) removed-jids))
            own? (fn [j] (and (mint-informant? (:informant j))
                              (contains? edges (first (:antecedents j)))))]
        (into #{}
              (filter (fn [sx] (let [js (by-conclusion (:id sx))]
                                 (and (seq js) (every? own? js)))))
              removed)))))

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
  rules fire again over them: a `genl` edge's spec subtree (each part's, for a cover),
  and for a `genlCx` edge the two sets `visibility-seeds` names — `super`'s ancestor set
  and what the lower contexts see besides it.  The rules with an antecedent on the edge's
  own relation go back too (`closure-reader-rules`), since what they join over is the
  closure rather than a fact under the edge.

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
  exactly the ones that need re-joining.  The two context sets are read at the same moment
  and are not sensitive to it.  Removing `(genlCx sub super)` changes neither who reaches
  `sub` nor what `super` reaches, and a lower context loses only contexts reached through
  `super`, which are `super`'s ancestor set and are subtracted from the second set; reading
  them early is the same answer, from the one place that has the records in hand.

  And it is gated on the sweep having taken **something besides the records asked
  for**: a justification naming the departing edge is deleted with it, so a conclusion
  that survived kept another one and needs no re-derivation, and a conclusion that did
  not is in `removed`.  So retracting an edge that licensed nothing — the common case —
  costs one functor read per removed record and no chaining at all.  An argument-type
  mint whose every removed justification types the departing edge itself (first
  antecedent, `mint-informant?`) is not counted: the edge was its fact, not a route it
  was found over, so no surviving reachability re-licenses it (`edge-own-mints`).

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
  [kb removed removed-jids]
  (when (next (remove (edge-own-mints kb removed removed-jids) removed))
    (into []
          (comp (map :sentence)
                (filter closure-edge-relation)
                (distinct)
                (mapcat #(departed-edge-rejoin kb %))
                (distinct))
          removed)))

(defn departed-edge-seeds
  "The chaining seeds a settle owes the records among `handles` that hold closure edges
  (`closure-edge-relation`: a `genl` or `genlCx` edge, or a cover) and went **IN ⇒ OUT**
  in it — `resubsumption-seeds` for an edge that lost belief rather than its record.

  A defeat sweeps nothing: the firings that named the edge as a witness go OUT with it and
  are retained for revival, so the retraction path's re-join never runs, and a
  reachability that outlives the edge over a second route never re-derives them.  The same
  three sentences then leave a conclusion believed where the negation arrived first and
  withdrawn where it arrived last (docs/nmtms.md, \"Where the layer stops\").

  Gated per edge on a dependent that is now OUT, the defeat's counterpart of
  `resubsumption-seeds`' gate on the sweep having taken something: an edge nothing rests
  on, or whose dependents all kept another justification, owes no re-join.  The spec
  subtree is read with the edge already OUT, which changes no answer: `specs` of the edge's
  own `sub` is what lies below `sub`, and the edge runs above it."
  [kb handles]
  (let [tms (reasoning/tms kb)
        lost-dependent? (fn [h]
                          (some (fn [jid]
                                  (when-let [j (jtms/justification tms jid)]
                                    (not (jtms/in? tms (:consequence j)))))
                                (jtms/dependents tms h)))]
    (into []
          ;; the dependents are a network read and the record a store fetch, so the gate
          ;; that drops nearly every departed datum runs first
          (comp (filter lost-dependent?)
                (keep (fn [h]
                        (let [s (:sentence (p/get-sentex (:records kb) h))]
                          (when (closure-edge-relation s) s))))
                (distinct)
                (mapcat #(departed-edge-rejoin kb %))
                (distinct))
          handles)))

(defn- handle-twins
  "The live twins a merge has already made of sentex `orig`, a reader's copies among them:
  `[{:twin :informant :witnesses :reader}]`.  A twin is the `:consequence` of a
  `rewriteOf`- or `except`-informant justification whose first antecedent is `orig`
  (`justify-twin!`); `jtms/dependents` names those from the original's side.  Grouping by
  consequence and informant recovers each twin, the witnesses that raised it, and its
  context — the same `reader` its form was elected from — exactly the arguments the first
  migration took.  Empty when `orig` has no twin, the common path.  A forward-chaining or
  defeat use of `orig` carries a different informant and is filtered out.

  Empty for an **equality sentence** too.  Migration never restates one
  (`kb/rewritable-sentex?`), and an equality is the *other* antecedent of every twin it
  raised, so reading its `rewriteOf` dependents as twins of its own would carry an
  `except` of the equality onto every fact the equality restated, hiding a premise
  stated in the representative's spelling along with it."
  [kb orig]
  (let [tms (reasoning/tms kb)]
    (->> (when-not (some-> (p/get-sentex (:records kb) orig) :sentence kb/equality-sentence?)
           (jtms/dependents tms orig))
         (map #(jtms/justification tms %))
         (filter #(and (#{'rewriteOf 'except} (:informant %)) (= orig (first (:antecedents %)))))
         (group-by (juxt :consequence :informant))
         (keep (fn [[[twin informant] justs]]
                 (when-let [tsx (p/get-sentex (:records kb) twin)]
                   {:twin      twin
                    :informant informant
                    :witnesses (into [] (comp (map #(subvec (vec (:antecedents %)) 1)) (distinct))
                                     justs)
                    :reader    (:context tsx)}))))))

;; `departed-edge-seeds` reads an edge that left belief by a relabel, and its gate is a
;; dependent whose conclusion went OUT.  A redundant mint the settle withdraws
;; (`subsumed-mint-blocks`) leaves by a sweep instead, and the firings that named it as
;; their witness are deleted with it while their conclusion usually stands on another
;; firing — so that gate would read nothing, and the firing itself is never drawn again
;; over the route that made the mint redundant.
(defn withdrawn-edge-seeds
  "The chaining seeds a settle owes the closure edges among `handles` — mints it is about
  to withdraw as redundant (`subsumed-mint-blocks`), or spellings a merge retired
  (`settle/withdraw-retired-firings!`) — that a rule firing names as its witness:
  `departed-edge-rejoin`'s facts and rules for each such edge and for each of its twins
  (`handle-twins`).  The closure holds a retired edge's twin in place of the edge, so the
  re-join over the twin draws the firing the merge-first order makes.

  The firing is what is owed, not the conclusion.  A `genl` mint is withdrawn because a
  stated route now reaches as far as it did, so every firing that climbed it has a
  surviving route, and the same content loaded with the stated route first stores that
  firing over it.  Its conclusion keeping another firing says nothing about this one,
  so the gate is a dependent justification whose informant is a rule, read **before** the
  sweep deletes it, and not a dependent conclusion that went OUT.  Without the re-join the
  store keeps whichever firings the arrival order happened to draw, and a later full join
  — a re-join, `forward-chain` — draws the rest at fresh handles."
  [kb handles]
  (let [tms (reasoning/tms kb)
        fired-over? (fn [h]
                      (some (fn [jid]
                              (when-let [j (jtms/justification tms jid)]
                                (integer? (:informant j))))
                            (jtms/dependents tms h)))]
    (into []
          (comp (filter fired-over?)
                (mapcat (fn [h] (cons h (map :twin (handle-twins kb h)))))
                (keep (fn [h]
                        (let [s (:sentence (p/get-sentex (:records kb) h))]
                          (when (closure-edge-relation s) s))))
                (distinct)
                (mapcat #(departed-edge-rejoin kb %))
                (distinct))
          handles)))

;; ---- equality: rewriteOf / sameAs / equals ------------------------------
;;
;; Three assertable relations feed one equivalence closure in the taxonomy
;; (docs/equality.md).  The closure itself is `vaelii.impl.taxonomy`'s and the
;; read/rewrite half (`rewrite-term`, `rewrite-goal`, `displaced-terms`,
;; `rewritable-sentex?`) lives in `vaelii.impl.kb` beside `query`; what lives here
;; is everything that happens *because* two names turned out to denote one thing:
;;
;;   the equality table arm   the edge reaches the closure, like a genl edge
;;   migrate-class            every sentex naming a term some reader retires gets a
;;                            rewritten twin under that reader's representative, derived
;;                            and justified by [the original, the equality]
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
  "Justify a migrated twin `twin-handle` by `[orig-handle & w]` under `informant` for each
  witness `w` in `witnesses`: `[equality]` under `rewriteOf` for a twin, `[equality except]`
  under `except` for a reader's copy (`migrate-into`).  One independent justification per
  witness, so dropping any single one leaves the rest and the ordinary sweep collects the
  twin when the last goes.  The restatement adds no defeasibility of its own, so each
  justification confers `:monotonic` and `conferred-class` caps it at the weakest of its
  antecedents.  Idempotent (`has-justification?`)."
  [kb orig-handle twin-handle informant witnesses]
  (let [tms (reasoning/tms kb)]
    (doseq [w (distinct witnesses)]
      (let [antes (into [orig-handle] w)
            depth (inc (reduce max (map #(jtms/depth tms %) antes)))]
        (jtms/ensure-node tms twin-handle depth)
        (when-not (jtms/has-justification? tms informant antes twin-handle)
          (let [jid  (p/next-id (:records kb))
                just (jtms/->just jid informant antes twin-handle {} :monotonic)]
            (p/put-justification (:records kb) just)
            (jtms/add-justification tms just)))))))

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
     (mapv #(sx/canon (sx/rename-vars (kb/rewrite-term kb % reader) realign))
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
  twin differs between the two callers, what a stranded meta costs does not.  The 6-arity
  takes `justify-twin!`'s `informant` and `witnesses`, for a reader's copy.

  Rewrites read from `reader`, the vantage the twin's own form was elected from
  (`migrate-into`), so a meta elects the spellings its target does; the unscoped rewrite
  used the global election, which a merge `reader` cannot see would diverge from — a twin
  mis-guarded, mis-hidden or mis-aimed."
  ([kb orig twin eqs reader]
   (migrate-handle-metas kb orig twin 'rewriteOf (map vector eqs) reader))
  ([kb orig twin informant witnesses reader]
   (let [realign (varmap-realign (p/get-sentex (:records kb) twin))]
     (doseq [mh   (reads/as-stored-with-term (:index kb) (sx/sentex-handle orig))
             :let  [msx (p/get-sentex (:records kb) mh)
                    s   (and msx (:sentence msx))]
             :when (and msx (jtms/in? (reasoning/tms kb) mh) (= orig (meta-target kb s)))]
       (let [m'  (rebuild-handle-meta kb s orig twin realign reader)
             ctx (:context msx)
             [h sx2 new?] (kb/find-or-create-sentex kb m' ctx)]
         (when new? (integrate-twin kb sx2 h))
         (justify-twin! kb mh h informant witnesses))))))

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
    (doseq [{:keys [twin informant witnesses reader]} (handle-twins kb target)]
      (migrate-handle-metas kb target twin informant witnesses reader))))

(defn- bearing-equalities
  "The handles of every equality edge and schematic rewrite rule that could bear on
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
            (concat (for [t terms, m (tax/equiv-class tx t), eh (tax/equality-supporters tx m)]
                      eh)
                    (map :handle rules))))))

(defn- except-contexts
  "The contexts holding an `except` of one of the handles `ehs`, read by target
  (`reads/as-stored-naming-by-context`).  Empty on one count read for a KB storing no
  `except`."
  [kb ehs]
  (let [idx (:index kb)]
    (if-not (reads/stores-any? idx sx/except-functor)
      #{}
      (into #{} (comp (mapcat #(reads/as-stored-naming-by-context idx sx/except-functor %))
                      (map first))
            ehs))))

(defn- reader-contexts-for
  "The contexts whose election could restate `sentex` differently: its own, and every
  context where it meets an equality that bears on it or an `except` of one.

  **The reader is not the fact's own context.**  A merge holds where it is visible, and
  who reads the fact is any context below it — each electing a representative over a
  different set of visible edges (`tax/scoped-class`).  A single normal form computed
  at the fact's context serves only that one reader; one computed globally serves none
  reliably, since it can be elected by an edge no reader of the fact inherits.  So the
  parties are `tax/meet-closure` of the fact's context with the equalities' — the same
  enumeration a qualitative network takes (docs/qcn.md) and for the same reason.  The
  contexts holding an `except` of one of those equalities are parties too: a reader
  below the fact that reads the except sees less than the fact's context, and
  `migrate-into` stores the fact's spelling there when the fact's context supersedes it.

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
        ehs   (bearing-equalities kb (sx/sentence-of sentex))]
    (when (seq ehs)
      (->> (tax/meet-closure tx (-> #{pctx}
                                    (into (keep #(:context (p/get-sentex (:records kb) %))) ehs)
                                    (into (except-contexts kb ehs))))
           (filter #(tax/sees? tx % pctx))
           ;; the middle key is a taxonomy-closure read — built once per context, not
           ;; ~2·n·log n times; the tuple is `[0/1 long string]`, ordered by `compare`
           (nm/sort-by-content-key
            (juxt #(if (= % pctx) 0 1) #(count (tax/context-up tx %)) nm/print-key)
            compare)))))

(defn- copy-witnesses
  "The `[equality except]` witnesses of a reader's copy of `sentex` in `reader`, sorted:
  each equality among `cands` that is believed and stated where the sentex's own context
  sees it, paired with each believed `except` of it stated in a context `reader` sees and
  the sentex's own context does not.  Empty for the sentex's own context, and on one
  deref for a KB storing no `except`.  An except of that `except` is not read here: it
  withdraws the copy through the copy's third antecedent, so the copies stored do not
  depend on whether it arrived first."
  [kb sentex reader cands]
  (let [idx  (:index kb)
        pctx (:context sentex)]
    (when (and (not= reader pctx) (reads/stores-any? idx sx/except-functor))
      (let [tx  (reasoning/taxonomy kb)
            tms (reasoning/tms kb)
            x?  #(and (tax/sees? tx reader %) (not (tax/sees? tx pctx %)))]
        (not-empty
         (sort (for [eh     (distinct cands)
                     :let   [esx (p/get-sentex (:records kb) eh)]
                     :when  (and esx (jtms/in? tms eh) (tax/sees? tx pctx (:context esx)))
                     [c xs] (reads/as-stored-naming-by-context idx sx/except-functor eh)
                     :when  (x? c)
                     xh     xs
                     :when  (jtms/in? tms xh)]
                 [eh xh])))))))

(defn- store-restatement
  "Store `form`, `sentex`'s restatement for `reader`, in `reader`, justified by `[sentex &
  w]` under `informant` for each witness `w` (`justify-twin!`), and carry the sentex's
  handle-naming metas onto it.  Returns `{:form :new}`, or `{:form :violations}` when the
  form is inadmissible on the derivation path (`checks/derivation-violation`, or
  malformed).  An arbitrable clash is admitted: the twin is stored and its clash decided
  at each reader like any stored clash."
  [kb sentex reader form informant witnesses]
  (let [existing (kb/find-sentex-handle kb form reader)
        v        (when-not existing
                   (or (checks/derivation-violation kb form reader)
                       (wff-violation* kb form reader)))]
    (if v
      {:form form :violations [(assoc v :sentence form :context reader :rule (:id sentex))]}
      ;; A rule stores its wrappers on the record, not in the sentence, so the rewritten
      ;; form is a *bare* implication — re-wrap it with the original's direction /
      ;; defeasibility (`rules/rewrap-sentex`) before find-or-create, or a forward-only or
      ;; defeasible rule's twin would default to a plain two-way `implies`.  The path drops
      ;; the wrapper either way, so dedup and the `existing` probe above are unaffected.
      (let [twin-sentence (if (rules/rule-sentence? form) (rules/rewrap-sentex form sentex) form)
            [h s new?]    (kb/find-or-create-sentex kb twin-sentence reader)]
        ;; `integrate-twin`, not `derived-sentex-added`: a twin is a restated
        ;; **declaration** and must reach every cache/index arm an asserted one does (the
        ;; disjoint / metadata caches, the rule index), not merely the genl closure edges
        ;; the forward-chaining conclusion path narrows to.
        (when new? (integrate-twin kb s h))
        (justify-twin! kb (:id sentex) h informant witnesses)
        ;; A migrated sentex's handle-naming meta-sentexes — `exceptWhen` exceptions, an
        ;; `except` hiding it, a target-following reply naming it — ride separate sentexes
        ;; keyed by its handle, so they must be re-pointed onto the twin or the twin fires
        ;; unguarded / becomes visible / loses its reply (docs/equality.md, round two).
        ;; Any sentex can bear one, not only a rule, so this is unconditional; a sentex
        ;; with no meta enumerates nothing.
        (migrate-handle-metas kb (:id sentex) h informant witnesses reader)
        {:form form :new (if new? [h] []) :handle h}))))

(defn- migrate-into
  "Restate `sentex` as `reader` sees it, and store the result there.  Returns
  `{:form <normal form> :new [h] :superseded [[datum reason]] :violations [v]}`, or nil
  when `reader`'s election leaves the sentence alone, rests on nothing it believes, or
  reproduces a form `placed` already holds somewhere `reader` can see — that twin is
  already this reader's answer and a second copy would report the fact twice.

  A reader strictly below the sentex's context whose election leaves the sentence alone
  because it reads an `except` of an equality the sentex's context rewrites under gets a
  **copy**: the sentex's own spelling stored in `reader`, justified by `[sentex equality
  except]` under informant `except` (`copy-witnesses`).  The sentex's context supersedes
  the original and the twin rests on the equality `reader` cannot see, so without the copy
  `reader` reads the fact under neither spelling.  The copy is handed to the reconcile as
  a `:superseded` candidate, which retires it while the original is not superseded
  (`displacement`)."
  [kb sentex reader placed]
  (let [sentence  (sx/sentence-of sentex)
        tx        (reasoning/taxonomy kb)
        tms       (reasoning/tms kb)
        rewritten (sx/canon (kb/rewrite-term kb sentence reader))]
    (when-not (some (fn [[c f]] (and (= f rewritten) (tax/sees? tx reader c))) placed)
      ;; every equality that restates a subterm of the sentence, each an independent
      ;; support so dropping any one leaves the rest.  Two kinds:
      (let [cands (concat
                   ;; symbol equalities incident on a term of the sentence
                   (mapcat #(tax/equality-supporters tx %)
                           (filter symbol? (tree-seq sequential? seq sentence)))
                   ;; schematic rewrite rules that normalize a subterm of the sentence —
                   ;; the oriented equational rewriting of docs/equality.md.  A rule that
                   ;; rewrites nothing here contributed nothing to the normal form and
                   ;; must not appear as a support.
                   (for [{:keys [handle] :as rule} (tax/rewrite-rules tx)
                         :when (rewrite/rule-applies? rule sentence)]
                     handle))]
        (if (= rewritten (sx/canon sentence))
          (when-let [ws (seq (copy-witnesses kb sentex reader cands))]
            (let [r (store-restatement kb sentex reader rewritten 'except ws)]
              (cond-> (dissoc r :handle)
                (:handle r) (assoc :superseded [[(:handle r) {}]]))))
          ;; the witnesses of a twin are belief-following and apply only where visible
          ;; from the reader whose restatement this is
          (let [eqs (filter (fn [eh]
                              (when-let [esx (p/get-sentex (:records kb) eh)]
                                (and (jtms/in? tms eh) (tax/sees? tx reader (:context esx)))))
                            cands)]
            (when (seq eqs)
              (let [r (store-restatement kb sentex reader rewritten 'rewriteOf (map vector eqs))]
                (cond-> (dissoc r :handle)
                  ;; only the fact's own context supersedes: a reader below it restates
                  ;; the fact for itself and leaves the original believed where it lives
                  (and (:handle r) (= reader (:context sentex)))
                  (assoc :superseded [[(:id sentex) (kb/displaced-terms kb sentence reader)]]))))))))))

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
  * **Checked as a derivation.**  The twin is asked what a rule's conclusion is asked
    (`checks/derivation-violation`).  A merge that *creates* a disjointness clash —
    `(dog Rex)` + `(cat Fluffy)` + a merge makes one individual both — stores the twin,
    and the clash is decided and reported like any stored clash.  Only an inadmissible
    twin (an argument conviction, a malformed form) is dropped and reported through
    `violations`, and the original is then left believed: superseding a spelling whose
    restatement was dropped would lose the caller's knowledge outright.
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
  "Restate every stored sentex naming a term of `terms` some reader's election retires
  (`tax/retirable?`), which can be the global representative itself.

  `find-sentexes` answers \"every sentex containing this term, at any nesting depth\"
  in one index lookup, which is what makes migration affordable and what makes
  congruence free.  The whole class is walked rather than just the arriving edge's
  endpoints, because **a late `rewriteOf` can move the representative**: `(sameAs A
  B)` elects a term lexicographically and a later `(rewriteOf B A)` re-elects `B`, so
  everything already migrated to `A` has to migrate again.  Walking the class covers
  re-migration with no separate path — it is the expensive case, not a special one.

  A sentex is migrated whatever its label.  The superseded ones are the twins of a
  previous election, which re-election has to reach, and an OUT one takes a twin labelled
  OUT with it (`justify-twin!`), so the twins stored depend on the stored set alone and
  not on which member of a clash was OUT when the merge arrived."
  [kb terms]
  (reduce
   (fn [acc t]
     (reduce (fn [acc sx] (merge-with into acc (migrate-sentex kb sx)))
             acc
             (filter #(kb/rewritable-sentex? kb %) (kb/find-sentexes kb t))))
   {:new [] :superseded [] :violations []}
   (filter #(tax/retirable? (reasoning/taxonomy kb) %) terms)))

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
  than by a merged term's class, and like it whatever the sentex's label."
  [kb head]
  (reduce (fn [acc sx] (merge-with into acc (migrate-sentex kb sx)))
          {:new [] :superseded [] :violations []}
          (filter #(kb/rewritable-sentex? kb %) (kb/find-sentexes kb head))))

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

  An equality edge contributes the members of its symbol arguments' **class** that some
  reader retires (`tax/retirable?`), which is `migrate-class`'s candidate set and
  is the unit for `bearing-equalities`' reason: chain composition means an edge touching
  neither of a sentence's own terms still decides what they rewrite to.  A schematic
  rule contributes its LHS head, which is `migrate-matching`'s: the head is present in
  every occurrence of the redex, so the term index gives a superset in one lookup.

  Read off the three equality predicates' extents and the taxonomy's rule cache, so the cost
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
                                                   (filter #(tax/retirable? tx %)))
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
  migration may restate: rewritable, whatever its label, as `migrate-class` admits them.
  Keyed by handle, so a sentex reached through two of its terms is migrated once."
  [kb terms ctxs]
  (into {}
        (comp (mapcat #(kb/find-sentexes kb %))
              (filter #(and (contains? ctxs (:context %)) (kb/rewritable-sentex? kb %)))
              (map (juxt :id identity)))
        terms))

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
  in exactly the orderings that wire the contexts last.  `reconcile-context-edge` runs
  the full supersession reconcile on the same edge, which re-derives which spellings are
  displaced; what it cannot do is *write* the restatement, since an entry there is only
  ever dropped or restated and a spelling starts being displaced when migration says so.

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
              ;; ancestor set
              readers (context-edge-reader-ancestors tx sub)
              rs      (believed-restatements kb)
              near    (restated-terms-in rs above)
              far     (restated-terms-in rs readers)
              cands   (merge (when (seq near) (ancestor-migration-candidates kb near readers))
                             (when (seq far)  (ancestor-migration-candidates kb far above)))]
          (reduce (fn [acc sx] (merge-with into acc (migrate-sentex kb sx)))
                  {:new [] :superseded [] :violations []}
                  (vals cands)))))))

(defn- spelling-displacement
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

(defn- reader-copies
  "The reader's copies of datum `d` (`migrate-into`): the consequences of the `except`
  justifications whose first antecedent is `d`."
  [kb d]
  (let [tms (reasoning/tms kb)]
    (into []
          (keep (fn [jid]
                  (let [j (jtms/justification tms jid)]
                    (when (and (= 'except (:informant j)) (= d (first (:antecedents j))))
                      (:consequence j)))))
          (jtms/dependents tms d))))

(defn- retired-copy
  "The supersession entry `[d {}]` for a reader's copy `d` whose reason is gone, or nil.
  A copy (`migrate-into`) restates an original its own context supersedes, and it is
  retired once one of its originals is no longer displaced: the reader then reads that
  original, and the copy would report the fact a second time.  A datum that is a premise,
  or holds any justification besides a copy's, is not retired.  Nil on one deref for a
  KB storing no `except`."
  [kb visible-for d]
  (when (reads/stores-any? (:index kb) sx/except-functor)
    (let [tms (reasoning/tms kb)
          js  (keep #(jtms/justification tms %) (jtms/supports tms d))]
      (when (and (seq js)
                 (not (jtms/premise? tms d))
                 (every? #(= 'except (:informant %)) js)
                 (some #(nil? (spelling-displacement kb visible-for (first (:antecedents %)))) js))
        [d {}]))))

(defn- displacement
  "The supersession entry for datum `d`: `spelling-displacement`'s, or a retired reader's
  copy's (`retired-copy`), or nil."
  [kb visible-for d]
  (or (spelling-displacement kb visible-for d) (retired-copy kb visible-for d)))

(defn- with-copies
  "`ds` followed by the reader's copies of each (`reader-copies`): a copy's retirement
  reads its original's displacement (`retired-copy`), so a reconcile that examines the
  original examines its copies.  `ds` alone on one count read for a KB storing no
  `except`."
  [kb ds]
  (if-not (reads/stores-any? (:index kb) sx/except-functor)
    ds
    (into (vec ds) (mapcat #(reader-copies kb %)) ds)))

(defn- note-supersession-moves!
  "Add `changed` to the moves `(reasoning/supersessions kb)` holds for the next settle
  (`take-supersession-moves!`), each with its entry in `held`, the map before the change,
  the first time it moves in the window."
  [kb held changed]
  (when (seq changed)
    (some-> (reasoning/supersessions kb)
            (swap! (fn [a]
                     (-> (or a {})
                         (update ::moved (fnil into #{}) changed)
                         (update ::was (fn [w]
                                         (reduce (fn [w d] (if (contains? w d) w (assoc w d (get held d))))
                                                 (or w {}) changed)))))))))

(defn- supersession-map
  "The `datum -> displaced-terms` map of spellings the equality closure currently
  displaces, reconciled against the taxonomy.

  Derived state, like `defeated` and `blocked`: it is recomputed rather than
  accumulated, so a supersession cannot outlive the merge that caused it and a
  retracted equality gives the caller's premise back with no un-supersede path of its
  own.  Entries are only ever dropped or restated here — a spelling *starts* being
  displaced when migration says so, and arrives as `extra` — except a reader's copy,
  which starts being retired when its original is examined and found no longer displaced
  (`with-copies`).

  An entry reads the datum's record, the class its terms belong to, the rewrite rules,
  the `genlCx` ancestor set and whether the restatement is stored.  The equality
  relations, the rewrite rules and `genlCx` are forced monotonic, so an entry moves when
  a sentence is stored or removed, when an `except` moves, and when an equality edge
  moves in belief.  So the walk is
  narrowed to what moved: `extra`, the entries `region` names, and the entries
  naming a term of a class the equality partition moved (`tax/take-equality-moves!`).
  Each examined entry costs a record fetch, a rewrite through the closure and a store
  probe.  `region` nil is the full pass, which a `genlCx` edge, a rewrite rule leaving
  and `recover` owe, since each moves entries no class move names.

  Returns `[map changed]`, `changed` being the datums whose entry differs from `held`'s,
  and adds `changed` to the moves the next settle publishes (`note-supersession-moves!`)."
  [kb extra region]
  (let [tms   (reasoning/tms kb)
        held  (jtms/superseded tms)
        vis   (memoize #(res/visible-supporter-fn kb %))
        moved (tax/take-equality-moves! (reasoning/taxonomy kb) :supersessions)
        diff  (fn [m ds] (into #{} (filter #(not= (get held %) (get m %))) ds))
        [m changed]
        (if (some? region)
          (let [ds (with-copies kb (-> (mapv first extra)
                                       (into (filter #(contains? held %)) region)
                                       (into (comp (mapcat #(kb/find-sentexes kb %))
                                                   (map :id)
                                                   (filter #(contains? held %))
                                                   (distinct))
                                             moved)))
                m  (reduce (fn [m d] (if-let [e (displacement kb vis d)] (conj m e) (dissoc m d)))
                           (into held extra)
                           ds)]
            [m (diff m ds)])
          (let [m (into {} (keep #(displacement kb vis %)) (with-copies kb (keys (into held extra))))]
            [m (diff m (concat (keys held) (keys m)))]))]
    (note-supersession-moves! kb held changed)
    [m changed]))

(defn take-supersession-moves!
  "`{:moved #{datum} :was {datum entry}}`: the datums whose supersession entry changed
  since the last call, each with its entry before the first change (nil when it was not
  superseded), emptied; nil when the KB keeps no supersession moves.  `settle-finish`
  reads it once per settle: a supersession moves belief with no relabel, so
  `jtms/touched` does not name these."
  [kb]
  (when-let [a (reasoning/supersessions kb)]
    (let [{moved ::moved was ::was} @a]
      (reset! a {})
      {:moved (or moved #{}) :was (or was {})})))

(defn refresh-supersessions
  "Reconcile the superseded set with the equality closure (`supersession-map`), on the
  write path: where a migration hands over `extra` (the two-arity, which examines `extra`
  and the moved classes), where a sentence leaves the store
  (`reconcile-removed-supersession!`), where a `genlCx` edge arrives
  (`reconcile-context-edge`), and at `recover`, which passes nil for the full pass.  The
  settle calls it only for an `except` that moved and for an equality edge that moved in
  belief (`settle/settle-finish`)."
  ([kb] (refresh-supersessions kb nil))
  ([kb extra] (refresh-supersessions kb extra #{}))
  ([kb extra region]
   (jtms/supersede (reasoning/tms kb) (first (supersession-map kb extra region)))))

(defn reconcile-removed-supersession!
  "The supersession reconcile `sentex` leaving the store owes, from the removal choke
  point: the full pass for a `genlCx` edge or a schematic rewrite rule while any spelling
  is superseded, and the narrowed one over `sentex` and the classes it moved for a
  superseded datum or an equality sentence.  A superseded datum leaving drops its entry,
  and an equality leaving gives back the spellings its class displaced."
  [kb sentex]
  (let [held (jtms/superseded (reasoning/tms kb))
        s    (sx/sentence-of sentex)]
    (cond
      (or (= 'genlCx (nm/functor s)) (rewrite/schematic-equation? s))
      (when (seq held) (refresh-supersessions kb nil nil))

      (or (contains? held (:id sentex)) (kb/equality-sentence? s))
      (refresh-supersessions kb nil #{(:id sentex)}))))

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

(defn- monotonic-pair?
  "Are both members `h` and `o` of a collision `:monotonic`?  Only such a pair of two
  symbols merges; any other is a nogood the settle places (docs/reference.md, decision 6)."
  [kb h o]
  (let [tms (reasoning/tms kb)]
    (and (tuple/monotonic-member? tms h) (tuple/monotonic-member? tms o))))

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
        ;; only a pair of two `:monotonic` members merges, so a `:default` arrival reads
        ;; no clash, and the order-free gates run before the content sort
        clashes (when (tuple/monotonic-member? (reasoning/tms kb) handle)
                  (nm/sort-by-content-key
                   (fn [[oh v via n]] (let [s (p/get-sentex recs oh)]
                                        [v (:sentence s) (:context s) via n]))
                   (filter (fn [[oh v :as clash]]
                             (and (checks/mergeable-values? v (checks/functional-filler sentence clash))
                                  (monotonic-pair? kb handle oh)))
                           (checks/functional-clashes kb sentence context))))]
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
                               (monotonic-pair? kb handle oh)
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
  "Could the predicate `f`, or something it descends from, carry a `functional` or
  `functionalInArg` mark — the cheap pre-gate `derive-functional-equalities` reads of a
  fact's functor before paying for a reader sweep, so a fact of a predicate no mark
  reaches never pays for one, and `equate-under-edge` reads of an edge's upper end.  Two
  unscoped, over-approximating `genl`-walk reads (`tax/props-over`,
  `tax/functional-in-arg-over`), the same reads `checks/functional-clashes` already
  makes internally to answer the single-context question."
  [tax f]
  (and (symbol? f)
       (or (seq (tax/props-over tax :functional f))
           (seq (tax/functional-in-arg-over tax f)))))

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
       (if (functional-mark-relevant? tax (nm/functor sentence))
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
  * **Nogoods (`vaelii.impl.decide`):** the candidate index the settle places from, which
    reads every mark of the family (`tax/functional-in-arg-over`, `tax/props-over`).

  The spellings are not written in each lane: `tax/functional-family-marks` is this entry
  point's read of the declaration's `:family`, so a new spelling reaches this entry point
  with no second roster.  What stays here is the arity, since this entry point is
  downstream of well-formedness."
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
  predicate-extent read.

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
  off the predicate extents of `P`'s whole `genl` **spec** subtree, because the mark binds
  every predicate beneath the one it names (`tax/props-over`) — an extent read off `P`
  alone would merge two `parentOf` fillers and leave two `fatherOf` ones apart.
  `subtree-sentexes` reads it, snapshotted before the first merge, since migration writes
  twins to the extents the walk is reading."
  [kb sentence]
  (when-let [pred (functional-family-declaration sentence)]
    (equate-declared-subtree kb pred derive-functional-equalities)))

(defn- derive-over-premises
  "Each premise among `sxs` (a fact, not a rule, not a negation) handed to the family's
  `derive` in its own context, as one `{:new :superseded :violations}`."
  [kb sxs derive]
  (reduce (fn [acc sx]
            (if-not (and (nil? (:antecedent sx)) (not (sx/negative? sx)))
              acc
              (merge-with into acc (derive kb (:sentence sx) (:context sx) (:id sx)))))
          {:new [] :superseded [] :violations []}
          sxs))

(defn- equate-under-edge-via
  "The body `equate-under-edge` and `antisym-equate-under-edge` share: a `(genl sub
  super)` edge arriving over facts already stored, with every believed premise of `sub`'s
  spec subtree handed back to the family's `derive` in its own context.

  Read only when a mark of the family stands on `super` or above it: the edge puts the
  subtree under the marks over `super` and under no other, so a subtree no mark newly
  reaches derives nothing.  `declares?` is the family's KB-wide gate, one map lookup, and
  `relevant?` the walk up from `super`, both asked before the subtree is read
  (`revived-edge-sweep` asks the same two).

  **Shared rather than written twice, because the two entry points differ in nothing else.**
  They answer one arrival order — the edge arriving last — for two mark families, and a
  fix to that order has to reach both or reach neither: vaelii#43 was exactly such a fix,
  applied to two copies by hand.  A family joins by passing its gate and its derive, which
  is the same reading `tax/functional-family-marks` gives the spellings one lane up."
  [kb sentence declares? relevant? derive]
  (when (and (= 'genl (nm/functor sentence)) (= 2 (nm/arity sentence)))
    (let [tax           (reasoning/taxonomy kb)
          [_ sub super] sentence]
      (when (and (symbol? sub) (declares? tax) (relevant? tax super))
        (derive-over-premises kb (subtree-sentexes kb sub) derive)))))

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

  **Free for an edge no functional-family mark stands above**, decided *before* the
  subtree is read rather than per fact inside the fold (`equate-under-edge-via`).  This
  arm fires on a `genl` edge — the commonest thing an ontology says — so it is the one
  that reaches for an extent on an ordinary write, and an edge under a broad type whose
  subtree holds most of the vocabulary reads nothing unless a mark stands over its upper
  end.

  **The family, not the arity-2 spelling alone**: the fold asks
  `derive-functional-equalities`, which reads both spellings, so the gate reads both too
  (`tax/functional-family-declared?`, `functional-mark-relevant?`), or an edge arriving
  last under `(functionalInArg P n)` would merge nothing where `(functional P)` in the
  same order merges (`functional_in_arg_test`).

  `subsumption-seeds` reads the subtree's believed handles on every edge regardless,
  since those facts become matchable at the new supertype."
  [kb sentence]
  (equate-under-edge-via kb sentence
                         tax/functional-family-declared?
                         functional-mark-relevant?
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
  (`checks/mergeable-values?`) and both members `:monotonic` (`monotonic-pair?`); a self
  tuple, or a pair some visible merge already reconciles, is skipped.  Any other converse
  is a nogood the settle places (`vaelii.impl.decide`)."
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
                   (if (or (= oh handle) (not (monotonic-pair? kb handle oh))
                           (res/same-class-in? kb a b context))
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
  "The antisymmetric twin of `functional-mark-relevant?`: could the predicate `f`, or
  something it descends from, carry an `anti_symmetric` mark?  One unscoped
  `tax/props-over` read — no `functionalInArg` twin exists for this mark, so this is
  the whole of the check."
  [tax f]
  (and (symbol? f) (seq (tax/props-over tax :anti-symmetric f))))

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
       (if (anti-symmetric-mark-relevant? tax (nm/functor sentence))
         (reduce (fn [acc r]
                   (merge-with into acc (derive-antisymmetric-equalities-in kb sentence r handle)))
                 {:new [] :superseded [] :violations []}
                 (cond->> (tax/context-down tax context)
                   readers (filter readers)))
         (derive-antisymmetric-equalities-in kb sentence context handle))))))

(defn- note-and-derive-antisymmetric
  "`derive-antisymmetric-equalities`, after offering the stored fact `handle` to the
  converse candidates again (`decide/offer!`): a mark or a predicate edge arriving after
  its tuples makes converse pairs the candidate index did not read at their store.  The
  other families read no `anti_symmetric` mark, so the fact is not offered to them."
  [kb sentence context handle]
  (some->> (p/get-sentex (:records kb) handle) vector (#(decide/offer! kb % :converse)))
  (derive-antisymmetric-equalities kb sentence context handle))

(defn antisym-equate-existing
  "When an `(anti_symmetric P)` declaration arrives, derive the equalities P's **already
  stored** facts license — the twin of `equate-existing`, over the antisymmetric merge.
  Sweeps the whole spec subtree beneath `P` (the mark descends), and hands each stored
  fact back to `derive-antisymmetric-equalities`, so the two arrival directions cannot
  drift about what a converse licenses or what justifies the merge.  nil when `sentence`
  declares nothing antisymmetric."
  [kb sentence]
  (when (and (= 'anti_symmetric (nm/functor sentence)) (= 1 (nm/arity sentence)))
    (equate-declared-subtree kb (first (nm/args sentence)) note-and-derive-antisymmetric)))

(defn antisym-equate-under-edge
  "When a `(genl sub super)` edge arrives, derive the equalities an `(anti_symmetric …)`
  mark above `super` now licenses over the `(sub …)` facts already stored — the twin of
  `equate-under-edge`.  Free for an edge no `anti_symmetric` mark stands above, decided
  before the subtree is read.  nil when `sentence` is not a `genl` edge."
  [kb sentence]
  (equate-under-edge-via kb sentence
                         #(seq (tax/props % :anti-symmetric))
                         anti-symmetric-mark-relevant?
                         note-and-derive-antisymmetric))

(def ^:private offered-marks
  "The marks whose nogoods the settle places from a candidate index, each with the arity
  it is written at: their arrival offers the stored tuples beneath the marked predicate
  to `decide/offer!`."
  '{functional 1, functionalInArg 2, asymmetric 1, anti_transitive 1})

(defn- offered-mark-over?
  "Does a mark of `offered-marks` stand on `p` or above it?  Four map reads for a KB
  declaring none."
  [tax p]
  (boolean (or (seq (tax/props-over tax :functional p))
               (seq (tax/functional-in-arg-over tax p))
               (seq (tax/props-over tax :asymmetric p))
               (seq (tax/props-over tax :anti-transitive p)))))

(defn offer-marked-existing
  "When a `functional`, `functionalInArg`, `asymmetric` or `anti_transitive` mark arrives,
  offer every stored fact of the marked predicate's spec subtree to `decide/offer!`,
  which reads the nogoods each forms under the mark.  nil."
  [kb sentence]
  (when (and (seq? sentence) (= (offered-marks (nm/functor sentence)) (nm/arity sentence)))
    (let [p (first (nm/args sentence))]
      (when (symbol? p)
        (decide/offer! kb (subtree-sentexes kb p))))))

(defn offer-marked-under-edge
  "When a `(genl sub super)` edge arrives under an `offered-marks` mark on `super` or
  above it, offer the stored facts of `sub`'s spec subtree to `decide/offer!`.  nil, and
  free for a KB declaring none of the marks."
  [kb sentence]
  (when (and (seq? sentence) (= 'genl (nm/functor sentence)) (= 2 (nm/arity sentence)))
    (let [[_ sub super] sentence]
      (when (and (symbol? sub) (symbol? super)
                 (offered-mark-over? (reasoning/taxonomy kb) super))
        (decide/offer! kb (subtree-sentexes kb sub))))))

(def ^:private collision-informants
  "The informants a collision merge's justification carries (`derive-equality`)."
  '#{functional anti_symmetric})

(defn- collision-members
  "The antecedents of the collision justification `j` that are its colliding tuples: the
  ones with a term of the equality `j` concludes among their arguments.  The others are
  the declarations and the `genl` edges."
  [recs j]
  (let [terms (set (nm/args (:sentence (p/get-sentex recs (:consequence j)))))]
    (filterv #(when-let [s (:sentence (p/get-sentex recs %))]
                (and (not (contains? '#{functional functionalInArg anti_symmetric genl}
                                     (nm/functor s)))
                     (some terms (nm/args s))))
             (:antecedents j))))

(defn class-moved-merges
  "Re-ask the collision merges of the handles in `region` (a delay over `jtms/touched`)
  whose class can have moved: drop each collision justification whose members are all IN
  and one at `:default` (off when `drop?` is false), and re-derive from each member IN at
  `:monotonic` but a premise this window created at that class.  `asked` is the settle's
  volatile set of `[handle class]` asked already.  `{:new :superseded :violations :removed
  :members}`, `:removed` the merged removals for the caller's stores and `:members` the
  dropped justifications' members; nil, with `region` unforced, when no merge mark is
  declared.  See docs/equality.md, \"`functional` infers equality instead of throwing\"."
  [kb region asked drop?]
  (let [tax (reasoning/taxonomy kb)]
    (when (or (tax/functional-family-declared? tax) (seq (tax/props tax :anti-symmetric)))
      (let [tms   (reasoning/tms kb)
            recs  (:records kb)
            born  (jtms/touched-new tms)
            fresh (fn [cls] (into [] (filter #(and (= cls (jtms/defeat-class tms %))
                                                   (not (contains? @asked [% cls]))))
                                  @region))
            down  (fresh :default)
            up    (into [] (remove #(and (contains? born %)
                                         (= :monotonic (jtms/premise-strength tms %))))
                        (fresh :monotonic))
            _     (vswap! asked into (concat (map #(vector % :default) down)
                                             (map #(vector % :monotonic) up)))
            stale (when drop?
                    (into (sorted-set)
                          (comp (mapcat #(jtms/dependents tms %))
                                (keep #(jtms/justification tms %))
                                (filter #(contains? collision-informants (:informant %)))
                                (keep (fn [j]
                                        (let [ms (collision-members recs j)]
                                          (when (and (every? #(jtms/defeat-class tms %) ms)
                                                     (not-every? #(tuple/monotonic-member? tms %) ms))
                                            [(:id j) ms])))))
                          down))
            removed (reduce (fn [acc [jid]]
                              (let [r (jtms/drop-justification! tms jid)]
                                (p/delete-justification! recs jid)
                                (merge-with into acc r)))
                            nil stale)
            sxs   (nm/sort-by-content-key (juxt :sentence :context)
                                          (into [] (comp (keep #(p/get-sentex recs %))
                                                         (filter #(nil? (:antecedent %))))
                                                up))
            mig   (reduce (fn [acc {:keys [sentence context id]}]
                            (merge-with into acc
                                        (derive-functional-equalities kb sentence context id)
                                        (derive-antisymmetric-equalities kb sentence context id)))
                          {:new [] :superseded [] :violations []}
                          sxs)]
        (assoc mig :removed removed :members (into [] (comp (mapcat second) (distinct)) stale))))))

;; ---- a departing `genl` edge re-derives what descended through it ----------
;; Three derivations descend the predicate hierarchy and name the `genl` edges they
;; descended through (`checks/edge-support`): the argument-type entailment, and the
;; equality a `functional` or `anti_symmetric` mark on a super-predicate licenses.  Each
;; names **one** route, a shortest visible one, so removing an edge on that route
;; deletes the justification even where a second route still reaches the declaration.
;; The removal then re-derives from the taxonomy it left, as `resubsumption-seeds` does
;; for a firing: the justification is a conjunction of supports, not a proof that no
;; other route exists.

(def ^:private edge-descended-informants
  "The informants of the derivations that cite the `genl` edges they descended through
  (and, for an entailment, the `genlCx` edges it sees its declaration through), mapped to
  how each is drawn again for the fact at the head of its antecedents."
  (into {'functional     :functional
         'anti_symmetric :anti-symmetric}
        (map (fn [k] [k :entailment]))
        (keys entailing-declarations)))

(def ^:private route-functors
  "The edges a descended derivation names as its route: `genl` between predicates, and
  `genlCx` for an entailment drawn through an inherited declaration."
  '#{genl genlCx})

(defn edge-descended-justifications
  "The justifications among `removed-jids` that a departing route edge (`route-functors`)
  invalidated while every other ingredient survives, as records — the derivations a
  teardown owes a re-derivation (`rederive-descended`).  `gone` is the sentexes the sweep
  removed.

  Read **before** the teardown deletes the justification records, since the records are
  what name the fact and the declaration to derive from again.  Gated on `gone` holding
  a route edge, so a removal that took none fetches no justification record.

  A justification qualifies when its informant is an edge-descended derivation, one of
  its antecedents is a removed route edge, and no removed antecedent is anything else:
  a removed fact or declaration withdraws the derivation, and re-deriving it would undo
  the removal."
  [kb gone removed-jids]
  (let [edges (into #{}
                    (comp (filter #(let [s (:sentence %)]
                                     (and (seq? s) (contains? route-functors (nm/functor s)))))
                          (map :id))
                    gone)]
    (when (seq edges)
      (let [ids  (into #{} (map :id) gone)
            recs (:records kb)]
        (into []
              (comp (keep #(p/get-justification recs %))
                    (filter #(contains? edge-descended-informants (:informant %)))
                    (filter #(some edges (:antecedents %)))
                    (remove #(some (fn [a] (and (contains? ids a) (not (contains? edges a))))
                                   (:antecedents %))))
              removed-jids)))))

(defn lost-descended-derivations
  "The edge-descended derivations among the dependents of `handles` whose conclusion is
  OUT, as justification records — `edge-descended-justifications` for an ingredient that
  lost belief rather than its record.  `edges-only?` keeps only the handles that are
  route edges (`route-functors`).

  Two settle arms read it.  A `genl` edge that went **IN ⇒ OUT** takes the derivation
  naming it OUT, where a second route to the declaration still licenses it; a defeat
  deletes nothing, so the justification stays and nothing else draws the derivation
  again.  And a spelling an un-merge gives back is a fact the derivation could not be
  drawn from while the merge superseded it: an equality over two spellings of one merged
  pair is found by matching both, so it is drawn only once both are believed again.

  Only a justification whose conclusion is OUT, or withdrawn at its own context
  (`exc/believed-own?`), qualifies: one that kept another support
  owes nothing to belief, and asking it again every pass of the settle would re-read a
  conclusion that cannot move.  The dependents are a network read and the record a
  store fetch, so the gate that drops nearly every handle runs first."
  [kb handles edges-only?]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)
        lost (fn [h]
               (into []
                     (comp (keep #(jtms/justification tms %))
                           (filter #(contains? edge-descended-informants (:informant %)))
                           ;; OUT, or withdrawn where it is stored
                           (remove #(exc/believed-own? kb (:consequence %))))
                     (jtms/dependents tms h)))]
    (into []
          (comp (map (juxt identity lost))
                (filter (comp seq second))
                (filter (fn [[h _]]
                          (or (not edges-only?)
                              (let [s (:sentence (p/get-sentex recs h))]
                                (and (seq? s) (contains? route-functors (nm/functor s)))))))
                (mapcat second)
                (distinct))
          handles)))

(defn rederive-descended
  "Draw each of `justs` (`edge-descended-justifications`) again from the taxonomy as it
  now stands, and return the handles it created as chaining seeds.  The violations are
  reported and the spellings a merge displaces are refreshed here, as the arrival path
  does for the same derivations.

  Each derivation is asked for through the function its arrival arms ask: the entailment
  through `retroactive-mints`, narrowed to the declaration the removed justification
  named; a descended equality through `derive-functional-equalities` or
  `derive-antisymmetric-equalities` over the fact at the head of its antecedents.  So
  where a second route survives, the derivation comes back resting on it, and where none
  does, nothing is drawn.  A conclusion that kept another justification takes the
  surviving route's as well, which is the justification the same content loaded without
  the edge records.

  An entailment's antecedents lead with the fact and the declaration, in that order
  (`entail-arg-type`).  An equality's are in content order (`derive-equality`), so its
  facts are read off by functor: every antecedent that is neither a `genl` edge nor a
  mark declaration.  Each task is drawn once however many of the removed justifications
  name it."
  [kb justs]
  (let [recs  (:records kb)
        facts (fn [antes]
                (filter (fn [h]
                          (when-let [s (:sentence (p/get-sentex recs h))]
                            (not (contains? '#{genl genlCx functional functionalInArg anti_symmetric}
                                            (nm/functor s)))))
                        antes))
        tasks (into []
                    (comp (mapcat (fn [j]
                                    (let [kind  (edge-descended-informants (:informant j))
                                          antes (:antecedents j)]
                                      (if (= :entailment kind)
                                        [[kind (nth antes 0) (nth antes 1)]]
                                        (map (fn [src] [kind src nil]) (facts antes))))))
                          (distinct))
                    justs)
        res   (reduce
               (fn [acc [kind src dh]]
                 (if-let [sx (p/get-sentex recs src)]
                   (merge-with into acc
                               (case kind
                                 :entailment     (retroactive-mints kb sx dh)
                                 :functional     (derive-functional-equalities
                                                  kb (:sentence sx) (:context sx) src)
                                 :anti-symmetric (derive-antisymmetric-equalities
                                                  kb (:sentence sx) (:context sx) src)))
                   acc))
               {:new [] :superseded [] :violations []}
               tasks)]
    (when (seq (:superseded res))
      (refresh-supersessions kb (:superseded res)))
    (violations/report kb (:violations res))
    (minted-seeds kb (:new res))))

;; ---- the decontextualized predicate ---------------------------------------
;; `(decontextualized_predicate P)` lifts every `(P ...)` out of the context it was
;; stated in and into CxUniverse, which every context below the joint sees — so the fact
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
;; context below the joint sees, so the copy is visible to the next assert and the
;; ordinary check catches the clash at its source.  `unchecked-target?` below covers
;; the one case that leaves: a context wired outside the spindle, which does not see
;; CxUniverse either.

(def universal-context 'CxUniverse)

(defn- unchecked-target?
  "Could the definitional checks have missed what this lift is about to create?

  They run at `src-context` against what is visible from there, so they have already
  considered everything in CxUniverse whenever `src-context` sees it — which is
  every context in a spindle-shaped KB.  When it does not, the copy lands where the
  stating context cannot look, and the check has to be re-run on the copy itself."
  [kb src-context]
  (not (tax/sees? (reasoning/taxonomy kb) src-context universal-context)))

(defn- lift-of? [dh] #(and (:lift %) (= dh (:dh %))))

(defn- copy-merges
  "The equalities a lifted copy at `h` licenses as content new to CxUniverse, as `{:new
  :superseded :violations}`: the copy meeting a `functional` or `anti_symmetric` mark
  above its predicate, and the copy *being* one and meeting that predicate's stored
  facts.  The assert entry point and `chain/place-fact-conclusion` run the same four for
  what they store, and a copy is stored by neither.

  Owed because each merge is placed where its mark is visible.  A `(functional P)`
  stated in a theory after `P`'s facts merges their values below that theory alone, and
  its copy is what makes the mark visible from CxUniverse; without this the copy
  arrived with nothing to merge from it, so the same three sentences merged at
  CxUniverse when the declaration came first and below the theory when it came last.
  Each arm is gated on its own functor, so a copy of anything else pays four map reads."
  [kb sentence h]
  (merge-with into {:new [] :superseded [] :violations []}
              (derive-functional-equalities kb sentence universal-context h)
              (equate-existing kb sentence)
              (derive-antisymmetric-equalities kb sentence universal-context h)
              (antisym-equate-existing kb sentence)))

(defn- deduce-lift
  "Deduce `sentence` (stored at `src-handle` in `src-context`) into CxUniverse, checked
  there when `(unchecked? src-context)` (`unchecked-target?`), and justified by
  `src-handle` and each of `witnesses` in turn — a vector of the further antecedents one
  justification rests on.  A declared lift passes one `[declaration]`
  per declaring sentex, as a migrated twin gets one witness per equality, so retracting
  one of two declarations leaves the copy standing on the other; a permuting mark's lift
  passes `[[]]`, since nothing but the mark's own statement holds it
  (`deduce-lifts`).  A refused lift is kept once per witness, under its declaration's
  handle, or under nil for a permuting mark's.

  Returns `{:new [handle …] :violations [v]}` — the copy's handle when it was newly
  created, with the twins its merges wrote (`copy-merges`; the caller seeds chaining with
  all of them), and the violation when the copy could not be admitted.  Reported rather
  than thrown, like every check off the assert path: a lift runs inside a fixpoint and
  inside `settle`, neither of which may abort halfway."
  [kb unchecked? sentence src-handle src-context witnesses]
  (if (or (empty? witnesses) (= src-context universal-context))
    empty-entailment-result
    ;; the check the stating context could not run, run here — and only here, so a KB
    ;; whose contexts all see CxUniverse (the ordinary spindle) pays one `sees?`
    (if-let [v (and (unchecked? src-context)
                    (checks/derivation-violation kb sentence universal-context))]
      (do
        ;; an argument conviction reads the absence of a type, which later content can
        ;; supply — so the lift waits to be re-asked rather than being lost to the order
        ;; the type and the declaration arrived in (`release-lift!`)
        (doseq [[dh] witnesses]
          (note-pending! kb src-handle
                         (merge {:lift true :dh dh :gens (taxonomy-generations kb)}
                                (checks/conviction-watch v))
                         (lift-of? dh)))
        {:new [] :violations [(-> v
                                  (assoc :sentence sentence :context universal-context)
                                  (assoc-in [:detail :lifted-from] src-context))]})
      (let [[h2 s2 new?] (kb/find-or-create-sentex kb sentence universal-context)]
        (if (= h2 src-handle)
          empty-entailment-result
          (do
            ;; the copy is a derived sentex in a context that did not have it: it
            ;; reaches the closures and posts its exception re-check trigger exactly as
            ;; a rule conclusion does
            (when new? (derived-sentex-added kb s2 h2))
            (doseq [w witnesses]
              (let [antes (into [src-handle] w)
                    depth (inc (reduce max (map #(jtms/depth (reasoning/tms kb) %) antes)))]
                (jtms/ensure-node (reasoning/tms kb) h2 depth)
                (when-not (jtms/has-justification? (reasoning/tms kb) 'decontextualized_predicate antes h2)
                  (let [jid  (p/next-id (:records kb))
                        ;; The lift adds no defeasibility of its own, so it confers
                        ;; :monotonic and `conferred-class` caps it at the weakest of its
                        ;; antecedents.
                        just (jtms/->just jid 'decontextualized_predicate antes h2 {} :monotonic)]
                    (p/put-justification (:records kb) just)
                    (jtms/add-justification (reasoning/tms kb) just)))))
            ;; ...and the merges the copy owes as content new to CxUniverse, after the
            ;; justifications because a merge takes only the supporters it believes,
            ;; and the argument-type derivations it draws there, as a fact stated in
            ;; CxUniverse draws them
            (let [mig  (when new? (copy-merges kb sentence h2))
                  args (when new? (deduce-placed kb sentence h2 universal-context))]
              (when (seq (:superseded mig))
                (refresh-supersessions kb (:superseded mig)))
              {:new        (-> (if new? [h2] []) (into (:new mig)) (into (:new args)))
               :violations (-> [] (into (:violations mig)) (into (:violations args)))})))))))

(defn deduce-lifts
  "Deduce `sentence` (stored at `handle` in `context`) into CxUniverse if its
  predicate is decontextualized or is a permuting mark — `{:new [handles] :violations
  [v]}`, nil when neither holds.

  Called from both stores of new content — `assert` and forward chaining's
  `place-conclusion` — because a decontextualized predicate is a claim about the
  predicate, not about how a particular sentence arrived.  Lifting only what a caller
  asserted would make belief depend on arrival order: declare-then-derive would leave
  the conclusion unlifted while derive-then-declare lifted it through `lift-existing`,
  and the two orders are the same knowledge.

  **A permuting mark is lifted whatever the KB declares.**  `(symmetric P)` and the
  three commutativity marks (`inherit/permuting-marks`) decide the argument order a
  `(P …)` sentex is stored in, and the store sorts by a mark stated in any context
  (`res/kb-sentex`) from the moment it is stated anywhere.  Every other reader of the mark — `has-prop?` from a context, the
  symmetric prover, the supporter a mirrored firing names — reads it where its sentex is
  visible, so a mark stated in one theory would answer the mirror from a sibling through
  the store and deny it through every other path.  The copy in CxUniverse is what makes
  the two agree: it is visible wherever the store's reading holds.  It rests on the
  mark's statement alone, since a `(decontextualized_predicate symmetric)` declaration
  adds nothing the key has not already decided, and on a KB carrying CxCore, which
  declares one, the copy is the same copy.

  The gate is a single in-memory cache read, because every assert and every placed rule
  conclusion pays it to find out there is nothing to do."
  [kb sentence handle context]
  (let [tax  (reasoning/taxonomy kb)
        pred (nm/functor sentence)]
    (cond
      (inherit/permuting-mark? pred)
      (deduce-lift kb #(unchecked-target? kb %) sentence handle context [[]])
      ;; the global property read on purpose: the lift decides the *storage* context,
      ;; and scoping it by what could see the declaration would be circular
      (and pred (tax/has-prop? tax :decontextualized pred))
      (deduce-lift kb #(unchecked-target? kb %) sentence handle context
                   (map vector (tax/prop-supporters tax :decontextualized pred))))))

(defn lift-refusals
  "The lifts waiting on an argument conviction, as `[source-handle entry]` pairs in
  handle order."
  [kb]
  (->> (kind-entries @(reasoning/refused kb) :lift)
       (sort-by (fn [[h e]] [h (:dh e)]))
       vec))

(defn release-lift!
  "Re-ask the lift of the fact at `src-handle` under declaration `(:dh entry)`, or on
  the statement alone where that is nil (a permuting mark's):
  `{:new [handle …]}` when it is admitted now, the entry restamped under `gens` and the
  term of the conviction read now (`checks/conviction-watch`) when the conviction still
  holds, and retired when the fact or the declaration has left.  An admitted lift
  withdraws the ledger entry its refusal filed, since the order that brought the type
  first would have filed none."
  [kb src-handle entry gens]
  (let [rec (:records kb)
        sx  (p/get-sentex rec src-handle)
        dh  (:dh entry)]
    (if-not (and sx (or (nil? dh) (p/get-sentex rec dh)))
      (do (drop-pending! kb src-handle (lift-of? dh)) empty-entailment-result)
      (do (drop-pending! kb src-handle (lift-of? dh))
          (let [r (deduce-lift kb #(unchecked-target? kb %) (:sentence sx) src-handle
                               (:context sx) [(if dh [dh] [])])]
            (if-let [v (first (:violations r))]
              (do (note-pending! kb src-handle
                                 (merge entry {:gens gens} (checks/conviction-watch v))
                                 (lift-of? dh))
                  empty-entailment-result)
              (do (violations/withdraw! kb (:sentence sx) universal-context nil)
                  r)))))))

(defn- lift-statements
  "Deduce every stored `(pred ...)` sentex outside CxUniverse into it on `witnesses`
  (`deduce-lift`), as one `{:new :violations}`.  The extent is snapshotted before the
  first copy is made, for `lift-existing`'s reason.

  `unchecked-target?` is asked once per stating context.  The walk writes copies of
  `pred` into CxUniverse and no `genlCx` edge (a `genlCx` statement is stored in
  CxUniverse, so no walk reads one), and the answer holds for the whole walk."
  [kb pred witnesses]
  (let [unchecked? (memoize #(unchecked-target? kb %))]
    (reduce (fn [acc s]
              (if-not (and (= pred (nm/functor (:sentence s)))
                           (not= universal-context (:context s)))
                acc
                (merge-with into acc (deduce-lift kb unchecked? (:sentence s) (:id s)
                                                  (:context s) witnesses))))
            empty-entailment-result
            (vec (kb/find-sentexes kb pred)))))

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
  ;; a permuting mark's statements are lifted as they arrive, on nothing but themselves
  (if (inherit/permuting-mark? pred)
    empty-entailment-result
    (lift-statements kb pred [[dh]])))

(defn rebuild-pending!
  "Rebuild the engine's own waiting derivations after `recover`: every stored entailing
  declaration whose type is not yet mintable, and every decontextualized lift an argument
  conviction refuses (a permuting mark's included), re-noted as their arrival noted them.  The refusal record is
  in-memory state no store holds, and `chain/rerecord-refusals!` rebuilds only the rules'
  half of it.  The lift sweep is `lift-existing`'s, which over copies already stored adds
  nothing and so only re-notes the refused ones."
  [kb]
  (when checks/*assertive-arg-types?*
    ;; the walk writes no genl edge, so one walk down from `thing` answers every
    ;; declaration
    (let [mintable? (checks/mintable-types (reasoning/taxonomy kb))]
      (doseq [f (keys entailing-declarations)
              h (reads/as-stored-with-functor (:index kb) f)
              :let [sx (p/get-sentex (:records kb) h)]
              :when (and sx (= (entailing-declarations f) (nm/arity (:sentence sx))))]
        (note-unmintable! kb mintable? (:sentence sx) h))))
  (let [tax (reasoning/taxonomy kb)]
    (doseq [pred (sort-by nm/name-key (tax/props tax :decontextualized))
            dh   (sort (tax/prop-supporters tax :decontextualized pred))]
      (lift-existing kb pred dh)))
  ;; the permuting marks, which lift on their statement alone
  (doseq [f inherit/permuting-marks]
    (lift-statements kb f [[]])))

(defn- revived-edge-sweep
  "The merges and candidate offers a revived `(genl sub super)` edge owes the facts of
  `sub`'s spec subtree: `equate-under-edge`, `antisym-equate-under-edge` (its converse
  re-offer included) and `offer-marked-under-edge` over one walk, bounded at
  `tax/*exposure-instance-budget*` sentexes.  nil when `sentence` is not a `genl` edge or
  no merge mark and no `offered-marks` mark stands at or above `super`.

  The walk reads the subtree's predicates in content order and each posting in the
  index's order, so past the budget the prefix merged is in handle order within a
  predicate.  A cut files one `:genl-edge-revival-truncated` entry naming the edge, and
  the facts past it stay unmerged until something else re-derives them.  `context` is the
  edge's."
  [kb sentence context]
  (when (and (= 'genl (nm/functor sentence)) (= 2 (nm/arity sentence)))
    (let [tax           (reasoning/taxonomy kb)
          [_ sub super] sentence
          fun?  (and (tax/functional-family-declared? tax)
                     (functional-mark-relevant? tax super))
          anti? (and (seq (tax/props tax :anti-symmetric))
                     (anti-symmetric-mark-relevant? tax super))
          offer? (and (symbol? super) (offered-mark-over? tax super))]
      (when (and (symbol? sub) (or fun? anti? offer?))
        (let [budget (max 0 (long tax/*exposure-instance-budget*))
              walked (subtree-sentexes kb sub (inc budget))
              cut?   (> (count walked) budget)
              sxs    (cond-> walked cut? (subvec 0 budget))]
          (cond offer? (decide/offer! kb sxs)
                anti?  (decide/offer! kb sxs :converse))
          (cond-> (merge-with into
                              (when fun? (derive-over-premises kb sxs derive-functional-equalities))
                              (when anti? (derive-over-premises kb sxs derive-antisymmetric-equalities)))
            cut? (update :violations (fnil conj [])
                         {:violation :genl-edge-revival-truncated
                          :detail    {:edge    sentence
                                      :context context
                                      :budget  budget
                                      :message (str "revived " (pr-str sentence) " in " context
                                                    " bounded its merge sweep over the "
                                                    sub " subtree at " budget
                                                    " facts; facts past the cut that arrived"
                                                    " while the edge was OUT stay unmerged")}})))))))

(defn revived-declaration-sweeps
  "Run, for each sentex in `handles` the settle just brought back **OUT ⇒ IN**, the sweeps
  its arrival runs over the facts already stored: `equate-existing` and
  `antisym-equate-existing` for a merge mark, `revived-edge-sweep` for a `genl` edge under
  one, and `lift-existing` for a `decontextualized_predicate`.  Returns one `{:new
  :superseded :violations}`, or nil when the KB declares no merge or lift mark.

  A fact arriving while its mark is OUT meets a taxonomy that does not hold the mark, so
  its own arrival merges and lifts nothing, and nothing written later reaches it: the
  mark's arrival is over and the revival is a relabel, not an arrival.  Without this, a
  mark stated, defeated, handed two facts and revived leaves them unmerged where the mark
  stated first or last merges them.  The other direction needs no sweep: a merge or copy
  drawn while the mark held names the mark's sentex among its antecedents, so a defeat
  takes it OUT and the revival brings it back through the JTMS.

  The sweeps are the arrival ones, so they read what is **stored** and are idempotent:
  a revival of a mark whose facts all arrived while it held re-derives nothing new.  The
  handles are walked in content order.  The symmetric and commuting marks are not here;
  a revived permuting mark re-spells its rows through `chain/reconcile-spellings!`.

  A revived `genl` edge's sweep is budgeted where its arrival's is not: a settle revives
  an edge far more often than one arrives, and `lein perf`'s `constraint-genl-mark-descent`
  holds a revived edge flat in the subtree past the budget.

  Gated on the taxonomy holding any functional-family, `anti_symmetric` or
  `decontextualized_predicate` mark, so a KB declaring none pays three map reads."
  [kb handles]
  (let [tax (reasoning/taxonomy kb)]
    (when (and (seq handles)
               (or (tax/functional-family-declared? tax)
                   (seq (tax/props tax :anti-symmetric))
                   (seq (tax/props tax :asymmetric))
                   (seq (tax/props tax :anti-transitive))
                   (seq (tax/props tax :decontextualized))))
      (let [sxs (sort-by (juxt (comp nm/print-key :sentence) (comp nm/print-key :context))
                         (keep #(p/get-sentex (:records kb) %) handles))]
        (reduce (fn [acc {:keys [sentence context id]}]
                  (offer-marked-existing kb sentence)
                  (merge-with into acc
                              (equate-existing kb sentence)
                              (antisym-equate-existing kb sentence)
                              (revived-edge-sweep kb sentence context)
                              (when (and (= 'decontextualized_predicate (nm/functor sentence))
                                         (= 1 (nm/arity sentence))
                                         (symbol? (second sentence)))
                                (lift-existing kb (second sentence) id))))
                {:new [] :superseded [] :violations []}
                sxs)))))

(defn- equality-arrival-sweep
  "The migration an equality sentex's arrival runs, run again over what is stored now:
  `migrate-matching` over a schematic equation's LHS head, `migrate-class` over a ground
  merge's class.  nil for a NAT `rewriteOf`-to-compound, which restates nothing."
  [kb sentence]
  (let [[_ a b] sentence]
    (cond
      (rewrite/schematic-equation? sentence)
      (migrate-matching kb (first (first (rewrite/orient a b))))

      (and (symbol? a) (symbol? b))
      (let [tx (reasoning/taxonomy kb)]
        (migrate-class kb (into (set (tax/equiv-class tx a)) (tax/equiv-class tx b)))))))

(defn believed-again-sweeps
  "Run, for each symbol-merge supporter in `handles` that is stored and believed, what
  its arrival runs over the stored facts: the re-check of the merged class
  (`recheck-equality-edge`) and the migration (`equality-arrival-sweep`).  Returns one
  `{:new :superseded :violations}`.  `handles` is `tax/take-believed-again!`'s answer: a
  supporter whose firing was held void met its arrival with nothing to restate, and a
  relabel brings it IN with no arrival.  Walked in content order, and scoped to each
  supporter's class."
  [kb handles]
  (let [tms (reasoning/tms kb)
        sxs (sort-by (juxt (comp nm/print-key :sentence) (comp nm/print-key :context))
                     (keep #(when (jtms/in? tms %) (p/get-sentex (:records kb) %)) handles))]
    (reduce (fn [acc {:keys [sentence]}]
              (let [[_ a b] sentence
                    tx      (reasoning/taxonomy kb)]
                (recheck-equality-edge kb (into (set (tax/equiv-class tx a)) (tax/equiv-class tx b)))
                (merge-with into acc (equality-arrival-sweep kb sentence))))
            {:new [] :superseded [] :violations []}
            sxs)))

(defn- except-moved-records
  "The records whose visibility an `except` of one of `sxs` moved: `sxs`, and for each
  record that is itself an `except` the record it names, since the cascade moves that
  one's visibility too.  In content order."
  [kb sxs]
  (let [recs (:records kb)]
    (loop [seen #{} out [] todo (vec sxs)]
      (if-let [sx (peek todo)]
        (let [todo (pop todo)]
          (if (contains? seen (:id sx))
            (recur seen out todo)
            (let [inner (some->> (:sentence sx) kb/except-target (p/get-sentex recs))]
              (recur (conj seen (:id sx)) (conj out sx) (cond-> todo inner (conj inner))))))
        (sort-by (juxt (comp nm/print-key :sentence) (comp nm/print-key :context)) out)))))

(defn- drop-hidden-mints!
  "Drop each argument-type derivation resting on a record of `sxs`, stored in a context
  `in?` accepts, that an `except` now hides from that context (`exc/except-hidden-fn`),
  as `entail-arg-type` stores none when the `except` arrived first.  Returns the merged
  `jtms/drop-justification!` results for the caller to apply; the dropped records are
  deleted here."
  [kb sxs in?]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (reduce (fn [acc jid]
              (let [j (jtms/justification tms jid)]
                (if (and j (mint-informant? (:informant j))
                         (when-let [c (p/get-sentex recs (:consequence j))]
                           (when (in? (:context c))
                             (when-let [hidden? (exc/except-hidden-fn kb (:context c))]
                               (some hidden? (:antecedents j))))))
                  (let [r (jtms/drop-justification! tms jid)]
                    (p/delete-justification! recs jid)
                    (merge-with into acc r))
                  acc)))
            nil
            (into (sorted-set) (mapcat #(jtms/dependents tms (:id %))) sxs))))

(defn- revealed-entailments
  "The argument-type entailments the believed records of `sxs` owe the facts already
  stored, drawn as each record's arrival draws them: `entail-existing` for an entailing
  declaration, `entail-over` for a literal fact, and `trigger-entailments` for a trigger
  membership or edge.  Every draw reads the `except` hidden filter, so a record an
  `except` now hides draws nothing, and one it stopped hiding draws what a KB that never
  had the `except` holds.  Returns `{:new [handle …] :violations [v …]}`, the new handles
  as chaining seeds (`minted-seeds`)."
  [kb sxs]
  (let [tms (reasoning/tms kb)
        ins (filter #(jtms/in? tms (:id %)) sxs)
        r   (merge-with into
                        (reduce (fn [acc {:keys [sentence id]}]
                                  (merge-with into acc (entail-existing kb sentence id)))
                                empty-entailment-result
                                ins)
                        (entail-over kb ins)
                        (when (seq (declaring-predicates kb trigger-declarations))
                          (trigger-entailments kb (filter trigger-shaped? ins))))]
    (update r :new #(minted-seeds kb %))))

(defn except-move-sweeps
  "Run, for each handle in `handles` whose visibility an `except` moved, the sweep its
  arrival runs over the facts already stored: the equality migration for an equality
  sentex (`equality-arrival-sweep`), and `revived-declaration-sweeps`' for a merge or lift
  mark.  Returns one `{:new :superseded :violations :removed}`, or nil when `handles` is
  empty.

  An equality restates a fact for the readers that see it, and an `except` changes which
  readers those are without the equality arriving, leaving or changing label.  A fact
  stored while the except hid the equality from the fact's context was stored as spelled,
  with no twin, and every goal from that context is normalized under the equality the
  moment the except goes — so without this sweep the fact is believed and answered by no
  read (docs/equational.md, \"An except of an equation\").  The sweeps are the arrival
  ones and idempotent, so a twin already made gains nothing, and a handle that is no
  longer stored, or restates nothing, costs a record fetch.  The handles are walked in
  content order.

  The argument-type derivations move the same way (docs/argtypes.md, \"An except of an
  ingredient\"): with `sweep?`, the ones resting on a record an `except` now hides are
  dropped (`drop-hidden-mints!`, `:removed` for the caller to apply), and the records it
  stopped hiding draw again.  For a handle in `whole`, whose `except` itself moved, that
  is every context and the record's own arrival sweep (`revealed-entailments`).  For one
  only in `scoped`, `{handle #{[sub super]}}`, moved by `genlCx` edges, it is the contexts
  under each `sub` and the edge's own sweep over them (`entail-under-context-edge`)."
  [kb handles sweep? whole scoped]
  (when (seq handles)
    (let [sxs   (sort-by (juxt (comp nm/print-key :sentence) (comp nm/print-key :context))
                         (keep #(p/get-sentex (:records kb) %) handles))
          on?   (and checks/*assertive-arg-types?* (any-declaring? kb))
          mints (when on? (except-moved-records kb (filter #(contains? whole (:id %)) sxs)))
          edges (when on?
                  (->> scoped
                       (remove #(contains? whole (key %)))
                       (into #{} (mapcat val))
                       (sort-by #(mapv nm/name-key %))))
          moved (when (seq edges)
                  (except-moved-records kb (remove #(contains? whole (:id %)) sxs)))
          tx    (reasoning/taxonomy kb)
          under (fn [c] (some (fn [[sub _]] (or (= c sub) (tax/sees? tx c sub))) edges))
          gone  (when sweep?
                  (merge-with into
                              (when (seq mints) (drop-hidden-mints! kb mints (constantly true)))
                              (when (seq moved) (drop-hidden-mints! kb moved under))))
          drawn (reduce (fn [acc [sub super]]
                          (merge-with into acc
                                      (entail-under-context-edge kb (list 'genlCx sub super))))
                        (if (seq mints) (revealed-entailments kb mints) empty-entailment-result)
                        edges)]
      (reduce (fn [acc {:keys [sentence id]}]
                (merge-with into acc
                            (cond
                              (kb/equality-sentence? sentence)
                              (equality-arrival-sweep kb sentence)
                              :else
                              (revived-declaration-sweeps kb [id]))))
              (assoc drawn :superseded [] :removed gone)
              sxs))))

(defn- except-move-terms
  "The terms whose occurrences an `except` of one of `targets` can re-spell: for every
  equality sentex in the targets' forward consequence closure, a ground merge's class and
  a schematic equation's LHS head — `migrate-class`'s and `migrate-matching`'s candidate
  keys.  The closure is walked because an equality can rest on the excepted handle (a
  merge a `functional` mark derived), and a reader that cannot see the handle cannot see
  what rests only on it.  A target that is itself an `except` adds its own target, since
  the meta-exception cascade moves that one's visibility."
  [kb targets]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)
        tx   (reasoning/taxonomy kb)
        seen (loop [seen #{}, stack (vec targets)]
               (if (empty? stack)
                 seen
                 (let [d (peek stack), stack (pop stack)]
                   (if (contains? seen d)
                     (recur seen stack)
                     (let [meta (some-> (p/get-sentex recs d) :sentence kb/except-target)]
                       (recur (conj seen d)
                              (cond-> (into stack
                                            (comp (keep #(jtms/justification tms %))
                                                  (map :consequence))
                                            (jtms/dependents tms d))
                                meta (conj meta))))))))]
    (into #{}
          (comp (keep #(p/get-sentex recs %))
                (map :sentence)
                (mapcat (fn [[_ a b :as s]]
                          (cond
                            (not (kb/equality-sentence? s))    nil
                            (rewrite/schematic-equation? s) [(first (first (rewrite/orient a b)))]
                            (and (symbol? a) (symbol? b))   (into (set (tax/equiv-class tx a))
                                                                  (tax/equiv-class tx b))))))
          seen)))

(defn except-move-region
  "The superseded data whose supersession an `except` that moved can change: the ones
  naming a term an equality in the excepted handles' reach re-spells
  (`except-move-terms`), stored in a context that sees one of the contexts the moving
  `except`s are stated in.  `pending` is `{target #{except-context}}`.

  A supersession is decided at the datum's own context from the equalities that context
  sees (`displacement`), and an `except` changes that only for the contexts that read it
  and only for the equalities it withdraws, so this set is the whole of what the
  settle's reconcile re-examines for it.  Each candidate costs a term-index lookup per
  term, the same lookups the arrival sweep makes, and a KB superseding nothing costs one
  deref."
  [kb pending]
  (let [held (jtms/superseded (reasoning/tms kb))]
    (if (or (empty? held) (empty? pending))
      #{}
      (let [tx   (reasoning/taxonomy kb)
            ctxs (into #{} cat (vals pending))]
        (into #{}
              (comp (mapcat #(kb/find-sentexes kb %))
                    (filter #(contains? held (:id %)))
                    (filter (fn [sx] (some #(tax/sees? tx (:context sx) %) ctxs)))
                    (map :id))
              (except-move-terms kb (keys pending)))))))

(defn except-moved
  "The handles an `except` of which arrived, left or flipped since the last
  `drain-except-moves!`, read without emptying the queue (`note-except-move!`)."
  [kb]
  (keys (:pending @(reasoning/except-moves kb))))

(defn take-except-moves!
  "Empty `:except-moves` and return what the settle's supersession reconcile owes it:
  `{:extra [[datum reason]] :region #{datum} :full? bool}` — the supersessions
  `except-move-sweeps` found, the superseded data an `except` that moved can change
  (`except-move-region`), and whether a move is still pending undrained, which leaves the
  reconcile nothing narrower than a full pass.  nil when nothing moved."
  [kb]
  (let [a (reasoning/except-moves kb)
        m @a]
    (when (or (seq (:pending m)) (seq (:extra m)) (seq (:region m)))
      (reset! a {})
      {:extra (:extra m) :region (:region m)
       :full? (boolean (seq (:pending m)))})))

(defn drain-except-moves!
  "Take the pending handles off `:except-moves`, sweep them (`except-move-sweeps`, with
  `sweep?`), and keep the supersessions the sweeps found and the region the moves can
  change (`except-move-region`) for `take-except-moves!`.  Returns the sweeps' result,
  its `:new` joined by the believed facts of the targets' consequence closure and of the
  antecedents resting on it, to chain from, or nil when nothing was pending."
  [kb sweep?]
  (let [a                               (reasoning/except-moves kb)
        {:keys [pending whole scoped]} @a]
    (when (seq pending)
      (swap! a dissoc :pending :whole :scoped)
      (let [mig (or (except-move-sweeps kb (keys pending) sweep? (set whole) scoped)
                    {:new [] :superseded [] :violations []})
            reg (except-move-region kb pending)
            tms (reasoning/tms kb)
            ;; the firings the except refused or swept, re-joined from the moved targets'
            ;; consequence closure and the antecedents of the justifications resting on
            ;; it, so a firing a second route carries is placed again; that bounds the join
            cl  (jtms/consequence-closure tms (keys pending))
            src (into [] (comp (distinct)
                               (filter #(and (jtms/in? tms %)
                                             (some-> (p/get-sentex (:records kb) %) rules/rule? not))))
                      (concat cl (mapcat #(some-> (jtms/justification tms %) :antecedents)
                                         (mapcat #(jtms/dependents tms %) cl))))]
        (swap! a #(-> %
                      (update :extra (fnil into []) (:superseded mig))
                      (update :region (fnil into #{}) reg)))
        (update mig :new (fnil into []) src)))))

(defn clear-except-moves!
  "Empty `:except-moves` outright — a rebuild reconciles every supersession from scratch."
  [kb]
  (reset! (reasoning/except-moves kb) {}))

(defn- marked-roots
  "The predicates carrying `prop` — `:functional` or `:anti-symmetric` — whose specs are
  every functor `functional-mark-relevant?` or `anti-symmetric-mark-relevant?` admits:
  the `functional` roster and every `functionalInArg` predicate, or the
  `anti_symmetric` roster."
  [tax prop]
  (case prop
    :functional     (into (tax/props tax :functional) (keys (:functional-in-arg @tax)))
    :anti-symmetric (tax/props tax :anti-symmetric)))

(defn- stored-facts-in-ancestors
  "Stored, positive, non-rule sentexes across `contexts`, kept when `marked?` admits
  them — the ancestor-set-scoped analogue of `subtree-sentexes`' spec-subtree walk, over
  contexts instead of predicates, and lazy for the same reason: a budgeted caller
  realizes only its prefix, and a context cycle can make an ancestor set the whole graph.

  This walk is deliberately not **belief**-filtered, for `equate-existing`'s reason:
  an equality derived off a defeated fact rests on that fact and is defeated with it,
  so skipping a defeated candidate here would leave a revival's merge missing —
  `derive-functional-equalities`/`-in` read the store, never the belief filter, and
  this feeds them, so it has to agree.

  **Read from the smaller side.**  `roots` are the predicates carrying the mark, and a
  fact `marked?` admits is one of their specs', so the candidates are the facts of those
  functors that sit in `contexts` as well as the facts in `contexts` that `marked?` admits
  — one set read two ways.  The ancestor set of an edge into a corpus context holds
  the corpus, where the marked predicates hold a few of its facts, and every handle
  walked is a record paged; the side is chosen by the two stored counts, index
  cardinality reads.  The functors are the roots' `tax/specs-global`, unscoped, because
  `marked?` reads the mark unscoped (`tax/props-over` with no context) and this has to
  enumerate every functor it admits.  The enumeration order, and so which prefix a cut budget takes,
  follows the side read (`budgeted-context-edge-candidates` names that residual)."
  [kb contexts marked? roots]
  (let [tax   (reasoning/taxonomy kb)
        idx   (:index kb)
        cs    (filterv symbol? contexts)
        ;; `marked?` reads the functor alone and admits a spec of a marked root, so these
        ;; are every functor it can admit
        fs    (into [] (comp (mapcat #(tax/specs-global tax %))
                             (distinct)
                             (filter #(pos? (reads/stored-count-with-functor idx %))))
                    roots)
        keep? (fn [s] (and s (nil? (:antecedent s)) (not (sx/negative? s))
                           (sequential? (:sentence s))
                           (marked? tax (nm/functor (:sentence s)))))]
    (if (< (transduce (map #(reads/stored-count-with-functor idx %)) + 0 fs)
           (transduce (map #(reads/stored-count-in-context idx %)) + 0 cs))
      (let [in-set? (set cs)]
        (for [f     fs
              h     (reads/as-stored-with-functor idx f)
              :let  [s (p/get-sentex (:records kb) h)]
              :when (and s (contains? in-set? (:context s)) (keep? s))]
          s))
      (for [c     cs
            h     (reads/as-stored-in-context idx c)
            :let  [s (p/get-sentex (:records kb) h)]
            :when (keep? s)]
        s))))

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

  Sharing `*exposure-instance-budget*` with the revived-edge merge sweep rather than
  inventing a second knob: both are 'how much work will one edge's merge sweep spend', and
  a KB operator wants one dial for that, not two that can drift apart.

  **The residual this leaves, stated plainly.**  The candidate set is scoped to *this*
  edge's own ancestor set, so an unrelated later edge does not retry a merge it misses,
  and a *later* `genlCx` edge widening the *same* ancestor set re-walks it and can still
  reach the pair.  That is why the caller files a violation naming the cut."
  [kb sub marked? roots]
  (let [tax    (reasoning/taxonomy kb)
        budget (max 0 (long tax/*exposure-instance-budget*))
        xs     (into [] (take (inc budget))
                     (stored-facts-in-ancestors kb (context-edge-reader-ancestors tax sub)
                                                marked? roots))]
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
        (let [[candidates cut] (budgeted-context-edge-candidates kb sub relevant?
                                                                 (marked-roots tax prop))
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
  `derive-functional-equalities` at `tax/*exposure-instance-budget*` — the same knob the
  revived-edge merge sweep spends, so a cut here and a cut there answer to one dial —
  and files a `:context-edge-exposure-truncated` violation when it cuts,
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
  "Everything a `(genlCx sub super)` edge means for the **equality** closure and the
  argument-type entailments, in one call: the sentexes the widened ancestor set newly
  exposes to a standing merge (`migrate-under-context-edge`), the two merges the same
  widening newly licenses (`equate-under-context-edge` for the functional family,
  `antisym-equate-under-context-edge` for the antisymmetric one), and the derivations the
  declarations it makes visible draw (`entail-under-context-edge`).  Returns the usual
  `{:new :superseded :violations}`.  Safe on any sentence: each arm gates on the
  `genlCx` functor itself, so a non-edge costs three functor reads and returns the
  empty result.

  **One function because a `genlCx` edge arrives by three entry points, and only two of them
  remembered the list.**  An edge can be *asserted* (`assert-entry/assert-one`), *concluded* by
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
  rather than to an empty accumulator.

  An edge changes which merges a reader sees, so while any spelling is superseded it runs
  the full supersession reconcile itself, over the arms' output too, and hands back no
  `:superseded` for the caller to reconcile again."
  [kb sentence]
  (let [cme (migrate-under-context-edge kb sentence)
        cfn (equate-under-context-edge kb sentence)
        cax (antisym-equate-under-context-edge kb sentence)
        ent (let [r (entail-under-context-edge kb sentence)]
              (when (or (seq (:new r)) (seq (:violations r))) r))
        mig (when (or cme cfn cax ent)
              (merge-with into {:new [] :superseded [] :violations []} cme cfn cax ent))]
    (if (and (= 'genlCx (nm/functor sentence)) (seq (jtms/superseded (reasoning/tms kb))))
      (do (refresh-supersessions kb (:superseded mig) nil)
          (some-> mig (assoc :superseded [])))
      mig)))

(defn- stored-declarations
  "Every **stored** sentex whose functor is `f`, believed or not.

  Read by the passes that sweep what is *already there* — `post-taxonomy-supporters!`'
  replay, `rebuild-taxonomy`'s replay of the equality relations, and the
  `disjoint_metatype` arm picking up memberships asserted before the declaration —
  because each records supporters rather than deciding belief, and a supporter omitted
  here is one no later reconcile can find.  The supporter families and the equality
  partition record *every* asserting sentex, with `refresh-beliefs` deciding which
  entries are active: omit a disbelieved supporter and clearing its defeat could never
  revive the entry, so a defeated `(disjoint dog cat)` would answer differently either
  side of a restart.

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

(defn- reifiable-entry
  "`prop-entry`'s arms for `(reifiable_function F)`, with the arrival queued as its leaving
  and a relabel are (`note-permuting-moves!`): the mark arriving re-spells the
  applications of `F` stored before it (`chain/reconcile-reified!`, docs/nat.md)."
  []
  (let [e (prop-entry 'reifiable_function)
        g (:integrate e)]
    (assoc e :integrate (fn [kb sx h]
                          (let [before (permuting-marks (reasoning/taxonomy kb))]
                            (g kb sx h)
                            (note-permuting-moves! kb before))))))

(defn- forcing-entry
  "`prop-entry`'s arms for a roster declaration `(functor P)`, each followed by the
  switch when P joins or leaves the roster (`decide/on-roster?`, so a baseline member
  never switches): `checks/force-reach!` rewrites the forced memberships over what P
  reaches, and the rules in that reach are queued for a fresh join (docs/nmtms.md, \"The
  forced-monotonic roster\")."
  [functor]
  (let [{:keys [integrate disintegrate] :as entry} (prop-entry functor)
        kind    (pr/prop-kind functor)
        switch! (fn [kb pred]
                  (mark-recheck kb (checks/force-reach! kb pred) :all-rejoin))]
    (assoc entry
           :integrate    (fn [kb sx h]
                           (let [pred (second (:sentence sx))
                                 had? (decide/on-roster? (reasoning/taxonomy kb) kind pred)
                                 r    (integrate kb sx h)]
                             (when-not had? (switch! kb pred))
                             r))
           :disintegrate (fn [kb sx]
                           (let [pred (second (:sentence sx))
                                 r    (disintegrate kb sx)]
                             (when-not (decide/on-roster? (reasoning/taxonomy kb) kind pred)
                               (switch! kb pred))
                             r)))))

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
   ;; the removal choke point's `reconcile-removed-supersession!` gives the displaced
   ;; spellings back —
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
  "Bound by `post-taxonomy-supporters!` to a volatile the genl / genlCx `:rebuild` arms bump each
  time `replay-edge` drops a stored declaration that is not a well-formed edge.  Nil off
  the replay path, where `replay-edge` still guards but counts nothing."
  nil)

(defn- replay-edge
  "Replay one stored `genl` / `genlCx` declaration through `add` (`tax/add-genl` or
  `tax/add-genlCx`), but only when the stored sentence's **complete shape** is exactly
  `(expected-f <symbol> <symbol>)` — a valid two-endpoint taxonomy edge.

  `reindex` replays the **stored** sentexes rather than the checked ones
  (`post-taxonomy-supporters!`), and `stored-declarations` is a candidate read over the durable predicate extent, not proof that
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
                     (when-let [[whole parts] (tax/cover-parts (:sentence sx))]
                       (let [tax (reasoning/taxonomy kb) ctx (:context sx)]
                         (tax/add-cover tax whole parts kind h ctx)
                         (edges! kb tax h ctx whole parts))))
     :disintegrate (fn [kb sx]
                     (when-let [[whole parts] (tax/cover-parts (:sentence sx))]
                       (let [tax (reasoning/taxonomy kb)]
                         (tax/del-cover! tax whole parts kind (:id sx))
                         (doseq [p parts :when (not= p whole)]
                           (tax/del-genl! tax p whole (:id sx))
                           (recheck-genl-edge kb p whole)))))
     ;; The rebuild arm takes `tax` alone, so it replays both halves and posts no
     ;; re-check — the `recover` after a `reindex` re-evaluates every exception rather
     ;; than per edge.
     :rebuild      (fn [tax {sentence :sentence id :id ctx :context}]
                     (if-let [[whole parts] (tax/cover-parts sentence)]
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
  predicates rather than about the arms, and `post-taxonomy-supporters!` replays it.  Writing
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
                               (recheck-except-ancestors kb a b)
                               (note-split-marks! kb)))
             :disintegrate (fn [kb sx]
                             (let [[_ a b] (:sentence sx)]
                               (tax/del-genlCx! (reasoning/taxonomy kb) a b (:id sx))
                               (recheck-genlCx-edge kb a)
                               (recheck-except-ancestors kb a b)
                               (note-split-marks! kb)))
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
                       ;; that handle out of the supporter families entirely.  Clearing the
                       ;; defeat could then never revive the entry, since the reconcile
                       ;; has no key to find: belief depending on the order the defeat and
                       ;; the declaration arrived in, and permanently.  It would also put
                       ;; the live KB and a reindexed one at odds over one store,
                       ;; `post-taxonomy-supporters!`' second pass reading what is stored
                       ;; through this very function.
                       (doseq [{[_ t] :sentence id :id mctx :context}
                               (stored-declarations kb m)]
                         (tax/add-metatype-member (reasoning/taxonomy kb) m t id mctx))))
     :disintegrate (fn [kb sx]
                     (let [[_ m] (:sentence sx)]
                       (tax/unmark-disjoint-metatype! (reasoning/taxonomy kb) m (:id sx))))
     ;; marks only: membership is replayed by post-taxonomy-supporters!' second pass, once every
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
    ;; `(orthogonal x y)` exempts nothing and fills no cache: `decide.related` reports its
    ;; clash with a genl edge or with a separation a reader sees.
    'orthogonal
    {:wff          wff/type-pair-problems}
    ;; `(siblingDisjointException x y)` exempts one pair from the separation marks — the
    ;; plain add/drop `disjoint` has, keyed as the same unordered pair.  A reader reads the
    ;; exemption where it reads the separation (`membership/sync-memberships`).
    'siblingDisjointException
    {:integrate    (fn [kb sx h]
                     (let [[_ a b] (:sentence sx)]
                       (tax/add-sib-exception (reasoning/taxonomy kb) a b h (:context sx))))
     :disintegrate (fn [kb sx]
                     (let [[_ a b] (:sentence sx)]
                       (tax/del-sib-exception! (reasoning/taxonomy kb) a b (:id sx))))
     :rebuild      (fn [tax {[_ a b] :sentence id :id ctx :context}]
                     (tax/add-sib-exception tax a b id ctx))
     :wff          wff/type-pair-problems}
    ;; `(arity P n)` is read by the per-assert arity check, so it is cached like the
    ;; other declarations the engine interprets rather than re-queried per assertion.
    ;; No `:wff` arm: the arity of `arity` is what would check it.
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
    ;; A roster declaration is a switch: its arriving or leaving rewrites the forced
    ;; memberships over what the predicate reaches and re-joins the rules in that reach,
    ;; so the stored content a firing swept while held void comes back
    ;; (docs/nmtms.md, "The forced-monotonic roster")
    'forced_monotonic_predicate (forcing-entry 'forced_monotonic_predicate)
    'forced_monotonic_between_predicates (forcing-entry 'forced_monotonic_between_predicates)
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
    ;; `(closedExtentForArg P n v)` is `closed_extent_predicate` narrowed to the goals
    ;; whose argument n is v.  The arms mark P under `:closed-extent-arg`, scoped like
    ;; `:closed-extent`, which is the gate `provers/closed-extent-for-arg?` reads before it
    ;; reads the grant's position and value back from the believed grants.  The re-check
    ;; postings are the whole-predicate grant's, for the same reason.
    'closedExtentForArg
    (-> (prop-entry 'closedExtentForArg)
        (assoc :integrate
               (fn [kb sx h]
                 (let [pred (second (:sentence sx))]
                   (tax/mark-prop (reasoning/taxonomy kb) :closed-extent-arg pred h (:context sx))
                   (index-closed-extent-rules kb pred))))
        (assoc :disintegrate
               (fn [kb sx]
                 (let [pred (second (:sentence sx))]
                   (tax/unmark-prop! (reasoning/taxonomy kb) :closed-extent-arg pred (:id sx))
                   (index-closed-extent-rules kb pred))))
        (assoc :wff wff/closed-extent-for-arg-problems))
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
    'reifiable_function   (assoc (reifiable-entry) :wff wff/function-decl-problems)
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
    ;; the homogeneity constraints share the covering forms' shape — a relation, an
    ;; optional start, a type — and so their wff arm
    'interArgs       (assoc (prop-entry 'interArgs)       :wff wff/covering-constraint-problems)
    'interArgAndRest (assoc (prop-entry 'interArgAndRest) :wff wff/covering-constraint-problems)
    ;; The two preservation declarations really are wff-only — read back per query, with
    ;; the transitivity of the relation they name checked here because `arg`'s open-world
    ;; reading cannot (docs/inherit.md).
    'transitiveInArgInverse {:wff wff/arg-preserving-problems}
    'transitiveInArg        {:wff wff/arg-preserving-problems}
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
   ;; (`pr/prop-kind`).
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
  this table holds an entry for.  `post-taxonomy-supporters!` replays it top to bottom and a
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
  to every arm.  Every arm is a context-free structural check and ignores it."
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
  is a fixpoint and must not abort halfway through one."
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
      (when-let [g (:disintegrate (get table f))]
        (let [before (permuting-marks (reasoning/taxonomy kb))]
          (g kb sentex)
          (note-permuting-moves! kb before)))
      (sx/exceptWhen-meta? sentence)
      (unindex-exceptWhen-meta kb sentex)
      ;; a visibility `except` leaving: queue the firings that use its target so settle
      ;; revives the conclusions it was hiding — the mirror of the integrate arm
      (= sx/except-functor f)
      (recheck-except kb sentex)
      (rules/rule-sentence? sentence)
      (do (p/unindex-rule! (:index kb) (:id sentex)
                           (rules/antecedent-keys (:antecedent sentex))
                           (rules/consequent-index-pred sentex)
                           (:context sentex))
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
          (swap! (reasoning/refused kb) #(-> (dissoc % (:id sentex)) (forget-kinds (:id sentex)))))
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
  index holds it from the store primitive (`kb/create-sentex`) — while no firing that
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

(defn post-taxonomy-supporters!
  "Post the taxonomy's supporter families (`kv/post-supporter!`) for every stored
  declaration in `kb`: the `:rebuild` column replayed in entry order over a scratch
  taxonomy whose index store is `kb`'s, then each stored disjoint metatype's members.
  `reindex`'s share of the index that its per-record pass cannot post, since the key a
  declaration installs is the table's to say.  `kb`'s own taxonomy is not touched, and the
  equality relations, whose partition keeps its own supporters, post nothing.

  A stored `genl` / `genlCx` declaration whose positional read is not a well-formed edge
  is dropped rather than posted (`replay-edge`), and the count is warned once — the same
  discipline `rebuild-tms` follows for a justification the store cannot root.  A
  well-formed store never has one; a store an older or foreign writer left a non-edge
  sentex in the genl / genlCx predicate extent does, and posting it would seed a null
  closure node that crashes `restore-depths`."
  [kb]
  (let [scratch (tax/create-taxonomy)
        skips   (volatile! 0)]
    (tax/install-index! scratch (:index kb))
    (binding [tax/*defer-depths?*    true
              tax/*defer-cycle-scc?* true
              *edge-replay-skips*    skips]
      (doseq [[f {:keys [rebuild]}] entries
              :when (and rebuild (not (contains? kb/equality-predicates f)))
              sx (stored-declarations kb f)]
        (rebuild scratch sx))
      (doseq [m (tax/stored-disjoint-metatypes scratch)
              {[_ t] :sentence id :id ctx :context} (stored-declarations kb m)]
        (tax/add-metatype-member scratch m t id ctx)))
    (when (pos? (long @skips))
      (trove/log! {:level :warn :id ::edges-malformed
                   :msg  (str @skips " stored genl/genlCx declarations are not well-formed"
                              " edges and are left out of the taxonomy")
                   :data {:skipped @skips}}))
    nil))

(defn rebuild-taxonomy
  "Rebuild the in-memory taxonomy over a cleared one: the believed side of every key the
  index's supporter families hold (`tax/refresh-beliefs` with no region, reading the
  network's labels), and the equality partition and rewrite rules, which keep their own
  supporters, replayed from their stored declarations by the `:rebuild` column.  Reads
  no other record.

  Drops every cache first: a rebuild that merged into the existing one could only ever
  *add*, so an entry whose sentex is gone would survive the recovery that was supposed to
  re-derive it."
  [kb]
  (let [tax (reasoning/taxonomy kb)]
    (tax/clear-relations! tax)
    (doseq [f    kb/equality-predicates
            :let [rebuild (:rebuild (get table f))]
            :when rebuild
            sx   (stored-declarations kb f)]
      (rebuild tax sx))
    (tax/refresh-beliefs tax (partial jtms/in? (reasoning/tms kb)))))

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(caches/register-derived
 {:id :S5 :label "Refused firings" :kind :index :keyed-by :handle :reads [:records :T1]
  :retired-by {:integrated :K :removed :K :settle-pass :G :recover :R :image-install :R
               :cleared :W}
  :computed :write :imaged? :state :at [[:refused]]
  :note "`{rule #{refusal}}` and the `:kinds` sub-roster; a constraint, lift or mint entry carries the `[genl genlCx]` generations it was refused under, and a settle pass releases it when they move"})

(caches/register-derived
 {:id :Q8 :label "Mint departures" :kind :queue :keyed-by :handle :reads [:records]
  :retired-by {:settle-pass :Q :recover :W :cleared :W}
  :computed :write :imaged? false :at [[:mint-queues :departed]]
  :note "the removed records that can have subsumed a mint (`note-departure!`); `withheld-releases` drains it"})

(caches/register-derived
 {:id :Q9 :label "Unpremised mints" :kind :queue :keyed-by :handle :reads [:records]
  :retired-by {:settle-pass :Q :recover :W :cleared :W}
  :computed :write :imaged? false :at [[:mint-queues :unpremised]]
  :note "the records a retraction left on a derivation alone (`note-unpremised!`); `subsumed-mint-blocks` drains it"})

(caches/register-derived
 {:id :Q1 :label "Exception re-check queue" :kind :queue :keyed-by :handle :reads [:records]
  :retired-by {:settle-pass :Q :recover :R :image-install :R}
  :computed :write :imaged? :state :at [[:recheck]]
  :note "`{rule triggers}` posted by `mark-recheck`, drained by `settle/drain-recheck!` each pass"})

(caches/register-derived
 {:id :Q2 :label "Supersession moves" :kind :queue :keyed-by :value :reads [:Q5 :M1]
  :retired-by {:settle-exit :Q :cleared :W :recover :R :image-install :R}
  :computed :write :imaged? :state :at [[:supersessions]]
  :note "the datums whose supersession entry moved, with each entry before its first move; `take-supersession-moves!` drains it"})

(caches/register-derived
 {:id :Q3 :label "Except moves" :kind :queue :keyed-by :handle :reads [:index :T1]
  :retired-by {:settle-pass :Q :settle-exit :Q :recover :W}
  :computed :write :imaged? false :at [[:except-moves]]
  :note "the handles an except began or stopped hiding, drained in two stages (`drain-except-moves!`, `take-except-moves!`)"})

(caches/register-derived
 {:id :Q4 :label "Respell queue" :kind :queue :keyed-by :functor :reads [:index]
  :retired-by {:held :Q :recover :W}
  :computed :write :imaged? false :at [[:respell]]
  :note "the predicates whose permuting marks moved; `settle/respelled-seeds` drains it"})
