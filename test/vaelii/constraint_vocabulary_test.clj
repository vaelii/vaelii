;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.constraint-vocabulary-test
  "Declared vocabulary that convicts something, and vocabulary that convicts nothing and
  says so.

  Two findings, one theme — a KB author gets identical silence from a constraint that is
  enforced and one that was never implemented, and each of these closes one way that
  happened:

  * **`arity` reaches back.**  It was enforced going forward and silent in the other
    order: `(arity P 2)` arriving after `(P A B C)` left the fact stored, believed and
    unmentioned, while an identical fact one line later was refused.  It now reports.  It
    deliberately does **not** arbitrate, and that is tested here too — the sentex it would
    pair with is the vocabulary entry the conviction is read through, so a nogood over the
    pair would defeat its own premise.

  * **`interArgIsa` exists.**  It was a plausible-looking declaration that stored fine and
    did nothing.  The conditional argument constraint reads open-world *twice, in opposite
    directions*, which is what these tests are mostly about: silence about the trigger
    argument's type leaves it dormant, silence about the target's is what convicts.

  The third finding of the same shape — that the grammar itself is now audited, so a new
  declaration nobody classified fails a test rather than landing in silence — needs a
  CoreContext baseline where these need a cleared one, and lives in
  `vocabulary-audit-test`."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.settle :as settle]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- arity-entries
  "The retroactive arity reports in the ledger, by the predicate each is about — one entry
  per declaration, so the predicate is the key."
  [kb]
  (into {} (for [e (v/violations kb) :when (= :arity (:violation e))]
             [(:predicate (:detail e)) (:detail e)])))

;;; ── arity: the declaration that arrives after the facts ────────────────

(tu/deftest-kb a-declaration-arriving-last-reports-the-facts-it-convicts
  ;; The measured gap.  Before this, `violations` came back empty and the wrong-arity
  ;; fact was indistinguishable from a right one — while the very next assert of the
  ;; same shape was refused.
  (tu/with-terms [parentOf A B C D E F]
    (v/assert kb (list parentOf A B C) 'UniverseContext)
    (v/assert kb (list parentOf D E F) 'UniverseContext)
    (v/assert kb (list 'arity parentOf 2) 'UniverseContext)
    (let [e  (get (arity-entries kb) parentOf)
          dh (v/handle-of kb (list 'arity parentOf 2) 'UniverseContext)]
      (is (some? e) "the declaration files a finding")
      (is (= 2 (:count e)) "both stored facts are counted")
      (is (= #{(list parentOf A B C) (list parentOf D E F)} (set (:sample e))))
      (is (= 2 (:expected e)))
      (is (= dh (:declared-after e))
          "the entry points at the declaration that convicted")
      (is (not (:truncated e)))
      (is (v/ask? kb (list parentOf A B C) 'UniverseContext)
          "reported, not withdrawn — nothing here moves belief"))))

(tu/deftest-kb one-entry-per-declaration-and-not-one-per-fact
  ;; The ledger keeps the newest 1000 entries, so a per-fact entry would let one
  ;; predicate's extent evict every other violation in it — the failure the disjointness
  ;; exposure beside this already had and fixed for its truncation notices.  Nothing is
  ;; lost by counting: the facts are all still stored, so anybody who wants the list can
  ;; re-derive it.
  (tu/with-terms [wideOf X]
    (doseq [i (range 30)]
      (v/assert kb (list wideOf X (symbol (str "TmpW" i)) 'Extra) 'UniverseContext))
    (v/assert kb (list 'arity wideOf 2) 'UniverseContext)
    (let [es (arity-entries kb)]
      (is (= 1 (count es)) "thirty convicted facts, one entry")
      (is (= 30 (:count (get es wideOf))))
      (is (= 3 (count (:sample (get es wideOf)))) "a sample, not the extent"))))

(tu/deftest-kb the-conforming-facts-of-the-same-predicate-are-not-counted
  (tu/with-terms [parentOf A B C G H]
    (v/assert kb (list parentOf A B C) 'UniverseContext)
    (v/assert kb (list parentOf G H) 'UniverseContext)
    (v/assert kb (list 'arity parentOf 2) 'UniverseContext)
    (is (= [(list parentOf A B C)] (:sample (get (arity-entries kb) parentOf)))
        "the sweep is over the predicate's extent; only the offender is in the finding")))

(tu/deftest-kb the-membership-spelling-of-an-arity-reaches-back-too
  ;; `(binaryPredicate P)` says the same thing as `(arity P 2)`, and `declared-arity`
  ;; reads both — so the trigger set and the O(1) gate have to know both, or the reach
  ;; works for a KB carrying CoreContext's derivation rules and silently not for one
  ;; loaded without them.
  (tu/with-terms [relOf A B C]
    (v/assert kb (list relOf A B C) 'UniverseContext)
    (v/assert kb (list 'binaryPredicate relOf) 'UniverseContext)
    (is (= [(list relOf A B C)] (:sample (get (arity-entries kb) relOf))))))

(tu/deftest-kb a-variableArity-predicate-is-exempt-on-the-retroactive-path-too
  ;; The exemption is the declaration's whole point (`lessThan` is declared binary *and*
  ;; reads a chain), and it is read by one `arity-problem` — so it must hold whichever
  ;; direction the check is asked from.
  (tu/with-terms [chainOf A B C]
    (v/assert kb (list chainOf A B C) 'UniverseContext)
    (v/assert kb (list 'variableArity chainOf) 'UniverseContext)
    (v/assert kb (list 'arity chainOf 2) 'UniverseContext)
    (is (empty? (arity-entries kb)))))

(tu/deftest-kb a-kb-that-declares-no-arity-reports-nothing
  (tu/with-terms [otherOf A B C D E]
    (v/assert kb (list otherOf A B C) 'UniverseContext)
    (v/assert kb (list otherOf D E) 'UniverseContext)
    (is (empty? (v/violations kb)))))

(tu/deftest-kb the-reach-is-an-event-and-an-unrelated-settle-does-not-re-file-it
  ;; Same contract as the disjointness exposure beside it: the entry says a declaration
  ;; *newly* convicted stored content.  A settle whose region holds neither the
  ;; declaration nor the facts has nothing new to say.
  (tu/with-terms [stableOf A B C X]
    (v/assert kb (list stableOf A B C) 'UniverseContext)
    (v/assert kb (list 'arity stableOf 2) 'UniverseContext)
    (is (= 1 (count (arity-entries kb))))
    (v/assert kb (list 'thing X) 'UniverseContext)
    (is (= 1 (count (arity-entries kb))) "not re-filed")))

(tu/deftest-kb a-rebuild-files-no-arity-reach-entry
  ;; The entry says a declaration *newly* convicted stored content, and on a rebuild
  ;; everything arrives at once, so there is no newly — the same reason the disjointness
  ;; exposure sits out `*rebuilding?*`.  Without the gate, every `recover` would re-file
  ;; the whole corpus's worth of findings.
  ;;
  ;; This is the opposite of `constraint-nogoods`' answer, and the difference is the kind:
  ;; a nogood is *state* belief depends on, so it must be re-derived on a rebuild or the
  ;; KB answers differently after a restart.  A report is an event, and re-filing it says
  ;; nothing new.
  (tu/with-terms [rebuiltOf A B C]
    (v/assert kb (list rebuiltOf A B C) 'UniverseContext)
    (v/assert kb (list 'arity rebuiltOf 2) 'UniverseContext)
    (is (= 1 (count (arity-entries kb))) "filed once when the declaration arrived")
    (v/clear-violations! kb)
    (v/recover kb)
    (is (empty? (arity-entries kb)) "and not again by the rebuild")
    (is (v/ask? kb (list rebuiltOf A B C) 'UniverseContext)
        "the fact survives the rebuild — nothing here withdrew it")))

(tu/deftest-kb a-reach-cut-short-by-the-budget-says-so
  ;; A bounded sweep that read as full coverage would be worse than no sweep: a reader
  ;; would take an entry's `:count` for the whole answer.  Budget bound low rather than
  ;; asserting 4096 facts, which is what the var is dynamic for.
  (binding [settle/*exposure-instance-budget* 2]
    (tu/with-terms [manyOf X]
      (doseq [i (range 6)]
        (v/assert kb (list manyOf X (symbol (str "TmpM" i)) 'Extra) 'UniverseContext))
      (v/assert kb (list 'arity manyOf 2) 'UniverseContext)
      (let [e (get (arity-entries kb) manyOf)]
        (is (:truncated e) "the entry admits the sweep was bounded")
        (is (= 2 (:budget e)))
        (is (<= (:count e) 2) "and counts only what it looked at")))))

(tu/deftest-kb a-wrong-arity-fact-is-refused-at-the-door-under-either-policy
  ;; The forward door has a caller to refuse and the conviction is not a weighable pair,
  ;; so unlike disjointness and functionality the constraint policy does not move it.
  (doseq [policy [:refuse :arbitrate]]
    (testing (str policy)
      (tu/with-neutral-kb [kb #(v/open-kb (assoc tu/scratch-space :constraints policy))]
        (tu/with-terms [firstOf A B C]
          (v/assert kb (list 'arity firstOf 2) 'UniverseContext)
          (is (thrown? clojure.lang.ExceptionInfo
                       (v/assert kb (list firstOf A B C) 'UniverseContext)))
          (is (nil? (v/handle-of kb (list firstOf A B C) 'UniverseContext))))))))

(deftest an-arity-clash-is-not-a-nogood
  ;; The decision, pinned rather than argued.  `arity` names a second believed sentex, so
  ;; it looks exactly like the three arbitrable kinds — and the sentex it names is the
  ;; vocabulary entry `declared-arity` answers from, which follows belief.  Arbitrating
  ;; the pair defeats the declaration, the taxonomy's arity table drops it at
  ;; settle-finish, and the next settle re-derives no clash because the table it would
  ;; read is empty: the dilemma is decided once and then reported by nobody, and while
  ;; the declaration is out it constrains no *other* use of the predicate either.
  ;;
  ;; So the pair stays out of `arbitrable-kinds`, and this is the test that fails if it
  ;; is ever put back without first making the vocabulary read independent of the belief
  ;; the nogood moves.
  (is (not (contains? checks/arbitrable-kinds :arity))
      "arity is not arbitrable; the comment above arbitrable-kinds has the measurement")
  (tu/with-neutral-kb [kb #(v/open-kb (assoc tu/scratch-space :constraints :arbitrate))]
    (tu/with-terms [relOf A B C]
      (v/assert kb (list relOf A B C) 'UniverseContext {:strength :monotonic})
      (v/assert kb (list 'arity relOf 2) 'UniverseContext)
      (is (empty? (v/contradictions kb)) "no dilemma is opened")
      (is (empty? (v/conflicts kb))      "and no irreducible clash")
      (is (v/ask? kb (list 'arity relOf 2) 'UniverseContext)
          "the declaration is not defeated, so it still constrains everything else")
      (is (v/ask? kb (list relOf A B C) 'UniverseContext))
      (is (seq (arity-entries kb)) "the finding is reported instead"))))

;;; ── interArgIsa: the conditional argument constraint ───────────────────

(defn- eats-world
  "`(interArgIsa eats 1 carnivore 2 meat)` over a hierarchy deep enough to test
  transitivity, with the four terms a caller needs back."
  [kb]
  (let [carnivore (tu/tmp-type "carnivore")
        meat      (tu/tmp-type "meat")
        beef      (tu/tmp-type "beef")
        grass     (tu/tmp-type "grass")
        eats      (tu/tmp-pred "eats")]
    (doseq [s [(list 'genl carnivore 'thing)
               (list 'genl meat 'thing)
               (list 'genl beef meat)
               (list 'genl grass 'thing)
               (list 'interArgIsa eats 1 carnivore 2 meat)]]
      (v/assert kb s 'UniverseContext))
    {:carnivore carnivore :meat meat :beef beef :grass grass :eats eats}))

(tu/deftest-kb a-conditional-constraint-refuses-the-violating-fact
  (let [{:keys [carnivore grass eats]} (eats-world kb)]
    (tu/with-terms [Rex Hay]
      (v/assert kb (list carnivore Rex) 'UniverseContext)
      (v/assert kb (list grass Hay) 'UniverseContext)
      (let [e (try (v/assert kb (list eats Rex Hay) 'UniverseContext) nil
                   (catch clojure.lang.ExceptionInfo x (ex-data x)))]
        (is (= :inter-arg-type (:type e)))
        (is (= Hay (:arg e)))
        (is (= Rex (:trigger e)))
        (is (= 1 (:trigger-position e)))
        (is (= 2 (:position e)))))))

(tu/deftest-kb the-target-type-is-reached-transitively
  ;; `argIsa` reads the genl closure and so does this: beef is a meat, so a carnivore
  ;; eating beef conforms.  Without the closure the constraint would only ever admit the
  ;; exact type named, which is not what a type hierarchy is for.
  (let [{:keys [carnivore beef eats]} (eats-world kb)]
    (tu/with-terms [Rex Chunk]
      (v/assert kb (list carnivore Rex) 'UniverseContext)
      (v/assert kb (list beef Chunk) 'UniverseContext)
      (is (v/assert kb (list eats Rex Chunk) 'UniverseContext)))))

(tu/deftest-kb an-unestablished-trigger-leaves-the-constraint-dormant
  ;; Half of the reading, and the half that inverts the constraint if it is got backwards:
  ;; silence about the eater's type is not evidence that it is a carnivore, so nothing
  ;; fires.  Read the other way, every untyped first argument would convict.
  (let [{:keys [grass eats]} (eats-world kb)]
    (tu/with-terms [Nobody Straw]
      (v/assert kb (list grass Straw) 'UniverseContext)
      (is (v/assert kb (list eats Nobody Straw) 'UniverseContext)))))

(tu/deftest-kb an-untyped-target-is-excused-by-open-world
  ;; The other half.  The target is convicted by *absence* of a path to the constraint
  ;; type — but an argument with no place in the hierarchy at all may simply be waiting
  ;; for the edges that place it, exactly as `args-problem` allows.
  (let [{:keys [carnivore eats]} (eats-world kb)]
    (tu/with-terms [Rex Mystery]
      (v/assert kb (list carnivore Rex) 'UniverseContext)
      (is (v/assert kb (list eats Rex Mystery) 'UniverseContext)))))

(tu/deftest-kb a-declaration-the-context-cannot-see-does-not-convict
  ;; Scoped like every other definitional check: a context is refused only on grounds
  ;; it can see.  The declaration is written in a sibling context, so it reaches nobody.
  (tu/with-terms [carnivore_t meat_t grass_t eatsOf Rex Hay SideContext OtherContext]
    (doseq [s [(list 'genl carnivore_t 'thing) (list 'genl meat_t 'thing)
               (list 'genl grass_t 'thing)]]
      (v/assert kb s 'UniverseContext))
    (v/assert kb (list 'genlContext SideContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'genlContext OtherContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'interArgIsa eatsOf 1 carnivore_t 2 meat_t) OtherContext)
    (v/assert kb (list carnivore_t Rex) SideContext)
    (v/assert kb (list grass_t Hay) SideContext)
    (is (v/assert kb (list eatsOf Rex Hay) SideContext))))

(tu/deftest-kb a-conditional-constraint-does-not-reach-back-over-stored-content
  ;; Deliberate, and the argument is `argIsa`'s verbatim: the conviction rests on the
  ;; absence of a path to the target type, so there is nothing to weigh and no policy
  ;; question anybody has answered about whether pre-existing silence is a violation.
  ;; Answering it inside a sweep would turn an open-world check into a closed-world one.
  (tu/with-terms [carnivore_t meat_t grass_t eatsOf Rex Hay]
    (doseq [s [(list 'genl carnivore_t 'thing) (list 'genl meat_t 'thing)
               (list 'genl grass_t 'thing)
               (list carnivore_t Rex) (list grass_t Hay) (list eatsOf Rex Hay)
               (list 'interArgIsa eatsOf 1 carnivore_t 2 meat_t)]]
      (v/assert kb s 'UniverseContext))
    (is (v/ask? kb (list eatsOf Rex Hay) 'UniverseContext))
    (is (empty? (v/violations kb)))
    (is (empty? (v/contradictions kb)))))

(tu/deftest-kb a-position-the-predicate-does-not-have-is-refused
  ;; Both positions, since `interArgIsa` names two and each is the same mistake: a
  ;; constraint that can never fire reads as enforced while enforcing nothing.
  (tu/with-terms [carnivore_t meat_t biteOf]
    (v/assert kb (list 'genl carnivore_t 'thing) 'UniverseContext)
    (v/assert kb (list 'genl meat_t 'thing) 'UniverseContext)
    (v/assert kb (list 'arity biteOf 2) 'UniverseContext)
    (doseq [bad [(list 'interArgIsa biteOf 1 carnivore_t 5 meat_t)
                 (list 'interArgIsa biteOf 5 carnivore_t 1 meat_t)]]
      (is (= :arg-position
             (:type (try (v/assert kb bad 'UniverseContext) nil
                         (catch clojure.lang.ExceptionInfo x (ex-data x)))))
          (str bad)))))

(tu/deftest-kb a-structurally-malformed-conditional-declaration-is-refused
  (tu/with-terms [carnivore_t meat_t someOf Muffet]
    (v/assert kb (list 'genl carnivore_t 'thing) 'UniverseContext)
    (v/assert kb (list 'genl meat_t 'thing) 'UniverseContext)
    (doseq [bad [(list 'interArgIsa someOf 1 carnivore_t)               ; four arguments
                 (list 'interArgIsa someOf 0 carnivore_t 2 meat_t)      ; position 0
                 (list 'interArgIsa someOf 1 carnivore_t 0 meat_t)
                 (list 'interArgIsa someOf 1 carnivore_t 2 Muffet)]]      ; an individual
      (is (= :not-well-formed
             (:type (try (v/assert kb bad 'UniverseContext) nil
                         (catch clojure.lang.ExceptionInfo x (ex-data x)))))
          (str bad)))))

(tu/deftest-kb the-conditional-declaration-entails-the-target-type
  ;; Under `*assertive-arg-types?*` the constraint reads as an entailment as well, exactly
  ;; as strong as `argIsa`'s and drawn under the same condition it convicts on — so a
  ;; dormant declaration entails nothing.
  (binding [checks/*assertive-arg-types?* true]
    (let [{:keys [carnivore meat eats]} (eats-world kb)]
      (tu/with-terms [Rex Chunk Nobody Other]
        (v/assert kb (list carnivore Rex) 'UniverseContext)
        (v/assert kb (list eats Rex Chunk) 'UniverseContext)
        (is (v/ask? kb (list meat Chunk) 'UniverseContext))
        (let [w (v/why kb (v/handle-of kb (list meat Chunk) 'UniverseContext))
              j (first (:support w))]
          (is (= 1 (count (:support w))) "one justification, not one per settle")
          (is (= 'interArgIsa (:informant j)))
          (is (= #{(list eats Rex Chunk)
                   (list 'interArgIsa eats 1 carnivore 2 meat)}
                 (set (map :sentence (:because j))))
              "justified by the fact and the declaration, so retracting either takes it back"))
        (v/assert kb (list eats Nobody Other) 'UniverseContext)
        (is (not (v/ask? kb (list meat Other) 'UniverseContext))
            "an unestablished trigger entails nothing")))))

(tu/deftest-kb the-conditional-entailment-is-drawn-in-either-arrival-order
  ;; `special/entail-existing` is the retroactive half, and it is the half that makes the
  ;; entailment order-independent: a declaration arriving after the facts must reach them
  ;; as readily as one arriving before reaches the facts that follow, or the same three
  ;; sentences derive a type in one order and not the other (docs/argtypes.md opens on
  ;; exactly this).  The *constraint* half deliberately does not reach back; the
  ;; entailment half does, and the two are not the same claim.
  (binding [checks/*assertive-arg-types?* true]
    (tu/with-terms [carnivore_t meat_t eatsOf Rex Chunk]
      (doseq [s [(list 'genl carnivore_t 'thing) (list 'genl meat_t 'thing)
                 (list carnivore_t Rex)
                 (list eatsOf Rex Chunk)]]                  ; the fact arrives FIRST
        (v/assert kb s 'UniverseContext))
      (is (not (v/ask? kb (list meat_t Chunk) 'UniverseContext))
          "nothing to entail from yet")
      (v/assert kb (list 'interArgIsa eatsOf 1 carnivore_t 2 meat_t) 'UniverseContext)
      (is (v/ask? kb (list meat_t Chunk) 'UniverseContext)
          "the declaration reaches back over the fact already stored"))))

(tu/deftest-kb retracting-either-half-takes-the-conditional-entailment-back
  ;; The entailment is justified by [the fact, the declaration], so it is not a fact of
  ;; its own — dropping either antecedent must withdraw it.  Asserted rather than argued,
  ;; because a derived type that outlived its support would be a type nothing licenses.
  (binding [checks/*assertive-arg-types?* true]
    (tu/with-terms [carnivore_t meat_t eatsOf Rex Chunk]
      (doseq [s [(list 'genl carnivore_t 'thing) (list 'genl meat_t 'thing)
                 (list carnivore_t Rex)
                 (list 'interArgIsa eatsOf 1 carnivore_t 2 meat_t)
                 (list eatsOf Rex Chunk)]]
        (v/assert kb s 'UniverseContext))
      (is (v/ask? kb (list meat_t Chunk) 'UniverseContext))
      (v/retract! kb (v/handle-of kb (list 'interArgIsa eatsOf 1 carnivore_t 2 meat_t)
                                  'UniverseContext))
      (is (not (v/ask? kb (list meat_t Chunk) 'UniverseContext))
          "retracting the declaration withdraws what it entailed"))))

(tu/deftest-kb a-derived-conclusion-violating-a-conditional-constraint-is-dropped
  ;; The derivation path cannot throw — a fixpoint that aborted mid-run would make belief
  ;; depend on firing order — so an argument-constraint violation there is dropped and
  ;; reported, exactly as `argIsa`'s is.  `interArgIsa` joins that path or a rule becomes
  ;; a way around the check.
  (tu/with-terms [carnivore_t meat_t grass_t eatsOf feedsOf Rex Hay]
    (doseq [s [(list 'genl carnivore_t 'thing) (list 'genl meat_t 'thing)
               (list 'genl grass_t 'thing)
               (list 'interArgIsa eatsOf 1 carnivore_t 2 meat_t)
               (list carnivore_t Rex) (list grass_t Hay)
               (list 'set/forwardRule (vr/rule-sentence [(list feedsOf '?a '?b)]
                                                        (list eatsOf '?a '?b)))]]
      (v/assert kb s 'UniverseContext))
    (v/assert kb (list feedsOf Rex Hay) 'UniverseContext)
    (is (nil? (v/handle-of kb (list eatsOf Rex Hay) 'UniverseContext))
        "the violating conclusion is not stored")
    (is (some #{:inter-arg-type} (map :violation (v/violations kb)))
        "and it is reported rather than silently lost")))
