;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.constraint-vocabulary-test
  "Declared vocabulary that convicts something, and vocabulary that convicts nothing and
  says so.

  Two findings, one theme — a KB author gets identical silence from a constraint that is
  enforced and one that was never implemented, and each of these closes one way that
  happened:

  * **`arity` reaches back.**  A tuple of a length its predicate's binding breaks is a
    one-member nogood each reader decides, whichever of the two arrived first.  The
    binding is forced-monotonic, so the nogood never takes it OUT.

  * **`interArg` exists.**  It was a plausible-looking declaration that stored fine and
    did nothing.  The conditional argument constraint reads open-world *twice, in opposite
    directions*, which is what these tests are mostly about: silence about the trigger
    argument's type leaves it dormant, silence about the target's is what convicts.

  The third finding of the same shape — that the grammar itself is now audited, so a new
  declaration nobody classified fails a test rather than landing in silence — needs an
  upper-layer baseline where these need a cleared one, and lives in
  `vocabulary-audit-test`."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;;; ── arity: the declaration that arrives after the facts ────────────────

(tu/deftest-kb a-declaration-arriving-last-takes-the-facts-it-convicts-out
  (tu/with-terms [parentOf A B C D E F G H]
    (v/assert kb (list parentOf A B C) 'CxUniverse)
    (v/assert kb (list parentOf D E F) 'CxUniverse)
    (v/assert kb (list parentOf G H) 'CxUniverse)
    (v/assert kb (list 'arity parentOf 2) 'CxUniverse)
    (is (not (v/ask? kb (list parentOf A B C) 'CxUniverse)))
    (is (not (v/ask? kb (list parentOf D E F) 'CxUniverse)))
    (is (v/ask? kb (list parentOf G H) 'CxUniverse) "the conforming fact stays believed")
    (is (empty? (v/violations kb)) "and nothing is filed in the ledger")))

(tu/deftest-kb the-membership-spelling-of-an-arity-reaches-back-too
  ;; `(binary_predicate P)` says the same thing as `(arity P 2)`, and a reader reads both.
  (tu/with-terms [relOf A B C]
    (v/assert kb (list relOf A B C) 'CxUniverse)
    (v/assert kb (list 'binary_predicate relOf) 'CxUniverse)
    (is (not (v/ask? kb (list relOf A B C) 'CxUniverse)))))

(tu/deftest-kb a-variableArity-predicate-is-exempt-on-the-retroactive-path-too
  (tu/with-terms [chainOf A B C]
    (v/assert kb (list chainOf A B C) 'CxUniverse)
    (v/assert kb (list 'variable_arity chainOf) 'CxUniverse)
    (v/assert kb (list 'arity chainOf 2) 'CxUniverse)
    (is (v/ask? kb (list chainOf A B C) 'CxUniverse))))

(tu/deftest-kb a-kb-that-declares-no-arity-reports-nothing
  (tu/with-terms [otherOf A B C D E]
    (v/assert kb (list otherOf A B C) 'CxUniverse)
    (v/assert kb (list otherOf D E) 'CxUniverse)
    (is (empty? (v/violations kb)))))

(tu/deftest-kb a-rebuild-reads-the-inert-tuple-the-same
  ;; `recover` rebuilds the `:out` members (`arity/drain!`), so the reading after a
  ;; restart is the reading before it.
  (tu/with-terms [rebuiltOf A B C]
    (v/assert kb (list rebuiltOf A B C) 'CxUniverse)
    (v/assert kb (list 'arity rebuiltOf 2) 'CxUniverse)
    (is (not (v/ask? kb (list rebuiltOf A B C) 'CxUniverse)))
    (v/recover kb)
    (is (not (v/ask? kb (list rebuiltOf A B C) 'CxUniverse)) "and the same after the rebuild")))

(tu/deftest-kb a-wrong-arity-fact-is-stored-and-read-out-at-the-entry-point
  ;; No refusal reads a binding, so the stored set is the same in either arrival order.
  (tu/with-terms [firstOf A B C]
    (v/assert kb (list 'arity firstOf 2) 'CxUniverse)
    (is (some? (v/assert kb (list firstOf A B C) 'CxUniverse)))
    (is (not (v/ask? kb (list firstOf A B C) 'CxUniverse)))))

(deftest a-monotonic-tuple-breaking-a-binding-is-inert-and-the-binding-stays-in
  ;; The binding is forced-monotonic, and the tuple breaking it is in the
  ;; `:out` forced set at `:monotonic` as at `:default`.  No dilemma opens, and `conflicts`
  ;; reports the tuple grounded on the declaration.
  (is (not (contains? checks/arbitrable-kinds :arity)))
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (tu/with-terms [relOf A B C]
      (let [t    (v/assert kb (list relOf A B C) 'CxUniverse {:strength :monotonic})
            decl (v/assert kb (list 'arity relOf 2) 'CxUniverse)]
        (is (empty? (v/contradictions kb)) "no dilemma is opened")
        (is (= [[:arity [t] [decl]]]
               (mapv (juxt :kind :handles #(mapv :handle (:grounds %))) (v/conflicts kb))))
        (is (v/ask? kb (list 'arity relOf 2) 'CxUniverse))
        (is (not (v/ask? kb (list relOf A B C) 'CxUniverse)))))))

;;; ── interArg: the conditional argument constraint ───────────────────

(defn- eats-world
  "`(interArg eats 1 carnivore 2 meat)` over a hierarchy deep enough to test
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
               (list 'disjoint grass meat)
               (list 'interArg eats 1 carnivore 2 meat)]]
      (v/assert kb s 'CxUniverse))
    {:carnivore carnivore :meat meat :beef beef :grass grass :eats eats}))

(tu/deftest-kb a-conditional-constraint-holds-the-violating-fact-inert
  ;; the constraint-only reading: the conviction is the subject
  (tu/without-entailing
   (let [{:keys [carnivore grass eats]} (eats-world kb)]
     (tu/with-terms [Rex Hay]
       (v/assert kb (list carnivore Rex) 'CxUniverse)
       (v/assert kb (list grass Hay) 'CxUniverse)
       (let [e (tu/write-conviction kb (list eats Rex Hay) 'CxUniverse)]
         (is (= :inter-arg-type (:type e)))
         (is (= Hay (:arg e)))
         (is (= Rex (:trigger e)))
         (is (= 1 (:trigger-position e)))
         (is (= 2 (:position e))))))))

(tu/deftest-kb the-target-type-is-reached-transitively
  ;; `arg` reads the genl closure and so does this: beef is a meat, so a carnivore
  ;; eating beef conforms.  Without the closure the constraint would only ever admit the
  ;; exact type named, which is not what a type hierarchy is for.
  (let [{:keys [carnivore beef eats]} (eats-world kb)]
    (tu/with-terms [Rex Chunk]
      (v/assert kb (list carnivore Rex) 'CxUniverse)
      (v/assert kb (list beef Chunk) 'CxUniverse)
      (is (v/assert kb (list eats Rex Chunk) 'CxUniverse)))))

(tu/deftest-kb an-unestablished-trigger-leaves-the-constraint-dormant
  ;; Half of the reading, and the half that inverts the constraint if it is got backwards:
  ;; silence about the eater's type is not evidence that it is a carnivore, so nothing
  ;; fires.  Read the other way, every untyped first argument would convict.
  (let [{:keys [grass eats]} (eats-world kb)]
    (tu/with-terms [Nobody Straw]
      (v/assert kb (list grass Straw) 'CxUniverse)
      (is (v/assert kb (list eats Nobody Straw) 'CxUniverse)))))

(tu/deftest-kb an-untyped-target-is-excused-by-open-world
  ;; The other half.  The target is convicted only by a type the taxonomy separates from
  ;; the constraint type, so an argument with no place in the hierarchy is admitted, as
  ;; `args-problem` admits it.
  (let [{:keys [carnivore eats]} (eats-world kb)]
    (tu/with-terms [Rex Mystery]
      (v/assert kb (list carnivore Rex) 'CxUniverse)
      (is (v/assert kb (list eats Rex Mystery) 'CxUniverse)))))

(tu/deftest-kb a-declaration-the-context-cannot-see-does-not-convict
  ;; Scoped like every other definitional check: a context is refused only on grounds
  ;; it can see.  The declaration is written in a sibling context, so it reaches nobody.
  (tu/with-terms [carnivore_t meat_t grass_t eatsOf Rex Hay CxSide CxOther]
    (doseq [s [(list 'genl carnivore_t 'thing) (list 'genl meat_t 'thing)
               (list 'genl grass_t 'thing)]]
      (v/assert kb s 'CxUniverse))
    (v/assert kb (list 'genlCx CxSide 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxOther 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'interArg eatsOf 1 carnivore_t 2 meat_t) CxOther)
    (v/assert kb (list carnivore_t Rex) CxSide)
    (v/assert kb (list grass_t Hay) CxSide)
    (is (v/assert kb (list eatsOf Rex Hay) CxSide))))

(tu/deftest-kb a-conditional-constraint-does-not-reach-back-over-stored-content
  ;; `assert` of the declaration stores it over the stored fact. Hay has no type the
  ;; taxonomy separates from meat_t, so neither the write nor `try-assert` has a
  ;; conflict to report.
  (tu/with-terms [carnivore_t meat_t grass_t eatsOf Rex Hay]
    (doseq [s [(list 'genl carnivore_t 'thing) (list 'genl meat_t 'thing)
               (list 'genl grass_t 'thing)
               (list carnivore_t Rex) (list grass_t Hay) (list eatsOf Rex Hay)
               (list 'interArg eatsOf 1 carnivore_t 2 meat_t)]]
      (v/assert kb s 'CxUniverse))
    (is (v/ask? kb (list eatsOf Rex Hay) 'CxUniverse))
    (is (empty? (v/violations kb)))
    (is (empty? (v/contradictions kb)))))

(tu/deftest-kb try-assert-refuses-a-position-the-predicate-does-not-have
  ;; Both positions, since `interArg` names two and each is the same mistake: a
  ;; constraint that can never fire reads as enforced while enforcing nothing.
  (tu/with-terms [carnivore_t meat_t biteOf]
    (v/assert kb (list 'genl carnivore_t 'thing) 'CxUniverse)
    (v/assert kb (list 'genl meat_t 'thing) 'CxUniverse)
    (v/assert kb (list 'arity biteOf 2) 'CxUniverse)
    (doseq [bad [(list 'interArg biteOf 1 carnivore_t 5 meat_t)
                 (list 'interArg biteOf 5 carnivore_t 1 meat_t)]]
      (is (= :arg-position (tu/try-violation kb bad 'CxUniverse)) (str bad)))))

(tu/deftest-kb a-structurally-malformed-conditional-declaration-is-refused
  (tu/with-terms [carnivore_t meat_t someOf Muffet]
    (v/assert kb (list 'genl carnivore_t 'thing) 'CxUniverse)
    (v/assert kb (list 'genl meat_t 'thing) 'CxUniverse)
    (doseq [bad [(list 'interArg someOf 1 carnivore_t)               ; four arguments
                 (list 'interArg someOf 0 carnivore_t 2 meat_t)      ; position 0
                 (list 'interArg someOf 1 carnivore_t 0 meat_t)
                 (list 'interArg someOf 1 carnivore_t 2 Muffet)]]      ; an individual
      (is (= :not-well-formed
             (:type (try (v/assert kb bad 'CxUniverse) nil
                         (catch clojure.lang.ExceptionInfo x (ex-data x)))))
          (str bad)))))

(tu/deftest-kb the-conditional-declaration-entails-the-target-type
  ;; Under `*assertive-arg-types?*` the constraint is read as an entailment as well, exactly
  ;; as strong as `arg`'s and drawn under the same condition it convicts on — so a
  ;; dormant declaration entails nothing.
  (binding [argument/*assertive-arg-types?* true]
    (let [{:keys [carnivore meat eats]} (eats-world kb)]
      (tu/with-terms [Rex Chunk Nobody Other]
        (v/assert kb (list carnivore Rex) 'CxUniverse)
        (v/assert kb (list eats Rex Chunk) 'CxUniverse)
        (is (v/ask? kb (list meat Chunk) 'CxUniverse))
        (let [w (tu/why-root kb (v/handle-of kb (list meat Chunk) 'CxUniverse))
              j (first (:support w))]
          (is (= 1 (count (:support w))) "one justification, not one per settle")
          (is (= 'interArg (kb/mint-kind kb (:informant j))))
          (is (= #{(list eats Rex Chunk)
                   (list 'interArg eats 1 carnivore 2 meat)
                   (list carnivore Rex)}
                 (set (map :sentence (:because j))))
              "justified by the fact, the declaration and the trigger, so retracting any takes it back"))
        (v/assert kb (list eats Nobody Other) 'CxUniverse)
        (is (not (v/ask? kb (list meat Other) 'CxUniverse))
            "an unestablished trigger entails nothing")))))

(tu/deftest-kb the-conditional-entailment-is-drawn-in-either-arrival-order
  ;; `special/entail-existing` is the retroactive half, and it is the half that makes the
  ;; entailment order-independent: a declaration arriving after the facts must reach them
  ;; as readily as one arriving before reaches the facts that follow, or the same three
  ;; sentences derive a type in one order and not the other (docs/argtypes.md opens on
  ;; exactly this).  The *constraint* half deliberately does not reach back; the
  ;; entailment half does, and the two are not the same claim.
  (binding [argument/*assertive-arg-types?* true]
    (tu/with-terms [carnivore_t meat_t eatsOf Rex Chunk]
      (doseq [s [(list 'genl carnivore_t 'thing) (list 'genl meat_t 'thing)
                 (list carnivore_t Rex)
                 (list eatsOf Rex Chunk)]]                  ; the fact arrives FIRST
        (v/assert kb s 'CxUniverse))
      (is (not (v/ask? kb (list meat_t Chunk) 'CxUniverse))
          "nothing to entail from yet")
      (v/assert kb (list 'interArg eatsOf 1 carnivore_t 2 meat_t) 'CxUniverse)
      (is (v/ask? kb (list meat_t Chunk) 'CxUniverse)
          "the declaration reaches back over the fact already stored"))))

(tu/deftest-kb retracting-either-half-takes-the-conditional-entailment-back
  ;; The entailment is justified by [the fact, the declaration], so it is not a fact of
  ;; its own — dropping either antecedent must withdraw it.  Asserted rather than argued,
  ;; because a derived type that outlived its support would be a type nothing licenses.
  (binding [argument/*assertive-arg-types?* true]
    (tu/with-terms [carnivore_t meat_t eatsOf Rex Chunk]
      (doseq [s [(list 'genl carnivore_t 'thing) (list 'genl meat_t 'thing)
                 (list carnivore_t Rex)
                 (list 'interArg eatsOf 1 carnivore_t 2 meat_t)
                 (list eatsOf Rex Chunk)]]
        (v/assert kb s 'CxUniverse))
      (is (v/ask? kb (list meat_t Chunk) 'CxUniverse))
      (v/retract! kb (v/handle-of kb (list 'interArg eatsOf 1 carnivore_t 2 meat_t)
                                  'CxUniverse))
      (is (not (v/ask? kb (list meat_t Chunk) 'CxUniverse))
          "retracting the declaration withdraws what it entailed"))))

(tu/deftest-kb a-derived-conclusion-violating-a-conditional-constraint-is-held
  ;; the constraint-only reading: the conviction is the subject
  (tu/without-entailing
   ;; The derivation path cannot throw, so an argument-constraint violation there is
   ;; stored, held OUT and reported, exactly as `arg`'s is.  `interArg` joins that path
   ;; or a rule becomes a way around the check.
   (tu/with-terms [carnivore_t meat_t grass_t eatsOf feedsOf Rex Hay]
     (doseq [s [(list 'genl carnivore_t 'thing) (list 'genl meat_t 'thing)
                (list 'genl grass_t 'thing) (list 'disjoint grass_t meat_t)
                (list 'interArg eatsOf 1 carnivore_t 2 meat_t)
                (list carnivore_t Rex) (list grass_t Hay)
                (list 'set/forwardRule (vr/rule-sentence [(list feedsOf '?a '?b)]
                                                         (list eatsOf '?a '?b)))]]
       (v/assert kb s 'CxUniverse))
     (v/assert kb (list feedsOf Rex Hay) 'CxUniverse)
     (is (some? (v/handle-of kb (list eatsOf Rex Hay) 'CxUniverse))
         "the violating conclusion is stored")
     (is (not (v/ask? kb (list eatsOf Rex Hay) 'CxUniverse)) "and not believed")
     (is (some #(and (= :inert-argument (:violation %)) (= :inter-arg-type (:type (:detail %))))
               (v/violations kb))
         "and it is reported rather than silently lost"))))
