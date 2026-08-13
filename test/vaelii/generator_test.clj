;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.generator-test
  "Rule generators: a rule whose consequent is a rule, whose firing stamps that rule out
  with its holes filled (docs/generators.md).

  The scoping rule is the thing to pin, because nothing in the spelling announces it.
  A variable the generator's antecedents also mention is a **hole** — bound by the join,
  ground in the mint.  Every other variable in the stamped rule is the stamped rule's
  own and must survive as a variable, or the mint is a rule that matches one tuple
  instead of a pattern.  Half these tests are about that one distinction.

  The other half is what a mint *is*: derived content, justified by the firing, so it
  leaves the way any conclusion leaves.  That only works because both chainers ask
  belief of a rule before using it, so `a-defeated-generator-stops-stamping` and
  `retracting-the-fill-retracts-the-rule` are as much tests of `res/rule-believed?` as
  of the generator."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- rule-sentexes
  "The stored rules in `ctx`, as sentexes — a rule is the sentex with an `:antecedent`."
  [kb ctx]
  (filter :antecedent (v/sentexes-in-context kb ctx)))

(defn- stamped
  "The rules in `ctx` that conclude a fact — every stored rule but the generators."
  [kb ctx]
  (remove vr/generator-sentex? (rule-sentexes kb ctx)))

(defn- generators
  "The stored rules in `ctx` that conclude a rule, at any nesting depth."
  [kb ctx]
  (filter vr/generator-sentex? (rule-sentexes kb ctx)))

;; ---- the shape works ------------------------------------------------------

(tu/deftest-kb a-generator-stamps-one-rule-per-firing
  (tu/with-terms [planVerb outcomeEmotion planOf feels succeededAt failedAt Joy Regret]
    (v/assert kb (list 'implies
                       (list 'and (list planVerb '?outcome)
                             (list outcomeEmotion '?outcome '?emotion))
                       (list 'implies
                             (list 'and (list planOf '?a '?p) (list '?outcome '?a '?p))
                             (list feels '?a '?emotion)))
              'CxUniverse)
    (v/assert kb (list planVerb succeededAt) 'CxUniverse)
    (v/assert kb (list planVerb failedAt) 'CxUniverse)
    (v/assert kb (list outcomeEmotion succeededAt Joy) 'CxUniverse)
    (v/assert kb (list outcomeEmotion failedAt Regret) 'CxUniverse)
    (testing "one stamped rule per fill, and no more"
      (is (= 2 (count (stamped kb 'CxUniverse)))))
    (testing "the hole is ground in the mint and the stamped rule keeps its own variables"
      (let [s (:sentence (first (filter #(some #{succeededAt}
                                               (vr/antecedent-predicates (:sentence %)))
                                        (stamped kb 'CxUniverse))))]
        (is (some? s) "a rule was stamped for succeededAt")
        ;; the stamped rule's own `?a` / `?p` survive as variables — canonically
        ;; renumbered, but variables
        (is (every? #(re-matches #"\?var\d+" (str %))
                    (filter #(and (symbol? %) (.startsWith (str %) "?"))
                            (tree-seq sequential? seq s)))
            "no stamped variable was frozen into a constant")))))

(tu/deftest-kb a-stamped-rule-draws-conclusions
  (tu/with-terms [planVerb outcomeEmotion planOf feels succeededAt Joy Tom Plan]
    (v/assert kb (list 'implies
                       (list 'and (list planVerb '?outcome)
                             (list outcomeEmotion '?outcome '?emotion))
                       (list 'implies
                             (list 'and (list planOf '?a '?p) (list '?outcome '?a '?p))
                             (list feels '?a '?emotion)))
              'CxUniverse)
    (v/assert kb (list planVerb succeededAt) 'CxUniverse)
    (v/assert kb (list outcomeEmotion succeededAt Joy) 'CxUniverse)
    (v/assert kb (list planOf Tom Plan) 'CxUniverse)
    (v/assert kb (list succeededAt Tom Plan) 'CxUniverse)
    (is (= #{Joy} (into #{} (map '?e) (v/ask kb (list feels Tom '?e) 'CxUniverse))))))

(tu/deftest-kb both-arrival-orders-agree
  ;; order independence, the first invariant: whether the generator or the facts it
  ;; ranges over arrive first cannot change what the KB believes.  A generator needs no
  ;; retroactive sweep of its own for this — it is an ordinary rule, and a newly
  ;; asserted rule is a datum that joins over what is already stored.
  ;;
  ;; Two disjoint term sets in the one KB rather than two KBs: the temporaries are
  ;; gensym'd, so neither order can see the other's vocabulary.
  (let [run (fn [generator-first?]
              (tu/with-terms [marker pairing subject feels src Joy Tom Plan]
                (let [gen   #(v/assert kb (list 'implies
                                                (list 'and (list marker '?o)
                                                      (list pairing '?o '?e))
                                                (list 'implies
                                                      (list 'and (list subject '?a '?p)
                                                            (list '?o '?a '?p))
                                                      (list feels '?a '?e)))
                                       'CxUniverse)
                      facts #(do (v/assert kb (list marker src) 'CxUniverse)
                                 (v/assert kb (list pairing src Joy) 'CxUniverse)
                                 (v/assert kb (list subject Tom Plan) 'CxUniverse)
                                 (v/assert kb (list src Tom Plan) 'CxUniverse))]
                  (if generator-first? (do (gen) (facts)) (do (facts) (gen)))
                  {:derived (into #{} (map '?e) (v/ask kb (list feels Tom '?e)
                                                       'CxUniverse))
                   :joy     Joy})))
        a   (run true)
        b   (run false)]
    (is (= #{(:joy a)} (:derived a)) "generator first derives the conclusion")
    (is (= #{(:joy b)} (:derived b)) "facts first derives it too")))

(tu/deftest-kb the-wrapper-on-the-stamped-rule-sets-its-direction
  ;; the answer to "how do I say the generated rule is a default / backward one": the
  ;; wrapper rides inside the consequent, where substitution never touches it
  (tu/with-terms [marker src dst thing]
    (v/assert kb (list 'implies (list marker '?p)
                       (list 'set/defaultRule
                             (list 'implies (list '?p '?x) (list dst '?x))))
              'CxUniverse)
    (v/assert kb (list marker src) 'CxUniverse)
    (let [minted (first (stamped kb 'CxUniverse))]
      (is (some? minted) "a rule was stamped")
      (is (:defeasible minted) "the stamped rule carries the defaultRule the template set")
      (is (= :both (:direction minted))))))

;; ---- a mint is derived content -------------------------------------------

(tu/deftest-kb retracting-the-fill-retracts-the-rule
  (tu/with-terms [marker src dst Fido]
    (v/assert kb (list 'implies (list marker '?p)
                       (list 'implies (list '?p '?x) (list dst '?x)))
              'CxUniverse)
    (let [fill (v/assert kb (list marker src) 'CxUniverse)]
      (v/assert kb (list src Fido) 'CxUniverse)
      (testing "the stamped rule fired"
        (is (seq (v/sentexes-matching kb (list dst Fido) 'CxUniverse))))
      (let [minted (:id (first (stamped kb 'CxUniverse)))]
        (is (some? minted))
        (v/retract! kb fill)
        (testing "the mint is no longer believed"
          (is (not (v/in? kb minted))))
        (testing "and neither is what it concluded"
          (is (empty? (v/sentexes-matching kb (list dst Fido) 'CxUniverse))))))))

(tu/deftest-kb a-disbelieved-rule-does-not-fire
  ;; the belief filter on its own, with no generator in sight: this is the property
  ;; `res/rule-believed?` adds, and a mint is only retractable because it holds
  (tu/with-terms [marker src dst Fido Rex]
    (v/assert kb (list 'implies (list marker '?p)
                       (list 'implies (list '?p '?x) (list dst '?x)))
              'CxUniverse)
    (let [fill (v/assert kb (list marker src) 'CxUniverse)]
      (v/assert kb (list src Fido) 'CxUniverse)
      (v/retract! kb fill)
      (testing "a fact arriving after the mint lost its support draws nothing"
        (v/assert kb (list src Rex) 'CxUniverse)
        (v/forward-chain kb)
        (is (empty? (v/sentexes-matching kb (list dst Rex) 'CxUniverse)))))))

(tu/deftest-kb one-rule-stamped-two-ways-is-one-handle
  ;; dedup is the ordinary sentex dedup, so it costs nothing: two fills that substitute
  ;; to the same rule share a handle and collect a justification each
  (tu/with-terms [markerA markerB src dst]
    (doseq [m [markerA markerB]]
      (v/assert kb (list 'implies (list m '?p)
                         (list 'implies (list '?p '?x) (list dst '?x)))
                'CxUniverse))
    (v/assert kb (list markerA src) 'CxUniverse)
    (v/assert kb (list markerB src) 'CxUniverse)
    (is (= 1 (count (stamped kb 'CxUniverse)))
        "the two generators stamped one rule, not two")
    (let [h (:id (first (stamped kb 'CxUniverse)))]
      (is (<= 2 (count (v/supporting-justifications kb h)))
          "and it rests on both firings"))))

;; ---- what is refused ------------------------------------------------------

(defn- refusal
  "The `:type` `assert` throws for `sentence`, or `:accepted`."
  [kb sentence]
  (try (v/assert kb sentence 'CxUniverse) :accepted
       (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(tu/deftest-kb a-level-that-fills-nothing-new-is-refused
  ;; The per-level form of `a-generator-sharing-no-variable-is-refused`, and under
  ;; nesting it is a mistake the *outer* fill creates: `?x` is a hole of the first
  ;; level, so it is already ground when the second level is stored, and that level
  ;; stamps the same rule at every firing.  Saying so at the sentence is what keeps it
  ;; out of the ledger, one mint at a time.
  (tu/with-terms [aa bb cc dd]
    (is (= :not-range-restricted
           (refusal kb (list 'implies (list aa '?x)
                             (list 'implies (list bb '?x)
                                   (list 'implies (list cc '?x) (list dd '?x)))))))))

(tu/deftest-kb a-generator-is-forward-only
  (tu/with-terms [marker dst]
    (is (= :not-indexable
           (refusal kb (list 'set/backwardRule
                             (list 'implies (list marker '?p)
                                   (list 'implies (list '?p '?x) (list dst '?x)))))))))

(tu/deftest-kb a-generator-sharing-no-variable-is-refused
  ;; it would stamp the same rule at every firing, which is a rule the author could
  ;; have written
  (tu/with-terms [marker src dst]
    (is (= :not-range-restricted
           (refusal kb (list 'implies (list marker '?p)
                             (list 'implies (list src '?x) (list dst '?x))))))))

(tu/deftest-kb the-stamped-rule-owes-its-own-range-restriction
  (tu/with-terms [marker dst]
    (is (= :not-range-restricted
           (refusal kb (list 'implies (list marker '?p)
                             (list 'implies (list '?p '?x) (list dst '?x '?loose))))))))

(tu/deftest-kb a-hole-may-stand-in-functor-position-but-a-non-hole-may-not
  (tu/with-terms [marker dst]
    (testing "a hole in functor position is what a generator is for"
      (is (= :accepted
             (refusal kb (list 'implies (list marker '?p)
                               (list 'implies (list '?p '?x) (list dst '?x)))))))
    (testing "a variable functor beside the hole binds to nothing, so it is unindexable"
      ;; `?p` is a hole and fine; `?q` is not and never will be, so every mint this
      ;; generator could produce is a rule the index cannot key
      (is (= :not-indexable
             (refusal kb (list 'implies (list marker '?p)
                               (list 'implies (list 'and (list '?p '?x) (list '?q '?x))
                                     (list dst '?x)))))))
    (testing "and with no hole at all the sharper complaint comes first"
      (is (= :not-range-restricted
             (refusal kb (list 'implies (list marker '?p)
                               (list 'implies (list '?q '?x) (list dst '?x)))))))))

(tu/deftest-kb an-exceptWhen-on-the-stamped-rule-is-refused
  ;; it would be dropped in silence — a firing has no way to split an exception into
  ;; the meta-sentex that carries it — and a guard that vanishes is worse than one
  ;; refused
  (tu/with-terms [marker src dst blocked Fido]
    (is (= :not-well-formed
           (refusal kb (list 'implies (list marker '?p)
                             (list 'exceptWhen (list blocked '?x)
                                   (list 'implies (list '?p '?x) (list dst '?x)))))))
    (testing "but an exceptWhen on the generator says when not to generate, and holds"
      (is (= :accepted
             (refusal kb (list 'exceptWhen (list blocked '?p)
                               (list 'implies (list marker '?p)
                                     (list 'implies (list '?p '?x) (list dst '?x)))))))
      (v/assert kb (list blocked src) 'CxUniverse)
      (v/assert kb (list marker src) 'CxUniverse)
      (is (empty? (stamped kb 'CxUniverse))
          "the blocked fill stamped nothing")
      (v/assert kb (list src Fido) 'CxUniverse)
      (is (empty? (v/sentexes-matching kb (list dst Fido) 'CxUniverse))))))

(tu/deftest-kb a-stamped-existential-head-skolemizes-when-the-stamped-rule-fires
  ;; the generator's firing must NOT skolemize — the stamped rule's variables are its
  ;; own — but an `exists` the author marked inside the stamped rule still means what it
  ;; means, one firing later and against the stamped rule's own handle
  (tu/with-terms [marker src linked Fido]
    (v/assert kb (list 'implies (list marker '?p)
                       (list 'implies (list '?p '?x)
                             (list 'exists '?y (list linked '?x '?y))))
              'CxUniverse)
    (v/assert kb (list marker src) 'CxUniverse)
    (is (= 1 (count (stamped kb 'CxUniverse))))
    (v/assert kb (list src Fido) 'CxUniverse)
    (is (seq (v/sentexes-matching kb (list linked Fido '?y) 'CxUniverse))
        "the stamped rule minted its witness")))

(tu/deftest-kb a-generator-cycle-is-refused
  (tu/with-terms [mm nn kk pp qq]
    (testing "one generator stamping what another reads"
      (is (= :accepted
             (refusal kb (list 'implies (list mm '?o)
                               (list 'implies (list '?o '?a) (list kk '?a))))))
      (is (= :not-stratified
             (refusal kb (list 'implies (list 'and (list kk '?o) (list nn '?o))
                               (list 'implies (list '?o '?a) (list pp '?a)))))))
    (testing "and a generator that feeds itself"
      (is (= :not-stratified
             (refusal kb (list 'implies (list qq '?o)
                               (list 'implies (list '?o '?a) (list qq '?a)))))))))

(tu/deftest-kb the-cycle-check-sees-a-wrapped-generator-too
  ;; every generator is filed under the one key `implies`, which means peeling the
  ;; wrapper off the stamped rule first — it is the stamped rule's, not the
  ;; generator's.  Without the peel this generator files under `set/defaultRule`, the
  ;; roster misses it, and the cycle below is admitted.
  (tu/with-terms [mm nn kk pp]
    (is (= :accepted
           (refusal kb (list 'implies (list mm '?o)
                             (list 'set/defaultRule
                                   (list 'implies (list '?o '?a) (list kk '?a)))))))
    (is (= :not-stratified
           (refusal kb (list 'implies (list 'and (list kk '?o) (list nn '?o))
                             (list 'implies (list '?o '?a) (list pp '?a))))))))

(tu/deftest-kb check-predicts-assert-on-every-generator-refusal
  ;; the repo's contract, and it matters most at the one door that writes two records:
  ;; an editor validating a generator must be told what the firing would refuse
  (tu/with-terms [marker dst aa bb cc dd mid inner]
    (doseq [[label sentence]
            [["a level that fills nothing new"
              (list 'implies (list aa '?x)
                    (list 'implies (list bb '?x)
                          (list 'implies (list cc '?x) (list dd '?x))))]
             ["backward"     (list 'set/backwardRule
                                   (list 'implies (list marker '?p)
                                         (list 'implies (list '?p '?x) (list dst '?x))))]
             ["backward on a middle level"
              (list 'implies (list marker '?p)
                    (list 'set/backwardRule
                          (list 'implies (list '?p '?q)
                                (list 'implies (list '?q '?x) (list dst '?x)))))]
             ["an exceptWhen an inner level carries"
              (list 'implies (list marker '?p)
                    (list 'implies (list '?p '?q)
                          (list 'exceptWhen (list mid '?x)
                                (list 'implies (list '?q '?x) (list dst '?x)))))]
             ["a functor no level binds, three levels in"
              (list 'implies (list marker '?p)
                    (list 'implies (list '?p '?q)
                          (list 'implies (list 'and (list '?q '?x) (list '?zz '?x))
                                (list dst '?x))))]
             ["loose var"    (list 'implies (list marker '?p)
                                   (list 'implies (list '?p '?x) (list dst '?x '?loose)))]
             ["loose var, three levels in"
              (list 'implies (list marker '?p)
                    (list 'implies (list '?p '?q)
                          (list 'implies (list '?q '?x) (list inner '?x '?loose))))]]]
      (testing label
        (let [predicted (v/check kb sentence 'CxUniverse)
              thrown    (refusal kb sentence)]
          (is (seq predicted) "check reports a problem")
          (is (= thrown (:type (first predicted)))
              "and it is the one assert throws"))))))

;; ---- nesting: a stamped rule may stamp one in turn ------------------------
;; The scoping rule composes, so nothing is capped: a variable belongs to the outermost
;; level whose antecedents mention it, and that level's firing grounds it.  What the
;; extra level buys is a functor: a predicate bound *further out* is concrete before the
;; rule that uses it is stored, so a family of predicates can range over a family of
;; types without the index ever seeing a variable in functor position.

(tu/deftest-kb a-generator-may-stamp-a-generator
  ;; the type-level/instance-level bridge, stated once instead of once per pair: the
  ;; outer level fills the two predicates, the middle fills the type, and what is stored
  ;; at the bottom is an ordinary rule over concrete functors
  (tu/with-terms [typeVersion hasCap capType bird flying Tweety]
    (v/assert kb (list 'implies (list typeVersion '?ipred '?tpred)
                       (list 'implies (list '?tpred '?type '?cap)
                             (list 'implies (list '?type '?instance)
                                   (list '?ipred '?instance '?cap))))
              'CxUniverse)
    (testing "the pair fact stamps a generator, not a rule"
      (v/assert kb (list typeVersion hasCap capType) 'CxUniverse)
      (is (= 2 (count (generators kb 'CxUniverse))) "the written one and its mint")
      (is (empty? (stamped kb 'CxUniverse)) "and nothing that concludes a fact yet"))
    (testing "the type-level fact stamps the rule the mint was for"
      (v/assert kb (list capType bird flying) 'CxUniverse)
      (is (= 1 (count (stamped kb 'CxUniverse))))
      (is (= bird (first (vr/antecedent-predicates
                          (:sentence (first (stamped kb 'CxUniverse))))))
          "keyed on the type, which was a variable two levels up"))
    (testing "and the instance-level conclusion follows"
      (v/assert kb (list bird Tweety) 'CxUniverse)
      (is (= #{flying} (into #{} (map '?c) (v/ask kb (list hasCap Tweety '?c) 'CxUniverse)))))))

(tu/deftest-kb an-outer-level-binds-the-functor-a-middle-one-cannot
  ;; the distinction nesting exists for, in one pair of sentences.  Both write the same
  ;; join; only the nested one stores rules the index can key.
  (tu/with-terms [typeVersion hasCap capType]
    (testing "same level: the type is bound by a literal of the rule being stored"
      (is (= :not-indexable
             (refusal kb (list 'implies (list typeVersion '?ipred '?tpred)
                               (list 'implies (list 'and (list '?tpred '?type '?cap)
                                                    (list '?type '?instance))
                                     (list '?ipred '?instance '?cap)))))))
    (testing "a level out: the type is a hole of the middle level, ground before it stores"
      (is (= :accepted
             (refusal kb (list 'implies (list typeVersion '?ipred '?tpred)
                               (list 'implies (list '?tpred '?type '?cap)
                                     (list 'implies (list '?type '?instance)
                                           (list '?ipred '?instance '?cap))))))))))

(tu/deftest-kb nesting-is-not-capped
  ;; three levels, so the middle mint is itself a generator that stamps a generator.
  ;; What bounds a generator is the cycle check, not the depth.
  (tu/with-terms [aFor m1 m2 m3 endsAt Zed]
    (v/assert kb (list 'implies (list aFor '?p)
                       (list 'implies (list '?p '?q)
                             (list 'implies (list '?q '?r)
                                   (list 'implies (list '?r '?x) (list endsAt '?x)))))
              'CxUniverse)
    (v/assert kb (list aFor m1) 'CxUniverse)
    (v/assert kb (list m1 m2) 'CxUniverse)
    (v/assert kb (list m2 m3) 'CxUniverse)
    (v/assert kb (list m3 Zed) 'CxUniverse)
    (is (v/ask? kb (list endsAt Zed) 'CxUniverse))
    (is (empty? (v/violations kb)) "every level's mint stood on its own")
    (is (= 3 (count (generators kb 'CxUniverse))) "the written generator and two mints")
    (is (= 1 (count (stamped kb 'CxUniverse))) "and one rule at the bottom")))

(tu/deftest-kb retracting-an-outer-fill-unwinds-the-whole-chain
  ;; a mint is derived content at every level, so one relabel takes the chain: the fill
  ;; goes, the generator it stamped stops being believed, the rule *that* stamped goes
  ;; with it, and so does the conclusion
  (tu/with-terms [typeVersion hasCap capType bird flying Tweety]
    (v/assert kb (list 'implies (list typeVersion '?ipred '?tpred)
                       (list 'implies (list '?tpred '?type '?cap)
                             (list 'implies (list '?type '?instance)
                                   (list '?ipred '?instance '?cap))))
              'CxUniverse)
    (let [pair (v/assert kb (list typeVersion hasCap capType) 'CxUniverse)]
      (v/assert kb (list capType bird flying) 'CxUniverse)
      (v/assert kb (list bird Tweety) 'CxUniverse)
      (is (seq (v/ask kb (list hasCap Tweety '?c) 'CxUniverse)))
      (let [minted (mapv :id (remove #(vr/generator-sentex? %)
                                     (rule-sentexes kb 'CxUniverse)))]
        (v/retract! kb pair)
        (testing "the conclusion goes"
          (is (empty? (v/ask kb (list hasCap Tweety '?c) 'CxUniverse))))
        (testing "and so does every rule the chain minted, at both levels"
          (is (every? #(not (v/in? kb %)) minted))
          (is (= 1 (count (filter #(v/in? kb (:id %)) (rule-sentexes kb 'CxUniverse))))
              "only the generator the author wrote is left"))))))

(tu/deftest-kb both-arrival-orders-agree-under-nesting
  ;; order independence again, now over three levels: each level's mint is a datum that
  ;; joins over what is already stored, so no arrival order needs a sweep of its own
  (let [run (fn [reverse?]
              (tu/with-terms [typeVersion hasCap capType bird flying Tweety]
                (let [gen   #(v/assert kb (list 'implies (list typeVersion '?ipred '?tpred)
                                                (list 'implies (list '?tpred '?type '?cap)
                                                      (list 'implies (list '?type '?instance)
                                                            (list '?ipred '?instance '?cap))))
                                       'CxUniverse)
                      facts #(do (v/assert kb (list bird Tweety) 'CxUniverse)
                                 (v/assert kb (list capType bird flying) 'CxUniverse)
                                 (v/assert kb (list typeVersion hasCap capType) 'CxUniverse))]
                  (if reverse? (do (facts) (gen)) (do (gen) (facts)))
                  {:derived (into #{} (map '?c) (v/ask kb (list hasCap Tweety '?c)
                                                       'CxUniverse))
                   :flying  flying})))
        a   (run false)
        b   (run true)]
    (is (= #{(:flying a)} (:derived a)) "generator first derives the conclusion")
    (is (= #{(:flying b)} (:derived b)) "facts first derives it too")))

(tu/deftest-kb a-middle-level-owes-what-a-generator-owes
  ;; every level reaches the store as a rule, and the mint reads the same check list the
  ;; assert door does — so a wrapper or a guard the firing could not honour is refused
  ;; at the sentence rather than one mint later
  (tu/with-terms [marker dst blocked]
    (testing "a backward wrapper on a middle level"
      (is (= :not-indexable
             (refusal kb (list 'implies (list marker '?p)
                               (list 'set/backwardRule
                                     (list 'implies (list '?p '?q)
                                           (list 'implies (list '?q '?x) (list dst '?x)))))))))
    (testing "an exceptWhen on an inner level, which no firing can split off"
      (is (= :not-well-formed
             (refusal kb (list 'implies (list marker '?p)
                               (list 'implies (list '?p '?q)
                                     (list 'exceptWhen (list blocked '?x)
                                           (list 'implies (list '?q '?x)
                                                 (list dst '?x)))))))))
    (testing "and the innermost rule still owes its own range restriction"
      (is (= :not-range-restricted
             (refusal kb (list 'implies (list marker '?p)
                               (list 'implies (list '?p '?q)
                                     (list 'implies (list '?q '?x)
                                           (list dst '?x '?loose))))))))))

(tu/deftest-kb a-nested-mint-that-cannot-stand-is-dropped-and-recorded
  ;; the mint door under nesting: a fill can make the *middle* rule junk, and the
  ;; firing must record it rather than throw — the fixpoint is halfway through itself
  (tu/with-terms [typeVersion capType]
    (v/assert kb (list 'implies (list typeVersion '?ipred '?tpred)
                       (list 'implies (list '?tpred '?type '?cap)
                             (list 'implies (list '?type '?instance)
                                   (list '?ipred '?instance '?cap))))
              'CxUniverse)
    (v/clear-violations! kb)
    ;; a number in the instance-level predicate's place heads a literal no index can key
    (v/assert kb (list typeVersion 7 capType) 'CxUniverse)
    (is (empty? (stamped kb 'CxUniverse)) "nothing was stored for it")
    (is (= 1 (count (generators kb 'CxUniverse))) "and no generator was minted either")
    (is (seq (v/violations kb)) "the drop is readable")))

(tu/deftest-kb a-cycle-through-a-nested-generator-is-refused
  ;; the cycle check reads the *innermost* conclusion, because that is what reaches the
  ;; fact store — the levels between conclude rules, under a key no fact carries
  (tu/with-terms [mm nn kk pp]
    (testing "a nested generator that feeds itself"
      (is (= :not-stratified
             (refusal kb (list 'implies (list mm '?p)
                               (list 'implies (list '?p '?q)
                                     (list 'implies (list '?q '?x) (list mm '?x))))))))
    (testing "and one whose innermost conclusion another generator reads"
      (is (= :accepted
             (refusal kb (list 'implies (list nn '?p)
                               (list 'implies (list '?p '?q)
                                     (list 'implies (list '?q '?x) (list kk '?x)))))))
      (is (= :not-stratified
             (refusal kb (list 'implies (list 'and (list kk '?o) (list pp '?o))
                               (list 'implies (list '?o '?a) (list pp '?a)))))))))

;; ---- the mint goes through the same door ---------------------------------

(tu/deftest-kb a-mint-that-cannot-stand-is-dropped-and-recorded
  ;; a fill can put a name in functor position that the index cannot key.  The firing
  ;; must not throw — a fixpoint may not abort halfway through itself — so the mint is
  ;; dropped and lands in the violation ledger instead.
  (tu/with-terms [marker dst]
    (v/assert kb (list 'implies (list marker '?p)
                       (list 'implies (list '?p '?x) (list dst '?x)))
              'CxUniverse)
    (v/clear-violations! kb)
    ;; a fill that is a *number* heads a literal no index can key
    (v/assert kb (list marker 7) 'CxUniverse)
    (testing "nothing was stored for it"
      (is (empty? (stamped kb 'CxUniverse))))
    (testing "and the drop is readable"
      (is (seq (v/violations kb))))))

(tu/deftest-kb a-stamped-conjunctive-consequent-is-polycanonicalized
  ;; the same split an asserted rule gets: one rule per conjunct, each keyed by its own
  ;; consequent predicate, or `rules-by-consequent` could not answer for either
  (tu/with-terms [marker src dstA dstB]
    (v/assert kb (list 'implies (list marker '?p)
                       (list 'implies (list '?p '?x)
                             (list 'and (list dstA '?x) (list dstB '?x))))
              'CxUniverse)
    (v/assert kb (list marker src) 'CxUniverse)
    (is (= 2 (count (stamped kb 'CxUniverse)))
        "one stamped rule per conjunct")
    (is (= #{dstA dstB}
           (into #{} (map #(vr/consequent-predicate (:sentence %)))
                 (stamped kb 'CxUniverse))))))

(tu/deftest-kb a-mint-is-reachable-by-the-index-both-ways
  ;; the whole point of minting rather than interpreting: what gets stored is an
  ;; ordinary rule, so it is keyed by concrete predicates and both engines find it
  (tu/with-terms [marker src dst Fido]
    (v/assert kb (list 'implies (list marker '?p)
                       (list 'implies (list '?p '?x) (list dst '?x)))
              'CxUniverse)
    (v/assert kb (list marker src) 'CxUniverse)
    (let [h (:id (first (stamped kb 'CxUniverse)))]
      (testing "posted under the stamped antecedent, not under a variable"
        (is (contains? (set (p/rules-by-antecedent (:index kb) src)) h)))
      (testing "and under the stamped consequent"
        (is (contains? (set (p/rules-by-consequent (:index kb) dst)) h))))
    (testing "so a backward goal reaches it too"
      (v/assert kb (list src Fido) 'CxUniverse)
      (is (v/provable? kb (list dst Fido) 'CxUniverse)))))

(tu/deftest-kb asserting-a-stamped-rule-gives-it-a-ground-of-its-own
  ;; A stamped rule is a *conclusion*: it rests on the generator's justification and
  ;; goes when the generator does.  Asserting the same rule is a second and independent
  ;; ground for it, and the rule door marks the premise for it as the fact door does —
  ;; so the rule outlives the generator that first stamped it, and carries the class
  ;; the assertion stated rather than none.
  (tu/with-terms [marker src dst Fido]
    (let [gh (v/assert kb (list 'implies (list marker '?p)
                                (list 'implies (list '?p '?x) (list dst '?x)))
                       'CxUniverse)]
      (v/assert kb (list marker src) 'CxUniverse)
      (let [sx (first (stamped kb 'CxUniverse))]
        (is (some? sx) "the generator stamped a rule")
        (is (false? (v/premise? kb (:id sx))) "a conclusion, resting on the generator")
        (let [h (v/assert kb (:sentence sx) 'CxUniverse {:strength :monotonic})]
          (is (= (:id sx) h) "one rule, one handle — the assertion is not a second sentex")
          (is (true? (v/premise? kb h)) "and now a premise in its own right")
          (is (= :monotonic (:strength (v/sentex kb h)))))
        (testing "so retracting the generator leaves the asserted rule standing"
          (v/retract! kb gh)
          (is (v/in? kb (:id sx)))
          (v/assert kb (list src Fido) 'CxUniverse)
          (is (seq (v/sentexes-matching kb (list dst Fido) 'CxUniverse))
              "and still firing"))))))
