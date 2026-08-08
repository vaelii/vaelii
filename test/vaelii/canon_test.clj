;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.canon-test
  "Sentex canonicalization: the structural connectives (not / implies / and) are
  decomposed into the record and kept out of both indexes; numbers and strings are
  not term-indexed; rules identical up to variable names collapse to one handle; a
  conjunctive consequent polycanonicalizes into one rule per conjunct; an
  `exceptWhen` exception is split off into a separate belief-following meta-sentex
  that names the rule by handle and aligns its query to the rule's canonical
  variables; and a spec-type fact in a spec context triggers a general rule (genl +
  genlContext together)."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- flatten-key [k]
  (filter (complement sequential?) (tree-seq sequential? seq k)))

;; ---- the struct stores truth / antecedent / consequent ------------------

(tu/deftest-kb connectives-canonicalize-into-the-record
  (testing "a negation decomposes into truth :false over the positive body"
    (let [s (sx/sentex '(not (flies Tweety)) 'AContext)]
      (is (= :false (:truth s)))
      (is (= '(flies Tweety) (sx/body s)))
      (is (nil? (:antecedent s)))))
  (testing "double negation is eliminated"
    (let [s (sx/sentex '(not (not (flies Tweety))) 'AContext)]
      (is (= :true (:truth s)))
      (is (= '(flies Tweety) (:sentence s)))))
  (testing "a rule decomposes into antecedent (a vector) and consequent, canonically named"
    (let [s (sx/sentex '(implies (and (parentOf ?x ?y) (parentOf ?y ?z)) (grandparentOf ?x ?z)) 'AContext)]
      (is (= '[(parentOf ?var0 ?var1) (parentOf ?var1 ?var2)] (:antecedent s)))
      (is (= '(grandparentOf ?var0 ?var2) (:consequent s)))
      (is (= :true (:truth s)))
      (testing "and the varmap gets back to the author's names"
        (is (= '{?var0 ?x ?var1 ?y ?var2 ?z} (:varmap s)))
        (is (= '(implies (and (parentOf ?x ?y) (parentOf ?y ?z)) (grandparentOf ?x ?z))
               (sx/originalize (:sentence s) (:varmap s)))))))
  (testing "the trie key contains none of not / implies / and"
    (let [k (sx/path (sx/sentex '(implies (and (a ?x)) (b ?x)) 'AContext))]
      (is (not (some '#{implies and not} (flatten-key k)))))))

;; ---- numbers, strings, connectives are not term-indexed -----------------

(tu/deftest-kb term-index-skips-numbers-strings-and-connectives
  (let [person (tu/tmp-type) animal (tu/tmp-type)
        tom (tu/tmp-ind) bone (tu/tmp-ind)
        birthYearOf (tu/tmp-pred) mortal (tu/tmp-pred)
        immortal (tu/tmp-pred) likes (tu/tmp-pred)]
    (v/assert kb (list 'genl person animal) 'UContext)
    (v/assert kb (list 'argIsa birthYearOf 1 person) 'UContext)
    (v/assert kb (list person tom) 'UContext)
    (v/assert kb (list birthYearOf tom 1970) 'UContext)
    (v/assert kb (list 'comment tom "a fine fellow") 'UContext)
    (v/assert-rule kb [(list person '?p)] (list mortal '?p) 'UContext)
    (v/assert-rule kb [(list person '?p)] (list 'not (list immortal '?p)) 'UContext)   ; a nested `not` inside a rule
    (v/assert-rule kb [(list person '?p)] (list likes '?p bone) 'UContext)             ; a constant argument
    (v/assert kb (list 'not (list mortal tom)) 'UContext)
    (testing "a number is not a term-index key"
      (is (empty? (v/find-sentexes kb 1970))))
    (testing "a string is not a term-index key"
      (is (empty? (v/find-sentexes kb "a fine fellow"))))
    (testing "the structural connectives are never term-indexed, even nested in a rule"
      (is (empty? (v/find-sentexes kb 'implies)))
      (is (empty? (v/find-sentexes kb 'and)))
      (is (empty? (v/find-sentexes kb 'not))))           ; the (not (immortal ?p)) rule must not leak it
    (testing "symbols and ground compounds are still found"
      (is (seq (v/find-sentexes kb birthYearOf)))
      (is (seq (v/find-sentexes kb tom)))
      (is (seq (v/find-sentexes kb (list birthYearOf tom 1970))))
      (is (seq (v/find-sentexes kb mortal)))             ; a rule is found by its predicates
      (is (seq (v/find-sentexes kb immortal)))           ; the stripped-`not` literal's predicate
      (is (seq (v/find-sentexes kb bone))))))            ; and by a constant argument

;; ---- rules identical up to variable names collapse to one handle --------

(tu/deftest-kb alpha-equivalent-rules-share-one-sentex
  (let [dog (tu/tmp-type) animal (tu/tmp-type)
        breathes (tu/tmp-pred) mortal (tu/tmp-pred)]
    (v/assert kb (list 'genl dog animal) 'UContext)
    (let [h1 (v/assert-rule kb [(list animal '?x)] (list breathes '?x) 'UContext)
          n1 (count (p/sentex-ids (:records kb)))
          h2 (v/assert-rule kb [(list animal '?y)] (list breathes '?y) 'UContext)]   ; same rule, renamed
      (testing "the second assertion finds the existing handle, stores nothing new"
        (is (= h1 h2))
        (is (= n1 (count (p/sentex-ids (:records kb))))))
      (testing "a genuinely different rule is a different sentex"
        (is (not= h1 (v/assert-rule kb [(list animal '?x)] (list mortal '?x) 'UContext))))
      (testing "dedup is scoped to context — the same rule elsewhere is distinct"
        (is (not= h1 (v/assert-rule kb [(list animal '?z)] (list breathes '?z) 'OtherContext)))))))

;; ---- a conjunctive consequent polycanonicalizes -------------------------

(tu/deftest-kb conjunctive-consequent-splits-into-multiple-rules
  (let [a (tu/tmp-type) b (tu/tmp-type) c (tu/tmp-type) d (tu/tmp-type)
        x1 (tu/tmp-ind)]
    (doseq [t [a b c d]] (v/assert kb (list 'genl t 'thing) 'UContext))
    (v/assert kb (list a x1) 'UContext)
    (let [handles (v/assert-rule kb [(list a '?x)] (list 'and (list b '?x) (list c '?x) (list d '?x)) 'UContext)]
      (testing "assert-rule returns one handle per conjunct"
        (is (vector? handles))
        (is (= 3 (count (distinct handles)))))
      (testing "each conjunct is derived independently"
        (is (seq (v/sentexes-matching kb (list b x1) 'UContext)))
        (is (seq (v/sentexes-matching kb (list c x1) 'UContext)))
        (is (seq (v/sentexes-matching kb (list d x1) 'UContext))))
      (testing "retracting one split rule leaves the others standing"
        (v/retract! kb (first handles))                  ; the (b ?x) rule
        (is (empty? (v/sentexes-matching kb (list b x1) 'UContext)))
        (is (seq (v/sentexes-matching kb (list c x1) 'UContext)))))))

(tu/deftest-kb polycanon-covers-directed-and-default-rules
  (let [a (tu/tmp-type) b (tu/tmp-type) c (tu/tmp-type)
        d (tu/tmp-type) e (tu/tmp-type) f (tu/tmp-type)
        x (tu/tmp-ind)]
    (doseq [t [a b c d e f]] (v/assert kb (list 'genl t 'thing) 'UContext))
    (v/assert kb (list a x) 'UContext)
    (testing "a backward directed conjunctive consequent splits; each conjunct is provable"
      (v/assert-rule kb [(list a '?x)] (list 'and (list b '?x) (list c '?x)) 'UContext {:direction :backward})
      (is (v/provable? kb (list b x) 'UContext))
      (is (v/provable? kb (list c x) 'UContext)))
    (testing "a default conjunctive consequent splits; each conjunct is derived"
      (v/assert kb (list 'set/defaultRule (list 'implies (list a '?x) (list 'and (list d '?x) (list e '?x)))) 'UContext)
      (is (seq (v/sentexes-matching kb (list d x) 'UContext)))
      (is (seq (v/sentexes-matching kb (list e x) 'UContext))))
    (testing "a negated conjunction consequent does NOT split (De Morgan ⇒ a disjunction)"
      (is (not (vector? (v/assert-rule kb [(list a '?x)] (list 'not (list 'and (list f '?x) (list b '?x))) 'UContext)))))))

;; ---- spec-type fact in a spec context triggers a general rule -----------

(tu/deftest-kb spec-fact-in-spec-context-triggers-a-general-rule
  (let [dog (tu/tmp-type) mammal (tu/tmp-type) animal (tu/tmp-type)
        fido (tu/tmp-ind) rex (tu/tmp-ind)
        breathes (tu/tmp-pred) hasFur (tu/tmp-pred)]
    (v/assert kb (list 'genlContext 'SpecContext 'GenContext) 'GenContext)
    (v/assert kb (list 'genl mammal animal) 'GenContext)
    (v/assert kb (list 'genl dog mammal) 'GenContext)
    (v/assert-rule kb [(list animal '?x)] (list breathes '?x) 'GenContext)   ; general type, general context
    (v/assert kb (list dog fido) 'SpecContext)                               ; spec type, spec context
    (testing "genl (subtype) and genlContext (subcontext) combine to fire the rule"
      (is (seq (v/sentexes-matching kb (list breathes fido) 'SpecContext))))
    (testing "and the conclusion is placed in the spec context"
      (is (= '(SpecContext) (v/contexts-of kb (list breathes fido)))))
    (testing "it fires regardless of assertion order (rule after fact)"
      (v/assert kb (list dog rex) 'SpecContext)
      (v/assert-rule kb [(list mammal '?y)] (list hasFur '?y) 'GenContext)
      (is (seq (v/sentexes-matching kb (list hasFur rex) 'SpecContext))))))

(tu/deftest-kb a-join-rule-fires-over-spec-facts-with-a-common-viewpoint
  ;; The requirement's join case: two antecedents, spec-type facts, genl + genlContext.
  (let [dog (tu/tmp-type) cat (tu/tmp-type) animal (tu/tmp-type)
        fido (tu/tmp-ind) tom (tu/tmp-ind) whiskers (tu/tmp-ind)
        coexist (tu/tmp-pred)]
    (v/assert kb (list 'genlContext 'AContext 'TopContext) 'TopContext)
    (v/assert kb (list 'genlContext 'BContext 'TopContext) 'TopContext)        ; AContext, BContext are sibling subs of TopContext
    (v/assert kb (list 'genl dog animal) 'TopContext)
    (v/assert kb (list 'genl cat animal) 'TopContext)
    (v/assert-rule kb [(list animal '?x) (list animal '?y)] (list coexist '?x '?y) 'TopContext)  ; join on animal
    (v/assert kb (list dog fido) 'AContext)
    (v/assert kb (list cat tom) 'TopContext)
    (testing "a spec fact in a sub joins a fact in the shared super, placed in the sub"
      (is (seq (v/sentexes-matching kb (list coexist fido tom) 'AContext))))
    (testing "two facts in sibling subs (no common viewpoint) derive nothing"
      (v/assert kb (list cat whiskers) 'BContext)
      (is (empty? (v/sentexes-matching kb (list coexist fido whiskers) '?ctx)))
      (is (empty? (v/sentexes-matching kb (list coexist whiskers fido) '?ctx))))))

;; ---- the fixes surfaced by review: soundness of assert ------------------

(tu/deftest-kb a-bare-implies-is-range-restriction-checked
  (let [bird (tu/tmp-type) animal (tu/tmp-type)
        flies (tu/tmp-pred) robin (tu/tmp-ind)]
    (v/assert kb (list 'genl bird animal) 'UContext)
    (testing "a bare (implies ..) with an unbound consequent variable is rejected"
      (is (= :not-range-restricted
             (try (v/assert kb (list 'implies (list bird '?x) (list flies '?y)) 'UContext) nil
                  (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))))
    (testing "and no junk (flies ?y) fact was stored to match against everything"
      (is (empty? (v/find-sentexes kb flies))))
    (testing "a range-restricted bare implies works and fires"
      (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) 'UContext)
      (v/assert kb (list bird robin) 'UContext)
      (is (seq (v/sentexes-matching kb (list flies robin) 'UContext))))))

(tu/deftest-kb double-negation-respects-premise-constraints
  (let [dog (tu/tmp-type) cat (tu/tmp-type) animal (tu/tmp-type)
        felix (tu/tmp-ind) rex (tu/tmp-ind)]
    (v/assert kb (list 'genl dog animal) 'UContext)
    (v/assert kb (list 'genl cat animal) 'UContext)
    (v/assert kb (list 'disjoint dog cat) 'UContext)
    (v/assert kb (list cat felix) 'UContext)
    (testing "(not (not (dog Felix))) canonicalizes to (dog Felix) and hits the disjoint check"
      (is (thrown? clojure.lang.ExceptionInfo (v/assert kb (list 'not (list 'not (list dog felix))) 'UContext))))
    (testing "a genuine single negation is not arg/disjoint-checked"
      (is (some? (v/assert kb (list 'not (list dog rex)) 'UContext))))))

(tu/deftest-kb an-empty-conjunction-consequent-is-rejected
  (let [a (tu/tmp-type)]
    (v/assert kb (list 'genl a 'thing) 'UContext)
    (is (= :not-range-restricted
           (try (v/assert-rule kb [(list a '?x)] (list 'and) 'UContext) nil
                (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))))

(tu/deftest-kb a-positive-wildcard-query-does-not-match-negations
  (let [dog (tu/tmp-type) animal (tu/tmp-type)
        fido (tu/tmp-ind) rex (tu/tmp-ind)]
    (v/assert kb (list 'genl dog animal) 'UContext)
    (v/assert kb (list dog fido) 'UContext)
    (v/assert kb (list 'not (list dog rex)) 'UContext)
    (testing "(?p ?x) binds ?p only to real predicates, never to `not` via a negation"
      (let [preds (set (map #(get % '?p) (v/prove kb '(?p ?x) '?ctx)))]
        (is (contains? preds dog))
        (is (not (contains? preds 'not)))))))

(tu/deftest-kb rule-assertion-is-idempotent
  (let [a (tu/tmp-type) b (tu/tmp-type)]
    (v/assert kb (list 'genl a 'thing) 'UContext)
    (v/assert kb (list 'genl b 'thing) 'UContext)
    (testing "re-asserting a rule with a different direction resolves to one record"
      (let [h  (v/assert kb (list 'set/forwardRule (list 'implies (list a '?x) (list b '?x))) 'UContext)
            h2 (v/assert kb (list 'set/backwardRule (list 'implies (list a '?x) (list b '?x))) 'UContext)]
        (is (= h h2) "one rule, however its direction is spelled")
        (testing "both predicate indexes are complete — a rule is findable either way"
          (is (contains? (p/rules-by-antecedent (:index kb) a) h))
          (is (contains? (p/rules-by-consequent (:index kb) b) h)))
        (testing "and the direction is the least restrictive of the two, not the first"
          ;; forward joined with backward is both: the two assertions are two claims
          ;; about one rule, and a rule that may run each way may run both.  Resolving
          ;; from content is what makes the answer the same in either arrival order.
          (is (= :both (:direction (v/sentex kb h))))
          (is (= :both (:direction (v/sentex kb (v/assert kb (list 'set/backwardRule (list 'implies (list a '?x) (list b '?x))) 'UContext))))
              "and a third assertion changes nothing — the join is idempotent")))))
  (let [bird (tu/tmp-type) animal (tu/tmp-type) penguin (tu/tmp-type)
        flies (tu/tmp-pred) pengu (tu/tmp-ind)]
    (v/assert kb (list 'genl bird animal) 'UContext)
    (v/assert kb (list 'genl penguin bird) 'UContext)
    (testing "re-asserting resolves defeasibility to strict — stated once outright, it holds"
      (let [h (v/assert kb (list 'set/defaultRule (list 'implies (list bird '?x) (list flies '?x))) 'UContext)]
        (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) 'UContext)   ; bare: strict wins
        (is (nil? (:defeasible (v/sentex kb h)))
            "a rule somebody also stated without set/defaultRule is not a default")
        (v/assert kb (list 'implies (list penguin '?x) (list 'not (list flies '?x))) 'UContext)
        (v/assert kb (list penguin pengu) 'UContext {:strength :monotonic})
        ;; the same answer in either arrival order, which is the point: a conclusion
        ;; capped by its own premise's strength, and the exception rule taking it.
        (is (empty? (v/sentexes-matching kb (list flies pengu) 'UContext)))
        (is (seq   (v/sentexes-matching kb (list 'not (list flies pengu)) 'UContext)))
        (is (empty? (v/conflicts kb)))))))

(tu/deftest-kb slot-resolution-reaches-conclusions-already-derived
  ;; The two spellings of one rule may arrive with the facts *between* them, so the
  ;; rule fires before the slots resolve.  The record slot resolves by content either
  ;; way; what this pins is that the justifications already fired through the rule
  ;; move with it (`jtms/restrength-informant`): a firing bakes the rule's
  ;; contribution in as the justification's `:strength`, and a defeasible→strict
  ;; resolution that left it there would keep exactly the arrival order the slot join
  ;; removes — a conclusion at `:default` in one order losing to a monotonic rival it
  ;; ties with in the other.
  (let [run (fn [spell-first spell-second]
              (let [bird (tu/tmp-type) flies (tu/tmp-pred) tweety (tu/tmp-ind)
                    rule (list 'implies (list bird '?x) (list flies '?x))]
                (v/assert kb (list 'genl bird 'thing) 'UContext)
                (v/assert kb (spell-first rule) 'UContext)
                (v/assert kb (list bird tweety) 'UContext {:strength :monotonic})
                (v/assert kb (spell-second rule) 'UContext)
                (v/assert kb (list 'not (list flies tweety)) 'UContext
                          {:strength :monotonic})
                (let [fid (some-> (first (v/sentexes-matching kb (list flies tweety)
                                                              'UContext))
                                  :id)]
                  {:conclusion-class (when fid (v/defeat-class kb fid))
                   :just-strengths   (when fid
                                       (set (map :strength
                                                 (v/supporting-justifications kb fid))))
                   :standing?        [(some? fid)
                                      (boolean
                                       (seq (v/sentexes-matching
                                             kb (list 'not (list flies tweety))
                                             'UContext)))]})))
        defaulted #(list 'set/defaultRule %)
        a (run defaulted identity)      ; defeasible, fact, then strict
        b (run identity defaulted)]     ; strict, fact, then defeasible
    (is (= :monotonic (:conclusion-class a))
        "the conclusion reads the resolved slot, not the fire-time copy")
    (is (= #{:monotonic} (:just-strengths a))
        "the stored justification's strength moved with the record")
    (is (= a b) "the same knowledge in either order is one belief state")))

;; ---- strength is a first-class field on sentexes and justifications ---------

(tu/deftest-kb strength-is-carried-by-sentexes-and-justifications
  (let [bird (tu/tmp-type) animal (tu/tmp-type) dog (tu/tmp-type)
        fido (tu/tmp-ind) tweety (tu/tmp-ind) flies (tu/tmp-pred)]
    (v/assert kb (list 'genl bird animal) 'UContext)
    (v/assert kb (list dog fido) 'UContext {:strength :monotonic})
    (v/assert kb (list bird tweety) 'UContext)                       ; default strength
    (v/assert kb (list 'set/defaultRule (list 'implies (list bird '?x) (list flies '?x))) 'UContext)
    (testing "a premise sentex carries its assumption strength"
      (is (= :monotonic (:strength (v/sentex kb (:id (first (v/sentexes-matching kb (list dog fido) 'UContext)))))))
      (is (= :default   (:strength (v/sentex kb (:id (first (v/sentexes-matching kb (list bird tweety) 'UContext))))))))
    (testing "and its effective defeat-class after settling"
      (is (= :monotonic (v/defeat-class kb (:id (first (v/sentexes-matching kb (list dog fido) 'UContext)))))))
    (testing "a justification carries its strength — a default rule confers :default"
      (let [flies-id (:id (first (v/sentexes-matching kb (list flies tweety) 'UContext)))
            d        (first (v/supporting-justifications kb flies-id))]
        (is (= :default (:strength d)))))))

;; ---- canonical variables, literal order, symmetry, comparisons ----------

(tu/deftest-kb canonical-variables-are-positional-and-reversible
  (testing "every rule variable is renamed ?var0, ?var1, … by first occurrence"
    (let [s (sx/sentex '(implies (and (p ?who ?whom)) (q ?whom ?who)) 'AContext)]
      (is (= '[(p ?var0 ?var1)] (:antecedent s)))
      (is (= '(q ?var1 ?var0) (:consequent s)))))
  (testing "the varmap restores the author's names"
    (let [s (sx/sentex '(implies (and (p ?who ?whom)) (q ?whom ?who)) 'AContext)]
      (is (= '{?var0 ?who ?var1 ?whom} (:varmap s)))
      (is (= '(implies (p ?who ?whom) (q ?whom ?who))
             (sx/originalize (:sentence s) (:varmap s))))))
  (testing "a fact carries no varmap — canonical variables are a rule concern"
    (is (nil? (:varmap (sx/sentex '(dog Muffet) 'AContext))))))

(tu/deftest-kb literal-order-is-structural-not-lexical
  (testing "a smaller-arity literal sorts first, even when its name is lexically later"
    (let [s (sx/sentex '(implies (and (aaa ?x ?y ?z) (zzz ?x)) (out ?x)) 'AContext)]
      (is (= 'zzz (ffirst (:antecedent s))))))
  (testing "a computed literal is held back until its variables are bound"
    ;; written first, but (evaluate ?z (+ ?x ?y)) can only run once ?x/?y are bound
    (let [s (sx/sentex '(implies (and (evaluate ?z (+ ?x ?y)) (foo ?x ?y)) (bar ?z)) 'AContext)]
      (is (= 'foo      (ffirst (:antecedent s))))
      (is (= 'evaluate (first (second (:antecedent s))))))))

(tu/deftest-kb rules-dedup-up-to-variable-names-and-literal-order
  (let [p (tu/tmp-pred) q (tu/tmp-pred) r (tu/tmp-pred)]
    (let [h1 (v/assert-rule kb [(list p '?x '?y) (list q '?y '?z)] (list r '?x '?z) 'UContext)
          n1 (count (p/sentex-ids (:records kb)))
          ;; the same rule: variables renamed AND the antecedents written in the other order
          h2 (v/assert-rule kb [(list q '?b '?c) (list p '?a '?b)] (list r '?a '?c) 'UContext)]
      (testing "the reordered, renamed rule is the same sentex"
        (is (= h1 h2))
        (is (= n1 (count (p/sentex-ids (:records kb))))))
      (testing "a genuinely different join is still a different sentex"
        (is (not= h1 (v/assert-rule kb [(list p '?a '?b) (list q '?c '?b)]
                                    (list r '?a '?c) 'UContext)))))))

(tu/deftest-kb a-same-predicate-self-join-dedups-across-antecedent-order
  ;; the hard tie case: both antecedents have the SAME predicate, so nothing but the
  ;; variable-sharing structure distinguishes them — the order they were written in
  ;; must not leak into the canonical form.
  (let [par (tu/tmp-pred) grand (tu/tmp-pred)]
    (let [h1 (v/assert-rule kb [(list par '?x '?y) (list par '?y '?z)]
                            (list grand '?x '?z) 'UContext)
          n1 (count (p/sentex-ids (:records kb)))
          h2 (v/assert-rule kb [(list par '?b '?c) (list par '?a '?b)]
                            (list grand '?a '?c) 'UContext)]
      (testing "written in the other order, it is the same sentex"
        (is (= h1 h2))
        (is (= n1 (count (p/sentex-ids (:records kb))))))
      (testing "but the reversed join (grand ?z ?x) is genuinely different"
        (is (not= h1 (v/assert-rule kb [(list par '?x '?y) (list par '?y '?z)]
                                    (list grand '?z '?x) 'UContext)))))))

(tu/deftest-kb a-framed-consequent-holds-only-the-recursive-literal
  ;; the recursive-literal hold-back keys on the predicate a literal is *about*, not on
  ;; its outermost functor: under a `not`- or `ist`-headed consequent an antecedent's
  ;; own frame is not "the recursive literal", so it sorts like any generator — and the
  ;; genuinely recursive antecedent is held back either way.
  (let [p (tu/tmp-pred) q (tu/tmp-pred) r (tu/tmp-pred) ctx (tu/tmp-ctx)]
    (testing "a negated-head rule dedups across antecedent order"
      (let [h1 (v/assert-rule kb [(list 'not (list p '?x)) (list 'not (list q '?x))]
                              (list 'not (list r '?x)) 'UContext)
            n1 (count (p/sentex-ids (:records kb)))
            h2 (v/assert-rule kb [(list 'not (list q '?x)) (list 'not (list p '?x))]
                              (list 'not (list r '?x)) 'UContext)]
        (is (= h1 h2))
        (is (= n1 (count (p/sentex-ids (:records kb)))))))
    (testing "an ist-headed rule dedups across antecedent order"
      (let [h1 (v/assert-rule kb [(list p '?x) (list q '?x)] (list 'ist ctx (list r '?x))
                              'UContext)
            h2 (v/assert-rule kb [(list q '?x) (list p '?x)] (list 'ist ctx (list r '?x))
                              'UContext)]
        (is (= h1 h2))))
    (testing "a recursive rule with a negated head keeps its recursive literal held"
      (let [b (tu/tmp-pred) a (tu/tmp-pred)
            h (v/assert-rule kb [(list b '?x '?y) (list a '?y '?z)]
                             (list 'not (list a '?x '?z)) 'UContext)]
        ;; held-back literals follow the generators, so the author's right-recursion
        ;; survives canonicalization instead of being hoisted to position 0
        (is (= [b a] (mapv first (:antecedent (v/sentex kb h)))))))))

(tu/deftest-kb canonicalization-is-idempotent
  (testing "canonicalizing an already-canonical rule is a no-op"
    (let [a (sx/sentex '(implies (and (p ?x ?y) (q ?y ?z)) (r ?x ?z)) 'AContext)
          b (sx/sentex (:sentence a) 'AContext)]
      (is (= (:sentence a) (:sentence b)))
      (is (= (:antecedent a) (:antecedent b)))
      (is (= (:consequent a) (:consequent b)))))
  (testing "and the trie path is stable across the round trip"
    (let [a (sx/sentex '(implies (and (foo ?a ?b) (bar ?b)) (baz ?a)) 'AContext)]
      (is (= (sx/path a) (sx/path (sx/sentex (:sentence a) 'AContext)))))))

(tu/deftest-kb a-symmetric-fact-answers-from-either-direction
  ;; only fully-ground literals are stored sorted; a *pattern* keeps its order and
  ;; lookup probes both ways, so the stored fact is reachable either way.
  (let [sib (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind)]
    (v/assert kb (list 'symmetric sib) 'UContext)
    (v/assert kb (list sib a b) 'UContext)
    (testing "a partially-ground query finds it from both sides"
      (is (seq (v/sentexes-matching kb (list sib '?x b) 'UContext)))
      (is (seq (v/sentexes-matching kb (list sib b '?x) 'UContext)))
      (is (seq (v/sentexes-matching kb (list sib '?x a) 'UContext)))
      (is (seq (v/sentexes-matching kb (list sib a '?x) 'UContext))))
    (testing "and so does the prover engine"
      (is (v/ask? kb (list sib '?x b) 'UContext))
      (is (v/ask? kb (list sib b '?x) 'UContext)))
    (testing "a fully-open pattern returns the one stored sentex, not a duplicate"
      (is (= 1 (count (v/sentexes-matching kb (list sib '?x '?y) 'UContext)))))
    (testing "an unrelated individual still does not match"
      (is (empty? (v/sentexes-matching kb (list sib '?x (tu/tmp-ind)) 'UContext))))))

(tu/deftest-kb a-fact-asserted-before-its-symmetric-declaration-stays-reachable
  ;; canonical sorting only applies once (symmetric P) is known, so a fact stored
  ;; earlier may sit in the "wrong" order — lookup probes both ways so it never
  ;; becomes unreachable, and re-asserting its mirror resolves rather than duplicates.
  (let [sib (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind)]
    (let [h (v/assert kb (list sib a b) 'UContext)]        ; stored before the metadata
      (v/assert kb (list 'symmetric sib) 'UContext)
      (testing "it is still found from either direction"
        (is (seq (v/sentexes-matching kb (list sib a b) 'UContext)))
        (is (seq (v/sentexes-matching kb (list sib b a) 'UContext))))
      (testing "and asserting the mirror image resolves to it rather than duplicating"
        (is (= h (v/assert kb (list sib b a) 'UContext)))))))

(tu/deftest-kb an-anonymous-wildcard-consequent-is-rejected
  ;; `_` is a fresh variable at each occurrence, so it can never carry a binding from
  ;; an antecedent to the consequent — allowing it would store a non-ground junk fact.
  (let [p (tu/tmp-pred) q (tu/tmp-pred)]
    (is (= :not-range-restricted
           (try (v/assert-rule kb [(list p '_)] (list q '_) 'UContext) nil
                (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
    (testing "and nothing was stored"
      (is (empty? (v/find-sentexes kb q))))))

(tu/deftest-kb a-rule-antecedent-over-a-symmetric-predicate-still-joins
  ;; a partially-substituted antecedent is a pattern, so it must not be reordered —
  ;; otherwise forward chaining would under-derive over symmetric relations.
  (let [sib (tu/tmp-pred) knows (tu/tmp-pred)
        a (tu/tmp-ind) b (tu/tmp-ind)]
    (v/assert kb (list 'symmetric sib) 'UContext)
    (v/assert kb (list sib a b) 'UContext)
    (v/assert-rule kb [(list sib '?p '?q)] (list knows '?p '?q) 'UContext)
    (testing "the rule fires on the stored symmetric fact"
      (is (seq (v/sentexes-matching kb (list knows '?x '?y) 'UContext))))))

(tu/deftest-kb symmetric-arguments-canonicalize-to-one-sentex
  (let [sib (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind)]
    (v/assert kb (list 'symmetric sib) 'UContext)
    (let [h1 (v/assert kb (list sib a b) 'UContext)
          n1 (count (p/sentex-ids (:records kb)))
          h2 (v/assert kb (list sib b a) 'UContext)]     ; the mirror image
      (testing "the mirrored assertion resolves to the same sentex, storing nothing new"
        (is (= h1 h2))
        (is (= n1 (count (p/sentex-ids (:records kb))))))
      (testing "and it is found from either direction"
        (is (seq (v/sentexes-matching kb (list sib a b) 'UContext)))
        (is (seq (v/sentexes-matching kb (list sib b a) 'UContext)))))
    (testing "an asymmetric predicate keeps its argument order"
      (let [ord (tu/tmp-pred)]
        (is (not= (v/assert kb (list ord a b) 'UContext)
                  (v/assert kb (list ord b a) 'UContext)))))))

(tu/deftest-kb comparison-siblings-fold-onto-less-than
  (testing "greaterThan is stored as lessThan with reversed arguments"
    (is (= '(lessThan 3 5) (:sentence (sx/sentex '(greaterThan 5 3) 'AContext))))
    (is (= '(lessThan ?var0 ?var1)
           (:consequent (sx/sentex '(implies (p ?a ?b) (greaterThan ?b ?a)) 'AContext)))))
  (testing "both directions resolve to one sentex in the store"
    (let [h1 (v/assert kb '(greaterThan 5 3) 'UContext)
          h2 (v/assert kb '(lessThan 3 5) 'UContext)]
      (is (= h1 h2)))))

(tu/deftest-kb comparison-chains-collapse-into-one-variable-arity-literal
  (testing "chained comparisons in an antecedent merge into a single literal"
    (let [s   (sx/sentex '(implies (and (foo ?a ?b ?c) (lessThan ?a ?b) (lessThan ?b ?c))
                                   (bar ?a ?c)) 'AContext)
          lts (filterv #(= 'lessThan (first %)) (:antecedent s))]
      (is (= 1 (count lts)) "one chain literal, not two")
      (is (= 4 (count (first lts))) "variable arity: (lessThan a b c)")))
  (testing "a folded greaterThan joins the same chain"
    (let [s   (sx/sentex '(implies (and (foo ?a ?b ?c) (greaterThan ?b ?a) (lessThan ?b ?c))
                                   (bar ?a ?c)) 'AContext)
          lts (filterv #(= 'lessThan (first %)) (:antecedent s))]
      (is (= 1 (count lts)))
      (is (= 4 (count (first lts))))))
  (testing "a branch is not merged — (a<b) and (a<c) stay separate"
    (let [s   (sx/sentex '(implies (and (foo ?a ?b ?c) (lessThan ?a ?b) (lessThan ?a ?c))
                                   (bar ?a ?c)) 'AContext)
          lts (filterv #(= 'lessThan (first %)) (:antecedent s))]
      (is (= 2 (count lts))))))

(tu/deftest-kb different-is-deferred-but-never-merged
  ;; `different` shares exactly one property with the comparisons above — it consumes
  ;; bindings rather than producing them, so it is held back — and none of the others.
  (testing "a `different` antecedent is held back after the literals that bind it"
    (let [s     (sx/sentex '(implies (and (different ?x ?y) (parentOf ?p ?x) (parentOf ?p ?y))
                                     (siblingOf ?x ?y))
                           'AContext)
          antes (:antecedent s)]
      (is (= 3 (count antes)))
      (is (= 'different (first (last antes)))
          "written first, but it can only run once ?x/?y are bound")
      (is (every? #(= 'parentOf (first %)) (butlast antes)))
      (testing "and every variable it tests is already bound by an earlier literal"
        (let [bound (set (mapcat rest (butlast antes)))]
          (is (every? bound (rest (last antes))))))))
  (testing "two `different` literals are not merged into one variable-arity literal"
    ;; the lessThan analogy fails: `different` is not transitive, so folding
    ;; (different a b) + (different b c) into (different a b c) would manufacture the
    ;; pairwise claim a≠c that nobody asserted.  See docs/equality.md.
    (let [s     (sx/sentex '(implies (and (foo ?a ?b ?c) (different ?a ?b) (different ?b ?c))
                                     (bar ?a ?c)) 'AContext)
          diffs (filterv #(= 'different (first %)) (:antecedent s))]
      (is (= 2 (count diffs)) "two literals, not one chain")
      (is (every? #(= 3 (count %)) diffs) "each still binary — no (different a b c)")))
  (testing "nor are its arguments sorted, and no sibling folds onto it"
    (let [s (sx/sentex '(different Zeta Alpha) 'AContext)]
      (is (= '(different Zeta Alpha) (:sentence s))))))

(tu/deftest-kb the-prover-answers-variable-arity-comparisons
  (do
    (testing "a ground chain is checked end to end"
      (is (v/ask? kb '(lessThan 1 2 3)))
      (is (not (v/ask? kb '(lessThan 1 3 2))))
      (is (v/ask? kb '(lessThan 1 2 3 4 5))))
    (testing "greaterThan is still answerable as a goal"
      (is (v/ask? kb '(greaterThan 3 2 1)))
      (is (not (v/ask? kb '(greaterThan 3 1 2)))))
    (testing "the binary case is unchanged"
      (is (v/ask? kb '(lessThan 1 2)))
      (is (not (v/ask? kb '(lessThan 2 1)))))))

(tu/deftest-kb a-collapsed-chain-still-drives-a-rule
  ;; two chained comparisons collapse into one 4-ary literal — and the rule must
  ;; still prove, so the merged chain really is discharged by the prover.
  (let [born (tu/tmp-pred) between (tu/tmp-pred)
        a (tu/tmp-ind) b (tu/tmp-ind) c (tu/tmp-ind)]
    (v/assert kb (list born a 1970) 'UContext)
    (v/assert kb (list born b 1980) 'UContext)
    (v/assert kb (list born c 1990) 'UContext)
    (let [h (v/assert-rule kb [(list born '?x '?bx) (list born '?y '?by) (list born '?z '?bz)
                               (list 'lessThan '?bx '?by) (list 'lessThan '?by '?bz)]
                           (list between '?x '?y '?z) 'UContext {:direction :backward})
          lts (filterv #(= 'lessThan (first %)) (:antecedent (v/sentex kb h)))]
      (testing "the two comparisons are stored as one chain literal"
        (is (= 1 (count lts)))
        (is (= 4 (count (first lts)))))
      (testing "and the collapsed chain still discharges through the prover"
        (is (v/query? kb (list between a b c) 'UContext {:max-depth 2}))
        (is (not (v/query? kb (list between c b a) 'UContext {:max-depth 2})))
        (is (not (v/query? kb (list between b a c) 'UContext {:max-depth 2})))))))

;; ---- exceptWhen: the exception is a separate meta-sentex ----------------
;; `(exceptWhen <query> <rule>)` is split at the assert layer: the rule stores
;; normally and the exception becomes a belief-following meta-sentex
;; `(exceptWhen <query> (sentexHandle H))` naming the rule H by handle, its query
;; aligned to the rule's canonical variables.  These tests pin that representation —
;; not the blocking semantics, which `except_test` specifies.

(tu/deftest-kb the-constructor-drops-a-surface-exceptWhen-wrapper-onto-the-bare-rule
  ;; The pure constructor cannot represent an exception (it needs a rule handle), so a
  ;; surface `(exceptWhen …)` wrapper is stripped and the bare rule stored — the
  ;; sibling wrappers still become their own fields.
  (let [s (sx/sentex '(exceptWhen (penguin ?b)
                                  (set/defaultRule (implies (bird ?b) (flies ?b)))) 'AContext)]
    (testing "no wrapper survives onto the stored sentence"
      (is (= '(implies (bird ?var0) (flies ?var0)) (:sentence s)))
      (is (not (some '#{exceptWhen set/defaultRule}
                     (tree-seq sequential? seq (:sentence s))))))
    (testing "the sibling wrappers still canonicalize into their own fields"
      (is (true? (:defeasible s)))
      (is (= :both (:direction s))))
    (testing "the record carries no exception — that lives on a meta-sentex"
      (is (nil? (:except s))))))

(tu/deftest-kb the-stored-meta-sentex-names-the-rule-and-aligns-the-query
  ;; asserting the wrapper stores the rule and a `(exceptWhen Q (sentexHandle H))`
  ;; meta-sentex whose query is in the rule's canonical variables, so a firing's
  ;; bindings substitute straight in.
  (let [bird (tu/tmp-type) penguin (tu/tmp-type) flies (tu/tmp-pred)
        rule-form (vr/rule-sentence [(list bird '?b)] (list flies '?b))
        mh   (v/assert kb (list 'exceptWhen (list penguin '?b)
                                (list 'set/defaultRule
                                      (list 'implies (list bird '?b) (list flies '?b))))
                       'UContext)
        rh   (v/handle-of kb rule-form 'UContext)]
    (testing "the meta-sentex names the rule by handle and holds the aligned query"
      (is (= (list 'exceptWhen (list penguin '?var0) (sx/sentex-handle rh))
             (:sentence (v/sentex kb mh)))))
    (testing "the rule reads its exception back through provers/rule-exceptions"
      (is (= [[(list penguin '?var0)]] (provers/rule-exceptions kb rh))))))

(tu/deftest-kb an-exceptions-variables-are-aligned-to-the-rules
  ;; the exception is substituted with the rule's bindings, so a shared variable must
  ;; carry the rule's *canonical* number — align them wrong and the substitution binds
  ;; nothing.
  (let [p (tu/tmp-type) q (tu/tmp-type) rel (tu/tmp-pred) out (tu/tmp-pred)
        rule-form (vr/rule-sentence [(list p '?x) (list q '?y)] (list out '?x '?y))
        _  (v/assert kb (list 'exceptWhen (list rel '?y '?x)
                              (list 'implies
                                    (list 'and (list p '?x) (list q '?y))
                                    (list out '?x '?y)))
                     'UContext)
        rh (v/handle-of kb rule-form 'UContext)
        s  (v/sentex kb rh)]
    (testing "the rule's own canonicalization is unchanged by the exception"
      (is (= [(list p '?var0) (list q '?var1)] (:antecedent s)))
      (is (= (list out '?var0 '?var1) (:consequent s)))
      (is (= {'?var0 '?x '?var1 '?y} (:varmap s))))
    (testing "and the exception query is aligned to those canonical variables"
      (is (= [[(list rel '?var1 '?var0)]] (provers/rule-exceptions kb rh))))))

(tu/deftest-kb a-bare-and-a-vector-exception-normalize-to-one-shape
  (let [bird (tu/tmp-type) penguin (tu/tmp-type) flies (tu/tmp-pred)
        rule-form (vr/rule-sentence [(list bird '?b)] (list flies '?b))
        bare (v/assert kb (list 'exceptWhen (list penguin '?b)
                                (list 'implies (list bird '?b) (list flies '?b))) 'UContext)
        vec1 (v/assert kb (list 'exceptWhen [(list penguin '?b)]
                                (list 'implies (list bird '?b) (list flies '?b))) 'UContext)
        rh   (v/handle-of kb rule-form 'UContext)]
    (testing "a single literal may be written bare or as a one-vector; one meta-sentex"
      (is (= bare vec1))
      (is (= [[(list penguin '?var0)]] (provers/rule-exceptions kb rh))))))

(tu/deftest-kb a-vector-exceptions-conjuncts-are-order-insensitive
  ;; conjuncts within one exceptWhen are independent ground checks, so their order (and
  ;; a duplicate) is not their identity — the meta-sentex dedups.
  (let [bird (tu/tmp-type) penguin (tu/tmp-type) young (tu/tmp-type) flies (tu/tmp-pred)
        rule-form (vr/rule-sentence [(list bird '?b)] (list flies '?b))
        a (v/assert kb (list 'exceptWhen [(list young '?b) (list penguin '?b)]
                             (list 'implies (list bird '?b) (list flies '?b))) 'UContext)
        b (v/assert kb (list 'exceptWhen [(list penguin '?z) (list young '?z) (list penguin '?z)]
                             (list 'implies (list bird '?z) (list flies '?z))) 'UContext)
        rh (v/handle-of kb rule-form 'UContext)]
    (is (= a b))
    (is (= 1 (count (provers/rule-exceptions kb rh))))
    (is (= #{(list young '?var0) (list penguin '?var0)}
           (set (first (provers/rule-exceptions kb rh)))))))

(tu/deftest-kb polycanonicalization-carries-the-exception-onto-each-conjunct
  ;; splitting a conjunctive consequent must not drop the exception: each rule the
  ;; split produces gets its own exception meta-sentex.
  (let [bird (tu/tmp-type) penguin (tu/tmp-type) flies (tu/tmp-pred) light (tu/tmp-pred)
        _ (v/assert kb (list 'exceptWhen (list penguin '?b)
                             (list 'set/forwardRule
                                   (list 'implies (list bird '?b)
                                         (list 'and (list flies '?b) (list light '?b)))))
                    'UContext)
        rh1 (v/handle-of kb (vr/rule-sentence [(list bird '?b)] (list flies '?b)) 'UContext)
        rh2 (v/handle-of kb (vr/rule-sentence [(list bird '?b)] (list light '?b)) 'UContext)]
    (testing "each conjunct is its own rule with its own exception"
      (is (some? rh1))
      (is (some? rh2))
      (is (not= rh1 rh2))
      (is (= [[(list penguin '?var0)]] (provers/rule-exceptions kb rh1)))
      (is (= [[(list penguin '?var0)]] (provers/rule-exceptions kb rh2))))))

(tu/deftest-kb an-exception-amends-the-rule-in-place-sharing-one-handle
  (let [bird (tu/tmp-type) penguin (tu/tmp-type) young (tu/tmp-type) flies (tu/tmp-pred)
        rule-form (vr/rule-sentence [(list bird '?b)] (list flies '?b))
        plain (v/assert kb (list 'set/defaultRule
                                 (list 'implies (list bird '?b) (list flies '?b)))
                        'UContext)
        exc   (v/assert kb (list 'exceptWhen (list penguin '?b)
                                 (list 'set/defaultRule
                                       (list 'implies (list bird '?b) (list flies '?b))))
                        'UContext)]
    (testing "the exception is a separate meta-sentex, but names the one rule"
      (is (not= plain exc))
      (is (= plain (v/handle-of kb rule-form 'UContext))))
    (testing "an α-equivalent exception dedups to the same meta-sentex"
      (let [n2   (count (p/sentex-ids (:records kb)))
            same (v/assert kb (list 'exceptWhen [(list penguin '?w)]
                                    (list 'set/defaultRule
                                          (list 'implies (list bird '?w) (list flies '?w))))
                           'UContext)]
        (is (= exc same))
        (is (= n2 (count (p/sentex-ids (:records kb)))))))
    (testing "a different exception is a second meta-sentex on the same rule"
      (let [exc2 (v/assert kb (list 'exceptWhen (list young '?b)
                                    (list 'set/defaultRule
                                          (list 'implies (list bird '?b) (list flies '?b))))
                           'UContext)]
        (is (not= exc exc2))
        (is (= plain (v/handle-of kb rule-form 'UContext)))
        (is (= 2 (count (provers/rule-exceptions kb plain))))))))

(tu/deftest-kb an-exception-variable-no-antecedent-binds-is-rejected
  ;; closure is what makes the exception a ground existence check instead of a
  ;; search, and it is why an *existential* exception ("unless it has a sick child")
  ;; is not expressible.
  (let [bird (tu/tmp-type) sick (tu/tmp-pred) flies (tu/tmp-pred)
        rule (list 'exceptWhen (list sick '?child)
                   (list 'set/defaultRule (list 'implies (list bird '?b) (list flies '?b))))]
    (testing "assert refuses an exception whose variable no antecedent binds"
      (let [e (try (v/assert kb rule 'UContext)
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (= :exception-not-closed (:type (ex-data e))))
        (is (= '[?child] (:unbound (ex-data e))))))
    (testing "and stores nothing about the conclusion"
      (is (empty? (v/find-sentexes kb flies))))
    (testing "an antecedent that binds the witness is the workaround, and is accepted"
      (is (some? (v/assert kb (list 'exceptWhen (list sick '?child)
                                    (list 'set/defaultRule
                                          (list 'implies
                                                (list 'and (list bird '?b) (list bird '?child))
                                                (list flies '?b))))
                           'UContext))))))

;; ---- regression: the whole starter still reasons ------------------------

(tu/deftest-kb starter-reasons-under-canonicalized-sentexes
  (do
    (starter/load-into kb)
    (world/load-cast kb)
    (testing "facts, negation, rules, and derivations all survive"
      (is (seq (v/sentexes-matching kb '(grandparentOf Tom Ann) 'NaturalWorldContext)))
      (is (empty? (v/sentexes-matching kb '(flies Tweety) 'NaturalWorldContext)))
      (is (seq (v/sentexes-matching kb '(not (flies Tweety)) 'NaturalWorldContext)))
      (is (v/ask? kb '(ancestorOf Tom Ann)))
      (is (empty? (v/conflicts kb))))))

;; ---- the symbol pool is bounded, and the bound changes no answer ---------

(deftest the-symbol-pool-is-bounded-and-a-flush-changes-no-answer
  ;; Interning is a pure space optimization, and the pool is not vocabulary-sized: NAT
  ;; reification, head-existential skolemization and abduction each mint a fresh symbol
  ;; per fact, so an unbounded pool grows with the KB.  With room for a handful, minting
  ;; past it flushes the pool wholesale — and because interning changes identity and never
  ;; equality, a canonicalization either side of a flush still answers `=`, hashes the
  ;; same, and keys a map the same.
  (binding [sx/*symbol-pool-limit* 8]
    (let [^java.util.concurrent.ConcurrentHashMap pool @#'sx/symbol-pool
          before (sx/canon '(parentOf Tom Bob))]
      (dotimes [i 200]
        (sx/canon (list (symbol (str "minted" i)) (symbol (str "Witness" i))))
        (is (<= (.size pool) 8) (str "the pool never exceeds its bound (mint " i ")")))
      (let [after (sx/canon '(parentOf Tom Bob))]
        (testing "the canonical form survives every flush in between"
          (is (= before after))
          (is (= (hash before) (hash after)))
          (is (= {before :v} {after :v}) "so it still keys a map"))
        (testing "and a sentex built either side is still the same sentex"
          (is (= (sx/sentex before 'AContext) (sx/sentex after 'AContext)))))
      (testing "sharing resumes for whatever is named after a flush"
        (is (identical? (sx/intern-sym 'pooledAgain) (sx/intern-sym 'pooledAgain)))))))
