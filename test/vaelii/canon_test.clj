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
  genlCx together)."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.starter :as starter]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- flatten-key [k]
  (filter (complement sequential?) (tree-seq sequential? seq k)))

;; ---- the struct stores one head `not` / antecedent / consequent ---------

(tu/deftest-kb connectives-canonicalize-into-the-record
  (testing "a negation keeps one `not` at the head over the positive body"
    (let [s (sx/sentex '(not (flies Tweety)) 'CxA)]
      (is (sx/negative? s))
      (is (= '(flies Tweety) (sx/body s)))
      (is (nil? (:antecedent s)))))
  (testing "double negation is eliminated"
    (let [s (sx/sentex '(not (not (flies Tweety))) 'CxA)]
      (is (not (sx/negative? s)))
      (is (= '(flies Tweety) (:sentence s)))))
  (testing "a rule decomposes into antecedent (a vector) and consequent, canonically named"
    (let [s (sx/sentex '(implies (and (parentOf ?x ?y) (parentOf ?y ?z)) (grandparentOf ?x ?z)) 'CxA)]
      (is (= '[(parentOf ?var0 ?var1) (parentOf ?var1 ?var2)] (:antecedent s)))
      (is (= '(grandparentOf ?var0 ?var2) (:consequent s)))
      (is (not (sx/negative? s)))
      (testing "and the varmap gets back to the author's names"
        (is (= '{?var0 ?x ?var1 ?y ?var2 ?z} (:varmap s)))
        (is (= '(implies (and (parentOf ?x ?y) (parentOf ?y ?z)) (grandparentOf ?x ?z))
               (sx/originalize (sx/sentence-of s) (:varmap s)))))
      (testing "and the record holds no sentence of its own"
        (is (not (contains? s :sentence))))))
  (testing "the trie key contains none of not / implies / and"
    (let [k (sx/path (sx/sentex '(implies (and (a ?x)) (b ?x)) 'CxA))]
      (is (not (some '#{implies and not} (flatten-key k)))))))

;; ---- numbers, strings, connectives are not term-indexed -----------------

(tu/deftest-kb term-index-skips-numbers-strings-and-connectives
  (let [person (tu/tmp-type) animal (tu/tmp-type)
        tom (tu/tmp-ind) bone (tu/tmp-ind)
        birthYearOf (tu/tmp-pred) mortal (tu/tmp-pred)
        immortal (tu/tmp-pred) likes (tu/tmp-pred)]
    (v/assert kb (list 'genl person animal) 'CxU)
    (v/assert kb (list 'arg birthYearOf 1 person) 'CxU)
    (v/assert kb (list person tom) 'CxU)
    (v/assert kb (list birthYearOf tom 1970) 'CxU)
    (v/assert kb (list 'comment tom "a fine fellow") 'CxU)
    (v/assert-rule kb [(list person '?p)] (list mortal '?p) 'CxU {:direction :forward})
    (v/assert-rule kb [(list person '?p)] (list 'not (list immortal '?p)) 'CxU {:direction :forward})   ; a nested `not` inside a rule
    (v/assert-rule kb [(list person '?p)] (list likes '?p bone) 'CxU {:direction :forward})             ; a constant argument
    (v/assert kb (list 'not (list mortal tom)) 'CxU)
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
    (v/assert kb (list 'genl dog animal) 'CxU)
    (let [h1 (v/assert-rule kb [(list animal '?x)] (list breathes '?x) 'CxU {:direction :forward})
          n1 (count (p/sentex-ids (:records kb)))
          h2 (v/assert-rule kb [(list animal '?y)] (list breathes '?y) 'CxU {:direction :forward})]   ; same rule, renamed
      (testing "the second assertion finds the existing handle, stores nothing new"
        (is (= h1 h2))
        (is (= n1 (count (p/sentex-ids (:records kb))))))
      (testing "a genuinely different rule is a different sentex"
        (is (not= h1 (v/assert-rule kb [(list animal '?x)] (list mortal '?x) 'CxU {:direction :forward}))))
      (testing "dedup is scoped to context — the same rule elsewhere is distinct"
        (is (not= h1 (v/assert-rule kb [(list animal '?z)] (list breathes '?z) 'CxOther {:direction :forward})))))))

;; ---- a conjunctive consequent polycanonicalizes -------------------------

(tu/deftest-kb conjunctive-consequent-splits-into-multiple-rules
  (let [a (tu/tmp-type) b (tu/tmp-type) c (tu/tmp-type) d (tu/tmp-type)
        x1 (tu/tmp-ind)]
    (doseq [t [a b c d]] (v/assert kb (list 'genl t 'thing) 'CxU))
    (v/assert kb (list a x1) 'CxU)
    (let [handles (v/assert-rule kb [(list a '?x)] (list 'and (list b '?x) (list c '?x) (list d '?x)) 'CxU {:direction :forward})]
      (testing "assert-rule returns one handle per conjunct"
        (is (vector? handles))
        (is (= 3 (count (distinct handles)))))
      (testing "each conjunct is derived independently"
        (is (seq (v/sentexes-matching kb (list b x1) 'CxU)))
        (is (seq (v/sentexes-matching kb (list c x1) 'CxU)))
        (is (seq (v/sentexes-matching kb (list d x1) 'CxU))))
      (testing "retracting one split rule leaves the others standing"
        (v/retract! kb (first handles))                  ; the (b ?x) rule
        (is (empty? (v/sentexes-matching kb (list b x1) 'CxU)))
        (is (seq (v/sentexes-matching kb (list c x1) 'CxU)))))))

(tu/deftest-kb polycanon-covers-directed-and-default-rules
  (let [a (tu/tmp-type) b (tu/tmp-type) c (tu/tmp-type)
        d (tu/tmp-type) e (tu/tmp-type) f (tu/tmp-type)
        x (tu/tmp-ind)]
    (doseq [t [a b c d e f]] (v/assert kb (list 'genl t 'thing) 'CxU))
    (v/assert kb (list a x) 'CxU)
    (testing "a backward directed conjunctive consequent splits; each conjunct is provable"
      (v/assert-rule kb [(list a '?x)] (list 'and (list b '?x) (list c '?x)) 'CxU {:direction :backward})
      (is (v/provable? kb (list b x) 'CxU))
      (is (v/provable? kb (list c x) 'CxU)))
    (testing "a default conjunctive consequent splits; each conjunct is derived"
      (v/assert kb (list 'set/defaultRule (list 'set/forwardRule (list 'implies (list a '?x) (list 'and (list d '?x) (list e '?x))))) 'CxU)
      (is (seq (v/sentexes-matching kb (list d x) 'CxU)))
      (is (seq (v/sentexes-matching kb (list e x) 'CxU))))
    (testing "a negated conjunction consequent does NOT split (De Morgan ⇒ a disjunction)"
      (is (not (vector? (v/assert-rule kb [(list a '?x)] (list 'not (list 'and (list f '?x) (list b '?x))) 'CxU {:direction :forward})))))))

;; ---- spec-type fact in a spec context triggers a general rule -----------

(tu/deftest-kb spec-fact-in-spec-context-triggers-a-general-rule
  (let [dog (tu/tmp-type) mammal (tu/tmp-type) animal (tu/tmp-type)
        muffet (tu/tmp-ind) rex (tu/tmp-ind)
        breathes (tu/tmp-pred) has_fur (tu/tmp-pred)]
    (v/assert kb (list 'genlCx 'CxSpec 'CxGen) 'CxGen)
    (v/assert kb (list 'genl mammal animal) 'CxGen)
    (v/assert kb (list 'genl dog mammal) 'CxGen)
    (v/assert-rule kb [(list animal '?x)] (list breathes '?x) 'CxGen {:direction :forward})   ; general type, general context
    (v/assert kb (list dog muffet) 'CxSpec)                               ; spec type, spec context
    (testing "genl (subtype) and genlCx (subcontext) combine to fire the rule"
      (is (seq (v/sentexes-matching kb (list breathes muffet) 'CxSpec))))
    (testing "and the conclusion is placed in the spec context"
      (is (= '(CxSpec) (v/contexts-of kb (list breathes muffet)))))
    (testing "it fires regardless of assertion order (rule after fact)"
      (v/assert kb (list dog rex) 'CxSpec)
      (v/assert-rule kb [(list mammal '?y)] (list has_fur '?y) 'CxGen {:direction :forward})
      (is (seq (v/sentexes-matching kb (list has_fur rex) 'CxSpec))))))

(tu/deftest-kb a-join-rule-fires-over-spec-facts-with-a-common-viewpoint
  ;; The requirement's join case: two antecedents, spec-type facts, genl + genlCx.
  (let [dog (tu/tmp-type) cat (tu/tmp-type) animal (tu/tmp-type)
        muffet (tu/tmp-ind) tom (tu/tmp-ind) whiskers (tu/tmp-ind)
        coexist (tu/tmp-pred)]
    (v/assert kb (list 'genlCx 'CxA 'CxTop) 'CxTop)
    (v/assert kb (list 'genlCx 'CxB 'CxTop) 'CxTop)        ; CxA, CxB are sibling subs of CxTop
    (v/assert kb (list 'genl dog animal) 'CxTop)
    (v/assert kb (list 'genl cat animal) 'CxTop)
    (v/assert-rule kb [(list animal '?x) (list animal '?y)] (list coexist '?x '?y) 'CxTop {:direction :forward})  ; join on animal
    (v/assert kb (list dog muffet) 'CxA)
    (v/assert kb (list cat tom) 'CxTop)
    (testing "a spec fact in a sub joins a fact in the shared super, placed in the sub"
      (is (seq (v/sentexes-matching kb (list coexist muffet tom) 'CxA))))
    (testing "two facts in sibling subs (no common viewpoint) derive nothing"
      (v/assert kb (list cat whiskers) 'CxB)
      (is (empty? (v/sentexes-matching kb (list coexist muffet whiskers) '?ctx)))
      (is (empty? (v/sentexes-matching kb (list coexist whiskers muffet) '?ctx))))))

;; ---- the fixes surfaced by review: soundness of assert ------------------

(tu/deftest-kb a-bare-implies-is-range-restriction-checked
  (let [bird (tu/tmp-type) animal (tu/tmp-type)
        flies (tu/tmp-pred) robin (tu/tmp-ind)]
    (v/assert kb (list 'genl bird animal) 'CxU)
    (testing "a bare (implies ..) with an unbound consequent variable is rejected"
      (is (= :not-range-restricted
             (try (v/assert kb (list 'implies (list bird '?x) (list flies '?y)) 'CxU {:direction :forward}) nil
                  (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))))
    (testing "and no junk (flies ?y) fact was stored to match against everything"
      (is (empty? (v/find-sentexes kb flies))))
    (testing "a range-restricted bare implies works and fires"
      (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) 'CxU {:direction :forward})
      (v/assert kb (list bird robin) 'CxU)
      (is (seq (v/sentexes-matching kb (list flies robin) 'CxU))))))

(tu/deftest-kb double-negation-respects-premise-constraints
  (let [dog (tu/tmp-type) cat (tu/tmp-type) animal (tu/tmp-type)
        felix (tu/tmp-ind) rex (tu/tmp-ind)]
    (v/assert kb (list 'genl dog animal) 'CxU)
    (v/assert kb (list 'genl cat animal) 'CxU)
    (v/assert kb (list 'disjoint dog cat) 'CxU)
    (v/assert kb (list cat felix) 'CxU)
    (testing "(not (not (dog Felix))) canonicalizes to (dog Felix) and hits the disjoint check"
      (is (thrown? clojure.lang.ExceptionInfo (v/assert kb (list 'not (list 'not (list dog felix))) 'CxU))))
    (testing "a genuine single negation is not arg/disjoint-checked"
      (is (some? (v/assert kb (list 'not (list dog rex)) 'CxU))))))

(tu/deftest-kb an-empty-conjunction-consequent-is-rejected
  (let [a (tu/tmp-type)]
    (v/assert kb (list 'genl a 'thing) 'CxU)
    (is (= :not-range-restricted
           (try (v/assert-rule kb [(list a '?x)] (list 'and) 'CxU {:direction :forward}) nil
                (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))))

(tu/deftest-kb a-positive-wildcard-query-does-not-match-negations
  (let [dog (tu/tmp-type) animal (tu/tmp-type)
        muffet (tu/tmp-ind) rex (tu/tmp-ind)]
    (v/assert kb (list 'genl dog animal) 'CxU)
    (v/assert kb (list dog muffet) 'CxU)
    (v/assert kb (list 'not (list dog rex)) 'CxU)
    (testing "(?p ?x) binds ?p only to real predicates, never to `not` via a negation"
      (let [preds (set (map #(get % '?p) (v/prove kb '(?p ?x) '?ctx)))]
        (is (contains? preds dog))
        (is (not (contains? preds 'not)))))))

(tu/deftest-kb rule-assertion-is-idempotent
  (let [a (tu/tmp-type) b (tu/tmp-type)]
    (v/assert kb (list 'genl a 'thing) 'CxU)
    (v/assert kb (list 'genl b 'thing) 'CxU)
    (testing "re-asserting a rule with a different direction resolves to one record"
      (let [h  (v/assert kb (list 'set/forwardRule (list 'implies (list a '?x) (list b '?x))) 'CxU)
            h2 (v/assert kb (list 'set/backwardRule (list 'implies (list a '?x) (list b '?x))) 'CxU)]
        (is (= h h2) "one rule, however its direction is spelled")
        (testing "both predicate indexes are complete — a rule is findable either way"
          (is (contains? (p/rules-by-antecedent (:index kb) a) h))
          (is (contains? (p/rules-by-consequent (:index kb) b) h)))
        (testing "and the direction is the least restrictive of the two, not the first"
          ;; forward joined with backward is both: the two assertions are two claims
          ;; about one rule, and a rule that may run each way may run both.  Resolving
          ;; from content is what makes the answer the same in either arrival order.
          (is (= :both (:direction (v/sentex kb h))))
          (is (= :both (:direction (v/sentex kb (v/assert kb (list 'set/backwardRule (list 'implies (list a '?x) (list b '?x))) 'CxU))))
              "and a third assertion changes nothing — the join is idempotent")))))
  (let [bird (tu/tmp-type) animal (tu/tmp-type) penguin (tu/tmp-type)
        flies (tu/tmp-pred) pengu (tu/tmp-ind)]
    (v/assert kb (list 'genl bird animal) 'CxU)
    (v/assert kb (list 'genl penguin bird) 'CxU)
    (testing "re-asserting resolves defeasibility to strict — stated once outright, it holds"
      (let [h (v/assert kb (list 'set/defaultRule (list 'set/forwardRule (list 'implies (list bird '?x) (list flies '?x)))) 'CxU)]
        (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) 'CxU {:direction :forward})   ; bare: strict wins
        (is (nil? (:defeasible (v/sentex kb h)))
            "a rule somebody also stated without set/defaultRule is not a default")
        (v/assert kb (list 'implies (list penguin '?x) (list 'not (list flies '?x))) 'CxU {:direction :forward})
        (v/assert kb (list penguin pengu) 'CxU {:strength :monotonic})
        ;; the same answer in either arrival order, which is the point: a conclusion
        ;; capped by its own premise's strength, and the exception rule taking it.
        (is (empty? (v/sentexes-matching kb (list flies pengu) 'CxU)))
        (is (seq   (v/sentexes-matching kb (list 'not (list flies pengu)) 'CxU)))
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
                    rule (list 'set/forwardRule (list 'implies (list bird '?x) (list flies '?x)))]
                (v/assert kb (list 'genl bird 'thing) 'CxU)
                (v/assert kb (spell-first rule) 'CxU)
                (v/assert kb (list bird tweety) 'CxU {:strength :monotonic})
                (v/assert kb (spell-second rule) 'CxU)
                (v/assert kb (list 'not (list flies tweety)) 'CxU
                          {:strength :monotonic})
                (let [[concl & more] (v/sentexes-matching kb (list flies tweety) 'CxU)
                      fid            (:id concl)]
                  (is (nil? more) "at most one believed conclusion, so reading it is not a choice")
                  {:conclusion-class (when fid (v/defeat-class kb fid))
                   :just-strengths   (when fid
                                       (set (map :strength
                                                 (v/supporting-justifications kb fid))))
                   :standing?        [(some? fid)
                                      (boolean
                                       (seq (v/sentexes-matching
                                             kb (list 'not (list flies tweety))
                                             'CxU)))]})))
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
        muffet (tu/tmp-ind) tweety (tu/tmp-ind) flies (tu/tmp-pred)]
    (v/assert kb (list 'genl bird animal) 'CxU)
    (v/assert kb (list dog muffet) 'CxU {:strength :monotonic})
    (v/assert kb (list bird tweety) 'CxU)                       ; default strength
    (v/assert kb (list 'set/defaultRule (list 'set/forwardRule (list 'implies (list bird '?x) (list flies '?x)))) 'CxU)
    (testing "a premise sentex carries its assumption strength"
      (is (= :monotonic (:strength (v/sentex kb (v/handle-of kb (list dog muffet) 'CxU)))))
      (is (= :default   (:strength (v/sentex kb (v/handle-of kb (list bird tweety) 'CxU))))))
    (testing "and its effective defeat-class after settling"
      (is (= :monotonic (v/defeat-class kb (v/handle-of kb (list dog muffet) 'CxU)))))
    (testing "a justification carries its strength — a default rule confers :default"
      (let [flies-id (v/handle-of kb (list flies tweety) 'CxU)
            d        (first (v/supporting-justifications kb flies-id))]
        (is (= :default (:strength d)))))))

(tu/deftest-kb a-rules-own-defeat-class-is-the-one-its-assertion-states
  ;; Two different questions read two different slots, and the rule entry point must not
  ;; answer the first with a constant.  `:strength` is the rule's *own* class, and comes
  ;; from `opts` as it does at the fact entry point; what a firing confers is `:defeasible`'s to
  ;; say (`chain/rule-view-of`), so storing a rule known-true leaves its conclusions
  ;; where they were.  Nothing in the engine defeats a rule (docs/nmtms.md states the
  ;; absence), so the slot is one that reads back rather than one that moves belief —
  ;; which is why `defeat-class` is asserted below beside the record: it is the read a
  ;; caller has, and the whole of what the flag buys them.
  (let [bird (tu/tmp-type) flies (tu/tmp-pred) chirps (tu/tmp-pred) tweety (tu/tmp-ind)
        h (v/assert-rule kb [(list bird '?x)] (list flies '?x) 'CxU
                         {:direction :forward :strength :monotonic})]
    (is (= :monotonic (:strength (v/sentex kb h))) "the flag reaches the record")
    (is (= :monotonic (v/defeat-class kb h)) "...and reads back off the handle")
    (testing "and it is not the class the firing confers — a bare rule caps at its weakest antecedent"
      (v/assert kb (list bird tweety) 'CxU)                     ; default
      (let [c (v/handle-of kb (list flies tweety) 'CxU)]
        (is (= :default (v/defeat-class kb c)))))
    (testing "a second spelling states the class again, and the record follows it"
      (let [d (v/assert-rule kb [(list bird '?y)] (list chirps '?y) 'CxU {:direction :forward})]
        (is (= :default (:strength (v/sentex kb d))))
        (is (= d (v/assert-rule kb [(list bird '?y)] (list chirps '?y) 'CxU
                                {:direction :forward :strength :monotonic}))
            "one rule, one handle — the re-assertion is not a second sentex")
        (is (= :monotonic (:strength (v/sentex kb d)))
            "the slot the identity key does not carry is not dropped with it")))
    (testing "and it resolves from content, so the two orders agree"
      ;; The third slot follows the two beside it (`reconcile-rule-slots!`): the stronger
      ;; claim stands, because a re-assert carrying no `:strength` states nothing about
      ;; the class and reading that silence as a downgrade is what would make the same
      ;; two assertions answer differently in the two orders.  Narrowing one is
      ;; `retract!` and re-assert, as it is for direction and defeasibility.
      (let [chomps (tu/tmp-pred)
            plain-first (v/assert-rule kb [(list bird '?z)] (list chomps '?z) 'CxU {:direction :forward})]
        (v/assert-rule kb [(list bird '?z)] (list chomps '?z) 'CxU {:direction :forward :strength :monotonic})
        (is (= :monotonic (:strength (v/sentex kb plain-first))) "plain then monotonic")
        ;; ...and the same pair the other way round, on the rule asserted monotonic above
        (v/assert-rule kb [(list bird '?x)] (list flies '?x) 'CxU {:direction :forward})
        (is (= :monotonic (:strength (v/sentex kb h))) "monotonic then plain")
        (is (= :monotonic (v/defeat-class kb h)) "the read-back agrees with the record")))))

;; ---- canonical variables, literal order, symmetry, comparisons ----------

(tu/deftest-kb canonical-variables-are-positional-and-reversible
  (testing "every rule variable is renamed ?var0, ?var1, … by first occurrence"
    (let [s (sx/sentex '(implies (and (p ?who ?whom)) (q ?whom ?who)) 'CxA)]
      (is (= '[(p ?var0 ?var1)] (:antecedent s)))
      (is (= '(q ?var1 ?var0) (:consequent s)))))
  (testing "the varmap restores the author's names"
    (let [s (sx/sentex '(implies (and (p ?who ?whom)) (q ?whom ?who)) 'CxA)]
      (is (= '{?var0 ?who ?var1 ?whom} (:varmap s)))
      (is (= '(implies (p ?who ?whom) (q ?whom ?who))
             (sx/originalize (sx/sentence-of s) (:varmap s))))))
  (testing "a fact carries no varmap — canonical variables are a rule concern"
    (is (nil? (:varmap (sx/sentex '(dog Muffet) 'CxA))))))

(tu/deftest-kb literal-order-is-structural-not-lexical
  (testing "a smaller-arity literal sorts first, even when its name is lexically later"
    (let [s (sx/sentex '(implies (and (aaa ?x ?y ?z) (zzz ?x)) (out ?x)) 'CxA)]
      (is (= 'zzz (ffirst (:antecedent s))))))
  (testing "a computed literal is held back until its variables are bound"
    ;; written first, but (evaluate ?z (+ ?x ?y)) can only run once ?x/?y are bound
    (let [s (sx/sentex '(implies (and (evaluate ?z (+ ?x ?y)) (foo ?x ?y)) (bar ?z)) 'CxA)]
      (is (= 'foo      (ffirst (:antecedent s))))
      (is (= 'evaluate (first (second (:antecedent s))))))))

(tu/deftest-kb rules-dedup-up-to-variable-names-and-literal-order
  (let [p (tu/tmp-pred) q (tu/tmp-pred) r (tu/tmp-pred)]
    (let [h1 (v/assert-rule kb [(list p '?x '?y) (list q '?y '?z)] (list r '?x '?z) 'CxU {:direction :forward})
          n1 (count (p/sentex-ids (:records kb)))
          ;; the same rule: variables renamed AND the antecedents written in the other order
          h2 (v/assert-rule kb [(list q '?b '?c) (list p '?a '?b)] (list r '?a '?c) 'CxU {:direction :forward})]
      (testing "the reordered, renamed rule is the same sentex"
        (is (= h1 h2))
        (is (= n1 (count (p/sentex-ids (:records kb))))))
      (testing "a genuinely different join is still a different sentex"
        (is (not= h1 (v/assert-rule kb [(list p '?a '?b) (list q '?c '?b)]
                                    (list r '?a '?c) 'CxU {:direction :forward})))))))

(tu/deftest-kb a-same-predicate-self-join-dedups-across-antecedent-order
  ;; the hard tie case: both antecedents have the SAME predicate, so nothing but the
  ;; variable-sharing structure distinguishes them — the order they were written in
  ;; must not leak into the canonical form.
  (let [par (tu/tmp-pred) grand (tu/tmp-pred)]
    (let [h1 (v/assert-rule kb [(list par '?x '?y) (list par '?y '?z)]
                            (list grand '?x '?z) 'CxU {:direction :forward})
          n1 (count (p/sentex-ids (:records kb)))
          h2 (v/assert-rule kb [(list par '?b '?c) (list par '?a '?b)]
                            (list grand '?a '?c) 'CxU {:direction :forward})]
      (testing "written in the other order, it is the same sentex"
        (is (= h1 h2))
        (is (= n1 (count (p/sentex-ids (:records kb))))))
      (testing "but the reversed join (grand ?z ?x) is genuinely different"
        (is (not= h1 (v/assert-rule kb [(list par '?x '?y) (list par '?y '?z)]
                                    (list grand '?z '?x) 'CxU {:direction :forward})))))))

(tu/deftest-kb a-framed-consequent-holds-only-the-recursive-literal
  ;; the recursive-literal hold-back keys on the predicate a literal is *about*, not on
  ;; its outermost functor: under a `not`- or `ist`-headed consequent an antecedent's
  ;; own frame is not "the recursive literal", so it sorts like any generator — and the
  ;; genuinely recursive antecedent is held back either way.
  (let [p (tu/tmp-pred) q (tu/tmp-pred) r (tu/tmp-pred)]
    (testing "a negated-head rule dedups across antecedent order"
      (let [h1 (v/assert-rule kb [(list 'not (list p '?x)) (list 'not (list q '?x))]
                              (list 'not (list r '?x)) 'CxU {:direction :forward})
            n1 (count (p/sentex-ids (:records kb)))
            h2 (v/assert-rule kb [(list 'not (list q '?x)) (list 'not (list p '?x))]
                              (list 'not (list r '?x)) 'CxU {:direction :forward})]
        (is (= h1 h2))
        (is (= n1 (count (p/sentex-ids (:records kb)))))))
    (testing "a recursive rule with a negated head keeps its recursive literal held"
      (let [b (tu/tmp-pred) a (tu/tmp-pred)
            h (v/assert-rule kb [(list b '?x '?y) (list a '?y '?z)]
                             (list 'not (list a '?x '?z)) 'CxU {:direction :forward})]
        ;; held-back literals follow the generators, so the author's right-recursion
        ;; survives canonicalization instead of being hoisted to position 0
        (is (= [b a] (mapv first (:antecedent (v/sentex kb h)))))))))

(tu/deftest-kb canonicalization-is-idempotent
  (testing "canonicalizing an already-canonical rule is a no-op"
    (let [a (sx/sentex '(implies (and (p ?x ?y) (q ?y ?z)) (r ?x ?z)) 'CxA)
          b (sx/sentex (sx/sentence-of a) 'CxA)]
      (is (= (sx/sentence-of a) (sx/sentence-of b)))
      (is (= (:antecedent a) (:antecedent b)))
      (is (= (:consequent a) (:consequent b)))))
  (testing "and the trie path is stable across the round trip"
    (let [a (sx/sentex '(implies (and (foo ?a ?b) (bar ?b)) (baz ?a)) 'CxA)]
      (is (= (sx/path a) (sx/path (sx/sentex (sx/sentence-of a) 'CxA)))))))

(tu/deftest-kb a-symmetric-fact-answers-from-either-direction
  ;; only fully-ground literals are stored sorted; a *pattern* keeps its order and
  ;; lookup probes both ways, so the stored fact is reachable either way.
  (let [sib (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind)]
    (v/assert kb (list 'symmetric sib) 'CxU)
    (v/assert kb (list sib a b) 'CxU)
    (testing "a partially-ground query finds it from both sides"
      (is (seq (v/sentexes-matching kb (list sib '?x b) 'CxU)))
      (is (seq (v/sentexes-matching kb (list sib b '?x) 'CxU)))
      (is (seq (v/sentexes-matching kb (list sib '?x a) 'CxU)))
      (is (seq (v/sentexes-matching kb (list sib a '?x) 'CxU))))
    (testing "and so does the prover engine"
      (is (v/ask? kb (list sib '?x b) 'CxU))
      (is (v/ask? kb (list sib b '?x) 'CxU)))
    (testing "a fully-open pattern returns the one stored sentex, not a duplicate"
      (is (= 1 (count (v/sentexes-matching kb (list sib '?x '?y) 'CxU)))))
    (testing "an unrelated individual still does not match"
      (is (empty? (v/sentexes-matching kb (list sib '?x (tu/tmp-ind)) 'CxU))))))

(tu/deftest-kb a-fact-asserted-before-its-symmetric-declaration-stays-reachable
  ;; Canonical sorting only applies once `(symmetric P)` is known, so a fact stored
  ;; earlier may sit in the "wrong" order.  The declaration re-spells it where it lies
  ;; (`integrate/symmetrize-existing`), so the handle survives, both directions answer,
  ;; and the mirror asserted afterwards resolves to it rather than storing a second row.
  ;;
  ;; Both orders of the pair, because only one of them is out of order and which one is
  ;; decided by the generated names: run over the canonically-spelled fact alone this
  ;; is indistinguishable from a claim about the other and never stores one.
  (let [a (tu/tmp-ind) b (tu/tmp-ind)]
    (doseq [[x y] [[a b] [b a]]]
      (let [sib (tu/tmp-pred)
            h   (v/assert kb (list sib x y) 'CxU)]    ; stored before the metadata
        (v/assert kb (list 'symmetric sib) 'CxU)
        (testing "it is still found from either direction"
          (is (seq (v/sentexes-matching kb (list sib x y) 'CxU)))
          (is (seq (v/sentexes-matching kb (list sib y x) 'CxU))))
        (testing "and it is one row, at the handle the assertion returned"
          (is (= 1 (count (v/sentexes-matching kb (list sib '?p '?q) 'CxU))))
          (is (= h (v/handle-of kb (list sib x y) 'CxU)))
          (is (= h (v/handle-of kb (list sib y x) 'CxU))))
        (testing "and asserting the mirror image resolves to it rather than duplicating"
          (is (= h (v/assert kb (list sib y x) 'CxU)))
          (is (= 1 (count (v/sentexes-matching kb (list sib '?p '?q) 'CxU)))))))))

(tu/deftest-kb the-bulk-path-dedups-a-symmetric-mirror-against-a-stored-fact
  ;; `bulk-assert-facts!` skips the dedup trie-walk, but a symmetric functor keeps it: the
  ;; caller who writes `(sib b a)` cannot know it is the mirror of a stored `(sib a b)`
  ;; without the `(symmetric P)` read the fast path is avoiding.  Stored raw it was a second
  ;; record for one proposition — `count-with-functor` 2, both spellings retractable apart —
  ;; which broke the "identical to loading one-by-one" contract (vaelii#61).
  (let [sib (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind)]
    (v/assert kb (list 'symmetric sib) 'CxU)
    (let [h (v/assert kb (list sib a b) 'CxU)]
      (testing "the mirror, loaded in bulk, resolves to the stored handle"
        (is (= [h] (v/bulk-assert-facts! kb [(list sib b a)] 'CxU))))
      (testing "one record for the one proposition, at every read"
        (is (= 1 (count (v/sentexes-matching kb (list sib '?p '?q) 'CxU))))
        (is (= 1 (v/count-with-functor kb sib)))
        (is (= h (v/handle-of kb (list sib b a) 'CxU)))
        (is (= h (v/handle-of kb (list sib a b) 'CxU))))
      (testing "retracting the one handle leaves nothing"
        (v/retract! kb h)
        (is (empty? (v/sentexes-matching kb (list sib '?p '?q) 'CxU)))))))

(tu/deftest-kb an-anonymous-wildcard-consequent-is-rejected
  ;; `_` is a fresh variable at each occurrence, so it can never carry a binding from
  ;; an antecedent to the consequent — allowing it would store a non-ground junk fact.
  (let [p (tu/tmp-pred) q (tu/tmp-pred)]
    (is (= :not-range-restricted
           (try (v/assert-rule kb [(list p '_)] (list q '_) 'CxU {:direction :forward}) nil
                (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
    (testing "and nothing was stored"
      (is (empty? (v/find-sentexes kb q))))))

(tu/deftest-kb a-rule-antecedent-over-a-symmetric-predicate-still-joins
  ;; a partially-substituted antecedent is a pattern, so it must not be reordered —
  ;; otherwise forward chaining would under-derive over symmetric relations.
  (let [sib (tu/tmp-pred) knows (tu/tmp-pred)
        a (tu/tmp-ind) b (tu/tmp-ind)]
    (v/assert kb (list 'symmetric sib) 'CxU)
    (v/assert kb (list sib a b) 'CxU)
    (v/assert-rule kb [(list sib '?p '?q)] (list knows '?p '?q) 'CxU {:direction :forward})
    (testing "the rule fires on the stored symmetric fact"
      (is (seq (v/sentexes-matching kb (list knows '?x '?y) 'CxU))))))

(tu/deftest-kb symmetric-arguments-canonicalize-to-one-sentex
  (let [sib (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind)]
    (v/assert kb (list 'symmetric sib) 'CxU)
    (let [h1 (v/assert kb (list sib a b) 'CxU)
          n1 (count (p/sentex-ids (:records kb)))
          h2 (v/assert kb (list sib b a) 'CxU)]     ; the mirror image
      (testing "the mirrored assertion resolves to the same sentex, storing nothing new"
        (is (= h1 h2))
        (is (= n1 (count (p/sentex-ids (:records kb))))))
      (testing "and it is found from either direction"
        (is (seq (v/sentexes-matching kb (list sib a b) 'CxU)))
        (is (seq (v/sentexes-matching kb (list sib b a) 'CxU)))))
    (testing "an asymmetric predicate keeps its argument order"
      (let [ord (tu/tmp-pred)]
        (is (not= (v/assert kb (list ord a b) 'CxU)
                  (v/assert kb (list ord b a) 'CxU)))))))

(tu/deftest-kb comparison-siblings-fold-onto-less-than
  (testing "greaterThan is stored as lessThan with reversed arguments"
    (is (= '(lessThan 3 5) (:sentence (sx/sentex '(greaterThan 5 3) 'CxA))))
    (is (= '(lessThan ?var0 ?var1)
           (:consequent (sx/sentex '(implies (p ?a ?b) (greaterThan ?b ?a)) 'CxA)))))
  (testing "both directions resolve to one sentex in the store"
    (let [h1 (v/assert kb '(greaterThan 5 3) 'CxU)
          h2 (v/assert kb '(lessThan 3 5) 'CxU)]
      (is (= h1 h2)))))

(tu/deftest-kb comparison-chains-collapse-into-one-variable-arity-literal
  (testing "chained comparisons in an antecedent merge into a single literal"
    (let [s   (sx/sentex '(implies (and (foo ?a ?b ?c) (lessThan ?a ?b) (lessThan ?b ?c))
                                   (bar ?a ?c)) 'CxA)
          lts (filterv #(= 'lessThan (first %)) (:antecedent s))]
      (is (= 1 (count lts)) "one chain literal, not two")
      (is (= 4 (count (first lts))) "variable arity: (lessThan a b c)")))
  (testing "a folded greaterThan joins the same chain"
    (let [s   (sx/sentex '(implies (and (foo ?a ?b ?c) (greaterThan ?b ?a) (lessThan ?b ?c))
                                   (bar ?a ?c)) 'CxA)
          lts (filterv #(= 'lessThan (first %)) (:antecedent s))]
      (is (= 1 (count lts)))
      (is (= 4 (count (first lts))))))
  (testing "a branch is not merged — (a<b) and (a<c) stay separate"
    (let [s   (sx/sentex '(implies (and (foo ?a ?b ?c) (lessThan ?a ?b) (lessThan ?a ?c))
                                   (bar ?a ?c)) 'CxA)
          lts (filterv #(= 'lessThan (first %)) (:antecedent s))]
      (is (= 2 (count lts))))))

(tu/deftest-kb different-is-deferred-but-never-merged
  ;; `different` shares exactly one property with the comparisons above — it consumes
  ;; bindings rather than producing them, so it is held back — and none of the others.
  (testing "a `different` antecedent is held back after the literals that bind it"
    (let [s     (sx/sentex '(implies (and (different ?x ?y) (parentOf ?p ?x) (parentOf ?p ?y))
                                     (siblingOf ?x ?y))
                           'CxA)
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
                                     (bar ?a ?c)) 'CxA)
          diffs (filterv #(= 'different (first %)) (:antecedent s))]
      (is (= 2 (count diffs)) "two literals, not one chain")
      (is (every? #(= 3 (count %)) diffs) "each still binary — no (different a b c)")))
  (testing "nor are its arguments sorted, and no sibling folds onto it"
    (let [s (sx/sentex '(different Zeta Alpha) 'CxA)]
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
    (v/assert kb (list born a 1970) 'CxU)
    (v/assert kb (list born b 1980) 'CxU)
    (v/assert kb (list born c 1990) 'CxU)
    (let [h (v/assert-rule kb [(list born '?x '?bx) (list born '?y '?by) (list born '?z '?bz)
                               (list 'lessThan '?bx '?by) (list 'lessThan '?by '?bz)]
                           (list between '?x '?y '?z) 'CxU {:direction :backward})
          lts (filterv #(= 'lessThan (first %)) (:antecedent (v/sentex kb h)))]
      (testing "the two comparisons are stored as one chain literal"
        (is (= 1 (count lts)))
        (is (= 4 (count (first lts)))))
      (testing "and the collapsed chain still discharges through the prover"
        (is (v/query? kb (list between a b c) 'CxU {:max-depth 2}))
        (is (not (v/query? kb (list between c b a) 'CxU {:max-depth 2})))
        (is (not (v/query? kb (list between b a c) 'CxU {:max-depth 2})))))))

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
                                  (set/defaultRule (implies (bird ?b) (flies ?b)))) 'CxA)]
    (testing "no wrapper survives onto the stored sentence"
      (is (= '(implies (bird ?var0) (flies ?var0)) (sx/sentence-of s)))
      (is (not (some '#{exceptWhen set/defaultRule}
                     (tree-seq sequential? seq (sx/sentence-of s))))))
    (testing "the sibling wrappers still canonicalize into their own fields"
      (is (true? (:defeasible s)))
      (is (= :backward (:direction s))))
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
                                      (list 'set/forwardRule (list 'implies (list bird '?b) (list flies '?b)))))
                       'CxU)
        rh   (v/handle-of kb rule-form 'CxU)]
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
                     'CxU)
        rh (v/handle-of kb rule-form 'CxU)
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
                                (list 'implies (list bird '?b) (list flies '?b))) 'CxU)
        vec1 (v/assert kb (list 'exceptWhen [(list penguin '?b)]
                                (list 'implies (list bird '?b) (list flies '?b))) 'CxU)
        rh   (v/handle-of kb rule-form 'CxU)]
    (testing "a single literal may be written bare or as a one-vector; one meta-sentex"
      (is (= bare vec1))
      (is (= [[(list penguin '?var0)]] (provers/rule-exceptions kb rh))))))

(tu/deftest-kb a-vector-exceptions-conjuncts-are-order-insensitive
  ;; conjuncts within one exceptWhen are independent ground checks, so their order (and
  ;; a duplicate) is not their identity — the meta-sentex dedups.
  (let [bird (tu/tmp-type) penguin (tu/tmp-type) young (tu/tmp-type) flies (tu/tmp-pred)
        rule-form (vr/rule-sentence [(list bird '?b)] (list flies '?b))
        a (v/assert kb (list 'exceptWhen [(list young '?b) (list penguin '?b)]
                             (list 'implies (list bird '?b) (list flies '?b))) 'CxU)
        b (v/assert kb (list 'exceptWhen [(list penguin '?z) (list young '?z) (list penguin '?z)]
                             (list 'implies (list bird '?z) (list flies '?z))) 'CxU)
        rh (v/handle-of kb rule-form 'CxU)]
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
                    'CxU)
        rh1 (v/handle-of kb (vr/rule-sentence [(list bird '?b)] (list flies '?b)) 'CxU)
        rh2 (v/handle-of kb (vr/rule-sentence [(list bird '?b)] (list light '?b)) 'CxU)]
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
                                 (list 'set/forwardRule (list 'implies (list bird '?b) (list flies '?b))))
                        'CxU)
        exc   (v/assert kb (list 'exceptWhen (list penguin '?b)
                                 (list 'set/defaultRule
                                       (list 'set/forwardRule (list 'implies (list bird '?b) (list flies '?b)))))
                        'CxU)]
    (testing "the exception is a separate meta-sentex, but names the one rule"
      (is (not= plain exc))
      (is (= plain (v/handle-of kb rule-form 'CxU))))
    (testing "an α-equivalent exception dedups to the same meta-sentex"
      (let [n2   (count (p/sentex-ids (:records kb)))
            same (v/assert kb (list 'exceptWhen [(list penguin '?w)]
                                    (list 'set/defaultRule
                                          (list 'set/forwardRule (list 'implies (list bird '?w) (list flies '?w)))))
                           'CxU)]
        (is (= exc same))
        (is (= n2 (count (p/sentex-ids (:records kb)))))))
    (testing "a different exception is a second meta-sentex on the same rule"
      (let [exc2 (v/assert kb (list 'exceptWhen (list young '?b)
                                    (list 'set/defaultRule
                                          (list 'set/forwardRule (list 'implies (list bird '?b) (list flies '?b)))))
                           'CxU)]
        (is (not= exc exc2))
        (is (= plain (v/handle-of kb rule-form 'CxU)))
        (is (= 2 (count (provers/rule-exceptions kb plain))))))))

(tu/deftest-kb an-exception-variable-no-antecedent-binds-is-rejected
  ;; closure is what makes the exception a ground existence check instead of a
  ;; search, and it is why an *existential* exception ("unless it has a sick child")
  ;; is not expressible.
  (let [bird (tu/tmp-type) sick (tu/tmp-pred) flies (tu/tmp-pred)
        rule (list 'exceptWhen (list sick '?child)
                   (list 'set/defaultRule (list 'set/forwardRule (list 'implies (list bird '?b) (list flies '?b)))))]
    (testing "assert refuses an exception whose variable no antecedent binds"
      (let [e (try (v/assert kb rule 'CxU)
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (= :exception-not-closed (:type (ex-data e))))
        (is (= '[?child] (:unbound (ex-data e))))))
    (testing "and stores nothing about the conclusion"
      (is (empty? (v/find-sentexes kb flies))))
    (testing "an antecedent that binds the witness is the workaround, and is accepted"
      (is (some? (v/assert kb (list 'exceptWhen (list sick '?child)
                                    (list 'set/defaultRule
                                          (list 'set/forwardRule (list 'implies
                                                                       (list 'and (list bird '?b) (list bird '?child))
                                                                       (list flies '?b)))))
                           'CxU))))))

;; ---- regression: the whole starter still reasons ------------------------

(tu/deftest-kb ^:slow starter-reasons-under-canonicalized-sentexes
  (do
    (starter/load-into kb)
    (world/load-cast kb)
    (testing "facts, negation, rules, and derivations all survive"
      (is (seq (v/sentexes-matching kb '(grandparentOf Tom Ann) 'CxNaturalWorld)))
      (is (empty? (v/sentexes-matching kb '(flies Tweety) 'CxNaturalWorld)))
      (is (seq (v/sentexes-matching kb '(not (hasCapability Tweety flying)) 'CxNaturalWorld)))
      (is (v/ask? kb '(ancestorOf Tom Ann)))
      (is (empty? (v/conflicts kb))))))

;; ---- the symbol pool is bounded, and the bound changes no answer ---------

(deftest the-symbol-pool-is-bounded-and-a-rotation-changes-no-answer
  ;; Interning is a pure space optimization, and the pool is not vocabulary-sized: NAT
  ;; reification, head-existential skolemization and abduction each mint a fresh symbol
  ;; per fact, so an unbounded pool grows with the KB.  With room for a handful, minting
  ;; past it rotates the pool's generations — and because interning changes identity and
  ;; never equality, a canonicalization either side of a rotation still answers `=`,
  ;; hashes the same, and keys a map the same.
  (binding [sx/*symbol-pool-limit* 8]
    (let [before (sx/canon '(parentOf Tom Bob))]
      (dotimes [i 200]
        (sx/canon (list (symbol (str "minted" i)) (symbol (str "Witness" i))))
        (is (<= (#'sx/pool-size) 8) (str "the pool never exceeds its bound (mint " i ")")))
      (let [after (sx/canon '(parentOf Tom Bob))]
        (testing "the canonical form survives every rotation in between"
          (is (= before after))
          (is (= (hash before) (hash after)))
          (is (= {before :v} {after :v}) "so it still keys a map"))
        (testing "and a sentex built either side is still the same sentex"
          (is (= (sx/sentex before 'CxA) (sx/sentex after 'CxA)))))
      (testing "sharing resumes for whatever is named after a rotation"
        (is (identical? (sx/intern-sym 'pooledAgain) (sx/intern-sym 'pooledAgain)))))))

(deftest a-rotation-keeps-a-name-in-use-and-drops-a-name-left-unused
  ;; A lookup that finds a name in the previous generation puts it into the current one, so
  ;; a name read between every two rotations keeps one object while the pool rotates under
  ;; it.  A name nobody reads for two rotations leaves the pool, and the next mention pools
  ;; a fresh instance.  `(symbol …)` builds a new, unpooled object on every call, so
  ;; `identical?` against the first pooled instance tells the two cases apart.
  (binding [sx/*symbol-pool-limit* 8]
    (let [hot  (sx/intern-sym (symbol "poolHotName"))
          cold (sx/intern-sym (symbol "poolColdName"))]
      (dotimes [i 100]
        (sx/intern-sym (symbol (str "poolFiller" i)))
        (is (identical? hot (sx/intern-sym (symbol "poolHotName")))
            (str "a name read every step keeps its object (filler " i ")")))
      (is (not (identical? cold (sx/intern-sym (symbol "poolColdName"))))
          "a name unread across the rotations was dropped and is pooled afresh"))))

(tu/deftest-kb a-double-negated-rule-antecedent-fires-like-the-plain-one
  ;; The fact entry point peels double negation; the rule entry point must too.  A
  ;; `(not (not (foo ?x)))` antecedent otherwise keys under `[:not not]`, which no stored
  ;; fact's trigger key ever is (a fact canonicalizes that away to `(foo ?x)`), so the
  ;; rule never fires and is accepted with no refusal — silently inert.
  (let [p (tu/tmp-pred) foo (tu/tmp-pred) q (tu/tmp-pred) A (tu/tmp-ind)]
    (v/assert-rule kb [(list p '?x) (list 'not (list 'not (list foo '?x)))]
                   (list q '?x) 'CxU {:direction :forward})
    (v/assert kb (list p A) 'CxU)
    (v/assert kb (list foo A) 'CxU)
    (testing "the double-negated antecedent triggers the rule"
      (is (seq (v/sentexes-matching kb (list q A) 'CxU))))
    (testing "and it is one rule with the plain-antecedent spelling, not two handles"
      (is (= (v/assert-rule kb [(list p '?x) (list foo '?x)] (list q '?x) 'CxU {:direction :forward})
             (v/assert-rule kb [(list p '?x) (list 'not (list 'not (list foo '?x)))]
                            (list q '?x) 'CxU {:direction :forward}))))))
