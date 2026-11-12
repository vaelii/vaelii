;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.defn-inference-test
  "Query-time definitional *inference*.  Two behaviours this suite asserts, both TDD-red
  until the build lands:

  1. **Evaluative `defnSufficient`.**  A sufficient condition built from *computed*
     predicates (`integer`, `lessThan`, or any `add-evaluatable` check) must admit a
     member by **evaluating the condition at query time** — not only by a forward rule
     firing on an already-*believed* condition.  Computed conditions are never stored
     sentexes (see `evaluatable-test`), so the forward rule never fires and the member
     is never derived today.  This is the wall the `-212` predAll demo hit.

  2. **Admittance precedence + fast-fail over the genl lattice.**  A `defnSufficient`
     never admits a member that fails any `defnNecessary` of the collection or its
     genls (necessary wins).  The admittance walk checks each defn **once** on success
     and **short-circuits** on the first failing necessary — checking the most general
     necessary before descending to a spec's sufficient, and never re-checking a defn
     reachable by two genl paths.

  Call-counts are observed from outside the walk: each defn's condition is an `add-evaluatable`
  predicate backed by a counter atom, so the count is a side effect of the real
  admittance walk, not a peek into its internals."
  (:require [clojure.test :refer [is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- counted!
  "Register `pred` on `kb` as a 1-ary evaluatable check that increments `cnt` on every
  call and returns `ret`.  The counter is how we watch the admittance walk touch a defn."
  [kb pred cnt ret]
  (v/add-evaluatable kb pred (fn [_x] (swap! cnt inc) ret)))

;; ---- 1. evaluative defnSufficient: prove on query by evaluating the condition ----

(tu/deftest-kb sufficient-admits-by-evaluating-a-computed-condition
  ;; The core build.  `qualifies` is computed, never a stored fact, so the forward
  ;; rule (implies (qualifies ?x) (widget ?x)) has nothing to fire on.  Admittance
  ;; must EVALUATE the sufficient condition against the queried member.
  (tu/with-terms [widget qualifies]
    (v/add-evaluatable kb qualifies (fn [n] (> n 40)))
    (v/assert kb (list 'defnSufficient widget (list qualifies '?x)) 'CxUniverse)
    (is (v/ask? kb (list widget 42) 'CxUniverse)
        "42 qualifies, so evaluating the sufficient condition admits it — no stored membership needed")
    (is (not (v/ask? kb (list widget 10) 'CxUniverse))
        "10 does not qualify, so it is not admitted")))

(tu/deftest-kb sufficient-conjunction-of-computed-predicates-mirrors-negative-integer
  ;; The `-212` shape exactly: (and (integer ?x) (lessThan ?x 0)) as a defnSufficient,
  ;; both conjuncts computed.  `negative_integer` inherits this once the inference lands.
  (tu/with-terms [negnum isInt below0]
    (v/add-evaluatable kb isInt  integer?)
    (v/add-evaluatable kb below0 (fn [n] (neg? n)))
    (v/assert kb (list 'defnSufficient negnum
                       (list 'and (list isInt '?x) (list below0 '?x)))
              'CxUniverse)
    (is (v/ask? kb (list negnum -212) 'CxUniverse)
        "-212 is an integer below zero, so the evaluated sufficient condition admits it from the bare number")
    (is (not (v/ask? kb (list negnum 7) 'CxUniverse))
        "7 is an integer but not below zero")))

;; ---- 2. semantics: sufficient is authoritative, necessary is an optimization ----
;; defns are two-valued; a defnSufficient that passes admits, full stop;
;; a defnNecessary is a sound negative witness / fast-fail, never a condition that admits.

(tu/deftest-kb sufficient-is-authoritative-a-failing-necessary-does-not-veto
  ;; A passing sufficient admits even when a necessary fails. That makes the KB
  ;; inconsistent — (widget 7) and (not (widget 7)) both become provable — which is FINE:
  ;; we DOCUMENT it and assert no arbitration. Here we assert only the rule (sufficient
  ;; admits); the negative half is exercised in the negation tests below.
  ;; Green after Phase A: the query-time sufficient prover admits without consulting necessaries.
  (tu/with-terms [widget suff nec]
    (v/add-evaluatable kb suff (fn [_] true))
    (v/add-evaluatable kb nec  (fn [_] false))
    (v/assert kb (list 'defnSufficient widget (list suff '?x)) 'CxUniverse)
    (v/assert kb (list 'defnNecessary  widget (list nec  '?x)) 'CxUniverse)
    (is (v/ask? kb (list widget 7) 'CxUniverse)
        "sufficient is authoritative: (suff 7) holds, so 7 is admitted; the failing necessary does not veto (the resulting inconsistency is documented, not asserted)")))

;; ---- 3. positive membership descends to a SPEC's sufficient (down the genl edges) ----

(tu/deftest-kb positive-membership-descends-to-a-specs-sufficient
  ;; Specs down the genl edges: (animal 7) is provable because 7 is a dog (dog's
  ;; sufficient holds) and dog ⊑ animal. The positive walk descends to a spec's sufficient.
  ;; RED until Phase B — Phase A consults only the queried collection's OWN sufficient.
  (tu/with-terms [animal dog dogSuff]
    (v/add-evaluatable kb dogSuff (fn [_] true))
    (v/assert kb (list 'genl dog animal) 'CxUniverse)               ; dog is the spec (below animal)
    (v/assert kb (list 'defnSufficient dog (list dogSuff '?x)) 'CxUniverse)
    (is (v/ask? kb (list animal 7) 'CxUniverse)
        "7 is a dog and dog ⊑ animal, so 7 is an animal — positive walk descends to the spec's sufficient")))

;; ---- 4. negation: (not (coll x)) via a FAILING necessary, ascending genls (the converse) ----

(tu/deftest-kb negative-membership-from-a-failing-own-necessary
  ;; (not (widget x)) is provable when widget's own necessary fails for x (member ⇒ nec,
  ;; contrapositive). Two-valued: a necessary that does not hold is a disproof. RED until Phase B.
  (tu/with-terms [widget nec]
    (v/add-evaluatable kb nec (fn [_] false))
    (v/assert kb (list 'defnNecessary widget (list nec '?x)) 'CxUniverse)
    (is (v/ask? kb (list 'not (list widget 7)) 'CxUniverse)
        "(nec 7) fails and member ⇒ nec, so ¬(widget 7) is provable")))

(tu/deftest-kb negative-membership-ascends-to-a-genls-necessary
  ;; the converse of positive-descends-to-specs: (not (dog x)) is provable when a GENL's
  ;; necessary fails — ascend up the genl edges. RED until Phase B.
  (tu/with-terms [animal dog animalNec]
    (v/add-evaluatable kb animalNec (fn [_] false))
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (v/assert kb (list 'defnNecessary animal (list animalNec '?x)) 'CxUniverse)
    (is (v/ask? kb (list 'not (list dog 7)) 'CxUniverse)
        "animal's necessary fails and dog ⊑ animal, so ¬(animal 7) ⇒ ¬(dog 7) — negative walk ascends to the genl's necessary")))

(tu/deftest-kb negated-defn-of-non-members-is-provable
  ;; A concrete slice: (not (positive_integer x)) for a zero / a string / a predicate,
  ;; each provable by FAILING a necessary conjunct. Self-contained pos_int. RED until Phase B.
  (tu/with-terms [pos_int isInt isPos]
    (v/add-evaluatable kb isInt integer?)
    (v/add-evaluatable kb isPos (fn [n] (and (number? n) (pos? n))))
    (v/assert kb (list 'defnNecessary pos_int
                       (list 'and (list isInt '?x) (list isPos '?x)))
              'CxUniverse)
    (is (v/ask? kb (list 'not (list pos_int 0)) 'CxUniverse)
        "0 fails isPos ⇒ ¬(pos_int 0)")
    (is (v/ask? kb (list 'not (list pos_int "string")) 'CxUniverse)
        "a string fails isInt ⇒ ¬(pos_int string)")
    (is (v/ask? kb (list 'not (list pos_int 'unary_predicate)) 'CxUniverse)
        "a predicate fails isInt ⇒ ¬(pos_int unary_predicate)")))

;; ---- 3. the genl diamond: dedup on admit, short-circuit on reject ----

(defn- diamond!
  "Build the diamond dbottom ⊏ {dmid_a,dmid_b} ⊏ dtop with a defnNecessary on all four and a
  defnSufficient on dbottom, each condition a counted evaluatable.  Returns the counters."
  [kb dtop dmid_a dmid_b dbottom topNec midANec midBNec bottomNec bottomSuff
   {:keys [top mida midb bottomn bsuff] :or {bsuff true}}]
  (let [ct  (atom 0) ca (atom 0) cb (atom 0) cbn (atom 0) cbs (atom 0)]
    (counted! kb topNec     ct  top)
    (counted! kb midANec    ca  mida)
    (counted! kb midBNec    cb  midb)
    (counted! kb bottomNec  cbn bottomn)
    (counted! kb bottomSuff cbs bsuff)
    (v/assert kb (list 'genl dbottom dmid_a) 'CxUniverse)
    (v/assert kb (list 'genl dbottom dmid_b) 'CxUniverse)
    (v/assert kb (list 'genl dmid_a dtop) 'CxUniverse)
    (v/assert kb (list 'genl dmid_b dtop) 'CxUniverse)
    (v/assert kb (list 'defnNecessary  dtop     (list topNec     '?x)) 'CxUniverse)
    (v/assert kb (list 'defnNecessary  dmid_a    (list midANec    '?x)) 'CxUniverse)
    (v/assert kb (list 'defnNecessary  dmid_b    (list midBNec    '?x)) 'CxUniverse)
    (v/assert kb (list 'defnNecessary  dbottom  (list bottomNec  '?x)) 'CxUniverse)
    (v/assert kb (list 'defnSufficient dbottom  (list bottomSuff '?x)) 'CxUniverse)
    {:top ct :mida ca :midb cb :bottomn cbn :bottomsuff cbs}))

(tu/deftest-kb diamond-admitted-checks-no-defn-more-than-once
  ;; Admitting via dbottom's sufficient does NOT require checking necessaries
  ;; (sufficient authoritative). Whatever necessaries the walk touches, it touches each
  ;; AT MOST once — dtop is reachable by two genl paths and must never be double-checked.
  ;; The admitting sufficient is evaluated exactly once.
  (tu/with-terms [dtop dmid_a dmid_b dbottom
                  topNec midANec midBNec bottomNec bottomSuff]
    (let [c (diamond! kb dtop dmid_a dmid_b dbottom
                      topNec midANec midBNec bottomNec bottomSuff
                      {:top true :mida true :midb true :bottomn true})]
      (is (v/ask? kb (list dbottom 42) 'CxUniverse)
          "dbottom's sufficient holds ⇒ 42 admitted")
      (is (= 1 @(:bottomsuff c)) "the admitting sufficient is evaluated exactly once")
      (is (<= @(:top c) 1)     "dtop's necessary checked at most once — never twice across the two genl paths (dedup)")
      (is (<= @(:mida c) 1)    "dmid_a's necessary at most once")
      (is (<= @(:midb c) 1)    "dmid_b's necessary at most once")
      (is (<= @(:bottomn c) 1) "dbottom's necessary at most once"))))

(tu/deftest-kb a-conjunct-shared-by-sufficient-conditions-is-evaluated-once-per-walk
  (tu/with-terms [dtop dspa dspb dspc sharedCond condA condB condC]
    (let [n (atom 0)]
      (counted! kb sharedCond n false)
      (doseq [[t c] [[dspa condA] [dspb condB] [dspc condC]]]
        (v/add-evaluatable kb c (constantly true))
        (v/assert kb (list 'genl t dtop) 'CxUniverse)
        (v/assert kb (list 'defnSufficient t (list 'and (list sharedCond '?x) (list c '?x)))
                  'CxUniverse))
      (is (not (v/ask? kb (list dtop 42) 'CxUniverse)))
      (is (= 1 @n) "sharedCond fails for 42, so each of the three conditions reaches it"))))

(tu/deftest-kb diamond-a-failing-topmost-necessary-short-circuits-the-optimization
  ;; The optimization: querying (dbottom 42) where 42 genuinely is NOT a dbottom
  ;; (sufficient false — consistent KB) and the topmost necessary (dtop) fails. The
  ;; fast-fail checks the most-general necessary first, sees it fail, and rejects WITHOUT
  ;; evaluating the sides or the (possibly expensive) sufficient — a pure speedup.
  ;; RED until Phase B builds the fast-fail. (Phase A would call bottomSuff and skip the
  ;; necessaries: top==0, bottomsuff==1 — the inverse of the target.)
  (tu/with-terms [dtop dmid_a dmid_b dbottom
                  topNec midANec midBNec bottomNec bottomSuff]
    (let [c (diamond! kb dtop dmid_a dmid_b dbottom
                      topNec midANec midBNec bottomNec bottomSuff
                      {:top false :mida true :midb true :bottomn true :bsuff false})]
      (is (not (v/ask? kb (list dbottom 42) 'CxUniverse))
          "42 is not a dbottom (sufficient false), and the failing top necessary confirms it")
      (is (= 1 @(:top c))       "dtop's necessary checked exactly once, first — the broadest disqualifier")
      (is (= 0 @(:mida c))      "dmid_a not checked — short-circuit before the sides")
      (is (= 0 @(:midb c))      "dmid_b not checked")
      (is (= 0 @(:bottomsuff c)) "the sufficient is skipped once the top necessary fails"))))

;; ---- 4. characterization: assert what asking a defn collection of a number does TODAY ----

(tu/deftest-kb baseline-a-computed-sufficient-does-not-admit-a-number-yet
  ;; The characterization question: what currently happens when you ask (?pred 212)? Assert
  ;; it with a test, with a comment about defns.  This assertion was written against the PRE-evaluative baseline
  ;; (a computed defnSufficient never fired forward, so the number was not admitted) and
  ;; was designed to FLIP once `sufficient-admits-by-evaluating-a-computed-condition` went
  ;; green.  Phase A (query-time evaluative defnSufficient) is exactly that change, so it
  ;; is flipped here in the same commit: 12 is now admitted by EVALUATING `(under 12)`
  ;; against the queried number, no stored membership and no forward firing needed.
  (tu/with-terms [small under]
    (v/add-evaluatable kb under (fn [n] (< n 100)))
    (v/assert kb (list 'defnSufficient small (list under '?x)) 'CxUniverse)
    (is (v/ask? kb (list small 12) 'CxUniverse)
        "POST-Phase-A: the computed sufficient condition (under 12) is evaluated at query time and admits number 12; no forward defn rule fires, no membership is stored.")))
