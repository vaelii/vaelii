;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.preserving-recheck-test
  "The exception re-check of a settle that queued many `{::preserving s}` markers: what
  each marker's `inherit/moved-goal-test` reads, and that reading it cheaply answers as
  reading it whole did.

  A `genl` edge into a type moves the goals of a predicate preserved along `genl` whose
  arguments the type's reach names, and with `(transitive P)` that reach is joined with
  `P`'s own facts (`inherit/reach`): every term of the type's closure, and a `P` literal
  of each.  Three things keep a batch of such edges from costing a reach each:

  * the re-check reads every marker under one question memo (`recheck/exception-candidates`);
  * the test is a membership over the reaches the memo holds, not their union copied;
  * a `P` literal's fan is cut by the slot predicate sets whatever its size
    (`res/*cut-every-fan?*`), so a term no fact of `P` names costs the slot reads.

  Each is checked here against the reading it replaced."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.recheck :as recheck]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.special :as special]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(def ^:private ctx 'CxUniverse)

(def ^:private kinds
  "`prt_material` over eight specs, `prt_mammal` over two and `prt_insect` over one."
  (concat (for [i (range 8)] [(symbol (str "prt_m" i)) 'prt_material])
          '[[prt_dog prt_mammal] [prt_cat prt_mammal] [prt_ant prt_insect]
            [prt_mammal prt_animal] [prt_insect prt_animal]]))

(defn- preserving-kb!
  "`prtLarger` transitive and preserved along `genl` at both positions, two sub-predicates
  and three `genlInverse` ones under it, a symmetric sub-predicate, a forward rule on it,
  and its facts: two stated of kinds, one through a sub-predicate, one through a
  `genlInverse` one, and one from a spec of `prt_material`."
  [kb]
  (v/with-deferred-settle kb
    (doseq [[a b] kinds] (v/assert kb (list 'genl a b) ctx))
    (v/assert kb '(transitive prtLarger) ctx)
    (v/assert kb '(transitiveInArgInverse prtLarger 1 genl) ctx)
    (v/assert kb '(transitiveInArgInverse prtLarger 2 genl) ctx)
    (v/assert kb '(genl prtHeavier prtLarger) ctx)
    (v/assert kb '(genl prtTaller prtLarger) ctx)
    (v/assert kb '(symmetric prtBeside) ctx)
    (v/assert kb '(genl prtBeside prtLarger) ctx)
    (doseq [i (range 3)]
      (v/assert kb (list 'genlInverse (symbol (str "prtInside" i)) 'prtLarger) ctx))
    (v/assert kb '(prtLarger prt_mammal prt_insect) ctx)
    (v/assert kb '(prtLarger prt_animal prt_pebble) ctx)
    (v/assert kb '(prtHeavier prt_m3 prt_dust) ctx)
    (v/assert kb '(prtInside0 prt_grain prt_m5) ctx)
    (v/assert kb '(prtBeside prt_pebble prt_grain) ctx)
    (v/assert-rule kb '[(prtLarger ?x ?y)] '(prtOutweighs ?x ?y) ctx {:direction :forward})))

(def ^:private terms
  (into '[prt_material prt_mammal prt_insect prt_animal prt_pebble prt_dust prt_grain
          prt_stuff prt_unrelated]
        (map first kinds)))

;; ---- the fan cut ---------------------------------------------------------

(tu/deftest-kb a-fan-cut-by-the-slot-sets-answers-what-the-whole-fan-does
  (preserving-kb! kb)
  (let [rels '[prtLarger prtHeavier prtBeside prtInside0]
        pats (for [r rels, t terms, p [(list r '?rv t) (list r t '?rv)]] p)
        raws (atom 0)
        raw  res/raw-match
        read (fn [cut? p c]
               (binding [res/*cut-every-fan?* cut?]
                 (set (res/matches-visible kb p c false))))]
    (doseq [c ['?ctx ctx]]
      (testing (str "from " c)
        (doseq [p pats]
          (is (= (read false p c) (read true p c)) (pr-str p)))))
    (testing "the cut runs: a term no member holds reads no member"
      (with-redefs [res/raw-match (fn [& args] (swap! raws inc) (apply raw args))]
        (let [whole (do (reset! raws 0) (read false '(prtLarger ?rv prt_m0) '?ctx) @raws)
              cut   (do (reset! raws 0) (read true '(prtLarger ?rv prt_m0) '?ctx) @raws)]
          (is (< 1 whole))
          (is (zero? cut)))))))

;; ---- the goal test -------------------------------------------------------

(def ^:private sentences
  "The edges and claims a settle's markers carry."
  (concat (for [i (range 4)] (list 'genl (symbol (str "prt_new" i)) 'prt_material))
          '[(genl prt_new9 prt_mammal) (prtLarger prt_dog prt_ant) (prtHeavier prt_cat prt_m1)
            (prtBeside prt_m2 prt_dust)]))

(defn- goals []
  (for [r '[prtLarger prtHeavier] a terms b terms] (list r a b)))

(defn- verdicts
  "`{sentence #{goal …}}`: the goals each sentence's test moves, nil for a sentence with
  no test."
  [test-for]
  (into {} (for [s sentences]
             [s (when-let [t (test-for s)] (into #{} (filter t) (goals)))])))

(tu/deftest-kb a-shared-memo-moves-the-goals-a-memo-per-sentence-does
  (preserving-kb! kb)
  (let [alone  (verdicts #(inherit/moved-goal-test kb %))
        shared (inherit/with-memo (verdicts #(inherit/moved-goal-test kb %)))
        backwards (inherit/with-memo
                    (doseq [s (reverse sentences)] (inherit/moved-goal-test kb s))
                    (verdicts #(inherit/moved-goal-test kb %)))]
    (is (= alone shared))
    (is (= alone backwards))
    (testing "the edge into the broad type moves the goals its reach names, and no other"
      (let [g (alone '(genl prt_new0 prt_material))]
        (is (contains? g '(prtLarger prt_m0 prt_unrelated)) "a spec of the type")
        (is (contains? g '(prtLarger prt_unrelated prt_m7)) "at either position")
        (is (contains? g '(prtLarger prt_dust prt_unrelated))
            "a term a fact on a sub-predicate carries from a spec")
        (is (contains? g '(prtLarger prt_grain prt_unrelated))
            "a term a genlInverse fact carries to a spec")
        (is (not (contains? g '(prtLarger prt_dog prt_cat))) "no term of its reach")))
    (testing "a fact on the transitive predicate moves the goals naming a term its ends reach"
      (let [g (alone '(prtLarger prt_dog prt_ant))]
        (is (contains? g '(prtLarger prt_dog prt_ant)))
        (is (contains? g '(prtLarger prt_m0 prt_ant)))
        (is (not (contains? g '(prtLarger prt_m0 prt_unrelated))))))))

;; ---- the re-check --------------------------------------------------------

(tu/deftest-kb the-re-check-of-many-markers-keeps-the-firings-each-marker-keeps
  ;; a firing a marker's test keeps is kept whatever else is queued, so one memo over
  ;; every marker must keep the union of what each keeps under its own
  (preserving-kb! kb)
  (v/with-deferred-settle kb
    (doseq [[a b] '[[prt_m0 prt_dust] [prt_cat prt_ant] [prt_pebble prt_m6]]]
      (v/assert kb (list 'prtLarger a b) ctx)))
  (let [marks  (map #(hash-map ::special/preserving %) sentences)
        rhs    (into #{} (mapcat #(inherit/recheck-rules kb %)) sentences)
        queue  (fn [ms] (into {} (for [rh rhs] [rh (set ms)])))
        all    (recheck/exception-candidates kb (queue marks))
        each   (into #{} (mapcat #(recheck/exception-candidates kb (queue [%]))) marks)
        firings (into #{} (mapcat #(jtms/dependents (reasoning/tms kb) %)) rhs)]
    (is (seq rhs))
    (is (= each all))
    (is (seq all) "some firing is re-decided")
    (is (some #(< (count (recheck/exception-candidates kb (queue [%]))) (count firings)) marks)
        "and some marker leaves a firing alone")))
