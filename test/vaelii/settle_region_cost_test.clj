;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.settle-region-cost-test
  "What a settle costs, as call counts rather than durations, for `assert_cost_test`'s
  reason: a count is a property of the algorithm and a millisecond a property of the
  box (docs/nmtms.md, \"The runtime of a settle\").

  * The relabelled region is materialized at most `passes + 1` times: one delay per pass
    that reads it, and one at the finish.
  * A `genl` or `genlCx` edge no standing clash depends on re-derives none of them, and a
    `genlCx` edge reads no opposed body.  The bound is zero, which cannot drift upward; a
    plain fact retracted beside each edge is the control, and `clash_oracle_test` /
    `negation_oracle_test` hold the answers.
  * A `genl` edge no `functional` or `anti_symmetric` mark stands above hands no fact
    below it to a merge derivation.
  * A definitional clash is re-asked at a reader only once the reader withdraws a ground.
  * The phase clock charges six buckets, and a settle's total is the sum of its own.
  * A settle reads the standing merges and `except`s only where they moved: a batch of
    merges reads the region once per settle, an un-merge re-examines its own class, a
    settle that moves no equality premise calls no supersession reconcile, and
    resolution's flip check reads no `except` root when the region is smaller.
  * The placement settle a `recover` closes with walks each subsumption its nogoods'
    routes climb, and each `genlCx` reach their placements see over, once per scope,
    however many nogoods share it.  A cover nogood's routes read the covers above a held
    type off the cover table and build no closure of it.  A witness walk expands a
    bounded number of nodes off its target's down-closure, and what a placement pass
    holds does not grow with the targets' down-closures.
  * Nogoods placed below their ingredients over one shared subsumption read its routes
    once per pass.
  * A nogood whose subsumption is one edge, seen where its members are or the only edge
    out of its type, is placed with no witness walk or route search, and a placement
    pass holds the routes of one batch of nogoods at a time.
  * A settle's tuple placement reads the `genl` edges' lower ends against the marks with
    one closure per marked predicate, however many edges the settle relabels."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing]]
            [clojure.walk :as walk]
            [vaelii.core :as v]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.membership :as membership]
            [vaelii.impl.decide.negation :as negation]
            [vaelii.impl.discovery :as discovery]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.settle-phases :as phases]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(def ^:private n
  "Standing dilemmas per workload, so a per-pair term shows as a three-digit count."
  60)

;; ---- how many times the region is materialized ---------------------------

(defn- region-reads
  "`jtms/touched` calls made while `f` runs.  The read is what materializes the region, so
  the read is what is counted; `jtms/revived`'s one-arity reads through this var too."
  [f]
  (let [calls (atom 0)
        orig  jtms/touched]
    (with-redefs [jtms/touched (fn [& args] (swap! calls inc) (apply orig args))]
      (f))
    @calls))

(def ^:private one-pass-reads
  "Region materializations of a one-pass settle: the finish's.  A pass forces its own
  delay only when something it reads needs the region, and a pass that owes nothing reads
  none."
  1)

(deftest a-settle-materializes-its-region-once-per-pass-and-once-at-the-finish
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        ;; one write outside the count, so no reading below is a class-loading first call
        (v/assert kb '(srm_warm SrmWarm) 'CxUniverse {})
        (testing "a plain fact — nothing derived, nothing opposed, nothing merged"
          (is (= one-pass-reads (region-reads #(v/assert kb '(srm_plain SrmA) 'CxUniverse {})))))
        (testing "a forward rule firing"
          (v/assert-rule kb ['(srm_trig ?x)] '(srm_concl ?x) 'CxUniverse {:direction :forward})
          (is (= one-pass-reads (region-reads #(v/assert kb '(srm_trig SrmB) 'CxUniverse {}))))
          (is (v/ask? kb '(srm_concl SrmB) 'CxUniverse) "the firing must have placed"))
        (testing "and a retraction"
          (let [h (v/handle-of kb '(srm_plain SrmA) 'CxUniverse)]
            (is (= one-pass-reads (region-reads #(v/retract! kb h)))))))
      (finally (tu/clear-kb! kb)))))

(deftest a-batch-is-charged-per-settle-and-not-per-write
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (v/assert kb '(srm_warm SrmWarm) 'CxUniverse {})
        (is (= one-pass-reads
               (region-reads #(v/with-deferred-settle kb
                                (dotimes [i 50]
                                  (v/assert kb (list 'srm_batch (symbol (str "SrmZ" i)))
                                            'CxUniverse {})))))))
      (finally (tu/clear-kb! kb)))))

(deftest a-defeat-takes-two-passes-and-a-revival-one
  ;; a negation pair is placed in the pass that discovers it, and the placed sentexes are
  ;; chained in a second; the target a removed defeat gives back is not re-chained, so a
  ;; revival takes one pass.  Each pass reads the region, as the finish does: the growth
  ;; term is the pass, not the belief move
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (v/assert kb '(srm_neg SrmX) 'CxUniverse {})
        (testing "the defeat takes two passes, each reading the region"
          (is (= (+ 2 one-pass-reads)
                 (region-reads #(v/assert kb '(not (srm_neg SrmX)) 'CxUniverse
                                          {:strength :monotonic}))))
          (is (not (v/ask? kb '(srm_neg SrmX) 'CxUniverse)) "the default must have lost"))
        (testing "the revival takes one pass"
          (let [h (v/handle-of kb '(not (srm_neg SrmX)) 'CxUniverse)]
            (is (= one-pass-reads (region-reads #(v/retract! kb h)))))
          (is (v/ask? kb '(srm_neg SrmX) 'CxUniverse) "the default must be believed again")))
      (finally (tu/clear-kb! kb)))))

;; ---- the clash memo ------------------------------------------------------

(defn- clash-kb
  "n individuals each holding two separated types, so the KB carries n standing
  definitional dilemmas — plus the two victims: one `genl` edge with nothing above or
  below it, and one plain fact."
  [kb]
  (v/assert kb '(disjoint srca_t srcb_t) 'CxUniverse {:strength :monotonic})
  (dotimes [i n]
    (let [x (symbol (str "SRC" i))]
      (v/assert kb (list 'srca_t x) 'CxUniverse {})
      (v/assert kb (list 'srcb_t x) 'CxUniverse {})))
  (v/assert kb '(genl srcvictim_t srctop_t) 'CxUniverse {:strength :monotonic})
  (v/assert kb '(src_plain SrcTarget) 'CxUniverse {})
  kb)

(defn- nogood-reads
  "Terms whose membership nogoods `membership/term-nogoods` derives while `f` runs: a
  settle re-derives a term's nogoods only through it."
  [f]
  (let [terms (atom [])
        orig  @#'membership/term-nogoods]
    (with-redefs [membership/term-nogoods
                  (fn [tax w c x] (swap! terms conj x) (orig tax w c x))]
      (f))
    @terms))

(deftest a-genl-edge-elsewhere-re-derives-no-standing-clash
  (let [kb (tu/fresh)]
    (try
      (clash-kb kb)
      (is (= n (count (v/contradictions kb)))
          "the standing set is standing, or the counts below are about an empty candidate index")
      (testing "retracting the lone genl edge derives no term's nogoods"
        (let [h (v/handle-of kb '(genl srcvictim_t srctop_t) 'CxUniverse)]
          (is (empty? (nogood-reads #(v/retract! kb h))))))
      (testing "and asserting it back derives none either"
        (is (empty? (nogood-reads
                     #(v/assert kb '(genl srcvictim_t srctop_t) 'CxUniverse
                                {:strength :monotonic})))))
      (testing "the control: a plain fact leaving is already free"
        (let [h (v/handle-of kb '(src_plain SrcTarget) 'CxUniverse)]
          (is (empty? (nogood-reads #(v/retract! kb h))))))
      (testing "an edge above a standing type re-derives each term holding it"
        (let [e '(genl srca_t srcabove_t)]
          (is (= n (count (set (nogood-reads #(v/assert kb e 'CxUniverse
                                                        {:strength :monotonic}))))))
          (v/retract! kb (v/handle-of kb e 'CxUniverse))))
      (is (= n (count (v/contradictions kb)))
          "and every standing dilemma is still reported")
      (finally (tu/clear-kb! kb)))))

;; ---- the negation pairs -------------------------------------------------

(defn- negation-kb
  "n P/¬P dilemmas in one context and n across two contexts a third sees, sharing no
  body, plus the two victims: one `genlCx` edge with nothing below it, and one plain fact.
  No separation, so the clash memo is not asked."
  [kb]
  (doseq [[c up] '[[CxSrL CxUniverse] [CxSrR CxUniverse] [CxSrJ CxSrL] [CxSrJ CxSrR]]]
    (v/assert kb (list 'genlCx c up) 'CxUniverse {}))
  (dotimes [i n]
    (let [pr (symbol (str "srneg" i))
          px (symbol (str "srnegx" i))
          x  (symbol (str "SRN" i))]
      (v/assert kb (list pr x) 'CxUniverse {})
      (v/assert kb (list 'not (list pr x)) 'CxUniverse {})
      (v/assert kb (list px x) 'CxSrL {})
      (v/assert kb (list 'not (list px x)) 'CxSrR {})))
  (v/assert kb '(genlCx CxSrVictim CxUniverse) 'CxUniverse {})
  (v/assert kb '(sr_plain SrTarget) 'CxUniverse {})
  kb)

(defn- body-reads
  "Opposed bodies read off the index while `f` runs: `negation/polarity-handles` is the only
  site that reads one."
  [f]
  (let [calls (atom 0)
        orig  @#'negation/polarity-handles]
    (with-redefs [negation/polarity-handles (fn [& args] (swap! calls inc) (apply orig args))]
      (f))
    @calls))

(deftest a-genlCx-edge-elsewhere-reads-no-opposed-body
  (let [kb (tu/fresh)]
    (try
      (negation-kb kb)
      (is (= (* 2 n) (count (v/contradictions kb)))
          "the standing set is standing, or the counts below are about an empty index")
      (testing "retracting the lone genlCx edge reads no body"
        (let [h (v/handle-of kb '(genlCx CxSrVictim CxUniverse)
                             'CxUniverse)]
          (is (zero? (body-reads #(do (v/retract! kb h) (v/contradictions kb)))))))
      (testing "and asserting it back reads none either"
        (is (zero? (body-reads
                    #(do (v/assert kb '(genlCx CxSrVictim CxUniverse) 'CxUniverse {})
                         (v/contradictions kb))))))
      (testing "the control: a plain fact leaving is already free"
        (let [h (v/handle-of kb '(sr_plain SrTarget) 'CxUniverse)]
          (is (zero? (body-reads #(v/retract! kb h))))))
      (is (= (* 2 n) (count (v/contradictions kb)))
          "and every standing dilemma is still reported")
      (finally (tu/clear-kb! kb)))))

;; ---- a genl edge's merge sweeps ------------------------------------------

(defn- edge-sweep-calls
  "Facts handed to the two merge derivations while `f` runs."
  [f]
  (let [calls (atom {})
        vs    [#'special/derive-functional-equalities #'special/derive-antisymmetric-equalities]]
    (with-redefs-fn (into {} (map (fn [v] (let [orig @v]
                                            [v (fn [& args]
                                                 (swap! calls update (:name (meta v)) (fnil inc 0))
                                                 (apply orig args))])))
                          vs)
      f)
    @calls))

(deftest a-genl-edge-under-no-merge-mark-re-derives-no-fact-below-it
  ;; each fact below the edge is an exact-arity membership
  (let [kb   (tu/fresh)
        m    {:strength :monotonic}
        edge (fn [top] (edge-sweep-calls
                        #(v/assert kb (list 'genl 'sre_rel top) 'CxUniverse m)))]
    (try
      (v/assert kb '(functional sreFn) 'CxUniverse m)
      (v/assert kb '(anti_symmetric sreAnti) 'CxUniverse m)
      (v/assert kb '(genl binary_predicate sre_rel) 'CxUniverse m)
      (v/assert kb '(binary_predicate sreRel0) 'CxUniverse m)
      (let [small (edge 'sre_top1)]
        (dotimes [i n]
          (v/assert kb (list 'binary_predicate (symbol (str "sreRel" (inc i)))) 'CxUniverse m))
        (is (= small (edge 'sre_top2)) "flat in the facts below the edge"))
      (finally (tu/clear-kb! kb)))))

(defn- seeds-sent
  "Chaining seeds `special/subsumption-seeds` returns while `f` runs."
  [f]
  (let [sent (atom 0)
        orig special/subsumption-seeds]
    (with-redefs [special/subsumption-seeds (fn [kb s] (let [r (orig kb s)]
                                                         (swap! sent + (count r))
                                                         r))]
      (f))
    @sent))

(deftest a-genl-edge-under-no-rule-reading-above-it-seeds-no-fact-below-it
  ;; the rule reads a predicate the edge does not reach, so the set of rule antecedent functors is not empty
  (let [kb   (tu/fresh)
        m    {:strength :monotonic}
        edge (fn [top] (seeds-sent #(v/assert kb (list 'genl 'sss_low top) 'CxUniverse m)))]
    (try
      (v/assert kb '(implies (sss_else ?x) (sss_seen ?x)) 'CxUniverse {:direction :forward})
      (v/assert kb '(sss_low SssA0) 'CxUniverse m)
      (let [small (edge 'sss_top1)]
        (dotimes [i n]
          (v/assert kb (list 'sss_low (symbol (str "SssA" (inc i)))) 'CxUniverse m))
        (is (zero? small))
        (is (zero? (edge 'sss_top2)) "flat in the facts below the edge")
        (v/assert kb '(implies (sss_top3 ?x) (sss_seen ?x)) 'CxUniverse {:direction :forward})
        (is (= (inc n) (edge 'sss_top3)) "a rule above the edge is seeded every fact below it")
        (is (seq (v/sentexes-matching kb (list 'sss_seen (symbol (str "SssA" n))) 'CxUniverse))))
      (finally (tu/clear-kb! kb)))))

;; ---- the phase clock -----------------------------------------------------

(deftest the-phase-clock-partitions-each-settle-into-its-buckets
  (let [kb (tu/fresh)]
    (try
      (phases/start)
      (v/assert kb '(srp_fact SrpA) 'CxUniverse {})
      (v/assert kb '(not (srp_fact SrpA)) 'CxUniverse {})
      (let [{:keys [run settles]} (phases/stop)]
        (is (= #{:belief :discovery :chaining :finish :glue :outside}
               (set (keys run))))
        (is (seq settles))
        (doseq [s settles]
          (is (= (:total s) (reduce + (vals (:nanos s)))))
          (is (pos? (:passes s)))))
      (finally (phases/stop) (tu/clear-kb! kb)))))

;; ---- the scans a settle runs over a standing population ---------------------

(defn- calls-to
  "Calls made to the var `v` while `f` runs, each call's arguments kept."
  [v f]
  (let [calls (atom [])
        orig  @v]
    (with-redefs-fn {v (fn [& args] (swap! calls conj args) (apply orig args))} f)
    @calls))

(defn- merge-kb
  "`kb` holding `n` standing `sameAs` merges, each displacing one fact of its own, asserted
  under one deferred settle.  Returns the displaced facts' handles."
  [kb n]
  (let [hs (volatile! [])]
    (v/with-deferred-settle kb
      (dotimes [i n]
        (vswap! hs conj (v/assert kb (list 'srmBorn (symbol (str "SrmHi" i)) 'SrmPlace)
                                  'CxUniverse {}))
        (v/assert kb (list 'sameAs (symbol (str "SrmAa" i)) (symbol (str "SrmHi" i)))
                  'CxUniverse {})))
    @hs))

(deftest a-batch-of-merges-reads-the-region-once-per-settle
  ;; the write path's supersession reconcile leaves the touched set to the batch's settle
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (v/assert kb '(srm_warm SrmWarm) 'CxUniverse {})
        (let [reads (fn [tag n]
                      (region-reads
                       #(v/with-deferred-settle kb
                          (dotimes [i n]
                            (v/assert kb (list 'srmBorn (symbol (str "SrmZ" tag i)) 'SrmPlace)
                                      'CxUniverse {})
                            (v/assert kb (list 'sameAs (symbol (str "SrmC" tag i))
                                               (symbol (str "SrmZ" tag i)))
                                      'CxUniverse {})))))]
          ;; each merge displaces its fact: `SrmC…` sorts first and represents the class
          (is (= (reads "a" 1) (reads "b" 20)))))
      (finally (tu/clear-kb! kb)))))

(deftest an-un-merge-re-examines-the-class-it-split-and-no-standing-merge
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (let [standing (set (merge-kb kb n))
              f        (v/assert kb '(srmBorn SrmVHi SrmPlace) 'CxUniverse {})
              e        (v/assert kb '(sameAs SrmVAa SrmVHi) 'CxUniverse {})
              examined (into #{} (map #(nth % 2))
                             (calls-to #'special/displacement #(v/retract! kb e)))]
          (is (contains? examined f) "the split class's own displaced fact is re-examined")
          (is (empty? (set/intersection standing examined)))
          (is (v/ask? kb '(srmBorn SrmVHi SrmPlace) 'CxUniverse)
              "the spelling the un-merge gave back is believed")))
      (finally (tu/clear-kb! kb)))))

(deftest a-settle-hands-the-belief-reconcile-no-supersession-it-did-not-move
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (let [standing (set (merge-kb kb n))
              handed   (into #{} (comp (map second) cat)
                             (calls-to #'special/reconcile-belief-change
                                       #(v/assert kb '(srm_plain SrmUnrelated) 'CxUniverse {})))]
          (is (every? #(jtms/superseded? (reasoning/tms kb) %) standing))
          (is (empty? (set/intersection standing handed)))))
      (finally (tu/clear-kb! kb)))))

(deftest a-settle-that-moves-no-equality-premise-calls-no-supersession-reconcile
  ;; the write path reconciles what a stored or removed sentence moves
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (merge-kb kb n)
        (is (empty? (calls-to #'special/refresh-supersessions
                              #(v/assert kb '(srm_plain SrmNoMerge) 'CxUniverse {}))))
        (is (empty? (calls-to #'special/refresh-supersessions
                              #(v/retract! kb (v/handle-of kb '(srm_plain SrmNoMerge)
                                                           'CxUniverse))))))
      (finally (tu/clear-kb! kb)))))

(deftest a-settle-over-standing-excepts-reads-no-except-root-when-its-region-is-smaller
  ;; no resolution defeats an `except`, so the settle reads no `except` root at all
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (dotimes [i n]
          (let [h (v/assert kb (list 'srm_decoy (symbol (str "SrmD" i))) 'CxUniverse
                            {:strength :monotonic})]
            (v/assert kb (list 'except (sx/sentex-handle h)) 'CxUniverse {:strength :monotonic})))
        (is (empty? (filter #(= sx/except-functor (second %))
                            (calls-to #'reads/believed-with-functor
                                      #(v/assert kb '(srm_plain SrmAfterExcepts) 'CxUniverse {}))))))
      (finally (tu/clear-kb! kb)))))

(deftest a-settles-loops-over-no-items-schedule-no-timer
  (let [kb      (tu/isolated-fresh)
        start   progress/start
        timer?  #(instance? java.util.concurrent.Future
                            (.get ^java.util.concurrent.atomic.AtomicReference (:timer %)))
        started (atom [])]
    (try
      (with-redefs [progress/start (fn [id label total & opts]
                                     (let [r (apply start id label total opts)]
                                       (swap! started conj [id total (timer? r)])
                                       r))]
        (v/assert kb '(srm_plain SrmNoReporter) 'CxUniverse {}))
      (let [empty-loops (filter #(= 0 (second %)) @started)]
        (is (some #(= ::settle/withdraw-retired (first %)) empty-loops))
        (is (not-any? peek empty-loops)))
      (finally (tu/clear-kb! kb)))))

;; ---- the placement settle a recover closes with -----------------------------

(deftest a-recovers-placement-settle-walks-each-subsumption-once-per-vantage
  ;; CxUniverse  (disjoint srw_a srw_b) M, srw_a2 → srw_a1 → srw_a and srw_b2 → srw_b1 →
  ;; srw_b, and n terms each in srw_a2 and srw_b2: n membership nogoods, every one placed
  ;; over the same two subsumptions from the one vantage.
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (v/with-deferred-settle kb
          (v/assert kb '(disjoint srw_a srw_b) 'CxUniverse {:strength :monotonic})
          (doseq [[s u] '[[srw_a1 srw_a] [srw_a2 srw_a1] [srw_b1 srw_b] [srw_b2 srw_b1]]]
            (v/assert kb (list 'genl s u) 'CxUniverse {}))
          (dotimes [i n]
            (let [x (symbol (str "SrwT" i))]
              (v/assert kb (list 'srw_a2 x) 'CxUniverse {})
              (v/assert kb (list 'srw_b2 x) 'CxUniverse {}))))
        (let [walks (into [] (comp (map #(vec (take 4 (rest %)))) (filter #(= :genl (first %))))
                          (calls-to #'tax/reach-support #(v/recover kb)))]
          (is (= n (count (v/sentexes-with-functor kb 'contradicts))))
          (is (= #{[:genl 'srw_a2 'srw_a 'CxUniverse] [:genl 'srw_b2 'srw_b 'CxUniverse]}
                 (set walks)))
          (is (= 2 (count walks)))))
      (finally (tu/clear-kb! kb)))))

(deftest a-recovers-placement-settle-walks-each-genlCx-reach-once
  ;; CxSrvR → CxUniverse, (disjoint srv_a srv_b) M and srv_a1 → srv_a, srv_b1 → srv_b in
  ;; CxUniverse, and n terms each in srv_a1 and srv_b1 in CxSrvR: n membership nogoods
  ;; placed in CxSrvR, each seeing its ingredients in CxUniverse over the one edge.
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (v/assert kb '(genlCx CxSrvR CxUniverse) 'CxUniverse {:strength :monotonic})
        (v/with-deferred-settle kb
          (v/assert kb '(disjoint srv_a srv_b) 'CxUniverse {:strength :monotonic})
          (v/assert kb '(genl srv_a1 srv_a) 'CxUniverse {})
          (v/assert kb '(genl srv_b1 srv_b) 'CxUniverse {})
          (dotimes [i n]
            (let [x (symbol (str "SrvT" i))]
              (v/assert kb (list 'srv_a1 x) 'CxSrvR {})
              (v/assert kb (list 'srv_b1 x) 'CxSrvR {}))))
        ;; the five-argument arity calls the six-argument one through the var
        (let [walks (into [] (comp (filter #(= 6 (count %))) (map #(vec (take 4 (rest %))))
                                   (filter #(= :genlCx (first %))))
                          (calls-to #'tax/reach-support #(v/recover kb)))]
          (is (= n (count (v/sentexes-with-functor kb 'contradicts))))
          (is (= [[:genlCx 'CxSrvR 'CxUniverse 'CxSrvR]] walks))))
      (finally (tu/clear-kb! kb)))))

(deftest a-witness-walk-expands-a-bounded-number-of-nodes-off-the-targets-down-closure
  ;; CxUniverse  srp_sub → srp_mid → srp_top, and srp_sub → srp_side_i for 300 sides, none
  ;; of them under srp_top.  The sides sort after srp_mid, so a breadth-first walk from
  ;; srp_sub reaches every side before srp_top.
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (v/with-deferred-settle kb
          (v/assert kb '(genl srp_sub srp_mid) 'CxUniverse {})
          (v/assert kb '(genl srp_mid srp_top) 'CxUniverse {})
          (dotimes [i 300]
            (v/assert kb (list 'genl 'srp_sub (symbol (str "srp_side_" i))) 'CxUniverse {})))
        (let [tx    (reasoning/taxonomy kb)
              path  (atom nil)
              sorts (count (calls-to #'nm/sort-by-content-key
                                     #(reset! path (tax/reach-support tx :genl 'srp_sub 'srp_top 'CxUniverse))))]
          (is (= [(v/handle-of kb '(genl srp_mid srp_top) 'CxUniverse)
                  (v/handle-of kb '(genl srp_sub srp_mid) 'CxUniverse)]
                 (mapv first @path)))
          (is (< sorts 100))))
      (finally (tu/clear-kb! kb)))))

(deftest a-tuple-placement-reads-genl-ends-against-the-marks-with-a-closure-per-mark
  ;; CxUniverse  srtFnSub2 → srtFnSub1 → srtFn under a `functional`, `functionalInArg` and
  ;; `irreflexive` mark, two srtFnSub2 tuples one determinant apart, and 3n `genl` edges
  ;; between collections in the same settle: the placement reads every edge's lower end.
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (let [inside? (atom false)
              walks   (atom 0)
              ends    (atom #{})
              mark    @#'chain/mark-ends
              closure @#'tax/closure-of]
          (with-redefs-fn {#'chain/mark-ends (fn [& args]
                                               (reset! inside? true)
                                               (try (let [r (apply mark args)] (swap! ends into r) r)
                                                    (finally (reset! inside? false))))
                           #'tax/closure-of  (fn [& args]
                                               (when @inside? (swap! walks inc))
                                               (apply closure args))}
            #(v/with-deferred-settle kb
               (doseq [s '[(functional srtFn) (functionalInArg srtFn 2) (irreflexive srtFn)
                           (genl srtFnSub1 srtFn) (genl srtFnSub2 srtFnSub1)]]
                 (v/assert kb s 'CxUniverse {:strength :monotonic}))
               (dotimes [i (* 3 n)]
                 (v/assert kb (list 'genl (symbol (str "srt_c" (inc i))) (symbol (str "srt_c" (quot i 3))))
                           'CxUniverse {}))
               (v/assert kb '(srtFnSub2 SrtA SrtB) 'CxUniverse {})
               (v/assert kb '(srtFnSub2 SrtA SrtC) 'CxUniverse {})))
          (is (= 1 (count (v/sentexes-with-functor kb 'contradicts))))
          (is (= '#{srtFn srtFnSub1 srtFnSub2} @ends))
          ;; one closure, the marked predicate's subtypes, where each end built its own
          (is (= 1 @walks))))
      (finally (tu/clear-kb! kb)))))

(defn- held-by-passes
  "The terms each reading pass's neighbour cache holds once its walks return
  (`tax/with-neighbours`), over the settle of `f`."
  [f]
  (let [held (atom [])
        orig @#'tax/with-neighbours]
    (with-redefs-fn {#'tax/with-neighbours
                     (fn [nc g] (let [r (orig nc g)]
                                  (swap! held conj (transduce (comp (map val) (filter coll?) (map count)) + @nc))
                                  r))}
      f)
    @held))

(deftest a-placement-pass-holds-no-targets-down-closure
  ;; CxUniverse  (disjoint sha_top_t sha_other) on 3 tops, each over `fans` types of its
  ;; own, sha_mid under every top, and 2 types under sha_mid and under 70 sides that sort
  ;; after it, each holding a term also in sha_other: every route walk from one passes its
  ;; first 64 expansions and prunes, and what the pass holds does not grow with the fans.
  (let [held (fn [fans]
               (let [kb (tu/isolated-fresh)
                     m  {:strength :monotonic}]
                 (try
                   (tu/with-shipped-config
                     (let [h (held-by-passes
                              #(v/with-deferred-settle kb
                                 (dotimes [t 3]
                                   (let [top (symbol (str "sha_top" t))]
                                     (v/assert kb (list 'disjoint top 'sha_other) 'CxUniverse m)
                                     (v/assert kb (list 'genl 'sha_mid top) 'CxUniverse m)
                                     (dotimes [j fans]
                                       (v/assert kb (list 'genl (symbol (str "sha_top" t "_f" j)) top) 'CxUniverse m))))
                                 (dotimes [i 2]
                                   (let [q (symbol (str "sha_q" i))
                                         x (symbol (str "ShaX" i))]
                                     (v/assert kb (list 'genl q 'sha_mid) 'CxUniverse m)
                                     (dotimes [j 70]
                                       (v/assert kb (list 'genl q (symbol (str "sha_side" j))) 'CxUniverse m))
                                     (v/assert kb (list q x) 'CxUniverse {})
                                     (v/assert kb (list 'sha_other x) 'CxUniverse {})))))]
                       [(count (v/sentexes-with-functor kb 'contradicts)) (reduce + h)]))
                   (finally (tu/clear-kb! kb)))))
        [n10 w10] (held 10)
        [n40 w40] (held 40)]
    (is (pos? n10))
    (is (= n10 n40))
    (is (= w10 w40) (str w10 " terms held over 10 fans, " w40 " over 40"))))

(deftest the-cover-routes-of-a-held-type-build-no-closure-of-it
  ;; a held type under two types of a braid of 20 levels of four types below a root, a
  ;; cover over the root with both parts denied: the route reads the covers above the
  ;; held type off the cover table, so no type of the braid holds a closure after the read
  (let [t    (tax/create-taxonomy)
        h    (atom 0)
        add  #(tax/add-genl t %1 %2 (swap! h inc))
        node #(symbol (str "crb_" %1 "_" %2))]
    (dotimes [j 4] (add (node 0 j) 'crbroot))
    (doseq [i (range 1 20) j (range 4)]
      (add (node i j) (node (dec i) j))
      (add (node i j) (node (dec i) (mod (inc j) 4))))
    (add 'crbleaf (node 19 0))
    (add 'crbleaf (node 19 1))
    (tax/add-cover t 'crbroot '[crbpa crbpb] :covering (swap! h inc))
    (let [routes ((deref #'membership/cover-routes) (decide/unscoped-closures t)
                                                    '#{crbleaf} '#{crbpa crbpb})
          held   (fn [n] (caches/lru-get (:closure-lru @t) [:genl (:gen (:genl @t)) :fwd n]))]
      (is (= [{:keys #{[:cover '[crbroot [crbpa crbpb]] :covering]} :links '[[crbleaf crbroot]]}]
             (vec routes)))
      (is (not-any? held (list* 'crbleaf 'crbroot (for [i (range 20) j (range 4)] (node i j))))))))

(deftest descent-placements-over-a-shared-subsumption-read-its-routes-once
  ;; CxSrdD → CxUniverse, (disjoint srd_top srd_other) and n terms each in srd_q and
  ;; srd_other in CxUniverse, and (genl srd_q srd_top) in CxSrdD alone: CxUniverse sees no
  ;; route, so each of the n membership nogoods is placed below it, in CxSrdD, over the
  ;; one subsumption.
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (v/assert kb '(genlCx CxSrdD CxUniverse) 'CxUniverse {:strength :monotonic})
        (let [searches (count (calls-to #'tax/reach-supports
                                        #(v/with-deferred-settle kb
                                           (v/assert kb '(disjoint srd_top srd_other) 'CxUniverse {:strength :monotonic})
                                           (v/assert kb '(genl srd_q srd_top) 'CxSrdD {:strength :monotonic})
                                           (dotimes [i n]
                                             (let [x (symbol (str "SrdA" i))]
                                               (v/assert kb (list 'srd_q x) 'CxUniverse {})
                                               (v/assert kb (list 'srd_other x) 'CxUniverse {}))))))
              placed   (v/sentexes-with-functor kb 'contradicts)]
          (is (= n (count placed)))
          (is (every? #(= 'CxSrdD (:context %)) placed))
          ;; one search per placement pass that reads them, where each nogood read its own
          (is (<= searches 2) (str searches " route searches for " n " nogoods"))))
      (finally (tu/clear-kb! kb)))))

(defn- descent-world!
  "In one deferred settle, SrX in sr_other and in `n` types under each of three shapes of
  subsumption to a type disjoint from sr_other: `sra_q_i` with one edge to sra_top in
  CxUniverse, `srb_q_i` with its only edge, to srb_top, in CxSrbD, and `src_q_i` over
  src_mid in CxSrbD.  CxUniverse sees the first edge, so those nogoods place there; it
  sees neither of the others, so those descend to CxSrbD.  The nogoods are all SrX's, so
  one placement pass reads them."
  [kb n]
  (let [m {:strength :monotonic}]
    (v/assert kb '(genlCx CxSrbD CxUniverse) 'CxUniverse m)
    (v/with-deferred-settle kb
      (doseq [top '[sra_top srb_top src_top]] (v/assert kb (list 'disjoint top 'sr_other) 'CxUniverse m))
      (v/assert kb '(genl src_mid src_top) 'CxSrbD m)
      (v/assert kb '(sr_other SrX) 'CxUniverse {})
      (dotimes [i n]
        (let [[a b c] (map #(symbol (str % i)) ["sra_q" "srb_q" "src_q"])]
          (v/assert kb (list 'genl a 'sra_top) 'CxUniverse m)
          (v/assert kb (list 'genl b 'srb_top) 'CxSrbD m)
          (v/assert kb (list 'genl c 'src_mid) 'CxSrbD m)
          (doseq [q [a b c]] (v/assert kb (list q 'SrX) 'CxUniverse {})))))))

(deftest a-placement-over-one-edge-runs-no-witness-walk-or-route-search
  (let [kb (tu/isolated-fresh)
        k  20]
    (try
      (tu/with-shipped-config
        (let [walks    (atom {})
              count-in (fn [v k] (let [orig @v] [v (fn [& args] (swap! walks update k (fnil inc 0)) (apply orig args))]))]
          (with-redefs-fn (into {} [(count-in #'tax/bfs-witness-path :bfs) (count-in #'tax/uncovered-routes :search)])
            #(descent-world! kb k))
          (let [placed (v/sentexes-with-functor kb 'contradicts)]
            (is (= (* 3 k) (count placed)))
            (is (= {'CxUniverse k 'CxSrbD (* 2 k)} (frequencies (map :context placed)))))
          ;; CxUniverse sees no edge out of srb_q_i or src_q_i, and src_q_i's routes climb two
          ;; edges, so its search alone is run
          (is (zero? (get @walks :bfs 0)) (str @walks))
          (is (= k (get @walks :search 0)) (str @walks))))
      (finally (tu/clear-kb! kb)))))

(deftest a-placement-pass-holds-the-routes-of-one-batch
  (let [kb      (tu/isolated-fresh)
        k       20
        open    (atom 0)
        most    (atom 0)
        batch   (resolve 'vaelii.impl.chain/plan-batch)
        planned @#'chain/route-placements
        written @#'chain/place-justified!]
    (try
      (tu/with-shipped-config
        (with-redefs-fn (cond-> {#'chain/route-placements (fn [& args] (swap! most max (swap! open inc)) (apply planned args))
                                 #'chain/place-justified! (fn [& args] (swap! open dec) (apply written args))}
                          batch (assoc batch 8))
          #(descent-world! kb k))
        (is (= (* 3 k) (count (v/sentexes-with-functor kb 'contradicts))))
        (is (<= @most 8) (str @most " nogoods planned and unwritten at once")))
      (finally (tu/clear-kb! kb)))))

(defn- strict-ladder
  "In one deferred settle, `depth` levels of three types between `<pre>_leaf` and
  `<pre>_top` in CxUniverse, each type with `genl` edges at `strength` to two of the
  level above, and SlX in `<pre>_leaf` denied `<pre>_top`: a `:supertype` nogood whose
  one link is a strict one.  `[contradicts placed, holding-class reads]`."
  [pre depth strength]
  (let [kb    (tu/isolated-fresh)
        reads (atom 0)
        orig  @#'res/holding-class
        n     #(symbol (str pre "_" %1 "_" %2))
        e!    #(v/assert kb (list 'genl %1 %2) 'CxUniverse {:strength strength})]
    (try
      (tu/with-shipped-config
        (with-redefs-fn {#'res/holding-class (fn [kb] (let [f (orig kb)] (fn [h] (swap! reads inc) (f h))))}
          #(v/with-deferred-settle kb
             (dotimes [j 3]
               (e! (n 1 j) (symbol (str pre "_top")))
               (e! (symbol (str pre "_leaf")) (n depth j)))
             (doseq [i (range 2 (inc depth)) j (range 3)]
               (e! (n i j) (n (dec i) j))
               (e! (n i j) (n (dec i) (mod (inc j) 3))))
             (v/assert kb (list (symbol (str pre "_leaf")) 'SlX) 'CxUniverse {})
             (v/assert kb (list 'not (list (symbol (str pre "_top")) 'SlX)) 'CxUniverse {})))
        [(count (v/sentexes-with-functor kb 'contradicts)) @reads])
      (finally (tu/clear-kb! kb)))))

(deftest a-strict-link-walks-no-default-edge
  (let [[n4 r4]   (strict-ladder "slw" 4 :default)
        [n16 r16] (strict-ladder "slw" 16 :default)
        [m4 _]    (strict-ladder "slm" 4 :monotonic)
        [m16 _]   (strict-ladder "slm" 16 :monotonic)]
    (is (= [0 0 1 1] [n4 n16 m4 m16]))
    (is (= r4 r16) (str r4 " holding-class reads at depth 4, " r16 " at 16"))))

(defn- placement-digest
  "Every placed `contradicts` and `defeat` of `kb`: sentence, context, belief, and each
  justification's informant and antecedents, by content."
  [kb]
  (let [tms (reasoning/tms kb)
        ct  (fn [h] (let [s (p/get-sentex (:records kb) h)] (pr-str [(:sentence s) (:context s)])))]
    (sort (for [f '[contradicts defeat] s (v/sentexes-with-functor kb f)]
            (pr-str [(ct (:id s)) (v/in? kb (:id s))
                     (sort (map (fn [j] (let [j (jtms/justification tms j)]
                                          (pr-str [(:informant j) (sort (map ct (:antecedents j)))])))
                                (jtms/supports tms (:id s))))])))))

(deftest the-shortcuts-and-batches-place-what-the-whole-plan-and-the-walks-place
  ;; the world above, two supporters on some edges and a second route on some, placed
  ;; with every shortcut and a batch of 4, and with the walks taken and one plan
  (let [world! (fn [kb]
                 (descent-world! kb 12)
                 (v/with-deferred-settle kb
                   (dotimes [i 6]
                     (v/assert kb (list 'genl (symbol (str "sra_q" i)) 'sra_top) 'CxSrbD {})
                     (v/assert kb (list 'genl (symbol (str "srb_q" i)) 'src_mid) 'CxUniverse {:strength :monotonic}))))
        run    (fn [redefs]
                 (let [kb (tu/isolated-fresh)]
                   (try
                     (tu/with-shipped-config
                       (with-redefs-fn redefs #(world! kb))
                       (placement-digest kb))
                     (finally (tu/clear-kb! kb)))))
        batch  (resolve 'vaelii.impl.chain/plan-batch)
        direct (resolve 'vaelii.impl.taxonomy/direct-witness)
        every  (resolve 'vaelii.impl.taxonomy/every-uncovered-route)
        plain  (run (cond-> {}
                      direct (assoc direct (constantly nil))
                      every  (assoc every @#'tax/uncovered-routes)
                      batch  (assoc batch Integer/MAX_VALUE)))]
    (is (= 36 (count plain)))
    (is (= plain (run (cond-> {} batch (assoc batch 4)))))))

(defn- hub-world!
  "In one deferred settle: `nl_a` and `nl_b` disjoint, `nl_z` under `nl_hub` with
  `nl_zs` under it at `:monotonic`, and `nl_s1` under `nl_s0`.  Each of `n` terms NlX_i holds `nl_zs`
  beside an `nl_a` and an `nl_b` membership, one `:disjoint` nogood that names no type
  at or below `nl_z`.  NlW holds `nl_zs` and is denied `nl_hub`, a `:supertype` nogood
  no `:monotonic` path places, and NlY holds `nl_zs` and is denied `nl_s0`."
  [kb n]
  (let [m {:strength :monotonic}]
    (v/with-deferred-settle kb
      (v/assert kb '(disjoint nl_a nl_b) 'CxUniverse m)
      (doseq [[s t] '[[nl_a1 nl_a] [nl_b1 nl_b] [nl_s1 nl_s0] [nl_z nl_hub]]]
        (v/assert kb (list 'genl s t) 'CxUniverse {}))
      (v/assert kb '(genl nl_zs nl_z) 'CxUniverse m)
      (dotimes [i n]
        (let [x (symbol (str "NlX" i))]
          (doseq [t '[nl_a1 nl_b1 nl_zs]] (v/assert kb (list t x) 'CxUniverse {}))))
      (doseq [[x q] '[[NlW nl_hub] [NlY nl_s0]]]
        (v/assert kb (list 'nl_zs x) 'CxUniverse {})
        (v/assert kb (list 'not (list q x)) 'CxUniverse {})))))

(defn- edge-placements
  "The member sets `chain/route-placements` reads while `(genl nl_z nl_s1)` is added to
  `hub-world!` over `n` terms, as `[sets contradicts]`."
  [n]
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (hub-world! kb n)
        (let [sets (atom [])
              orig @#'chain/route-placements
              term #(into #{} (map (fn [h] (let [s (:sentence (p/get-sentex (:records kb) h))]
                                             (second (if (sx/negation? s) (second s) s)))))
                          %)]
          (with-redefs-fn {#'chain/route-placements (fn [kb ms routes within]
                                                      (swap! sets conj (term ms))
                                                      (orig kb ms routes within))}
            #(v/edit! kb {:add [['(genl nl_z nl_s1) 'CxUniverse]]}))
          [(frequencies @sets) (count (v/sentexes-with-functor kb 'contradicts))]))
      (finally (tu/clear-kb! kb)))))

(deftest a-genl-edge-places-again-only-the-nogoods-under-its-lower-end
  (let [[s8 c8]   (edge-placements 8)
        [s16 c16] (edge-placements 16)]
    (is (= '{#{NlW} 1 #{NlY} 1} s8 s16))
    (is (= [8 16] [c8 c16]))))

(defn- store-digest
  "Every stored sentex of `kb` as `[sentence context strength in?]`, a `(sentexHandle h)`
  in a sentence read as the sentence and context it names, sorted."
  [kb]
  (let [recs (:records kb)
        named (fn named [s]
                (walk/postwalk #(if-let [h (and (seq? %) (sx/handle-id %))]
                                  (let [t (p/get-sentex recs h)] [(named (:sentence t)) (:context t)])
                                  %)
                               s))]
    (sort (map (fn [h] (let [s (p/get-sentex recs h)]
                         (pr-str [(named (:sentence s)) (:context s) (:strength s) (v/in? kb h)])))
               (p/sentex-ids recs)))))

(deftest a-genl-edge-narrowed-to-its-lower-end-places-what-every-nogood-placed-again-does
  (let [ladder! (fn [kb pre strength]
                  (let [n #(symbol (str pre "_" %1 "_" %2))
                        e! #(v/assert kb (list 'genl %1 %2) 'CxUniverse {:strength strength})]
                    (v/with-deferred-settle kb
                      (dotimes [j 2]
                        (e! (n 1 j) (symbol (str pre "_top")))
                        (e! (symbol (str pre "_leaf")) (n 3 j)))
                      (doseq [i [2 3] j (range 2)]
                        (e! (n i j) (n (dec i) j))
                        (e! (n i j) (n (dec i) (mod (inc j) 2))))
                      (v/assert kb (list (symbol (str pre "_leaf")) 'NlX0) 'CxUniverse {})
                      (v/assert kb (list 'not (list (symbol (str pre "_top")) 'NlX0)) 'CxUniverse {}))))
        mono    {:strength :monotonic}
        steps   [{:add [['(genl nl_z nl_s1) 'CxUniverse] ['(genl nld_3_0 nl_a) 'CxUniverse]]}
                 {:add [['(genl nl_z nl_mid) 'CxUniverse mono] ['(genl nl_mid nl_hub) 'CxUniverse mono]]}
                 {:add [['(genl nl_s0 nl_a) 'CxUniverse] ['(genl nlm_2_1 nl_b) 'CxUniverse]]}
                 {:remove [['(genl nld_2_0 nld_1_0) 'CxUniverse] ['(genl nl_zs nl_z) 'CxUniverse]]}
                 {:add [['(genl nl_zs nl_z) 'CxUniverse] ['(genl nlm_1_0 nl_hub) 'CxUniverse]
                        ['(nl_s0 NlX2) 'CxUniverse]]}
                 {:remove [['(genl nl_z nl_s1) 'CxUniverse]]}]
        run     (fn [redefs]
                  (let [kb (tu/isolated-fresh)]
                    (try
                      (tu/with-shipped-config
                        (with-redefs-fn redefs
                          (fn []
                            (hub-world! kb 4)
                            (ladder! kb "nld" :default)
                            (ladder! kb "nlm" :monotonic)
                            (let [h (v/handle-of kb '(nl_a1 NlX1) 'CxUniverse)]
                              (v/assert kb (list 'except (list 'sentexHandle h)) 'CxUniverse {}))
                            (mapv (fn [step]
                                    (v/edit! kb (update step :remove
                                                        (fn [rs] (mapv (fn [[s c]] (v/handle-of kb s c)) rs))))
                                    [(store-digest kb) (placement-digest kb)])
                                  steps))))
                      (finally (tu/clear-kb! kb)))))
        whole   (some-> (resolve 'vaelii.impl.decide.membership/reaches-lows?)
                        (vector (constantly true)))
        narrow  (run {})]
    (is (some #(seq (second %)) narrow))
    (is (= narrow (run (into {} (when whole [whole])))))))

(defn- clash-world!
  "In one deferred settle, every sentence `:monotonic`: `nr_red`, preserved along
  `nrPartOf`, `disjoint` from `nr_wheel`, and the claim `(nr_red NrCar)` reaching each of
  `n` members NrW_i of `nr_wheel` through `(nrPartOf NrW_i NrCar)`, `n` clashes of a
  separated membership.  `nrCap` preserved at argument 1 against `genl` and `nr_up` along
  it; `n` claims `(nrCap nr_s0 NrH_i)` above `nr_s1`, and `nr_zs` under `nr_z` under
  `nr_hub`, holding `(not (nrCap nr_zs NrH0))`, `(nr_up nr_zs)` and the member `NrZm`,
  part of `NrCar`.  `nr_s0` is denied `nr_up` at `:default`."
  [kb n]
  (let [m {:strength :monotonic}
        a! #(v/assert kb %1 'CxUniverse (or %2 m))]
    (v/with-deferred-settle kb
      (doseq [s '[(transitive nrPartOf) (binary_predicate nrCap) (transitiveInArgInverse nr_red 1 nrPartOf)
                  (transitiveInArgInverse nrCap 1 genl) (transitiveInArg nr_up 1 genl)
                  (genl nr_wheel thing) (genl nr_hub thing) (genl nr_s0 thing) (genl nr_s1 nr_s0)
                  (genl nr_z nr_hub) (genl nr_zs nr_z) (disjoint nr_red nr_wheel) (nr_red NrCar)
                  (nr_up nr_zs) (nr_zs NrZm) (nrPartOf NrZm NrCar)]]
        (a! s nil))
      (a! '(not (nrCap nr_zs NrH0)) {})
      (a! '(not (nr_up nr_s0)) {})
      (dotimes [i n]
        (let [w (symbol (str "NrW" i))]
          (a! (list 'nrPartOf w 'NrCar) nil)
          (a! (list 'nr_wheel w) nil)
          (a! (list 'nrCap 'nr_s0 (symbol (str "NrH" i))) nil))))))

(defn- edge-questions
  "The `preserving-entry` calls the settle of `(genl nr_z nr_s1)` makes over `clash-world!`
  of `n`, and the `contradicts` stored before and after it."
  [n]
  (let [kb    (tu/isolated-fresh)
        calls (atom 0)
        orig  @#'discovery/preserving-entry
        ct    #(count (v/sentexes-with-functor kb 'contradicts))]
    (try
      (tu/with-shipped-config
        (clash-world! kb n)
        (let [before (ct)]
          (with-redefs [discovery/preserving-entry (fn [kb s] (swap! calls inc) (orig kb s))]
            (v/edit! kb {:add [['(genl nr_z nr_s1) 'CxUniverse {:strength :monotonic}]]}))
          [@calls before (ct)]))
      (finally (tu/clear-kb! kb)))))

(deftest a-genl-edge-asks-no-clash-whose-reach-it-does-not-cross
  (let [[q8 b8 a8]    (edge-questions 8)
        [q32 b32 a32] (edge-questions 32)]
    (is (= q8 q32) (str "questions per settle " [q8 q32]))
    (is (= [8 32] [b8 b32]))
    (is (= [10 34] [a8 a32]))))

(defn- preserved-digest
  "Every inherited clash `kb`'s memo holds, by content: the stored claim, the members,
  the vantages and the priority."
  [kb]
  (let [ct #(let [s (p/get-sentex (:records kb) %)] (pr-str [(:sentence s) (:context s)]))]
    (sort (for [[h e] (:entries @(reasoning/preserved-clashes kb)), ng (:nogoods e)]
            (pr-str [(ct h) (sort (map ct (:nogood ng))) (sort (:vantages ng)) (:priority ng)])))))

(deftest a-genl-edge-narrowed-by-its-crossing-finds-the-clashes-every-question-asked-again-finds
  (let [m     {:strength :monotonic}
        steps [{:add [['(genl nr_z nr_s1) 'CxUniverse m] ['(nrCap nrl_d_2 NrH1) 'CxUniverse m]]}
               {:add [['(genl nr_hub nr_wheel) 'CxUniverse m] ['(genl nrl_m_2 nr_s1) 'CxUniverse m]]}
               {:add [['(genl nrl_d_0 nr_zs) 'CxUniverse] ['(nr_up nrl_m_0) 'CxUniverse m]]}
               {:remove [['(genl nr_hub nr_wheel) 'CxUniverse] ['(genl nrl_d_1 nrl_d_2) 'CxUniverse]]}
               {:remove [['(genl nr_z nr_s1) 'CxUniverse]]}
               {:add [['(genl nr_hub nr_wheel) 'CxUniverse m] ['(except (sentexHandle 0)) 'CxUniverse m]]}
               {:add [['(genl nr_z nr_s1) 'CxUniverse m] ['(genl nrl_d_1 nrl_d_2) 'CxUniverse]]}
               {:remove [['(genl nrl_m_1 nrl_m_2) 'CxUniverse]]}]
        run   (fn [redefs]
                (let [kb (tu/isolated-fresh)]
                  (try
                    (tu/with-shipped-config
                      (with-redefs-fn redefs
                        (fn []
                          (clash-world! kb 3)
                          (doseq [[pre strength] [["nrl_d" :default] ["nrl_m" :monotonic]]
                                  :let [t #(symbol (str pre "_" %))]]
                            (v/with-deferred-settle kb
                              (dotimes [i 2]
                                (v/assert kb (list 'genl (t i) (t (inc i))) 'CxUniverse {:strength strength}))
                              (v/assert kb (list 'genl (t 2) 'nr_s0) 'CxUniverse {:strength strength})
                              (v/assert kb (list 'nrCap (t 2) 'NrH2) 'CxUniverse {:strength strength})
                              (v/assert kb (list 'not (list 'nrCap (t 0) 'NrH2)) 'CxUniverse {})
                              (v/assert kb (list 'not (list 'nr_up (t 2))) 'CxUniverse {})))
                          (let [claim (v/handle-of kb '(nr_red NrCar) 'CxUniverse)]
                            (mapv (fn [step]
                                    (v/edit! kb (-> step
                                                    (update :add (fn [as] (mapv #(update % 0 (partial walk/postwalk-replace {0 claim})) as)))
                                                    (update :remove (fn [rs] (mapv (fn [[s c]] (v/handle-of kb s c)) rs)))))
                                    [(store-digest kb) (placement-digest kb) (preserved-digest kb)])
                                  steps)))))
                    (finally (tu/clear-kb! kb)))))
        off   (into {} (keep (fn [[sym f]] (some-> (resolve sym) (vector f))))
                    {'vaelii.impl.inherit/edge-terms
                     (fn [kb a b _ _ ns]
                       (let [tax (reasoning/taxonomy kb)
                             ts  (into (tax/specs-global tax a) (tax/genls-global tax b))]
                         (zipmap ns (repeat ts))))
                     'vaelii.impl.discovery/separated-under
                     (fn [_ _ _ sep _] sep)})
        narrow (run {})]
    (is (some #(seq (nth % 2)) narrow))
    (is (= narrow (run off)))))
