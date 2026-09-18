;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.grounded-forcing-out-test
  "`jtms/grounded-forcing-out` — the belief read behind the solve-free skeptical/credulous
  bracket (`vaelii.impl.asp.label/classify-local`, docs/labeling.md) — and the backend-free
  properties of the classifier it feeds.  None of these needs an ASP backend
  (`classify-local` reads the JTMS graph directly, never `solver/available?`), so they are
  tested here rather than beside the `bravely`/`cautiously` prover, whose tests do drive the
  backend or the prover.

  Three things: that forcing a set OUT equals the engine's own `defeat` of that set; how the
  classifier's cost scales in the number of dilemmas — measured as a **call count**, a
  property of the algorithm, the way the other `*_cost_test` files measure (see
  `settle_region_cost_test`); and that it classifies the same content the same way whatever
  order the knowledge arrived in."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.asp.label :as label]
            [vaelii.impl.config :as config]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(defn- default-rule [antes conseq]
  (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence antes conseq))))

(defn- bare-rule [antes conseq]
  (list 'set/forwardRule (vr/rule-sentence antes conseq)))

(defn- one-diamond
  "A single Nixon diamond with two downstream conclusions: `ethical` from both sides,
  `opposes` from the pacifist side alone.  Returns the handles the correctness test reads."
  [kb]
  (let [q (tu/tmp-pred) pac (tu/tmp-pred) r (tu/tmp-pred)
        e (tu/tmp-pred) o (tu/tmp-pred) x (tu/tmp-ind)]
    (v/assert kb (default-rule [(list q '?x)] (list pac '?x))             'CxUniverse)
    (v/assert kb (default-rule [(list r '?x)] (list 'not (list pac '?x))) 'CxUniverse)
    (v/assert kb (bare-rule [(list pac '?x)]             (list e '?x)) 'CxUniverse)
    (v/assert kb (bare-rule [(list 'not (list pac '?x))] (list e '?x)) 'CxUniverse)
    (v/assert kb (bare-rule [(list pac '?x)]             (list o '?x)) 'CxUniverse)
    (v/assert kb (list q x) 'CxUniverse)
    (v/assert kb (list r x) 'CxUniverse)
    {:pos     (v/handle-of kb (list pac x)             'CxUniverse)
     :neg     (v/handle-of kb (list 'not (list pac x)) 'CxUniverse)
     :ethical (v/handle-of kb (list e x) 'CxUniverse)
     :opposes (v/handle-of kb (list o x) 'CxUniverse)
     :q       (v/handle-of kb (list q x) 'CxUniverse)}))

(deftest grounded-forcing-out-equals-defeat
  ;; The primitive's contract: forcing a set OUT and reading belief equals the belief the
  ;; engine's own `defeat` of that set leaves — and it drops what rests only on the set
  ;; while keeping the rest.  Runs under both TMS representations.
  (tu/with-neutral-kb [kb tu/fresh]
    (let [{:keys [pos neg ethical opposes q]} (one-diamond kb)
          tms        (reasoning/tms kb)
          extra      #{pos neg}
          via-defeat (do (jtms/defeat tms extra)
                         (let [r (set (jtms/in-datums tms))]
                           (jtms/clear-defeats! tms)   ; restore — nothing else was defeated
                           r))
          core       (jtms/grounded-forcing-out tms extra)]
      (is (= via-defeat core)
          "grounded-forcing-out equals the belief left after defeating the same set")
      (testing "the forced sides and everything resting only on a side drop out"
        (is (not (contains? core pos)))
        (is (not (contains? core neg)))
        (is (not (contains? core opposes)))   ; one-sided downstream
        (is (not (contains? core ethical))))  ; both supports gone once both sides are out
      (testing "the monotonic background survives, so the read is region-local"
        (is (contains? core q))))))

(deftest grounded-forcing-out-empty-is-belief
  ;; Forcing nothing out is the believed set unchanged.
  (tu/with-neutral-kb [kb tu/fresh]
    (one-diamond kb)
    (is (= (set (jtms/in-datums (reasoning/tms kb)))
           (jtms/grounded-forcing-out (reasoning/tms kb) #{})))))

;; ---- scaling of the classify-local bracket over N dilemmas ---------------

(defn- build-diamonds!
  "`n` rebutting dilemmas that **intersect below themselves**: every diamond concludes
  `pac(xᵢ)`/`¬pac(xᵢ)` and a both-sided `e(xᵢ)`, and a single `shared` sits below every
  diamond (concluded from each `pac(xᵢ)`), so the diamonds' forward closures overlap at it."
  [kb n]
  (let [q (tu/tmp-pred) r (tu/tmp-pred) pac (tu/tmp-pred)
        e (tu/tmp-pred) shared (tu/tmp-pred) hub (tu/tmp-ind)]
    (v/assert kb (default-rule [(list q '?x)] (list pac '?x))             'CxUniverse)
    (v/assert kb (default-rule [(list r '?x)] (list 'not (list pac '?x))) 'CxUniverse)
    (v/assert kb (bare-rule [(list pac '?x)]             (list e '?x))      'CxUniverse)
    (v/assert kb (bare-rule [(list 'not (list pac '?x))] (list e '?x))      'CxUniverse)
    (v/assert kb (bare-rule [(list pac '?x)]             (list shared hub)) 'CxUniverse)
    (dotimes [_ n]
      (let [x (tu/tmp-ind)]
        (v/assert kb (list q x) 'CxUniverse)
        (v/assert kb (list r x) 'CxUniverse)))
    kb))

(defn- classify-cost
  "Runs `classify-local` and returns how much work it did as counts: `:calls` is the number
  of `grounded-in-region` invocations and `:work` the total size of the regions they walked
  (the read is region-local, so the region is the unit of work); `:edges` is the number of
  union pairs clustering considered — the work that is *not* a region read, and where an
  all-pairs coupling test would go quadratic while the region reads stayed linear."
  [kb]
  (let [calls (atom 0), work (atom 0), edges (atom 0)
        orig-gir jtms/grounded-in-region
        orig-cl  @#'label/cluster-indices]
    (with-redefs [jtms/grounded-in-region
                  (fn [tms extra]
                    (let [res (orig-gir tms extra)]
                      (swap! calls inc)
                      (swap! work + (count (:region res)))
                      res))
                  label/cluster-indices
                  (fn [n es]
                    (let [es (vec es)]
                      (swap! edges + (count es))
                      (orig-cl n es)))]
      (label/classify-local kb))
    {:calls @calls :work @work :edges @edges}))

(deftest classify-local-scales-linearly
  ;; `classify-local` reads `grounded-in-region`, which is region-local, so the total work
  ;; is the sum of the regions walked. With N dilemmas that intersect below themselves, the
  ;; regions are bounded and the work grows **linearly** — doubling N at most doubles it —
  ;; where a per-pass belief materialization would make it quadratic (one O(believed) read
  ;; per pass, believed itself O(N)). Measured as counts (`settle_region_cost_test`).
  (let [cost (fn [n] (tu/with-neutral-kb [kb tu/fresh]
                       (build-diamonds! kb n)
                       (classify-cost kb)))
        c1   (cost 16)
        c2   (cost 64)                       ; 4x the dilemmas
        work-ratio (/ (double (:work c2)) (:work c1))
        call-ratio (/ (double (:calls c2)) (:calls c1))
        edge-ratio (/ (double (inc (:edges c2))) (inc (:edges c1)))]
    (testing "the number of region reads grows linearly in the dilemma count"
      ;; each independent dilemma is its own cluster and adds a constant number of region
      ;; reads (the all-out read, its own dep read, its resolutions' reads), so a 4x dilemma
      ;; count is ~4x the reads; a quadratic classifier would be ~16x.
      (is (< call-ratio 6.0)
          (format "call ratio %.1f (16→64 dilemmas): expected ~4x linear, quadratic would be ~16x"
                  call-ratio)))
    (testing "clustering grows linearly, not by comparing every pair of dilemmas"
      ;; the union edges come from the `touch` index, one per member per nogood it moves, so
      ;; independent dilemmas add a constant each; an all-pairs coupling test would be ~16x.
      (is (< edge-ratio 6.0)
          (format "edge ratio %.1f (16→64 dilemmas): expected ~4x linear, all-pairs would be ~16x"
                  edge-ratio)))
    (testing "region work grows no worse than linearly — a 4x dilemma count is under ~6x work"
      ;; linear predicts ~4x; the bound leaves slack. Quadratic would be ~16x and fail.
      (is (< work-ratio 6.0)
          (format "work ratio %.1f (16→64 dilemmas): expected ~4x linear, quadratic would be ~16x"
                  work-ratio)))))

;; ---- order independence of the classification ----------------------------

(defn- class-of
  "The class `cls` gives sentence `s` in `ctx` of `kb` — :true/:supportable/:false, :none
  when `s` is in no bracket (read off ordinary belief), :absent when it is not stored."
  [kb cls s ctx]
  (let [h (v/handle-of kb s ctx)]
    (cond (nil? h)                          :absent
          (contains? (:true cls) h)         :true
          (contains? (:supportable cls) h)  :supportable
          (contains? (:false cls) h)        :false
          :else                             :none)))

(deftest classify-local-is-order-independent
  ;; Belief is order-independent, so classify-local — which reads it — must classify the same
  ;; content the same way whatever order the knowledge arrived in. Handles are allocated in
  ;; assertion order and so differ per order, so the classification is compared by SENTENCE,
  ;; not by handle. The content mixes a coupled cluster (pb rebuts both pa and pc) with an
  ;; independent dilemma and its both-sided downstream conclusion.
  (let [pa (tu/tmp-pred) pb (tu/tmp-pred) pc (tu/tmp-pred)
        qd (tu/tmp-pred) rd (tu/tmp-pred) pd (tu/tmp-pred) e (tu/tmp-pred)
        x  (tu/tmp-ind) y (tu/tmp-ind)
        asserts [[(default-rule [(list pa x)] (list 'not (list pb x))) 'CxUniverse]
                 [(default-rule [(list pb x)] (list 'not (list pa x))) 'CxUniverse]
                 [(default-rule [(list pc x)] (list 'not (list pb x))) 'CxUniverse]
                 [(default-rule [(list pb x)] (list 'not (list pc x))) 'CxUniverse]
                 [(list pa x) 'CxUniverse]
                 [(list pb x) 'CxUniverse]
                 [(list pc x) 'CxUniverse]
                 [(default-rule [(list qd '?z)] (list pd '?z)) 'CxUniverse]
                 [(default-rule [(list rd '?z)] (list 'not (list pd '?z))) 'CxUniverse]
                 [(bare-rule [(list pd '?z)]             (list e '?z)) 'CxUniverse]
                 [(bare-rule [(list 'not (list pd '?z))] (list e '?z)) 'CxUniverse]
                 [(list qd y) 'CxUniverse]
                 [(list rd y) 'CxUniverse]]
        tracked [(list pa x) (list pb x) (list pc x) (list pd y) (list e y)]
        run   (fn [order]
                (tu/with-neutral-kb [kb tu/fresh]
                  (doseq [[s ctx] order] (v/assert kb s ctx))
                  (let [cls (label/classify-local kb)]
                    (into {} (map (fn [s] [s (class-of kb cls s 'CxUniverse)])) tracked))))
        base  (run asserts)]
    (testing "the coupled cluster and the independent dilemma classify as expected"
      (is (= :false       (base (list pb x))) "pb rebuts both, dropped in the one optimum")
      (is (= :true        (base (list pa x))))
      (is (= :true        (base (list pc x))))
      (is (= :supportable (base (list pd y))))
      (is (= :true        (base (list e y))) "both-sided downstream conclusion"))
    (testing "every assertion order yields the same classification by content"
      (dotimes [_ 8]
        (let [shuffled (shuffle asserts)]
          (is (= base (run shuffled))
              (str "classification differs under order " (mapv first shuffled))))))))

(deftest double-diamond-conjunction-is-order-independent
  ;; Two independent Nixon diamonds on the SAME individual, each with a both-sided conclusion
  ;; (e1, e2), plus a forward rule (e1 ?x) (e2 ?x) -> (f ?x). e1 and e2 are each :true in
  ;; their own diamond, so f — which needs both — holds in every joint resolution and is
  ;; :true too, though its support spans BOTH clusters. classify-local reaches that by
  ;; enumerating the product of the two clusters' optima. The classification is
  ;; order-independent, compared by sentence.
  (let [q1 (tu/tmp-pred) r1 (tu/tmp-pred) p1 (tu/tmp-pred) e1 (tu/tmp-pred)
        q2 (tu/tmp-pred) r2 (tu/tmp-pred) p2 (tu/tmp-pred) e2 (tu/tmp-pred)
        f  (tu/tmp-pred) x (tu/tmp-ind)
        diamond (fn [q r p e]
                  [[(default-rule [(list q '?x)] (list p '?x))             'CxUniverse]
                   [(default-rule [(list r '?x)] (list 'not (list p '?x))) 'CxUniverse]
                   [(bare-rule [(list p '?x)]             (list e '?x)) 'CxUniverse]
                   [(bare-rule [(list 'not (list p '?x))] (list e '?x)) 'CxUniverse]
                   [(list q x) 'CxUniverse]
                   [(list r x) 'CxUniverse]])
        asserts (concat (diamond q1 r1 p1 e1)
                        (diamond q2 r2 p2 e2)
                        [[(bare-rule [(list e1 '?x) (list e2 '?x)] (list f '?x)) 'CxUniverse]])
        tracked [(list p1 x) (list p2 x) (list e1 x) (list e2 x) (list f x)]
        run   (fn [order]
                (tu/with-neutral-kb [kb tu/fresh]
                  (doseq [[s ctx] order] (v/assert kb s ctx))
                  (let [cls (label/classify-local kb)]
                    (into {} (map (fn [s] [s (class-of kb cls s 'CxUniverse)])) tracked))))
        base  (run asserts)]
    (testing "each diamond's both-sided conclusion is :true, and so is their conjunction"
      (is (= :true (base (list e1 x))))
      (is (= :true (base (list e2 x))))
      (is (= :true (base (list f x)))
          "f = e1 ∧ e2 holds in every joint resolution — cross-cluster, still :true"))
    (testing "the dilemma members themselves stay credulous-only"
      (is (= :supportable (base (list p1 x))))
      (is (= :supportable (base (list p2 x)))))
    (testing "every assertion order yields the same classification by content"
      (dotimes [_ 8]
        (let [shuffled (shuffle asserts)]
          (is (= base (run shuffled))
              (str "classification differs under order " (mapv first shuffled))))))))

(defn- n-way-conjunction!
  "`n` independent Nixon diamonds on one individual, each with a both-sided `eᵢ`, and a
  single forward rule concluding `(f x)` from the conjunction of all `n` of them.  `f` joins
  all `n` clusters, so its joint-resolution product is 2ⁿ.  Returns the handle of `(f x)`."
  [kb n]
  (let [x  (tu/tmp-ind)
        es (vec (for [_ (range n)]
                  (let [q (tu/tmp-pred) r (tu/tmp-pred) p (tu/tmp-pred) e (tu/tmp-pred)]
                    (v/assert kb (default-rule [(list q '?x)] (list p '?x))             'CxUniverse)
                    (v/assert kb (default-rule [(list r '?x)] (list 'not (list p '?x))) 'CxUniverse)
                    (v/assert kb (bare-rule [(list p '?x)]             (list e '?x)) 'CxUniverse)
                    (v/assert kb (bare-rule [(list 'not (list p '?x))] (list e '?x)) 'CxUniverse)
                    (v/assert kb (list q x) 'CxUniverse)
                    (v/assert kb (list r x) 'CxUniverse)
                    e)))
        f  (tu/tmp-pred)]
    (v/assert kb (bare-rule (mapv #(list % '?x) es) (list f '?x)) 'CxUniverse)
    (v/handle-of kb (list f x) 'CxUniverse)))

(deftest cross-cluster-product-is-capped
  ;; A datum that joins MANY clusters — (f x) from the conjunction of 16 diamonds' both-sided
  ;; conclusions — has a joint-resolution product of 2^16. VAELII_CLASSIFY_MAX_JOINT_OPTIMA caps it: past
  ;; the cap f degrades to :supportable rather than enumerating exponentially, and
  ;; classify-local does bounded work. Without the cap, f alone would force 2^16 = 65536 region
  ;; reads; the guard is that the whole classification stays a small multiple of the diamond
  ;; count. Measured as a call count, like classify-local-scales-linearly.
  (tu/with-neutral-kb [kb tu/fresh]
    (let [f-h  (n-way-conjunction! kb 16)
          cost (classify-cost kb)
          cls  (label/classify-local kb)]
      (testing "f is believed — the conjunction fired from all 16 diamonds"
        (is (true? (v/in? kb f-h))))
      (testing "past the cap f is :supportable, neither enumerated :true nor :false"
        (is (contains? (:supportable cls) f-h))
        (is (not (contains? (:true cls) f-h)))
        (is (not (contains? (:false cls) f-h))))
      (testing "and classify-local does bounded work — no 2^16 blowup"
        (is (< (:calls cost) 200)
            (format "%d region reads for 16 conjoined diamonds; uncapped would be >= 65536"
                    (:calls cost)))))))

;; ---- the per-cluster caps ------------------------------------------------

(defn- coupled-cluster!
  "`b` rebuts both `a` and `c`, and each rebuts `b`: two dilemmas coupled through `b`, so one
  cluster, whose one optimal resolution defeats `b`.  Returns the handles of `a`, `b`, `c`."
  [kb]
  (let [pa (tu/tmp-pred) pb (tu/tmp-pred) pc (tu/tmp-pred) x (tu/tmp-ind)]
    (doseq [[p q] [[pa pb] [pb pa] [pc pb] [pb pc]]]
      (v/assert kb (default-rule [(list p x)] (list 'not (list q x))) 'CxUniverse))
    (doseq [p [pa pb pc]] (v/assert kb (list p x) 'CxUniverse))
    (mapv #(v/handle-of kb (list % x) 'CxUniverse) [pa pb pc])))

(deftest a-cluster-past-either-cap-is-left-supportable
  ;; classify-local enumerates a cluster's resolutions within two caps: the cluster's member
  ;; count (VAELII_CLASSIFY_MAX_CLUSTER_MEMBERS) and the candidate subsets examined
  ;; (VAELII_CLASSIFY_RESOLUTION_BUDGET).  Under the defaults the coupled cluster classifies
  ;; exactly.  Past either cap every member is :supportable, which claims neither forced nor
  ;; excluded.
  (tu/with-neutral-kb [kb tu/fresh]
    (let [[a b c] (coupled-cluster! kb)]
      (testing "under the defaults the cluster classifies exactly"
        (let [cls (label/classify-local kb)]
          (is (contains? (:true cls) a))
          (is (contains? (:true cls) c))
          (is (contains? (:false cls) b))))
      (testing "past the member cap every member is :supportable"
        (with-redefs [config/classify-max-cluster-members (constantly 1)]
          (let [cls (label/classify-local kb)]
            (is (every? (:supportable cls) [a b c])))))
      (testing "past the resolution budget every member is :supportable"
        (let [generated (atom 0)
              orig      @#'label/k-subsets]
          (with-redefs [config/classify-resolution-budget (constantly 1)
                        label/k-subsets (fn [coll k] (swap! generated inc) (orig coll k))]
            (let [cls (label/classify-local kb)]
              (is (every? (:supportable cls) [a b c]))
              (is (zero? @generated)
                  "the budget is checked against a size's binomial count before its subsets are generated"))))))))
