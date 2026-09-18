;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.limit-alloc-cost-test
  "What a **caller-parameterized** reader allocates, as a counted invariant: the claim is
  that a bounded read costs what it *matched* and never what it was *asked for*.

  A reader taking a `:limit` is handed a number by whoever called it, and on the web that
  whoever is a URL.  The browser's result list computes its bound from a query-string
  parameter (`web/find-rows-page`: `limit = offset + find-cap + 1`), so
  `GET /find/rows?q=M&offset=200000000` reaches `core/find-terms` asking for two hundred
  million of a KB that may hold one hit — and `offset=2000000000` for ten times that.
  It is not a browser-only reach either: `:find-terms` is a daemon RPC op and a model
  tool, so that number arrives from three directions and is trusted from none of them.

  A container sized on such a number allocates at *construction*: `java.util.PriorityQueue
  (int)` builds its backing array before a single element is offered, so 200,000,201
  would be an 840 MB array to return one term and 2,000,000,201 would be ~8.4 GB.  That
  is why `core/smallest-n`'s heap takes a small initial capacity and grows into the
  answer instead — a few doublings in the case where the hits really do run to the bound,
  and nothing at all in the case the bound exists for.

  **The property, not the bytes**, is what this file pins: the slope of allocation in the
  requested bound is zero, and the slope in the matched set is not.  Two arms, one per
  reader, and a control beside each.

  ## Why allocation, and why a slope

  Allocation is the read-path quantity that behaves the way retained heap does — a
  property of the code and the corpus rather than of the box — which is
  `bench/vaelii/bench/alloc.clj`'s argument for measuring trie walks in bytes instead of
  milliseconds, and the same instrument answers here:
  `com.sun.management.ThreadMXBean/getCurrentThreadAllocatedBytes`, exact to the byte
  across a region bounded by two reads on one thread, needing no agent and no instrumentation in the
  engine.  That harness is on the `:bench` source path, which `lein test` does not carry,
  so the few lines below are the instrument and not a copy of its analysis; the reasoning
  it records about escape analysis, warm-up and what the counter cannot see is the
  reasoning here.

  The **absolute** byte figure is a property of the corpus — the roster filter dominates
  it — so it is not what is pinned.  A slope is: bytes per unit of requested bound, as an
  integer, and the number is **0**.  The defect reads 4 (one compressed reference per
  requested element), which is what an `Object[]` costs and what the floor of a
  four-byte-per-unit slope makes visible at any size.  A budget of zero is also the one
  number that cannot drift quietly upward.

  ## What it does not catch

  - **A cost that is not an allocation.**  A bound the reader spends *time* on without
    allocating — a loop to the requested limit over an empty answer — is invisible here.
  - **A caller that clamps before the engine sees it.**  This measures the engine's
    readers, so a bound the browser fixed on its way in is not being tested.
  - **Anything about the answer.**  `find_terms_test` holds what a bounded search
    *returns*; the arms below re-check the answer only so far as proving they ran."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.test-util :as tu])
  (:import [com.sun.management ThreadMXBean]
           [java.lang.management ManagementFactory]))

;; ---- the instrument ------------------------------------------------------

(def ^:private ^ThreadMXBean thread-mx (ManagementFactory/getThreadMXBean))

(defn- allocated
  "Bytes this thread has allocated so far."
  ^long []
  (.getCurrentThreadAllocatedBytes thread-mx))

;; A live sink for each pass's answer, so nothing measured can be dead code.  Written
;; after the closing read, so the write is outside the measured region.
(def ^:private sink (volatile! nil))

(def ^:private warm-passes
  "Unmeasured passes before the first reading.  Escape analysis runs only once a path is
  hot and what it does is *remove* allocations, so a cold arm reads high — and both arms
  here warm by the same count, which is `bench/perf.clj`'s hardest-won rule applied to
  bytes: warming one arm more hands it an optimizer the other never got."
  4)

(def ^:private samples 8)

(defn- alloc-bytes
  "The smallest allocation `f` costs over `samples` measured passes, after `warm-passes`
  unmeasured ones.  The **minimum** rather than a mean: every pass allocates the same
  structural bytes and anything above that floor is a class load, a resize of something
  outside the region, or a lazy seq another pass had already realized."
  ^long [f]
  (dotimes [_ warm-passes] (f))
  (reduce min (repeatedly samples
                          (fn [] (let [a (allocated), r (f), b (allocated)]
                                   (vreset! sink r)
                                   (- b a))))))

(defn- bytes-per-requested-unit
  "Allocation's slope in the requested bound: the extra bytes the larger request cost,
  divided by how much larger it was, floored to a whole byte.

  `max 0` because the two arms are not obliged to be equal — a larger bound may cost
  *less*, and does on the paging arm, where the page past the end renders nothing — and a
  negative slope is not a smaller claim than a zero one.  What the claim rules out is
  allocation that *tracks* the request, and the smallest such slope worth naming is one
  byte per unit."
  ^long [^long small-bytes ^long large-bytes ^long span]
  (quot (max 0 (- large-bytes small-bytes)) span))

;; ---- the corpus ----------------------------------------------------------

(def ^:private vocabulary
  "Terms in the roster the readers filter.  Big enough that the filter is the reading's
  dominant term — which is the honest baseline, since that is what a search really costs
  — and small enough that building it is a second."
  600)

(def ^:private needle
  "The query, and it matches exactly one term of the corpus below.  A single hit is the
  case the defect is about: the answer is one element and the request is eight million."
  "Zq")

(defn- corpus!
  "`vocabulary` individuals of one predicate, of which exactly one carries `needle` in its
  name.  `:chain? false` throughout — no rule exists to fire, and the reading is about a
  read path rather than about how the KB was filled."
  [kb]
  (dotimes [i vocabulary]
    (v/assert kb (list 'lacRel (symbol (str "LacInd" i)) i) 'CxUniverse {:chain? false}))
  (v/assert kb '(lacRel LacNeedleZq 1) 'CxUniverse {:chain? false})
  kb)

(defn- more-needles!
  "Widen the matched set without widening the roster much: `n` further terms carrying
  `needle`.  The control's fixture — a reader whose allocation is bounded by the answer
  must move when the *answer* does, or the arms above are measuring a constant."
  [kb n]
  (dotimes [i n]
    (v/assert kb (list 'lacRel (symbol (str "LacZq" i)) i) 'CxUniverse {:chain? false}))
  kb)

;; ---- the reader taking a :limit ------------------------------------------

(def ^:private small-limit 1024)
(def ^:private large-limit 8000000)

(defn- find-terms-bytes
  "Bytes one `find-terms` bounded at `limit` allocates over `kb`."
  ^long [kb ^long limit]
  (alloc-bytes #(count (v/find-terms kb needle {:match :substring
                                                :case-sensitive? true
                                                :limit limit}))))

(deftest find-terms-allocates-for-the-hits-not-for-the-limit
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (corpus! kb)
        (is (= 1 (count (v/find-terms kb needle {:match :substring :case-sensitive? true})))
            "the corpus must hold exactly one hit, or the arms below are about a real answer")
        (let [small (find-terms-bytes kb small-limit)
              large (find-terms-bytes kb large-limit)
              span  (- large-limit small-limit)]
          (testing "the answer is the same one hit at either bound"
            (is (= (v/find-terms kb needle {:match :substring :case-sensitive? true
                                            :limit small-limit})
                   (v/find-terms kb needle {:match :substring :case-sensitive? true
                                            :limit large-limit}))))
          (testing "and asking for 8 million of it costs not one byte per element asked for"
            (is (zero? (bytes-per-requested-unit small large span))
                (str "allocation tracks the requested bound — a caller's :limit is sizing "
                     "something: " small " B at :limit " small-limit " against " large
                     " B at :limit " large-limit)))
          (testing "the control: the matched set is what moves it"
            (more-needles! kb 1000)
            (is (= 1001 (count (v/find-terms kb needle {:match :substring
                                                        :case-sensitive? true}))))
            (is (< large (find-terms-bytes kb large-limit))
                "1000 more hits at the same bound must cost more, or the instrument is
                 reading a constant and the arms above prove nothing"))))
      (finally (tu/clear-kb! kb)))))

;; ---- the paging reader, whose bound is a URL parameter -------------------
;;
;; `web/find-rows-page` is the same shape one level up and the one the report was written
;; about: the offset is read off the query string and the bound handed to `find-terms` is
;; `offset + find-cap + 1`.  Both offsets below are past the single hit, so both render
;; the same empty fragment — what separates the two readings is the bound and nothing
;; else.

(def ^:private small-offset 1000)
(def ^:private large-offset 8000000)

(defn- find-rows-bytes
  "Bytes one continuation fragment at `offset` allocates."
  ^long [view ^long offset]
  (alloc-bytes #(count (:body (web/find-rows-page view needle offset)))))

(deftest a-page-offset-off-the-url-sizes-nothing
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (corpus! kb)
        (let [view  (web/view kb {})
              small (find-rows-bytes view small-offset)
              large (find-rows-bytes view large-offset)
              span  (- large-offset small-offset)]
          (testing "both offsets are past the only hit, so both render nothing"
            (is (= "" (:body (web/find-rows-page view needle small-offset))))
            (is (= "" (:body (web/find-rows-page view needle large-offset)))))
          (testing "so the millionth page costs what the thousandth did"
            (is (zero? (bytes-per-requested-unit small large span))
                (str "the offset is sizing something — " small " B at offset " small-offset
                     " against " large " B at offset " large-offset)))))
      (finally (tu/clear-kb! kb)))))
