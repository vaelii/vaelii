;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.caches-test
  "What `vaelii.core/caches` promises, and the two things about it that are easy to get
  wrong.

  **A number's scope.**  A row carries `:scope` for what its entries count and
  `:counters` for what its hit and miss counters count, and the literal cache is exactly
  the case where they differ: entries are this KB's and the counters are global
  `AtomicLong`s across every KB in the process.  Reading the second as though it were the
  first attributes another KB's work to this one, so it is asserted with two live KBs
  rather than by reading the keyword back.

  **Completeness.**  A diagnostics list that quietly omits a cache is worse than no list:
  a reader concludes the engine holds nothing else.  Two tests enforce it — a roster,
  so adding a cache is a visible change in a diff, and a scan of the sources for the
  **bounded**-cache idiom, so a cache spelled with a `…-limit` / `…-budget` /
  `…-capacity` constant and no registration fails here rather than going unnoticed.  The
  scan reaches exactly that far and no further: an *unbounded* cache has no constant to
  find — `:taxonomy-closures` is one, retired by a generation bump rather than by size —
  so the roster is what catches those, and it catches them only by being read."
  (:require [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu])
  (:import [java.io File]))

(defn- reset-profile-after
  "The cache profile and the memory-pressure guard are process-wide and outlive a KB, so a
  test that set a scale, drove pressure, or attached the guard and left it would change what
  every later test reads.  Restore the default and detach the guard after each."
  [f]
  (try (f) (finally (caches/uninstall-memory-guard!) (caches/reset-profile))))

(use-fixtures :each (tu/neutral-fresh tu/fresh) reset-profile-after)

(defn- row [kb id] (first (filter #(= id (:cache %)) (v/caches kb))))

(defn- with-registered
  "Run `f` with `descriptor` in the register, and take it out again — the register is
  process-wide and outlives a KB, so a test that left one behind would change what every
  later test sees the page holding."
  [descriptor f]
  (let [reg @#'caches/registry]
    (try (caches/register-cache descriptor)
         (f)
         (finally (swap! reg dissoc (:cache descriptor))))))

;; ---- the structure of a row -------------------------------------------------

(tu/deftest-kb every-row-says-what-it-counts-and-what-it-is-about
  (let [rows (v/caches kb)]
    (is (seq rows) "the registry is populated by the namespaces that hold caches")
    (doseq [{:keys [cache label scope unit note entries limit hits misses counters]} rows]
      (testing (str cache)
        (is (keyword? cache))
        (is (and (string? label) (seq label)))
        (is (#{:kb :process} scope) "a row is about this KB or about this process")
        (is (and (string? unit) (seq unit))
            "entries mix units across caches, so a bare integer column compares nothing")
        (is (and (string? note) (seq note))
            "what it holds, and what retires an entry — the unit alone does not say")
        (is (or (nil? entries) (nat-int? entries)))
        (is (or (nil? limit) (pos-int? limit)))
        (is (= (some? hits) (some? misses)) "counted on both sides or on neither")
        (is (= (some? hits) (some? counters))
            "a counted cache says whose counters those are; an uncounted one has none")))))

(tu/deftest-kb a-row-is-data-all-the-way-down
  ;; `caches` is a public read: it is served over the remote surface and rendered on a
  ;; page, so a row has to be a value both can carry.  The descriptor a cache registers
  ;; holds three *functions* — `:read`, `:clear` and `:reset-counters` — and what a
  ;; caller needs of the last two is already on the row as `:clearable?` and `:counters`.
  ;; One left in reads as `#function[…]` on the page and refuses to serialize on the
  ;; wire, and only the two caches that keep process-wide counters would show it.
  (let [rows (v/caches kb)]
    (is (seq rows))
    (doseq [row rows]
      (testing (str (:cache row))
        (doseq [[k v] row]
          (is (not (fn? v))
              (str "a row carries no function — " k " does")))))
    (testing "and the two that would have leaked one are in the answer"
      (is (some #(= :literal-matches (:cache %)) rows))
      (is (some :counters rows) "at least one row reports process-wide counters"))))

(tu/deftest-kb a-namespace-registers-its-caches-by-being-loaded
  ;; Which is what lets an unloaded one hold no row: a process with no metric-time
  ;; reasoner has no metric closures, and a row of zeroes would claim a cache that does
  ;; not exist.  Asserted in the positive direction, because the negative one depends on
  ;; what every other namespace in the run happens to have loaded first.
  (is (some? (row kb :literal-matches)) "a namespace core loads is registered")
  (require 'vaelii.impl.stp)
  (is (some? (row kb :metric-closures))
      "and one it does not is registered the moment something requires it"))

(tu/deftest-kb the-order-is-a-function-of-the-content
  ;; Ranked by entries descending, a row that cannot be counted last, ties on the cache's
  ;; own name — never on registration order, which is namespace load order and so is not
  ;; a property of the process's state.
  (let [rows (v/caches kb)
        key' (fn [r] [(- (long (or (:entries r) -1))) (name (:cache r))])]
    (is (= (map :cache rows) (map :cache (sort-by key' rows))))
    (is (= (map :cache rows) (map :cache (v/caches kb)))
        "and two reads of an unchanged process agree")
    (let [counted (take-while (comp some? :entries) rows)]
      (is (every? (comp nil? :entries) (drop (count counted) rows))
          "a nil entry count is not a small number, so it sorts last"))))

;; ---- whose numbers are whose --------------------------------------------

(tu/deftest-kb the-literal-cache-counts-entries-per-kb-and-hits-per-process
  (let [other (v/open-kb tu/plain-memory-space)
        lit   #(row % :literal-matches)]
    (try
      (v/clear-caches kb {:counters? true})
      (is (= :kb      (:scope    (lit kb))))
      (is (= :process (:counters (lit kb))))
      (tu/with-terms [parentOf Tom Bob CxFarm]
        (v/assert other (list parentOf Tom Bob) CxFarm)
        (v/clear-caches other {:counters? true})
        (dotimes [_ 2] (doall (v/prove other (list parentOf Tom '?y) CxFarm)))
        (is (pos? (:hits (lit other))) "the second ask of one literal is served")
        (is (= (:hits (lit other)) (:hits (lit kb)))
            (str "the counters are the mechanism's, not the store's — so this KB reports "
                 "the other KB's hits, which is exactly why the row says :process"))
        (is (zero? (:entries (lit kb)))
            "and the entries are not shared: this KB was asked nothing"))
      (finally (v/clear-caches other) (v/clear! other)))))

(tu/deftest-kb a-bound-that-can-be-rebound-is-read-where-it-is-read
  ;; A descriptor is built once, at namespace load. Capturing a `^:dynamic` bound into it
  ;; would report the root value while the engine enforced the binding — and being
  ;; rebindable is the only reason either of these vars is dynamic, so the stale reading
  ;; is the one a reader would meet. `:limit` takes a thunk for exactly this.
  (is (= 1000000 (:limit (row kb :symbol-pool))))
  (binding [sx/*symbol-pool-limit* 8]
    (is (= 8 (:limit (row kb :symbol-pool)))
        "the pool flushes at 8 here, so the page must not say a million"))
  (is (= 128 (:limit (row kb :taxonomy-scoped-closures))))
  (binding [tax/*scoped-memo-budget* 1]
    (is (= 1 (:limit (row kb :taxonomy-scoped-closures))))))

;; ---- the tunable profile ------------------------------------------------

(tu/deftest-kb the-default-profile-is-the-shipped-bounds
  ;; The invariant the whole scale rests on: at scale 1.0 with no override, a routed cache
  ;; enforces and reports exactly the number it shipped with, so the goldens and the cost
  ;; budgets are the ones the engine always had.
  (is (= {:scale 1.0 :pressure 1.0 :overrides {}} (v/cache-profile)))
  (is (= 4096   (:limit (row kb :literal-matches))))
  (is (= 256    (:limit (row kb :resident))))
  (is (= 256    (:limit (row kb :path-consistency))))
  (is (= 8192   (:limit (row kb :relation-decode))))
  (is (= 100000 (:limit (row kb :closure-answers))))
  (is (= 4096 (caches/limit-of :literal-matches 4096))
      "and limit-of returns the shipped default untouched, not a rounded copy of it"))

(tu/deftest-kb a-scale-moves-every-routed-cache-and-restores
  (v/set-cache-scale 0.5)
  (is (= 2048 (:limit (row kb :literal-matches))) "half the shipped 4096")
  (is (= 128  (:limit (row kb :resident))))
  (is (= 128  (:limit (row kb :path-consistency))))
  (v/set-cache-scale 4)
  (is (= 16384 (:limit (row kb :literal-matches))) "four times the shipped 4096")
  (is (= 1024  (:limit (row kb :resident))))
  (is (= 1.0 (:scale (v/set-cache-scale 1.0))))
  (is (= 4096 (:limit (row kb :literal-matches))) "and 1.0 is the shipped bound again"))

(tu/deftest-kb the-scale-floors-rather-than-shrinking-to-uselessness
  (v/set-cache-scale 0.0001)
  (is (= 16 (:limit (row kb :resident)))
      "a scale that would compute fewer than min-limit is read as min-limit")
  (is (= 16 (:limit (row kb :literal-matches)))))

(tu/deftest-kb a-scale-past-the-range-of-a-long-saturates-rather-than-throwing
  ;; `(long ##Inf)` throws, and every counted cache reads its bound on its store path, so
  ;; a scale the refusal admits left every query in the process throwing until reset
  (tu/with-terms [parentOf Tom Bob CxFarm]
    (v/assert kb (list parentOf Tom Bob) CxFarm)
    (doseq [scale [##Inf 1e300]]
      (v/set-cache-scale scale)
      (is (= Long/MAX_VALUE (:limit (row kb :literal-matches))) (str "at " scale))
      (is (nil? (:error (row kb :literal-matches))) (str "the row reads at " scale))
      (is (seq (v/query kb (list parentOf Tom '?x) CxFarm)) (str "a query answers at " scale)))))

(tu/deftest-kb the-symbol-pool-is-structural-and-the-scale-leaves-it-alone
  ;; The interning pool's check runs per symbol interned — the hottest path on a load — and
  ;; scaling it risks the sharing it exists for, so it keeps its own dynamic bound and is
  ;; not routed through the scale.
  (v/set-cache-scale 0.25)
  (is (= 1000000 (:limit (row kb :symbol-pool))) "the pool is not scaled by the profile")
  (is (= 1024 (:limit (row kb :literal-matches))) "while a routed cache is"))

(tu/deftest-kb an-override-pins-a-cache-and-the-scale-does-not-move-it
  (v/set-cache-scale 0.5)
  (v/set-cache-limit :resident 1000)
  (is (= 1000 (:limit (row kb :resident))) "the override wins over the scale")
  (is (= 2048 (:limit (row kb :literal-matches))) "a cache with no override still scales")
  (is (= {:resident 1000} (:overrides (v/cache-profile))))
  (v/set-cache-limit :resident nil)
  (is (= 128 (:limit (row kb :resident))) "clearing the override returns it to the scale")
  (is (= {} (:overrides (v/cache-profile)))))

(tu/deftest-kb a-bad-scale-or-override-is-refused-by-name
  (doseq [bad [-1 "big" nil]]
    (is (= :unknown-option
           (:type (try (v/set-cache-scale bad)
                       (catch clojure.lang.ExceptionInfo e (ex-data e)))))
        (str "a scale of " (pr-str bad) " is refused, not read as the nearest legal one")))
  (is (= :unknown-option
         (:type (try (v/set-cache-limit "resident" 10)
                     (catch clojure.lang.ExceptionInfo e (ex-data e)))))
      "an id that is not a keyword is refused")
  (doseq [bad [-5 0 2.5]]
    (is (= :unknown-option
           (:type (try (v/set-cache-limit :resident bad)
                       (catch clojure.lang.ExceptionInfo e (ex-data e)))))
        (str "a limit of " (pr-str bad) " is refused"))))

;; ---- the memory-pressure guard ------------------------------------------

(deftest pressure-response-decides-by-the-two-water-marks
  ;; A pure function of the post-collection reading and the current pressure, so the
  ;; decision is checked without a heap that is actually full.
  (is (= :shrink (caches/pressure-response 0.90 1.0)) "over the high-water mark")
  (is (= :shrink (caches/pressure-response 0.86 0.5)) "and again while already shrunk")
  (is (= :grow   (caches/pressure-response 0.50 0.5)) "under the low mark with room to grow")
  (is (= :hold   (caches/pressure-response 0.50 1.0)) "under the low mark but already at the ceiling")
  (is (= :hold   (caches/pressure-response 0.70 1.0)) "between the marks")
  (is (= :hold   (caches/pressure-response 0.70 0.5)) "between the marks, either way"))

(tu/deftest-kb a-shrink-lowers-pressure-and-the-bound-and-a-grow-raises-them
  (is (= 256 (:limit (row kb :resident))) "the shipped bound at pressure 1.0")
  (caches/shrink! [])
  (is (= 0.5 (:pressure (v/cache-profile))))
  (is (= 128 (:limit (row kb :resident))) "half, under pressure 0.5")
  (caches/shrink! [])
  (is (= 0.25 (:pressure (v/cache-profile))))
  (is (= 64 (:limit (row kb :resident))))
  (caches/grow!)
  (is (< 0.25 (:pressure (v/cache-profile))) "and a grow raises pressure")
  (dotimes [_ 10] (caches/grow!))
  (is (= 1.0 (:pressure (v/cache-profile))) "capped at the operator's scale")
  (is (= 256 (:limit (row kb :resident))) "so the bound is the shipped one again"))

(tu/deftest-kb the-pressure-floor-keeps-a-fraction-rather-than-running-cold
  (dotimes [_ 20] (caches/shrink! []))
  (is (<= 0.1 (:pressure (v/cache-profile))) "pressure never reaches zero")
  (is (pos? (:limit (row kb :resident)))
      "so a cache under sustained pressure still holds something"))

(tu/deftest-kb pressure-trims-an-override-even-though-the-scale-does-not
  ;; The decision behind the guard: a pin the operator set with set-cache-limit stands against
  ;; the scale but not against a filling heap.  The scale leaves a pinned bound alone; pressure
  ;; shrinks it like any other counted cache, because a pin the guard could not reach would
  ;; keep the heap short of the reclaim the guard exists to force.
  (v/set-cache-scale 0.5)
  (v/set-cache-limit :resident 1000)
  (is (= 1000 (:limit (row kb :resident))) "the scale does not move a pinned bound")
  (caches/shrink! [])
  (is (= 500 (:limit (row kb :resident))) "but pressure 0.5 halves the pin")
  (dotimes [_ 20] (caches/shrink! []))
  (is (= 125 (:limit (row kb :resident)))
      "and the floor is pressure-min (0.125) times the pin, not min-limit"))

(deftest a-trim-keeps-the-target-rather-than-emptying-the-map
  ;; The "not too much" property, on the plain-map helper the trims share: past its target a
  ;; cache keeps that many entries where a wholesale clear keeps none, so the reads the
  ;; survivors serve are not all recomputed at once.
  (let [a (atom (into {} (map (fn [i] [i i])) (range 100)))]
    (is (= 60 (caches/trim-map! a 40)) "dropped the excess")
    (is (= 40 (count @a)) "and kept the target, not zero")
    (is (zero? (caches/trim-map! a 40)) "a map already at the target is left alone")
    (is (= 40 (count @a)))))

(tu/deftest-kb a-shrink-trims-a-registered-cache-to-its-lowered-bound
  (let [a (atom (into {} (map (fn [i] [i i])) (range 100)))]
    (with-registered
      {:cache :probe-trim :label "Probe" :scope :process :unit "probes"
       :limit (caches/limit-thunk :probe-trim 80) :counters nil :note "a probe."
       :read (fn [_] {:entries (count @a)})
       :trim (fn [_ target] (caches/trim-map! a target))}
      (fn []
        (is (= 80 (:limit (row kb :probe-trim))) "the effective bound at pressure 1.0")
        (let [{:keys [dropped]} (caches/shrink! [])]   ; pressure 0.5 -> bound 40
          (is (= 40 (:limit (row kb :probe-trim))))
          (is (= 40 (count @a)) "trimmed to the lowered bound, not emptied")
          (is (>= dropped 60) "and the shrink reports what it dropped"))))))

(tu/deftest-kb a-kb-scoped-shrink-hands-the-trim-each-live-kb
  ;; trim-to-bounds! runs a :process cache's trim once and a :kb cache's trim once for each
  ;; live KB, handing it the KB — the path the literal cache's per-KB trim takes, which the
  ;; :process probe above does not reach.  Driven with shrink! [kb] rather than a real
  ;; collection.
  (let [seen (atom [])
        a    (atom (into {} (map (fn [i] [i i])) (range 100)))]
    (with-registered
      {:cache :probe-kb-trim :label "Probe" :scope :kb :unit "probes"
       :limit (caches/limit-thunk :probe-kb-trim 80) :counters nil :note "a probe."
       :read (fn [_] {:entries (count @a)})
       :trim (fn [k target] (swap! seen conj k) (caches/trim-map! a target))}
      (fn []
        (is (= 80 (:limit (row kb :probe-kb-trim))) "the effective bound at pressure 1.0")
        (let [{:keys [dropped]} (caches/shrink! [kb])]   ; pressure 0.5 -> bound 40
          (is (= [kb] @seen) "the :kb trim received the live KB, once")
          (is (= 40 (count @a)) "trimmed to the lowered bound, not emptied")
          (is (>= dropped 60)))))))

(tu/deftest-kb the-listener-body-shrinks-grows-and-holds-by-the-reading
  ;; on-collection is the listener's body: it reads the old-generation fraction from a
  ;; collection's after-usage map, decides by pressure-response, and drives shrink!, grow! or a
  ;; hold — pulling the KBs a shrink trims from the guard's own :kbs thunk.  Every piece is
  ;; tested apart from this one; this drives the assembled chain with usage maps rather than a
  ;; real collection, which is what the body was lifted out of the listener to allow.
  (let [on-collection @#'caches/on-collection
        guard   @#'caches/guard
        old-gen (fn [used] (doto (java.util.HashMap.)
                             (.put "G1 Old Gen"
                                   (java.lang.management.MemoryUsage. 0 used 1000 1000))))
        kbs0    (:kbs @guard)]
    ;; The :kbs thunk is set on the guard directly rather than by install-memory-guard!.  An
    ;; installed listener runs this same on-collection on every collection the JVM makes.  A
    ;; collection during this test reads an old generation under pressure-low, and the
    ;; listener then grows the pressure these assertions read, one 1.5 step per collection.
    ;; the-guard-attaches-to-the-collectors-and-detaches covers install-memory-guard!.
    (swap! guard assoc :kbs (fn [] [kb]))
    (try
      (is (= 1.0 (:pressure (v/cache-profile))))
      (on-collection (old-gen 900))
      (is (= 0.5 (:pressure (v/cache-profile))) "a reading over the high mark shrinks")
      (on-collection (old-gen 900))
      (is (= 0.25 (:pressure (v/cache-profile))) "and again while already shrunk")
      (on-collection (old-gen 700))
      (is (= 0.25 (:pressure (v/cache-profile))) "a reading between the marks holds")
      (on-collection (old-gen 100))
      (is (< 0.25 (:pressure (v/cache-profile))) "a reading under the low mark grows")
      (testing "a collection that names no old-gen pool leaves pressure where it is"
        (let [p (:pressure (v/cache-profile))]
          (on-collection (java.util.HashMap.))
          (is (= p (:pressure (v/cache-profile))))))
      (finally (swap! guard assoc :kbs kbs0)))))

(deftest the-guard-attaches-to-the-collectors-and-detaches
  (is (false? (:installed? (caches/memory-guard))) "nothing attached to start")
  (let [g (caches/install-memory-guard! {:kbs (constantly [])})]
    (is (true? (:installed? g)) "it attaches to the JVM's collectors"))
  (is (true? (:installed? (caches/memory-guard))))
  (let [g (caches/uninstall-memory-guard!)]
    (is (false? (:installed? g)) "and detaches again")
    (is (= 1.0 (:pressure g)) "restoring pressure on the way out")))

(deftest the-old-generation-fraction-is-read-from-the-tenured-pool
  (let [ogf @#'caches/old-gen-fraction
        m   (doto (java.util.HashMap.)
              (.put "G1 Old Gen"    (java.lang.management.MemoryUsage. 0 900 1000 1000))
              (.put "G1 Eden Space" (java.lang.management.MemoryUsage. 0 50 100 -1)))]
    (is (== 0.9 (ogf m)) "used over max on the old-gen pool, not eden")
    (is (nil? (ogf (java.util.HashMap.)))
        "a collector that names no old-gen pool reads nil, and the guard then holds")))

;; ---- a row answers for itself, and fails for itself ---------------------

(tu/deftest-kb a-read-that-throws-costs-its-own-row-and-no-other
  ;; The register is open — any namespace may declare a descriptor — so a read here runs
  ;; code this namespace never saw. A diagnostic is worth most while something is already
  ;; wrong, which is exactly when it must not be the next thing to break.
  (let [broken {:cache :probe-unreadable :label "Probe" :scope :kb :unit "probes"
                :limit nil :counters nil :note "a probe."
                :read (fn [_] (throw (ex-info "the read blew up" {})))}]
    (with-registered broken
      (fn []
        (let [rows (v/caches kb)
              r    (row kb :probe-unreadable)]
          (is (< 1 (count rows)) "every other row still answered")
          (is (some? (row kb :literal-matches)))
          (is (nil? (:entries r)))
          (is (str/includes? (:error r) "the read blew up")
              "and the broken one says what happened")))))
  (is (nil? (row kb :probe-unreadable)) "and the probe left no trace")
  (is (every? (comp nil? :error) (v/caches kb))
      "nothing the engine actually registers fails to read"))

(tu/deftest-kb a-clear-that-throws-costs-its-own-entry-and-no-other
  (let [broken {:cache :probe-unclearable :label "Probe" :scope :kb :unit "probes"
                :limit nil :counters nil :note "a probe."
                :read  (fn [_] {:entries 0})
                :clear (fn [_] (throw (ex-info "the clear blew up" {})))}]
    (with-registered broken
      (fn []
        (tu/with-terms [parentOf Tom Bob CxFarm]
          (v/assert kb (list parentOf Tom Bob) CxFarm)
          (doall (v/prove kb (list parentOf Tom '?y) CxFarm))
          (let [{:keys [cleared entries]} (v/clear-caches kb)
                by-id (into {} (map (juxt :cache identity)) cleared)]
            (is (pos? entries) "the caches that could be dropped were")
            (is (zero? (:entries (row kb :literal-matches))))
            (is (str/includes? (:error (by-id :probe-unclearable)) "the clear blew up"))
            (is (zero? (:entries (by-id :probe-unclearable)))
                "a clear that threw dropped nothing, and says nothing else")))))))

;; ---- what the page costs ------------------------------------------------

(tu/deftest-kb reading-the-page-does-not-move-the-numbers-it-reports
  ;; The claim behind "it can be polled": a row is a count off a map the engine already
  ;; holds, never a query.  A page that queried the KB to describe it would report its
  ;; own reads, and a poll would climb the miss counter it is displaying.
  (tu/with-terms [parentOf Tom Bob CxFarm]
    (v/assert kb (list parentOf Tom Bob) CxFarm)
    (v/clear-caches kb)
    (doall (v/prove kb (list parentOf Tom '?y) CxFarm))
    (let [before (row kb :literal-matches)]
      (dotimes [_ 5] (v/caches kb))
      (let [after (row kb :literal-matches)]
        (is (= (:entries before) (:entries after)))
        (is (= (:hits before) (:hits after)))
        (is (= (:misses before) (:misses after)))))))

;; ---- the clear ----------------------------------------------------------

(tu/deftest-kb a-clear-costs-the-next-ask-a-miss-and-costs-belief-nothing
  (tu/with-terms [parentOf Tom Bob CxFarm]
    (v/assert kb (list parentOf Tom Bob) CxFarm)
    (v/clear-caches kb {:counters? true})
    (doall (v/prove kb (list parentOf Tom '?y) CxFarm))
    (doall (v/prove kb (list parentOf Tom '?y) CxFarm))
    (let [warm (row kb :literal-matches)]
      (is (pos? (:hits warm)) "the second ask was served from the cache")
      (is (pos? (:hit-rate warm)))
      ;; the counters go only because this call asked for them; the entry drop below is
      ;; what a plain clear does, and the miss after it is the measurement
      (let [report (v/clear-caches kb {:counters? true})
            cold   (row kb :literal-matches)]
        (is (pos? (:entries report)) "and the clear says how much it dropped")
        (is (every? #(and (keyword? (:cache %)) (nat-int? (:entries %)))
                    (:cleared report)))
        (is (zero? (:entries cold)))
        (is (zero? (:hits cold)))
        (doall (v/prove kb (list parentOf Tom '?y) CxFarm))
        (is (pos? (:misses (row kb :literal-matches)))
            (str "the ask that was a hit is a miss again — which is what makes a clear "
                 "a measuring instrument rather than an edit"))
        (is (v/ask? kb (list parentOf Tom Bob) CxFarm)
            "and nothing that was believed stopped being believed")))))

(tu/deftest-kb a-clear-is-scoped-to-its-argument-and-the-counter-reset-is-asked-for
  ;; The scope split is not only a rendering question. The literal cache's counters are
  ;; the mechanism's and span every KB in the process, so zeroing them is *wider* than
  ;; the KB a clear names — which is why a plain clear must not do it. Both halves are
  ;; pinned here, in both directions: what a plain clear leaves alone, and what
  ;; `:counters? true` then reaches.
  (let [other (v/open-kb tu/plain-memory-space)
        lit   #(row % :literal-matches)]
    (try
      (tu/with-terms [parentOf Tom Bob CxFarm]
        (v/assert other (list parentOf Tom Bob) CxFarm)
        (v/clear-caches other {:counters? true})
        (dotimes [_ 2] (doall (v/prove other (list parentOf Tom '?y) CxFarm)))
        (is (pos? (:hits (lit other))))
        (let [held (:entries (lit other))
              rate (:hits (lit other))]
          (is (pos? held))
          (let [report (v/clear-caches kb)]
            (is (not (contains? report :counters-reset))
                "a clear that was not asked to reset counters does not report doing so"))
          (is (= rate (:hits (lit other)))
              (str "clearing this KB left the other's rate alone — the counters are the "
                   "mechanism's, so reaching them is wider than the argument and is asked "
                   "for separately"))
          (is (= held (:entries (lit other)))
              "and did not touch a single entry of the other KB's")
          (is (v/ask? other (list parentOf Tom Bob) CxFarm)
              "nor anything it believed")
          ;; and the opt-in half: asked for, it does reach, and says what it zeroed
          (let [report (v/clear-caches kb {:counters? true})]
            (is (seq (:counters-reset report))
                "the wider control names the caches it reset")
            (is (every? #(and (keyword? (:cache %)) (nat-int? (:hits %)))
                        (:counters-reset report))
                "and what each of them held, so the measurement is not merely lost")
            (is (zero? (:hits (lit other)))
                "which is process-wide, exactly as the :counters column says")
            (is (= held (:entries (lit other)))
                "while still costing the other KB no entry"))))
      (finally (v/clear-caches other) (v/clear! other)))))

(tu/deftest-kb an-unknown-clear-caches-option-is-refused
  (is (thrown? clojure.lang.ExceptionInfo (v/clear-caches kb {:counter? true})))
  (is (= :unknown-option
         (:type (try (v/clear-caches kb {:counter? true})
                     (catch clojure.lang.ExceptionInfo e (ex-data e)))))
      "the near-miss spelling is refused like every other bound on a run"))

(tu/deftest-kb the-rows-the-counter-reset-is-about-are-answerable-from-the-read
  ;; The `:counters? true` opt is the one control here wider than its KB argument, and a
  ;; caller has to be able to say which caches it would reach without naming one in prose
  ;; that would outlive it — which is how the page writes the warning above its button.
  (let [wide (->> (v/caches kb)
                  (filter #(and (:clearable? %) (= :process (:counters %))))
                  (map :cache)
                  set)]
    (is (= #{:literal-matches} wide))))

(tu/deftest-kb the-structural-caches-are-left-alone-and-the-page-can-say-which
  (let [rows  (v/caches kb)
        kept  (into #{} (comp (remove :clearable?) (map :cache)) rows)
        going (into #{} (comp (filter :clearable?) (map :cache)) rows)]
    (is (contains? kept :symbol-pool)
        (str "dropping the pool costs the sharing every symbol minted before it was "
             "paying for, and buys no measurement — nothing counts a pool hit"))
    (is (contains? kept :compiled-algebras))
    (is (contains? going :literal-matches))
    (is (= going (into #{} (map :cache) (:cleared (v/clear-caches kb))))
        "and the clear touches exactly the rows that said it would")))

;; ---- completeness -------------------------------------------------------

(def ^:private roster
  "Every cache registered by a namespace `vaelii.core` loads.  A roster rather than a
  count, so adding one is a visible change in a diff and not merely a number that moved."
  #{:literal-matches :resident :stored-handles :closure-neighbours :closure-answers
    :pinned-values :justification-dedup :symbol-pool :compiled-algebras :relation-decode
    :path-consistency :network-support :taxonomy-closures :taxonomy-scoped-closures
    :taxonomy-visibility :hot-records :rete-alpha :source-parses :preservation-crossing})

(def ^:private optional-roster
  "Caches registered by a namespace core does **not** load, so whether they are present
  depends on what else the run required.  Held apart from the roster rather than folded
  into it: the roster is a claim about what every process holds, and one that moved with
  the test order would be a claim about nothing."
  #{:metric-closures :metric-reconstructions})

(tu/deftest-kb the-roster-is-what-this-process-holds
  (let [registered (into #{} (map :cache) (v/caches kb))]
    (is (empty? (set/difference roster registered))
        (str "a cache in the roster that no namespace registers — either it is gone, in "
             "which case the roster entry goes with it, or its registration was dropped"))
    (is (empty? (set/difference registered roster optional-roster))
        (str "a cache the page shows that the roster does not name. Adding one changes "
             "what the page claims the engine holds — name it here in the same commit, "
             "and check it has a :unit and a :note that say what an entry is"))))

;; A bounded cache in this engine is spelled one way: a `…-limit` / `…-budget` /
;; `…-capacity` constant, and a wholesale clear when the count reaches it.  So the
;; constants are enumerable, and each one either names a cache with a row or is not a
;; cache bound at all — which is a sentence somebody has to write down.
(def ^:private limit-form
  #"\(def[a-z-]* (?:\^[^\s]+ )*(\*?[a-z][a-z0-9-]*(?:limit|budget|capacity)\*?)[\s\n]")

(def ^:private not-a-cache-bound
  "Limit-shaped constants in `src/` that bound something other than a cache, each with
  what it does bound.  Explicit rather than a pattern: a pattern excusing `*-budget*`
  would excuse the taxonomy's scoped memo, which is a cache bound and has a row."
  {"min-limit"           (str "caches.clj — the floor `limit-of` never scales a bound "
                              "below; a clamp on the tunable bound, not a cache of its own")
   "set-limit"           (str "caches.clj — the setter that pins one cache's bound; a "
                              "function, not a constant, and it writes a bound rather than "
                              "being one")
   "set-cache-limit"     "core.clj — the public setter wrapping `caches/set-limit`"
   "default-limit"       "quality.clj — how many findings a report lists"
   "dense-table-limit"   (str "qcn.clj — whether a composition table is built whole or "
                              "per base relation; a build decision, and the table is not "
                              "evicted")
   "disk-cache-capacity" "config.clj — the reader for the hot-record LRU, which has a row"
   "asp-time-limit"      (str "config.clj — the seconds one ASP solve may run before the "
                              "backend is interrupted; a time bound, nothing retained")
   "classify-resolution-budget" (str "config.clj — the reader for the solve-free "
                                     "classifier's per-cluster search ceiling "
                                     "(VAELII_CLASSIFY_RESOLUTION_BUDGET); a per-read "
                                     "search bound, nothing retained")
   "wrap-body-limit"     "guard.clj — the HTTP request-body ceiling"
   "graph-side-budget"   "web.clj — how many expansions a term page's picture may spend"
   "matrix-node-limit"   "web.clj — how many nodes the network page will draw"
   "default-node-budget" (str "inference.clj — how many nodes the debugger's bounded "
                              "search-tree walk expands before it stops; a per-read "
                              "search bound, not a retained cache")
   "*exposure-instance-budget*" (str "settle.clj — how many members of a type a "
                                     "disjointness exposure check instantiates")
   "regex-step-budget"   (str "core.clj — how many characters a `find-terms` regex may "
                              "read against one term before it is refused too costly; a "
                              "per-match evaluation bound, nothing retained")
   "regex-scan-budget"   (str "core.clj — how many characters one `find-terms` regex may "
                              "read across the whole vocabulary before it is refused; the "
                              "scan-wide half of the same bound, nothing retained")
   "match-step-budget"   (str "provers.clj — how many characters one `matchesPattern` match "
                              "may read before it is refused too costly; a per-match "
                              "evaluation bound, nothing retained")
   "default-describe-limit" (str "core.clj — how many entries one of `describe`'s bounded "
                                 "lists carries; a per-read window on an answer computed "
                                 "fresh each call, nothing retained")})

(def ^:private bound-to-cache
  "The cache each remaining constant bounds.  Every one of them is a row on the page,
  which is the claim: a bounded cache the engine holds is one a reader can see."
  {"cache-limit"           :literal-matches
   "*closure-answer-limit*" :closure-answers
   "resident-limit"        :resident
   "pc-cache-limit"        :path-consistency
   "decode-cache-limit"    :relation-decode
   "compiled-cache-limit"  :compiled-algebras
   "closure-cache-limit"   :metric-closures
   "*symbol-pool-limit*"   :symbol-pool
   "generation-limit"      :symbol-pool
   "*scoped-memo-budget*"  :taxonomy-scoped-closures
   "parse-memo-limit"      :source-parses
   "crossing-reads-limit"  :preservation-crossing})

(defn- limit-constants
  "Every limit-shaped constant defined under `src/`."
  []
  (into (sorted-set)
        (comp (filter #(.isFile ^File %))
              (filter #(str/ends-with? (.getPath ^File %) ".clj"))
              (mapcat #(map second (re-seq limit-form (slurp %)))))
        (file-seq (io/file "src"))))

(tu/deftest-kb every-bounded-cache-in-the-sources-is-one-the-page-can-show
  (let [found   (limit-constants)
        known   (into (set (keys not-a-cache-bound)) (keys bound-to-cache))
        strays  (remove known found)
        missing (remove found known)]
    (is (empty? strays)
        (str "a bounded constant nothing here accounts for: " (sort strays)
             ". If it bounds a cache, register that cache with `caches/register-cache`"
             " so the page can show it, and add it to `bound-to-cache`; if it bounds"
             " anything else, say what in `not-a-cache-bound`."))
    (is (empty? missing)
        (str "accounted for here but no longer in the sources: " (sort missing)
             ". A stale entry excuses a name nothing defines."))
    (testing "and each cache bound names a cache that is registered"
      ;; `:metric-closures` among them: it is registered by a namespace `core` does not
      ;; load, so it is checked by loading that namespace rather than against `caches`.
      (require 'vaelii.impl.stp)
      (let [registered (into #{} (map :cache) (v/caches kb))]
        (doseq [[nm id] (sort bound-to-cache)]
          (is (contains? registered id)
              (str nm " bounds " id ", which no namespace registered")))))))
