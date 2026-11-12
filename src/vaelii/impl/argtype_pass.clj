;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.argtype-pass
  "The argument-type pass over every stored fact (`special/arg-type-extents`), run so that
  it can stop and resume: `run-all` draws every fact in one call, and `run!` draws them
  under a per-fact budget, stops at a fact boundary when asked, and keeps what it still
  owes in the store, where the next call resumes it.  docs/argtypes.md, \"The pass over a
  stored KB\".

  **What it owes** is one value, the *owed record*: the functors it has drawn whole (by
  name), the fact handle it reached in the next one, the facts it set aside over budget
  with the part of the checks that ran out, and whether the sweep over the functors has
  ended.  A KB with a directory keeps it there as `arg-types-owed.edn`, replaced whole
  through a temp file, an fsync and an atomic rename; a KB without one keeps it in memory.
  It names stored content and nothing else, so a pass stopped under one engine resumes
  under another.

  **A commit** is where the record moves: the violations drawn since the last one are
  filed, belief is settled, every registered store is forced to disk, and only then is the
  record written.  So the record never runs ahead of the stored mints, and a process killed
  between two commits resumes, once belief is rebuilt, at the last one: the facts after it
  are drawn again, which adds nothing to what they already wrote (`has-justification?`,
  `find-sentex-handle`)."
  (:require [clojure.java.io :as io]
            [vaelii.impl.budget :as budget]
            [vaelii.impl.disk.durability :as dur]
            [vaelii.impl.disk.files :as files]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.special :as special]
            [vaelii.impl.violations :as viol])
  (:import (java.io File FileOutputStream)
           (java.nio.file CopyOption Files StandardCopyOption)))

;; ---- the owed record ---------------------------------------------------------------

(def ^:private owed-file
  "The owed record's name in the KB's directory."
  "arg-types-owed.edn")

(def ^:private owed-version
  "The owed record's shape.  A record of another shape is refused rather than read."
  1)

(defn- from-the-start
  "The owed record of a pass that has drawn nothing."
  []
  {:version owed-version :drawn #{} :at nil :deferred [] :swept? false :facts 0})

(defn- owed-path ^File [kb]
  (when-let [d (:dir kb)] (io/file d owed-file)))

(defn read-owed
  "The owed record `kb` keeps, or nil when the pass owes nothing."
  [kb]
  (if-let [f (owed-path kb)]
    (when (.exists f)
      (let [o (files/read-edn-manifest f nil)]
        (when-not (= owed-version (:version o))
          (throw (ex-info (str "the argument-type pass's owed record at " f " has shape "
                               (pr-str (:version o)) ", and this engine reads shape "
                               owed-version)
                          {:type :unknown-owed-record :path (str f) :version (:version o)})))
        o))
    (:arg-types-owed @(:unrecovered kb))))

(defn- write-owed!
  "Replace `kb`'s owed record with `o`, or remove it when `o` is nil."
  [kb o]
  (if-let [f (owed-path kb)]
    (if (nil? o)
      (when (Files/deleteIfExists (.toPath f))
        (files/fsync-dir! (str f)))
      (let [tmp (io/file (.getParentFile f) (str owed-file ".tmp"))
            txt (binding [*print-length* nil *print-level* nil *print-namespace-maps* false]
                  (pr-str o))]
        (with-open [out (FileOutputStream. tmp)]
          (.write out (.getBytes ^String txt "UTF-8"))
          (.sync (.getFD out)))
        (Files/move (.toPath tmp) (.toPath f)
                    (into-array CopyOption [StandardCopyOption/ATOMIC_MOVE
                                            StandardCopyOption/REPLACE_EXISTING]))
        (files/fsync-file! (str f))))
    (swap! (:unrecovered kb) #(if o (assoc % :arg-types-owed o) (dissoc % :arg-types-owed))))
  nil)

(defn owe-all!
  "Record that the whole pass is owed: a removal from the records of a KB without belief
  can release a mint anywhere a removed membership or edge withheld one."
  [kb]
  (write-owed! kb (from-the-start)))

(defn clear-owed!
  "Record that the pass owes nothing: a pass ran to its end with nothing set aside."
  [kb]
  (write-owed! kb nil))

(defn owed
  "What the pass still owes over `kb`, or nil: `{:facts :total :swept? :deferred}`, the
  facts drawn and counted when it last committed, whether the sweep over every functor has
  ended, and the facts set aside, each `{:fact :phase :budget-ms :ms}`."
  [kb]
  (when-let [o (read-owed kb)]
    {:facts    (:facts o)
     :total    (:total o)
     :swept?   (:swept? o)
     :deferred (mapv #(dissoc % :transitions) (:deferred o))}))

;; ---- a stop request ------------------------------------------------------------------

(defn- watch-stop!
  "Register the running pass's stop flag in `kb`'s `:unrecovered` atom, a volatile and so
  never read as a write hazard (`kb/write-hazards` reads the entries that are `true`)."
  [kb]
  (let [v (volatile! false)]
    (swap! (:unrecovered kb) assoc :stop-pass v)
    v))

(defn- unwatch-stop!
  [kb v]
  (swap! (:unrecovered kb) #(if (identical? v (:stop-pass %)) (dissoc % :stop-pass) %)))

(defn request-stop!
  "Ask the pass running over `kb` to stop at its next fact boundary.  True when one runs,
  false when none does: a request is not held for a pass that has not started."
  [kb]
  (if-let [v (:stop-pass @(:unrecovered kb))]
    (do (vreset! v true) true)
    false))

;; ---- the pass ----------------------------------------------------------------------

(def default-budget-ms
  "The checks one fact's draw may run for before the fact is set aside."
  2000)

(def ^:private default-commit-every-ms
  "How long the pass draws between two commits: what a killed process redraws at most."
  30000)

(def ^:private default-progress-every-ms
  "How often the pass reports, and so how soon a cancel thrown from `:on-progress` lands."
  1000)

(defn- now-ms [] (quot (System/nanoTime) 1000000))

(defn- check-not-restored!
  "Refuse an owed record written past the records the store now holds: a store restored
  from a copy older than the record would have the pass skip facts it never drew there.
  The record carries a handle allocated at its commit before the stores are forced to
  disk (`:mark`), so a store holding the records of that commit allocates above it."
  [kb o]
  (when-let [m (:mark o)]
    (let [n (p/next-id (:records kb))]
      (when (<= (long n) (long m))
        (throw (ex-info (str "the argument-type pass's owed record was written after the"
                             " records this store holds (its mark " m ", the store's next"
                             " handle " n "): the store was restored from an older copy."
                             "  Start the pass over with :resume? false.")
                        {:type :owed-record-ahead :mark m :next n}))))))

(defn- fact-entries
  "The facts left to draw, after `o`'s position, as a lazy seq of `[functor-name h]`, each
  functor closed by `[functor-name nil]`.  A functor's handles are sorted when it is
  reached, so the position within it is a handle."
  [extents o]
  (let [drawn (:drawn o)
        [af ah] (:at o)]
    (mapcat (fn [[f hs]]
              (let [fname (str f)]
                (when-not (contains? drawn fname)
                  (lazy-cat (map #(vector fname %)
                                 (cond->> (sort hs)
                                   (= fname af) (drop-while #(<= (long %) (long ah)))))
                            [[fname nil]]))))
            extents)))

(defn- position-count
  "How many facts `o`'s position accounts for among `extents`: the functors drawn whole,
  and the handles at or before its handle in the one it reached."
  [extents o]
  (let [drawn (:drawn o)
        [af ah] (:at o)]
    (reduce (fn [n [f hs]]
              (let [fname (str f)]
                (cond (contains? drawn fname) (+ n (count hs))
                      (= fname af) (+ n (count (filter #(<= (long %) (long ah)) hs)))
                      :else n)))
            0 extents)))

(defn- pass-state
  [kb o extents]
  {:kb        kb
   :owed      (volatile! o)
   :done      (volatile! (position-count extents o))
   :total     (reduce + (map (comp count second) extents))
   :recorded  (volatile! 0)
   :drawn     (volatile! 0)
   :steps     (volatile! 0)
   :pending   (volatile! [])
   :violations (volatile! 0)
   :settled   (volatile! (now-ms))
   :reported  (volatile! 0)})

(defn- file-violations!
  [{:keys [kb pending violations]}]
  (let [vs @pending]
    (vreset! pending [])
    (vswap! violations + (count vs))
    (viol/report kb vs)))

(defn- owed-at
  "The owed record the run `st` has reached, with the counts and the mark a commit files.
  The mark allocates a handle, so the caller takes it before `dur/fsync-registered!`: the
  forced counter is then past it, and a store recovered from that fsync allocates above
  the mark."
  [{:keys [kb owed done total]}]
  (assoc @owed :facts @done :total total :mark (p/next-id (:records kb))))

(defn- commit!
  "File the violations drawn since the last commit, settle, force the stores to disk, and
  write the owed record unless `record?` is false: the order a killed process needs."
  ([st] (commit! st true))
  ([{:keys [kb settled] :as st} record?]
   (file-violations! st)
   (settle/settle kb)
   (vreset! settled (now-ms))
   (let [o (when record? (owed-at st))]
     (dur/fsync-registered!)
     (when o (write-owed! kb o)))))

(defn- take-result!
  "Count a draw's result into the run and the record: its mints, its violations, and, for
  a draw set aside, the owed entry."
  [{:keys [owed recorded pending]} h fname budget-ms ms r]
  (vswap! recorded + (count (:new r)))
  (vswap! pending into (:violations r))
  (when-let [d (:deferred r)]
    (vswap! owed update :deferred conj
            {:fact h :functor fname :reason :over-budget :phase (:phase d)
             :budget-ms budget-ms :ms ms :transitions (:transitions d)})))

(defn- deadline-for
  "The `budget/now` instant `budget-ms` from now, or nil for none."
  [budget-ms]
  (when budget-ms (+ (long (budget/now)) (long (* (double budget-ms) 1e6)))))

(defn- sweep!
  "Draw the facts of `entries` in order until they end or `stop` answers a reason, each
  draw under the fact budget, and commit every `commit-every-ms`.  `stop` is asked from
  the second step of a run on, so every run moves the pass on by one.  Returns
  nil at the end, else the reason.  The pass caches (`special/call-with-pass-caches`) are
  held across draws and dropped after a commit's settle or a fact set aside, since
  either can leave an answer they hold stale."
  [{:keys [kb owed done drawn] :as st} entries {:keys [budget-ms stop commit-every-ms]}]
  (loop [entries entries]
    (let [step (special/call-with-pass-caches
                kb
                #(loop [es entries]
                   (if-let [[fname h] (first es)]
                     (if-let [why (when (< 1 (long (vswap! (:steps st) inc))) (stop))]
                       {:stop why :rest es}
                       (if (nil? h)
                         (do (vswap! owed (fn [o] (-> o (update :drawn conj fname) (assoc :at nil))))
                             (recur (rest es)))
                         (let [t0 (now-ms)
                               r  (special/draw-fact kb h (deadline-for budget-ms))]
                           (take-result! st h fname budget-ms (- (now-ms) t0) r)
                           (vswap! owed assoc :at [fname h])
                           (vswap! done inc)
                           (vswap! drawn inc)
                           (cond
                             (>= (- (now-ms) (long @(:settled st))) (long commit-every-ms))
                             (do (commit! st) {:rest (rest es)})

                             (:deferred r) {:rest (rest es)}

                             :else (recur (rest es))))))
                     {:rest nil})))]
      (cond (:stop step)         (:stop step)
            (seq (:rest step))   (recur (:rest step))
            :else                nil))))

(defn- retry-deferred!
  "Draw again each fact set aside, once, under the budget, until the list is through or
  `stop` answers a reason: a fact drawn whole leaves the owed list, and one set aside
  again goes to its back with the transitions of both attempts.  `tried` counts the
  attempts.  Returns nil when the list is through, else the reason."
  [{:keys [kb owed recorded pending] :as st} tried {:keys [budget-ms stop commit-every-ms]}]
  (loop [n (count (:deferred @owed))]
    (if (zero? (long n))
      nil
      (if-let [why (when (< 1 (long (vswap! (:steps st) inc))) (stop))]
        why
        (let [e  (first (:deferred @owed))
              t0 (now-ms)
              r  (special/call-with-pass-caches
                  kb #(special/redraw-deferred kb (:fact e) (:transitions e)
                                               (deadline-for budget-ms)))]
          (vswap! recorded + (count (:new r)))
          (vswap! pending into (:violations r))
          (vswap! owed update :deferred
                  (fn [ds]
                    (cond-> (vec (rest ds))
                      (:deferred r) (conj (assoc e
                                                 :phase       (get-in r [:deferred :phase])
                                                 :budget-ms   budget-ms
                                                 :ms          (- (now-ms) t0)
                                                 :transitions (get-in r [:deferred :transitions]))))))
          (vswap! tried inc)
          (when (>= (- (now-ms) (long @(:settled st))) (long commit-every-ms))
            (commit! st))
          (recur (dec (long n))))))))

(defn- reporter
  "The pass's report to `on-progress`, at most every `every-ms` unless `force?`:
  `{:phase :done :total :recorded :deferred}`, `:done` and `:total` the units of the phase
  running (`units`, a fn answering the pair).  A throw from `on-progress` is the caller's
  cancel: kept in `cancel` and answered as a stop reason, so the pass commits before the
  throw is rethrown."
  [{:keys [recorded owed reported]} on-progress every-ms cancel]
  (fn [phase units force?]
    (when (and on-progress (nil? @cancel)
               (or force? (>= (- (now-ms) (long @reported)) (long every-ms))))
      (vreset! reported (now-ms))
      (let [[done total] (units)]
        (try (on-progress {:phase    phase
                           :done     done
                           :total    total
                           :recorded @recorded
                           :deferred (count (:deferred @owed))})
             (catch Throwable t (vreset! cancel t)))))
    (when @cancel :cancelled)))

(defn run-pass!
  "The pass under a budget, stoppable and resumable; the implementation of
  `vaelii.core/record-arg-types!`, whose docstring is the contract."
  [kb {:keys [resume? budget-ms stop? on-progress progress-every-ms commit-every-ms
              retry-deferred?]
       :or   {resume? true budget-ms default-budget-ms}}]
  (let [o0       (or (when resume? (read-owed kb)) (from-the-start))
        _        (check-not-restored! kb o0)
        extents  (special/arg-type-extents kb)
        st       (pass-state kb o0 extents)
        flag     (watch-stop! kb)
        cancel   (volatile! nil)
        report!  (reporter st on-progress (or progress-every-ms default-progress-every-ms) cancel)
        tried    (volatile! 0)
        retrying (volatile! 0)
        phase    (volatile! [:arg-types #(vector @(:done st) (:total st))])
        report   (fn [force?] (let [[k units] @phase] (report! k units force?)))
        enter!   (fn [k units] (vreset! phase [k units]) (report true))
        stop     (fn []
                   (cond @flag                 :requested
                         (dur/stop-requested?) :shutdown
                         (and stop? (stop?))   :requested
                         :else                 (report false)))
        opts     {:budget-ms       budget-ms
                  :stop            stop
                  :commit-every-ms (or commit-every-ms default-commit-every-ms)}]
    (try
      (report true)
      (let [why  (or (when-not (:swept? o0)
                       (or (sweep! st (fact-entries extents o0) opts)
                           ;; swept only once the release returns: a record written
                           ;; after a throw from it leaves the release owed
                           (do (enter! :releases (constantly [0 1]))
                               (let [r (special/release-withheld! kb)]
                                 (vswap! (:recorded st) + (long (:released r))))
                               (vswap! (:owed st) assoc :swept? true :at nil)
                               nil)))
                     (when retry-deferred?
                       (vreset! retrying (count (:deferred @(:owed st))))
                       (enter! :deferred #(vector @tried @retrying))
                       (retry-deferred! st tried opts)))
            o    @(:owed st)
            end? (and (nil? why) (:swept? o) (empty? (:deferred o)))]
        (enter! :settle (constantly [0 1]))
        (commit! st (not end?))
        (when end? (clear-owed! kb))
        ;; a cancel that arrived once nothing was left is not one: the pass is done
        (when-let [t (when-not end? @cancel)] (throw t))
        (enter! :done #(vector @(:done st) (:total st)))
        {:drawn      @(:drawn st)
         :done       @(:done st)
         :total      (:total st)
         :recorded   @(:recorded st)
         :violations @(:violations st)
         :deferred   (count (:deferred o))
         :stopped    why
         :complete?  end?})
      (catch Throwable t
        ;; a draw that threw mid-fact left that fact's mints as far as they got; the record
        ;; is written at the fact before it, which the next run draws again
        (when-not (identical? t @cancel)
          (try (file-violations! st)
               (let [o (owed-at st)]
                 (dur/fsync-registered!)
                 (write-owed! kb o))
               (catch Throwable _ nil)))
        (throw t))
      (finally (unwatch-stop! kb flag)))))

(defn run-all
  "The pass over every fact in one call, with no budget, no stop and no record: the
  implementation of `vaelii.core/record-arg-types`.  `{:facts n :recorded n :violations
  [v …]}`; the caller files the violations and settles."
  [kb]
  (let [extents (special/arg-type-extents kb)
        st      (pass-state kb (from-the-start) extents)
        vs      (volatile! [])]
    (special/call-with-pass-caches
     kb
     #(doseq [[_ hs] extents, h (sort hs)]
        (let [r (special/draw-fact kb h nil)]
          (vswap! (:recorded st) + (count (:new r)))
          (vswap! vs into (:violations r)))))
    {:facts (:total st) :recorded @(:recorded st) :violations @vs}))
