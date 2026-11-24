;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.kb-concurrency-test
  "A reader thread beside the writer, one level up from the network.

  `vaelii.jtms-concurrency-test` holds the same guarantee for the truth-maintenance
  structures themselves.  This is the guarantee **through the API**: the reads an
  application actually makes — `sentexes-matching`, the `genl` closure, and belief off a
  handle — while a writer asserts and retracts in bursts.  Those reads cross more state
  than the TMS: the index postings, the record store behind them, the taxonomy closure
  caches, and the literal-match cache, each of which the writer is moving.

  Four things must hold, and they are what the checks below count:

  - **No reader ever throws.**  An index posting is written before the record it points
    at is, and swept after — a read that caught either gap on an unsynchronized
    structure would fault or hand back nothing.
  - **Nothing is invented.**  Every sentence a read returns is one the writer wrote.  A
    torn posting is not a wrong answer that looks plausible; it is content from another
    handle, which is what makes this the check worth having.
  - **A read is internally consistent.**  A sentex a match returns carries its own
    sentence and handle — the posting resolved to a record inside the one read, rather
    than to a hole the sweep had already made.
  - **Locality holds under load.**  The writer churns one region; a monotonic fact and a
    taxonomy edge *outside* it are believed and true at every sample, never briefly
    false while a relabel or a closure recompute passes over something else.

  **A settle is published once.**  A settle lifts every standing defeat before it
  re-decides any, so the tests at the foot of this file seed a standing contradiction and
  read its loser beside a settle: the reader reads the belief the settle began from, and
  the writer decides on its own network and on no cache entry the reader filled.

  Both representations run, in one test, with the same assertions either way — the
  reference (persistent maps, consistent by construction) is the control, and the dense
  network (bitmaps mutated in place under a `StampedLock`) is the claim the default
  rests on.  Which one the suite's own KBs use (`VAELII_TEST_TMS`) changes nothing
  here: each arm names its representation."
  (:require [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.literal-cache :as literal-cache]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(def ^:private pool
  "The individuals the writer churns.  A fixed pool, so \"nothing invented\" is a set
  membership rather than a pattern match."
  (mapv #(symbol (str "Churn" %)) (range 8)))

(def ^:private burst-ms
  "How long one representation's writer churns.  Long enough that a reader samples the
  middle of many bursts and not only their edges; short enough that both arms and the
  suite around them stay a test rather than a run."
  2500)

(defn- seed!
  "The fixed region — believed throughout, and never written again — plus the rule that
  makes the churned region derive something."
  [kb]
  (v/assert kb '(genl dog animal) 'CxUniverse {:strength :monotonic})
  (v/assert kb '(genl animal thing) 'CxUniverse {:strength :monotonic})
  (v/assert-rule kb '[(dog ?x)] '(likes ?x Water) 'CxUniverse)
  (v/assert kb '(dog Anchor) 'CxUniverse {:strength :monotonic})
  (v/handle-of kb '(dog Anchor) 'CxUniverse))

(defn- known-sentences
  "Every sentence the writer can ever have written, as a set — the churned facts, what
  the rule concludes from them, and the fixed region."
  []
  (into #{'(genl dog animal) '(genl animal thing) '(dog Anchor) '(likes Anchor Water)
          '(genl churn_kind animal)}
        (mapcat (fn [x] [(list 'dog x) (list 'likes x 'Water)]))
        pool))

(defn- stress
  "Run the readers-beside-a-writer stress on a KB using `tms` and report what the readers
  saw: `{:errors [...] :invented n :torn n :stale n :reads n :writes n}`."
  [tms]
  (let [kb      (v/open-kb {:backend :memory :space [::kb-concurrency tms]
                            :tms tms :recover? false})
        _       (tu/clear-kb! kb)
        anchor  (seed! kb)
        known   (known-sentences)
        stop    (atom false)
        errs    (atom [])
        invented (atom 0)
        torn    (atom 0)
        stale   (atom 0)
        reads   (atom 0)
        writes  (atom 0)
        reader  (fn []
                  (try
                    (while (not @stop)
                      (let [ms (v/sentexes-matching kb '(likes ?x Water) 'CxUniverse)]
                        (doseq [sx ms]
                          (when-not (contains? known (:sentence sx)) (swap! invented inc))
                          (when-not (and (:sentence sx) (integer? (:id sx)))
                            (swap! torn inc))))
                      ;; the region the writer never touches: a relabel or a closure
                      ;; recompute over the churned region must not pass through it
                      (when-not (v/genl? kb 'dog 'thing)          (swap! stale inc))
                      (when-not (v/isa? kb 'Anchor 'animal)       (swap! stale inc))
                      (when-not (v/believed? kb anchor 'CxUniverse) (swap! stale inc))
                      (swap! reads inc))
                    (catch Throwable t (swap! errs conj t))))
        writer  (future
                  (try
                    (let [deadline (+ (System/currentTimeMillis) (long burst-ms))]
                      (while (< (System/currentTimeMillis) deadline)
                        ;; a burst: every churned fact in, then every one out, so the
                        ;; rule's conclusions are minted and swept each pass
                        (let [hs (mapv #(v/assert kb (list 'dog %) 'CxUniverse) pool)]
                          (doseq [h hs] (v/retract! kb h)))
                        ;; and a taxonomy edge, which moves the genl closure the readers
                        ;; are asking about the *other* side of
                        (let [h (v/assert kb '(genl churn_kind animal) 'CxUniverse)]
                          (v/retract! kb h))
                        (swap! writes inc)))
                    (finally (reset! stop true))))
        rs      (mapv (fn [_] (future (reader))) (range 3))]
    @writer
    (run! deref rs)
    (tu/clear-kb! kb)
    {:errors @errs :invented @invented :torn @torn :stale @stale
     :reads @reads :writes @writes}))

(defn- check!
  "The four claims, asserted the same number of times for either representation."
  [label {:keys [errors invented torn stale reads writes]}]
  (is (empty? errors)
      (str label ": a reader faulted beside the writer — "
           (when-let [^Throwable t (first errors)]
             (str (class t) ": " (.getMessage t)))))
  (is (zero? invented)
      (str label ": a read returned a sentence the writer never wrote (" invented ")"))
  (is (zero? torn)
      (str label ": a match returned a sentex with no sentence or no handle (" torn ")"))
  (is (zero? stale)
      (str label ": a fact or taxonomy edge outside the churned region read false ("
           stale ") — a relabel or a closure recompute reached past its region"))
  (is (pos? reads) (str label ": the readers never ran"))
  (is (pos? writes) (str label ": the writer never completed a burst")))

(deftest ^:slow kb-reads-stay-consistent-under-a-concurrent-writer
  ;; Both representations in one test, so the count is the same however the suite's own
  ;; KBs are configured — `VAELII_TEST_TMS` picks what `tu/fresh` builds and has no say
  ;; over the two KBs here.
  (doseq [tms [:dense :reference]]
    (check! (name tms) (stress tms))))

(deftest a-match-computed-across-a-tms-call-is-not-served-after-it
  ;; A TMS call moves the change clock and then the network.  The writer's call is parked
  ;; between the two, and a reader on this thread computes `(perch ?x)` there: it reads the
  ;; moved clock and the network before the call, and installs its answer in the literal
  ;; cache under that clock.  Once the call has taken `(perch Robin)` out of force, a read
  ;; at the clock the call leaves behind must not be served the reader's answer.
  (doseq [tms [:dense :reference]]
    (let [kb      (v/open-kb {:backend :memory :space [::clock-order tms]
                              :tms tms :recover? false})
          _       (tu/clear-kb! kb)
          h       (v/assert kb '(perch Robin) 'CxUniverse)
          writer  (promise)
          armed   (atom true)
          parked  (promise)
          release (promise)
          bump    @#'observe/note-change
          answer  #(set (map '?x (v/query kb '(perch ?x) 'CxUniverse)))]
      (with-redefs [observe/note-change
                    (fn [clk]
                      (let [c (bump clk)]
                        (when (and (realized? writer)
                                   (identical? (Thread/currentThread) @writer)
                                   (compare-and-set! armed true false))
                          (deliver parked true)
                          @release)
                        c))]
        (let [w (future (deliver writer (Thread/currentThread))
                        (jtms/suspend-premise (reasoning/tms kb) h)
                        (answer))]
          (is (true? (deref parked 10000 false)) (str (name tms) ": the writer never parked"))
          (is (= '#{Robin} (answer))
              (str (name tms) ": the reader reads the network before the call"))
          (deliver release true)
          (is (= #{} (deref w 10000 ::timeout))
              (str (name tms) ": the writer read the reader's answer about the network"
                   " before its own call"))
          (is (false? (v/believed? kb h 'CxUniverse)))
          (is (= #{} (answer))
              (str (name tms) ": a read after the call read the answer computed across it"))))
      (tu/clear-kb! kb))))

;; ---- a settle publishes once ------------------------------------------------------
;;
;; A reader beside a settle reads the belief the settle began from, and then the belief it
;; reached; never one in between.

(defn- standing-contradiction!
  "A KB on `tms` holding a standing contradiction whose `:default` member loses: globally
  when `scoped?` is false, and at the vantage `CxLow` below the loser's own context `CxTop`
  when it is true.  Answers `[kb loser vantage home]`, the context the loser is withdrawn
  from and the one it is stored in."
  [tms scoped?]
  (let [kb (v/open-kb {:backend :memory :space [::standing tms scoped?] :tms tms :recover? false})]
    (tu/clear-kb! kb)
    (let [[home vantage] (if scoped? '[CxTop CxLow] '[CxUniverse CxUniverse])]
      (when scoped?
        (v/assert kb '(genlCx CxTop CxUniverse) 'CxUniverse)
        (v/assert kb '(genlCx CxLow CxTop) 'CxUniverse))
      (v/assert kb '(flies Tweety) home)
      (v/assert kb '(not (flies Tweety)) vantage {:strength :monotonic})
      [kb (v/handle-of kb '(flies Tweety) home) vantage home])))

(defn- loser-reading
  "What a reader reads about `loser`: the network's label, its belief at the vantage and
  at its own context, and whether a match at the vantage returns it."
  [kb loser vantage home]
  {:in?          (v/believed? kb loser)
   :at-vantage   (v/believed? kb loser vantage)
   :at-home      (v/believed? kb loser home)
   :matched      (boolean (some #(= loser (:id %))
                                (v/sentexes-matching kb '(flies Tweety) vantage)))})

(deftest a-reader-beside-a-settle-reads-the-belief-the-settle-began-from
  ;; The writer asserts an unrelated fact, and its settle is parked at one of two points:
  ;; inside a pass, and before it publishes the readers' readings.  A reader on this thread
  ;; reads the loser there, and must read what it read before the settle.
  (doseq [tms   [:dense :reference]
          scoped? [false true]
          park  [#'settle/drain-recheck! #'settle/defeat-moves]]
    (let [[kb loser vantage home] (standing-contradiction! tms scoped?)
          label   (str (name tms) (if scoped? " scoped" " global") " at " (:name (meta park)))
          before  (loser-reading kb loser vantage home)
          armed   (atom true)
          parked  (promise)
          release (promise)
          orig    @park]
      (is (false? (:at-vantage before)) (str label ": the seed does not defeat the loser"))
      (let [during (with-redefs-fn {park (fn [& args]
                                           (when (compare-and-set! armed true false)
                                             (deliver parked true)
                                             @release)
                                           (apply orig args))}
                     (fn []
                       (let [w (future (v/assert kb '(noise Kay) 'CxUniverse))]
                         (try
                           (when (deref parked 10000 false)
                             (loser-reading kb loser vantage home))
                           (finally (deliver release true) (deref w 10000 nil))))))]
        (is (= before during)
            (str label ": a reader beside the settle read the loser as the settle held it"))
        (is (= before (loser-reading kb loser vantage home))
            (str label ": the settle reached the belief it began from")))
      (tu/clear-kb! kb))))

(deftest a-held-reader-and-the-writer-share-no-cache-entry
  ;; While a settle holds belief, a reader derives what it reads from the belief the
  ;; settle began from, and the writer from the network it is deciding.  The change clock
  ;; each keys a cache entry by keeps the two apart, in both directions.
  (let [clk    (observe/new-clock)
        cache  (atom {})
        opened (promise)
        done   (promise)
        writer (future
                 (let [h (observe/new-hold)]
                   (observe/open-hold! h clk)
                   (try
                     (deliver opened (observe/change-clock clk))
                     @done
                     (literal-cache/lookup clk cache ::k (constantly [:writer]))
                     (finally (observe/close-hold! h clk)))))
        wclock (deref opened 10000 nil)]
    (is (and wclock (not (neg? (long wclock)))) "the writer reads the clock itself")
    (is (neg? (observe/change-clock clk)) "a reader beside the hold reads a clock no writer keys by")
    (is (= [:reader] (vec (literal-cache/lookup clk cache ::k (constantly [:reader])))))
    (deliver done true)
    (is (= [:writer] (vec @writer)) "the writer computes past the reader's entry")
    (is (not (neg? (observe/change-clock clk))) "a closed hold leaves the reader on the clock")
    (is (not= [:reader] (vec (literal-cache/lookup clk cache ::k (constantly [:after]))))
        "nor does a reader after the hold read the entry a held reader stored")))

(deftest ^:slow a-standing-loser-never-reads-believed-beside-a-writer
  ;; The probe behind the settle's hold: every settle lifts the standing defeat, including
  ;; one for an unrelated fact, so a reader looping on the loser while the writer asserts
  ;; unrelated facts reads it believed on a share of its reads unless the settle holds.
  (doseq [tms [:dense :reference]]
    (let [[kb loser vantage home] (standing-contradiction! tms false)
          stop   (atom false)
          reads  (atom 0)
          hits   (atom 0)
          errs   (atom [])
          reader (future
                   (while (not @stop)
                     (try
                       (swap! reads inc)
                       (let [r (loser-reading kb loser vantage home)]
                         (when (or (:in? r) (:at-vantage r) (:matched r)) (swap! hits inc)))
                       (catch Throwable t (swap! errs conj t)))))]
      (try
        (dotimes [i 400] (v/assert kb (list 'noise (symbol (str "Kay" i))) 'CxUniverse))
        (finally (reset! stop true) @reader))
      (is (empty? @errs) (str (name tms) ": a reader threw beside the writer"))
      (is (pos? @reads) (str (name tms) ": the reader never ran"))
      (is (zero? @hits)
          (str (name tms) ": " @hits " of " @reads " reads beside the writer read the loser"))
      (tu/clear-kb! kb))))

(defn- holding
  "Run `f` on a fresh thread that owns an open hold on the KB whose clock is `clk`, and
  answer what `f` answers."
  [clk f]
  @(future (let [h (observe/new-hold)]
             (observe/open-hold! h clk)
             (try (f) (finally (observe/close-hold! h clk))))))

(deftest a-hold-on-one-kb-leaves-another-kb-s-reader-on-its-clock
  (let [open (fn [tag] (v/open-kb {:backend :memory :space [::two-kb-hold tag] :recover? false}))
        a    (open :a)
        b    (open :b)
        lm   #(select-keys (literal-cache/stats a) [:hits :misses])]
    (try
      (tu/with-terms [livesIn Ann Dover]
        (let [ask    #(doall (res/matches-visible a (list livesIn '?x Dover) 'CxUniverse))
              _      (v/assert a (list livesIn Ann Dover) 'CxUniverse)
              _      (dotimes [_ 2] (ask))
              opened (promise)
              done   (promise)
              holder (future (holding (:clock b) #(do (deliver opened true) @done)))]
          (is (true? (deref opened 10000 false)))
          (let [before (lm)]
            (ask)
            (is (= (update before :hits inc) (lm)) "A's entry is a hit while B's hold is open"))
          (deliver done true)
          (deref holder 10000 nil)
          (let [before (lm)]
            (ask)
            (is (= (update before :hits inc) (lm)) "A's entry is a hit after B's hold closes"))))
      (finally (doseq [kb [a b]] (v/clear! kb) (v/close! kb))))))

(deftest a-thread-holding-one-kb-reads-another-kb-s-settle-as-it-began
  (doseq [tms   [:dense :reference]
          scoped? [false true]
          park  [#'settle/drain-recheck! #'settle/defeat-moves]]
    (let [[kb loser vantage home] (standing-contradiction! tms scoped?)
          other   (v/open-kb {:backend :memory :space [::holding-reader tms] :tms tms :recover? false})
          label   (str (name tms) (if scoped? " scoped" " global") " at " (:name (meta park)))
          _       (v/retract! kb (v/handle-of kb '(not (flies Tweety)) vantage))
          before  (loser-reading kb loser vantage home)
          armed   (atom true)
          parked  (promise)
          release (promise)
          orig    @park]
      (try
        (let [during (with-redefs-fn {park (fn [& args]
                                             (when (compare-and-set! armed true false)
                                               (deliver parked true)
                                               @release)
                                             (apply orig args))}
                       (fn []
                         (let [w (future (v/assert kb '(not (flies Tweety)) vantage
                                                   {:strength :monotonic}))]
                           (try
                             (when (deref parked 10000 false)
                               (holding (:clock other) #(loser-reading kb loser vantage home)))
                             (finally (deliver release true) (deref w 10000 nil))))))]
          (is (= before during) (str label ": a thread holding another KB's hold read the denial's settle live"))
          (is (not= before (loser-reading kb loser vantage home)) (str label ": the denial moved the loser")))
        (finally (tu/clear-kb! kb) (v/close! other))))))
