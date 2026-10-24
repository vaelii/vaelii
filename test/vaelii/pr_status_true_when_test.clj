;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.pr-status-true-when-test
  "A pull request's status, end to end, in the TRUE-WHEN design: a notifier pushes the
  status transitions, each status is true over the time it held, a watermark says how
  far the record is complete, and the status as of the watermark is read with the time
  region that supports it.  No temporal projection: Iris ruled on 2026-10-24 to start
  with true-when and leave projection for later, so every answer is read from what was
  written (level 1), never carried forward past it.

  The watermark is written as Iris ruled it:

    (ist (CxTimeFn <monad> (IntervalBeforeFn W)) (closed_extent_predicate prStatus))

  — up to and including W, along the PR's monad, the status record is complete, so a
  status not recorded there is false there rather than unknown.

  `IntervalBeforeFn` is not in the shipped KB: time.txt has no function naming the time
  before a moment.  It is used here only inside `^:red` tests, as Iris's ruling spells it.
  `prStatus` and the request bookkeeping are the test's own domain terms, temporaries in
  the way temporal_capability_test.clj's `StateFn` is.  `CxTimeFn` is declared here as
  that namespace declares it.

  W itself is inside (IntervalBeforeFn W): the non-strict form includes its boundary, and
  IntervalStrictlyBeforeFn is the form that excludes it (Iris, 2026-10-24).  Completeness
  through W is therefore inclusive, unlike a status's own [start, end) stretch, and the
  status \"as of W\" is read at W."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core-with! '[[CxChange "middle"] [CxRealWorld "middle"]
                                              [CxNow "middle"] [CxRealWorldNow "middle"]]))))

(def ^:private U 'CxUniverse)

(defn- slice
  "The time-sliced context `(CxTimeFn monad time)`."
  [monad time]
  (list 'CxTimeFn monad time))

(defn- declare-cxtimefn!
  "What docs/context-nat.md declares for `CxTimeFn`, as temporal_capability_test.clj
  declares it."
  [kb]
  (v/assert kb '(result CxTimeFn context) U)
  (v/assert kb '(contextArgSubrelation CxTimeFn 2 subintervalOf) U))

(defn- at
  "The InstantFn moment of October 2026 on `day` at `h`:`m`:`s`."
  ([day] (at day 0 0 0))
  ([day h m s] (list 'InstantFn 2026 10 day h m s)))

(defn- mint!
  "Write a fresh fact into each of `ctxs`, so a read naming one names a real context
  (temporal_capability_test.clj, a-slice-nobody-wrote-into-still-inherits)."
  [kb & ctxs]
  (doseq [c ctxs] (v/assert kb (list (tu/tmp-pred "mint")) c)))

(defn- spelled
  "The context term the `cx/` constant `k` was minted from, or `k` itself."
  [kb k]
  (or (some #(get % '?e) (v/ask kb (list 'natFormula k '?e) U)) k))

(defn- true-in
  "In which contexts is the ground sentence `s` true: the witnesses a variable-context
  read unifies into `?where`, each spelled as a context term.  vaelii.true-in-contexts-test
  states the inverse query and the choice of a symbolic region."
  [kb s]
  (into #{} (map #(spelled kb (get % '?where))) (v/ask kb s '?where)))

(defn- verdict [kb s ctx] (:verdict (v/argue kb s ctx)))

;; ---- the notifier --------------------------------------------------------------

(defn- transition!
  "The notifier's push of one transition: `status` holds from the moment `from` along
  `monad`, true over the stretch `stretch` (a named time_interval that starts at `from`),
  and `previous`, the stretch of the status before it when there is one, ends at `from`.
  A stretch's end is stated only when the next transition arrives, so the current
  status's stretch has a known start and an unknown end."
  [kb {:keys [prStatus monad pr]} status stretch from previous]
  (v/assert kb (list 'time_interval stretch) U)
  (v/assert kb (list 'startOf stretch from) U)
  (when previous (v/assert kb (list 'endOf previous from) U))
  (v/assert kb (list prStatus pr status) (slice monad stretch)))

(defn- watermark!
  "The notifier's push of a watermark `w`: the status record along `monad` is complete
  before `w`, and the current status's stretch `current` has not ended before `w`.  The
  push is `push`, and when it answers an on-demand request, `request` names it."
  [kb {:keys [prStatus monad answersRequest pushWatermark]} push w current request]
  (v/assert kb (list 'ist (slice monad (list 'IntervalBeforeFn w))
                     (list 'closed_extent_predicate prStatus))
            U)
  (v/assert kb (list 'instantNotBefore (list 'EndFn current) w) U)
  (v/assert kb (list pushWatermark push w) monad)
  (when request (v/assert kb (list answersRequest push request) monad)))

(defn- refresh-watermarks
  "The watermarks of the pushes that answer the on-demand request `request`."
  [kb {:keys [monad answersRequest pushWatermark]} request]
  (set (map #(get % '?w)
            (v/query kb [(list answersRequest '?push request) (list pushWatermark '?push '?w)]
                     monad {}))))

(tu/deftest-kb ^:red pr-status-as-of-the-watermark-is-read-with-its-supported-region-and-a-stale-watermark-is-refreshed-on-demand
  ;; One pull request along its own monad, CxGitHub.  The notifier pushes Draft on 1
  ;; October, Open on 3 October and Merged on 5 October, then a watermark at midnight
  ;; starting 6 October.  Read in level 1, with no projection:
  ;;
  ;; - as of the watermark, the status is Merged, and Draft and Open are false there, by
  ;;   the closed extent the watermark grants and not by any stored negation;
  ;; - Merged's supported region is its stretch: it starts on 5 October, that start is
  ;;   inside it, no end is answered (none was guessed), and the end is known to be no
  ;;   earlier than the watermark;
  ;; - on 10 October, after the watermark, nothing is known: neither Merged nor its
  ;;   absence.
  ;;
  ;; Then the asker requests a refresh with id R1.  A notification queued before the
  ;; request arrives first: it carries the earlier request id R0 and a watermark of 8
  ;; October.  It is not the refresh — it answers no R1, and 10 October is still past its
  ;; watermark, so the re-ask is still unknown.  The push answering R1 carries a
  ;; watermark of 11 October, and the re-ask on 10 October answers from it.
  ;;
  ;; Today nothing ships IntervalBeforeFn, and no slice keyed by an instant is ordered
  ;; under the interval holding it, so no read at a moment sees the stretches or the
  ;; watermark's grant.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar :point :includes-instant)
  (tu/with-terms [prStatus answersRequest pushWatermark CxGitHub PR219
                  Draft Open Merged DraftStretch OpenStretch MergedStretch
                  FirstPush QueuedPush RefreshPush R0 R1]
    (v/assert kb (list 'genlCx CxGitHub 'CxWell) U)
    (let [env      {:prStatus prStatus :monad CxGitHub :pr PR219
                    :answersRequest answersRequest :pushWatermark pushWatermark}
          status   (fn [s] (list prStatus PR219 s))
          w1       (at 6)
          as-of-w1 (slice CxGitHub w1)
          later    (slice CxGitHub (at 10 12 0 0))]
      (transition! kb env Draft DraftStretch (at 1) nil)
      (transition! kb env Open OpenStretch (at 3) DraftStretch)
      (transition! kb env Merged MergedStretch (at 5) OpenStretch)
      (watermark! kb env FirstPush w1 MergedStretch nil)
      (mint! kb as-of-w1 later)

      (testing "control: the stretches are ordered, and Merged's end is not before the watermark"
        (is (true? (v/ask? kb (list 'instantBefore (at 1) (at 3)) U)))
        (is (true? (v/ask? kb (list 'instantNotBefore (list 'EndFn MergedStretch) w1) U))))

      (testing "as of the watermark the status is Merged, and only Merged"
        (is (= [{'?s Merged}] (v/ask kb (list prStatus PR219 '?s) as-of-w1)))
        (is (= :true (verdict kb (status Merged) as-of-w1))))
      (testing "and Draft and Open are false there, by the watermark's closed extent"
        (is (true? (v/ask? kb (list 'not (status Draft)) as-of-w1)))
        (is (true? (v/ask? kb (list 'not (status Open)) as-of-w1)))
        (is (= :false (verdict kb (status Open) as-of-w1))))

      (testing "Merged's supported region is its stretch along CxGitHub"
        (is (= #{(slice CxGitHub MergedStretch)} (true-in kb (status Merged)))))
      (testing "which starts on 5 October, inclusively"
        (is (= [{'?i (at 5)}] (v/ask kb (list 'startOf MergedStretch '?i) U)))
        (is (true? (v/ask? kb (list 'includesInstant MergedStretch (at 5)) U))))
      (testing "and has no end answered, only an end no earlier than the watermark"
        (is (empty? (v/ask kb (list 'endOf MergedStretch '?i) U)))
        (is (true? (v/ask? kb (list 'instantNotBefore (list 'EndFn MergedStretch) w1) U))))

      (testing "after the watermark nothing is projected: on 10 October the status is unknown"
        (is (= :unknown (verdict kb (status Merged) later)))
        (is (= :unknown (verdict kb (status Open) later))))

      ;; the refresh: request R1, an older queued notification first, then the answer
      (watermark! kb env QueuedPush (at 8) MergedStretch R0)
      (testing "the queued notification is not the refresh: it answers R0, not R1"
        (is (= #{} (refresh-watermarks kb env R1)))
        (is (= #{(at 8)} (refresh-watermarks kb env R0))))
      (testing "and 10 October is past its watermark, so the re-ask is still unknown"
        (is (= :unknown (verdict kb (status Merged) later)))
        (is (= :unknown (verdict kb (status Open) later))))

      (watermark! kb env RefreshPush (at 11) MergedStretch R1)
      (testing "the push answering R1 refreshes the watermark to 11 October"
        (is (= #{(at 11)} (refresh-watermarks kb env R1))))
      (testing "and the re-ask on 10 October answers from it: Merged, and Open false"
        (is (= [{'?s Merged}] (v/ask kb (list prStatus PR219 '?s) later)))
        (is (= :true (verdict kb (status Merged) later)))
        (is (= :false (verdict kb (status Open) later))))
      (testing "Merged's supported region is still its stretch, now known to last to 11 October"
        (is (= #{(slice CxGitHub MergedStretch)} (true-in kb (status Merged))))
        (is (true? (v/ask? kb (list 'instantNotBefore (list 'EndFn MergedStretch) (at 11)) U)))
        (is (empty? (v/ask kb (list 'endOf MergedStretch '?i) U)))))))
