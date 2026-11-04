;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.pr-status-true-when-test
  "A pull request's status, end to end, in the TRUE-WHEN design: a notifier pushes the
  status transitions, each status is true over the time it held, a watermark says how
  far the record is complete, and the status as of the watermark is read with the time
  region that supports it.  No temporal projection: every answer is read from what was written (level 1), never
  carried forward past it.

  The watermark is written as:

    (ist (CxTimeFn <monad> (IntervalBeforeFn W)) (closed_extent_predicate prStatus))

  — everywhere strictly before W, along the PR's monad, the status record is complete, so
  a status not recorded there is false there rather than unknown.

  Every interval is [start, end), the convention time.txt's `startOf`/`endOf`
  have.  `(IntervalBeforeFn W)` is (…, W) and `(IntervalAfterFn W)` is
  [W, …): the pair meets at W, and W belongs to the after side alone.  The watermark W
  therefore says that every transition before W is in: W itself is outside
  (IntervalBeforeFn W), so the status \"as of W\" is read at the last second before W, and
  at W a status not recorded is unknown.  A query at the exact instant of a transition
  reads the new status, since the new status's stretch starts there and the old one's
  ends there; endpoint contact between two stretches is Allen `meets`, never a clash.

  time.txt declares `IntervalBeforeFn` and `IntervalAfterFn`, each with a backward rule
  giving its bound at W, but the rule reads `(time_point W)`, which no reasoner answers
  for an `InstantFn` term.  So a test that needs a bound states it, the ordinary bound
  each one's meaning fixes.  `prStatus`, `credentialValid` and the request bookkeeping are the test's own domain
  terms, temporaries in the way temporal_capability_test.clj's `StateFn` is.  `CxTimeFn`
  is declared here as that namespace declares it."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

;; The KB is built per test because a test registers reasoners, which a KB shared
;; across tests would keep.
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core-with! '[[CxChange "middle"] [CxRealWorld "middle"]]))))

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
  ;; - as of the watermark, at 23:59:59 on 5 October, the last second before it, the
  ;;   status is Merged, and Draft and Open are false there, by the closed extent the
  ;;   watermark grants and not by any stored negation;
  ;; - at the watermark's own instant, midnight starting 6 October, the closed extent
  ;;   does not reach: the watermark covers the time strictly before it, so Open is
  ;;   unknown there, and so is Merged, whose end is known only to be no earlier than
  ;;   the watermark;
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
          as-of-w1 (slice CxGitHub (at 5 23 59 59))
          at-w1    (slice CxGitHub w1)
          later    (slice CxGitHub (at 10 12 0 0))]
      (transition! kb env Draft DraftStretch (at 1) nil)
      (transition! kb env Open OpenStretch (at 3) DraftStretch)
      (transition! kb env Merged MergedStretch (at 5) OpenStretch)
      (watermark! kb env FirstPush w1 MergedStretch nil)
      (mint! kb as-of-w1 at-w1 later)

      (testing "control: the stretches are ordered, and Merged's end is not before the watermark"
        (is (true? (v/ask? kb (list 'instantBefore (at 1) (at 3)) U)))
        (is (true? (v/ask? kb (list 'instantNotBefore (list 'EndFn MergedStretch) w1) U))))

      (testing "as of the watermark, the last second before it, the status is Merged, and only Merged"
        (is (= [{'?s Merged}] (v/ask kb (list prStatus PR219 '?s) as-of-w1)))
        (is (= :true (verdict kb (status Merged) as-of-w1))))
      (testing "and Draft and Open are false there, by the watermark's closed extent"
        (is (true? (v/ask? kb (list 'not (status Draft)) as-of-w1)))
        (is (true? (v/ask? kb (list 'not (status Open)) as-of-w1)))
        (is (= :false (verdict kb (status Open) as-of-w1))))
      (testing "at the watermark's own instant the closed extent does not reach: (IntervalBeforeFn W) excludes W"
        (is (= :unknown (verdict kb (status Open) at-w1)))
        (is (= :unknown (verdict kb (status Merged) at-w1))))

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

;; ---- the interval pair: before and after a moment w, meeting at w ---------------
;;
;; `(IntervalBeforeFn w)` is (…, w) and `(IntervalAfterFn w)` is [w, …).  Every interval is [start, end), the convention time.txt's `startOf` and
;; `endOf` have, so each member of the pair is stated with one ordinary bound: an
;; `endOf` at w for the before side and a `startOf` at w for the after side.  The two
;; meet at w, share no time, and w belongs to the after side alone.
;;
;; Every Allen row here is red for one reason: `:allen` reads a stored `startOf`/`endOf`
;; fact only when both bounds are named moments on the point network, and every bound here
;; is an `InstantFn` moment, so no Allen relation is derived.  `includesInstant` reads
;; each stated bound as a reading of the side it bounds.
;; `registering-allen-makes-an-entailed-relation-derivable` (public_api_test.clj)
;; composes `before` from two stated `before` facts, never from endpoints, and
;; `a-calendar-term-stops-a-calculus-running-alone` (calendar_test.clj) gets its
;; endpoint-to-relation derivation from the `:calendar` channel reading
;; calendar-constructor fields structurally, a channel `IntervalBeforeFn` and
;; `IntervalAfterFn` do not have.  So a relation between two named intervals answers
;; `:unknown` today whatever it asks.
(defn- interval-pair!
  "Stands up the pair of `w`-relative intervals in `kb`, plus two ordinary dated
  intervals to compare them against.  `before-w` gets an ordinary `endOf` at `w`, which
  `w` is outside; `after-w` gets an ordinary `startOf` at `w`, which `w` is inside.
  `dated-ending-at-w` is the ordinary interval `[2000-01-01, w)`; `dated-starting-at-w` is
  `[w, 2027-01-01)`."
  [kb {:keys [w before-w after-w dated-ending-at-w dated-starting-at-w]}]
  (doseq [i [before-w after-w dated-ending-at-w dated-starting-at-w]]
    (v/assert kb (list 'time_interval i) U))
  (v/assert kb (list 'endOf before-w w) U)
  (v/assert kb (list 'startOf after-w w) U)
  (v/assert kb (list 'startOf dated-ending-at-w (list 'InstantFn 2000 1 1 0 0 0)) U)
  (v/assert kb (list 'endOf dated-ending-at-w w) U)
  (v/assert kb (list 'startOf dated-starting-at-w w) U)
  (v/assert kb (list 'endOf dated-starting-at-w (list 'InstantFn 2027 1 1 0 0 0)) U))

(defn- pair-at
  "The pair's `IntervalBeforeFn`/`IntervalAfterFn` terms at the instant `w`, keyed the way
  `interval-pair!` wants, plus `w` and the caller's two dated-interval individuals."
  [w dated-ending-at-w dated-starting-at-w]
  {:w w
   :before-w            (list 'IntervalBeforeFn w)
   :after-w             (list 'IntervalAfterFn w)
   :dated-ending-at-w   dated-ending-at-w
   :dated-starting-at-w dated-starting-at-w})

(defn- run-allen-table!
  "Runs `table` — each row `[desc goal expected reason]` — as one `is` per row inside a
  `testing` named `desc`, read against `kb` at `ctx`. `reason` is not asserted: it is here
  so a failing row's red reason reads next to the row that fails."
  [kb ctx table]
  (doseq [[desc goal expected _reason] table]
    (testing desc
      (is (= expected (verdict kb goal ctx))))))

(tu/deftest-kb ^:red w-belongs-to-the-after-side-of-the-pair-alone
  ;; w equals before-w's end, so before-w excludes w, and w equals after-w's start, which
  ;; comes before after-w's end, so after-w includes w.  The third row is red: before-w
  ;; states no start, so nothing places the last second before w inside it.
  (v/add-reasoner kb :allen :point :calendar :includes-instant)
  (tu/with-terms [DatedEndingAtW DatedStartingAtW]
    (let [w (at 6)
          {:keys [before-w after-w] :as terms} (pair-at w DatedEndingAtW DatedStartingAtW)]
      (interval-pair! kb terms)
      (run-allen-table!
       kb U
       [["w is not in before-w: before-w ends at w, and an interval excludes its end"
         (list 'includesInstant before-w w) :false]

        ["w is in after-w: after-w starts at w, and an interval includes its start"
         (list 'includesInstant after-w w) :true]

        ["the last second before w is in before-w"
         (list 'includesInstant before-w (at 5 23 59 59)) :true]

        ["the last second before w is not in after-w"
         (list 'includesInstant after-w (at 5 23 59 59)) :false]]))))

(tu/deftest-kb ^:red interval-pair-allen-relations-at-w
  ;; Every row is red for the one reason the comment above interval-pair! gives: no
  ;; shipped reasoner derives an Allen relation from a stored endpoint pair on a
  ;; non-calendar individual, so each row reads :unknown.
  (v/add-reasoner kb :allen :point :calendar :includes-instant)
  (tu/with-terms [DatedEndingAtW DatedStartingAtW]
    (let [w (at 6)
          {:keys [before-w after-w dated-ending-at-w dated-starting-at-w] :as terms}
          (pair-at w DatedEndingAtW DatedStartingAtW)]
      (interval-pair! kb terms)
      (run-allen-table!
       kb U
       [["before-w meets after-w: before-w's end and after-w's start are both w"
         (list 'meets before-w after-w) :true
         "an Allen relation off two stored bounds; no shipped reasoner derives one"]

        ["before-w and after-w are temporally disjoint: meeting at w, they share no time"
         (list 'temporallyDisjoint before-w after-w) :true
         "the derived predicate over the same meets"]

        ["a dated interval ending at w finishes before-w: the two share the end w, and the dated one starts later"
         (list 'finishes dated-ending-at-w before-w) :true
         "needs before-w declared as having no start, not merely no startOf fact stated, and an Allen relation off stored bounds"]

        ["a dated interval ending at w meets after-w"
         (list 'meets dated-ending-at-w after-w) :true
         "an Allen relation off two stored bounds; no shipped reasoner derives one"]

        ["before-w meets a dated interval starting at w"
         (list 'meets before-w dated-starting-at-w) :true
         "an Allen relation off two stored bounds; no shipped reasoner derives one"]

        ["a dated interval starting at w starts after-w: the two share the start w"
         (list 'starts dated-starting-at-w after-w) :true
         "needs after-w declared as having no end, not merely no endOf fact stated; :allen cannot entail a-end < b-end against a wholly unconstrained b-end"]]))))

;; ---- the exact instant of a transition -------------------------------------------
;;
;; A status's stretch is [start, end), so a transition at the instant T ends the old
;; status's stretch at T and starts the new one's there: at T the new status holds and
;; the old one does not.  A pull request queried at its exact merge timestamp reads
;; Merged.  The interval rows read `includesInstant` against the stretches' stored
;; `startOf`/`endOf` facts.  The status rows read a slice keyed by an instant, which the
;; stretch's stated bounds order under the stretch's slice when the instant is inside it.
(defn- merge-at-t!
  "Pushes Draft from 1 October, Open from 3 October and Merged from T, midnight starting
  5 October, along `CxGitHub`, then a watermark at midnight starting 6 October; answers
  the env `transition!` and `watermark!` read."
  [kb {:keys [prStatus CxGitHub PR219 Draft Open Merged
              DraftStretch OpenStretch MergedStretch Push]}]
  (let [env {:prStatus prStatus :monad CxGitHub :pr PR219
             :answersRequest (tu/tmp-pred "answersRequest")
             :pushWatermark (tu/tmp-pred "pushWatermark")}]
    (declare-cxtimefn! kb)
    (v/assert kb (list 'genlCx CxGitHub 'CxWell) U)
    (transition! kb env Draft DraftStretch (at 1) nil)
    (transition! kb env Open OpenStretch (at 3) DraftStretch)
    (transition! kb env Merged MergedStretch (at 5) OpenStretch)
    (watermark! kb env Push (at 6) MergedStretch nil)
    env))

(tu/deftest-kb the-instant-of-a-transition-belongs-to-the-new-stretch
  ;; T is Open's end, which Open's stretch excludes, and Merged's start, which Merged's
  ;; stretch includes.
  (v/add-reasoner kb :allen :point :calendar :includes-instant)
  (tu/with-terms [prStatus CxGitHub PR219 Draft Open Merged
                  DraftStretch OpenStretch MergedStretch Push]
    (merge-at-t! kb {:prStatus prStatus :CxGitHub CxGitHub :PR219 PR219 :Draft Draft
                     :Open Open :Merged Merged :DraftStretch DraftStretch
                     :OpenStretch OpenStretch :MergedStretch MergedStretch :Push Push})
    (run-allen-table!
     kb U
     [["T is in Merged's stretch: the stretch starts at T"
       (list 'includesInstant MergedStretch (at 5)) :true]

      ["T is not in Open's stretch: the stretch ends at T"
       (list 'includesInstant OpenStretch (at 5)) :false]

      ["the last second before T is in Open's stretch"
       (list 'includesInstant OpenStretch (at 4 23 59 59)) :true]

      ["the last second before T is not in Merged's stretch"
       (list 'includesInstant MergedStretch (at 4 23 59 59)) :false]])))

(tu/deftest-kb ^:red a-query-at-the-exact-merge-instant-reads-merged
  ;; The two :false rows, which rest on the watermark's closed extent, read :unknown.
  (v/add-reasoner kb :allen :point :calendar :includes-instant)
  (tu/with-terms [prStatus CxGitHub PR219 Draft Open Merged
                  DraftStretch OpenStretch MergedStretch Push]
    (merge-at-t! kb {:prStatus prStatus :CxGitHub CxGitHub :PR219 PR219 :Draft Draft
                     :Open Open :Merged Merged :DraftStretch DraftStretch
                     :OpenStretch OpenStretch :MergedStretch MergedStretch :Push Push})
    (let [status   (fn [s] (list prStatus PR219 s))
          at-t     (slice CxGitHub (at 5))
          before-t (slice CxGitHub (at 4 23 59 59))]
      (mint! kb at-t before-t)
      (testing "at T, the merge instant, Merged holds"
        (is (= :true (verdict kb (status Merged) at-t))))
      (testing "and Open does not, by the watermark's closed extent"
        (is (= :false (verdict kb (status Open) at-t))))
      (testing "the last second before T, Open holds"
        (is (= :true (verdict kb (status Open) before-t))))
      (testing "and Merged does not"
        (is (= :false (verdict kb (status Merged) before-t)))))))

;; ---- a validity interval [nbf, exp) --------------------------------------------------
;;
;; A credential valid from nbf until exp holds over the stretch [nbf, exp): valid at nbf,
;; dead at exp.  The interval rows read `includesInstant` against the interval's stored
;; `startOf`/`endOf` facts.  The validity rows read a slice keyed by an instant, which the
;; interval's stated bounds order under the interval's slice when the instant is inside it.
(def ^:private nbf (at 7 9 0 0))
(def ^:private exp (at 7 10 0 0))

(defn- validity-interval!
  "States `interval` as [nbf, exp) and `(credentialValid token)` true over it
  along `issuer`, with the issuer's record of `credentialValid` complete before midnight
  starting 8 October."
  [kb {:keys [credentialValid issuer token interval]}]
  (declare-cxtimefn! kb)
  (v/assert kb (list 'genlCx issuer 'CxWell) U)
  (v/assert kb (list 'time_interval interval) U)
  (v/assert kb (list 'startOf interval nbf) U)
  (v/assert kb (list 'endOf interval exp) U)
  (v/assert kb (list credentialValid token) (slice issuer interval))
  (v/assert kb (list 'ist (slice issuer (list 'IntervalBeforeFn (at 8)))
                     (list 'closed_extent_predicate credentialValid))
            U))

(tu/deftest-kb a-validity-interval-includes-nbf-and-excludes-exp
  ;; nbf is the interval's start, which the interval includes, and exp its end, which the
  ;; interval excludes.
  (v/add-reasoner kb :allen :point :calendar :includes-instant)
  (tu/with-terms [credentialValid CxIssuer Token Validity]
    (validity-interval! kb {:credentialValid credentialValid :issuer CxIssuer
                            :token Token :interval Validity})
    (run-allen-table!
     kb U
     [["nbf is in the interval: the interval starts at nbf"
       (list 'includesInstant Validity nbf) :true]

      ["exp is not in the interval: the interval ends at exp"
       (list 'includesInstant Validity exp) :false]

      ["the last second before exp is in the interval"
       (list 'includesInstant Validity (at 7 9 59 59)) :true]])))

(tu/deftest-kb ^:red a-credential-is-valid-at-nbf-and-dead-at-exp
  ;; The two :false rows read :unknown.
  (v/add-reasoner kb :allen :point :calendar :includes-instant)
  (tu/with-terms [credentialValid CxIssuer Token Validity]
    (validity-interval! kb {:credentialValid credentialValid :issuer CxIssuer
                            :token Token :interval Validity})
    (let [valid       (list credentialValid Token)
          at-nbf      (slice CxIssuer nbf)
          at-exp      (slice CxIssuer exp)
          before-nbf  (slice CxIssuer (at 7 8 59 59))
          before-exp  (slice CxIssuer (at 7 9 59 59))]
      (mint! kb at-nbf at-exp before-nbf before-exp)
      (testing "at nbf the credential is valid"
        (is (= :true (verdict kb valid at-nbf))))
      (testing "at exp the credential is not valid, by the issuer's closed extent"
        (is (= :false (verdict kb valid at-exp))))
      (testing "the last second before nbf the credential is not valid"
        (is (= :false (verdict kb valid before-nbf))))
      (testing "the last second before exp the credential is valid"
        (is (= :true (verdict kb valid before-exp)))))))

;; ---- adjacent statuses: endpoint contact is meets, never a clash -----------------
;;
;; `(functional prStatus)` gives a pull request at most one status.  A functional clash
;; is placed at the contexts below both members' contexts, and under [start, end) no
;; instant lies in both Draft's stretch [1 October, 3 October) and Open's stretch [3
;; October, …): the two stretches meet, so no context reads both statuses and no clash
;; is reported.  Two stretches that share a second of time do clash, at that second.
(defn- functional-statuses!
  "Declares `CxTimeFn`, `CxGitHub` and `(functional prStatus)`, and states Draft over
  `draft-stretch` [1 October, `draft-end`) and Open over `open-stretch` [3 October, …)."
  [kb {:keys [prStatus CxGitHub PR219 Draft Open draft-stretch open-stretch]} draft-end]
  (declare-cxtimefn! kb)
  (v/assert kb (list 'genlCx CxGitHub 'CxWell) U)
  (v/assert kb (list 'functional prStatus) U)
  (doseq [i [draft-stretch open-stretch]] (v/assert kb (list 'time_interval i) U))
  (v/assert kb (list 'startOf draft-stretch (at 1)) U)
  (v/assert kb (list 'endOf draft-stretch draft-end) U)
  (v/assert kb (list 'startOf open-stretch (at 3)) U)
  (v/assert kb (list prStatus PR219 Draft) (slice CxGitHub draft-stretch))
  (v/assert kb (list prStatus PR219 Open) (slice CxGitHub open-stretch)))

(tu/deftest-kb adjacent-statuses-meet-without-a-functional-clash
  ;; Draft's stretch ends at 3 October, where Open's starts: no context sees both
  ;; statuses, so neither the KB-wide reading nor the slice at the shared endpoint
  ;; reports a contradiction or a conflict.
  (v/add-reasoner kb :allen :point :calendar :includes-instant)
  (tu/with-terms [prStatus CxGitHub PR219 Draft Open DraftStretch OpenStretch]
    (functional-statuses! kb {:prStatus prStatus :CxGitHub CxGitHub :PR219 PR219
                              :Draft Draft :Open Open
                              :draft-stretch DraftStretch :open-stretch OpenStretch}
                          (at 3))
    (let [at-endpoint (slice CxGitHub (at 3))]
      (mint! kb at-endpoint)
      (testing "no contradiction or conflict KB-wide"
        (is (empty? (v/contradictions kb)))
        (is (empty? (v/conflicts kb))))
      (testing "and none at the shared endpoint"
        (is (empty? (v/contradictions kb at-endpoint)))))))

(tu/deftest-kb ^:red overlapping-statuses-clash-at-a-second-inside-both
  ;; The control for the meets case above: Draft's stretch runs to 4 October, a day
  ;; past Open's start, so noon on 3 October lies in both stretches and the slice there
  ;; reads both statuses.  Red because the slice at an instant is not ordered under the
  ;; stretches holding it, so no context below both members is known and no clash is
  ;; placed: the contradictions read is empty.
  (v/add-reasoner kb :allen :point :calendar :includes-instant)
  (tu/with-terms [prStatus CxGitHub PR219 Draft Open DraftStretch OpenStretch]
    (functional-statuses! kb {:prStatus prStatus :CxGitHub CxGitHub :PR219 PR219
                              :Draft Draft :Open Open
                              :draft-stretch DraftStretch :open-stretch OpenStretch}
                          (at 4))
    (let [inside-both (slice CxGitHub (at 3 12 0 0))]
      (mint! kb inside-both)
      (testing "the slice at noon on 3 October reports one functional clash"
        (is (= [:functional] (mapv :kind (v/contradictions kb inside-both))))))))

;; ---- open-ended stretches: a status still current, and the same status capped ---
;;
;; prStatus's own prose for a status still current reads "Draft from Oct 1 until Now" and
;; "Open from Oct 3 until Now": a stretch with a stated start and no stated end at all,
;; exactly what `transition!` above writes for whichever status is current — no
;; `IntervalBeforeFn`, no watermark, just an ordinary `startOf` with nothing said about
;; where the stretch ends.  Once a later transition caps it, the same stretch reads
;; "Draft from Oct 1 until Oct 3": the ordinary half-open `[Oct 1, Oct 3)` the rest of
;; this namespace uses.
;;
;; Every row below is red for the reason the comment above `interval-pair!` gives:
;; `:allen`/`:point`, registered, do not turn a stored `startOf`/`endOf` pair into a
;; derivable Allen relation for a non-calendar individual at all, so a relation between
;; two named stretches answers `:unknown` today whatever it asks — including every row
;; here, where both ends in question (the open stretches' missing end, the capped
;; stretches' ordinary stated one) are each the half-open shape the pair's `before-w` and
;; `after-w` use.
(defn- open-ended-stretches!
  "Stands up `draft-open` and `open-open` in `kb`, each with only a stated `startOf` and no
  `endOf` — the \"until Now\" shape for whichever status is current — `draft-capped`, the
  same Draft narrowed to end where Open began, and `wider`, an ordinary dated interval
  from 30 September to 4 October to compare `draft-capped` against for containment."
  [kb {:keys [draft-open open-open draft-capped wider]}]
  (doseq [i [draft-open open-open draft-capped wider]]
    (v/assert kb (list 'time_interval i) U))
  (v/assert kb (list 'startOf draft-open (at 1)) U)
  (v/assert kb (list 'startOf open-open (at 3)) U)
  (v/assert kb (list 'startOf draft-capped (at 1)) U)
  (v/assert kb (list 'endOf draft-capped (at 3)) U)
  (v/assert kb (list 'startOf wider (list 'InstantFn 2026 9 30 0 0 0)) U)
  (v/assert kb (list 'endOf wider (at 4)) U))

(tu/deftest-kb ^:red open-ended-stretches-overlap-until-a-later-transition-caps-them
  ;; See the comment above open-ended-stretches! for the one reason every row here is red.
  (v/add-reasoner kb :allen :point :calendar :includes-instant)
  (tu/with-terms [DraftOpen OpenOpen DraftCapped Wider]
    (open-ended-stretches! kb {:draft-open DraftOpen :open-open OpenOpen
                               :draft-capped DraftCapped :wider Wider})
    (run-allen-table!
     kb U
     [["uncapped Draft and uncapped Open overlap: neither stretch has a stated end, so they are not temporally disjoint"
       (list 'temporallyDisjoint DraftOpen OpenOpen) :false]

      ["capped Draft meets Open: Draft's stated end is exactly Open's stated start"
       (list 'meets DraftCapped OpenOpen) :true]

      ["capped Draft and Open are temporally disjoint: meets is one of the relations the complement counts"
       (list 'temporallyDisjoint DraftCapped OpenOpen) :true]

      ["capped Draft sits properly inside the wider 30 September-4 October stretch"
       (list 'during DraftCapped Wider) :true]])))
