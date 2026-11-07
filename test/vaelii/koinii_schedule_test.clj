;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.koinii-schedule-test
  "A koinii scheduling conversation, over real calendar dates.  Three teammates — Ada, Bo
  and Cyra — try to book a design review before their sprint ends, and the KB carries the
  whole discussion: the date proposed, who cannot make it, the reasons, the ballots, the
  dispute standing open while the house is split, the majority that settles it, and — when
  the calendar is over-constrained enough that no hand-agreement is possible — the answer
  the ASP solver finds that the team could not.  Every move is a sentex, so afterwards a
  plain query answers 'what date, who objected, why, and how it was decided.'

  Dates are `DatetimeFn` terms (`docs/nat.md`, `docs/context-nat.md`) — `(DatetimeFn
  \"2026-03-10\")` is Tuesday the 10th — asserted as ordinary koinii claim content and read
  back by calendar containment (`datetime/subinterval?`: is the chosen day inside the sprint
  month?).  Two shapes of the same story:

  - **the argument** (in-process, no solver) — Ada proposes a date, Bo (away that day)
    disputes it, the house is split 1-1 and stays OPEN (Priest's LP), and a third
    ballot carries it 2-1.  Composes the koinii dispute reads, the channel, and majority
    adjudication — the roommates story, but the subject is a calendar date.
  - **the solve** (guarded on the ASP solver) — the team's availability is over-constrained:
    every candidate day is blocked by someone, so `do/label` finds ZERO feasible schedules
    (the conflict, as answer-set unsatisfiability).  Then Cyra frees a day, and the solver
    returns the ONE date that works — real constraint solving over the calendar, resolving a
    schedule the teammates could not settle by hand (`docs/solving.md`, `docs/labeling.md`).

  Plain `deftest`s, each over its own fresh KB (not the net-neutral `deftest-kb` fixture):
  `do/label` materializes an inert labeling context that the teardown check would flag as a
  leak, which is why every solving test builds a disposable KB instead.  The solve degrades:
  with no clingo/clasp present `(solver/available?)` is false and that test no-ops."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.datetime :as dt]
            [vaelii.impl.sentex :as sx]
            [vaelii.koinii.adjudication :as adj]
            [vaelii.koinii.channel :as ch]
            [vaelii.koinii.dispute :as d]
            [vaelii.koinii.identity :as id]
            [vaelii.koinii.speech-acts :as sa]
            [vaelii.test-util :as tu]))

(defn- schedule-kb []
  (doto (tu/empty-kb) (tu/load-core!) (sa/load-speech-acts)
        (v/assert '(unreifiable_function DatetimeFn) 'CxUniverse)))

;; Majority resolution requires the :proof-tier identity policy and counts only attested
;; ballots, so these tests run under it and vote through `vote!`.
(use-fixtures :each (fn [f] (binding [id/*policy* :proof-tier] (f))))

(defn- vote!
  "Cast `agent`'s attested `stance` ballot on `claim-h`, under a `:proof-tier` principal
  whose credential is its id."
  [kb agent stance claim-h]
  (adj/cast-ballot kb (id/authenticate {:claimed-id agent :credential agent}
                                       {:policy :proof-tier :verify-fn (fn [a c] (= a c))})
                   stance claim-h))

(def ^:private asp? (solver/available?))

;; the sprint runs across March 2026; the review must fall inside it
(def ^:private sprint '(DatetimeFn "2026-03"))
(def ^:private mon '(DatetimeFn "2026-03-09"))   ; Monday the 9th
(def ^:private tue '(DatetimeFn "2026-03-10"))   ; Tuesday the 10th
(def ^:private wed '(DatetimeFn "2026-03-11"))   ; Wednesday the 11th

(defn- dispute-id [kb] (:dispute-id (first (d/disputes-in kb 'CxSchedule))))

(defn- reasons-for
  "The grounds of every justification naming `target-h`, as a set — 'the reasons on record
  for this claim', a plain query."
  [kb target-h]
  (->> (v/sentexes-matching kb (list 'justifies '?a '?g (sx/sentex-handle target-h)) '?ctx)
       (map #(nth (:sentence %) 2)) set))

;; ── the argument: a date proposed, an objection, a 1-1 split, a tiebreaker ──

(deftest a-team-argues-over-a-date-and-a-majority-settles-it
  (let [kb   (schedule-kb)
        ada  (ch/join (ch/local kb) 'CxSchedule 'AgentAda)   ; proposes the 10th
        bo   (ch/join (ch/local kb) 'CxSchedule 'AgentBo)    ; away the 10th
        cyra (ch/join (ch/local kb) 'CxSchedule 'AgentCyra)  ; the tiebreaker
        proposal (list 'meetsOn 'Review tue)
        ph   (ch/assert ada proposal)]                      ; Ada: "let's meet Tuesday the 10th"
    (ch/justify ada 'FallsInThisSprint ph)

    (testing "the proposed date is a real calendar term, inside the sprint window"
      (is (dt/datetime-term? tue))
      (is (dt/subinterval? tue sprint) "Tuesday the 10th is in March 2026"))

    ;; Bo states his own availability, then disputes the date
    (ch/assert bo (list 'unavailableOn 'AgentBo tue))
    (ch/dispute bo ph)                                       ; asserts ¬proposal + a disputes edge
    (let [nope-h (v/handle-of kb (list 'not proposal) 'CxBo)] ; the rebuttal lives in Bo's context
      (ch/justify bo 'AwayThatDay nope-h)                    ; his reason attaches to HIS side
      (testing "Bo's objection makes the date a live dispute — nobody is wrong yet"
        (is (d/disputed? kb proposal 'CxSchedule))
        (is (= :contradiction (:verdict (v/argue kb proposal 'CxSchedule))))
        (is (v/ask? kb proposal 'CxSchedule) "Ada's proposal still stands")
        (is (v/ask? kb (list 'not proposal) 'CxSchedule) "and so does Bo's objection"))

      ;; Cyra asks the group; Ada answers
      (let [q (ch/pose-query cyra 'CanEveryoneMakeTheTenth)]
        (ch/answer ada 'AdaAndCyraCan q)
        (is (= 'AdaAndCyraCan (ch/answer-content (first (ch/answers-to cyra q))))))

      (let [id (dispute-id kb)]
        (vote! kb 'AgentAda :for ph)
        (vote! kb 'AgentBo :against ph)
        (testing "1-1 leaves the date undecided — the split house stays open"
          (is (= :tie (:outcome (adj/resolve-by-majority kb id ph 'CxSchedule))))
          (is (d/disputed? kb proposal 'CxSchedule)))

        (testing "Cyra breaks it 2-1 — the review is booked for the 10th, over Bo's objection"
          (vote! kb 'AgentCyra :for ph)
          (let [r (adj/resolve-by-majority kb id ph 'CxSchedule)]
            (is (= {:for 2 :against 1} (select-keys r [:for :against])))
            (is (= :for (:outcome r)))
            (is (not (d/disputed? kb proposal 'CxSchedule)) "the date is settled")
            (is (= :true (:verdict (v/argue kb proposal 'CxSchedule))))
            (is (= 'AgentMajority (:arbiter (adj/who-ruled kb (:ruling r))))
                "recorded as the house's call, not a chair's decree")

            (testing "the whole discussion is recoverable — the date, the reasons, the objection"
              (is (= tue (nth (:sentence (v/sentex kb ph)) 2)) "the booked date")
              (is (dt/subinterval? tue sprint) "and it is inside the sprint")
              (is (= 'AgentAda (:creator (v/provenance kb ph))) "Ada proposed it")
              (is (= #{'FallsInThisSprint} (reasons-for kb ph)) "Ada's reason for the 10th")
              (is (= #{'AwayThatDay} (reasons-for kb nope-h)) "and Bo's reason against")
              (is (v/ask? kb (list 'unavailableOn 'AgentBo tue) 'CxBo)
                  "Bo's conflict is still on record — outvoted, not erased"))

            (testing "reversible: retract the ruling and the date is contested again"
              (v/retract! kb (:ruling r))
              (is (d/disputed? kb proposal 'CxSchedule)))))))))

;; ── the solve: over-constrained by hand, the ASP solver finds the one date ──
;;
;; The team's three candidate days are each blocked by exactly one member, so no date
;; suits everyone and no vote can help — the disagreement is not about preference but
;; about feasibility.  The scheduler hands the availability to the answer-set solver:
;; a choice rule (the review may fall on any candidate day), a hard constraint (never on
;; a day a member is unavailable), `functional` (at most one day), and a negated-choice
;; at-least-one (some day must be picked).  Over-constrained → ZERO answer sets.  Free one
;; day → exactly one, and the solver names the date.

(defn- install-scheduling-rules!
  "The shared scheduling policy, in the channel `ctx`: the candidate days, the choice rule,
  and the constraints the solver reads."
  [kb ctx]
  (doseq [m '[AgentAda AgentBo AgentCyra]] (v/assert kb (list 'memberOf m 'Team) ctx))
  (doseq [day [mon tue wed]] (v/assert kb (list 'candidate_day day) ctx))
  ;; choice: the review may be scheduled on any candidate day
  (v/assert kb (list 'set/assumptionRule
                     (list 'implies (list 'candidate_day '?d) (list 'meetsOn 'Review '?d))) ctx)
  ;; at most one day
  (v/assert kb '(functional meetsOn) ctx {:strength :monotonic})
  ;; hard: never meet on a day a member is unavailable
  (v/assert kb (list 'set/hardConstraint
                     (list 'implies
                           (list 'and (list 'meetsOn 'Review '?d) (list 'memberOf '?p 'Team)
                                 (list 'unavailableOn '?p '?d))
                           (list 'clash '?p '?d))) ctx)
  ;; hard at-least-one: the review must land on SOME candidate day (a negated-choice
  ;; constraint anchored on a positive domain literal, the way the bench recipe anchors it)
  (v/assert kb '(scheduled_meeting Review) ctx {:strength :monotonic})
  (v/assert kb (list 'set/hardConstraint
                     (list 'implies
                           (list 'and (list 'scheduled_meeting '?m)
                                 (list 'not (list 'meetsOn '?m mon))
                                 (list 'not (list 'meetsOn '?m tue))
                                 (list 'not (list 'meetsOn '?m wed)))
                           (list 'unscheduled '?m))) ctx))

(defn- solve-schedule
  "Run the solver from the channel and return `{:count :date}`: the number of feasible
  schedules, and the single scheduled date (nil if none).  `do/label` in `:all` mode
  enumerates every feasible assignment; the labelings are inert (materialized aside), so
  base belief is untouched."
  [kb into]
  (let [r (v/assert kb (list 'do/label 'CxSchedule into :all) 'CxSchedule)]
    {:count (:count r)
     :date  (some (fn [l] (some (fn [s] (when (= 'meetsOn (first s)) (nth s 2))) (:true l)))
                  (:labelings r))}))

(deftest the-solver-schedules-a-date-the-team-could-not-agree
  (when asp?
    (let [kb   (schedule-kb)
          ada  (ch/join (ch/local kb) 'CxSchedule 'AgentAda)
          bo   (ch/join (ch/local kb) 'CxSchedule 'AgentBo)
          cyra (ch/join (ch/local kb) 'CxSchedule 'AgentCyra)]
      (install-scheduling-rules! kb 'CxSchedule)
      ;; each teammate states their OWN unavailability (a claim in their own context, which
      ;; the channel sees up the genlCx ancestor set) — and between them every day is blocked
      (ch/assert ada  (list 'unavailableOn 'AgentAda tue))   ; Ada out Tuesday
      (ch/assert bo   (list 'unavailableOn 'AgentBo  wed))   ; Bo out Wednesday
      (let [cyra-h (ch/assert cyra (list 'unavailableOn 'AgentCyra mon))]  ; Cyra out Monday

        (testing "over-constrained: no candidate day works for everyone — zero schedules"
          (let [{:keys [count date]} (solve-schedule kb 'CxSchedPlanA)]
            (is (= 0 count) "the answer-set solver finds the calendar unsatisfiable")
            (is (nil? date) "so no date is scheduled — the conflict, made precise")))

        (testing "Cyra frees up Monday; now exactly one date works, and the solver names it"
          (sa/retract-move kb cyra-h)                          ; the koinii 'retracts' move
          (let [{:keys [count date]} (solve-schedule kb 'CxSchedPlanB)]
            (is (= 1 count) "a unique feasible schedule")
            (is (= mon date) "Monday the 9th — the only day no one is out")
            (is (dt/subinterval? date sprint) "and it falls inside the sprint")))

        (testing "the agreed date is recorded back into the conversation as a claim"
          (let [ph (ch/assert ada (list 'meetsOn 'Review mon))]
            (is (v/ask? kb (list 'meetsOn 'Review mon) 'CxSchedule)
                "the whole team can read the booked date off the channel")
            (is (= 'AgentAda (:creator (v/provenance kb ph))))
            (is (not (d/disputed? kb (list 'meetsOn 'Review mon) 'CxSchedule))
                "and nobody disputes it — it satisfies everyone's availability")))))))
