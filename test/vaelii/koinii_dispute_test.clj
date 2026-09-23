;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.koinii-dispute-test
  "Koinii dispute reads: context-scoped `disputes-in` / `disputed?` over the
  engine's whole-KB contradiction surface, and the open->notified->resolved (+stale)
  lifecycle the adjudication driver drives.  A dispute is a COEXISTING clash — both sides believed, no
  strength winner, `argue` -> `:contradiction` — never a resolved strength-defeat."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.koinii.dispute :as d]
            [vaelii.koinii.identity :as id]
            [vaelii.test-util :as tu]))

(defn- dispute-kb [] (tu/load-core! (tu/fresh)))
(use-fixtures :each (tu/neutral-fresh dispute-kb))

(def P '(reliable ProdCluster))
(def not-P '(not (reliable ProdCluster)))

(defn- holds!
  "`agent` asserts `claim` into its own context, stamped, at `strength` (default :default)."
  ([kb agent claim] (holds! kb agent claim :default))
  ([kb agent claim strength]
   (v/assert kb claim (id/context-for agent) {:creator agent :strength strength})))

(defn- channel-sees!
  "Wire `(genlCx channel CxAgent<a>)` for each agent, so `channel` sees their contexts."
  [kb channel agents]
  (doseq [a agents]
    (v/assert kb (list 'genlCx channel (id/context-for a)) 'CxUniverse {:strength :monotonic})))

(defn- cross-agent-clash!
  "Atlas holds P and Boreas holds ¬P (both :default); channel CxDeploy sees both.  A
  coexisting rebuttal — the canonical koinii dispute."
  [kb]
  (let [ha (holds! kb 'AgentAtlas P)
        hb (holds! kb 'AgentBoreas not-P)]
    (channel-sees! kb 'CxDeploy '[AgentAtlas AgentBoreas])
    {:ha ha :hb hb}))

;; ---- disputed? named S: the argue-based hot path -------------------------

(tu/deftest-kb a-coexisting-default-clash-is-disputed-not-defeated
  (cross-agent-clash! kb)
  (testing "both sides stay believed — the engine tolerates the dilemma (paraconsistent)"
    (is (v/ask? kb P 'CxDeploy))
    (is (v/ask? kb not-P 'CxDeploy)))
  (testing "argue names it a contradiction from a context that sees both sides"
    (is (= :contradiction (:verdict (v/argue kb P 'CxDeploy)))))
  (testing "so P is disputed in CxDeploy — and it is NOT 'false' or 'defeated'"
    (is (d/disputed? kb P 'CxDeploy))
    (is (d/disputed? kb 'CxDeploy))))

(tu/deftest-kb a-dispute-derived-from-facts-and-rules-is-detected-like-an-asserted-one
  ;; The clash need not be an explicit ¬P rebuttal.  Here neither agent states P or ¬P;
  ;; each asserts a FACT, and common-sense rules in the channel derive the opposing
  ;; conclusions.  05 must surface the emergent contradiction exactly as it does a stated one.
  (channel-sees! kb 'CxDeploy '[AgentAtlas AgentBoreas])
  (v/assert kb '(implies (green_audit ?x) (reliable ?x)) 'CxDeploy {:direction :forward})
  (v/assert kb '(implies (failed_failover ?x) (not (reliable ?x))) 'CxDeploy {:direction :forward})
  (holds! kb 'AgentAtlas '(green_audit ProdCluster))       ; Atlas's fact -> derives P
  (holds! kb 'AgentBoreas '(failed_failover ProdCluster))  ; Boreas's fact -> derives ¬P
  (testing "both stances are DERIVED — neither is a premise anyone stated"
    (is (v/ask? kb P 'CxDeploy))
    (is (v/ask? kb not-P 'CxDeploy))
    (is (not (v/premise? kb (v/handle-of kb P 'CxDeploy))) "P follows from the green audit")
    (is (not (v/premise? kb (v/handle-of kb not-P 'CxDeploy))) "¬P from the failed failover"))
  (testing "and 05 detects it exactly like an asserted rebuttal"
    (is (d/disputed? kb P 'CxDeploy))
    (is (= :contradiction (:verdict (v/argue kb P 'CxDeploy))))
    (is (= 1 (count (d/disputes-in kb 'CxDeploy))))))

(tu/deftest-kb a-clean-strength-defeat-is-resolved-not-disputed
  ;; monotonic P beats default ¬P: the loser is defeated, argue -> :false.  Resolved.
  (v/assert kb P 'CxDeploy {:strength :monotonic})
  (v/assert kb not-P 'CxDeploy {:strength :default})
  (testing "the default side lost and is out; no dilemma stands"
    (is (v/ask? kb P 'CxDeploy))
    (is (not (v/ask? kb not-P 'CxDeploy)))
    (is (empty? (v/contradictions kb))))
  (testing "argue collapses to :true — a strength-defeat is resolved, so NOT disputed"
    (is (= :true (:verdict (v/argue kb P 'CxDeploy))))
    (is (not (d/disputed? kb P 'CxDeploy)))
    (is (not (d/disputed? kb 'CxDeploy)))))

(tu/deftest-kb an-uncontested-sentence-is-not-disputed
  (holds! kb 'AgentAtlas P)
  (channel-sees! kb 'CxDeploy '[AgentAtlas])
  (is (not (d/disputed? kb P 'CxDeploy)) "believed and unchallenged")
  (is (not (d/disputed? kb '(reliable Nothing) 'CxDeploy)) "unknown is not disputed")
  (is (not (d/disputed? kb 'CxDeploy))))

(tu/deftest-kb a-monotonic-conflict-is-disputed-and-tagged-conflict
  ;; two things asserted known-true that cannot both hold — the harder class.
  (v/assert kb P 'CxDeploy {:strength :monotonic})
  (v/assert kb not-P 'CxDeploy {:strength :monotonic})
  (testing "argue still calls it a contradiction — both provable, no strength winner"
    (is (= :contradiction (:verdict (v/argue kb P 'CxDeploy))))
    (is (d/disputed? kb P 'CxDeploy)))
  (testing "and disputes-in surfaces it tagged :conflict, distinct from a rebuttal"
    (let [ds (d/disputes-in kb 'CxDeploy)]
      (is (= 1 (count ds)))
      (is (= :conflict (:dispute-class (first ds))))
      (is (seq (v/conflicts kb)))
      (is (empty? (v/contradictions kb))))))

;; ---- scoping is real: per-channel, not global ----------------------------

(tu/deftest-kb a-dispute-surfaces-only-where-both-sides-are-visible
  (cross-agent-clash! kb)
  ;; a context above the channel sees both sides transitively; two negatives:
  (v/assert kb '(genlCx CxUpper CxDeploy) 'CxUniverse {:strength :monotonic})   ; sees both (via CxDeploy)
  (v/assert kb (list 'genlCx 'CxOnlyAtlas (id/context-for 'AgentAtlas)) 'CxUniverse {:strength :monotonic}) ; one side
  (v/assert kb '(genlCx CxSibling CxCore) 'CxUniverse {:strength :monotonic})   ; neither side
  (testing "disputed where both sides are readable"
    (is (d/disputed? kb 'CxDeploy) "the channel that sees both")
    (is (d/disputed? kb 'CxUpper)  "and every context that sees that channel"))
  (testing "NOT disputed from a one-sided or unrelated vantage — this is the per-channel property"
    (is (not (d/disputed? kb 'CxOnlyAtlas)) "sees only Atlas's side — no clash to observe")
    (is (not (d/disputed? kb 'CxSibling))   "sees neither side")
    (is (not (d/disputed? kb (id/context-for 'AgentAtlas)))
        "and not from a single agent's own context — argue there returns :true, not :contradiction"))
  (testing "the named read agrees with the whole-surface read, context for context"
    (is (d/disputed? kb P 'CxUpper))
    (is (not (d/disputed? kb P 'CxOnlyAtlas)))))

(tu/deftest-kb disputes-in-hides-nothing-and-invents-nothing
  (cross-agent-clash! kb)
  ;; add a second, independent clash in a different channel
  (holds! kb 'AgentCiel '(fast ProdCluster))
  (holds! kb 'AgentDoris '(not (fast ProdCluster)))
  (channel-sees! kb 'CxOps '[AgentCiel AgentDoris])
  (let [whole (into #{} (map d/dispute-id) (concat (v/contradictions kb) (v/conflicts kb)))
        union (into #{} (mapcat #(map :dispute-id (d/disputes-in kb %))) (v/contexts kb))]
    (testing "the union of disputes-in over every context equals the whole-KB surface"
      (is (= 2 (count whole)) "two independent clashes")
      (is (= whole union)))))

(tu/deftest-kb each-channel-sees-only-its-own-dispute
  (cross-agent-clash! kb)                                   ; P clash under CxDeploy
  (holds! kb 'AgentCiel '(fast ProdCluster))
  (holds! kb 'AgentDoris '(not (fast ProdCluster)))
  (channel-sees! kb 'CxOps '[AgentCiel AgentDoris])         ; fast clash under CxOps
  (is (= 1 (count (d/disputes-in kb 'CxDeploy))))
  (is (= 1 (count (d/disputes-in kb 'CxOps))))
  (is (not= (:dispute-id (first (d/disputes-in kb 'CxDeploy)))
            (:dispute-id (first (d/disputes-in kb 'CxOps))))
      "the two channels name two different disputes"))

;; ---- the named path does not scan (a perf property) ----------------------

(tu/deftest-kb the-named-read-detects-without-computing-whole-kb-contradictions
  (cross-agent-clash! kb)
  (let [scans (atom 0)]
    (with-redefs [v/contradictions (fn [_] (swap! scans inc) [])]
      (testing "disputed? on a named S detects the clash via argue, scanning nothing"
        (is (d/disputed? kb P 'CxDeploy))
        (is (zero? @scans) "no whole-KB contradictions scan on the hot path"))
      (testing "the any-path (no named S) is the one that scans"
        (d/disputed? kb 'CxDeploy)
        (is (pos? @scans))))))

;; ---- dispute id: stable and order-independent ----------------------------

(tu/deftest-kb a-dispute-id-is-a-function-of-the-clash-not-the-side-order
  (cross-agent-clash! kb)
  (let [entry (first (d/disputes-in kb 'CxDeploy))]
    (testing "the id is the sorted handle pair, however the engine ordered the sides"
      (is (= (vec (sort (:handles entry))) (:dispute-id entry)))
      (is (= (d/dispute-id entry) (d/dispute-id (update entry :handles reverse)))))
    (testing "and the reified term is order-independent for the same reason"
      (is (= (d/dispute-term (:dispute-id entry))
             (d/dispute-term (reverse (:dispute-id entry))))))))

;; ---- the lifecycle: open -> notified -> resolved, plus stale -------------

(tu/deftest-kb the-lifecycle-runs-open-notified-resolved
  (let [hb  (:hb (cross-agent-clash! kb))
        did (:dispute-id (first (d/disputes-in kb 'CxDeploy)))]
    (testing "a fresh clash is :open — derived, nothing stored"
      (is (= :open (d/dispute-state kb did)))
      (is (= [(first (d/disputes-in kb 'CxDeploy))] (d/pending-disputes kb 'CxDeploy))))
    (testing "adjudication notifies: recorded as an assertion, so it reads :notified"
      (d/mark-notified kb did 1750000000000)
      (is (d/notified? kb did))
      (is (= :notified (d/dispute-state kb did)))
      (is (empty? (d/pending-disputes kb 'CxDeploy)) "no longer pending — announced"))
    (testing "retract a side (a human/trust-resolve ruling) and it reads :resolved"
      (v/retract! kb hb)
      (is (not (v/ask? kb not-P 'CxDeploy)))
      (is (= :true (:verdict (v/argue kb P 'CxDeploy))) "argue collapsed")
      (is (empty? (d/disputes-in kb 'CxDeploy)))
      (is (= :resolved (d/dispute-state kb did))))))

(tu/deftest-kb retracting-a-notify-mark-reopens-the-dispute
  (cross-agent-clash! kb)
  (let [did (:dispute-id (first (d/disputes-in kb 'CxDeploy)))]
    (d/mark-notified kb did 1750000000000)
    (is (= :notified (d/dispute-state kb did)))
    (testing "reopen! retracts the mark; the still-live clash returns to :open"
      (is (= 1 (d/reopen! kb did)))
      (is (not (d/notified? kb did)))
      (is (= :open (d/dispute-state kb did))))))

(tu/deftest-kb an-unruled-dispute-can-be-swept-stale-and-stays-live
  (cross-agent-clash! kb)
  (let [did (:dispute-id (first (d/disputes-in kb 'CxDeploy)))]
    (d/mark-stale kb did 1750000009999 'TimedOut)
    (testing "stale flags an aged-out dispute without resolving it — the clash still stands"
      (is (d/stale? kb did))
      (is (= :stale (d/dispute-state kb did)))
      (is (seq (d/disputes-in kb 'CxDeploy)) "still a live clash")
      (is (= :contradiction (:verdict (v/argue kb P 'CxDeploy)))))
    (testing "the stale mark is a plain fact why can explain"
      (let [[sx & more] (v/sentexes-matching
                         kb (list 'disputeStale (d/dispute-term did) '?at '?r) d/state-context)]
        (is (nil? more) "one stale mark for the dispute, so reading it names no order")
        (is (some? sx))
        (is (:believed? (v/why kb (:id sx))))))
    (testing "reopen! clears it too"
      (is (= 1 (d/reopen! kb did)))
      (is (= :open (d/dispute-state kb did))))))

(tu/deftest-kb reopen-clears-both-mark-kinds-in-one-pass
  ;; The reopen walks two mark reads and retracts as it goes.  Both kinds present is the
  ;; case that has the second read running after the first retracts have landed, so the
  ;; whole mark set is realized before anything is torn down — a live index read is not a
  ;; snapshot, and a retract in the middle of one is a read of a KB that has moved.
  (cross-agent-clash! kb)
  (let [did (:dispute-id (first (d/disputes-in kb 'CxDeploy)))]
    (d/mark-notified kb did 1750000000000)
    (d/mark-stale kb did 1750000009999 'TimedOut)
    (is (d/notified? kb did))
    (is (d/stale? kb did))
    (is (= :stale (d/dispute-state kb did)) "stale outranks notified while both stand")
    (testing "one reopen takes both, and counts both"
      (is (= 2 (d/reopen! kb did)))
      (is (not (d/notified? kb did)))
      (is (not (d/stale? kb did)))
      (is (= :open (d/dispute-state kb did)) "the still-live clash is back at :open"))
    (testing "and it is idempotent — a second reopen finds nothing"
      (is (zero? (d/reopen! kb did))))))

;; ---- a clash with more than two members gets a name of its own -----------

(clojure.test/deftest a-three-member-dispute-is-named-by-all-three-handles
  ;; A nogood is a SET, and `anti_transitive` forms one over three sentexes
  ;; (docs/nmtms.md), so `disputes-in` hands back three-handle entries — "a caller
  ;; destructuring `:handles` as a pair is reading a coincidence."  The lifecycle term is
  ;; where that bites: the stored `:notified` / `:stale` marks are keyed on it and the
  ;; sweeps read them as their idempotency key, so a term naming only the two lowest
  ;; handles would mark one dispute and silently retire another.
  ;;
  ;; A pure test — `dispute-term` needs no KB, and the collision is a property of the
  ;; term rather than of any clash a scenario happens to build.
  (testing "the pair case is a sorted pair, unchanged"
    (is (= '(dispute (sentexHandle 478) (sentexHandle 479))
           (d/dispute-term [479 478]))))
  (testing "a three-member clash names all three, sorted"
    (is (= '(dispute (sentexHandle 478) (sentexHandle 479) (sentexHandle 999))
           (d/dispute-term [999 478 479]))))
  (testing "so two three-member disputes sharing their lowest pair are told apart"
    (is (not= (d/dispute-term [478 479 999]) (d/dispute-term [478 479 1234]))))
  (testing "and a three-member one is not the pair over its two lowest handles"
    (is (not= (d/dispute-term [478 479 999]) (d/dispute-term [478 479])))))
