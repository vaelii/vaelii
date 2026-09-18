;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.refused-firing-test
  "A firing refused at derive time, and the release that has to reach it.

  `derive-conclusion` does not place a firing whose exception already holds, so such a
  firing owns no justification and sits in no blocked set.  Reading a released *block*
  is therefore blind to it, and without a second record it never comes back — which
  makes belief depend on whether the exception's answer moved before or after the facts
  arrived.  These pin the three orderings of one shape: the release arriving late by a
  fact, by a `genlCx` edge, and the order that never needed a record at all, which
  is the oracle the other two are scored against.

  Each test builds its own KB on the **isolated** database pair: it rebuilds in a loop,
  which would clear the shared pair out from under another namespace's `:once`
  fixture."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(def ^:private ctx 'CxRefusedFiring)

(defn- recorded
  "How many refusals stand against the one rule in `kb`'s record."
  [kb]
  (reduce + 0 (map (fn [v] (if (set? v) (count v) 0)) (vals @(reasoning/refused kb)))))

(defn- inheritance!
  "`(bigger dog cat)` inherited down to `[chi mc]` by argument preservation, with the
  predicate asymmetric so a specific converse can undercut it."
  [kb]
  (v/assert kb '(transitiveInArg fbigger 1 genl) ctx)
  (v/assert kb '(transitiveInArg fbigger 2 genl) ctx)
  (v/assert kb '(asymmetric fbigger) ctx)
  (v/assert kb '(genl fchi fdog) ctx)
  (v/assert kb '(genl fmc fcat) ctx)
  (v/assert kb '(fbigger fdog fcat) ctx))

(defn- excepted-rule!
  "`(fmark ?x) => (fseen ?x)`, excepted when the inherited claim holds."
  [kb]
  (v/assert kb '(exceptWhen (fbigger fchi fmc)
                            (set/defaultRule (set/forwardRule (implies (and (fmark ?x)) (fseen ?x)))))
            ctx))

(deftest a-firing-refused-at-derive-time-is-re-derived-when-a-fact-releases-it
  (testing "the converse fact arrives after the firing was refused"
    ;; The exception holds when `(fmark FM1)` arrives, so the firing is refused: no
    ;; justification, no node, nothing in `jtms/blocked`.  `(fbigger fmc fchi)` then
    ;; undercuts the inherited claim and the exception stops holding — a release with no
    ;; block to be read off.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (inheritance! kb)
      (excepted-rule! kb)
      (v/assert kb '(fmark FM1) ctx)
      (is (v/ask? kb '(fbigger fchi fmc) ctx)
          "the general claim reaches the pair, so the exception holds")
      (is (empty? (v/sentexes-matching kb '(fseen FM1) '?ctx))
          "and the firing is refused at derive time")
      (v/assert kb '(fbigger fmc fchi) ctx)
      (is (not (v/ask? kb '(fbigger fchi fmc) ctx))
          "the specific converse undercuts the inherited claim")
      (is (seq (v/sentexes-matching kb '(fseen FM1) '?ctx))
          "so the refused firing is re-derived")
      (v/assert kb '(fmark FM2) ctx)
      (is (seq (v/sentexes-matching kb '(fseen FM2) '?ctx))
          "and a firing made after the release is not blocked"))))

(deftest the-release-arriving-first-reaches-the-same-belief
  (testing "the order that never needed a record is the oracle"
    ;; Nothing here is refused: the converse is in place before the rule ever fires, so
    ;; this order works with no second record at all.  If the order above disagrees with
    ;; it, belief depends on arrival order.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (inheritance! kb)
      (v/assert kb '(fbigger fmc fchi) ctx)
      (excepted-rule! kb)
      (v/assert kb '(fmark FM1) ctx)
      (v/assert kb '(fmark FM2) ctx)
      (is (= 2 (count (v/sentexes-matching kb '(fseen ?x) '?ctx)))
          "released first, both firings conclude"))))

(deftest a-firing-refused-at-derive-time-is-re-derived-when-an-edge-releases-it
  (testing "a genlCx edge makes the more specific claim visible"
    ;; No inheritance and no declaration: the converse is stated in a context the
    ;; rule's context cannot see, so the exception holds and the firing is refused.
    ;; Wiring the two contexts together is what brings the converse into view.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb (list 'genlCx 'CxFSub ctx) ctx {:strength :monotonic})
      (v/assert kb '(transitiveInArg ebigger 1 genl) ctx)
      (v/assert kb '(transitiveInArg ebigger 2 genl) ctx)
      (v/assert kb '(asymmetric ebigger) ctx)
      (v/assert kb '(genl echi edog) ctx)
      (v/assert kb '(genl emc ecat) ctx)
      (v/assert kb '(ebigger edog ecat) ctx)
      (v/assert kb '(exceptWhen (ebigger echi emc)
                                (set/defaultRule (set/forwardRule (implies (and (emark ?x)) (eseen ?x)))))
                ctx)
      ;; the converse lives where the rule's own context cannot see it
      (v/assert kb '(ebigger emc echi) 'CxFAside)
      (v/assert kb '(emark EM1) 'CxFSub)
      (is (empty? (v/sentexes-matching kb '(eseen EM1) '?ctx))
          "the exception holds where the conclusion would land, so the firing is refused")
      (v/assert kb '(genlCx CxFSub CxFAside) ctx {:strength :monotonic})
      (is (not (v/ask? kb '(ebigger echi emc) 'CxFSub))
          "the sub-context now sees the converse, which undercuts the general claim")
      (is (seq (v/sentexes-matching kb '(eseen EM1) '?ctx))
          "so the refused firing is re-derived"))))

;; ---- what the record is, and what retires an entry ----------------------

(defn- skip-rule!
  "`(rmark ?x) => (rseen ?x)`, excepted when `(rskip ?x)` — the plain shape, where the
  exception is a fact that can simply be retracted."
  [kb]
  (v/assert kb '(exceptWhen (rskip ?x)
                            (set/defaultRule (set/forwardRule (implies (and (rmark ?x)) (rseen ?x)))))
            ctx))

(deftest a-refusal-is-recorded-and-retired-when-it-fires
  (testing "one entry per refused firing, and it goes when the firing is made"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (skip-rule! kb)
      (v/assert kb '(rskip RM1) ctx)
      (let [h (v/assert kb '(rmark RM1) ctx)]
        (is (= 1 (recorded kb)) "the refused firing left an entry")
        (is (empty? (v/sentexes-matching kb '(rseen RM1) '?ctx)))
        (v/retract! kb (v/handle-of kb '(rskip RM1) ctx))
        (is (seq (v/sentexes-matching kb '(rseen RM1) '?ctx))
            "the release re-derives it")
        (is (zero? (recorded kb)) "and the entry is retired, not left to fire twice")
        (is (nil? (chain/refusals kb h))
            "nothing is recorded against a handle that is not a rule")))))

(deftest a-refusal-does-not-resurrect-a-firing-whose-support-left
  (testing "the bindings are a snapshot, so what they rest on is re-checked"
    ;; The antecedent fact is retracted while the exception still holds, so the firing
    ;; is not one the KB could make any more.  Releasing the exception afterwards must
    ;; find nothing to place — a record that placed it would be deriving a conclusion
    ;; from a premise nobody believes.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (skip-rule! kb)
      (v/assert kb '(rskip RM1) ctx)
      (let [h (v/assert kb '(rmark RM1) ctx)]
        (is (= 1 (recorded kb)))
        (v/retract! kb h)
        (v/retract! kb (v/handle-of kb '(rskip RM1) ctx))
        (is (empty? (v/sentexes-matching kb '(rseen RM1) '?ctx))
            "the premise is gone, so the released exception derives nothing")
        (is (zero? (recorded kb)) "and the dead entry is dropped")))))

(deftest a-refusal-remembers-the-run-s-depth-bound-not-the-default
  (testing "the bound a release honours travels on the entry, set to the refusing run's"
    ;; `release-refusal!` re-derives in a settle with no run config in scope, so the
    ;; depth bound has to ride on the entry.  Recorded as the *default* 64 it would place
    ;; (or drop) a released firing at a ceiling the configured run never set; recorded as
    ;; the run's own, the release honours what the firing was refused under.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (skip-rule! kb)
      (v/assert kb '(rskip RM1) ctx)
      ;; the mark's chain runs at a non-default max-depth; the firing it refuses must
      ;; remember *that* bound
      (v/assert kb '(rmark RM1) ctx {:max-depth 7})
      (is (= 1 (recorded kb)))
      (let [entry (-> @(reasoning/refused kb) vals first first)]
        (is (= 7 (:max-depth entry))
            "the entry carries the run's bound, which release-refusal! reads over the default")))))

(deftest a-rebuild-re-records-at-the-default-bound-not-the-live-one
  (testing "a run's max-depth is live-session config no store holds; recover rebuilds at the default"
    ;; The bound on an entry refines *that session's* releases (`release-refusal!` reads it
    ;; over the default).  It is not durable: `recover` replays stored justifications but
    ;; resets derivation depths to 0, and a bound only ever governs future chaining, so the
    ;; re-fire that rebuilds the record runs at the default.  A KB chained under a smaller
    ;; bound therefore rebuilds its refusals at the default — documented in
    ;; docs/exceptions.md as the one place a recovered KB can release differently from the
    ;; live one, and the reason it is coherent rather than a drift: the recovered KB's
    ;; reset depths bound future chaining against that same default.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (skip-rule! kb)
      (v/assert kb '(rskip RM1) ctx)
      (v/assert kb '(rmark RM1) ctx {:max-depth 7})
      (is (= 7 (:max-depth (-> @(reasoning/refused kb) vals first first)))
          "the live entry carries the run's bound")
      (v/recover kb)
      (is (= 1 (recorded kb)) "the rebuild re-records the standing refusal")
      (is (= (:max-depth chain/default-chain-opts)
             (:max-depth (-> @(reasoning/refused kb) vals first first)))
          "and at the default bound, since the run's bound did not survive the restart"))))

(deftest a-refusal-is-not-a-contradiction
  (testing "nothing was believed and nothing conflicts: the rule simply did not fire"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (skip-rule! kb)
      (v/assert kb '(rskip RM1) ctx)
      (v/assert kb '(rmark RM1) ctx)
      (is (= 1 (recorded kb)))
      (is (empty? (v/contradictions kb)) "a refusal is not a represented dilemma")
      (is (empty? (v/conflicts kb)) "nor an unsatisfiable clash"))))

(deftest a-rebuilt-kb-agrees-with-the-live-one-about-a-standing-refusal
  (testing "recover re-records what nothing in the store could replay"
    ;; A refused firing left no justification, so `rebuild-tms` cannot bring it back and
    ;; a restarted KB would answer the later release differently from one that never
    ;; restarted.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (skip-rule! kb)
      (v/assert kb '(rskip RM1) ctx)
      (v/assert kb '(rmark RM1) ctx)
      (is (= 1 (recorded kb)))
      (v/recover kb)
      (is (= 1 (recorded kb)) "the rebuild re-decides the record rather than reading it")
      (is (empty? (v/sentexes-matching kb '(rseen RM1) '?ctx))
          "and the exception still holds after the rebuild")
      (v/retract! kb (v/handle-of kb '(rskip RM1) ctx))
      (is (seq (v/sentexes-matching kb '(rseen RM1) '?ctx))
          "so the release reaches the refused firing across the restart"))))

(deftest a-preview-leaves-the-record-where-it-found-it
  (testing "a batch reads the record and writes to it, and neither survives the rollback"
    ;; Both directions in one KB.  The suspension *consumes* an entry — the refused
    ;; firing releases, the conclusion is placed and the entry retired — and the added
    ;; mark *writes* one, at handles the rollback then takes away.  A preview promises to
    ;; leave the KB as it found it, and the record is part of what it found.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (skip-rule! kb)
      (v/assert kb '(rskip RM1) ctx)
      (v/assert kb '(rskip RM2) ctx)
      (v/assert kb '(rmark RM1) ctx)
      (is (= 1 (recorded kb)))
      (let [h (v/handle-of kb '(rskip RM1) ctx)
            p (v/preview kb {:remove [h] :add [['(rmark RM2) ctx]]})]
        (is (= '[(rmark RM2) (rseen RM1)] (mapv :sentence (:believed-added p)))
            "the preview sees the refused firing come back, and the mark it added")
        (is (= 1 (recorded kb))
            "and the rollback hands back the entry it consumed without keeping the
             one it invented")
        (is (empty? (v/sentexes-matching kb '(rseen ?x) '?ctx))
            "with the KB at baseline")
        (v/retract! kb h)
        (is (seq (v/sentexes-matching kb '(rseen RM1) '?ctx))
            "so the real release still reaches it")))))

(deftest a-rule-past-the-cap-falls-back-to-the-coarse-re-join
  (testing "the record collapses to :overflow, and the release still happens"
    ;; The cap is what keeps a rule excepted on a common condition from keeping one
    ;; entry per firing it never made.  Past it the rule keeps none and is re-joined
    ;; instead, which finds the same releases at the cost the record avoids — so the
    ;; behaviour on the far side of the line is slower, never wrong.
    (with-redefs [chain/max-refusals-per-rule 4]
      (tu/with-cleared-kb [kb tu/isolated-fresh]
        (skip-rule! kb)
        ;; the exception fact is derived from `rpre`, which arrives first, so every
        ;; `rmark` firing meets a condition that already holds and is refused rather
        ;; than placed and swept
        (v/assert kb '(set/forwardRule (implies (and (rpre ?x)) (rskip ?x))) ctx)
        (dotimes [i 10] (v/assert kb (list 'rpre (symbol (str "RM" i))) ctx))
        (dotimes [i 10] (v/assert kb (list 'rmark (symbol (str "RM" i))) ctx))
        (is (empty? (v/sentexes-matching kb '(rseen ?x) '?ctx))
            "every firing is refused")
        (is (= [:overflow] (vec (vals @(reasoning/refused kb))))
            "and past the cap the rule keeps no entries at all")
        (testing "and the release still reaches every one of them"
          (dotimes [i 10]
            (v/retract! kb (v/handle-of kb (list 'rpre (symbol (str "RM" i))) ctx)))
          (is (= 10 (count (v/sentexes-matching kb '(rseen ?x) '?ctx)))
              "the coarse re-join finds what the record would have found"))))))
