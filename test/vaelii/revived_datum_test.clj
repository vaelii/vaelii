;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.revived-datum-test
  "A datum whose label goes OUT ⇒ IN is a datum the agenda has not seen.

  The sibling of `refused_firing_test` through the other entry point.  There a firing was built
  and refused at placement, so its release is found by re-asking the refusal record.
  Here the join never produced a candidate at all: `chain/*matcher*` is belief filtered,
  so an OUT antecedent is not a match and a partner arriving after it joins against
  nothing.  Reviving the antecedent then moves a label and nothing else — no
  justification enters or leaves a blocked set, and no refusal was ever recorded — so a
  pass reading only those instruments converges having derived nothing.

  The cost half is as required as the belief half.  *Every* datum a settle's window
  created is newly believed too, and re-seeding those would chain the whole window a
  second time, on the hottest path in the engine; `jtms/touched-new` is what keeps them
  out, and the two cost guards below are what says so.

  Each test builds its own KB on the **isolated** database pair: it rebuilds in a loop,
  which would clear the shared pair out from under another namespace's `:once`
  fixture."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(def ^:private ctx 'CxRevivedDatum)

(defn- join-rule!
  "`(pa ?x ?z) ∧ (qa ?z ?y) => (ra ?x ?y)` — the two-antecedent shape, where one
  antecedent being OUT when the other arrives is what loses the firing."
  [kb pa qa ra]
  (v/assert-rule kb [(list pa '?x '?z) (list qa '?z '?y)] (list ra '?x '?y) ctx
                 {:direction :forward}))

;; ---- the belief the join could not reach --------------------------------

(deftest a-revived-antecedent-derives-what-its-partner-could-not
  (testing "assert, defeat, partner, undefeat — and the join is owed a second look"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (tu/with-terms [pa qa ra X Y Z]
        (join-rule! kb pa qa ra)
        ;; a *default*, so a monotonic negation can take it OUT
        (v/assert kb (list pa X Z) ctx)
        (let [defeater (v/assert kb (list 'not (list pa X Z)) ctx {:strength :monotonic})]
          (is (empty? (v/sentexes-matching kb (list pa X Z) ctx))
              "the first antecedent is OUT")
          (v/assert kb (list qa Z Y) ctx {:strength :monotonic})
          (is (empty? (v/sentexes-matching kb (list ra X Y) ctx))
              "an OUT antecedent licenses no firing")
          (v/retract! kb defeater)
          (is (seq (v/sentexes-matching kb (list pa X Z) ctx))
              "the defeated antecedent revived")
          (is (seq (v/sentexes-matching kb (list ra X Y) ctx))
              "and the revival re-derives the conclusion the join could not make")
          (testing "on one justification, naming both antecedents"
            ;; the revived datum carries the *older* handle of the pair, so a run that
            ;; ordered on the handle rather than on arrival would filter the partner out
            ;; from under it (`witness_order_test`)
            (let [h (kb/find-sentex-handle kb (list ra X Y) ctx)]
              (is (= 1 (count (jtms/supports (reasoning/tms kb) h))))
              (is (= #{[(list pa X Z) ctx] [(list qa Z Y) ctx]}
                     (into #{}
                           (comp (map #(jtms/justification (reasoning/tms kb) %))
                                 (mapcat :antecedents)
                                 (keep #(p/get-sentex (:records kb) %))
                                 (remove :antecedent)      ; the rule handle is in there too
                                 (map (juxt :sentence :context)))
                           (jtms/supports (reasoning/tms kb) h)))))))))))

(deftest the-partner-arriving-last-reaches-the-same-belief
  (testing "the order that never needed a revival is the oracle"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (tu/with-terms [pa qa ra X Y Z]
        (join-rule! kb pa qa ra)
        (v/assert kb (list pa X Z) ctx)
        (let [defeater (v/assert kb (list 'not (list pa X Z)) ctx {:strength :monotonic})]
          (v/retract! kb defeater)
          (v/assert kb (list qa Z Y) ctx {:strength :monotonic})
          (is (seq (v/sentexes-matching kb (list ra X Y) ctx))
              "the partner arriving while the antecedent is believed fires the ordinary way"))))))

(deftest a-revival-carries-down-the-derivations-that-rest-on-it
  (testing "the datum that flipped is not always the one the join needed"
    ;; A defeat takes a *derived* datum OUT with its premise, and the derived one is what
    ;; the second rule joins against.  Re-seeding the premise alone reaches nothing: the
    ;; rule that concludes the middle datum re-fires into a conclusion that already holds
    ;; its justification, and the dedup stops there.  So the whole flipped set is the
    ;; seed, not the roots of it.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (tu/with-terms [pa mid qa ra X Y Z]
        (v/assert-rule kb [(list pa '?x '?z)] (list mid '?x '?z) ctx {:direction :forward})
        (join-rule! kb mid qa ra)
        (v/assert kb (list pa X Z) ctx)
        (is (seq (v/sentexes-matching kb (list mid X Z) ctx)) "the middle datum is derived")
        (let [defeater (v/assert kb (list 'not (list pa X Z)) ctx {:strength :monotonic})]
          (is (empty? (v/sentexes-matching kb (list mid X Z) ctx))
              "and goes OUT with the premise it rests on, without being swept")
          (v/assert kb (list qa Z Y) ctx {:strength :monotonic})
          (is (empty? (v/sentexes-matching kb (list ra X Y) ctx)))
          (v/retract! kb defeater)
          (is (seq (v/sentexes-matching kb (list ra X Y) ctx))
              "reviving the premise revives the middle datum, and that is what joins"))))))

(deftest a-revival-that-derives-nothing-derives-nothing
  (testing "re-seeding says what to re-ask, never what the answer is"
    ;; The revived datum's rule has a second antecedent nothing satisfies, so the
    ;; re-seeded join must come back empty rather than concluding on one half of a pair.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (tu/with-terms [pa qa ra X Y Z]
        (join-rule! kb pa qa ra)
        (v/assert kb (list pa X Z) ctx)
        (let [defeater (v/assert kb (list 'not (list pa X Z)) ctx {:strength :monotonic})]
          (v/retract! kb defeater)
          (is (seq (v/sentexes-matching kb (list pa X Z) ctx)) "revived")
          (is (empty? (v/sentexes-matching kb (list ra '?x '?y) '?ctx))
              "and the partner is still missing, so the rule concludes nothing")
          (is (empty? (v/conflicts kb)) "with nothing to arbitrate")
          (is (empty? (v/contradictions kb))))))))

(deftest a-rebuilt-kb-agrees-with-the-live-one-about-a-revival
  (testing "the release reaches a revived datum across a restart"
    ;; A rebuild relabels the whole graph from the store, so nearly everything it
    ;; believes reads as newly believed and the re-seed stands aside (`*rebuilding?*`).
    ;; What it must not do is lose the *later* revival: the KB has to answer the undefeat
    ;; after the restart exactly as one that never restarted does.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (tu/with-terms [pa qa ra X Y Z]
        (join-rule! kb pa qa ra)
        (v/assert kb (list pa X Z) ctx)
        (v/assert kb (list 'not (list pa X Z)) ctx {:strength :monotonic})
        (v/assert kb (list qa Z Y) ctx {:strength :monotonic})
        (v/recover kb)
        (is (empty? (v/sentexes-matching kb (list pa X Z) ctx))
            "the rebuild re-decides the defeat rather than reading it")
        (is (empty? (v/sentexes-matching kb (list ra X Y) ctx))
            "and derives nothing it should not")
        (v/retract! kb (v/handle-of kb (list 'not (list pa X Z)) ctx))
        (is (seq (v/sentexes-matching kb (list ra X Y) ctx))
            "so the revival re-derives across the restart")))))

;; ---- what the re-seed must never grow into ------------------------------
;;
;; A relabelled region is mostly datums that did not move, plus every datum the window
;; created — and both read as "believed now" to anything comparing the region against
;; belief.  Seeding those is a second forward chain over the whole window, per settle.

(defn- reseeded
  "Every datum any re-seed route put back on the agenda while `f` ran.

  Wrapped at `rechain-seeds` rather than at either trigger, because that is the one entry point
  all of them go through — the relabelled revival, `settle`'s un-merge round, and a
  released refusal's placed conclusions alike.  A guard that watched one trigger would
  say nothing about the next one added."
  [f]
  (let [seen (atom [])
        orig settle/rechain-seeds]
    (with-redefs-fn {#'settle/rechain-seeds
                     (fn [kb seeds] (swap! seen into seeds) (orig kb seeds))}
      f)
    @seen))

(deftest an-ordinary-write-re-seeds-nothing
  (testing "a fact that arrives has already been chained from"
    ;; Every one of these datums — the asserted facts, the rule, the conclusions the rule
    ;; draws, and the twin the merge derives — is in its settle's region and is believed
    ;; at the end of it and was not believed at the start.  Only `jtms/touched-new`
    ;; separates them from a datum that came back, and without it this is indistinguishable from a dozen
    ;; revivals and chains twice.
    ;;
    ;; The merge is here rather than in a test of its own because it is the case the
    ;; second re-seed route could get wrong in the cheap direction: **displacing** a
    ;; spelling is not reviving one, and a settle that merges must put nothing back on
    ;; the agenda.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (tu/with-terms [pa qa ra Pref Dep X Y Z]
        (is (empty?
             (reseeded
              (fn []
                (join-rule! kb pa qa ra)
                (v/assert kb (list qa Z Y) ctx {:strength :monotonic})
                (dotimes [i 5]
                  (v/assert kb (list pa (symbol (str X i)) Z) ctx {:strength :monotonic}))
                (v/assert kb (list pa Dep Z) ctx {:strength :monotonic})
                (v/assert kb (list 'rewriteOf Pref Dep) ctx {:strength :monotonic}))))
            "an arrival is not a revival, and a displacement is not one either")
        (is (= 6 (count (v/sentexes-matching kb (list ra '?x '?y) ctx)))
            "and the ordinary chain still derived everything, the merged spelling too")
        (is (false? (v/in? kb (v/handle-of kb (list pa Dep Z) ctx)))
            "with the merge in force")))))

(deftest a-revival-re-seeds-what-flipped-not-the-settles-whole-region
  (testing "the seed is the flip, and its size does not follow the window's"
    ;; One deferred batch loads `n` facts *and* lifts a defeat, so one settle sees a
    ;; region holding the whole load beside the single datum that came back.  Re-seeding
    ;; the region would grow with `n`; re-seeding the flip is one datum at every size.
    (let [flipped
          (fn [n]
            (tu/with-cleared-kb [kb tu/isolated-fresh]
              (tu/with-terms [pa qa ra fill X Y Z]
                (join-rule! kb pa qa ra)
                (v/assert kb (list pa X Z) ctx)
                (v/assert kb (list 'not (list pa X Z)) ctx {:strength :monotonic})
                (v/assert kb (list qa Z Y) ctx {:strength :monotonic})
                (let [seeds (reseeded
                             (fn []
                               (v/with-deferred-settle kb
                                 (dotimes [i n]
                                   (v/assert kb (list fill (symbol (str Y i))) ctx
                                             {:strength :monotonic}))
                                 (v/retract! kb (v/handle-of kb (list 'not (list pa X Z)) ctx)))))]
                  (is (seq (v/sentexes-matching kb (list ra X Y) ctx))
                      (str "the revival still derives its conclusion at n=" n))
                  (count seeds)))))
          few  (flipped 4)
          many (flipped 32)]
      (is (= few many)
          (str "the re-seed followed the window rather than the flip: " few
               " datums at n=4, " many " at n=32")))))

;; ---- the equality entry point --------------------------------------------------
;;
;; A merge displaces a spelling and its twin joins in its place, so a partner arriving
;; during the merge concludes at the *twin's* spelling.  Un-merging sweeps the twin and
;; revives the original, and the conclusion has to be re-derived at the surviving
;; spelling or the KB holds neither — believing both antecedents of a forward rule and
;; none of its conclusions, where the same knowledge in the other order holds one.
;;
;; This reaches the re-seed by a different route from the defeat entry point above, and has to:
;; supersession moves belief with **no relabel behind it**, so an un-merged spelling is
;; in none of the three window sets and `jtms/revived` cannot see it.
;;
;; Both ways an equality stops being believed are here.  Asserting its *negation* is not
;; one of them and is not tested as one: the merge rewrites the negation's own terms, so
;; `(not (rewriteOf Pref Dep))` is stored as a claim about `Pref` alone and clashes with
;; nothing.

(defn- merged-scenario
  "Merge, partner, un-merge — or the same knowledge with the partner arriving after the
  un-merge.  `merge-with` is a pure description of the merge: which of the two spellings
  it displaces, and how to install it and lift it again."
  [partner-during-merge? merge-with]
  (tu/with-cleared-kb [kb tu/isolated-fresh]
    (tu/with-terms [pa qa ra Alpha Beta Z Y]
      (let [{:keys [displaced install!]} (merge-with Alpha Beta)]
        (join-rule! kb pa qa ra)
        ;; the fact has to precede the merge to be displaced by it — one arriving after
        ;; is rewritten on the way in and has no stale spelling to revive
        (v/assert kb (list pa displaced Z) ctx {:strength :monotonic})
        (let [lift! (install! kb)
              orig  (v/handle-of kb (list pa displaced Z) ctx)]
          (is (false? (v/in? kb orig)) "the merge displaces the original spelling")
          (when partner-during-merge?
            (v/assert kb (list qa Z Y) ctx {:strength :monotonic}))
          (lift!)
          (when-not partner-during-merge?
            (v/assert kb (list qa Z Y) ctx {:strength :monotonic}))
          ;; the two runs are two KBs with two sets of gensyms, so the reading names
          ;; *which spelling* each conclusion is about rather than the symbol itself
          {:antecedents [(v/in? kb orig)
                         (v/in? kb (v/handle-of kb (list qa Z Y) ctx))]
           :conclusions (frequencies
                         (map (fn [sx]
                                (if (= displaced (second (:sentence sx)))
                                  :at-the-surviving-spelling
                                  :at-the-representative))
                              (v/sentexes-matching kb (list ra '?x '?y) '?ctx)))})))))

(defn- asserted-equality
  "The equality is a premise, and retracting it is what un-merges.  `rewriteOf` is
  directional — the second argument is the one retired — so the displaced spelling is
  known without asking the closure."
  [A B]
  {:displaced B
   :install!  (fn [kb]
                (let [eq (v/assert kb (list 'rewriteOf A B) ctx {:strength :monotonic})]
                  #(v/retract! kb eq)))})

(defn- functional-equality
  "The other route, and the sanctioned way a merge is *inferred*: two symbol values for
  the same slot of a `functional` predicate derive `(equals V1 V2)`, and withdrawing
  either fact un-merges (docs/equality.md).  `equals` elects the smaller symbol, so the
  larger of the pair is the displaced one.  This arm moves a label on the equality
  itself, which the asserted case does not; the spelling it displaced still comes back
  with no relabel of its own, which is the point."
  [A B]
  {:displaced (last (sort [A B]))
   :install!  (fn [kb]
                (tu/with-terms [slotOf Subject]
                  (v/assert kb (list 'functional slotOf) ctx {:strength :monotonic})
                  (v/assert kb (list slotOf Subject (first (sort [A B]))) ctx
                            {:strength :monotonic})
                  (let [h (v/assert kb (list slotOf Subject (last (sort [A B]))) ctx
                                    {:strength :monotonic})]
                    #(v/retract! kb h))))})

(deftest an-un-merged-spelling-derives-what-its-twin-could-not
  (doseq [[label merge-with] [["a retracted equality" asserted-equality]
                              ["a functional merge losing a filler" functional-equality]]]
    (testing label
      (let [during (merged-scenario true merge-with)
            after  (merged-scenario false merge-with)]
        (is (= [true true] (:antecedents during))
            (str label ": both antecedents of the forward rule are believed at the end"))
        (is (= {:at-the-surviving-spelling 1} (:conclusions during))
            (str label ": the un-merged spelling derives its conclusion — held "
                 (pr-str (:conclusions during))))
        (is (= (:conclusions after) (:conclusions during))
            (str label ": same knowledge, two orders, one answer"))))))
