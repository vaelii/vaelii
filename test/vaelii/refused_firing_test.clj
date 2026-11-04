;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.refused-firing-test
  "A firing an `exceptWhen` blocks, stored with a guard defeat, and a firing a
  closed-extent antecedent refuses, kept in the refusal record; and the release that has
  to reach each.

  The first three tests assert three orderings of one guard: the release arriving late by
  a fact, by a `genlCx` edge, and the order where the guard never held, which is the
  oracle the other two are scored against.  The rest read the refusal record through a
  closed-extent rule, the block condition that still refuses a firing.

  Each test builds its own KB on the **isolated** database pair: it rebuilds in a loop,
  which would clear the shared pair out from under another namespace's `:once`
  fixture."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.settle :as settle]
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
  (v/assert kb '(transitiveInArgInverse fbigger 1 genl) ctx)
  (v/assert kb '(transitiveInArgInverse fbigger 2 genl) ctx)
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

(deftest a-guard-defeated-firing-is-believed-when-a-fact-releases-it
  (testing "the converse fact arrives after the firing was defeated"
    ;; The exception holds when `(fmark FM1)` arrives, so the firing is stored with a
    ;; guard defeat.  `(fbigger fmc fchi)` then undercuts the inherited claim and the
    ;; exception stops holding, which takes the defeat's support OUT.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (inheritance! kb)
      (excepted-rule! kb)
      (v/assert kb '(fmark FM1) ctx)
      (is (v/ask? kb '(fbigger fchi fmc) ctx)
          "the general claim reaches the pair, so the exception holds")
      (is (empty? (v/sentexes-matching kb '(fseen FM1) '?ctx))
          "and the firing's guard defeat hides it")
      (v/assert kb '(fbigger fmc fchi) ctx)
      (is (not (v/ask? kb '(fbigger fchi fmc) ctx))
          "the specific converse undercuts the inherited claim")
      (is (seq (v/sentexes-matching kb '(fseen FM1) '?ctx))
          "so the defeat is withdrawn")
      (v/assert kb '(fmark FM2) ctx)
      (is (seq (v/sentexes-matching kb '(fseen FM2) '?ctx))
          "and a firing made after the release is not blocked"))))

(deftest the-release-arriving-first-reaches-the-same-belief
  (testing "the order where the guard never held is the oracle"
    ;; The converse is in place before the rule ever fires, so no defeat is placed.  If
    ;; the order above disagrees with it, belief depends on arrival order.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (inheritance! kb)
      (v/assert kb '(fbigger fmc fchi) ctx)
      (excepted-rule! kb)
      (v/assert kb '(fmark FM1) ctx)
      (v/assert kb '(fmark FM2) ctx)
      (is (= 2 (count (v/sentexes-matching kb '(fseen ?x) '?ctx)))
          "released first, both firings conclude"))))

(deftest a-guard-defeated-firing-is-believed-when-an-edge-releases-it
  (testing "a genlCx edge makes the more specific claim visible"
    ;; No inheritance and no declaration: the converse is stated in a context the
    ;; rule's context cannot see, so the exception holds and a guard defeat hides the
    ;; firing.  Wiring the two contexts together is what brings the converse into view.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb (list 'genlCx 'CxFSub ctx) ctx {:strength :monotonic})
      (v/assert kb '(transitiveInArgInverse ebigger 1 genl) ctx)
      (v/assert kb '(transitiveInArgInverse ebigger 2 genl) ctx)
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
          "the exception holds where the conclusion lands, so its guard defeat hides it")
      (v/assert kb '(genlCx CxFSub CxFAside) ctx {:strength :monotonic})
      (is (not (v/ask? kb '(ebigger echi emc) 'CxFSub))
          "the sub-context now sees the converse, which undercuts the general claim")
      (is (seq (v/sentexes-matching kb '(eseen EM1) '?ctx))
          "so the defeat is withdrawn"))))

;; ---- a guard stores the firing, and records nothing ----------------------

(defn- skip-rule!
  "`(rmark ?x) => (rseen ?x)`, excepted when `(rskip ?x)` — the plain shape, where the
  exception is a fact that can simply be retracted."
  [kb]
  (v/assert kb '(exceptWhen (rskip ?x)
                            (set/defaultRule (set/forwardRule (implies (and (rmark ?x)) (rseen ?x)))))
            ctx))

(deftest a-firing-a-monotonic-blocker-blocks-is-stored-with-a-guard-defeat
  (testing "the conclusion and its defeat are stored, hidden at the reader, and nothing is recorded"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (skip-rule! kb)
      (v/assert kb '(rskip RM1) ctx {:strength :monotonic})
      (v/assert kb '(rmark RM1) ctx)
      (let [h (v/handle-of kb '(rseen RM1) ctx)]
        (is (some? h))
        (is (some? (v/handle-of kb (list 'defeat (list 'sentexHandle h)) ctx)))
        (is (not (v/ask? kb '(rseen RM1) ctx)))
        (is (zero? (recorded kb)))
        (v/recover kb)
        (is (not (v/ask? kb '(rseen RM1) ctx)) "the recovered store reads the stored defeat")
        (v/retract! kb (v/handle-of kb '(rskip RM1) ctx))
        (is (v/ask? kb '(rseen RM1) ctx) "and the blocker leaving withdraws it")))))

;; ---- what the record is, and what retires an entry ----------------------

(defn- member-rule!
  "`(rmark ?x) ∧ (not (rmember ?x)) => (rseen ?x)` under a `closed_extent_predicate` grant
  on `rmember`: a stored `(rmember X)` refuses the firing at `X`, and retracting it
  releases the firing."
  [kb]
  (v/assert kb '(closed_extent_predicate rmember) ctx)
  (v/assert kb '(implies (and (rmark ?x) (not (rmember ?x))) (rseen ?x)) ctx {:direction :forward}))

(deftest a-refusal-is-recorded-and-retired-when-it-fires
  (testing "one entry per refused firing, and it goes when the firing is made"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (member-rule! kb)
      (v/assert kb '(rmember RM1) ctx {:strength :monotonic})
      (let [h (v/assert kb '(rmark RM1) ctx)]
        (is (= 1 (recorded kb)) "the refused firing left an entry")
        (is (empty? (v/sentexes-matching kb '(rseen RM1) '?ctx)))
        (v/retract! kb (v/handle-of kb '(rmember RM1) ctx))
        (is (seq (v/sentexes-matching kb '(rseen RM1) '?ctx))
            "the release re-derives it")
        (is (zero? (recorded kb)) "and the entry is retired, not left to fire twice")
        (is (nil? (chain/refusals kb h))
            "nothing is recorded against a handle that is not a rule")))))

(deftest a-refused-firing-is-one-entry-in-every-arrival-order
  (let [step   {:rule   member-rule!
                :member #(v/assert % '(rmember RM1) ctx {:strength :monotonic})
                :mark   #(v/assert % '(rmark RM1) ctx)}
        ledger (fn [order]
                 (tu/with-cleared-kb [kb tu/isolated-fresh]
                   (run! #((step %) kb) order)
                   (v/forward-chain kb)
                   [(recorded kb)
                    (into #{} (comp (filter set?) cat (map :bindings)) (vals @(reasoning/refused kb)))]))
        orders [[:rule :member :mark] [:member :mark :rule] [:mark :rule :member]]]
    (is (= (repeat 3 [1 '#{{?var0 RM1}}]) (map ledger orders)))))

(deftest a-firing-swept-and-refused-by-a-bounded-join-is-one-entry-under-the-wider-bound
  (let [step   {:rule   member-rule!
                :member #(v/assert % '(rmember RM1) ctx {:strength :monotonic})
                :mark   #(v/assert % '(rmark RM1) ctx)
                :chain  #(v/forward-chain % {:max-depth 7})}
        ledger (fn [order]
                 (tu/with-cleared-kb [kb tu/isolated-fresh]
                   (run! #((step %) kb) order)
                   [(recorded kb)
                    (into #{} (comp (filter set?) cat (map :max-depth)) (vals @(reasoning/refused kb)))]))]
    (testing "placed, swept with no bound when the member arrives, then refused by a bounded re-join"
      (is (= [[1 #{nil}] [1 #{nil}]]
             (map ledger [[:rule :mark :member :chain] [:mark :rule :member :chain]]))))))

(deftest a-refusal-does-not-resurrect-a-firing-whose-support-left
  (testing "the bindings are a snapshot, so what they rest on is re-checked"
    ;; The antecedent fact is retracted while the member still refuses the firing, so the
    ;; firing is not one the KB could make any more.  Retracting the member afterwards
    ;; must find nothing to place — a record that placed it would be deriving a
    ;; conclusion from a premise nobody believes.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (member-rule! kb)
      (v/assert kb '(rmember RM1) ctx {:strength :monotonic})
      (let [h (v/assert kb '(rmark RM1) ctx)]
        (is (= 1 (recorded kb)))
        (v/retract! kb h)
        (v/retract! kb (v/handle-of kb '(rmember RM1) ctx))
        (is (empty? (v/sentexes-matching kb '(rseen RM1) '?ctx))
            "the premise is gone, so the release derives nothing")
        (is (zero? (recorded kb)) "and the dead entry is dropped")))))

(deftest a-release-that-places-an-exception-blocks-the-next-release
  (testing "two guard defeats withdrawn by one retraction, the first firing excepting the second"
    ;; `(rskip RM1)` defeats both firings and both defeats go once it goes.  The first
    ;; firing concludes `(cseen RM1)`, which the second rule is excepted by, so the second
    ;; keeps a guard defeat.  The order where `(rskip RM1)` never held is the oracle:
    ;; `cseen` holds and `dseen` does not.
    (let [rule    (fn [q head]
                    (list 'exceptWhen q (list 'set/defaultRule
                                              (list 'set/forwardRule
                                                    (list 'implies '(and (rmark ?x)) head)))))
          rules!  (fn [kb]
                    (v/assert kb (rule '(rskip ?x) '(cseen ?x)) ctx)
                    (v/assert kb (rule '(rskip ?x) '(dseen ?x)) ctx)
                    (v/assert kb (rule '(cseen ?x) '(dseen ?x)) ctx))
          reading (fn [kb] [(v/ask? kb '(cseen RM1) ctx) (v/ask? kb '(dseen RM1) ctx)])]
      (tu/with-cleared-kb [kb tu/isolated-fresh]
        (rules! kb)
        (v/assert kb '(rskip RM1) ctx {:strength :monotonic})
        (v/assert kb '(rmark RM1) ctx)
        (is (zero? (recorded kb)))
        (v/retract! kb (v/handle-of kb '(rskip RM1) ctx))
        (is (= [true false] (reading kb))))
      (tu/with-cleared-kb [kb tu/isolated-fresh]
        (rules! kb)
        (v/assert kb '(rmark RM1) ctx)
        (is (= [true false] (reading kb)) "the order with no blocker agrees")))))

(deftest a-refusal-remembers-the-run-s-depth-bound-not-the-default
  (testing "the bound a release honours travels on the entry, set to the refusing run's"
    ;; `release-refusal!` re-derives in a settle with no run config in scope, so the
    ;; depth bound has to ride on the entry.  Recorded as the default (none) it would
    ;; place a released firing the configured run's bound excludes; recorded as the run's
    ;; own, the release honours what the firing was refused under.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (member-rule! kb)
      (v/assert kb '(rmember RM1) ctx {:strength :monotonic})
      ;; the mark's chain runs at a non-default max-depth; the firing it refuses must
      ;; remember *that* bound
      (v/assert kb '(rmark RM1) ctx {:max-depth 7})
      (is (= 1 (recorded kb)))
      (let [entry (-> @(reasoning/refused kb) vals first first)]
        (is (= 7 (:max-depth entry))
            "the entry carries the run's bound, which release-refusal! reads over the default")))))

(deftest a-rebuild-re-records-at-the-default-bound-not-the-live-one
  (testing "a run's max-depth is live-session config no store holds; recover rebuilds at the default"
    ;; The bound on an entry refines *that session's* releases.  It is not durable:
    ;; `recover` replays stored justifications but resets derivation depths to 0, so the
    ;; re-fire that rebuilds the record runs at the default, which is no derivation-depth
    ;; bound.  docs/exceptions.md states this as the one place a recovered KB can release
    ;; differently from the live one.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (member-rule! kb)
      (v/assert kb '(rmember RM1) ctx {:strength :monotonic})
      (v/assert kb '(rmark RM1) ctx {:max-depth 7})
      (is (= 7 (:max-depth (-> @(reasoning/refused kb) vals first first)))
          "the live entry carries the run's bound")
      (v/recover kb)
      (is (= 1 (recorded kb)) "the rebuild re-records the standing refusal")
      (is (nil? (:max-depth (-> @(reasoning/refused kb) vals first first)))
          "and under no bound, since the run's bound did not survive the restart"))))

(deftest a-refusal-is-not-a-contradiction
  (testing "nothing was believed and nothing conflicts: the rule simply did not fire"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (member-rule! kb)
      (v/assert kb '(rmember RM1) ctx {:strength :monotonic})
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
      (member-rule! kb)
      (v/assert kb '(rmember RM1) ctx {:strength :monotonic})
      (v/assert kb '(rmark RM1) ctx)
      (is (= 1 (recorded kb)))
      (v/recover kb)
      (is (= 1 (recorded kb)) "the rebuild re-decides the record rather than reading it")
      (is (empty? (v/sentexes-matching kb '(rseen RM1) '?ctx))
          "and the member still refuses it after the rebuild")
      (v/retract! kb (v/handle-of kb '(rmember RM1) ctx))
      (is (seq (v/sentexes-matching kb '(rseen RM1) '?ctx))
          "so the release reaches the refused firing across the restart"))))

(deftest a-preview-leaves-the-record-where-it-found-it
  (testing "a batch reads the record and writes to it, and neither survives the rollback"
    ;; Both directions in one KB.  The suspension *consumes* an entry — the refused
    ;; firing releases, the conclusion is placed and the entry retired — and the added
    ;; mark *writes* one, at handles the rollback then takes away.  A preview promises to
    ;; leave the KB as it found it, and the record is part of what it found.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (member-rule! kb)
      (v/assert kb '(rmember RM1) ctx {:strength :monotonic})
      (v/assert kb '(rmember RM2) ctx {:strength :monotonic})
      (v/assert kb '(rmark RM1) ctx)
      (is (= 1 (recorded kb)))
      (let [h (v/handle-of kb '(rmember RM1) ctx)
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
    ;; The cap is what keeps a rule refused on a common condition from keeping one
    ;; entry per firing it never made.  Past it the rule keeps none and is re-joined
    ;; instead, which finds the same releases at the cost the record avoids — so the
    ;; behaviour on the far side of the line is slower, never wrong.
    (with-redefs [chain/max-refusals-per-rule 4]
      (tu/with-cleared-kb [kb tu/isolated-fresh]
        (member-rule! kb)
        ;; the member is derived from `rpre`, which arrives first, so every `rmark`
        ;; firing meets a member already stored and is refused rather than placed and
        ;; swept
        (v/assert kb '(set/forwardRule (implies (and (rpre ?x)) (rmember ?x))) ctx)
        (dotimes [i 10] (v/assert kb (list 'rpre (symbol (str "RM" i))) ctx {:strength :monotonic}))
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

(defn- swept-then-released
  "`[recorded rseen? recorded re-chained]` for the firing of `skip-rule!` placed before its
  blocker `(rskip RM1)`, asserted at `strength`, arrives: the entries recorded once the
  blocker arrives, whether it is believed and the entries recorded after `trigger` lifts
  the block, and the rules re-chained over their extent meanwhile.  `:except` hides the
  blocker, `:retract` retracts it, `:defeat` stores a `:monotonic` denial whose placed
  defeat hides it."
  [strength trigger]
  (tu/with-cleared-kb [kb tu/isolated-fresh]
    (skip-rule! kb)
    (v/assert kb '(rmark RM1) ctx)
    (let [blk   (v/assert kb '(rskip RM1) ctx {:strength strength})
          swept (recorded kb)
          seen  (atom #{})
          real  settle/rechain-exception-rules]
      (with-redefs [settle/rechain-exception-rules (fn [kb rhs] (swap! seen into rhs) (real kb rhs))]
        (case trigger
          :except  (v/assert kb (list 'except (list 'sentexHandle blk)) ctx)
          :retract (v/retract! kb blk)
          :defeat  (v/assert kb '(not (rskip RM1)) ctx {:strength :monotonic})))
      [swept (v/ask? kb '(rseen RM1) ctx) (recorded kb) @seen])))

(deftest a-late-blocker-of-either-class-defeats-the-firing-and-records-nothing
  ;; A blocker sweeps nothing: the firing stays stored with a guard defeat resting on the
  ;; blocker, whichever its class, and each trigger that lifts the block gives it
  ;; back with nothing recorded or re-chained.
  (doseq [[strength trigger expected] [[:monotonic :except [0 true 0 #{}]]
                                       [:monotonic :retract [0 true 0 #{}]]
                                       [:default :except [0 true 0 #{}]]
                                       [:default :retract [0 true 0 #{}]]
                                       [:default :defeat [0 true 0 #{}]]]]
    (testing (str (name strength) " " (name trigger))
      (is (= expected (swept-then-released strength trigger))))))

;; ---- a firing an argument conviction convicts is stored and held ---------------

(defn- convicted-world!
  "Contexts, types and the declaration `(arg cowns 2 canimal)` above the rule's context.
  `CRex` is a `cpoodle`, a `cdog` by the edge `release!` removes, and `cdog` is disjoint
  from `canimal`, so under the constraint-only reading `(cowns CAnn CRex)` is convicted on
  argument 2 until the edge leaves."
  [kb]
  (v/assert kb '(genlCx CxRCTheory CxUniverse) 'CxUniverse {:strength :monotonic})
  (v/assert kb '(genlCx CxRCWorld CxRCTheory) 'CxUniverse {:strength :monotonic})
  (v/assert kb '(genl canimal thing) 'CxRCTheory {:strength :monotonic})
  (v/assert kb '(genl cdog thing) 'CxRCTheory {:strength :monotonic})
  (v/assert kb '(genl cpoodle thing) 'CxRCTheory {:strength :monotonic})
  (v/assert kb '(genl cpoodle cdog) 'CxRCTheory {:strength :monotonic})
  (v/assert kb '(disjoint cdog canimal) 'CxRCTheory {:strength :monotonic})
  (v/assert kb '(arg cowns 2 canimal) 'CxRCTheory)
  (v/assert kb '(cpoodle CRex) 'CxRCWorld))

(defn- release!
  "Retract `(genl cpoodle cdog)`, the edge the conviction of `convicted-world!` reads."
  [kb]
  (v/retract! kb (v/handle-of kb '(genl cpoodle cdog) 'CxRCTheory)))

(defn- convicted-firing!
  "`(cpetOf ?x ?y) => (cowns ?y ?x)` firing on `(cpetOf CRex CAnn)` into `convicted-world!`.
  The rule carries no re-check condition."
  [kb]
  (convicted-world! kb)
  (v/assert kb '(set/forwardRule (implies (cpetOf ?x ?y) (cowns ?y ?x))) 'CxRCWorld)
  (v/assert kb '(cpetOf CRex CAnn) 'CxRCWorld))

(defn- held-reading
  "What `kb` holds of `(cowns CAnn CRex)`: whether it is stored, whether it is believed,
  and the `:inert-argument` entries `violations` reports for it."
  [kb]
  {:stored (some? (v/handle-of kb '(cowns CAnn CRex) 'CxRCWorld))
   :owns   (boolean (v/ask? kb '(cowns CAnn CRex) 'CxRCWorld))
   :inert  (count (filter #(and (= :inert-argument (:violation %))
                                (= '(cowns CAnn CRex) (:sentence %)))
                          (v/violations kb)))})

(deftest a-convicted-firing-is-held-and-released-alike-live-in-place-and-over-a-fresh-open
  ;; The release is the retraction of the `genl` edge the conviction reads.  Each reading builds the
  ;; same content on a cleared store, reaches it the way `reach` names, then asserts the
  ;; edge.  A watched rule beside it is what makes a recover re-fire, so both rule sets
  ;; are read.
  (tu/without-entailing
   (let [reading (fn [watched? reach]
                   (tu/with-cleared-kb [kb tu/isolated-fresh]
                     (when watched? (skip-rule! kb))
                     (convicted-firing! kb)
                     (let [kb'    (case reach
                                    :live     kb
                                    :in-place (doto kb (v/recover))
                                    :fresh    (doto (tu/isolated-test-kb) (v/recover)))
                           before (assoc (held-reading kb') :recorded (recorded kb'))]
                       (release! kb')
                       [before (assoc (held-reading kb') :recorded (recorded kb'))])))
         rows    (for [w [false true] r [:live :in-place :fresh]] [w r])]
     (is (= (mapv #(conj % [{:stored true :owns false :inert 1 :recorded 0}
                            {:stored true :owns true :inert 0 :recorded 0}])
                  rows)
            (mapv (fn [[w r]] [w r (reading w r)]) rows))
         "every path stores the conclusion held, records nothing, and the retraction releases it"))))

(deftest a-sentence-derived-and-asserted-is-held-alike-in-both-arrival-orders
  ;; The same sentence reaches the store by the rule and by `assert`, in both orders.
  ;; Each order stores one sentex, held, with one `:inert-argument` entry, and the edge
  ;; retraction releases it.
  (tu/without-entailing
   (let [reading (fn [order]
                   (tu/with-cleared-kb [kb tu/isolated-fresh]
                     (let [assert! #(v/assert kb '(cowns CAnn CRex) 'CxRCWorld)]
                       (when (= :asserted-first order) (convicted-world! kb) (assert!))
                       (convicted-firing! kb)
                       (when (= :derived-first order) (assert!))
                       (let [before (held-reading kb)]
                         (release! kb)
                         [before (held-reading kb)]))))]
     (is (= {:asserted-first [{:stored true :owns false :inert 1} {:stored true :owns true :inert 0}]
             :derived-first  [{:stored true :owns false :inert 1} {:stored true :owns true :inert 0}]}
            {:asserted-first (reading :asserted-first)
             :derived-first  (reading :derived-first)})))))
