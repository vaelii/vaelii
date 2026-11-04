;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.feed-test
  "The change feed: an application told that belief moved, instead of asking again.

  Every claim here is about the *extension point*, not about inference — the engine already
  computes what a listener receives and used to discard it, so what these tests hold are
  the four things a feed can get wrong.

  * **Altitude.**  A listener hears about *belief*, not storage.  So a defeat and a
    revival both arrive, a re-asserted sentex is not news, and a `preview` — which
    stores, reads and takes it all back — is silent.
  * **Granularity.**  One settle is one event, and an operation that settles twice (a
    teardown that re-derives what it swept) is still one: a datum that went OUT and came
    back moved no net belief, and reporting both halves of that flicker is the failure
    mode.  The batch a feed reports is the batch `edit-with-consequences` reports.
  * **Reentrancy.**  Listeners run after the settle, never inside it, so one that writes
    starts a fresh settle and gets its own event — and one that throws loses its own
    event and nothing else, since the settle it is hearing about is already committed.
  * **Honesty about what it cannot answer.**  A goal whose truth is a function of
    something outside the moved region is refused rather than watched for nothing.

  House rules as everywhere: gensym'd temporaries through `tu/with-terms`, engine
  vocabulary (`genl`, `genlCx`, `set/defaultRule`, `exceptWhen`) literal, and the
  neutral fixture asserts the KB is restored."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [taoensso.trove :as trove]
            [vaelii.core :as v]
            [vaelii.impl.feed :as feed]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as vr]
            [vaelii.ref.gen :as gen]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- recorder
  "An atom collecting events, and the listener that fills it."
  []
  (let [seen (atom [])]
    [seen (fn [e] (swap! seen conj e))]))

(defn- sentences
  "The sentences one half of every event names, flattened in arrival order."
  [events half]
  (into [] (mapcat #(map :sentence (half %))) events))

(defn- added [events] (sentences events :believed-added))
(defn- removed [events] (sentences events :believed-removed))

;;; ── what arrives, and in what shape ────────────────────────────────────

(tu/deftest-kb an-assert-that-moves-belief-arrives-once
  (tu/with-terms [dog Muffet]
    (let [[seen f] (recorder)]
      (v/watch kb f)
      (v/assert kb (list dog Muffet) 'CxUniverse)
      (is (= 1 (count @seen)) "one settle, one event")
      (is (= [(list dog Muffet)] (added @seen)))
      (is (empty? (removed @seen)))
      (let [e (first (:believed-added (first @seen)))]
        (is (= 'CxUniverse (:context e)))
        (is (true? (:premise? e)) "an asserted fact is a premise")
        (is (= (v/handle-of kb (list dog Muffet) 'CxUniverse) (:handle e))
            "the entry is addressable")))))

(tu/deftest-kb a-derived-conclusion-arrives-with-the-rule-that-derived-it
  (tu/with-terms [dog barks Muffet]
    (let [[seen f] (recorder)]
      (v/assert kb (vr/rule-sentence [(list dog '?x)] (list barks '?x)) 'CxUniverse {:direction :forward})
      (v/watch kb f)
      (v/assert kb (list dog Muffet) 'CxUniverse)
      (is (= 1 (count @seen)))
      (is (= #{(list dog Muffet) (list barks Muffet)} (set (added @seen)))
          "the premise and what followed from it are one event")
      (let [c (first (filter #(= (list barks Muffet) (:sentence %))
                             (:believed-added (first @seen))))]
        (is (false? (:premise? c)))
        (is (= (vr/rule-sentence [(list dog '?x)] (list barks '?x))
               (:rule (:justification c)))
            "the entry carries why it is believed")
        (is (= [(list dog Muffet)] (:antecedents (:justification c))))))))

(tu/deftest-kb a-firing-an-exceptWhen-rule-makes-on-its-arrival-arrives-with-it
  ;; The assert stores the rule and then its exception, and each store settles: the
  ;; firing the first settle places is believed when the second one reads it.
  (tu/with-terms [bird penguin flies Opus]
    (let [rule (list 'exceptWhen (list penguin '?x)
                     (list 'set/forwardRule (list 'implies (list bird '?x) (list flies '?x))))]
      (v/assert kb (list bird Opus) 'CxUniverse)
      (let [[seen f] (recorder)
            tok      (v/watch kb f)]
        (v/assert kb rule 'CxUniverse)
        (v/unwatch kb tok)
        (is (some #{(list flies Opus)} (added @seen)))))))

(tu/deftest-kb nothing-arrives-for-a-mutation-that-moved-no-belief
  (tu/with-terms [dog Muffet cat Tom]
    (let [[seen f] (recorder)]
      (v/assert kb (list dog Muffet) 'CxUniverse)
      (v/watch kb f)
      (testing "re-asserting a stored sentex is not news"
        (v/assert kb (list dog Muffet) 'CxUniverse)
        (is (empty? @seen)))
      (testing "...but an unrelated fact is, to a plain listener"
        (v/assert kb (list cat Tom) 'CxUniverse)
        (is (= [(list cat Tom)] (added @seen)))))))

(tu/deftest-kb a-batch-settles-once-and-is-one-event
  (tu/with-terms [dog barks Muffet Rex Spot]
    (let [[seen f] (recorder)]
      (v/assert kb (vr/rule-sentence [(list dog '?x)] (list barks '?x)) 'CxUniverse {:direction :forward})
      (v/watch kb f)
      (v/assert-many kb (mapv #(list dog %) [Muffet Rex Spot]) 'CxUniverse)
      (is (= 1 (count @seen)) "three asserts, one settle, one event")
      (is (= 6 (count (added @seen))) "three premises and three conclusions"))))

(tu/deftest-kb one-batch-in-two-orders-is-one-event-in-one-order
  ;; an event's entries are ranked by content (`moved-handles`), so the order a batch
  ;; lists its sentences in, and the handles they get, do not reach the order a listener
  ;; reads them in
  (tu/with-terms [dog Zed Abe Mo Bo]
    (let [run (fn [order]
                (let [[seen f] (recorder)
                      tok      (v/watch kb f)]
                  (v/assert-many kb (mapv #(list dog %) order) 'CxUniverse)
                  (v/unwatch kb tok)
                  (doseq [x order] (v/retract! kb (v/handle-of kb (list dog x) 'CxUniverse)))
                  (added @seen)))
          a (run [Zed Abe Mo Bo])]
      (is (= 4 (count a)))
      (is (= a (run [Bo Mo Abe Zed]))))))

(tu/deftest-kb the-feed-and-the-consequence-report-are-the-same-answer
  ;; Two mechanisms, one answer.  If they diverged an application would have no way to
  ;; tell which one was the KB's.
  (tu/with-terms [dog barks Muffet]
    (let [[seen f] (recorder)]
      (v/assert kb (vr/rule-sentence [(list dog '?x)] (list barks '?x)) 'CxUniverse {:direction :forward})
      (v/watch kb f)
      (let [report (v/edit-with-consequences! kb {:add [[(list dog Muffet) 'CxUniverse]]})]
        (is (= 1 (count @seen)))
        (is (= (set (map :sentence (:believed-added report))) (set (added @seen))))
        (is (= (set (map :sentence (:believed-removed report))) (set (removed @seen))))))))

;;; ── belief, not storage ────────────────────────────────────────────────

(tu/deftest-kb a-defeat-and-its-revival-both-arrive
  (tu/with-terms [dog barks Muffet]
    (let [[seen f] (recorder)]
      (v/assert kb (vr/rule-sentence [(list dog '?x)] (list barks '?x)) 'CxUniverse {:direction :forward})
      (v/assert kb (list dog Muffet) 'CxUniverse)
      (v/watch kb f)
      (let [neg (v/assert kb (list 'not (list barks Muffet)) 'CxUniverse
                          {:strength :monotonic})]
        (is (= 1 (count @seen)))
        (is (= [(list barks Muffet)] (removed @seen)) "the default lost to known-true content")
        (is (= :defeated (:reason (first (:believed-removed (first @seen))))))
        (reset! seen [])
        (v/retract! kb neg)
        (is (= 1 (count @seen)) "the revival is its own event")
        (is (= [(list barks Muffet)] (added @seen)))
        (is (empty? (removed @seen))
            "and not a duplicate of the defeat — the second event is the other direction")))))

(tu/deftest-kb a-preview-fires-nothing
  ;; The rollback of a removal restores a premise, a change of its own, so the next write's
  ;; event is where a region the rollback accumulated would surface.
  (tu/with-terms [dog barks Muffet Rex]
    (let [[seen f] (recorder)
          rex      (v/assert kb (list dog Rex) 'CxUniverse)]
      (v/assert kb (vr/rule-sentence [(list dog '?x)] (list barks '?x)) 'CxUniverse {:direction :forward})
      (v/watch kb f)
      (let [pv (v/preview kb {:add [[(list dog Muffet) 'CxUniverse]]})]
        (is (= 2 (count (:believed-added pv))) "the preview itself still answers"))
      (is (= 2 (count (:believed-removed (v/preview kb {:remove [rex]})))))
      (is (empty? @seen) "and the listener heard none of it")
      (let [h (v/assert kb (list barks Muffet) 'CxUniverse)]
        (is (= [(list barks Muffet)] (added @seen)) "the next write's event carries its own news")
        (is (empty? (removed @seen)))
        (v/retract! kb h)))))

(tu/deftest-kb a-rebuild-fires-nothing
  ;; `recover` relabels everything, so a feed through one would hand a reconnecting
  ;; application the whole KB as newly believed.
  (tu/with-terms [dog barks Muffet]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list barks '?x)) 'CxUniverse {:direction :forward})
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (let [[seen f] (recorder)]
      (v/watch kb f)
      (v/recover kb)
      (is (empty? @seen))
      (is (v/ask? kb (list barks Muffet) 'CxUniverse) "the rebuild did happen"))))

(tu/deftest-kb a-teardown-that-re-derives-what-it-swept-is-still-one-event
  ;; The exception's evidence leaves, so the block lifts, so the conclusion is
  ;; re-derived — two settles.  Delivered per settle, that would be a removal followed
  ;; by an addition of content whose net belief never moved.
  (tu/with-terms [dog barks sick Muffet]
    (v/assert kb (list 'exceptWhen [(list sick '?x)]
                       (list 'set/defaultRule
                             (list 'set/forwardRule (vr/rule-sentence [(list dog '?x)] (list barks '?x)))))
              'CxUniverse)
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (let [h (v/assert kb (list sick Muffet) 'CxUniverse)]
      (is (not (v/ask? kb (list barks Muffet) 'CxUniverse)) "the exception holds")
      (let [[seen f] (recorder)]
        (v/watch kb f)
        (v/retract! kb h)
        (is (= 1 (count @seen)) "one operation, one event")
        (is (= [(list barks Muffet)] (added @seen)))
        (is (v/ask? kb (list barks Muffet) 'CxUniverse))))))

(tu/deftest-kb a-reindex-fires-nothing-either
  ;; `recover`'s sibling: it rebuilds the index and then recovers, so it relabels
  ;; everything twice over.
  (tu/with-terms [dog Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (let [[seen f] (recorder)]
      (v/watch kb f)
      (v/reindex kb)
      (is (empty? @seen))
      (is (v/ask? kb (list dog Muffet) 'CxUniverse) "the rebuild did happen"))))

(tu/deftest-kb an-inert-sentex-arrives-nowhere
  ;; `assert-inert` stores without making a TMS datum, so there is no label to move and
  ;; nothing for a feed to be about.  The sharpest case of "belief, not storage".
  (tu/with-terms [dog Muffet]
    (let [[seen f] (recorder)]
      (v/watch kb f)
      (let [h (v/assert-inert kb (list dog Muffet) 'CxUniverse)]
        (is (some? h) "it was stored")
        (is (empty? @seen) "and no belief moved, so nothing arrived")
        ;; retracted here rather than by the fixture: an inert sentex is not a premise,
        ;; so the teardown's premise sweep cannot find it
        (v/retract! kb h)
        (is (empty? @seen) "removing one is not news either")))))

(tu/deftest-kb the-mint-rule-a-first-declaration-stores-arrives-with-it
  (tu/with-terms [animal parentOf]
    (let [[seen f] (recorder)]
      (v/watch kb f)
      (v/assert kb (list 'arg parentOf 1 animal) 'CxUniverse)
      (let [h (get (kb/mint-rule-table kb) 'arg)]
        (is (some? h))
        (is (some #(= h (:handle %)) (mapcat :believed-added @seen)))))))

(tu/deftest-kb forward-chain-delivers-what-it-derived
  ;; A second entry point into a settle, so it must feed too — `assert` is not the only
  ;; entry point.
  (tu/with-terms [dog barks Muffet]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list barks '?x)) 'CxUniverse
              {:direction :forward :chain? false})
    (v/assert kb (list dog Muffet) 'CxUniverse {:chain? false})
    (let [[seen f] (recorder)]
      (v/watch kb f)
      (is (= 1 (:derived (v/forward-chain kb))))
      (is (= [(list barks Muffet)] (added @seen))))))

(tu/deftest-kb a-batch-that-throws-reports-nothing-then-or-later
  ;; `edit!` is all-or-nothing, so a batch that throws leaves no belief to report — not
  ;; at the time and not at the next settle either.  The rollback runs with the feed off,
  ;; so it accumulates no region of its own, and the one event this entry point delivers has
  ;; nothing to hand anybody.
  (tu/with-terms [dog Muffet cat Tom]
    (let [[seen f] (recorder)]
      (v/watch kb f)
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/edit! kb {:add [[(list dog Muffet) 'CxUniverse]
                                      ['(not_ground ?x) 'CxUniverse]]})))
      (is (empty? @seen) "the batch was taken back, so nothing was reported")
      (v/edit! kb {:add [[(list dog Muffet) 'CxUniverse] [(list cat Tom) 'CxUniverse]]})
      (is (= 1 (count @seen)) "one settle, one event — the successful batch's")
      (is (= #{(list dog Muffet) (list cat Tom)} (set (added @seen)))
          "and it reports its own news, never the rolled-back batch's"))))

(tu/deftest-kb an-equality-merge-agrees-with-the-consequence-report
  ;; The contract is that a feed event and `edit-with-consequences` are the same answer,
  ;; and a merge is where that is tested: the displaced spelling loses belief with
  ;; no relabel to record it, and both read the supersession moves the settle publishes
  ;; (`special/take-supersession-moves!`), which name a spelling the assert path's
  ;; reconcile displaced with the entry it had before.
  (tu/with-terms [dog Pref Dep CxName]
    (v/assert kb (list dog Pref) CxName)
    (let [[seen f] (recorder)]
      (v/watch kb f)
      (let [report (v/edit-with-consequences!
                    kb {:add [[(list 'sameAs Pref Dep) CxName]]})]
        (is (= 1 (count @seen)))
        (is (= (set (map :sentence (:believed-added report))) (set (added @seen))))
        (is (= (set (map :sentence (:believed-removed report))) (set (removed @seen))))
        (is (= #{(list dog Pref)} (set (removed @seen)))
            "the displaced spelling is in both")))))

(tu/deftest-kb registering-a-listener-does-not-move-belief
  ;; A feed is a read.  If registering one moved an `in?`, the delivery point is wrong.
  (tu/with-terms [dog barks Muffet Rex]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list barks '?x)) 'CxUniverse {:direction :forward})
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (let [quiet (mapv #(v/ask? kb % 'CxUniverse)
                      [(list dog Muffet) (list barks Muffet)])]
      (v/watch kb (fn [_] nil))
      (v/assert kb (list dog Rex) 'CxUniverse)
      (is (= quiet (mapv #(v/ask? kb % 'CxUniverse)
                         [(list dog Rex) (list barks Rex)]))
          "the same scenario believes the same things with a listener attached"))))

;;; ── reentrancy, ordering, removal ──────────────────────────────────────

(tu/deftest-kb delivery-is-registration-order
  (tu/with-terms [dog Muffet]
    (let [order (atom [])]
      (doseq [k [:a :b :c]] (v/watch kb (fn [_] (swap! order conj k))))
      (v/assert kb (list dog Muffet) 'CxUniverse)
      (is (= [:a :b :c] @order)))))

(tu/deftest-kb a-listener-that-throws-loses-its-own-event-and-nothing-else
  (tu/with-terms [dog Muffet]
    (let [[seen f] (recorder)
          bug      (ex-info "a listener's bug" {})
          logged   (atom [])]
      (v/watch kb (fn [_] (throw bug)))
      (v/watch kb f)
      (let [h (binding [trove/*log-fn* (fn [_ns _coords _level id payload]
                                         (swap! logged conj [id (force payload)]))]
                (v/assert kb (list dog Muffet) 'CxUniverse))]
        (is (v/in? kb h) "the settle was already committed; the write stands")
        (is (= [(list dog Muffet)] (added @seen))
            "and the listener registered after the thrower still ran")
        (is (some (fn [[id p]] (and (= ::v/listener-threw id) (identical? bug (:error p))))
                  @logged)
            "and the log line carries what the listener threw, not its message alone")))))

(tu/deftest-kb a-listener-jvm-error-propagates-and-an-interrupt-keeps-its-flag
  (tu/with-terms [dog Muffet Rex]
    (let [token (v/watch kb (fn [_] (throw (OutOfMemoryError. "heap"))))]
      (is (thrown? OutOfMemoryError (v/assert kb (list dog Muffet) 'CxUniverse)))
      (is (some->> (v/handle-of kb (list dog Muffet) 'CxUniverse) (v/in? kb))
          "the settle was committed before delivery; the write stands")
      (v/unwatch kb token))
    (let [[seen f] (recorder)
          token    (v/watch kb (fn [_] (throw (InterruptedException. "stop the writer"))))]
      (v/watch kb f)
      (let [h     (v/assert kb (list dog Rex) 'CxUniverse)
            flag? (Thread/interrupted)]
        (is (v/in? kb h))
        (is flag? "the writing thread's interrupt flag is set again")
        (is (= [(list dog Rex)] (added @seen)) "and the next listener still ran"))
      (v/unwatch kb token))))

(tu/deftest-kb a-retraction-arrives-as-nothing-with-what-its-sweep-deleted
  ;; docs/feed.md, "What does not arrive": the premise and the conclusion that rested only
  ;; on it are both deleted, so neither has a record left for an entry to describe.
  (tu/with-terms [dog pet Muffet]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list pet '?x)) 'CxUniverse
              {:direction :forward})
    (let [h        (v/assert kb (list dog Muffet) 'CxUniverse)
          [seen f] (recorder)]
      (is (v/ask? kb (list pet Muffet) 'CxUniverse))
      (v/watch kb f)
      (v/retract! kb h)
      (is (not (v/ask? kb (list pet Muffet) 'CxUniverse)) "the conclusion went with it")
      (is (= [] @seen) "and the feed said nothing about either"))))

(tu/deftest-kb an-unwatch-off-the-writers-thread-can-see-one-more-event
  ;; docs/feed.md: delivery reads the registry once per event, so an event whose delivery
  ;; read it before the `unwatch` still reaches the listener, once, after `unwatch` returns.
  (tu/with-terms [dog Muffet Rex]
    (let [entered  (promise)
          release  (promise)
          [seen f] (recorder)
          first?   (atom true)]
      (v/watch kb (fn [_] (when (compare-and-set! first? true false)
                            (deliver entered true)
                            @release)))
      (let [t (v/watch kb f)
            w (future (v/assert kb (list dog Muffet) 'CxUniverse))]
        (is (true? (deref entered 10000 false)) "the writer is delivering")
        (is (true? (v/unwatch kb t)))
        (deliver release true)
        @w
        (is (= [(list dog Muffet)] (added @seen)) "the event in flight still arrived")
        (v/assert kb (list dog Rex) 'CxUniverse)
        (is (= 1 (count @seen)) "and nothing after it")))))

(tu/deftest-kb a-listener-that-asserts-is-delivered-its-own-event
  ;; Listeners run *after* the settle, so a write from one is an ordinary write: it
  ;; settles, and the delivery loop picks its region up in the next round.
  (tu/with-terms [dog pet Muffet]
    (let [[seen _] (recorder)
          wrote?   (atom false)]
      (v/watch kb (fn [e]
                    (swap! seen conj e)
                    (when (compare-and-set! wrote? false true)
                      (v/assert kb (list pet Muffet) 'CxUniverse))))
      (v/assert kb (list dog Muffet) 'CxUniverse)
      (is (= [[(list dog Muffet)] [(list pet Muffet)]]
             (mapv #(mapv :sentence (:believed-added %)) @seen))
          "two rounds, the second being what the listener itself wrote")
      (is (v/ask? kb (list pet Muffet) 'CxUniverse)))))

(tu/deftest-kb a-listeners-own-writes-are-not-the-batchs-consequences
  ;; A listener's `assert` settles, and that settle would fold its region into whatever
  ;; sink the *original* caller bound — so an `edit-with-consequences` would report the
  ;; listener's assertions as consequences of the batch.  The sinks are closed for the
  ;; duration of delivery, which is what this asserts.
  (tu/with-terms [dog Muffet sideEffect Yes]
    (let [wrote? (atom false)]
      (v/watch kb (fn [_] (when (compare-and-set! wrote? false true)
                            (v/assert kb (list sideEffect Yes) 'CxUniverse))))
      (let [report (v/edit-with-consequences!
                    kb {:add [[(list dog Muffet) 'CxUniverse]]})]
        (is (= [(list dog Muffet)] (mapv :sentence (:believed-added report)))
            "the report is about the batch, not about what a listener did in response")
        (is (v/ask? kb (list sideEffect Yes) 'CxUniverse)
            "and the listener's write did happen")))))

(tu/deftest-kb a-listener-that-writes-on-every-event-terminates-at-the-bound
  ;; The listener's bug, not the engine's — but the engine must report it rather than
  ;; hang the writer.  Unwatched inside the test, or the fixture's teardown retractions
  ;; would feed it again.
  (tu/with-terms [dog Muffet]
    (let [rounds (atom 0)
          token  (atom nil)]
      (reset! token (v/watch kb (fn [_]
                                  (swap! rounds inc)
                                  (v/assert kb (list dog (tu/tmp-ind "Round"))
                                            'CxUniverse))))
      (v/assert kb (list dog Muffet) 'CxUniverse)
      (v/unwatch kb @token)
      (is (= @#'feed/max-delivery-rounds @rounds)
          "it stops at the documented bound instead of spinning")
      (is (v/ask? kb (list dog Muffet) 'CxUniverse) "and the KB is usable after"))))

(tu/deftest-kb a-listener-may-unwatch-itself-mid-delivery
  ;; The registry is read once per event, so a listener editing it cannot make the
  ;; delivery loop skip or repeat one of its neighbours.
  (tu/with-terms [dog Muffet Rex]
    (let [[seen f] (recorder)
          also    (atom 0)
          token   (atom nil)]
      (reset! token (v/watch kb (fn [e] (f e) (v/unwatch kb @token))))
      (v/watch kb (fn [_] (swap! also inc)))
      (v/assert kb (list dog Muffet) 'CxUniverse)
      (is (= 1 (count @seen)))
      (is (= 1 @also) "the neighbour registered after it still ran for that event")
      (v/assert kb (list dog Rex) 'CxUniverse)
      (is (= 1 (count @seen)) "and the self-dropped one heard nothing more")
      (is (= 2 @also)))))

(tu/deftest-kb a-standing-query-does-not-render-what-it-did-not-match
  ;; The cost claim in the other direction from `lein perf`: the entries are the
  ;; expensive half of an event (a supporting justification and a `why-not` apiece), so
  ;; they are a `delay` a goal listener never forces.  Counted at the renderer, because
  ;; that is the only place the difference is observable.
  (tu/with-terms [dog cat Muffet Tom]
    (let [calls (atom 0)
          real  @#'v/preview-added-entry]
      (with-redefs [v/preview-added-entry (fn [kb h] (swap! calls inc) (real kb h))]
        (let [token (v/watch kb (list cat '?x) 'CxUniverse (fn [_] nil))]
          (v/assert kb (list dog Muffet) 'CxUniverse)
          (is (zero? @calls) "nothing the goal answers moved, so nothing was rendered")
          (v/assert kb (list cat Tom) 'CxUniverse)
          (is (= 1 @calls) "and a match renders exactly itself")
          (v/unwatch kb token))
        (reset! calls 0)
        (let [token (v/watch kb (fn [_] nil))]
          (v/assert kb (list dog (tu/tmp-ind "Plain")) 'CxUniverse)
          (is (pos? @calls) "a plain listener does want the whole diff")
          (v/unwatch kb token))))))

(tu/deftest-kb listeners-belong-to-one-kb
  ;; The renderer behind the extension point is installed once per process (`observe`'s pattern), so
  ;; the thing that must be per-KB is the registry.  Two live KBs, and neither hears the
  ;; other.  The second one is on the **isolated** pair: a `tu/fresh` here would clear the
  ;; scratch space out from under the `:each` fixture holding the first.
  (tu/with-cleared-kb [other tu/isolated-fresh]
    (tu/with-terms [dog Muffet Rex]
      (let [[here hf]  (recorder)
            [there tf] (recorder)]
        (v/watch kb hf)
        (v/watch other tf)
        (v/assert kb (list dog Muffet) 'CxUniverse)
        (v/assert other (list dog Rex) 'CxUniverse)
        (is (= [(list dog Muffet)] (added @here)))
        (is (= [(list dog Rex)] (added @there)))
        (is (= [{:token 0}] (v/watchers kb)) "each registry counts its own tokens")
        (is (= [{:token 0}] (v/watchers other)))))))

(deftest a-fork-starts-with-no-listeners-and-tells-its-base-nothing
  ;; A fork is a new KB over the base's stores, so its registry is its own — and taking
  ;; one is a `recover` over the merged contents, which is silent for the usual reason.
  ;;
  ;; Its own base rather than the fixture's, following `overlay_test`: a fork needs an
  ;; index written over the `KvBackend` protocol, so forking whatever `VAELII_TEST_BACKEND`
  ;; chose would throw on the two columnar pairs — and the claim here is about the
  ;; registry, not about the store under it.
  (let [base (doto (v/open-kb {:backend :memory :space [::base] :recover? false})
               tu/clear-kb!)]
    (tu/with-terms [dog Muffet cat Tom]
      (v/assert base (list dog Muffet) 'CxUniverse)
      (let [[seen f] (recorder)]
        (v/watch base f)
        (let [forked (v/fork base {:backend :memory :space [::fork]})]
          (is (empty? (v/watchers forked)) "a fork inherits no listeners")
          (is (empty? @seen) "and taking one is a rebuild, so the base heard nothing")
          (v/assert forked (list cat Tom) 'CxUniverse)
          (is (empty? @seen) "nor does a write into the fork reach the base's listeners")
          (is (v/ask? forked (list cat Tom) 'CxUniverse) "the fork did take the write")
          (tu/clear-kb! forked))))
    (tu/clear-kb! base)))

(tu/deftest-kb unwatch-stops-a-listener-and-says-whether-there-was-one
  (tu/with-terms [dog Muffet Rex]
    (let [[seen f] (recorder)
          token    (v/watch kb f)]
      (v/assert kb (list dog Muffet) 'CxUniverse)
      (is (= 1 (count @seen)))
      (is (true? (v/unwatch kb token)))
      (is (false? (v/unwatch kb token)) "idempotent — a token is not reissued")
      (v/assert kb (list dog Rex) 'CxUniverse)
      (is (= 1 (count @seen)) "nothing arrived after the token was dropped"))))

(tu/deftest-kb exactly-one-of-several-concurrent-unwatches-of-one-token-says-true
  ;; The boolean is the whole answer `unwatch` gives, and a caller uses it to decide
  ;; whether IT was the one that closed the subscription — so two callers both told true
  ;; is two callers each believing they own a teardown that happened once.  Read-then-swap
  ;; makes that routine under any real concurrency: both see the listener, both remove it,
  ;; both answer true.  One `swap-vals!` reads the answer off the CAS that did the removal.
  (let [rounds 60
        racers 8]
    (dotimes [_ rounds]
      (let [token (v/watch kb (fn [_] nil))
            start (java.util.concurrent.CountDownLatch. 1)
            fs    (doall (repeatedly racers
                                     #(future (.await start) (v/unwatch kb token))))]
        (.countDown start)
        (is (= 1 (count (filter true? (map deref fs))))
            "one caller removed the listener, so exactly one is told it did")
        (is (empty? (v/watchers kb)) "and the listener is gone either way")))))

(tu/deftest-kb watchers-lists-what-is-registered-without-the-functions
  (tu/with-terms [dog]
    (let [a (v/watch kb (fn [_] nil))
          b (v/watch kb (list dog '?x) 'CxUniverse (fn [_] nil))]
      (is (= [{:token a} {:token b :goal (list dog '?x) :context 'CxUniverse}]
             (v/watchers kb)))
      (v/unwatch kb a)
      (is (= [b] (mapv :token (v/watchers kb)))))))

;;; ── standing queries ───────────────────────────────────────────────────

(tu/deftest-kb a-standing-query-fires-only-on-what-answers-it
  (tu/with-terms [dog cat Muffet Tom]
    (let [[seen f] (recorder)]
      (v/watch kb (list dog '?x) 'CxUniverse f)
      (v/assert kb (list cat Tom) 'CxUniverse)
      (is (empty? @seen) "no call at all when nothing the goal answers moved")
      (v/assert kb (list dog Muffet) 'CxUniverse)
      (is (= [(list dog Muffet)] (added @seen)))
      (is (= [{'?x Muffet}] (mapv :bindings (:believed-added (first @seen))))
          "the entry says which solution moved"))))

(tu/deftest-kb a-standing-query-is-answered-by-a-subtype-and-a-sub-predicate
  ;; The same subsumption a rule antecedent gets — one cached closure lookup, not a
  ;; re-run of the goal.
  (tu/with-terms [animal_ dog_ Muffet parentOf fatherOf Tom Bob]
    (let [[types tf] (recorder)
          [rels rf]  (recorder)]
      (v/assert kb (list 'genl dog_ animal_) 'CxUniverse)
      (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
      (v/watch kb (list animal_ '?x) 'CxUniverse tf)
      (v/watch kb (list parentOf '?a '?b) 'CxUniverse rf)
      (v/assert kb (list dog_ Muffet) 'CxUniverse)
      (v/assert kb (list fatherOf Tom Bob) 'CxUniverse)
      (is (= [(list dog_ Muffet)] (added @types)) "a subtype answers a supertype goal")
      (is (= [{'?x Muffet}] (mapv :bindings (:believed-added (first @types)))))
      (is (= [(list fatherOf Tom Bob)] (added @rels))
          "and a sub-predicate answers a super-predicate goal")
      (is (= [{'?a Tom '?b Bob}] (mapv :bindings (:believed-added (first @rels))))))))

(tu/deftest-kb a-standing-query-sees-what-its-context-sees-and-no-more
  (tu/with-terms [dog Muffet Rex CxChild CxParent CxSibling]
    (v/assert kb (list 'genlCx CxChild CxParent) 'CxUniverse)
    (let [[seen f] (recorder)]
      (v/watch kb (list dog '?x) CxChild f)
      (v/assert kb (list dog Muffet) CxParent)
      (is (= [(list dog Muffet)] (added @seen)) "up the genlCx ancestor set, as any read is")
      (v/assert kb (list dog Rex) CxSibling)
      (is (= [(list dog Muffet)] (added @seen))
          "a context the watch cannot see is not its business"))))

(tu/deftest-kb a-variable-context-watches-every-context-and-binds-the-one-that-answered
  (tu/with-terms [dog Muffet Rex CxStory CxOther]
    (let [[seen f] (recorder)]
      (v/watch kb (list dog '?x) '?ctx f)
      (v/assert kb (list dog Muffet) CxStory)
      (v/assert kb (list dog Rex) CxOther)
      (is (= [(list dog Muffet) (list dog Rex)] (added @seen)))
      (is (= [{'?x Muffet '?ctx CxStory} {'?x Rex '?ctx CxOther}]
             (mapv #(:bindings (first (:believed-added %))) @seen))))))

(tu/deftest-kb a-standing-query-reports-what-left-belief-too
  (tu/with-terms [dog barks Muffet]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list barks '?x)) 'CxUniverse {:direction :forward})
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (let [[seen f] (recorder)]
      (v/watch kb (list barks '?x) 'CxUniverse f)
      (v/assert kb (list 'not (list barks Muffet)) 'CxUniverse {:strength :monotonic})
      (is (= [(list barks Muffet)] (removed @seen)))
      (is (= [{'?x Muffet}] (mapv :bindings (:believed-removed (first @seen)))))
      (is (= :defeated (:reason (first (:believed-removed (first @seen)))))))))

(tu/deftest-kb a-negated-goal-watches-the-negative-side-and-not-the-positive
  ;; The `not` is part of the stored sentence, so it separates the two watches with no
  ;; special handling — and a positive watch must not fire for a believed negation.
  (tu/with-terms [dog Muffet]
    (let [[pos pf] (recorder)
          [neg nf] (recorder)]
      (v/watch kb (list dog '?x) 'CxUniverse pf)
      (v/watch kb (list 'not (list dog '?x)) 'CxUniverse nf)
      (v/assert kb (list 'not (list dog Muffet)) 'CxUniverse)
      (is (empty? @pos))
      (is (= [(list 'not (list dog Muffet))] (added @neg)))
      (is (= [{'?x Muffet}] (mapv :bindings (:believed-added (first @neg))))))))

(tu/deftest-kb a-goal-whose-answer-is-not-in-the-region-is-refused
  ;; Being incomplete is one thing; being quietly wrong is the thing a feed must not
  ;; be.  Each of these has a truth that is a function of something no relabel carries.
  (tu/with-terms [dog cat]
    (doseq [goal [[(list dog '?x) (list cat '?y)]
                  (list 'agg/count '?n '?v (list dog '?v))
                  (list 'unknown (list dog '?x))
                  (list 'thereExists '?x (list dog '?x))
                  (list 'evaluate '?z '(+ 1 2))
                  (list 'ist 'CxUniverse (list dog '?x))
                  (list 'lessThan '?a '?b)
                  (list 'or (list dog '?x) (list cat '?x))
                  (list 'and (list dog '?x) (list cat '?x))
                  'notASentence]]
      (let [e (try (v/watch kb goal 'CxUniverse (fn [_] nil))
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (instance? clojure.lang.ExceptionInfo e)
            (str "watch accepted a goal it cannot answer: " (pr-str goal)))
        (is (= :not-watchable (:type (ex-data e))))
        (is (string? (:reason (ex-data e))) "the refusal says why")))
    (is (empty? (v/watchers kb)) "and registered nothing")))

(tu/deftest-kb one-conjunction-is-refused-in-both-its-spellings
  ;; `[(dog ?x) (cat ?x)]` and `(and (dog ?x) (cat ?x))` are one goal written two ways.
  ;; The vector was refused and the connective was not, so a watch on the second
  ;; registered and then fired never: no stored sentence has `and` for a functor, which
  ;; is the same silent-nothing the `or` arm beside it refuses by name.
  (tu/with-terms [dog cat]
    (let [vector-form [(list dog '?x) (list cat '?x)]
          and-form    (list 'and (list dog '?x) (list cat '?x))
          refusal     (fn [goal] (try (v/watch kb goal 'CxUniverse (fn [_] nil))
                                      (catch clojure.lang.ExceptionInfo e (ex-data e))))]
      (is (= :not-watchable (:type (refusal vector-form))))
      (is (= :not-watchable (:type (refusal and-form)))
          "the connective spelling of the same conjunction is refused too")
      (is (string? (:reason (refusal and-form))) "and says why")
      (testing "nested, not only at the top"
        (is (= :not-watchable
               (:type (refusal (list 'implies (list 'and (list dog '?x) (list cat '?x))
                                     (list dog '?x)))))))
      (is (empty? (v/watchers kb)) "and registered nothing"))))

(tu/deftest-kb a-goal-a-registered-calculus-answers-is-refused
  ;; The network entails tuples no fact stores and answers none naming a blocked node, so
  ;; a match over the region's stored facts would miss the first and report the second.
  (tu/with-terms [RegA]
    (let [goals   [(list 'nonTangentialProperPart RegA '?y)
                   (list 'not (list 'partOfRegion RegA '?y))]
          refusal (fn [goal] (try (v/watch kb goal 'CxUniverse (fn [_] nil)) nil
                                  (catch clojure.lang.ExceptionInfo e (ex-data e))))
          before  @(:provers kb)]
      (testing "with no prover registered the predicate's facts are ordinary facts"
        (let [t (v/watch kb (first goals) 'CxUniverse (fn [_] nil))]
          (is (some? t))
          (v/unwatch kb t)))
      (v/add-reasoner kb :rcc8)
      (try
        (doseq [g goals]
          (is (= :not-watchable (:type (refusal g))) (pr-str g)))
        (finally (reset! (:provers kb) before)))
      (is (empty? (v/watchers kb))))))

(tu/deftest-kb add-reasoner-refuses-a-calculus-answering-a-standing-watchs-goal
  ;; the watch was accepted while the predicate's facts were ordinary facts, and the
  ;; calculus would answer its goal off the network from then on
  (tu/with-terms [RegA]
    (let [before @(:provers kb)
          t      (v/watch kb (list 'not (list 'partOfRegion RegA '?y)) 'CxUniverse (fn [_] nil))]
      (try
        (let [e (try (v/add-reasoner kb :allen :rcc8) nil
                     (catch clojure.lang.ExceptionInfo e (ex-data e)))]
          (is (= :not-watchable (:type e)))
          (is (= [{:token t :calculus :rcc8}] (mapv #(dissoc % :goal) (:watches e))))
          (is (identical? before @(:provers kb)) "and registers neither name"))
        (finally (v/unwatch kb t) (reset! (:provers kb) before))))))

(tu/deftest-kb a-listener-that-is-not-a-function-is-refused
  ;; A keyword is `ifn?`, and so is a symbol — so the three-argument form written with
  ;; two would register its goal as the listener and fail at the first delivery, having
  ;; said nothing at the call that was wrong.
  (doseq [f [nil :not-a-fn 'alsoNotAFn {:a 1}]]
    (is (thrown? clojure.lang.ExceptionInfo (v/watch kb f)) (pr-str f)))
  (is (empty? (v/watchers kb)))
  (testing "a var naming one is a function"
    (let [t (v/watch kb #'identity)]
      (is (some? t))
      (v/unwatch kb t))))

(tu/deftest-kb a-goal-with-no-context-to-scope-it-is-refused
  ;; A context that names nothing sees nothing, so the watch would match forever and
  ;; report never — the same silent-nothing the goal refusals exist to prevent.
  (tu/with-terms [dog]
    (doseq [ctx [nil "CxUniverse" 7]]
      (let [e (try (v/watch kb (list dog '?x) ctx (fn [_] nil))
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (instance? clojure.lang.ExceptionInfo e) (pr-str ctx))
        (is (= :not-watchable (:type (ex-data e))))))
    (is (empty? (v/watchers kb)))))

;; ---- the delivery on the failure path ------------------------------------

(defn- with-throwing-dispatch
  "Run `f` with the extension point's renderer replaced by one that throws, then put the real one
  back.  The extension point is global (`feed/install-dispatch!`), so restoring it is what keeps
  this test from being the reason a later namespace sees no events."
  [f]
  (let [prior @#'feed/dispatch]
    (try (feed/install-dispatch!
          (fn [_ _ _] (throw (ex-info "the renderer fell over" {:type :error}))))
         (f)
         (finally (feed/install-dispatch! prior)))))

(deftest a-delivery-that-throws-rides-with-the-refusal-rather-than-replacing-it
  ;; `with-one-event` delivers on the failure path too, so a half-applied batch still
  ;; reports the belief it moved.  What the caller must not lose is *why the batch
  ;; failed* — it asked to write and was told no, and that is the news.  Out of a
  ;; `finally` a throwing delivery would be the only thing it ever saw.
  ;;
  ;; A bare feed rather than a KB: nothing here is about inference, and the renderer has
  ;; to throw somewhere `notify-listener!`'s own guard does not already catch it.
  (let [fake {:feed (feed/create-feed)}]
    (feed/register! fake {:f (fn [_] nil)})
    (with-throwing-dispatch
      (fn []
        (feed/note-region! fake #{1} #{})
        (let [t (try (feed/with-one-event fake
                       (throw (ex-info "the batch was refused" {:type :naming})))
                     (catch clojure.lang.ExceptionInfo e e))]
          (is (instance? clojure.lang.ExceptionInfo t))
          (is (= :naming (:type (ex-data t)))
              "the caller reads its own refusal, not the renderer's failure")
          (is (= ["the renderer fell over"]
                 (mapv ex-message (.getSuppressed ^Throwable t)))
              "and the delivery's failure rides with it, where a reader finds both"))))))

(deftest a-delivery-that-throws-on-the-way-out-still-throws
  ;; The other direction, so the change above cannot be read as "the failure path
  ;; swallows": a body that returns and a renderer that throws is a throw, exactly as
  ;; the `finally` spelling gave.
  (let [fake {:feed (feed/create-feed)}]
    (feed/register! fake {:f (fn [_] nil)})
    (with-throwing-dispatch
      (fn []
        (feed/note-region! fake #{1} #{})
        (let [t (try (feed/with-one-event fake :answered)
                     (catch clojure.lang.ExceptionInfo e e))]
          (is (instance? clojure.lang.ExceptionInfo t))
          (is (= "the renderer fell over" (ex-message t)))))))
  (testing "and a delivery that does not throw hands back the body's value"
    (let [fake {:feed (feed/create-feed)}]
      (is (= :answered (feed/with-one-event fake :answered))))))

(tu/deftest-kb a-standing-query-with-a-variable-functor-fires
  ;; A goal whose functor is a variable — `(?p Muffet)` — is answered by any stored
  ;; unary fact about Muffet.  `sentexes-matching` and `ask` answer it, so a watch must
  ;; too; the unary match arm read `specs` of the variable (reflexive, holding no
  ;; concrete functor) and left it silently unfired.
  (tu/with-terms [dog Muffet]
    (let [[seen f] (recorder)]
      (v/watch kb (list '?p Muffet) 'CxUniverse f)
      (v/assert kb (list dog Muffet) 'CxUniverse)
      (is (= [(list dog Muffet)] (added @seen))
          "a matching unary fact fires the variable-functor goal"))))

;;; ── a belief a reader's verdict moved ──────────────────────────────────

(defn- believed-pairs
  "The `[sentence context]` pairs of `pairs` believed at their own context now."
  [kb pairs]
  (into #{} (filter (fn [[s c]] (when-let [h (v/handle-of kb s c)] (v/believed? kb h c))))
        pairs))

(defn- reported
  "The `[added removed]` halves of a report or of `events`, as the `[sentence context]`
  pairs of `pairs` they name."
  [pairs added removed]
  (let [keep (fn [entries] (into #{} (comp (map (juxt :sentence :context)) (filter (set pairs)))
                                 entries))]
    [(keep added) (keep removed)]))

(tu/deftest-kb a-verdict-a-reader-reaches-arrives-in-every-order
  ;; CxJ sees CxA, CxB and CxD, so it decides the membership nogood and takes (cat Rex)
  ;; OUT, and (meows Rex), stored at CxJ, rests only on it.  Neither member's own context
  ;; sees the other, so no label moves: the published set has to carry the move.  Each write,
  ;; and each retraction after them, is made in every order twice: once previewed first,
  ;; once through `edit-with-consequences!` under a listener.  Each report names what the
  ;; readings of belief at each sentence's own context before and after differ by; a
  ;; preview also names a removed premise, and the other two leave out what a removal
  ;; deleted.
  ;;
  ;;   CxA  (cat Rex) default     CxB  (dog Rex) monotonic     CxD  (disjoint dog cat)
  ;;   CxJ sees CxA, CxB and CxD:  (cat ?x) => (meows ?x)
  (doseq [mode  [:preview :edit]
          order (gen/permutations [:disjoint :dog :cat :rule])]
    (tu/with-terms [dog cat meows Rex CxA CxB CxD CxJ]
      (doseq [[c up] [[CxA 'CxUniverse] [CxB 'CxUniverse] [CxD 'CxUniverse]
                      [CxJ CxA] [CxJ CxB] [CxJ CxD]]]
        (v/assert kb (list 'genlCx c up) 'CxUniverse {:strength :monotonic}))
      (let [writes {:disjoint [(list 'disjoint dog cat) CxD {:strength :monotonic}]
                    :dog      [(list dog Rex) CxB {:strength :monotonic}]
                    :cat      [(list cat Rex) CxA {}]
                    :rule     [(vr/rule-sentence [(list cat '?x)] (list meows '?x)) CxJ
                               {:direction :forward}]}
            pairs  [[(list cat Rex) CxA] [(list dog Rex) CxB] [(list meows Rex) CxJ]]
            step   (fn [label batch]
                     (let [before (believed-pairs kb pairs)
                           msg    (str (name mode) " " label " " order)]
                       (if (= :preview mode)
                         (let [r (v/preview kb batch)]
                           (v/edit! kb batch)
                           (let [after (believed-pairs kb pairs)]
                             (is (= [(into #{} (remove before) after)
                                     (into #{} (remove after) before)]
                                    (reported pairs (:believed-added r) (:believed-removed r)))
                                 msg)))
                         (let [[seen f] (recorder)
                               tok      (v/watch kb f)
                               r        (v/edit-with-consequences! kb batch)
                               _        (v/unwatch kb tok)
                               after    (believed-pairs kb pairs)
                               want     [(into #{} (remove before) after)
                                         (into #{} (comp (remove after)
                                                         (filter (fn [[s c]] (v/handle-of kb s c))))
                                               before)]]
                           (is (= want (reported pairs (:believed-added r) (:believed-removed r)))
                               (str msg " sinks"))
                           (is (= want (reported pairs (mapcat :believed-added @seen)
                                                 (mapcat :believed-removed @seen)))
                               (str msg " feed"))))))]
        (doseq [k order] (step [:add k] {:add [(writes k)]}))
        (is (= #{[(list dog Rex) CxB]} (disj (believed-pairs kb pairs) [(list cat Rex) CxA]))
            "CxJ withdraws (meows Rex)")
        (doseq [k order
                :let [[s c] (writes k)]]
          (step [:remove k] {:remove [(v/handle-of kb s c)]}))))))

(defn- own-belief
  "Every stored handle believed at its own context, the reading an event is a diff of."
  [kb]
  (into #{} (filter #(when-let [sx (p/get-sentex (:records kb) %)]
                       (res/believed-at? kb % (:context sx))))
        (p/sentex-ids (:records kb))))

(defn- step-disagreements
  "Each step `[label f]` of `steps`, `f` taking the KB, run under a listener on a KB of its
  own after the writes of `order`, as one entry per step whose events differ from the diff
  of `own-belief` around it.  An entry also names a step delivering one handle twice."
  [order steps]
  (let [loaded (gen/load-world! nil [] {})
        kb     (:kb loaded)
        seen   (atom [])
        out    (atom [])]
    (try
      (v/watch kb #(swap! seen conj %))
      (doseq [{:keys [sentence context strength]} order]
        (v/assert kb (gen/engine-form sentence) context {:strength (or strength :default)}))
      (doseq [[label f] steps]
        (let [before (own-belief kb)]
          (reset! seen [])
          (try (f kb) (catch clojure.lang.ExceptionInfo _ nil))
          (let [after  (own-belief kb)
                stored (set (p/sentex-ids (:records kb)))
                want   [(into #{} (remove before) after)
                        (into #{} (comp (remove after) (filter stored)) before)]
                hs     (fn [half] (into [] (comp (mapcat half) (map :handle)) @seen))
                named  (concat (hs :believed-added) (hs :believed-removed))
                got    [(set (hs :believed-added)) (set (hs :believed-removed))]]
            (when-not (and (= want got) (or (empty? named) (apply distinct? named)))
              (swap! out conj {:step label :want want :got got :named named})))))
      @out
      (finally (gen/close-kb! loaded)))))

(defn- event-disagreements
  "Each write of `world` in `order`, then each retraction in `removals` (`order` when
  not given), made under a listener on a KB of its own, as one entry per step whose event
  differs from the diff of `own-belief` around it."
  ([world order] (event-disagreements world order order))
  ([world order removals]
   (let [loaded (gen/load-world! world [] {})
         kb     (:kb loaded)
         seen   (atom [])
         out    (atom [])
         step   (fn [label f]
                  (let [before (own-belief kb)]
                    (reset! seen [])
                    (try (f) (catch clojure.lang.ExceptionInfo _ nil))
                    (let [after  (own-belief kb)
                          stored (set (p/sentex-ids (:records kb)))
                          want   [(into #{} (remove before) after)
                                  (into #{} (comp (remove after) (filter stored)) before)]
                          got    [(into #{} (comp (mapcat :believed-added) (map :handle)) @seen)
                                  (into #{} (comp (mapcat :believed-removed) (map :handle)) @seen)]]
                      (when-not (= want got)
                        (swap! out conj {:step label :want want :got got})))))]
     (try
       (v/watch kb #(swap! seen conj %))
       (doseq [{:keys [sentence context strength]} order]
         (step [:add sentence context]
               #(v/assert kb (gen/engine-form sentence) context {:strength (or strength :default)})))
       (doseq [{:keys [sentence context]} removals]
         (step [:remove sentence context]
               #(some->> (v/handle-of kb (gen/engine-form sentence) context) (v/retract! kb))))
       @out
       (finally (gen/close-kb! loaded))))))

(defn- random-event-check [seeds]
  (let [bad (for [seed  seeds
                  :let  [world (gen/gen-world seed {})
                         ws    (vec (:writes world))]
                  order [ws (vec (rseq ws))]
                  d     (event-disagreements world order)]
              (assoc d :seed seed))]
    (is (= [] (vec (take 4 bad))))))

(deftest an-un-merge-reports-no-given-back-spelling-the-step-did-not-move
  ;; (relb IndA IndB) is superseded by (relb IndA IndA) under the merge of IndA and IndB,
  ;; so it is not believed before the retraction.  In the first two rows the retraction
  ;; un-merges, and the given-back spelling is decided OUT beside the :monotonic
  ;; (relb IndA IndA); in the third the merge stands and the spelling stays superseded.
  (let [w     (fn [s st] {:sentence s :context 'CxA :strength st})
        R     '(set/forwardRule (implies (route ?x ?y) (relb ?x ?y)))
        route (w '(route IndA IndB) :monotonic)
        eq    (w '(equals IndA IndB) :monotonic)]
    (doseq [[label writes removal]
            [["the route retracted: the class drop un-merges"
              [(w R :monotonic) route (w '(relb IndA IndB) :default)] route]
             ["the equality retracted"
              [(w '(relb IndA IndB) :default) eq] eq]
             ["the route retracted beside a :monotonic premise: the merge stands"
              [(w R :monotonic) route (w '(relb IndA IndB) :monotonic)] route]]]
      (let [order (into [{:sentence '(genlCx CxA CxUniverse) :context 'CxUniverse
                          :strength :monotonic}
                         (w '(functional relb) :monotonic) (w '(relb IndA IndA) :monotonic)]
                        writes)]
        (is (= [] (event-disagreements {:contexts #{'CxA}} order [removal])) label)))))

(deftest a-deferred-batch-reports-against-the-belief-before-its-first-write
  ;; (cat Rex) loses to the :monotonic (dog Rex) in CxA.  An except of the winner hides it
  ;; when it is stored, before the batch's settle; a retraction inside a batch settles at
  ;; once, and the batch's closing settle has nothing left to report.
  (let [w     (fn [s st] {:sentence s :context 'CxA :strength st})
        order [{:sentence '(genlCx CxA CxUniverse) :context 'CxUniverse :strength :monotonic}
               (w '(disjoint dog cat) :monotonic) (w '(dog Rex) :monotonic) (w '(cat Rex) :default)]
        dog   #(v/handle-of % '(dog Rex) 'CxA)]
    (doseq [[label f]
            [["an except of the winner, deferred"
              #(v/with-deferred-settle %
                 (v/assert % (list 'except (v/sentex-handle (dog %))) 'CxA {:strength :monotonic}))]
             ["the winner retracted inside a batch"
              #(v/with-deferred-settle % (v/retract! % (dog %)))]
             ["a fact beside the winner's retraction, in one batch"
              #(v/with-deferred-settle %
                 (v/assert % '(color Sky Blue) 'CxA)
                 (v/retract! % (dog %)))]]]
      (is (= [] (step-disagreements order [[label f]])) label))))

(deftest a-write-moving-a-conflict-a-reader-s-excepts-decide-reports-its-member-s-consequences
  ;;   CxUniverse  (disjoint dog cat)
  ;;     ├─ CxA     (cat Rex) default, and :monotonic through (cat_src Rex)
  ;;     ├─ CxB     (dog Rex) :monotonic
  ;;     └─ CxHide  (except (cat_src Rex)), in the steps that store it
  ;;   CxW sees CxA and CxB: the conflict's placement, no defeat
  ;;   CxZ sees CxW and CxHide: (cat ?x) => (meows ?x), and (meows Rex) rests on (cat Rex),
  ;;   whose class at CxZ is :default while the except is stored, so the conflict defeats it there
  (let [m     (fn [s c] {:sentence s :context c :strength :monotonic})
        order (-> (mapv (fn [[c up]] (m (list 'genlCx c up) 'CxUniverse))
                        [['CxA 'CxUniverse] ['CxB 'CxUniverse] ['CxHide 'CxUniverse]
                         ['CxW 'CxA] ['CxW 'CxB] ['CxZ 'CxW] ['CxZ 'CxHide]])
                  (into [(m '(disjoint dog cat) 'CxUniverse)
                         (m '(set/forwardRule (implies (cat_src ?x) (cat ?x))) 'CxA)
                         (m '(cat_src Rex) 'CxA)
                         {:sentence '(cat Rex) :context 'CxA :strength :default}
                         (m '(dog Rex) 'CxB)
                         (m '(set/forwardRule (implies (cat ?x) (meows ?x))) 'CxZ)]))
        hide  (fn [kb] (v/assert kb (list 'except (v/sentex-handle (v/handle-of kb '(cat_src Rex) 'CxA)))
                                 'CxHide {:strength :monotonic}))
        shown #(v/retract! % (v/handle-of % (list 'except (v/sentex-handle (v/handle-of % '(cat_src Rex) 'CxA)))
                                          'CxHide))]
    (is (= [] (step-disagreements order [["the except stored" hide] ["the except retracted" shown]])))
    (is (= [] (step-disagreements order [["the except stored" hide]
                                         ["the winner retracted" #(v/retract! % (v/handle-of % '(dog Rex) 'CxB))]])))))

(deftest a-genlcx-edge-to-a-declaring-context-reports-the-denials-it-defeats
  ;; (not (dog Rex)) and (dog Rex) are a default dilemma at CxA.  The edge (genlCx CxA D)
  ;; makes dog forced-monotonic at CxA, so the denial loses there, and its retraction
  ;; undoes that; no label moves either way.  D is CxUniverse in the second row.
  (doseq [d ['CxD 'CxUniverse]]
    (let [m     (fn [s c] {:sentence s :context c :strength :monotonic})
          edge  (list 'genlCx 'CxA d)
          order [(m '(genlCx CxA CxUniverse) 'CxUniverse)
                 (m '(genlCx CxD CxUniverse) 'CxUniverse)
                 {:sentence '(forced_monotonic_predicate dog) :context d :strength :default}
                 {:sentence '(not (dog Rex)) :context 'CxA :strength :default}
                 {:sentence '(dog Rex) :context 'CxA :strength :default}]]
      (is (= [] (step-disagreements order [["the edge stored" #(v/assert % edge 'CxUniverse {:strength :monotonic})]
                                           ["the edge retracted" #(v/retract! % (v/handle-of % edge 'CxUniverse))]]))
          (str d)))))

;; (flies Opus) rests on (bird Opus), which the :monotonic denial defeats at CxA, and on
;; (winged Opus) through a second rule.  Removing the second support leaves (flies Opus)
;; IN in the network and hidden at CxA; adding it back believes it with no label moving.
(deftest a-support-beside-a-defeated-one-reports-its-conclusion-when-it-goes-and-comes
  (let [m      (fn [s] {:sentence s :context 'CxA :strength :monotonic})
        order  [{:sentence '(genlCx CxA CxUniverse) :context 'CxUniverse :strength :monotonic}
                (m '(implies (bird ?x) (flies ?x))) (m '(implies (winged ?x) (flies ?x)))
                {:sentence '(bird Opus) :context 'CxA :strength :default} (m '(not (bird Opus)))]
        winged (fn [kb] (v/handle-of kb '(winged Opus) 'CxA))]
    (is (= [] (step-disagreements (conj order (m '(winged Opus)))
                                  [["the second support retracted" #(v/retract! % (winged %))]])))
    (is (= [] (step-disagreements order
                                  [["the second support asserted"
                                    #(v/assert % '(winged Opus) 'CxA {:strength :monotonic})]])))))

;; (dog Rex) and (cat Rex) are :default in CxA under (disjoint dog cat).  A :monotonic
;; support for (dog Rex) through a rule raises its class with no label moving, and the
;; conflict's verdict turns from a dilemma to a defeat of (cat Rex); its retraction turns
;; it back.
(deftest a-class-a-write-moves-reports-the-verdict-it-turns
  (let [m     (fn [s] {:sentence s :context 'CxA :strength :monotonic})
        d     (fn [s] {:sentence s :context 'CxA :strength :default})
        order [{:sentence '(genlCx CxA CxUniverse) :context 'CxUniverse :strength :monotonic}
               (m '(disjoint dog cat)) (m '(implies (dog_src ?x) (dog ?x)))
               (d '(dog Rex)) (d '(cat Rex))]
        src   #(v/handle-of % '(dog_src Rex) 'CxA)]
    (is (= [] (step-disagreements order [["the support asserted" #(v/assert % '(dog_src Rex) 'CxA {:strength :monotonic})]
                                         ["the support retracted" #(v/retract! % (src %))]])))))

;; (t1 Pip) :default and (t2 Pip) :monotonic in CxB under (sibling_disjoint col): the
;; separation defeats (t1 Pip) at CxB.  A `siblingDisjointException` stated in CxB exempts
;; the pair there, so (t1 Pip) is believed with no label moving; its retraction hides it.
(deftest an-exemption-a-write-moves-reports-the-member-it-releases
  (let [u     (fn [s] {:sentence s :context 'CxUniverse :strength :monotonic})
        order [(u '(genlCx CxB CxUniverse)) (u '(genl t1 col)) (u '(genl t2 col)) (u '(sibling_disjoint col))
               {:sentence '(t1 Pip) :context 'CxB :strength :default}
               {:sentence '(t2 Pip) :context 'CxB :strength :monotonic}]
        exc   '(siblingDisjointException t1 t2)]
    (is (= [] (step-disagreements order [["the exception stored" #(v/assert % exc 'CxB {:strength :monotonic})]
                                         ["the exception retracted" #(v/retract! % (v/handle-of % exc 'CxB))]])))))

(deftest every-event-is-the-diff-of-own-context-belief-in-random-worlds
  (random-event-check (range 40)))

(deftest ^:slow every-event-is-the-diff-of-own-context-belief-in-400-random-worlds
  (random-event-check (range 400)))

;;; ── a defeat placed by the settle ──────────────────────────────────────

(tu/deftest-kb an-observation-that-defeats-a-default-arrives-as-a-defeat-report
  ;; docs/feed.md, "A defeat arrives as a report".  The clash is placed at CxSeat, where
  ;; (cat Muffet) is no longer believed; CxUniverse, where it is stored, still believes it,
  ;; so no `:believed-removed` entry names it.
  (tu/with-terms [dog_t cat_t Muffet CxSeat]
    (v/assert kb (list 'genlCx CxSeat 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list cat_t Muffet) 'CxUniverse)
    (let [[seen f]     (recorder)
          [below fb]   (recorder)
          [above fa]   (recorder)
          tokens       [(v/watch kb f) (v/watch kb (list cat_t '?x) CxSeat fb)
                        (v/watch kb (list cat_t '?x) 'CxUniverse fa)]
          content      (fn [events]
                         (into [] (comp (mapcat :defeats)
                                        (map (juxt (comp (juxt :sentence :context) :loser)
                                                   #(mapv (juxt :sentence :context) (:winners %))
                                                   :placed-in :verdict)))
                               events))
          expected     [[[(list cat_t Muffet) 'CxUniverse] [[(list dog_t Muffet) CxSeat]]
                         [CxSeat] :defeat]]]
      (v/assert kb (list dog_t Muffet) CxSeat {:strength :monotonic})
      (is (= expected (content @seen)) "a plain listener reads the defeat")
      (is (= [] (removed @seen)))
      (is (= expected (content @below)) "a standing query below the placement reads it")
      (is (empty? @above) "a standing query above the placement is not called")
      (run! #(v/unwatch kb %) tokens))))
