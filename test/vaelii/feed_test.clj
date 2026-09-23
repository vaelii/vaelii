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
            [vaelii.core :as v]
            [vaelii.impl.feed :as feed]
            [vaelii.impl.rules :as vr]
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
  ;; A preview stores, settles, reads the diff and takes every write back.  A feed
  ;; through one would send a change and then its exact reverse.
  (tu/with-terms [dog barks Muffet]
    (let [[seen f] (recorder)]
      (v/assert kb (vr/rule-sentence [(list dog '?x)] (list barks '?x)) 'CxUniverse {:direction :forward})
      (v/watch kb f)
      (let [pv (v/preview kb {:add [[(list dog Muffet) 'CxUniverse]]})]
        (is (= 2 (count (:believed-added pv))) "the preview itself still answers")
        (is (empty? @seen) "and the listener heard none of it")))))

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
  ;; and a merge is where that is worth pinning: the displaced spelling loses belief with
  ;; no relabel to record it, and the hand-off both read covers only what the *settle*
  ;; supersedes — an equality merge installs its supersession on the assert path.  So
  ;; neither reports it, `preview` does, and this test is what keeps the two that must
  ;; agree agreeing (and names the third).
  (tu/with-terms [dog Pref Dep CxName]
    (v/assert kb (list dog Pref) CxName)
    (let [[seen f] (recorder)]
      (v/watch kb f)
      (let [report (v/edit-with-consequences!
                    kb {:add [[(list 'sameAs Pref Dep) CxName]]})]
        (is (= 1 (count @seen)))
        (is (= (set (map :sentence (:believed-added report))) (set (added @seen))))
        (is (= (set (map :sentence (:believed-removed report))) (set (removed @seen))))
        (is (empty? (removed @seen))
            "the displaced spelling is not in either — see preview_test for the one that
             does report it")))))

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
    (let [[seen f] (recorder)]
      (v/watch kb (fn [_] (throw (ex-info "a listener's bug" {}))))
      (v/watch kb f)
      (let [h (v/assert kb (list dog Muffet) 'CxUniverse)]
        (is (v/in? kb h) "the settle was already committed; the write stands")
        (is (= [(list dog Muffet)] (added @seen))
            "and the listener registered after the thrower still ran")))))

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
  ;; duration of delivery, which is what this pins.
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
  ;; one is a `recover` over the merged view, which is silent for the usual reason.
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
