;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.feed-test
  "The change feed: an application told that belief moved, instead of asking again.

  Every claim here is about the *seam*, not about inference — the engine already
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
  vocabulary (`genl`, `genlContext`, `set/defaultRule`, `exceptWhen`) literal, and the
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
      (v/assert kb (list dog Muffet) 'UniverseContext)
      (is (= 1 (count @seen)) "one settle, one event")
      (is (= [(list dog Muffet)] (added @seen)))
      (is (empty? (removed @seen)))
      (let [e (first (:believed-added (first @seen)))]
        (is (= 'UniverseContext (:context e)))
        (is (true? (:premise? e)) "an asserted fact is a premise")
        (is (= (v/handle-of kb (list dog Muffet) 'UniverseContext) (:handle e))
            "the entry is addressable")))))

(tu/deftest-kb a-derived-conclusion-arrives-with-the-rule-that-derived-it
  (tu/with-terms [dog barks Muffet]
    (let [[seen f] (recorder)]
      (v/assert kb (vr/rule-sentence [(list dog '?x)] (list barks '?x)) 'UniverseContext)
      (v/watch kb f)
      (v/assert kb (list dog Muffet) 'UniverseContext)
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
      (v/assert kb (list dog Muffet) 'UniverseContext)
      (v/watch kb f)
      (testing "re-asserting a stored sentex is not news"
        (v/assert kb (list dog Muffet) 'UniverseContext)
        (is (empty? @seen)))
      (testing "...but an unrelated fact is, to a plain listener"
        (v/assert kb (list cat Tom) 'UniverseContext)
        (is (= [(list cat Tom)] (added @seen)))))))

(tu/deftest-kb a-batch-settles-once-and-is-one-event
  (tu/with-terms [dog barks Muffet Rex Spot]
    (let [[seen f] (recorder)]
      (v/assert kb (vr/rule-sentence [(list dog '?x)] (list barks '?x)) 'UniverseContext)
      (v/watch kb f)
      (v/assert-many kb (mapv #(list dog %) [Muffet Rex Spot]) 'UniverseContext)
      (is (= 1 (count @seen)) "three asserts, one settle, one event")
      (is (= 6 (count (added @seen))) "three premises and three conclusions"))))

(tu/deftest-kb the-feed-and-the-consequence-report-are-the-same-answer
  ;; Two mechanisms, one answer.  If they diverged an application would have no way to
  ;; tell which one was the KB's.
  (tu/with-terms [dog barks Muffet]
    (let [[seen f] (recorder)]
      (v/assert kb (vr/rule-sentence [(list dog '?x)] (list barks '?x)) 'UniverseContext)
      (v/watch kb f)
      (let [report (v/edit-with-consequences! kb {:add [[(list dog Muffet) 'UniverseContext]]})]
        (is (= 1 (count @seen)))
        (is (= (set (map :sentence (:believed-added report))) (set (added @seen))))
        (is (= (set (map :sentence (:believed-removed report))) (set (removed @seen))))))))

;;; ── belief, not storage ────────────────────────────────────────────────

(tu/deftest-kb a-defeat-and-its-revival-both-arrive
  (tu/with-terms [dog barks Muffet]
    (let [[seen f] (recorder)]
      (v/assert kb (vr/rule-sentence [(list dog '?x)] (list barks '?x)) 'UniverseContext)
      (v/assert kb (list dog Muffet) 'UniverseContext)
      (v/watch kb f)
      (let [neg (v/assert kb (list 'not (list barks Muffet)) 'UniverseContext
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
      (v/assert kb (vr/rule-sentence [(list dog '?x)] (list barks '?x)) 'UniverseContext)
      (v/watch kb f)
      (let [pv (v/preview kb {:add [[(list dog Muffet) 'UniverseContext]]})]
        (is (= 2 (count (:believed-added pv))) "the preview itself still answers")
        (is (empty? @seen) "and the listener heard none of it")))))

(tu/deftest-kb a-rebuild-fires-nothing
  ;; `recover` relabels everything, so a feed through one would hand a reconnecting
  ;; application the whole KB as newly believed.
  (tu/with-terms [dog barks Muffet]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list barks '?x)) 'UniverseContext)
    (v/assert kb (list dog Muffet) 'UniverseContext)
    (let [[seen f] (recorder)]
      (v/watch kb f)
      (v/recover kb)
      (is (empty? @seen))
      (is (v/ask? kb (list barks Muffet) 'UniverseContext) "the rebuild did happen"))))

(tu/deftest-kb a-teardown-that-re-derives-what-it-swept-is-still-one-event
  ;; The exception's evidence leaves, so the block lifts, so the conclusion is
  ;; re-derived — two settles.  Delivered per settle, that would be a removal followed
  ;; by an addition of content whose net belief never moved.
  (tu/with-terms [dog barks sick Muffet]
    (v/assert kb (list 'exceptWhen [(list sick '?x)]
                       (list 'set/defaultRule
                             (vr/rule-sentence [(list dog '?x)] (list barks '?x))))
              'UniverseContext)
    (v/assert kb (list dog Muffet) 'UniverseContext)
    (let [h (v/assert kb (list sick Muffet) 'UniverseContext)]
      (is (not (v/ask? kb (list barks Muffet) 'UniverseContext)) "the exception holds")
      (let [[seen f] (recorder)]
        (v/watch kb f)
        (v/retract! kb h)
        (is (= 1 (count @seen)) "one operation, one event")
        (is (= [(list barks Muffet)] (added @seen)))
        (is (v/ask? kb (list barks Muffet) 'UniverseContext))))))

(tu/deftest-kb a-reindex-fires-nothing-either
  ;; `recover`'s sibling: it rebuilds the index and then recovers, so it relabels
  ;; everything twice over.
  (tu/with-terms [dog Muffet]
    (v/assert kb (list dog Muffet) 'UniverseContext)
    (let [[seen f] (recorder)]
      (v/watch kb f)
      (v/reindex kb)
      (is (empty? @seen))
      (is (v/ask? kb (list dog Muffet) 'UniverseContext) "the rebuild did happen"))))

(tu/deftest-kb an-inert-sentex-arrives-nowhere
  ;; `assert-inert` stores without making a TMS datum, so there is no label to move and
  ;; nothing for a feed to be about.  The sharpest case of "belief, not storage".
  (tu/with-terms [dog Muffet]
    (let [[seen f] (recorder)]
      (v/watch kb f)
      (let [h (v/assert-inert kb (list dog Muffet) 'UniverseContext)]
        (is (some? h) "it was stored")
        (is (empty? @seen) "and no belief moved, so nothing arrived")
        ;; retracted here rather than by the fixture: an inert sentex is not a premise,
        ;; so the teardown's premise sweep cannot find it
        (v/retract! kb h)
        (is (empty? @seen) "removing one is not news either")))))

(tu/deftest-kb forward-chain-delivers-what-it-derived
  ;; A second entry point into a settle, so it must feed too — `assert` is not the only
  ;; door.
  (tu/with-terms [dog barks Muffet]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list barks '?x)) 'UniverseContext
              {:chain? false})
    (v/assert kb (list dog Muffet) 'UniverseContext {:chain? false})
    (let [[seen f] (recorder)]
      (v/watch kb f)
      (is (= 1 (:derived (v/forward-chain kb))))
      (is (= [(list barks Muffet)] (added @seen))))))

(tu/deftest-kb a-batch-that-throws-leaves-belief-unsettled-and-reports-it-next-time
  ;; `edit` is not a transaction: a throw mid-batch leaves what was already stored in
  ;; place with the settle not run.  So the delivery is not *lost* — there was nothing to
  ;; deliver yet, and the next settle's region still holds the handle.
  (tu/with-terms [dog Muffet cat Tom]
    (let [[seen f] (recorder)]
      (v/watch kb f)
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/edit! kb {:add [[(list dog Muffet) 'UniverseContext]
                                      ['(notGround ?x) 'UniverseContext]]})))
      (is (empty? @seen) "nothing settled, so nothing was reported")
      (v/assert kb (list cat Tom) 'UniverseContext)
      (is (= #{(list dog Muffet) (list cat Tom)} (set (added @seen)))
          "and the next settle reports the belief the half-applied batch left behind"))))

(tu/deftest-kb an-equality-merge-agrees-with-the-consequence-report
  ;; The contract is that a feed event and `edit-with-consequences` are the same answer,
  ;; and a merge is where that is worth pinning: the displaced spelling loses belief with
  ;; no relabel to record it, and the hand-off both read covers only what the *settle*
  ;; supersedes — an equality merge installs its supersession on the assert path.  So
  ;; neither reports it, `preview` does, and this test is what keeps the two that must
  ;; agree agreeing (and names the third).
  (tu/with-terms [dog Pref Dep NameContext]
    (v/assert kb (list dog Pref) NameContext)
    (let [[seen f] (recorder)]
      (v/watch kb f)
      (let [report (v/edit-with-consequences!
                    kb {:add [[(list 'sameAs Pref Dep) NameContext]]})]
        (is (= 1 (count @seen)))
        (is (= (set (map :sentence (:believed-added report))) (set (added @seen))))
        (is (= (set (map :sentence (:believed-removed report))) (set (removed @seen))))
        (is (empty? (removed @seen))
            "the displaced spelling is not in either — see preview_test for the one that
             does report it")))))

(tu/deftest-kb registering-a-listener-does-not-move-belief
  ;; A feed is a read.  If registering one moved an `in?`, the delivery point is wrong.
  (tu/with-terms [dog barks Muffet Rex]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list barks '?x)) 'UniverseContext)
    (v/assert kb (list dog Muffet) 'UniverseContext)
    (let [quiet (mapv #(v/ask? kb % 'UniverseContext)
                      [(list dog Muffet) (list barks Muffet)])]
      (v/watch kb (fn [_] nil))
      (v/assert kb (list dog Rex) 'UniverseContext)
      (is (= quiet (mapv #(v/ask? kb % 'UniverseContext)
                         [(list dog Rex) (list barks Rex)]))
          "the same scenario believes the same things with a listener attached"))))

;;; ── reentrancy, ordering, removal ──────────────────────────────────────

(tu/deftest-kb delivery-is-registration-order
  (tu/with-terms [dog Muffet]
    (let [order (atom [])]
      (doseq [k [:a :b :c]] (v/watch kb (fn [_] (swap! order conj k))))
      (v/assert kb (list dog Muffet) 'UniverseContext)
      (is (= [:a :b :c] @order)))))

(tu/deftest-kb a-listener-that-throws-loses-its-own-event-and-nothing-else
  (tu/with-terms [dog Muffet]
    (let [[seen f] (recorder)]
      (v/watch kb (fn [_] (throw (ex-info "a listener's bug" {}))))
      (v/watch kb f)
      (let [h (v/assert kb (list dog Muffet) 'UniverseContext)]
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
                      (v/assert kb (list pet Muffet) 'UniverseContext))))
      (v/assert kb (list dog Muffet) 'UniverseContext)
      (is (= [[(list dog Muffet)] [(list pet Muffet)]]
             (mapv #(mapv :sentence (:believed-added %)) @seen))
          "two rounds, the second being what the listener itself wrote")
      (is (v/ask? kb (list pet Muffet) 'UniverseContext)))))

(tu/deftest-kb a-listeners-own-writes-are-not-the-batchs-consequences
  ;; A listener's `assert` settles, and that settle would fold its region into whatever
  ;; sink the *original* caller bound — so an `edit-with-consequences` would report the
  ;; listener's assertions as consequences of the batch.  The sinks are closed for the
  ;; duration of delivery, which is what this pins.
  (tu/with-terms [dog Muffet sideEffect Yes]
    (let [wrote? (atom false)]
      (v/watch kb (fn [_] (when (compare-and-set! wrote? false true)
                            (v/assert kb (list sideEffect Yes) 'UniverseContext))))
      (let [report (v/edit-with-consequences!
                    kb {:add [[(list dog Muffet) 'UniverseContext]]})]
        (is (= [(list dog Muffet)] (mapv :sentence (:believed-added report)))
            "the report is about the batch, not about what a listener did in response")
        (is (v/ask? kb (list sideEffect Yes) 'UniverseContext)
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
                                            'UniverseContext))))
      (v/assert kb (list dog Muffet) 'UniverseContext)
      (v/unwatch kb @token)
      (is (= @#'feed/max-delivery-rounds @rounds)
          "it stops at the documented bound instead of spinning")
      (is (v/ask? kb (list dog Muffet) 'UniverseContext) "and the KB is usable after"))))

(tu/deftest-kb a-listener-may-unwatch-itself-mid-delivery
  ;; The registry is read once per event, so a listener editing it cannot make the
  ;; delivery loop skip or repeat one of its neighbours.
  (tu/with-terms [dog Muffet Rex]
    (let [[seen f] (recorder)
          also    (atom 0)
          token   (atom nil)]
      (reset! token (v/watch kb (fn [e] (f e) (v/unwatch kb @token))))
      (v/watch kb (fn [_] (swap! also inc)))
      (v/assert kb (list dog Muffet) 'UniverseContext)
      (is (= 1 (count @seen)))
      (is (= 1 @also) "the neighbour registered after it still ran for that event")
      (v/assert kb (list dog Rex) 'UniverseContext)
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
        (let [token (v/watch kb (list cat '?x) 'UniverseContext (fn [_] nil))]
          (v/assert kb (list dog Muffet) 'UniverseContext)
          (is (zero? @calls) "nothing the goal answers moved, so nothing was rendered")
          (v/assert kb (list cat Tom) 'UniverseContext)
          (is (= 1 @calls) "and a match renders exactly itself")
          (v/unwatch kb token))
        (reset! calls 0)
        (let [token (v/watch kb (fn [_] nil))]
          (v/assert kb (list dog (tu/tmp-ind "Plain")) 'UniverseContext)
          (is (pos? @calls) "a plain listener does want the whole diff")
          (v/unwatch kb token))))))

(tu/deftest-kb listeners-belong-to-one-kb
  ;; The renderer behind the seam is installed once per process (`observe`'s pattern), so
  ;; the thing that must be per-KB is the registry.  Two live KBs, and neither hears the
  ;; other.  The second one is on the **isolated** pair: a `tu/fresh` here would clear the
  ;; scratch space out from under the `:each` fixture holding the first.
  (tu/with-cleared-kb [other tu/isolated-fresh]
    (tu/with-terms [dog Muffet Rex]
      (let [[here hf]  (recorder)
            [there tf] (recorder)]
        (v/watch kb hf)
        (v/watch other tf)
        (v/assert kb (list dog Muffet) 'UniverseContext)
        (v/assert other (list dog Rex) 'UniverseContext)
        (is (= [(list dog Muffet)] (added @here)))
        (is (= [(list dog Rex)] (added @there)))
        (is (= [{:token 0}] (v/watchers kb)) "each registry counts its own tokens")
        (is (= [{:token 0}] (v/watchers other)))))))

(deftest a-fork-starts-with-no-listeners-and-tells-its-base-nothing
  ;; A fork is a new KB over the base's stores, so its registry is its own — and taking
  ;; one is a `recover` over the merged view, which is silent for the usual reason.
  ;;
  ;; Its own base rather than the fixture's, following `overlay_test`: a fork needs an
  ;; index written over the `KvBackend` seam, so forking whatever `VAELII_TEST_BACKEND`
  ;; chose would throw on the two columnar pairs — and the claim here is about the
  ;; registry, not about the store under it.
  (let [base (doto (v/open-kb {:backend :memory :space [::base] :recover? false})
               tu/clear-kb!)]
    (tu/with-terms [dog Muffet cat Tom]
      (v/assert base (list dog Muffet) 'UniverseContext)
      (let [[seen f] (recorder)]
        (v/watch base f)
        (let [forked (v/fork base {:backend :memory :space [::fork]})]
          (is (empty? (v/watchers forked)) "a fork inherits no listeners")
          (is (empty? @seen) "and taking one is a rebuild, so the base heard nothing")
          (v/assert forked (list cat Tom) 'UniverseContext)
          (is (empty? @seen) "nor does a write into the fork reach the base's listeners")
          (is (v/ask? forked (list cat Tom) 'UniverseContext) "the fork did take the write")
          (tu/clear-kb! forked))))
    (tu/clear-kb! base)))

(tu/deftest-kb unwatch-stops-a-listener-and-says-whether-there-was-one
  (tu/with-terms [dog Muffet Rex]
    (let [[seen f] (recorder)
          token    (v/watch kb f)]
      (v/assert kb (list dog Muffet) 'UniverseContext)
      (is (= 1 (count @seen)))
      (is (true? (v/unwatch kb token)))
      (is (false? (v/unwatch kb token)) "idempotent — a token is not reissued")
      (v/assert kb (list dog Rex) 'UniverseContext)
      (is (= 1 (count @seen)) "nothing arrived after the token was dropped"))))

(tu/deftest-kb watchers-lists-what-is-registered-without-the-functions
  (tu/with-terms [dog]
    (let [a (v/watch kb (fn [_] nil))
          b (v/watch kb (list dog '?x) 'UniverseContext (fn [_] nil))]
      (is (= [{:token a} {:token b :goal (list dog '?x) :context 'UniverseContext}]
             (v/watchers kb)))
      (v/unwatch kb a)
      (is (= [b] (mapv :token (v/watchers kb)))))))

;;; ── standing queries ───────────────────────────────────────────────────

(tu/deftest-kb a-standing-query-fires-only-on-what-answers-it
  (tu/with-terms [dog cat Muffet Tom]
    (let [[seen f] (recorder)]
      (v/watch kb (list dog '?x) 'UniverseContext f)
      (v/assert kb (list cat Tom) 'UniverseContext)
      (is (empty? @seen) "no call at all when nothing the goal answers moved")
      (v/assert kb (list dog Muffet) 'UniverseContext)
      (is (= [(list dog Muffet)] (added @seen)))
      (is (= [{'?x Muffet}] (mapv :bindings (:believed-added (first @seen))))
          "the entry says which solution moved"))))

(tu/deftest-kb a-standing-query-is-answered-by-a-subtype-and-a-sub-predicate
  ;; The same subsumption a rule antecedent gets — one cached closure lookup, not a
  ;; re-run of the goal.
  (tu/with-terms [animal_ dog_ Muffet parentOf fatherOf Tom Bob]
    (let [[types tf] (recorder)
          [rels rf]  (recorder)]
      (v/assert kb (list 'genl dog_ animal_) 'UniverseContext)
      (v/assert kb (list 'genl fatherOf parentOf) 'UniverseContext)
      (v/watch kb (list animal_ '?x) 'UniverseContext tf)
      (v/watch kb (list parentOf '?a '?b) 'UniverseContext rf)
      (v/assert kb (list dog_ Muffet) 'UniverseContext)
      (v/assert kb (list fatherOf Tom Bob) 'UniverseContext)
      (is (= [(list dog_ Muffet)] (added @types)) "a subtype answers a supertype goal")
      (is (= [{'?x Muffet}] (mapv :bindings (:believed-added (first @types)))))
      (is (= [(list fatherOf Tom Bob)] (added @rels))
          "and a sub-predicate answers a super-predicate goal")
      (is (= [{'?a Tom '?b Bob}] (mapv :bindings (:believed-added (first @rels))))))))

(tu/deftest-kb a-standing-query-sees-what-its-context-sees-and-no-more
  (tu/with-terms [dog Muffet Rex ChildContext ParentContext SiblingContext]
    (v/assert kb (list 'genlContext ChildContext ParentContext) 'UniverseContext)
    (let [[seen f] (recorder)]
      (v/watch kb (list dog '?x) ChildContext f)
      (v/assert kb (list dog Muffet) ParentContext)
      (is (= [(list dog Muffet)] (added @seen)) "up the genlContext cone, as any read is")
      (v/assert kb (list dog Rex) SiblingContext)
      (is (= [(list dog Muffet)] (added @seen))
          "a context the watch cannot see is not its business"))))

(tu/deftest-kb a-variable-context-watches-every-context-and-binds-the-one-that-answered
  (tu/with-terms [dog Muffet Rex StoryContext OtherContext]
    (let [[seen f] (recorder)]
      (v/watch kb (list dog '?x) '?ctx f)
      (v/assert kb (list dog Muffet) StoryContext)
      (v/assert kb (list dog Rex) OtherContext)
      (is (= [(list dog Muffet) (list dog Rex)] (added @seen)))
      (is (= [{'?x Muffet '?ctx StoryContext} {'?x Rex '?ctx OtherContext}]
             (mapv #(:bindings (first (:believed-added %))) @seen))))))

(tu/deftest-kb a-standing-query-reports-what-left-belief-too
  (tu/with-terms [dog barks Muffet]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list barks '?x)) 'UniverseContext)
    (v/assert kb (list dog Muffet) 'UniverseContext)
    (let [[seen f] (recorder)]
      (v/watch kb (list barks '?x) 'UniverseContext f)
      (v/assert kb (list 'not (list barks Muffet)) 'UniverseContext {:strength :monotonic})
      (is (= [(list barks Muffet)] (removed @seen)))
      (is (= [{'?x Muffet}] (mapv :bindings (:believed-removed (first @seen)))))
      (is (= :defeated (:reason (first (:believed-removed (first @seen)))))))))

(tu/deftest-kb a-negated-goal-watches-the-negative-side-and-not-the-positive
  ;; The `not` is part of the stored sentence, so it separates the two watches with no
  ;; special handling — and a positive watch must not fire for a believed negation.
  (tu/with-terms [dog Muffet]
    (let [[pos pf] (recorder)
          [neg nf] (recorder)]
      (v/watch kb (list dog '?x) 'UniverseContext pf)
      (v/watch kb (list 'not (list dog '?x)) 'UniverseContext nf)
      (v/assert kb (list 'not (list dog Muffet)) 'UniverseContext)
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
                  (list 'ist 'UniverseContext (list dog '?x))
                  (list 'lessThan '?a '?b)
                  'notASentence]]
      (let [e (try (v/watch kb goal 'UniverseContext (fn [_] nil))
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (instance? clojure.lang.ExceptionInfo e)
            (str "watch accepted a goal it cannot answer: " (pr-str goal)))
        (is (= :not-watchable (:type (ex-data e))))
        (is (string? (:reason (ex-data e))) "the refusal says why")))
    (is (empty? (v/watchers kb)) "and registered nothing")))

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
    (doseq [ctx [nil "UniverseContext" 7]]
      (let [e (try (v/watch kb (list dog '?x) ctx (fn [_] nil))
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (instance? clojure.lang.ExceptionInfo e) (pr-str ctx))
        (is (= :not-watchable (:type (ex-data e))))))
    (is (empty? (v/watchers kb)))))
