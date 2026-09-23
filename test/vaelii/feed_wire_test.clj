;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.feed-wire-test
  "The change feed across the process boundary: a subscription the daemon holds, read
  forward with a cursor (`vaelii.host.subscribe`, docs/feed.md).

  `feed_test` holds what an event *means*; nothing here re-tests that.  What a wire
  feed can get wrong is a different list, and it is these five:

  * **The two targets are one answer.**  A batch driven through `POST /op` produces, on
    the wire, exactly the event an in-process listener over the same KB receives — after
    a full EDN round-trip, since a caller with no vaelii classes on its classpath is who
    this is for.  That equality is the contract.
  * **Falling behind is said out loud.**  The ring is bounded, so a subscriber that
    stops reading loses events; one that loses them and is not told is strictly worse
    off than one that polls, because it believes it is current.  `:lagged` carries the
    count, and a token naming no subscription is refused rather than answered empty.
  * **A refusal is the same refusal.**  A goal `core/watch` will not answer is refused
    on the wire under the same `:type`, since it is the same check.
  * **The wait is outside the monitor.**  A long poll parks; parked inside the daemon's
    one lock it would stall every writer, which is the opposite of the feature.
  * **What a stranger can allocate is bounded.**  A ceiling on subscriptions, a ceiling
    on each one's ring, and an idle one reaped.

  Driven against `serve/app` directly — the handler is pure `request -> response`, so
  no socket — except the one full loop that proves the client's own wrappers, timeout
  and all.  Every handler here is built with an explicit `{:token nil}`, so a
  `VAELII_API_TOKEN` in the shell running the suite changes nothing."
  (:require [clojure.edn :as edn]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.client :as vc]
            [vaelii.core :as v]
            [vaelii.host.serve :as serve]
            [vaelii.host.subscribe :as sub]
            [vaelii.test-util :as tu])
  (:import [java.io ByteArrayInputStream]
           [org.eclipse.jetty.server Server]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- open-app
  "`serve/app` with no bearer token — the loopback default, and the posture every test
  here needs: one that 401s first exercises none of this."
  [kb]
  (serve/app kb {:token nil}))

(defn- post
  "One `{:op :args}` request against `handler`, parsed, with the status assoc'd."
  [handler op args]
  (let [body (pr-str {:op op :args (vec args)})
        resp (handler {:request-method :post :uri "/op"
                       :headers {"content-type" "application/edn"}
                       :body (ByteArrayInputStream. (.getBytes ^String body "UTF-8"))})]
    (assoc (edn/read-string (:body resp)) :status (:status resp))))

(defn- ok!
  "The `:result` of a request that must have succeeded."
  [reply]
  (is (:ok reply) (str "refused: " (pr-str (select-keys reply [:type :error]))))
  (:result reply))

(defn- over-the-wire
  "A reply's result as a caller with none of this repo's classes reads it: printed and
  read back as plain EDN.  Every equality below runs through this rather than over the
  in-process value, since the round trip is exactly where a record, a lazy seq or a
  list-turned-vector would show up."
  [x]
  (edn/read-string (pr-str x)))

(defn- recorder
  "An atom collecting in-process events, and the listener that fills it."
  []
  (let [seen (atom [])]
    [seen (fn [e] (swap! seen conj e))]))

;;; ── one op stream, two targets ─────────────────────────────────────────

(tu/deftest-kb the-same-batch-is-the-same-event-in-process-and-on-the-wire
  ;; The contract, and the reason the wire feed is a transport rather than a second
  ;; feature: one settle files one region, `dispatch-feed!` renders it once, and both
  ;; listeners are handed that one answer.  What this can still catch is the transport —
  ;; a sentence arriving as a vector, a record reaching a client that cannot read it, a
  ;; lazy seq realized after the reply closed.
  (tu/with-terms [dog animal barks Muffet CxWireFeed]
    (let [handler  (open-app kb)
          [seen f] (recorder)]
      (v/assert kb (list 'genl dog animal) CxWireFeed)
      (v/watch kb f)
      (let [{:keys [token cursor]} (ok! (post handler :watch []))]
        (testing "a fresh subscription starts at nothing"
          (is (zero? cursor))
          (is (= sub/max-events (:max-events (ok! (post handler :watch []))))
              "and says how much slack it has before it drops anything"))
        ;; every write goes through the daemon, so the events being compared are the
        ;; daemon's own writes rather than a listener watching something else's
        (ok! (post handler :assert-rule [[(list dog '?x)] (list barks '?x)
                                         CxWireFeed {:direction :forward}]))
        (ok! (post handler :assert [(list dog Muffet) CxWireFeed]))
        ;; and a defeat, so both halves of an event cross the wire: known-true content
        ;; takes the default conclusion out of belief with its record left standing
        (ok! (post handler :assert [(list 'not (list barks Muffet)) CxWireFeed
                                    {:strength :monotonic}]))
        (let [{:keys [events lagged]} (ok! (post handler :poll [token 0]))]
          (is (zero? lagged))
          (is (= (count @seen) (count events))
              "one settle is one event on both sides")
          (is (= @seen (over-the-wire events))
              "and the events are equal through a full EDN round trip")
          (testing "the derived conclusion arrives with the rule that derived it, and
                    its defeat arrives as a removal"
            (let [derived (first (filter #(= (list barks Muffet) (:sentence %))
                                         (mapcat :believed-added events)))]
              (is (some? derived))
              (is (false? (:premise? derived)))
              (is (= (list dog Muffet) (first (:antecedents (:justification derived))))))
            (is (some #(= (list barks Muffet) (:sentence %))
                      (mapcat :believed-removed events)))))))))

(tu/deftest-kb the-cursor-advances-and-never-repeats-an-event
  (tu/with-terms [dog Muffet Rex CxWireFeed]
    (let [handler (open-app kb)
          {:keys [token]} (ok! (post handler :watch []))]
      (ok! (post handler :assert [(list dog Muffet) CxWireFeed]))
      (let [first-poll (ok! (post handler :poll [token 0]))]
        (is (= 1 (count (:events first-poll))))
        (is (= 1 (:cursor first-poll)))
        (testing "polling again from the cursor it handed back is silence, not a repeat"
          (let [again (ok! (post handler :poll [token (:cursor first-poll)]))]
            (is (empty? (:events again)))
            (is (= 1 (:cursor again)))))
        (ok! (post handler :assert [(list dog Rex) CxWireFeed]))
        (testing "and the next write picks up exactly where it left off"
          (let [next-poll (ok! (post handler :poll [token (:cursor first-poll)]))]
            (is (= [(list dog Rex)]
                   (map :sentence (mapcat :believed-added (:events next-poll)))))
            (is (= 2 (:cursor next-poll)))))))))

(tu/deftest-kb a-standing-query-filters-the-wire-feed-and-carries-its-bindings
  ;; The wire subscription is `core/watch`'s standing query with a cursor bolted on, so
  ;; what has to hold is that the filter survives the trip: an unrelated write is
  ;; silence, and a matching one arrives with the solution that matched.
  (tu/with-terms [dog animal cat Muffet Tom CxWireFeed]
    (let [handler (open-app kb)]
      (v/assert kb (list 'genl dog animal) CxWireFeed)
      (let [{:keys [token]} (ok! (post handler :watch [(list animal '?x) CxWireFeed]))]
        (ok! (post handler :assert [(list cat Tom) CxWireFeed]))
        (is (empty? (:events (ok! (post handler :poll [token 0]))))
            "a write the goal does not answer is silence, not an empty event")
        (ok! (post handler :assert [(list dog Muffet) CxWireFeed]))
        (let [{:keys [events]} (ok! (post handler :poll [token 0]))
              entry (first (mapcat :believed-added events))]
          (is (= 1 (count events)))
          (is (= (list dog Muffet) (:sentence entry))
              "subsumption through the genl closure, exactly as in process")
          (is (= {'?x Muffet} (over-the-wire (:bindings entry)))
              "and the binding that answered rides the wire as a symbol map"))))))

;;; ── falling behind, and being told ─────────────────────────────────────

(tu/deftest-kb a-subscriber-the-ring-outran-is-told-how-much-it-missed
  ;; The decision the feature stands on.  A bounded ring is what keeps a subscriber that
  ;; stops reading from growing the daemon's heap; a bounded ring that drops silently is
  ;; worse than no feed at all, because the caller believes it is current and has no way
  ;; to find out otherwise.
  (tu/with-terms [dog CxWireFeed]
    (let [handler (open-app kb)]
      (with-redefs [sub/max-events 3]
        (let [{:keys [token max-events]} (ok! (post handler :watch []))
              names (mapv #(symbol (str "Lagger" %)) (range 8))]
          (is (= 3 max-events) "the caller is told the depth it has to keep up with")
          (doseq [n names]
            (ok! (post handler :assert [(list dog n) CxWireFeed])))
          (let [{:keys [events cursor lagged]} (ok! (post handler :poll [token 0]))]
            (is (= 8 cursor) "the cursor counts every event, dropped ones included")
            (is (= 3 (count events)) "the ring held its bound and no more")
            (is (= 5 lagged) "and the five it dropped are reported, not swallowed")
            (is (= (mapv #(list dog %) (subvec names 5))
                   (mapv :sentence (mapcat :believed-added events)))
                "what survived is the newest, so a caller that resyncs is closest to now"))
          (testing "and a poll that lost nothing still carries the field, at zero, so a
                    client cannot read this feed without seeing it"
            (let [r (ok! (post handler :poll [token 8]))]
              (is (contains? r :lagged))
              (is (zero? (:lagged r))))))))))

(tu/deftest-kb an-abandoned-subscription-holds-a-bounded-ring-and-then-is-reaped
  (tu/with-terms [dog CxWireFeed]
    (let [handler (open-app kb)]
      (with-redefs [sub/max-events 4]
        (let [{:keys [token]} (ok! (post handler :watch []))]
          (dotimes [i 40]
            (ok! (post handler :assert [(list dog (symbol (str "Gone" i)))
                                        CxWireFeed])))
          (testing "forty events into a subscriber that never reads, the daemon holds four"
            (let [[held] (ok! (post handler :watchers []))]
              (is (= 4 (:pending held)))
              (is (= 40 (:delivered held))
                  "and says it has been handed forty, so the gap is visible from here
                   too rather than only from the reader's :lagged")))
          (testing "and one nobody has polled inside the idle window is reaped, listener
                    and all — a client that went away without saying so must not hold a
                    slot against a live one"
            (with-redefs [sub/idle-ms -1]
              ;; any call is a reap, and `:watchers` is the cheapest one to make
              (is (empty? (ok! (post handler :watchers [])))))
            (is (empty? (v/watchers kb))
                "the engine-side listener went with it, not just the registry entry")
            (is (= :unknown-subscription (:type (post handler :poll [token 0])))
                "and the token afterwards is refused, never answered empty")))))))

;;; ── the refusals ───────────────────────────────────────────────────────

(tu/deftest-kb a-goal-refused-in-process-is-refused-on-the-wire-the-same-way
  (tu/with-terms [dog cat Muffet CxWireFeed]
    (let [handler (open-app kb)]
      (doseq [[label goal] [["a conjunction"  [(list dog '?x) (list cat '?y)]]
                            ["an aggregate"   (list 'agg/count (list dog '?x))]
                            ["unknown"        (list 'unknown (list dog '?x))]
                            ["thereExists"    (list 'thereExists '?x (list dog '?x))]
                            ["an evaluable"   (list 'lessThan '?x 3)]
                            ["an ist"         (list 'ist CxWireFeed (list dog '?x))]]]
        (testing label
          (let [in-process (is (thrown? clojure.lang.ExceptionInfo
                                        (v/watch kb goal CxWireFeed (fn [_]))))
                remote     (post handler :watch [goal CxWireFeed])]
            (is (= :not-watchable (:type (ex-data in-process))) label)
            (is (= :not-watchable (:type remote)) label)
            (is (= 400 (:status remote)) label))))
      (testing "a goal with no context to scope it is refused on the wire too"
        (let [r (post handler :watch [(list dog '?x) nil])]
          (is (= :not-watchable (:type r)))
          (is (= 400 (:status r)))))
      (testing "and so is the mirror image: a context with no goal to scope"
        ;; The whole-feed subscription is not scoped — `core/watch`'s no-goal arity takes
        ;; no context at all — so a context arriving alone would register an unscoped
        ;; listener while the registry stored the context and `:watchers` reported it
        ;; back, the daemon naming a scope it is not applying.
        (let [r (post handler :watch [nil CxWireFeed])]
          (is (= :not-watchable (:type r)))
          (is (= 400 (:status r)))
          (is (empty? (ok! (post handler :watchers [])))
              "nothing was registered under the context it refused")))
      (testing "and nothing a refused watch touched is left registered"
        (is (empty? (v/watchers kb)))
        (is (empty? (ok! (post handler :watchers []))))))))

(tu/deftest-kb the-feed-refusals-are-a-status-and-a-type-like-every-other
  (tu/with-terms [dog Muffet CxWireFeed]
    (let [handler (open-app kb)
          {:keys [token]} (ok! (post handler :watch []))]
      (ok! (post handler :assert [(list dog Muffet) CxWireFeed]))
      (doseq [[label reply ty]
              [["a token naming no subscription"  (post handler :poll [4200 0])
                :unknown-subscription]
               ["a cursor that is not a number"   (post handler :poll [token :soon])
                :bad-cursor]
               ["a cursor ahead of the feed"      (post handler :poll [token 99])
                :bad-cursor]
               ["an option poll does not read"    (post handler :poll [token 0 {:wait-msec 5}])
                :unknown-option]
               ["a :wait-ms that is not a wait"   (post handler :poll [token 0 {:wait-ms "soon"}])
                :unknown-option]
               ["the wrong number of args"        (post handler :poll [token])
                :bad-args]
               ["a watch shape nothing takes"     (post handler :watch [(list dog '?x)])
                :bad-args]]]
        (testing label
          (is (false? (:ok reply)) label)
          (is (= 400 (:status reply)) label)
          (is (= ty (:type reply)) label)))
      (testing "and a poll that was legal all along still works, so the refusals above
                are the arguments' doing rather than the subscription's"
        (is (= 1 (count (:events (ok! (post handler :poll [token 0]))))))))))

(tu/deftest-kb the-daemon-refuses-to-hold-more-subscriptions-than-its-ceiling
  ;; Nothing authenticates `POST /op` on the loopback default, so a subscription is heap
  ;; a stranger can allocate.  The ceiling is what bounds that, and it refuses the new
  ;; one rather than evicting an old one: a subscription dropped without being told is
  ;; the silent gap this whole feature exists to refuse.
  (let [handler (open-app kb)]
    (with-redefs [sub/max-subscriptions 3]
      (dotimes [_ 3] (ok! (post handler :watch [])))
      (let [r (post handler :watch [])]
        (is (= 400 (:status r)))
        (is (= :too-many-subscriptions (:type r)))
        (is (= 3 (count (ok! (post handler :watchers []))))
            "and the three that were there are untouched"))
      (testing "dropping one makes room again"
        (ok! (post handler :unwatch [0]))
        (is (:ok (post handler :watch [])))))))

(tu/deftest-kb unwatch-is-idempotent-and-takes-the-engine-side-listener-with-it
  (let [handler (open-app kb)
        {:keys [token]} (ok! (post handler :watch []))]
    (is (= 1 (count (v/watchers kb))) "the subscription registered an ordinary listener")
    (is (true? (ok! (post handler :unwatch [token]))))
    (is (empty? (v/watchers kb)) "and dropping the subscription unregistered it")
    (is (false? (ok! (post handler :unwatch [token])))
        "a token already dropped removes nothing and says so")
    (testing "a token is never reissued, so a stale one cannot land on the next
              subscription"
      (let [next-token (:token (ok! (post handler :watch [])))]
        (is (not= token next-token))
        (is (false? (ok! (post handler :unwatch [token]))))
        (is (= 1 (count (ok! (post handler :watchers []))))
            "the live one is still live")))))

;;; ── the wait, and the monitor ──────────────────────────────────────────

(tu/deftest-kb a-write-completes-while-a-long-poll-is-parked
  ;; The constraint the whole design turns on.  `serve` serializes ops behind one
  ;; monitor, so a poll that waited inside it would block every writer for the length of
  ;; its wait — a feature about liveness turned into a global stall.  Two things are
  ;; asserted, and they are different claims: the write *returns* while the poll is still
  ;; parked, and the poll then wakes with what the write moved rather than timing out.
  (tu/with-terms [dog Muffet CxWireFeed]
    (let [handler  (open-app kb)
          {:keys [token]} (ok! (post handler :watch []))
          polled   (promise)
          parked   (promise)
          poller   (Thread. #(do (deliver parked true)
                                 (deliver polled
                                          (post handler :poll [token 0 {:wait-ms 10000}]))))]
      (.start poller)
      @parked
      ;; the poll is parked (or about to be); the write must not wait behind it
      (let [began (System/currentTimeMillis)
            _     (ok! (post handler :assert [(list dog Muffet) CxWireFeed]))
            took  (- (System/currentTimeMillis) began)]
        (is (< took 5000)
            (str "the write took " took "ms — a parked poll is holding the daemon's "
                 "monitor, which is the one thing it must not do"))
        (let [r (deref polled 15000 :timed-out)]
          (is (not= :timed-out r) "the poll never came back")
          (is (= [(list dog Muffet)]
                 (map :sentence (mapcat :believed-added (:events (ok! r)))))
              "and it woke with the event rather than sitting out its full wait")
          (is (< (- (System/currentTimeMillis) began) 9000)
              "waking on the notify, not on the timeout")))
      (.join poller 15000))))

(tu/deftest-kb a-long-poll-with-nothing-to-report-answers-empty-rather-than-hanging
  (let [handler (open-app kb)
        {:keys [token]} (ok! (post handler :watch []))
        began   (System/currentTimeMillis)
        r       (ok! (post handler :poll [token 0 {:wait-ms 150}]))
        took    (- (System/currentTimeMillis) began)]
    (is (empty? (:events r)))
    (is (zero? (:lagged r)))
    (is (>= took 100) "it did wait")
    (is (< took 10000) "and it stopped waiting")
    (testing "the wait is capped whatever the caller asks for, so one caller cannot
              hold a server thread for as long as it likes"
      (is (= 30000 sub/max-wait-ms))
      (with-redefs [sub/max-wait-ms 50]
        (let [t0 (System/currentTimeMillis)]
          (ok! (post handler :poll [token 0 {:wait-ms 60000}]))
          (is (< (- (System/currentTimeMillis) t0) 5000)))))))

(tu/deftest-kb dropping-a-subscription-wakes-the-poll-parked-on-it
  ;; A parked reader whose feed is dropped must learn that rather than sitting out its
  ;; wait and then being told nothing happened — which is the silent-stop failure again,
  ;; wearing a timeout.
  (let [handler (open-app kb)
        {:keys [token]} (ok! (post handler :watch []))
        answered (promise)
        parked   (promise)
        poller   (Thread. #(do (deliver parked true)
                               (deliver answered
                                        (post handler :poll [token 0 {:wait-ms 10000}]))))]
    (.start poller)
    @parked
    (ok! (post handler :unwatch [token]))
    (let [r (deref answered 15000 :timed-out)]
      (is (not= :timed-out r))
      (is (= :unknown-subscription (:type r))))
    (.join poller 15000)))

;;; ── what the wire must not become a way to observe ─────────────────────

(tu/deftest-kb preview-recover-and-reindex-deliver-nothing-over-the-wire-either
  ;; The in-process feed is off for all three (docs/feed.md), and the wire subscription
  ;; is an ordinary listener, so it inherits that — this is the test that says the
  ;; inheritance is real rather than assumed.  A preview through a feed would send a
  ;; change and then its exact reverse; a recover would hand a reconnecting client the
  ;; whole KB as newly believed.
  (tu/with-terms [dog Muffet Rex CxWireFeed]
    (let [handler (open-app kb)]
      (v/assert kb (list dog Muffet) CxWireFeed)
      (let [{:keys [token]} (ok! (post handler :watch []))]
        (ok! (post handler :preview [{:add [[(list dog Rex) CxWireFeed]]}]))
        (is (empty? (:events (ok! (post handler :poll [token 0]))))
            "a preview stores, reads and takes it all back — a feed through one reports
             a change and then its reverse")
        (v/recover kb)
        (v/reindex kb)
        (let [r (ok! (post handler :poll [token 0]))]
          (is (empty? (:events r)))
          (is (zero? (:lagged r))
              "and nothing was dropped either — there was nothing to drop"))))))

(tu/deftest-kb two-handlers-over-one-kb-are-two-daemons
  ;; The registry is per handler, beside the monitor, and this is what that means: a
  ;; token means nothing to the daemon that did not issue it.  Answered rather than
  ;; refused, it would hand one caller another's feed.
  (tu/with-terms [dog Muffet CxWireFeed]
    (let [a (open-app kb)
          b (open-app kb)
          {:keys [token]} (ok! (post a :watch []))]
      (ok! (post a :assert [(list dog Muffet) CxWireFeed]))
      (is (= 1 (count (:events (ok! (post a :poll [token 0]))))))
      (is (= :unknown-subscription (:type (post b :poll [token 0])))
          "b never issued this token, so it refuses it rather than guessing")
      (is (empty? (ok! (post b :watchers []))))
      (ok! (post a :unwatch [token])))))

;;; ── the roster, and the client ─────────────────────────────────────────

(clojure.test/deftest the-feed-ops-are-reachable-and-are-not-a-model-tool
  (testing "the four are op keywords the daemon answers"
    (is (= [:poll :unwatch :watch :watchers] (sort (keys serve/feed-ops))))
    (is (every? (set serve/op-names) (keys serve/feed-ops))
        "and an unknown-op refusal lists them, so a caller discovering the surface
         sees one roster rather than the larger half of two"))
  (testing "they are not in the vaelii.core allowlist, which is what keeps them out of
            the model's tool set and out of the local access facade"
    (is (empty? (filter serve/ops (keys serve/feed-ops))))
    (require 'vaelii.host.llm.tools)
    (let [read-ops ((resolve 'vaelii.host.llm.tools/read-ops))]
      (is (empty? (filter (set (keys serve/feed-ops)) read-ops))
          "a subscription is heap, and heap is not a thing a model allocates"))))

(tu/deftest-kb ^:slow the-client-drives-the-feed-over-a-socket
  ;; The one full loop: `vaelii.client`'s three wrappers against a real daemon, which is
  ;; what proves the long poll's read timeout is extended to cover the wait — a claim the
  ;; in-process handler cannot make, because there is no socket to time out.
  (tu/with-terms [dog animal Muffet Rex CxWireFeed]
    (let [^Server server (serve/start kb {:port 0 :token nil})]
      (try
        (let [conn (vc/client "localhost" (serve/port server) {:token nil :timeout-ms 2000})
              {:keys [token cursor max-events]} (vc/watch conn)]
          (is (nat-int? token))
          (is (zero? cursor))
          (is (= sub/max-events max-events))
          (testing "a write and the poll that reports it"
            (vc/assert conn (list dog Muffet) CxWireFeed)
            (let [{:keys [events cursor lagged]} (vc/poll conn token 0)]
              (is (zero? lagged))
              (is (= 1 cursor))
              (is (= [(list dog Muffet)]
                     (map :sentence (mapcat :believed-added events))))))
          (testing "a long poll outlives the conn's own 2s timeout, because the client
                    extends the read timeout by the wait it asked for"
            (let [began (System/currentTimeMillis)
                  r     (vc/poll conn token 1 {:wait-ms 4000})]
              (is (>= (- (System/currentTimeMillis) began) 3500)
                  "it waited the whole time rather than failing at the conn's timeout")
              (is (empty? (:events r)))))
          (testing "a standing query over the socket, with its bindings"
            (vc/assert conn (list 'genl dog animal) CxWireFeed)
            (let [{q :token} (vc/watch conn (list animal '?x) CxWireFeed)]
              (vc/assert conn (list dog Rex) CxWireFeed)
              (let [{:keys [events]} (vc/poll conn q 0)]
                (is (= [{'?x Rex}] (map :bindings (mapcat :believed-added events)))))
              (testing "watchers names both, and unwatch takes them down"
                (is (= 2 (count (vc/watchers conn))))
                (is (true? (vc/unwatch conn token)))
                (is (true? (vc/unwatch conn q)))
                (is (empty? (vc/watchers conn)))
                (is (empty? (v/watchers kb))))))
          (testing "and a remote feed refusal is an ex-info like any other"
            (let [e (is (thrown? clojure.lang.ExceptionInfo (vc/poll conn token 0)))]
              (is (= :unknown-subscription (:type (ex-data e)))))))
        (finally (.stop server))))))

(tu/deftest-kb the-listing-in-feed-md-is-the-listing-the-daemon-answers
  ;; docs/feed.md prints a five-line transcript of the wire feed, and the last line is
  ;; what `watchers` answers *after* the `unwatch` above it.  It listed the token that
  ;; line had just dropped, with a `:pending` the reap could not produce and neither of
  ;; the two fields a standing query's row carries.
  (tu/with-terms [dog animal Muffet Rex Fido CxWell]
    (let [^Server server (serve/start kb {:port 0 :token nil})]
      (try
        (let [conn (vc/client "localhost" (serve/port server) {:token nil})]
          (v/assert kb (list 'genlCx CxWell 'CxUniverse) 'CxUniverse)
          (vc/assert conn (list 'genl dog animal) CxWell)
          (let [{plain :token}    (vc/watch conn)
                {standing :token} (vc/watch conn (list animal '?x) CxWell)]
            (doseq [t [Muffet Rex Fido]] (vc/assert conn (list dog t) CxWell))
            (let [{:keys [events cursor lagged]} (vc/poll conn plain 0 {:wait-ms 20000})]
              (is (= 3 (count events)))
              (is (= 3 cursor))
              (is (zero? lagged)))
            (is (true? (vc/unwatch conn plain)))
            (is (= [{:token standing :delivered 3 :pending 3
                     :goal (list animal '?x) :context CxWell}]
                   (vc/watchers conn))
                "the dropped token is gone, and :pending is what the ring holds")))
        (finally (.stop server))))))

;; ---- what a parked poll costs the daemon --------------------------------
;;
;; Moving the wait outside `serve`'s monitor keeps a parked poll from blocking the
;; *writer*.  It does nothing about the *threads*: a parked poll holds one HTTP worker
;; for the length of its wait, and a daemon with more of them parked than its pool has
;; threads answers nothing at all until one times out.  Two separate ceilings, and the
;; second one had no bound.

(tu/deftest-kb a-poll-that-would-wait-is-refused-when-the-daemon-is-out-of-permits
  (let [handler (open-app kb)
        token   (:token (ok! (post handler :watch [])))]
    (with-redefs [sub/max-parked 0]
      (testing "asking to wait is refused, and says which ceiling it hit"
        (let [r (post handler :poll [token 0 {:wait-ms 5000}])]
          (is (= 400 (:status r)))
          (is (= :too-many-waiters (:type r)))))
      (testing "a poll that does not ask to wait is never refused, whatever is parked"
        (let [r (ok! (post handler :poll [token 0]))]
          (is (= [] (:events r)))
          (is (= 0 (:lagged r)))))
      (testing "and neither is one whose events are already there, since it will not block"
        (v/assert kb (list 'genlCx 'CxTmpWait 'CxUniverse) 'CxUniverse)
        (let [r (ok! (post handler :poll [token 0 {:wait-ms 5000}]))]
          (is (seq (:events r)) "the wait was never entered, so no permit was wanted"))))))

(tu/deftest-kb a-permit-is-held-for-the-wait-and-handed-back
  (let [reg   (sub/registry)
        token (:token (sub/watch reg kb nil nil))]
    (with-redefs [sub/max-parked 1]
      (let [parked (future (try (sub/poll reg kb token 0 {:wait-ms 20000})
                                (catch Exception e (:type (ex-data e)))))]
        ;; wait for it to actually be parked rather than sleeping a guessed interval
        (loop [n 0]
          (when (and (< n 400) (not= 1 (:parked @reg))) (Thread/sleep 5) (recur (inc n))))
        (is (= 1 (:parked @reg)) "the permit is held for the duration of the wait")
        (testing "and the next poll asking to wait is refused rather than queued"
          (let [e (is (thrown? clojure.lang.ExceptionInfo
                               (sub/poll reg kb token 0 {:wait-ms 20000})))]
            (is (= :too-many-waiters (:type (ex-data e))))))
        (testing "while a timer poll goes through beside it"
          (is (= [] (:events (sub/poll reg kb token 0)))))
        (sub/unwatch reg kb token)
        (is (= :unknown-subscription @parked)
            "dropping the subscription wakes the parked poll rather than leaving it to time out")
        (is (zero? (:parked @reg)) "and the permit came back")))))

(tu/deftest-kb an-interrupted-park-answers-and-puts-the-interrupt-back
  ;; A parked poll holds a server thread, so it is precisely what a container shutting
  ;; down interrupts.  `.wait` clears the flag on its way out, so letting the
  ;; `InterruptedException` travel would answer a 500 — a reader's feed reads as having
  ;; failed when it has not — and would lose the interrupt for whoever owns the thread.
  ;; It ends the park the way the deadline does: answer what is there, flag restored.
  (let [reg    (sub/registry)
        token  (:token (sub/watch reg kb nil nil))
        result (promise)
        flag   (promise)
        body   (fn []
                 (deliver result (try {:ok (sub/poll reg kb token 0 {:wait-ms 20000})}
                                      (catch Throwable e {:threw e})))
                 (deliver flag (.isInterrupted (Thread/currentThread))))
        t      (Thread. ^Runnable body "vaelii-test-parked-poll")]
    (.start t)
    ;; wait for it to actually be parked rather than sleeping a guessed interval
    (loop [n 0]
      (when (and (< n 400) (not= 1 (:parked @reg))) (Thread/sleep 5) (recur (inc n))))
    (is (= 1 (:parked @reg)) "it is parked")
    (.interrupt t)
    (let [r (deref result 5000 ::timeout)]
      (is (not= ::timeout r) "the interrupt ends the park rather than being waited out")
      (is (nil? (:threw r)) (str "and answers rather than throwing: " (pr-str (:threw r))))
      (is (= [] (:events (:ok r)))
          "with the events it has, which is what a wait that ran out answers too")
      (is (true? (deref flag 5000 ::timeout))
          "and the interrupt is back for whoever owns the thread"))
    (is (zero? (:parked @reg)) "and the permit came back")
    (sub/unwatch reg kb token)))

(tu/deftest-kb a-wait-value-no-long-holds-is-a-refusal-and-not-a-fault
  ;; Every one of these is a well-formed request with a bad option *value*.  Answered
  ;; 500 they would read as a backend fault at every reverse proxy between the caller and
  ;; the daemon; `##NaN` was worse than that, coercing to 0 so the long poll silently
  ;; became one that never waits.
  (let [handler (open-app kb)
        token   (:token (ok! (post handler :watch [])))]
    (doseq [[what v] [["larger than a long" 1e300]
                      ["an infinity"        ##Inf]
                      ["not a number at all" ##NaN]
                      ["a fraction of a millisecond" 1.5]
                      ["negative"           -1]]]
      (testing what
        (let [r (post handler :poll [token 0 {:wait-ms v}])]
          (is (= 400 (:status r)) (str ":wait-ms " what " must not read as a server fault"))
          (is (= :unknown-option (:type r))))))))

(tu/deftest-kb a-subscription-dropped-mid-registration-leaves-no-listener-and-no-zombie
  ;; `watch` files its registry entry before registering the listener, so an event fired
  ;; between the two has somewhere to go.  The window that opens is the other way round:
  ;; if the entry goes while `core/watch` is in flight, an unguarded `assoc-in` at the
  ;; end **recreates** it with nothing in it but `:watch-token` — and `reap` runs at the
  ;; head of every feed op, so the next one on this daemon reads `(- at nil)` and throws.
  (let [reg  (sub/registry)
        real v/watch
        before (count (v/watchers kb))]
    (with-redefs [v/watch (fn [& args]
                            (swap! reg update :subs dissoc (first (keys (:subs @reg))))
                            (apply real args))]
      (let [e (is (thrown? clojure.lang.ExceptionInfo (sub/watch reg kb nil nil)))]
        (is (= :unknown-subscription (:type (ex-data e))))))
    (is (empty? (:subs @reg)) "no entry was resurrected")
    (is (= before (count (v/watchers kb)))
        "and the listener came straight back off the KB rather than leaking onto it")
    (testing "so the feed still answers, which a zombie entry would have stopped"
      (is (= [] (sub/subscriptions reg kb)))
      (is (:token (sub/watch reg kb nil nil))))))
