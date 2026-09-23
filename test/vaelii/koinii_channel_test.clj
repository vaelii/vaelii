;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.koinii-channel-test
  "Koinii's coordination library: join / subscribe / reply over the change
  feed, with the KB as the medium.  One `Medium` protocol, two shapes — an in-process KB
  (`local`, the fast tests here) and a daemon connection (`wire`, the one `^:slow` test
  against a real daemon, where the properties that NEED a process boundary live:
  decoupled-in-time catch-up, the off-thread poll loop, and the writer never blocked by a
  slow subscriber).

  The reply loop's required claims: a reply is a meta-sentex in the replier's own
  context (D1), idempotent by sentence identity (so an at-least-once feed is safe), and
  torn down with its target (D7, no dangling edges).  Belief is never special-cased — every
  move is an ordinary assert / retract, which the full suite staying green is the check on."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [taoensso.trove :as trove]
            [vaelii.client :as vc]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.host.serve :as serve]
            [vaelii.impl.sentex :as sx]
            [vaelii.koinii.channel :as ch]
            [vaelii.koinii.identity :as id]
            [vaelii.koinii.speech-acts :as sa]
            [vaelii.koinii.types :as koinii-types]
            [vaelii.test-util :as tu])
  (:import [org.eclipse.jetty.server Server]))

(defn- channel-kb
  "A fresh CxCore KB with the koinii speech-act vocabulary loaded — the deployment's
  substrate: the reply verbs' `target_following_predicate` marks must be in force for a
  reply to cascade."
  []
  (tu/load-dumped! (tu/fresh) :koinii/speech-acts
                   #(doto % (core-context/load-into) (sa/load-speech-acts))))

(use-fixtures :each (tu/neutral-fresh channel-kb))

(defn- join!
  "Join `agent` to a `local` medium over `kb` on channel `CxDeploy`."
  [kb agent]
  (ch/join (ch/local kb) 'CxDeploy agent))

;; ---- join / assert: the per-agent context and write boundary (D8) --------

(tu/deftest-kb join-lifts-the-agents-own-context-under-the-channel
  (let [atlas (join! kb 'AgentAtlas)]
    (is (= 'CxAtlas (:context atlas)) "the agent's own context is a function of its id")
    (is (= 'CxDeploy (:channel atlas)))
    (is (v/sees? kb 'CxDeploy 'CxAtlas) "lifted under the channel, so the channel sees it")
    (is (v/sees? kb 'CxAtlas 'CxSpeechActs) "and rooted so it speaks the reply vocabulary")
    (testing "assert writes into the agent's OWN context, creator stamped"
      (let [h (ch/assert atlas (list 'usesDatabase 'ProdCluster 'PostgreSQL14))]
        (is (= 'CxAtlas (:context (v/sentex kb h))))
        (is (= 'AgentAtlas (:creator (v/provenance kb h))))))
    (testing "re-joining is idempotent topology, no second edge"
      (let [again (join! kb 'AgentAtlas)]
        (is (= (:context atlas) (:context again)))))))

(tu/deftest-kb an-agent-cannot-assert-under-another-agents-name
  ;; The creator is the write boundary's other half: the context is fixed by identity, and
  ;; so is the stamp.  A caller's `:creator` neither wins (Atlas signing Boreas's name) nor
  ;; is dropped in silence (a stamp that looks like it took) — it is refused.
  (let [atlas (join! kb 'AgentAtlas)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cannot assert as"
                          (ch/assert atlas '(usesDatabase ProdCluster PostgreSQL14)
                                     {:creator 'AgentBoreas})))
    (let [e (try (ch/assert atlas '(usesDatabase ProdCluster PostgreSQL14)
                            {:creator 'AgentBoreas})
                 nil
                 (catch clojure.lang.ExceptionInfo e e))]
      (is (= :koinii/creator-mismatch (:type (ex-data e))))
      (is (= 'AgentBoreas (:creator (ex-data e)))))
    (testing "nothing was written under either name"
      (is (nil? (v/handle-of kb '(usesDatabase ProdCluster PostgreSQL14) 'CxAtlas)))
      (is (nil? (v/handle-of kb '(usesDatabase ProdCluster PostgreSQL14) 'CxBoreas))))
    (testing "the agent's own id is redundant, not a conflict, and other opts pass through"
      (let [h (ch/assert atlas '(usesDatabase ProdCluster PostgreSQL14)
                         {:creator 'AgentAtlas :strength :monotonic})]
        (is (= 'AgentAtlas (:creator (v/provenance kb h))))
        (is (= 'CxAtlas (:context (v/sentex kb h))))
        (is (= :monotonic (:strength (v/sentex kb h))) "the other opt reached the store")))))

;; ---- reply: a meta-sentex in the replier's own context (D1) --------------

(tu/deftest-kb answer-is-a-meta-sentex-recoverable-as-knowledge
  (let [atlas (join! kb 'AgentAtlas)
        boreas (join! kb 'AgentBoreas)
        qh (ch/pose-query atlas 'WhichDbProdClusterUses)
        ah (ch/answer boreas 'PostgreSQL14 qh)]
    (testing "the query node is Atlas's, in Atlas's own context"
      (is (= 'CxAtlas (:context (v/sentex kb qh)))))
    (testing "the answer is Boreas's meta-sentex ON the query, in Boreas's own context"
      (is (= 'CxBoreas (:context (v/sentex kb ah))))
      (is (= (list 'answers 'AgentBoreas 'PostgreSQL14 (sx/sentex-handle qh))
             (:sentence (v/sentex kb ah)))))
    (testing "recover 'what answered the query, and who said it' — off the ANSWER"
      (let [as (ch/answers-to atlas qh)
            a  (first as)]
        (is (= 1 (count as)))
        (is (= 'AgentBoreas (ch/speaker-of a)) "the answerer, from the reply's own sentence")
        (is (= 'PostgreSQL14 (ch/answer-content a)))
        (is (= 'CxBoreas (:context a)) "and where from")))))

(tu/deftest-kb a-reply-is-idempotent-by-sentence-identity
  ;; Why an at-least-once feed is safe to act on: replaying a reply changes nothing.
  (let [atlas (join! kb 'AgentAtlas)
        boreas (join! kb 'AgentBoreas)
        qh (ch/pose-query atlas 'WhichDb)
        a1 (ch/answer boreas 'PostgreSQL14 qh)
        a2 (ch/answer boreas 'PostgreSQL14 qh)]
    (is (= a1 a2) "the same answer asserted twice is one sentex, one handle")
    (is (= 1 (count (ch/answers-to atlas qh))) "no duplicate in the KB")))

(tu/deftest-kb endorsement-survives-first-writer-wins
  (let [atlas (join! kb 'AgentAtlas)
        boreas (join! kb 'AgentBoreas)
        ciel (join! kb 'AgentCiel)
        ph (ch/assert atlas (list 'usesDatabase 'ProdCluster 'PostgreSQL14))
        e1 (ch/endorse boreas ph)
        e2 (ch/endorse ciel ph)]
    (is (not= e1 e2) "two endorsers are two distinct meta-sentexes, two creators")
    (is (= #{'AgentBoreas 'AgentCiel}
           (set (map ch/speaker-of (ch/endorsements-of atlas ph))))
        "both recover as data — two distinct sources for the claim")))

(tu/deftest-kb dispute-rebuts-and-surfaces-in-contradictions
  (let [atlas (join! kb 'AgentAtlas)
        boreas (join! kb 'AgentBoreas)
        ph (ch/assert atlas (list 'usesDatabase 'ProdCluster 'PostgreSQL14))
        dh (ch/dispute boreas ph)]
    (testing "the rebuttal makes the pair a contradiction, both sides believed"
      (is (= 1 (count (v/contradictions kb)))))
    (testing "and the disputes edge is Boreas's meta on the claim"
      (is (= 'CxBoreas (:context (v/sentex kb dh))))
      (is (= (list 'disputes 'AgentBoreas (sx/sentex-handle ph))
             (:sentence (v/sentex kb dh)))))))

(tu/deftest-kb vote-is-a-ballot-meta-sentex-idempotent-by-identity
  (let [atlas  (join! kb 'AgentAtlas)
        boreas (join! kb 'AgentBoreas)
        ph (ch/assert atlas (list 'usesDatabase 'ProdCluster 'PostgreSQL14))
        v1 (ch/vote boreas :against ph)
        v2 (ch/vote boreas :against ph)]
    (is (= (list 'votesAgainst 'AgentBoreas (sx/sentex-handle ph)) (:sentence (v/sentex kb v1)))
        "the ballot names the claim by handle")
    (is (= 'CxBoreas (:context (v/sentex kb v1))) "in the voter's own context")
    (is (= v1 v2) "one ballot per agent per stance — idempotent by sentence identity")
    (is (= (list 'votesFor 'AgentAtlas (sx/sentex-handle ph))
           (:sentence (v/sentex kb (ch/vote atlas :for ph))))
        "and the :for stance is the other predicate")))

(tu/deftest-kb justify-offers-a-ground-as-a-meta-sentex
  (let [atlas (join! kb 'AgentAtlas)
        boreas (join! kb 'AgentBoreas)
        ph (ch/assert atlas (list 'usesDatabase 'ProdCluster 'PostgreSQL14))
        jh (ch/justify boreas 'MigratedInQ2 ph)]
    (is (= (list 'justifies 'AgentBoreas 'MigratedInQ2 (sx/sentex-handle ph))
           (:sentence (v/sentex kb jh))))
    (is (= 'CxBoreas (:context (v/sentex kb jh))) "in the justifier's own context")))

(tu/deftest-kb retracting-the-target-tears-down-the-reply-no-dangling-edge
  ;; D7: the reply lives ON the target, so the target's teardown takes it.
  (let [atlas (join! kb 'AgentAtlas)
        boreas (join! kb 'AgentBoreas)
        qh (ch/pose-query atlas 'WhichDb)
        ah (ch/answer boreas 'PostgreSQL14 qh)
        eh (ch/endorse boreas qh)]
    (is (some? (v/sentex kb ah)))
    (is (some? (v/sentex kb eh)))
    (v/retract! kb qh)
    (is (nil? (v/sentex kb qh)) "the target query is gone")
    (is (nil? (v/sentex kb ah)) "its answer cascaded")
    (is (nil? (v/sentex kb eh)) "and its endorsement — no dangling edges")))

;; ---- reply-many: validate before commit (item 4) -------------------------

(tu/deftest-kb a-multi-claim-reply-validates-before-it-commits
  (let [atlas (join! kb 'AgentAtlas)
        boreas (join! kb 'AgentBoreas)
        qh (ch/pose-query atlas 'WhichStack)
        claim  (list 'usesDatabase 'ProdCluster 'PostgreSQL14)
        answer (list 'answers 'AgentBoreas 'PostgreSQL14 (sx/sentex-handle qh))]
    (testing "an admissible batch commits both linked claims in one settle"
      (let [r (ch/reply-many boreas [claim answer])]
        (is (= 2 (count (:added r))) "both linked claims landed in the one edit")
        (is (seq (v/sentexes-matching kb claim 'CxBoreas)))
        (is (seq (v/sentexes-matching kb answer 'CxBoreas)))))
    (testing "an inadmissible batch is refused whole — no HALF-reply lands"
      (let [good  (list 'usesCache 'ProdCluster 'Redis)
            e (is (thrown? clojure.lang.ExceptionInfo
                           (ch/reply-many boreas [good :not-a-sentence])))]
        (is (= :koinii/reply-inadmissible (:type (ex-data e))))
        (is (seq (:problems (ex-data e))) "carrying the check-edit problems")
        (is (empty? (v/sentexes-matching kb good 'CxBoreas))
            "and the admissible half never landed — edit! never ran")))))

(tu/deftest-kb a-multi-claim-reply-cannot-sign-anothers-name
  ;; The batch entry point is the SAME entry point `assert` is, or the batch is a way round it: a vote
  ;; is counted off the sentence (`adjudication/tally` reads the voter there), so a batch
  ;; of ballots naming other agents would be one principal casting a house of votes.
  (let [atlas  (join! kb 'AgentAtlas)
        boreas (join! kb 'AgentBoreas)
        claim  (ch/assert atlas '(usesDb prodCluster postgres))
        ballot (fn [a] (list 'votesFor a (v/sentex-handle claim)))
        e (is (thrown? clojure.lang.ExceptionInfo
                       (ch/reply-many boreas [(ballot 'AgentAtlas) (ballot 'AgentBoreas)])))]
    (is (= :koinii/speaker-mismatch (:type (ex-data e))))
    (is (= 'AgentAtlas (:named (ex-data e))))
    (testing "and the batch is refused BEFORE the first write, so no ballot stands"
      (is (empty? (v/sentexes-matching kb (list 'votesFor '?a (v/sentex-handle claim)) '?ctx))
          "not even the one naming Boreas himself, which the batch would have written first"))
    (testing "a batch of the agent's own acts still commits"
      (let [r (ch/reply-many boreas [(ballot 'AgentBoreas)
                                     (list 'usesCache 'prodCluster 'redis)])]
        (is (= 2 (count (:added r))))))))

(tu/deftest-kb a-multi-claim-reply-cannot-write-the-admin-registry
  ;; The batch builds its own edit! payload, so the registry line has to be drawn on it
  ;; too — a handle carrying CxRegistry is the whole exploit, and the governed may never
  ;; write the authority that governs them.
  (let [boreas (join! kb 'AgentBoreas)
        rogue  (assoc boreas :context 'CxRegistry)
        e (is (thrown? clojure.lang.ExceptionInfo
                       (ch/reply-many rogue ['(trustLevel AgentBoreas 99)])))]
    (is (= :koinii/registry-forbidden (:type (ex-data e))))
    (is (empty? (v/sentexes-matching kb '(trustLevel ?a ?v) 'CxRegistry))
        "no trust value was written into the registry")))

;; ---- subscribe: the async reply trigger, in-process ----------------------

(tu/deftest-kb subscribe-fires-on-a-matching-write-and-stops-when-dropped
  ;; The single-process path: a plain `core/watch` listener, callback on the writer's
  ;; thread.  Watch the CHANNEL and a write in an agent's own context is delivered up the
  ;; genlCx ancestor set.
  (let [atlas (join! kb 'AgentAtlas)
        boreas (join! kb 'AgentBoreas)
        seen (atom [])
        sub  (ch/subscribe boreas (list 'queries '?a '?q) 'CxDeploy
                           (fn [e] (swap! seen conj e)))]
    (ch/pose-query atlas 'WhichDb)
    (is (= 1 (count @seen)) "the subscriber saw Atlas's query, posed in CxAtlas")
    (is (= [(list 'queries 'AgentAtlas 'WhichDb)]
           (map :sentence (mapcat :believed-added @seen))))
    (testing "dropping the subscription stops delivery, and is idempotent"
      (ch/unsubscribe sub)
      (ch/pose-query atlas 'WhichCache)
      (is (= 1 (count @seen)) "no further events after unsubscribe")
      (ch/unsubscribe sub)                                  ; a second drop must not throw
      (ch/pose-query atlas 'WhichMore)
      (is (= 1 (count @seen)) "still stopped after a double unsubscribe"))))

(tu/deftest-kb local-subscribe-with-a-nil-goal-sees-every-change
  ;; the goal-less branch: a plain listener, not a standing query
  (let [atlas (join! kb 'AgentAtlas)
        seen  (atom 0)
        sub   (ch/subscribe atlas nil nil (fn [_] (swap! seen inc)))]
    (ch/assert atlas (list 'usesDatabase 'ProdCluster 'PostgreSQL14))
    (is (pos? @seen) "a nil-goal listener fires on any belief change")
    (ch/unsubscribe sub)))

(tu/deftest-kb a-goal-core-watch-refuses-is-refused-here-too
  (let [boreas (join! kb 'AgentBoreas)]
    (is (thrown? clojure.lang.ExceptionInfo
                 (ch/subscribe boreas (list 'agg/count (list 'queries '?a '?q)) 'CxDeploy
                               (fn [_])))
        "an aggregate goal is not watchable — the same check as in process")))

;; ---- the wire shape: the properties that need a process boundary ----------

(tu/deftest-kb ^:slow the-wire-shape-decoupled-in-time-off-thread-and-nonblocking
  ;; One daemon, several agents on their own connections.  Everything a single process
  ;; cannot demonstrate: agents decoupled in time, the poll loop off the agent's thread,
  ;; and a slow subscriber that does not stall the writer.
  (let [^Server server (serve/start kb {:port 0 :token nil})
        port (serve/port server)
        conn (fn [] (vc/client "localhost" port {:token nil :timeout-ms 3000}))]
    (try
      (testing "decoupled in time: A asks and disconnects; B connects LATER, reads the
                query off the durable KB, answers; A reconnects and reads its answer"
        (let [qh (let [a-conn (conn)                         ; A connects
                       atlas  (ch/join (ch/wire a-conn) 'CxDeploy 'AgentAtlas)
                       qh     (ch/pose-query atlas 'WhichDbProdClusterUses)]
                   qh)]                                       ; A's conn goes out of scope — "disconnected"
          (let [b-conn (conn)                                ; B connects later
                boreas (ch/join (ch/wire b-conn) 'CxDeploy 'AgentBoreas)
                open   (ch/open-queries boreas)]             ; catch-up is a KB read, not a cursor replay
            (is (some #(= (list 'queries 'AgentAtlas 'WhichDbProdClusterUses) (:sentence %)) open)
                "B sees A's query though A is gone — the KB is the medium")
            (let [ah (ch/answer boreas 'PostgreSQL14 qh)]
              (is (= 'AgentBoreas (:creator (v/provenance kb ah)))
                  "the daemon stamped the creator from the wire opts, not from the connection")))
          (let [a2     (conn)                                ; A reconnects
                atlas2 (ch/join (ch/wire a2) 'CxDeploy 'AgentAtlas)
                as     (ch/answers-to atlas2 qh)]
            (is (= 1 (count as)))
            (is (= 'AgentBoreas (ch/speaker-of (first as))) "who answered, from the reply itself")
            (is (= 'PostgreSQL14 (ch/answer-content (first as))))
            (testing "a reply is recoverable and reversible: retract the query, answer goes"
              (vc/retract! a2 qh)
              (is (empty? (ch/answers-to atlas2 qh)) "no dangling edge across the wire")))))

      (testing "the poll loop runs OFF the agent's thread, and a matching write is delivered"
        (let [b-conn (conn)
              boreas (ch/join (ch/wire b-conn) 'CxDeploy 'AgentBoreas)
              a-conn (conn)
              atlas  (ch/join (ch/wire a-conn) 'CxDeploy 'AgentAtlas)
              got    (promise)
              sub    (ch/subscribe boreas (list 'queries '?a '?q) 'CxDeploy
                                   (fn [e] (deliver got e)) {:wait-ms 8000})]
          (try
            (ch/pose-query atlas 'WhichCacheProdClusterUses)
            (let [e (deref got 8000 :timed-out)]
              (is (not= :timed-out e) "the off-thread poll delivered the event")
              (is (= [(list 'queries 'AgentAtlas 'WhichCacheProdClusterUses)]
                     (map :sentence (:believed-added e)))))
            (finally (ch/unsubscribe sub)))))

      (testing "a slow subscriber does not block the writer — the wire feed was the right
                primitive (an in-process callback would run on the writer's thread)"
        (let [b-conn (conn)
              boreas (ch/join (ch/wire b-conn) 'CxDeploy 'AgentBoreas)
              a-conn (conn)
              atlas  (ch/join (ch/wire a-conn) 'CxDeploy 'AgentAtlas)
              slow-started (promise)
              sub (ch/subscribe boreas (list 'queries '?a '?q) 'CxDeploy
                                (fn [_] (deliver slow-started true) (Thread/sleep 4000))
                                {:wait-ms 8000})]
          (try
            (ch/pose-query atlas 'FirstQuery)                ; triggers the slow callback
            (is (true? (deref slow-started 8000 false)) "the slow callback is running")
            ;; while B's callback sleeps 4s on its OWN thread, A's next write must return fast
            (let [began (System/currentTimeMillis)
                  _     (ch/pose-query atlas 'SecondQuery)
                  took  (- (System/currentTimeMillis) began)]
              ;; a real block would take ~4s (the callback's sleep); 3s cleanly distinguishes
              ;; that from a fast write while tolerating GC / load jitter on the threshold
              (is (< took 3000)
                  (str "A's write took " took "ms — a slow subscriber must not stall the writer")))
            (finally (ch/unsubscribe sub)))))

      (testing "a callback that throws loses its own event and nothing else — the wire
                subscription survives and keeps delivering (the engine's listener contract)"
        (let [b-conn (conn)
              boreas (ch/join (ch/wire b-conn) 'CxDeploy 'AgentBoreas)
              a-conn (conn)
              atlas  (ch/join (ch/wire a-conn) 'CxDeploy 'AgentAtlas)
              n      (atom 0)
              errs   (atom [])
              second-seen (promise)
              sub (ch/subscribe boreas (list 'queries '?a '?q) 'CxDeploy
                                (fn [_] (if (= 1 (swap! n inc))
                                          (throw (ex-info "boom on the first event" {}))
                                          (deliver second-seen true)))
                                {:wait-ms 8000 :on-error (fn [e] (swap! errs conj e))})]
          (try
            (ch/pose-query atlas 'ThrowsHere)                ; callback throws
            (ch/pose-query atlas 'DeliveredAnyway)           ; must still arrive
            (is (true? (deref second-seen 8000 false))
                "the second event was delivered though the first threw")
            (is (seq @errs) ":on-error was told about the throw")
            (finally (ch/unsubscribe sub)))))

      (testing "at-least-once is safe: the same reply asserted twice over the wire is one
                sentex"
        (let [a-conn (conn)
              atlas  (ch/join (ch/wire a-conn) 'CxDeploy 'AgentAtlas)
              b-conn (conn)
              boreas (ch/join (ch/wire b-conn) 'CxDeploy 'AgentBoreas)
              qh (ch/pose-query atlas 'WhichQueue)
              a1 (ch/answer boreas 'Kafka qh)
              a2 (ch/answer boreas 'Kafka qh)]
          (is (= a1 a2) "idempotent by sentence identity across the wire")
          (is (= 1 (count (ch/answers-to atlas qh))))))
      (finally (.stop server)))))

;; ---- a local medium has no cursor feed: catch-up is wire-only -------------

(tu/deftest-kb a-local-medium-has-no-cursor-feed
  (testing "the ring / cursor / lag live only on the wire feed, so a local medium refuses
            the raw feed primitives rather than pretend to resume"
    (let [m (ch/local kb)
          refusal (fn [f] (try (f) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))]
      (is (= :koinii/no-wire-feed (:type (refusal #(koinii-types/-feed-open m nil 'CxDeploy))))
          "opening a feed on a medium that issues no cursor")
      (is (= :koinii/no-wire-feed (:type (refusal #(koinii-types/-feed-poll m nil nil nil))))
          "and resuming from one it never issued"))))

;; ---- the two entry points that nil-punned: a bad handle, and a bad stance -------

(tu/deftest-kb dispute-refuses-a-handle-that-names-no-record
  ;; `dispute` reads the target's sentence to build the rebuttal, so a handle naming
  ;; nothing would assert the literal `(not nil)` and a `disputes` edge on nothing — a
  ;; challenge to a claim that does not exist, stored as though it were one.
  (let [boreas (join! kb 'AgentBoreas)
        absent (+ 1000000 (count (v/handles kb)))
        e (is (thrown? clojure.lang.ExceptionInfo (ch/dispute boreas absent)))]
    (is (= :koinii/no-such-handle (:type (ex-data e))))
    (is (= absent (:handle (ex-data e))))
    (is (empty? (v/sentexes-matching kb '(not ?s) 'CxBoreas))
        "and the rebuttal was never written")))

(tu/deftest-kb vote-refuses-a-stance-that-is-neither-by-name
  ;; The ballot predicate is chosen from the stance, so an unrecognized one has no
  ;; ballot to cast.  A bare `case` fell out as an `IllegalArgumentException` naming
  ;; nothing a caller could act on; the refusal is typed and lists the two that exist.
  (let [atlas (join! kb 'AgentAtlas)
        ph    (ch/assert atlas (list 'usesDatabase 'ProdCluster 'PostgreSQL14))
        e     (is (thrown? clojure.lang.ExceptionInfo (ch/vote atlas :abstain ph)))]
    (is (= :koinii/no-such-stance (:type (ex-data e))))
    (is (= :abstain (:stance (ex-data e))))
    (is (= [:for :against] (:known (ex-data e))) "the refusal names the legal directions")))

;; ---- the wire poll loop's two extension points are never silent ---------------------
;;
;; A scripted daemon: `wire-subscribe` reaches the far end only through `client/watch`,
;; `client/poll` and `client/unwatch`, so redefining those three says exactly what the
;; daemon does and when — no Jetty, no ring, no timing.

(defn- collecting-log-fn
  "Install a `*log-fn*` collecting `[level id]` at the ROOT, not as a thread-local: the
  poll loop runs on its own daemon thread, which inherits no dynamic binding.  Returns
  `[collected restore!]`."
  []
  (let [collected (atom [])
        root      (.getRawRoot #'trove/*log-fn*)]
    (alter-var-root #'trove/*log-fn*
                    (constantly (fn [_ns _coords level id _payload]
                                  (swap! collected conj [level id]))))
    [collected #(alter-var-root #'trove/*log-fn* (constantly root))]))

(defn- stopped?
  "Wait up to 3s for `sub` to read stopped, and answer whether it does."
  [sub]
  (loop [n 300]
    (cond (false? @(:running sub)) true
          (zero? n)                false
          :else                    (do (Thread/sleep 10) (recur (dec n))))))

(defn- scripted-wire
  "A `wire` medium whose daemon answers from `poll-fn` — `(fn [n] …)` on the 1-based poll
  count, returning a reply or throwing."
  [poll-fn]
  (let [polls (atom 0)]
    [(ch/wire ::scripted)
     (fn [_conn _token _cursor _opts] (poll-fn (swap! polls inc)))]))

(deftest a-wire-poll-that-fails-ends-the-subscription-and-reports-it
  ;; The failure a subscriber cannot detect: the loop exits on a transport error and the
  ;; subscription still reads live, so nobody resubscribes and no event ever arrives
  ;; again.  Now the exit is recorded — `:running` false — and, with no `:on-error`, said
  ;; out loud at `:error` rather than dropped.
  (let [[medium poll] (scripted-wire (fn [_] (throw (ex-info "the proxy hung up" {}))))
        [logged restore!] (collecting-log-fn)]
    (try
      (with-redefs [vc/watch   (fn ([_] {:token "T" :cursor 0})
                                 ([_ _ _] {:token "T" :cursor 0}))
                    vc/unwatch (fn [_ _] true)
                    vc/poll    poll]
        (let [sub (koinii-types/-subscribe medium nil 'CxDeploy (fn [_]) nil)]
          (is (stopped? sub) "the dead subscription reads stopped, not live")
          (is (some #{[:error ::ch/subscription-failed]} @logged)
              "and the failure was logged at :error rather than swallowed")))
      (finally (restore!)))))

(deftest a-caller-supplied-on-error-replaces-the-default-line
  (let [[medium poll] (scripted-wire (fn [_] (throw (ex-info "the proxy hung up" {}))))
        [logged restore!] (collecting-log-fn)
        seen (atom [])]
    (try
      (with-redefs [vc/watch   (fn ([_] {:token "T" :cursor 0})
                                 ([_ _ _] {:token "T" :cursor 0}))
                    vc/unwatch (fn [_ _] true)
                    vc/poll    poll]
        (let [sub (koinii-types/-subscribe medium nil 'CxDeploy (fn [_])
                                           {:on-error #(swap! seen conj %)})]
          (is (stopped? sub))
          (is (= 1 (count @seen)) ":on-error was told")
          (is (= "the proxy hung up" (ex-message (first @seen))))
          (is (not-any? #{[:error ::ch/subscription-failed]} @logged)
              "and the default line stood aside for it")))
      (finally (restore!)))))

(deftest a-lagged-wire-reply-is-not-dropped-in-silence
  ;; `:lagged` is the one field a feed reader must not ignore (docs/feed.md): non-zero,
  ;; the ring dropped events and the reader owes the KB a resync.  Unset, `:on-lagged`
  ;; made that number disappear; it now reaches the log at `:warn`.
  (let [[medium poll] (scripted-wire
                       (fn [n] (if (= 1 n)
                                 {:events [] :cursor 1 :lagged 3}
                                 (throw (ex-info "gone" {:type :unknown-subscription})))))
        [logged restore!] (collecting-log-fn)]
    (try
      (with-redefs [vc/watch   (fn ([_] {:token "T" :cursor 0})
                                 ([_ _ _] {:token "T" :cursor 0}))
                    vc/unwatch (fn [_ _] true)
                    vc/poll    poll]
        (let [sub (koinii-types/-subscribe medium nil 'CxDeploy (fn [_]) nil)]
          (is (stopped? sub) "the reaped subscription reads stopped too, and quietly")
          (is (some #{[:warn ::ch/subscription-lagged]} @logged)
              "the dropped count was reported")
          (is (not-any? #{[:error ::ch/subscription-failed]} @logged)
              "a reaped subscription is not an error — it is the normal end")))
      (finally (restore!)))))

(deftest a-caller-supplied-on-lagged-replaces-the-default-line
  (let [[medium poll] (scripted-wire
                       (fn [n] (if (= 1 n)
                                 {:events [] :cursor 1 :lagged 3}
                                 (throw (ex-info "gone" {:type :unknown-subscription})))))
        [logged restore!] (collecting-log-fn)
        drops (atom [])]
    (try
      (with-redefs [vc/watch   (fn ([_] {:token "T" :cursor 0})
                                 ([_ _ _] {:token "T" :cursor 0}))
                    vc/unwatch (fn [_ _] true)
                    vc/poll    poll]
        (let [sub (koinii-types/-subscribe medium nil 'CxDeploy (fn [_])
                                           {:on-lagged #(swap! drops conj %)})]
          (is (stopped? sub))
          (is (= [3] @drops) ":on-lagged was told the count")
          (is (not-any? #{[:warn ::ch/subscription-lagged]} @logged))))
      (finally (restore!)))))

;; ---- the registry write boundary (docs/koinii.md) ------------------------

(tu/deftest-kb the-admin-registry-is-never-writable-through-a-cooperative-entry-point
  ;; `CxRegistry` is admin-only: the governed may not write the authority that governs
  ;; them.  The channel and speech-act entry points carry no authenticated principal, so they
  ;; enforce that one boundary at the entry point — `check-write-boundary!` (the proof-tier
  ;; own-context rule) is not what these cooperative entry points impose, only the registry line.
  (testing "joining AS the registry (AgentRegistry -> CxRegistry) is refused"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"registry-forbidden"
                          (join! kb 'AgentRegistry))))
  (testing "a speech act aimed straight at CxRegistry is refused"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"registry-forbidden"
                          (sa/assert-claim kb 'AgentAtlas '(trustLevel AgentAtlas 1) 'CxRegistry)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"registry-forbidden"
                          (sa/pose-query kb 'AgentAtlas 'WhichTrust 'CxRegistry))))
  (testing "an ordinary agent still joins and writes its own context"
    (let [atlas (join! kb 'AgentAtlas)]
      (is (= 'CxAtlas (:context atlas)))
      (is (some? (ch/assert atlas '(usesDb prod postgres))))))
  (testing "and a cooperative cross-context write (first-writer-wins) is still allowed"
    (is (some? (sa/assert-claim kb 'AgentCiel '(usesDb prod postgres) 'CxAtlas))
        "writing another agent's context is a cooperative move, not the registry breach")))

(tu/deftest-kb an-agent-cannot-sign-anothers-name-in-a-speech-act
  ;; `speaker-of` reads the speaker off the reply's own sentence; the entry point stamps the
  ;; creator off the handle.  For the two to agree — the invariant every reader relies on
  ;; — a handle may assert a speech act only when it names itself as the speaker.
  (let [atlas (join! kb 'AgentAtlas)
        _     (join! kb 'AgentBoreas)
        claim (ch/assert atlas '(usesDb prodCluster postgres))]
    (testing "endorsing or voting under another agent's name is refused"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cannot speak as"
                            (ch/assert atlas (list 'endorses 'AgentBoreas (v/sentex-handle claim)))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cannot speak as"
                            (ch/assert atlas (list 'votesFor 'AgentBoreas (v/sentex-handle claim))))))
    (testing "the agent's own speech acts still go through"
      (is (some? (ch/endorse atlas claim)))
      (is (some? (ch/assert atlas (list 'endorses 'AgentAtlas (v/sentex-handle claim))))
          "naming itself is fine, redundant with the constructor"))
    (testing "an ordinary (non-speech-act) claim is unaffected"
      (is (some? (ch/assert atlas '(usesCache prodCluster redis)))))))

;; ---- join: the parent must be a channel (D8) -----------------------------

(tu/deftest-kb a-join-refuses-a-parent-that-is-not-a-coordination-channel
  ;; A join widens what the PARENT sees: `(genlCx parent CxMallory)` makes every ancestor set read
  ;; of the parent return Mallory's claims, and with `belief/believe-own` in force they
  ;; become what the parent's own agent is proved to believe.  So the parent is held to the
  ;; standard `assert` holds a destination to — a context the agent may legitimately be
  ;; grafted under, never the registry and never another principal's own.
  (let [medium (ch/local kb)]
    (join! kb 'AgentAtlas)
    (testing "another agent's own context, which would make Mallory's claims Atlas's"
      (let [e (is (thrown? clojure.lang.ExceptionInfo
                           (ch/join medium 'CxAtlas 'AgentMallory)))]
        (is (= :koinii/not-a-channel (:type (ex-data e))))
        (is (= 'CxAtlas (:parent (ex-data e))))
        (is (not (v/sees? kb 'CxAtlas 'CxMallory)) "and no edge landed")))
    (testing "the admin registry, which governs the agents rather than hosting them"
      (let [e (is (thrown? clojure.lang.ExceptionInfo
                           (ch/join medium 'CxRegistry 'AgentMallory)))]
        (is (= :koinii/not-a-channel (:type (ex-data e))))
        (is (not (v/sees? kb 'CxRegistry 'CxMallory)))))
    (testing "the agent's own context, which a join lifts rather than lifts under"
      (let [e (is (thrown? clojure.lang.ExceptionInfo
                           (ch/join medium 'CxMallory 'AgentMallory)))]
        (is (= :koinii/not-a-channel (:type (ex-data e))))))
    (testing "and the channel itself still takes every agent that asks"
      (let [ciel (ch/join medium 'CxDeploy 'AgentCiel)]
        (is (= 'CxCiel (:context ciel)))
        (is (v/sees? kb 'CxDeploy 'CxCiel))
        (is (some? (ch/assert ciel '(usesDb prodCluster postgres))))))))

(tu/deftest-kb a-join-refuses-an-agent-context-placed-by-any-route
  ;; The mark is written at the ONE chokepoint every placement goes through
  ;; (`id/place-agent-context`), so an agent placed by a sibling API is recognized here
  ;; exactly as one placed by `join` is — the entry point reads a fact somebody wrote, not a
  ;; shape it infers from the lattice.
  (let [medium (ch/local kb)]
    (id/agent-context kb 'CxDeploy 'AgentAtlas)      ; the bare placement, rooted CxCore
    (sa/speaker-context kb 'CxDeploy 'AgentBoreas)   ; the speech-act placement
    (doseq [victim '[CxAtlas CxBoreas]]
      (testing (str "grafting under " victim)
        (let [e (is (thrown? clojure.lang.ExceptionInfo
                             (ch/join medium victim 'AgentMallory)))]
          (is (= :koinii/not-a-channel (:type (ex-data e))))
          (is (= victim (:parent (ex-data e))))
          (is (not (v/sees? kb victim 'CxMallory)) "and no edge landed"))))
    (testing "the refusal names the agent the mark says the context belongs to"
      (let [e (try (ch/join medium 'CxAtlas 'AgentMallory)
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (= #{'AgentAtlas} (set (:owners (ex-data e)))))))))

(tu/deftest-kb a-join-admits-a-channel-however-the-lattice-around-it-grew
  ;; Admission is a positive stored fact about the parent, so it cannot move with what
  ;; else has landed.  The two shapes a structural test gets wrong: a channel rooted at
  ;; the vocabulary the join itself speaks, and a channel rolled up under a wider context
  ;; AFTER agents are already on it.
  (let [medium (ch/local kb)]
    (testing "a `:speaks CxCore` join, on a channel already rooted at CxCore and rolled up"
      (v/assert kb '(genlCx CxDeploy CxCore) 'CxUniverse {:strength :monotonic})
      (v/assert kb '(genlCx CxOrg CxDeploy) 'CxUniverse {:strength :monotonic})
      (let [atlas (ch/join medium 'CxDeploy 'AgentAtlas {:speaks 'CxCore})]
        (is (= 'CxAtlas (:context atlas)))
        (is (v/sees? kb 'CxAtlas 'CxCore) "rooted where the override said")))
    (testing "and ordinary edges landing later change nothing for the next agent"
      (v/assert kb '(genlCx CxDeploy CxSpeechActs) 'CxUniverse {:strength :monotonic})
      (v/assert kb '(genlCx CxUpper CxDeploy) 'CxUniverse {:strength :monotonic})
      (is (= 'CxBoreas (:context (ch/join medium 'CxDeploy 'AgentBoreas)))
          "the same channel admits the same way whenever it is asked")
      (is (= 'CxAtlas (:context (ch/join medium 'CxDeploy 'AgentAtlas)))
          "and re-joining an agent already on it stays a no-op"))))

(tu/deftest-kb a-registry-entry-named-after-the-channel-does-not-brick-it
  ;; Membership is not placement: an id in the registry says an agent EXISTS, never that
  ;; some context is its own.  `AgentDeploy` maps to `CxDeploy` by the naming convention,
  ;; and the channel of that name is still a channel until a placement says otherwise.
  (id/load-registry kb)
  (id/register-agent kb (id/admin-principal) 'AgentDeploy "the deploy bot" 1)
  (let [atlas (ch/join (ch/local kb) 'CxDeploy 'AgentAtlas)]
    (is (= 'CxAtlas (:context atlas)))
    (is (v/sees? kb 'CxDeploy 'CxAtlas))))
