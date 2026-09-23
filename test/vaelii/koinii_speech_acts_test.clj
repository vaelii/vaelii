;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.koinii-speech-acts-test
  "Koinii speech-acts: the moves agents make, as sentexes in the KB — a
  query is a node, a reply is a META-SENTEX on it, and the response predicates carry
  `target_following_predicate` so retracting a target cascades to its replies.  One
  deftest per 'How to verify' bullet: a round-trip conversation recoverable as data,
  endorsement surviving first-writer-wins, a dispute surfacing in `contradictions`, and
  — the required check — the cascade, modeled on `target_following_meta_test`."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.impl.sentex :as sx]
            [vaelii.koinii.speech-acts :as sa]
            [vaelii.test-util :as tu]))

(defn- speech-acts-kb
  "A fresh CxCore KB with the koinii speech-act vocabulary loaded."
  []
  (tu/load-dumped! (tu/fresh) :koinii/speech-acts
                   #(doto % (core-context/load-into) (sa/load-speech-acts))))

(use-fixtures :each (tu/neutral-fresh speech-acts-kb))

;; ---- the context loads ----------------------------------------------------

(tu/deftest-kb speech-acts-context-loads-under-core
  (is (v/sees? kb 'CxSpeechActs 'CxCore) "CxSpeechActs wires itself under CxCore")
  (is (seq (v/sentexes-matching kb (list 'comment 'endorses '?t) 'CxSpeechActs))
      "and its vocabulary — the endorses doc — is present"))

;; ---- verify (1): a round-trip conversation, recoverable as data ----------

(tu/deftest-kb a-round-trip-conversation-is-recoverable-as-data
  (sa/speaker-context kb 'CxDeploy 'AgentAtlas)
  (sa/speaker-context kb 'CxDeploy 'AgentBoreas)
  (let [qh (sa/pose-query kb 'AgentAtlas 'WhichDbProdClusterUses)   ; A asks, in CxAtlas
        ah (sa/answer kb 'AgentBoreas 'PostgreSQL14 qh)]            ; B answers, in CxBoreas
    (testing "the query node is A's, in A's own context"
      (is (= 'CxAtlas (:context (v/sentex kb qh))))
      (is (= 'AgentAtlas (sa/responder-of kb qh))))
    (testing "recover what answered A's question, and who said it — read off the ANSWER"
      (let [as (sa/answers-to kb qh)            ; a plain query, wherever the answer was posted
            a  (first as)]
        (is (= 1 (count as)) "exactly one answer to the query")
        (is (= 'PostgreSQL14 (nth (:sentence a) 2)) "the answer content")
        (is (= ah (:id a)))
        (is (= 'CxBoreas (:context a))
            "the answerer's identity comes from the answer's context, not the query's")
        (is (= 'AgentBoreas (sa/responder-of kb ah)) "and from its provenance")))))

;; ---- verify (2): endorsement survives the first-writer-wins trap ----------

(tu/deftest-kb endorsement-survives-first-writer-wins
  (doseq [a '[AgentAtlas AgentBoreas AgentCiel]] (sa/speaker-context kb 'CxDeploy a))
  (let [P  (list 'usesDatabase 'ProdCluster 'PostgreSQL14)
        ph (sa/assert-claim kb 'AgentAtlas P)]           ; Atlas originates P in CxAtlas
    (testing "the trap: a second agent RE-asserting P writes no new provenance"
      (let [re (sa/assert-claim kb 'AgentCiel P 'CxAtlas)]   ; same sentence, same context
        (is (= ph re) "a re-assert of the same sentence in the same context is one sentex")
        (is (= 'AgentAtlas (:creator (v/provenance kb re)))
            "first-writer-wins: an endorsement modeled as a re-assert is lost")))
    (testing "the fix: each endorsement is its OWN meta-sentex, with its OWN creator"
      (let [e1 (sa/endorse kb 'AgentBoreas ph)
            e2 (sa/endorse kb 'AgentCiel   ph)]
        (is (not= e1 e2) "two endorsers are two distinct meta-sentexes")
        (is (= 'AgentBoreas (:creator (v/provenance kb e1))))
        (is (= 'AgentCiel   (:creator (v/provenance kb e2))))
        (is (= 'CxBoreas (:context (v/sentex kb e1))) "each in its own context")
        (is (= 'CxCiel   (:context (v/sentex kb e2))))
        (is (= #{'AgentBoreas 'AgentCiel}
               (set (map (comp second :sentence) (sa/endorsements-of kb ph))))
            "both endorsements recover as data — two distinct sources for P")))))

;; ---- verify (3): a dispute surfaces in contradictions --------------------

(tu/deftest-kb a-dispute-surfaces-in-contradictions
  (sa/speaker-context kb 'CxDeploy 'AgentAtlas)
  (sa/speaker-context kb 'CxDeploy 'AgentBoreas)
  (let [P  (list 'usesDatabase 'ProdCluster 'PostgreSQL14)
        ph (sa/assert-claim kb 'AgentAtlas P)       ; Atlas claims P in CxAtlas
        dh (sa/dispute kb 'AgentBoreas ph)]         ; Boreas disputes in CxBoreas
    (testing "the pair surfaces in contradictions, both sides carrying the adjudication material"
      (let [cs (v/contradictions kb)]
        (is (= 1 (count cs)))
        (let [{:keys [sides]} (first cs)]
          (is (= 2 (count sides)))
          (is (every? :context sides) "each side names its :context")
          (is (every? :defeat-class sides) "and its :defeat-class"))))
    (testing "the dispute edge is Boreas's target_following_predicate meta on P"
      (is (= 'CxBoreas (:context (v/sentex kb dh))))
      (is (= 'AgentBoreas (:creator (v/provenance kb dh))))
      (is (v/has-prop? kb :target-following 'disputes)))
    (testing "and the disputed claim is queryable via the contested rule"
      (is (seq (v/sentexes-matching kb (list 'contested (sx/sentex-handle ph))))
          "'which claims are under dispute' is a plain read, not a meta-sentex walk"))))

;; ---- justify: a reason offered for a claim, as a cascading meta -----------

(tu/deftest-kb a-justification-names-the-claim-it-grounds
  (sa/speaker-context kb 'CxDeploy 'AgentAtlas)
  (sa/speaker-context kb 'CxDeploy 'AgentBoreas)
  (let [P  (list 'usesDatabase 'ProdCluster 'PostgreSQL14)
        ph (sa/assert-claim kb 'AgentAtlas P)                      ; Atlas claims P in CxAtlas
        jh (sa/justify kb 'AgentBoreas 'ReleaseNotesSayPg14 ph)]   ; Boreas offers a reason
    (testing "the justification is Boreas's meta-sentex, in his own context, naming the claim by handle"
      (is (= 'CxBoreas (:context (v/sentex kb jh))))
      (is (= 'AgentBoreas (:creator (v/provenance kb jh))))
      (is (= (list 'justifies 'AgentBoreas 'ReleaseNotesSayPg14 (sx/sentex-handle ph))
             (:sentence (v/sentex kb jh)))))
    (testing "justifies is target_following_predicate, so retracting the claim sweeps the reason"
      (is (v/has-prop? kb :target-following 'justifies))
      (sa/retract-move kb ph)
      (is (nil? (v/sentex kb ph)) "the claim is gone")
      (is (nil? (v/sentex kb jh)) "and its justification cascaded with it"))))

;; ---- verify (4): THE CASCADE (the required check) --------------------

(tu/deftest-kb the-cascade-tears-down-reply-edges-and-the-mark-is-what-does-it
  (doseq [a '[AgentAtlas AgentBoreas AgentCiel AgentDelta]]
    (sa/speaker-context kb 'CxDeploy a))
  (testing "koinii's four response predicates carry the mark; the error acts do not"
    (doseq [p '[answers disputes endorses justifies]]
      (is (v/has-prop? kb :target-following p) (str p " is target_following_predicate")))
    (is (not (v/has-prop? kb :target-following 'notUnderstood))
        "error acts are deliberately unmarked")
    (is (not (v/has-prop? kb :target-following 'refuse))))
  (let [qh (sa/pose-query kb 'AgentAtlas 'WhichDbProdClusterUses)
        ah (sa/answer  kb 'AgentBoreas 'PostgreSQL14 qh)                        ; ternary marked meta
        eh (sa/endorse kb 'AgentCiel qh)                                        ; binary  marked meta
        mh (v/assert kb (list 'mentions 'AgentDelta (sx/sentex-handle qh)) 'CxDeploy)] ; unmarked, same shape
    (is (some? (v/sentex kb ah)) "the answer is stored, naming the query by handle")
    (is (some? (v/sentex kb eh)) "so is the endorsement")
    (is (some? (v/sentex kb mh)))
    (sa/retract-move kb qh)                                                      ; retract the target query
    (is (nil? (v/sentex kb qh)) "the target query is gone")
    (testing "its marked reply edges cascaded — no dangling edges"
      (is (nil? (v/sentex kb ah)) "the ternary answers meta went with the query")
      (is (nil? (v/sentex kb eh)) "the endorses meta went with the query"))
    (testing "contrast: the SAME-shaped UNMARKED meta survives — the mark cascades, not the shape"
      (is (some? (v/sentex kb mh))
          "an unmarked meta orphans harmlessly (core.clj:1667 / meta_sentex_test)"))))

;; ---- item 7: error acts name the received edge, in the refuser's context --

(tu/deftest-kb error-acts-name-the-received-edge-in-the-refusers-context
  (sa/speaker-context kb 'CxDeploy 'AgentAtlas)
  (sa/speaker-context kb 'CxDeploy 'AgentBoreas)
  (let [qh (sa/pose-query kb 'AgentAtlas 'WhichDbProdClusterUses)
        nh (sa/not-understood kb 'AgentBoreas qh)
        rh (sa/refuse kb 'AgentBoreas qh)]
    (is (= 'CxBoreas (:context (v/sentex kb nh))) "the error act lives in the refusing agent's context")
    (is (= 'CxBoreas (:context (v/sentex kb rh))))
    (is (= 'AgentBoreas (sa/responder-of kb nh)))
    (testing "unmarked: an error act outlives the edge it names"
      (sa/retract-move kb qh)
      (is (nil? (v/sentex kb qh)))
      (is (some? (v/sentex kb nh)) "notUnderstood survives — a parse failure is a fact about the exchange")
      (is (some? (v/sentex kb rh))))))

;; ---- ballots are response acts too: marked, and swept with their claim ----

(tu/deftest-kb ballots-cascade-with-the-claim-they-were-cast-on
  ;; `votesFor` / `votesAgainst` are response acts like `endorses`, so they carry the same
  ;; family — `target_following_predicate` above all.  Undeclared, a ballot outlives the
  ;; claim it was cast on: the disputed claim is retracted and the count stands over
  ;; nothing, which is exactly what the mark exists to prevent.
  (let [ctxs (into {} (for [a '[AgentAtlas AgentBoreas AgentCiel]]
                        [a (sa/speaker-context kb 'CxDeploy a)]))]
    (testing "both ballot predicates carry the mark, as the four reply verbs do"
      (is (v/has-prop? kb :target-following 'votesFor))
      (is (v/has-prop? kb :target-following 'votesAgainst)))
    (doseq [order ['[AgentBoreas AgentCiel] '[AgentCiel AgentBoreas]]]
      (let [[voter-1 voter-2] order
            ph   (sa/assert-claim kb 'AgentAtlas '(usesDatabase ProdCluster PostgreSQL14))
            cast (fn [agent pred]
                   (v/assert kb (list pred agent (sx/sentex-handle ph)) (ctxs agent)
                             {:creator agent}))
            for-h     (cast voter-1 'votesFor)
            against-h (cast voter-2 'votesAgainst)
            who  (str " (" voter-1 " voted first)")]
        (is (some? (v/sentex kb for-h)) (str "the for-ballot is stored" who))
        (is (some? (v/sentex kb against-h)) (str "and the against-ballot" who))
        (sa/retract-move kb ph)
        (is (nil? (v/sentex kb ph)) (str "the disputed claim is gone" who))
        (testing "and the ballots on it went with it, in either casting order"
          (is (nil? (v/sentex kb for-h)) (str "the for-ballot was withdrawn" who))
          (is (nil? (v/sentex kb against-h)) (str "and the against-ballot" who)))))))

;; ---- a response act on a handle that names nothing is refused ------------

(tu/deftest-kb dispute-refuses-a-handle-that-names-no-record
  ;; `dispute` builds its rebuttal from the target's own sentence, so a handle naming
  ;; nothing reads `nil` off `sentex` and stores the literal `(not nil)` plus a `disputes`
  ;; edge on nothing — a challenge to a claim that does not exist, indistinguishable in
  ;; the KB from one that does.  Refused by type, as `deref/marker` refuses one.
  (sa/speaker-context kb 'CxDeploy 'AgentBoreas)
  (let [absent (+ 1000000 (count (v/handles kb)))
        e (is (thrown? clojure.lang.ExceptionInfo (sa/dispute kb 'AgentBoreas absent)))]
    (is (= :koinii/no-such-handle (:type (ex-data e))))
    (is (= absent (:handle (ex-data e))))
    (testing "and nothing was written on the way to the refusal"
      (is (empty? (v/sentexes-matching kb '(not ?s) 'CxBoreas)))
      (is (empty? (v/sentexes-matching kb (list 'disputes 'AgentBoreas '?t) 'CxBoreas))))))
