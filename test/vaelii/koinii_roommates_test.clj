;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.koinii-roommates-test
  "End-to-end koinii scenarios: THREE roommates — Ava (wants a dog), Ben (allergic), and
  Ciel (the third) — argue about adopting a dog, and the KB carries the WHOLE conversation:
  facts, derived stances, questions and answers, endorsements, the reasons each side gives,
  ballots cast, the dispute standing OPEN while the house is split (nobody is wrong yet —
  koinii tolerates that: Priest's LP), and a majority vote that settles it once a tie is
  broken.  Every move is a sentex, so afterwards a plain query answers 'who wanted the dog,
  who objected, why, how each voted, and how it was decided.'

  Resolution is by COUNTED VOTE (`adjudication/resolve-by-majority`), not an arbiter's
  decree: a 1-1 split upholds nobody and stays open, and a third ballot breaks it 2-1 — the
  count decides, and a tie decides nothing.  Three shapes of the same story, composing the
  `dispute` reads, the `channel` (join / subscribe / reply / vote), and `adjudication`:

  - **emergent** (in-process) — nobody states a stance; each roommate's facts plus the
    house rules DERIVE the opposing conclusions, which collide;
  - **tiebreaker** (in-process) — the vote arc on its own: a 1-1 tie left open, then broken;
  - **long, over the WIRE** — a real multi-turn three-way conversation: roommates on their
    own daemon connections (separate processes), a live subscriber polling the feed
    off-thread, and one roommate who goes offline mid-argument and catches up from the
    durable KB on reconnect.  The vote is tallied where the KB lives (server-side), and
    the count is refused: a ballot cast over the wire carries no attestation.

  A miniature of the reference-agents proof minus trust-resolve:
  here a vote of the roommates decides, not the engine weighing their trust."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.client :as vc]
            [vaelii.core :as v]
            [vaelii.host.serve :as serve]
            [vaelii.impl.sentex :as sx]
            [vaelii.koinii.adjudication :as adj]
            [vaelii.koinii.channel :as ch]
            [vaelii.koinii.dispute :as d]
            [vaelii.koinii.identity :as id]
            [vaelii.koinii.speech-acts :as sa]
            [vaelii.test-util :as tu])
  (:import [org.eclipse.jetty.server Server]))

(defn- household-kb [kb]
  (tu/load-dumped! kb :koinii/speech-acts
                   #(doto % (tu/load-core!) (sa/load-speech-acts))))

;; Majority resolution requires the :proof-tier identity policy and counts only attested
;; ballots, so these tests run under it and the in-process ones vote through `vote!`.
(defn- with-proof-tier [f] (binding [id/*policy* :proof-tier] (f)))

(defn- vote!
  "Cast `agent`'s attested `stance` ballot on `claim-h`, under a `:proof-tier` principal
  whose credential is its id."
  [kb agent stance claim-h]
  (adj/cast-ballot kb (id/authenticate {:claimed-id agent :credential agent}
                                       {:policy :proof-tier :verify-fn (fn [a c] (= a c))})
                   stance claim-h))

(use-fixtures :once (tu/loaded household-kb))
(use-fixtures :each (tu/neutral) with-proof-tier)

(def ^:private proposal (list 'shouldAdopt 'Apartment 'Dog))

(defn- dispute-id [kb]
  (:dispute-id (first (d/disputes-in kb 'CxApartment))))

(defn- wait-for
  "Poll `pred` up to ~5s (the feed is async off-thread), returning its final value — so a
  test waits for a live event to land rather than sleeping a guessed interval."
  [pred]
  (loop [n 0] (if (or (pred) (>= n 500)) (pred) (do (Thread/sleep 10) (recur (inc n))))))

(def ^:private house-rules
  "The household's common sense — four rules that turn a roommate's private facts into a
  stance on the dog, in two 2-hop chains.  Nobody ever asserts `(not (shouldAdopt …))`; it
  is DERIVED, and so is its opposite.  Shared knowledge, so they live in the channel."
  [(list 'set/forwardRule (list 'implies (list 'wants_companionship '?p) (list 'wouldEnjoy '?p 'Dog)))
   (list 'set/forwardRule (list 'implies (list 'and (list 'memberOf '?p 'Apartment) (list 'wouldEnjoy '?p 'Dog))
                                proposal))
   (list 'set/forwardRule (list 'implies (list 'allergicTo '?p 'DogDander) (list 'harmedBy '?p 'Dog)))
   (list 'set/forwardRule (list 'implies (list 'and (list 'memberOf '?p 'Apartment) (list 'harmedBy '?p 'Dog))
                                (list 'not proposal)))])

;; ── the argument nobody stated: it emerges from facts + house rules ───────

(tu/deftest-kb an-argument-that-emerges-from-facts-and-house-rules
  (let [ava  (ch/join (ch/local kb) 'CxApartment 'AgentAva)   ; wants companionship
        ben  (ch/join (ch/local kb) 'CxApartment 'AgentBen)   ; allergic
        _ciel (ch/join (ch/local kb) 'CxApartment 'AgentCiel)] ; the tiebreaker
    (doseq [r house-rules] (v/assert kb r 'CxApartment))
    ;; each roommate states only FACTS about themselves — never a stance on the dog
    (ch/assert ava (list 'memberOf 'AgentAva 'Apartment))
    (ch/assert ava (list 'wants_companionship 'AgentAva))
    (ch/assert ben (list 'memberOf 'AgentBen 'Apartment))
    (ch/assert ben (list 'allergicTo 'AgentBen 'DogDander))

    (testing "neither roommate stated a conclusion — the disagreement is DERIVED"
      (is (v/ask? kb proposal 'CxApartment) "adopt-the-dog follows from Ava's facts")
      (is (v/ask? kb (list 'not proposal) 'CxApartment) "and don't-adopt from Ben's")
      (is (empty? (v/sentexes-matching kb (list 'not proposal) 'CxBen))
          "Ben never asserted the negation — the rules did")
      (is (d/disputed? kb proposal 'CxApartment) "yet the household sees a real dispute")
      (is (= :contradiction (:verdict (v/argue kb proposal 'CxApartment)))))

    (testing "the two stances are opinions the rules produced, not premises anyone stated"
      (is (not (v/premise? kb (v/handle-of kb proposal 'CxApartment)))
          "the pro-dog conclusion is derived")
      (is (not (v/premise? kb (v/handle-of kb (list 'not proposal) 'CxApartment)))
          "and so is the anti-dog one"))

    ;; the roommates vote on the emergent question; the majority resolves the DERIVED clash
    (let [claim-h (v/handle-of kb proposal 'CxApartment)
          id (dispute-id kb)]
      (vote! kb 'AgentAva :for claim-h)
      (vote! kb 'AgentBen :against claim-h)
      (testing "1-1 leaves the derived dispute open, both derivations still standing"
        (is (= :tie (:outcome (adj/resolve-by-majority kb id claim-h 'CxApartment))))
        (is (d/disputed? kb proposal 'CxApartment)))
      (testing "Ciel breaks it 2-1, and the derived contradiction resolves"
        (vote! kb 'AgentCiel :for claim-h)
        (let [r (adj/resolve-by-majority kb id claim-h 'CxApartment)]
          (is (= :for (:outcome r)))
          (is (not (d/disputed? kb proposal 'CxApartment)))
          (is (= :true (:verdict (v/argue kb proposal 'CxApartment))))
          (testing "the vote didn't erase Ben's reason — his allergy still stands, the
                    anti-dog opinion is outvoted (defeated on strength), not deleted"
            (is (v/ask? kb (list 'allergicTo 'AgentBen 'DogDander) 'CxBen))
            (is (some? (v/handle-of kb (list 'not proposal) 'CxApartment))
                "the losing derivation is still in the graph, just defeated"))
          (testing "reversible: retract the ruling and the facts clash again"
            (v/retract! kb (:ruling r))
            (is (d/disputed? kb proposal 'CxApartment))))))))

;; ── the simple one: propose, object, a 1-1 tie, then a tiebreaker ─────────

(tu/deftest-kb a-tiebreaker-vote-settles-a-split-house
  (let [ava  (ch/join (ch/local kb) 'CxApartment 'AgentAva)   ; wants a dog
        ben  (ch/join (ch/local kb) 'CxApartment 'AgentBen)   ; allergic, does not
        _ciel (ch/join (ch/local kb) 'CxApartment 'AgentCiel)  ; the third roommate
        ph   (ch/assert ava proposal)]                       ; Ava: "let's get a dog"
    (ch/justify ava 'GoodForExercise ph)
    (ch/dispute ben ph)                                       ; Ben: "no — I'm allergic"
    (ch/justify ben 'Allergy ph)
    (vote! kb 'AgentAva :for ph)
    (vote! kb 'AgentBen :against ph)
    (let [id (dispute-id kb)]

      (testing "1-1: a split house is left OPEN — the vote decides nobody"
        (let [r (adj/resolve-by-majority kb id ph 'CxApartment)]
          (is (= {:for 1 :against 1} (select-keys r [:for :against])))
          (is (= :tie (:outcome r)))
          (is (nil? (:ruling r)) "nothing was upheld")
          (is (d/disputed? kb proposal 'CxApartment) "still disputed — nobody was decreed the winner")
          (is (v/believed? kb ph) "and both sides still stand")))

      (testing "the tiebreaker: Ciel votes for, and 2-1 carries it"
        (vote! kb 'AgentCiel :for ph)
        (let [r (adj/resolve-by-majority kb id ph 'CxApartment)]
          (is (= {:for 2 :against 1} (select-keys r [:for :against])))
          (is (= :for (:outcome r)))
          (is (not (d/disputed? kb proposal 'CxApartment)) "the dispute resolves")
          (is (= :true (:verdict (v/argue kb proposal 'CxApartment))))
          (is (= 'AgentMajority (:arbiter (adj/who-ruled kb (:ruling r))))
              "recorded as the majority's call, not an arbiter's decree")
          (testing "and reversible: retract the ruling and the argument comes back"
            (v/retract! kb (:ruling r))
            (is (d/disputed? kb proposal 'CxApartment))))))))

;; ── the long one: THREE roommates, over the wire, a real back-and-forth ───
;;
;; A genuine multi-turn, three-way conversation — facts, derivations, questions,
;; answers, an endorsement, justifications on each side, a compromise floated and
;; rebutted, votes, one roommate going offline and catching up, and a count the resolver
;; refuses because no wire ballot is attested.  Every turn is a real koinii move landing
;; in the one shared KB.

(defn- justify-grounds
  "The grounds of every justification naming `target-h`, as a set — 'the reasons on
  record for this conclusion', a plain query."
  [kb target-h]
  (->> (v/sentexes-matching kb (list 'justifies '?a '?g (sx/sentex-handle target-h)) '?ctx)
       (map #(nth (:sentence %) 2)) set))

(defn- ballot-handles
  "The handles of every ballot cast on `claim-h`, in any context."
  [kb claim-h]
  (into #{} (map :id)
        (mapcat #(v/sentexes-matching kb (list % '?a (sx/sentex-handle claim-h)) '?ctx)
                '[votesFor votesAgainst])))

(defn- unattested
  "The ballots `resolve-by-majority` names unattested when it refuses, or nil when it rules."
  [kb id claim-h channel]
  (try (adj/resolve-by-majority kb id claim-h channel) nil
       (catch clojure.lang.ExceptionInfo e (:unattested (ex-data e)))))

(tu/deftest-kb ^:slow three-roommates-a-long-argument-over-the-wire
  (let [^Server server (serve/start kb {:port 0 :token nil})
        port (serve/port server)
        conn #(vc/client "localhost" port {:token nil})]
    (try
      ;; the apartment is configured with its common-sense house rules (server-side);
      ;; the three roommates are remote and only ever state FACTS — stances are derived
      (doseq [r house-rules] (v/assert kb r 'CxApartment))
      (let [ava   (ch/join (ch/wire (conn)) 'CxApartment 'AgentAva)   ; wants a dog
            ciel  (ch/join (ch/wire (conn)) 'CxApartment 'AgentCiel)  ; the third roommate
            ;; Ciel's phone: a LIVE subscriber polling the feed OFF-thread — the house
            ;; group-chat, which watches each opinion FORM (a derived conclusion arrives on
            ;; the feed like any belief change).  Started before anyone speaks.
            chat  (atom [])
            sub   (ch/subscribe ciel nil nil
                                (fn [e] (swap! chat into (map :sentence (:believed-added e))))
                                {:wait-ms 8000})]
        (try
          ;; ── 1. Ava states her facts; the house rules FORM the pro-dog opinion ──
          (ch/assert ava (list 'memberOf 'AgentAva 'Apartment))
          (ch/assert ava (list 'wants_companionship 'AgentAva))
          (is (wait-for #(some #{proposal} @chat))
              "the chat watched the pro-dog opinion form — nobody stated it, the rules derived it")
          (let [adopt-h (v/handle-of kb proposal 'CxApartment)]

            ;; ── 2. Ava says why ──
            (ch/justify ava 'GoodCompany adopt-h)
            ;; ── 3-4. Ciel asks who'd care for it; Ava answers ──
            (let [q-care (ch/pose-query ciel 'WhoWouldCareForIt)]
              (ch/answer ava 'AvaWalksAndFeeds q-care)
              ;; ── 5. Ciel likes the idea and endorses adopting ──
              (ch/endorse ciel adopt-h)
              (is (wait-for #(some #{(list 'endorses 'AgentCiel (sx/sentex-handle adopt-h))} @chat))
                  "the chat hears Ciel come down on the dog's side")

              ;; ── 6. Ben joins, states his allergy; the OPPOSITE opinion forms → they collide ──
              (let [ben (ch/join (ch/wire (conn)) 'CxApartment 'AgentBen)]  ; allergic
                (ch/assert ben (list 'memberOf 'AgentBen 'Apartment))
                (ch/assert ben (list 'allergicTo 'AgentBen 'DogDander))
                (is (wait-for #(some #{(list 'not proposal)} @chat)) "and then the anti-dog opinion")
                (testing "the household now disagrees — an emergent contradiction"
                  (is (d/disputed? kb proposal 'CxApartment))
                  (is (= :contradiction (:verdict (v/argue kb proposal 'CxApartment)))))
                (let [nope-h (v/handle-of kb (list 'not proposal) 'CxApartment)
                      id (dispute-id kb)]

                  ;; ── 7. Ben says why he objects ──
                  (ch/justify ben 'MyAllergy nope-h)
                  ;; ── 8-10. the compromise thread: Ciel asks, Ava offers, Ben rebuts ──
                  (let [q-hypo (ch/pose-query ciel 'CouldWeGetHypoallergenic)]
                    (ch/assert ava (list 'hypoallergenic_breed 'Poodle))
                    (ch/answer ava 'PoodlesAreHypoallergenic q-hypo)
                    (ch/justify ben 'DanderStillSheds nope-h))  ; the compromise doesn't cure it
                  (testing "the clash still stands — a floated compromise changed no belief"
                    (is (d/disputed? kb proposal 'CxApartment)))

                  ;; ── 11-12. they vote their derived stances → 1-1 ──
                  (ch/vote ava :for adopt-h)
                  (ch/vote ben :against adopt-h)
                  (testing "a count of wire ballots is refused, naming each: the daemon
                            attests nothing, so no wire ballot proves who cast it"
                    (is (= 2 (count (ballot-handles kb adopt-h))))
                    (is (= (ballot-handles kb adopt-h) (unattested kb id adopt-h 'CxApartment)))
                    (is (d/disputed? kb proposal 'CxApartment)))

                  ;; ── 13. Ben asks one more thing, then goes offline ──
                  (let [q-when (ch/pose-query ben 'WhenWouldWeGetIt)]
                    ;; ben's connection is abandoned — he is offline; the KB keeps every move

                    ;; ── 14-15. the two still awake carry on ──
                    (ch/answer ava 'ThisWeekendIfWeAgree q-when)
                    (ch/vote ciel :for adopt-h)              ; Ciel breaks the tie: tally now 2-1

                    ;; ── 16. Ben wakes on a NEW connection and catches up from the KB ──
                    (let [ben2-conn (conn)
                          ben2 (ch/join (ch/wire ben2-conn) 'CxApartment 'AgentBen)]
                      (testing "decoupled in time: Ben reads what he missed off the durable KB"
                        (is (= 3 (count (ch/open-queries ben2)))
                            "all three questions are on record — his and Ciel's two")
                        (is (= 'ThisWeekendIfWeAgree
                               (ch/answer-content (first (ch/answers-to ben2 q-when))))
                            "Ava's answer to his last question, made while he slept")
                        (testing "and he discovers the house is split on the dog"
                          (is (vc/ask? ben2-conn proposal 'CxApartment))
                          (is (vc/ask? ben2-conn (list 'not proposal) 'CxApartment))))

                      ;; ── 17. the 2-1 count stays a count ──
                      (testing "2-1 over the wire rules nothing: every ballot is named unattested"
                        (is (= {:for 2 :against 1} (adj/tally kb adopt-h)) "the tally is readable")
                        (is (= 3 (count (ballot-handles kb adopt-h))))
                        (is (= (ballot-handles kb adopt-h) (unattested kb id adopt-h 'CxApartment)))
                        (is (d/disputed? kb proposal 'CxApartment))
                        (is (vc/ask? ben2-conn (list 'allergicTo 'AgentBen 'DogDander) 'CxBen)
                            "his allergy fact still stands"))

                      ;; ── the whole conversation is recoverable as knowledge (sibling of resolve) ──
                      (testing "afterwards a plain query recovers the reasons and the vote"
                        (is (= #{'GoodCompany} (justify-grounds kb adopt-h)) "Ava's reason for")
                        (is (= #{'MyAllergy 'DanderStillSheds} (justify-grounds kb nope-h))
                            "and Ben's two reasons against")
                        (is (= #{'AgentCiel}
                               (set (map ch/speaker-of (ch/endorsements-of ben2 adopt-h))))
                            "Ciel's endorsement of the dog"))))))))
          (finally (ch/unsubscribe sub))))
      (finally (.stop server)))))

;; ── over the wire, under the daemon's token table ─────────────────────────
;;
;; Each roommate holds a token whose grant writes only their own context; the operator
;; holds the admin token and runs the joins.  The boundary holds against a plain client
;; that bypasses `channel`, and the ballots each roommate casts over their own connection
;; carry the principal the daemon recorded, so the majority count rules.

(def ^:private roommate-table
  {"tok-ava"  {:principal 'AgentAva  :writes #{'CxAva}}
   "tok-ben"  {:principal 'AgentBen  :writes #{'CxBen}}
   "tok-ciel" {:principal 'AgentCiel :writes #{'CxCiel}}
   "tok-op"   {:principal 'AgentOperator :admin? true}})

(defn- refusal
  "The `:type` a daemon call refused with, or nil when it answered."
  [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(tu/deftest-kb a-token-table-holds-each-roommate-to-their-own-context-and-proves-their-ballots
  (let [^Server server (serve/start kb {:port 0 :token-table roommate-table})
        conn #(vc/client "localhost" (serve/port server) {:token %})]
    (try
      (let [op     (ch/wire (conn "tok-op"))
            seat   (fn [agent tok]
                     (assoc (ch/join op 'CxApartment agent) :medium (ch/wire (conn tok))))
            ava    (seat 'AgentAva "tok-ava")
            ben    (seat 'AgentBen "tok-ben")
            ciel   (seat 'AgentCiel "tok-ciel")
            ava-c  (:conn (:medium ava))
            ph     (ch/assert ava proposal)
            ben-no (ch/dispute ben ph)]
        (testing "a roommate's claim lands in their own context, recorded as theirs"
          (is (= {:creator 'AgentAva :principal 'AgentAva}
                 (select-keys (v/provenance kb ph) [:creator :principal]))))
        (testing "a plain client holding Ava's token cannot write as anyone else"
          (is (= :forbidden-context (refusal #(vc/assert ava-c (list 'allergicTo 'AgentBen 'DogDander) 'CxBen))))
          (is (= :forbidden-context (refusal #(vc/retract! ava-c ben-no))))
          (is (= :forbidden-context (refusal #(vc/assert ava-c (list 'registered_agent 'AgentAva) 'CxRegistry))))
          (is (= :creator-mismatch (refusal #(vc/assert ava-c (list 'memberOf 'AgentAva 'Apartment) 'CxAva {:creator 'AgentBen}))))
          (is (v/believed? kb ben-no) "Ben's claim stands"))
        (testing "the admin token writes CxRegistry"
          (is (nil? (refusal #(vc/assert (conn "tok-op") (list 'registered_agent 'AgentAva) 'CxRegistry)))))
        (testing "ballots cast over each roommate's own connection carry the recorded principal,
                  so the count rules"
          (ch/vote ava :for ph)
          (ch/vote ben :against ph)
          (ch/vote ciel :for ph)
          (let [r (adj/resolve-by-majority kb (dispute-id kb) ph 'CxApartment)]
            (is (= {:for 2 :against 1 :outcome :for} (select-keys r [:for :against :outcome])))
            (is (not (d/disputed? kb proposal 'CxApartment))))))
      (finally (.stop server)))))
