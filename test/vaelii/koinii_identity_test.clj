;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.koinii-identity-test
  "Koinii actor identity: per-agent contexts as identity substrate and
  write boundary, an admin-only registry with trust as a mutable number, and the
  policy-conditional auth extension point.  One deftest per 'How to verify' bullet, plus the
  registry-load and trust-mutation checks the design decisions (D3) demand."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.koinii.identity :as id]
            [vaelii.test-util :as tu])
  (:import (clojure.lang ExceptionInfo)))

(defn- registry-kb
  "A fresh CxCore KB with the koinii registry vocabulary loaded."
  []
  (tu/load-dumped! (tu/fresh) :koinii/registry
                   #(doto % (core-context/load-into) (id/load-registry))))

(use-fixtures :each (tu/neutral-fresh registry-kb))

;; ---- the registry context loads ------------------------------------------

(tu/deftest-kb registry-context-loads-under-core
  (is (v/sees? kb 'CxRegistry 'CxCore) "CxRegistry wires itself under CxCore")
  (is (seq (v/sentexes-matching kb (list 'comment 'trustLevel '?t) 'CxRegistry))
      "and its vocabulary — the trustLevel doc — is present"))

;; ---- verify (c): the registry is a plain context-scoped read -------------

(tu/deftest-kb registry-is-queryable
  (let [admin (id/admin-principal)]
    (id/register-agent kb admin 'AgentAtlas  "Atlas"  0.9)
    (id/register-agent kb admin 'AgentBoreas "Boreas" 0.6)
    (testing "which agents exist, and at what trust — a CxRegistry read"
      (is (= #{'AgentAtlas 'AgentBoreas} (set (id/registered-agents kb))))
      (is (= 0.9 (id/trust-of kb 'AgentAtlas)))
      (is (= 0.6 (id/trust-of kb 'AgentBoreas)))
      (is (= "Atlas" (id/display-name-of kb 'AgentAtlas))))
    (testing "and it really is a bare context-scoped match, ready for adjudication"
      (is (seq (v/sentexes-matching kb (list 'trustLevel 'AgentAtlas '?t) 'CxRegistry))))))

;; ---- verify (d): registry writes refused to non-admin principals ---------

(tu/deftest-kb registry-writes-refused-to-non-admin
  (let [boreas (id/authenticate {:claimed-id 'AgentBoreas} {:policy :cooperative})]
    (testing "a governed agent cannot self-register / self-promote"
      (is (thrown-with-msg? ExceptionInfo #"registry-forbidden"
                            (id/register-agent kb boreas 'AgentBoreas "Boreas" 1)))
      (is (thrown-with-msg? ExceptionInfo #"registry-forbidden"
                            (id/set-trust! kb boreas 'AgentBoreas 1)))
      (testing "even a raw ingest aimed at CxRegistry"
        (is (thrown-with-msg? ExceptionInfo #"registry-forbidden"
                              (id/ingest-into kb boreas 'CxRegistry (list 'trustLevel 'AgentBoreas 1))))))
    (testing "nothing landed — the authority the agent is governed by is untouched"
      (is (empty? (id/registered-agents kb)))
      (is (nil? (id/trust-of kb 'AgentBoreas))))
    (testing "only the admin principal writes it"
      (id/register-agent kb (id/admin-principal) 'AgentBoreas "Boreas" 0.6)
      (is (= 0.6 (id/trust-of kb 'AgentBoreas))))))

;; ---- verify (a): an agent cannot write another agent's context -----------

(tu/deftest-kb agent-cannot-write-another-agents-context
  (id/agent-context kb 'CxDeploy 'AgentAtlas)
  (id/agent-context kb 'CxDeploy 'AgentBoreas)
  (let [boreas (id/authenticate {:claimed-id 'AgentBoreas} {:policy :cooperative})]
    (testing "the write boundary refuses Boreas targeting CxAtlas (enforced)"
      (is (thrown-with-msg? ExceptionInfo #"foreign-context"
                            (id/ingest-into kb boreas 'CxAtlas (list 'ran 'ProdCluster)))))
    (testing "and ingest auto-routes to Boreas's OWN context — no call site can name another"
      (let [h (id/ingest kb boreas (list 'ran 'ProdCluster))]
        (is (= h (v/handle-of kb (list 'ran 'ProdCluster) 'CxBoreas)))
        (is (nil? (v/handle-of kb (list 'ran 'ProdCluster) 'CxAtlas))
            "nothing of Boreas's landed in Atlas's context")))
    (testing "under cooperative, WHO you are is documented-unenforced (not silently assumed)"
      (is (false? (:authenticated? boreas)) "the cooperative principal is marked unverified")
      (is (= :cooperative (:policy boreas)))
      (is (thrown-with-msg? ExceptionInfo #"identity unverified"
                            (id/authenticate {:claimed-id 'AgentBoreas} {:policy :proof-tier}))
          "proof-tier is the extension point that closes the gap — an unverified claim is refused"))))

;; ---- verify (b): no writing under another *creator* ----------------------

(tu/deftest-kb no-writing-under-another-creator
  (id/agent-context kb 'CxDeploy 'AgentAtlas)
  (id/agent-context kb 'CxDeploy 'AgentBoreas)
  (let [verify (fn [id cred] (= cred (str "sig:" (name id))))]
    (testing "proof-tier: provenance reflects the AUTHENTICATED principal, not a client string"
      (let [atlas (id/authenticate {:claimed-id 'AgentAtlas :credential "sig:AgentAtlas"
                                    :source "atlas-daemon"}
                                   {:policy :proof-tier :verify-fn verify})
            h     (id/ingest kb atlas (list 'ran 'ProdCluster))
            prov  (v/provenance kb h)]
        (is (= 'AgentAtlas (:creator prov)))
        (is (true? (:authenticated? prov)))
        (is (= "atlas-daemon" (:source prov)) "the source hint rides the open provenance map")))
    (testing "a client cannot stamp AgentAtlas without the credential — refused at the extension poinface"
      (is (thrown-with-msg? ExceptionInfo #"identity unverified"
                            (id/authenticate {:claimed-id 'AgentAtlas :credential "forged"}
                                             {:policy :proof-tier :verify-fn verify}))))
    (testing "ingest offers no creator override — the creator is always the principal id"
      (let [boreas (id/authenticate {:claimed-id 'AgentBoreas} {:policy :cooperative})
            h      (id/ingest kb boreas (list 'ran 'ProdCluster))]
        (is (= 'AgentBoreas (:creator (v/provenance kb h))))))))

;; ---- verify (e): first-writer-wins is NOT required for attribution ----

(tu/deftest-kb co-attribution-survives-first-writer-wins
  (id/agent-context kb 'CxDeploy 'AgentAtlas)
  (id/agent-context kb 'CxDeploy 'AgentBoreas)
  (let [P      (list 'usesDatabase 'ProdCluster 'PostgreSQL14)
        atlas  (id/authenticate {:claimed-id 'AgentAtlas}  {:policy :cooperative})
        boreas (id/authenticate {:claimed-id 'AgentBoreas} {:policy :cooperative})
        ha     (id/ingest kb atlas P)
        hb     (id/ingest kb boreas P)]     ; a re-assert of the SAME sentence
    (testing "Atlas's P and Boreas's P are distinct sentexes in distinct contexts"
      (is (not= ha hb))
      (is (= ha (v/handle-of kb P 'CxAtlas)))
      (is (= hb (v/handle-of kb P 'CxBoreas))))
    (testing "each keeps its own creator — first-writer-wins loses no co-source"
      (is (= 'AgentAtlas  (:creator (v/provenance kb ha))))
      (is (= 'AgentBoreas (:creator (v/provenance kb hb)))))
    (testing "co-attribution = the set of agent-contexts backing P (no retired source index)"
      (is (= #{'CxAtlas 'CxBoreas} (set (id/co-attribution kb P)))))))

;; ---- D3: trust is a MUTABLE number, overwritten not accumulated -----------

(tu/deftest-kb trust-is-a-mutable-number
  (let [admin (id/admin-principal)]
    (id/register-agent kb admin 'AgentAtlas "Atlas" 1)   ; operator-assigned tier at bootstrap
    (is (= 1 (id/trust-of kb 'AgentAtlas)))
    (id/set-trust! kb admin 'AgentAtlas 0.94)             ; later overwritten by earned reputation
    (is (= 0.94 (id/trust-of kb 'AgentAtlas)))
    (is (= 1 (count (v/sentexes-matching kb (list 'trustLevel 'AgentAtlas '?t) 'CxRegistry)))
        "exactly one trust value stands — the update overwrote, did not accumulate")))

(tu/deftest-kb a-registry-read-rests-on-the-functional-refusal-and-says-so
  ;; `trust-of` and `set-trust!` both read one row out of a *set* of matches, and
  ;; `sentexes-matching` promises the set and not an order: over two rows a bare `first`
  ;; would answer with whichever the index enumerated, so the trust a reader sees and the
  ;; row an overwrite retracts would follow the order the registry was written in.
  ;;
  ;; What makes one row the only possibility is the vocabulary, not the read: `trustLevel`
  ;; is declared `functional`, so the second value is refused at assert.  Both halves are
  ;; pinned here — the refusal that holds it, and the read's own refusal for the state the
  ;; first one prevents.
  (let [admin (id/admin-principal)]
    (id/register-agent kb admin 'AgentAtlas "Atlas" 1)
    (testing "a second trust value is refused outright — never stored beside the first"
      (is (thrown-with-msg? ExceptionInfo #"functional violation"
                            (v/assert kb '(trustLevel AgentAtlas 0.5) 'CxRegistry)))
      (is (= 1 (id/trust-of kb 'AgentAtlas))))
    (testing "and the registry read refuses two rows rather than halving them silently"
      ;; a temp predicate nothing declares functional is the only way to build the state
      (let [p  (tu/fresh-term :predicate "heldBy")
            h1 (v/assert kb (list p 'AgentAtlas 1) 'CxRegistry)
            h2 (v/assert kb (list p 'AgentAtlas 2) 'CxRegistry)]
        (is (= 2 (count (v/sentexes-matching kb (list p 'AgentAtlas '?v) 'CxRegistry)))
            "two rows stand, since nothing declared this one functional")
        (let [e (try (#'id/sole-registry-match kb (list p 'AgentAtlas '?v))
                     (catch ExceptionInfo e e))]
          (is (instance? ExceptionInfo e) "the read refuses rather than naming one of the two")
          (is (= :koinii/registry-not-functional (:type (ex-data e))))
          (is (= #{h1 h2} (:handles (ex-data e)))
              "and it names both handles, so the KB state is readable from the refusal"))))))

;; ---- the admin writes the registry, and ONLY the registry -----------------

(tu/deftest-kb admin-writes-only-the-registry
  (testing "an admin aimed at a non-registry context is refused — it curates the authority,
            it is not a general writer over every agent's context"
    (is (thrown-with-msg? ExceptionInfo #"admin-off-registry"
                          (id/ingest-into kb (id/admin-principal) 'CxAtlas
                                          (list 'ran 'ProdCluster))))))

;; ---- authenticate refuses a policy it does not know -----------------------

(deftest authenticate-refuses-an-unknown-policy
  (testing "a policy that is neither :cooperative nor :proof-tier is refused, not silently
            treated as one of them"
    (let [d (try (id/authenticate {:claimed-id 'AgentAtlas} {:policy :made-up})
                 nil
                 (catch ExceptionInfo e (ex-data e)))]
      (is (= :koinii/unknown-policy (:type d))
          "refused by name — a caller catching this must not have to read the message")
      (is (= :made-up (:policy d)) "and the refusal names the policy it did not know"))))

;; ---- a seed context nothing ships is a failure to start -------------------

(tu/deftest-kb a-seed-context-with-no-file-on-the-classpath-is-refused
  (testing "koinii loads its own seed files, so a missing one is not a KB that came up
            with an empty registry — it is a build with a file left out, and the loader
            says which"
    (let [d (try (id/load-seed-context kb 'CxNoSuchKoiniiSeed)
                 nil
                 (catch ExceptionInfo e (ex-data e)))]
      (is (= :koinii/missing-seed (:type d)) "refused by name rather than read as empty")
      (is (= "kb/koinii/CxNoSuchKoiniiSeed.txt" (:resource d))
          "naming the classpath resource the build did not ship"))))
