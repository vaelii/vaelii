;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.sandbox-test
  "Somewhere safe to be wrong — `vaelii.browser.sandbox`, and the browser wiring that puts a
  reader in one without asking them to choose a context.

  The property that matters is asymmetric visibility, and it is not a permission check:
  the sandbox hangs below `CxWell`, so `genlCx` — the same relation that decides
  what any context can see — gives it every shipped type and rule while giving nothing
  shipped a way to look back in. These tests assert both directions, because only having
  half of it is a sandbox that either cannot be used or cannot be trusted."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.catalog :as catalog]
            [vaelii.browser.sandbox :as sandbox]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defn- fresh-sandbox
  "A sandbox context symbol nobody else is using, from a real minted token."
  [] (sandbox/context-for (sandbox/mint-token)))

;; ---- the context itself --------------------------------------------------

(tu/deftest-kb a-sandbox-sees-the-ontology-and-nothing-sees-it
  (let [sbx (fresh-sandbox)]
    (sandbox/open kb sbx)
    (try
      (testing "it sees the whole shipped spindle, so every type and rule is usable"
        (doseq [c ['CxWell 'CxBiology 'CxUniverse 'CxCore]]
          (is (v/sees? kb sbx c) (str "the sandbox should see " c))))
      (testing "and nothing sees it — no shipped context, and no other sandbox"
        (is (empty? (into [] (comp (remove #{sbx}) (filter #(v/sees? kb % sbx)))
                          (v/contexts kb)))))
      (testing "a shipped type is usable from inside, and the shipped rule fires there"
        (v/assert kb '(living_thing SandboxRufus) sbx)
        (is (v/ask? kb '(mortal SandboxRufus) sbx)
            "CxBiology's default rule reached content in the sandbox")
        (testing "and the conclusion was placed in the sandbox, not in the rule's context"
          (is (= #{sbx} (set (map :context (v/sentexes-matching kb '(mortal SandboxRufus)
                                                                '?ctx)))))))
      (finally (sandbox/reset! kb sbx)))))

(tu/deftest-kb nothing-is-created-until-something-is-written
  (let [sbx (fresh-sandbox)]
    (is (not (sandbox/live? kb sbx)) "naming a sandbox does not make one")
    (is (= [] (sandbox/extent kb sbx)))
    (let [before (tu/sentex-ids kb)]
      (is (= before (tu/sentex-ids kb)) "and reading it stores nothing either")
      (sandbox/open kb sbx)
      (try
        (is (sandbox/live? kb sbx))
        (is (= 1 (- (count (tu/sentex-ids kb)) (count before)))
            "exactly one sentex: the genlCx edge that makes it a context")
        (finally (sandbox/reset! kb sbx))))))

(tu/deftest-kb opening-twice-is-the-same-sandbox
  (let [sbx (fresh-sandbox)]
    (sandbox/open kb sbx)
    (try
      (let [after-first (tu/sentex-ids kb)]
        (sandbox/open kb sbx)
        (is (= after-first (tu/sentex-ids kb)) "find-or-create, so a re-open writes nothing"))
      (finally (sandbox/reset! kb sbx)))))

(tu/deftest-kb reset-returns-the-kb-to-exactly-what-it-was
  (testing "the whole point: a reader can be wrong in here and leave no trace.  Compared
            as *sets of handles*, not counts — a teardown that removed one thing and
            derived another would balance and still be wrong"
    (let [sentexes-before (tu/sentex-ids kb)
          justs-before    (tu/justification-ids kb)
          sbx             (fresh-sandbox)]
      (sandbox/open kb sbx)
      (v/assert kb '(living_thing SandboxTibbles) sbx)
      (v/assert kb '(bird SandboxPingu) sbx)
      (v/assert-rule kb '[(bird ?x)] '(sandbox_feathered ?x) sbx)
      (is (< (count sentexes-before) (count (tu/sentex-ids kb))) "there is something to lose")
      (is (< (count justs-before) (count (tu/justification-ids kb)))
          "including derived content, which is what a naive teardown leaves behind")
      (let [r (sandbox/reset! kb sbx)]
        (is (pos? (:removed-sentexes r)))
        (is (= sentexes-before (tu/sentex-ids kb)) "every sentex the session made is gone")
        (is (= justs-before (tu/justification-ids kb))
            "and every justification — no orphan pointing at a deleted sentex"))
      (testing "the context is not a context any more either"
        (is (not (sandbox/live? kb sbx)))
        (is (not (some #{sbx} (v/contexts kb))))))))

(tu/deftest-kb a-conclusion-derived-into-the-sandbox-is-torn-down-with-it
  (testing "the sweep, not the extent list, is what has to reach this: the conclusion is
            not something the reader wrote, so nothing but dependency-directed retraction
            knows it should go"
    (let [justs-before (tu/justification-ids kb)
          sbx          (fresh-sandbox)]
      (sandbox/open kb sbx)
      (v/assert kb '(living_thing SandboxMoggy) sbx)
      (let [derived (v/handle-of kb '(mortal SandboxMoggy) sbx)]
        (is (nat-int? derived) "the shipped rule concluded into the sandbox")
        (is (v/in? kb derived))
        (sandbox/reset! kb sbx)
        (is (nil? (v/sentex kb derived)) "the conclusion went with its premise")
        (is (= justs-before (tu/justification-ids kb))
            "and its justification with it, leaving nothing dangling")))))

(tu/deftest-kb resetting-a-sandbox-that-was-never-opened-is-a-no-op
  (let [before (tu/sentex-ids kb)]
    (is (= {:removed-sentexes 0 :removed-justifications 0}
           (sandbox/reset! kb (fresh-sandbox))))
    (is (= before (tu/sentex-ids kb)))))

;; ---- session identity ----------------------------------------------------

(deftest two-sessions-never-share-a-sandbox
  (let [tokens (repeatedly 200 sandbox/mint-token)]
    (is (= 200 (count (set tokens))) "tokens are distinct")
    (is (= 200 (count (set (map sandbox/context-for tokens)))) "and so are their contexts")
    (is (every? #(re-matches #"CxSandbox[0-9a-f]+" (str %))
                (map sandbox/context-for tokens))
        "each is a well-formed context name")))

(deftest a-cookie-cannot-name-a-context-it-was-not-given
  (testing "the token is interpolated into a symbol, so an unvalidated one is an
            injection — a crafted cookie naming a shipped context would make the assert
            form write straight into the ontology"
    (doseq [bad ["CxWell" "../../etc" "abc" "" "0123456789abcdef0123456789abcdef0"
                 "Universe" "deadbeefZZZZ"]]
      (is (nil? (sandbox/context-for bad)) (str "refused: " (pr-str bad)))))
  (testing "and a token we did mint is accepted"
    (let [t (sandbox/mint-token)]
      (is (some? (sandbox/context-for t))))))

;; ---- the browser ---------------------------------------------------------

(defn- cookie-of [resp]
  (some-> (get-in resp [:headers "Set-Cookie"]) (str/split #";") first))

(tu/deftest-kb the-browser-mints-a-session-and-creates-nothing-by-looking
  (let [app    (web/app kb)
        before (tu/sentex-ids kb)
        r      (app {:request-method :get :uri "/assert" :headers {}})]
    (testing "a first visit gets a session cookie, scoped and script-proof"
      (let [c (get-in r [:headers "Set-Cookie"])]
        (is (str/starts-with? c "vaelii-sandbox="))
        (is (str/includes? c "HttpOnly"))
        (is (str/includes? c "SameSite=Lax"))
        (is (not (str/includes? c "Max-Age")) "a sitting, not a subscription")))
    (testing "and the KB is untouched — looking is not writing"
      (is (= before (tu/sentex-ids kb))))
    (testing "the context field is pre-filled with the sandbox, so the safe thing is the
              default rather than a choice the reader has to know to make"
      (is (re-find #"id=\"assert-ctx\"[^>]*value=\"CxSandbox[0-9a-f]+\"" (:body r))))
    (testing "a returning request keeps the same sandbox rather than being handed a new one"
      (let [c  (cookie-of r)
            r2 (app {:request-method :get :uri "/assert" :headers {"cookie" c}})]
        (is (nil? (get-in r2 [:headers "Set-Cookie"])) "no re-mint")
        (is (str/includes? (:body r2) (str/replace c "vaelii-sandbox=" "Sandbox")))))))

(tu/deftest-kb writing-through-the-form-creates-the-sandbox-and-reset-empties-it
  (let [app    (web/app kb)
        before (tu/sentex-ids kb)
        r      (app {:request-method :get :uri "/assert" :headers {}})
        cookie (cookie-of r)
        sbx    (second (re-find #"value=\"(CxSandbox[0-9a-f]+)\"" (:body r)))
        hdrs   {"cookie" cookie "host" "localhost:3000"}
        post   #(app {:request-method :post :uri %1 :params %2 :headers hdrs})]
    (testing "the first write brings the context into being and the rules run in it"
      (let [b (:body (post "/assert" {"text" "(living_thing SandboxWebRufus)" "ctx" sbx}))]
        (is (str/includes? b "Stored"))
        (is (v/ask? kb '(mortal SandboxWebRufus) (symbol sbx)))
        (is (str/includes? b "Your sandbox") "the panel says where the writing went")))
    (testing "it is behind the write guard like every other write to a KB's content, so a
              job holding this process's one writer refuses it rather than emptying the
              sandbox behind a page with nothing to say about why"
      (with-redefs [catalog/write-blocked? (constantly true)]
        (let [r (post "/sandbox/reset" {})]
          (is (= 200 (:status r)) "a page, not a status htmx would decline to swap")
          (is (str/includes? (:body r) "Nothing was written"))))
      (is (sandbox/live? kb (symbol sbx)) "and the sandbox it did not discard is still there"))
    (testing "reset discards it and says what it took"
      (let [b (:body (post "/sandbox/reset" {}))]
        (is (re-find #"sandbox reset — \d+ sentexes and \d+ justification" b))
        (is (= before (tu/sentex-ids kb)) "back to exactly the pre-session KB")))
    (testing "and it is a write, so a cross-origin caller cannot trigger it"
      (is (= 403 (:status (app {:request-method :post :uri "/sandbox/reset" :params {}
                                :headers {"cookie" cookie "host" "localhost:3000"
                                          "origin" "http://evil.example"}})))))))

(tu/deftest-kb two-browser-sessions-write-to-different-sandboxes
  (let [app    (web/app kb)
        before (tu/sentex-ids kb)
        open   (fn [] (let [r (app {:request-method :get :uri "/assert" :headers {}})]
                        {:cookie (cookie-of r)
                         :ctx    (second (re-find #"value=\"(CxSandbox[0-9a-f]+)\"" (:body r)))}))
        a      (open)
        b      (open)]
    (is (not= (:ctx a) (:ctx b)) "two readers of one process are not in one sandbox")
    (try
      (doseq [{:keys [cookie ctx]} [a b]]
        (app {:request-method :post :uri "/assert"
              :params {"text" "(living_thing SandboxShared)" "ctx" ctx}
              :headers {"cookie" cookie "host" "localhost:3000"}}))
      (testing "each sees only its own writing"
        (is (= 1 (count (v/sentexes-matching kb '(living_thing SandboxShared) (symbol (:ctx a))))))
        (is (not (v/sees? kb (symbol (:ctx a)) (symbol (:ctx b))))))
      (testing "and one resetting leaves the other's alone"
        (app {:request-method :post :uri "/sandbox/reset" :params {}
              :headers {"cookie" (:cookie a) "host" "localhost:3000"}})
        (is (not (sandbox/live? kb (symbol (:ctx a)))))
        (is (sandbox/live? kb (symbol (:ctx b))))
        (app {:request-method :post :uri "/sandbox/reset" :params {}
              :headers {"cookie" (:cookie b) "host" "localhost:3000"}}))
      (is (= before (tu/sentex-ids kb)))
      (finally
        (sandbox/reset! kb (symbol (:ctx a)))
        (sandbox/reset! kb (symbol (:ctx b)))))))
