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
            [vaelii.browser.jobs :as jobs]
            [vaelii.browser.sandbox :as sandbox]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.impl.decide.argument :as argument]
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
      (testing "it sees every shipped context, so every type and rule is usable"
        (doseq [c ['CxWell 'CxBiology 'CxUniverse]]
          (is (v/sees? kb sbx c) (str "the sandbox should see " c))))
      (testing "and nothing sees it — no shipped context, and no other sandbox"
        (is (empty? (into [] (comp (remove #{sbx}) (filter #(v/sees? kb % sbx)))
                          (v/contexts kb)))))
      (testing "a shipped type is usable from inside, and the shipped rule fires there"
        (v/assert kb '(organism SandboxRufus) sbx)
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
        ;; under the entailing reading CxUniverse's (arg genlCx 1 context) derives the edge's
        ;; membership; the starter loaded under the same reading already holds CxWell's
        (is (= (cond-> #{(list 'genlCx sbx 'CxWell)}
                 argument/*assertive-arg-types?* (conj (list 'context sbx)))
               (into #{} (map #(:sentence (v/sentex kb %)))
                     (remove before (tu/sentex-ids kb))))
            "the genlCx edge that makes it a context, and what the edge derives")
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
      (v/assert kb '(organism SandboxTibbles) sbx)
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
      (v/assert kb '(organism SandboxMoggy) sbx)
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

(deftest a-listed-sandbox-name-is-not-a-cookie
  (testing "every reader sees every context's name (/find, CxWell's page, /op :contexts),
            so the name must not carry the token the owner's cookie carries"
    (let [t      (sandbox/mint-token)
          cx     (sandbox/context-for t)
          lifted (subs (str cx) (count "CxSandbox"))]
      (is (not (str/includes? (str cx) t)))
      (is (some? (sandbox/context-for lifted)) "the lifted suffix is a well-formed token")
      (is (not= cx (sandbox/context-for lifted)) "naming another sandbox")
      (is (nil? (sandbox/context-of {:headers {"cookie" (str "vaelii-sandbox=" lifted)}}))
          "and a cookie carrying it, with no tag, names none"))))

(deftest a-cookie-names-a-sandbox-only-with-the-tag-the-server-gave-it
  (let [t     (sandbox/mint-token)
        named (fn [v] (sandbox/context-of {:headers {"cookie" (str "vaelii-sandbox=" v)}}))]
    (doseq [v [t (str t ".") (str t "." (sandbox/mint-token)) (str (sandbox/mint-token) "." t)]]
      (is (nil? (named v)) v))))

;; ---- the browser ---------------------------------------------------------

(defn- cookie-of [resp]
  (some-> (get-in resp [:headers "Set-Cookie"]) (str/split #";") first))

(defn- session
  "A browser session's cookie and the sandbox name its assert form offers."
  [app]
  (let [r (app {:request-method :get :uri "/assert" :headers {}})]
    {:cookie (cookie-of r)
     :ctx    (second (re-find #"value=\"(CxSandbox[0-9a-f]+)\"" (:body r)))}))

(tu/deftest-kb the-browser-replaces-a-cookie-it-did-not-mint
  (let [app    (web/app kb)
        chosen "0123456789abcdef0123456789abcdef"
        r      (app {:request-method :get :uri "/assert"
                     :headers {"cookie" (str "vaelii-sandbox=" chosen)}})]
    (is (str/starts-with? (str (get-in r [:headers "Set-Cookie"])) "vaelii-sandbox=")
        "a fresh token is minted in its place")
    (is (not (str/includes? (:body r) (str (sandbox/context-for chosen))))
        "and the form does not offer the sandbox the client chose")))

(tu/deftest-kb the-browser-mints-a-session-and-creates-nothing-by-looking
  (let [app    (web/app kb)
        before (tu/sentex-ids kb)
        r      (app {:request-method :get :uri "/assert" :headers {}})]
    (testing "a first visit gets a session cookie, scoped and script-proof"
      (let [c (get-in r [:headers "Set-Cookie"])]
        (is (str/starts-with? c "vaelii-sandbox="))
        (is (str/includes? c "HttpOnly"))
        (is (str/includes? c "SameSite=Lax"))
        (is (not (str/includes? c "Max-Age")) "a sitting, not a subscription")
        (is (not (str/includes? c "Secure")) "over plain HTTP")
        (is (str/includes? (get-in (app {:request-method :get :uri "/assert" :scheme :https
                                         :headers {}})
                                   [:headers "Set-Cookie"])
                           "; Secure")
            "and Secure over HTTPS")
        (is (str/includes? (get-in (app {:request-method :get :uri "/assert"
                                         :headers {"x-forwarded-proto" "https"}})
                                   [:headers "Set-Cookie"])
                           "; Secure")
            "and Secure behind a proxy that terminated HTTPS")))
    (testing "and the KB is untouched — looking is not writing"
      (is (= before (tu/sentex-ids kb))))
    (testing "the context field is pre-filled with the sandbox, so the safe thing is the
              default rather than a choice the reader has to know to make"
      (is (re-find #"id=\"assert-ctx\"[^>]*value=\"CxSandbox[0-9a-f]+\"" (:body r))))
    (testing "a returning request keeps the same sandbox rather than being handed a new one"
      (let [c  (cookie-of r)
            r2 (app {:request-method :get :uri "/assert" :headers {"cookie" c}})]
        (is (nil? (get-in r2 [:headers "Set-Cookie"])) "no re-mint")
        (is (str/includes? (:body r2)
                           (str (sandbox/context-of {:headers {"cookie" c}}))))))))

(tu/deftest-kb writing-through-the-form-creates-the-sandbox-and-reset-empties-it
  (let [app    (web/app kb)
        before (tu/sentex-ids kb)
        r      (app {:request-method :get :uri "/assert" :headers {}})
        cookie (cookie-of r)
        sbx    (second (re-find #"value=\"(CxSandbox[0-9a-f]+)\"" (:body r)))
        hdrs   {"cookie" cookie "host" "localhost:3000"}
        post   #(app {:request-method :post :uri %1 :params %2 :headers hdrs})]
    (testing "the first write brings the context into being and the rules run in it"
      (let [b (:body (post "/assert" {"text" "(organism SandboxWebRufus)" "ctx" sbx}))]
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

(tu/deftest-kb a-refused-form-leaves-no-sandbox-behind
  ;; the form is refused for what it holds — unreadable, empty, not a sentence, a bad
  ;; name — and the session's sandbox did not exist before it, so none exists after it
  (let [app    (web/app kb)
        before (tu/sentex-ids kb)
        r      (app {:request-method :get :uri "/assert" :headers {}})
        sbx    (second (re-find #"value=\"(CxSandbox[0-9a-f]+)\"" (:body r)))
        hdrs   {"cookie" (cookie-of r) "host" "localhost:3000"}]
    (doseq [text ["(organism SandboxRefused" "" ":oops" "(Bad_Pred SandboxRefused)"]]
      (testing (pr-str text)
        (let [b (:body (app {:request-method :post :uri "/assert"
                             :params {"text" text "ctx" sbx} :headers hdrs}))]
          (is (not (str/includes? b "Stored")))
          (is (not (sandbox/live? kb (symbol sbx))))
          (is (= before (tu/sentex-ids kb))))))))

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
              :params {"text" "(organism SandboxShared)" "ctx" ctx}
              :headers {"cookie" cookie "host" "localhost:3000"}}))
      (testing "each sees only its own writing"
        (is (= 1 (count (v/sentexes-matching kb '(organism SandboxShared) (symbol (:ctx a))))))
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

;; ---- the eviction table ----------------------------------------------------

(def ^:private minute 60000)
(def ^:private day (* 24 60 minute))
(def ^:private t0 (* 1000 minute))

(defn- admit
  "`table` after the browser's admission of fresh sandbox `ctx` at `t` under `cap`, and
  its one write."
  [table ctx t cap]
  (let [[r _] (#'sandbox/room table cap t day)]
    (#'sandbox/wrote (#'sandbox/enter r ctx 0 t) ctx 2 t)))

(defn- used-for
  "`table` with `ctx` entered at `from` and written once a minute for `n` minutes."
  [table ctx from n]
  (reduce (fn [r i] (#'sandbox/wrote r ctx (* 3 (inc i)) (+ from (* i minute))))
          (#'sandbox/enter table ctx 0 from)
          (range n)))

(defn- flood
  "`table` after `n` fresh one-write sandboxes are admitted at `t` under `cap`."
  [table n t cap]
  (reduce (fn [r i] (admit r (symbol (str "CxSandboxFlood" i)) (+ t i) cap)) table (range n)))

(deftest a-sandbox-used-for-twenty-minutes-survives-a-flood-of-fresh-ones
  (let [cap 4
        r   (used-for @#'sandbox/empty-eviction-table 'CxSandboxLong t0 21)
        out (flood r (* 3 cap) (+ t0 (* 20 minute) 1000) cap)]
    (is (contains? (:entries out) 'CxSandboxLong))
    (is (= cap (count (:entries out))))
    (is (zero? (:level out)) "a fresh sandbox is worth 0, so evicting one ages nothing")))

(deftest a-sandbox-idle-past-the-horizon-is-reset-first
  (let [cap 4
        r   (used-for @#'sandbox/empty-eviction-table 'CxSandboxLong t0 21)
        [_ gone] (#'sandbox/room (flood r (dec cap) (+ t0 (* 20 minute)) cap)
                                 cap (+ t0 (* 21 minute) day) day)]
    (is (= ['CxSandboxLong] gone) "whatever its history")))

(deftest of-two-equal-histories-the-more-recently-used-is-kept
  (let [r (-> @#'sandbox/empty-eviction-table
              (used-for 'CxSandboxEarly t0 5)
              (used-for 'CxSandboxLate t0 5)
              (#'sandbox/used 'CxSandboxEarly (+ t0 (* 6 minute)))
              (#'sandbox/used 'CxSandboxLate (+ t0 (* 6 minute) 1)))
        [_ gone] (#'sandbox/room r 2 (+ t0 (* 7 minute)) day)]
    (is (= (get-in r [:entries 'CxSandboxEarly :h]) (get-in r [:entries 'CxSandboxLate :h])))
    (is (= ['CxSandboxEarly] gone))))

(deftest an-eviction-raises-the-level-so-an-unused-sandbox-falls-behind
  (let [r (-> @#'sandbox/empty-eviction-table
              (used-for 'CxSandboxA t0 10)
              (used-for 'CxSandboxB t0 10))
        [r' gone] (#'sandbox/room r 2 (+ t0 (* 11 minute)) day)
        h-before (get-in r [:entries 'CxSandboxB :h])]
    (is (= ['CxSandboxA] gone))
    (is (= (get-in r [:entries 'CxSandboxA :h]) (:level r')))
    (testing "a sandbox used after the eviction restarts from the raised level, so it now
              outranks one of equal history that was not used since"
      (let [r'' (used-for r' 'CxSandboxC (+ t0 (* 11 minute)) 10)]
        (is (< h-before (get-in r'' [:entries 'CxSandboxC :h])))
        (is (= ['CxSandboxB] (second (#'sandbox/room r'' 2 (+ t0 (* 21 minute)) day))))))))

(tu/deftest-kb a-rebuilt-eviction-table-holds-every-live-sandbox-as-fresh
  (let [a (fresh-sandbox) b (fresh-sandbox)]
    (sandbox/open kb a)
    (sandbox/open kb b)
    (try
      (v/assert kb '(organism SandboxRebuilt) a)
      (let [r (#'sandbox/rebuilt kb t0)]
        (is (every? (:entries r) [a b]))
        (is (= (v/count-in-context kb a) (get-in r [:entries a :size])))
        (is (every? zero? (map :h (vals (select-keys (:entries r) [a b]))))
            "activity is not in the KB, so a restart forgets it"))
      (finally (sandbox/reset! kb a) (sandbox/reset! kb b)))))

(defn- live-sandboxes [kb]
  (set (filter #(str/starts-with? (name %) "CxSandbox") (v/contexts kb))))

(tu/deftest-kb a-flood-of-fresh-sessions-leaves-at-most-the-cap
  ;; one instant for every request: `value` counts calendar minutes, so a first session
  ;; whose requests fall either side of a minute boundary is worth more than 0
  (with-redefs [sandbox/max-sandboxes (constantly 3)
                sandbox/now           (constantly (System/currentTimeMillis))]
    (let [app      (web/app kb)
          before   (live-sandboxes kb)
          sessions (vec (repeatedly 8 #(session app)))
          ;; a write slower than the form's wait goes on as a job, and the KB refuses the
          ;; next write until it settles, so each write waits for its job
          write    (fn [{:keys [cookie ctx]} text]
                     (app {:request-method :post :uri "/assert"
                           :params {"text" text "ctx" ctx}
                           :headers {"cookie" cookie "host" "localhost:3000"}})
                     (doseq [{:keys [id]} (jobs/running)] (jobs/wait id)))]
      (try
        (write (first sessions) "(organism SandboxFloodRufus)")
        (let [derived (v/handle-of kb '(mortal SandboxFloodRufus) (symbol (:ctx (first sessions))))]
          (is (nat-int? derived) "the shipped rule concluded into the first sandbox")
          (doseq [s (rest sessions)] (write s "(organism SandboxFloodTibbles)"))
          (is (= 3 (count (remove before (live-sandboxes kb)))))
          (testing "the first sandbox, fresh and least recently used, was reset through the
                    ordinary retraction, so what the rules derived in it went too"
            (is (not (sandbox/live? kb (symbol (:ctx (first sessions))))))
            (is (nil? (v/sentex kb derived)))))
        (finally (doseq [s sessions] (sandbox/reset! kb (symbol (:ctx s)))))))))

(tu/deftest-kb a-form-past-the-sandbox-ceiling-is-refused
  (with-redefs [sandbox/max-sentexes 2]
    (let [app (web/app kb)
          {:keys [cookie ctx]} (session app)
          before (tu/sentex-ids kb)
          b (:body (app {:request-method :post :uri "/assert"
                         :params {"text" "(organism SandboxCeilA)\n(organism SandboxCeilB)\n(organism SandboxCeilC)"
                                  "ctx" ctx}
                         :headers {"cookie" cookie "host" "localhost:3000"}}))]
      (try
        (is (not (str/includes? b "Stored")))
        (is (str/includes? b "past its ceiling of 2"))
        (is (= before (tu/sentex-ids kb)) "and no sandbox was opened for it")
        (finally (sandbox/reset! kb (symbol ctx)))))))
