;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.demo-test
  "The non-monotonicity walkthrough — `/demo`, the page whose only claim is that this is
  the engine and not a story about one.

  Two halves.  The **engine** half pins the three transitions the page narrates, because
  the page is worth nothing if they do not hold: a conclusion nobody asserted, that same
  conclusion *deleted* by learning one more true thing, and that same conclusion
  re-derived at a **different handle** when the new thing is taken back.  The **browser**
  half checks the page says all three out loud, offers the step the KB is actually up to,
  and links records rather than describing them.

  The handle changing is the required assertion.  `exceptWhen` blocks rather than
  rebuts, so a blocked justification is invalid, groundability goes with it, and the
  dependency-directed sweep deletes the conclusion — revival is a re-derivation, not a
  flag being flipped.  A test that only checked belief flipping back would pass against
  an implementation that hid the sentex and un-hid it, which is exactly the thing the
  page promises it is not doing."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.sandbox :as sandbox]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private bird    '(bird Pingu))
(def ^:private penguin '(penguin Pingu))
(def ^:private flies   '(hasCapability Pingu flying))
(def ^:private travel  '(hasCapability Pingu travelling))

(defn- fresh-sandbox [] (sandbox/context-for (sandbox/mint-token)))

;; ---- the three transitions ----------------------------------------------

(tu/deftest-kb the-walkthrough-holds-in-the-engine
  (let [sbx (fresh-sandbox)]
    (sandbox/open kb sbx)
    (try
      (v/assert kb bird sbx)
      (let [h1 (v/handle-of kb flies sbx)]
        (testing "step 1 — a conclusion nobody asserted"
          (is (nat-int? h1) "the shipped flight rule concluded it into the sandbox")
          (is (v/in? kb h1))
          (is (not (v/premise? kb h1)) "derived, not something the reader wrote")
          (is (seq (:support (v/why kb h1))) "and it has a proof"))

        (v/assert kb penguin sbx)
        (testing "step 2 — one more true thing, and the conclusion is *gone*"
          (is (nil? (v/handle-of kb flies sbx)) "not merely OUT — there is no handle")
          (is (nil? (v/sentex kb h1)) "the record itself was swept")
          (is (not (v/ask? kb travel sbx))
              "and the hierarchy answer goes with it — flying gone means travelling unanswerable")
          (let [{:keys [reason rule exception]} (v/why-not kb flies sbx)]
            (is (= :excepted reason) "blocked by the rule's own exception, not defeated")
            (is (nat-int? rule) "which names the rule, so the page can link it")
            (is (= penguin exception) "and the exception, ground at this binding"))
          (is (some? (v/handle-of kb (list 'not flies) sbx))
              "flightlessness is a separate positive claim, not the absence of flight"))

        (v/retract! kb (v/handle-of kb penguin sbx))
        (let [h2 (v/handle-of kb flies sbx)]
          (testing "step 3 — it comes back, and it is not the same record"
            (is (nat-int? h2))
            (is (v/in? kb h2))
            (is (not= h1 h2) "revival is a re-derivation; a flipped flag would reuse the handle")
            (is (nil? (v/sentex kb h1)) "and step 1's handle still resolves to nothing")
            (is (v/ask? kb travel sbx) "and the hierarchy answer returns — travelling answerable again"))
          (testing "the proof is identical, which is the other half of the point"
            (let [rule-of #(-> (v/why kb %) :support first :rule)
                  from-of #(-> (v/why kb %) :support first :because first :handle)]
              (is (= (rule-of h2) '(implies (bird ?x) (hasCapability ?x flying))))
              (is (= (from-of h2) (v/handle-of kb bird sbx)))))))
      (finally (sandbox/reset! kb sbx)))))

;; ---- the page -----------------------------------------------------------

(defn- cookie-of [resp]
  (some-> (get-in resp [:headers "Set-Cookie"]) (str/split #";") first))

(defn- sandbox-of
  "The sandbox the page says it is writing to — read off the page, not computed, so the
  test is checking what a reader would see."
  [body]
  (some-> (re-find #"CxSandbox[0-9a-f]+" body) symbol))

(defn- carried
  "The `first`-handle the page threads through its step forms."
  [body]
  (some-> (re-find #"name=\"first\"[^>]*value=\"(\d+)\"" body) second parse-long))

(defn- open-session
  "Start a session on /demo and answer what the caller needs to drive it."
  [app]
  (let [r (app {:request-method :get :uri "/demo" :headers {}})]
    {:cookie (cookie-of r) :body (:body r) :sandbox (sandbox-of (:body r))}))

(defn- step
  "Run one step as the browser would: a POST carrying the hidden fields the page put in
  the form it is answering."
  [app cookie op prev-body]
  (:body (app {:request-method :post :uri "/demo"
               :params (cond-> {"do" op}
                         (carried prev-body) (assoc "first" (str (carried prev-body))))
               :headers {"cookie" cookie "host" "localhost:3000"}})))

(defn- run-through
  "The whole script, one step after another, answering each step's rendered page."
  [app cookie start-body ops]
  (vec (reductions (fn [b op] (step app cookie op b)) start-body ops)))

(defn- text-of
  "The page as a reader sees it — tags stripped, whitespace flattened.  A rendered
  sentence is a nest of role-coloured links, so a test asking what the page *says* has to
  ask it of the text and not of the markup."
  [body]
  (-> body (str/replace #"<[^>]+>" " ") (str/replace #"\s+" " ")))

(tu/deftest-kb the-front-page-reaches-it-in-one-click
  (let [body (:body ((web/app kb) {:request-method :get :uri "/" :headers {}}))]
    (is (str/includes? body "href=\"/demo\"")
        "the highest-value sixty seconds must not require knowing what to type")))

(tu/deftest-kb looking-at-the-page-writes-nothing
  (let [app    (web/app kb)
        before (tu/sentex-ids kb)
        {:keys [body]} (open-session app)]
    (is (str/includes? body "Not stored, not believed"))
    (is (str/includes? body "Step 1 — Assert (bird Pingu)") "and offers the first step")
    (is (= before (tu/sentex-ids kb)) "a visitor who only reads costs the KB nothing")))

(tu/deftest-kb the-three-steps-run-and-the-page-says-what-happened
  (let [app (web/app kb)
        {:keys [cookie sandbox body]} (open-session app)]
    (try
      (let [b1 (step app cookie "start" body)
            h1 (carried b1)]
        (testing "step 1 shows the conclusion believed, with its proof and its record"
          (is (str/includes? b1 "<b>Believed</b>"))
          (is (nat-int? h1) "and threads the handle it reached forward")
          (is (str/includes? b1 (str "/why/" h1)) "linking the proof")
          (is (str/includes? (text-of b1) "( implies ( bird ?x ) ( hasCapability ?x flying ) )")
              "the rule that concluded it is on the page, not just its name"))

        (let [b2 (step app cookie "except" b1)]
          (testing "step 2 says why, in the engine's own terms"
            (is (str/includes? b2 "<b>Not believed</b>"))
            (is (str/includes? b2 "states its own exception"))
            (is (str/includes? b2 "(penguin Pingu)"))
            (is (str/includes? b2 "sweep deleted"))
            (is (= h1 (carried b2)) "still carrying step 1's handle, which is the point"))

          (let [b3 (step app cookie "restore" b2)
                h2 (v/handle-of kb flies sandbox)]
            (testing "step 3 shows it back, and names the two handles side by side"
              (is (str/includes? b3 "<b>Believed</b>"))
              (is (str/includes? b3 "re-derivation"))
              (is (not= h1 h2))
              (is (str/includes? b3 (str "Step 1 concluded <code>#" h1 "</code>"))
                  "the swept handle is named")
              (is (str/includes? b3 (str "this is <code>#" h2 "</code>"))
                  "beside the one that replaced it"))
            (testing "and it links the new record, never the swept one, as the live link"
              (is (str/includes? b3 (str "href=\"/sentex/" h2 "\"")))
              (is (str/includes? b3 (str "href=\"/why/" h2 "\"")))))))
      (finally (sandbox/reset! kb sandbox)))))

(tu/deftest-kb the-cascade-is-visible-at-every-step
  ;; The page renders every watched sentence at every step: a stored one with its record,
  ;; and travelling with what `ask?` answers, because the capability hierarchy answers it
  ;; at retrieval and stores no record.
  (testing "the page shows what moved, stored and answered alike"
    (let [app (web/app kb)
          {:keys [cookie sandbox body]} (open-session app)
          shows? (fn [b form tag]
                   (some? (re-find (re-pattern (str (java.util.regex.Pattern/quote form)
                                                    " \\) " tag))
                                   (text-of b))))
          travel-row "( hasCapability Pingu travelling"]
      (try
        (let [[_ b1 b2 b3] (run-through app cookie body ["start" "except" "restore"])]
          (is (shows? b1 "( penguin Pingu" "not stored") "before step 2, nothing says Pingu is a penguin")
          (is (shows? b1 travel-row "answerable") "step 1: what flies travels")
          (is (shows? b2 travel-row "unanswerable") "step 2: travelling goes with the flight")
          (is (shows? b3 "( penguin Pingu" "not stored") "and step 3 takes the penguin claim back")
          (is (shows? b3 travel-row "answerable") "so travelling is answerable again"))
        (finally (sandbox/reset! kb sandbox)))))
  (testing "the hierarchy cascade — travelling tracks flying without a stored record"
    (let [sbx (fresh-sandbox)]
      (sandbox/open kb sbx)
      (try
        (v/assert kb bird sbx)
        (is (v/ask? kb travel sbx) "step 1: flying earned → travelling answerable via hierarchy")
        (v/assert kb penguin sbx)
        (is (not (v/ask? kb travel sbx)) "step 2: flying defeated → travelling unanswerable")
        (v/retract! kb (v/handle-of kb penguin sbx))
        (is (v/ask? kb travel sbx) "step 3: flying restored → travelling answerable again")
        (finally (sandbox/reset! kb sbx))))))

(tu/deftest-kb running-it-twice-leaves-no-residue
  (let [app    (web/app kb)
        before (tu/sentex-ids kb)
        justs  (tu/justification-ids kb)]
    (dotimes [_ 2]
      (let [{:keys [cookie sandbox body]} (open-session app)]
        (try
          (dorun (run-through app cookie body ["start" "except" "restore" "reset"]))
          (finally (sandbox/reset! kb sandbox)))))
    (testing "compared as sets, not counts — a run that removed one thing and derived
              another would balance and still have left a trace"
      (is (= before (tu/sentex-ids kb)))
      (is (= justs (tu/justification-ids kb))))))

(tu/deftest-kb the-step-offered-is-read-from-the-kb-not-from-a-counter
  (let [app (web/app kb)
        {:keys [cookie sandbox body]} (open-session app)]
    (try
      (testing "a step whose precondition does not hold writes nothing and does not throw"
        (let [b (step app cookie "restore" body)]
          (is (str/includes? b "Step 1 — Assert (bird Pingu)")
              "the page still offers the step the KB is up to")))
      (testing "and after a real step 1, reloading the page cold lands on step 2"
        (step app cookie "start" body)
        (let [b (:body (app {:request-method :get :uri "/demo"
                             :headers {"cookie" cookie}}))]
          (is (str/includes? b "Step 2 — Assert (penguin Pingu)"))
          (is (str/includes? b "<b>Believed</b>"))))
      (finally (sandbox/reset! kb sandbox)))))

(tu/deftest-kb every-step-writes-so-every-step-is-origin-checked
  (let [app    (web/app kb)
        before (tu/sentex-ids kb)
        {:keys [cookie]} (open-session app)]
    (doseq [op ["start" "except" "restore" "reset"]]
      (is (= 403 (:status (app {:request-method :post :uri "/demo" :params {"do" op}
                                :headers {"cookie" cookie "host" "localhost:3000"
                                          "origin" "http://evil.example"}})))
          (str op " must not be drivable from another site")))
    (is (= before (tu/sentex-ids kb)) "and none of them wrote")))

(tu/deftest-kb two-readers-run-it-independently
  (let [app    (web/app kb)
        before (tu/sentex-ids kb)
        a      (open-session app)
        b      (open-session app)]
    (is (not= (:sandbox a) (:sandbox b)))
    (try
      (let [ba (step app (:cookie a) "start" (:body a))]
        (dorun (run-through app (:cookie b) (:body b) ["start" "except"]))
        (testing "one reader reaching step 2 does not move the other off step 1"
          (is (v/in? kb (carried ba)) "the first reader's conclusion still stands")
          (is (nil? (v/handle-of kb penguin (:sandbox a)))
              "and nothing crossed between the sandboxes")))
      (finally
        (sandbox/reset! kb (:sandbox a))
        (sandbox/reset! kb (:sandbox b))))
    (is (= before (tu/sentex-ids kb)))))
