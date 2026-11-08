;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.web-kbs-test
  "The browser's knowledge-bases page: what it lists, what its controls do, and the one
  property the whole feature exists for — activating another entry re-points every other
  page at it, with no restart."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.access :as access]
            [vaelii.browser.catalog :as catalog]
            [vaelii.browser.jobs :as jobs]
            [vaelii.browser.web :as web]
            [vaelii.client :as vc]
            [vaelii.core :as v]
            [vaelii.host.io.generate :as generate]
            [vaelii.host.starter :as starter]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.protocols :as p]
            [vaelii.test-util :as tu])
  (:import [java.io ByteArrayInputStream]
           [org.eclipse.jetty.server Server ServerConnector]))

(def ^:dynamic *app* nil)

;; The browser is built against a **holder**, not a KB — that is the switch.  The
;; fallback KB stands in for the one `-main` starts with.
(use-fixtures :each
  (fn [f]
    (catalog/reset-registry!)
    (let [kb (doto (tu/empty-kb) tu/load-core!)]
      (catalog/register! "base" "Base KB" kb {:source (catalog/source "core")})
      (binding [tu/*kb* kb, *app* (web/app (catalog/holder kb))]
        (try (f) (finally (catalog/reset-registry!) (tu/clear-kb! kb)))))))

(defn- GET [uri & [qs]]
  (*app* (cond-> {:request-method :get :uri uri} qs (assoc :query-string qs))))

(defn- POST [uri params & [headers]]
  (*app* {:request-method :post :uri uri :params params :headers (or headers {})}))

(defn- settled []
  (let [deadline (+ (System/currentTimeMillis) (tu/load-budget-ms))]
    (while (and (catalog/loading?) (< (System/currentTimeMillis) deadline))
      (Thread/sleep 20))))

;; ---- what the page shows -------------------------------------------------

(deftest the-page-lists-what-is-loaded-and-what-can-be
  (let [body (:body (GET "/kbs"))]
    (is (= 200 (:status (GET "/kbs"))))
    (testing "the loaded KB, with the counts and the active marker"
      (is (re-find #"Base KB" body))
      (is (re-find #"tag-done" body))
      (is (re-find #"active" body)))
    (testing "and every source the catalog offers, each with its own controls"
      (is (re-find #"Starter ontology" body))
      (is (re-find #"Generated corpus" body))
      (is (re-find #"Forward-chain after loading" body)))))

(deftest the-generator-renders-one-slider-per-knob
  (let [body (:body (GET "/kbs"))]
    (testing "every knob the generator documents becomes a control, so the page and the
              generator cannot disagree about a range or a default"
      (doseq [{:keys [key label]} generate/knobs]
        (is (re-find (re-pattern (str "data-knob=\"" (name key) "\"")) body)
            (str "slider for " label))))
    (testing "a slider carries the mapping vaelii.js needs to turn a position into a value"
      (is (re-find #"data-log=\"1\"" body))
      (is (re-find #"type=\"range\"" body)))
    (testing "and the value the form submits is its own field, not the track position"
      (is (re-find #"data-knob-value=\"facts\"" body)))))

(deftest the-header-says-which-kb-every-other-page-is-about
  (let [body (:body (GET "/"))]
    (is (re-find #"href=\"/kbs\"" body))
    (is (re-find #"id=\"kb-label\"" body))
    (is (re-find #"Base KB" body))))

;; ---- loading, switching, unloading --------------------------------------

(deftest loading-from-the-page-starts-a-load-and-shows-its-progress
  (let [r (POST "/kbs/load" {"id" "generated" "types" "10" "individuals" "10"
                             "facts" "10" "rules" "2" "predicates" "6" "layers" "2"
                             "contexts" "1" "branching" "3" "forward" "50"
                             "defeasible" "0" "antecedents" "2" "seed" "1" "base" "core"})]
    (is (= 200 (:status r)))
    (settled)
    (testing "the entry is listed, and the polling fragment is a fragment"
      (let [rows (GET "/kbs/rows")]
        (is (= 200 (:status rows)))
        (is (re-find #"id=\"kb-entries\"" (:body rows)))
        (is (re-find #"generated#1" (:body rows)))))
    (testing "the poll stops asking once no load is running — the trigger is the server's
              to include, so an idle page is not a request per second"
      (is (not (re-find #"hx-trigger=\"every" (:body (GET "/kbs/rows")))))))
  (testing "the slider values actually reached the generator"
    (settled)
    (is (= 10 (:types (:params (catalog/entry "generated#1")))))
    (is (= 2 (:rules (:params (catalog/entry "generated#1")))))))

(deftest switching-re-points-every-other-page
  (POST "/kbs/load" {"id" "generated" "types" "6" "individuals" "6" "facts" "6"
                     "rules" "1" "predicates" "4" "layers" "2" "contexts" "1"
                     "branching" "3" "forward" "0" "defeasible" "0" "antecedents" "2"
                     "seed" "1" "base" "core"})
  (settled)
  (testing "before the switch the ontology page is about the KB the browser started on"
    (is (not (re-find #"gen_type_0" (:body (GET "/"))))))
  (POST "/kbs/activate" {"key" "generated#1"})
  (testing "after it, the same page is about the generated one — the handler was never
            rebuilt, it reads the holder per request"
    (is (= "generated#1" (catalog/active)))
    (is (re-find #"gen_type_0" (:body (GET "/"))))
    (is (re-find #"CxGenerated" (:body (GET "/stats")))))
  (testing "and the header's label moved with it"
    (is (re-find #"Generated corpus" (:body (GET "/kbs"))))))

(deftest unloading-hands-the-browser-back-to-what-is-left
  (POST "/kbs/load" {"id" "generated" "types" "6" "individuals" "6" "facts" "6"
                     "rules" "1" "predicates" "4" "layers" "2" "contexts" "1"
                     "branching" "3" "forward" "0" "defeasible" "0" "antecedents" "2"
                     "seed" "1" "base" "core"})
  (settled)
  (POST "/kbs/activate" {"key" "generated#1"})
  (let [r (POST "/kbs/unload" {"key" "generated#1"})]
    (is (= 200 (:status r)))
    (is (nil? (catalog/entry "generated#1")))
    (is (= "base" (catalog/active)))
    (testing "and the pages answer from the KB that is left, not from a torn-down one"
      (is (= 200 (:status (GET "/")))))))

(deftest a-second-starter-open-releases-the-first-and-shares-no-stores-with-it
  (with-redefs [starter/load-into (fn [kb] (v/assert kb '(genl starter_probe thing) 'CxUniverse))]
    (let [{kb1 :kb} (#'web/opening-kb nil)
          _         (catalog/activate "starter")
          {kb2 :kb} (#'web/opening-kb nil)
          h         (v/assert kb2 '(genl second_starter_probe thing) 'CxUniverse)]
      (is (= [true nil "starter" true]
             [(catalog/released? kb1) (p/get-sentex (:records kb1) h) (catalog/active)
              (identical? kb2 (:kb (catalog/entry "starter")))])))))

(deftest the-starter-dump-property-restores-the-starter-and-its-absence-loads-it
  (tu/with-tmp
    (fn [root]
      (let [loads (atom 0)
            where {:backend :memory :space [::dump-property]}]
        (with-redefs [starter/load-into           (fn [kb]
                                                    (swap! loads inc)
                                                    (v/assert kb '(genl starter_probe thing)
                                                              'CxUniverse))
                      starter/edited-since-start? (constantly false)]
          (web/fresh-starter-kb! where)
          (is (= [1 0] [@loads (count (.list (io/file root)))]) "unset reads and writes no dump")
          (System/setProperty "vaelii.starter.dump" (str root))
          (try
            (web/fresh-starter-kb! where)
            (let [kb (web/fresh-starter-kb! where)]
              (is (= 2 @loads) "the first start writes the dump and the second reads it")
              (is (v/handle-of kb '(genl starter_probe thing) 'CxUniverse)))
            (finally (System/clearProperty "vaelii.starter.dump"))))))))

(deftest a-dev-repl-refused-by-a-job-writing-the-starter-leaves-the-running-server
  (with-redefs [starter/load-into    (fn [kb] (v/assert kb '(genl starter_probe thing) 'CxUniverse))
                web/console-logging! (fn [])]
    (let [{kb :kb} (#'web/opening-kb nil)
          server   (Server.)
          held     (promise)
          release  (promise)
          id       (jobs/submit {:label "Chain starter" :kind :chain :writes kb}
                                (fn [_] (deliver held true) (deref release 60000 nil)))]
      (reset! @#'web/dev-instance server)
      (try
        (deref held 10000 nil)
        (is (= [:still-writing server]
               [(:type (ex-data (try (web/dev-repl) nil (catch Exception e e))))
                @@#'web/dev-instance]))
        (finally
          (deliver release true)
          (jobs/wait id 10000)
          (reset! @#'web/dev-instance nil))))))

(deftest an-unload-during-a-chain-answers-without-waiting-for-it
  ;; A chaining job holds the process-wide write monitor for its whole run.  This job
  ;; stands in for one: it claims the KB as its writer and holds the monitor until
  ;; `release` is delivered.
  (let [kb      tu/*kb*
        other   (tu/isolated-fresh)
        monitor @#'web/write-monitor
        release (promise)
        held    (promise)
        id      (jobs/submit {:label "Chain base" :kind :chain :writes kb}
                             (fn [_] (locking monitor (deliver held true) (deref release 60000 nil))))]
    (catalog/register! "other" "Other KB" other)
    (try
      (deref held 10000 nil)
      (testing "unloading the KB the chain writes answers with a refusal naming the job"
        (let [r (deref (future (POST "/kbs/unload" {"key" "base"})) 5000 ::parked)]
          (is (not= ::parked r) "the unload waited for the chain")
          (is (= 200 (:status r)))
          (is (re-find #"being written by Chain base" (str (:body r)))))
        (is (some? (catalog/entry "base")) "and nothing was released"))
      (testing "an unload of another KB waits for the monitor without holding the catalog's,
                so a load asked for meanwhile answers"
        (let [u (future (POST "/kbs/unload" {"key" "other"}))]
          (Thread/sleep 200)
          (let [l (deref (future (POST "/kbs/load" {"id" "core"})) 5000 ::parked)]
            (is (not= ::parked l) "the load waited behind the parked unload")
            (is (= 200 (:status l))))
          (deliver release true)
          (is (= 200 (:status (deref u 10000 nil))))
          (is (nil? (catalog/entry "other")))))
      (finally
        (deliver release true)
        (jobs/wait id 10000)
        (tu/clear-kb! other)))))

(deftest a-refused-load-is-reported-on-the-page
  (testing "loading what is already loaded is a state the page shows, not an error status"
    (let [r (POST "/kbs/load" {"id" "core"})]
      (settled)
      (let [r2 (POST "/kbs/load" {"id" "core"})]
        (is (= 200 (:status r)))
        (is (= 200 (:status r2)))
        (is (re-find #"already loaded" (:body r2)))))))

(deftest a-choice-the-option-does-not-offer-is-refused-rather-than-loaded
  ;; A `:choice` reaches `keyword` and then a reader's `case`, so a value nothing offers
  ;; takes that reader's own default in silence — at a setting nobody chose, on the one
  ;; action here nobody watches finish.  Refused at the entry point instead, in the shape every
  ;; other catalog refusal takes: a 200 carrying the note, since an error status is a
  ;; swap htmx never makes.
  (let [r (POST "/kbs/load" {"id" "generated" "types" "6" "individuals" "6" "facts" "6"
                             "rules" "1" "predicates" "4" "layers" "2" "contexts" "1"
                             "branching" "3" "forward" "0" "defeasible" "0"
                             "antecedents" "2" "seed" "1" "base" "no-such-vocabulary"})]
    (settled)
    (is (= 200 (:status r)))
    (is (re-find #"no such base" (:body r)) "the note names the field and the value")
    (is (re-find #"core, starter" (:body r)) "and what the option does offer")
    (is (nil? (catalog/entry "generated#1")) "nothing was loaded"))
  (testing "and the accepted set is the option's own, so the legal spellings still pass"
    (let [ok (POST "/kbs/load" {"id" "generated" "types" "6" "individuals" "6"
                                "facts" "6" "rules" "1" "predicates" "4" "layers" "2"
                                "contexts" "1" "branching" "3" "forward" "0"
                                "defeasible" "0" "antecedents" "2" "seed" "1"
                                "base" "core"})]
      (settled)
      (is (= 200 (:status ok)))
      (is (some? (catalog/entry "generated#1")) "a spelling the option offers loads"))))

;; ---- the writes are writes ----------------------------------------------

(deftest the-three-controls-are-post-only-and-origin-checked
  (doseq [uri ["/kbs/load" "/kbs/unload" "/kbs/activate"]]
    (testing (str uri " refuses a cross-origin caller")
      (is (= 403 (:status (POST uri {"id" "core" "key" "base"}
                            {"host" "localhost:3000" "origin" "http://evil.example"})))))
    (testing (str uri " is not reachable by navigation")
      ;; a POST-only route answers a GET with 405, the same as `/chain`: changing which
      ;; KB this process holds is a write, and a write is never a link
      (is (= 405 (:status (GET uri)))))))

(deftest a-write-lands-on-the-kb-its-refusal-judged-not-on-one-activated-under-it
  ;; `/kbs/activate` takes no monitor, and an entry still loading is activatable by
  ;; design — so the holder can be re-pointed between a write entry point's refusal and its
  ;; write.  The entry point derefs the holder once and hands that KB to both halves; this
  ;; lands the switch exactly in the gap (the refusal's own `write-blocked?` read is
  ;; where it fires) and asks which KB took the fact.  Written through the second deref,
  ;; the fact lands on a KB the refusal never judged — one whose loader may be this
  ;; process's writer.
  (let [other (doto (tu/isolated-fresh) tu/load-core!)
        ctx   (tu/tmp-ctx "Switch")
        s     (list 'likes 'Tom 'Ann)]
    (catalog/register! "other" "Other KB" other {:source (catalog/source "core")})
    (try
      (is (= "base" (catalog/active)))
      (with-redefs [catalog/write-blocked? (fn [_] (catalog/activate "other") false)]
        (is (= 200 (:status (POST "/assert" {"text" (pr-str s) "ctx" (str ctx)})))))
      (is (= "other" (catalog/active)) "the switch landed between the refusal and the write")
      (is (some? (v/handle-of tu/*kb* s ctx)) "the KB the refusal judged is the KB written")
      (is (nil? (v/handle-of other s ctx)) "and the one activated under it took nothing")
      (finally
        (catalog/activate "base")
        (tu/clear-kb! other)))))

(deftest a-refusal-names-the-kb-it-judged-not-the-one-activated-under-it
  ;; The same gap, one step later.  An entry point that resolves the holder once and then renders
  ;; `(active-kb-name)` reports the refusal against whatever `/kbs/activate` pointed at
  ;; while the page was being built — which, on this path, is by construction the one KB
  ;; the refusal is not about.  Each arm lands the switch inside its own read.
  (let [other (doto (tu/isolated-fresh) tu/load-core!)
        ctx   (tu/tmp-ctx "Named")
        s     (list 'likes 'Tom 'Ann)
        POST! #(:body (POST "/assert" {"text" (pr-str s) "ctx" (str ctx)}))
        switch (fn [answer] (fn [& _] (catalog/activate "other") answer))]
    (catalog/register! "other" "Other KB" other {:source (catalog/source "core")})
    (try
      (doseq [[label redefs pattern]
              [["a job holds the writer"
                {#'catalog/write-blocked? (switch true)}
                #"<b>Base KB</b> is being written by"]
               ["an export is walking it"
                {#'catalog/write-blocked? (constantly false)
                 #'catalog/exporting-kb?  (switch true)}
                #"<b>Base KB</b> is being exported"]
               ["its belief was never rebuilt"
                {#'catalog/write-blocked? (constantly false)
                 #'catalog/exporting-kb?  (constantly false)
                 #'kb/write-hazards       (switch {:no-index true})}
                #"<b>Base KB</b> is stored but not built"]]]
        (catalog/activate "base")
        (let [body (with-redefs-fn redefs POST!)]
          (is (= "other" (catalog/active))
              (str label ": the switch landed while the refusal was being rendered"))
          (is (re-find pattern body) (str label ": the refusal names the KB it judged"))
          (is (not (re-find #"<b>Other KB</b> is (being|stored)" body))
              (str label ": and not the one activated under it"))))
      (finally
        (catalog/activate "base")
        (tu/clear-kb! other)))))

(deftest an-unloaded-kb-cannot-be-reached-by-the-pages
  (testing "unloading the only KB leaves the holder's fallback, so the browser still
            answers rather than throwing on a nil KB"
    (POST "/kbs/unload" {"key" "base"})
    (is (nil? (catalog/active)))
    (is (= 200 (:status (GET "/kbs"))))
    (is (= 200 (:status (GET "/"))))))

;; ---- what reaches a KB after its release ---------------------------------

(defn- op
  "`POST /op` with `form` as its EDN body, and the reply read back into `:edn`."
  [form]
  (let [r (*app* {:request-method :post :uri "/op"
                  :headers {"content-type" "application/edn"}
                  :body (ByteArrayInputStream. (.getBytes (pr-str form) "UTF-8"))})]
    (assoc r :edn (edn/read-string (:body r)))))

(deftest an-op-kb-diff-names-a-catalog-entry-and-loads-nothing
  (tu/with-terms [dog Rex CxDiffEntry]
    (let [other (tu/isolated-fresh)]
      (try
        (tu/load-core! other)
        (v/assert other (list dog Rex) CxDiffEntry)
        (catalog/register! "other" "Other KB" other)
        (let [entries (count (catalog/entries))
              r       (op {:op :kb-diff :args ["other"]})]
          (testing "the active entry diffs against the entry the key names"
            (is (= 200 (:status r)))
            (is (some #(= (list dog Rex) (:sentence %)) (:added (:result (:edn r))))))
          (is (= entries (count (catalog/entries))) "and the catalog holds no new entry"))
        (testing "a key naming no entry is a path, and a path is refused"
          (is (= [403 :path-not-served]
                 ((juxt :status (comp :type :edn)) (op {:op :kb-diff :args ["no-such"]})))))
        (finally (tu/clear-kb! other))))))

(defn- late-kb!
  "A memory KB registered as entry \"late\" with a release to perform, and active."
  []
  (let [kb (tu/isolated-fresh)]
    (catalog/register! "late" "Late KB" kb {:where {:backend :memory}})
    (catalog/activate "late")
    kb))

(defn- parked-behind-an-unload
  "Run `request` on its own thread while this thread holds the browser's write monitor,
  as a chain on another KB does.  Once `request`'s op is blocked entering the monitor, and
  so past every refusal read outside it, unload entry `key` from this thread: the monitor
  is reentrant, so the unload runs to completion before the op enters.  Answers what
  `request` answered."
  [key request]
  (let [monitor @#'web/write-monitor
        out     (promise)
        ^Runnable run (bound-fn [] (deliver out (try (request) (catch Throwable e e))))
        t       (Thread. run)]
    (locking monitor
      (.start t)
      (is (tu/await-blocked-on monitor 10000) "the request is parked on the write monitor")
      (is (= 200 (:status (POST "/kbs/unload" {"key" key}))))
      (is (nil? (catalog/entry key)) "and the unload released the entry"))
    (deref out 10000 ::no-answer)))

(deftest a-write-parked-on-the-monitor-does-not-land-on-a-kb-unloaded-before-it
  (tu/with-terms [likesOf Ann Bob]
    (testing "an op answers 404 :not-found and stores nothing"
      (let [kb (late-kb!)
            r  (parked-behind-an-unload
                "late" #(op {:op :assert :args [(list likesOf Ann Bob) 'CxUniverse]}))]
        (is (= [404 :not-found] [(:status r) (get-in r [:edn :type])]))
        (is (zero? (v/sentex-count kb)))))
    (testing "a :watch answers 404 :not-found and registers no listener"
      (let [kb (late-kb!)
            r  (parked-behind-an-unload "late" #(op {:op :watch :args []}))]
        (is (= [404 :not-found] [(:status r) (get-in r [:edn :type])]))
        (is (empty? (v/watchers kb)))))
    ;; a page write is an `:edit` job: it claims the KB's writer before it waits for the
    ;; monitor, so the unload arriving behind it is refused as `:still-writing`, the way
    ;; it is for a chain, and the write lands on the KB that is still loaded
    (testing "a page write holds the writer, so the unload is refused and the write lands"
      (let [kb      (late-kb!)
            monitor @#'web/write-monitor
            out     (promise)
            ^Runnable run (bound-fn []
                            (deliver out (try (POST "/assert" {"text" (pr-str (list likesOf Ann Bob))
                                                               "ctx"  "CxUniverse"})
                                              (catch Throwable e e))))
            t       (Thread. run)]
        (locking monitor
          (.start t)
          (is (tu/await-blocked-on monitor 10000) "the write's job is parked on the monitor")
          (is (= 200 (:status (POST "/kbs/unload" {"key" "late"}))))
          (is (some? (catalog/entry "late")) "and the unload left the entry in place"))
        (is (= 200 (:status (deref out 10000 ::no-answer))))
        (is (= 1 (v/sentex-count kb)) "the write landed on the KB still loaded")
        (catalog/unload! "late")))))

(deftest a-chain-whose-kb-is-unloaded-before-its-job-is-submitted-does-not-run
  ;; `/chain` reads its refusals and then submits; an unload landing between the two finds
  ;; no job writing the KB and releases it.  The redefined submit stages that order.
  (let [_       (late-kb!)
        submit  jobs/submit
        id      (atom nil)
        chained (atom 0)]
    (with-redefs [jobs/submit     (fn [spec work]
                                    (when (= :chain (:kind spec))
                                      (is (= 200 (:status (POST "/kbs/unload" {"key" "late"})))))
                                    (reset! id (submit spec work)))
                  access/forward-chain (fn [& _] (swap! chained inc) {:derived 0})]
      (POST "/chain" {})
      (jobs/wait @id 10000))
    (is (nil? (catalog/entry "late")))
    (is (zero? @chained) "the chain never ran over the released KB")
    (is (= :failed (:status (jobs/job @id))))
    (is (re-find #"unloaded" (str (:error (jobs/job @id)))))))

(deftest an-unload-ends-the-feeds-over-its-kb
  (let [kb     (late-kb!)
        token  (get-in (op {:op :watch :args []}) [:edn :result :token])
        parked (future (op {:op :poll :args [token 0 {:wait-ms 20000}]}))
        reg    @#'web/op-registry
        until  (+ (System/currentTimeMillis) 10000)]
    (while (and (zero? (:parked @reg)) (< (System/currentTimeMillis) until))
      (Thread/sleep 5))
    (is (= 1 (:parked @reg)) "the poll is parked")
    (is (= 1 (count (v/watchers kb))))
    (POST "/kbs/unload" {"key" "late"})
    (let [r (deref parked 1000 ::still-parked)]
      (is (not= ::still-parked r) "the parked poll is woken, not left to its deadline")
      (is (= :unknown-subscription (get-in r [:edn :type]))))
    (is (empty? (v/watchers kb)) "the listener is off the released KB")
    (is (= :unknown-subscription (get-in (op {:op :poll :args [token 0]}) [:edn :type]))
        "and a later poll of the token is refused")))

(deftest a-stopped-server-ends-the-feeds-it-served
  (let [kb     tu/*kb*
        before (count (v/watchers kb))
        ^Server server (web/start (catalog/holder kb) {:port 0 :token nil})
        conn   (vc/client "localhost" (.getLocalPort ^ServerConnector (first (.getConnectors server)))
                          {:token nil})
        token  (:token (vc/watch conn))
        parked (future (try (vc/poll conn token 0 {:wait-ms 20000}) (catch Exception _ nil)))
        reg    @#'web/op-registry
        within (fn [ms pred]
                 (let [until (+ (System/currentTimeMillis) ms)]
                   (while (and (not (pred)) (< (System/currentTimeMillis) until))
                     (Thread/sleep 5))
                   (pred)))]
    (is (within 10000 #(= 1 (:parked @reg))) "the poll is parked")
    (is (= (inc before) (count (v/watchers kb))))
    (.stop server)
    (deref parked 10000 nil)
    (is (= [true before] [(within 5000 #(zero? (:parked @reg))) (count (v/watchers kb))])
        "the parked poll stopped waiting, and the listener is off the KB")))

;; ---- and back out again --------------------------------------------------

(defn- exported []
  (let [deadline (+ (System/currentTimeMillis) (tu/load-budget-ms))]
    (while (and (catalog/exporting?) (< (System/currentTimeMillis) deadline))
      (Thread/sleep 20))))

(deftest the-page-exports-the-active-kb-under-the-write-root-and-offers-what-it-wrote
  (let [root (io/file (System/getProperty "java.io.tmpdir")
                      (str "vaelii-web-export-" (System/nanoTime)))
        prop (System/getProperty "vaelii.kb.path")]
    (try
      (.mkdirs root)
      (System/setProperty "vaelii.kb.path" (.getAbsolutePath root))
      (testing "the control names the KB it would write, where, and the knobs the writer takes"
        (let [body (:body (GET "/kbs"))]
          (is (re-find #"id=\"kb-export\"" body))
          (is (re-find #"hx-post=\"/kbs/export\"" body))
          (is (not (re-find #"name=\"dir\"" body)) "a request names no destination")
          (is (str/includes? body (.getAbsolutePath root)))
          (is (re-find #"name=\"variant\"" body))
          (is (re-find #"records\+index" body))
          (is (re-find #"Base KB" body))))
      (let [r (POST "/kbs/export" {"compression" "none"})]
        (is (= 200 (:status r)))
        (exported)
        (let [[dump :as written] (vec (.listFiles root))]
          (is (= 1 (count written)) "one directory, under the write root")
          (testing "the job's report is the panel's, and it says where the dump went"
            (let [body (:body (GET "/kbs/export/rows"))]
              (is (re-find #"tag-done" body))
              (is (str/includes? body (.getAbsolutePath ^java.io.File dump)))
              (is (re-find #"sentexes" body))))
          (testing "the poll stops on its own once nothing is running"
            (is (not (re-find #"hx-trigger=\"every" (:body (GET "/kbs/export/rows"))))))
          (testing "and the loop is closed: what was written is offered as a source"
            (is (= :dump (catalog/classify dump)))
            (is (some #(= (.getName ^java.io.File dump) (:name %)) (catalog/sources)))
            (is (re-find #"Offered below" (:body (GET "/kbs")))))))
      (testing "a request naming a destination is refused on the page and writes nothing"
        (let [named (io/file root "named")
              r     (POST "/kbs/export" {"dir" (.getPath named)})]
          (is (= 200 (:status r)))
          (is (re-find #"names no directory" (:body r)))
          (is (not (.exists named)))
          (is (false? (catalog/exporting?)))))
      (testing "VAELII_REQUEST_PATHS lets a request name one, and the writer's refusal shows"
        (with-redefs [catalog/request-paths? (constantly true)]
          (is (re-find #"name=\"dir\"" (:body (GET "/kbs"))))
          (let [taken (first (.listFiles root))]
            (POST "/kbs/export" {"dir" (.getPath ^java.io.File taken)})
            (exported)
            (is (re-find #"is not empty" (:body (GET "/kbs/export/rows")))))))
      (finally
        (if prop (System/setProperty "vaelii.kb.path" prop) (System/clearProperty "vaelii.kb.path"))
        (doseq [f (reverse (file-seq root))] (.delete ^java.io.File f))))))

(deftest a-load-naming-a-directory-is-refused-and-starts-nothing
  (let [dir (io/file (System/getProperty "java.io.tmpdir")
                     (str "vaelii-web-load-" (System/nanoTime)))
        n   (count (catalog/entries))
        r   (POST "/kbs/load" {"id" "core" "dir" (.getPath dir)})]
    (is (= 200 (:status r)))
    (is (re-find #"names no directory" (:body r)))
    (is (= n (count (catalog/entries))))
    (is (not (.exists dir)))))

(deftest a-loaded-dump-is-a-card-the-page-draws
  ;; an import's summary accounts for its refused frames as a map, where the card's
  ;; count line once read a number, so every dump load left `/kbs` answering 500
  (let [dump (io/file (System/getProperty "java.io.tmpdir")
                      (str "vaelii-web-dump-" (System/nanoTime)))]
    (try
      (v/export! tu/*kb* (.getPath dump))
      (catalog/load-dir (.getPath dump) {})
      (settled)
      (is (map? (:refused (:summary (catalog/entry (catalog/active)))))
          "the shape the card has to read")
      (doseq [uri ["/kbs" "/kbs/rows"]]
        (let [r (GET uri)]
          (is (= 200 (:status r)) uri)
          (is (re-find #"vaelii-web-dump-\d+" (:body r)) uri)))
      (finally
        (doseq [f (reverse (file-seq dump))] (.delete ^java.io.File f))))))

(deftest the-export-controls-are-post-only-and-origin-checked
  (doseq [uri ["/kbs/export" "/kbs/export/cancel"]]
    (testing (str uri " refuses a cross-origin caller")
      (is (= 403 (:status (POST uri {"dir" "/tmp/vaelii-nowhere"}
                            {"host" "localhost:3000" "origin" "http://evil.example"})))))
    (testing (str uri " is not reachable by navigation")
      (is (= 405 (:status (GET uri))))))
  (testing "a named destination writes nothing, and says so on the page"
    (let [r (POST "/kbs/export" {"dir" "/tmp/vaelii-nowhere"})]
      (is (= 200 (:status r)))
      (is (re-find #"names no directory" (:body r)))
      (is (false? (catalog/exporting?))))))

;; ---- what it costs to hold ----------------------------------------------

(deftest the-page-heads-the-loaded-list-with-what-this-process-is-holding
  (let [body (:body (GET "/kbs"))]
    (testing "the strip: the measured heap, and the estimated cost of what is loaded"
      (is (re-find #"id=\"kb-memory\"" body))
      (is (re-find #"heap " body))
      (is (re-find #"hx-get=\"/kbs/memory\?detail=1\"" body)
          "clicking it asks for the breakdown"))
    (testing "and each KB carries its own estimate, marked as one"
      (is (re-find #"tag-est" body))
      (is (re-find #"class=\"est\">≈ " body)))))

(deftest the-breakdown-is-a-fragment-that-collapses-again
  (let [detail (GET "/kbs/memory" "detail=1")
        strip  (GET "/kbs/memory")]
    (is (= 200 (:status detail)))
    (is (re-find #"kb-mem-table" (:body detail)))
    (is (re-find #"Base KB" (:body detail)) "a row per loaded KB")
    (testing "the expanded panel offers the way back, and the collapsed one does not
              pretend to be expanded"
      (is (re-find #"hx-get=\"/kbs/memory\"" (:body detail)))
      (is (not (re-find #"kb-mem-table" (:body strip)))))
    (testing "it is a read of this process, so it needs no KB and never scans one"
      (POST "/kbs/unload" {"key" "base"})
      (is (= 200 (:status (GET "/kbs/memory" "detail=1")))))))

(deftest the-strip-refreshes-at-the-state-it-is-in-and-only-the-line-toggles
  (testing "the header line is the toggle: it fetches the state the panel is *not* in"
    (is (re-find #"kb-mem-line\" hx-get=\"/kbs/memory\?detail=1\"" (:body (GET "/kbs/memory")))
        "collapsed, the line offers the breakdown")
    (is (re-find #"kb-mem-line\" hx-get=\"/kbs/memory\"" (:body (GET "/kbs/memory" "detail=1")))
        "expanded, the line offers the way back"))
  (testing "while a load runs the panel polls *itself*, at the state it is in — a
            breakdown left open stays open.  One element carrying both would poll the
            toggle URL and flip the breakdown open and shut every two seconds."
    (with-redefs [catalog/loading? (constantly true)]
      (let [detail (:body (GET "/kbs/memory" "detail=1"))
            strip  (:body (GET "/kbs/memory"))]
        (is (re-find #"kb-memory\" hx-get=\"/kbs/memory\?detail=1\"[^>]*hx-trigger=\"every 2s\"" detail)
            "expanded, the poll asks for expanded")
        (is (re-find #"kb-memory\" hx-get=\"/kbs/memory\"[^>]*hx-trigger=\"every 2s\"" strip)
            "collapsed, the poll asks for collapsed")
        (is (re-find #"kb-mem-table" detail) "and the answer is still the expanded one")
        (is (= 1 (count (re-seq #"every 2s" detail)))
            "one poller in the panel, and it is not the toggle"))))
  (testing "idle, nothing polls at all — the trigger is the server's to include"
    (is (not (re-find #"every 2s" (:body (GET "/kbs/memory")))))
    (is (not (re-find #"every 2s" (:body (GET "/kbs/memory" "detail=1")))))))

(deftest the-catalog-page-costs-no-kb-scan
  (testing "the listing reads counts that were computed once, when each KB loaded — a
            page that summed a corpus per page render would be unusable at eleven million"
    (let [e (catalog/entry "base")]
      (is (= (v/sentex-count tu/*kb*) (:sentexes (:stats e)))))))
