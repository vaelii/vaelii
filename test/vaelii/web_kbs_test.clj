;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.web-kbs-test
  "The browser's knowledge-bases page: what it lists, what its controls do, and the one
  property the whole feature exists for — activating another entry re-points every other
  page at it, with no restart."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.catalog :as catalog]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.host.io.generate :as generate]
            [vaelii.impl.kb :as kb]
            [vaelii.test-util :as tu]))

(def ^:dynamic *app* nil)

;; The browser is built against a **holder**, not a KB — that is the switch.  The
;; fallback KB stands in for the one `-main` starts with.
(use-fixtures :each
  (fn [f]
    (catalog/reset-registry!)
    (let [kb (doto (tu/fresh) core-context/load-into)]
      (catalog/register! "base" "Base KB" kb {:source (catalog/source "core")})
      (binding [tu/*kb* kb, *app* (web/app (catalog/holder kb))]
        (try (f) (finally (catalog/reset-registry!) (tu/clear-kb! kb)))))))

(defn- GET [uri & [qs]]
  (*app* (cond-> {:request-method :get :uri uri} qs (assoc :query-string qs))))

(defn- POST [uri params & [headers]]
  (*app* {:request-method :post :uri uri :params params :headers (or headers {})}))

(defn- settled []
  (let [deadline (+ (System/currentTimeMillis) 120000)]
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
  (testing "and the roster is the option's own, so the legal spellings still pass"
    (let [ok (POST "/kbs/load" {"id" "generated" "types" "6" "individuals" "6"
                                "facts" "6" "rules" "1" "predicates" "4" "layers" "2"
                                "contexts" "1" "branching" "3" "forward" "0"
                                "defeasible" "0" "antecedents" "2" "seed" "1"
                                "base" "starter"})]
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
  (let [other (doto (tu/isolated-fresh) core-context/load-into)
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
  (let [other (doto (tu/isolated-fresh) core-context/load-into)
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

;; ---- and back out again --------------------------------------------------

(defn- exported []
  (let [deadline (+ (System/currentTimeMillis) 120000)]
    (while (and (catalog/exporting?) (< (System/currentTimeMillis) deadline))
      (Thread/sleep 20))))

(deftest the-page-exports-the-active-kb-and-offers-what-it-wrote
  (let [root (io/file (System/getProperty "java.io.tmpdir")
                      (str "vaelii-web-export-" (System/nanoTime)))
        dump (io/file root "browser-dump")
        prop (System/getProperty "vaelii.kb.path")]
    (try
      (.mkdirs root)
      (System/setProperty "vaelii.kb.path" (.getAbsolutePath root))
      (testing "the control names the KB it would write and the three knobs the writer takes"
        (let [body (:body (GET "/kbs"))]
          (is (re-find #"id=\"kb-export\"" body))
          (is (re-find #"hx-post=\"/kbs/export\"" body))
          (is (re-find #"name=\"dir\"" body))
          (is (re-find #"name=\"variant\"" body))
          (is (re-find #"records\+index" body))
          (is (re-find #"Base KB" body))))
      (let [r (POST "/kbs/export" {"dir" (.getPath dump) "compression" "none"})]
        (is (= 200 (:status r)))
        (exported)
        (testing "the job's report is the panel's, and it says where the dump went"
          (let [body (:body (GET "/kbs/export/rows"))]
            (is (re-find #"id=\"kb-export\"" body))
            (is (re-find #"tag-done" body))
            (is (re-find (re-pattern (java.util.regex.Pattern/quote (.getAbsolutePath dump)))
                         body))
            (is (re-find #"sentexes" body))))
        (testing "the poll stops on its own once nothing is running"
          (is (not (re-find #"hx-trigger=\"every" (:body (GET "/kbs/export/rows"))))))
        (testing "and the loop is closed: what was written is offered as a source, said so
                  on the page rather than left for the reader to discover"
          (is (= :dump (catalog/classify dump)))
          (is (some #(= "browser-dump" (:name %)) (catalog/sources)))
          (is (re-find #"Offered below" (:body (GET "/kbs"))))
          (is (re-find #"browser-dump" (:body (GET "/kbs"))))))
      (testing "a refusal is a state the page shows, in the writer's own words"
        (let [r (POST "/kbs/export" {"dir" (.getPath dump)})]
          (exported)
          (is (= 200 (:status r)))
          (is (re-find #"is not empty" (:body (GET "/kbs/export/rows"))))))
      (finally
        (if prop (System/setProperty "vaelii.kb.path" prop) (System/clearProperty "vaelii.kb.path"))
        (doseq [f (reverse (file-seq root))] (.delete ^java.io.File f))))))

(deftest the-export-controls-are-post-only-and-origin-checked
  (doseq [uri ["/kbs/export" "/kbs/export/cancel"]]
    (testing (str uri " refuses a cross-origin caller")
      (is (= 403 (:status (POST uri {"dir" "/tmp/vaelii-nowhere"}
                            {"host" "localhost:3000" "origin" "http://evil.example"})))))
    (testing (str uri " is not reachable by navigation")
      (is (= 405 (:status (GET uri))))))
  (testing "a destination nobody named writes nothing, and says so on the page"
    (let [r (POST "/kbs/export" {"dir" ""})]
      (is (= 200 (:status r)))
      (is (re-find #"destination" (:body r)))
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
            page that summed a corpus per view would be unusable at eleven million"
    (let [e (catalog/entry "base")]
      (is (= (v/sentex-count tu/*kb*) (:sentexes (:stats e)))))))
