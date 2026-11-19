;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.web-extension-test
  "The browser's extension registry, driven through the public `vaelii.web` shim as an
  outside library would drive it: what a registered extension adds to every page, which
  guard each route method carries, and what the registry refuses at registration.

  Every test registers under a name of its own and unregisters in a `finally`, so the
  registry is empty again when the test ends — the registry is process state, and a
  leaked extension would add a panel to every term page another namespace renders."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [hiccup2.core :as h]
            [vaelii.browser.catalog :as catalog]
            [vaelii.browser.web :as bweb]
            [vaelii.client :as vc]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]
            [vaelii.web :as web])
  (:import [org.eclipse.jetty.server Server ServerConnector]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defmacro ^:private with-extension
  "Run `body` with `ext` registered under `nm`, and unregistered after."
  [nm ext & body]
  `(do (web/register-extension ~nm ~ext)
       (try ~@body (finally (web/unregister-extension ~nm)))))

(def ^:private same-site {"host" "localhost:3000" "origin" "http://localhost:3000"})

(defn- request
  ([app method uri] (request app method uri nil nil))
  ([app method uri params headers]
   (app (cond-> {:request-method method :uri uri :scheme :http}
          params  (assoc :params params)
          headers (assoc :headers headers)))))

(tu/deftest-kb a-registered-extension-is-on-every-page-and-gone-after
  (tu/with-terms [dog]
    (v/assert kb (list 'genl dog 'animal) 'CxUniverse)
    (let [app (bweb/app kb)]
      (with-extension :probe
        {:routes     [["/ext/probe/hello" {:get (fn [env _] [:p.probe "hello " (some? (:kb env))])}]]
         :menu       [["Probe" "/ext/probe/hello"]]
         :term-actions (fn [_ term] [:a#probe-action {:href "/ext/probe/hello"} "probe " (str term)])
         :term-panel (fn [env term] [:div#probe-panel "panel for " (web/term-link env term)])
         :stylesheet "public/vaelii.css"
         :script     "public/vaelii.js"}
        (testing "its route answers, as a fragment"
          (let [r (request app :get "/ext/probe/hello")]
            (is (= 200 (:status r)))
            (is (str/includes? (:body r) "<p class=\"probe\">hello"))))
        (testing "its panel is drawn on a term page, with the term the page is about"
          (let [body (:body (app {:request-method :get :uri "/term" :query-string (str "q=" dog)}))]
            (is (str/includes? body "id=\"probe-panel\""))
            (is (str/includes? body "panel for "))))
        (testing "its actions are drawn in the term page's heading, with the term"
          (let [body    (:body (app {:request-method :get :uri "/term" :query-string (str "q=" dog)}))
                heading (re-find #"(?s)<h2>.*?</h2>" body)]
            (is (str/includes? heading "id=\"probe-action\""))
            (is (str/includes? heading (str "probe " dog)))))
        (testing "its menu item is in the menubar on every page"
          (is (re-find #"(?s)<nav class=\"menubar\">.*<a href=\"/ext/probe/hello\">Probe</a>"
                       (:body (request app :get "/")))))
        (testing "its assets are linked from the head and served under /ext/"
          (let [body (:body (request app :get "/"))]
            (is (str/includes? body "href=\"/ext/probe.css\""))
            (is (str/includes? body "src=\"/ext/probe.js\"")))
          (let [css (request app :get "/ext/probe.css")
                js  (request app :get "/ext/probe.js")]
            (is (= 200 (:status css)))
            (is (str/starts-with? (get-in css [:headers "Content-Type"]) "text/css"))
            (is (= 200 (:status js)))
            (is (str/starts-with? (get-in js [:headers "Content-Type"]) "text/javascript")))))
      (testing "and after unregistering, the route, the panel and the links are gone —
                from the same handler, since the registry is read per request"
        (is (= 404 (:status (request app :get "/ext/probe/hello"))))
        (is (not (str/includes? (:body (app {:request-method :get :uri "/term" :query-string (str "q=" dog)}))
                                "probe-panel")))
        (is (not (str/includes? (:body (request app :get "/")) ">Probe</a>")))
        (is (not (str/includes? (:body (request app :get "/")) "/ext/probe.css")))))))

(tu/deftest-kb a-route-carries-the-guard-its-method-names
  (let [app   (bweb/app kb)
        calls (atom [])]
    (with-extension :guarded
      {:routes [["/ext/guarded/read"  {:post  (fn [_ _] (swap! calls conj :post) [:p "read"])}]
                ["/ext/guarded/write" {:write (fn [env _]
                                                (swap! calls conj :write)
                                                {:status 200
                                                 :headers {"Content-Type" "text/plain"}
                                                 :body (str (some? (web/local-kb env)))})}]]}
      (testing "a same-origin :post runs"
        (is (= 200 (:status (request app :post "/ext/guarded/read" {} same-site)))))
      (testing "a cross-origin :post and :write are refused before the handler runs"
        (reset! calls [])
        (doseq [uri ["/ext/guarded/read" "/ext/guarded/write"]]
          (is (= 403 (:status (request app :post uri {} {"host" "localhost:3000"
                                                         "origin" "http://evil.example"})))
              uri))
        (is (empty? @calls)))
      (testing "a :write is a POST, answers a ring map as given, and sees the in-process KB"
        (let [r (request app :post "/ext/guarded/write" {} same-site)]
          (is (= [200 "true"] [(:status r) (:body r)])))
        (is (= 404 (:status (request app :get "/ext/guarded/write")))
            "and nothing answers a GET of it"))
      (testing "a :write is refused while a job is writing the KB, as every browser write is"
        (reset! calls [])
        (with-redefs [catalog/write-blocked? (constantly true)]
          (let [r (request app :post "/ext/guarded/write" {} same-site)]
            (is (str/includes? (:body r) "Nothing was written"))))
        (is (empty? @calls))))))

(tu/deftest-kb a-route-answering-a-page-is-drawn-inside-the-browser
  (let [app (bweb/app kb)]
    (with-extension :paged
      {:routes [["/ext/paged/" {:get (fn [_ req] (web/page req "Paged" [:p#paged "hello"]))}]]
       :menu   [["Paged" "/ext/paged/"]]}
      (testing "a plain request gets the whole document, the menubar around the body"
        (let [body (:body (request app :get "/ext/paged/"))]
          (is (str/starts-with? body "<!DOCTYPE html>"))
          (is (str/includes? body "<title>vaelii · Paged</title>"))
          (is (re-find #"(?s)<nav class=\"menubar\">.*<main id=\"main\">.*id=\"paged\"" body))))
      (testing "an htmx request gets the #main region alone, which is what a boosted
                menubar click selects"
        (let [body (:body (request app :get "/ext/paged/" nil {"hx-request" "true"}))]
          (is (not (str/includes? body "<!DOCTYPE")))
          (is (not (str/includes? body "menubar")))
          (is (re-find #"(?s)<main id=\"main\">.*id=\"paged\"" body))))
      (testing "a history restore is answered the whole document, as every page answers it"
        (is (str/starts-with? (:body (request app :get "/ext/paged/" nil
                                              {"hx-request" "true"
                                               "hx-history-restore-request" "true"}))
                              "<!DOCTYPE html>"))))))

(deftest a-malformed-extension-is-refused-at-registration
  (doseq [[label nm ext] [["a name that is not a plain keyword" :a/b {}]
                          ["an upper-case name" :Probe {}]
                          ["an unknown key" :probe {:routez []}]
                          ["a route outside the prefix" :probe {:routes [["/term" {:get identity}]]}]
                          ["another extension's prefix" :probe {:routes [["/ext/other/x" {:get identity}]]}]
                          ["an unknown method" :probe {:routes [["/ext/probe/x" {:put identity}]]}]
                          ["a menu item outside the prefix" :probe {:menu [["Home" "/"]]}]
                          ["a menu item that is not a pair" :probe {:menu [["Probe"]]}]
                          ["both POST kinds on one path"
                           :probe {:routes [["/ext/probe/x" {:post identity :write identity}]]}]]]
    (is (= :unknown-option
           (try (web/register-extension nm ext) nil
                (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))
        label))
  (is (not (str/includes? (:body ((bweb/app tu/*kb*) {:request-method :get :uri "/"}))
                          "/ext/"))
      "and nothing refused was filed"))

(tu/deftest-kb the-shim-helpers-render-what-the-pages-render
  (tu/with-terms [dog Rex CxExt]
    (v/assert kb (list 'genlCx CxExt 'CxWell) 'CxUniverse)
    (v/assert kb (list 'genl dog 'animal) CxExt)
    (let [env (bweb/render-env kb {})]
      (testing "a preview names what would be believed, and stores nothing"
        (let [before (v/sentex-count kb)
              html   (str (h/html (web/consequences env "Heading"
                                                    {:add [[(list dog Rex) CxExt]]})))]
          (is (str/includes? html "Heading"))
          (is (str/includes? html "newly believed"))
          (is (= before (v/sentex-count kb)))))
      (testing "a write's result renders its rows"
        (let [result (v/edit-with-consequences! kb {:add [[(list dog Rex) CxExt]] :remove []})
              html   (str (h/html (web/stored-sentexes env result)))]
          (is (str/includes? html (str Rex)))))
      (testing "read-form reads EDN and answers nil for what does not read"
        (is (= (list dog Rex) (web/read-form (pr-str (list dog Rex)))))
        (is (nil? (web/read-form "(unclosed")))))))

(tu/deftest-kb the-shim-serves-what-the-browser-serves
  ;; `vaelii.web` is one-line delegations, and a delegation to the wrong var passes every
  ;; test written against `vaelii.browser.web`.  Each shim here is called beside the var it
  ;; names.
  (let [health {:request-method :get :uri "/health" :headers {"host" "localhost:3000"}}]
    (is (= (select-keys ((bweb/handler kb) health) [:status :body])
           (select-keys ((web/handler kb) health) [:status :body])
           (select-keys ((web/handler kb {:host "127.0.0.1"}) health) [:status :body]))))
  (is (= (str (h/html (bweb/render-form (bweb/render-env kb {}) '(genl dog animal))))
         (str (h/html (web/render-form (bweb/render-env kb {}) '(genl dog animal))))))
  (let [refusal (fn [start] (try (start kb {:port 0 :reload? true}) nil
                                 (catch clojure.lang.ExceptionInfo e (ex-data e))))]
    (is (= :unknown-option (:type (refusal web/start))))
    (is (= (refusal bweb/start) (refusal web/start))))
  (let [^Server server (web/start kb {:port 0 :token nil})]
    (try
      (let [port (.getLocalPort ^ServerConnector (first (.getConnectors server)))]
        (is (= {:ok true} (vc/health (vc/client "localhost" port {:token nil})))))
      (finally (.stop server)))))

(deftest a-bounded-preview-says-so-rather-than-implying-completeness
  ;; the renderer directly: making a real batch cascade past the cap costs more than the
  ;; claim is worth, and what is under test here is that the panel *reports* the flag
  ;; `preview` sets (`preview_test` asserts that it sets it)
  (let [panel  (fn [result]
                 (str (h/html (#'bweb/consequence-panel (bweb/render-env tu/*kb* {})
                                                        "Heading" result))))
        capped (panel {:believed-added [{:sentence '(dog Muffet) :context 'CxWell}]
                       :believed-removed [] :refused [] :violations []
                       :contradictions [] :bounded? true})
        whole  (panel {:believed-added [{:sentence '(dog Muffet) :context 'CxWell}]
                       :believed-removed [] :refused [] :violations []
                       :contradictions [] :bounded? false})]
    (is (str/includes? capped "cut short"))
    (is (str/includes? capped (str @#'bweb/preview-max-results))
        "a reader told the answer is partial should be told where it stopped")
    (is (not (str/includes? whole "cut short")))
    (testing "and either way, that nothing was stored"
      (is (str/includes? whole "Nothing here is stored")))))
