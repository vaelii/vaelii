;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.browser.web
  "A small reitit-ring web browser over a KB:

    /                 the upper ontology (contexts, types, core predicates, disjointness)
    /stats            KB-wide counts, contexts by size, and the reasoning-health ledgers
    /find?q=<pattern> the terms whose name matches, from the index's term-name set
    /term?q=<term>    every sentex containing the term, grouped by the index root that
                      reaches it (functor / argument-position / context / term-index)
    /sentex/:id       a sentex (literal or rule): its belief state (IN, or the why-not
                      reason — superseded / defeated / unsupported), supports, dependents
    /justification/:id    a justification: its supports (arguments) and dependent sentex
    /levels?q=<goal>  the lookup-to-query stack: what each of the 8 levels answers
    /edit             the multi-sentex editor (GET seeds it, POST saves) — a fragment
    /{term,find,levels}/rows   one more page of a capped list, as bare rows

  Run it with `lein run -m vaelii.browser.web` (serves a starter-loaded KB on :3000).
  Handlers are pure `request -> response`, so they are testable without a server.

  Every page is answered twice over: as a whole document, and — when htmx asks, which
  is every navigation and search — as the `#main` fragment that actually lands.  What a
  page costs in KB reads is part of what this demonstrates, since the browser reads the
  public surface alone and each read is a round-trip under `--attach`; see the `render-env`
  section below and docs/web.md."
  (:require [cheshire.core :as json]
            [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.walk :as walk]
            [hiccup.page :as hpage]
            [hiccup2.core :as h]
            [reitit.ring :as ring]
            [ring.adapter.jetty :as jetty]
            [ring.middleware.params :refer [wrap-params]]
            [taoensso.trove :as trove]
            ;; `v` is the access facade, not `vaelii.core` directly: it re-exports the
            ;; read surface the browser uses but dispatches each KB read to an
            ;; in-process KB *or* a remote daemon, so `app` runs against either.  Every
            ;; `v/…` call here is still a public read — just target-polymorphic.
            [vaelii.browser.access :as v]
            ;; the KB catalog: what this process can load, what it has loaded, and which
            ;; of those is active.  The browser is the thing that drives it (`/kbs`), and
            ;; reads the active KB through a holder rather than holding one itself.
            [vaelii.browser.backup :as backup]
            [vaelii.browser.catalog :as catalog]
            [vaelii.browser.examples :as ex]
            [vaelii.browser.inflight :as inflight]
            ;; the registry every long operation runs in — a load, an export, a chaining
            ;; run.  Process state rather than a KB read, so it is not a hole in the ledger
            ;; below: it reads no KB and writes none.
            [vaelii.browser.jobs :as jobs]
            [vaelii.browser.reload :as reload]
            [vaelii.browser.removed :as removed]
            [vaelii.browser.sandbox :as sandbox]
            ;; the inline-SVG primitives the term page's concept graph is drawn with.
            ;; Pure geometry — it takes no KB and reads nothing, so it is not a hole in
            ;; the ledger below either.
            [vaelii.browser.svg :as svg]
            ;; the origin/Host checks this page and the daemon both hold to
            [vaelii.host.guard :as guard]
            ;; the editor's line format, which spells a rule's wrappers off its record
            [vaelii.host.lines :as lines]
            [vaelii.host.serve :as serve]
            [vaelii.host.starter :as starter]
            [vaelii.host.subscribe :as sub]))

;; The browser reads the KB through `vaelii.core` alone, by way of `access`, and requires no
;; `vaelii.impl` namespace (`public_api_test/browser-reaches-into-no-impl`).  A read the
;; page needs and the API does not publish is published in `vaelii.core` first.  The
;; `vaelii.host` requires are peers that check does not read, so a KB read added to one of
;; them goes around it: publish it in `vaelii.core`.

;; ---- rendering ----------------------------------------------------------
;; Every page is built with `hiccup2.core/html`, which **escapes strings in body position**
;; and in attributes, so KB content (a symbol may contain `<`) is safe to render.  A node
;; that must emit literal markup opts in with `h/raw` (`theme-init-js` only).  `html`
;; returns a `RawString`, so `resp` / `frag` coerce with `str` for the ring body.

(def stylesheet-resource
  "The browser's stylesheet, on the classpath (resources/public/vaelii.css)."
  "public/vaelii.css")

(def ^:private stylesheet-uri "/vaelii.css")

(def ^:private dev?
  "Is this a development server?  `VAELII_DEV` in the environment says so.  It decides
  how the static assets are treated: in dev the stylesheet is re-read per request (so
  editing it shows on a refresh, no restart) and nothing is cached by the browser;
  otherwise each is read once and served with a cache header, so a pageview is not a
  file read and a repeat visit is not a download."
  (v/switch-value "VAELII_DEV"))

(def ^:private static-cache-control
  (if dev? "no-cache" "public, max-age=3600"))

(defn- read-stylesheet [] (some-> (io/resource stylesheet-resource) slurp))

(def ^:private cached-stylesheet (delay (read-stylesheet)))

(defn- stylesheet [] (if dev? (read-stylesheet) @cached-stylesheet))

(def ^:private theme-init-js
  "A pre-paint script: read the saved palette and theme from localStorage and set them on
  <html> before the page renders, so the page opens in the chosen colours with no flash.
  A theme is written only when one was *stored*: without `data-theme` the page follows the
  OS through the stylesheet's `prefers-color-scheme: light` block.  Both values are checked
  against the recognised set and an unrecognised one is ignored, since any `data-theme`
  value fails the media query's `:not([data-theme])` scope and leaves the page dark.
  Runs synchronously in <head>; it is the one node rendered raw (`h/raw`, in `page`)."
  (str "(function(){var d=document.documentElement,s;try{s=localStorage}catch(e){return}"
       "var p=s.getItem('vaelii-palette');"
       "d.setAttribute('data-palette',/^(violet|red|green|rainbow)$/.test(p)?p:'violet');"
       "var t=s.getItem('vaelii-theme');"
       "if(t==='light'||t==='dark'){d.setAttribute('data-theme',t)}})();"))

(defn current
  "The KB a request reads.  A **holder** (anything deref-able —
  `vaelii.browser.catalog/holder`) yields whichever KB is active right now; a KB or an
  access value is itself.  Every handler goes through here, which is what lets the
  browser switch KBs under a running server."
  [target]
  (if (instance? clojure.lang.IDeref target) @target target))

(defn- active-kb-name
  "What to call the KB on screen — the active catalog entry's name, or a plain label when
  the browser is running against a KB nobody registered (a test, an `--attach`)."
  []
  (or (:name (catalog/active-entry)) "in-process"))

(defn- kb-name
  "What to call a KB a handler has already **resolved** — the name of the entry holding
  it, by identity, and the same plain label when nobody registered it.

  Not `active-kb-name`, and the difference is the whole point: `/kbs/activate` re-points
  the holder at any moment and takes no monitor, so a page rendered after a judgement can
  be reading a different entry than the one judged.  A refusal names the KB the refusal
  was about."
  [kb]
  (or (catalog/name-of kb) "in-process"))

(defn- removed-owner
  "Whose removed list `kb` reads and writes (`vaelii.browser.removed`): the printed key and
  name of the catalog entry holding it, or the KB itself when no entry does, so two KBs
  never share a list."
  [kb]
  (if-let [{:keys [key name]} (catalog/entry-of kb)] (pr-str [key name]) kb))

;; a token per KB no catalog entry holds, keyed weakly so a settled job's report does not
;; keep the KB it read alive (a KB's atoms compare by identity, so equal KBs are one KB)
(defonce ^:private unregistered-owners
  (java.util.Collections/synchronizedMap (java.util.WeakHashMap.)))

(defn- job-owner
  "The string a read job over `kb` files as `:kb-owner`, which `/lists` and `/quality`
  match a held result on: `removed-owner`'s string for an entry, and a token of this KB's
  own for a KB no entry holds, so two unregistered KBs never read each other's result."
  [kb]
  (let [o (removed-owner kb)]
    (if (string? o)
      o
      (.computeIfAbsent ^java.util.Map unregistered-owners o
                        (reify java.util.function.Function
                          (apply [_ _] (str (gensym "unregistered-"))))))))

(defn- jobs-badge
  "How many jobs are running, for the header.  Its own element with an id because the
  header sits outside the region a swap replaces: `/jobs/rows` ships a fresh copy out of
  band, exactly as the entries list does for the active KB's name.  The element is rendered
  whether or not anything is running, since an absent element is a swap with nowhere to
  land."
  ([] (jobs-badge false))
  ([oob?]
   (let [n (count (jobs/running))]
     [:span#job-count (cond-> {}
                        oob?     (assoc :hx-swap-oob "true")
                        (pos? n) (assoc :class "job-count-on"))
      (when (pos? n) (str " " n))])))

;; ---- extensions ---------------------------------------------------------
;; A library on the classpath adds to this browser through `register-extension`.  The
;; registry is process state read per request, so an extension registered after `start`
;; is served from the next request and `unregister-extension` removes it the same way.
;; Routes live under `/ext/<name>/`; handlers get the request's render env (`render-env`)
;; and the helpers the `vaelii.web` shim publishes, and the browser applies the origin
;; check and the write guard by the route's method (`extension-handler`).  docs/web.md,
;; "Extensions".

(defonce ^:private extensions
  ;; sorted, so the term page draws the panels, and the head links the assets, in the
  ;; same order on every request and in every process
  (atom (sorted-map)))

(def ^:private extension-keys
  #{:routes :menu :term-actions :term-panel :on-start :stylesheet :script})

(def ^:private extension-methods #{:get :post :write})

(defn- check-extension!
  "Refuse an extension map the registry could not serve, naming what is wrong: a name
  that is not a plain lower-case keyword (it becomes a URL segment), a key the registry
  does not read, a route or a menu item outside the extension's own prefix, a menu item
  that is not a `[label href]` pair, or a method it does not know.  Refusing at registration is what keeps a typo from surfacing as a page that
  silently never appears."
  [ext-name ext]
  (when-not (and (simple-keyword? ext-name) (re-matches #"[a-z][a-z0-9-]*" (name ext-name)))
    (throw (ex-info (str "an extension name is a plain lower-case keyword, got "
                         (pr-str ext-name))
                    {:type :unknown-option :mismatch :bad-value :name ext-name})))
  (when-let [unknown (seq (remove extension-keys (keys ext)))]
    (throw (ex-info (str "an extension map takes " (str/join " " (sort extension-keys))
                         ", not " (str/join " " unknown))
                    {:type :unknown-option :mismatch :unknown-key
                     :unknown (vec unknown) :options (vec (sort extension-keys))})))
  (let [prefix (str "/ext/" (name ext-name) "/")]
    (doseq [[path methods] (:routes ext)]
      (when-not (and (string? path) (str/starts-with? path prefix))
        (throw (ex-info (str "extension " ext-name " serves under " prefix ", not at "
                             (pr-str path))
                        {:type :unknown-option :mismatch :bad-value :path path})))
      (when-let [unknown (seq (remove extension-methods (keys methods)))]
        (throw (ex-info (str "an extension route takes " (str/join " " (sort extension-methods))
                             ", not " (str/join " " unknown))
                        {:type :unknown-option :mismatch :unknown-key
                         :unknown (vec unknown) :options (vec (sort extension-methods))})))
      ;; both are served as POST, so one path cannot carry both
      (when (and (:post methods) (:write methods))
        (throw (ex-info (str "extension route " path " names both :post and :write, "
                             "which are both a POST")
                        {:type :unknown-option :mismatch :conflict :path path}))))
    (doseq [item (:menu ext)]
      (when-not (and (vector? item) (= 2 (count item)) (string? (first item))
                     (string? (second item)) (str/starts-with? (second item) prefix))
        (throw (ex-info (str "extension " ext-name " menu items are [label href] with the"
                             " href under " prefix ", got " (pr-str item))
                        {:type :unknown-option :mismatch :bad-value :item item}))))))

(defn register-extension
  "File `ext` under `ext-name` (a lower-case keyword), replacing any extension of that
  name, and answer the name.  Every key is optional:

    :routes      [[\"/ext/<name>/…\" {:get f :post f :write f}] …] — each `f` is
                 `(fn [env req] …)` answering hiccup (sent as a fragment) or a ring
                 response map.  `:post` is refused cross-origin; `:write` is a POST that
                 runs under the browser's write guard, with `env` over the KB the guard
                 judged.
    :menu        [[label \"/ext/<name>/…\"] …] — links in the menubar.
    :term-actions (fn [env term] hiccup) — drawn beside the heading of every term page.
    :term-panel  (fn [env term] hiccup) — drawn last on every term page.
    :on-start    (fn []) — run when `-main` or `dev-repl` starts the server, before it
                 serves.
    :stylesheet  a classpath resource, served at /ext/<name>.css and linked from every page.
    :script      a classpath resource, served at /ext/<name>.js and loaded (deferred)."
  [ext-name ext]
  (check-extension! ext-name ext)
  (swap! extensions assoc ext-name ext)
  ext-name)

(defn unregister-extension
  "Take the extension filed under `ext-name` out of the browser; its routes, panel and
  assets are gone from the next request.  Answers the name."
  [ext-name]
  (swap! extensions dissoc ext-name)
  ext-name)

(defn- extension-assets
  "The `<head>` elements for every registered extension's stylesheet and script."
  []
  (for [[n {:keys [stylesheet script]}] @extensions]
    (list (when stylesheet [:link {:rel "stylesheet" :href (str "/ext/" (name n) ".css")}])
          (when script [:script {:src (str "/ext/" (name n) ".js") :defer true}]))))

(defn- extension-menu
  "Every registered extension's menubar links, in name order."
  []
  (for [[_ {:keys [menu]}] @extensions
        [label href] menu]
    [:a {:href href} label]))

(defn- extension-term-actions
  "Every registered extension's actions for `term`, in name order, each in its own span."
  [env term]
  (for [[n {:keys [term-actions]}] @extensions :when term-actions]
    [:span.ext-term-actions {:data-extension (name n)} (term-actions env term)]))

(defn- extension-panels
  "Every registered extension's term-page panel for `term`, in name order."
  [env term]
  (for [[_ {:keys [term-panel]}] @extensions :when term-panel]
    (term-panel env term)))

(defn- start-extensions
  "Run every registered extension's `:on-start`.  A hook that throws is logged and the
  rest still run: one extension's startup failing is not a reason for the browser not
  to serve."
  []
  (doseq [[n {:keys [on-start]}] @extensions :when on-start]
    (try (on-start)
         (catch Throwable t
           (trove/log! {:level :warn :id ::extension-start :error t
                        :msg (str "extension " (name n) " failed to start")})))))

(def ^:private build
  "This process's `{:version … :revision …}`, read from the Maven descriptor Leiningen
  writes onto the classpath and into the jar, or nil when the classpath holds none."
  (when-let [u (io/resource "META-INF/maven/com.vaelii/vaelii/pom.properties")]
    (let [props (java.util.Properties.)]
      (with-open [in (io/input-stream u)] (.load props in))
      {:version (.getProperty props "version") :revision (.getProperty props "revision")})))

(defn- header
  "The site header.  The logo, wordmark and running version (a home link), the term-search
  box, the KB link with the colour controls, and the menubar are four grid items, and
  vaelii.css places them (docs/web.md).  The
  search is an htmx active-search — a debounced `hx-get` to /find swaps just the `#main` region out of
  the answer.  The palette dot (cycling the four accent pairs) and the theme dot
  (flipping light against dark) are wired by vaelii.js and persisted in localStorage
  (docs/web.md)."
  []
  [:header.site
   ;; the request indicator every navigation and search points `hx-indicator` at:
   ;; htmx marks it `.htmx-request` for the life of the request, so a slow page says
   ;; so instead of looking dead
   [:div#page-indicator.htmx-indicator {:aria-hidden "true"}]
   [:a.brand {:href "/"}
    [:img.logo {:src "/logo.svg" :width 30 :height 30 :alt ""}]
    [:span.wordmark "Vaelii"]
    (when-some [{:keys [version revision]} build]
      [:span.version {:title (some->> revision (str "revision "))} version])]
   ;; top-level tools; vaelii.js marks the one matching the current path active
   [:nav.menubar
    [:a {:href "/"} "Ontology"]
    [:a {:href "/reasoning"} "Reasoning"]
    [:a {:href "/levels"} "Query"]
    ;; the assert page writes into the reader's sandbox, names it and offers the reset
    [:a {:href "/assert"} "Assert"]
    [:a {:href "/removed" :title "the last sentexes removed from this KB, to put back"}
     "Removed"]
    [:a {:href "/network"} "Network"]
    [:a {:href "/stats" :title "counts, reasoning health and the whole-KB lists: defeats, contradictions, types without a genl, held facts and rules"}
     "Stats"]
    ;; long work runs on its own thread, so the way to it has to be in the chrome rather
    ;; than on the page that started it — the reader who wants it navigated away
    [:a {:href "/jobs" :title "long work: what is running, and how to stop it"}
     "Jobs" (jobs-badge)]
    (extension-menu)]
   [:input.search {:type "search" :name "q" :placeholder "regex search"
                   :autocomplete "off" :aria-label "find terms by regex"
                   :hx-get "/find" :hx-target "#main" :hx-select "#main"
                   :hx-swap "outerHTML" :hx-push-url "true"
                   :hx-trigger "keyup changed delay:400ms, search"}]
   [:div.header-end
    ;; which KB every other page is about, and the way to change it
    ;; the label is its own element with an id because it changes without the header
    ;; being re-rendered: switching KBs swaps it out of band (`entries-panel`)
    [:a.kb-active {:href "/kbs" :title "knowledge bases: load, unload, switch"}
     [:span.muted "KB:"] " " [:span#kb-label (active-kb-name)]]
    ;; each dot is painted in what it controls, so neither needs a label beside it:
    ;; vaelii.js keeps the titles saying which value is live
    [:span.theme-controls
     [:button#palette-dot.palette-btn {:type "button" :aria-label "switch colour palette"
                                       :title "Switch colour palette"}]
     [:button#theme-dot.theme-btn {:type "button"
                                   :aria-label "toggle light or dark theme"
                                   :title "Toggle light or dark theme"}]]]])

(defn- restart-notice
  "The notice every page carries while a held namespace, or a protocol, record or type,
  has changed on disk since the process started (`vaelii.browser.reload/restart-owed`), or
  nil.  The running process still runs the definitions it loaded, so those edits take a
  restart."
  []
  (when-some [nss (seq (reload/restart-owed))]
    [:div.callout {:role "status"}
     [:strong "Restart to load " (str/join ", " nss) "."]
     " The reloader does not redefine a protocol, record or type, or re-evaluate a held"
     " namespace, under a loaded KB (docs/web.md)."]))

(def ^:private line-break-at
  "The positions where a page's source takes a newline: before a block element's opening
  tag and after its closing tag.  Whitespace at those positions renders nothing.  Hiccup
  escapes every text node and attribute, and `theme-init-js`, the one raw node, holds no
  tag, so each match is a real tag boundary.  The list omits inline elements because a
  newline beside one renders as a space, cells and definition pairs so a table row or a
  `dl` stays on one line, and `title` so no newline lands inside an `svg`."
  (let [block (str "html|head|meta|link|script|body|header|nav|main|footer|section|"
                   "aside|div|table|caption|thead|tbody|tr|ul|ol|li|dl|"
                   "h1|h2|h3|h4|h5|h6|p|pre|hr|blockquote|details|summary|figure|"
                   "figcaption|option")]
    (re-pattern (str "(?<=>)(?=<)(?:(?=<(?:" block ")\\b)|(?<=</(?:" block ")>))"))))

(defn- page
  "A whole HTML5 document.  `{:mode :html}` is what makes void elements render as
  `<meta …>` rather than self-closed, and the doctype is prepended around the
  `<html>` element hiccup renders."
  [title & body]
  (str
   (:html5 hpage/doctype)
   (h/html
    {:mode :html}
    [:html {:lang "en"}
     [:head
      [:title (str "vaelii · " title)]
      [:meta {:charset "utf-8"}]
      [:meta {:name "viewport" :content "width=device-width, initial-scale=1"}]
      ;; apply the saved colour mode + theme before first paint (no flash)
      [:script (h/raw theme-init-js)]
      [:link {:rel "icon" :href "/favicon.svg" :type "image/svg+xml"}]
      [:link {:rel "stylesheet" :href stylesheet-uri}]
      ;; htmx drives the interactive bits (active search, boosted navigation, the
      ;; editor's load/save) declaratively; vaelii.js is the small hand-written module
      ;; for what htmx cannot express — the colour-mode and theme toggles, the active
      ;; menubar link, and the sentex editor's own keys (docs/web.md).
      [:script {:src "/htmx.min.js" :defer true}]
      [:script {:src "/vaelii.js" :defer true}]
      (extension-assets)]
     ;; hx-boost turns every in-page link and form into an ajax swap with history and
     ;; degrades to plain links without htmx.  The swap is scoped to `#main`, so the header
     ;; and the editor are never torn down.  `show:window:top` is needed: a boosted swap
     ;; whose target is not the body scrolls the target into the viewport, which would
     ;; scroll the header off the top on every navigation.
     [:body {:hx-boost "true" :hx-target "#main" :hx-select "#main"
             :hx-swap "outerHTML show:window:top"
             :hx-indicator "#page-indicator"}
      (header)
      [:main#main (restart-notice) body]
      ;; the panel the editor form is swapped into, outside #main so a navigation or
      ;; search swap does not tear it down mid-edit.  A row's [edit] link fills it.
      [:div#editor]]])))

(defn- resp [body]
  {:status 200 :headers {"Content-Type" "text/html; charset=utf-8"} :body (str body)})

(defn- frag
  "Render a hiccup fragment (not a whole page) as an HTML response — what htmx swaps
  into a target.  Same `:html` mode as `page`, so a fragment is written the way the
  document it lands in is."
  [hiccup]
  {:status  200
   :headers {"Content-Type" "text/html; charset=utf-8"}
   :body    (str (h/html {:mode :html} hiccup))})

(defn- url-enc [s] (java.net.URLEncoder/encode (str s) "UTF-8"))

;; ---- the per-request render env ---------------------------------------
;; Rendering asks the KB the same few questions per row (the type set, whether a handle is
;; believed, a handle's record), an N+1 per listing page and an HTTP round-trip each under
;; `--attach`.  A render env holds those answers for one request: the type set read at
;; most once, and a belief cache the row renderers fill in **batch** through
;; `prime-belief!`.

(def ^:private derived-cookie
  "The cookie carrying the hide-derived reading preference: `hide` or `show`."
  "vaelii-derived")

(def ^:private derived-cookie-re
  "`derived-cookie`'s value off the raw `Cookie` header.  One cookie is read here and the
  header split lives in `vaelii.browser.sandbox`, which parses the whole thing for the
  session token; a second full parse to answer one question is not worth the coupling."
  (re-pattern (str "(?:^|;\\s*)" derived-cookie "=([^;]*)")))

(def ^:private derived-cookie-max-age
  "How long the hide-derived preference outlives the request that set it — one year in
  seconds.  A **persistent** cookie, where the sandbox's is a session one
  (`sandbox/set-cookie`): a sandbox is scoped to the sitting and one that outlived the
  browser would be a sandbox nobody remembers making, while a reading preference asked
  again on every visit is the preferences panel this exists instead of."
  31536000)

(defn- asked-derived
  "`\"hide\"`, `\"show\"`, or nil — what this request said about derived rows, if
  anything.  Read off `:params`, so it arrives the same way from a link's query string."
  [req]
  (#{"hide" "show"} (some-> (get-in req [:params "derived"]) str/trim str/lower-case)))

(defn- hide-derived?
  "Does this request want the derived rows of a term page's index groups left out?

  The request's own answer first, then the cookie, then no.  Derived is read off the
  record — an asserted sentex carries a `:strength` and a derived one does not — which is
  the same discriminant `badge` draws a ring for, so a row the reader sees as derived is
  a row this leaves out.  Not `vaelii.core/premise?`, which asks the network whether
  anything concludes the sentex: a sentex can be asserted **and** derivable, and the two
  answers then disagree with each other and with what the page drew."
  [req]
  (if-let [a (asked-derived req)]
    (= "hide" a)
    (= "hide" (second (re-find derived-cookie-re
                               (str (get-in req [:headers "cookie"])))))))

(defn- remember-derived
  "`resp` carrying this request's hide-derived choice forward in a cookie, when it made
  one.  `HttpOnly` because no script reads it, and `SameSite=Lax` because no other site
  has business setting how this one reads — the same reasoning as the sandbox cookie.

  `sandbox/wrap-session` may be setting its own cookie on the same response, so both go
  through `sandbox/add-cookie`, which appends."
  [resp req]
  (if-let [a (asked-derived req)]
    (sandbox/add-cookie resp (str derived-cookie "=" a
                                  "; Path=/; Max-Age=" derived-cookie-max-age
                                  "; HttpOnly; SameSite=Lax"))
    resp))

(defn- fragment-request?
  "Is htmx asking for the `#main` fragment rather than a whole document?  `HX-Request`
  marks every htmx-issued request, so the answer can skip the chrome the client would
  discard.  `HX-History-Restore-Request` is the exception: htmx is repopulating a
  history entry and needs the document back."
  [req]
  (and (some? (get-in req [:headers "hx-request"]))
       (nil? (get-in req [:headers "hx-history-restore-request"]))))

(defn render-env
  "What one request's rendering reads that does not vary row to row — built once per
  request and threaded through every render fn in place of a bare KB."
  [kb req]
  {:kb        kb
   ;; The type set, as the set the taxonomy already holds: a delay, never copied.  It is
   ;; read to colour a term (`term-class`) and to count the types, which `/jobs`, `/kbs`,
   ;; `/caches` and fragment continuations never do.  In-process the deref is one atom read
   ;; (`tax/types` hands back the set by reference).  Under `--attach` it is one EDN transfer
   ;; per term page; the `set` below is for a target that does not hand back a set.
   :types     (delay (let [t (v/types kb)] (if (set? t) t (set t))))
   ;; the believed `logical_connective` members, for `term-class`: a closed extent of a
   ;; handful of rows, read once per page that renders a term
   :connectives (delay (into #{} (keep (fn [s] (when-not (v/negative? s)
                                                 (second (:sentence s)))))
                             (v/sentexes-with-functor kb 'logical_connective
                                                      {:believed? true})))
   :fragment? (fragment-request? req)
   ;; whether this reader wants only what the KB was told, not what it concluded.  It
   ;; rides the render env rather than a parameter because a group's continuation
   ;; (`/term/rows`) has to page the same sequence the page it continues did.
   :hide-derived? (hide-derived? req)
   ;; which scratch context this session writes to by default.  Naming it adds no work
   ;; — `sandbox/context-of` reads a cookie — and the context itself is not created
   ;; until something is actually written to it.  Whether it *has* been is a KB read, so
   ;; it is a delay: a page that never mentions the sandbox never pays for it.
   :sandbox   (sandbox/context-of req)
   :sandbox-live? (delay (boolean (when-let [c (sandbox/context-of req)]
                                    (sandbox/live? kb c))))
   :belief    (atom {})
   ;; what each reified term on the page denotes.  There is no batched read for these
   ;; — the map is `(natFormula K ?e)`, one probe per constant — so the cache is what
   ;; bounds it at one read per *distinct* constant rendered, however many times the
   ;; page renders it.  Empty and untouched on a KB that has minted none.
   :nat-exprs     (atom {})
   ;; each predicate's arity, one `v/relation-arity` read per distinct predicate on the
   ;; page, for `term-class`
   :arities       (atom {})})

(defn- env-of
  "The render env of the request `req` over the KB `target` currently names."
  [target req]
  (render-env (current target) req))

(defn local-kb
  "The in-process KB behind `env`, or nil when the browser reads a remote daemon
  (`--attach`).  What an extension checks before work that needs the KB in this process
  — a preview, a write, dozens of reads a round-trip each would make slow."
  [env]
  (v/local-kb (:kb env)))

(defn- prime-belief!
  "Learn the belief state of `handles` in **one** batched read (`v/believed`), so the
  rows that follow read the cache instead of the KB.  Handles already known are not
  re-asked, and a call with nothing new to learn reads nothing at all."
  [{:keys [kb belief]} handles]
  (let [want (into [] (comp (distinct) (remove #(contains? @belief %))) handles)]
    (when (seq want)
      (let [in (set (v/believed kb want))]
        (swap! belief into (map (fn [h] [h (contains? in h)])) want))))
  nil)

(defn- believed?
  "Is this handle believed?  From the per-request cache when `prime-belief!` fetched it
  — the listing case, one read for the page — else a single `v/in?`, cached, so no
  handle is ever asked about twice in one render."
  [{:keys [kb belief]} h]
  (if-let [e (find @belief h)]
    (val e)
    (let [b (boolean (v/in? kb h))]
      (swap! belief assoc h b)
      b)))

(def ^:private verdict-text
  "What each justification verdict other than `:supports` and `:antecedent-out` says on a
  page (`v/justification-verdicts`): why a justification whose arguments are all
  believed confers nothing."
  {:blocked "a block its rule carries holds (a closed extent, a withdrawn different), so the truth-maintenance network blocks this justification"
   :guard   "a guard defeat in force at its context covers this justification: its rule's exception or unknown antecedent holds there"
   :void    "the forced-monotonic declarations its context sees hold this firing void"
   :exempt  "its context exempts the placement this justification concludes"})

(defn- commas [n] (when (number? n) (format "%,d" (long n))))

(defn- css-percent
  "A fraction as the percentage a `width:` declaration takes, to one decimal.
  `clojure.core/format` uses the default locale, and a comma-decimal one writes `12,5`,
  which is not a CSS number.  Every number that lands in markup goes through this; `commas`
  does not, since a thousands separator is display text."
  [frac]
  (String/format java.util.Locale/ROOT "%.1f" (object-array [(* 100.0 frac)])))

(defn- progress-bar
  "Where a running load has got to.  A corpus knows its own total (its `report.edn` /
  `meta.edn` says how many sentences it holds) and gets a real bar; a load with no total
  gets a striped indeterminate one and the count it has reached, which shows that the
  loader does not know how far there is to go."
  [{:keys [phase done total note]}]
  (let [frac (when (and total (pos? total) done) (min 1.0 (/ (double done) (double total))))]
    [:div.kb-progress
     [:div.bar (if frac
                 [:span.bar-fill {:style (str "width:" (css-percent frac) "%")}]
                 [:span.bar-fill.indeterminate])]
     [:p.muted
      [:b (some-> phase name)] " · " (or (commas done) 0)
      (when total (str " / " (commas total)))
      (when frac (str " (" (format "%.0f" (* 100.0 frac)) "%)"))
      (when note (str " · " note))]]))

(defn- duration-text
  "`ms` as whole seconds below a minute, and as minutes to one decimal from a minute."
  [ms]
  (let [ms (long ms)]
    (if (< ms 60000)
      (str (quot ms 1000) " s")
      (format "%.1f min" (/ ms 60000.0)))))

(defn- local-time
  "An ISO-8601 instant as `yyyy-MM-dd HH:mm` in this machine's zone, or the string as given
  when it does not parse as an instant."
  [s]
  (try (.format (.atZone (java.time.Instant/parse (str s)) (java.time.ZoneId/systemDefault))
                (java.time.format.DateTimeFormatter/ofPattern "yyyy-MM-dd HH:mm"))
       (catch Exception _ (str s))))

(defn- short-digest [d] (let [d (str d)] (subs d 0 (min 12 (count d)))))

(defn- rebuild-bar
  "Where a belief rebuild behind an installed image has got to (`v/rebuild-progress`).  The
  bar fills to `:fraction`, the share of the image's recorded recover that the steps done
  so far took there, and is striped when the image records no recover; the line names the
  step, the time spent, and the recorded recover's total.  A rebuild that threw shows no
  bar: the line names the step it was in, the exception, and `recover` as the repair."
  [{:keys [step of label elapsed-ms expected-ms fraction failed]}]
  (if failed
    [:div.kb-progress
     [:p [:b "The rebuild failed at step " step " of " of] " (" label ") after "
      (duration-text elapsed-ms) ": " [:code (:class failed)] " " (:message failed)
      ". Belief stays the image's and writing stays refused until " [:code "(recover kb)"]
      " rebuilds belief under this build in place."]]
    [:div.kb-progress
     [:div.bar (if fraction
                 [:span.bar-fill {:style (str "width:" (css-percent fraction) "%")}]
                 [:span.bar-fill.indeterminate])]
     [:p.muted
      [:b "step " step " of " of] " · " label " · " (duration-text elapsed-ms) " so far"
      (when expected-ms
        (str " · the recover this image was written after took " (duration-text expected-ms)))]]))

(defn- polling
  "What makes a panel refresh **itself** while something is running: it fetches its own
  replacement every `every` and swaps in place.  The server stops including these once the
  job finishes.  `hx-indicator` is `unset` so a poll does not sweep the top-of-page
  `#page-indicator` bar, which the body points every request at."
  [uri every]
  {:hx-get uri :hx-trigger (str "every " every) :hx-target "this"
   :hx-select "unset" :hx-swap "outerHTML" :hx-indicator "unset"})

(defn- caveat-banner
  "The strip a page carries while the KB it reads is provisional: still loading, stopped
  part-way, or holding no belief.  Empty the rest of the time.  It lives at the top of
  `#main`, which every navigation swaps, and polls itself while a load runs; the endpoint
  answers with the empty element once nothing is left to say.  Two conditions are stated
  separately: a *prefix* of the corpus costs completeness, and *no belief* empties every
  believed answer and can outlive the load."
  []
  (let [{:keys [name status progress belief? recoverable? rebuilding? rebuild]}
        (catalog/active-caveat)
        loading? (= :running status)]
    [:div#kb-caveat
     (cond-> {}
       ;; a rebuild polls too, so the banner leaves the page when the rebuilt belief lands;
       ;; a failed one has nothing left to land
       (or loading? (and rebuilding? (not (:failed rebuild))))
       (merge (polling "/kbs/banner" "2s")))
     (when status
       (let [[lead tail] (if (and rebuilding? (= :done status))
                           (if (:failed rebuild)
                             ["Reading " " — the rebuild of its belief under this build failed."]
                             ["Reading " " — its belief is being rebuilt under this build."])
                           (case status
                             :running    ["Loading "     " — you are reading it as it arrives."]
                             :cancelling ["Stopping "    " — you are reading what has landed."]
                             :cancelled  ["Stopped part-way: " " — you are reading what had landed."]
                             :failed     ["Load failed: " " — you are reading what had landed."]
                             ;; :done reaches here only for the beliefless case, where the
                             ;; load is not the story and the bullet below it is — but the
                             ;; line still has to say which KB, and a bare name is not a
                             ;; sentence
                             ["Reading "   " — and it is stored, not merely missing."]))]
         [:div.kb-caveat {:class (str "kb-caveat-" (clojure.core/name status))}
          [:p.kb-caveat-line
           (when (seq lead) [:b lead])
           [:a {:href "/kbs"} name] tail]
          (when loading? (progress-bar progress))
          (when (and rebuilding? rebuild) (rebuild-bar rebuild))
          [:ul.kb-caveat-why
           (when-not (= :done status)
             [:li "Everything below is drawn from what is stored " [:i "now"] ", so a term "
              "or a rule that has not arrived yet reads as absent — which is what an "
              "absent fact always means here, and never as false."])
           (when loading?
             [:li "Writing is on hold: a load is this process's one writer, so this KB can "
              "be read while it fills up but not changed. Cancel it, or switch to another "
              "KB, to write again."])
           (when rebuilding?
             [:li [:b "Belief is the image an earlier engine build wrote."] " A rebuild "
              "under this build replaces it when it finishes, and this page updates then. "
              "Until then an answer can differ from the rebuilt belief wherever the engine "
              "change moved belief, and writing is refused."
              (when-let [{:keys [image source]} rebuild]
                (list " The image was written " (local-time (:written-at image))
                      " under engine source " [:code (short-digest (:source image))]
                      ", and this build's source is " [:code (short-digest source)] "."))
              " The rebuild writes an image under this build when it finishes, so the next "
              "open under the same engine source installs belief with no rebuild; "
              [:code "scripts/upgrade-kb.sh"] " runs the rebuild ahead of an open, on a "
              "store no process holds open."])
           (when-not belief?
             [:li [:b "Belief and the taxonomy are not built."] " Everything is stored and "
              "findable — the term pages, the extents, the raw index levels — but with no "
              "truth-maintenance network every " [:i "believed"] " answer is empty, and "
              "with no genl closures there is no type hierarchy, so the ontology page "
              "gives the impression that the KB held nothing. "
              (if loading?
                "The load builds both at the end."
                ;; Two repairs, and the store knows which applies: a KB holding
                ;; justifications has everything `recover` reads and needs no second pass
                ;; over the dump, while one holding none cannot be recovered into belief and
                ;; has to be loaded again.  Prescribing the reload to both would send the
                ;; first case back through hours of work.
                (if recoverable?
                  "Everything belief is built from is stored: run recover on this KB."
                  "Load this KB again with belief on to get them back."))])]]))]))

(defn- render
  "One page's answer: the whole document, or — when htmx asked for a fragment — the
  `#main` element alone.  The client swaps `#main` either way, so a fragment carries
  exactly what lands: no head, no header, no selection chrome.  The `<title>` rides
  along because htmx lifts one out of a fragment to retitle the tab.

  Every page is headed by `caveat-banner`, since every page reads the active KB and any
  of them can be the one a reader lands on first."
  [{:keys [fragment?]} title & body]
  (let [body (list (caveat-banner) body)]
    (if fragment?
      (frag (list [:title (str "vaelii · " title)] [:main#main body]))
      (resp (str/replace (page title body) line-break-at "\n")))))

(defn- edges-of
  "The [sub super] edges of a transitivity relation, read as the believed sentexes
  that state them.  The taxonomy caches the *closure*; the tree wants the direct
  edges it was built from, and those are exactly the believed `(genl a b)` /
  `(genlCx a b)` sentexes — the same input the cache is maintained from, and
  belief-filtered the same way."
  [kb pred]
  (into #{} (keep (fn [s] (let [[_ a b] (:sentence s)] (when (and a b) [a b]))))
        (v/sentexes-matching kb (list pred '?a '?b) '?ctx)))

(defn- disjoint-pair
  "The display key for a separation of `a` and `b`: the two terms in name order, so
  `(disjoint dog cat)` and `(disjoint cat dog)` are one row.  A **vector**, not a set: a
  type may be declared disjoint from itself, and `#{a a}` throws."
  [a b]
  (if (neg? (compare (str a) (str b))) [a b] [b a]))

(defn- disjoint-pairs
  "The disjointness pairs to display: the believed `(disjoint a b)` sentexes, the pairs a
  `disjoint_metatype` induces, and the pairs a believed `separating` or `partition`
  declaration separates (`separating-covers`, the table `disjoint?` reads).  Induced pairs
  are computed, since a metatype separates by being consulted, not by storing a clique.  A
  member is not separated from itself by belonging to one, so those halves filter the
  diagonal; a stated `(disjoint A A)` is shown."
  [kb]
  (let [declared (into #{} (keep (fn [s] (let [[_ a b] (:sentence s)]
                                           (when (and a b (not (v/negative? s)))
                                             (disjoint-pair a b)))))
                       ;; the predicate extent rather than `(disjoint ?a ?b)`: a pattern with
                       ;; no ground argument gives the trie nothing to narrow on and fans
                       ;; over every child token it has
                       (v/sentexes-with-functor kb 'disjoint {:believed? true}))
        induced  (for [m  (v/disjoint-metatypes kb)
                       :let [ms (vec (v/metatype-members kb m))]
                       a  ms
                       b  ms
                       :when (neg? (compare (str a) (str b)))]
                   (disjoint-pair a b))
        covered  (for [[_whole parts] (v/separating-covers kb)
                       :let [ps (vec (distinct parts))]
                       a    ps
                       b    ps
                       :when (neg? (compare (str a) (str b)))]
                   (disjoint-pair a b))]
    (-> declared (into induced) (into covered))))

(defn- arity-of
  "`t`'s exact arity, or nil, from the per-request cache: one `v/relation-arity` read per
  distinct predicate on the page."
  [{:keys [kb arities]} t]
  (if-let [e (find @arities t)]
    (val e)
    (let [n (v/relation-arity kb t)]
      (swap! arities assoc t n)
      n)))

(defn- pred-class
  "`t-pred`, plus `t-pred-n` when `t` takes three or more places by its stored arity."
  [env t]
  (if (some-> (arity-of env t) (>= 3)) "t-pred t-pred-n" "t-pred"))

(defn- term-class
  "The role class of a term, used to color it: type / individual / predicate (with
  `pred-class`'s mark on a ternary or wider one) / connective / context / number /
  variable.  A connective is a stored `logical_connective` member.  `v/term-role` supplies
  the naming role; the render env's `types` set overlays it so a node of the taxonomy
  colors by stored content, as `describe`'s role does: a predicate when `v/relation?`
  answers for it, else a type.  The overlay comes **before** the non-symbol fallback,
  because a type node may be a function term."
  [{:keys [kb types connectives] :as env} t]
  (let [role (v/term-role t)]
    (cond
      (= role :variable)  "t-var"
      (= role :number)    "t-num"
      (= role :context)   "t-context"
      (contains? @connectives t) "t-conn"
      (contains? @types t) (if (v/relation? kb t) (pred-class env t) "t-type")
      (not (symbol? t))   "t-num"
      (= role :individual) "t-ind"
      (= role :predicate) (pred-class env t)
      (= role :type)      "t-type"                        ; snake_case not yet in the taxonomy
      :else               (pred-class env t))))

;; ---- reified terms ------------------------------------------------------
;; A ground `(F a…)` under a `reifiable_function` is stored as an opaque constant in the
;; reserved `nat/` namespace (docs/nat.md), so **no page ever shows one**: every place a
;; term is rendered goes through `term-link`, and a reified one renders as the expression
;; it was minted from.  The parens are **bold**, which separates a reified NAT from an
;; ordinary compound beside it (on the constant's own page `(natFormula K E)` would
;; otherwise render K and E identically).  The opening paren links to the constant's page.

(defn- nat-expression
  "What reified term `k` denotes, from the per-request cache — one `v/term-expression`
  read per distinct constant on the page, however many times it is rendered.  nil when
  the KB holds no believed `natFormula` map for it."
  [{:keys [kb nat-exprs]} k]
  (if-let [e (find @nat-exprs k)]
    (val e)
    (let [e (v/term-expression kb k)]
      (swap! nat-exprs assoc k e)
      e)))

;; Expansion recurses, so it carries the constants already on the path.  The write path
;; cannot build a reified term that reaches itself, but a *stored* one can say anything
;; (docs/web.md, "The browser reads what is stored"), and an unguarded walk over
;; `(natFormula K (F K))` is a stack overflow.  A term already on the path renders as the
;; back-edge it is.

(defn- term-text
  "The text of a term, for the places that take a string rather than an element — a
  page `<title>`, a tooltip, a graph node's label, a link's own text.  A reified term
  is displayed as the expression it denotes, recursively, so it says the same thing there as in
  the prose; a term that is itself a compound (an unreified structural NAT, a function term an
  imported ontology names a collection by) is walked for the same reason."
  ([env t] (term-text env t #{}))
  ([env t seen]
   (cond
     (v/reified-term? t)
     (if-let [e (and (not (seen t)) (nat-expression env t))]
       (str "(" (str/join " " (map #(term-text env % (conj seen t)) e)) ")")
       "(…)")

     (sequential? t) (str "(" (str/join " " (map #(term-text env % seen) t)) ")")
     :else           (pr-str t))))

;; The cycle: a reified term renders as its expression, whose arguments are terms — an
;; unreified structural NAT compound, or another reified term, which renders as *its* expression.
(declare render-form)

;; The second cycle: a `(sentexHandle N)` subterm renders as the sentence N holds, whose
;; own subterms go back through `layout`.  `handle-layout` is below because it needs the
;; badge, so the two cannot be ordered.
(declare handle-layout)

(defn- nat-ref
  "A reified term, rendered as the expression it was minted from with **bold parens**.
  The opening paren links to the constant's own page — the one place its `natFormula`
  map, its materialized result types and its uses are listed — so the reified term is
  one click away and still never spelled out.

  A constant whose expression is not believed renders `(…)` rather than falling back to
  the raw symbol: the map can be defeated or gone while a use of the constant survives,
  and there the page cannot say what it denotes."
  [env k seen]
  (let [e (and (not (seen k)) (nat-expression env k))]
    [:span.nat
     [:a.nat-paren {:href  (str "/term?q=" (url-enc (pr-str k)))
                    :title "the reified term itself"} "("]
     (if e
       (interpose " " (map #(render-form env % (conj seen k)) e))
       [:span.muted {:title "no believed expression for this reified term"} "…"])
     [:span.nat-paren ")"]]))

(defn term-link
  "A role-colored link to a term's page (variables are not links; a reified term is its
  expression — `nat-ref`)."
  ([env t] (term-link env t #{}))
  ([env t seen]
   (cond
     (= :variable (v/term-role t)) [:span.t-var (pr-str t)]
     (= '. t)                      [:span.sx "."]   ; a rest marker is syntax, not a term
     (v/reified-term? t)           (nat-ref env t seen)
     ;; the href is the term as stored — what the page is *about* — and the text is how
     ;; the page writes it.  The two differ for a compound term holding a reified one
     :else [:a {:class (str "sx " (term-class env t))
                :href  (str "/term?q=" (url-enc (pr-str t)))}
            (term-text env t seen)])))

(def ^:private in-cx
  "The word between a sentence and the context it holds in.  The space after it is a
  no-break space, so a line never ends between `in` and the context."
  [:span.cx-in " in "])

(def ^:private rb-depths
  "How many steps the paren colours count along the spectrum before repeating —
  `--rb1` … `--rb9` (vaelii.css), the nine vaelii.com's stylesheet draws in the same
  order.  Nine because that is the scale the rest of the browser already counts along:
  a graph's series and the palette both start at red and wrap here."
  9)

(defn- paren
  "One parenthesis, coloured by nesting depth.  `depth` counts from 0 at a sentence's
  outermost paren and wraps at `rb-depths`, so a matching pair is one colour and no pair
  is the colour of the one inside it.  With `href`, the paren is a link there, in the
  same colour."
  ([depth s]
   [:span {:class (str "rb" (inc (mod depth rb-depths)))} s])
  ([depth s href]
   [:a {:class (str "rb" (inc (mod depth rb-depths))) :href href :title "the term itself"} s]))

(defn- term-compound?
  "Is `form` a ground compound term, a structural NAT: its functor is spelled as a function
  or a context (CapitalCamelCase), which no literal is headed by.  Its open paren links to
  its term page, as a reified term's does (`nat-ref`)."
  [form]
  (and (#{:individual :context} (v/term-role (first form)))
       (not-any? #(= :variable (v/term-role %)) (tree-seq sequential? seq form))))

(defn- sentex-reference
  "The id a `(sentexHandle N)` subterm names, or nil for any other form.

  A meta-sentex points at a stored sentence by its handle — `(except (sentexHandle 41))`
  hides one, `(exceptWhen <query> (sentexHandle 41))` guards a rule — and the handle is
  an ordinary ground compound rather than a reified term, so nothing else on the page
  treats it as a reference.  Matched by shape here rather than through
  `vaelii.impl.sentex/sentex-handle?`: this namespace holds no engine require (the
  ledger above), and the shape is the same four conditions that function tests."
  [form]
  (when (and (sequential? form)
             (= 'sentexHandle (first form))
             (= 2 (count form))
             (integer? (second form)))
    (second form)))

(def ^:private laid-out-connectives
  "The n-ary connectives a rule is broken across lines at, one argument per line."
  '#{and or})

(def ^:private badge-cols
  "The characters a badge occupies inside a sentence: `.sx .badge` (vaelii.css) sizes it
  to `2ch`, so a sentence expanded from a `(sentexHandle N)` starts two columns in."
  2)

(def ^:private docs-base
  "Where a `docs/…` reference in a comment links: the page in the public repository."
  "https://github.com/vaelii/vaelii/blob/develop/")

(def ^:private comment-token-re
  "One token `comment-text` marks up: a backquoted span, a `docs/…` page, a variable, a
  word, or an opening paren."
  #"`[^`]+`|docs/[\w/-]+\.md(?:#[\w-]+)?|\?[A-Za-z][\w-]*|[A-Za-z][\w-]*|\(")

(defn- term-shaped?
  "Whether word `w` is spelled as a term rather than as an English word: a camelCase
  predicate, a snake_case type, or a context or name with a second capital (`CxChange`,
  `QuantityFn`)."
  [w]
  (boolean (or (re-matches #"[a-z][a-z0-9]*[A-Z][A-Za-z0-9]*" w)
               (re-matches #"[a-z][a-z0-9]*(?:_[a-z0-9]+)+" w)
               (re-matches #"[A-Z][a-z0-9]+[A-Z][A-Za-z0-9]*" w))))

(defn- matching-paren
  "The index just past the `)` closing the `(` at `i` in `s`, or nil when none closes it."
  [^String s i]
  (loop [j i depth 0]
    (when (< j (count s))
      (case (.charAt s j)
        \( (recur (inc j) (inc depth))
        \) (if (= 1 depth) (inc j) (recur (inc j) (dec depth)))
        (recur (inc j) depth)))))

(defn- comment-formula
  "The form text `s` spells when it is a formula, else nil.  A formula parses to an EDN
  list headed by a connective or by a symbol `known?` answers for, and holds no comma: a
  prose parenthetical separates its items with commas, and EDN parses a comma as space."
  [known? s]
  (when-not (str/includes? s ",")
    (let [f (try (edn/read-string s) (catch Exception _ nil))]
      (when (and (seq? f) (symbol? (first f))
                 (or (contains? '#{implies and or not} (first f)) (known? (first f))))
        f))))

(defn- comment-text
  "A `comment`'s text with what it names marked up, inside its quotes: a formula renders
  as a sentence does (`render-form`), a variable in the variable colour, a word spelled
  as a term (`term-shaped?`) that a stored sentex mentions as that term's link, a
  backquoted span as a term, a formula or code, and a `docs/…` page as a link to it
  (`docs-base`).  Everything else is the literal's text.  Runs of whitespace collapse to
  one space, since a KB file wraps a comment to its line length."
  [{:keys [kb] :as env} text seen]
  (let [s      (str/replace (str/trim text) #"\s+" " ")
        known? (memoize #(some? (first (v/find-sentexes kb %))))
        m      ^java.util.regex.Matcher (re-matcher comment-token-re s)
        token  (fn [a b ^String tok]
                 (cond
                   (= "(" tok)
                   (let [e (matching-paren s a)
                         f (some->> e (subs s a) (comment-formula known?))]
                     (if f [(render-form env f seen) e] [tok b]))

                   (str/starts-with? tok "`")
                   (let [inner (subs tok 1 (dec (count tok)))
                         f     (comment-formula known? inner)]
                     (cond
                       (and (re-matches #"[A-Za-z][\w-]*" inner) (known? (symbol inner)))
                       [(term-link env (symbol inner) seen) b]
                       f     [(render-form env f seen) b]
                       :else [[:code inner] b]))

                   (str/starts-with? tok "docs/") [[:a {:href (str docs-base tok)} tok] b]
                   (str/starts-with? tok "?")     [[:span.t-var tok] b]
                   (and (term-shaped? tok) (known? (symbol tok)))
                   [(term-link env (symbol tok) seen) b]
                   :else [tok b]))]
    (loop [pos 0, out [:span.str-text]]
      (if (and (< pos (count s)) (.find m (int pos)))
        (let [a (.start m)
              [el end] (token a (.end m) (.group m))]
          (recur (long end) (conj out (subs s pos a) el)))
        [:span.sx.t-str "\"" (conj out (subs s pos)) "\""]))))

(defn- layout
  "`[element multi-line?]` for `form`, its first character `col` characters from the left
  margin.  The layout is Clojure's: a form spanning lines keeps its first argument beside
  the functor and aligns every later argument under it.

      (exceptWhen (dead ?x)
                  (implies (organism ?x)
                           (alive ?x)))

  An implication always spans lines, a connective over two or more arguments spans lines
  inside one, and any other compound spans lines when one of its arguments does.  A
  `(sentexHandle N)` subterm renders as the sentence N holds behind its badge
  (`handle-layout`); `seen` carries the handles on the path.  `depth` is the paren
  colour's; `in-rule?` is whether the form is an implication's part or a connective's
  argument below one."
  [env form seen col depth in-rule?]
  (cond
    (sentex-reference form)
    (let [h (sentex-reference form)]
      (if (seen [::handle h])
        [[:span.muted "#" h " (above)"] false]
        (handle-layout env h (conj seen [::handle h]) col)))

    (and (sequential? form) (seq form))
    (let [f     (first form)
          rule? (and (= 'implies f) (= 3 (count form)))
          conn? (and in-rule? (contains? laid-out-connectives f) (> (count form) 2))
          k     (+ col 2 (count (term-text env f seen)))
          args  (mapv #(if (and (= 'comment f) (string? %))
                         [(comment-text env % seen) false]
                         (layout env % seen k (inc depth) (or rule? conn?)))
                      (rest form))
          multi (boolean (or rule? conn? (some second args)))
          sep   (if multi (str "\n" (apply str (repeat k \space))) " ")]
      [[:span.sx (if (term-compound? form)
                   (paren depth "(" (str "/term?q=" (url-enc (pr-str form))))
                   (paren depth "("))
        (first (layout env f seen (inc col) (inc depth) false))
        (when (seq args) " ")
        (interpose sep (map first args))
        (paren depth ")")]
       multi])

    (sequential? form) [[:span.sx (paren depth "(") (paren depth ")")] false]
    (string? form)     (let [q (pr-str form)]
                         [[:span.sx.t-str "\"" [:span.str-text (subs q 1 (dec (count q)))] "\""]
                          false])
    :else              [(term-link env form seen) false]))

(defn render-form
  "Render a sentence (or subterm) with every atomic subterm an individually role-colored
  link, structure shown with parentheses, laid out by `layout`.  A form spanning lines is
  wrapped in `.sx-rule`, which keeps its newlines and indent.  A `(sentexHandle N)` subterm
  renders as **the sentence N holds**, linked, on every surface that prints a meta-sentex
  (a term-page row, the sentex page, a preview's `excepts` line)."
  ([env form] (render-form env form #{} 0))
  ([env form seen] (render-form env form seen 0))
  ([env form seen depth]
   (let [[e multi?] (layout env form seen 0 depth false)]
     (if multi? [:span.sx-rule e] e))))

(defn- readable
  "A sentex's sentence with the author's variable names restored, so a stored rule
  reads as it was written rather than as ?var0 / ?var1 — `vaelii.core/readable-sentence`."
  [s]
  (v/readable-sentence s))

(defn- justification-link [jid] [:a {:href (str "/justification/" jid)} "justification #" jid])

(def ^:private rule-runs
  "Per way a rule runs (`rule-run`): the badge's hue, the badge's word and what the sentex
  page says of it."
  {:forward-only {:hue "badge-forward" :word "forward rule"
                  :says "Forward chaining fires it and stores each conclusion. Backward proof does not use it."}
   :both         {:hue "badge-both" :word "rule, both ways"
                  :says "Forward chaining fires it and stores each conclusion, and backward proof uses it to answer goals."}
   :backward     {:hue "badge-backward" :word "backward rule"
                  :says "Backward proof uses it to answer goals and stores no conclusion. Forward chaining does not fire it."}
   :lazy-forward {:hue "badge-backward" :word "lazy-forward rule"
                  :says "Backward proof uses it, and a forward rule's join proves its conclusion when the join needs one. It stores no conclusion."}
   :inert        {:hue "badge-inert" :word "inert rule"
                  :says "Neither forward chaining nor backward proof runs it. It stays believed, indexed and findable by its terms."}
   :solve        {:hue "badge-solve" :word "solve rule"
                  :says "It runs in a solve alone, which derives its head in every answer set satisfying its body. Forward chaining and backward proof do not run it."}
   :choice       {:hue "badge-choice" :word "choice rule"
                  :says "Its head is a choice offered to a solve, not a truth to derive. Forward chaining and backward proof do not run it."}
   :constraint   {:hue "badge-constraint" :word "constraint rule"
                  :says "Its body is a nogood a solve grounds: a hard constraint excludes each answer set the body holds in, and a soft one counts a violation against it. Forward chaining and backward proof do not run it."}})

(defn- rule-run
  "How the rule record `s` runs, as a key of `rule-runs`, read off its `:effect` and
  `:engines`.  A choice or constraint head runs in a solve and nowhere else."
  [s]
  (let [e (set (:engines s))]
    (cond (= :choose (:effect s))          :choice
          (not= :derive (:effect s))       :constraint
          (and (e :forward) (e :backward)) :both
          (e :forward)                     :forward-only
          (e :lazy)                        :lazy-forward
          (e :backward)                    :backward
          (e :solve)                       :solve
          :else                            :inert)))

(defn- badge-kind
  "What the badge of record `s` says of its kind: `{:hue :word :run}`, `:run` the key of
  `rule-runs` and nil for a fact.  A negation's hue outranks every other: a reader who
  misses a `not` has the sentex backwards, and no other confusion costs that."
  [s]
  (let [rule?    (some? (:antecedent s))
        neg?     (v/negative? s)
        strength (:strength s)
        run      (when rule? (rule-run s))
        {:keys [hue word]} (rule-runs run)]
    {:run  run
     :hue  (cond neg?                    "badge-neg"
                 rule?                   hue
                 (= :monotonic strength) "badge-monotonic"
                 (= :default strength)   "badge-default"
                 :else                   "badge-derived")
     :word (str (when neg? "negative ")
                (cond rule?    (str word (when (:defeasible s) ", defeasible"))
                      strength (str (name strength) " premise")
                      :else    "derived"))}))

(defn- badge
  "The circle that stands in for a sentex's bare handle before its sentence.  Its colour
  says the kind (`badge-kind`, docs/web.md has the scale), a ring means derived, and a
  dimmed circle is stored and not believed (OUT).  The `title` carries the reading, and the
  link and the `title` carry the handle.  It links to the sentex page, which says the
  same in sentences (`badge-reading`), and keys only on the record `s` the caller already
  fetched, plus belief (`state-tag`), so a remote-attached browser badges identically."
  [env s]
  (let [h             (:id s)
        in?           (believed? env h)
        {:keys [hue word]} (badge-kind s)
        classes       (cond-> ["badge" hue]
                        (nil? (:strength s)) (conj "badge-open")
                        (not in?)            (conj "badge-out"))]
    [:a.badge-link {:href (str "/sentex/" h) :title (str word " · #" h (when-not in? " · out"))}
     [:span {:class (str/join " " classes)}]]))

(defn- belief-span
  "`content` in a span classed by whether sentex `h` is believed: `.sx-in` or `.sx-out`,
  which set how much of its colour each sentence part keeps (`--lit`, vaelii.css).  Each
  nested sentex sets its own, so an IN sentence inside an OUT meta-sentex reads as IN."
  [env h & content]
  [:span {:class (if (believed? env h) "sx-in" "sx-out")} content])

(defn- sentex-ref
  "A colour-coded handle badge (see `badge`) placed BEFORE the sentence, then the
  sentence rendered with individually-linked subterms.  It takes the **record**, which
  every listing already holds — re-fetching it by handle here is the N+1 that turns one
  page into one store read (or one round-trip) per row.

  `seen` is the expansion path `render-form` carries, so a sentence reached through a
  `(sentexHandle N)` subterm cannot expand its way back to the one it came from."
  ([env s] (sentex-ref env s #{}))
  ([env s seen]
   (belief-span env (:id s) (badge env s) (render-form env (readable s) seen))))

(defn- handle-layout
  "`layout`'s arm for a `(sentexHandle N)` subterm: the badge and the sentence `h` holds,
  the sentence starting `badge-cols` past `col`, and whether it spans lines."
  [{:keys [kb] :as env} h seen col]
  (if-let [s (v/sentex kb h)]
    (let [[e multi?] (layout env (readable s) seen (+ col badge-cols) 0 false)]
      [(belief-span env h (badge env s) e) multi?])
    [[:span.muted "#" h " (gone)"] false]))

(defn- handle-ref
  "`sentex-ref` for a caller holding only a handle — a justification's antecedent, a
  contradictor, a `(sentexHandle N)` subterm — so it fetches the one record it needs.  A
  handle whose record is gone renders as such rather than vanishing."
  ([env h] (handle-ref env h #{}))
  ([{:keys [kb] :as env} h seen]
   (if-let [s (v/sentex kb h)]
     (sentex-ref env s seen)
     [:span.muted "#" h " (gone)"])))

(defn- state-tag
  "The belief-state pill for a sentex: IN when the JTMS believes it, else the `why-not`
  reason (superseded / defeated / excepted / inert / unsupported / not-stored), followed for a placed
  defeat by the declarations its nogood convicts through, and for an inert tuple by the
  grounds of the length it breaks.  The sentex page shows it always; a list row shows only the reason and only when the row is OUT — a believed
  row's dimmed badge already reads as believed.  The one authority `in?` folds every
  not-believed reason into, and the page reads it back."
  [{:keys [kb] :as env} h]
  (if (believed? env h)
    [:span.tag.tag-in "IN"]
    (let [{:keys [reason grounds binding]} (v/why-not kb h)
          r  (name reason)
          hs (concat (map :handle grounds) (:grounds binding))]
      (list [:span.tag {:class (str "tag-" r)} r]
            (when (seq hs)
              [:span.muted " through " (interpose ", " (map #(handle-ref env %) hs))])))))

(defn- edit-link
  "A way into the editor: an htmx GET of `/edit`, swapped into the `#editor` panel.  A
  button rather than a link, so `hx-boost` leaves it alone and a press on the sentence
  beside it is an ordinary text selection.

  `query` is `handles=<h>` for one row, or `q=<term>` for a term — which opens on the
  sentexes the term's most direct index reaches (`term-main-handles`)."
  [query label]
  [:button.sx-edit {:type "button" :hx-get (str "/edit?" query)
                    :hx-target "#editor" :hx-select "unset" :hx-swap "innerHTML"
                    :aria-label label} "edit"])

(defn- sentex-actions
  "What a reader does to one sentex: Copy, Edit, Remove.  The sentex page's action bar,
  and the menu a right-click on a badge opens (vaelii.js fetches it from
  `/sentex-actions`), so the two are one definition.  Copy opens the assert form seeded
  with the sentex; Edit opens the editor panel on it; Remove opens the retraction's
  confirmation in the same panel, which writes nothing until its own button is pressed."
  [h]
  (let [panel {:type "button" :hx-target "#editor" :hx-select "unset" :hx-swap "innerHTML"}]
    [:div.sx-actions {:role "menu"}
     ;; a link, so the body's boost makes it the navigation it is
     [:a.button {:role "menuitem" :href (str "/assert?copy=" h)} "Copy"]
     [:button (assoc panel :role "menuitem" :hx-get (str "/edit?handles=" h)) "Edit"]
     [:button.danger (assoc panel :role "menuitem" :hx-get (str "/retract?handles=" h))
      "Remove"]]))

(def ^:private term-ops
  "What each operation is called on its button, on its panel and on the jobs screen."
  {"rename" {:verb "Rename" :named? true}
   "copy"   {:verb "Copy"   :named? true}
   "remove" {:verb "Remove" :named? false}})

(defn- term-actions
  "The term bar: the operations on the term as a whole, beside its heading.  Each opens
  its confirmation in the editor panel and writes nothing until that panel's button."
  [term]
  [:div.sx-actions.term-actions
   (for [[op {:keys [verb]}] term-ops]
     [(if (= "remove" op) :button.danger :button)
      {:type "button" :hx-get (str "/term-op?op=" op "&q=" (url-enc (pr-str term)))
       :hx-target "#editor" :hx-select "unset" :hx-swap "innerHTML"}
      verb])])

(defn- sentex-line
  "The content of an `.sx-item`: the badge of `s`, then its sentence in its context, dimmed
  by belief (`belief-span`), with `after` behind the context.  The badge and the sentence
  are two boxes: a newline in a rule's layout returns to the left edge of the row, so the
  sentence gets its own block and the indent and trailing context count from where it
  starts."
  [env s & after]
  (list (badge env s)
        [:span.sx-body
         (belief-span env (:id s)
                      (render-form env (readable s)) in-cx (term-link env (:context s)))
         after]))

(defn- sentex-row
  "One sentex row (`sentex-line`), and the control that opens the editor on it.
  `data-h` is what an out-of-band swap addresses after a save, so a row can be replaced
  where it sits.

  The row carries no selection state and no script.  A sentence is text a reader copies,
  so a press-drag across it selects that text; editing is the row's own `[edit]`."
  [env s]
  [:li {:data-h (:id s) :class "sx-item"}
   (sentex-line env s
                ;; the reason pill says WHY a row is OUT (superseded / defeated /
                ;; unsupported) — shown only when not believed, so a believed row stays
                ;; clean.  Its proof is a click away on the sentex page.
                (when-not (believed? env (:id s)) (list " " (state-tag env (:id s))))
                " " (edit-link (str "handles=" (:id s)) (str "edit sentex " (:id s))))])

(defn- sx-list
  "A list of sentex rows, labelled for a reader who arrives at it out of context."
  [label & rows]
  [:ul.sx-list {:aria-label label} rows])

(def ^:private complete-cap
  "How many completions a keystroke asks for.  A list longer than a reader takes in at a
  glance is one they read instead of one they pick from."
  12)

(def ^:private complete-q-cap
  "The longest prefix `/complete` answers.  The route is reachable per keystroke and,
  through the daemon, by whoever can reach it, so the prefix is bounded like every other
  untrusted read on this page."
  128)

(defn- code-area
  "A sentence editor: the `<textarea>` that holds the value and takes the keys, the
  highlight layer vaelii.js paints behind it (rainbow parens by depth, strings, numbers,
  variables), and the list it drops under the caret from `/complete`.  Enter lands under
  the form's first argument and Tab re-indents the line.  The field submits as a bare
  textarea would, so a page with no script is still editable."
  [{:keys [name id rows value placeholder submit?]}]
  [:div.ed (cond-> {:data-ed ""}
             submit?      (assoc :data-ed-submit "")
             (= 1 rows)   (assoc :class "ed ed-1"))
   [:pre.ed-hl {:aria-hidden "true"} [:code.ed-code]]
   [:textarea (cond-> {:class "ed-in" :name name :rows (or rows 6) :spellcheck "false"
                       :autocomplete "off" :autocapitalize "off" :wrap "off"}
                id          (assoc :id id)
                placeholder (assoc :placeholder placeholder))
    value]
   [:ul.ed-complete {:role "listbox" :aria-label "term completions" :hidden "hidden"}]])

(defn- fold-button
  "A region's index, and the control that folds the region away — shown in the top
  border the way a terminal monitor numbers a box for its hotkey, and answering both the
  click on the number and the digit `n` pressed anywhere off a text field.  The region it
  folds is the nearest `[data-panel]` ancestor, so one script serves every framed region
  without knowing which page drew it."
  [n]
  [:button.panel-n {:type "button" :aria-expanded "true"
                    :title (str "fold this region away — or press " n)} n])

(defn- panel
  "One framed region: a square box whose title sits in its top border, carrying the
  index the page counts it by.  `n` is that index, shown before the title and doubling as
  the fold control; `title` is the rest of the heading, and everything after it is the
  region's content."
  [n title & body]
  [:section.panel (when n {:data-panel n})
   [:h2.panel-title (when n (fold-button n)) title]
   body])

(defn- visit-mark
  "A hidden element naming the page for the reader's browsing history, which vaelii.js
  records in localStorage and the front page's `#history` panel lists.  `kind` is
  `term`, `literal` or `rule`, and `cls` the role class a term's entry is coloured by."
  [kind href label cls]
  [:span {:hidden true :data-visit kind :data-href href :data-label label :data-class cls}])

(def ^:private history-panel
  "The front page's browsing history: empty and hidden as served, and filled by
  vaelii.js from localStorage, since the server keeps no per-reader state."
  [:section#history.panel {:hidden true}
   [:h2.panel-title "Browsed"]
   [:div.history-body]])

(def ^:private history-cap
  "The most entries one history row holds: vaelii.js's `HISTORY_CAP`."
  50)

(defn- history-sentexes
  "The `Literals` or `Rules` row of the browsing history: each of the handles `hs` in the
  order given, one clipped `sentex-line` with its remove button.  The server renders it
  because vaelii.js keeps only the handle of a visited sentex and builds no markup from
  localStorage."
  [{:keys [kb] :as env} hs]
  (let [ss (into [] (keep #(v/sentex kb %)) (take history-cap hs))]
    (prime-belief! env (map :id ss))
    (frag (for [{h :id :as s} ss]
            [:div.sx-item.sx-clip.history-item
             (sentex-line env s)
             [:button.history-x {:type       "button"
                                 :aria-label (str "remove sentex " h " from the history")
                                 :data-kind  (if (:antecedent s) "rule" "literal")
                                 :data-href  (str "/sentex/" h)} "×"]]))))

(defn- sentex-list [env sentexes]
  (let [ss (sort-by :id sentexes)]
    (prime-belief! env (map :id ss))
    (if (seq ss)
      (sx-list "sentexes" (for [s ss] (sentex-row env s)))
      [:p.muted "none"])))

(defn- justification-list
  "`justifications` as links, each with its rule and conclusion.  The sentex `self` the page
  is about reads \"this sentex\": it would otherwise repeat on every row."
  [env justifications self]
  (let [ds  (sort-by :id justifications)
        ref #(if (= self %) [:span.muted "this sentex"] (handle-ref env %))]
    (prime-belief! env (into (mapv :consequence ds) (filter integer?) (map :informant ds)))
    (if (seq ds)
      [:ul (for [{:keys [id informant consequence]} ds]
             [:li (justification-link id) " — "
              (if (integer? informant)
                (list "via " (ref informant))
                [:span.muted "via " (pr-str informant)])
              " ⇒ " (ref consequence)])]
      [:p.muted "none"])))

(def ^:private legend
  [:p.legend "Terms: "
   [:a.sx.t-type "unary predicate"] " · "
   [:a.sx.t-pred "binary predicate"] " · " [:a.sx.t-pred.t-pred-n "ternary+ predicate"] " · "
   [:a.sx.t-conn "connective"] " · " [:a.sx.t-context "context"] " · "
   [:a.sx.t-ind "individual"] " · " [:a.sx.t-num "literal"] " · "
   [:span.t-var "?variable"] "."])

(def ^:private badge-legend
  [:p.legend "The circle before a sentence: "
   [:span.badge.badge-monotonic] "monotonic · "
   [:span.badge.badge-default] "default · "
   [:span.badge.badge-neg] "negation · "
   [:span.badge.badge-derived.badge-open] "derived · "
   [:span.badge.badge-forward] "forward rule · "
   [:span.badge.badge-backward] "backward rule · "
   [:span.badge.badge-both] "rule, both ways · "
   [:span.badge.badge-inert] "inert rule · "
   [:span.badge.badge-choice] "choice rule · "
   [:span.badge.badge-constraint] "constraint rule · "
   [:span.badge.badge-solve] "solve rule · "
   [:span.badge.badge-default.badge-out] "not believed."])

;; ---- belief state (the sentex page) -------------------------------------

(defn- rewrite-arrow [env [old rep]]
  [:span (term-link env old) " → " (term-link env rep)])

(defn- belief-detail
  "When a sentex is stored but OUT, render *why* from `why-not`, one arm per `:reason`.  A
  reason with no arm of its own prints its name, so no OUT sentex goes unexplained.
  Nothing for a believed sentex: its proof is the \"Supported by\" section."
  [{:keys [kb] :as env} h]
  (let [{:keys [reason superseded-by contradicted-by grounds binding conviction support rule
                exception via withdrawn-by convicted]}
        (v/why-not kb h)]
    (case reason
      :superseded
      [:div.belief
       [:p [:b "Superseded"] " by an equality merge — stored but not believed, restated "
        "under its class representative as "
        (if-let [nh (:handle superseded-by)]
          (handle-ref env nh)
          (render-form env (:sentence superseded-by))) "."]
       (when-let [rw (seq (:rewrites superseded-by))]
         [:p.muted "rewrites: " (interpose ", " (map #(rewrite-arrow env %) rw))])]
      :defeated
      [:div.belief
       [:p [:b "Defeated"] " — contradiction resolution forced it OUT."]
       (when (seq contradicted-by)
         [:ul (for [c contradicted-by]
                [:li "contradicted by " (handle-ref env (:handle c))
                 in-cx (term-link env (:context c))
                 (when-let [dc (:defeat-class c)] [:span.tag (str "class " (name dc))])])])
       (when (seq grounds)
         [:ul (for [g grounds]
                [:li "convicted through " (handle-ref env (:handle g))
                 in-cx (term-link env (:context g))])])
       (when (and (empty? contradicted-by) (empty? grounds))
         [:p.muted "the winning sentex has since been retracted; nothing contradicts it now."])]
      :inert
      [:div.belief
       [:p [:b "Inert"] " — held OUT by the labeller before any contest: it is never "
        "believed, forms no nogood and fires no rule"
        (when-let [{:keys [length min via]} binding]
          (list ". Its length breaks " (if length (str "length " length) (str "floor " min))
                ", bound through " (term-link env via)))
        (when-not (or binding conviction)
          ". An open application in it respells in no context it reaches")
        "."]
       (when-let [m (:message conviction)] [:p m])
       (when (seq (:grounds binding))
         [:ul (for [g (:grounds binding)]
                [:li "bound through " (handle-ref env g)])])]
      :excepted
      [:div.belief
       [:p [:b "Excepted"] " — the rule " (handle-ref env rule) " states its own exception, "
        [:span.sx (pr-str exception)] ", which holds here"
        (when (seq via)
          (list " for the binding from " (interpose ", " (map #(handle-ref env %) via))))
        "."]]
      :unsupported
      [:div.belief
       [:p [:b "Unsupported"] " — not a premise, and every justification has an OUT argument."]
       (when (seq support)
         [:ul (for [j support]
                [:li (justification-link (:justification j)) " — missing "
                 (interpose ", " (map #(handle-ref env %) (:missing j)))])])]
      :withdrawn
      [:div.belief
       [:p [:b "Withdrawn"] " — the network holds it IN, and its own context does not "
        "believe it: every justification rests on a sentex a defeat in force here hides."]
       [:ul (for [{:keys [handle context vantage defeat]} withdrawn-by]
              [:li "hidden: " (handle-ref env handle) in-cx (term-link env context)
               ", by " [:a {:href (str "/sentex/" defeat)} "the defeat"]
               in-cx (term-link env vantage)])]]
      :forced-conclusion
      [:div.belief
       [:p [:b "Forced conclusion"] " — not a premise, and a firing supporting it is held "
        "void: the firing concludes a forced-monotonic literal from antecedents that are not "
        "forced-monotonic."]
       [:ul (for [{:keys [justification informant not-forced-monotonic]} convicted]
              [:li (justification-link justification) " by " (handle-ref env informant)
               (when (seq not-forced-monotonic)
                 (list " — a " [:code "forced_monotonic_predicate"] " declaration on "
                       (interpose ", " (map #(term-link env %) not-forced-monotonic))
                       " would lift it"))])]]
      (when reason [:div.belief [:p [:b (name reason)]]]))))

;; ---- index-organized term page --------------------------

(def ^:private group-cap
  "How many sentexes a single index group renders at a time.  The O(1) stored count is
  always shown, so a large root reports its true size; the rest arrives a page at a time
  as the reader scrolls (`more-rows`)."
  60)

(defn- more-rows
  "The continuation sentinel that ends a capped list: a row which fetches the next page
  and **replaces itself** with it.  `revealed` is htmx's intersection trigger; `click` and
  Enter are the same request for a reader who asks.  `tr?` makes the sentinel a row
  spanning the columns of a `<table>`; `div?` a `<div>` card for the funnel; every other
  list takes the plain `<li>` shape."
  ([href label] (more-rows href label nil))
  ([href label {:keys [tr? div?]}]
   ;; `hx-target`/`hx-select` are set on the body so every boosted link swaps #main, and
   ;; they are inherited — so a sentinel says explicitly that it replaces *itself* with
   ;; the rows it fetched, and selects nothing out of them
   (let [attrs {:hx-get href :hx-trigger "revealed, click, keyup[key=='Enter']"
                :hx-target "this" :hx-select "unset" :hx-swap "outerHTML"
                :hx-indicator "#page-indicator"}
         cell  [:span.more-cell {:role "button" :tabindex "0"} [:span.muted label]]]
     (cond
       tr?   [:tr.more attrs [:td.more-td {:colspan "2"} cell]]
       div?  [:div.more attrs cell]
       :else [:li.more attrs cell]))))

(defn- fact-body
  "The positive body of a stored fact sentence — `(P a b)` unchanged, `(not (P a b))`
  unwrapped — so an argument position reads off the same body the `[:argument-root]` root keys."
  [sent]
  (if (and (sequential? sent) (= 'not (first sent)) (sequential? (second sent)))
    (second sent)
    sent))

(def ^:private arg-position-cap
  "The highest argument position a term page asks about.  The roots are maintained per
  1-based position, so the positions a term sits at are found by asking each in turn —
  which is only bounded because a stored predicate's arity is.  Twelve is past the widest
  arity the shipped vocabulary declares, and a term sitting deeper than that is in the
  term index either way, so it reaches the page through the remainder groups."
  12)

(def ^:private remainder-scan
  "How many of a term's index entries are walked to work out what the roots did not
  claim.  A root's extent has an O(1) count, and the remainder has none: the only way to
  know a sentex is not in a root is to look at it.  Fifty thousand is two orders past the
  widest term the shipped ontology reaches (`ExceptWhen`, 28,579) and costs ~0.4 s at the
  walk's measured rate; a term as wide as `genl` on a large store reaches millions of
  entries, and walking them all costs tens of times that.  A term the walk runs out on
  gets no remainder groups and a line saying the page did not look."
  50000)

(def ^:private group-sort-cap
  "How many sentexes a group orders by context before it pages in the index's own order
  instead.  The order costs a `pr-str` of a context per member plus the sort, and the page
  shows sixty rows of it: at a functor group of millions, as `genl`'s is on a large store,
  that cost grows with the group and is paid twice per page.
  Past the cap the group pages in the order the index read it in, which is reproducible
  for an unchanged store — the one property paging needs — and is the order
  `comment-rows` already pages the predicate extents in."
  20000)

(def ^:private extent-defer-cap
  "How large a root extent may be and still have its first page of rows built with the
  page.  Past it, the group renders its O(1) count and fetches the rows on the reveal every
  later page takes (`group-rows`).  Reading a root extent materializes every handle under
  the root, and the page shows sixty.  The number is also `group-sort-cap`, the size past
  which the group stops ordering by context; 20,000 is ~8 ms of that build."
  20000)

(defn- mentions?
  "Does `form` hold `term` anywhere inside it?  A rule's own two halves are what this is
  asked of — which side of the arrow the term is on — so it walks one formula rather
  than reading an index, and a formula is bounded where an extent is not."
  [term form]
  (cond (= term form)      true
        (sequential? form) (boolean (some #(mentions? term %) form))
        :else              false))

(defn- direct-arg-positions
  "The 1-based argument positions at which `term` sits directly in some stored fact:
  exactly the positions the predicate-scoped argument roots (`[pred pos term]`) maintain.
  Rules are excluded.  Asked of the counts, not the records: `count-with-arg` is one O(1)
  read per predicate declaring an argument at the slot."
  [kb term]
  (into (sorted-set)
        (for [p    (range 1 (inc arg-position-cap))
              :when (pos? (v/count-with-arg kb p term))]
          p)))

(defn- term-index-groups
  "Every stored sentex containing `term`, grouped by the **index** that reaches it, each
  group carrying its cheap count: the argument-position groups `[:argument-slot pos]`, then
  the term-index remainder `[:term-index]` split into rules and deeper nestings, then the
  predicate extent `[:predicate-extent]` and the context root `[:context-root]` (when the
  term is a context).

  **The order goes from what the term IS to what uses it**: argument position 1, 2, … N,
  then the rules that conclude about it, the rules that require it, the deeper nestings,
  then the extents, **largest-last**.  **An extent carries a `:fetch`, not a `:sentexes`**
  (`group-sentexes`), and a large one is `:deferred?` (`extent-defer-cap`).

  `text` is how the term is *written* in each group's key.  Answers `{:groups :remainder?}`.
  The two remainder groups are the term index **minus** what a root claimed, which no count
  answers: the walk reads at most `remainder-scan` records, `:remainder?` says whether it
  finished, and a term it ran out on gets no remainder groups."
  ([kb term] (term-index-groups kb term (pr-str term)))
  ([kb term text]
   (let [positions (direct-arg-positions kb term)
         arg-grps  (for [p positions
                         :let [ss (v/sentexes-with-arg kb p term)]
                         :when (seq ss)]
                     ;; `:pos` is what the group is *about*, and the concept graph reads
                     ;; its ego edges off these groups rather than paying a second extent
                     ;; read — an arrow needs to know which end of the fact the term is
                     {:label (str "Argument position " p)
                      :idx (str "[:argument-slot " p " " text "]")
                      :pos p :count (v/count-with-arg kb p term) :sentexes ss})
         ctx?      (= :context (v/term-role term))
         ;; a root's claim is decided per record rather than against a set of every id a
         ;; root holds: building that set is the extent read the walk is bounded to avoid
         ;; (`genl` holds millions).  An argument claims a record only at a position
         ;; `direct-arg-positions` probes, so a deeper one stays in the remainder
         claimed?  (fn [s]
                     (let [body (fact-body (:sentence s))]
                       (or (and (sequential? body) (= term (first body)))
                           (and (not (:antecedent s))
                                (sequential? body)
                                (boolean (some #(= term %) (take arg-position-cap (rest body)))))
                           (and ctx? (= term (:context s))))))
         ;; A lower bound on the term index out of counts already in hand: every sentex a
         ;; root holds is one the term index holds, so the widest root is at least that many
         ;; entries.  Past the scan the walk will be truncated, which the page learns without
         ;; paying for the walk (the `genl` term index costs 0.9 s before its first record,
         ;; a large context's 4.2 s).  **The context root is in the bound**: the term index
         ;; is keyed on `kv/sentex-terms`, the content terms *plus the context*, so a
         ;; context's extent bounds it below as a predicate's does.
         fn-count  (v/count-with-functor kb term)
         cx-count  (if ctx? (v/count-in-context kb term) 0)
         floor     (reduce max 0 (list* fn-count cx-count (map :count arg-grps)))
         scanned   (when (<= floor remainder-scan)
                     (into [] (take (inc remainder-scan)) (v/find-sentexes kb term)))
         whole?    (and (<= floor remainder-scan) (<= (count scanned) remainder-scan))
         remainder (when whole? (remove claimed? scanned))
         rules     (filter :antecedent remainder)
         ;; a rule that both concludes about the term and reads it is listed under the
         ;; conclusion: what a rule *says* about a term outranks what it needs of it
         concl     (filter #(mentions? term (:consequent %)) rules)
         conds     (remove #(mentions? term (:consequent %)) rules)
         nested    (remove :antecedent remainder)
         ;; the two extents, largest last (the docstring's one size rule), and each a
         ;; `:fetch` rather than a seq: the read behind an extent is the one read on this
         ;; page that is not bounded by the index, so it happens when a reader reaches the
         ;; group and not when the page is built (`group-sentexes`)
         extents   (sort-by :count
                            (concat
                             (when (pos? fn-count)
                               [{:label "Predicate extent" :idx (str "[:predicate-extent " text "]")
                                 :count fn-count :extent? true
                                 :deferred? (> fn-count extent-defer-cap)
                                 :fetch #(v/sentexes-with-functor kb term)}])
                             (when (pos? cx-count)
                               [{:label "Context extent" :idx (str "[:context-root " text "]")
                                 :count cx-count :extent? true
                                 :deferred? (> cx-count extent-defer-cap)
                                 :fetch #(v/sentexes-in-context kb term)}])))]
     {:remainder? whole?
      :groups
      (concat
       arg-grps
       (when (seq concl)
         [{:label "Rule conclusion" :idx "[:rule-consequent] · [:term-index]"
           :count (count concl) :sentexes concl}])
       (when (seq conds)
         [{:label "Rule condition" :idx "[:rule-antecedent] · [:term-index]"
           :count (count conds) :sentexes conds}])
       (when (seq nested)
         [{:label "Nested elsewhere" :idx (str "[:term-index " text "]")
           :count (count nested) :sentexes nested}])
       extents)})))

(defn- group-sentexes
  "The records behind one group of `term-index-groups`: the seq it already holds, or — for
  an extent — the root read its `:fetch` defers.  Called where rows are rendered and
  nowhere else, so a page that shows an extent's count without its rows does no root read."
  [{:keys [sentexes fetch]}]
  (if fetch (fetch) sentexes))

;; ---- ordering what a page lists ------------------------------------------
;; A listed term may be a **NAT**, so a page's order is taken off the printed form, not
;; `compare`.  `str` on a compound honours `*print-length*` / `*print-level*`, so under an
;; ambient bound two long terms print to one prefix; these two release the bounds around
;; the printing.  `naming/print-key` holds the same guard for the engine.

(def ^:private print-key
  "`x` printed as an ordering key, with the print bounds released."
  guard/edn-str)

(defn- sort-by-once
  "`coll` as a vector ordered by `(f x)`, with `f` called once per element:
  decorate-sort-undecorate, where `sort-by` calls its key fn at every comparison.  The
  print bounds are released for the whole sort, so `f` may print."
  [f coll]
  (binding [*print-length* nil *print-level* nil *print-meta* false]
    (mapv second (sort-by first (mapv (fn [x] [(f x) x]) coll)))))

(defn- by-print-key
  "`coll` as a vector ordered by its elements' printed form (`sort-by-once`)."
  [coll]
  (sort-by-once pr-str coll))

(defn- comment-first
  "0 for a `(comment term \"…\")` sentex and 1 for everything else: the leading component
  of `group-order`'s key, so a term's own description is the first row of its group.  Part
  of the sort key, not a prepended row, because paging re-slices this sequence at an
  offset and a prepend would repeat the comment on every page."
  [s]
  (let [body (fact-body (:sentence s))]
    (if (and (sequential? body) (= 'comment (first body))) 0 1)))

(defn- group-order
  "A group's sentexes in display order: the term's own comment, then by context, then
  handle.  **Handle order is allocation order, by design**: paging re-slices this sequence
  at an offset, so a later request must reproduce the order, and a content ordering moves
  under every write.  It is not a ranking, and nothing is dropped; `group-rows`' sentinel
  walks the whole group.  `n` is the group's stored count, and a group past
  `group-sort-cap` pages in the index's own order, which is reproducible for an unchanged
  store."
  [sentexes n]
  (if (<= (long n) group-sort-cap)
    (sort-by-once (juxt comment-first (comp print-key :context) :id) sentexes)
    sentexes))

(def ^:private derived-scan
  "How many of a group's sentexes the hide-derived filter walks to fill one page.

  Hiding the derived rows turns a page from a slice into a search, and a search with no
  bound is the whole extent: a term whose group is millions of derived facts and one
  premise would read all of them to render one row.  Five thousand is 83 pages' worth of
  records for one page of rows, so a group where one row in eighty is a premise still
  fills a page in one request, and a sparser one fills it over several — each bounded, each
  resumable, none of them the extent."
  5000)

(defn- group-page
  "One page of a group, as `{:rows :next-offset}`: the sentexes to render, and the offset
  into `ordered` the continuation resumes at (nil when exhausted).  With derived rows
  shown, a page is `group-cap` consecutive records.  With them hidden, the page is the
  premises among at most `derived-scan` consecutive records and `:next-offset` is just
  past the last record **looked at**, so an offset means the same under either setting."
  [ordered offset hide?]
  (if-not hide?
    (let [rows (into [] (take (inc group-cap)) (drop offset ordered))]
      {:rows        (into [] (take group-cap) rows)
       :next-offset (when (> (count rows) group-cap) (+ offset group-cap))})
    (loop [ss   (seq (drop offset ordered))
           seen 0
           kept []]
      (if (or (nil? ss) (= group-cap (count kept)) (= seen derived-scan))
        {:rows kept :next-offset (when (some? ss) (+ offset seen))}
        (recur (next ss) (inc seen)
               (cond-> kept (some? (:strength (first ss))) (conj (first ss))))))))

(defn- group-rows
  "One group's `page` (`group-page`) as rows, plus the sentinel that fetches the next one.
  Belief for the page is read once (`prime-belief!`).  `total` is the group's stored
  count.  With derived rows hidden the sentinel carries no number, since how many of the
  records behind it are premises is unknown.  `page` is **nil** for a group whose first
  page is deferred (`extent-defer-cap`): it renders as the sentinel alone, at offset 0."
  [env term g {:keys [rows next-offset] :as page} total]
  (prime-belief! env (map :id rows))
  ;; data-h is what a save's out-of-band swap addresses; the handle badge dims an
  ;; OUT sentex and `sentex-row` names the reason it is out
  (list (map #(sentex-row env %) rows)
        (when-let [next-offset (if (nil? page) 0 next-offset)]
          (more-rows (str "/term/rows?q=" (url-enc (pr-str term))
                          "&g=" g "&offset=" next-offset)
                     (if (:hide-derived? env)
                       "show more"
                       (str "show " (max 0 (- total next-offset)) " more"))))))

(def ^:private term-edit-cap
  "How many of a term's sentexes its `[edit]` opens the editor on.  A textarea holding a
  term's whole extent is not an editor — `isa` reaches 115 sentexes at its first index
  alone — so the control takes the head of the most direct group and the page keeps the
  rest, each row with its own `[edit]`."
  20)

(defn- term-main-handles
  "The handles a term's `[edit]` opens the editor on: the head of its **most direct**
  index group, which is the group the term page renders first.  Empty for a term the KB
  does not reach."
  [{:keys [kb]} term]
  (if (nil? term)
    []
    ;; an extent is the last group `[edit]` will head, and a deferred one it will not head
    ;; at all: `[edit]` opens what the term *is*, and reading millions of handles to find
    ;; twenty rows that say nothing about the term is the one read this control cannot
    ;; justify
    (let [gs (:groups (term-index-groups kb term))
          {n :count :as g} (or (first (remove :extent? gs)) (first gs))]
      (if (:deferred? g)
        []
        (into [] (comp (take term-edit-cap) (map :id))
              (group-order (group-sentexes g) n))))))

(defn- index-group
  "Render one index group as a framed region: its number, its name, the index key it
  reads and its stored count in the top border, then its sentexes a page at a time.
  `page` is the group's first page, built once by the caller so the page's single belief
  read covers exactly the rows it is about to render."
  [env term [g {:keys [label idx count]} page]]
  [:div.idxgrp {:data-panel (inc g)}
   [:h4 (fold-button (inc g)) label " " [:code idx] " " [:span.muted "· " count " stored"]]
   (sx-list label (group-rows env term g page count))])

;; ---- what a batch would do (`v/preview`) --------------------------------
;; `check-edit` says whether each line would be *admitted*; `v/preview` (docs/preview.md)
;; says what the batch would *mean*, which lines can fail together while passing one at a
;; time (two lines each admissible alone can be a disjointness clash).  It stores nothing,
;; so the editor runs it on every change of the text.

(def ^:private preview-max-results
  "How many lines of each half of the diff to render.  A batch whose conclusions cascade
  has an answer in the thousands and a panel has no use for it; `preview` reports
  `:bounded?` when the cap bit, and the panel says so rather than implying it showed
  everything."
  50)

(defn- consequence-item
  "One consequence, linked where there is something to link to.  A datum the batch would
  **create** has no handle until it is stored — `preview` reports nil rather than the
  number it briefly held — so the line that explains it is the rule that would conclude
  it, which the preview carries.  A datum that already exists (a default this batch
  defeats, one it revives) keeps its handle either way, and that one links."
  [env {:keys [handle sentence context premise? justification reason]}]
  [:li
   (if handle (handle-ref env handle) (render-form env sentence))
   in-cx (term-link env context)
   (when reason [:span {:class (str "tag tag-" (name reason))} (name reason)])
   (when-let [rule (:rule justification)]
     (list " " [:span.muted "by "] (render-form env rule)))
   (when (and (not premise?) (nil? justification) (nil? reason))
     [:span.muted " derived"])
   (when handle
     (list " " [:a.muted {:href (str "/why/" handle)} "why"]))])

(defn- consequence-group
  "One collapsed group.  `<details>` so the summary is the whole panel until a reader
  asks, and so opening one costs no script and no request — the consequences are already
  rendered, just folded."
  [env {:keys [class glyph label items open?]}]
  (when (seq items)
    [:details.p-cons {:class class :open (when open? "open")}
     [:summary [:b glyph] " " (count items) " " label]
     [:ul.p-cons-list (map #(consequence-item env %) items)]]))

(defn- refusal-items
  "The lines the KB would not take, and the conclusions it would drop — one group,
  because a reader asking \"what will not land?\" does not care which side of the
  assert/derive line the answer came from.  Each keeps its own type tag, which is where
  that distinction actually matters."
  [{:keys [refused violations]}]
  (concat
   (for [p refused]
     {:tag (name (:type p :error)) :message (:message p)
      :where (when (:index p) (str "line " (inc (:index p))))})
   (for [v violations]
     {:tag (name (:violation v :dropped))
      ;; the same two shapes `violation-rows` handles: an entry about no sentence printed
      ;; the string "nil — ", and the two kinds carrying `:message` at the top level
      ;; printed the fallback instead of the message they had
      :message (let [m (or (:message (:detail v)) (:message v)
                           "dropped on the derivation path")]
                 (if-let [s (:sentence v)] (str (pr-str s) " — " m) m))
      :where "a conclusion"})))

(defn- consequence-panel
  "What a batch would do, as `v/preview` answers it.  `heading` names the batch, since
  the same panel reads an open edit and whatever batch an extension previews
  (`consequences`).

  The refused group leads and opens itself: it is the one a reader must not miss, and it
  is what catches a stratification cycle or a disjointness clash *before* anything is
  stored.  The other two are counts until asked for."
  [env heading {:keys [believed-added believed-removed contradictions bounded?] :as result}]
  (let [bad (refusal-items result)]
    (list
     [:h5.p-cons-head heading]
     (when (seq bad)
       [:details.p-cons.p-cons-bad {:open "open"}
        [:summary [:b "⚠"] " " (count bad) " refused"]
        [:ul.p-cons-list
         (for [{:keys [tag message where]} bad]
           [:li [:span.tag tag] " " message
            (when where [:span.muted " · " where])])]])
     ;; a dilemma is not a refusal and not a withdrawal — both sides stay believed — so
     ;; it gets its own group, open, because it is the answer a reader asserting a
     ;; negation would otherwise never be given
     (when (seq contradictions)
       [:details.p-cons.p-cons-tie {:open "open"}
        [:summary [:b "⚡"] " " (count contradictions) " now contested"]
        [:ul.p-cons-list
         (for [{:keys [sides]} contradictions]
           [:li (interpose [:span.muted " ⟷ "]
                           (for [{:keys [handle sentence]} sides]
                             [:span (if handle (handle-ref env handle) (render-form env sentence))
                              (when handle
                                (list " " [:a.muted {:href (str "/why/" handle)} "why"]))]))])]])
     (consequence-group env {:class "p-cons-add" :glyph "+" :label "newly believed"
                             :items believed-added})
     (consequence-group env {:class "p-cons-drop" :glyph "−" :label "no longer believed"
                             :items believed-removed})
     (when (and (empty? bad) (empty? contradictions)
                (empty? believed-added) (empty? believed-removed))
       [:p.muted "Nothing follows: this adds no belief and withdraws none."])
     (when bounded?
       [:p.hint "This preview was cut short at " preview-max-results
        " lines per group — there is more than is shown."])
     [:p.hint "Nothing here is stored. The KB is exactly as it was before this ran."])))

(defn consequences
  "The consequence panel for `batch` (`{:add [[sentence context] …] :remove [handle …]}`)
  over the render env's KB: `v/preview` capped at `preview-max-results` per group, rendered
  under `heading`.  A read — `preview` stores nothing and hands the KB back at the same
  handles — but it asserts and rolls back to get there, so a route calling it is a
  writer for the duration (an extension's `:write` route)."
  [{:keys [kb] :as env} heading batch]
  (consequence-panel env heading (v/preview kb batch {:max-results preview-max-results})))

;; ---- what followed from a commit ----------------------------------------
;; A commit reports the lines it stored.  What the KB did with them comes from two
;; mechanisms the callout keeps apart:
;;
;;   - a **rule fired**: a real derived sentex with a justification, believed in the JTMS
;;     sense, with a handle and a proof a click away.
;;   - a **type subsumes**: `(genl dog animal)` plus `(dog Muffet)` makes Muffet an animal,
;;     and the engine never materializes `(animal Muffet)`; matching fans a functor out over
;;     its genl spec closure (docs/taxonomy.md).  There is no record or justification to
;;     link, and the claim is answered on demand by `isa?` / `ask`.
;;
;; The second kind is not called "derived", since no sentex of it is stored.

(def ^:private callout-cap
  "How many consequences the callout names before it counts the rest.  Three is the
  prompt's number and it is about attention, not cost: a wall of conclusions is read as a
  log, and the point of the callout is that it is *not* one."
  3)

(defn- entailed-supertypes
  "The type claims a stored `(T X)` makes true without anyone stating them: every strict
  supertype of `T`, as `(super X)`.

  `thing` is dropped — it is the root every type reaches, so it is true of everything and
  informative about nothing — and so is any supertype the same batch stated outright,
  which is not news either.  Nearest-first, so what is dropped by the cap is the vaguest
  claim rather than an arbitrary one."
  [{:keys [kb]} sentexes]
  (let [stated (into #{} (map :sentence) sentexes)]
    (for [sx    sentexes
          :let  [[t x :as s] (:sentence sx)]
          :when (and (= 2 (count s)) (symbol? t) (not (coll? x)))
          ;; nearest first: a nearer supertype has the *larger* up-closure of its own,
          ;; since everything above it is above the further one too; then the name, so
          ;; two supertypes the same distance up are ordered by something a reader can
          ;; account for.  The list is capped, so the tie decides which claims are shown
          super (v/sort-by-content (juxt #(- (count (v/genls kb %))) print-key)
                                   compare (v/genls kb t))
          :let  [claim (list super x)]
          :when (and (not= super t) (not= 'thing super) (not (stated claim)))]
      {:sentence claim :context (:context sx) :type t :individual x})))

(defn- callout-item
  "One consequence line: the claim, and the one-level `because` under it."
  [env {:keys [sentence handle justification type individual]}]
  [:li.callout-line
   (if handle (handle-ref env handle) (render-form env sentence))
   (if justification
     [:span.muted.callout-why " because "
      (interpose ", " (map #(render-form env %) (:antecedents justification)))
      (when-let [r (:rule justification)]
        (list " and the rule " (render-form env r)))
      (when handle
        (list " · " [:a {:href (str "/why/" handle)} "proof"]))]
     [:span.muted.callout-why " because "
      (render-form env (list type individual))
      ", and every " (render-form env type) " is a "
      (render-form env (first sentence))])])

(defn- derived-callout
  "**You didn't say this, but it follows** — the consequences of a commit, capped.

  `result` is `v/edit-with-consequences!`'s answer and `stored` the sentexes the batch
  wrote.  Renders nothing at all when nothing followed: a callout reading \"0 new
  conclusions\" is worse than silence, because it makes the empty case as loud as the
  interesting one."
  [env result stored]
  (let [derived (into [] (remove :premise?) (:believed-added result))
        typed   (entailed-supertypes env stored)
        all     (concat derived typed)
        shown   (take callout-cap all)
        more    (- (count all) (count shown))]
    (when (seq all)
      [:div.callout
       [:h4 "You didn't say this, but it follows"]
       [:ul.callout-list (for [c shown] (callout-item env c))]
       (when (pos? more)
         [:p.muted "and " more (if (= 1 more) " more consequence" " more consequences")
          " — every one of them is on the "
          [:a {:href "/stats"} "statistics page"] "."])])))

(defn stored-sentexes
  "What a write stored, as the assert form shows it: a row per stored sentex, then the
  callout of what followed from them (`derived-callout`).  `result` is
  `v/edit-with-consequences!`'s answer."
  [{:keys [kb] :as env} result]
  (let [ss (keep #(v/sentex kb %) (flatten (:added result)))]
    (list (sentex-list env ss)
          (derived-callout env result ss))))

;; ---- the hierarchy trees, one level at a time ---------------------------
;; A hierarchy is wide as well as deep, and the front page opens against a KB of unchosen
;; size (the catalog loads ontologies with hundreds of thousands of `genl` edges).  A
;; level is therefore read from the index when it is opened, and every list is paged like
;; an index group.

(def ^:private tree-cap
  "How many direct children of one node render at a time."
  50)

(def ^:private front-cap
  "How many rows the front page's flat lists — core predicates, disjointness — render at
  a time."
  50)

(def ^:private sortable-cap
  "How many rows a flat list will realize in order to sort them.  Alphabetical order is
  worth reading and adds no work at the size the shipped schema has; realizing an
  imported ontology's every comment to show fifty of them is not worth it, so past this
  the list is in index order and says so."
  1000)

(def ^:private lattice-cap
  "How many `genlCx` edges the context lattice will read to find its roots.  A root
  is a context that no edge makes a sub of anything, which is a property of the *whole*
  edge set — there is no partial answer — so beyond this the page says it cannot root a
  lattice and lists the contexts instead.  Every KB we ship or import states contexts in
  the hundreds; this is the guard, not the working path."
  5000)

(defn- child-terms
  "The direct sub-nodes of `node` under transitivity relation `pred`, deduped (one edge
  asserted in two contexts is one child).  For `genl` the answer is the closure's one-step
  adjacency (`direct-specs`), so a child a `covering`, `separating` or `partition`
  declaration installs is a child.  For any other relation it is one `query` the
  predicate-scoped argument root answers (`[pred 2 node]`, docs/indexing.md).  The cost is
  this node's own fan-out."
  [kb pred node]
  (if (= 'genl pred)
    (v/direct-specs kb node)
    (->> (v/sentexes-matching kb (list pred '?sub node) '?ctx)
         (keep (fn [s] (let [[_ sub super] (:sentence s)]
                         (when (and sub (= super node)) sub))))
         (distinct))))

(defn- parent-terms
  "The direct super-nodes of `node` under transitivity relation `pred` — `child-terms`'
  mirror.  For `genl` the closure's one-step adjacency (`direct-genls`), so a parent a
  cover declaration installs is drawn as a stated parent is.  For any other relation the
  pattern binds `node` in argument position **1**, which `query` answers from the
  predicate-scoped argument root (the node `[pred 1 node]`), so the cost is this
  node's own fan-*in* rather than the number of edges in the KB.  Deduped for the same
  reason — one edge asserted in two contexts is two sentexes and one parent."
  [kb pred node]
  (if (= 'genl pred)
    (v/direct-genls kb node)
    (->> (v/sentexes-matching kb (list pred node '?super) '?ctx)
         (keep (fn [s] (let [[_ sub super] (:sentence s)]
                         (when (and super (= sub node)) super))))
         (distinct))))

(defn- expandable?
  "Whether a tree node gets a disclosure control.  For `genl`, whether the closure's
  one-step adjacency (`direct-specs`) holds a child, which counts a child a cover declaration
  installs and costs the node's own fan-out.  For any other relation, `count-with-arg`
  at position 2: the facts holding `t` there, summed over every binary predicate, so an
  *upper* bound on having stated children.  Wrong only in the safe direction: a node
  whose second-position facts are all something else opens to \"none\", and no real
  child is ever hidden."
  [kb pred t]
  (if (= 'genl pred)
    (boolean (seq (v/direct-specs kb t)))
    (pos? (v/count-with-arg kb 2 t))))

(defn- tree-caret
  "The control that opens a node's children, and the id it is addressed by.  A checkbox
  and its label, not a `<details>`/`<summary>`, which would swallow the click on a term
  inside it.  `attrs` is what the caret fetches, empty for a node whose children are
  already on the page.  CSS hides `ul.tree-kids` until the box is checked, so a page with
  no script still opens a level.  The id keys on the edge (`pred`, `node`): a type with two
  parents is a different disclosure under each."
  [pred node attrs]
  (let [id (str "tg" (Math/abs ^int (hash [pred node])))]
    (list
     [:input.tree-tog (merge {:type "checkbox" :id id} attrs)]
     [:label.tree-tog-l {:for id :title (str "subterms of " (pr-str node))}])))

(defn- tree-rows
  "One level of a hierarchy: `node`'s direct children from `offset`, each either a leaf
  or a disclosure that fetches its own children the first time it is opened.  Bare
  `<li>`s, so the same call answers the page and the continuation that extends it."
  [{:keys [kb] :as env} pred node offset]
  (let [;; a `genl` level is the closure's realized adjacency set, so it is always
        ;; sorted.  For another relation, an upper bound on the level's width decides
        ;; `sortable` without reading the level: a node too wide to sort is a node whose
        ;; children nobody reads alphabetically anyway.  One count per predicate holding
        ;; `node` at argument 2 and never the extent (`core/count-with-arg`)
        sortable (or (= 'genl pred) (<= (v/count-with-arg kb 2 node) sortable-cap))
        kids     (cond->> (child-terms kb pred node) sortable by-print-key)
        shown    (into [] (comp (drop offset) (take (inc tree-cap))) kids)
        ;; a child's disclosure asks for *its own* children; the sentinel asks for more
        ;; of this level, which is the one place `node` is the right node
        href     (fn [n off] (str "/tree/rows?rel=" (url-enc (str pred))
                                  "&node=" (url-enc (str n)) "&offset=" off))]
    (list
     (for [t (take tree-cap shown)]
       (if (expandable? kb pred t)
         ;; `hx-select="#main"` is set on the body so every boosted link swaps the main
         ;; column, and it is **inherited** — against a fragment of bare rows it selects
         ;; nothing and the open would swap in nothing.  So a caret says explicitly that
         ;; it selects nothing out of what it fetched, exactly as a sentinel does.
         [:li (tree-caret pred t {:hx-get (href t 0) :hx-trigger "change once"
                                  :hx-target "next ul.tree-kids" :hx-select "unset"
                                  :hx-swap "innerHTML" :hx-indicator "#page-indicator"})
          (term-link env t)
          [:ul.tree-kids [:li.muted "…"]]]
         [:li (term-link env t)]))
     (when (> (count shown) tree-cap)
       ;; a count only where one was paid for.  Unsorted, `kids` was never realized and
       ;; the O(1) width spans every predicate holding `node` in second position, so it
       ;; would be an over-count dressed as a fact
       (more-rows (href node (+ offset tree-cap))
                  (if sortable
                    (str "show " (- (count kids) offset tree-cap) " more")
                    "show more"))))))

(defn- context-roots
  "The tops of the `genlCx` lattice — the contexts no edge makes a sub of anything —
  or **nil** past `lattice-cap`, which is the page's cue to say so rather than draw a
  lattice it cannot root."
  [kb]
  (when (<= (v/count-with-functor kb 'genlCx) lattice-cap)
    (let [es (edges-of kb 'genlCx)]
      (by-print-key (set/difference (set (map second es)) (set (map first es)))))))

(defn- elided
  "The line a bounded list ends with when it did not show everything: what was shown, out
  of what there is.  A truncated listing that does not announce itself is worse than no
  env."
  [shown total note]
  [:p.muted "showing " shown " of " total (when note (str " — " note))])

(defn- comment-rows
  "One page of the core-predicate list, from `offset`, with the sentinel that fetches the
  next.

  Read from the **predicate extent**, not from `(comment ?term ?text)`.  A wholly-open
  pattern gives the trie nothing to narrow on, so it fans over every child token at every
  level: `take` would then bound the records fetched and not the candidates enumerated,
  and showing fifty rows would cost a walk of every commented term in the KB.  The extent
  is one posting set per context, and a page out of it costs a page."
  [{:keys [kb] :as env} offset]
  (let [total (v/count-with-functor kb 'comment)
        ;; the term, then the text: a term carrying two comments ties on the term alone,
        ;; and the tie falls to the order `sentexes-with-functor` returns, which is stable
        ;; while the stored comments do not change.  `core-context/comment-of` keys the
        ;; same pair for the same reason
        rows  (cond->> (v/sentexes-with-functor kb 'comment)
                (<= total sortable-cap)
                (sort-by-once (juxt (comp print-key second :sentence)
                                    (comp print-key #(nth (:sentence %) 2 nil)))))
        shown (into [] (comp (drop offset) (take (inc front-cap))) rows)
        page  (take front-cap shown)]
    ;; the extent is what is *stored*; belief is the page's own question, asked in one read
    (prime-belief! env (map :id page))
    (list
     (for [s     page
           :when (and (not (v/negative? s)) (believed? env (:id s)))
           :let  [[_ _ text] (:sentence s)]]
       ;; one clipped line; the whole comment hovers as a title and is on the term's
       ;; own page, so the front page stays scannable
       [:li.sx-item.sx-clip {:title text :data-h (:id s)} (sentex-line env s)])
     (when (> (count shown) front-cap)
       (more-rows (str "/front/rows?section=predicates&offset=" (+ offset front-cap))
                  (str "show " (- total offset front-cap) " more"))))))

(defn- disjoint-rows
  "One page of the disjointness list, out of the pairs `disjoint-pairs` computed.  They
  arrive realized because a metatype separates its members by being *consulted* rather
  than by storing a clique, so the induced half has to be worked out either way — and
  both halves are bounded by the separations an ontology declares rather than by its
  size."
  [env pairs offset]
  (let [ordered (by-print-key pairs)
        shown   (into [] (comp (drop offset) (take (inc front-cap))) ordered)]
    (list
     (for [[a b] (take front-cap shown)]
       [:li (term-link env a) " ⊥ " (term-link env b)])
     (when (> (count shown) front-cap)
       (more-rows (str "/front/rows?section=disjoint&offset=" (+ offset front-cap))
                  (str "show " (- (count ordered) offset front-cap) " more"))))))

;; ---- the small useful amount --------------------------------------------
;; The first fifty of a set in an order nobody chose is an arbitrary sample on a real
;; corpus.  Where a **cheap ranking** exists the page shows the top of it and says what
;; the whole is; otherwise the list is capped and continues on scroll.  A ranking that
;; costs more than the page is not used: ordering the type tree's 6,260 children of
;; `thing` by subtree size measured 2.2 s, so the tree stays in index order and lazy.

(def ^:private summary-cap
  "How many rows a **ranked summary** shows.  A summary does not continue: its point is
  the top of an order, not the whole of a set, and a reader who wants the rest wants a
  different page rather than more of this one."
  12)

(def ^:private stats-table-cap
  "How many rows the contexts-by-size table shows before its scroll sentinel."
  25)

(def ^:private context-rank-cap
  "How many contexts will be sized in order to rank them.  `count-in-context` is an O(1) read,
  but it is one read *each* — 13,196 of them is 150 ms in process and 13,196 HTTP
  round-trips under `--attach` — so past this the pages say they cannot rank rather than
  quietly spending it."
  20000)

(defn- contexts-by-size
  "Every context that holds something, largest first — or **nil** past `context-rank-cap`.

  The one ranking on either page that answers *what is this KB about*: a corpus's mass is
  not spread evenly over its contexts, and the handful holding most of it name the
  subject far better than any fifty of them in alphabetical order.  Ties break on name, so
  the order is a function of the content and not of the order `v/contexts` returns."
  [kb]
  (let [cs (vec (v/contexts kb))]
    (when (<= (count cs) context-rank-cap)
      (->> cs
           (map (fn [c] [c (v/count-in-context kb c)]))
           (filter (comp pos? second))
           (sort-by (juxt (comp - second) (comp print-key first)))))))

(defn- separating-types
  "How many types are separated from anything, and the ones separated from the most.  At a
  size where the pairs are unreadable, what a reader can use is *which* types the
  ontology's partitions are about — and each one links to its own page, where its own
  partners are now listed.

  One pass and a frequency count.  Sorting the pairs themselves by name, to show fifty of
  27,196, measured **4.5 s** and was the whole cost of the front page."
  [pairs]
  (let [freq (frequencies (into [] cat pairs))]
    {:distinct (count freq)
     :top      (take summary-cap (sort-by (juxt (comp - val) (comp print-key key)) freq))}))

(defn- stat-card
  "One headline number: a big count over a small label.  `cls` tags a card by state
  (e.g. \"stat-warn\" / \"stat-ok\") so a health count reads as one at a glance."
  ([label n] (stat-card label n nil))
  ([label n cls]
   [:div {:class (str "stat" (when cls (str " " cls)))}
    [:span.stat-n (or (commas n) n)] [:span.stat-l label]]))

;; ---- pages --------------------------------------------------------------

(defn default-page [{:keys [kb types] :as env}]
  (let [roots     (context-roots kb)
        genls     (v/count-with-functor kb 'genl)
        comments  (v/count-with-functor kb 'comment)
        ctx-count (count (v/contexts kb))
        pairs     (disjoint-pairs kb)]
    (render env "upper ontology"
            history-panel
            ;; what this KB *is*, before anything it contains.  Four O(1) reads, and the
            ;; question a reader landing on an unfamiliar corpus asks first
            ;; the four destinations on one line, each named by what it does.  The page
            ;; each one opens says what it is for
            (panel 1 "This knowledge base"
                   [:div.stats-grid
                    (stat-card "Sentexes" (v/sentex-count kb))
                    (stat-card "Types" (count @types))
                    (stat-card "Contexts" ctx-count)
                    (stat-card "Terms" (v/term-count kb))]
                   [:p.actions
                    [:a.action {:href "/demo"} "Watch belief change"] " · "
                    [:a.action {:href "/reasoning"} "What this ontology can work out"] " · "
                    [:a {:href "/levels"} "Lookup-to-query stack"] " · "
                    [:a.action {:href "/assert"} "Assert a sentex"]]
                   legend
                   badge-legend)
            (panel 2 (list "Contexts " [:span.muted "(genlCx)"])
                   (if roots
                     [:ul.tree (for [r roots]
                                 (if (expandable? kb 'genlCx r)
                                   ;; the root's children are already on the page, so its
                                   ;; caret opens the level rather than fetching it
                                   [:li (tree-caret 'genlCx r {:checked "checked"})
                                    (term-link env r)
                                    [:ul.tree-kids (tree-rows env 'genlCx r 0)]]
                                   [:li (term-link env r)]))]
                     ;; no lattice to draw, so the question changes from "how do they nest" to
                     ;; "where is the knowledge" — which the sizes answer and an alphabetical
                     ;; first-fifty never did
                     (let [ranked (contexts-by-size kb)]
                       (list
                        [:p.muted "Too many genlCx edges to root a lattice — the contexts "
                         "holding the most, instead."]
                        (if ranked
                          (list
                           [:ul (for [[c n] (take summary-cap ranked)]
                                  [:li (term-link env c)
                                   [:span.muted " — " (commas n) " sentexes"]])]
                           [:p.muted (commas (count ranked)) " of " (commas ctx-count)
                            " contexts hold something. " [:a {:href "/stats"} "All of them by size"]
                            ", or search from the header."])
                          [:p.muted (commas ctx-count) " contexts — too many to size. "
                           "Search from the header."])))))
            (panel 3 (list "Types " [:span.muted "(genl, rooted at thing)"])
                   ;; the root is drawn open, as the context roots are: the heading names it, and
                   ;; a tree whose stated root is not on the page is indistinguishable from a list of orphans
                   [:ul.tree [:li (tree-caret 'genl 'thing {:checked "checked"})
                              (term-link env 'thing)
                              [:ul.tree-kids (tree-rows env 'genl 'thing 0)]]]
                   [:p.muted (commas genls) " genl edges — a subtype list opens when you open its node."])
            ;; titled by what it is.  On the shipped schema every commented term is engine
            ;; vocabulary; on an imported corpus there are 105,882 of them and calling that
            ;; "core predicates" is a claim the page cannot make
            (panel 4 (if (> comments sortable-cap) "Documented terms" "Core predicates")
                   [:ul.sx-list (comment-rows env 0)]
                   (when (> comments sortable-cap)
                     [:p.muted (commas comments) " terms carry a " [:code "comment"]
                      " — index order, too many to sort. Search from the header for one."]))
            (panel 5 "Disjointness"
                   (if (<= (count pairs) front-cap)
                     [:ul (disjoint-rows env pairs 0)]
                     (let [{:keys [distinct top]} (separating-types pairs)]
                       (list
                        [:p.muted (commas (count pairs)) " separated pairs, declared and "
                         "metatype-induced, over " (commas distinct) " types — too many to read as "
                         "pairs, so: the types separated from the most. Any type's own separations "
                         "are on its page."]
                        [:ul (for [[t n] top]
                               [:li (term-link env t)
                                [:span.muted " — disjoint from " (commas n)
                                 (if (= 1 n) " type" " types")]])])))))))

(defn tree-rows-page
  "One node's children, as bare rows — what a disclosure fetches when it is opened, and
  what its `show more` sentinel fetches to extend it."
  [env pred node offset]
  (frag (tree-rows env pred node offset)))

(defn front-rows-page
  "One more page of a front-page list."
  [env section offset]
  (frag (case section
          "predicates" (comment-rows env offset)
          "disjoint"   (disjoint-rows env (disjoint-pairs (:kb env)) offset)
          "")))

(def ^:private ledger-cap
  "How many contradictions / conflicts the page lists.  Unlike the violations these are
  **unbounded** — `contradictions` reports every represented dilemma the KB holds — so
  this is the only thing standing between a page and a corpus's whole disagreement.

  Small, because a ledger row is not a name: it is one or two whole sentences with every
  subterm linked, so fifty of them was 60 KB and the bulk of the page.  The headline card
  above already gives the count; what the list is for is seeing what one *looks* like, and
  the rest arrives on scroll."
  12)

(defn- context-count-rows
  "One page of the contexts-by-size table, from `offset`, ending in the sentinel that
  fetches the next when it scrolls into the viewport.  `ranked` is `contexts-by-size`'s answer, so
  the rows are the top of an order rather than a slice of an arbitrary one — which is what
  makes a capped table an *answer* and not a truncation."
  [env ranked offset]
  (let [shown (into [] (comp (drop offset) (take (inc stats-table-cap))) ranked)]
    (list
     (for [[c n] (take stats-table-cap shown)]
       [:tr [:td (term-link env c)] [:td.num (commas n)]])
     (when (> (count shown) stats-table-cap)
       (more-rows (str "/stats/rows?section=contexts&offset=" (+ offset stats-table-cap))
                  (str "show " (commas (- (count ranked) offset stats-table-cap)) " more")
                  {:tr? true})))))

(def ^:private clash-cap
  "How many standing disjointness clashes the page lists."
  50)

(defn- ledger-rows
  "One page of a reasoning-health ledger — contradictions, conflicts, dropped derivations
  — from `offset`, ending in the scroll sentinel that fetches the next.  `row` renders one
  entry; `section` names the ledger to the continuation route, which re-reads it.

  Re-reading is the right thing rather than a compromise: a ledger is a function of the KB
  as it is *now*, so a continuation asks the same question the page asked."
  [section items offset row]
  (let [shown (into [] (comp (drop offset) (take (inc ledger-cap))) items)]
    (list
     (map row (take ledger-cap shown))
     (when (> (count shown) ledger-cap)
       (more-rows (str "/stats/rows?section=" section "&offset=" (+ offset ledger-cap))
                  (str "show " (commas (- (count items) offset ledger-cap)) " more"))))))

(defn- contradiction-rows
  "The represented dilemmas `ds` (`v/contradictions`), a page at a time.  Belief for the
  page is one batched read — each row renders two sentexes and badges both."
  [env ds offset]
  (prime-belief! env (mapcat #(map :handle (:sides %))
                             (take (+ offset ledger-cap 1) ds)))
  (ledger-rows "contradictions" ds offset
               (fn [d] [:li (interpose " ⇄ " (map #(handle-ref env (:handle %)) (:sides d)))])))

(defn- conflict-rows
  "The irreducible clashes among known-true content `cs` (`v/conflicts`), a page at a
  time."
  [env cs offset]
  (ledger-rows "conflicts" cs offset
               (fn [c] [:li (interpose " ⇄ " (map #(handle-ref env (:handle %)) (:sides c)))])))

(defn- violation-row
  "One `violations` entry as a list item: its kind, then whichever of its sentence,
  context, run and message it carries.  A `:handle` a caller added draws the sentence with
  its badge; the entry itself names none, so a `/stats` load reads no record for it."
  [env v]
  ;; **Not every entry is about a sentence.**  The cross-context reports and both sweep
  ;; notices carry a `:detail` and no `:sentence` or `:context`.  `:message` sits at the
  ;; top level on `:non-confluent` and `:aggregate` and under `:detail` elsewhere.  The
  ;; present-field arms are seqs, not `[:span …]` wrappers, so an entry with a sentence
  ;; renders the same markup.
  [:li [:span.tag (name (:violation v))]
   (when-let [s (:sentence v)]
     (list " " (if-let [h (:handle v)] (handle-ref env h) (render-form env s))))
   (when-let [c (:context v)] (list in-cx (term-link env c)))
   (when-let [r (:run v)] [:span.muted " · run " r])
   (when-let [m (or (:message (:detail v)) (:message v))]
     [:span.muted " — " m])])

(defn- violation-rows
  "The filed ledger of dropped derivations (`filed-violations`), a page at a time.  The
  ledger accumulates across runs and is capped at the newest 1000, so which run dropped a
  conclusion is part of the entry rather than something the reader can infer from where
  it sits."
  [{:keys [kb] :as env} offset]
  (ledger-rows "violations" (v/filed-violations kb) offset #(violation-row env %)))

(defn stats-rows-page
  "One more page of a stats-page list — what its scroll sentinel fetches.  Every section is
  recomputed rather than carried: each is a function of the KB, so a continuation asks the
  same question the page asked and gets the same order."
  [{:keys [kb] :as env} section offset]
  (frag (case section
          "contexts"       (context-count-rows env (contexts-by-size kb) offset)
          "contradictions" (contradiction-rows env (v/contradictions kb) offset)
          "conflicts"      (conflict-rows env (v/conflicts kb) offset)
          "violations"     (violation-rows env offset)
          "")))

(defn- exposed-clashes-section
  "The **standing** disjointness question: every term holding two types some context can
  see as disjoint, where each membership was admissible where it was written.  It sits
  behind a control because `exposed-clashes` computes on demand and is not filed.
  `settle` reports a clash as it *arises*, so a KB that arrived all at once, such as an
  imported corpus, holds clashes nothing reports until something asks."
  [{:keys [kb] :as env} asked?]
  [:div
   [:h3 "Standing disjointness clashes"]
   [:p.muted "A term holding two types some context sees as disjoint, where each "
    "membership was admissible where it was written. Computed on demand, not filed as "
    "it arises."]
   (if-not asked?
     [:p [:a.action {:href "/stats?clashes=1"} "Ask the KB"]
      [:span.muted " — one pass over the separations it declares."]]
     (let [cs (v/exposed-clashes kb)]
       (if (empty? cs)
         [:p "No term is jointly visible under two disjoint types. "
          [:span.muted "Computed just now, not read from a ledger."]]
         [:div
          ;; **Each half is a `[type context]` pair, and both halves are links** (handed
          ;; whole, the pair would take `term-link`'s fallback arm).  The context is half of
          ;; what the row says: a membership admissible where it was written is only
          ;; interesting beside *where*.  The `:violation` guard covers a second entry shape:
          ;; a kind this does not know renders its own message rather than blanks.
          [:ul (for [{:keys [violation detail]} (take clash-cap cs)]
                 [:li
                  (if (= :disjoint violation)
                    (list (term-link env (:term detail)) " holds "
                          (interpose ", "
                                     (for [h (:held detail)]
                                       (let [[t c] (if (sequential? h) h [h nil])]
                                         (list (term-link env t)
                                               (when c
                                                 (list " " [:span.muted "in "]
                                                       (term-link env c))))))))
                    (list [:span.tag (name violation)] " "
                          (or (:message detail) "a standing clash")))
                  (when-let [vf (seq (:visible-from detail))]
                    [:span.muted " — visible together from "
                     (interpose ", " (for [c vf] (term-link env c)))])])]
          (when (> (count cs) clash-cap)
            (elided clash-cap (count cs) nil))])))])

(defn- nogoods-section
  "The contradictions and conflicts the placed nogoods come to, behind a control.

  The settle stores a `(contradicts …)` where it places a nogood, so the card above counts
  them in one index read.  What it does not file is the reading: whether a placement is a
  dilemma or a conflict at its context, whether that context believes and sees it, and
  which declarations convicted it.  Each is a belief read at the placement's own context,
  so the lists cost a read per placement — minutes on a corpus holding tens of thousands
  of them — and a page load pays none of it.  `placed` is the card's count."
  [{:keys [kb] :as env} asked? placed]
  [:div
   [:h3 "Placed nogoods"]
   (if-not asked?
     [:p [:a.action {:href "/stats?nogoods=1"} "Read the contradictions and conflicts"]
      [:span.muted " — each of the " (commas placed) " placements read at its own context."]]
     (let [ds (v/contradictions kb)
           cs (v/conflicts kb)]
       (if (and (empty? ds) (empty? cs))
         [:p "No placed nogood stands as a contradiction or a conflict. "
          [:span.muted "Computed just now, not read from a ledger."]]
         (list
          (when (seq ds)
            [:div
             [:h3 "Contradictions " [:span.muted "(represented dilemmas, believed at :default)"]]
             [:ul (contradiction-rows env ds 0)]])
          (when (seq cs)
            [:div
             [:h3 "Conflicts " [:span.muted "(irreducible clashes among known-true content)"]]
             [:ul (conflict-rows env cs 0)]])))))])

(defn- block-tally
  "Over every type in `types`: how many types the KB answers each part of the definitional
  block for, as `[[label n] …]` with the type count.  One `describe` per type, each a
  progress report to `progress!`, which throws on a cancel."
  [kb types progress!]
  (let [ts     (by-print-key types)
        blocks (doall
                (for [[i t] (map-indexed vector ts)
                      :let [_ (progress! {:phase :describe :done i :total (count ts)})
                            d (v/describe kb t)]
                      :when (= :type (:role d))]
                  (into {} (map (juxt :part :value)) (:definitional-block d))))
        has?   (fn [b k] (not= :missing (get b k :missing)))
        count* (fn [f] (count (filter f blocks)))]
    {:types (count blocks)
     :rows  [["comment" (count* #(has? % :comment))]
             ["positive example" (count* #(has? % :positive-examples))]
             ["negative example" (count* #(has? % :negative-examples))]
             ["both examples" (count* #(and (has? % :positive-examples)
                                            (has? % :negative-examples)))]
             ["parent" (count* #(has? % :parents))]
             ["every listed sibling decided"
              (count* #(not-any? (comp #{:missing} :separation) (:rows (:siblings %))))]
             ["kind" (count* #(has? % :kind))]
             ["arity class" (count* #(has? % :arity-class))]]}))

(defn- block-tally-job
  "Run `block-tally` over `kb`'s types as a read job and return its id.  The tally rides
  in the summary's metadata, as a quality reading does."
  [kb types]
  (jobs/submit {:label (str "Definitional block tally of " (kb-name kb)) :kind :blocks
                :kb-name (kb-name kb) :kb-owner (job-owner kb) :result-url "/stats"}
               (fn [progress!] (with-meta {} {:tally (block-tally kb types progress!)}))))

(defn- block-tally-section
  "How many types hold each part of the definitional block: the newest finished tally over
  `kb` (matched by `job-owner`), a link to a running one, and the button that runs
  another as a job (`/stats/blocks`).  A page load describes no type."
  [{:keys [kb]}]
  (let [js      (filterv #(and (= :blocks (:kind %)) (= (job-owner kb) (:kb-owner %)))
                         (jobs/jobs))
        done    (first (filter #(= :done (:status %)) js))
        running (first (filter #(#{:running :cancelling} (:status %)) js))]
    [:div
     [:h3 "Definitional blocks " [:span.muted "(types holding each part)"]]
     (when-let [{n :types rows :rows} (:tally (meta (:summary done)))]
       [:table.stats-table
        [:thead [:tr [:th "Part"] [:th.num "Types"] [:th.num (str "of " (commas n))]]]
        [:tbody (for [[label k] rows]
                  [:tr [:td label] [:td.num (commas k)] [:td.num (commas (- n k)) " missing"]])]])
     (if running
       [:p "A tally is running: " [:a {:href "/jobs"} "job " (:id running)] "."]
       [:form {:method "post" :action "/stats/blocks"}
        [:button.primary {:type "submit"}
         (if done "Count again" "Count the parts of every type's block")]
        [:span.muted " — one describe per type, run as a " [:a {:href "/jobs"} "job"]
         "; a finished tally is kept for an hour."]])]))

;; ---- the concept graph at the top of a term page ------------------------
;; The three type lines say a term's supertypes, subtypes and disjointness exactly; the
;; picture gives its *shape* (a leaf or a hub, what points at it).  It renders **live**,
;; server-drawn with no click, route or state, which is affordable because the reads are
;; nearly all ones the page already made (the relation flank comes off `term-index-groups`,
;; and the taxonomy is probed only in a direction the closures `term-page` read say has
;; something) and because every expansion is spent from one hard budget.  Over budget means
;; **draw less and say so**, never fall back to a button.

(def ^:private graph-hops-up
  "How many rows of supertypes to climb.  Three is enough to show where a term sits;
  past it the rows stack near `thing`, where every ontology looks the same."
  3)

(def ^:private graph-hops-down
  "How many rows of subtypes to descend.  Two, and fewer than the climb, because subtype
  fan-out is wider than supertype fan-in and a third row is mostly elision caption."
  2)

(def ^:private graph-row-cap
  "How many nodes one row may hold.  Past eight the labels collide at the column's width
  and the row stops being a row."
  8)

(def ^:private graph-row-limit
  "How many direct neighbours one node may have and still have some of them drawn.
  `graph-step` reads at most one more than this and sorts what it read, so a row is
  chosen by print order from the node's **whole** fan-out.  A node past the limit draws
  none and the caption says so.  Five hundred is far past every node of the shipped
  ontology, and is the same fixed read `ego-scan` makes."
  500)

(def ^:private graph-spread
  "How many neighbours **one** node contributes to the row below/above it, past the first
  row.  Three, so a row spreads across its parents instead of one prolific node eating
  it — the picture is about the neighbourhood, not about its widest member."
  3)

(def ^:private graph-flank-cap
  "How many relation neighbours flank the centre **per side** — four in, four out."
  4)

(def ^:private graph-side-budget
  "The hard bound on expansions (one bounded facade read each) the graph may spend
  climbing, and again descending.  A side that runs out stops one row short and the
  caption says so.  Per side rather than shared, so a deep hierarchy above a term cannot
  starve the subtypes below it of every read."
  6)

(def ^:private graph-ego-cap
  "How many neighbours the radial graph's inner ring holds."
  8)

(def ^:private graph-ego-expand
  "How many of those get their own neighbours read for the outer ring.  Each costs two
  O(1) argument counts (`ego-expand-cap`'s width check) and two bounded pattern reads,
  and those are the only reads the radial graph makes: twelve at most."
  3)

(def ^:private ego-expand-cap
  "How wide a neighbour may be and still have its own relations read for the outer arc.
  The second hop is `(?p N ?y)` with the functor open, which the index answers by unioning
  the scoped roots over `[:argument-slot 1 N]`; at `isa` one such read took 851 ms.  A
  neighbour past this cap is drawn on the inner ring and not expanded.  The width is
  `count-with-arg`, one O(1) read per predicate at the slot."
  2000)

(def ^:private ego-scan
  "How many matches the radial graph's second hop reads before ordering them.  Five hundred
  is sixty times the eight it places, so the order is a claim about a sample rather than
  about the first few the index happened to hand back — and it is a fixed read, where the
  neighbour's own extent is not."
  500)

(def ^:private graph-flank-scan
  "How many of a group's sentexes the ego edges are read out of, **per argument position**.
  The groups are already realized, so this bounds the work and the handles the graph adds
  to the page's one batched belief read.  Five times the eight neighbours either layout can
  draw; widening it to 200 draws the identical picture on a 148k-sentex corpus."
  40)

(def ^:private subsumption-relations
  "The two relations drawn on the vertical axis, not relation-flank edges: a `genl` edge
  drawn as a row and as an arrow would say two things about one claim.  The `/tree/rows`
  handler reads this too, so a relation the tree opens on is one this axis draws.  The
  engine's name for the set is `taxonomy/closure-relations`."
  '#{genl genlCx})

;; layout, in the flat user space `vaelii.browser.svg` crops to what is drawn
(def ^:private graph-level 76)
(def ^:private graph-row-gap 20)
;; the clear space between two group frames of one row, wider than the gap between two
;; boxes so a frame's edge is not read as the next box's
(def ^:private graph-group-gap 32)
(def ^:private graph-flank-gap 12)
(def ^:private graph-flank-offset 96)
(def ^:private graph-ring-r 150)
;; the clear space between the inner ring's boxes and an outer arc's, so the arc's radius
;; is derived from the two widths rather than being a number that holds until a label
;; gets longer
(def ^:private graph-arc-gap 28)

(defn- graph-node
  "A node of the picture: the term, the **same role class its links use** (so the graph
  can never drift from the text beside it), its page, and the whole term in a tooltip
  since the label is cut."
  ([env term] (graph-node env term nil))
  ([env term extra]
   (let [text (term-text env term)]
     (svg/measure (merge {:term    term
                          ;; the label is the term's *display*, which for a reified term
                          ;; is the expression it denotes and not its opaque constant.
                          ;; `:term` stays the constant: it is the node's identity, what
                          ;; the layout dedups on and what its page is
                          :display text
                          :class   (term-class env term)
                          :href    (str "/term?q=" (url-enc (pr-str term)))
                          :title   text}
                         extra)))))

(defn- graph-step
  "One expansion: the nearest neighbours of `node` under `pred` going `:up` or `:down`, at
  most `cap` of them, and how many there are.

  **A `genl` step draws the node's minimal supertypes going up and its maximal subtypes
  going down** (`min-genls` / `max-specs`) over every believed edge, so a stated
  `(genl dog animal)` beside `dog ⊂ mammal ⊂ animal` draws `animal` above `mammal`.  It
  does not read `hide-derived?`.  **A `genlCx` step draws the context's minimal parents and
  maximal children** (`min-context-parents` / `max-context-children`).  **A step under any
  other relation draws its one-step neighbours unreduced.**

  **The neighbours drawn are the first `cap` in print order.**  The read realizes at most
  `graph-row-limit` + 1 one-step neighbours.  A node with more than `graph-row-limit`
  contributes **no** neighbours, since the index order is not the print order and a partial
  read would differ between KBs holding the same edges.  `:more?` marks that case,
  `:total` is then the limit it exceeded, and the caption says the node has too many to
  draw."
  [kb pred dir node cap]
  (let [up? (= :up dir)
        got (into [] (take (inc graph-row-limit))
                  ((if up? parent-terms child-terms) kb pred node))]
    (if (> (count got) graph-row-limit)
      {:terms [] :total graph-row-limit :exact? false :more? true}
      (let [near (if (> (count got) 1)
                   (case pred
                     genl   ((if up? v/min-genls v/max-specs) kb node)
                     genlCx ((if up? v/min-context-parents v/max-context-children) kb node)
                     got)
                   got)]
        {:terms (into [] (take cap) (by-print-key near)) :total (count near)
         :exact? true :more? false}))))

(defn- fresh-neighbours
  "The neighbours a row is built from: what the expansions found, minus anything already
  drawn and minus repeats, in the order they were found.  Deduping is not cosmetic — a
  diamond in the taxonomy reaches one term by two paths, and drawing it twice would put
  two nodes where the KB has one."
  [found seen]
  (first (reduce (fn [[out got] e]
                   (if (or (seen (:term e)) (got (:term e)))
                     [out got]
                     [(conj out e) (conj got (:term e))]))
                 [[] #{}] found)))

(defn- grow
  "One side of the taxonomy graph: up to `hops` rows of nearest neighbours of `centre` under
  `rel`, going `dir`.  Each row entry is `{:term :rel :from}`, one drawn subsumption edge
  between `:term` and the node `:from` it was found from.  Each row is capped, each node
  past the first row contributes at most `graph-spread`, and every expansion is spent from
  `budget`, so the reads are bounded before the first.  Running out **shortens the
  picture**: `:truncated?` says a row was not read.  `:direct` is the centre's own row
  before the row cap."
  [kb rel dir hops centre budget]
  (loop [frontier [centre], depth 1, seen #{centre}
         rows [], spent 0, direct nil, deeper? false]
    (let [left (- budget spent)]
      (cond
        (or (> depth hops) (empty? frontier))
        {:rows rows :spent spent :direct direct :deeper? deeper? :truncated? false}

        (< left 1)
        {:rows rows :spent spent :direct direct :deeper? deeper? :truncated? true}

        :else
        (let [cap    (if (= 1 depth) graph-row-cap graph-spread)
              probed (into [] (take left) frontier)
              steps  (mapv (fn [n] [n (graph-step kb rel dir n cap)]) probed)
              spent' (+ spent (count probed))
              found  (for [[from {:keys [terms]}] steps, t terms]
                       {:term t :rel rel :from from})
              fresh  (fresh-neighbours found seen)
              row    (into [] (take graph-row-cap) fresh)
              short? (or (< (count probed) (count frontier))
                         (> (count fresh) (count row))
                         (boolean (some (fn [[_ s]] (> (:total s) (count (:terms s)))) steps)))
              ;; recorded before the empty-row exit: a centre with too many neighbours to
              ;; draw has an empty row, and that is the row the caption must explain
              direct (or direct
                         (when (= 1 depth)
                           (let [s (second (first steps))]
                             {:shown (count row) :total (:total s)
                              :exact? (:exact? s) :more? (:more? s)})))]
          (if (empty? row)
            {:rows rows :spent spent' :direct direct :deeper? deeper? :truncated? false}
            (recur (mapv :term row) (inc depth) (into seen (map :term) row)
                   (conj rows row) spent' direct
                   (or deeper? (and (> depth 1) short?)))))))))

(defn- subsumption-plan
  "Which subsumption relation to walk, and in which directions, decided from what
  `term-page` has **already read**, so a term with no taxonomy costs the graph nothing.  A
  term is a context or it is not: `genl` relates types and predicates, `genlCx` relates
  contexts, and `wff` refuses the mixture, so each term page walks exactly one subsumption
  relation and the class on its edges says which."
  [term gls sps]
  (if (= :context (v/term-role term))
    {:rel 'genlCx :up? true :down? true}
    (when (or (seq gls) (seq sps))
      {:rel 'genl :up? (boolean (seq gls)) :down? (boolean (seq sps))})))

(defn- flank-scan
  "The prefix of a group's sentexes the ego edges are read out of: its **earliest**
  `graph-flank-scan`, by handle.  A group comes off a *set* of handles, so a prefix taken as
  it arrives is a sample by hash that draws a different picture for two assertion orders of
  the same knowledge.  The records are already in hand, so the sort is over handles.  Past
  `group-sort-cap` the prefix is the index's own first `graph-flank-scan`, and
  `flank-reach` already reports the reach as a bound."
  [sentexes n]
  (if (<= (long n) group-sort-cap)
    (take graph-flank-scan (sort-by :id sentexes))
    (into [] (take graph-flank-scan) sentexes)))

(defn- flank-handles
  "The handles the ego edges will ask the belief of, so the graph rides the page's **one**
  batched belief read instead of adding a read per node."
  [groups]
  (for [{:keys [pos sentexes] n :count} groups :when pos
        s (flank-scan sentexes n)]
    (:id s)))

(defn- flank-edges
  "The centre's binary-relation neighbours, read off the groups the page **already built**,
  so the ego edges cost no extent read.  An edge is:

    · **binary facts only**: a ternary `(arg parentOf 1 person)` drops the position;
    · **positive only**: `(not (P a b))` says the relation does not hold;
    · **believed only**, from the page's belief cache;
    · **symbols only**: a number, a comment's text and a compound are not graph nodes;
    · **not the subsumption relations**, which are the vertical axis;
    · **not the term itself**.

  One edge in two contexts is **one** edge (`merge-neighbours` dedups by term)."
  [env term groups]
  (for [{:keys [pos sentexes] n :count} groups
        :when (and pos (<= pos 2))
        s     (flank-scan sentexes n)
        :when (and (nil? (:antecedent s)) (not (v/negative? s)) (believed? env (:id s)))
        :let  [sent (:sentence s)]
        :when (and (sequential? sent) (= 3 (count sent)))
        :let  [[p a b] sent
               mine   (if (= 1 pos) a b)
               other  (if (= 1 pos) b a)]
        :when (and (= term mine) (symbol? p) (not (subsumption-relations p))
                   (symbol? other) (not= other term)
                   (not= :variable (v/term-role other)))]
    {:term other :pred p :out? (= 1 pos)}))

(defn- merge-neighbours
  "Collapse raw ego edges to **one per neighbour term**, in the order they were found.

  A node per *fact* puts two `Ann`s on the page where the KB has one term — the same
  defect that drawing an edge once per asserting context would be, and it wants the same
  fix.  So the node is the term, and the edge carries every relation that reaches it.
  Where two facts run opposite ways the edge gets a head at each end, which is what
  `(marriedTo Bob Nancy)` beside `(marriedTo Nancy Bob)` actually says — the pair is one
  claim about two people, not two arrows."
  [edges]
  (let [{:keys [order by-term]}
        (reduce (fn [{:keys [order by-term]} {:keys [term pred out?]}]
                  {:order   (if (by-term term) order (conj order term))
                   :by-term (update by-term term
                                    (fn [e]
                                      (-> (or e {:term term :preds [] :out? false :in? false})
                                          (update :preds #(if (some #{pred} %) % (conj % pred)))
                                          (assoc (if out? :out? :in?) true))))})
                {:order [] :by-term {}} edges)]
    (mapv by-term order)))

(defn- edge-label
  "What an edge says: the relations that reach the neighbour, at most two of them spelled
  out.  A neighbour reached by five predicates is a fact about the neighbour, not five
  edges, and the term page below names all five."
  [preds]
  (str (str/join ", " (take 2 preds)) (when (> (count preds) 2) " …")))

(defn- flank-reach
  "How many related terms there are to have drawn — the number `neighbours` is *of*.

  Exact when the ego-edge scan ran out of facts before it ran out of scan: `neighbours`
  is then a census.  A group longer than `graph-flank-scan` stops it short, and the count
  falls back to the groups' own O(1) stored totals — an over-count, since each of those is
  facts rather than distinct terms and a term reached twice is one node.  So it travels
  with `:exact? false` and the caption words it as the bound it is; the alternative is a
  page that reports a scan limit as a fact about the KB."
  [groups neighbours]
  (let [binary (filter (fn [{:keys [pos]}] (and pos (<= pos 2))) groups)]
    (if (some (fn [{c :count}] (> c graph-flank-scan)) binary)
      {:total (reduce + 0 (map :count binary)) :exact? false}
      {:total (count neighbours) :exact? true})))

(defn- ego-neighbours
  "One hop out from `t`: its believed binary neighbours, both directions, bounded.  Two
  reads: `(?p T ?y)` leaves the functor open, but `T` is ground at argument position 1, so
  the predicate-agnostic read, a union of the scoped roots over `[:argument-slot 1 T]`,
  answers it (docs/indexing.md).  Believed, binary and positive because that is what
  `query` unifies.  **Ordered by handle before the cap cuts**, for `flank-scan`'s reason,
  over `ego-scan` matches rather than the whole match: realizing a hub's extent to place
  eight nodes took 1.5 s of a term page."
  [kb t cap]
  (let [pull (fn [pattern out?]
               (into []
                     (comp (map :sentence)
                           (keep (fn [[p a b]]
                                   (let [other (if out? b a)]
                                     (when (and (symbol? p) (not (subsumption-relations p))
                                                (symbol? other) (not= other t)
                                                (not= :variable (v/term-role other)))
                                       {:term other :pred p :out? out?}))))
                           (take cap))
                     (sort-by :id (into [] (take ego-scan) (v/sentexes-matching kb pattern '?ctx)))))]
    (concat (pull (list '?p t '?y) true)
            (pull (list '?p '?y t) false))))

(defn- rel-edge
  "One relation edge between two placed nodes.  Direction is the arrowhead and the label
  together, never colour: a neighbour the centre points at gets the head at its end, one
  that points back gets it at the centre's, and a pair that does both gets a head at each.
  An edge one of whose relations is `disjoint` takes the `g-rel-disjoint` stroke as a
  second cue beside its label."
  [centre n {:keys [preds out? in?]}]
  (let [disjoint? (boolean (some #{'disjoint} preds))]
    (some-> (if out? (svg/trim centre n) (svg/trim n centre))
            (assoc :label (edge-label preds) :back? (and out? in?)
                   :kind (if disjoint? "g-rel g-rel-disjoint" "g-rel")
                   :tone (when disjoint? :disjoint)))))

(defn- place-flanks
  "The relation flank: things that point **at** the term on the left, things it points at
  on the right, so the two directions are told apart by where they are and not only by an
  arrowhead.  Returns the placed nodes and their edges to the centre together, which is
  what makes every drawn arrow end on a drawn node by construction rather than by a check."
  [env centre neighbours]
  (let [half (/ (:w centre) 2.0)
        ;; a neighbour reached both ways is an outgoing claim as much as an incoming one,
        ;; so it goes on the right and its edge carries the second head
        side (fn [out?]
               (let [es (into [] (comp (filter #(= out? (boolean (:out? %))))
                                       (take graph-flank-cap))
                              neighbours)
                     ns (map #(graph-node env (:term %)) es)
                     x  (if out? (+ half graph-flank-offset) (- (- half) graph-flank-offset))]
                 (map vector (svg/column ns x 0 graph-flank-gap (if out? 1 -1)) es)))
        placed (concat (side false) (side true))]
    {:nodes (map first placed)
     :edges (keep (fn [[n e]] (rel-edge centre n e)) placed)
     :shown (count placed)}))

(defn- drawn-subsumptions
  "The subsumption edges one side of the taxonomy graph draws, as a set of `[sub super]`
  pairs: plain data, for a caller that asks whether the picture drew a given edge."
  [{:keys [rows]} dir]
  (into #{}
        (map (fn [{:keys [term from]}] (if (= :up dir) [from term] [term from])))
        (apply concat rows)))

(def ^:private cover-claims
  "The three cover kinds, in the order the taxonomy graph draws their groups, each with
  the claims its frame label states: a `partition` covers its whole and separates its
  parts, a `covering` covers it, a `separating` separates."
  [[:partition "covers, disjoint"] [:covering "covers"] [:separating "disjoint"]])

(defn- spec-groups
  "The centre's drawn subtype row, grouped by the cover declarations over the centre
  (`covers`, `vaelii.core/covers-of`).  Answers `{:groups [{:label :entries}] :rest
  [entry …] :notes [s …]}`: each group holds the row entries that are its parts, `:rest`
  the entries no cover names, and `:notes` the caption lines.  Groups are in content order:
  by kind in `cover-claims` order, then by the printed part list; a kind with two or more
  covers numbers them.  An entry is drawn once, in the first group naming it, and a later
  group naming it says so in a note."
  [env covers row]
  (let [rank    (into {} (map-indexed (fn [i [k]] [k i])) cover-claims)
        claims  (into {} cover-claims)
        sorted  (sort-by (fn [[kind parts]] [(rank kind 3) (str/join " " parts)]) covers)
        per     (frequencies (map first sorted))
        by-term (into {} (map (juxt :term identity)) row)
        step    (fn [{:keys [groups placed seen notes]} [kind parts]]
                  (let [n      (inc (seen kind 0))
                        label  (str (name kind) (when (> (per kind) 1) (str " " n)))
                        drawn  (filterv by-term parts)
                        mine   (filterv (complement placed) drawn)
                        shared (filterv placed drawn)
                        head   (str label ": " (claims kind)
                                    (when (< (count drawn) (count parts))
                                      (str " · " (count drawn) " of " (count parts)
                                           " parts in this row")))]
                    {:groups (cond-> groups
                               (seq mine) (conj {:label head :entries (mapv by-term mine)}))
                     :placed (into placed (map (fn [t] [t label])) mine)
                     :seen   (assoc seen kind n)
                     :notes  (cond-> notes
                               (seq shared)
                               (conj (str label " also names "
                                          (str/join ", " (map (fn [t] (str (term-text env t)
                                                                           " (drawn under "
                                                                           (placed t) ")"))
                                                              shared)))))}))
        {:keys [groups placed notes]}
        (reduce step {:groups [] :placed {} :seen {} :notes []} sorted)]
    {:groups groups
     :rest   (filterv #(not (placed (:term %))) row)
     :notes  notes}))

(defn- taxonomy-scene
  "The top-down graph: the term in the middle, its supertypes in rows above and its
  subtypes in rows below, relations flanking.  Vertical position **is** the subsumption
  relation, and every vertical arrow points at the more general term — going up that is
  the neighbour, going down it is the node it was found from, which is why one edge
  builder serves both."
  [{:keys [kb] :as env} term plan neighbours]
  (let [centre (graph-node env term {:x 0 :y 0 :class (str (term-class env term) " g-centre")})
        ;; the cover read is one facade read, spent from the descending side's budget
        grouped? (and (:down? plan) (= 'genl (:rel plan)))
        covers   (when grouped? (v/covers-of kb term))
        up     (when (:up? plan)   (grow kb (:rel plan) :up   graph-hops-up   term graph-side-budget))
        down   (when (:down? plan) (grow kb (:rel plan) :down graph-hops-down term
                                         (cond-> graph-side-budget grouped? dec)))
        node   (fn [e] (graph-node env (:term e) (select-keys e [:from :rel])))
        groups (when (seq covers) (spec-groups env covers (first (:rows down))))
        lay    (fn [{:keys [rows]} sign]
                 (map-indexed
                  (fn [i row]
                    (let [y (* sign graph-level (inc i))]
                      (if (and groups (pos? sign) (zero? i))
                        (svg/grouped-row (conj (mapv (fn [g] {:nodes (map node (:entries g))
                                                              :label (:label g)})
                                                     (:groups groups))
                                               {:nodes (map node (:rest groups))})
                                         0 y graph-row-gap graph-group-gap)
                        {:nodes (svg/row (map node row) 0 y graph-row-gap) :frames []})))
                  rows))
        laid   (concat (lay up -1) (lay down 1))
        placed (mapcat :nodes laid)
        by-term (into {term centre} (map (juxt :term identity)) placed)
        flank  (place-flanks env centre neighbours)
        rel-kind (str "g-" (:rel plan))
        tax-edges (keep (fn [{:keys [from] :as n}]
                          (let [a (by-term from)
                                ;; the arrow always ends at whichever of the two is higher
                                ;; on the page, which is the more general term either way
                                [lo hi] (if (< (:y n) (:y a)) [a n] [n a])]
                            (some-> (svg/trim lo hi) (assoc :kind rel-kind :tone :sub))))
                        placed)]
    {:nodes (concat [centre] placed (:nodes flank))
     :edges (concat tax-edges (:edges flank))
     :frames (mapcat :frames laid)
     :subsumptions (into (drawn-subsumptions up :up) (drawn-subsumptions down :down))
     :up up :down down
     :group-notes (:notes groups)
     :flank {:shown (:shown flank)}}))

(defn- ego-scene
  "The radial graph, for a term with no subsumption structure at all: the term at the
  origin, its relation neighbours on an inner ring, and each of the first few of *those*
  neighbours' own relations clustered on a short arc outside it.  Edges carry the
  predicate, so two hops of a relation graph read as claims rather than as connectivity."
  [{:keys [kb] :as env} term neighbours]
  (let [centre (graph-node env term {:x 0 :y 0 :class (str (term-class env term) " g-centre")})
        inner  (into [] (take graph-ego-cap) neighbours)
        ring   (svg/ring (map #(graph-node env (:term %)) inner) 0 0 graph-ring-r
                         (- (/ Math/PI 2)))
        pairs  (mapv vector ring inner)
        ;; `ring` picks its own radius off the widest box it was given, so the arc outside
        ;; it reads that back rather than assuming the minimum: a cluster placed at a fixed
        ;; radius overlaps the ring as soon as either side's labels grow
        ring-r (if-let [n (first ring)] (Math/hypot (double (:x n)) (double (:y n)))
                       (double graph-ring-r))
        ring-w (reduce max 0 (map :w ring))
        wide?  (fn [t] (> (+ (v/count-with-arg kb 1 t) (v/count-with-arg kb 2 t))
                          ego-expand-cap))
        out    (reduce (fn [{:keys [nodes edges drawn] :as acc} [n _]]
                         (let [kids   (into [] (comp (remove #(drawn (:term %)))
                                                     (take graph-spread))
                                            (when-not (wide? (:term n))
                                              (merge-neighbours
                                               (ego-neighbours kb (:term n) graph-ego-cap))))
                               boxes  (mapv #(graph-node env (:term %)) kids)
                               placed (svg/arc boxes 0 0
                                               (+ ring-r graph-arc-gap
                                                  (/ (+ ring-w (reduce max 0 (map :w boxes)))
                                                     2.0))
                                               (:angle n))]
                           (-> acc
                               (assoc :drawn (into drawn (map :term) kids))
                               (assoc :nodes (concat nodes placed))
                               (assoc :edges (concat edges
                                                     (keep (fn [[k e]] (rel-edge n k e))
                                                           (map vector placed kids)))))))
                       {:nodes [] :edges [] :drawn (into #{term} (map :term) inner)}
                       (take graph-ego-expand pairs))]
    {:nodes (concat [centre] ring (:nodes out))
     :edges (concat (keep (fn [[n e]] (rel-edge centre n e)) pairs) (:edges out))
     :inner (count inner)}))

(defn- elision-note
  "How a row says what it left out.  A truncated picture that does not announce itself is
  worse than no picture, and worse here than in a list — a picture reads as complete.  The
  count is exact where the neighbours were read whole.  A relation flank's count is
  otherwise the argument-root bound, worded as the bound it is rather than passed off as an
  edge count.  A taxonomy node past `graph-row-limit` (`:more?`) draws no row, and the note
  says so and points at the rows below, which list every neighbour."
  [what {:keys [shown total exact? more?]}]
  (when (and total (> total shown))
    (if more?
      (str "more than " (commas total) " " what ", too many to draw; they are listed below")
      (str "showing " shown " of " (when-not exact? "up to ") (commas total) " " what))))

(def ^:private flank-sample-note
  "What the caption says a partial flank *is*.  A picture drawing eight of forty
  neighbours has sampled, and a sample a reader can name — the term's earliest mentions,
  by handle (`flank-scan`) — is the difference between a bound that can be reasoned about
  and an arbitrary one."
  "the related terms shown are the term's earliest mentions")

(defn- graph-notes
  "The captions under the picture: what was elided, which of it was drawn, whether the
  read budget rather than the term's own shape is what stopped it, and which drawn
  subtypes a later cover group also names (`spec-groups`)."
  [{:keys [up down flank group-notes]} plan]
  (let [word (fn [dir] (if (= 'genlCx (:rel plan))
                         (if (= :up dir) "contexts it sees" "contexts that see it")
                         (if (= :up dir) "direct supertypes" "direct subtypes")))
        near (elision-note "related terms" flank)]
    (->> (into [(some->> (:direct up) (elision-note (word :up)))
                (some->> (:direct down) (elision-note (word :down)))
                near
                (when near flank-sample-note)
                (when (or (:deeper? up) (:deeper? down))
                  "deeper rows are sampled, not complete")
                (when (or (:truncated? up) (:truncated? down))
                  "and the read budget stopped it a row short")]
               group-notes)
         (remove nil?)
         seq)))

(defn- graph-figure
  "The picture, its caption and its legend — or **nil** when there is nothing worth
  drawing.  No empty frame and no \"no graph available\" box: a term nothing mentions gets
  the page it gets today."
  [text scene notes legend]
  (when-let [svg (svg/scene (assoc scene :aria-label
                                   (str "concept graph for " text
                                        "; the same terms are listed below as text")))]
    ;; a caller may hand one note or several; either way an absent one is not a bullet
    (let [notes (seq (remove nil? (if (string? notes) [notes] notes)))]
      ;; the picture scrolls inside its own box and the caption sits under the box rather
      ;; than inside it — a caption that scrolls out of the viewport with the thing it describes
      ;; is a caption a reader does not have
      [:figure.kb-graph-fig
       [:div.kb-graph-box svg]
       [:figcaption.muted legend (when notes (list " · " (str/join " · " notes)))]])))

(defn- term-graph
  "The concept graph at the top of a term page: the top-down taxonomy graph when the term
  has subsumption structure, the radial ego graph when it has relations and no subsumption,
  and **nothing at all** when it has neither.

  Wrapped, and not decoratively: this is the one part of the page that does arithmetic on
  KB-derived numbers, and a term page that fails to render because its picture could not
  be drawn would be a strictly worse page than the one without a picture.  A throw here
  costs the figure and nothing else."
  [env term gls sps groups]
  (try
    (let [near  (merge-neighbours (flank-edges env term groups))
          reach (flank-reach groups near)]
      (if-let [plan (subsumption-plan term gls sps)]
        (let [scene (taxonomy-scene env term plan near)
              scene (update scene :flank merge reach)]
          (graph-figure (term-text env term) scene (graph-notes scene plan)
                        (if (= 'genlCx (:rel plan))
                          "arrows point at the more general context; relations flank it · believed edges only"
                          (str "arrows point at the more general type; relations flank it"
                               " · a subsumption arrow is blue, a disjoint edge amber"
                               (when (seq (:frames scene))
                                 (str " · a frame holds the subtypes one partition, covering"
                                      " or separating declaration names"))
                               " · believed edges only"))))
        (when (seq near)
          (let [scene (ego-scene env term near)
                note  (elision-note "related terms" (assoc reach :shown (:inner scene)))]
            (graph-figure (term-text env term) scene
                          [note (when note flank-sample-note)]
                          "relations of the term, two hops out; an arrow runs subject to object")))))
    (catch Throwable t
      (trove/log! {:level :warn :id ::graph-failed :data {:term term :error (ex-message t)}})
      nil)))

;; ---- a type's whole closure, drawn ---------------------------------------
;; The term page draws a sampled neighbourhood; `/closure` draws all of one direction as a
;; layered picture of the reduced order (`min-genls` / `max-specs`, so no edge is implied
;; by two others).  Each type sits on the row of its **longest** path from the term, so a
;; genl closure narrows to `thing` (a diamond) and a spec closure only widens (a triangle).

(def ^:private closure-cap
  "How many types a closure picture draws.  Past it the walk stops at the nearest types
  by steps, and the page says how many there are in all."
  250)

(def ^:private closure-dirs
  {"genls" {:title "All genls" :step v/min-genls :word "supertype"}
   "specs" {:title "All specs" :step v/max-specs :word "subtype"}})

(def ^:private closure-row-cap
  "How many types one line of a closure picture holds.  A wider row is wrapped onto lines
  stacked under one another, so a type with forty subtypes is a block rather than a strip
  forty boxes wide."
  12)

(def ^:private closure-line-gap
  "The space between two wrapped lines of one row."
  14)

(defn- closure-walk
  "The types reachable from `term` by `step`, nearest first, at most `closure-cap` of
  them besides `term`, and each one's steps within what was collected: `{:nodes [t …]
  :next {t #{t …}} :more? bool}`."
  [kb step term]
  (loop [queue (conj clojure.lang.PersistentQueue/EMPTY term)
         seen  #{term}
         nodes []
         nxt   {}
         more? false]
    (if-let [t (peek queue)]
      (let [ns    (by-print-key (disj (set (step kb t)) t))
            fresh (remove seen ns)
            room  (- (inc closure-cap) (count seen))
            take' (take (max 0 room) fresh)]
        (recur (into (pop queue) take') (into seen take') (conj nodes t)
               (assoc nxt t (set ns)) (or more? (> (count fresh) (count take')))))
      {:nodes nodes :more? more?
       :next  (into {} (map (fn [[t ns]] [t (into #{} (filter seen) ns)])) nxt)})))

(defn- closure-layers
  "Each node's row: the length of the longest path to it from `term` along `next`, read in
  a topological order.  A node on a cycle, which a well-built taxonomy has none of, keeps
  the row its first visit gave it."
  [term {:keys [nodes next]}]
  (let [indeg (reduce (fn [m n] (reduce #(update %1 %2 (fnil inc 0)) m (next n)))
                      (zipmap nodes (repeat 0)) nodes)]
    (loop [ready [term] indeg indeg layer {term 0}]
      (if-let [n (first ready)]
        (let [l (layer n)
              [ready' indeg' layer']
              (reduce (fn [[r d ly] m]
                        (let [d (update d m dec)]
                          [(if (zero? (d m)) (conj r m) r) d
                           (update ly m (fnil max 0) (inc l))]))
                      [(subvec ready 1) indeg layer] (by-print-key (next n)))]
          (recur ready' indeg' layer'))
        ;; what the order never reached sits on a cycle: one row past its deepest parent
        (reduce (fn [ly n] (if (ly n) ly (assoc ly n (inc (reduce max 0 (vals ly))))))
                layer nodes)))))

(defn- closure-scene
  "The layered picture: `term` on row 0, at the bottom for `genls` and the top for
  `specs`, each row ordered by where its nodes' links in the rows before it sit and
  wrapped past `closure-row-cap`, and every arrow pointing at the more general type."
  [env term dir {:keys [next] :as walk}]
  (let [layer  (closure-layers term walk)
        rows   (vals (into (sorted-map) (group-by layer (keys layer))))
        sign   (if (= "genls" dir) -1 1)
        line-h (+ svg/node-h closure-line-gap)
        prev   (reduce-kv (fn [m a bs] (reduce #(update %1 %2 (fnil conj []) a) m bs)) {} next)
        node   #(graph-node env % (when (= term %)
                                    {:class (str (term-class env %) " g-centre")}))
        [placed _]
        (reduce
         (fn [[placed y] row]
           (let [x     (fn [n] (let [xs (keep #(:x (placed %)) (prev n))]
                                 (if (seq xs) (/ (reduce + xs) (double (count xs))) 0.0)))
                 lines (partition-all closure-row-cap (sort-by-once (juxt x print-key) row))
                 ;; a row's lines run away from the term, so the last is nearest the next row
                 nodes (mapcat (fn [i line]
                                 (svg/row (map node line) 0 (+ y (* sign line-h i)) graph-row-gap))
                               (range) lines)]
             [(into placed (map (juxt :term identity)) nodes)
              (+ y (* sign (+ graph-level (* line-h (dec (count lines))))))]))
         [{} 0]
         rows)
        edges  (for [[a bs] next, b bs
                     :let [[lo hi] (if (= "genls" dir) [a b] [b a])]
                     e [(svg/trim (placed lo) (placed hi))] :when e]
                 (assoc e :kind "g-genl" :tone :sub))]
    {:nodes (vals placed) :edges edges :rows rows}))

(defn- closure-actions
  "The buttons under a type's graph that open its whole closure, one per direction it
  has anything in."
  [term gls sps]
  (when (or (seq gls) (seq sps))
    [:div.sx-actions.closure-actions
     (for [[dir has?] [["genls" gls] ["specs" sps]] :when (seq has?)]
       [:a.button {:href (str "/closure?dir=" dir "&q=" (url-enc (pr-str term)))}
        (:title (closure-dirs dir))])]))

(defn- closure-page
  "Every supertype (`dir` \"genls\") or subtype (\"specs\") of `term`, drawn, and listed
  row by row below the picture."
  [{:keys [kb] :as env} term dir]
  (let [{:keys [title step word]} (closure-dirs dir)
        text  (term-text env term)
        walk  (closure-walk kb step term)
        scene (closure-scene env term dir walk)
        shown (dec (count (:nodes walk)))]
    (render env (str (str/lower-case title) " of " text)
            [:h2 title " of " (term-link env term)]
            ;; past the cap the whole count is not read: a spec closure near the root is
            ;; most of the KB's types
            [:p.muted (if (:more? walk) "More than " "") (commas shown) " " word
             (when (not= 1 shown) "s")
             (when (:more? walk) (list "; the nearest " (commas shown) " are drawn"))
             ". Each sits on the row of its longest path from " text
             (if (= "genls" dir)
               ", so a well-built taxonomy narrows to thing at the top: a diamond."
               ", so a well-built taxonomy only widens downward: a triangle.")]
            (when (pos? shown)
              (graph-figure text (select-keys scene [:nodes :edges]) nil
                            "arrows point at the more general type · the reduced order: no arrow two others imply"))
            [:div.sx-actions
             [:a.button {:href (str "/term?q=" (url-enc (pr-str term)))} "Back to " text]
             (let [other (if (= "genls" dir) "specs" "genls")]
               [:a.button {:href (str "/closure?dir=" other "&q=" (url-enc (pr-str term)))}
                (:title (closure-dirs other))])]
            (when (pos? shown)
              [:ol.closure-rows {:start 0}
               (for [row (:rows scene)]
                 [:li (interpose " " (map #(term-link env %) (by-print-key row)))])]))))

(defn- derived-switch
  "The control that leaves the **derived** rows (`vaelii.core/premise?` false) out of every
  index group on the page, or brings them back.  An ordinary link: `hx-boost` swaps
  `#main` for it, so the feature is one query parameter, one cookie and a re-render.  The
  cookie carries the choice onto the next term (`remember-derived`)."
  [{:keys [hide-derived?]} term]
  [:a.action {:href  (str "/term?q=" (url-enc (pr-str term))
                          "&derived=" (if hide-derived? "show" "hide"))
              :title (if hide-derived?
                       "also list what the engine concluded"
                       "list only what the KB was told, not what it concluded")}
   (if hide-derived? "show derived" "hide derived")])

(def ^:private arity-class-names
  "The exact-arity predicate class for each length, which a predicate's arity-class seed
  names."
  {1 "unary_predicate" 2 "binary_predicate" 3 "ternary_predicate"
   4 "quaternary_predicate" 5 "quinary_predicate"})

(def ^:private block-parts
  "Each part of `describe`'s `:definitional-block`: its label, and the sentence the
  assert form opens on to add it, a template over the term's text `t` and the `describe`
  answer `d`.  A predicate's arity-class seed names the class of its arity, and a blank
  functor where the KB binds no arity."
  {:comment           ["comment"             (fn [t _] (str "(comment " t " \"\")"))]
   :positive-examples ["positive examples"   (fn [t _] (str "(positiveExampleComment " t " \"\")"))]
   :negative-examples ["negative examples"   (fn [t _] (str "(negativeExampleComment " t " \"\")"))]
   :parents           ["parents"             (fn [t _] (str "(genl " t " )"))]
   :siblings          ["siblings"            nil]
   :kind              ["kind"                (fn [t _] (str "( " t ")"))]
   :arity-class       ["arity class"         (fn [t d]
                                               (str "("
                                                    (if (= :predicate (:role d))
                                                      (get arity-class-names (:arity d) " ")
                                                      "unary_predicate")
                                                    " " t ")"))]
   :arity             ["arity"               (fn [t _] (str "(arity " t " )"))]
   :arg-declarations  ["arg declarations"    (fn [t _] (str "(arg " t " 1 )"))]
   :props             ["relation properties" (fn [t _] (str "( " t ")"))]})

(def ^:private overlap-witness
  "How a sibling row's `:witness` reads beside `overlaps`."
  {:shared-instance "shared instance" :shared-spec "shared subtype"
   :unwitnessed-spec "shared subtype not known nonempty"})

(defn- missing-mark
  "A part the block lacks: the tag, and one link per `[label sentence]` in `seeds`, each
  opening the assert form on that sentence."
  [seeds]
  (list [:span.tag.tag-missing "missing"]
        (for [[label text] seeds]
          (list " " [:a.action {:href (str "/assert?text=" (url-enc text))} label]))))

(defn- more-note [total shown]
  (when (> total shown)
    [:span.muted " and " (commas (- total shown)) " more"]))

(defn- block-value
  "One present part of the definitional block of the term whose text is `text`, by the
  shape `describe` answers that part in."
  [env text part v]
  (cond
    (= :siblings part)
    (if (empty? (:rows v))
      [:span.muted "none"]
      (list (interpose
             ", "
             (for [{s :term sep :separation w :witness via :via} (:rows v)
                   :let [pair (str text " " (term-text env s) ")")]]
               (list (term-link env s) " "
                     (case sep
                       :missing  (missing-mark [["disjoint" (str "(disjoint " pair)]
                                                ["orthogonal" (str "(orthogonal " pair)]])
                       :overlaps [:span.muted "overlaps (" (overlap-witness w) " "
                                  (term-link env via) ")"]
                       [:span.muted (name sep)]))))
            (more-note (:total v) (count (:rows v)))))
    (map? v)                   (list (interpose ", " (map #(term-link env %) (:terms v)))
                                     (more-note (:total v) (count (:terms v))))
    (= :arg-declarations part) (interpose " " (map (fn [{:keys [sentence context]}]
                                                     (if-let [h (v/handle-of (:kb env) sentence context)]
                                                       (handle-ref env h)
                                                       (render-form env sentence)))
                                                   v))
    (= :props part)            (interpose ", " (map name v))
    (coll? v)                  (interpose [:br] (map #(if (string? %) [:q %] (render-form env %)) v))
    :else                      (str v)))

(defn- definitional-block
  "The term's definitional block (`describe`'s `:definitional-block`, docs/web.md), one
  line per part in the handbook's order.  A missing part is tagged, beside a link that
  opens the assert form on the sentence that would supply it; so is a sibling no
  declaration separates."
  [env term {:keys [definitional-block] :as about}]
  (when (seq definitional-block)
    (let [text (term-text env term)]
      [:div.def-block
       [:h3 "Definitional block "
        [:span.muted "(the parts a term ships with, and which of them the KB holds)"]]
       [:dl.def-parts
        (for [{:keys [part value]} definitional-block
              :let [[label seed] (block-parts part)]]
          (list [:dt label]
                [:dd (if (= :missing value)
                       (missing-mark (when seed [["add" (seed text about)]]))
                       (block-value env text part value))]))]])))

(defn term-page
  "A term's page: the concept graph, the three type lines, the sentexes grouped by the
  index root that reaches them, and what a registered extension adds: actions beside the
  heading (`extension-term-actions`) and panels at the foot (`extension-panels`).  The page
  lists what the KB was told (the index groups) and draws position (the graph) instead of
  restating a closure in prose; `vaelii.core/describe` answers all six readings (docs/api.md).
  Each part has its own budget: the index groups in rows (`group-cap`), root extents
  deferred to a reveal (`group-sentexes`), and the graph in reads (`graph-side-budget`)."
  [{:keys [kb] :as env} term]
  (let [about  (v/describe kb term '?ctx)
        ;; the page reads two things off `describe`: whether the term has anything above
        ;; or below it, which decides the graph it draws, and the definitional block
        gls    (:terms (:genls about))
        sps    (:terms (:specs about))
        text   (term-text env term)
        {:keys [groups remainder?]} (term-index-groups kb term text)
        groups (vec groups)
        ;; a large extent's first page is deferred with the rest of it, so rendering this
        ;; page reads no root it cannot afford: the group shows its O(1) count and fetches
        ;; its rows when a reader scrolls it into the viewport (`extent-defer-cap`)
        pages  (mapv #(when-not (:deferred? %)
                        (group-page (group-order (group-sentexes %) (:count %)) 0
                                    (:hide-derived? env)))
                     groups)]
    ;; one belief read for the whole page: every group's first page of rows, **and** the
    ;; sentexes the graph reads its ego edges out of, in the same batch
    (prime-belief! env (concat (mapcat #(map :id (:rows %)) pages)
                               (flank-handles groups)))
    (let [graph (term-graph env term gls sps groups)]
      ;; `.term-layout` puts the picture under the heading on a portrait screen and in a
      ;; column of its own on the right of a landscape one; with no picture the prose
      ;; keeps the full width
      (render env (str "term " text)
              [(if graph :div.term-layout.with-graph :div.term-layout)
               [:div.term-head
                [:h2 "Term " (term-link env term) " "
                 ;; the label does not name the term: a reified one prints as the opaque
                 ;; constant the page exists not to show (`nat-ref`), and the heading beside
                 ;; this already says which term it is about
                 (edit-link (str "q=" (url-enc (pr-str term)))
                            "edit what this term is most directly in")
                 (extension-term-actions env term)]
                (term-actions term)
                (visit-mark "term" (str "/term?q=" (url-enc (pr-str term))) text
                            (term-class env term))]
               ;; the prose beside the picture is unchanged: the type lines are the
               ;; accessible equivalent and the exact answer the picture approximates
               (when graph
                 [:div.term-fig graph (closure-actions term gls sps)])
               [:div.term-body
                (definitional-block env term about)
                (when-not graph (closure-actions term gls sps))
                [:p [:a.action {:href (str "/assert?q=" (url-enc (pr-str term)))} "Assert a sentex"]
                 [:span.muted " — the form opens with this term already in it."]]
                [:h3 "Sentexes by index "
                 [:span.muted "(arguments, rules, nestings, extents)"] " "
                 (derived-switch env term)]
                (when-not remainder?
                  [:p.muted "This term reaches more than " (commas remainder-scan)
                   " sentexes, so the page did not walk the term index for what the roots "
                   "below do not claim. The groups it does show are complete."])
                (if (seq groups)
                  (map-indexed #(index-group env term [%1 %2 (nth pages %1)]) groups)
                  [:p.muted "none"])
                ;; last on the page, and deliberately: what the KB holds is the page, and
                ;; what an extension adds is read after it
                (extension-panels env term)]]))))

(defn term-rows-page
  "One more page of rows for index group `g` of `term` — what a group's continuation
  sentinel fetches.  The groups are recomputed and indexed the same way the page built
  them, so `g` names the same group it did then."
  [{:keys [kb] :as env} term g offset]
  (let [groups (vec (:groups (term-index-groups kb term)))]
    (frag (if-let [grp (get groups g)]
            (group-rows env term g
                        (group-page (group-order (group-sentexes grp) (:count grp))
                                    offset (:hide-derived? env))
                        (:count grp))
            ""))))

(defn- term-href [term] (str "/term?q=" (url-enc (pr-str term))))

(def ^:private find-cap
  "How many matching terms a search lists at a time; the rest follows on scroll."
  200)

(def ^:private pattern-cap
  "The longest search pattern that is compiled as a regex.  A pattern reaches
  `re-pattern` — an engine with no step bound, on a route a browser hits per keystroke
  and a daemon serves to whoever can reach it — so the length it may have is capped.
  Long enough for any pattern a person types by hand; short enough that a
  catastrophically-backtracking one cannot be built."
  128)

(def ^:private regex-metacharacters
  "What makes a pattern a *pattern* rather than a literal.  A query holding none of
  these matches exactly what `re-find` would — substring containment — so it is answered
  by `:match :substring` for the result list. The separate whole-name probe quotes
  the literal query rather than interpreting its syntax."
  (set "\\^$.|?*+()[]{}"))

(defn- term-hits
  "The terms matching `q`, from the index's **term-name set** (`v/find-terms`) — the size
  of the vocabulary, never a walk of the sentexes.  `re-find` semantics either way: a
  literal query is a substring match by default, and a query carrying regex syntax
  uses a pattern. Answers `::too-long` for a user pattern past `pattern-cap`,
  which is never compiled, `::bad` for one that does not compile or whose match overflows
  the stack, and `{::failed <message>}` for any other failure of the read, logged.

  `limit` bounds the answer; `exact?` asks for a quoted case-insensitive whole name."
  ([kb q limit] (term-hits kb q limit false))
  ([kb q limit exact?]
   (let [regex? (and (not exact?) (some regex-metacharacters q))]
     (cond
       (and regex? (> (count q) pattern-cap)) ::too-long
       ;; compiled here as well as in `find-terms`: an attached daemon answers a pattern
       ;; that does not compile as a server fault, which the arms below would show as one
       (and regex? (nil? (try (re-pattern q)
                              (catch java.util.regex.PatternSyntaxException _ nil))))
       ::bad
       :else
       (try
         ;; case-insensitive: a literal query matches a term of any case, so a
         ;; lowercase `transitiveinarg` finds `transitiveInArg`.  A regex query
         ;; carries its own case in the pattern and asks for insensitivity with
         ;; `(?i)`; `find-terms`' regex matcher ignores this flag, so it is unchanged.
         (v/find-terms kb (if exact?
                            (str "(?iu)\\A" (java.util.regex.Pattern/quote q) "\\z")
                            q)
                       {:match (if (or exact? regex?) :regex :substring)
                        :case-sensitive? false :limit limit})
         ;; a catastrophic pattern can raise `StackOverflowError` out of the regex
         ;; engine, and this handler stack has no exception middleware to make a page of
         ;; it, so the pattern is reported as unusable
         (catch java.util.regex.PatternSyntaxException _ ::bad)
         (catch StackOverflowError _ ::bad)
         ;; a store fault or an unreachable daemon is not the pattern's fault
         (catch Exception t
           (trove/log! {:level :warn :id ::find-failed :error t
                        :data {:q q :error (ex-message t)}})
           {::failed (or (ex-message t) (.getName (class t)))}))))))

(defn- find-list
  "The result list for a search: one page of hits and the sentinel that fetches the
  next.  `hits` is one longer than the page when there is more to come."
  [env q offset hits]
  (let [page (take find-cap hits)]
    (list (for [t page] [:li (term-link env t)])
          (when (> (count hits) find-cap)
            (more-rows (str "/find/rows?q=" (url-enc q) "&offset=" (+ offset find-cap))
                       "show more")))))

(defn find-page
  "Term search over the KB's vocabulary: list every term whose name matches `q`, each
  linking to its term page.  `q` reads as `re-find` does (a bare `dog` finds every term
  containing it, `^parent` anchors) and filters the index's term-name set.  **A pattern
  that resolves to a single term jumps to that term's page**, because it is the only match
  or is a literal naming exactly one term ignoring case; the jump sets `HX-Push-Url`.
  Case-only name collisions stay a list. An unusable pattern or an empty
  query reports gently."
  [{:keys [kb] :as env} q]
  (let [hits (when-not (str/blank? q) (term-hits kb q (inc find-cap)))
        exact (when (and (sequential? hits) (not-any? regex-metacharacters q))
                (term-hits kb q 2 true))
        hits (if (and exact (not (sequential? exact))) exact hits)]
    (cond
      (str/blank? q)
      (render env "find"
              [:h2 "Find terms"]
              [:p.muted "Type a regular expression to match term names — e.g. "
               [:code "^parent"] ", " [:code "Of$"] ", or " [:code "(?i)dog"] "."])
      ;; a 400, as `bad-parameter` answers a value its page cannot read, rendered here in
      ;; the search's own words
      (= ::too-long hits)
      (assoc (render env (str "find " (pr-str q))
                     [:h2 "Find terms"]
                     [:p.muted "The pattern is " (count q) " characters long. A pattern "
                      "holding regular-expression syntax is compiled only up to "
                      pattern-cap " characters; a literal one of any length is a substring "
                      "match."])
             :status 400)

      (= ::bad hits)
      (assoc (render env (str "find " (pr-str q))
                     [:h2 "Find terms " [:span.muted "matching /" q "/"]]
                     [:p.muted "Not a valid regular expression: " [:code q] "."])
             :status 400)

      ;; a 200: the page script swaps a 400 into main and no other error status, and a
      ;; read that failed is not a value the route refuses
      (::failed hits)
      (render env (str "find " (pr-str q))
              [:h2 "Find terms " [:span.muted "matching /" q "/"]]
              [:p.muted "Search failed: " (::failed hits)])
      :else
      (let [target (if exact
                     (or (when (= 1 (count exact)) (first exact))
                         (when (and (empty? exact) (= 1 (count hits))) (first hits)))
                     (or (first (filter #(= q (str %)) hits))
                         (when (= 1 (count hits)) (first hits))))]
        (if target
          ;; jump: render the term page, and tell htmx to show the term URL
          (assoc-in (term-page env target) [:headers "HX-Push-Url"] (term-href target))
          (render env (str "find " (pr-str q))
                  [:h2 "Find terms " [:span.muted "matching /" q "/"]]
                  (if (empty? hits)
                    [:p.muted "No terms match " [:code q] "."]
                    [:div
                     [:p.muted (if (> (count hits) find-cap)
                                 (str "More than " find-cap " matching terms")
                                 (str (count hits) " matching terms")) "."]
                     [:ul.find-hits (find-list env q 0 hits)]])))))))

(defn find-rows-page
  "One more page of search hits — what the result list's continuation sentinel fetches."
  [{:keys [kb] :as env} q offset]
  (let [hits (term-hits kb q (+ offset find-cap 1))]
    (frag (if (or (#{::bad ::too-long} hits) (map? hits))
            ""
            (find-list env q offset (drop offset hits))))))

(defn- provenance-list
  "The provenance map `v/provenance` answers, a row per key in key order.  `:created` is
  epoch milliseconds (`*clock*`) and shows as local time; every other value prints as
  EDN."
  [prov]
  (if (seq prov)
    [:dl.provenance
     (for [k (by-print-key (keys prov)) :let [x (get prov k)]]
       (list [:dt (pr-str k)]
             [:dd (if (and (= :created k) (integer? x))
                    (local-time (java.time.Instant/ofEpochMilli x))
                    (pr-str x))]))]
    [:p.muted "none"]))

(defn- badge-reading
  "The badge of record `s` in sentences, one row per thing it draws: the kind its colour
  says, the origin its fill says and the belief its brightness says."
  [env s]
  (let [{:keys [run word]} (badge-kind s)
        strength (:strength s)
        also     (set (:engines s))]
    [:dl.provenance
     [:dt "Colour"]
     [:dd [:b (str/capitalize word)] ". "
      (when (v/negative? s) "It states that the sentence inside its `not` is false. ")
      (cond run                     (:says (rule-runs run))
            (= :monotonic strength) "Asserted as known true."
            (= :default strength)   "Asserted as true unless something says otherwise."
            :else                   "The engine concluded it.")
      (when (and (:defeasible s) run) " Its conclusions are defaults.")
      (when (and (also :solve) (#{:forward-only :both :backward :lazy-forward} run))
        " It also runs in a solve.")]
     [:dt "Fill"]
     [:dd (if strength
            (str "Filled: asserted, at strength " (name strength) ".")
            "Ring: derived. \"Supported by\" lists what concluded it.")]
     [:dt "Brightness"]
     [:dd (if (believed? env (:id s))
            "Full colour: believed."
            "Dimmed: stored and not believed, for the reason below.")]]))

(defn- inert-rule-why
  "Why the inert rule `s` runs in neither engine, read from what the KB holds: a mint rule
  is computed in code, a generator concluded a derived one, and an asserted one was
  written inert.  An `implementationNote` on its consequent's functor, or on the antecedent
  functors of the generator that concluded it, gives the author's reason."
  [{:keys [kb] :as env} s]
  (let [kind  (v/mint-rule-kind s)
        gens  (into [] (keep #(when (integer? (:informant %)) (v/sentex kb (:informant %))))
                    (v/supporting-justifications kb (:id s)))
        terms (into [(first (:consequent s))]
                    (comp (mapcat :antecedent) (map first)) gens)
        terms (distinct (filter #(and (symbol? %) (not= :variable (v/term-role %))) terms))
        notes (mapcat #(v/sentexes-matching kb (list 'implementationNote % '?text) '?ctx) terms)]
    [:div.belief
     (cond
       kind [:p "It states what the engine computes: the " [:code (str kind)]
             " declarations' mints run in code, each naming this rule in its justification."]
       (seq gens) [:p "It is inert because "
                   (interpose " and " (map #(sentex-ref env %) gens))
                   " concluded it inside " [:code "set/inertRule"] "."]
       :else [:p "It is inert because it was written inside " [:code "set/inertRule"]
              " or asserted with " [:code "{:direction :inert}"] "."])
     (cond (seq notes)  (sentex-list env notes)
           (not kind)   [:p.muted "No " [:code "implementationNote"] " says why."])]))

(defn sentex-page [{:keys [kb] :as env} h]
  (if-let [s (v/sentex kb h)]
    (let [premise? (v/premise? kb h)]
      (render env (str "sentex #" h)
              [:h2 "Sentex " [:span.muted "#" h]]
              (sentex-actions h)
              (visit-mark (if (:antecedent s) "rule" "literal") (str "/sentex/" h)
                          (term-text env (readable s)) nil)
              [:p.sx-item
               (sentex-line env s
                            (state-tag env h)
                            (when premise? [:span.tag.tag-premise "premise"])
                            ;; a rule is exactly a sentex with a decomposed antecedent —
                            ;; read off the record `v/sentex` returned, rather than
                            ;; re-deriving it from the sentence
                            (when (:antecedent s) [:span.tag "rule"])
                            (when-let [st (:strength s)] [:span.tag (str "assumed " (name st))])
                            (when-let [dc (v/defeat-class kb h)] [:span.tag (str "class " (name dc))]))]
              [:h3 "What its circle says"]
              (badge-reading env s)
              (when (= :inert (:run (badge-kind s))) (inert-rule-why env s))
              (when-not (believed? env h) (belief-detail env h))
              [:h3 "Supported by " [:span.muted "(justifications concluding it)"]]
              (if premise?
                [:p.muted "asserted as a premise"]
                (justification-list env (v/supporting-justifications kb h) h))
              ;; one hop up there; the whole way down to the premises is the why page
              (when (believed? env h)
                [:p [:a.action {:href (str "/why/" h)} "Why is this believed?"]
                 [:span.muted " — the full proof tree, not just the first hop."]])
              [:h3 "Dependents " [:span.muted "(justifications using it as an argument)"]]
              (justification-list env (v/dependent-justifications kb h) h)
              [:h3 "Metas naming it " [:span.muted "(sentexes holding (sentexHandle " h "))"]]
              (let [ms (into [] (take (inc group-cap)) (v/sentexes-naming kb h))]
                (list (sentex-list env (take group-cap ms))
                      (when (> (count ms) group-cap)
                        [:p.muted "the first " group-cap " shown"])))
              [:h3 "Provenance"]
              (provenance-list (v/provenance kb h))
              [:h3 "Subterms " [:span.muted "(each findable individually)"]]
              [:p (interpose " · " (map #(term-link env %) (by-print-key (v/indexable-terms s))))]
              [:p [:a {:href (str "/levels?q=" (url-enc (pr-str (readable s)))
                                  "&ctx=" (url-enc (pr-str (:context s))))}
                   "Trace through the stack"]
               [:span.muted " — which level of machinery reaches this sentence."]]))
    (render env "not found" [:p "No sentex #" h])))

;; ---- the lookup-to-query stack ------------------------------------------

(def ^:private result-cap
  "How many results a level shows at a time.  The page takes cap+1 from each level and
  never more: every level is lazy, so browsing a goal with thousands of answers costs
  cap+1 results per level rather than a full answer set, and the tail is fetched only if
  the reader asks for it.  This is why the page uses `v/lookup` per level instead of
  `v/explain-levels`, which counts and so realizes everything."
  25)

(defn- level-rows
  "One page of a level's results, plus the sentinel that fetches the next.  Realizes
  cap+1 results and no more, so the level's laziness survives the paging."
  [{:keys [kb] :as env} goal ctx lvl offset]
  (let [rs   (into [] (comp (drop offset) (take (inc result-cap)))
                   (v/lookup kb lvl goal ctx))
        page (take result-cap rs)]
    (prime-belief! env (keep :handle page))
    (list page (when (> (count rs) result-cap)
                 (str "/levels/rows?q=" (url-enc (pr-str goal)) "&ctx=" (url-enc (pr-str ctx))
                      "&level=" lvl "&offset=" (+ offset result-cap))))))

(defn- bindings-str [env b]
  (interpose ", " (for [[k val] (by-print-key b)]
                    [:span (render-form env k) " = " (render-form env val)])))

(defn- result-item
  "One result.  A result read off the store carries a handle, so the answer links to
  its sentex: every result of levels 0-4 and the level-4 matches level 5 includes.  A
  closure answer at level 5 and every answer of levels 6-7 is derived and carries none,
  so the sentence is rendered inline and tagged."
  [env r]
  [:li
   (if-let [h (:handle r)]
     ;; a storage level (0-1) can return a sentex the KB does not believe — the badge
     ;; already dims, the reason pill says why (superseded / defeated).  Cache hit:
     ;; level-rows primed these handles.
     (list (handle-ref env h)
           (when-not (believed? env h) (list " " (state-tag env h))))
     [:span (render-form env (:sentence r)) [:span.tag "derived"]])
   (when-let [c (:context r)] [:span in-cx (term-link env c)])
   (when (seq (:bindings r)) [:span.muted " — " (bindings-str env (:bindings r))])])

(defn- result-list
  "A level's rows and, when the level has more, the continuation sentinel."
  [env [page more-href]]
  (list (map #(result-item env %) page)
        (when more-href (more-rows more-href "show more"))))

(defn- level-section [env goal ctx {lvl :level nm :name adds :adds}]
  (let [[page :as rows] (level-rows env goal ctx lvl 0)]
    [:div
     [:h3 lvl " " [:span.tag (name nm)] " " [:span.muted adds]]
     (if (seq page)
       [:ul (result-list env rows)]
       [:p.muted "nothing"])]))

(defn levels-rows-page
  "One more page of results for a single level — what a level's continuation sentinel
  fetches."
  [env goal ctx lvl offset]
  (frag (result-list env (level-rows env goal ctx lvl offset))))

;; ---- the query plan ------------------------------------------------------
;; The levels below say what each mechanism *answers*; the plan says what the engine would
;; *do*: which provers bear on the goal, what each expects to cost, which one runs and
;; why, and for a conjunction the join order and the counts that decided it.  It takes the
;; same two inputs the levels take, so it sits on the same page.

(defn- prover-plan
  "The provers applicable to a single goal.  Applicable is not the same as consulted:
  when one prover is *complete* for the goal and no shadowing channel bears on it, the
  engine runs it alone and every other entry is shadowed, so the table says which ran as
  well as what each would cost.  When a channel does bear on the goal every applicable
  prover runs, and a complete one's row names the channels it is guarded by
  (`provers/plan`'s `:guarded-by`)."
  [rows]
  (list
   [:p.muted "One prover runs alone when it is complete for the goal and nothing it does "
    "not read, such as a rule concluding the predicate, bears on the goal; otherwise the "
    "applicable ones union, cheapest cost tier first. Cost is a tier — is the answer "
    "something you look up, compute, or search for — not a predicted duration."]
   [:div.qcn-scroll
    [:table.stats-table
     [:thead [:tr [:th "Prover"] [:th.num "est. bindings"] [:th "cost"]
              [:th.num "completeness"] [:th "runs?"]]]
     [:tbody
      (for [{:keys [prover est-bindings cost completeness runs? shadowed-by guarded-by]} rows]
        [:tr
         [:td (if runs? [:b prover] [:span.muted prover])]
         [:td.num est-bindings]
         [:td [:span.tag (name (or cost :unknown))]]
         [:td.num completeness (when (= 100 completeness)
                                 [:span.muted " — the sole complete method"])]
         [:td (if runs?
                (list [:span.tag.tag-in "runs"]
                      (when (seq guarded-by)
                        [:span.muted " guarded by "
                         (str/join ", " (map name (sort guarded-by)))]))
                [:span.muted "shadowed by " shadowed-by])]])]]]))

(defn- join-plan
  "The order a conjunction's literals will actually run in, with the three numbers the
  order was decided on.  `est. matches` is the sound upper bound on one literal's
  fan-out under the bindings the rows above produce — sideways information passing, and
  why the column does not read as sorted.  `rows` is the literal's own expected size,
  and `plan rows` the expected size of everything up to and including it, which is the
  number a join was actually costed in and the one to read a surprising order against."
  [env rows]
  (list
   [:p.muted "Solved left to right, so the first literal's fan-out multiplies everything "
    "after it. Each row is costed under the bindings the rows above it produce, which is "
    "why the estimates are not a sorted column."]
   [:div.qcn-scroll
    [:table.stats-table
     [:thead [:tr [:th.num "#"] [:th "literal"] [:th.num "est. matches"] [:th.num "rows"]
              [:th.num "plan rows"] [:th.num "block"]
              [:th "bound before"] [:th "position"]]]
     [:tbody
      (for [[i {:keys [goal est-matches est-rows est-prefix block bound-before
                       deferred? recursive? isolated?]}]
            (map-indexed vector rows)]
        [:tr
         [:td.num (inc i)]
         [:td (render-form env goal)]
         [:td.num est-matches]
         [:td.num est-rows]
         [:td.num est-prefix]
         [:td.num (if block (inc (long block)) [:span.muted "—"])]
         [:td (if (seq bound-before)
                (interpose ", " (for [b (by-print-key bound-before)] (render-form env b)))
                [:span.muted "—"])]
         [:td (cond
                deferred?  [:span.tag {:title "consumes bindings rather than producing them"}
                            "fixed: evaluable"]
                recursive? [:span.tag {:title "reordering could turn right-recursion into left"}
                            "fixed: recursive"]
                isolated?  [:span.tag {:title "shares no variable with the rest and matches more than once, so it multiplies whatever follows it"}
                            "deferred: cartesian"]
                :else      [:span.muted "costed"])]])]]]
   [:p.legend "A " [:b "fixed"] " literal keeps the order it was written in, because "
    "its position is operational rather than cost: an evaluable may not outrun what "
    "binds it, and a recursive rule's recursive literal stays last so right-recursion "
    "survives.  A " [:b "cartesian"] " literal shares no variable with the rest, so "
    "nothing narrows it and it narrows nothing — wherever it runs it multiplies the "
    "row count of everything after it.  One that matches at most once multiplies "
    "by at most one, so it leads like any cheap literal and carries no tag."]
   [:p.legend "The " [:b "block"] " column is the rest of that answer.  Literals sharing "
    "a variable are one block and run together; blocks are ranked against each other by "
    "how much each multiplies what follows, so a whole block can be held back the way a "
    "single cartesian literal is — two literals sharing a variable with each other and "
    "with nothing else are a cartesian factor just as much, and neither carries the tag. "
    "A block number that jumps back and forth down the table is the fixed literals threading "
    "evaluables in where they became ready."]))

(defn- plan-section
  "How the engine would answer this goal — the join plan for a conjunction, the prover
  table for a single sentence."
  [{:keys [kb] :as env} goal ctx]
  (let [rows (v/query-plan kb goal ctx)]
    [:div
     [:h3 "How it would be answered"]
     (cond
       (empty? rows) [:p.muted "No prover bears on this goal."]
       (vector? goal) (join-plan env rows)
       :else          (prover-plan rows))]))

(defn levels-page
  "The lookup-to-query stack over a goal: what each of the eight levels answers, so
  the level at which results first appear is the mechanism the answer depends on.
  With no goal, the stack itself.

  A **vector** goal is the conjunctive query `prove` takes, and the levels do not take
  one — they answer about a literal.  So a conjunction gets the join plan and stops
  there, rather than being rendered through eight sections that cannot address it."
  [{:keys [kb] :as env} goal ctx]
  (let [table (v/levels)]
    (render env (if goal (str "levels " (pr-str goal)) "levels")
            [:h2 "Lookup-to-query stack"]
            [:p.muted "Eight levels of escalating machinery over one goal. Each adds exactly "
             "one mechanism to the one below, so a result that appears at level n and not "
             "at n-1 is attributable to that mechanism."]
            [:form.q {:method "get" :action "/levels"}
             (code-area {:name "q" :rows 1 :submit? true :placeholder "(animal ?x)"
                         :value (when goal (pr-str goal))})
             [:input {:type "text" :name "ctx" :size 18 :placeholder "?ctx"
                      :value (when (and ctx (not= '?ctx ctx)) (pr-str ctx))}]
             [:button {:type "submit"} "run"]]
            (cond
              (not (sequential? goal))
              [:div
               (when goal [:p.muted "A goal is a sentence, e.g. " [:code "(animal ?x)"]
                           " — or a vector of them, e.g. "
                           [:code "[(bird ?x) (able ?x flying)]"] ", which is a conjunctive "
                           "query and gets a join plan."])
               [:h3 "The levels"]
               [:ul (for [{lvl :level nm :name adds :adds} table]
                      [:li lvl " " [:span.tag (name nm)] " — " adds])]]

              ;; a conjunction is `prove`'s goal shape, not a literal, so the levels have
              ;; nothing to say about it.
              ;; a vector whose members are not sentences is not a conjunction: it is the
              ;; sentence spelling `query-plan` refuses, and asking for its plan would throw
              ;; where the page has no exception middleware to render it.  Refused here
              ;; as in the guidance above.
              (and (vector? goal) (not-every? seq? goal))
              [:div
               [:h2 "Not a goal" in-cx (term-link env ctx)]
               [:p.muted "A vector goal is a conjunction, so each member has to be a "
                "sentence — e.g. " [:code "[(bird ?x) (able ?x flying)]"] ". "
                "One sentence is written as a list: " [:code "(animal ?x)"] ", not "
                [:code "[animal ?x]"] "."]]

              (vector? goal)
              [:div
               [:h2 "Conjunctive goal" in-cx (term-link env ctx)]
               [:ul (for [g goal] [:li (render-form env g)])]
               (plan-section env goal ctx)
               [:p [:a {:href (str "/inference?q=" (url-enc (pr-str goal))
                                   (when (not= '?ctx ctx) (str "&ctx=" (url-enc (pr-str ctx)))))}
                    "Step through the search for this goal →"]]
               [:p.legend "The eight levels answer about a single literal, so they are "
                "not shown for a conjunction. Ask one conjunct on its own to see them."]]

              :else
              (let [esc (v/escalate kb goal ctx)]
                [:div
                 [:h2 "Goal " (render-form env goal) in-cx (term-link env ctx)]
                 (if-let [lvl (:level esc)]
                   [:p "Answered at level " [:b lvl] " " [:span.tag (name (:name esc))] " "
                    [:span.muted (:adds (nth table lvl))]]
                   [:p.muted "No level answers this goal."])
                 [:p.legend "Escalation starts at level 2 — levels 0 and 1 answer about "
                  "storage rather than truth, so either can claim a goal it cannot verify."]
                 [:p [:a {:href (str "/inference?q=" (url-enc (pr-str goal))
                                     (when (not= '?ctx ctx) (str "&ctx=" (url-enc (pr-str ctx)))))}
                      "Step through the search for this goal →"]]
                 (plan-section env goal ctx)
                 (map #(level-section env goal ctx %) table)])))))

;; ---- the inference debugger ----------------------------------------------
;; `/levels` shows the *plan*; this shows the *run*: the search tree the node engine built
;; for a goal (every node the frontier reached), and the same goal under several tacticians
;; side by side.  Both read through `search-tree` / `compare-tacticians`, which bound their
;; own work, so the page holds no session and works under `--attach`.

(def ^:private debug-depth-default 3)
(def ^:private debug-depth-max
  "The deepest rule expansion the search page will run.  The form's `max` and the route's
  bound are the *same* number rather than two: a form that offers 12 beside a route that
  accepts any depth is a control that describes nothing, and a hand-edited URL is how a
  reader finds out."
  12)
(def ^:private debug-max-ms 4000)
(def ^:private tree-render-cap
  "How many nodes the tree draws before it stops and says so.  The *search* is bounded by
  its own node budget; this bounds the *render*, a different promise — a bounded search can
  still build more nodes than a page should draw at once.  Nodes are numbered in expansion
  order and a child's id always exceeds its parent's, so the first `tree-render-cap` by id
  are prefix-closed under parent and nest into a valid subtree."
  150)

(defn- estimate-line
  "The four terms `estimate` summed, on one line — the same numbers `/levels` reports for
  the same conjunction, so a node's cost is legible against the plan."
  [{:keys [base size-penalty depth-term tree-term total sum-allowance]}]
  [:p.est-line
   "estimate " [:b total] " = base " (commas base) " + size " (commas size-penalty)
   " + depth " (commas depth-term) " + tree " (commas tree-term)
   [:span.muted " · Σ rewriting allowance " sum-allowance]])

(defn- node-literals
  "The node's conjunction as it will be solved, in join order, each literal with the index
  estimate it is costed at — `plan/explain`'s numbers, the same the join runs on."
  [env literals]
  [:div.qcn-scroll
   [:table.stats-table
    [:thead [:tr [:th "literal (join order)"] [:th.num "est. matches"] [:th.num "block"] [:th "placement"]]]
    [:tbody
     (for [{:keys [sentence cost block isolated? deferred? recursive?]} literals]
       [:tr
        [:td (render-form env sentence)]
        [:td.num (commas cost)]
        [:td.num (if block (inc (long block)) [:span.muted "—"])]
        [:td (cond
               deferred?  [:span.tag {:title "consumes bindings rather than producing them"} "evaluable"]
               recursive? [:span.tag {:title "kept last so right-recursion survives"} "recursive"]
               isolated?  [:span.tag {:title "shares no variable with the rest and multiplies it"} "cartesian"]
               :else      [:span.muted "—"])]])]]])

(defn- node-summary
  "The one-line handle on a node: its id, tree depth, the rewrite that produced it (the
  literal it replaced and the rule that did it), its total cost, and — if it produced any
  — an answer count."
  [env {:keys [id tree-depth rewrite results estimate]}]
  (let [n (count results)]
    [:summary {:id (str "node-" id)}
     [:span.node-tag "#" id]
     [:span.muted "depth " tree-depth " · "]
     (if rewrite
       (list (render-form env (:goal rewrite))
             [:span.muted " via "]
             (if-let [rh (:rule rewrite)]
               (handle-ref env rh)
               [:span.muted "a rule"]))
       [:b "the query"])
     [:span.muted " · cost " (commas (:total estimate))]
     (when (pos? n)
       [:span.tag.tag-in n (if (= 1 n) " answer" " answers")])]))

(defn- render-node
  "One node as a collapsible `<details>`: its summary, the itemized estimate that ordered
  it, the rewrite that produced it, the answers that came off it, and its children rendered
  the same way.  Self-recursive over the parent→children map, which is finite and drawn
  from a bounded search."
  [env children-of {:keys [id tree-depth estimate rewrite results guards] :as node}]
  [:details.node (cond-> {:id (str "detail-" id)} (< (long tree-depth) 1) (assoc :open true))
   (node-summary env node)
   [:div.node-body
    ;; goal → answers → children read first; the cost decomposition and per-literal
    ;; estimates are internal tuning, one click away rather than in the default path
    [:details.cost-breakdown
     [:summary [:span.muted "cost breakdown"]]
     (estimate-line estimate)
     (node-literals env (:literals estimate))]
    (when rewrite
      [:p.muted "Rewrote " (render-form env (:goal rewrite)) " through "
       (if-let [rh (:rule rewrite)] (handle-ref env rh) [:span "a rule"])])
    (when (pos? (long guards))
      [:p.muted guards " guard" (when (> (long guards) 1) "s") " carried here (an "
       [:code "exceptWhen"] ", asked when the conjunction completes)."])
    (when (seq results)
      [:div
       [:p.muted "Answers off this node:"]
       [:ul (for [b results]
              [:li (if (seq b) (bindings-str env b) [:span.muted "(ground — the conjunction holds)"])])]])
    (for [k (get children-of id)] (render-node env children-of k))]])

(defn- status-tag
  [status]
  (let [cls (case status :complete "tag-in" :bounded "tag" :timeout "tag-defeated" "tag")]
    [:span {:class (str "tag " cls)} (name status)]))

(defn- tactician-table
  "The same goal under several tacticians, tabled by the work each did and the answers each
  found, with the identity property **verified** below rather than asserted: every
  tactician is complete, so the answer sets must match, and a row that differs is a bug the
  completeness sweep exists to catch."
  [_env rows]
  (let [complete (filter #(= :complete (:status %)) rows)
        baseline (:answers (first complete))
        agree?   (or (< (count complete) 2) (apply = (map :answers complete)))]
    (list
     [:div.qcn-scroll
      [:table.stats-table
       [:thead [:tr [:th "tactician"] [:th.num "nodes"] [:th.num "expanded"] [:th.num "dropped"]
                [:th.num "solutions"] [:th.num "ms"] [:th.num "answers"] [:th "status"]]]
       [:tbody
        (for [{:keys [tactician nodes expanded dropped solutions ms answers status]} rows]
          (let [odd? (and (= :complete status) baseline (not= answers baseline))]
            [:tr
             [:td (if (= :ground-first tactician)
                    [:span [:b (name tactician)] [:span.muted " · default"]]
                    (name tactician))]
             [:td.num (commas nodes)] [:td.num (commas expanded)] [:td.num (commas dropped)]
             [:td.num (commas solutions)] [:td.num (commas ms)] [:td.num (commas (count answers))]
             [:td (status-tag status)
              (when odd? [:span.tag.tag-defeated {:title "differs from the other tacticians"} "differs"])]]))]]]
     (if agree?
       [:div.verdict.verdict-agree
        [:p [:b "The same answer set across every complete tactician."]
         (when (seq complete)
           (list " " (commas (count complete)) " orderings, " (commas (count baseline))
                 " answer" (when (not= 1 (count baseline)) "s") " each — verified here, not "
                 "assumed. Ordering is a cost decision and never a semantic one; what differs "
                 "between the rows is the work and the wall-clock, not the answers."))]]
       [:div.verdict.verdict-disagree
        [:p [:b "The tacticians disagree on the answer set."] " Every tactician here is "
         "complete — each only reorders the frontier — so this cannot happen unless one "
         "dropped a node, which is a real bug the completeness sweep is meant to catch. The "
         "differing rows are marked."]]))))

(defn- search-answers
  "The answers the search found, each tagged with the node it came off — so the answer is
  reachable to the subtree that produced it."
  [env {:keys [answers unenumerated]}]
  (let [n (count answers)]
    [:div
     [:h3 (commas n) " answer" (when (not= 1 n) "s")]
     (when (seq unenumerated)
       [:p [:b "Incomplete: "] "a goal asked " (interpose ", " (map #(term-link env %) unenumerated))
        " with both arguments open, which answers the stored pairs and not the transitive "
        "closure. Bind one argument to get the derived pairs."])
     (if (seq answers)
       (list
        [:ul (for [a (take 50 answers)]
               [:li (if (seq (:bindings a))
                      (bindings-str env (:bindings a))
                      [:span.muted "(ground — the goal holds)"])
                [:span.muted " · from "] [:a {:href (str "#node-" (:node a))} "node #" (:node a)]])]
        (when (> n 50) [:p.muted "… " (commas (- n 50)) " more."]))
       [:p.muted "No answer within the depth bound. A derivation deeper than the bound is "
        "not found — the depth a query needs is a property of the data, so raise it and re-run."])]))

(defn- search-tree-summary
  "One line of what the run cost, and whether the tree shown is
  the whole search or a prefix a bound cut off."
  [{:keys [status stats strategy]}]
  (let [{:keys [nodes expanded dropped solutions max-depth]} stats]
    [:p.muted
     "Ordered by " [:b (name strategy)] ". Built " [:b (commas nodes)] " nodes, expanded "
     (commas expanded) ", dropped " (commas dropped) " duplicate arrivals, completed "
     (commas solutions) " solutions, deepest rewrite " max-depth ". "
     (case status
       :complete "The frontier emptied, so this is the whole search."
       :bounded  [:b "Stopped at the node budget — the tree below is a prefix of the search."]
       :timeout  [:b "Stopped at the time bound — the tree below is a prefix of the search."]
       nil)]))

(defn inference-page
  "The search stepped through — a goal, a context and a depth in; the tree the node engine
  builds out, plus the same goal raced across tacticians.  Sits beside `/levels`: a goal
  typed at either is answerable at both.

  A depth is required (the node engine's termination is the bound and nothing else), so the
  form always carries one.  A malformed goal, or one the search cannot run, is rendered
  rather than thrown — the page has no exception middleware."
  [{:keys [kb] :as env} goal ctx depth]
  (render env (if goal (str "search " (pr-str goal)) "search")
          [:h2 "The search, stepped through"]
          [:p.muted "The " [:a {:href "/levels"} "levels page"] " shows the plan; this shows "
           "the run it predicted — the tree the node engine builds for a goal, every node the "
           "frontier reached and what each cost, and the same goal under several tacticians "
           "side by side. Expanding rules needs a depth bound."]
          [:form.q {:method "get" :action "/inference"}
           [:input {:type "text" :name "q" :size 40 :placeholder "(anc ?x ?z)"
                    :value (when goal (pr-str goal))}]
           [:input {:type "text" :name "ctx" :size 14 :placeholder "?ctx"
                    :value (when (and ctx (not= '?ctx ctx)) (pr-str ctx))}]
           [:input {:type "number" :name "d" :min 1 :max debug-depth-max :value depth
                    :title "depth bound"}]
           [:button {:type "submit"} "search"]]
          (cond
            (nil? goal)
            [:div
             [:p.muted "A goal is a sentence, e.g. " [:code "(anc ?x ?z)"] " — or a vector of "
              "them, e.g. " [:code "[(edgeOf ?x ?y) (anc ?y ?z)]"] ", a conjunctive query. The "
              "search runs the same one " [:code "query"] " runs: the registry is the leaf, so an "
              "antecedent is answerable by any prover, and this is only the rule expansion on top."]]

            (and (vector? goal) (not-every? seq? goal))
            [:div
             [:h2 "Not a goal" in-cx (term-link env ctx)]
             [:p.muted "A vector goal is a conjunction, so each member has to be a sentence — "
              "e.g. " [:code "[(edgeOf ?x ?y) (anc ?y ?z)]"] ". One sentence is a list: "
              [:code "(anc ?x ?z)"] ", not " [:code "[anc ?x ?z]"] "."]]

            (not (or (seq? goal) (vector? goal)))
            [:div
             [:h2 "Not a goal" in-cx (term-link env ctx)]
             [:p.muted "A goal is a sentence like " [:code "(anc ?x ?z)"] ", or a vector of them."]]

            :else
            (try
              (let [opts        {:max-depth depth :max-ms debug-max-ms}
                    tree        (v/search-tree kb goal ctx opts)
                    rows        (v/compare-tacticians kb goal ctx opts)
                    nodes       (:nodes tree)
                    capped      (into [] (take tree-render-cap) nodes)
                    children-of (group-by :parent-id capped)
                    root        (first (filter #(nil? (:parent-id %)) capped))
                    ctx-q       (when (and ctx (not= '?ctx ctx)) (str "&ctx=" (url-enc (pr-str ctx))))]
                (prime-belief! env (keep #(get-in % [:rewrite :rule]) capped))
                [:div
                 [:p [:a {:href (str "/levels?q=" (url-enc (pr-str goal)) ctx-q)}
                      "See the plan and the eight levels for this goal →"]]

                 [:h3 "Tacticians, side by side"]
                 [:p.muted "Each ordering run to completion over the same goal, timed on its "
                  "own. A latency measurement over a fixed answer set — the fast column is fast "
                  "because it reached the answers sooner, not because it found fewer."]
                 (tactician-table env rows)

                 (search-answers env tree)

                 [:h3 "The search tree"]
                 (search-tree-summary tree)
                 [:p.legend "Nodes are written in the search's own "
                  [:span.t-var "?var0"] "/" [:span.t-var "?var1"] " names; two questions "
                  "equal up to variable names are one node."]
                 [:div.search-tree (when root (render-node env children-of root))]
                 (when (> (count nodes) tree-render-cap)
                   [:p.legend "Showing the first " tree-render-cap " of " (commas (count nodes))
                    " nodes by allocation order; the search itself is bounded by the node "
                    "engine's own budget."])])
              (catch clojure.lang.ExceptionInfo e
                [:div
                 [:h3 "The search could not run"]
                 [:p.muted (.getMessage e)]])))))

;; ---- the constraint network ---------------------------------------------
;; The one subsystem whose object is not a sentex.  A qualitative calculus computes a
;; *network* over a whole context — every pair of terms its predicates relate, at once —
;; so a page that showed one pair at a time would hide precisely what the algebra does.
;; This renders the matrix, the consistency verdict, and one arrangement out of it.

(def ^:private matrix-node-limit
  "Nodes past which the matrix is a wall rather than a picture.  The network is computed
  either way; this bounds only the render, and the determined pairs are listed instead."
  16)

(defn- relation-cell
  "One constraint: the base relations still possible between two nodes.  A singleton is
  a determined arrangement and is shown as the one name; the whole universe is ignorance and
  is shown as a dot, because a matrix saying `unknown` in every cell is noise."
  [rels base]
  (let [n (count rels)]
    (cond
      (nil? rels)      [:span.muted {:title "unknown"} "·"]
      (zero? n)        [:span.tag.tag-defeated {:title "no relation possible"} "∅"]
      (= n (count base)) [:span.muted {:title "unknown"} "·"]
      (= n 1)          [:b {:title "determined"} (name (first rels))]
      :else            [:span.muted {:title (str n " still possible")}
                        (str/join " " (map name (sort rels)))])))

(defn- network-matrix
  "The tightened network as a table — row *r*, column *c* is what still holds of
  `(r c)`.  Not symmetric: the cell below the diagonal is the converse of the one
  above, which is what makes a directional relation legible."
  [env {:keys [nodes constraints]} base]
  [:div.qcn-scroll
   [:table.stats-table.qcn-matrix
    [:thead [:tr [:th] (for [c nodes] [:th (term-link env c)])]]
    [:tbody
     (for [r nodes]
       [:tr [:th (term-link env r)]
        (for [c nodes]
          [:td (if (= r c)
                 [:span.muted {:title "the diagonal is the identity"} "—"]
                 (relation-cell (get constraints [r c]) base))])])]]])

(defn- determined-pairs
  "The pairs path consistency narrowed to a single relation — the matrix's content when
  the matrix itself would be too wide to read."
  [env {:keys [constraints]}]
  (let [determined (sort-by (comp print-key key)
                            (filter (fn [[_ rels]] (= 1 (count rels))) constraints))]
    (if (seq determined)
      [:ul (for [[[a b] rels] determined]
             [:li (term-link env a) " " [:b (name (first rels))] " " (term-link env b)])]
      [:p.muted "No pair is narrowed to a single relation."])))

(defn network-page
  "The constraint network a calculus computes over one context: which terms it relates,
  what still holds of every pair, whether the believed facts are satisfiable at all, and
  one concrete arrangement consistent with them.

  Every calculus is offered whether or not its prover is registered — a network is a
  property of the stored facts, and `add-prover` only decides whether `ask` consults it."
  [{:keys [kb] :as env} ctx calc]
  (let [table    (v/calculi)
        stated   #(reduce + (map (partial v/count-with-functor kb) (:predicates %)))
        sized    (when ctx
                   (for [{nm :calculus :as c} table]
                     (assoc c :net (v/qualitative-network kb nm ctx))))
        by-name  (into {} (map (juxt :calculus identity)) (or sized []))
        chosen   (or (get by-name calc)
                     (->> sized (filter #(seq (:nodes (:net %)))) first))
        net      (:net chosen)
        base     (:base chosen)]
    (render env (if ctx (str "network " (pr-str ctx)) "network")
            [:h2 "Qualitative constraint network"]
            [:p.muted "A relation algebra reads every fact of its own vocabulary in a "
             "context into one network and tightens it by composition, so a relation "
             "nobody stated is entailed by the ones that were. Name a context to read "
             "its network."]
            [:form.q {:method "get" :action "/network"}
             [:input {:type "text" :name "ctx" :size 24 :placeholder "a context"
                      :value (when ctx (pr-str ctx))}]
             [:select {:name "calc"}
              (for [{nm :calculus} table]
                [:option (cond-> {:value (name nm)}
                           (= nm (:calculus chosen)) (assoc :selected "selected"))
                 (name nm)])]
             [:button {:type "submit"} "read"]]
            (if-not ctx
              [:div
               [:h3 "The calculi"]
               [:p.muted "Each is a set of jointly exhaustive, pairwise disjoint base "
                "relations — exactly one holds of any two terms — plus the derived "
                "predicates naming disjunctions of them."]
               (when (zero? (reduce + (map stated table)))
                 [:p "This KB states no fact in any calculus's vocabulary, so every network "
                  "in it is empty."])
               [:div.table-scroll
                [:table.stats-table
                 [:thead [:tr [:th "calculus"] [:th.num "base"] [:th.num "predicates"]
                          [:th.num "stored facts"] [:th "vocabulary"]]]
                 [:tbody
                  (for [{nm :calculus b :base preds :predicates :as c} table]
                    [:tr [:th (name nm)]
                     [:td.num (count b)] [:td.num (count preds)] [:td.num (commas (stated c))]
                     [:td.muted (str/join ", " (map str (take 6 preds)))
                      (when (> (count preds) 6) " …")]])]]]]
              [:div
               [:h3 "Contexts and calculi"]
               [:p.legend "How many terms each calculus relates in " (term-link env ctx)
                ". A calculus with none has no facts of its vocabulary visible here."]
               [:ul.qcn-sizes
                (for [{nm :calculus n :net} sized
                      :let [cnt (count (:nodes n))]]
                  [:li (if (= nm (:calculus chosen)) [:b (name nm)] (name nm))
                   " " [:span.muted cnt " node" (when (not= 1 cnt) "s")]
                   (when-not (:consistent? n)
                     [:span.tag.tag-defeated {:title "unsatisfiable"} "inconsistent"])])]
               (cond
                 (nil? net)
                 [:p.muted "No calculus relates anything in this context."]

                 (empty? (:nodes net))
                 [:p.muted "This calculus relates nothing in " (term-link env ctx) "."]

                 :else
                 [:div
                  [:h3 (name (:calculus chosen)) " in " (term-link env ctx)]
                  (if (:consistent? net)
                    [:p [:span.tag.tag-in "satisfiable"] " "
                     [:span.muted (count (:nodes net)) " nodes"]]
                    [:div
                     [:p [:span.tag.tag-defeated "unsatisfiable"]
                      " — no arrangement satisfies every believed fact, so this "
                      "calculus answers no goal in this context."]
                     (if-let [bad (seq (:unsatisfiable net))]
                       [:p.legend "Unsatisfiable as written: "
                        (interpose ", " (for [[a b] bad]
                                          [:span (term-link env a) "/" (term-link env b)]))]
                       (when-not (seq (:unsatisfiable-sources net))
                         [:p.legend "No single pair is to blame — composition is what "
                          "emptied a constraint, so the clash is a property of the set."]))
                     (for [{:keys [source pairs cycle dimensions support]}
                           (:unsatisfiable-sources net)]
                       [:p.legend "The " (name source) " network this calculus reads is "
                        "unsatisfiable"
                        (when (seq dimensions)
                          (list ": its constraints span the dimensions "
                                (interpose ", " (for [d dimensions] (term-link env d)))))
                        (when (seq cycle)
                          (list ": the instants on a negative cycle are "
                                (interpose ", " (for [i cycle] (term-link env i)))))
                        (when (seq pairs)
                          (list (if (seq cycle) "; unsatisfiable as written: " ": unsatisfiable as written: ")
                                (interpose ", " (for [[a b] pairs]
                                                  [:span (term-link env a) "/" (term-link env b)]))))
                        " (" (count support) " fact" (when (not= 1 (count support)) "s") ")."])])
                  (if (<= (count (:nodes net)) matrix-node-limit)
                    (network-matrix env net base)
                    [:div [:p.legend "Too many nodes to draw the matrix; the determined "
                           "pairs are:"]
                     (determined-pairs env net)])
                  [:p.legend "A cell is what still holds of (row, column): "
                   [:b "one name"] " is determined, several are still open, "
                   [:span.muted "·"] " is unknown."]
                  (when (:consistent? net)
                    (let [scen (v/qualitative-scenario kb (:calculus chosen) ctx)]
                      [:div
                       [:h3 "One scenario"]
                       [:p.muted "Path consistency leaves a set per pair; a scenario "
                        "picks one member of every set at once — the difference between "
                        "\"nothing rules this out\" and \"here is a world\"."]
                       (if (seq scen)
                         [:ul.qcn-scenario
                          (for [[[a b] rel] (sort-by (comp print-key key) scen)
                                :when (neg? (compare (print-key a) (print-key b)))]
                            [:li (term-link env a) " " [:b (name rel)] " "
                             (term-link env b)])]
                         [:p.muted "Nothing to arrange."])]))])]))))

(defn justification-page [{:keys [kb] :as env} jid]
  (if-let [d (v/justification kb jid)]
    (let [antes    (:antecedents d)
          ;; the antecedents plus the rule: what validity reads, so what can be OUT
          grounds  (v/rests-on d)
          conc     (:consequence d)
          ;; one batched read; sentex-list below re-uses the same primed cache
          _        (prime-belief! env (conj grounds conc))
          out      (into [] (remove #(believed? env %)) grounds)
          ;; the verdict the conclusion's context reads on this justification: a blocked,
          ;; guarded, void or exempt one supports nothing even when every argument is IN,
          ;; a separate condition from an argument being OUT, and stated separately below
          verdict  (get (v/justification-verdicts kb conc (:context (v/sentex kb conc))) jid)
          valid?   (= :supports verdict)
          conc-in? (believed? env conc)]
      (render env (str "justification #" jid)
              [:h2 "Justification " [:span.muted "#" jid]]
              [:p "Rule / informant: "
               (if (number? (:informant d))
                 (handle-ref env (:informant d))
                 [:code (pr-str (:informant d))])
               " · strength " [:code (name (:strength d :monotonic))]]
              ;; is this justification currently carrying its conclusion?  It supports iff
              ;; every argument is IN *and* the JTMS has not blocked it.  The conclusion being
              ;; IN is a separate question — a second justification may carry it — so both are
              ;; stated.
              [:div.belief
               (cond
                 valid?
                 [:p [:span.tag.tag-in "valid"] " — every argument is believed, so this "
                  "justification currently supports its conclusion "
                  (handle-ref env conc) " "
                  (if conc-in? [:span.tag.tag-in "IN"]
                      (list (state-tag env conc)
                            [:span.muted " (carried, if at all, by another justification)"])) "."]

                 ;; blocked, guarded, void or exempt: it confers nothing whatever its
                 ;; arguments read.  Said apart from the OUT-argument case, whose "N of M
                 ;; arguments are OUT" would read "0 of M" here and mislead.
                 (verdict-text verdict)
                 [:p [:span.tag.tag-out "not supporting"] " — " (verdict-text verdict)
                  ": it confers nothing even though its arguments may be believed. Its conclusion "
                  (handle-ref env conc) " is "
                  (if conc-in? [:span.tag.tag-in "IN"] (state-tag env conc))
                  (when conc-in? [:span.muted " (carried by another justification)"]) "."]

                 :else
                 (list
                  [:p [:span.tag.tag-out "not supporting"] " — "
                   (if (seq out)
                     (str (count out) " of " (count grounds) " arguments are OUT")
                     "an argument is withdrawn at its conclusion's context")
                   ", so this justification confers nothing right now. Its conclusion "
                   (handle-ref env conc) " is "
                   (if conc-in? [:span.tag.tag-in "IN"] (state-tag env conc)) "."]
                  [:ul (for [h out]
                         [:li (handle-ref env h) " " (state-tag env h)])]))]
              [:h3 "Supports " [:span.muted "(arguments)"]]
              (sentex-list env (keep #(v/sentex kb %) antes))
              [:h3 "Dependent sentex " [:span.muted "(conclusion)"]]
              (sentex-list env (keep #(v/sentex kb %) [conc]))))
    (render env "not found" [:p "No justification #" jid])))

;; ---- why: the proof tree ------------------------------------------------
;; The sentex page shows one hop.  `vaelii.core/why` returns the whole justification graph
;; down to premises, each handle once.  The page renders it as a tree from the root: one
;; `<details>` per derived node, its justifications as branches.  A derived node expands
;; at its first occurrence in content order, and later occurrences (a shared antecedent, a
;; cycle to an ancestor) link to it.  A derived node first reached `why-nest-depth` levels
;; down continues as a tree of its own.  A branch ends at a premise or at a node that is
;; not believed (`why-not` answers it).

(def ^:private why-open-depth
  "How deep the tree opens by default.  A proof's shape is the point, so the first
  levels are open; deeper branches are one click away rather than a wall of text."
  3)

(defn- why-head
  "One node's line: its badge, its sentence, and the context it holds in."
  [env {:keys [handle context]}]
  (list (handle-ref env handle)
        (when context (list in-cx (term-link env context)))))

(defn- why-anchor
  "The element id of handle `h`'s expanded node on a rendered proof."
  [h]
  (str "why-" h))

(def ^:private why-nest-depth
  "How many proof levels one rendered tree nests before a derived node continues as a tree
  of its own below it.  hiccup renders nested elements by recursion: a 300-level chain
  nested whole renders, and a 1,000-level one overflows the stack."
  64)

(defn- why-tree
  "`v/why`'s graph `w` as `<ul>` trees: the tree from its root, then one tree per derived
  node first reached at `why-nest-depth`, in content order.  A node is a leaf, and says
  which kind, unless it is derived:

    premise         asserted, with the assumption strength it was asserted at
    not believed    stored but OUT; `why-not` (the sentex page) gives the reason
    not stored      the handle names nothing
    shown above     a derived node already expanded earlier on the page, linked
    continued below a derived node expanded in a later tree, linked

  A derived node is a `<details>` whose branches are its justifications, expanded once."
  [env w]
  (let [nodes   (:nodes w)
        seen    (volatile! #{})                 ; expanded, or queued as a tree of its own
        done    (volatile! #{})                 ; expanded
        pending (volatile! clojure.lang.PersistentQueue/EMPTY)
        link    (fn [h text] [:a {:href (str "#" (why-anchor h))} text])]
    (letfn [(expand [depth {:keys [handle defeat-class support] :as node}]
              (vswap! done conj handle)
              [:details (cond-> {:id (why-anchor handle)}
                          (< depth why-open-depth) (assoc :open "open"))
               [:summary (why-head env node) " "
                ;; every <details> node is believed (why expands only believed nodes), so
                ;; IN is a constant — no KB read
                [:span.tag.tag-in "IN"] " "
                (when defeat-class [:span.tag (str "class " (name defeat-class))])
                [:span.muted " · " (count support)
                 (if (= 1 (count support)) " justification" " justifications")]]
               [:ul.why
                ;; a justification is supporting when its verdict at the node's context is
                ;; `:supports` (`v/why` reads it, `v/justification-verdicts`): every
                ;; argument believed there, and no exception, guard defeat or declaration
                ;; voiding it.  `doall`: `seen` must fill in content order, and hiccup
                ;; reads a vector as an element, so the branches are a seq
                (doall
                 (map (fn [{:keys [justification informant rule strength verdict because]}]
                        [:li (justification-link justification) " "
                         (if rule
                           [:span "via " (handle-ref env informant)]
                           [:span.muted "via " (pr-str informant)])
                         " " [:span.tag (name (or strength :monotonic))] " "
                         (if (= :supports verdict)
                           [:span.tag.tag-in {:title "every argument is believed here and nothing blocks it, so this justification currently supports the conclusion"} "supporting"]
                           [:span.tag.tag-out
                            {:title (or (verdict-text verdict)
                                        "an argument is not believed here, so this justification is not currently supporting")}
                            "blocked"])
                         (when (seq because)
                           [:ul.why (doall (map #(node-li (inc depth) %) because))])])
                      support))]])
            (node-li [depth h]
              (let [{:keys [handle stored? believed? premise? strength] :as node} (get nodes h)
                    head (why-head env node)]
                (cond
                  (false? stored?)   [:li head " " [:span.tag.tag-not-stored "not stored"]]
                  (false? believed?) [:li head " " [:span.tag.tag-out "not believed"] " "
                                      [:a {:href (str "/sentex/" handle)} "why not"]]
                  premise?           [:li head " " [:span.tag.tag-premise "premise"]
                                      (when strength [:span.tag (str "assumed " (name strength))])]
                  (@done handle)     [:li head " " (link handle "shown above")]
                  (@seen handle)     [:li head " " (link handle "continued below")]
                  (>= depth why-nest-depth)
                  (do (vswap! seen conj handle)
                      (vswap! pending conj handle)
                      [:li head " " (link handle "continued below")])
                  :else
                  (do (vswap! seen conj handle)
                      [:li (expand depth node)]))))]
      (let [main (node-li 0 (:root w))]
        (loop [trees [[:ul.why main]]]
          (if-let [h (peek @pending)]
            (do (vswap! pending pop)
                (recur (conj trees [:ul.why [:li (expand 0 (get nodes h))]])))
            (seq trees)))))))

(defn why-page
  "The whole proof tree for a handle — `vaelii.core/why` rendered, collapsible.  Linked
  from the sentex page, which shows only the first hop."
  [{:keys [kb] :as env} h]
  (if-let [s (v/sentex kb h)]
    (let [w    (v/why kb h)
          root (get (:nodes w) (:root w))]
      (render env (str "why #" h)
              [:h2 "Why " [:span.muted "#" h]]
              [:p.sx-item (sentex-line env s)]
              (if (:believed? root)
                (let [sup (:support root)
                      ;; the verdict the tree's pills show, so the count and the pills agree
                      ok  (count (filter #(= :supports (:verdict %)) sup))]
                  (list
                   [:p.muted "The proof, down to the premises it rests on. Each branch is a "
                    "justification; the rule that licensed it is named beside it."]
                   (when (> (count sup) 1)
                     [:p.legend ok " of " (count sup) " justifications currently support this; "
                      "the rest are shown " [:span.tag.tag-out "blocked"] "."])))
                [:p.muted "This sentex is not believed, so there is no proof to show — "
                 [:a {:href (str "/sentex/" h)} "the sentex page"] " reports why not."])
              (why-tree env w)))
    (render env "not found" [:p "No sentex #" h])))

;; ---- the non-monotonicity demo ------------------------------------------
;; `(able Pingu flying)` is believed; the KB then learns `(penguin Pingu)` and
;; stops believing it, with nothing deleted or overridden.  Retracting the penguin claim
;; brings it back.  Every step is an ordinary `edit` against the reader's own sandbox, and
;; every handle links to its record.  The conclusion that comes back is the **same
;; sentex**: `exceptWhen` blocks rather than rebuts, so the firing stays stored and a guard
;; defeat resting on `(penguin Pingu)` hides it (docs/naf.md).  The page names the handle
;; at both steps, since belief changing while the record does not shows belief is read
;; from what is stored.

(def ^:private demo-subject
  "Who the walkthrough is about.  One individual, in the reader's own sandbox, so two
  readers of one process never collide and the sandbox reset takes every trace away."
  'Pingu)

(defn- demo-claim
  "`(<pred> Pingu)` — a sentence the demo makes, or asks about."
  [pred] (list pred demo-subject))

(defn- demo-cap
  "`(able Pingu <event-kind>)` — what the walkthrough's conclusion is about.
  Flight is an event kind Pingu can be the doer of rather than a one-place property, so the
  conclusion under test is a binary sentence and the demo builds it apart from `demo-claim`."
  [event-kind] (list 'able demo-subject event-kind))

(def ^:private demo-script
  "The three steps.  `:from` is the state the KB has to be in for a step to be the next
  one, so which button the page offers is a fact about the KB rather than a counter the
  page keeps."
  [{:n 1 :from :before   :op "start"
    :button "Assert (bird Pingu)"
    :does   "Tell the KB that Pingu is a bird. Say nothing whatever about flying."
    :then   "(able Pingu flying) becomes believed"}
   {:n 2 :from :believed :op "except"
    :button "Assert (penguin Pingu)"
    :does   "Tell it Pingu is a penguin. Retract nothing, delete nothing, override nothing."
    :then   "(able Pingu flying) stops being believed"}
   {:n 3 :from :blocked  :op "restore"
    :button "Retract (penguin Pingu)"
    :does   "Take the penguin claim back."
    :then   "(able Pingu flying) is believed again — the same record"}])

(def ^:private demo-watched
  "The five sentences the walkthrough touches, in the order they make sense in: the two
  the reader asserts, the conclusion under test, what the event-kind hierarchy answers
  from it, and the positive claim a penguin carries.  All five are rendered at every step, because the
  cascade is the part worth seeing — the conclusion does not go alone, and the KB does
  not merely fail to conclude flight, it concludes flightlessness, which is a different
  statement."
  [{:form (demo-claim 'bird)
    :note "asserted — step 1"}
   {:form (demo-claim 'penguin)
    :note "asserted — step 2, taken back in step 3"}
   {:form (demo-cap 'flying)
    :note "derived — the conclusion under test"}
   {:form      (demo-cap 'travelling)
    :answered? true
    :note      "answered through the event-kind hierarchy, never stored — it goes when the flight goes"}
   {:form (list 'not (demo-cap 'flying))
    :note "derived from (penguin Pingu) — a positive claim, not the absence of one"}])

(defn- demo-state
  "Where the walkthrough stands, read off the KB rather than remembered.  `first-h` is
  the handle the flight conclusion carried the first time round, threaded through the step
  forms, so step 3 can name the handle step 1 reached.  `returned?` is true on the answer
  to step 3's write: the KB after step 3 holds what it held after step 1, so the write is
  what tells the two apart."
  [{:keys [kb sandbox] :as env} first-h returned?]
  (let [live?   (boolean (and sandbox @(:sandbox-live? env)))
        at      #(when live? (v/handle-of kb % sandbox))
        bird    (at (demo-claim 'bird))
        penguin (at (demo-claim 'penguin))
        flight  (at (demo-cap 'flying))
        stage   (cond (nil? bird)                :before
                      penguin                    :blocked
                      (and returned? flight)     :returned
                      :else                      :believed)]
    {:bird bird :penguin penguin :flight flight :stage stage
     ;; carried forward: at :believed we adopt whatever handle is visible, so a reader
     ;; who arrives part-way through still gets step 3's comparison
     :first (if (= :believed stage) (or first-h flight) first-h)}))

(def ^:private demo-done
  "How many steps are behind you in each stage."
  {:before 0 :believed 1 :blocked 2 :returned 3})

(defn- demo-ledger
  "The script, with the step you are on marked.  Which one that is comes from the KB
  (`demo-state`), so a reader who reloads, navigates away, or resets lands on the line
  that is actually true."
  [{:keys [stage]}]
  (let [done (demo-done stage 0)]
    [:ol.demo-steps
     (for [{:keys [n does then]} demo-script
           :let [where (cond (<= n done)      "is-done"
                             (= n (inc done)) "is-now"
                             :else            "is-next")]]
       [:li {:class (str "demo-step " where)}
        [:span.demo-mark {:aria-hidden "true"} (if (<= n done) "✓" n)]
        [:span.demo-does does " " [:span.muted "⇒ " then]]])]))

(defn- demo-verdict
  "What the flight conclusion is at this moment, with the evidence.  Believed: the proof tree,
  so the rule that concluded it is on the page and every node links to its record.
  Blocked: `why-not`'s sentence arity, and the stored record the guard defeat hides."
  [{:keys [kb sandbox] :as env} {:keys [stage flight first]}]
  (case stage
    :before
    [:div.belief
     [:p [:b "Not stored, not believed."] " Your sandbox holds nothing about Pingu yet."]]

    :blocked
    (let [{:keys [reason rule exception via]} (v/why-not kb (demo-cap 'flying) sandbox)]
      [:div.belief
       [:p [:b "Not believed"] " — and nobody said so. "
        (if (= :excepted reason)
          (list "The flight rule " (handle-ref env rule) " states its own exception, "
                [:span.sx (pr-str exception)] ", and that now holds of Pingu"
                (when (seq via)
                  (list " — from " (interpose ", " (map #(handle-ref env %) via))))
                ", so it does not conclude.")
          (list "why-not reports " [:code (str reason)] "."))]
       [:p "The conclusion is still stored"
        (when flight (list " as " (handle-ref env flight)))
        ". The rule's guard placed a " [:i "guard defeat"] " resting on the penguin claim, "
        "and the defeat hides the conclusion and what rests on it."]])

    ;; :believed / :returned
    [:div.belief
     [:p [:b "Believed"] " — and nobody asserted it. " (handle-ref env flight)
      " is a conclusion; the rule that reached it is one line down."]
     (why-tree env (v/why kb flight))
     (when (= :returned stage)
       [:p.demo-point
        [:b "Look at the handle."] " Step 1 concluded " [:code (str "#" first)]
        "; this is " [:code (str "#" flight)] ", the " [:i "same record"] ". Retracting "
        "the penguin claim took the guard defeat's support away, and nothing was "
        "re-derived: belief is read from what is stored, and the stored record never "
        "moved."])
     [:p.muted [:a {:href (str "/why/" flight)} "The whole proof"] " · "
      [:a {:href (str "/sentex/" flight)} "the record"]]]))

(defn- demo-fact-row
  "One watched sentence and what the KB says about it right now: the record and its
  belief pill when it is stored, and plainly *not stored* when it is not.  A row marked `:answered?` names a sentence the KB answers at
  retrieval and never stores, so it shows what `argue` answers instead: *answerable* with
  the records each reading rests on (the derivation leaf's `:supports`), or *unanswerable*."
  [{:keys [kb sandbox] :as env} {:keys [form note answered?]}]
  (let [live? (boolean (and sandbox @(:sandbox-live? env)))
        h     (when (and sandbox (not answered?)) (v/handle-of kb form sandbox))
        s     (when h (v/sentex kb h))]
    [:li.demo-fact
     (cond
       answered? (let [r    (when live? (v/argue kb form sandbox))
                       sups (when (seq (:for r)) (some :supports (:for-derivation r)))]
                   (list [:span.demo-absent (render-form env form)] " "
                         (if (seq (:for r))
                           [:span.tag.tag-in "answerable"]
                           [:span.tag.tag-out "unanswerable"])
                         (when sups
                           (list " from "
                                 (interpose " or "
                                            (for [reading sups]
                                              (interpose ", " (map #(handle-ref env (:handle %)) reading))))))))
       s         (list (sentex-ref env s) " " (state-tag env h))
       :else     (list [:span.demo-absent (render-form env form)] " "
                       [:span.tag.tag-out "not stored"]))
     [:span.demo-note note]]))

(defn- demo-step-form
  "One step's button.  A POST, because every one of them writes."
  [{:keys [op label first primary?]}]
  [:form.demo-run {:method "post" :action "/demo"
                   :hx-post "/demo" :hx-target "#main" :hx-select "#main"
                   :hx-swap "outerHTML"}
   [:input {:type "hidden" :name "do" :value op}]
   (when first [:input {:type "hidden" :name "first" :value (str first)}])
   [:button (cond-> {:type "submit"} primary? (assoc :class "primary")) label]])

(defn- demo-controls
  "The next step, and the way back to the beginning.  Exactly one step is ever offered:
  the script is a line, not a menu, and which line you are on is read from the KB."
  [{:keys [stage first]}]
  (let [nxt (some #(when (= stage (:from %)) %) demo-script)]
    [:div.demo-controls
     (when nxt
       (demo-step-form {:op (:op nxt) :first first :primary? true
                        :label (str "Step " (:n nxt) " — " (:button nxt))}))
     (when-not (= :before stage)
       (demo-step-form {:op "reset" :label "Start over"}))]))

(defn demo-page
  "The walkthrough: the script, the evidence for the conclusion under test, the next
  button, and what the KB currently holds about Pingu.  Everything on it is read back out
  of the KB *after* the write, so the page cannot claim a state the engine is not in."
  ([env] (demo-page env nil false))
  ([env first-h] (demo-page env first-h false))
  ([{:keys [sandbox] :as env} first-h returned?]
   (let [st (demo-state env first-h returned?)]
     (render env "belief that changes"
             [:h2 "Believed, then not, then believed again"]
             [:p.muted "A rule concludes that Pingu flies. Learning one more true thing "
              "stops the KB believing it — without deleting it, without contradicting it, "
              "and without anyone ranking one claim over another — and un-learning that "
              "thing brings it back. Each step below is a real write to "
              [:a {:href "/assert"} "your own sandbox"] "."]
             (demo-ledger st)
             [:h3 "The conclusion under test " [:span.muted "(able Pingu flying)"]]
             (demo-verdict env st)
             (demo-controls st)
             [:h3 "Everything about Pingu " [:span.muted "as the KB holds it right now"]]
             [:ul.demo-facts (for [w demo-watched] (demo-fact-row env w))]
             [:p.legend "Everything here is in " [:code (str sandbox)] ", your own sandbox. "
              [:b "Start over"] " discards it whole."]))))

(defn demo-apply
  "Do one step's write, and answer the `first`-handle to carry forward.  Split from the
  rendering because the page is built from a render env taken *after* the write (step 1
  creates the sandbox).  Both adding steps open the sandbox first: without its `genlCx`
  edge it sees no shipped context, so CxBiology's flight rule would derive nothing."
  [kb sandbox op first-h]
  (case op
    "start"   (do (sandbox/open kb sandbox)
                  (v/edit! kb {:add [[(demo-claim 'bird) sandbox]]})
                  (v/handle-of kb (demo-cap 'flying) sandbox))
    "except"  (do (sandbox/open kb sandbox)
                  (v/edit! kb {:add [[(demo-claim 'penguin) sandbox]]})
                  first-h)
    "restore" (do (when-let [h (and (sandbox/live? kb sandbox)
                                    (v/handle-of kb (demo-claim 'penguin) sandbox))]
                    (v/edit! kb {:remove [h]}))
                  first-h)
    "reset"   (do (sandbox/reset! kb sandbox) nil)
    first-h))

(def ^:private demo-ops
  "The `do` values `demo-apply` performs — the steps the page's buttons send.  The route
  refuses any other before it takes the writer."
  #{"start" "except" "restore" "reset"})

(def ^:private demo-first-legal
  "What a legal `first` looks like on `/demo`."
  "the handle step 1 wrote, a whole number — or leave it out before step 1")

;; ---- asserting something new --------------------------------------------
;; The editor amends what is already stored; this is the way in for knowledge that is
;; not.  It writes through `vaelii.core/edit!` like the editor does — one settle for the
;; whole form — and validates through `vaelii.core/check` first, so a refusal is a
;; message beside the line rather than an exception out of `assert`.

(defn- problem-line
  "One check problem, as the reader needs it: which line, what kind, and what it says."
  [{:keys [line type message]}]
  [:li (when line [:span.tag (str "line " (inc line))]) " "
   [:span.tag (name (or type :error))] " " message])

(defn- assert-form
  "The new-sentex form: the sentences, a context, and the known-true switch.  The text is
  read as successive **forms**, so a rule may be laid out over as many lines as it needs.
  `state` carries back what the reader typed and whatever `check` said about it."
  [{:keys [text ctx monotonic? problems sandbox]}]
  [:form.assert-form {:method "post" :action "/assert"
                      :hx-post "/assert" :hx-target "#main" :hx-select "#main"
                      :hx-swap "outerHTML"}
   (when (seq problems)
     [:ul.edit-errors (map problem-line problems)])
   [:label {:for "assert-text"} "Sentences " [:span.muted "(a context line switches context)"]]
   (code-area {:name "text" :id "assert-text" :rows 6 :value text
               :placeholder "(dog Muffet)"})
   [:div.assert-row
    [:label {:for "assert-ctx"} "Context"]
    [:input#assert-ctx {:type "text" :name "ctx" :size 24 :autocomplete "off"
                        :placeholder "CxUniverse" :value ctx}]
    (when (and sandbox (= (str sandbox) (str ctx)))
      [:span.muted.sbx-note "your sandbox — nothing shipped can see it"])
    [:label.check {:for "assert-mono"}
     [:input#assert-mono (cond-> {:type "checkbox" :name "strength" :value "monotonic"}
                           monotonic? (assoc :checked "checked"))]
     " known-true " [:code "{:strength :monotonic}"]]]
   [:p.hint "A fact is ground — " [:code "(dog Muffet)"] ". A rule is a universal — "
    [:code "(implies (dog ?x) (animal ?x))"] ". A sentence may take as many lines as it "
    "needs, and a bare context term on a line of its own moves everything under it into "
    "that context. Every sentence is checked before anything is written, and the whole "
    "form is one settle — one bad sentence stores none of it."]
   [:div.editor-actions [:button.primary {:type "submit"} "Assert"]]])

(defn- assert-seed
  "The form as a term page opens it.  A **context** seeds the context field; anything else
  seeds the first line where its role belongs (a predicate or a type as the functor, an
  individual as an argument).  A starting point, not a submission: `check` says so if the
  incomplete line is saved.  A reified term seeds as the **expression** it denotes
  (`term-text`), so the sentence writes about the term the page is about, not an opaque
  `nat/` constant."
  [env term]
  (let [role (when term (v/term-role term))
        text (when term (term-text env term))]
    (cond
      (nil? term)                            {}
      (= :context role)                      {:ctx text}
      (v/reified-term? term)                 {:text (str "( " text ")")}
      (contains? #{:predicate :type} role)   {:text (str "(" text " )")}
      :else                                  {:text (str "( " text ")")})))

(defn- sandbox-note
  "What a reset did, in the form the assert form shows a message in.  A teardown is
  worth reporting even when it is what was asked for: the number is the only evidence
  the sweep reached the conclusions as well as the premises."
  [{:keys [removed-sentexes removed-justifications]}]
  (when (pos? (or removed-sentexes 0))
    [{:type :reset
      :message (str "sandbox reset — " removed-sentexes
                    (if (= 1 removed-sentexes) " sentex" " sentexes") " and "
                    removed-justifications
                    (if (= 1 removed-justifications) " justification" " justifications")
                    " discarded")}]))

(defn- sandbox-panel
  "Where this session's writing goes, and the one control that takes it back.

  It names the context rather than offering a choice of one: the reader is not picking a
  context, they are being told they have somewhere safe.  The reset is a **write**,
  so it is a POST and origin-checked like the rest, and it is the only irreversible
  control on the page — which is why it says what it would take with it before it does."
  [{:keys [kb sandbox] :as env}]
  (when sandbox
    (let [n (if @(:sandbox-live? env) (count (sandbox/extent kb sandbox)) 0)]
      [:div#sbx-panel.sbx-panel
       [:p [:b "Your sandbox"] " "
        [:span.muted "— a context of your own, below everything shipped. It sees the whole "
         "KB; nothing shipped can see it, so you cannot break anything from here."]]
       [:p.muted [:code (str sandbox)] " · "
        (if (pos? n)
          (list n (if (= 1 n) " sentex" " sentexes")
                [:span.muted " (what you wrote, and what the rules concluded from it)"])
          "empty")]
       [:p.muted "This server keeps at most " (sandbox/max-sandboxes) " sandboxes of up to "
        sandbox/max-sentexes " sentexes each. When a new one needs room, the one least "
        "used lately is cleared, so a sandbox left idle can be cleared."]
       (when (pos? n)
         [:form {:hx-post "/sandbox/reset" :hx-target "#main" :hx-select "#main"
                 :hx-swap "outerHTML"}
          [:button {:type "submit"}
           "Reset — discard all " n]])])))

(defn assert-page
  "The new-sentex page: the form, and — after a save — what it stored."
  ([env] (assert-page env {} nil))
  ([{:keys [kb sandbox] :as env} state result]
   (render env "assert"
           [:h2 "Assert"]
           [:p.muted "Add knowledge the KB does not hold yet. "
            "The " [:a {:href "/levels"} "levels page"] " is for asking; this is for telling."]
           (sandbox-panel env)
           ;; the context field defaults to this session's sandbox, so writing somewhere
           ;; safe is what happens when the reader changes nothing
           (assert-form (cond-> (assoc state :sandbox sandbox)
                          (str/blank? (str (:ctx state))) (assoc :ctx (str sandbox))))
           (when-let [added (seq (flatten (:added result)))]
             (let [ss (keep #(v/sentex kb %) added)]
               (prime-belief! env (map :id ss))
               [:div
                [:h3 "Stored " [:span.muted "(" (count ss) " in one settle)"]]
                (sentex-list env ss)
                (derived-callout env result ss)])))))

;; ---- the reasoning gallery ----------------------------------------------
;; `/demo` argues one thing at length; this is the breadth: every kind of inference the
;; shipped ontology performs, each as a question with a live answer.  Each example **names
;; the sentexes it rests on**, looked up before anything is claimed, so a corpus that
;; lacks them greys the example out.  Each declares what the ontology should answer, which
;; `examples_test` asserts.  Most cards cost no write; those needing individuals write
;; them into the reader's own sandbox, one click at a time.

(defn- example-dependency
  "One sentex an example rests on: the record itself where the KB holds it, and plainly
  missing where it does not.  This is the line that makes the card checkable — every
  claim above it is about these handles."
  [env [sentence context h]]
  [:li (if h
         (list (handle-ref env h) " " [:span.muted (str context)])
         (list [:span.muted (render-form env sentence)] " "
               [:span.tag.tag-out "not in this KB"]))])

(def ^:private example-ms
  "How long one card's question may climb before its card says it stopped.  The gallery
  asks every card on a KB of millions of sentexes, where a goal no level answers runs
  the rule chainers to the end of their search."
  10000)

(def ^:private example-retry-ms
  "The longer climb a card that stopped offers on its own button."
  120000)

(defn- verdict-href [id ms]
  (str "/reasoning/verdict?id=" (url-enc id) "&ms=" ms))

(defn- example-verdict-pending
  "A card's verdict before it is asked: the page renders at once and each card asks its
  own question after it, one at a time, so a slow card holds neither the page nor the
  cards below it beyond its own deadline."
  [id]
  [:div.ex-verdict {:hx-get (verdict-href id example-ms) :hx-trigger "load"
                    :hx-sync "#main:queue all"
                    :hx-target "this" :hx-select "unset" :hx-swap "outerHTML"}
   [:p.muted "Asking"]])

(defn- example-verdict
  "What the KB answered, and by what machinery.  `escalate` stops at the first level
  that answers, so the level names the mechanism: 3 is context inheritance, 5 a cached
  closure, 7 the rule chainers.  A closure answer carries **no handle** — the engine
  never materialized a sentex for it — and the card says so rather than leaving a gap
  where a proof would be."
  [env {:keys [id expect]}
   {:keys [answered? level level-name handle why refused? problems timeout? max-ms]}]
  (cond
    timeout?
    [:div.ex-verdict
     [:p [:b "No answer within " (duration-text max-ms)]
      [:span.muted " — the climb stopped there, which says nothing about whether a level "
       "above would answer."]]
     (when (< max-ms example-retry-ms)
       [:p [:button {:type "button" :hx-get (verdict-href id example-retry-ms)
                     :hx-target "closest .ex-verdict" :hx-select "unset" :hx-swap "outerHTML"}
            "Give it " (duration-text example-retry-ms)]])]

    (some? refused?)
    [:div.ex-verdict
     (if refused?
       (list [:p [:b "Refused."] " Nothing was stored."]
             [:ul.edit-errors (map problem-line problems)])
       [:p [:b "Accepted"] [:span.muted " — which this example did not expect."]])]

    answered?
    [:div.ex-verdict
     [:p [:b "Answered"] " at level " [:code (str level)]
      [:span.muted " — " (name (or level-name :?)) "."]]
     (if handle
       (list [:details.ex-proof
              [:summary "the rule that reached it"]
              (why-tree env why)]
             [:p.muted [:a {:href (str "/why/" handle)} "the whole proof"] " · "
              [:a {:href (str "/sentex/" handle)} "the record"]])
       [:p.muted "No record: the answer is computed, so there is no sentex to link. "
        "Nothing was materialized to reach it."])]

    :else
    [:div.ex-verdict
     [:p [:b "Not answered"]
      (if (= :no expect)
        [:span.muted " — and that is what the example is about."]
        [:span.muted " — which this example did not expect."])]]))

(defn- example-run-form
  "The button that establishes one example's premises in the reader's sandbox."
  [id label]
  [:form.demo-run {:method "post" :action "/reasoning"
                   :hx-post "/reasoning" :hx-target "#main" :hx-select "#main"
                   :hx-swap "outerHTML"}
   [:input {:type "hidden" :name "id" :value id}]
   [:button {:type "submit" :class "primary"} label]])

(defn- example-card
  "One worked example: what it shows, what it rests on, its premises where it has any,
  and the live verdict."
  [{:keys [kb] :as env} {:keys [id title shows premises goal refuse kind] :as ex}
   result established? available?]
  [:section.ex-card {:id (str "ex-" id)}
   [:h3 title]
   [:p.muted (str/replace shows #"\s+" " ")]
   [:ul.ex-deps (map #(example-dependency env %) (ex/dependencies kb ex))]
   (when (seq premises)
     [:div.ex-premises
      [:p.muted (if established? "Written into your sandbox:" "This one needs individuals:")]
      [:ul.ex-given (for [p premises] [:li (render-form env p)])]])
   [:p.ex-ask
    [:span.muted (if (= :refusal kind) "Try to assert " "Ask ")]
    (render-form env (or goal refuse))]
   (cond
     (not available?)
     [:div.ex-verdict [:p.muted "Not available in this KB — the sentexes above are what "
                       "it would reason from, and they are not stored here."]]
     ;; availability is asked of the KB and the verdict of the sandbox, so they are
     ;; separate answers: a card whose premises are not established yet is available and
     ;; unrun, which is a button rather than a shrug
     (and (seq premises) (not established?))
     (example-run-form id "Run it in my sandbox")
     (nil? result)
     (example-verdict-pending id)
     :else
     (example-verdict env ex result))])

(defn- example-context
  "Where an example's question is asked: the reader's sandbox for one with premises, and
  its own context, else CxWell, for one without."
  [{:keys [sandbox]} {:keys [premises context]}]
  (if (seq premises) sandbox (or context 'CxWell)))

(defn- example-established? [{:keys [kb] :as env} ex]
  (boolean (and @(:sandbox-live? env) (ex/established? kb ex (example-context env ex)))))

(defn- reasoning-verdict
  "One card's verdict, asked under a deadline of `ms`: the fragment that replaces its
  pending verdict, or the button for a card whose premises are not in the sandbox."
  [{:keys [kb] :as env} ex ms]
  (if (and (seq (:premises ex)) (not (example-established? env ex)))
    (example-run-form (:id ex) "Run it in my sandbox")
    (example-verdict env ex (assoc (ex/run kb ex (example-context env ex) {:max-ms ms})
                                   :max-ms ms))))

(defn reasoning-page
  "The gallery.  The page asks nothing itself: each available card asks its question
  after the page has loaded, under `example-ms` (`/reasoning/verdict`).  The ones with
  premises ask the sandbox once the reader has established them, and show a button until
  then."
  [{:keys [kb sandbox] :as env}]
  (let [live?  (boolean @(:sandbox-live? env))
        rows   (for [ex ex/examples]
                 [ex nil (example-established? env ex) (ex/available? kb ex)])]
    (render env "reasoning"
            [:h2 "What this ontology can work out"]
            [:p.muted "Every card is a question put to this KB, asked once the page has "
             "loaded, one card at a time, for up to " (duration-text example-ms)
             " each. Each names the sentexes it reasons from; a card whose sentexes this "
             "KB does not hold says so instead of answering."]
            [:p [:a.action {:href "/demo"} "Watch belief change"]
             [:span.muted " — the one below at length, in three clicks."] " · "
             [:a {:href "/levels"} "Trace a goal through the eight levels"] " · "
             [:a {:href "/network"} "Qualitative constraint networks"]]
            (when (some (comp seq :premises first) rows)
              [:p.legend "The examples that need individuals write them into "
               (if live? (list [:code (str sandbox)] ", ") "a context of this browser session's own, ")
               "which sees what CxWell sees, every shipped context but the opt-in theories, "
               "and which nothing shipped can see into. "
               (when live?
                 (demo-step-form {:op "reset" :label "Discard my sandbox"}))])
            (for [g ex/groups]
              (list [:h2.ex-group g]
                    (for [[ex result est? avail] rows :when (= g (:group ex))]
                      (example-card env ex result est? avail)))))))

(defn reasoning-run
  "Establish one example's premises in the sandbox.  A write, so a POST — and the
  sandbox is opened first, exactly as the demo does: without its `genlCx` edge it
  would see no shipped rule and the example would quietly derive nothing."
  [kb sandbox id]
  (when-let [ex (ex/by-id id)]
    (sandbox/open kb sandbox)
    (ex/establish! kb ex sandbox))
  nil)

;; ---- retracting a selection ---------------------------------------------

(def ^:private sweep-cap
  "How far the consequence preview walks before it stops counting.  The walk is bounded
  because a retraction's blast radius can be the whole derived KB, and a confirmation
  dialogue that takes a second to render is a confirmation dialogue nobody reads."
  200)

(defn- swept-by
  "The stored sentexes that would go **besides** the selection, computed to a fixpoint from
  the justification graph, the criterion the dependency-directed sweep applies: a datum goes
  when it is not a premise in its own right and every justification concluding it has an
  argument that is going.  The walk reads no belief, so a derived sentex stored OUT is
  listed and its badge renders dimmed.  Answers `{:handles [...] :capped? bool}`.  It
  never *under*-states: a datum re-derivable through a witness the sweep finds and this
  walk did not is reported here and survives there."
  [{:keys [kb]} handles]
  (loop [doomed (set handles) frontier (vec handles) extra []]
    (if (or (empty? frontier) (>= (count extra) sweep-cap))
      {:handles extra :capped? (>= (count extra) sweep-cap)}
      (let [h    (peek frontier)
            gone (into []
                       (comp (map :consequence)
                             (distinct)
                             (remove doomed)
                             (remove #(v/premise? kb %))
                             (filter (fn [c]
                                       (every? #(some doomed (v/rests-on %))
                                               (v/supporting-justifications kb c)))))
                       (v/dependent-justifications kb h))]
        (recur (into doomed gone) (into (pop frontier) gone) (into extra gone))))))

(defn- retraction-plan
  "Which of the selected `handles` a retraction takes and which it leaves stored, with what
  the sweep takes besides.  A selected handle goes only when every justification
  concluding it rests on something going; one derived from what stays is left stored and
  believed, premise mark or not.  The going set starts as the whole selection and loses
  each handle with a justification none of whose supports go (`swept-by` over the rest).
  Answers `{:going [h] :staying [h] :swept [h] :capped? bool}`, in the selection's order;
  `:swept` and `:capped?` are `swept-by`'s for `:going`."
  [{:keys [kb] :as env} handles]
  (loop [going (vec handles)]
    (let [{swept :handles capped? :capped?} (swept-by env going)
          doomed (into (set going) swept)
          going' (filterv (fn [h] (every? #(some doomed (v/rests-on %))
                                          (v/supporting-justifications kb h)))
                          going)]
      (if (= (count going') (count going))
        {:going going :staying (filterv (complement (set going)) handles)
         :swept swept :capped? capped?}
        (recur going')))))

(defn- stays-because
  "Why a selected handle a retraction leaves stored stays, with the link to what it
  rests on.  `premise?` is whether it was asserted before the retraction: an asserted
  sentex that is also derived loses its premise mark and stays on its derivation; a
  derived one carries no mark to lose.  `done?` words it for a write that has run
  rather than for the confirmation before it."
  [handle premise? done?]
  (list [:span.muted
         (cond
           (and premise? done?) " — no longer asserted: it stays, believed on its derivation"
           premise?             " — asserted, and derived as well: it stops being asserted and stays, believed on its derivation"
           :else                " — derived, not asserted: there is no assertion to retract, and it goes when what it rests on goes")]
        " " [:a.muted {:href (str "/why/" handle)} "why"]))

(defn- stayed-rows
  "The selected sentexes a write left stored, each with why (`stays-because`), under
  `heading`.  `premises` is the set of them that were asserted before the write."
  [env stayed premises heading]
  (when (seq stayed)
    (list [:h4 heading]
          [:ul.retract-list
           (for [s stayed]
             [:li (sentex-ref env s) in-cx (term-link env (:context s))
              (stays-because (:id s) (premises (:id s)) true)])])))

(defn- retract-panel
  "The confirmation the Retract button opens: which selected sentexes go and which stay
  (`retraction-plan`), what the sweep would take with them, and the button that does it.
  A GET renders this and writes nothing; only its POST retracts.  A staying sentex is named
  with the reason and its `/why` link.  The button counts the sentexes that go and the
  asserted ones that lose their premise mark; a selection where nothing would change gets
  no button."
  [{:keys [kb] :as env} handles]
  (let [ss (keep #(v/sentex kb %) handles)]
    (if (empty? ss)
      [:span]
      (let [{:keys [going staying swept capped?]} (retraction-plan env (map :id ss))
            by-h     (into {} (map (juxt :id identity)) ss)
            premises (set (filter #(v/premise? kb %) staying))
            acts     (+ (count going) (count premises))
            swept-ss (keep #(v/sentex kb %) swept)
            row      (fn [s] (list (sentex-ref env s) in-cx (term-link env (:context s))))]
        (prime-belief! env (concat (map :id ss) swept))
        [:div.editor
         [:h3 "Retract " (count ss) " sentex" (when (not= 1 (count ss)) "es")]
         [:p.hint "Retraction is " [:b "dependency-directed"] ": it removes premise "
          "support and then sweeps every datum that has no witness left, so it can take "
          "conclusions the selection does not name. Anything still derivable another way "
          "stays."]
         (when (seq going)
           (list [:h4 (if (seq staying) "Goes" "Selected")]
                 [:ul.retract-list (for [h going] [:li (row (by-h h))])]))
         (when (seq staying)
           (list [:h4 "Stays"]
                 [:ul.retract-list
                  (for [h staying] [:li (row (by-h h)) (stays-because h (premises h) false)])]))
         (cond
           (seq swept-ss)
           [:div
            [:h4 "And these lose their last witness "
             [:span.muted "(" (count swept-ss) (when capped? "+") " derived)"]]
            [:ul.retract-list (for [s swept-ss] [:li (row s)])]
            (when capped?
              [:p.muted "The walk stops at " sweep-cap " — there may be more behind it."])]

           (seq going) [:p.muted "Nothing else rests on them."])
         (if (pos? acts)
           [:form {:hx-post "/retract" :hx-target "#editor" :hx-select "unset"
                   :hx-swap "innerHTML"}
            [:input {:type "hidden" :name "handles" :value (str/join "," (map :id ss))}]
            [:div.editor-actions
             [:button.danger {:type "submit"} "Retract " acts]
             [:button#sx-cancel {:type "button"} "Cancel"]]]
           (list [:p.muted "Retracting this selection changes nothing: it is derived, and "
                  "stays for as long as what it rests on does."]
                 [:div.editor-actions [:button#sx-cancel.primary {:type "button"} "Close"]]))]))))

;; ---- forward chaining, on demand ----------------------------------------

(defn- chain-note
  "What a forward-chaining run did, said plainly — and where to look at what it
  dropped."
  [{:keys [derived truncated?]}]
  [:p.chain-note "Forward chaining derived " [:b derived]
   (if (= 1 derived) " conclusion" " conclusions")
   (when truncated? " — and hit the depth bound, so the run was truncated")
   "."])

(defn- chain-job
  "Forward chaining as a job, and return its id.  `forward-chain` reports
  `{:derived :pending}` about four times a second, and a cancel lands at a report.  The
  run uses `:on-stop :keep`, so a cancel or the cap leaves a settled *prefix* of the run.
  `cap` bounds it (`:max-derivations`).  `in-monitor` runs the work inside this process's
  write monitor, on the job's own thread.  **A daemon's fixpoint reports nothing**: an
  `:on-progress` function does not cross an EDN wire (`serve.clj`), so a remote target
  gets the bound and no callback."
  ([kb label cap in-monitor] (chain-job kb label cap in-monitor "/stats"))
  ([kb label cap in-monitor result-url]
   (let [note   (fn [pending] (if pending
                                (format "%,d on the agenda" (long pending))
                                "forward chaining to a fixpoint"))
         local? (some? (v/local-kb kb))]
     (jobs/submit
      {:label      (str "Chain " label)
       :kind       :chain
       :writes     kb
       :result-url result-url
       :progress   {:phase :chaining :done 0
                    :note (if local? (note nil) "on the daemon, which reports no progress")}}
      (fn [progress!]
        (in-monitor
         (fn []
           (v/forward-chain
            kb (cond-> {:on-stop :keep}
                 cap    (assoc :max-derivations cap)
                 local? (assoc :on-progress
                               (fn [{:keys [derived pending]}]
                                 (progress! {:phase :chaining :total nil
                                             :done (or derived 0)
                                             :note (note pending)}))))))))))))

;; ---- the chaining funnel -------------------------------------------------
;; `/stats` says how many conclusions a run derived; this says *which rules* derived,
;; which refused, and which never fired.  It reads `chain-report` (placed / refused /
;; silent, off the ledger and the justification graph) and folds in the `violations`
;; carrying each rule's handle, with no per-run counters (docs/exceptions.md).

(def ^:private funnel-render-cap
  "How many rules the funnel shows at a time; the rest follows on scroll (`/funnel/rows`)."
  200)

(defn- funnel-status-tag
  [status]
  (let [cls (case status :fires "tag-in" :blocked "tag-superseded" :silent "tag-out" "tag-out")]
    [:span {:class (str "tag " cls)} (name status)]))

(defn- funnel-run-form
  "Run forward chaining to a fixpoint and land back here, so the funnel fills in front of
  the reader.  The same job `/chain` runs — bounded by `max-derivations`, watchable and
  cancellable on `/jobs` — only its result page is this one rather than `/stats`."
  [_env]
  [:form.chain-form {:method "post" :action "/funnel"
                     :hx-post "/funnel" :hx-target "#main" :hx-select "#main" :hx-swap "outerHTML"}
   [:span "Run forward chaining "]
   [:input {:type "number" :name "max-derivations" :min 1 :placeholder "to a fixpoint"
            :title "an optional derivation bound"}]
   [:button {:type "submit"} "run"]])

(defn- funnel-why
  "Why a rule placed nothing — the reasons its refusals cluster on, which is what separates
  'never completed an antecedent set' from 'completes them and every one is blocked'."
  [{:keys [status refused refusals void]}]
  (case status
    :fires  [:span.tag.tag-in "fires"]
    :silent [:span.muted "no antecedent set completed"]
    :blocked (let [blocked (filter #(= :blocked (:state %)) refusals)
                   freed   (- (count refusals) (count blocked))
                   by      (frequencies (keep #(or (:reason %) :blocked) blocked))]
               [:span
                ;; the count, then the reason's own name: two reasons a rule refused
                ;; equally often tie on the count alone, and the tie would fall to the
                ;; `frequencies` map's iteration order — hash order, or the refusal
                ;; ledger's arrival order below eight entries
                (interpose ", "
                           (for [[reason n] (sort-by (juxt (comp - val) (comp print-key key)) by)]
                             [:span (commas n) " " [:span.tag (name reason)]]))
                (when (= :overflow refused) [:span.tag.tag-superseded " overflow"])
                (when (pos? freed) [:span.muted (str " (" freed " since freed)")])
                (when (pos? (long (or void 0))) [:span " " (commas void) " " [:span.tag "void"]])
                (when (and (empty? by) (not= :overflow refused) (zero? freed) (zero? (long (or void 0))))
                  [:span.muted "blocked"])])
    [:span.muted "—"]))

(defn- funnel-violation
  [env {:keys [violation sentence context]}]
  [:div [:span.tag.tag-defeated (name violation)]
   (when sentence [:span " " (render-form env sentence)])
   (when context [:span.muted in-cx (term-link env context)])])

(defn- funnel-refused-rank
  [{:keys [refused]}]
  (if (= :overflow refused) Long/MAX_VALUE (long (or refused 0))))

(defn- funnel-row
  "One rule as a card, not a table row: the sentence on its own full-width line (so it
  wraps at spaces rather than being crushed into a column), then a compact metrics line.
  The reason is shown for a `:blocked` rule (its cluster) or a `:silent` one (the single
  reason it has); a `:fires` status pill already says everything its reason would repeat."
  [env {:keys [rule placed refused] :as row} viols]
  [:div.funnel-row
   [:div.funnel-sx (handle-ref env rule) " " (funnel-status-tag (:status row))]
   [:div.funnel-meta
    [:span.funnel-metric [:span.muted "placed "]
     (if (pos? (long placed)) (commas placed) [:span.muted "—"])]
    [:span.funnel-metric [:span.muted "refused "]
     (cond (= :overflow refused)        [:span.tag.tag-superseded "overflow"]
           (pos? (long (or refused 0))) (commas refused)
           :else                        [:span.muted "—"])]
    (when (contains? #{:blocked :silent} (:status row))
      [:span.funnel-metric.funnel-why (funnel-why row)])]
   (when (seq viols)
     [:div.funnel-viols (for [v viols] (funnel-violation env v))])])

(defn- funnel-ranked
  "Every forward rule's `chain-report` row, ranked by what is wrong: no-placement rules
  first, by refusals descending, firing rules last."
  [rows]
  ;; **The last key is what the rule says, never its handle.**  Every silent rule placed
  ;; and refused nothing, so the first two keys tie across the silent block, and with
  ;; `funnel-render-cap` rules per page the tie decides *which rules a reader sees first*.
  ;; A handle would answer "which rules were written first".  Keyed once per row, printed
  ;; with the print bounds released.  The same order on every request lets `/funnel/rows`
  ;; continue at an offset.
  (binding [*print-length* nil *print-level* nil]
    (->> rows
         (mapv (fn [r] [[(if (pos? (long (:placed r))) 1 0)
                         (- (funnel-refused-rank r))
                         (pr-str (:sentence r))]
                        r]))
         (sort-by first)
         (mapv second))))

(defn- funnel-list
  "One page of funnel cards from `offset` in `ranked`, and the sentinel that fetches the
  next when there is one."
  [{:keys [kb] :as env} ranked offset]
  (let [shown (into [] (comp (drop offset) (take funnel-render-cap)) ranked)
        viols (group-by :rule (v/violations kb))
        nxt   (+ offset funnel-render-cap)]
    (prime-belief! env (map :rule shown))
    (list (for [row shown] (funnel-row env row (get viols (:rule row))))
          (when (> (count ranked) nxt)
            (more-rows (str "/funnel/rows?offset=" nxt) "show more" {:div? true})))))

(defn funnel-rows-page
  "One more page of the funnel — what its continuation sentinel fetches."
  [{:keys [kb] :as env} offset]
  (frag (funnel-list env (funnel-ranked (v/chain-report kb)) offset)))

(defn funnel-page
  "Every forward rule and what chaining did with it — placed, refused (and why), or silent
  — ranked by what is wrong (`funnel-ranked`), one page of cards at a time.  A run form on
  `32`'s job registry populates it live."
  [{:keys [kb] :as env}]
  (let [rows   (v/chain-report kb)
        ranked (funnel-ranked rows)
        freq   (frequencies (map :status rows))]
    (render env "funnel"
            [:h2 "The chaining funnel"]
            [:p.muted "Every forward rule in the KB and what it does when chaining runs — "
             "what it placed, what it refused and why, or whether it never fired at all. "
             "The question " [:a {:href "/stats"} "the headline counts"] " cannot answer: "
             [:i "which"] " of the rules derive anything."]
            (funnel-run-form env)
            [:div.stats-grid
             [:div.stat [:span.stat-n (commas (count rows))] [:span.stat-l "forward rules"]]
             [:div.stat [:span.stat-n (commas (:fires freq 0))] [:span.stat-l "fire"]]
             [:div {:class (str "stat" (when (pos? (:blocked freq 0)) " stat-warn"))}
              [:span.stat-n (commas (:blocked freq 0))] [:span.stat-l "blocked"]]
             [:div.stat [:span.stat-n (commas (:silent freq 0))] [:span.stat-l "silent"]]]
            (if (empty? rows)
              [:p.muted "No forward rules in this KB. Forward chaining has nothing to run."]
              (list
               [:div.funnel-list (funnel-list env ranked 0)]
               (when (> (count ranked) funnel-render-cap)
                 [:p.legend (commas (count ranked)) " rules held, no-placement first; "
                  funnel-render-cap " at a time, the rest on scroll."])))
            [:p.legend "A " [:b "silent"] " rule never completed an antecedent set — nothing "
             "it needs is believed. A " [:b "blocked"] " one completes firings and cannot "
             "place them: an " [:span.tag "exception"] " holds, a " [:span.tag "naf"] " literal "
             "is contradicted, a " [:span.tag "post-join"] " literal had no answer, or an "
             "antecedent is " [:span.tag "hidden"] " in the placement context. A reason "
             "shown still holds against current belief — retract what blocks it and the "
             "rule is owed its conclusion."])))

;; ---- sentex editing (a row's [edit] → textarea → one settle) ------------
;; A row opens the editor on its own handle, and the panel takes a set of them, so a
;; batch arrives by handing `/edit` a comma-separated list.  Save is `vaelii.core/edit!`
;; reached through the access facade, so it retracts the changed/removed sentexes and
;; asserts the new lines in **one settle**, in-process or against a live daemon alike.

(defn- ->long [s] (try (Long/parseLong (str s)) (catch Exception _ nil)))

(defn ->form
  "Read a `?q=` / `?ctx=` query param as EDN, or nil when it is not readable.  Every route
  that takes a term or a goal parses through this, since a URL may carry `(`.  It catches
  `Throwable`, not `Exception`, because a deeply nested form overflows the reader's stack
  with a `StackOverflowError`, which would escape as a 500."
  [s]
  (try (edn/read-string (str s)) (catch Throwable _ nil)))

(defn- skip-to-form!
  "Advance `rdr` past whitespace and `;` comments, and answer the 0-based line the next
  form opens on — nil at end of input.  `edn/read` skips that same run itself, but it
  answers a value and not where the value started, and a problem has to name the line
  there is to go and fix."
  [^java.io.PushbackReader rdr ^java.io.LineNumberReader lnr]
  (loop []
    (let [c (.read rdr)]
      (cond
        (neg? c)                   nil
        (Character/isWhitespace c) (recur)
        (= (char c) \;)            (do (loop []
                                         (let [d (.read rdr)]
                                           (when (and (not (neg? d)) (not= (char d) \newline))
                                             (recur))))
                                       (recur))
        :else                      (do (.unread rdr c) (.getLineNumber lnr))))))

(defn- read-forms
  "Read a textarea's content as successive EDN **forms**, so one sentence may span lines.
  Answers `{:forms [{:pos i :line n :form v} …] :problem p|nil}`: `pos` is the form's
  position in the text, which a save pairs with its handle, and `line` is the 0-based line
  it opens on.  Reading stops at the first form that does not read, and that is the only
  problem reported, since everything after an unbalanced form is inside it."
  [text]
  (let [lnr (java.io.LineNumberReader. (java.io.StringReader. (str text)))
        rdr (java.io.PushbackReader. lnr)
        eof (Object.)]
    (loop [forms []]
      (if-let [line (skip-to-form! rdr lnr)]
        ;; `Throwable` for `->form`'s reason: a nested-enough form overflows the reader's
        ;; stack, and that form is a problem to report rather than a 500
        (let [v (try {:ok (edn/read {:eof eof} rdr)}
                     (catch Throwable e {:bad (.getMessage e)}))]
          (cond
            (:bad v)                 {:forms forms
                                      :problem {:line line :type :unreadable
                                                :message (str "does not read as EDN: "
                                                              (:bad v))}}
            (identical? eof (:ok v)) {:forms forms :problem nil}
            :else                    (recur (conj forms {:pos  (count forms)
                                                         :line line
                                                         :form (:ok v)}))))
        {:forms forms :problem nil}))))

;; The editable line format is `vaelii.host.lines`', not a second copy of it: a save is
;; diffed against the seeded lines by content, so a byte of drift between the two
;; spellings turns every unchanged line into a retract plus an assert of the same fact.

(defn- read-entries
  "Read an editor's text: **contexts and sentences interleaved**.  A bare symbol on a line
  of its own sets the context every sentence under it is in, a map sets the options they
  carry (`{:strength :monotonic}`, `{}` for the default), and every list is a sentence in
  whatever is current.  Answers

    {:entries  [{:pos i :line n :entry [sentence context opts?] :key [sentence context]} …]
     :problems [{:line n :type … :message …} …]}

  `pos` counts **sentences**, which a save pairs with a handle; `line` is the line the
  sentence opens on.  `start` seeds the context and options."
  ([text] (read-entries text nil))
  ([text {:keys [ctx opts]}]
   (let [{:keys [forms problem]} (read-forms text)]
     (loop [[{:keys [line form] :as f} & more] forms
            cx ctx, op opts, entries [], problems []]
       (cond
         (nil? f)       {:entries  entries
                         :problems (cond-> problems problem (conj problem))}
         (symbol? form) (recur more form op entries problems)
         (map? form)    (recur more cx (not-empty form) entries problems)
         (seq? form)    (if (nil? cx)
                          (recur more cx op entries
                                 (conj problems
                                       {:line line :type :shape
                                        :message (str "no context yet — write a context "
                                                      "term on a line above this sentence")}))
                          (recur more cx op
                                 (conj entries {:pos   (count entries)
                                                :line  line
                                                :key   [form cx]
                                                :entry (if op [form cx op] [form cx])})
                                 problems))
         :else          (recur more cx op entries
                               (conj problems
                                     {:line line :type :shape
                                      :message (str "expected a sentence, a context term "
                                                    "or an options map — got "
                                                    (pr-str form))})))))))

(defn- pretty-layout
  "`[text multi-line?]` for `form` starting at column `col`: `layout`'s alignment as
  text.  An implication and a connective over two or more arguments span lines, and any
  other compound spans lines when one of its arguments does."
  [form col]
  (if-not (and (sequential? form) (seq form))
    [(print-key form) false]
    (let [f     (first form)
          k     (+ col 2 (count (print-key f)))
          args  (mapv #(pretty-layout % k) (rest form))
          multi (boolean (or (and (= 'implies f) (= 3 (count form)))
                             (and (contains? laid-out-connectives f) (> (count form) 2))
                             (some second args)))]
      [(if multi
         (str "(" (print-key f) " "
              (str/join (str "\n" (apply str (repeat k \space))) (map first args)) ")")
         (print-key form))
       multi])))

(defn- pretty-sentence
  "`form` as **text**, laid out the way a row lays it out (`layout`): the editor's copy
  of the same alignment, so a rule reads in the field the way it reads on the page it
  was opened from.  `col` is the column the form starts at.

  The whitespace is not read back: `read-entries` reads EDN **forms** and the save diffs
  by content, so the layout is for the reader and the sentence reaching the KB is the one
  that was there."
  [form col]
  (first (pretty-layout form col)))

(defn- seed-text
  "The editor's text for a set of sentexes, in the order the handles name them: a context on
  its own line, then its sentences, and an options map where the strength changes, with a
  blank line before each new context group.  Print vars are bound off because the text is
  read back and diffed by content: an ambient `*print-length*` would elide a long sentence
  into legal EDN that no longer matches its sentex, and an untouched save would retract the
  real fact and store the mutilated one."
  [kb handles]
  (binding [*print-length* nil *print-level* nil *print-meta* false]
    (->> (keep #(v/sentex kb %) handles)
         (reduce (fn [{:keys [cx op lines]} sx]
                   (let [c (:context sx)
                         o (when (= :monotonic (:strength sx)) {:strength :monotonic})]
                     {:cx c :op o
                      :lines (cond-> lines
                               (and (not= c cx) (seq lines)) (conj "")
                               (not= c cx)                   (conj (pr-str c))
                               (not= o op)                   (conj (pr-str (or o {})))
                               :always (conj (pretty-sentence
                                              (lines/wrapped-sentence sx) 0)))}))
                 {:cx nil :op nil :lines []})
         :lines
         (str/join "\n"))))

(defn- removal-rows
  "What `removed/note!` keeps of each still-stored sentex `handles` names, by handle: its
  sentence as the editor prints it, its context and its strength.  Read **before** the
  write that removes them, since afterwards there is nothing left to read."
  [kb handles]
  (binding [*print-length* nil *print-level* nil *print-meta* false]
    (into {} (for [h handles :let [s (v/sentex kb h)] :when s]
               [h {:sentence (pretty-sentence (lines/wrapped-sentence s) 0)
                   :context  (pr-str (:context s))
                   :strength (:strength s)}]))))

(defn- edit-panel
  "The editor form for a set of handles: a `code-area` seeded with the still-present ones
  as contexts and sentences interleaved (`seed-text`), above Save / Retract / Cancel, and
  the lookahead panel that says what the save would do.  `problems` and `text` are supplied
  when re-rendering after a save that did not go through.  The lookahead posts to
  `/edit/preview` on a pause in the typing (`v/preview` is a read).  `/retract` GET only
  **previews** the teardown; its POST is the write."
  [{:keys [kb]} handles & [{:keys [text problems]}]]
  (let [live (into [] (filter #(v/sentex kb %)) handles)
        csv  (str/join "," live)]
    (if (empty? live)
      [:span]
      [:div.editor
       [:h3 "Edit " (count live) " sentex" (when (not= 1 (count live)) "es")]
       (when (seq problems) [:ul.edit-errors (map problem-line problems)])
       [:form.edit-form {:hx-post "/edit" :hx-target "#editor" :hx-select "unset"
                         :hx-swap "innerHTML"}
        [:input {:type "hidden" :name "handles" :value csv}]
        (code-area {:name "text" :rows (max 5 (+ 2 (count live)))
                    :value (or text (seed-text kb live))})
        [:p.hint "A context on a line of its own, then the sentences in it — each may "
         "take as many lines as it needs. A map (" [:code "{:strength :monotonic}"]
         ") sets what the sentences under it carry. Save retracts what you changed and "
         "asserts the new sentences in one settle; an unchanged sentence touches "
         "nothing. Editing a rule drops any " [:code "exceptWhen"] " guard it carries."]
        [:div.editor-actions
         [:button.primary {:type "submit"} "Save"]
         [:button#sx-retract {:type "button"
                              :hx-get (str "/retract?handles=" csv)
                              :hx-target "#editor" :hx-select "unset" :hx-swap "innerHTML"}
          "Retract"]
         [:button#sx-cancel {:type "button"} "Cancel"]]
        ;; the lookahead: what this save would do, recomputed on a pause rather than on
        ;; a keystroke, and posting the very fields the Save button would post
        [:div.ed-preview {:hx-post "/edit/preview"
                          :hx-trigger "keyup changed delay:600ms from:closest form"
                          :hx-include "closest form" :hx-target "this"
                          :hx-select "unset" :hx-swap "innerHTML" :aria-live "polite"}]]])))

(defn- oob
  "Mark a rendered element as an out-of-band swap addressing every row for `handle`.
  Rows are addressed by their `data-h` attribute rather than by an id because one
  handle can appear in more than one index group on a term page, and htmx's selector
  form of `hx-swap-oob` swaps **all** the matches — so every copy of a row moves."
  [style handle element]
  (assoc-in element [1 :hx-swap-oob] (str style ":[data-h='" handle "']")))

(defn- saved-rows
  "The out-of-band swaps a successful save sends in place of reloading the page: each
  retracted handle's row is replaced by the row its form became, or deleted when the form
  was deleted.  A form and its handle are paired **by position**, since the textarea is
  seeded one form per named handle; a form with no handle, or a handle with no form, is
  unpaired and shows in the result panel.  `went` is the removals the save took out of the
  store, and only those are swapped out; a removal still stored (derived) keeps its row.
  `restyled` are the handles whose premise mark the save took: their row is re-rendered,
  since the badge now reads derived."
  [{:keys [kb] :as env} went restyled by-pos]
  (concat
   (for [{:keys [h pos]} went
         :let [replacement (some->> (get by-pos pos) (v/sentex kb))]]
     (if replacement
       (oob "outerHTML" h (sentex-row env replacement))
       (oob "delete" h [:li {:data-h h}])))
   (for [h restyled :let [s (v/sentex kb h)] :when s]
     (oob "outerHTML" h (sentex-row env s)))))

(defn- save-result
  "What lands in the editor panel after a save: the tally, the sentexes that were added
  without replacing a row (a line the reader appended has no row to swap, so this is
  where it becomes visible and linkable), the named sentexes the save left stored with
  why each stays (`stayed-rows`), and a Close button — `#sx-cancel`, which vaelii.js
  already wires to close the editor.  `n-removed` counts the named handles gone from the
  store after the settle."
  [env unpaired stayed premises n-added n-removed]
  [:div.editor
   [:h3 "Saved"]
   [:p.muted n-added " asserted · " n-removed " retracted · one settle."]
   ;; plain rows, not `sentex-row`: these sit in the editor panel rather than in a
   ;; listing, so they carry no [edit] of their own
   (when (seq unpaired)
     [:ul (for [s unpaired]
            [:li (sentex-ref env s) in-cx (term-link env (:context s))])])
   (stayed-rows env stayed premises "Still stored")
   [:div.editor-actions [:button#sx-cancel.primary {:type "button"} "Close"]]])

(defn- batch-problems
  "What `vaelii.core/check` says of the batch a save is about to apply, rewritten in
  the reader's terms: an `:add` problem carries the **textarea line** its entry came
  from rather than the batch index, since the line is what there is to go back and fix.

  This is why the editor never surfaces an exception: `check` runs `assert`'s own chain
  for its answer and writes nothing, so a save that would be refused is refused here,
  before `edit` is called at all."
  [kb batch additions]
  (for [p (v/check-edit kb batch)]
    (cond-> (select-keys p [:type :message])
      (= :add (:in p)) (assoc :line (:line (nth additions (:index p) nil))))))

(defn- handle-problems
  "`check-edit`'s problems for the named handles as a removal — `:unknown-handle` for each
  that holds no sentex — in the shape `problem-line` renders."
  [kb handles]
  (vec (for [p (v/check-edit kb {:remove (vec handles)})]
         (select-keys p [:type :message]))))

(defn- not-written
  "The editor panel for a write refused before it started: `title`, the problems, and the
  statement that nothing was written."
  [title problems]
  (frag [:div.editor
         [:h3 title]
         [:ul.edit-errors (map problem-line problems)]
         [:p.muted "Nothing was written."]
         [:div.editor-actions [:button#sx-cancel.primary {:type "button"} "Close"]]]))

(defn- edit-post
  "Apply a save: diff the edited **sentences** against the named handles by content, check
  the batch that diff produces, then `edit`: retract the handles whose sentence changed or
  was deleted, assert the sentences that are new; an unchanged one touches nothing.  The
  text is read by `read-entries`.

  The answer **re-renders what changed**: the rows of the retracted handles are swapped out
  of band, the selection chrome is corrected the same way, and the editor panel reports the
  save.  A line that does not parse, or a batch `check` refuses, writes nothing and comes
  back as a message beside the line with the text intact.  A changed derived handle is
  still stored, counts as nothing retracted, keeps its row and is listed with why it
  stays.  A named handle that holds no sentex is `check-edit`'s `:unknown-handle`, and
  nothing is written."
  [{:keys [kb] :as env} handles text]
  (let [{parsed :entries unread :problems} (read-entries text)
        stale (handle-problems kb handles)]
    (cond
      (seq stale)
      (not-written "Not saved" stale)

      (seq unread)
      (frag (edit-panel env handles {:text text :problems unread}))

      :else
      (let [orig      (vec (for [[i h] (map-indexed vector handles)
                                 :let  [s (v/sentex kb h)] :when s]
                             {:h h :pos i :key [(lines/wrapped-sentence s) (:context s)]}))
            orig-keys (set (map :key orig))
            new-keys  (set (map :key parsed))
            removals  (vec (remove #(new-keys (:key %)) orig))
            additions (vec (remove #(orig-keys (:key %)) parsed))
            batch     {:add (mapv :entry additions) :remove (mapv :h removals)}
            problems  (vec (batch-problems kb batch additions))]
        (if (seq problems)
          (frag (edit-panel env handles {:text text :problems problems}))
          (let [premises  (set (filter #(v/premise? kb %) (map :h removals)))
                rows      (removal-rows kb (map :h removals))
                {:keys [added]} (v/edit! kb batch)
                ;; position -> the handle the form became, for the positional pairing.
                ;; An entry is `assert`-shaped, so a form concluding a conjunction became
                ;; a *vector* of handles — no single row replaces the old one, so it
                ;; stays unpaired and surfaces in the result panel like an appended form
                by-pos    (into {} (map-indexed (fn [k a]
                                                  (let [h (nth added k nil)]
                                                    [(:pos a) (when-not (vector? h) h)])))
                                additions)
                ;; what the save took out of the store, read after the settle: a removal
                ;; that is derived stays, and the form over it pairs with nothing
                {went true kept false} (group-by #(nil? (v/sentex kb (:h %))) removals)
                _         (removed/note! (removed-owner kb) :edit (keep (comp rows :h) went))
                stayed    (into [] (keep #(v/sentex kb (:h %))) kept)
                stored    (flatten added)
                paired    (set (keep #(get by-pos (:pos %)) went))
                unpaired  (into [] (comp (remove paired) (keep #(v/sentex kb %))) stored)]
            (prime-belief! env (concat stored (map :id unpaired) (map :id stayed)))
            (frag (list (save-result env unpaired stayed premises (count stored) (count went))
                        (saved-rows env went (filter premises (map :id stayed))
                                    by-pos)))))))))

(defn edit-preview-post
  "What this save would do, without doing it: the same diff `edit-post` computes, read
  through `v/preview`, so it can run on a pause in the typing.  A form that does not read
  is reported here too, and a named handle that holds no sentex is reported as the save
  would refuse it.  The heading counts a changed handle as retracted only when
  `retraction-plan` says it goes; the plan reads the KB before the save's own adds."
  [{:keys [kb] :as env} handles text]
  (frag
   (let [local   (v/local-kb kb)
         {parsed :entries unread :problems} (read-entries text)
         stale   (when local (handle-problems kb handles))]
     (cond
       (nil? local) [:p.muted "A preview runs inference, so it needs the KB in this process."]
       (seq stale)  [:ul.edit-errors (map problem-line stale)]
       (seq unread) [:ul.edit-errors (map problem-line unread)]
       :else
       (let [orig      (vec (for [h handles :let [s (v/sentex kb h)] :when s]
                              {:h h :key [(lines/wrapped-sentence s) (:context s)]}))
             orig-keys (set (map :key orig))
             new-keys  (set (map :key parsed))
             removals  (mapv :h (remove #(new-keys (:key %)) orig))
             additions (mapv :entry (remove #(orig-keys (:key %)) parsed))]
         (if (and (empty? removals) (empty? additions))
           [:p.muted "Nothing has changed yet."]
           (let [staying (:staying (retraction-plan env removals))]
             (consequences env
                           (str "This save: " (count additions) " asserted · "
                                (- (count removals) (count staying)) " retracted"
                                (when (seq staying)
                                  (str " · " (count staying)
                                       (if (= 1 (count staying)) " stays" " stay")
                                       ", derived from what the save keeps")))
                           {:add additions :remove removals}))))))))

(defn completions-page
  "The terms a prefix could become, as the list the editor drops under the caret: a
  `v/find-terms` **prefix** match, so a keystroke costs the size of the vocabulary, each
  hit carrying its role colour.  A blank prefix, and one past `complete-q-cap`, answer
  nothing, since the route is reachable per keystroke and through the daemon."
  [{:keys [kb] :as env} q]
  (frag
   (let [q (str q)]
     (when (and (not (str/blank? q)) (<= (count q) complete-q-cap))
       (for [t (v/find-terms kb q {:match :prefix :case-sensitive? false
                                   :limit complete-cap})]
         [:li {:role "option" :data-t (str t) :class (str "sx " (term-class env t))}
          (str t)])))))

;; ---- the assert / retract / chain writes --------------------------------
;; Each goes through `vaelii.core/edit!` (or `forward-chain`) via the access facade, so
;; a browser attached to a daemon writes through the daemon's single-writer lock, and
;; every one of them is one settle.

(defn- assert-lines
  "Read the new-sentex textarea the editor panel's way: contexts and sentences
  interleaved (`read-entries`).  The form's **context field** and its known-true switch
  seed the first sentence, so a box holding nothing but sentences asserts them all where
  the field says; a context written in the box takes over from that line down."
  [text ctx opts]
  (read-entries text {:ctx ctx :opts opts}))

(defn assert-post
  "Assert what the new-sentex form holds: read the lines, check them all against the KB,
  and only when every one is admissible apply them in one `edit`.  Nothing partial is
  written.  A form addressed to the session's sandbox before it exists opens it first, once
  the lines have read cleanly and before they are checked, since the checks are
  context-scoped and a sandbox with no `genlCx` edge sees none of the shipped vocabulary.
  When the check then refuses the form, the edge is taken out again (`sandbox/reset!` over
  the empty extent).  A form past `sandbox/max-sentexes` is refused `:over-ceiling` before
  the sandbox is opened."
  [{:keys [kb sandbox] :as env} {:keys [text ctx monotonic?] :as state}]
  (let [ctx-sym (->form ctx)
        opts    (when monotonic? {:strength :monotonic})
        {:keys [entries problems]} (assert-lines text ctx-sym opts)
        ctx-problem (when-not (symbol? ctx-sym)
                      [{:type :shape
                        :message (str "the context must be a bare symbol, got "
                                      (if (str/blank? (str ctx)) "nothing" (pr-str ctx)))}])
        batch    {:add (mapv :entry entries)}
        into-sbx (when sandbox (count (filter #(= sandbox (second (:entry %))) entries)))
        held     (when (and into-sbx (pos? into-sbx))
                   (+ (v/count-in-context kb sandbox) into-sbx))
        cap-problem (when (and held (> held sandbox/max-sentexes))
                      [{:type :over-ceiling :option :sandbox-sentexes :requested held
                        :ceiling sandbox/max-sentexes
                        :message (str "these lines would take your sandbox to " held
                                      " sentexes, past its ceiling of " sandbox/max-sentexes
                                      " — reset it, or write fewer")}])
        readable? (and (seq entries) (empty? problems) (not ctx-problem) (not cap-problem))
        opening? (and readable? sandbox (= ctx-sym sandbox) (not (sandbox/live? kb sandbox)))
        _        (when opening? (sandbox/open kb sandbox))
        checked  (when readable?
                   (vec (for [p (v/check-edit kb batch)]
                          (cond-> (select-keys p [:type :message])
                            (= :add (:in p)) (assoc :line (:line (nth entries (:index p) nil)))))))
        _        (when (and opening? (seq checked)) (sandbox/reset! kb sandbox))
        all      (vec (concat ctx-problem problems cap-problem checked))]
    (cond
      (empty? entries)
      (assert-page env (assoc state :problems
                              (or (seq all)
                                  [{:type :shape :message "nothing to assert — write a sentence"}]))
                   nil)
      (seq all) (assert-page env (assoc state :problems all) nil)
      :else     (assert-page env (assoc state :text nil)
                             (v/edit-with-consequences! kb batch)))))

(defn- retract-apply
  "Apply a checked retraction batch and render what it did, read off the store after the
  settle: the heading and the sweep's count follow the selected handles that are gone.  A
  selected sentex still stored is listed with why it stays and its row is re-rendered in
  place; every row that is gone is deleted.  The batch holds the handles `retraction-plan`
  says go and the asserted ones that stay; a selection of derived handles writes nothing
  and says so."
  [{:keys [kb] :as env} handles]
  (let [{:keys [going staying swept]} (retraction-plan env handles)
        premises (set (filter #(v/premise? kb %) staying))
        batch    (into (vec going) (filter premises) staying)
        rows     (removal-rows kb going)
        removed  (when (seq batch) (:removed (v/edit! kb {:remove batch})))
        doomed   (into (vec handles) swept)
        gone     (into [] (remove #(v/sentex kb %)) doomed)
        went     (filterv (set gone) handles)
        _        (removed/note! (removed-owner kb) :retract (keep rows went))
        stayed   (into [] (keep #(v/sentex kb %)) (remove (set gone) handles))]
    (prime-belief! env (map :id stayed))
    (frag (list [:div.editor
                 [:h3 (if (seq went) "Retracted" "Nothing retracted")]
                 (if removed
                   [:p.muted (:removed-sentexes removed) " sentexes · "
                    (:removed-justifications removed) " justifications · one settle."]
                   [:p.muted "Nothing was written."])
                 (when (> (count gone) (count went))
                   [:p.muted "The sweep took " (- (count gone) (count went))
                    " derived sentexes with them."])
                 (when (seq went)
                   [:p.muted "The " [:a {:href "/removed"} "removed list"]
                    " keeps what went, to put back."])
                 (stayed-rows env stayed premises "Still stored")
                 [:div.editor-actions [:button#sx-cancel.primary {:type "button"} "Close"]]]
                (for [h gone] (oob "delete" h [:li {:data-h h}]))
                (for [s stayed :when (premises (:id s))]
                  (oob "outerHTML" (:id s) (sentex-row env s)))))))

(defn retract-post
  "Retract the named handles through `edit`: one settle for the batch, the write path the
  editor's save takes.  The answer deletes every row that is gone out of band, the named
  handles and whatever the sweep took.  The write follows the `check-edit` round-trip every
  write post makes (docs/operations.md), so a stale handle comes back as the problem panel."
  [{:keys [kb] :as env} handles]
  (if-let [problems (seq (handle-problems kb handles))]
    (not-written "Not retracted" problems)
    (retract-apply env handles)))

;; ---- what was removed, to put back ---------------------------------------
;;
;; Every removal the browser makes is noted after its write returns (`removed/note!`), so
;; a retraction the reader regrets is one click from undone rather than a sentence to
;; retype from memory.

(defn- copy-href
  "The assert form, opened on `sentence` in `context` with `strength`: what Copy links
  to, from a row's menu or from this list."
  [sentence context strength]
  (str "/assert?text=" (url-enc sentence) "&ctx=" (url-enc context)
       (when (= :monotonic strength) "&strength=monotonic")))

(defn- removed-page
  "The removals noted for the KB, newest first, each with Put back and Copy.  `note` is
  what the last Put back said."
  [{:keys [kb] :as env} note]
  (let [label (kb-name kb)
        es    (removed/entries (removed-owner kb))]
    (render env "removed"
            [:h2 "Removed"]
            note
            [:p.muted "The last " removed/max-kept " sentexes removed from " [:b label]
             " through this browser, newest first. Put back asserts the sentence in its "
             "context again, as a job; Copy opens the assert form on it. The derived "
             "sentexes a removal swept away are not listed: they return with what they "
             "rest on."]
            (if (empty? es)
              [:p.muted "Nothing removed yet."]
              [:ul.removed-list
               (for [{:keys [id at sentence context strength via]} es]
                 [:li
                  [:div.muted (local-time at) " · " (name via) " · in " [:code context]
                   (when (= :monotonic strength) " · known-true")]
                  [:pre.removed-sentence sentence]
                  [:div.editor-actions
                   [:form {:hx-post "/removed/restore"}
                    [:input {:type "hidden" :name "id" :value id}]
                    [:button.primary {:type "submit"} "Put back"]]
                   [:a.button {:href (copy-href sentence context strength)} "Copy"]]])]))))

(defn- restore-post
  "Put back the noted removal `id`: read its sentence in its context, check it as
  `assert-post` checks a form, and assert it; only an assert that went through drops it
  from the list.  Answers the list, with what happened above it."
  [{:keys [kb] :as env} id]
  (let [owner (removed-owner kb)
        e     (removed/entry owner id)]
    (if-not e
      (removed-page env [:p.problem "That removal is not on the list any more."])
      (let [{:keys [entries problems]}
            (read-entries (:sentence e)
                          {:ctx  (->form (:context e))
                           :opts (when (= :monotonic (:strength e)) {:strength :monotonic})})
            batch   {:add (mapv :entry entries)}
            checked (when (and (seq entries) (empty? problems))
                      (map #(select-keys % [:type :message]) (v/check-edit kb batch)))
            all     (concat problems checked)]
        (cond
          (empty? entries)
          (removed-page env [:p.problem "The noted sentence no longer parses as a sentence."])
          (seq all)
          (removed-page env (list [:p.problem "Not put back:"]
                                  [:ul.edit-errors (map problem-line all)]))
          :else
          (do (v/edit! kb batch)
              (removed/forget! owner id)
              (removed-page env [:p.chain-note "Put back in " [:code (:context e)] ": "
                                 [:code (:sentence e)]])))))))

;; ---- a term's operations: rename, copy, remove ---------------------------
;;
;; Each one rewrites every **asserted** sentex that mentions the term — the derived ones
;; follow what they rest on — so each is a job, and each opens on a panel saying how
;; many sentexes it touches and roughly how long that takes before anything is written.

(def ^:private term-op-scan
  "How many sentexes the confirmation panel walks a term's index for.  Past it the panel
  says \"more than\" and the estimate is a floor, since counting a term with millions of
  mentions is itself a read of millions of records."
  50000)

(def ^:private term-op-chunk
  "How many sentexes one `edit!` of a term operation carries.  A chunk is one settle, and
  the boundary between two is where a cancel lands and the progress moves, so a rename of
  a large term reports as it goes and stops cleanly when asked."
  500)

(def ^:private term-op-confirm-ms
  "The estimated run past which a term operation asks for an explicit acknowledgement of
  its length, on top of its own button."
  60000)

(def ^:private default-ms-per-sentex
  "The estimate's rate before this process has timed a term operation on a KB."
  50.0)

;; milliseconds per sentex of the last term operation on each KB, by name
(defonce ^:private term-op-rates (atom {}))

(defn- asserted-mentions
  "The handles of the asserted sentexes mentioning `term` — at most `cap` of them, with
  whether the walk stopped at the cap, when `cap` is given."
  ([kb term]
   (into [] (comp (filter :strength) (map :id)) (v/find-sentexes kb term)))
  ([kb term cap]
   (let [hs (into [] (comp (filter :strength) (map :id) (take (inc cap)))
                  (v/find-sentexes kb term))]
     [(vec (take cap hs)) (> (count hs) cap)])))

(defn- term-op-estimate-ms [kb n]
  (long (* n (get @term-op-rates (kb-name kb) default-ms-per-sentex))))

(defn- rewrite-entry
  "Sentex `s` as an `edit!` entry with `to` in place of `term`, its context included."
  [s term to]
  (let [swap #(if (= term %) to %)
        opts (when (= :monotonic (:strength s)) {:strength :monotonic})]
    (cond-> [(walk/postwalk swap (lines/wrapped-sentence s)) (swap (:context s))]
      opts (conj opts))))

(def ^:private term-op-sample
  "How many of a term's asserted sentexes the new-name check rewrites and asks
  `check-edit` about: enough to catch the clash a merge makes, few enough to answer on a
  pause in typing."
  50)

(defn- merge-problems
  "Why `term` should not be merged into the existing term `to`, as text, or nil: the two
  disjoint, a type and a relation, two relations of different arities, or a rewritten
  sentex among the first `term-op-sample` that `check-edit` refuses."
  [kb term to]
  (let [rel?  #(v/relation? kb %)
        arity #(v/relation-arity kb %)
        [hs]  (asserted-mentions kb term term-op-sample)
        adds  (into [] (comp (keep #(v/sentex kb %)) (map #(rewrite-entry % term to))) hs)
        bad   (filter #(= :add (:in %)) (when (seq adds) (v/check-edit kb {:add adds})))]
    (seq (concat
          (when (v/disjoint? kb term to)
            [(str term " and " to " are disjoint, so nothing can be both.")])
          (when (not= (rel? term) (rel? to))
            ["One is a relation and the other a type."])
          (when (and (rel? term) (rel? to) (arity term) (arity to) (not= (arity term) (arity to)))
            [(str term " takes " (arity term) " arguments and " to " takes " (arity to) ".")])
          (when (seq bad)
            [(str (count bad) " of the first " (count adds) " rewritten sentexes would be "
                  "refused and stay as they are: " (or (:message (first bad)) "check-edit refuses it") ".")])))))

(defn- term-op-name-status
  "What a rename or copy panel says of the new name `to` as it is typed (read as a
  parameter: nil for none, anything but a symbol for text that names no term): not a name, the
  term's own name, a name for another role, a new term, or an existing one — and then
  whether `term` merges into it cleanly (`merge-problems`).  A GET: it writes nothing."
  [{:keys [kb]} op term to]
  (let [role #(some-> (v/term-role %) name)]
    (cond
      (nil? to) nil
      (not (symbol? to))
      [:p.problem "Not a term name."]
      (= term to)
      [:p.problem "That is its own name."]
      (not= (v/term-role term) (v/term-role to))
      [:p.problem [:code (pr-str to)] " is spelled as a " (or (role to) "name of no role") ", and "
       [:code (pr-str term)] " is a " (or (role term) "name of no role") "; the new name keeps its role."]
      (empty? (v/find-sentexes kb to))
      [:p.term-op-new [:code (pr-str to)] " is a new term: nothing mentions it yet."]
      (= "copy" op)
      [:p.term-op-exists [:code (pr-str to)] " exists: the copies join what it already has."]
      :else
      (let [problems (merge-problems kb term to)]
        [:div.term-op-exists
         [:p [:code (pr-str to)] " exists, so this merges " [:code (pr-str term)] " into it."]
         (if problems
           (list [:p.problem "Not compatible:"] [:ul (for [p problems] [:li p])])
           [:p.muted "Compatible: not disjoint, the same kind of term, and the first "
            term-op-sample " rewritten sentexes pass check-edit."])]))))

(defn- term-op-panel
  "The confirmation a term bar button opens: what the operation does, how many asserted
  sentexes it touches, roughly how long that takes, the new name for one that needs it,
  and the button.  A run estimated past `term-op-confirm-ms` also needs its length
  acknowledged.  A GET: it writes nothing."
  [{:keys [kb] :as env} op term]
  (let [{:keys [verb named?]} (term-ops op)
        [hs more?] (asserted-mentions kb term term-op-scan)
        n      (count hs)
        est    (term-op-estimate-ms kb n)
        long?  (> est term-op-confirm-ms)
        text   (term-text env term)
        close  [:button#sx-cancel {:type "button"} "Cancel"]]
    [:div.editor
     [:h3 verb " " [:code text]]
     [:p (case op
           "rename" (list "Every asserted sentex that mentions " [:code text]
                          " is asserted again with the new name in its place, and the old "
                          "one is retracted. If the new name is already a term, this "
                          "merges the two.")
           "copy"   (list "Every asserted sentex that mentions " [:code text]
                          " is asserted again with the new name in its place; the "
                          "originals stay.")
           "remove" (list "Every asserted sentex that mentions " [:code text]
                          " is retracted, and the derived ones go with what they rest on. "
                          "The " [:a {:href "/removed"} "removed list"]
                          " keeps the last " removed/max-kept " of them."))]
     [:p.muted (if more? "More than " "") (commas n) " asserted sentex"
      (when (not= 1 n) "es") " · about " (duration-text est)
      (when-not (contains? @term-op-rates (kb-name kb))
        " (a guess until a term operation on this KB has been timed)")
      ". It runs as a job, " (commas term-op-chunk) " sentexes a settle, and a cancel "
      "stops it between two."]
     (if (zero? n)
       (list [:p.muted "Nothing to do: no asserted sentex mentions it."]
             [:div.editor-actions close])
       ;; the answer replaces #main (the body's target); the panel closes once it lands
       ;; a rename and a remove ask once more in a browser dialog, after the panel's button
       [:form (cond-> {:hx-post "/term-op"
                       "hx-on::after-request" "if (event.detail.successful) vaelii.closeEditor()"}
                (not= "copy" op)
                (assoc :hx-confirm (str verb " " text "? " (if more? "More than " "")
                                        (commas n) " asserted sentex" (when (not= 1 n) "es")
                                        (if (= "remove" op) " will be retracted." " will be rewritten."))))
        [:input {:type "hidden" :name "op" :value op}]
        [:input {:type "hidden" :name "q" :value (pr-str term)}]
        (when named?
          (list
           [:div.assert-row
            [:label {:for "term-op-to"} "New name"]
            ;; each pause in typing asks whether the name is a term and, for a rename,
            ;; whether the two merge
            [:input#term-op-to {:type "text" :name "to" :size 32 :autocomplete "off"
                                :required true
                                :hx-get "/term-op/name" :hx-include "closest form"
                                :hx-trigger "input changed delay:300ms"
                                :hx-target "#term-op-to-status" :hx-select "unset"
                                :hx-swap "innerHTML"}]]
           [:div#term-op-to-status {:aria-live "polite"}]))
        (when long?
          [:label.check
           [:input {:type "checkbox" :name "long" :value "1" :required true}]
           " I know this runs for about " (duration-text est) "."])
        [:div.editor-actions
         [(if (= "copy" op) :button.primary :button.danger) {:type "submit"}
          verb " " (when more? "over ") (commas n)]
         close]])]))

(defn- term-op-chunk!
  "Apply one chunk of a term operation and answer `{:written :refused}`.  The additions
  are checked first; an addition `check-edit` refuses is dropped **with** the retraction
  it pairs with, so a rename never removes a sentex whose replacement was not admitted."
  [kb op term to hs]
  (let [ss      (into [] (keep #(v/sentex kb %)) hs)
        adds    (when (not= "remove" op) (mapv #(rewrite-entry % term to) ss))
        bad     (into #{} (keep #(when (= :add (:in %)) (:index %)))
                      (when (seq adds) (v/check-edit kb {:add adds})))
        keep-i  (remove bad (range (count ss)))
        batch   (cond-> {}
                  adds              (assoc :add (mapv adds keep-i))
                  (not= "copy" op)  (assoc :remove (mapv #(:id (ss %)) keep-i)))
        rows    (when (= "remove" op) (removal-rows kb (:remove batch)))]
    (when (or (seq (:add batch)) (seq (:remove batch)))
      (v/edit! kb batch))
    (when rows
      (removed/note! (removed-owner kb) :term (keep #(when-not (v/sentex kb %) (rows %))
                                                    (:remove batch))))
    {:written (count keep-i)
     :refused (for [i (sort bad)] (pr-str (first (adds i))))}))

(defn- term-op-job
  "A term operation as a job, and return its id.  The handles are read once, up front, so
  the chunks walk a fixed list rather than an index the rewrite is changing under them."
  [kb op term to in-monitor]
  (let [{:keys [verb]} (term-ops op)
        label  (str verb " " (pr-str term) (when to (str " → " (pr-str to))) " in " (kb-name kb))
        target (or (when (not= "remove" op) to) term)]
    (jobs/submit
     {:label label :kind :edit :writes kb
      :result-url (str "/term?q=" (url-enc (pr-str target)))
      :progress {:phase (keyword op) :done 0}}
     (fn [progress!]
       (in-monitor
        (fn []
          (let [t0  (System/currentTimeMillis)
                hs  (asserted-mentions kb term)
                total (count hs)]
            (progress! {:phase (keyword op) :done 0 :total total})
            (let [r (reduce (fn [acc chunk]
                              (let [{:keys [written refused]} (term-op-chunk! kb op term to chunk)
                                    acc (-> acc
                                            (update :sentexes + written)
                                            (update :done + (count chunk))
                                            (update :refused into refused))]
                                (progress! {:phase (keyword op) :done (:done acc) :total total})
                                acc))
                            {:sentexes 0 :done 0 :refused []}
                            (partition-all term-op-chunk hs))
                  ms (- (System/currentTimeMillis) t0)]
              (when (pos? total)
                (swap! term-op-rates assoc (kb-name kb) (/ (double ms) total)))
              (with-meta (select-keys r [:sentexes])
                {:answer {:op op :term term :to to :total total
                          :written (:sentexes r) :refused (:refused r)}})))))))))

(defn- term-op-result
  "What a finished term operation says: how many sentexes it wrote, the ones it could
  not, and where its result is."
  [env {:keys [op term to total written refused]}]
  (let [target (if (= "remove" op) term to)]
    (render env "term operation"
            [:h2 (:verb (term-ops op)) " " [:code (term-text env term)]
             (when to (list " → " [:code (pr-str to)]))]
            [:p (commas written) " of " (commas total) " asserted sentexes "
             (case op "rename" "rewritten" "copy" "copied" "remove" "removed") "."]
            (when (seq refused)
              (list [:h3 (commas (count refused)) " refused"]
                    [:p.muted "Their replacement did not pass "
                     [:code "check-edit"] ", so the original stays."]
                    [:ul (for [r (take 50 refused)] [:li [:code r]])]))
            [:p [:a {:href (str "/term?q=" (url-enc (pr-str target)))}
                 "The term " [:code (pr-str target)]]])))

;; ---- knowledge bases: the catalog page ----------------------------------
;; This page lists what this process can load (`catalog/sources`) and has loaded
;; (`catalog/entries`) and drives the transitions.  A load runs on the catalog's own thread;
;; the loaded panel re-fetches itself once a second **while a load is running**, and the
;; server stops the poll by omitting the trigger.

(defn- slider-pos
  "Where a knob's default sits on its 0–1000 track.  A count that ranges to millions is
  useless on a linear track — every interesting value is in the first pixel — so those
  knobs are marked `:scale :log` and mapped logarithmically here and in vaelii.js, which
  does the inverse when the reader drags."
  [v lo hi scale]
  (let [v (double (max lo (min hi (or v lo))))]
    (long (Math/round
           (* 1000.0
              (if (= :log scale)
                (let [l (Math/log (+ 1.0 (double lo)))
                      h (Math/log (+ 1.0 (double hi)))]
                  (if (== h l) 0.0 (/ (- (Math/log (+ 1.0 v)) l) (- h l))))
                (let [d (- (double hi) (double lo))]
                  (if (zero? d) 0.0 (/ (- v (double lo)) d)))))))))

(defn- option-control
  "One form control for a source option, from its own description — the generator's
  sliders are `vaelii.host.io.generate/knobs` rendered, so the page cannot disagree with
  the generator about a parameter's range or default."
  [{:keys [key type label default help choices min max step scale unit placeholder]}]
  (let [k (name key)]
    (case type
      :slider [:label.knob
               [:span.knob-l label (when help [:span.knob-h help])]
               [:input.knob-r {:type "range" :min 0 :max 1000 :step 1
                               :value (slider-pos default min max scale)
                               :data-min min :data-max max :data-step (or step 1)
                               :data-log (if (= :log scale) "1" "0")
                               :data-unit (or unit "") :data-knob k}]
               [:output.knob-v {:name (str "out-" k)} (str (commas default) (or unit ""))]
               [:input {:type "hidden" :name k :value default :data-knob-value k}]]
      :flag   [:label.kb-opt
               [:input {:type "checkbox" :name k :value "1" :checked (boolean default)}]
               [:span " " label] (when help [:span.muted " — " help])]
      :choice [:label.kb-opt [:span label " "]
               [:select {:name k}
                (for [[v lbl] choices]
                  [:option (cond-> {:value v} (= v default) (assoc :selected true)) lbl])]]
      :number [:label.kb-opt [:span label " "]
               [:input {:type "number" :name k :value default :placeholder placeholder
                        :min (or min 0) :max (or max 1000000) :step (or step 1)}]]
      :path   [:label.kb-opt [:span label " "]
               [:input {:type "text" :name k :value (or default "") :placeholder "(memory)"
                        :size 30}]
               (when help [:span.muted " — " help])]
      nil)))

(defn- kb-action
  "One action button, as its own POST form: loading, unloading and activating all change
  the process's state, so each is a write, each is origin-checked, and each answers with
  the page it changed."
  [label uri params & [cls]]
  [:form.kb-action {:method "post" :action uri
                    :hx-post uri :hx-target "#main" :hx-select "#main" :hx-swap "outerHTML"}
   (for [[k v] params] [:input {:type "hidden" :name (name k) :value (str v)}])
   [:button (cond-> {:type "submit"} cls (assoc :class cls)) label]])

;; ---- what it all costs in RAM -------------------------------------------
;; The **heap** is measured and belongs to the whole process; a KB's **footprint** is
;; estimated from its stored sentex count, since measuring one of several resident KBs would
;; mean unloading it and diffing.  The panel keeps the two apart.

(defn- est-bytes
  "An estimated byte count, marked as one.  Everything the panel shows about a KB is an
  estimate, and a figure that is indistinguishable from a measurement is worse than no figure."
  [n]
  (when n [:span.est "≈ " (catalog/human-bytes n)]))

(defn- meter
  "A proportion bar — the heap's own, drawn like a load's progress bar so the page has one
  visual language for \"how full is this\"."
  [frac]
  [:div.bar [:span.bar-fill {:style (str "width:" (css-percent (min 1.0 frac)) "%")}]])

(defn- memory-panel
  "The memory strip that heads the loaded list, collapsed or expanded.  Two htmx requests
  that must not be confused for each other: the header line **toggles** (it fetches the
  state it is not in), while the panel itself **refreshes** at the state it is in, and
  only while a load is running — a corpus arriving is exactly when a reader wants to
  watch this number, and the server decides by including the trigger, as the entries list
  does.  One element carrying both would poll the toggle and flip the breakdown open and
  shut every two seconds."
  [detail?]
  (let [{:keys [heap entries total]} (catalog/memory)
        {:keys [used committed max]} heap
        busy? (catalog/loading?)
        here  (str "/kbs/memory" (when detail? "?detail=1"))
        there (str "/kbs/memory" (when-not detail? "?detail=1"))]
    [:div#kb-memory.kb-memory
     (cond-> {}
       busy? (merge (polling here "2s")))
     [:div.kb-mem-line
      {:hx-get there :hx-trigger "click, keyup[key=='Enter']"
       :hx-target "#kb-memory" :hx-select "unset" :hx-swap "outerHTML"
       :role "button" :tabindex "0"
       :title (if detail? "Hide the breakdown" "Show the breakdown")}
      [:b "Memory"]
      [:span.muted " heap " (catalog/human-bytes used)
       (when max (str " of " (catalog/human-bytes max)))]
      (when (pos? total) [:span.muted " · loaded KBs " (est-bytes total)])
      [:span.kb-mem-more (if detail? "hide" "details")]]
     (when max (meter (/ (double used) (double max))))
     (when detail?
       [:div.kb-mem-detail
        [:div.table-scroll
         [:table.kb-mem-table
          [:thead [:tr [:th "KB"] [:th "sentexes"] [:th "records"] [:th "index"]
                   [:th "belief"] [:th "estimated total"]]]
          [:tbody
           (for [{:keys [name sentexes records index tms total paged? belief?]} entries]
             [:tr [:td name]
              [:td (commas sentexes)]
              [:td (if paged? [:span.muted "paged"] (catalog/human-bytes records))]
              [:td (catalog/human-bytes index)]
              [:td (if belief? (catalog/human-bytes tms) [:span.muted "not built"])]
              [:td (est-bytes total)]])
           (when (empty? entries) [:tr [:td.muted {:colspan "6"} "Nothing loaded."]])]]]
        [:p.muted "Heap: " (catalog/human-bytes used) " used · "
         (catalog/human-bytes committed) " committed"
         (when max (str " · " (catalog/human-bytes max) " max"))
         ". Used includes garbage not yet collected, so it drifts up between collections."]
        [:p.muted "A KB's size is an estimate — its stored sentex count times what a "
         "sentex measured, per resident component: "
         (commas (:index catalog/resident-bytes-per-sentex)) " B of index, "
         (commas (:records catalog/resident-bytes-per-sentex)) " B of records, "
         (commas (:tms catalog/resident-bytes-per-sentex))
         " B of truth-maintenance network. A disk-backed KB pages its records, and a KB "
         "loaded without belief has no network, so those terms drop. Fat sentences index "
         "heavier than the coefficient, so a rich corpus reads low."]])]))

(defn- refused-count
  "How many sentences a load refused.  An import accounts for them as a map,
  `{:checked n :skipped n :by-type {…}}` (docs/naming.md), and the skipped frames are the
  refused ones; a summary carrying a bare count is read as it stands."
  [summary]
  (let [r (:refused summary 0)] (if (map? r) (:skipped r 0) r)))

;; ---- a backup of a store kept in Postgres -------------------------------
;;
;; A `:pg-snapshot` store is a directory of images plus a schema of records, and a large
;; edit wants both saved first.  The card offers it as a button; the job is
;; `vaelii.browser.backup`'s, and the card says where the last one went.

(defn- backup-action
  "The Back up button on a `:pg-snapshot` store's card, confirmed in the browser: the
  backup holds off every write for as long as the dump runs."
  [key name]
  [:form.kb-action {:method "post" :action "/kbs/backup"
                    :hx-post "/kbs/backup" :hx-target "#main" :hx-select "#main" :hx-swap "outerHTML"
                    :hx-confirm (str "Back up " name "? The KB is sealed, its directory cloned and its "
                                     "Postgres schema written out with pg_dump, beside the store. "
                                     "Nothing can write to it until the dump is done.")}
   [:input {:type "hidden" :name "key" :value key}]
   [:button {:type "submit"} "Back up"]])

(defn- backup-line
  "Where the newest backup of entry `key` went, or how it is getting on."
  [key]
  (when-let [{:keys [status summary progress error]}
             (first (filter #(and (= :backup (:kind %)) (= key (:entry %))) (jobs/jobs)))]
    (case status
      :done                  [:p.muted "Backed up to " [:span.kb-path (:dir summary)] " · "
                              (catalog/human-bytes (:dump-bytes summary)) " of records in "
                              (format "%.0f" (/ (:ms summary 0) 1000.0)) " s"]
      (:running :cancelling) [:p.muted "Backing up: " (:note progress)]
      [:p.kb-error "The last backup " (clojure.core/name status) ": " error])))

(defn- entry-card
  "One loaded (or loading, or failed) KB.  Its footprint is read live rather than off the
  entry's load-time stats, so it tracks a KB that has been asserted into since — and a
  KB still loading, whose bar is then two readings of the same thing: how far the load has
  got, and what it is costing."
  [{:keys [key name status stats progress error elapsed-ms summary kb? job params where]} active?]
  (let [fp (catalog/footprint key)]
    [:div.kb-card {:class (str "kb-" (clojure.core/name status) (when active? " kb-on"))}
     [:div.kb-head
      [:span.kb-name name]
      [:span.tag {:class (str "tag-" (clojure.core/name status))} (clojure.core/name status)]
      (when active? [:span.tag.tag-in "active"])
      (when fp [:span.tag.tag-est (est-bytes (:total fp))])
      [:span.muted.kb-key key]
      ;; the load is a job like any other, so the card links to it rather than restating
      ;; what the jobs screen says about it
      (when job [:a.muted.kb-job {:href "/jobs"} "job " job])]
     (when (#{:running :cancelling} status) (progress-bar progress))
     (when-let [d (:dir params)] [:p.muted "On disk at " [:span.kb-path d]])
     (when error [:p.kb-error error])
     (backup-line key)
     (when (and stats (= :done status))
       [:p.muted (commas (:sentexes stats)) " sentexes · " (commas (:terms stats)) " terms · "
        (commas (:types stats)) " types · " (commas (:contexts stats)) " contexts"
        (when (pos? (:derived summary 0)) (str " · " (commas (:derived summary)) " derived"))
        (when (pos? (refused-count summary)) (str " · " (commas (refused-count summary)) " refused"))
        ;; the withheld mints the open left undrawn until `release-withheld!` runs
        (when-let [o (:owed-releases stats)] (str " · " (commas o) " mint releases owed"))
        ;; the records with no premise and no justification, which the open deletes none of
        (when-let [u (:unsupported stats)]
          (str " · " (commas (:n u)) " unsupported records (an earlier build's inert"
               " records count too)"))
        ;; a dump either brought its index or had one rebuilt for it.  Worth a word: the
        ;; rebuild is silent otherwise, and a cache that quietly stops being used is a
        ;; cache nobody maintains.
        (when-let [ix (:index summary)]
          (str " · index " (clojure.core/name ix)
               (when-let [r (:reason summary)] (str " (" (clojure.core/name r) ")"))))
        (when elapsed-ms (str " · loaded in " (format "%.1f" (/ elapsed-ms 1000.0)) "s"))])
     [:div.kb-actions
      ;; anything holding a KB can be read, including the one still arriving — the label
      ;; says which of those you are getting, since the button does the same thing either
      ;; way and only the answer differs
      (when (and kb? (not active?))
        (kb-action (case status
                     :done                     "Switch to"
                     (:running :cancelling)    "Browse as it loads"
                     (:cancelled :failed)      "Browse what landed"
                     "Switch to")
                   "/kbs/activate" {:key key} (when (= :done status) "primary")))
      (when (and kb? (= :done status) (= :pg-snapshot (:backend where)))
        (backup-action key name))
      (if (= :running status)
        (kb-action "Cancel" "/kbs/unload" {:key key})
        (kb-action "Unload" "/kbs/unload" {:key key}))]]))

(defn- source-card
  "One loadable source, with the form that loads it.  A source already loaded and not
  repeatable (an ontology is an ontology) offers no second copy; the generator does,
  since a different shape is a different KB.

  A source that knows how much it holds also says what loading it would cost in RAM —
  which is the number that decides whether to load it at all, and the one the reader
  otherwise finds out by watching the heap fill."
  [{:keys [id name blurb scale options repeat? missing? path] :as src} loaded? busy?]
  [:div.kb-card.kb-source
   [:div.kb-head [:span.kb-name name] [:span.muted.kb-key scale]
    (when-let [b (and (not missing?) (catalog/predicted-footprint src))]
      [:span.tag.tag-est (est-bytes b) " in RAM"])]
   [:p.muted blurb (when path [:span.kb-path " " path])]
   (cond
     missing?               [:p.muted "Unavailable."]
     (and loaded? (not repeat?)) [:p.muted "Loaded."]
     :else
     [:form.kb-load {:method "post" :action "/kbs/load"
                     :hx-post "/kbs/load" :hx-target "#main" :hx-select "#main"
                     :hx-swap "outerHTML"}
      [:input {:type "hidden" :name "id" :value id}]
      (when (seq options) [:div.kb-opts (map option-control options)])
      [:button.primary {:type "submit" :disabled busy?}
       (if loaded? "Load another" "Load")]
      (when busy? [:span.muted " — a load is already running"])])])

(defn- entries-panel
  "The loaded-KB list, as the fragment that refreshes itself.  `hx-trigger` is present
  only while a load is running, so the polling stops on its own.

  The header's KB name rides along as an out-of-band swap, because activating a KB
  changes it and the header sits outside the region a swap replaces — but only when this
  *is* an answer to a swap.  A whole document carries a freshly rendered header already,
  so shipping the out-of-band copy in one would put a second `#kb-label` in the page: a
  duplicate id, which is what every later `#kb-label` target would then resolve against."
  [fragment?]
  (let [es     (catalog/entries)
        active (catalog/active)
        busy?  (catalog/loading?)]
    [:div#kb-entries
     (cond-> {}
       busy? (merge (polling "/kbs/rows" "1s")))
     (when fragment? [:span#kb-label {:hx-swap-oob "true"} (active-kb-name)])
     (if (seq es)
       (for [e es] (entry-card e (= (:key e) active)))
       [:p.muted "Nothing loaded."])]))

;; ---- and back out again -------------------------------------------------
;;
;; The Available list is the outbound half of a loop; this is the return leg.  A dump
;; written under the KB search path is a `:dump` source the moment `meta.edn` lands, so
;; export-then-reload is two clicks and never leaves the browser.

(defn- exported-source
  "The catalog source a finished dump became, or nil — the loop closed, or not.
  Asked of `catalog/sources` rather than assumed, which also answers the partial
  case correctly: `classify` keys on `meta.edn` and `export!` writes it last, so a cancelled
  export answers nil here for the same reason it is not loadable."
  [dir]
  (when dir (first (filter #(= dir (:path %)) (catalog/sources)))))

(defn- export-report
  "What the last export did — running, finished, cancelled or failed.  A finished one says
  where the dump went *and* whether the catalog can see it there, since a dump outside the
  search path is a perfectly good dump that this page will never offer."
  [{:keys [name dir status progress summary error elapsed-ms]}]
  (list
   [:p [:span.tag {:class (str "tag-" (clojure.core/name status))} (clojure.core/name status)]
    " " [:b name] " → " [:span.kb-path dir]]
   (when (#{:running :cancelling} status) (progress-bar progress))
   (when error [:p.kb-error error])
   (when summary
     [:p.muted (commas (:sentexes summary)) " sentexes · "
      (commas (:justifications summary)) " justifications"
      (when (pos? (:index-entries summary 0))
        (str " · " (commas (:index-entries summary)) " index entries"))
      " · " (catalog/human-bytes (:bytes summary))
      (when elapsed-ms (str " · " (format "%.1f" (/ elapsed-ms 1000.0)) "s"))])
   (when (= :done status)
     (if-let [s (exported-source (:dir summary))]
       [:p.muted "Offered below as " [:b (:name s)] " — " (:scale s) "."]
       [:p.muted "It is outside the KB search path, so it is not offered below. Move it "
        "under a " [:code "VAELII_KB_PATH"] " directory to load it from here."]))
   (when (= :running status) (kb-action "Cancel" "/kbs/export/cancel" {}))))

(def ^:private export-choices
  "The two choices the export form offers, per parameter, as `[value label]` with the
  writer's default first.  The form is rendered from this, and `/kbs/export` refuses any
  other value before an export job starts."
  {"variant"     [["records" "Records — the whole KB"]
                  ["records+index" "Records and index — larger, loads faster"]]
   "compression" [["gzip" "gzip"]
                  ["xz" "xz — smaller, slower to write"]
                  ["none" "none"]]})

(defn- export-form
  "The three knobs `export!` takes, and nothing restated: the defaults are the writer's,
  and a field left alone sends nothing rather than sending the default back."
  [entry-name busy?]
  [:form.kb-load {:method "post" :action "/kbs/export"
                  :hx-post "/kbs/export" :hx-target "#main" :hx-select "#main"
                  :hx-swap "outerHTML"}
   [:p.muted "Writes " [:b entry-name] " as a portable dump — one that survives a "
    "backend, index or record-name change the on-disk store would not."]
   [:div.kb-opts
    (if (catalog/request-paths?)
      [:label.kb-opt [:span "Destination directory "]
       [:input {:type "text" :name "dir" :size 40 :placeholder "/path/to/new-dump"}]
       [:span.muted " — a path on this machine; must be empty or not exist yet. Empty"
        " writes under " (str (or (catalog/write-root) "the KB search path")) "."]]
      (if-let [root (catalog/write-root)]
        [:p.muted "Written under " [:span.kb-path (str root)]
         ", in a new directory named after the KB and the time."]
        [:p.muted "Every " [:code "VAELII_KB_PATH"] " entry is itself a KB, so there is"
         " no directory to write a dump under."]))
    (for [[param label] [["variant" "Variant "] ["compression" "Compression "]]]
      [:label.kb-opt [:span label]
       [:select {:name param}
        (for [[i [value text]] (map-indexed vector (export-choices param))]
          [:option (cond-> {:value value} (zero? i) (assoc :selected true)) text])]])]
   [:button.primary {:type "submit" :disabled busy?} "Export"]
   (when busy? [:span.muted " — an export is already running"])])

(defn- export-panel
  "Writing the active KB out, as the fragment that refreshes itself.  Like the entries
  list and the memory strip it polls only while there is something to watch — the trigger
  is the server's to include, so a finished export stops asking on its own.

  The report it shows is the **registry's** newest export job, not a slot of its own: one
  export at a time and the last report worth keeping, which is what lets the panel say
  where the dump went after the job has finished."
  []
  (let [job    (jobs/latest :export)
        key    (catalog/active)
        e      (catalog/active-entry)
        busy?  (catalog/exporting?)]
    [:div#kb-export
     (cond-> {}
       busy? (merge (polling "/kbs/export/rows" "1s")))
     [:div.kb-card
      (when job (export-report job))
      (cond
        (nil? e)
        [:p.muted "Nothing is loaded to export."]

        (not (catalog/in-process? key))
        [:p.muted [:b (:name e)] " is served by a daemon, so its dump is written on that "
         "daemon's own host — export it from there."]

        :else
        (export-form (:name e) busy?))]]))

(defn kbs-page
  "The knowledge bases page: what is loaded, and what can be.  `note` is what the catalog
  said about the action that led here — a refusal is a state to show, not an error
  status, since the page is still the right answer."
  ([env] (kbs-page env nil))
  ([env note]
   (let [loaded (into #{} (map (comp :id :source)) (catalog/entries))
         busy?  (catalog/loading?)]
     (render env "knowledge bases"
             [:h2 "Knowledge bases"]
             (when note [:p.problem note])
             [:p.muted "One KB is active at a time; every page reads it. Loading runs in "
              "the background — keep browsing, or switch to the arriving one and watch it "
              "fill. An unfinished KB says so at the top of every page."]
             [:h3 "Loaded"]
             (memory-panel false)
             ;; the heap is half the cost question and the derived structures beside it
             ;; are the other half, so the strip that measures one points at the page
             ;; that measures the other
             [:p.muted "Heap is what the stores cost. What the engine holds "
              [:i "beside"] " them — the caches, their bounds and their hit rates — is on "
              [:a {:href "/caches"} "the caches page"] "."]
             (entries-panel (:fragment? env))
             [:h3 "Export"]
             (export-panel)
             [:h3 "Available"]
             ;; the cap says so on the page as well as in the log: a list silently
             ;; ending early reads as "this machine has no other KBs", which is the
             ;; one answer a KB list must not give by accident (docs/catalog.md)
             (let [srcs (catalog/sources)]
               (list
                (for [{:keys [dir passed-over]} (:truncated (meta srcs))]
                  [:p.muted "Listing the first " catalog/max-discovered " entries of "
                   [:code dir] " — " passed-over " more are not shown. Name one in the "
                   "catalog file to list it regardless."])
                (for [s srcs] (source-card s (contains? loaded (:id s)) busy?))))))))

;; ---- long work, watched: the jobs screen --------------------------------
;; A load, an export and a chaining run take minutes and share one mechanism
;; (`vaelii.browser.jobs`) and one status vocabulary.  This screen renders that registry;
;; the `/kbs` panels are the same registry filtered to two kinds.  A job **outlives the
;; request that started it**: closing the tab cancels nothing.  The poll is the
;; self-terminating htmx one every watching panel uses, which survives a reload.

(defn- job-card
  "One job: what it is, where it has got to, and what it left behind.  A running one offers
  the cancel; a finished one offers the page its result is on, since a job that ran while
  the reader was elsewhere is exactly the case a result link is for."
  [{:keys [id label kind status progress error elapsed-ms summary result-url writes? no-cancel]}]
  [:div.kb-card {:class (str "kb-" (clojure.core/name status))}
   [:div.kb-head
    [:span.kb-name label]
    [:span.tag {:class (str "tag-" (clojure.core/name status))} (clojure.core/name status)]
    (when kind [:span.muted.kb-key (clojure.core/name kind)])
    [:span.muted.kb-key "job " id]]
   (when (#{:running :cancelling} status) (progress-bar progress))
   (when error [:p.kb-error error])
   ;; A stopped job has **no summary** — it never reached its return value — so its last
   ;; progress reading is the only account of what landed, and a reader who cancelled is
   ;; owed exactly that.  It is what a stopped run left in the KB, not a fraction of a
   ;; run that is still going, so it is said in the past tense and not as a bar.
   (when (and (#{:cancelled :failed} status) (pos? (:done progress 0)))
     [:p.muted "Reached " [:b (commas (:done progress))]
      (when-let [t (:total progress)] (list " of " (commas t)))
      (when-let [p (:phase progress)] (str " at " (clojure.core/name p)))
      " before it stopped — that much is in the KB."])
   ;; whichever of these the job's own summary carries — a load counts sentexes, a chaining
   ;; run counts derivations, an export counts bytes — and nothing where it carries none
   (let [parts (cond-> []
                 (:sentexes summary)       (conj (str (commas (:sentexes summary)) " sentexes"))
                 (:derived summary)        (conj (str (commas (:derived summary)) " derived"))
                 (:truncated? summary)     (conj "truncated at its bound")
                 (:justifications summary) (conj (str (commas (:justifications summary))
                                                      " justifications"))
                 (:bytes summary)          (conj (catalog/human-bytes (:bytes summary)))
                 elapsed-ms                (conj (str (format "%.1f" (/ elapsed-ms 1000.0)) "s")))]
     (when (seq parts) [:p.muted (str/join " · " parts)]))
   [:div.kb-actions
    ;; `:no-cancel` is the reason a job offers no cancel: a reading an attached daemon runs
    (when (= :running status)
      (if no-cancel [:span.muted no-cancel] (kb-action "Cancel" "/jobs/cancel" {:id id})))
    (when (and (= :cancelling status) writes?)
      [:span.muted "Stopping at its next progress report — a job that writes a KB is never "
       "interrupted, since an interrupt mid-write tears what it lands in."])
    (when (and result-url (not= :running status))
      [:a.button {:href result-url} "See the result"])]])

(defn- jobs-panel
  "The job list, as the fragment that refreshes itself — and, when it *is* a fragment, the
  header's running count out of band beside it.  Polls only while something is running, so
  an idle page stops asking; a whole document carries a freshly rendered header already,
  so shipping the out-of-band copy in one would put a second `#job-count` in the page."
  [fragment?]
  (let [js (jobs/jobs)]
    [:div#jobs
     (cond-> {}
       (seq (jobs/running)) (merge (polling "/jobs/rows" "1s")))
     (when fragment? (jobs-badge true))
     (if (seq js)
       (for [j js] (job-card j))
       [:p.muted "Nothing has run yet."])]))

(defn- inflight-list
  "The page reads running now, each with its age and the engine frame it is in, or nil
  when there are none. `except` is an id to leave out: the reader's own, on its waiting
  page."
  ([] (inflight-list nil))
  ([except]
   (when-let [rs (seq (remove #(= except (:id %)) (inflight/running)))]
     [:ul.inflight
      (for [{:keys [ms frame] :as r} rs]
        [:li [:a {:href (inflight/href r)} [:code (inflight/href r)]] " · "
         (duration-text ms) (when frame (list " · " [:span.muted [:code frame]]))])])))

(defn- inflight-waiting
  "What a page load past `inflight/detach-ms` is answered with: what is being read and
  for how long, while a poll waits for it. The poll reloads the page once the read is
  done, and the reload is answered from the finished read."
  [target req {:keys [id started] :as e}]
  (render (env-of target req) "still reading"
          [:h2 "Still reading"]
          [:p [:code (inflight/href e)] " has been reading the KB for "
           (duration-text (- (System/currentTimeMillis) (long started)))
           ". It loads here when it is done, and every other page works meanwhile."]
          [:p.muted "Loading this address again joins the read instead of starting a "
           "second one. A read cannot be stopped from outside: interrupting a thread inside "
           "a disk store's read closes the store's file channel, so it runs to its end "
           "unless the browser is restarted."]
          [:div {:hx-get (str "/inflight/poll?id=" (url-enc id)) :hx-trigger "every 2s"
                 :hx-target "this" :hx-select "unset" :hx-swap "none"
                 :hx-indicator "unset"}]
          (when-let [others (inflight-list id)]
            (list [:h3 "Also reading"] others))))

(defn- jobs-page
  "The jobs screen.  `note` is what the registry said about the action that led here — a
  cancel of a job that has already finished is a state to report, not an error."
  ([env] (jobs-page env nil))
  ([env note]
   (render env "jobs"
           [:h2 "Jobs"]
           (when note [:p.problem note])
           [:p.muted "Loading a KB, writing one out and running the rules to a fixpoint all "
            "take longer than a request should, so each runs as a job, and so does every "
            "edit of a KB's content: an assert, an edit or a retraction can settle for "
            "minutes on a large KB. Closing this tab does not stop one — come back and it "
            "is still here. A finished job's report stays for an hour."]
           [:p.muted "Watching one and wondering what it costs: "
            [:a {:href "/caches"} "the caches page"] " says what this process is holding "
            "while it runs, and its numbers move as the job does."]
           (jobs-panel (:fragment? env))
           (when-let [rs (inflight-list)]
             (list [:h2 "Pages still reading"]
                   [:p.muted "A page load that takes longer than "
                    (duration-text (inflight/detach-ms)) " goes on reading after its "
                    "request is answered, and loading the same address joins it. Each "
                    "row is the page, how long it has read, and the engine frame it is in."]
                   rs)))))

;; ---- what this process is holding: caches, heap, and the profiler -------
;; The **programmer's** screen: the one page about the process rather than the knowledge.
;; It shows what the engine holds beside the store and the hit rates, which say whether a
;; repeated question is served from a cache.  The reads are `v/caches`, O(1) per row, so
;; the panel polls like every watching panel.  It reuses the heap strip and its
;; measurement/estimate distinction.

(defn- profiler-serve-ui
  "`clj-async-profiler.core/serve-ui`, or nil when the dependency is not on the
  classpath.  `requiring-resolve` is what lets the call site exist without the
  dependency: it ships in the `:repl` profile, so `lein browser` has it and `lein run -m
  vaelii.web` does not, and a page that rendered a dead link for the second case would be
  worse than one that says so."
  []
  (try (requiring-resolve 'clj-async-profiler.core/serve-ui)
       (catch Throwable _ nil)))

;; `{:port n}` once the profiler UI is up, `::starting` while a caller holds the claim to
;; start one, else nil.  A `defonce` so a namespace reload does not forget a server that is
;; still listening.
(defonce ^:private profiler-state (atom nil))

(defn start-profiler
  "Start the sampling profiler's UI when the operator asked for one (`VAELII_PROFILER`) and
  the class resolves.  A no-op otherwise, and a logged line when the operator asked and it
  is absent.  The claim is a `compare-and-set!` onto `::starting`, so a namespace reload and
  two concurrent callers cannot start a second one; a failed start restores the state.
  Bare, not `!`: it starts a server and destroys nothing.  Both entry points call it."
  []
  (when (and (v/switch-value "VAELII_PROFILER") (compare-and-set! profiler-state nil ::starting))
    (if-let [serve-ui (profiler-serve-ui)]
      (let [port (v/switch-value "VAELII_PROFILER_PORT")]
        (try
          (serve-ui port)
          (reset! profiler-state {:port port})
          (trove/log! {:level :info :id ::profiler
                       :msg (str "profiler UI on http://localhost:" port)})
          (catch Throwable t
            (reset! profiler-state nil)
            (trove/log! {:level :warn :id ::profiler
                         :msg (str "profiler UI would not start on port "
                                   (v/switch-value "VAELII_PROFILER_PORT") ": " (.getMessage t))}))))
      (do
        (reset! profiler-state nil)
        (trove/log! {:level :warn :id ::profiler
                     :msg (str "VAELII_PROFILER is set and clj-async-profiler is not on "
                               "the classpath — it ships in the :repl profile, which "
                               "`lein browser` activates and `lein run` does not")})))))

(defn- profiler-section
  "What the profiler is doing, in one of three states, and never a link to a port nothing
  is listening on."
  []
  (let [{:keys [port]} @profiler-state]
    (list
     [:h3 "Profiler"]
     (cond
       port
       [:p "Sampling profiler UI on "
        [:a {:href (str "http://localhost:" port)} "localhost:" port]
        [:span.muted " — flamegraphs of this JVM, on this machine. It attaches an agent "
         "and serves on a port of its own with no authentication, which is why it is "
         "started only when asked for."]]

       (profiler-serve-ui)
       [:p.muted "On the classpath, not started. Set " [:code "VAELII_PROFILER=1"]
        " before starting the browser (and " [:code "VAELII_PROFILER_PORT"]
        " to move it off 8080)."]

       :else
       [:p.muted "Not on the classpath. It ships in the " [:code ":repl"] " profile, so "
        [:code "lein browser"] " has it and " [:code "lein run -m vaelii.web"]
        " does not."]))))

(defn- cache-scope
  "Which thing a row's numbers are about — and, where the entries and the counters
  disagree, both: a row whose counters are the process's would otherwise attribute
  another KB's work to this one."
  [scope counters]
  (let [word {:kb "this KB" :process "this process"}]
    (list [:span (word scope)]
          (when (and counters (not= counters scope))
            [:div.muted "rates: " (word counters)]))))

(defn- cache-row
  "One cache: the counts on a row, and what it holds on the muted line under it. The
  note is not decoration — a column of bare integers over caches that count literals,
  networks, symbols and records compares nothing, and the unit column alone does not say
  what retires an entry."
  [{:keys [label entries limit unit hits misses hit-rate scope counters note error]}]
  (let [dash [:span.muted "—"]]
    (list
     [:tr
      [:td label]
      [:td.num (if entries (commas entries) dash)]
      [:td.num (if limit (commas limit) [:span.muted "none"])]
      [:td unit]
      [:td.num (if hits (commas hits) dash)]
      [:td.num (if misses (commas misses) dash)]
      [:td.num.cache-hit (if hit-rate (format "%.1f%%" (* 100.0 (double hit-rate))) dash)]
      [:td (cache-scope scope counters)]]
     ;; an errored row keeps its place and says what happened, rather than reading as a
     ;; cache that is empty — the two look identical in a column of dashes
     [:tr.cache-note [:td.muted {:colspan "8"}
                      (when error [:b.problem "Could not be read (" error "). "])
                      note]])))

(defn- caches-panel
  "The cache table, as the fragment that refreshes itself.  It polls only while a job is
  running — a load or a chaining run is exactly when these numbers move, and an idle page
  has nothing to watch — which is the same self-terminating trigger the KB panels use."
  [rows]
  [:div#caches
   (cond-> {}
     (seq (jobs/running)) (merge (polling "/caches/rows" "2s")))
   [:div.table-scroll
    [:table.stats-table.cache-table
     [:thead [:tr [:th "Cache"] [:th.num "Entries"] [:th.num "Limit"] [:th "Unit"]
              [:th.num "Hits"] [:th.num "Misses"] [:th.num "Hit rate"] [:th "Counts"]]]
     [:tbody (map cache-row rows)]]]
   [:p.muted "Ranked by entries. A blank entry count is a cache built and dropped inside "
    "a single chaining run or search step, so there is nothing to read between them; the "
    "row stays here rather than being left off."]
   [:p.muted "Every limit is a " [:b "wholesale"] " clear, not an eviction: past it the "
    "cache empties and refills by demand. A workload oscillating around a limit pays a "
    "full rebuild each time it crosses."]])

(defn- caches-clear-note
  "What a clear turned out to drop, for the line above the table it changed."
  [{:keys [cleared entries]}]
  (let [named  (->> cleared (filter (comp pos? :entries)) (map :label))
        failed (->> cleared (filter :error) (map :label))]
    (str "Dropped " (commas entries) " entr" (if (= 1 entries) "y" "ies")
         (if (seq named)
           (str " — " (str/join ", " named) ". ")
           " — everything clearable was already empty. ")
         "No belief moved: every entry was derived, and the next read recomputes it."
         (when (seq failed)
           (str " " (str/join ", " failed) " would not clear and "
                (if (= 1 (count failed)) "was" "were") " left as "
                (if (= 1 (count failed)) "it was" "they were") ".")))))

(defn- caches-scale-note
  "What setting the scale changed, above the numbers it moved."
  [scale]
  (str "Cache scale set to " scale ". Every counted cache now holds that multiple of its "
       "shipped bound — the table shows the effective limit each one enforces. 1.0 restores "
       "the shipped bounds, and no belief moved."))

(defn- caches-scale-form
  "The one field that tunes every counted cache at once: a multiplier on the shipped
  bounds, posted as its own origin-checked write like the clear beside it."
  [scale]
  [:form.kb-action {:method "post" :action "/caches/scale"
                    :hx-post "/caches/scale" :hx-target "#main" :hx-select "#main"
                    :hx-swap "outerHTML"}
   [:label "Scale "
    [:input {:type "number" :name "scale" :min "0" :step "0.25" :value (str scale)}]]
   [:button {:type "submit"} "Set scale"]])

(defn- caches-page
  "The cache screen.  `note` is what a clear or a scale change reported, above the numbers
  it changed."
  ([env] (caches-page env nil))
  ([{:keys [kb] :as env} note]
   (let [rows      (v/caches kb)
         permanent (->> rows (remove :clearable?) (map :label) sort)
         ;; the rows whose *rates* are the process's: clearing one of those from here
         ;; zeroes what every other KB's page is reading, which a control offered as a
         ;; per-KB one has to say before it is pressed rather than after
         shared    (->> rows
                        (filter #(and (:clearable? %) (= :process (:counters %))))
                        (map :label) sort)]
     (render env "caches"
             [:h2 "Caches"]
             (when note [:p.problem note])
             [:p.muted "What this process is holding beside the stores. Every row is a "
              "structure the engine keeps so a repeated question is not recomputed, and "
              "the hit rate is the only evidence that it is working."]
             (memory-panel false)
             [:h3 "What is cached"]
             (caches-panel rows)
             [:p.muted "Not listed, because none of it is a cache: the memory of a firing "
              "the chainer refused, the set awaiting a re-check, the disjointness and "
              "negation ledgers, and the reference counts behind the rule index. The engine "
              "cannot recompute them from what is stored, so dropping one would change an "
              "answer."]
             [:h3 "Tuning"]
             [:p.muted "Every counted cache above holds this multiple of its shipped bound. "
              "Below 1 shrinks the caches for a small heap; above 1 grows them for a bulk "
              "load. 1.0 restores the shipped bounds, and VAELII_CACHE_SCALE sets the value "
              "the process starts with. A per-cache floor keeps a small scale from taking a "
              "cache below the point where it saves nothing. This is process-wide: it moves "
              "every KB's caches in this JVM, not only this one's."]
             (caches-scale-form (:scale (v/cache-profile)))
             [:h3 "Clearing"]
             [:p.muted "A clear is a measuring instrument, not an edit: clear, ask the "
              "same question again, and watch the miss the second ask no longer gets to "
              "skip. Nothing is destroyed — every entry is derived — so it is safe while "
              "a load runs, and it is the one control here that does not hold the writer."]
             (when (seq permanent)
               [:p.muted "Left alone: " (str/join ", " permanent)
                ". Those are structural rather than derived-per-question — dropping them "
                "costs the sharing they exist for and buys no measurement, since nothing "
                "counts a hit on them."])
             (when (seq shared)
               [:p.muted "Wider than this KB: " (str/join ", " shared)
                (str (if (= 1 (count shared)) " keeps its rates" " keep their rates")
                     " for the whole process. Clearing here drops this KB's entries "
                     "alone and leaves those counters running — they are a measurement "
                     "every other KB's page is partway through, and zeroing them is "
                     "clear-caches' :counters? option on the API, not this button.")])
             (kb-action "Clear the derived caches" "/caches/clear" {} "primary")
             (profiler-section)))))

(defn- choice-value
  "The keyword a `:choice` field's submitted value names, **refused** when the option does
  not offer it (`:unknown-option`).  Both sides are read through `(comp keyword name)`,
  since a `:choices` entry is a keyword or a string, and `option-control` builds the
  `<option value>` from the same `name`.  Refused, not coerced, for `opts/check!`'s reason:
  an unmatched keyword falls to a reader's default, and `:belief?`'s default is the
  records-only load.  A non-string value refuses the same way."
  [{:keys [key label choices]} raw]
  (let [legal (into #{} (map (comp keyword name first)) choices)
        v     (when (string? raw) (keyword raw))]
    (if (contains? legal v)
      v
      (throw (ex-info (str "no such " (name key) ": " (pr-str raw) " — "
                           (or label (name key)) " offers "
                           (str/join ", " (map (comp name first) choices)))
                      {:type :unknown-option :mismatch :bad-value :option key :value raw
                       :choices (mapv (comp keyword name first) choices)})))))

(defn- option-params
  "The load parameters for `source`, read out of the submitted form under the option
  descriptions the form was rendered from — so a value is coerced by what the option
  said it was, and a field nobody described is ignored.

  A `:choice` is additionally held to the choices the option itself names
  (`choice-value`); the other four kinds carry their domain in the control."
  [source params]
  (into {}
        (keep (fn [{:keys [key type] :as opt}]
                (let [raw (get params (name key))]
                  (case type
                    :flag             [key (some? raw)]
                    (:slider :number) (when-let [n (->long raw)] [key n])
                    :choice           (when (seq raw) [key (choice-value opt raw)])
                    :path             (when (seq raw) [key raw])
                    nil))))
        (:options source)))

(defn kbs-post
  "Perform a catalog action and answer with the page it changed.

  The render env is built **after** the action, not before: activating changes which KB the
  page reads, and rendering the one it was reading a moment ago would show the switch as
  not having happened.  What the catalog refuses — a second concurrent load, a source
  already loaded, an entry whose loader has not yet stopped — comes back as a note on the
  page."
  [act make-env]
  (let [note (try (act) nil
                  (catch clojure.lang.ExceptionInfo e (.getMessage e)))]
    (kbs-page (make-env) note)))

(defn- refuse-a-named-dir!
  "Throw `:path-not-served` when `params` name a `dir` and `catalog/request-paths?` is
  off: the server picks where a store or a dump goes (`catalog/write-root`), and a request
  names no directory.  `route` names the route in the refusal."
  [route params]
  (when (and (not (str/blank? (str (get params "dir")))) (not (catalog/request-paths?)))
    (throw (ex-info (str "a request names no directory for this server to write: " route
                         " writes under " (or (catalog/write-root) "the KB search path") " with a name the server"
                         " picks.  VAELII_REQUEST_PATHS=1 at the server's start lets a"
                         " request name one.")
                    {:type :path-not-served :op route}))))

(defn kbs-load
  "Start loading source `id` with the options the form submitted.  An id the catalog
  holds no source for reaches `load-source` all the same, so its `:unknown-source`
  refusal — which names the ids there are — is the note `kbs-post` puts on the page.
  A `dir` is refused unless `catalog/request-paths?` (`refuse-a-named-dir!`)."
  [id params]
  (refuse-a-named-dir! "/kbs/load" params)
  ;; the one KB write that does not go through this namespace's write monitor, and
  ;; deliberately: a loader opens brand-new stores nothing else can name yet, so there is
  ;; no KB on screen for it to interleave with.  Its `:writes` claim in the job registry
  ;; is what keeps it the only writing job, which is the exclusion that actually matters
  (catalog/load-source id (option-params (catalog/source id) params)))

(defn- entry-action
  "Run `(act key)` for a `/kbs/unload` or `/kbs/activate` on entry `key`, throwing
  `:unknown-entry` when the catalog holds no entry under it — both answer nil for that
  key, which `kbs-post` would render as a page with nothing said.  `verb` names the
  action in the refusal."
  [key act verb]
  (if (catalog/entry key)
    (act key)
    (throw (ex-info (str "No loaded KB has the key " (pr-str key) " — nothing to " verb
                         ". The loaded KBs are the rows under Loaded.")
                    {:type :unknown-entry :key key}))))

(defn- export-choice-refused
  "The first `[param value]` among the export form's choices that names nothing
  `export-choices` offers, or nil.  An empty control is the control not being sent."
  [params]
  (first (for [p ["variant" "compression"]
               :let [raw (get params p)]
               :when (and (seq raw) (not (some #(= raw (first %)) (export-choices p))))]
           [p raw])))

(def ^:private entry-key-legal
  "What a legal `key` looks like on `/kbs/unload` and `/kbs/activate`."
  "the key of a loaded KB, as the rows under Loaded send it")

(defn- export-opts
  "The writer options the export form submitted, as `export!`'s own keywords — and only
  the ones actually named, so the defaults stay the writer's rather than being restated
  by whoever renders the form."
  [params]
  (cond-> {}
    (seq (get params "variant"))     (assoc :variant (keyword (get params "variant")))
    (seq (get params "compression")) (assoc :compression (keyword (get params "compression")))))

;; ---- routing ------------------------------------------------------------

;; The origin check lives in `vaelii.host.guard`, shared with the daemon: both servers
;; are unauthenticated and face the same two attacks, and one of them (DNS rebinding)
;; is invisible to this check alone — see that namespace.  `app` applies the `Host`
;; allowlist that closes it.
(def ^:private same-origin? guard/same-origin?)

(defn- cross-origin-refusal
  "The 403 a cross-origin write gets: plain text, since the caller is not one of our
  own pages and has no use for the chrome."
  []
  {:status  403
   :headers {"Content-Type" "text/plain; charset=utf-8"}
   :body    "cross-origin write refused"})

(defn- origin-checked
  "Wrap the POST handler `f` so a cross-origin request gets `cross-origin-refusal`."
  [f]
  (fn [req] (if (same-origin? req) (f req) (cross-origin-refusal))))

(defn- body-too-large-refusal
  "The 413 an oversized request body gets.  Plain text for `cross-origin-refusal`'s
  reason and one more: nothing on the page can send a body this big, so whatever did
  is not reading our chrome."
  [_req]
  {:status  413
   :headers {"Content-Type" "text/plain; charset=utf-8"}
   :body    (str "request body exceeds " guard/max-body-bytes " bytes")})

(defn- bad-parameter
  "The 400 a request carrying a parameter this page cannot read gets: the parameter named,
  the value quoted, and what would have been legal.  A rendered page, since the caller is a
  reader who edited a URL.  A refusal, not a fallback: a bound that does not parse would run
  the work **unbounded**, and a calculus name nothing answers to would draw a *different*
  calculus."
  [env param value legal]
  (assoc (render env "bad request"
                 [:h2 "Bad request"]
                 [:p "The " [:code param] " parameter is not readable: "
                  [:code (pr-str value)] "."]
                 [:p.muted legal])
         :status 400))

(defn- unsupported-context
  "The 400 a page owes for a `?ctx=` naming a **query context** it cannot resolve.
  `CxEverything` / `CxInference` / `CxNothing` are readings, not places (docs/contexts.md),
  and only four reads resolve one; the levels and the plan go through entry points that
  refuse with `:unsupported-context`, which this handler stack has no middleware to render.
  The page's own context box can send such a value, so it is checked here."
  [env ctx]
  (assoc (render env "bad request"
                 [:h2 "Bad request"]
                 [:p "The " [:code "ctx"] " parameter names a reading rather than a place: "
                  [:code (pr-str ctx)] "."]
                 [:p.muted "This page asks what a context holds, so it needs a context that "
                  "holds something. " (str/join ", " (sort (map str v/query-contexts)))
                  " are the three that do not: each is a way of reading the whole KB, and "
                  "only " [:code "query"] ", " [:code "ask"] ", " [:code "prove"] " and "
                  [:code "sentexes-matching"] " resolve one. Leave it blank for "
                  [:code "?ctx"] ", which asks every context at once."])
         :status 400))

(def ^:private derivations-legal
  "What a legal `max-derivations` looks like, in the words the refusal uses.  One string,
  because `/chain` and `/funnel` submit the same control and a bound that reads differently
  on the two pages would be two promises."
  (str "a whole number of derivations, at least 1 — or leave it out to chain to a "
       "fixpoint. It is the one parameter whose absence is unbounded work, so a value "
       "that does not read as a number is refused rather than dropped."))

(def ^:private unreadable
  "What `param-long` and `param-strength` answer for a parameter that **was** given and is
  not one this page can read.  Distinct from nil, which is a parameter that was not given
  at all: the two differ by whether the route falls back to its default or refuses, and
  collapsing them is what makes a typo indistinguishable from an omission."
  ::unreadable)

(defn- param-long
  "A request parameter as a long in `[lo hi]`: nil when it was not given, `unreadable`
  when it was given as something else.

  `->long` answers nil for both, and the two callers here read nil as \"not given\" — so a
  mistyped bound runs the work with no bound and a mistyped depth takes the default, with
  nothing on the resulting page to say either happened."
  [raw lo hi]
  (if (or (nil? raw) (str/blank? (str raw)))
    nil
    (let [n (when (string? raw) (->long raw))]
      (if (and n (<= (long lo) (long n) (long hi))) n unreadable))))

(defn- param-strength
  "The `strength` a form sent, as the keyword `assert` takes: nil when the control was not
  submitted, `unreadable` for a value the strength class does not name
  (`strength/assertable`, what `core/assert` and the CLI hold a caller to).

  The value is read, not only its presence: `strength=default` asserts at `:default`,
  the form's checkbox sends `monotonic`, and any other value is `unreadable`, which the
  route answers with a 400 naming the parameter."
  [raw]
  (cond
    (nil? raw)                                                nil
    (and (string? raw) (v/assertable-strengths (keyword raw)))  (keyword raw)
    :else                                                     unreadable))

(defn- param-form
  "A request parameter read as EDN: nil when it was not given — absent, or a control
  submitted empty — and `unreadable` when it was given and does not read.  `->form`
  answers nil for both, so a route reading through it takes `(` as the absent value."
  [raw]
  (if (str/blank? (str raw))
    nil
    (let [f (->form raw)] (if (nil? f) unreadable f))))

(defn- param-context
  "A `ctx` parameter: nil when not given, the symbol it names, or `unreadable` for a value
  that does not read or reads as something other than a symbol.  `42` reads, and names no
  context."
  [raw]
  (let [f (param-form raw)]
    (if (or (nil? f) (= unreadable f) (symbol? f)) f unreadable)))

(def ^:private context-legal
  "What a legal `ctx` looks like, for every page that asks a context and treats its absence
  as every context."
  "a context name, e.g. CxWell — or leave it out to ask every context at once (?ctx)")

(def ^:private goal-legal
  "What a legal `q` looks like on the two pages that take a goal."
  (str "a sentence, e.g. (animal ?x), or a vector of them — or leave it out for the empty "
       "form"))

(defn- param-handles
  "A comma-separated `handles` list as a vector of longs, in the order given and without
  repeats — or `unreadable` when any element does not read as a whole number.  Dropping
  that element instead would leave `/edit` a save against fewer handles than the reader
  selected, and a save against none asserts the text as new."
  [raw]
  (let [parts (->> (str/split (str raw) #",") (map str/trim) (remove str/blank?))
        hs    (mapv ->long parts)]
    (if (some nil? hs) unreadable (vec (distinct hs)))))

(def ^:private handles-legal
  "What a legal `handles` looks like."
  "comma-separated sentex handles, e.g. 12,40 — each a whole number")

(defn- history-known
  "Which of the browsing history's entries the render env's KB holds, as JSON
  `{\"complete\": true, \"terms\": [q …], \"handles\": [h …]}`: of the term pages' `qs`,
  each that parses to a term some stored sentex mentions, and of the handles `hs`, each
  naming a stored sentex.  vaelii.js forgets the rest.  The lists are bounded by
  `history-cap`.  **Only once the active KB has stored everything**: a load still running
  or stopped holds a prefix, and the answer is `{\"complete\": false}`.  A KB whose load is
  `:done` and lacks only belief (`catalog/active-caveat`) is judged."
  [{:keys [kb]} qs hs]
  (let [caveat (catalog/active-caveat)
        term?  (fn [q]
                 (let [t (param-form q)]
                   (and (some? t) (not= unreadable t) (some? (first (v/find-sentexes kb t))))))]
    {:status  200
     :headers {"content-type" "application/json"}
     :body    (json/generate-string
               (if (and caveat (not= :done (:status caveat)))
                 {:complete false}
                 {:complete true
                  :terms    (filterv term? (take history-cap qs))
                  :handles  (filterv #(some? (v/sentex kb %)) (take (* 2 history-cap) hs))}))}))

(defn- param-id
  "A `:id` path parameter as a long, or `unreadable`."
  [raw]
  (or (->long raw) unreadable))

(defonce ^:private ^Object write-monitor
  ;; Jetty serves the write routes on a thread pool, and two interleaved writers leave
  ;; `disk/kv.clj`'s WAL holding both frames and the RAM map one (`apply-ops!` publishes
  ;; outside its lock).  The monitor is process-wide, since two catalog entries can share
  ;; a store; docs/web.md names who holds it.  The daemon holds its own (`serve.clj`).
  (Object.))

(defn- after-writes-drain
  "Run `work` once any synchronous write already inside the write monitor has finished: a
  barrier, not a hold (docs/web.md, the export paragraphs)."
  [work]
  (locking write-monitor nil)
  (work))

(defn- refusal-page
  "The page saying nothing was written to the KB `label` names: `reason` follows the name,
  and `advice` is the closing paragraph."
  [env title label reason advice]
  (render env title
          [:h2 "Nothing was written"]
          (into [:p [:b label]] reason)
          (into [:p.muted] advice)))

(defn- exporting-refusal
  "The page refusing a write to `kb` while an export walks it."
  [kb req]
  (refusal-page (render-env kb req) "still exporting" (kb-name kb)
                [" is being exported, and the dump walks the "
                 "records one by one with no snapshot — a write landing mid-walk would "
                 "leave it a dump of no single state."]
                ["Wait for it to finish or cancel it on the "
                 [:a {:href "/kbs"} "knowledge bases"] " page."]))

(defn- late-refusal
  "The page refusing a write that passed `write-refusal` and then waited for the write
  monitor, or nil: `kb` was unloaded (`catalog/released?`) or an export started walking it
  (`catalog/exporting-kb?`) during the wait.  Asked inside the monitor.  `label` is the
  KB's name read before the wait, since an unload drops the entry; the page renders over
  `target`'s current KB."
  [target kb label req]
  (cond
    (catalog/released? kb)
    (refusal-page (env-of target req) "unloaded" label
                  [" was unloaded while this write waited for another writer to "
                   "finish, so its stores are released and this write had nowhere to land."]
                  ["Load it again from the " [:a {:href "/kbs"} "knowledge bases"]
                   " page to write to it."])

    (catalog/exporting-kb? kb)
    (exporting-refusal kb req)))

(defn- late-refusal-type
  "The `:type` and message `late-refusal` stands for, for a caller that answers in EDN or
  fails a job rather than rendering a page: `[:not-found msg]`, `[:still-exporting msg]`,
  or nil."
  [kb label]
  (cond
    (catalog/released? kb)
    [:not-found (str label " was unloaded while this write waited for the write monitor;"
                     " nothing was written")]
    (catalog/exporting-kb? kb)
    [:still-exporting (str label " is being exported; retry when the export finishes")]))

(defn- write-refusal
  "Nil when this request may write `kb`, else the page saying why not: a cross-origin
  request, a job holding this process's writer (named and linked), an export walking `kb`,
  or a KB whose belief was never built (`:unrecovered-kb`).  `kb` is the KB `writing` or
  `writing-job` resolved, and every arm names it (docs/web.md)."
  [kb req]
  (cond
    (not (same-origin? req))
    (cross-origin-refusal)

    (catalog/write-blocked? kb)
    (let [holder (jobs/writer)]
      (refusal-page (render-env kb req) "still writing" (kb-name kb)
                    [" is being written by "
                     (if holder
                       (list [:a {:href "/jobs"} (:label holder) " (job " (:id holder) ")"])
                       "a job")
                     ", and that job is this process's one writer — so this KB can be read while "
                     "it changes, but not changed."]
                    ["Wait for it to finish, cancel it on the "
                     [:a {:href "/jobs"} "jobs"] " page, or switch to another KB on the "
                     [:a {:href "/kbs"} "knowledge bases"] " page."]))

    ;; the reciprocal of `export-entry!`'s still-loading refusal: the dump walks the
    ;; records with no snapshot, so while it runs the KB can be read but not changed —
    ;; the export claims no writer (a load of another KB is none of its business), so
    ;; the job registry cannot answer for it and the catalog is asked directly
    (catalog/exporting-kb? kb)
    (exporting-refusal kb req)

    ;; ...and the caveat banner's second condition, seen from this side.  The banner
    ;; explains an *answer*; this is the same state refusing a *write*, which the engine
    ;; entry point would throw for (`:unrecovered-kb`), refused here so it renders as a page
    ;; rather than as an exception htmx cannot swap.  Asked only of an in-process KB: an
    ;; attached daemon has none of this to report, as with `catalog/active-caveat`.
    :else
    (when-let [hz (when (:records kb) (not-empty (v/write-hazards kb)))]
      (if (:stale-belief hz)
        (refusal-page (render-env kb req) "rebuilding belief" (kb-name kb)
                      [" answers from the reasoning image an earlier engine build "
                       "wrote while its belief is rebuilt under this build, and a write now would "
                       "be checked against the earlier build's belief."]
                      ["Writing resumes when the rebuild finishes, and the banner above "
                       "leaves the page then."])
        (refusal-page (render-env kb req) "not recovered" (kb-name kb)
                      [" is stored but not built: "
                       (if (:no-index hz)
                         "neither its belief network nor its index was rebuilt from the records"
                         "its belief network was never rebuilt from the records")
                       " — so every definitional check would match nothing and pass, and this KB "
                       "would keep a fact it would otherwise refuse."]
                      ["Reading it is fine, which is what the banner above is about. To "
                       "make it writable, run "
                       [:code (if (:no-index hz) "(reindex kb)" "(recover kb)")]
                       " against it, or load it again with belief on from the "
                       [:a {:href "/kbs"} "knowledge bases"] " page."])))))

(defn- writing
  "Run `(f kb)` for a synchronous write to the content of `target`'s KB: `write-refusal`,
  then the write monitor, then `late-refusal` inside it.  The holder is dereferenced once
  and `f` gets that KB.  A write that runs is recorded against the session's sandbox
  (`sandbox/note-write!`).  Not for the registry routes or a job (`writing-job`);
  docs/web.md."
  [target req f]
  (let [kb (current target)]
    (or (write-refusal kb req)
        (let [label (kb-name kb)]
          (locking write-monitor
            (or (late-refusal target kb label req)
                (let [resp (f kb)]
                  (sandbox/note-write! kb (sandbox/context-of req))
                  resp)))))))

(defn- writing-job
  "The same guard for a write that runs as a job: `write-refusal`, then `(f kb wrap)`, where
  `wrap` runs the job's work inside the write monitor on the job's own thread and fails the
  job with `late-refusal-type`'s message when that answers."
  [target req f]
  (let [kb    (current target)
        label (kb-name kb)]
    (or (write-refusal kb req)
        (f kb (fn [work]
                (locking write-monitor
                  (when-let [[ty msg] (late-refusal-type kb label)]
                    (throw (ex-info msg {:type ty})))
                  (work)))))))

(defn- job-answer
  "Start a job (`start`, returning its id) and answer for it.  **The fast path**: a job that
  settles inside `jobs/fast-path-ms` is answered with its result (`done`, given the
  finished job), and only one still running is answered with the jobs screen, so small
  operations get no spinner.  A job that settled by *failing* goes to the screen, where its
  error is written.  When the registry **refuses** the job (another job holds this
  process's writer) the answer is that screen with the refusal as a note naming the job.
  `wait-ms` replaces the fast path for a write the reader watches in place
  (`edit-wait-ms`)."
  ([env start done] (job-answer env start done jobs/fast-path-ms))
  ([env start done wait-ms]
   (try
     (let [j (jobs/wait (start) wait-ms)]
       (if (= :done (:status j))
         (done j)
         (jobs-page env)))
     (catch clojure.lang.ExceptionInfo e
       (jobs-page env (.getMessage e))))))

(def ^:private edit-wait-ms
  "How long a write made from the editor or the assert form is waited for before the
  answer is its job rather than its result.  Longer than `jobs/fast-path-ms`, because the
  reader is looking at the panel the result replaces, and a few sentexes settle well
  inside it on all but the largest KBs."
  5000)

(defn- edit-job
  "Run `work`, a write that renders its own answer, as a job writing `kb`, and return the
  job's id.  The answer rides in the summary's **metadata**: the summary is public (the
  jobs screen and `/op :jobs` print it) and a rendered page is no part of a report.
  `in-monitor` is `writing-job`'s wrapper, so the work holds the write monitor on the
  job's own thread, and the session's sandbox is noted as `writing` notes it."
  [kb req label in-monitor work]
  (jobs/submit {:label label :kind :edit :writes kb :result-url "/jobs"}
               (fn [_progress!]
                 (in-monitor
                  (fn []
                    (let [answer (work)]
                      (sandbox/note-write! kb (sandbox/context-of req))
                      (with-meta {} {:answer answer})))))))

(defn- job-result
  "The answer an `edit-job` rendered, off the finished job `j`."
  [j]
  (:answer (meta (:summary j))))

(defn- editor-job-answer
  "Start an `edit-job` (`start`, returning its id) from the editor panel and answer into
  that panel: the job's own answer when it settles inside `edit-wait-ms`, else a panel
  naming the job, its error when it failed, or the registry's refusal when another job
  holds the writer.  A panel rather than the jobs screen, because the editor is a fixed
  panel over the page and a whole page swapped into it would bury the page."
  [start]
  (let [close [:div.editor-actions [:button#sx-cancel.primary {:type "button"} "Close"]]]
    (try
      (let [j (jobs/wait (start) edit-wait-ms)]
        (case (:status j)
          :done   (job-result j)
          :failed (frag [:div.editor [:h3 (:label j) " failed"]
                         [:p.problem (:error j)] close])
          (frag [:div.editor [:h3 (:label j)]
                 [:p.muted "Still running as " [:a {:href "/jobs"} "job " (:id j)]
                  ". The jobs page follows it; this page shows the change once it is "
                  "reloaded after the job finishes."]
                 close])))
      (catch clojure.lang.ExceptionInfo e
        (frag [:div.editor [:h3 "Not started"] [:p.problem (.getMessage e)]
               [:p.muted "Nothing was written."] close])))))

;; ---- lists: whole-KB lists, each a read job ---------------------------------
;; A list holds one kind of thing across the whole KB.  The walk takes longer than a request
;; on a large corpus, so nothing is read until the list's button is pressed, and then it
;; runs as a job: shown on /jobs, with progress, stopped at its next progress report when
;; cancelled.  It writes nothing, so it claims no writer, and is never interrupted, since
;; an interrupt inside a disk store's read closes the store's file channel.

(def ^:private list-page-size
  "How many rows a list's result page shows before its continuation."
  200)

(def ^:private list-progress-every
  "How many sentexes a list reads between two progress reports, which is also how often
  a cancel can land."
  1000)

(def ^:private list-wait-ms
  "How long a read job's button (a list, the quality report) waits for the job before
  answering with the jobs screen: over a small KB the answer is the result."
  5000)

(defn- defeat-target
  "The handle a `(defeat (sentexHandle H))` sentence names, or nil."
  [s]
  (let [[f [hf h]] s]
    (when (and (= 'defeat f) (= 'sentexHandle hf) (integer? h)) (long h))))

(defn- counted
  "`xs`, calling `(progress! n)` every `list-progress-every` items with how many have
  been read."
  [progress! xs]
  (map-indexed (fn [i x]
                 (when (zero? (mod (inc i) list-progress-every)) (progress! (inc i)))
                 x)
               xs))

(defn- defeat-list
  "Every believed `defeat`: the sentex it takes out of belief and the context it holds in."
  [kb progress!]
  (let [total (v/count-with-functor kb 'defeat)
        tell  #(progress! {:phase :defeats :done % :total total})]
    (tell 0)
    (into [] (comp (keep (fn [s] (when-let [t (defeat-target (:sentence s))]
                                   {:defeat (:id s) :target t :context (:context s)}))))
          (counted tell (v/sentexes-with-functor kb 'defeat {:believed? true})))))

(defn- contradiction-list
  "Every contradiction the last settle left standing: the represented dilemmas
  (`contradictions`) and then the clashes among known-true content (`conflicts`).  Read
  without their grounds, which the rows do not show and which cost a taxonomy walk an
  entry: an hour on a corpus with tens of thousands of clashes, where the two reads
  alone take minutes."
  [kb progress!]
  (progress! {:phase :dilemmas})
  (let [ds (v/contradictions kb nil {:grounds? false})]
    (progress! {:phase :conflicts :dilemmas (count ds)})
    (into (mapv #(assoc % :source :dilemma) ds)
          (map #(assoc % :source :conflict))
          (v/conflicts kb {:grounds? false}))))

(defn- orphan-type-list
  "Every believed unary predicate whose only direct `genl` is `thing`, or which has none,
  `thing` itself aside, sorted by name.  A unary predicate is a member of
  `unary_predicate` or of one of its subtypes.  The members are read off the index
  (`stored-first-args`), one read a subtype and no record fetched, and belief is asked
  (`isa?`) only of a member the genl test keeps."
  [kb progress!]
  (let [terms (into #{} (comp (mapcat #(v/stored-first-args kb %))
                              (filter symbol?)
                              (remove #(or (= 'thing %) (= :variable (v/term-role %)))))
                    (v/specs kb 'unary_predicate))
        tell  #(progress! {:phase :types :done % :total (count terms)})]
    (tell 0)
    (into []
          (keep (fn [t]
                  (let [ups (disj (set (v/direct-genls kb t)) t)]
                    (when (and (empty? (disj ups 'thing)) (v/isa? kb t 'unary_predicate))
                      {:term t :thing? (contains? ups 'thing)}))))
          (counted tell (by-print-key terms)))))

(def ^:private held-kinds
  "The `violations` kinds read off the stored state rather than filed: what the `held`
  list keeps."
  #{:inert-argument :inert-rule :forced-conclusion})

(defn- held-list
  "The stored facts and rules held out of belief for a failed argument constraint, and the
  firings held void at a forced-monotonic conclusion: the `held-kinds` entries of
  `violations`, in its order.  One read with no progress inside it, so a cancel lands when
  it returns."
  [kb progress!]
  (progress! {:phase :held :done 0 :total nil :note "reading the held sentexes and firings"})
  (let [rs (filterv (comp held-kinds :violation) (v/violations kb))]
    (progress! {:phase :held :done (count rs) :total (count rs)})
    rs))

(def ^:private kb-lists
  "Each list by its name in a URL: what its row calls it, what it holds, and the fn
  computing its rows from a KB and a progress fn.  `:stored` is the functor whose stored
  count a page load shows, and `:button` a label other than \"Show\".
  `:zero-empties?` says a stored zero proves the list empty.  Contradictions does not say
  so: `conflicts` also reports inert tuples, which the `contradicts` count leaves out."
  (array-map
   "defeats"
   {:title "Defeats" :rows defeat-list :stored 'defeat :zero-empties? true
    :about "Every believed defeat: the sentex contradiction resolution took out of belief, and the context the defeat holds in."}
   "contradictions"
   {:title "Contradictions" :rows contradiction-list :stored 'contradicts
    :about "Every contradiction the last settle left standing: the represented dilemmas, then the clashes among known-true content that nothing could decide."}
   "orphan-types"
   {:title "Unary predicates without a genl" :rows orphan-type-list
    :about "Every believed unary predicate whose only direct genl is thing, or which has none."}
   "held"
   {:title "Held facts and rules" :rows held-list :button "Scan for held facts and rules"
    :about "Every stored fact and rule held out of belief for a failed argument constraint, and every firing held void at a forced-monotonic conclusion."}))

(defn- list-job
  "Run list `which` over `kb` as a job and return its id.  The rows ride in the summary's
  metadata, as an edit's answer does, so the jobs screen prints a count and not the rows."
  [kb which]
  (let [{:keys [title rows]} (kb-lists which)
        id (promise)
        j  (jobs/submit {:label (str title " in " (kb-name kb)) :kind :list :list which
                         :kb-name (kb-name kb) :kb-owner (job-owner kb) :result-url "/stats"}
                        (fn [progress!]
                          (let [rs (rows kb progress!)]
                            (with-meta {:rows (count rs)
                                        :result-url (str "/lists/result?job=" @id)}
                              {:rows rs}))))]
    (deliver id j)
    j))

(defn- list-row
  "One row of list `which`."
  [env which r]
  (case which
    "defeats"
    [:li (handle-ref env (:target r)) in-cx (term-link env (:context r))
     [:span.muted " · " [:a {:href (str "/sentex/" (:defeat r))} "the defeat"]]]
    "contradictions"
    [:li [:span.tag (name (:source r))]
     (when-let [k (:kind r)] [:span.tag (name k)])
     " " (interpose " ⇄ " (map #(handle-ref env (:handle %)) (:sides r)))]
    "orphan-types"
    [:li (term-link env (:term r))
     (when (:thing? r) [:span.muted " genl thing only"])]
    "held"
    (violation-row env (assoc r :handle (v/handle-of (:kb env) (:sentence r) (:context r))))))

(defn- list-rows
  "One page of a finished list job's rows from `offset`, ending in the continuation that
  fetches the next."
  [env j offset]
  (let [which (:list j)
        rs   (:rows (meta (:summary j)))
        page (subvec rs (min offset (count rs)) (min (count rs) (+ offset list-page-size)))]
    (list
     (map #(list-row env which %) page)
     (when (< (+ offset list-page-size) (count rs))
       (more-rows (str "/lists/rows?job=" (url-enc (:id j)) "&offset=" (+ offset list-page-size))
                  (str "show " (commas (- (count rs) offset list-page-size)) " more"))))))

(defn- list-button
  "The button that runs list `which`."
  [which label]
  [:form {:method "post" :action "/lists/run"}
   [:input {:type "hidden" :name "list" :value which}]
   [:button.primary {:type "submit"} label]])

(defn- latest-list-job
  "The newest job of list `which` over `kb`, matched by `job-owner`, or nil."
  [which kb]
  (first (filter #(and (= :list (:kind %)) (= which (:list %)) (= (job-owner kb) (:kb-owner %)))
                 (jobs/jobs))))

(defn- list-last-run
  "What the last run `j` of a list came to: a link to its rows, or to the jobs screen while
  it runs.  An empty run has no rows to link."
  [j]
  [:p "Last run: "
   (cond
     (not= :done (:status j))    [:a {:href "/jobs"} (name (:status j))]
     (zero? (:rows (:summary j))) "none"
     :else [:a {:href (str "/lists/result?job=" (url-enc (:id j)))}
            (commas (:rows (:summary j))) " rows"])])

(defn- lists-section
  "The whole-KB lists on `/stats`, one table row each.  A `:stored` count is one index read.
  Reading a list fetches records and asks belief, minutes on a corpus, so a page load reads
  none and each row's button runs `list-job`."
  [{:keys [kb]}]
  [:div
   [:h3 "Lists"]
   [:p.muted "Each list holds one kind of thing across the whole KB. On a large KB a list "
    "runs for minutes, so it runs as a " [:a {:href "/jobs"} "job"]
    " and its result is kept for an hour."]
   [:table.stats-table.list-table
    [:thead [:tr [:th "List"] [:th.num "Stored"] [:th "Holds"] [:th]]]
    [:tbody
     (for [[which {:keys [title about stored zero-empties? button]}] kb-lists
           :let [n (some->> stored (v/count-with-functor kb))
                 j (latest-list-job which kb)]]
       [:tr
        [:th title]
        [:td.num (some-> n commas)]
        [:td.muted about]
        [:td
         (if (and zero-empties? (zero? n))
           [:span.muted "none"]
           (list (some-> j list-last-run)
                 (list-button which (cond (= :done (:status j)) "Run again"
                                          button                button
                                          :else                 "Show"))))]])]]])

(defn- list-result-page
  "A list job's result: its rows when it has finished, else where it has got to."
  [env j]
  (let [{:keys [title about]} (kb-lists (:list j))]
    (render env "lists"
            [:h2 title]
            [:p.muted about " Read from " [:b (:kb-name j)] "."]
            (case (:status j)
              :done
              (let [n (:rows (:summary j))]
                (list [:p (commas n) " rows. " [:a {:href "/stats"} "All lists"]]
                      (when (pos? n) [:ul.list-rows (list-rows env j 0)])))
              :failed    [:p.problem (:error j)]
              :cancelled [:p "Cancelled before it finished."]
              [:p "Still " (name (:status j)) ": " [:a {:href "/jobs"} "the jobs page"]
               " follows it, and this page lists the rows once it has finished."])
            (when-not (= :running (:status j))
              (list-button (:list j) "Run again")))))

(defn- list-gone-page
  "The answer for a list job the registry no longer holds."
  [env]
  (render env "lists"
          [:h2 "Lists"]
          [:p "That list's result is gone: a finished job is kept for an hour. "
           [:a {:href "/stats"} "Run it again."]]))

(defn stats-page
  "KB-wide statistics: the headline counts (contexts, types, stored sentexes, the placed
  nogoods and the filed violations), what the last chaining run did and a control to run
  another, a contexts-by-size table, and the filed ledger of dropped derivations
  (`filed-violations`) when non-empty, and the whole-KB lists (`lists-section`).  A page
  load reads no belief and fetches no record.  `clashes?` asks the standing disjointness
  question and `nogoods?` the contradictions the placed nogoods come to
  (`nogoods-section`); each is computed, so neither runs unasked.  `note` is what a
  just-finished run reported."
  ([env] (stats-page env nil false false))
  ([env note] (stats-page env note false false))
  ([{:keys [kb types] :as env} note clashes? nogoods?]
   (let [ctxs    (vec (v/contexts kb))
         ;; the trie's own root count, not the sum of the table below it: a context the
         ;; taxonomy does not know (nothing states a `genlCx` edge for it) holds
         ;; sentexes all the same, and summing the table would quietly lose them
         total   (v/sentex-count kb)
         placed  (v/count-with-functor kb 'contradicts)
         viols   (v/filed-violations kb)
         chain   (v/chain-stats kb)]
     (render env "stats"
             [:h2 "Statistics"]
             note
             ;; size counts and health counts read alike as bare numbers, so split them:
             ;; the health row reddens a non-zero count and an all-clear line says when
             ;; there is nothing to look at
             (let [warn (fn [n] (if (pos? n) "stat-warn" "stat-ok"))]
               (list
                [:div.stats-grid
                 (stat-card "Contexts" (count ctxs))
                 (stat-card "Types" (count @types))
                 (stat-card "Sentexes" total)]
                [:p.stat-caption "Reasoning health"]
                [:div.stats-grid
                 (stat-card "Placed nogoods" placed (warn placed))
                 (stat-card "Violations" (count viols) (warn (count viols)))]
                (when (and (zero? placed) (empty? viols))
                  [:p.health-ok "No nogood is placed and no derivation was dropped."])))
             [:p.muted "Readings about the content (rules that never fire, extent skew, "
              "chain depth, taxonomy coverage, stranded declarations, covered rules and rule "
              "pairs that would clash) are on " [:a {:href "/quality"} "the quality page"] "."]
             ;; a reader who arrived here asking why something is slow wants the process
             [:p.muted "The caches, heap and profiler are on "
              [:a {:href "/caches"} "the caches page"] "."]
             (lists-section env)
             ;; what the rules have actually done, and the one control that makes them
             ;; do more.  A load's derivations and its drops are the two halves of the
             ;; same answer, so the trigger sits beside the ledgers it fills.
             [:h3 "Forward chaining"]
             [:p.muted (:runs chain 0) (if (= 1 (:runs chain 0)) " run" " runs")
              " so far; the last derived " [:b (:derived (:last chain) 0)]
              (when (:truncated? (:last chain)) " and was truncated at the depth bound")
              ". " (count viols) " conclusion" (when (not= 1 (count viols)) "s")
              " dropped for a definitional breach."]
             [:p [:a {:href "/funnel"} "Which rules fired, which refused, and which never did →"]]
             ;; a run over a corpus is minutes long, so it is a job: the cap is what bounds
             ;; it (a fixpoint's agenda grows as it derives, so nothing else does), and a
             ;; run that outlasts the fast path answers with the jobs screen instead
             [:form.chain-form {:method "post" :action "/chain"
                                :hx-post "/chain" :hx-target "#main" :hx-select "#main"
                                :hx-swap "outerHTML"}
              [:button.primary {:type "submit"} "Run forward chaining"]
              [:label.kb-opt [:span " up to "]
               [:input {:type "number" :name "max-derivations" :value 100000
                        :min 1000 :max 100000000 :step 1000}]
               [:span " derivations"]]
              [:span.muted " — join every rule over everything stored, to a fixpoint. It "
               "runs as a job you can watch and stop; a stopped run leaves the conclusions "
               "it had already placed."]]
             [:h3 "Contexts by size " [:span.muted "(stored sentexes per context)"]]
             (if-let [ranked (contexts-by-size kb)]
               [:table.stats-table
                [:thead [:tr [:th "Context"] [:th.num "Sentexes"]]]
                [:tbody (context-count-rows env ranked 0)]]
               [:p.muted (commas (count ctxs)) " contexts — too many to size."])
             ;; the filed ledger, a page at a time.  A row here is one or two whole
             ;; sentences with every subterm linked, so the count that matters is on the
             ;; card above and the list is for seeing what one looks like
             (when (seq viols)
               [:div
                [:h3 "Violations " [:span.muted "(derived conclusions dropped for a definitional breach)"]]
                [:p.muted "Newest first; the ledger itself caps at the most recent 1000."]
                [:ul (violation-rows env 0)]])
             ;; the standing disjointness question, behind a control because it is
             ;; computed on demand rather than filed — see the section below
             (when (or nogoods? (pos? placed))
               (nogoods-section env nogoods? placed))
             (block-tally-section env)
             (exposed-clashes-section env clashes?)))))

;; ---- the health report: `kb-quality` as a page (docs/web.md, "The health report") ----

(def ^:private quality-sections
  "The seven `kb-quality` readings in the order `quality-report` prints them, each with the
  heading the report gives it.  `web_quality_test` compares the two."
  [[:rules        "Rules that never fire"]
   [:extents      "Predicate extent skew"]
   [:chains       "Chain depth over the rule graph"]
   [:taxonomy     "Taxonomy coverage"]
   [:declarations "Argument constraints that constrain nothing"]
   [:subsumption  "Rules another rule already covers"]
   [:clashes      "Contradictions in waiting"]])

(def ^:private quality-remote-note
  "What a reading over an attached daemon says in place of a cancel."
  (str "The daemon runs this reading in its own process, and a cancel here cannot reach "
       "its loop, so the reading runs to its end."))

(defn- quality-job
  "Run `kb-quality` over `kb` as a read job and return its id.  The job claims no writer
  and is never interrupted.  In process, the job's progress fn is the census's
  `:on-progress`, so a cancel throws at the next phase report and no reading is filed.
  Against a daemon the fn does not cross the wire, so the job reports no phase and
  carries `:no-cancel`.  The reading rides in the summary's metadata."
  [kb]
  (let [label  (kb-name kb)
        local? (some? (v/local-kb kb))]
    (jobs/submit (cond-> {:label (str "Quality report on " label) :kind :quality
                          :kb-name label :kb-owner (job-owner kb) :result-url "/quality"}
                   (not local?) (assoc :no-cancel quality-remote-note
                                       :progress {:phase :daemon :done 0
                                                  :note "the daemon reports no phase"}))
                 (fn [progress!]
                   (with-meta {}
                     {:quality (if local?
                                 (v/kb-quality kb {:on-progress progress!})
                                 (v/kb-quality kb))})))))

(defn- quality-jobs
  "The newest finished reading over `kb` (matched by `job-owner`), the newest unsettled
  one, and the newest of any status, each a job or nil."
  [kb]
  (let [o  (job-owner kb)
        js (filterv #(and (= :quality (:kind %)) (= o (:kb-owner %))) (jobs/jobs))]
    {:done    (first (filter #(= :done (:status %)) js))
     :running (first (filter #(#{:running :cancelling} (:status %)) js))
     :last    (first js)}))

(defn- quality-progress
  "Running job `j`'s progress, refreshed by `/quality/progress` until the job settles,
  when that route reloads the page."
  [j]
  [:div#quality-progress (polling "/quality/progress" "1s")
   [:p "A reading is running: " [:a {:href "/jobs"} "job " (:id j)] "."]
   (progress-bar (:progress j))
   (if-let [why (:no-cancel j)]
     [:p.muted why]
     (kb-action "Cancel" "/jobs/cancel" {:id (:id j)}))])

(defn- quality-list
  "One capped list of a reading: its heading, a row per entry, and the `elided` line when
  the map's `total` counts more entries than the list holds."
  [title entries total row]
  (when (seq entries)
    (list [:h3 title]
          [:ul (map row entries)]
          (when (< (count entries) (long total))
            (elided (count entries) (commas total) "the reading caps each list")))))

(defn- quality-rules [env {:keys [total never never-count all-defeated all-defeated-count
                                  fired firings]}]
  (list
   [:p (commas total) " rules: " [:b (commas never-count) " never fired"] ", "
    (commas all-defeated-count) " fired with every conclusion defeated, " (commas fired)
    " live; " (commas firings) " recorded firings in all."]
   [:p.muted "A firing is a currently supported one: a rule whose conclusions were "
    "retracted has no live justification and counts as never fired."]
   (quality-list "Never fired" never never-count #(vector :li (handle-ref env (:handle %))))
   (quality-list "Fired, every conclusion defeated" all-defeated all-defeated-count
                 #(vector :li (handle-ref env (:handle %))))))

(defn- quality-extents [env {:keys [predicates with-extent stored gini buckets heaviest]}]
  (list
   [:p (commas predicates) " predicates, " (commas with-extent) " with an extent, "
    (commas stored) " stored facts, Gini " (format "%.4f" (double gini)) "."]
   [:table.stats-table
    [:thead [:tr [:th "Extent"] [:th.num "Predicates"]]]
    [:tbody (for [[k n] (sort buckets)] [:tr [:td "10^" k] [:td.num (commas n)]])]]
   (when (seq heaviest)
     (list [:h3 "The heaviest"]
           [:ul (for [[p n] heaviest] [:li (term-link env p) " " [:span.muted (commas n)]])]))))

(defn- quality-chains [_ {:keys [functors components cyclic largest rules depths at-least]}]
  (list
   [:p (commas functors) " functors in " (commas components) " components ("
    (commas cyclic) " cyclic, largest " (commas largest) "), over " (commas rules) " rules."]
   [:table.stats-table
    [:thead [:tr [:th "Depth"] [:th.num "Rules"] [:th.num "At least this deep"]]]
    [:tbody (for [[d n] (sort depths)]
              [:tr [:td d] [:td.num (commas n)]
               [:td.num (if-let [f (get at-least d)] (format "%.1f%%" (* 100.0 f)) "—")]])]]))

(defn- quality-taxonomy [env {:keys [names edged root rooted islands]}]
  (if root
    (list [:p (commas names) " type names: " (commas edged) " carry a genl edge, "
           (commas rooted) " reach " (term-link env root) "."]
          [:p [:b (commas islands)] " carry an edge and do not reach the root. "
           [:span.muted "These types sit in islands the root does not reach."]])
    [:p (commas names) " type names, and no genl edge anywhere, so there is no root to "
     "measure reach against."]))

(defn- quality-declarations [env {:keys [total stranded stranded-count typed-thing
                                         typed-thing-count]}]
  (list
   [:p (commas total) " argument declarations: " [:b (commas stranded-count)]
    " name a position their predicate does not have."]
   [:p.muted "Such a declaration constrains nothing. Correct the position, declare the "
    "arity meant, or mark the predicate variable_arity."]
   (quality-list "Stranded" stranded stranded-count
                 #(vector :li (handle-ref env (:handle %))
                          (when-let [m (:message %)] [:span.muted " — " m])))
   (quality-list "Typing a position thing" typed-thing (or typed-thing-count 0)
                 #(vector :li (handle-ref env (:handle %))
                          [:span.muted " — " (commas (:facts %)) " stored facts"]))))

(defn- quality-subsumption [env {:keys [total subsumed subsumed-count]}]
  (list
   [:p (commas total) " rules: " [:b (commas subsumed-count)] " covered by another."]
   [:p.muted "The covering rule fires wherever the covered one does and concludes at least "
    "as much. A pair is a redundancy or a deliberate specialization, and the reading does "
    "not decide which."]
   (quality-list "Covered" subsumed subsumed-count
                 (fn [{:keys [subsumed by substitution context]}]
                   [:li (handle-ref env subsumed)
                    [:div.muted "covered by"] (handle-ref env by)
                    [:div.muted "under " [:code (pr-str substitution)] in-cx
                     (term-link env context)]]))))

(defn- quality-clashes [env {:keys [total pairs pair-count]}]
  (list
   [:p (commas total) " rules: " [:b (commas pair-count)] " pairs would clash if both fired."]
   [:p.muted "No inference is run and no fact is consulted. A pair marked excepted carries "
    "an exceptWhen naming the other's case. A clash that has formed is on "
    [:a {:href "/stats?nogoods=1"} "the statistics page"] "."]
   (quality-list "Pairs" pairs pair-count
                 (fn [{hs :rules :keys [kind context excepted]}]
                   [:li [:span.tag (name kind)] (when excepted [:span.tag "excepted"])
                    in-cx (term-link env context)
                    [:div (handle-ref env (first hs))]
                    [:div.muted "against"]
                    [:div (handle-ref env (second hs))]]))))

(def ^:private quality-bodies
  "Each reading's renderer, `(fn [env reading-map])`."
  {:rules quality-rules :extents quality-extents :chains quality-chains
   :taxonomy quality-taxonomy :declarations quality-declarations
   :subsumption quality-subsumption :clashes quality-clashes})

(defn- quality-page
  "The newest finished `kb-quality` reading over the active KB, one framed region per
  reading in `quality-sections`' order, with the time it finished and the catalog entry it
  read; the progress of a running one; and the control that runs another.  Every figure
  is the reading's, and the page reads the KB only to render a listed handle."
  [{:keys [kb] :as env}]
  (let [label (kb-name kb)
        {:keys [done running last]} (quality-jobs kb)
        q     (:quality (meta (:summary done)))]
    (render env "quality"
            [:h2 "Quality"]
            [:p.muted "Seven readings about the knowledge itself, from " [:code "kb-quality"]
             ". The run ledgers (contradictions, conflicts, violations and the standing "
             "disjointness clashes) are on " [:a {:href "/stats"} "the statistics page"] "."]
            (when running (quality-progress running))
            (when (and last (#{:cancelled :failed} (:status last)))
              [:p.problem "The last run " (name (:status last))
               (when-let [e (:error last)] (list ": " e)) ". It filed no reading."])
            (if q
              (list
               [:p "Read " (local-time (java.time.Instant/ofEpochMilli (:finished done)))
                " from " [:b (:kb-name done)] "."]
               (for [[i [k title]] (map-indexed vector quality-sections)
                     :let [m (get q k)]
                     :when m]
                 (panel (inc i) title ((quality-bodies k) env m))))
              [:p "No reading of " [:b label] " is held. The report reads the vocabulary "
               "and the rules, not every sentex, and runs as a " [:a {:href "/jobs"} "job"]
               "; a finished reading is kept for an hour."])
            (when-not running
              [:form {:method "post" :action "/quality/run"}
               [:button.primary {:type "submit"} (if q "Run again" "Run the report")]]))))

(defn- cached
  "Set the `Cache-Control` header `dev?` chose on a static asset's answer.  A miss (nil) is
  passed straight through, so it still falls to the next handler."
  [handler]
  (letfn [(with-cache-control [r]
            (cond-> r
              (= 200 (:status r))
              (assoc-in [:headers "Cache-Control"] static-cache-control)))]
    (fn
      ([req] (some-> (handler req) with-cache-control))
      ([req respond raise] (handler req #(respond (some-> % with-cache-control)) raise)))))

(def ^:private offset-cap
  "The largest `&offset=` any continuation is read at: a billion rows, past any cursor this
  page writes.  `find-rows-page` asks the term-name set for `offset + find-cap + 1`
  names, and `Long/MAX_VALUE` from a hand-edited URL would overflow the addition.  Capped,
  not refused, since an offset past the end is a cursor that gets the empty page."
  1000000000)

(defn- ->offset
  "An `&offset=` param as a long in `[0 offset-cap]`: 0 when it was not given, the ceiling
  for anything past it, and `unreadable` for a value that is not a whole number 0 or more.
  Reading an unreadable one as the start would answer the first page again, appended to
  the list the reader was scrolling."
  [s]
  (if (str/blank? (str s))
    0
    (let [n (->long s)]
      (if (and n (>= (long n) 0)) (min (long n) offset-cap) unreadable))))

(defn- continued
  "Answer a continuation route: `(f offset)` at the request's `&offset=`, or the empty
  fragment when the offset does not read.  A continuation answers the empty fragment where
  a page answers `bad-parameter`'s 400: htmx swaps only a 2xx, so a 400 would leave the
  sentinel in place to be fetched again on the next scroll, and the empty fragment ends
  the list there."
  [req f]
  (let [off (->offset (get-in req [:query-params "offset"]))]
    (if (= unreadable off) (frag "") (f off))))

(defn- by-id
  "Render `(page env id)` for the request's `:id` path parameter, or `bad-parameter`'s 400
  quoting it when it does not read as a whole number.  An id that reads and names nothing
  stored is the page's own not-found answer, which quotes the number."
  [req target page legal]
  (let [raw (get-in req [:path-params :id])
        id  (param-id raw)
        env  (env-of target req)]
    (if (= unreadable id)
      (bad-parameter env "id" raw (str legal ", a whole number"))
      (page env id))))

(def ^:private loopback
  "The network interface the browser binds unless told otherwise.  It is an operator tool with
  a write route (`POST /edit`) and no authentication, so it answers only the machine it
  runs on; exposing it is an explicit choice (`--listen`), and one that **requires**
  `VAELII_API_TOKEN` (`guard/require-token!`, and `-main` below).

  Loopback says *which machine*, not which page: a page the operator visits runs on
  that machine too, which is what the guards in `vaelii.host.guard` are for."
  "127.0.0.1")

(defn- with-token
  "The handler a **public** bind serves: `served` behind the shared bearer token, with the
  browser's own 401 (`text/plain`).  Only a public bind: `--listen` with an address is the
  one configuration the token is *required* for, so the loopback default is not wrapped.
  `guard/require-token!` has already refused an open start on an address."
  [served host token]
  (if (guard/public-bind? host)
    (guard/wrap-bearer served token #{}
                       (fn [_] {:status  401
                                :headers {"Content-Type" "text/plain; charset=utf-8"
                                          "WWW-Authenticate" "Bearer"}
                                :body    (str "this browser is bound to " host
                                              " and requires Authorization: Bearer"
                                              " <VAELII_API_TOKEN>")}))
    served))

(defonce ^:private op-registry
  ;; The change-feed subscriptions `POST /op` issues.  One registry for the process, as
  ;; `write-monitor` is one monitor for it: a feed token names a subscription held by this
  ;; process.  `defonce` keeps the subscriptions a client holds across a namespace reload,
  ;; which rebuilds `app` and would otherwise drop them.
  (sub/registry))

(defn- edn-reply
  "An EDN response in the daemon's reply shape."
  [status m]
  {:status status :headers {"content-type" "application/edn"} :body (pr-str m)})

(defn- op-catalog
  "The `:kbs` op: the catalog as data — the active entry's key, the heap, and every entry
  with its status, progress and error, plus `:sentexes`, the stored count read live (one
  O(1) read, so it climbs while a load runs).  The footprint estimate is left out: it reads
  the dense network per call (`catalog/footprint`), and an entry's `:source` holds the
  loader's functions."
  []
  {:active  (catalog/active)
   :heap    (catalog/heap)
   :entries (vec (for [e (catalog/entries)
                       :let [kb (:kb (catalog/entry (:key e)))
                             n  (when (:records kb)
                                  (try (v/sentex-count kb) (catch Exception _ nil)))]]
                   (cond-> (dissoc e :source)
                     n (assoc :sentexes n))))})

(def ^:private browser-ops
  "The ops `POST /op` answers beside the daemon's table: the process's own state, which a
  daemon serving one KB has none of.  Each takes no args, and runs whatever the active KB
  is doing — a monitor polling a load reads them while the KB op beside it is refused."
  (let [no-args (fn [op f]
                  (fn [args]
                    (when (seq args)
                      (throw (ex-info (str "op " op " takes no args, got " (pr-str args))
                                      {:type :bad-args :op op})))
                    (f)))]
    {:kbs  (no-args :kbs op-catalog)
     :jobs (no-args :jobs jobs/jobs)}))

(defn- op-post
  "Answer `POST /op` over the active KB with the daemon's own handler (`serve/handle-op`):
  the same op table, guards, ceilings and refusals, under this process's `write-monitor`.
  Two ops are the browser's own (`browser-ops`): `:kbs`, the catalog, and `:jobs`, the job
  registry, which answer in every state below.

  The holder is dereferenced once, as `writing` does, and three states refuse every other
  op before it runs:

    404 :not-found        the browser reads a remote daemon (`--attach`); the op belongs
                          at that daemon
    409 :still-loading    a job is filling this KB; an op would be a second writer
    409 :still-exporting  an export walks the records with no snapshot

  The 409s refuse reads too, since the op table does not mark which ops write.  A
  `:kb-diff` side names a catalog entry by key (`serve/*served-kbs*`).  `handle-op` asks
  `late-refusal-type` once it holds the monitor: a KB released meanwhile answers **404
  `:not-found`**, one an export started walking 409 `:still-exporting`; `:watch` asks it
  too."
  [target req]
  (let [kb     (v/local-kb (current target))
        refuse (fn []
                 (cond
                   (nil? kb)
                   {:status 404 :ok false :type :not-found
                    :error (str "this browser reads a remote daemon (--attach); "
                                "send POST /op to that daemon")}

                   (catalog/write-blocked? kb)
                   {:status 409 :ok false :type :still-loading
                    :error (str (kb-name kb) " is being written by a job; "
                                "retry when the job finishes")}

                   (catalog/exporting-kb? kb)
                   {:status 409 :ok false :type :still-exporting
                    :error (str (kb-name kb) " is being exported; "
                                "retry when the export finishes")}))
        label  (some-> kb kb-name)]
    (binding [serve/*served-kbs* (fn [id] (when (catalog/in-process? id)
                                            (:kb (catalog/entry id))))]
      (serve/handle-op kb op-registry write-monitor req
                       (fn []
                         (when-let [[ty msg] (late-refusal-type kb label)]
                           {:status (if (= :not-found ty) 404 409) :type ty :error msg}))
                       {:ops browser-ops :refuse refuse}))))

(defn- unload-entry!
  "`catalog/unload!` entry `key` under the write monitor, and end the change feeds over the
  KB it released.  A write already inside the monitor finishes first, and one waiting for it
  is refused after the release (`late-refusal`).  Every `/op` subscription whose listener is
  on the released KB is dropped (`sub/unwatch-kb`), so a parked poll answers
  `:unknown-subscription` at once; a `:watch` waiting for the monitor is refused by
  `op-post`'s check.  An entry whose release released nothing (a KB `register!` filed with
  no `:where`) keeps its subscriptions."
  [key]
  (catalog/unload! key {:run-in (fn [work]
                                  (locking write-monitor
                                    (let [kb (:kb (catalog/entry key))]
                                      (work)
                                      (when (catalog/released? kb)
                                        (sub/unwatch-kb op-registry kb)))))}))

(defn- ending-feeds-on-stop
  "`server`, with a listener that drops every `/op` subscription as the server begins to
  stop (`sub/unwatch-all`): each feed listener comes off its KB, and a parked poll answers
  at once instead of holding its thread until `sub/max-wait-ms`.  `op-registry` is the
  process's, so the drop includes subscriptions another server in this process issued.
  The drop does not take `write-monitor`, which a chaining job holds for its whole run."
  ^org.eclipse.jetty.server.Server [^org.eclipse.jetty.server.Server server]
  (.addEventListener server
                     (reify org.eclipse.jetty.util.component.LifeCycle$Listener
                       (lifeCycleStopping [_ _] (sub/unwatch-all op-registry))))
  server)

(defn- extension-reply
  "An extension handler's answer as a ring response: a map carrying `:status` passes
  through, and anything else is hiccup, sent as a fragment."
  [r]
  (if (and (map? r) (contains? r :status)) r (frag r)))

(defn- extension-method
  "One extension route method as a ring handler, with the guard its kind carries: none
  for `:get`, the origin check for `:post`, and `writing` — the origin check, the
  write-refusal states and the write monitor — for `:write`."
  [target kind f]
  (case kind
    :get   (fn [req] (extension-reply (f (env-of target req) req)))
    :post  (origin-checked (fn [req] (extension-reply (f (env-of target req) req))))
    :write (fn [req]
             (writing target req (fn [kb] (extension-reply (f (render-env kb req) req)))))))

(defn- extension-asset
  "A registered extension's stylesheet or script, read off the classpath per request, so
  an edit to one shows on a refresh; the browser's cache header still spares a repeat
  visit the download."
  [resource content-type]
  (when-let [body (some-> (io/resource resource) slurp)]
    {:status  200
     :headers {"Content-Type" content-type "Cache-Control" static-cache-control}
     :body    body}))

(defn- extension-routes
  "The reitit route table for the registry value `exts`: every extension's routes, and its
  stylesheet and script at /ext/<name>.css and /ext/<name>.js.  `:write` is served as a
  POST, since that is the verb that reaches it."
  [target exts]
  (vec
   (concat
    (for [[_ {:keys [routes]}] exts
          [path methods] routes]
      [path (into {} (for [[kind f] methods]
                       [(if (= :write kind) :post kind) (extension-method target kind f)]))])
    (for [[n {:keys [stylesheet script]}] exts
          [resource ext ctype] [[stylesheet ".css" "text/css; charset=utf-8"]
                                [script ".js" "text/javascript; charset=utf-8"]]
          :when resource]
      [(str "/ext/" (name n) ext) {:get (fn [_] (extension-asset resource ctype))}]))))

(defn- extension-handler
  "The ring handler for whatever is registered **now**: the route table is rebuilt when the
  registry value changes and reused while it does not, so a request costs one identity
  check.  Answers nil for a path no extension serves, which `ring/routes` reads as \"try
  the next handler\"."
  [target]
  (let [built (atom nil)]                                   ; [registry value, handler]
    (fn [req]
      (let [exts @extensions]
        (when-not (identical? exts (first @built))
          (reset! built [exts (ring/ring-handler (ring/router (extension-routes target exts)))]))
        ((second @built) req)))))

;; ---- route constructors: what the `app` table repeats -----------------------

(defn- blank-refusal
  "`bad-parameter`'s 400 for the required request parameter `param` when it is absent or
  blank, else nil."
  [target req param legal]
  (let [v (get-in req [:params param])]
    (when (str/blank? v) (bad-parameter (env-of target req) param v legal))))

(defn- kbs-write-route
  "An origin-checked POST that names a catalog entry by the required parameter `param`
  (`legal` says what it should be) and runs `(act req value)`, a thunk, through `kbs-post`."
  [target param legal act]
  (origin-checked
   (fn [req]
     (or (blank-refusal target req param legal)
         (kbs-post (act req (get-in req [:params param])) #(env-of target req))))))

(defn- chain-route
  "A POST that reads `max-derivations` and runs the chaining job as a write job.
  `job-args` follow the monitor in the `chain-job` call; `answer` is `(fn [kb req job])`."
  [target job-args answer]
  (fn [req]
    (let [raw (get-in req [:params "max-derivations"])
          cap (param-long raw 1 Long/MAX_VALUE)]
      (if (= unreadable cap)
        (bad-parameter (env-of target req) "max-derivations" raw derivations-legal)
        (writing-job
         target req
         (fn [kb in-monitor]
           (job-answer
            (render-env kb req)
            #(apply chain-job kb (kb-name kb) cap in-monitor job-args)
            #(answer kb req %))))))))

(defn- continued-route
  "A GET continuation route: `(rows-page env arg… offset)`, each `arg` read off the
  request by one of `arg-fns`."
  [target rows-page & arg-fns]
  {:get (fn [req]
          (continued req #(apply rows-page (env-of target req)
                                 (concat (map (fn [f] (f req)) arg-fns) [%]))))})

(defn app
  "The ring handler for a KB.  Pure `request -> response`.  `target` is what each page
  reads: a KB, a remote access (`v/remote`), or a **holder**, a deref-able yielding either
  (`vaelii.browser.catalog/holder`).  Every handler resolves the holder per request, so
  activating another entry re-points the browser without rebuilding the handler.  This is
  the routing half; `handler` adds the `Host` allowlist, and a test drives `app` directly."
  [target]
  (-> (ring/ring-handler
       (ring/router
        [["/"           {:get (fn [req] (default-page (env-of target req)))}]
         ;; the daemon protocol, over the active KB (`op-post`), so a native client
         ;; connects to this browser as it would to `vaelii.serve`
         ["/health"     {:get (fn [_] (edn-reply 200 {:ok true}))}]
         ["/op"         {:post (fn [req] (op-post target req))}]
         ["/stats"      {:get (fn [req]
                                (stats-page (env-of target req) nil
                                            (some? (get-in req [:query-params "clashes"]))
                                            (some? (get-in req [:query-params "nogoods"]))))}]
         ;; the definitional block tally: a read job, one describe per type, answered with
         ;; the statistics page when it finishes inside `list-wait-ms`
         ["/stats/blocks"
          {:post (origin-checked
                  (fn [req]
                    (let [kb  (current target)
                          env (render-env kb req)]
                      (job-answer env #(block-tally-job kb @(:types env))
                                  (fn [_] (assoc-in (stats-page env) [:headers "HX-Push-Url"]
                                                    "/stats"))
                                  list-wait-ms))))}]
         ;; forward chaining is a write, so POST-only and origin-checked; it runs as a job, labelled
         ;; `(kb-name kb)` because `/kbs/activate` may re-point the holder after `writing-job` resolved it
         ["/chain"      {:post (chain-route target []
                                            (fn [kb req j]
                                              (stats-page (render-env kb req) (chain-note (:summary j)))))}]
         ;; the per-rule breakdown behind the chain headline: which forward rules placed,
         ;; which refused (and why), which never fired.  GET reads the standing ledger;
         ;; POST runs the same chaining job as /chain but lands back here, so the funnel
         ;; fills in front of the reader
         ["/funnel"     {:get  (fn [req] (funnel-page (env-of target req)))
                         :post (chain-route target ["/funnel"]
                                            (fn [kb req _] (funnel-page (render-env kb req))))}]
         ["/funnel/rows" (continued-route target funnel-rows-page)]
         ;; process state beside the store: caches, heap strip, profiler.  The clear is origin-checked
         ;; and not behind `writing`: it changes no belief and holds no writer.  The holder is
         ;; dereferenced once, for `write-refusal`'s reason
         ["/caches"       {:get (fn [req] (caches-page (env-of target req)))}]
         ["/caches/rows"  {:get (fn [_] (frag (caches-panel (v/caches (current target)))))}]
         ["/caches/clear" {:post (origin-checked
                                  (fn [req]
                                    (let [kb (current target)
                                          r  (v/clear-caches kb)]
                                      (caches-page (render-env kb req)
                                                   (caches-clear-note r)))))}]
         ;; a write to the whole process: the scale multiplies every counted cache bound (`v/set-cache-scale`).
         ;; It has no default; an absent, non-finite or negative scale is refused as an unreadable one
         ["/caches/scale" {:post (origin-checked
                                  (fn [req]
                                    (let [kb  (current target)
                                          raw (get-in req [:params "scale"])
                                          n   (some-> raw str str/trim not-empty parse-double)]
                                      (if (and n (Double/isFinite n) (>= (double n) 0.0))
                                        (do (v/set-cache-scale n)
                                            (caches-page (render-env kb req) (caches-scale-note n)))
                                        (bad-parameter (render-env kb req) "scale" raw
                                                       (str "a finite number 0 or more — 1.0 "
                                                            "is the shipped bounds; nothing "
                                                            "changed"))))))}]
         ;; the jobs screen and its stop control, a write to this process's registry: origin-checked,
         ;; not behind `writing`, so a cancel stays reachable while a job runs
         ["/jobs"        {:get (fn [req] (jobs-page (env-of target req)))}]
         ["/jobs/rows"   {:get (fn [_] (frag (jobs-panel true)))}]
         ;; a waiting page's poll: nothing while its read runs, and a reload once it is
         ;; done, which the finished read answers (`inflight/wrap`)
         ["/inflight/poll" {:get (fn [req]
                                   (if (= :running (inflight/status
                                                    (get-in req [:params "id"])))
                                     {:status 204 :headers {} :body ""}
                                     {:status 200 :headers {"HX-Refresh" "true"} :body ""}))}]
         ;; `cancel!` answers whether a run was stopped, not whether the registry still holds the id;
         ;; the note names both falses, which read the same
         ["/jobs/cancel" {:post (origin-checked
                                 (fn [req]
                                   (let [id (get-in req [:params "id"])]
                                     (or (blank-refusal target req "id" "the id of a job on this page")
                                         (jobs-page (env-of target req)
                                                    (when-not (jobs/cancel! id)
                                                      (str "No job " id " to stop — it has "
                                                           "already finished, or its report has "
                                                           "aged out of the registry.")))))))}]
         ;; the loaded KBs and the active one.  The three writes change process state, are
         ;; origin-checked, and rebuild the render env after, since activating changes what it reads
         ["/kbs"          {:get (fn [req] (kbs-page (env-of target req)))}]
         ["/kbs/rows"     {:get (fn [_] (frag (entries-panel true)))}]
         ;; the provisional-KB strip, re-read while a load runs: it speaks for the active KB, takes no
         ;; render env, and answers the empty element once there is nothing to say
         ["/kbs/banner"   {:get (fn [_] (frag (caveat-banner)))}]
         ;; the memory strip, collapsed or expanded — a read of this process rather than
         ;; of a KB, so it takes no render env and swaps only itself
         ["/kbs/memory"   {:get (fn [req]
                                  (frag (memory-panel
                                         (some? (get-in req [:query-params "detail"])))))}]
         ;; a blank id or key is `bad-parameter`'s; one naming nothing the catalog holds is
         ;; the catalog's own refusal, as a note on the page (`kbs-load`, `entry-action`)
         ["/kbs/load"     {:post (kbs-write-route target "id" "the id of a source under Available"
                                                  (fn [req id] #(kbs-load id (:params req))))}]
         ;; the monitor goes in as for export: *releasing* a KB's stores must wait for a synchronous
         ;; write already inside it (`unload-entry!`); a chain holds it, so `unload!` refuses `:still-writing`
         ["/kbs/unload"   {:post (kbs-write-route target "key" entry-key-legal
                                                  (fn [_ k] #(entry-action k unload-entry! "unload")))}]
         ["/kbs/activate" {:post (kbs-write-route target "key" entry-key-legal
                                                  (fn [_ k] #(entry-action k catalog/activate "switch to")))}]
         ;; export writes to the filesystem, not a KB, so it skips `writing`: `export-entry!` refuses
         ;; while a loader writes, `write-refusal`'s exporting arm refuses writes during the walk, and
         ;; `after-writes-drain` drains a synchronous write already past that refusal (docs/web.md)
         ["/kbs/export"        {:post (origin-checked
                                       (fn [req]
                                         (if-some [[p raw] (export-choice-refused (:params req))]
                                           (bad-parameter (env-of target req) p raw
                                                          (str "one of "
                                                               (str/join ", " (map first (export-choices p)))
                                                               " — or leave it out for "
                                                               (ffirst (export-choices p))))
                                           (kbs-post #(do (refuse-a-named-dir! "/kbs/export" (:params req))
                                                          (catalog/export-entry!
                                                           (catalog/active)
                                                           (get-in req [:params "dir"])
                                                           (assoc (export-opts (:params req))
                                                                  :run-in after-writes-drain)))
                                                     #(env-of target req)))))}]
         ;; a backup of a `:pg-snapshot` store: the job holds the writer claim, and the
         ;; write monitor from before its seal to after its dump (`vaelii.browser.backup`)
         ["/kbs/backup"        {:post (kbs-write-route
                                       target "key" entry-key-legal
                                       (fn [_ k]
                                         #(backup/backup-entry!
                                           k {:run-in (fn [work] (locking write-monitor (work)))})))}]
         ["/kbs/export/cancel" {:post (origin-checked
                                       (fn [req] (kbs-post catalog/cancel-export! #(env-of target req))))}]
         ["/kbs/export/rows"   {:get (fn [_] (frag (export-panel)))}]
         ["/vaelii.css" {:get (fn [_]
                                {:status  200
                                 :headers {"Content-Type"  "text/css; charset=utf-8"
                                           "Cache-Control" static-cache-control}
                                 :body    (stylesheet)})}]
         ["/term"       {:get (fn [req]
                                (let [q (get-in req [:query-params "q"])
                                      w (env-of target req)]
                                  ;; `?derived=hide|show` is the reading preference this
                                  ;; request chose; the response carries it forward
                                  (-> (let [t (param-form q)]
                                        (cond
                                          (nil? t)
                                          (render w "term" [:p "Pass ?q=<term>"])
                                          (= unreadable t)
                                          (bad-parameter w "q" q (str "a term, e.g. dog or "
                                                                      "(FruitFn Apple)"))
                                          :else
                                          (term-page w t)))
                                      (remember-derived req))))}]
         ["/closure"    {:get (fn [req]
                                (let [env (env-of target req)
                                      q   (get-in req [:params "q"])
                                      dir (get-in req [:params "dir"])
                                      t   (param-form q)]
                                  (cond
                                    (not (closure-dirs dir))
                                    (bad-parameter env "dir" dir "genls or specs")
                                    (or (nil? t) (= unreadable t))
                                    (bad-parameter env "q" q "a term, e.g. dog")
                                    :else (closure-page env t dir))))}]
         ;; the continuation routes: a capped list ends in a sentinel that fetches its
         ;; next page from here, so every long list is walkable without loading it whole
         ["/term/rows"  {:get (fn [req]
                                (let [q (->form (get-in req [:query-params "q"]))
                                      g (->long (get-in req [:query-params "g"]))]
                                  (if (and (some? q) (some? g))
                                    (continued req #(term-rows-page (env-of target req) q g %))
                                    (frag ""))))}]
         ["/find"       {:get (fn [req]
                                (find-page (env-of target req)
                                           (or (get-in req [:query-params "q"]) "")))}]
         ["/find/rows"  (continued-route target find-rows-page
                                         #(or (get-in % [:query-params "q"]) ""))]
         ;; one level of a hierarchy, fetched when its node is opened.  `rel` is one of
         ;; the two transitivity relations and nothing else — it reaches the index as a
         ;; functor, so it is checked rather than trusted.
         ["/tree/rows"  {:get (fn [req]
                                (let [rel  (->form (get-in req [:query-params "rel"]))
                                      node (->form (get-in req [:query-params "node"]))]
                                  (if (and (subsumption-relations rel) (symbol? node))
                                    (continued req #(tree-rows-page (env-of target req) rel node %))
                                    (frag ""))))}]
         ["/front/rows" (continued-route target front-rows-page #(get-in % [:query-params "section"]))]
         ;; which history entries the KB holds (`t` repeats), so vaelii.js can forget the rest; an
         ;; unreadable `handles` keeps none
         ["/history/known" {:get (fn [req]
                                   (let [t  (get-in req [:query-params "t"])
                                         hs (param-handles (get-in req [:query-params "handles"]))]
                                     (history-known (env-of target req)
                                                    (if (string? t) [t] (vec t))
                                                    (if (= unreadable hs) [] hs))))}]
         ["/history/sentexes" {:get (fn [req]
                                      (let [hs (param-handles (get-in req [:query-params "handles"]))]
                                        (if (= unreadable hs)
                                          (frag "")
                                          (history-sentexes (env-of target req) hs))))}]
         ["/stats/rows" (continued-route target stats-rows-page #(get-in % [:query-params "section"]))]
         ;; the context box can send a value the engine refuses (`CxEverything` is a reading, not a
         ;; place): checked before the read, or `:unsupported-context` reaches Jetty as a 500
         ["/levels"     {:get (fn [req]
                                (let [rq  (get-in req [:query-params "q"])
                                      rc  (get-in req [:query-params "ctx"])
                                      q   (param-form rq)
                                      ctx (or (param-context rc) '?ctx)
                                      env  (env-of target req)]
                                  (cond
                                    (= unreadable q)       (bad-parameter env "q" rq goal-legal)
                                    (= unreadable ctx)     (bad-parameter env "ctx" rc context-legal)
                                    (v/query-contexts ctx) (unsupported-context env ctx)
                                    :else                  (levels-page env q ctx))))}]
         ["/network"    {:get (fn [req]
                                (let [rc    (get-in req [:query-params "ctx"])
                                      ctx   (param-context rc)
                                      calc  (get-in req [:query-params "calc"])
                                      known (into #{} (map :calculus) (v/calculi))]
                                  (cond
                                    (= unreadable ctx)
                                    (bad-parameter (env-of target req) "ctx" rc
                                                   (str "a context name, e.g. CxWell — or "
                                                        "leave it out for the calculi and "
                                                        "their vocabularies"))

                                    ;; `qualitative-network` resolves no query context, as
                                    ;; the levels do not (`unsupported-context`)
                                    (v/query-contexts ctx)
                                    (unsupported-context (env-of target req) ctx)

                                    (and (seq calc) (not (known (keyword calc))))
                                    ;; checked, not fallen back from: the fallback draws a different calculus with nothing on
                                    ;; the page to say so
                                    (bad-parameter (env-of target req) "calc" calc
                                                   (str "one of "
                                                        (str/join ", " (sort (map name known)))))

                                    :else
                                    (network-page (env-of target req) ctx
                                                  (when (seq calc) (keyword calc))))))}]
         ;; the same refusal.  A 400, not the empty fragment: htmx swaps only a 2xx, so the reader keeps
         ;; the list.  An unreadable `ctx` is refused, since `?ctx` would continue another list
         ["/levels/rows" {:get (fn [req]
                                 (let [q   (->form (get-in req [:query-params "q"]))
                                       ctx (or (param-context (get-in req [:query-params "ctx"])) '?ctx)
                                       lvl (->long (get-in req [:query-params "level"]))]
                                   (cond
                                     (= unreadable ctx) (frag "")

                                     (v/query-contexts ctx)
                                     (unsupported-context (env-of target req) ctx)

                                     ;; a level the stack does not have is the unreadable
                                     ;; one's case, not the engine's `:bad-level` for Jetty
                                     ;; to answer as a 500
                                     (and (sequential? q) (some #(= lvl (:level %)) (v/levels)))
                                     (continued req #(levels-rows-page (env-of target req) q ctx lvl %))

                                     :else (frag ""))))}]
         ["/inference"  {:get (fn [req]
                                (let [rq  (get-in req [:query-params "q"])
                                      rc  (get-in req [:query-params "ctx"])
                                      q   (param-form rq)
                                      ctx (param-context rc)
                                      raw (get-in req [:query-params "d"])
                                      d   (param-long raw 1 debug-depth-max)
                                      env  (env-of target req)]
                                  (cond
                                    (= unreadable d)
                                    (bad-parameter env "d" raw
                                                   (str "a depth bound from 1 to "
                                                        debug-depth-max ", the range the "
                                                        "form on this page offers"))
                                    (= unreadable q)   (bad-parameter env "q" rq goal-legal)
                                    (= unreadable ctx) (bad-parameter env "ctx" rc context-legal)
                                    :else
                                    (inference-page env q (or ctx '?ctx)
                                                    (or d debug-depth-default)))))}]
         ;; an id that does not read is `bad-parameter`'s, quoting it; one that reads and
         ;; names nothing stored is the page's own "No sentex #n"
         ["/sentex/:id" {:get (fn [req] (by-id req target sentex-page "a sentex handle"))}]
         ;; the badge menu's controls, fetched on a right-click (vaelii.js)
         ["/sentex-actions" {:get (fn [req]
                                    (let [raw (get-in req [:params "h"])
                                          h   (param-long raw 0 Long/MAX_VALUE)]
                                      (if (or (nil? raw) (= unreadable h))
                                        (bad-parameter (env-of target req) "h" raw
                                                       "the handle of a stored sentex")
                                        (frag (sentex-actions h)))))}]
         ["/why/:id"    {:get (fn [req] (by-id req target why-page "a sentex handle"))}]
         ["/justification/:id" {:get (fn [req] (by-id req target justification-page
                                                      "a justification id"))}]
         ;; the editor: GET renders the textarea, POST applies the save (both htmx fragments for
         ;; #editor).  The completion list is a bounded read off the term-name set.
         ["/complete" {:get (fn [req]
                              (completions-page (env-of target req)
                                                (get-in req [:params "q"])))}]
         ;; an edit preview reads through `preview` on a typing pause, under `writing` (a preview holds
         ;; the writer).  `handles` is read first: an unreadable element is a 400 and takes no writer
         ["/edit/preview" {:post (fn [req]
                                   (let [raw (get-in req [:params "handles"])
                                         hs  (param-handles raw)]
                                     (if (= unreadable hs)
                                       (bad-parameter (env-of target req) "handles" raw
                                                      handles-legal)
                                       (writing target req
                                                (fn [kb]
                                                  (edit-preview-post (render-env kb req) hs
                                                                     (get-in req [:params "text"])))))))}]
         ["/edit" {:get  (fn [req]
                           (let [env  (env-of target req)
                                 raw (get-in req [:params "handles"])
                                 hs  (param-handles raw)
                                 rq  (get-in req [:params "q"])
                                 q   (param-form rq)]
                             (cond
                               (= unreadable hs) (bad-parameter env "handles" raw handles-legal)
                               (= unreadable q)  (bad-parameter env "q" rq "a term, e.g. dog")
                               :else
                               ;; `?q=` opens the editor on a *term*: the sentexes its most
                               ;; direct index reaches, which is what the term page shows
                               ;; first
                               (let [hs (or (seq hs) (seq (term-main-handles env q)))]
                                 (if (seq hs) (frag (edit-panel env hs)) (frag ""))))))
                   :post (fn [req]
                           (let [raw (get-in req [:params "handles"])
                                 hs  (param-handles raw)]
                             (if (= unreadable hs)
                               (bad-parameter (env-of target req) "handles" raw
                                              handles-legal)
                               (writing-job
                                target req
                                (fn [kb in-monitor]
                                  (editor-job-answer
                                   #(edit-job kb req (str "Edit " (count hs) " in " (kb-name kb))
                                              in-monitor
                                              (fn [] (edit-post (render-env kb req) hs
                                                                (get-in req [:params "text"]))))))))))}]
         ;; the form for new knowledge: GET seeds it (`?q=`, `?text=`, `?strength=monotonic`,
         ;; `?copy=<handle>`), POST checks every line and applies them in one `edit`
         ["/assert" {:get  (fn [req]
                             (let [q    (get-in req [:query-params "q"])
                                   ctx  (get-in req [:query-params "ctx"])
                                   text (get-in req [:query-params "text"])
                                   raw  (get-in req [:query-params "copy"])
                                   h    (when raw (param-long raw 0 Long/MAX_VALUE))
                                   env  (env-of target req)]
                               (let [t (param-form q)]
                                 (cond
                                   (= unreadable t)
                                   (bad-parameter env "q" q "a term, e.g. dog")
                                   (= unreadable h)
                                   (bad-parameter env "copy" raw "the handle of a stored sentex")
                                   :else
                                   (let [c (when h (get (removal-rows (:kb env) [h]) h))]
                                     (assert-page
                                      env
                                      (cond-> (assert-seed env t)
                                        c         (assoc :text (:sentence c) :ctx (:context c)
                                                         :monotonic? (= :monotonic (:strength c)))
                                        (seq text) (assoc :text text)
                                        (seq ctx)  (assoc :ctx ctx)
                                        (= "monotonic" (get-in req [:query-params "strength"]))
                                        (assoc :monotonic? true))
                                      nil))))))
                     :post (fn [req]
                             (let [raw (get-in req [:params "strength"])
                                   s   (param-strength raw)]
                               (if (= unreadable s)
                                 (bad-parameter (env-of target req) "strength" raw
                                                (str "one of "
                                                     (str/join ", " (sort (map name v/assertable-strengths)))
                                                     " — the classes an assertion may carry"))
                                 (writing-job
                                  target req
                                  (fn [kb in-monitor]
                                    (job-answer
                                     (render-env kb req)
                                     #(edit-job kb req (str "Assert in " (kb-name kb)) in-monitor
                                                (fn []
                                                  (assert-post (render-env kb req)
                                                               {:text       (get-in req [:params "text"])
                                                                :ctx        (get-in req [:params "ctx"])
                                                                :monotonic? (= :monotonic s)})))
                                     job-result
                                     edit-wait-ms))))))}]
         ;; the non-monotonicity walkthrough: GET renders the sandbox, every step is an origin-checked
         ;; POST rendered from a render env taken after the write (step 1 creates the sandbox).
         ;; `first` is the handle step 1 wrote, `do` names the step; both are read before `writing`
         ["/demo" {:get  (fn [req]
                           (let [raw (get-in req [:params "first"])
                                 f   (param-long raw 0 Long/MAX_VALUE)
                                 env  (env-of target req)]
                             (if (= unreadable f)
                               (bad-parameter env "first" raw demo-first-legal)
                               (demo-page env f))))
                   :post (fn [req]
                           (let [raw (get-in req [:params "first"])
                                 f   (param-long raw 0 Long/MAX_VALUE)
                                 op  (get-in req [:params "do"])]
                             (cond
                               (= unreadable f)
                               (bad-parameter (env-of target req) "first" raw
                                              demo-first-legal)
                               (not (demo-ops op))
                               (bad-parameter (env-of target req) "do" op
                                              (str "one of " (str/join ", " (sort demo-ops))
                                                   " — the steps this page offers"))
                               :else
                               (writing target req
                                        (fn [kb]
                                          (demo-page (render-env kb req)
                                                     (demo-apply kb (:sandbox (render-env kb req))
                                                                 op f)
                                                     (= "restore" op)))))))}]
         ;; the worked examples: GET computes the read-only cards, POST establishes one example's
         ;; premises in the sandbox; the page is built from a render env taken after the write
         ["/reasoning" {:get  (fn [req] (reasoning-page (env-of target req)))
                        ;; an id naming no example would take the writer and write
                        ;; nothing, answering with the page as if it had run
                        :post (fn [req]
                                (let [id (get-in req [:params "id"])]
                                  (if (ex/by-id id)
                                    (writing target req
                                             (fn [kb]
                                               (reasoning-run kb (:sandbox (render-env kb req)) id)
                                               (reasoning-page (render-env kb req))))
                                    (bad-parameter (env-of target req) "id" id
                                                   (str "the id of an example on this page, "
                                                        "e.g. " (:id (first ex/examples)))))))}]
         ;; one card's verdict, which the gallery asks for after it has rendered
         ["/reasoning/verdict"
          {:get (fn [req]
                  (let [env (env-of target req)
                        id  (get-in req [:params "id"])
                        raw (get-in req [:params "ms"])
                        ms  (param-long raw 1 example-retry-ms)
                        ex  (ex/by-id id)]
                    (cond
                      (nil? ex)
                      (bad-parameter env "id" id (str "the id of an example on /reasoning, e.g. "
                                                      (:id (first ex/examples))))
                      (= unreadable ms)
                      (bad-parameter env "ms" raw (str "a deadline in milliseconds, 1 to "
                                                       example-retry-ms))
                      :else
                      (frag (reasoning-verdict env ex (or ms example-ms))))))}]
         ;; discarding a sandbox: the one control that destroys knowledge on purpose, so
         ;; POST-only and origin-checked like every other write, and answering with the
         ;; page it emptied
         ["/sandbox/reset" {:post (fn [req]
                                    (writing target req
                                             (fn [kb]
                                               (let [w (render-env kb req)
                                                     r (sandbox/reset! kb (:sandbox w))]
                                                 (assert-page (render-env kb req)
                                                              {:problems (sandbox-note r)} nil)))))}]
         ;; retraction: GET only **previews** the teardown (it writes nothing, so it is
         ;; safe to reach by navigation); the POST is the destructive half, and goes
         ;; through `writing` like every other write
         ["/retract" {:get  (fn [req]
                              (let [raw (get-in req [:params "handles"])
                                    hs  (param-handles raw)]
                                (cond
                                  (= unreadable hs)
                                  (bad-parameter (env-of target req) "handles" raw
                                                 handles-legal)
                                  (seq hs) (frag (retract-panel (env-of target req) hs))
                                  :else    (frag ""))))
                      ;; a retraction of nothing has no default to fall back on, so an
                      ;; absent list is refused with an unreadable one
                      :post (fn [req]
                              (let [raw (get-in req [:params "handles"])
                                    hs  (param-handles raw)]
                                (if (or (= unreadable hs) (empty? hs))
                                  (bad-parameter (env-of target req) "handles" raw
                                                 handles-legal)
                                  (writing-job
                                   target req
                                   (fn [kb in-monitor]
                                     (editor-job-answer
                                      #(edit-job kb req (str "Retract " (count hs) " in " (kb-name kb))
                                                 in-monitor
                                                 (fn [] (retract-post (render-env kb req) hs)))))))))}]
         ;; the health report: POST runs one as a read job (no writer), the progress fragment polls
         ;; until it settles, and a second run while one runs answers with the page
         ["/quality" {:get (fn [req] (quality-page (env-of target req)))}]
         ["/quality/run"
          {:post (origin-checked
                  (fn [req]
                    (let [kb  (current target)
                          env (render-env kb req)
                          pushed #(assoc-in (quality-page env) [:headers "HX-Push-Url"] "/quality")]
                      (if (:running (quality-jobs kb))
                        (pushed)
                        (job-answer env #(quality-job kb) (fn [_] (pushed)) list-wait-ms)))))}]
         ["/quality/progress"
          {:get (fn [_]
                  (if-let [j (:running (quality-jobs (current target)))]
                    (frag (quality-progress j))
                    {:status 200 :headers {"HX-Refresh" "true"} :body ""}))}]
         ["/lists" {:get (fn [req] (stats-page (env-of target req)))}]
         ["/lists/run"
          {:post (origin-checked
                  (fn [req]
                    (let [kb   (current target)
                          env  (render-env kb req)
                          which (get-in req [:params "list"])]
                      (cond
                        (not (kb-lists which))
                        (bad-parameter env "list" which (str "one of " (str/join ", " (keys kb-lists))))
                        :else
                        (let [j (jobs/wait (list-job kb which) list-wait-ms)]
                          (cond
                            (not= :done (:status j)) (jobs-page env)
                            (zero? (:rows (:summary j)))
                            (assoc-in (stats-page env [:p.health-ok (:title (kb-lists which)) ": none."])
                                      [:headers "HX-Push-Url"] "/stats")
                            ;; the result has a URL of its own, so the address bar says it
                            :else
                            (assoc-in (list-result-page env j) [:headers "HX-Push-Url"]
                                      (str "/lists/result?job=" (url-enc (:id j))))))))))}]
         ["/lists/result"
          {:get (fn [req]
                  (let [env (env-of target req)
                        j   (some-> (get-in req [:params "job"]) jobs/job)]
                    (if (= :list (:kind j))
                      (list-result-page env j)
                      (list-gone-page env))))}]
         ["/lists/rows"
          {:get (fn [req]
                  (let [env (env-of target req)
                        j   (some-> (get-in req [:params "job"]) jobs/job)
                        raw (get-in req [:params "offset"])
                        off (some-> raw str/trim parse-long)]
                    (cond
                      (not (and off (not (neg? off))))
                      (bad-parameter env "offset" raw "a count of rows, e.g. 200")
                      (not (and (= :list (:kind j)) (= :done (:status j))))
                      (frag [:li.muted "That list's result is gone: "
                             [:a {:href "/stats"} "run it again"] "."])
                      :else (frag (list-rows env j off)))))}]
         ;; the removals noted once they were written, newest first; putting one back
         ;; is an assert, so a job like every other write
         ["/removed" {:get (fn [req] (removed-page (env-of target req) nil))}]
         ;; the term bar: GET is the confirmation (a read), POST runs the operation as a job
         ;; the new-name check under a rename or copy panel's name field: a read
         ["/term-op/name"
          {:get (fn [req]
                  (let [env (env-of target req)
                        op  (get-in req [:params "op"])
                        rq  (get-in req [:params "q"])
                        t   (param-form rq)]
                    (cond
                      (not (:named? (term-ops op)))
                      (bad-parameter env "op" op "rename or copy")
                      (or (= unreadable t) (not (symbol? t)))
                      (bad-parameter env "q" rq "a term, e.g. dog")
                      :else (frag (term-op-name-status env op t (param-form (get-in req [:params "to"])))))))}]
         ["/term-op"
          {:get  (fn [req]
                   (let [env (env-of target req)
                         op  (get-in req [:params "op"])
                         rq  (get-in req [:params "q"])
                         t   (param-form rq)]
                     (cond
                       (not (term-ops op))
                       (bad-parameter env "op" op (str "one of " (str/join ", " (keys term-ops))))
                       (or (= unreadable t) (not (symbol? t)))
                       (bad-parameter env "q" rq "a term, e.g. dog")
                       :else (frag (term-op-panel env op t)))))
           :post (fn [req]
                   (let [env (env-of target req)
                         op  (get-in req [:params "op"])
                         rq  (get-in req [:params "q"])
                         t   (param-form rq)
                         raw (some-> (get-in req [:params "to"]) str/trim)
                         to  (when (:named? (term-ops op)) (->form raw))]
                     (cond
                       (not (term-ops op))
                       (bad-parameter env "op" op (str "one of " (str/join ", " (keys term-ops))))
                       (or (= unreadable t) (not (symbol? t)))
                       (bad-parameter env "q" rq "a term, e.g. dog")
                       (and (:named? (term-ops op))
                            (or (not (symbol? to)) (= t to)
                                (not= (v/term-role t) (v/term-role to))))
                       (bad-parameter env "to" raw
                                      (str "a name other than " t " spelled as a "
                                           (name (v/term-role t)) " is"))
                       :else
                       (writing-job
                        target req
                        (fn [kb in-monitor]
                          (job-answer
                           (render-env kb req)
                           #(term-op-job kb op t to in-monitor)
                           (fn [j] (term-op-result (render-env kb req) (job-result j)))
                           edit-wait-ms))))))}]
         ["/removed/restore"
          {:post (fn [req]
                   (let [id (get-in req [:params "id"])]
                     (or
                      (blank-refusal target req "id" "the id of a removal on the removed page")
                      (writing-job
                       target req
                       (fn [kb in-monitor]
                         (job-answer
                          (render-env kb req)
                          #(edit-job kb req (str "Put back a removal in " (kb-name kb))
                                     in-monitor
                                     (fn [] (restore-post (render-env kb req) id)))
                          job-result
                          edit-wait-ms))))))}]])
       ;; what the router did not match falls through: first to the registered
       ;; extensions (`/ext/…`), then to the static assets (the fonts, the logo, vendored
       ;; htmx, the favicons) under resources/public
       (ring/routes
        (extension-handler target)
        (cached (ring/create-resource-handler {:path "/" :root "public"}))
        (ring/create-default-handler)))
      wrap-params
      ;; a page load that reads for longer than `inflight/detach-ms` is answered with a
      ;; waiting page and goes on reading, and a second load of it joins the first
      (inflight/wrap (fn [req e] (inflight-waiting target req e)) sandbox/token-of)
      ;; Outside `wrap-params`, so it runs first: that middleware slurps a form body
      ;; itself and has no ceiling, and this server authenticates nobody — an anonymous
      ;; caller streaming a body is heap it would otherwise spend.  The daemon holds the
      ;; same limit from the same variable (`guard/max-body-bytes`).
      (guard/wrap-body-limit body-too-large-refusal)
      ;; every request carries a session token, minted into a cookie the first time.  It
      ;; only *names* a sandbox — nothing is created until something is written there.
      (sandbox/wrap-session #(current target))))

(defn- unframed
  "Wrap `h` so no other site can frame a page.  `same-origin?` passes a POST a framed
  page sends, since the frame *is* this origin, so a page on another site that frames
  `/kbs` and lays its own content over it gets a click on Unload past the origin check.
  No page here frames another."
  [h]
  (fn [req]
    (some-> (h req)
            (update :headers merge {"X-Frame-Options"         "DENY"
                                    "Content-Security-Policy" "frame-ancestors 'none'"}))))

(defn- with-host
  "Wrap a built handler in the `Host` allowlist for the network interface it is bound to,
  and in `unframed`.

  It wraps **every** route rather than only the writes.  `same-origin?` guards a
  cross-site POST, but it folds under DNS rebinding — where the attacker's page is
  genuinely same-origin with this one — and a rebound page reads the KB as happily as
  it writes to it.  Reading it is what an attacker came for."
  [h host]
  (unframed
   (guard/wrap-host-allowed
    h
    (guard/allowed-hosts host)
    (fn [_] {:status  400
             :headers {"Content-Type" "text/plain; charset=utf-8"}
             :body    "unrecognized Host header"}))))

(defn handler
  "What the browser actually serves: `app` behind the `Host` allowlist, and at an address
  behind the bearer token (`:token`, or `VAELII_API_TOKEN` when the key is absent).  An
  address with no token is refused (`guard/require-token!`)."
  ([target] (handler target {}))
  ([target {:keys [host] :or {host loopback} :as opts}]
   (let [token (if (contains? opts :token) (:token opts) (guard/api-token))]
     (guard/require-token! "browser" host token)
     (with-token (with-host (app target) host) host token))))

(defn- reloading-handler
  "The handler a REPL session serves: what `app` answers, rebuilt whenever the **var** `app`
  changes and reused otherwise.  Jetty holds the ring handler it started with, so
  reloading `vaelii.browser.web` alone would not change what is served; reading `#'app` per
  request makes the new function object rebuild the routes once.  Namespaces `app` merely
  calls go through vars and need no rebuild.  `dev-repl` serves it; `start` and `-main` do
  not."
  [target]
  (let [built (atom nil)]                                   ; [the app fn, the handler it made]
    (fn [req]
      (let [f @#'app]
        (when-not (identical? f (first @built))
          (reset! built [f (f target)]))
        ((second @built) req)))))

(def ^:private hot-reload-dirs
  "The directory `hot-reloading` watches: all of `src`, engine included.

  `vaelii.browser.reload` reloads a changed namespace and every loaded namespace that
  requires it, never redefines a protocol, record or type that exists, and never
  re-evaluates a held namespace.  So an `impl/` edit reaches a running browser without
  disturbing a loaded KB (`the-engine-survives-a-reload` checks every watched file), and
  an edit to a record's definition or a held namespace takes a restart, which every page
  names (`restart-notice`)."
  ["src"])

(defn- hot-reloading
  "Wrap a dev handler so editing a source file under `hot-reload-dirs` shows on the next
  request: `vaelii.browser.reload/wrap-reload` reloads the changed namespaces from disk,
  and `reloading-handler`'s per-request `#'app` read serves the rebuilt routes.  The
  reloader uses tools.namespace, which ships in the `:dev` profile only.  Without it
  building the reloader throws `FileNotFoundException`, and this degrades to `h` and logs
  the reason (as `start-profiler` does): live routes survive and only the file watching is
  lost."
  [h]
  (try (reload/wrap-reload h {:dirs hot-reload-dirs :busy? #(seq (jobs/running))})
       (catch Throwable t
         (trove/log! {:level :warn :id ::hot-reload
                      :msg (str "hot reload is on but tools.namespace is not on the classpath — "
                                "serving without hot reload (it ships in the :dev profile, "
                                "which `lein browser` activates and a served jar does not): "
                                (.getMessage t))})
         h)))

(defn- kb-file-mtimes
  "`{path modified}` for each `.txt` file of the shipped `kb/upper/` and `kb/middle/`
  layers, read off the classpath where it is a directory; a jar's files never change."
  []
  (into (sorted-map)
        (for [layer ["upper" "middle"]
              :let  [r (io/resource (str "kb/" layer))]
              :when (and r (= "file" (.getProtocol r)))
              ^java.io.File f (.listFiles (io/file r))
              :when (str/ends-with? (.getName f) ".txt")]
          [(.getPath f) (.lastModified f)])))

(defn- kb-file-syncing
  "Wrap a dev handler so the shipped KB files and the loaded KBs follow each other.

  **Files to KBs.**  The first request after a file under `kb/upper/` or `kb/middle/` is
  saved, added or removed submits `catalog/sync-loaded!` as a job the KB page lists.  While
  another job holds the writer the change stays pending for a later request.

  **The starter to the files.**  After each non-GET request, what the starter entry holds
  in its exact contexts is compared with the last reading (`catalog/write-back!`), and the
  difference is written into the files.  No comparison runs while a job holds the writer,
  and a finished sync job takes a fresh reading, so a sync's own writes are not written
  back."
  [h]
  (let [st   (atom {:seen (kb-file-mtimes)})
        lock (Object.)
        busy (fn [e] (if (= :job-busy (:type (ex-data e))) nil (throw e)))]
    (fn [req]
      (locking lock
        (let [{:keys [seen job]} @st]
          (when (and job (not (#{:running :cancelling} (:status (jobs/job job)))))
            (swap! st assoc :job nil :base (catalog/held-premises "starter")))
          (let [now (kb-file-mtimes)]
            (when (and (nil? (:job @st)) (not= seen now))
              (try (swap! st assoc :seen now :job (catalog/sync-loaded!))
                   (catch clojure.lang.ExceptionInfo e (busy e)))))))
      (let [resp (h req)]
        (locking lock
          (let [{:keys [base job]} @st]
            (when-not (or job (jobs/writer))
              (if (nil? base)
                (swap! st assoc :base (catalog/held-premises "starter"))
                (when (not= :get (:request-method req))
                  (when-let [[now report] (catalog/write-back! "starter" base)]
                    (swap! st assoc :base now)
                    (when report
                      (trove/log! {:level :info :id ::kb-files-written
                                   :data {:written (:written report)
                                          :skipped (mapv :form (:skipped report))}}))))))))
        resp))))

(defn start
  "Start a Jetty server for `target` (a KB, an access value, or a catalog holder).
  Returns the server (non-blocking).  `:host` defaults to loopback; pass an address
  (`\"0.0.0.0\"`) to bind publicly, which requires a token: `:token`, or
  `VAELII_API_TOKEN` when the key is absent, as `-main` requires it
  (`guard/require-token!`).  It serves `app` as built: a reload does not reach
  it (`dev-repl` is the server that follows one), and `:reload?` is refused.  `.stop`
  drops every `/op` feed subscription (`ending-feeds-on-stop`)."
  [target {:keys [port host] :or {port 3000 host loopback} :as opts}]
  (when (contains? opts :reload?)
    (throw (ex-info (str "start takes no :reload? — a served browser never reloads; "
                         "scripts/start-vaelii-dev.sh runs the one that does")
                    {:type :unknown-option :mismatch :unknown-key :unknown [:reload?]
                     :options [:host :port :token]})))
  (ending-feeds-on-stop
   (jetty/run-jetty (handler target (assoc opts :host host))
                    {:port port :host host :join? false})))

(defn fresh-starter-kb!
  "A KB freshly loaded with the starter ontology.  Flushes the record + index
  stores first, so a repeated run (or one over data from an earlier code version)
  starts from a clean, deterministic state rather than re-asserting over stale
  handles.  The `vaelii.starter.dump` system property names a directory to restore the
  starter from (`starter/load-through-dump`); a blank value is unset.  For a persistent
  KB, construct one and call `core/recover` instead."
  ([] (fresh-starter-kb! {}))
  ([opts]
   ;; :recover? false — `open` clears the stores, so the unrecovered-store warning would
   ;; fire about data this fn exists to discard
   (let [open #(doto (v/open-kb (merge {:recover? false} opts)) v/clear!)]
     (if-let [root (some-> (System/getProperty "vaelii.starter.dump") str/trim not-empty)]
       (starter/load-through-dump open root)
       (doto (open) starter/load-into)))))

(defn- opening-kb
  "The KB the browser opens on, **registered with the catalog** and made active: the
  starter, or with `attach` (a `[host port]`) a running daemon.  The starter opens over a
  space of its own, after `unload-entry!` takes down the starter an earlier call filed.

  Answers `{:kb :entry :target}`, and the `:target` is the catalog **holder** rather than
  the KB — the browser reads whichever entry is active, so loading another one in the UI
  and switching to it re-points every page with no restart.  Shared by `-main` and
  `dev-repl` so the two cannot open on different things."
  [attach]
  (if attach
    (let [kb (apply v/remote attach)]
      {:kb     kb
       :entry  (catalog/register! "daemon" (str "Daemon " (first attach) ":" (second attach)) kb)
       :target (catalog/holder kb)})
    (let [active? (= "starter" (catalog/active))
          _       (when (catalog/entry "starter") (unload-entry! "starter"))
          where   {:backend :memory :space (catalog/claim-space!)}
          kb      (fresh-starter-kb! where)
          entry   (catalog/register! "starter" "Starter ontology" kb
                                     {:source (catalog/source "starter") :where where})]
      (when active? (catalog/activate entry))
      {:kb kb :entry entry :target (catalog/holder kb)})))

(defn- default-port
  "The port to bind when nothing on the command line names one: `VAELII_WEB_PORT`, else the
  `vaelii.web.port` system property (the env-then-property shape of `vaelii.kb.path`,
  docs/catalog.md; a JVM cannot change its own environment, so a test sets the property),
  else 3000.  `-main` and `dev-repl` both read it.  An unparseable value, or a number
  outside 0–65535, is logged at `:warn` naming the source and falls through to the next
  source."
  []
  (let [num (fn [source s]
              (let [n (try (some-> s str/trim Long/parseLong)
                           (catch NumberFormatException _ nil))]
                (if (and n (<= 0 n 65535))
                  (int n)
                  (when-not (str/blank? s)
                    (trove/log! {:level :warn :id ::bad-port
                                 :msg (str source " is " (pr-str s) ", which is not a port"
                                           " (0–65535); read the next source instead")})
                    nil))))]
    (or (num "VAELII_WEB_PORT" (System/getenv "VAELII_WEB_PORT"))
        (num "vaelii.web.port" (System/getProperty "vaelii.web.port"))
        3000)))

(defn- load-kb-dir
  "Start loading the KB directory `VAELII_KB_DIR` names, with belief recovered, as a
  catalog job that becomes the active KB when it finishes.  Returns the entry key, or nil
  when the variable is unset or blank.

  The browser opens on the starter and serves while the load runs, so `/kbs` shows the
  load's progress.  A path holding no KB is logged at `:warn` and the browser stays on the
  starter, since a startup variable naming the wrong directory should not stop the browser
  from starting."
  []
  (when-let [dir (some-> (System/getenv "VAELII_KB_DIR") str/trim not-empty)]
    (try
      (let [key (catalog/load-dir dir {:recover? true})]
        (trove/log! {:level :info :id ::kb-dir
                     :msg (str "loading " dir " (VAELII_KB_DIR) as " key)
                     :data {:dir dir :key key}})
        key)
      (catch clojure.lang.ExceptionInfo e
        (trove/log! {:level :warn :id ::kb-dir
                     :msg (str "VAELII_KB_DIR " dir " was not loaded: " (ex-message e))
                     :data (assoc (ex-data e) :dir dir)})
        nil))))

(defn- parse-args
  "`-main`'s options, in any order:

    --listen HOST            interface to bind (default loopback)
    --port N                 web port (default VAELII_WEB_PORT, else 3000)
    --attach HOST PORT [WEBPORT]   read a running daemon instead of an in-process KB

  `--attach`'s third argument is positional and taken only when it is a bare number.  A
  flag missing its value, a non-numeric number, or an unknown token is refused
  (`:unknown-option`), since a nil `--listen` host would bind **every** interface with the
  Host allowlist off."
  [args]
  (let [need (fn [flag v]
               (or v (throw (ex-info (str flag " needs a value and the line ends after it"
                                          " — write --listen <address>, --port <n>, or"
                                          " --attach <host> <port> [<webport>]")
                                     {:type :unknown-option :mismatch :missing-value :flag flag}))))
        num  (fn [flag v]
               (let [v (need flag v)]
                 (try (Integer/parseInt ^String v)
                      (catch NumberFormatException _
                        (throw (ex-info (str flag " wants a number, got " (pr-str v)
                                             " — write " flag " <n>")
                                        {:type :unknown-option :mismatch :bad-value :flag flag :value v}))))))]
    (loop [[a & more] (seq args)
           opts       {:host loopback :port (default-port)}]
      (case a
        nil        opts
        "--listen" (recur (rest more) (assoc opts :host (need "--listen" (first more))))
        "--port"   (recur (rest more) (assoc opts :port (num "--port" (first more))))
        "--attach" (let [[h p w & r] more
                         wport? (and w (re-matches #"\d+" w))]
                     (need "--attach" h)
                     (recur (if wport? r (when w (cons w r)))
                            (cond-> (assoc opts :attach [h (num "--attach" p)])
                              wport? (assoc :port (Integer/parseInt w)))))
        (throw (ex-info (str "unknown argument: " a " — the browser reads --listen"
                             " <address>, --port <n>, and --attach <host> <port>"
                             " [<webport>]")
                        {:type :unknown-option :mismatch :unknown-key :flag a}))))))

;; ---- the browser, inside a REPL -----------------------------------------
;; `lein browser` is `lein repl` with the browser running and a **reload channel**: nREPL
;; on loopback, so an editor can reload a namespace into the running server through
;; `.nrepl-port`.  `lein run -m vaelii.browser.web` starts no nREPL and serves a handler
;; value Jetty already holds, which is why `start` takes `:reload?`.  Both halves bind the
;; **loopback interface**, since the browser has a write route and no authentication and an
;; nREPL is arbitrary code execution; exposing the browser is `--listen` on `-main`.

(defonce ^{:private true
           :doc "The server `dev-repl` started, so a second call replaces it rather than
  colliding on the port, and `dev-stop` can find it.  `defonce` (which is why the
  docstring is metadata), so reloading this namespace — the whole point of the session —
  does not lose the handle to the server it is reloading into."}
  dev-instance
  (atom nil))

(defn dev-stop
  "Stop the server `dev-repl` started.  No `!`: it takes down a socket, not knowledge —
  the KB is untouched and still at the prompt."
  []
  (when-let [s @dev-instance]
    (.stop ^org.eclipse.jetty.server.Server s)
    (reset! dev-instance nil)
    :stopped))

(defn- dev-handler
  "What `dev-repl` serves: `reloading-handler`, so a namespace reloaded through the nREPL
  reaches the server, and with `VAELII_DEV` set — which only `scripts/start-vaelii-dev.sh`
  sets — the file-watching reloader over it (`hot-reloading`) and the shipped KB file sync
  under that (`kb-file-syncing`).  Nothing else turns hot reload on: `start` and `-main`
  serve `app` as built."
  [target]
  (cond-> (reloading-handler target)
    ;; outermost first: the sources reload, then a changed KB file syncs with the
    ;; reloaded loader
    (v/switch-value "VAELII_DEV") (-> kb-file-syncing hot-reloading)))

(defn- console-logging!
  "Install the engine's console backend at `:info` (`vaelii.core/set-log-level`) when no
  level is set.  Its lines read `HH:mm:ss message`, where Trove's own backend prints the
  ISO instant, namespace, coordinates and id before the message and a `data:` line after
  it.  A level `VAELII_LOG_LEVEL` set at load is left as it is."
  []
  (when-not (v/log-level) (v/set-log-level :info)))

(defn dev-repl
  "Start the browser for a REPL session and hand the prompt straight back.

  What `lein browser` calls, and the only thing `project.clj` names.  Port from
  `VAELII_WEB_PORT`, else 3000 — the same read `-main` does; loopback only.  A port
  already in use is **reported, not thrown** — you asked for a REPL and you get one
  either way, which is the difference between a busy port being an inconvenience and
  being a failed startup.  A refusal to release the earlier starter leaves the running
  server up."
  []
  (console-logging!)
  (let [port (default-port)
        {:keys [target]} (opening-kb nil)]
    (dev-stop)
    (start-extensions)
    ;; the profiler ships in the `:repl` profile, which is the one `lein browser`
    ;; activates — so this is the entry point where `VAELII_PROFILER` can actually find
    ;; the class, and the caches page links to whatever it started
    (start-profiler)
    (try
      (reset! dev-instance
              (ending-feeds-on-stop
               (jetty/run-jetty (with-host (dev-handler target) loopback)
                                {:port port :host loopback :join? false})))
      (load-kb-dir)
      (println (str "\n  vaelii browser  http://" loopback ":" port
                    "  (loopback only)\n"
                    (if (v/switch-value "VAELII_DEV")
                      "  edit a file under src and refresh — the change is served, no restart\n"
                      "  hot reload is off (scripts/start-vaelii-dev.sh turns it on)\n")
                    "  stop it with    (vaelii.browser.web/dev-stop)\n"))
      (catch java.io.IOException e
        (println (str "\n  the browser did not start on " loopback ":" port
                      " — " (ex-message e) "\n"
                      "  the REPL is yours regardless; retry with"
                      " (vaelii.browser.web/dev-repl) on a free port"
                      " (VAELII_WEB_PORT).\n"))
        nil))))

(defn -main
  "Serve the browser.

    lein run -m vaelii.browser.web                            ; a fresh starter-loaded in-process KB
    lein run -m vaelii.browser.web --port 8080
    lein run -m vaelii.browser.web --listen 0.0.0.0           ; reachable off-machine (opt-in)
    lein run -m vaelii.browser.web --attach HOST PORT [WEBPORT]

  `--attach` renders the KB a running daemon (`vaelii.host.serve`) owns *over the API*
  (docs/operations.md).  The bind decides the requirement (`guard/require-token!`):

  - a **non-loopback** `--listen` address ⇒ `VAELII_API_TOKEN` is **required**, presented
    as `Authorization: Bearer <token>`; without one it is a stderr line and exit **2**;
  - **Loopback**, the default, needs no token.

  The KB it starts on is **registered with the catalog** and made active, so it appears in
  `/kbs` as entry number one."
  [& args]
  (console-logging!)
  (let [{:keys [host port attach]} (try (parse-args args)
                                        (catch clojure.lang.ExceptionInfo e
                                          (binding [*out* *err*] (println (ex-message e)))
                                          (System/exit 1)))
        token (guard/api-token)
        ;; before the KB is opened, which takes a directory's single-writer lock: a
        ;; server that is going to refuse to serve must not first take a lock off the
        ;; process that could have.  The daemon orders it the same way, for the same
        ;; reason (`vaelii.host.serve`).
        _     (try (guard/require-token! "browser" host token)
                   (catch clojure.lang.ExceptionInfo e
                     (binding [*out* *err*] (println (ex-message e)))
                     (System/exit 2)))
        {:keys [kb entry target]} (opening-kb attach)]
    (trove/log! {:level :info :id ::start
                 :msg  (str "vaelii web browser on http://" host ":" port
                            (when attach (str " → daemon " (first attach) ":" (second attach))))
                 :data (cond-> {:listen host :port port :entry entry
                                ;; the same question the bind rule asks, so a
                                ;; `--listen localhost` counts as the loopback bind it is
                                :exposed? (guard/public-bind? host)
                                :kb-search-path (catalog/search-path)}
                         (not attach) (assoc :record-store (type (:records kb))
                                             :index-store  (type (:index kb))))})
    ;; A public bind reaches write routes (two of which, /kbs/export and /kbs/load, write
    ;; the host filesystem at a path the request names) over a plaintext wire, and drops the
    ;; Host allowlist unless `VAELII_ALLOWED_HOSTS` names one.  The required token is not
    ;; TLS and not a Host allowlist, so the line names what it still does not cover.
    (when (guard/public-bind? host)
      (let [open? (guard/allowlist-open? (guard/allowed-hosts host))]
        (trove/log! {:level :warn :id ::public-bind
                     :msg (str "browser bound to " host " — every request must carry "
                               "Authorization: Bearer <VAELII_API_TOKEN>, the wire is "
                               "plaintext (terminate TLS in a reverse proxy)"
                               (if open?
                                 ", and every Host header is answered"
                                 "; VAELII_ALLOWED_HOSTS bounds the Host headers"))
                     :data {:host host :hosts (if open? :open :allowlisted)}})))
    ;; whatever the registered extensions start: a hook that must not delay the bind
    ;; starts its own thread
    (start-extensions)
    ;; the same call `dev-repl` makes, so the variable means one thing to both entry
    ;; points.  Here the class is normally absent — it ships in the `:repl` profile — and
    ;; `start-profiler` says so in the log rather than failing the start
    (start-profiler)
    ;; shrink the derived caches when the heap fills and grow them back as it frees, over
    ;; every KB this process has open (`catalog/live-kbs`)
    (catalog/install-memory-guard!)
    ;; the KB directory `VAELII_KB_DIR` names loads as a job while the starter serves
    (load-kb-dir)
    ;; a served process never reloads: hot reload is `dev-repl`'s, under
    ;; `scripts/start-vaelii-dev.sh`, and this handler pays nothing for one
    (let [served (app target)]
      (jetty/run-jetty (with-token (with-host served host) host token)
                       {:port port :host host :join? true}))))
