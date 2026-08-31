;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.web
  "A small reitit-ring web browser over a KB:

    /                 the upper ontology (contexts, types, core predicates, disjointness)
    /stats            KB-wide counts, contexts by size, and the reasoning-health ledgers
    /find?q=<pattern> the terms whose name matches, from the index's term roster
    /term?q=<term>    every sentex containing the term, grouped by the index root that
                      reaches it (functor / argument-position / context / term-index)
    /sentex/:id       a sentex (literal or rule): its belief state (IN, or the why-not
                      reason — superseded / defeated / unsupported), supports, dependents
    /justification/:id    a justification: its supports (arguments) and dependent sentex
    /levels?q=<goal>  the lookup-to-query stack: what each of the 8 levels answers
    /edit             the multi-sentex editor (GET seeds it, POST saves) — a fragment
    /{term,find,levels}/rows   one more page of a capped list, as bare rows

  Run it with `lein run -m vaelii.impl.web` (serves a starter-loaded KB on :3000).
  Handlers are pure `request -> response`, so they are testable without a server.

  Every page is answered twice over: as a whole document, and — when htmx asks, which
  is every navigation and search — as the `#main` fragment that actually lands.  What a
  page costs in KB reads is part of what this demonstrates, since the browser reads the
  public surface alone and each read is a round-trip under `--attach`; see the `view`
  section below and docs/web.md."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.string :as str]
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
            [vaelii.impl.access :as v]
            ;; the KB catalog: what this process can load, what it has loaded, and which
            ;; of those is active.  The browser is the thing that drives it (`/kbs`), and
            ;; reads the active KB through a holder rather than holding one itself.
            [vaelii.impl.catalog :as catalog]
            ;; the build's switches, read against their domains — `VAELII_DEV` here
            [vaelii.impl.config :as config]
            [vaelii.impl.examples :as ex]
            ;; English composed from the KB's own comments, for the guided level.  Like
            ;; `llm` below it is an application over the engine rather than an internal —
            ;; and unlike it, it reaches no model at all.
            [vaelii.impl.gloss :as gloss]
            ;; the origin/Host checks this page and the daemon both hold to
            [vaelii.impl.guard :as guard]
            ;; the registry every long operation runs in — a load, an export, a chaining
            ;; run.  Process state rather than a KB read, so it is not a hole in the ledger
            ;; below: it reads no KB and writes none.
            [vaelii.impl.jobs :as jobs]
            ;; one read, `write-hazards`: whether the KB on screen is one whose belief was
            ;; never built, which the write guard below refuses on and `active-caveat`
            ;; already reports the read half of
            [vaelii.impl.kb :as kb]
            ;; the proposal panel on a term page.  `llm` is an application over the
            ;; engine exactly as this namespace is — a peer, not an internal — so
            ;; reaching it is not a hole in the ledger below; it never writes, and it
            ;; is reached from one route.
            [vaelii.impl.llm.provider :as llm-provider]
            ;; and the editable line format the proposal panel and this editor share —
            ;; one owner, because the two diff each other's lines by content
            [vaelii.impl.llm.selection :as selection]
            [vaelii.impl.llm.session :as llm]
            [vaelii.impl.llm.verdict :as verdict]
            ;; one read, `query-contexts`: the three reading modes that wear a context's
            ;; spelling, so the refusal a page owes for one names them off the roster
            ;; rather than restating it.  A spelling roster and no KB read, so it is not
            ;; a hole in the ledger below either
            [vaelii.impl.naming :as nm]
            [vaelii.impl.sandbox :as sandbox]
            [vaelii.impl.starter :as starter]
            ;; one read, `assertable?`: the strength class the assert form's control is
            ;; held to, so the page refuses what `core/assert` would refuse rather than
            ;; reading any value at all as "known-true"
            [vaelii.impl.strength :as strength]
            ;; the inline-SVG primitives the term page's concept graph is drawn with.
            ;; Pure geometry — it takes no KB and reads nothing, so it is not a hole in
            ;; the ledger below either.
            [vaelii.impl.svg :as svg]))

;; The browser reads the KB through `vaelii.core` alone — it reaches into **zero**
;; engine internals, so it is the standing proof that the public surface is complete
;; enough to build a real client on.  The reads it once took from `impl` are now public:
;;
;;   `term-role`         the naming role of a term, for coloring (was naming/*)
;;   `readable-sentence` a stored rule with the author's variable names (was sentex/originalize)
;;   `indexable-terms`   a sentex's findable subterms (was sentex/index-terms)
;;   `disjoint-metatypes` / `metatype-members`  the induced disjointness (was taxonomy/*)
;;   `clear!`            the backend-agnostic store wipe `fresh-starter-kb!` needs (was protocols/*)
;;
;; The one `impl` require left is `starter` — the demo ontology `-main` loads.  That is
;; *content*, not engine, so it is not a hole; a different app would load its own.  Keep
;; this ledger honest: a new `impl` reach here is a new gap in `vaelii.core` to close.

;; ---- rendering ----------------------------------------------------------
;;
;; Every page is built with `hiccup2.core/html`, which **escapes strings in body
;; position** as well as in attributes.  That is what makes KB content safe to render:
;; a Clojure symbol may legally contain `<` and `>`, so a term, a `comment` text, or a
;; `?q=` query param is markup unless something escapes it, and escaping at each call
;; site is a rule that gets forgotten.  A node that must emit literal markup opts in
;; with `h/raw` — one node does (`theme-init-js`).  `html` returns a `RawString`, so
;; `resp` / `frag` coerce with `str` for the ring body.

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
  (config/web-dev?))

(def ^:private static-cache-control
  (if dev? "no-cache" "public, max-age=3600"))

(defn- read-stylesheet [] (some-> (io/resource stylesheet-resource) slurp))

(def ^:private cached-stylesheet (delay (read-stylesheet)))

(defn- stylesheet [] (if dev? (read-stylesheet) @cached-stylesheet))

(def ^:private theme-init-js
  "A pre-paint script: read the saved palette + theme from localStorage and set them
  on <html> before the page renders, so it opens in the chosen colours with no flash.
  A theme is written only when one was *stored*, since the absence of `data-theme` is
  what leaves the page following the OS — the stylesheet's `prefers-color-scheme`
  block is the default, and it needs no JS at all.

  Both values are **checked against the set that means something**, and an unrecognised
  one is ignored rather than trusted.  `data-theme` is the case that matters: any value
  at all satisfies the `:not([data-theme])` the media query is scoped by, so writing
  through a value no rule matches would leave the page on the light base and deaf to the
  OS — a stuck light page rather than an OS-following one.  Same discipline for the
  palette, where the cost is only the wrong hue.

  Runs synchronously in <head>; the two dots that change these live in select.js.  It is
  the one node rendered raw (`h/raw`, in `page`) — a `<script>` body is not markup, so
  escaping it would emit the source as text instead of running it."
  (str "(function(){var d=document.documentElement,s;try{s=localStorage}catch(e){return}"
       "var p=s.getItem('vaelii-palette');"
       "d.setAttribute('data-palette',/^(violet|red|green|rainbow)$/.test(p)?p:'violet');"
       "var t=s.getItem('vaelii-theme');"
       "if(t==='light'||t==='dark'){d.setAttribute('data-theme',t)}})();"))

(defn current
  "The KB a request reads.  A **holder** (anything deref-able —
  `vaelii.impl.catalog/holder`) yields whichever KB is active right now; a KB or an
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

(defn- header
  "The site header: the vaelii logo and wordmark (a home link) at the left, a
  term-search box, and the colour controls at the right.  The search is an htmx
  active-search — a debounced `hx-get` to /find swaps just the `#main` region out of
  the answer.  The palette dot (cycling the four accent pairs) and the theme dot
  (flipping light against dark) are wired by select.js and persisted in localStorage
  (docs/web.md)."
  []
  [:header.site
   ;; the request indicator every navigation and search points `hx-indicator` at:
   ;; htmx marks it `.htmx-request` for the life of the request, so a slow page says
   ;; so instead of looking dead
   [:div#page-indicator.htmx-indicator {:aria-hidden "true"}]
   [:a.brand {:href "/"}
    [:img.logo {:src "/logo.svg" :width 30 :height 30 :alt ""}]
    [:span.wordmark "Vaelii"]]
   ;; top-level tools; select.js marks the one matching the current path active
   [:nav.menubar
    [:a {:href "/"} "Ontology"]
    [:a {:href "/reasoning"} "Reasoning"]
    [:a {:href "/levels"} "Query"]
    [:a {:href "/assert"} "Assert"]
    ;; the sandbox is reached as a place to write, never as a context to choose — the
    ;; assert page names it and offers the reset; this is only the way in
    [:a {:href "/assert"} "Sandbox"]
    [:a {:href "/network"} "Network"]
    [:a {:href "/stats"} "Stats"]
    ;; long work runs on its own thread, so the way to it has to be in the chrome rather
    ;; than on the page that started it — the reader who wants it navigated away
    [:a {:href "/jobs" :title "long work: what is running, and how to stop it"}
     "Jobs" (jobs-badge)]
    ;; which KB every other page is about, and the way to change it
    ;; the label is its own element with an id because it changes without the header
    ;; being re-rendered: switching KBs swaps it out of band (`entries-panel`)
    [:a.kb-active {:href "/kbs" :title "knowledge bases: load, unload, switch"}
     [:span.muted "KB:"] " " [:span#kb-label (active-kb-name)]]]
   [:input.search {:type "search" :name "q" :placeholder "regex over terms…"
                   :autocomplete "off" :aria-label "find terms by regex"
                   :hx-get "/find" :hx-target "#main" :hx-select "#main"
                   :hx-swap "outerHTML" :hx-push-url "true"
                   :hx-trigger "keyup changed delay:400ms, search"}]
   ;; each dot is painted in what it controls, so neither needs a label beside it:
   ;; select.js keeps the titles saying which value is live
   [:div.theme-controls
    [:button#palette-dot.palette-btn {:type "button" :aria-label "switch colour palette"
                                      :title "Switch colour palette"}]
    [:button#theme-dot.theme-btn {:type "button"
                                  :aria-label "toggle light or dark theme"
                                  :title "Toggle light or dark theme"}]]])

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
      ;; editor's load/save) declaratively; select.js is the small hand-written module
      ;; for what htmx cannot express — a pointer drag-selection, the colour-mode and
      ;; theme toggles, and the active menubar link (docs/web.md).
      [:script {:src "/htmx.min.js" :defer true}]
      [:script {:src "/select.js" :defer true}]]
     ;; hx-boost turns every in-page link and form into an ajax swap with history, so
     ;; ordinary navigation is snappy without a line of JS; it degrades to plain links
     ;; when htmx is absent.  The swap is scoped to `#main`, which is what makes the
     ;; fragment answer possible: the header, the selection bar, and the editor sit
     ;; outside it and are never torn down, so a navigation keeps the search box's focus
     ;; and an open editor, and the server sends only what actually lands.
     ;;
     ;; `show:window:top` is not decoration.  A boosted swap whose target is not the body
     ;; scrolls that target into view, so scoping the swap to `#main` would land every
     ;; navigation with the header scrolled off the top — the logo, the search box and the
     ;; menubar gone, on a page the reader had not scrolled.  Saying where to land instead
     ;; makes a boosted navigation end where an unboosted one does: the top of the document.
     [:body {:hx-boost "true" :hx-target "#main" :hx-select "#main"
             :hx-swap "outerHTML show:window:top"
             :hx-indicator "#page-indicator"}
      (header)
      [:main#main body]
      ;; the selection action bar (shown by select.js once ≥1 sentex is selected)
      ;; and the panel the editor form is swapped into — both outside #main so a
      ;; navigation/search swap does not tear them down mid-edit.
      [:div#sx-bar.hidden {:role "toolbar" :aria-label "selection actions"}
       ;; a live region: the count changes without the page moving, so it has to
       ;; announce itself for a reader who cannot see the rows tint
       [:span#sx-count {:role "status" :aria-live "polite" :aria-atomic "true"} "0 selected"]
       [:input#sx-handles {:type "hidden" :name "handles"}]
       ;; neither panel is a page: each swaps into #editor and takes the whole answer,
       ;; so both opt out of the #main selection the body sets for boosted navigation.
       ;; `/retract` GET only *previews* the teardown — the write is its POST.
       [:button.primary {:type "button" :hx-get "/edit" :hx-include "#sx-handles"
                         :hx-target "#editor" :hx-select "unset" :hx-swap "innerHTML"} "Edit"]
       [:button#sx-retract {:type "button" :hx-get "/retract" :hx-include "#sx-handles"
                            :hx-target "#editor" :hx-select "unset" :hx-swap "innerHTML"}
        "Retract…"]
       [:button#sx-clear {:type "button"} "Clear"]]
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

;; ---- the per-request view -----------------------------------------------
;;
;; Rendering asks the KB the same few questions over and over: what the types are (to
;; colour a term), whether a handle is believed (to dim a badge), what a handle's record
;; is.  Asked per row, that is the N+1 every listing page pays — and under `--attach`
;; each one is an HTTP round-trip, not a map lookup.  A `view` is those answers held for
;; the length of one request: the type set read at most once, and a belief cache the
;; row renderers fill in **batch** through `prime-belief!`.

(defn- fragment-request?
  "Is htmx asking for the `#main` fragment rather than a whole document?  `HX-Request`
  marks every htmx-issued request, so the answer can skip the chrome the client would
  discard.  `HX-History-Restore-Request` is the exception: htmx is repopulating a
  history entry and needs the document back."
  [req]
  (and (some? (get-in req [:headers "hx-request"]))
       (nil? (get-in req [:headers "hx-history-restore-request"]))))

(defn view
  "What one request's rendering reads that does not vary row to row — built once per
  request and threaded through every render fn in place of a bare KB."
  [kb req]
  {:kb        kb
   ;; the type set, as the set the taxonomy already holds — a delay, and never copied.
   ;; It is read to colour a term (`term-class`) and to count the types, and neither
   ;; happens on `/jobs`, `/kbs`, `/caches` or a fragment continuation, so those pages
   ;; never touch it.  In-process the deref is one atom read of a persistent set that
   ;; `tax/types` hands back by reference; copying it was ~125k `conj`s per request on
   ;; an imported ontology.  Under `--attach` it is one EDN transfer per page that
   ;; renders a term rather than one per request — the wire hands a set back, and the
   ;; `set` below is only for a target that does not.
   :types     (delay (let [t (v/types kb)] (if (set? t) t (set t))))
   :fragment? (fragment-request? req)
   ;; which scratch context this session writes to by default.  Naming it costs nothing
   ;; — `sandbox/context-of` reads a cookie — and the context itself is not created
   ;; until something is actually written to it.  Whether it *has* been is a KB read, so
   ;; it is a delay: a page that never mentions the sandbox never pays for it.
   :sandbox   (sandbox/context-of req)
   :sandbox-live? (delay (boolean (when-let [c (sandbox/context-of req)]
                                    (sandbox/live? kb c))))
   :belief    (atom {})
   ;; what each reified term on the page denotes.  There is no batched read for these
   ;; — the map is `(termOfUnit K ?e)`, one probe per constant — so the cache is what
   ;; bounds it at one read per *distinct* constant rendered, however many times the
   ;; page renders it.  Empty and untouched on a KB that has minted none.
   :nat-exprs     (atom {})})

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

(defn- blocked-justifications
  "The justifications the truth-maintenance network currently holds *blocked*: their
  rule's `exceptWhen` exception holds, so the JTMS has ruled them invalid and they
  confer nothing — even with every argument IN (`v/blocked-justifications`).

  This is a *different* condition from an argument being OUT, and the one the proof tree
  cannot read from belief alone: a blocked justification's arguments can all be believed,
  so an argument-only reading calls it supporting when it supports nothing.  Every
  `supporting`/`valid` verdict below `and`s membership here in.

  Read through `access`, so an attached browser reads the daemon's network rather than
  the empty set an in-process-only read would answer with: the argument-only reading is
  not a degraded rendering but a wrong one, drawing a blocked justification as
  supporting."
  [{:keys [kb]}]
  (set (v/blocked-justifications kb)))

(defn- commas [n] (when (number? n) (format "%,d" (long n))))

(defn- css-percent
  "A fraction as the percentage a `width:` declaration takes, to one decimal.

  `clojure.core/format` renders in the **default locale**, and a comma-decimal one
  (`fr-FR`, `de-DE`, most of Europe) writes `12,5` — which is not a CSS number, so the
  declaration is dropped and the bar draws at whatever width the stylesheet gave it.  The
  locale of the machine the daemon happens to run on decides that, and nothing on the page
  says so.  Every number that lands in markup rather than in prose goes through this;
  `commas` above deliberately does not, since a thousands separator is display text and
  reads in the reader's own convention."
  [frac]
  (String/format java.util.Locale/ROOT "%.1f" (object-array [(* 100.0 frac)])))

(defn- progress-bar
  "Where a running load has got to.  A corpus knows its own total (its `report.edn` /
  `meta.edn` says how many sentences it holds) and gets a real bar; a load with no total
  gets a striped indeterminate one and the count it has reached, which is the honest
  rendering of not knowing how far there is to go."
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

(defn- polling
  "What makes a panel refresh **itself** while something is running: it fetches its own
  replacement every `every` and swaps in place.  The server decides whether to include
  these at all, so a finished job stops being asked about — the four panels that watch a
  load or an export all say it this way.

  `hx-indicator` is `unset` rather than left to inherit.  htmx resolves an indicator by
  walking *up* the DOM, and the body points every request at `#page-indicator` — so a
  poll would sweep the top-of-page bar every second or two for the whole of a load,
  reporting the page as loading when nothing the reader did is in flight.  A poll is not
  a request they made, and the panel already draws its own progress."
  [uri every]
  {:hx-get uri :hx-trigger (str "every " every) :hx-target "this"
   :hx-select "unset" :hx-swap "outerHTML" :hx-indicator "unset"})

(defn- caveat-banner
  "The strip a page carries while the KB it reads is provisional — still loading, stopped
  part-way, or holding no belief.  Empty (and inert) the rest of the time.

  It lives at the top of `#main` rather than in the header because `#main` is what every
  navigation and search swaps: put it in the chrome and it would state the KB's condition
  as of whenever the document was first served.  While a load runs it polls itself, and
  the poll stops on its own — the endpoint answers with the empty element once there is
  nothing left to say, exactly as the entries list and the memory strip do.

  Two conditions, said separately, because they are independent and the second is the one
  that lasts: a *prefix* of the corpus is the ordinary open-world condition and costs a
  reader completeness, while *no belief* silently empties every believed answer and can
  outlive the load that explains it (a store opened without `:recover?`)."
  []
  (let [{:keys [name status progress belief? recoverable?]} (catalog/active-caveat)
        loading? (= :running status)]
    [:div#kb-caveat
     (cond-> {}
       loading? (merge (polling "/kbs/banner" "2s")))
     (when status
       (let [[lead tail] (case status
                           :running    ["Loading "     " — you are reading it as it arrives."]
                           :cancelling ["Stopping "    " — you are reading what has landed."]
                           :cancelled  ["Stopped part-way: " " — you are reading what had landed."]
                           :failed     ["Load failed: " " — you are reading what had landed."]
                           ;; :done reaches here only for the beliefless case, where the
                           ;; load is not the story and the bullet below it is — but the
                           ;; line still has to say which KB, and a bare name is not a
                           ;; sentence
                           ["Reading "   " — and it is stored, not merely missing."])]
         [:div.kb-caveat {:class (str "kb-caveat-" (clojure.core/name status))}
          [:p.kb-caveat-line
           (when (seq lead) [:b lead])
           [:a {:href "/kbs"} name] tail]
          (when loading? (progress-bar progress))
          [:ul.kb-caveat-why
           (when-not (= :done status)
             [:li "Everything below is drawn from what is stored " [:i "now"] ", so a term "
              "or a rule that has not arrived yet reads as absent — which is what an "
              "absent fact always means here, and never as false."])
           (when loading?
             [:li "Writing is on hold: a load is this process's one writer, so this KB can "
              "be read while it fills up but not changed. Cancel it, or switch to another "
              "KB, to write again."])
           (when-not belief?
             [:li [:b "Belief and the taxonomy are not built."] " Everything is stored and "
              "findable — the term pages, the extents, the raw index levels — but with no "
              "truth-maintenance network every " [:i "believed"] " answer is empty, and "
              "with no genl closures there is no type hierarchy, so the ontology page "
              "reads as though the KB held nothing. "
              (if loading?
                "The load builds both at the end."
                ;; Two different repairs, and the store knows which one applies: a KB
                ;; holding justifications has everything `recover` reads and needs no
                ;; second pass over the dump, while one holding none cannot be recovered
                ;; into belief at all and has to be loaded again.  Prescribing the reload
                ;; to both sends the first case back through hours of work for nothing.
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
      (resp (page title body)))))

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
  `(disjoint dog cat)` and `(disjoint cat dog)` are one row rather than two.

  A **vector**, not a set.  A type may be declared disjoint from *itself* — which is how
  an ontology says a type has no instances, and an imported one does say it — and a
  two-element set of one term is one element: `#{a b}` refuses to build at all (it is the
  checked `RT.set`, so it throws rather than folding), and a pair that did fold would
  render with half of it missing.  Order is by name, so it is a function of the content
  and not of which sentex was read first."
  [a b]
  (if (neg? (compare (str a) (str b))) [a b] [b a]))

(defn- disjoint-pairs
  "The disjointness pairs to display: the believed `(disjoint a b)` sentexes, plus the
  pairs a `disjointMetatype` induces.

  The induced ones are computed rather than read, because a metatype separates its
  members by being *consulted* rather than by materializing a clique of real
  sentexes, so a page listing only stored pairs would silently under-report.  A member is
  not separated from *itself* by belonging to one, which is why only that half filters
  the diagonal out — a stated `(disjoint A A)` is content and is shown."
  [kb]
  (let [declared (into #{} (keep (fn [s] (let [[_ a b] (:sentence s)]
                                           (when (and a b (= :true (:truth s)))
                                             (disjoint-pair a b)))))
                       ;; the functor root rather than `(disjoint ?a ?b)`: a pattern with
                       ;; no ground argument gives the trie nothing to narrow on and fans
                       ;; over every child token it has
                       (v/sentexes-with-functor kb 'disjoint {:believed? true}))
        induced  (for [m  (v/disjoint-metatypes kb)
                       :let [ms (vec (v/metatype-members kb m))]
                       a  ms
                       b  ms
                       :when (neg? (compare (str a) (str b)))]
                   (disjoint-pair a b))]
    (into declared induced)))

(defn- term-class
  "The role class of a term, used to color it: type / individual / predicate /
  context / number / variable.  `v/term-role` supplies the naming role; the view's
  `types` set overlays it so a term known to the taxonomy colors as a type even where
  naming would call it a predicate — and **before** the non-symbol fallback, because a
  type node need not be a symbol.  An imported ontology names a type it has no atomic
  name for with a function term (17,211 of the types in the OpenCyc import `docs/kbs.md`
  measures are compounds), and reading that as a number is the whole page in the wrong
  colour."
  [{:keys [types]} t]
  (let [role (v/term-role t)]
    (cond
      (= role :variable)  "t-var"
      (= role :number)    "t-num"
      (= role :context)   "t-context"
      (contains? @types t) "t-type"
      (not (symbol? t))   "t-num"
      (= role :individual) "t-ind"
      (= role :predicate) "t-pred"
      (= role :type)      "t-type"                        ; snake_case not yet in the taxonomy
      :else               "t-pred")))

;; ---- reified terms ------------------------------------------------------
;;
;; A ground `(F a…)` under a `reifiableFunction` is stored as an opaque constant in the
;; reserved `nat/` namespace (docs/nat.md), which is how a function term is indexed and
;; retracted like any symbol.  `nat/g4711` is not a name anybody wrote and says nothing
;; to a reader, so **no page ever shows one**: every place a term is rendered goes
;; through `term-link`, and a reified one renders as the expression it was minted from.
;;
;; The parens are **bold**, which is the whole of the notation.  A reified NAT is a *term* that
;; happens to have structure, and it appears in sentences beside ordinary compounds —
;; on the constant's own page `(termOfUnit K E)` renders K and E identically otherwise,
;; the constant and the literal expression it is mapped to reading as the same thing.
;; Weight is what separates them, and the opening paren links to the constant's page, so
;; the reified term stays reachable without being spelled out.

(defn- nat-expression
  "What reified term `k` denotes, from the per-request cache — one `v/term-expression`
  read per distinct constant on the page, however many times it is rendered.  nil when
  the KB holds no believed `termOfUnit` map for it."
  [{:keys [kb nat-exprs]} k]
  (if-let [e (find @nat-exprs k)]
    (val e)
    (let [e (v/term-expression kb k)]
      (swap! nat-exprs assoc k e)
      e)))

;; Expansion recurses, so it carries the constants already on the path.  The write path
;; cannot build a reified term that reaches itself — inner NATs are minted first, so a
;; constant's expression predates it — but a *stored* one can say anything (docs/web.md,
;; "The browser reads what is stored"), and an unguarded walk over `(termOfUnit K (F K))`
;; is a stack overflow rather than a page.  A term already on the path renders as the
;; back-edge it is.

(defn- term-text
  "The text of a term, for the places that take a string rather than an element — a
  page `<title>`, a tooltip, a graph node's label, a link's own text.  A reified term
  reads as the expression it denotes, recursively, so it says the same thing there as in
  the prose; a term that is itself a compound (an unreified structural NAT, a function term an
  imported ontology names a collection by) is walked for the same reason."
  ([view t] (term-text view t #{}))
  ([view t seen]
   (cond
     (v/reified-term? t)
     (if-let [e (and (not (seen t)) (nat-expression view t))]
       (str "(" (str/join " " (map #(term-text view % (conj seen t)) e)) ")")
       "(…)")

     (sequential? t) (str "(" (str/join " " (map #(term-text view % seen) t)) ")")
     :else           (pr-str t))))

;; The cycle: a reified term renders as its expression, whose arguments are terms — an
;; unreified structural NAT compound, or another reified term, which renders as *its* expression.
(declare render-form)

(defn- nat-ref
  "A reified term, rendered as the expression it was minted from with **bold parens**.
  The opening paren links to the constant's own page — the one place its `termOfUnit`
  map, its materialized result types and its uses are listed — so the reified term is
  one click away and still never spelled out.

  A constant whose expression is not believed renders `(…)` rather than falling back to
  the raw symbol: the map can be defeated or gone while a use of the constant survives,
  and the honest answer there is that the page cannot say what it denotes."
  [view k seen]
  (let [e (and (not (seen k)) (nat-expression view k))]
    [:span.nat
     [:a.nat-paren {:href  (str "/term?q=" (url-enc (pr-str k)))
                    :title "the reified term itself"} "("]
     (if e
       (interpose " " (map #(render-form view % (conj seen k)) e))
       [:span.muted {:title "no believed expression for this reified term"} "…"])
     [:span.nat-paren ")"]]))

(defn- term-link
  "A role-colored link to a term's page (variables are not links; a reified term is its
  expression — `nat-ref`)."
  ([view t] (term-link view t #{}))
  ([view t seen]
   (cond
     (= :variable (v/term-role t)) [:span.t-var (pr-str t)]
     (v/reified-term? t)           (nat-ref view t seen)
     ;; the href is the term as stored — what the page is *about* — and the text is how
     ;; the page writes it.  The two differ for a compound term holding a reified one
     :else [:a {:class (str "sx " (term-class view t))
                :href  (str "/term?q=" (url-enc (pr-str t)))}
            (term-text view t seen)])))

(defn- render-form
  "Render a sentence (or subterm) with every atomic subterm an individually
  role-colored link, structure shown with parentheses."
  ([view form] (render-form view form #{}))
  ([view form seen]
   (cond
     (sequential? form) [:span.sx "(" (interpose " " (map #(render-form view % seen) form)) ")"]
     (string? form)     [:span.sx (pr-str form)]
     :else              (term-link view form seen))))

(defn- readable
  "A sentex's sentence with the author's variable names restored, so a stored rule
  reads as it was written rather than as ?var0 / ?var1 — `vaelii.core/readable-sentence`."
  [s]
  (v/readable-sentence s))

(defn- justification-link [jid] [:a {:href (str "/justification/" jid)} "justification #" jid])

(defn- badge
  "The colour-coded badge that stands in for a sentex's bare handle before its
  sentence.  At a glance it says what the handle *is*:

    colour   indigo = a rule · violet = an asserted (premise) fact · teal = a derived fact
    glyph    → forward · ← backward · ↔ both · · inert (a rule's direction)
             • a positive fact · ¬ a negative literal
    dashed   a defeasible (default) rule
    dimmed   stored but not believed (OUT)

  It links to the sentex page, and its `title` carries the handle and a plain-English
  reading, so the number is one hover away.  It keys only on the record `s` the caller
  already fetched, plus belief — every field survives the daemon's sentex→map
  projection, so a remote-attached browser badges identically."
  [view s]
  (let [h         (:id s)
        rule?     (some? (:antecedent s))
        neg?      (= :false (:truth s))
        asserted? (some? (:strength s))
        in?       (believed? view h)
        dir       (:direction s)
        glyph     (cond rule? (case dir :forward "→" :backward "←" :inert "·" "↔")
                        neg?  "¬"
                        :else "•")
        classes   (cond-> ["badge"]
                    rule?                             (conj "badge-rule")
                    (and rule? (:defeasible s))       (conj "badge-defeasible")
                    (and (not rule?) asserted?)       (conj "badge-fact")
                    (and (not rule?) (not asserted?)) (conj "badge-derived")
                    (not in?)                         (conj "badge-out"))
        label     (str (if rule?
                         (str (name (or dir :both)) " rule"
                              (when (:defeasible s) ", defeasible"))
                         (str (if asserted? "asserted" "derived")
                              (if neg? " negative fact" " fact")))
                       " · #" h (when-not in? " · out"))]
    [:a.badge-link {:href (str "/sentex/" h) :title label}
     [:span {:class (str/join " " classes)} glyph]]))

(defn- sentex-ref
  "A colour-coded handle badge (see `badge`) placed BEFORE the sentence, then the
  sentence rendered with individually-linked subterms.  It takes the **record**, which
  every listing already holds — re-fetching it by handle here is the N+1 that turns one
  page into one store read (or one round-trip) per row."
  [view s]
  [:span (badge view s) (render-form view (readable s))])

(defn- handle-ref
  "`sentex-ref` for a caller holding only a handle — a justification's antecedent, a
  contradictor — so it fetches the one record it needs.  A handle whose record is gone
  renders as such rather than vanishing."
  [{:keys [kb] :as view} h]
  (if-let [s (v/sentex kb h)]
    (sentex-ref view s)
    [:span.muted "#" h " (gone)"]))

(defn- state-tag
  "The belief-state pill for a sentex: IN when the JTMS believes it, else the `why-not`
  reason (superseded / defeated / unsupported / not-stored).  The sentex page shows it
  always; a list row shows only the reason and only when the row is OUT — a believed
  row's dimmed badge already reads as believed.  The one authority `in?` folds every
  not-believed reason into, and the page reads it back."
  [{:keys [kb] :as view} h]
  (if (believed? view h)
    [:span.tag.tag-in "IN"]
    (let [r (name (:reason (v/why-not kb h)))]
      [:span.tag {:class (str "tag-" r)} r])))

(defn- sentex-row
  "One selectable sentex row: a toggle affordance, the handle badge, the sentence, and
  its context.  `data-h` is what select.js selects by *and* what an out-of-band swap
  addresses after a save, so a row can be replaced where it sits.

  The row is a `role=\"row\"` of a single-column ARIA **grid** (`sx-list` below): it
  carries `aria-selected`, and select.js roves `tabindex` across the rows so the list is
  one Tab stop with arrow keys inside it.  A grid rather than a listbox because a row is
  made of links, which a listbox option may not contain."
  [view s]
  [:li {:data-h (:id s) :class "sx-item" :role "row"
        :aria-selected "false" :tabindex "-1"}
   [:span {:role "gridcell"}
    [:span.sx-check {:aria-hidden "true"}]
    (sentex-ref view s) " @ " (term-link view (:context s))
    ;; the handle badge dims an OUT row; the reason pill says WHY it is out
    ;; (superseded / defeated / unsupported) — shown only when not believed, so a
    ;; believed row stays clean.  Its proof is a click away on the sentex page.
    (when-not (believed? view (:id s)) (list " " (state-tag view (:id s))))]])

(defn- select-all
  "A group's select-all control.  It reads its own state back — once everything in the
  group is selected the same button clears it — and select.js finds the rows through
  the enclosing `.sx-group`."
  [label]
  [:button.sx-all {:type "button" :data-select-all "" :aria-pressed "false"
                   :aria-label (str "select every sentex " label)} "Select all"])

(defn- sx-list
  "A selectable list of rows, with the ARIA a multi-selection needs: a single-column
  grid, labelled, plus the group control that takes the whole list at once."
  [label & rows]
  [:ul.sx-list {:role "grid" :aria-multiselectable "true" :aria-label label} rows])

(defn- sentex-list [view sentexes]
  (let [ss (sort-by :id sentexes)]
    (prime-belief! view (map :id ss))
    (if (seq ss)
      [:div.sx-group
       [:p.sx-head (select-all "in this list")]
       (sx-list "sentexes" (for [s ss] (sentex-row view s)))]
      [:p.muted "none"])))

(defn- justification-list [view justifications]
  (let [ds (sort-by :id justifications)]
    (prime-belief! view (map :consequence ds))
    (if (seq ds)
      [:ul (for [d ds]
             [:li (justification-link (:id d)) " — "
              [:span.muted "via " (pr-str (:informant d))] " ⇒ "
              (handle-ref view (:consequence d))])]
      [:p.muted "none"])))

(def ^:private legend
  [:p.legend "Terms are colored by role: "
   [:a.sx.t-type "type"] " · " [:a.sx.t-ind "individual"] " · "
   [:a.sx.t-pred "predicate"] " · " [:a.sx.t-context "context"] " · "
   [:a.sx.t-num "number"] " · " [:span.t-var "?variable"] "."])

(def ^:private badge-legend
  [:p.legend "Each sentence carries a handle badge: "
   [:span.badge.badge-rule "→"] "rule (the arrow is its direction) · "
   [:span.badge.badge-fact "•"] "asserted fact · "
   [:span.badge.badge-derived "•"] "derived fact · "
   [:span.badge.badge-fact "¬"] "negation · "
   [:span.badge.badge-rule.badge-defeasible "↔"] "defeasible rule · "
   [:span.badge.badge-out "•"] "not believed."])

;; ---- belief state (the sentex page) -------------------------------------

(defn- rewrite-arrow [view [old rep]]
  [:span (term-link view old) " → " (term-link view rep)])

(defn- belief-detail
  "When a sentex is stored but OUT, render *why* from `why-not`: the restatement that
  superseded it (an equality merge), the sentexes that contradict a defeated one, or
  the missing antecedents of an unsupported one.  Nothing for a believed sentex — its
  proof is the \"Supported by\" section."
  [{:keys [kb] :as view} h]
  (let [{:keys [reason superseded-by contradicted-by support]} (v/why-not kb h)]
    (case reason
      :superseded
      [:div.belief
       [:p [:b "Superseded"] " by an equality merge — stored but not believed, restated "
        "under its class representative as "
        (if-let [nh (:handle superseded-by)]
          (handle-ref view nh)
          (render-form view (:sentence superseded-by))) "."]
       (when-let [rw (seq (:rewrites superseded-by))]
         [:p.muted "rewrites: " (interpose ", " (map #(rewrite-arrow view %) rw))])]
      :defeated
      [:div.belief
       [:p [:b "Defeated"] " — contradiction resolution forced it OUT."]
       (if (seq contradicted-by)
         [:ul (for [c contradicted-by]
                [:li "contradicted by " (handle-ref view (:handle c))
                 " @ " (term-link view (:context c))
                 (when-let [dc (:defeat-class c)] [:span.tag (str "class " (name dc))])])]
         [:p.muted "the winning sentex has since been retracted; nothing contradicts it now."])]
      :unsupported
      [:div.belief
       [:p [:b "Unsupported"] " — not a premise, and every justification has an OUT argument."]
       (when (seq support)
         [:ul (for [j support]
                [:li (justification-link (:justification j)) " — missing "
                 (interpose ", " (map #(handle-ref view %) (:missing j)))])])]
      nil)))

;; ---- index-organized term view (the term page) --------------------------

(def ^:private group-cap
  "How many sentexes a single index group renders at a time.  The O(1) stored count is
  always shown, so a large root reports its true size; the rest arrives a page at a time
  as the reader scrolls (`more-rows`)."
  60)

(defn- more-rows
  "The continuation sentinel that ends a capped list: a row which fetches the next page
  and **replaces itself** with it.  `revealed` is htmx's intersection trigger, so a tail
  nobody scrolls to costs nothing; `click` is the same request for a reader who would
  rather ask, and for a viewport too tall to scroll; Enter is that reader's keyboard.

  `row?` says the sentinel is ending a **grid** of selectable rows (`sx-list`), whose
  children must all be rows — the term page's index groups.  `tr?` says it is ending a
  real `<table>`, whose `<tbody>` may hold nothing but `<tr>`, so the sentinel is one
  spanning the columns.  The `/find` and `/levels` lists are ordinary lists and take the
  plain shape."
  ([href label] (more-rows href label nil))
  ([href label {:keys [row? tr?]}]
   ;; `hx-target`/`hx-select` are set on the body so every boosted link swaps #main, and
   ;; they are inherited — so a sentinel says explicitly that it replaces *itself* with
   ;; the rows it fetched, and selects nothing out of them
   (let [attrs {:hx-get href :hx-trigger "revealed, click, keyup[key=='Enter']"
                :hx-target "this" :hx-select "unset" :hx-swap "outerHTML"
                :hx-indicator "#page-indicator"}
         cell  [:span.more-cell {:role (if row? "gridcell" "button") :tabindex "0"}
                [:span.muted label]]]
     (cond
       tr?  [:tr.more attrs [:td.more-td {:colspan "2"} cell]]
       row? [:li.more (assoc attrs :role "row") cell]
       :else [:li.more attrs cell]))))

(defn- fact-body
  "The positive body of a stored fact sentence — `(P a b)` unchanged, `(not (P a b))`
  unwrapped — so an argument position reads off the same body the `[:argument-root]` root keys."
  [sent]
  (if (and (sequential? sent) (= 'not (first sent)) (sequential? (second sent)))
    (second sent)
    sent))

(defn- direct-arg-positions
  "The 1-based argument positions at which `term` sits directly in some stored fact —
  exactly the positions the predicate-scoped argument roots (`[:argument-root pred pos
  term]`) maintain for it.  Rules are excluded (they are not in the argument roots)."
  [term sentexes]
  (into (sorted-set)
        (for [s sentexes
              :when (not (:antecedent s))
              :let [body (fact-body (:sentence s))]
              :when (sequential? body)
              [i a] (map-indexed vector (rest body))
              :when (= term a)]
          (inc i))))

(defn- term-index-groups
  "Every stored sentex containing `term`, grouped by the **index** that reaches it,
  each group carrying its cheap count (O(1) for the roots, one O(1) read per predicate
  at the slot for the argument groups): the functor root `[:functor-root]`, the argument-position
  groups `[:argument-slot pos]` (the roster the predicate-agnostic read unions the scoped
  roots over), the context root `[:context-root]` (when the term is a context), then the
  term-index remainder `[:term-index]` split into rules and deeper nestings.  The roots are a
  subset of the term index, so the remainder is `find-sentexes` minus what a root
  claimed.

  `text` is how the term is *written* in the key each group displays — the page's own
  spelling, so a reified term's key names the expression the rest of the page shows
  rather than the opaque constant nothing else on it mentions.  The key shape is the
  real one either way; what is substituted is only the term's rendering."
  ([kb term] (term-index-groups kb term (pr-str term)))
  ([kb term text]
   (let [fs        (v/find-sentexes kb term)
         functor   (v/sentexes-with-functor kb term)
         positions (direct-arg-positions term fs)
         arg-grps  (for [p positions
                         :let [ss (v/sentexes-with-arg kb p term)]
                         :when (seq ss)]
                     ;; `:pos` is what the group is *about*, and the concept graph reads
                     ;; its ego edges off these groups rather than paying a second extent
                     ;; read — an arrow needs to know which end of the fact the term is
                     {:label (str "In argument position " p)
                      :idx (str "[:argument-slot " p " " text "]")
                      :pos p :count (v/count-with-arg kb p term) :sentexes ss})
         ctx-ss    (when (= :context (v/term-role term)) (v/sentexes-in-context kb term))
         claimed   (set (map :id (concat functor (mapcat :sentexes arg-grps) ctx-ss)))
         remainder (remove #(claimed (:id %)) fs)
         rules     (filter :antecedent remainder)
         nested    (remove :antecedent remainder)]
     (concat
      (when (seq functor)
        [{:label "As predicate" :idx (str "[:functor-root " text "]")
          :count (v/count-with-functor kb term) :sentexes functor}])
      arg-grps
      (when (seq ctx-ss)
        [{:label "As context" :idx (str "[:context-root " text "]")
          :count (v/count-in-context kb term) :sentexes ctx-ss}])
      (when (seq rules)
        [{:label "In rules" :idx "[:rule-index] · [:term-index]"
          :count (count rules) :sentexes rules}])
      (when (seq nested)
        [{:label "Nested elsewhere" :idx (str "[:term-index " text "]")
          :count (count nested) :sentexes nested}])))))

;; ---- ordering what a page lists ------------------------------------------
;;
;; A term the browser lists may be a **NAT** — a compound, not a symbol — so a page's order
;; is taken off the printed form rather than off `compare`.  `str` on a compound honours
;; `*print-length*` / `*print-level*` exactly as `pr-str` does, so under an ambient bound
;; two long terms print to one prefix, the key collapses, and the order falls back to
;; whatever the KB enumerated.  These two release the bounds around the printing.
;;
;; Written here rather than reached for: `naming/print-key` holds the same guard for the
;; engine, and this namespace holds no engine require by design — see the ledger above.

(defn- print-key
  "`x` printed as an ordering key, with the print bounds released."
  ^String [x]
  (binding [*print-length* nil *print-level* nil *print-meta* false]
    (pr-str x)))

(defn- by-print-key
  "`coll` as a vector ordered by its elements' printed form.  Decorate-sort-undecorate, so
  the key is built once per element and one binding frame covers the whole sort."
  [coll]
  (binding [*print-length* nil *print-level* nil *print-meta* false]
    (mapv second (sort-by first (mapv (fn [x] [(pr-str x) x]) coll)))))

(defn- group-order
  "A group's sentexes in display order — by context, then handle.

  **Handle order is allocation order, and that is the ordering by design.**  Paging is a
  re-slice of this sequence at an offset, so the order has to be one a later request
  reproduces exactly; a content ordering moves under every write, and a reader who scrolled
  past an offset would then see a row twice or not at all.  Two things it is not: a
  *ranking* — the earliest-asserted sentex is not the most important one — and a *cap*.
  Nothing is dropped by it.  `group-rows`' sentinel walks the whole group a page at a time,
  and the count beside the heading is the group's stored total rather than the page's."
  [sentexes]
  (sort-by (juxt (comp print-key :context) :id) sentexes))

(defn- group-rows
  "One page of a group's rows, plus the sentinel that fetches the next page when it is
  reached.  Belief for the whole page is read once (`prime-belief!`), so a page of 60
  rows costs one belief read rather than 60.  `total` is the group's stored count, so
  the sentinel still says how many are behind it."
  [view term g offset total sentexes]
  (let [rows (into [] (take (inc group-cap)) (drop offset (group-order sentexes)))
        page (take group-cap rows)]
    (prime-belief! view (map :id page))
    ;; data-h + .sx-item make the row drag-selectable (select.js); the handle badge
    ;; dims an OUT sentex and `sentex-row` names the reason it is out
    (list (map #(sentex-row view %) page)
          (when (> (count rows) group-cap)
            (more-rows (str "/term/rows?q=" (url-enc (pr-str term))
                            "&g=" g "&offset=" (+ offset group-cap))
                       (str "show " (max 0 (- total offset group-cap)) " more")
                       {:row? true})))))

(defn- index-group
  "Render one index group: its name, the index key it reads, its stored count, then its
  sentexes a page at a time — with the control that selects the whole group at once."
  [view term [g {:keys [label idx count sentexes]}]]
  [:div.idxgrp.sx-group
   [:h4 label " " [:code idx] " " [:span.muted "· " count " stored"] " " (select-all label)]
   (sx-list label (group-rows view term g 0 count sentexes))])

;; ---- proposing knowledge: the model, on a term page ---------------------
;;
;; The term page says what the KB knows about a term.  This is the way to ask a model
;; what it is missing — `vaelii.impl.llm.session/propose-page`, which reads the page's
;; own content and the vocabulary its `genl` neighbourhood licenses, and answers with
;; assertions in that vocabulary.  It **proposes only**: nothing here writes, so this
;; route adds no write path and no trust boundary, and a reader reviews the lines before
;; any of them reaches the editor.
;;
;; The panel is an htmx fragment inside the term page — the instruction goes up, the
;; lines come back into `#propose-result`, and the page never navigates.  Losing the page
;; you were reading in order to ask a question about it is the workflow break the novice
;; literature names outright.

(def ^:dynamic *proposer*
  "The model a proposal runs against, as `{:kind <keyword> :provider <Provider>}`, or nil
  — the default — to resolve the configured backend per request.  A caller binds it to
  drive the panel against a scripted provider without a model, which is how the handlers
  below stay testable as pure `request -> response` like the rest of this namespace."
  nil)

(def ^:private propose-max-tokens
  "The output cap every proposal turn carries — Ollama's `num_predict`.

  Two of eight models measured degenerate into runaway generation; one wrote 8138 lines
  over 474 seconds.  A wall-clock timeout is no answer to that: the host goes on
  generating and the reader has paid the GPU time either way, so the bound has to be on
  **tokens**.  The number is arithmetic rather than taste — a turn asks for at most 24
  assertions, each one s-expression inside a small JSON object, which is comfortably
  under 1200 tokens — so this leaves an honest answer room to spare and still stops a
  runaway inside a few seconds."
  2048)

(def ^:private propose-timeout-ms
  "How long the transport waits on a turn.  A backstop *under* the token cap, not the
  runaway guard: it is what stops a host that has stopped answering from holding a
  request thread, where the cap is what stops one that is answering too much."
  90000)

(defn- proposal-provider
  "The model this request talks to: `{:kind :provider}`, from `*proposer*` when a caller
  supplied one, else the configured backend.  Resolving it is what probes the host, so it
  happens on the POST that runs a turn and never on rendering the panel."
  []
  (or *proposer*
      ;; the KIND label from `available?` — which rides the shared probe client — rather
      ;; than `active-kind`, whose `build` liveness test constructs a throwaway provider,
      ;; and a fresh `HttpClient` with it, on every POST and drops it to the collector.
      ;; `generation-provider` builds the one provider the turn actually runs on, itself
      ;; gated on the same reachability probe, so a broken backend still falls to the stub.
      (let [k    (or (llm-provider/configured) :stub)
            kind (if (llm-provider/available? k {}) k :stub)]
        {:kind kind
         :provider (llm-provider/generation-provider k {:timeout-ms propose-timeout-ms})})))

(defn- proposal-tally
  "The counts a reviewer reads first: how much of the answer is new, how much restates
  what is stored, and how much vocabulary it had to invent — the one number that says a
  proposal is fragmenting the ontology rather than extending it."
  [view {:keys [summary coined context]} kind elapsed-ms level]
  (let [{:keys [proposed new known duplicate]} summary]
    [:p.muted
     (or proposed 0) " proposed"
     (when (pos? (or new 0)) (list " · " [:b new] " new"))
     (when (pos? (or known 0)) (str " · " known " already stored"))
     (when (pos? (or duplicate 0)) (str " · " duplicate " repeated"))
     (when (seq coined) (str " · " (count coined) " coined"))
     ;; where it would land is engine vocabulary, and `guided` is the level for a reader
     ;; who does not have that word yet — the row withholds it for the same reason
     (when (and context (not= :guided level)) (list " · filed in " (term-link view context)))
     " · " (name (or kind :stub))
     (when elapsed-ms (str " · " elapsed-ms "ms"))]))

;; ---- the chip gutter ----------------------------------------------------
;; A proposed line has four independent things worth knowing (`vaelii.impl.llm.verdict`)
;; and prose buries all of them.  Each becomes a **chip**: a glyph and one word, in a
;; gutter the eye reads down.  What a chip *means* is one `?` away and never inline —
;; a reviewer scanning twenty lines is looking for the two that need them.

(def ^:private verdict-glyph
  "The leading glyph, by the worst thing true of the line.  Four shapes rather than four
  colours: colour alone is not a distinction every reader can make."
  {:refused "✗" :uncertain "!" :coins "+" :ok "✓"})

(def ^:private problem-word
  "One word per `check-edit` problem type — the reason, not the message.

  Every type `check` documents is here, and anything it grows later still renders as a
  chip: the fallback is the keyword's own name, which is short by construction and is
  never the exception text.  A raw message in the gutter is the failure this table
  exists to prevent — it is the one thing that cannot be scanned."
  {:naming               "naming"
   :not-ground           "open"
   :unsupported-context  "not a place"
   :not-well-formed      "malformed"
   :not-range-restricted "unbound"
   :not-indexable        "var predicate"
   :disjunction-too-wide "too many ors"
   :not-stratified       "cycle"
   :not-assertible       "imperative"
   :not-checkable        "imperative"
   :exception-not-closed "open guard"
   :naf-not-closed       "open naf"
   :quantifier-not-local "quantifier"
   :arg-type             "arg type"
   :arg-genl             "arg type"
   :inter-arg-type       "arg type"
   :quoted-arg-type      "quoted arg"
   :arg-position         "arg slot"
   :arg-constraint-kind  "arg kind"
   :arg-variable         "arg var"
   :arity                "arity"
   :disjoint             "disjoint"
   :asymmetric           "both ways"
   :functional           "functional"
   :irreflexive          "self tuple"
   :anti-symmetric       "forces equal"
   :anti-transitive      "chain closes"
   :shape                "shape"
   :not-encodable        "unstorable"
   :unknown-option       "opts"
   :unknown-handle       "no handle"
   :bad-handle           "bad handle"
   :not-watchable        "no feed"
   :context-escape       "wrong ctx"
   ;; the write side of the caveat banner's second condition: this KB's belief (or its
   ;; derived index) was never built, so the door refused rather than storing unchecked
   :unrecovered-kb       "not recovered"
   :unrecovered-premise  "no sweep"
   ;; a `find-terms` regex whose backtracking blew the per-term step budget — not a
   ;; `check-edit` problem, but the propose test scans every `:type` in core.clj
   :pattern-too-costly   "too costly"
   ;; and the other read-side one the same scan reaches: a bounded `ask` / `prove` whose
   ;; clock ran out before the search did, so what it held was a prefix
   :budget-exhausted     "out of time"
   :error                "error"})

(defn- problem-chip-word [t]
  (or (problem-word t) (some-> t name)))

(def ^:private correction-word
  "One word per correction rule — what *kind* of restatement it is."
  {:unary-on-type     "shape"
   :relation-on-types "lift"
   :arity-surplus     "arity"})

(def ^:private uncertainty-word
  "What a `:confidence :low` correction is unsure *about*, by the rule that produced it —
  because the word has to name the decision being handed back, and the two rules hand
  back different ones: `relation-on-types` cannot tell which argument is which when both
  positions want the same type, and `arity-surplus` cannot tell which argument is
  surplus when no two are equal."
  {:relation-on-types "direction"
   :arity-surplus     "ambiguous"})

(defn- chip
  "One chip: a glyph, one word, and the detail as a hover title.  The title is a
  convenience, never the only way to the explanation — every detail is also under the
  row's `?`, which is what a touch device and a screen reader get."
  [kind glyph word detail]
  [:span.chip {:class (str "chip-" (name kind)) :title (str detail)}
   [:span.chip-g {:aria-hidden "true"} glyph] " " word])

(defn- line-chips
  "The chips for one verdict, left to right in the order they are triaged: what the KB
  refuses, what shape it wants instead, what the engine could not decide, and what
  vocabulary the line invents."
  [{:keys [problems correction coined]}]
  (list
   (for [p problems]
     (chip :refused "✗" (problem-chip-word (:type p)) (:message p)))
   (when-let [rule (:rule correction)]
     (chip :correction "→" (or (correction-word rule) (name rule)) (:why correction)))
   (when (= :low (:confidence correction))
     (chip :uncertain "!" (or (uncertainty-word (:rule correction)) "uncertain")
           (:why correction)))
   (for [c coined]
     (chip :coins "+" (name (:kind c))
           (str (:predicate c) " takes " (:arity c) " argument"
                (when (not= 1 (:arity c)) "s")
                " and the KB has never seen it")))))

(defn- alternatives-hint
  "The other shapes a correction would accept, as their functors in brackets — the
  reader's cue that a choice exists at all.  The sentences themselves are under the `?`:
  a bracketed `[genl]` says \"there is a definitional reading too\" in four characters,
  where the sentence would take a line."
  [{:keys [alternatives]}]
  (let [fs (->> alternatives (keep #(when (seq? %) (first %))) distinct (take 2))]
    (when (seq fs)
      [:span.p-alts "[" (str/join " " (map str fs)) "]"])))

;; ---- disclosure: one renderer, three configurations ---------------------
;;
;; "Show the bad result and the fix", "show only the fix" and "let them edit" were never
;; three flows.  They are one row at three densities, and the density belongs to the
;; **view** — a reader working through fifty lines wants a gutter, a reader meeting their
;; first refusal wants the sentence spelled out, and the same reader is both within a
;; session.  So it is a control above the list, not a preference nobody opens, and the
;; default is a property of where the panel was opened.
;;
;; Three configurations of one renderer rather than three renderers, because three
;; renderers drift: the day the chip gutter learns a fifth axis, two of them forget.

(def ^:private levels
  "The three disclosure levels, densest last, each with what it says of itself."
  [{:id :guided  :label "Guided"  :hint "the fix, in words, with what it means"}
   {:id :working :label "Working" :hint "the fix, a chip gutter, reasons on demand"}
   {:id :dense   :label "Dense"   :hint "the gutter alone, keyboard-driven"}])

(def ^:private level-ids (into #{} (map :id) levels))

(defn- level-of
  "The level a request is at.  A **property of the entry point**, not of the reader: the
  sandbox is where someone is learning what the KB will accept and opens `guided`; a term
  page is where vocabulary gets worked through and opens `working`.  An explicit choice
  overrides both, and rides the request rather than a cookie — a density that followed a
  reader from the sandbox onto a term page would be the preferences panel this exists
  instead of."
  [{:keys [sandbox]} asked ctx]
  (or (level-ids (some-> asked str/trim not-empty keyword))
      (if (and sandbox ctx (= sandbox ctx)) :guided :working)))

(defn- level-switch
  "The control.  Each button re-posts the list's own originals at another level, so
  changing density re-renders the proposal it already has and **never re-runs the
  model** — the verdicts are pure functions of the KB and the sentences, and the
  sentences are in the rows."
  [level]
  [:div.p-levels {:role "group" :aria-label "disclosure"}
   [:span.muted "Detail: "]
   (for [{:keys [id label hint]} levels]
     [:button {:type "button"
               :class (str "p-level" (when (= id level) " on"))
               :aria-pressed (if (= id level) "true" "false")
               :title hint
               :hx-post "/propose/level"
               :hx-vals (str "{\"level\": \"" (name id) "\"}")
               :hx-include ".propose-apply"
               :hx-target "#propose-result"
               :hx-select "unset"
               :hx-swap "innerHTML"}
      label])])

(defn- line-gloss
  "What the line would *mean*, in the KB's own words — `guided` only.

  Composed rather than generated (`vaelii.impl.gloss`): a model writing English about a
  claim is the one place in this panel nothing verifies the output, and the reader most
  likely to believe it is the one this level is for.  A gloss the KB cannot compose says
  so rather than inventing a description, and the formal sentence is on the row above it
  either way."
  [kb sentence]
  (when kb
    (let [{:keys [text source]} (gloss/text kb sentence)]
      (when (seq text)
        [:p.p-gloss
         (when (= :named source) [:span.muted "no description on record — "])
         text]))))

(defn- line-why
  "Everything a chip put behind a title, spelled out under one `?` per row — a
  `<details>`, so it costs no script, no layout, and nothing until it is asked for."
  [view {:keys [problems correction]}]
  (when (or (seq problems) correction)
    [:details.p-why
     [:summary {:aria-label "why"} "?"]
     [:div.p-why-body
      (for [p problems]
        [:p [:span.tag (name (:type p :error))] " " (:message p)])
      (when correction
        (list [:p (:why correction)]
              (when-let [alts (seq (:alternatives correction))]
                [:p "Or: " (interpose ", " (map #(render-form view %) alts))])))]]))

;; ---- choosing a shape ---------------------------------------------------
;; `correct` refuses to choose between `(genl penguin mortal)` and the defeasible rule,
;; because the choice is definitional versus defeasible and no engine can make it for the
;; author.  That is the most common decision in a review pass, so it costs **one key**:
;; the shapes are numbered, `1`…`9` picks one, and picking re-checks the sentence that
;; would actually be stored — `correct` does not re-check its own output, by contract, so
;; the chips a reviewer commits against are earned rather than inherited.

(defn- shape-buttons
  "The numbered shapes, when there is more than one.  Each posts the **original**
  sentence back with its number rather than the chosen sentence itself: the correction is
  a pure function of the KB and what the model wrote, so the server re-derives the shape
  from `correct/apply-correction` instead of trusting a sentence that arrived over the
  wire.  The row's own hidden fields carry the original, so the button sends one number."
  [{:keys [shapes n]}]
  (when (> (count shapes) 1)
    [:span.p-opts {:role "group" :aria-label "shape"}
     (map-indexed
      (fn [k s]
        (let [num (inc k)]
          [:button {:type "button"
                    :class (str "p-opt" (when (= num n) " on"))
                    :data-n num
                    :aria-pressed (if (= num n) "true" "false")
                    :title (pr-str s)
                    :hx-post "/propose/line"
                    :hx-vals (str "{\"n\": \"" num "\"}")
                    :hx-include "closest li"
                    :hx-target "closest li"
                    :hx-select "unset"
                    :hx-swap "outerHTML"}
           num]))
      shapes)]))

(defn- proposal-row
  "One reviewable line.  The row is the unit htmx swaps (choosing a shape re-renders
  exactly this `<li>`) and the unit the keyboard moves between, so it carries everything
  either needs: the shape it is on, the original it came from, and — **disabled until the
  reader accepts it** — the `[sentence context]` the commit form would submit.

  Disabling is the whole accept mechanism. A disabled field is not submitted, so the
  form posts exactly the accepted lines with no script assembling a payload, and a line
  the correction cannot repair simply has no field to enable."
  [view i {:keys [from context chosen storable? report-only? verdict] :as row} level]
  (let [v       (:verdict verdict)
        guided? (= :guided level)
        dense?  (= :dense level)]
    [:li {:class (str "p-line p-" (name v))
          :data-i i
          :data-state "undecided"
          :role "row"
          :tabindex (if (zero? i) 0 -1)
          :aria-selected "false"}
     [:span.p-glyph {:title (name v)} (verdict-glyph v "·")]
     " "
     (if (= chosen from)
       [:span (render-form view from)]
       (list [:span.p-was (render-form view from)]
             " " [:span.p-arrow {:aria-hidden "true"} "→"] " "
             [:span.p-to (render-form view chosen)]))
     ;; a context name is a piece of engine vocabulary, and `guided` is the level for a
     ;; reader who does not have that word yet — the placement is still what it was, it
     ;; is simply not what they are being asked to decide
     (when-not guided? (list " " [:span.muted "@ "] (term-link view context)))
     " " [:span.p-chips (line-chips verdict) (alternatives-hint (:correction row))]
     (shape-buttons row)
     [:span.p-acts
      (cond
        storable?
        (list [:button.p-accept {:type "button" :data-accept "" :title "accept (a)"} "✓"]
              [:button.p-reject {:type "button" :data-reject "" :title "reject (x)"} "✗"])

        report-only?
        [:span.muted {:title (str "the correction found something it cannot repair, so "
                                  "there is no shape here to store")} "report only"]

        :else
        [:span.muted {:title "the KB refuses this shape — pick another, or leave it"}
         "nothing to store"])]
     ;; `dense` renders no sentence of explanation unasked — not folded behind a
     ;; `<details>`, *absent*, so the row is the gutter and nothing else.  The reason is
     ;; still one keystroke away, because the `?` returns with the level.
     (when-not dense? (line-why view verdict))
     ;; `guided` spells the reason out rather than folding it, and says what the line
     ;; would mean.  Both are the same data the `?` holds at `working`; the level decides
     ;; whether the reader has to ask.
     (when guided?
       (list
        (for [p (:problems verdict)]
          [:p.p-said [:span.tag (name (:type p :error))] " " (:message p)])
        (when-let [c (:correction verdict)]
          (when (:why c) [:p.p-said (:why c)]))
        (line-gloss (v/local-kb (:kb view)) chosen)))
     ;; what the row posts back: the original and its position (so a shape choice is
     ;; re-derived, never trusted) and, only when there is something to store, the line
     ;; the commit would write.  Print vars bound off on the two that carry a form: both
     ;; are read back as EDN by `propose-line-post`, and an elided sentence — or an elided
     ;; context NAT — is legal EDN naming something else, so the round trip would
     ;; re-derive the shape of a form the reader never saw
     (let [edn (fn [x] (binding [*print-length* nil *print-level* nil] (pr-str x)))]
       (list
        [:input {:type "hidden" :name "from" :value (edn from)}]
        [:input {:type "hidden" :name "ctx" :value (edn context)}]))
     [:input {:type "hidden" :name "i" :value i}]
     (when storable?
       ;; print vars bound off — the value is read back as EDN, and an elided
       ;; sentence is legal EDN naming something else (see `selection/edit-line`)
       [:input {:type "hidden" :name "line"
                :value (binding [*print-length* nil *print-level* nil]
                         (pr-str [chosen context]))
                :disabled "disabled"}])]))

(defn- proposal-lines
  "The proposed entries, one row each: the verdict glyph, the sentence — struck through
  and followed by its rewrite where a correction restates it — the chip gutter, and the
  `?`.

  A corrected original is shown **superseded rather than replaced**, because the rewrite
  is a proposal about a proposal: hiding what the model actually wrote would hide the
  error class the correction pass exists to catch, and the author is the one deciding
  between the two."
  [view rows level]
  [:ul.propose-lines {:role "grid" :aria-label "proposed lines"
                      :class (str "p-at-" (name level))}
   (map-indexed #(proposal-row view %1 %2 level) rows)])

(defn- proposal-note
  "What came back when no lines did — the status said plainly, with the model's own text
  under it (bounded, because an answer that could not be read is exactly the answer that
  might be enormous).

  On the stub the status is beside the point and the *reason* is the whole story: there
  is no model. Saying \"the answer could not be read\" of a machine with nothing
  configured would send a reader looking for a bug in the parser."
  [{:keys [status text]} kind]
  (let [said (case status
               :unparseable "The model's answer could not be read as assertions."
               :refused     "The model declined to answer."
               :exhausted   "The model did not produce an admissible answer, and the turn budget ran out."
               :too-large   "The prompt does not fit the model's context window."
               :no-term     "That page has no term to write about."
               :error       "The turn failed."
               "The model proposed nothing new.")]
    (list (if (= :stub kind)
            [:p "No model is configured, so this ran against the offline stub — it "
             "proposes nothing. Set " [:code "VAELII_LLM_PROVIDER"] " to "
             [:code "ollama"] " or " [:code "anthropic"] "."]
            [:p said])
          (when (seq text)
            [:pre.propose-raw (let [t (str/trim (str text))]
                                (if (> (count t) 600) (str (subs t 0 600) " …") t))]))))

(def ^:private verdict-legend
  "What the gutter's four glyphs mean, spelled out once under the list rather than
  repeated per row.  A glyph a reader has to guess at is worse than the word it saved."
  [:p.legend
   [:span.chip.chip-ok [:span.chip-g "✓"] " ok"] " the KB would take it as written · "
   [:span.chip.chip-coins [:span.chip-g "+"] " coins"] " it invents vocabulary · "
   [:span.chip.chip-uncertain [:span.chip-g "!"] " uncertain"] " a rewrite the engine "
   "cannot decide for you · "
   [:span.chip.chip-refused [:span.chip-g "✗"] " refused"] " a check says no. "
   [:b "?"] " opens the reason."])

(defn- verdict-counts
  "The gutter in one line: how many lines fell under each verdict, worst first, and the
  zeroes left out — a proposal with nothing refused should not have to say so."
  [verdicts]
  (let [n (verdict/summary verdicts)]
    [:p.muted (interpose " · "
                         (for [k verdict/verdict-rank :when (pos? (n k 0))]
                           [:span (n k) " " (name k)]))]))

(def ^:private review-keys
  "The keys the review list answers to, said where a reader will look for them.  Reviewing
  ten lines has to be possible without the mouse, which means the hands never leave the
  home row: move, decide, choose a shape."
  [:p.hint [:b "Keys: "]
   [:kbd "j"] " / " [:kbd "k"] " move · "
   [:kbd "a"] " accept · " [:kbd "x"] " reject · "
   [:kbd "1"] "–" [:kbd "9"] " choose a shape."])

;; ---- what accepting would do (`v/preview`) ------------------------------
;; The chips say whether a line would be *admitted*; this says what the accepted set
;; would *mean*.  They are different questions, and the second is the one a line can pass
;; on its own and fail together: two lines each admissible alone can be a disjointness
;; clash, and a rule can withdraw a belief nothing about the rule mentions.
;;
;; It is `v/preview` (docs/preview.md), so it stores nothing and hands the KB back at the
;; same handles — which is what lets this run on every change of the accepted set rather
;; than once, behind a confirmation, at the end.

(def ^:private preview-max-results
  "How many lines of each half of the diff to render.  A batch whose conclusions cascade
  has an honest answer in the thousands and a panel has no use for it; `preview` reports
  `:bounded?` when the cap bit, and the panel says so rather than implying it showed
  everything."
  50)

(defn- consequence-item
  "One consequence, linked where there is something to link to.  A datum the batch would
  **create** has no handle until it is stored — `preview` reports nil rather than the
  number it briefly held — so the line that explains it is the rule that would conclude
  it, which the preview carries.  A datum that already exists (a default this batch
  defeats, one it revives) keeps its handle either way, and that one links."
  [view {:keys [handle sentence context premise? justification reason]}]
  [:li
   (render-form view sentence)
   " " [:span.muted "@ "] (term-link view context)
   (when reason [:span {:class (str "tag tag-" (name reason))} (name reason)])
   (when-let [rule (:rule justification)]
     (list " " [:span.muted "by "] (render-form view rule)))
   (when (and (not premise?) (nil? justification) (nil? reason))
     [:span.muted " derived"])
   (when handle
     (list " " [:a.muted {:href (str "/why/" handle)} "why"]))])

(defn- consequence-group
  "One collapsed group.  `<details>` so the summary is the whole panel until a reader
  asks, and so opening one costs no script and no request — the consequences are already
  rendered, just folded."
  [view {:keys [class glyph label items open?]}]
  (when (seq items)
    [:details.p-cons {:class class :open (when open? "open")}
     [:summary [:b glyph] " " (count items) " " label]
     [:ul.p-cons-list (map #(consequence-item view %) items)]]))

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
  "What accepting the currently-accepted lines would do, as `v/preview` answers it.

  The refused group leads and opens itself: it is the one a reader must not miss, and it
  is what catches a stratification cycle or a disjointness clash *before* anything is
  stored.  The other two are counts until asked for."
  [view n {:keys [believed-added believed-removed contradictions bounded?] :as result}]
  (let [bad (refusal-items result)]
    (list
     [:h5.p-cons-head "Consequences of accepting " n (if (= 1 n) " line" " lines")]
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
                             [:span (render-form view sentence)
                              (when handle
                                (list " " [:a.muted {:href (str "/why/" handle)} "why"]))]))])]])
     (consequence-group view {:class "p-cons-add" :glyph "+" :label "newly believed"
                              :items believed-added})
     (consequence-group view {:class "p-cons-drop" :glyph "−" :label "no longer believed"
                              :items believed-removed})
     (when (and (empty? bad) (empty? contradictions)
                (empty? believed-added) (empty? believed-removed))
       [:p.muted "Nothing follows: the accepted lines add no belief and withdraw none."])
     (when bounded?
       [:p.hint "This preview was cut short at " preview-max-results
        " lines per group — there is more than is shown."])
     [:p.hint "Nothing here is stored. The KB is exactly as it was before this ran."])))

(defn- review-form
  "The reviewable list and the one button that writes.

  Accepting is a **disabled field flipped on**, so the form submits exactly the accepted
  lines and the payload is the browser's own — no script assembles it, and a line with
  nothing storable has no field to flip. The whole list is one form, so what it posts is
  one batch and lands in one settle."
  [view rows level]
  ;; `hx-disabled-elt` is the form's own — it disables the commit button while the write
  ;; is in flight.  htmx would hand it down to every request *inside* the form (the level
  ;; buttons, the shape buttons, the consequence preview), and `find` resolves within the
  ;; requesting element, none of which contains a submit button: each would disable
  ;; nothing and log that its selector matched nothing.  `hx-disinherit` keeps it here.
  [:form.propose-apply {:hx-post "/propose/apply" :hx-target "#propose-result"
                        :hx-select "unset" :hx-swap "innerHTML"
                        :hx-disabled-elt "find button[type='submit']"
                        :hx-disinherit "hx-disabled-elt"}
   (level-switch level)
   (proposal-lines view rows level)
   ;; the originals ride the form, so switching level re-renders this very proposal
   ;; without another turn — the model is asked once and read as many ways as wanted
   [:input {:type "hidden" :name "at-level" :value (name level)}]
   ;; The consequence preview recomputes off the accepted set, not off the keystroke:
   ;; `delay` debounces, so holding `a` down the list costs one preview rather than ten.
   ;; It includes the form, so what it previews is exactly the enabled `line` fields the
   ;; commit button would post — one payload, assembled by the browser, read twice.
   [:div#p-preview.p-preview
    {:hx-post    "/propose/preview"
     :hx-trigger "accepted-changed from:body delay:400ms"
     :hx-include ".propose-apply"
     :hx-target  "this"
     :hx-select  "unset"
     :hx-swap    "innerHTML"
     :aria-live  "polite"}
    [:p.muted "Accept a line to see what it would do."]]
   [:div.p-commit
    [:button.primary {:type "submit"} "Store accepted"]
    [:span#p-count.muted {:role "status" :aria-live "polite" :aria-atomic "true"}
     "0 accepted"]]
   review-keys])

(defn- proposal-result
  "One turn's answer, as it lands in `#propose-result`.

  The per-line reading is computed **here** rather than by the session, because it is
  what a reviewer needs and not what the loop needs: the session checks a batch to decide
  whether to repair it, and this asks three further questions of the same lines.  The
  check it already ran is passed through rather than repeated."
  [view {:keys [status notes problems] :as result} kind kb level]
  (let [verdicts (when (and kb (seq (:add (:batch result))))
                   (verdict/verdicts kb (:batch result)
                                     {:problems (:rejections result)}))]
    [:div.propose-answer
     (proposal-tally view result kind (:elapsed-ms result) level)
     (if (seq verdicts)
       (list (verdict-counts verdicts)
             (review-form view (mapv #(verdict/review-of kb %) verdicts) level)
             verdict-legend)
       (proposal-note result kind))
     (when (seq notes) [:p.hint [:b "The model's notes: "] notes])
     (when (seq problems)
       [:ul.edit-errors (for [p problems] [:li [:span.tag "unreadable"] " " p])])
     [:p.hint "The turn stored nothing. What you accept is stored — everything else is "
      "read and dropped"
      (when-not (= :ok status) ", and a refused line is one the KB would not take")
      "."]]))

(defn- propose-panel
  "The panel itself: an instruction box for the term, and the empty region a turn's
  answer swaps into.  Rendering it asks the model nothing and probes no host — it reads
  the configured backend's *name* only, so a term page costs exactly what it did before.

  `remote?` is the one state the panel cannot serve: a proposal reads the term's
  neighbourhood, its vocabulary and its checks through dozens of KB calls, which is not
  something to run a round-trip at a time against a daemon."
  [view term ctx {:keys [remote?]}]
  (let [kind (or (llm-provider/configured) :stub)]
    [:div#propose.propose
     [:h3 "Propose knowledge " [:span.muted "· " (name kind)
                                (when (= :stub kind) " (offline — set VAELII_LLM_PROVIDER)")]]
     (if remote?
       [:p.muted "The browser is attached to a daemon, so this reads a KB it does not "
        "hold. Proposing needs the KB in process."]
       (list
        [:form.propose-form {:hx-post "/propose" :hx-target "#propose-result"
                             :hx-select "unset" :hx-swap "innerHTML"
                             :hx-disabled-elt "find button"}
         [:input {:type "hidden" :name "q" :value (pr-str term)}]
         (when ctx [:input {:type "hidden" :name "ctx" :value (pr-str ctx)}])
         [:label {:for "propose-message"} "Ask for knowledge this page is missing"]
         [:textarea#propose-message {:name "message" :rows 2 :spellcheck "false"
                                     :placeholder "flesh out where it lives and what it eats"}]
         [:div.editor-actions [:button.primary {:type "submit"} "Propose"]]]
        [:p.hint "The model is shown this page's sentexes and the vocabulary "
         (term-link view term) "'s type neighbourhood licenses, and answers with "
         "type-level knowledge. It writes nothing: every line comes back for review."]))
     [:div#propose-result]]))

(defn propose-post
  "Run one proposal turn for a term and render what came back.

  Every bound the panel places on the model is here: the token cap, the transport
  deadline, and the session's own turn budget.  A throw out of the provider is caught and
  rendered — a browser panel is not the place to surface a stack trace, and a model
  backend is the one dependency that fails by *not answering* rather than by erroring."
  [{:keys [kb] :as view} term ctx message level]
  (let [{:keys [kind provider]} (proposal-provider)
        started (System/currentTimeMillis)]
    (frag
     (if-let [local (v/local-kb kb)]
       (try
         (proposal-result view
                          (llm/propose-page local (cond-> {:term term
                                                           :message (str message)
                                                           :provider provider
                                                           :max-tokens propose-max-tokens}
                                                    ctx (assoc :context ctx)))
                          kind local level)
         (catch Throwable t
           (trove/log! {:level :warn :id ::propose-failed :error t
                        :msg "a proposal turn failed" :data {:term term :kind kind}})
           (proposal-result view
                            {:status :error :elapsed-ms (- (System/currentTimeMillis) started)
                             :text (str (.getMessage t))}
                            kind nil level)))
       (proposal-result view {:status :error :text "no in-process KB to propose against"}
                        kind nil level)))))

(defn propose-line-post
  "Re-render one row on shape `n`.  What arrives is the **original** sentence and a
  number; the shape itself is re-derived here from `correct`, which is a pure function of
  the KB and what the model wrote — so a sentence cannot be smuggled into the row by
  editing the request, and the chips the reader ends up committing against were computed
  from the KB rather than sent to it."
  [{:keys [kb] :as view} from ctx i n level]
  (frag
   (if-let [local (v/local-kb kb)]
     (proposal-row view (or i 0) (verdict/review local from ctx n) level)
     "")))

(defn propose-level-post
  "The same proposal, re-read at another density.

  The originals ride the list's own hidden fields, so this re-derives every verdict from
  the KB and renders the rows again — **without another turn**.  That is the whole claim
  of the level control: a reader who opens `guided`, works out what a refusal meant and
  drops to `dense` has asked the model exactly once."
  [{:keys [kb] :as view} froms ctxs level]
  (frag
   (if-let [local (v/local-kb kb)]
     (let [rows (mapv (fn [f c] (verdict/review local f c nil)) froms ctxs)]
       (list (level-switch level)
             (proposal-lines view rows level)
             [:input {:type "hidden" :name "at-level" :value (name level)}]))
     "")))

(defn- accepted-entries
  "The `[sentence context]` entries a commit posted.  `line` repeats once per accepted
  row, so ring hands back a string or a vector of them; anything unreadable is dropped
  with a problem rather than guessed at."
  [lines]
  (reduce (fn [acc s]
            ;; `Throwable`, as every other untrusted-EDN read in this namespace: a deeply
            ;; nested form overflows the reader's stack with a `StackOverflowError`, which
            ;; an `Exception` catch lets escape — and the browser has no exception
            ;; middleware, so it leaves the handler entirely where an unreadable line is
            ;; the ordinary answer this exists to give.
            (let [form (try {:ok (edn/read-string s)} (catch Throwable e {:bad (.getMessage e)}))]
              (cond
                (:bad form)
                (update acc :problems conj {:type :unreadable
                                            :message (str "does not read as EDN: " (:bad form))})
                (and (vector? (:ok form)) (<= 2 (count (:ok form)) 3))
                (update acc :entries conj (:ok form))
                :else
                (update acc :problems conj {:type :shape
                                            :message (str "expected [sentence context], got "
                                                          (pr-str (:ok form)))}))))
          {:entries [] :problems []}
          (cond-> lines (string? lines) vector)))

(defn- report-only-problems
  "The accepted lines a correction found something in but could not repair.

  `correct/apply-correction` answering nil is what says so, and it is asked **here**
  rather than trusted from the client: the row renders no field for such a line, but the
  field is what the browser sends, and a check that only runs in the browser is not a
  check.  Storing one would store the sentence the correction was warning about."
  [kb entries]
  (for [[sentence context] entries
        :let [row (verdict/review kb sentence context 1)]
        :when (:report-only? row)]
    {:type :report-only
     :sentence sentence
     :message (str (pr-str sentence) " — " (:why (:correction row)))}))

(defn propose-preview-post
  "What the accepted lines would do, without doing it.

  The same payload the commit button posts, read through `v/preview` instead of
  `v/edit!` — so the panel a reader decides from is computed from the very batch that
  would land, rather than from a reconstruction of it.  A read: `preview` hands the KB
  back at the same handles, which is why this can run on every change of the accepted
  set instead of once behind a confirmation.

  A report-only line is held back rather than previewed: the commit refuses it
  (`report-only-problems`), so previewing it would promise a consequence the button will
  not deliver — and it would ask the engine about the very sentence the correction was
  warning about."
  [{:keys [kb] :as view} lines]
  (frag
   (let [local (v/local-kb kb)
         {:keys [entries]} (accepted-entries lines)]
     (cond
       (nil? local)
       [:p.muted "A preview runs inference, so it needs the KB in this process."]

       (empty? entries)
       [:p.muted "Accept a line to see what it would do."]

       :else
       (let [held (set (map :sentence (report-only-problems local entries)))
             ok   (into [] (remove #(held (first %))) entries)]
         (list
          (when (seq held)
            [:p.muted (count held)
             (if (= 1 (count held)) " accepted line is" " accepted lines are")
             " report-only and left out — the commit refuses them."])
          (if (empty? ok)
            [:p.muted "Nothing left to preview."]
            (consequence-panel view (count ok)
                               (v/preview kb {:add ok}
                                          {:max-results preview-max-results})))))))))

;; ---- what followed from a commit ----------------------------------------
;;
;; A commit reports the lines it stored, which is what the writer already said.  The
;; interesting half is what the KB did with them, and it comes from two places that are
;; *not* the same mechanism — the callout keeps them apart rather than blurring them into
;; one list of "conclusions":
;;
;;   - a **rule fired**.  There is a real derived sentex with a real justification, so it
;;     is believed in the JTMS sense, has a handle, and its whole proof is a click away.
;;   - a **type subsumes**.  `(genl dog animal)` plus `(dog Muffet)` makes Muffet an animal,
;;     and the engine deliberately never materializes `(animal Muffet)`: matching fans a
;;     functor out over its genl spec closure instead, which is what lets a hundred
;;     million facts avoid a hundred million more (docs/taxonomy.md).  So there is no
;;     record, no justification and nothing to link — the claim is answered on demand by
;;     `isa?` / `ask`.  It is still the single most convincing thing a two-line KB can
;;     show, so it is shown, and shown as what it is.
;;
;; Saying "derived" of the second kind would teach a first-time reader something false
;; about what the KB stores, and the first thing they will do is go looking for the record.

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
          ;; since everything above it is above the further one too — then the name, so
          ;; two supertypes the same distance up are ordered by something a reader can
          ;; account for rather than by where the closure set happens to hold them.  The
          ;; list is capped, so the tie decides which claims are shown
          super (sort-by (juxt #(- (count (v/genls kb %))) print-key) (v/genls kb t))
          :let  [claim (list super x)]
          :when (and (not= super t) (not= 'thing super) (not (stated claim)))]
      {:sentence claim :context (:context sx) :type t :individual x})))

(defn- callout-item
  "One consequence line: the claim, and the one-level `because` under it."
  [view {:keys [sentence handle justification type individual]}]
  [:li.callout-line
   (render-form view sentence)
   (if justification
     [:span.muted.callout-why " because "
      (interpose ", " (map #(render-form view %) (:antecedents justification)))
      (when-let [r (:rule justification)]
        (list " and the rule " (render-form view r)))
      (when handle
        (list " · " [:a {:href (str "/why/" handle)} "proof"]))]
     [:span.muted.callout-why " because "
      (render-form view (list type individual))
      ", and every " (render-form view type) " is a "
      (render-form view (first sentence))])])

(defn- derived-callout
  "**You didn't say this, but it follows** — the consequences of a commit, capped.

  `result` is `v/edit-with-consequences!`'s answer and `stored` the sentexes the batch
  wrote.  Renders nothing at all when nothing followed: a callout reading \"0 new
  conclusions\" is worse than silence, because it makes the empty case as loud as the
  interesting one."
  [view result stored]
  (let [derived (into [] (remove :premise?) (:believed-added result))
        typed   (entailed-supertypes view stored)
        all     (concat derived typed)
        shown   (take callout-cap all)
        more    (- (count all) (count shown))]
    (when (seq all)
      [:div.callout
       [:h4 "You didn't say this, but it follows"]
       [:ul.callout-list (for [c shown] (callout-item view c))]
       (when (pos? more)
         [:p.muted "and " more (if (= 1 more) " more consequence" " more consequences")
          " — every one of them is on the "
          [:a {:href "/stats"} "statistics page"] "."])])))

(defn- applied-result
  "What a commit did: the count, every sentex it stored, and what followed from them."
  [view result]
  (let [added (flatten (:added result))
        ss    (keep #(v/sentex (:kb view) %) added)]
    (prime-belief! view (map :id ss))
    [:div.propose-answer
     [:h4 "Stored " (count added) (if (= 1 (count added)) " line" " lines")
      [:span.muted " · one settle"]]
     (if (seq ss)
       (sentex-list view ss)
       [:p.muted "nothing was accepted"])
     (derived-callout view result ss)
     [:p.hint "These are premises now, like anything typed into the assert form: "
      "select a row to edit or retract it."]]))

(defn propose-apply-post
  "Store the accepted lines — the panel's one write, and the only one on this path.

  Everything up to here proposes; this applies, and it applies the way the editor does:
  `check-edit` over the whole batch first, and **`v/edit!` once** so the adds land in one
  settle rather than settling per line.  A batch with any problem stores nothing, since a
  partial commit of a reviewed set is the outcome nobody chose.

  **A remote target is refused here as it is at every other door on this path** — the
  panel, the turn and the preview all say the proposal needs the KB in process.  This is
  the one that writes, and it is the one that must not be the exception: the
  report-only check is a KB read, so without an in-process KB it does not run, and the
  line it exists to hold back would be stored instead.  A check that does not run is not
  a check, which is the reason the check is on this side at all."
  [{:keys [kb] :as view} lines]
  (frag
   ;; the target question **before** the batch is read, since the reads below are the
   ;; ones that would go over the wire
   (if-let [local (v/local-kb kb)]
     (let [{:keys [entries problems]} (accepted-entries lines)
           batch {:add entries :remove []}
           refusals (concat problems
                            (report-only-problems local entries)
                            (when (seq entries) (map #(select-keys % [:type :message])
                                                     (v/check-edit kb batch))))]
       (cond
         (empty? entries)
         [:div.propose-answer [:p.muted "Nothing was accepted, so nothing was stored."]]

         (seq refusals)
         [:div.propose-answer
          [:h4 "Nothing was stored"]
          [:ul.edit-errors (for [p refusals]
                             [:li [:span.tag (name (:type p :error))] " " (:message p)])]
          [:p.hint "The batch is applied whole or not at all. Propose again, or write the "
           "line yourself on the " [:a {:href "/assert"} "assert form"] "."]]

         :else
         (applied-result view (v/edit-with-consequences! kb batch))))
     [:div.propose-answer
      [:p.muted "A proposal is applied through the KB in this process, and the browser "
       "is attached to a daemon. Nothing was stored."]])))

;; ---- the hierarchy trees, one level at a time ---------------------------
;;
;; A hierarchy is wide as well as deep, and the front page is the first thing anyone
;; opens against a KB whose size they have not chosen — the catalog will load an
;; ontology with hundreds of thousands of `genl` edges.  So a level is read from the
;; index when it is opened rather than the whole relation being read to draw one, and
;; every list here is paged like an index group.

(def ^:private tree-cap
  "How many direct children of one node render at a time."
  50)

(def ^:private front-cap
  "How many rows the front page's flat lists — core predicates, disjointness — render at
  a time."
  50)

(def ^:private sortable-cap
  "How many rows a flat list will realize in order to sort them.  Alphabetical order is
  worth reading and costs nothing at the size the shipped schema has; realizing an
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
  "The direct sub-nodes of `node` under transitivity relation `pred`, lazily and deduped
  (one edge asserted in two contexts is two sentexes and one child).

  One index read, not a walk: the pattern pins an argument *after* a variable, which
  `query` answers from the predicate-scoped argument root (`[:argument-root pred 2
  node]`, docs/indexing.md), so the cost is this node's own fan-out rather than the
  number of edges in the KB."
  [kb pred node]
  (->> (v/sentexes-matching kb (list pred '?sub node) '?ctx)
       (keep (fn [s] (let [[_ sub super] (:sentence s)]
                       (when (and sub (= super node)) sub))))
       (distinct)))

(defn- parent-terms
  "The direct super-nodes of `node` under transitivity relation `pred` — `child-terms`'
  mirror, and bounded the same way: the pattern pins `node` in argument position **1**,
  which `query` answers from the predicate-scoped argument root (`[:argument-root pred 1
  node]`), so the cost is this node's own fan-*in* rather than the number of edges in the KB.
  Deduped for the same reason — one edge asserted in two contexts is two sentexes and one
  parent."
  [kb pred node]
  (->> (v/sentexes-matching kb (list pred node '?super) '?ctx)
       (keep (fn [s] (let [[_ sub super] (:sentence s)]
                       (when (and super (= sub node)) super))))
       (distinct)))

(defn- expandable?
  "Whether a tree node gets a disclosure control.  `count-with-arg` at position 2
  counts the facts holding `t` there — summed over the slot roster's predicates, every
  `(pred sub t)` among them and anything else binary that mentions it there — so it is
  a cheap *upper* bound on having children.  Wrong only in the safe direction: a node whose second-position facts are
  all something else opens to \"none\", and no real child is ever hidden."
  [kb t]
  (pos? (v/count-with-arg kb 2 t)))

(defn- tree-rows
  "One level of a hierarchy: `node`'s direct children from `offset`, each either a leaf
  or a disclosure that fetches its own children the first time it is opened.  Bare
  `<li>`s, so the same call answers the page and the continuation that extends it."
  [{:keys [kb] :as view} pred node offset]
  (let [;; an upper bound on this level's width: `sortable?` is therefore decided without
        ;; reading the level.  A node wide enough to be worth not sorting is a node whose
        ;; children nobody is going to read alphabetically anyway.  One count per
        ;; predicate holding `node` at argument 2 and never the extent (the shape
        ;; `core/count-with-arg` states), paid once per rendered child by `expandable?`
        width    (v/count-with-arg kb 2 node)
        sortable (<= width sortable-cap)
        kids     (cond->> (child-terms kb pred node) sortable by-print-key)
        shown    (into [] (comp (drop offset) (take (inc tree-cap))) kids)
        ;; a child's disclosure asks for *its own* children; the sentinel asks for more
        ;; of this level, which is the one place `node` is the right node
        href     (fn [n off] (str "/tree/rows?rel=" (url-enc (str pred))
                                  "&node=" (url-enc (str n)) "&offset=" off))]
    (list
     (for [t (take tree-cap shown)]
       (if (expandable? kb t)
         ;; `hx-select="#main"` is set on the body so every boosted link swaps the main
         ;; column, and it is **inherited** — against a fragment of bare rows it selects
         ;; nothing and the open would swap in nothing.  So a disclosure says explicitly
         ;; that it selects nothing out of what it fetched, exactly as a sentinel does.
         [:li [:details {:hx-get (href t 0) :hx-trigger "toggle once"
                         :hx-target "find ul.tree-kids" :hx-select "unset"
                         :hx-swap "innerHTML" :hx-indicator "#page-indicator"}
               [:summary (term-link view t)]
               [:ul.tree-kids [:li.muted "…"]]]]
         [:li (term-link view t)]))
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
  of what there is.  A truncated view that does not announce itself is worse than no
  view."
  [shown total note]
  [:p.muted "showing " shown " of " total (when note (str " — " note))])

(defn- first-sentence
  "A scannable one-line gloss of a comment for a flat list — its first sentence, or a
  hard-capped head when the first sentence runs long.  The whole text is a click away on
  the term's own page (and hovers as a `title`), so the front page stays a list rather
  than a wall of prose."
  [text]
  (let [t   (str/trim (str text))
        dot (str/index-of t ". ")]
    (cond
      (and dot (<= (inc dot) 160)) (subs t 0 (inc dot))     ; a complete first sentence
      (<= (count t) 160)           t                        ; a short comment, whole
      :else                        (str (str/trimr (subs t 0 160)) "…"))))

(defn- comment-rows
  "One page of the core-predicate list, from `offset`, with the sentinel that fetches the
  next.

  Read from the **functor root**, not from `(comment ?term ?text)`.  A wholly-open
  pattern gives the trie nothing to narrow on, so it fans over every child token at every
  level: `take` would then bound the records fetched and not the candidates enumerated,
  and showing fifty rows would cost a walk of every commented term in the KB.  The root
  is one posting set, and a page out of it costs a page."
  [{:keys [kb] :as view} offset]
  (let [total (v/count-with-functor kb 'comment)
        ;; the term, then the text: a term carrying two comments — the shipped ontology
        ;; gives each one, a KB adding a gloss of its own gives two — ties on the term
        ;; alone, and the tie falls to the functor root's own order, which is ascending
        ;; handle.  `core-context/comment-of` keys the same pair for the same reason
        rows  (cond->> (v/sentexes-with-functor kb 'comment)
                (<= total sortable-cap)
                (sort-by (juxt (comp print-key second :sentence)
                               (comp print-key #(nth (:sentence %) 2 nil)))))
        shown (into [] (comp (drop offset) (take (inc front-cap))) rows)
        page  (take front-cap shown)]
    ;; the root is what is *stored*; belief is the page's own question, asked in one read
    (prime-belief! view (map :id page))
    (list
     (for [s     page
           :when (and (= :true (:truth s)) (believed? view (:id s)))
           :let  [[_ term text] (:sentence s)]]
       ;; name prominent, first-sentence gloss muted; the whole comment hovers as a
       ;; title and is on the term's own page — the front page stays scannable
       [:li {:title text} (term-link view term)
        [:span.muted " — " (first-sentence text)]])
     (when (> (count shown) front-cap)
       (more-rows (str "/front/rows?section=predicates&offset=" (+ offset front-cap))
                  (str "show " (- total offset front-cap) " more"))))))

(defn- disjoint-rows
  "One page of the disjointness list, out of the pairs `disjoint-pairs` computed.  They
  arrive realized because a metatype separates its members by being *consulted* rather
  than by storing a clique, so the induced half has to be worked out either way — and
  both halves are bounded by the separations an ontology declares rather than by its
  size."
  [view pairs offset]
  (let [ordered (by-print-key pairs)
        shown   (into [] (comp (drop offset) (take (inc front-cap))) ordered)]
    (list
     (for [[a b] (take front-cap shown)]
       [:li (term-link view a) " ⊥ " (term-link view b)])
     (when (> (count shown) front-cap)
       (more-rows (str "/front/rows?section=disjoint&offset=" (+ offset front-cap))
                  (str "show " (- (count ordered) offset front-cap) " more"))))))

;; ---- the small useful amount --------------------------------------------
;;
;; The first fifty of a set in an order nobody chose is not a short answer on a real
;; corpus, it is an arbitrary sample of a long one: fifty of 13,196 contexts
;; alphabetically, fifty of 27,196 separated pairs, all 4,721 non-empty contexts in one
;; table.  Pagination alone does not fix that — nobody
;; scrolls 27,196 pairs — so where a **cheap ranking** exists the page shows the top of it
;; and says what the whole is, and where one does not the list is capped and continues on
;; scroll.  What is *not* here is a ranking that costs more than the page: ordering the
;; type tree's 6,260 children of `thing` by subtree size reads better and measured 2.2 s,
;; so the tree stays in index order and stays lazy.

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
  the order is a function of the content and not of the roster's own."
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

(defn default-page [{:keys [kb types] :as view}]
  (let [roots     (context-roots kb)
        genls     (v/count-with-functor kb 'genl)
        comments  (v/count-with-functor kb 'comment)
        ctx-count (count (v/contexts kb))
        pairs     (disjoint-pairs kb)]
    (render view "upper ontology"
            [:p.muted "A contextualized common-sense knowledge base."]
            ;; what this KB *is*, before anything it contains.  Four O(1) reads, and the
            ;; question a reader landing on an unfamiliar corpus asks first — which is why
            ;; it belongs here and not only on the stats page
            [:div.stats-grid
             (stat-card "Sentexes" (v/sentex-count kb))
             (stat-card "Types" (count @types))
             (stat-card "Contexts" ctx-count)
             (stat-card "Terms" (v/term-count kb))]
            [:p [:a.action {:href "/demo"} "Watch belief change"]
             [:span.muted " — a conclusion believed, then not, then believed again, in "
              "three clicks. The thing a database cannot do."]]
            [:p [:a.action {:href "/reasoning"} "What this ontology can work out"]
             [:span.muted " — every kind of inference it does, each as a live question "
              "over the sentexes it reasons from."]]
            [:p [:a {:href "/levels"} "Lookup-to-query stack"]
             [:span.muted " — trace a goal through the eight levels of inference."]]
            [:p [:a.action {:href "/assert"} "Assert a sentex"]
             [:span.muted " — add knowledge; every line is checked before anything is stored."]]
            legend
            badge-legend
            [:h2 "Contexts " [:span.muted "(genlCx)"]]
            (if roots
              [:ul.tree (for [r roots]
                          (if (expandable? kb r)
                            [:li [:details {:open "open"}
                                  [:summary (term-link view r)]
                                  [:ul.tree-kids (tree-rows view 'genlCx r 0)]]]
                            [:li (term-link view r)]))]
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
                           [:li (term-link view c)
                            [:span.muted " — " (commas n) " sentexes"]])]
                    [:p.muted (commas (count ranked)) " of " (commas ctx-count)
                     " contexts hold something. " [:a {:href "/stats"} "All of them by size"]
                     ", or search from the header."])
                   [:p.muted (commas ctx-count) " contexts — too many to size. "
                    "Search from the header."]))))
            [:h2 "Types " [:span.muted "(genl, rooted at thing)"]]
            ;; the root is drawn open, as the context roots are: the heading names it, and
            ;; a tree whose stated root is not on the page reads as a list of orphans
            [:ul.tree [:li [:details {:open "open"}
                            [:summary (term-link view 'thing)]
                            [:ul.tree-kids (tree-rows view 'genl 'thing 0)]]]]
            [:p.muted (commas genls) " genl edges — a subtype list opens when you open its node."]
            ;; titled by what it is.  On the shipped schema every commented term is engine
            ;; vocabulary; on an imported corpus there are 105,882 of them and calling that
            ;; "core predicates" is a claim the page cannot make
            [:h2 (if (> comments sortable-cap) "Documented terms" "Core predicates")]
            [:ul (comment-rows view 0)]
            (when (> comments sortable-cap)
              [:p.muted (commas comments) " terms carry a " [:code "comment"]
               " — index order, too many to sort. Search from the header for one."])
            [:h2 "Disjointness"]
            (if (<= (count pairs) front-cap)
              [:ul (disjoint-rows view pairs 0)]
              (let [{:keys [distinct top]} (separating-types pairs)]
                (list
                 [:p.muted (commas (count pairs)) " separated pairs, declared and "
                  "metatype-induced, over " (commas distinct) " types — too many to read as "
                  "pairs, so: the types separated from the most. Any type's own separations "
                  "are on its page."]
                 [:ul (for [[t n] top]
                        [:li (term-link view t)
                         [:span.muted " — disjoint from " (commas n)
                          (if (= 1 n) " type" " types")]])]))))))

(defn tree-rows-page
  "One node's children, as bare rows — what a disclosure fetches when it is opened, and
  what its `show more` sentinel fetches to extend it."
  [view pred node offset]
  (frag (tree-rows view pred node offset)))

(defn front-rows-page
  "One more page of a front-page list."
  [view section offset]
  (frag (case section
          "predicates" (comment-rows view offset)
          "disjoint"   (disjoint-rows view (disjoint-pairs (:kb view)) offset)
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
  fetches the next when it scrolls into view.  `ranked` is `contexts-by-size`'s answer, so
  the rows are the top of an order rather than a slice of an arbitrary one — which is what
  makes a capped table an *answer* and not a truncation."
  [view ranked offset]
  (let [shown (into [] (comp (drop offset) (take (inc stats-table-cap))) ranked)]
    (list
     (for [[c n] (take stats-table-cap shown)]
       [:tr [:td (term-link view c)] [:td.num (commas n)]])
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
  "The represented dilemmas, a page at a time.  Belief for the page is one batched read —
  each row renders two sentexes and badges both."
  [{:keys [kb] :as view} offset]
  (let [ds (v/contradictions kb)]
    (prime-belief! view (mapcat #(map :handle (:sides %))
                                (take (+ offset ledger-cap 1) ds)))
    (ledger-rows "contradictions" ds offset
                 (fn [d] [:li (interpose " ⇄ " (map #(handle-ref view (:handle %)) (:sides d)))]))))

(defn- conflict-rows
  "The irreducible clashes among known-true content, a page at a time."
  [{:keys [kb] :as view} offset]
  (ledger-rows "conflicts" (v/conflicts kb) offset
               (fn [c] [:li (render-form view (:sentence c))])))

(defn- violation-rows
  "The dropped derivations, a page at a time.  The ledger accumulates across runs and is
  capped at the newest 1000, so which run dropped a conclusion is part of the entry rather
  than something the reader can infer from where it sits."
  [{:keys [kb] :as view} offset]
  (ledger-rows "violations" (v/violations kb) offset
               ;; **Not every entry is about a sentence.**  The cross-context reports and
               ;; both sweep notices carry a `:detail` and no `:sentence` or `:context` —
               ;; rendered unconditionally those became the text "nil" beside a live link
               ;; to `/term?q=nil`, since `term-link`'s fallback arm links whatever it is
               ;; handed.  And `:message` sits at the top level on `:non-confluent` and
               ;; `:aggregate` where every other kind puts it under `:detail`, so reading
               ;; only one of the two dropped the line those two exist to print.
               ;; the present-field arms are seqs rather than `[:span …]` wrappers, so an
               ;; entry that has a sentence renders exactly the markup it always did
               (fn [v] [:li [:span.tag (name (:violation v))]
                        (when-let [s (:sentence v)] (list " " (render-form view s)))
                        (when-let [c (:context v)] (list " @ " (term-link view c)))
                        (when-let [r (:run v)] [:span.muted " · run " r])
                        (when-let [m (or (:message (:detail v)) (:message v))]
                          [:span.muted " — " m])])))

(defn stats-rows-page
  "One more page of a stats-page list — what its scroll sentinel fetches.  Every section is
  recomputed rather than carried: each is a function of the KB, so a continuation asks the
  same question the page asked and gets the same order."
  [{:keys [kb] :as view} section offset]
  (frag (case section
          "contexts"       (context-count-rows view (contexts-by-size kb) offset)
          "contradictions" (contradiction-rows view offset)
          "conflicts"      (conflict-rows view offset)
          "violations"     (violation-rows view offset)
          "")))

(defn- exposed-clashes-section
  "The **standing** disjointness question: every term holding two types some context can
  see as disjoint, where each membership was admissible where it was written.

  Behind a control rather than in the page load, because `exposed-clashes` computes on
  demand and is not filed — unlike the ledgers above it, which `settle` fills as it goes.
  That difference is the point of asking: `settle` reports a clash as it *arises*, which
  is the incremental question an author wants while writing, so a KB that arrived all at
  once has nothing newly anything and every clash it holds is invisible until something
  asks.  An imported corpus is exactly that case."
  [{:keys [kb] :as view} asked?]
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
          ;; **Each half is a `[type context]` pair, and both halves are links.** Handing
          ;; the pair to `term-link` whole took its fallback arm, which links whatever it
          ;; is given — so the page offered `/term?q=[dog CxA]`, a term no KB holds,
          ;; for every clash it reported. The context is half of what the row says
          ;; anyway: a membership admissible where it was written is only interesting
          ;; beside *where* that was.
          ;;
          ;; The `:violation` guard is the other half of the same lesson. This read
          ;; returns only `:disjoint` today, and destructuring `:term`/`:held` without
          ;; asking is exactly the assumption that made `violation-rows` print "nil" when
          ;; a second entry shape arrived. A kind this does not know renders its own
          ;; message rather than a row of blanks.
          [:ul (for [{:keys [violation detail]} (take clash-cap cs)]
                 [:li
                  (if (= :disjoint violation)
                    (list (term-link view (:term detail)) " holds "
                          (interpose ", "
                                     (for [h (:held detail)]
                                       (let [[t c] (if (sequential? h) h [h nil])]
                                         (list (term-link view t)
                                               (when c
                                                 (list " " [:span.muted "in "]
                                                       (term-link view c))))))))
                    (list [:span.tag (name violation)] " "
                          (or (:message detail) "a standing clash")))
                  (when-let [vf (seq (:visible-from detail))]
                    [:span.muted " — visible together from "
                     (interpose ", " (for [c vf] (term-link view c)))])])]
          (when (> (count cs) clash-cap)
            (elided clash-cap (count cs) nil))])))])

(defn stats-page
  "KB-wide statistics: the headline counts (contexts, types, stored sentexes, and the
  reasoning-health tallies), what the last chaining run did and a control to run
  another, a contexts-by-size table, and — when non-empty — the actual contradictions,
  conflicts, and dropped-derivation violations.

  `clashes?` asks the standing disjointness question, which is computed rather than
  filed and so is not asked unless the reader asks for it.

  `note` is what a just-finished forward-chaining run reported, shown above the
  numbers it changed."
  ([view] (stats-page view nil false))
  ([view note] (stats-page view note false))
  ([{:keys [kb types] :as view} note clashes?]
   (let [ctxs    (vec (v/contexts kb))
         ;; the trie's own root count, not the sum of the table below it: a context the
         ;; taxonomy does not know (nothing states a `genlCx` edge for it) holds
         ;; sentexes all the same, and summing the table would quietly lose them
         total   (v/sentex-count kb)
         contras (v/contradictions kb)
         confs   (v/conflicts kb)
         viols   (v/violations kb)
         chain   (v/chain-stats kb)]
     ;; belief is primed by `contradiction-rows`, for the page it actually renders —
     ;; priming every side of every dilemma would be a read for rows nobody is shown
     (render view "stats"
             [:h2 "Statistics"]
             note
             ;; size counts and health counts read alike as bare numbers, so split them:
             ;; the health row reddens a non-zero count and an all-clear line says when
             ;; there is nothing to look at
             (let [warn (fn [xs] (if (seq xs) "stat-warn" "stat-ok"))]
               (list
                [:div.stats-grid
                 (stat-card "Contexts" (count ctxs))
                 (stat-card "Types" (count @types))
                 (stat-card "Sentexes" total)]
                [:p.stat-caption "Reasoning health"]
                [:div.stats-grid
                 (stat-card "Contradictions" (count contras) (warn contras))
                 (stat-card "Conflicts" (count confs) (warn confs))
                 (stat-card "Violations" (count viols) (warn viols))]
                (when (and (empty? contras) (empty? confs) (empty? viols))
                  [:p.health-ok "No contradictions, conflicts or dropped derivations — "
                   "belief is consistent across every context."])))
             ;; a reader who arrived here asking why something is slow wants the process
             [:p.muted "The caches, heap and profiler are on "
              [:a {:href "/caches"} "the caches page"] "."]
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
                [:tbody (context-count-rows view ranked 0)]]
               [:p.muted (commas (count ctxs)) " contexts — too many to size."])
             ;; the three ledgers, each a page at a time.  A row here is one or two whole
             ;; sentences with every subterm linked, so the count that matters is on the
             ;; card above and the list is for seeing what one looks like
             (when (seq contras)
               [:div
                [:h3 "Contradictions " [:span.muted "(represented dilemmas, believed at :default)"]]
                [:ul (contradiction-rows view 0)]])
             (when (seq confs)
               [:div
                [:h3 "Conflicts " [:span.muted "(irreducible clashes among known-true content)"]]
                [:ul (conflict-rows view 0)]])
             (when (seq viols)
               [:div
                [:h3 "Violations " [:span.muted "(derived conclusions dropped for a definitional breach)"]]
                [:p.muted "Newest first; the ledger itself caps at the most recent 1000."]
                [:ul (violation-rows view 0)]])
             ;; the standing disjointness question, behind a control because it is
             ;; computed on demand rather than filed — see the section below
             (exposed-clashes-section view clashes?)))))

;; ---- the concept graph at the top of a term page ------------------------
;;
;; The three type lines below say a term's supertypes, subtypes and disjointness exactly.
;; What they cannot say is its *shape* — that `dog` sits under `mammal` under `animal`,
;; that four things point at it and it points at two, that it is a leaf or a hub — and
;; shape is what a picture gives for free and a list never gives at all.
;;
;; It renders **live**: server-drawn into the page, no click, no route, no state saying
;; whether it is shown.  That is affordable because the reads are nearly all ones the page
;; already made — the relation flank comes off `term-index-groups`, and the taxonomy is
;; probed only in a direction the closures `term-page` already read say has something in
;; it — and because every expansion is spent from one hard budget.  Being live is also
;; what obliges the budget: a picture nobody asked for may never be the reason a term page
;; is slow.  Over budget means **draw less and say so**, never fall back to a button.
;;
;; The counts below are the ones measured on the shipped schema and on an imported
;; ontology; they are starting points with reasons, not constants with authority.

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
  "How many neighbours the radial view's inner ring holds."
  8)

(def ^:private graph-ego-expand
  "How many of those get their own neighbours read for the outer ring — two bounded reads
  each, and the only reads the radial view makes."
  3)

(def ^:private graph-flank-scan
  "How many of a group's sentexes the ego edges are read out of, **per argument position**.
  The groups are already realized by the page, so this costs no read of its own — what it
  bounds is the work, and the handles the graph adds to the page's one batched belief read.

  Five times the eight neighbours either view can draw, because a window is only needed to
  survive a run of *disbelieved* facts; past that a hub's flank is decided by what is there
  rather than by looking at more of it.  Widening it to 200 draws the identical picture on
  a 148k-sentex corpus and costs a measurable few milliseconds at the widest individual in
  it, which is the whole argument for the number being small."
  40)

(def ^:private subsumption-relations
  "The two relations drawn on the vertical axis.  They are not relation-flank edges: a
  `genl` edge drawn twice, once as a row and once as an arrow, would say two different
  things about one claim.

  The same two the `/tree/rows` handler admits, and it reads this rather than spelling
  them again: a relation the tree can be opened on is one this axis draws, so the pair
  is one fact about the page and not two that can disagree.  (The engine's own name for
  the set is `taxonomy/closure-relations`; this namespace reaches the engine through
  `access` and does not require the taxonomy for it.)"
  '#{genl genlCx})

;; layout, in the flat user space `vaelii.impl.svg` crops to what is drawn
(def ^:private graph-level 76)
(def ^:private graph-row-gap 20)
(def ^:private graph-flank-gap 12)
(def ^:private graph-flank-offset 96)

(defn- graph-node
  "A node of the picture: the term, the **same role class its links use** (so the graph
  can never drift from the text beside it), its page, and the whole term in a tooltip
  since the label is cut."
  ([view term] (graph-node view term nil))
  ([view term extra]
   (let [text (term-text view term)]
     (svg/measure (merge {:term    term
                          ;; the label is the term's *display*, which for a reified term
                          ;; is the expression it denotes and not its opaque constant.
                          ;; `:term` stays the constant: it is the node's identity, what
                          ;; the layout dedups on and what its page is
                          :display text
                          :class   (term-class view term)
                          :href    (str "/term?q=" (url-enc (pr-str term)))
                          :title   text}
                         extra)))))

(defn- graph-step
  "One expansion: the direct neighbours of `node` under `pred` going `:up` or `:down`, at
  most `cap` of them, and how many there are.

  **One facade read in the common case.**  `(take (inc cap))` genuinely bounds it —
  `query` is lazy and the pattern pins an argument, so this costs the node's own fan-out
  and no more.  A node that fits under the cap is realized whole, and is therefore sorted
  (a stable picture) and counted **exactly**; one that does not is left in index order and
  the caption's count is the cheap `count-with-arg` bound, which spans every binary
  predicate holding the term at that position and is therefore an over-count — so
  `:exact?` travels with it and the caption words it as the bound it is.  The second read
  is paid only where something was actually elided."
  [kb pred dir node cap]
  (let [pos  (if (= :up dir) 1 2)
        read (if (= :up dir) parent-terms child-terms)
        got  (into [] (take (inc cap)) (read kb pred node))]
    (if (<= (count got) cap)
      {:terms (by-print-key got) :total (count got) :exact? true}
      {:terms (into [] (take cap) got) :total (v/count-with-arg kb pos node) :exact? false})))

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
  "One side of the taxonomy view: up to `hops` rows of direct neighbours of `centre` under
  `rel`, going `dir`.

  Each row is capped, each node past the first row contributes at most `graph-spread`,
  and every expansion is spent from `budget` — so the number of reads is bounded before
  the first one is made rather than discovered afterwards.  Running out **shortens the
  picture**: `:truncated?` says a row was not read, and the caption says it out loud.

  `:direct` is the centre's own row before the row cap — the one elision worth a precise
  caption, since it is the term the page is about."
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
                         (boolean (some (fn [[_ s]] (> (:total s) (count (:terms s)))) steps)))]
          (if (empty? row)
            {:rows rows :spent spent' :direct direct :deeper? deeper? :truncated? false}
            (recur (mapv :term row) (inc depth) (into seen (map :term) row)
                   (conj rows row) spent'
                   (or direct
                       (when (= 1 depth)
                         (let [s (second (first steps))]
                           {:shown (count row) :total (:total s) :exact? (:exact? s)})))
                   (or deeper? (and (> depth 1) short?)))))))))

(defn- subsumption-plan
  "Which subsumption relation to walk, and in which directions — decided from what
  `term-page` has **already read**, so a term with no taxonomy at all costs the graph
  nothing and an individual pays for no probe that was going to come back empty.

  A term is a context or it is not.  `genl` relates types and predicates, `genlCx`
  relates contexts, `wff` refuses the mixture, and the naming invariants keep the two
  vocabularies apart — so there is exactly one subsumption relation per term page, and the
  class on its edges is what says which.  A reader is never left to read a context edge as
  a type edge, and neither is ever silently absent, because the one that could be there is
  the one that was walked."
  [term gls sps]
  (if (= :context (v/term-role term))
    {:rel 'genlCx :up? true :down? true}
    (when (or (seq gls) (seq sps))
      {:rel 'genl :up? (boolean (seq gls)) :down? (boolean (seq sps))})))

(defn- flank-scan
  "The window of a group's sentexes the ego edges are read out of: its **earliest**
  `graph-flank-scan`, by handle.

  A group comes off a *set* of handles, so a fixed window taken off it as it arrives is a
  sample by hash — an order no reader can name, that moves with the index's representation,
  and that draws a different picture for two assertion orders of the same knowledge.
  Sorting first makes the window the term's earliest mentions, which is one answer per
  knowledge base on every backend, and is what the caption below says the sample is.
  `llm/page`'s `scanned` treats its own scan the same way and for the same reason.

  The records are already in hand — `term-index-groups` fetched them for the rows — so the
  order costs a sort over handles rather than a read."
  [sentexes]
  (take graph-flank-scan (sort-by :id sentexes)))

(defn- flank-handles
  "The handles the ego edges will ask the belief of, so the graph rides the page's **one**
  batched belief read instead of adding a read per node."
  [groups]
  (for [{:keys [pos sentexes]} groups :when pos
        s (flank-scan sentexes)]
    (:id s)))

(defn- flank-edges
  "The centre's binary-relation neighbours, read off the groups the page **already built**
  — a term's argument-position groups are exactly the facts it takes part in, so the ego
  edges cost no extent read of their own.

  What is and is not an edge, stated rather than left to fall out of the code:

    · **binary facts only** — a ternary `(arg parentOf 1 person)` relates three things,
      and an arrow between two of them drops the position it was about;
    · **positive only** — `(not (P a b))` says the relation does *not* hold, and an arrow
      says the opposite;
    · **believed only**, like every other edge here, from the page's belief cache;
    · **symbols only** — a number, `comment`'s text, and a compound in argument position
      are terms of a sentence rather than nodes of a graph;
    · **not the subsumption relations**, which are the vertical axis;
    · **not the term itself** — a self-loop is a shape, not information.

  One edge in two contexts is **one** edge: the graph is not context-scoped and does not
  label an edge with a context.  Drawing it twice would look like a bug, and colouring it
  per context is a different feature with a different budget.  The repeats are left here
  and folded by `merge-neighbours`, which is deduping by term anyway — a stateful filter
  over a *lazy* seq would answer differently the second time anything read it."
  [view term groups]
  (for [{:keys [pos sentexes]} groups
        :when (and pos (<= pos 2))
        s     (flank-scan sentexes)
        :when (and (nil? (:antecedent s)) (= :true (:truth s)) (believed? view (:id s)))
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
  page that reports a scan window as a fact about the KB."
  [groups neighbours]
  (let [binary (filter (fn [{:keys [pos]}] (and pos (<= pos 2))) groups)]
    (if (some (fn [{c :count}] (> c graph-flank-scan)) binary)
      {:total (reduce + 0 (map :count binary)) :exact? false}
      {:total (count neighbours) :exact? true})))

(defn- ego-neighbours
  "One hop out from `t`: its believed binary neighbours, both directions, bounded.

  Two reads, and the shape of the pattern is why two is enough.  `(?p T ?y)` leaves the
  functor open, so the trie can narrow on nothing and would fan over every functor in the
  KB — but `T` is ground in argument position 1, and the predicate-agnostic read spans
  every functor — a union of the scoped roots over `[:argument-slot 1 T]` — so `query`
  answers it with no functor to intersect (docs/indexing.md).  Believed, because that is what `query` means; binary, because the
  pattern has two argument slots and unification is arity-exact; positive, because a
  negative fact is stored as `(not …)` and does not unify with it either.

  **Ordered by handle before the cap cuts**, for `flank-scan`'s reason: a read that
  promises a set promises nothing about which of it comes first, so a window off it as it
  arrives draws one picture for a KB and another for the same knowledge asserted in another
  order.  The order is paid for by realizing the match rather than a prefix of it, which is
  what keeps this a claim about the *term* — the radial view expands `graph-ego-expand`
  neighbours, so it is that many matches, each the neighbour's own extent."
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
                     (sort-by :id (v/sentexes-matching kb pattern '?ctx))))]
    (concat (pull (list '?p t '?y) true)
            (pull (list '?p '?y t) false))))

(defn- rel-edge
  "One relation edge between two placed nodes.  Direction is the arrowhead and the label
  together, never colour: a neighbour the centre points at gets the head at its end, one
  that points back gets it at the centre's, and a pair that does both gets a head at each."
  [centre n {:keys [preds out? in?]}]
  (some-> (if out? (svg/trim centre n) (svg/trim n centre))
          (assoc :label (edge-label preds) :kind "g-rel" :back? (and out? in?))))

(defn- place-flanks
  "The relation flank: things that point **at** the term on the left, things it points at
  on the right, so the two directions are told apart by where they are and not only by an
  arrowhead.  Returns the placed nodes and their edges to the centre together, which is
  what makes every drawn arrow end on a drawn node by construction rather than by a check."
  [view centre neighbours]
  (let [half (/ (:w centre) 2.0)
        ;; a neighbour reached both ways is an outgoing claim as much as an incoming one,
        ;; so it goes on the right and its edge carries the second head
        side (fn [out?]
               (let [es (into [] (comp (filter #(= out? (boolean (:out? %))))
                                       (take graph-flank-cap))
                              neighbours)
                     ns (map #(graph-node view (:term %)) es)
                     x  (if out? (+ half graph-flank-offset) (- (- half) graph-flank-offset))]
                 (map vector (svg/column ns x 0 graph-flank-gap (if out? 1 -1)) es)))
        placed (concat (side false) (side true))]
    {:nodes (map first placed)
     :edges (keep (fn [[n e]] (rel-edge centre n e)) placed)
     :shown (count placed)}))

(defn- taxonomy-scene
  "The top-down view: the term in the middle, its supertypes in rows above and its
  subtypes in rows below, relations flanking.  Vertical position **is** the subsumption
  relation, and every vertical arrow points at the more general term — going up that is
  the neighbour, going down it is the node it was found from, which is why one edge
  builder serves both."
  [{:keys [kb] :as view} term plan neighbours]
  (let [centre (graph-node view term {:x 0 :y 0 :class (str (term-class view term) " g-centre")})
        up     (when (:up? plan)   (grow kb (:rel plan) :up   graph-hops-up   term graph-side-budget))
        down   (when (:down? plan) (grow kb (:rel plan) :down graph-hops-down term graph-side-budget))
        lay    (fn [{:keys [rows]} sign]
                 (mapcat (fn [d row]
                           (svg/row (map #(graph-node view (:term %) (select-keys % [:from :rel]))
                                         row)
                                    0 (* sign graph-level d) graph-row-gap))
                         (rest (range)) rows))
        placed (concat (lay up -1) (lay down 1))
        by-term (into {term centre} (map (juxt :term identity)) placed)
        flank  (place-flanks view centre neighbours)
        rel-kind (str "g-" (:rel plan))
        tax-edges (keep (fn [{:keys [from] :as n}]
                          (let [a (by-term from)
                                ;; the arrow always ends at whichever of the two is higher
                                ;; on the page, which is the more general term either way
                                [lo hi] (if (< (:y n) (:y a)) [a n] [n a])]
                            (some-> (svg/trim lo hi) (assoc :kind rel-kind))))
                        placed)]
    {:nodes (concat [centre] placed (:nodes flank))
     :edges (concat tax-edges (:edges flank))
     :up up :down down
     :flank {:shown (:shown flank)}}))

(defn- ego-scene
  "The radial view, for a term with no subsumption structure at all: the term at the
  origin, its relation neighbours on an inner ring, and each of the first few of *those*
  neighbours' own relations clustered on a short arc outside it.  Edges carry the
  predicate, so two hops of a relation graph read as claims rather than as connectivity."
  [{:keys [kb] :as view} term neighbours]
  (let [centre (graph-node view term {:x 0 :y 0 :class (str (term-class view term) " g-centre")})
        inner  (into [] (take graph-ego-cap) neighbours)
        ring   (svg/ring (map #(graph-node view (:term %)) inner) 0 0 150 (- (/ Math/PI 2)))
        pairs  (mapv vector ring inner)
        out    (reduce (fn [{:keys [nodes edges drawn] :as acc} [n _]]
                         (let [kids   (into [] (comp (remove #(drawn (:term %)))
                                                     (take graph-spread))
                                            (merge-neighbours
                                             (ego-neighbours kb (:term n) graph-ego-cap)))
                               placed (svg/arc (map #(graph-node view (:term %)) kids)
                                               0 0 300 (:angle n))]
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
  count is exact where the row was small enough to be read whole, and the argument-root
  bound otherwise, worded as the bound it is rather than passed off as an edge count."
  [what {:keys [shown total exact?]}]
  (when (and total (> total shown))
    (str "showing " shown " of " (when-not exact? "up to ") (commas total) " " what)))

(def ^:private flank-sample-note
  "What the caption says a partial flank *is*.  A picture drawing eight of forty
  neighbours has sampled, and a sample a reader can name — the term's earliest mentions,
  by handle (`flank-scan`) — is the difference between a bound that can be reasoned about
  and an arbitrary one."
  "the related terms shown are the term's earliest mentions")

(defn- graph-notes
  "The captions under the picture: what was elided, which of it was drawn, and whether the
  read budget rather than the term's own shape is what stopped it."
  [{:keys [up down flank]} plan]
  (let [word (fn [dir] (if (= 'genlCx (:rel plan))
                         (if (= :up dir) "contexts it sees" "contexts that see it")
                         (if (= :up dir) "direct supertypes" "direct subtypes")))
        near (elision-note "related terms" flank)]
    (->> [(some->> (:direct up) (elision-note (word :up)))
          (some->> (:direct down) (elision-note (word :down)))
          near
          (when near flank-sample-note)
          (when (or (:deeper? up) (:deeper? down))
            "deeper rows are sampled, not complete")
          (when (or (:truncated? up) (:truncated? down))
            "and the read budget stopped it a row short")]
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
      [:figure.kb-graph-fig svg
       [:figcaption.muted legend (when notes (list " · " (str/join " · " notes)))]])))

(defn- term-graph
  "The concept graph at the top of a term page: the top-down taxonomy view when the term
  has subsumption structure, the radial ego view when it has relations and no subsumption,
  and **nothing at all** when it has neither.

  Wrapped, and not decoratively: this is the one part of the page that does arithmetic on
  KB-derived numbers, and a term page that fails to render because its picture could not
  be drawn would be a strictly worse page than the one without a picture.  A throw here
  costs the figure and nothing else."
  [view term gls sps groups]
  (try
    (let [near  (merge-neighbours (flank-edges view term groups))
          reach (flank-reach groups near)]
      (if-let [plan (subsumption-plan term gls sps)]
        (let [scene (taxonomy-scene view term plan near)
              scene (update scene :flank merge reach)]
          (graph-figure (term-text view term) scene (graph-notes scene plan)
                        (if (= 'genlCx (:rel plan))
                          "arrows point at the more general context; relations flank it · believed edges only"
                          "arrows point at the more general type; relations flank it · believed edges only")))
        (when (seq near)
          (let [scene (ego-scene view term near)
                note  (elision-note "related terms" (assoc reach :shown (:inner scene)))]
            (graph-figure (term-text view term) scene
                          [note (when note flank-sample-note)]
                          "relations of the term, two hops out; an arrow runs subject to object")))))
    (catch Throwable t
      (trove/log! {:level :warn :id ::graph-failed :data {:term term :error (ex-message t)}})
      nil)))

;; ---- the three type lines, bounded --------------------------------------
;;
;; Supertypes, subtypes, and what the term is separated from.  On the shipped schema each
;; is a handful and the temptation is to render the lot; on an imported ontology `thing`
;; has 110,128 subtypes and one NAT collection is disjoint from 79,638 types, and a page
;; that renders those is 14 MB of links — not slow, unusable, and unclickable once it
;; arrives.  So each line is capped, and each says what it left out.

(defn- type-line
  "One of those three lines, from one of `describe`'s `{:terms :total :exact? :sorted?}`
  answers: the terms it holds, then — only when that window is not the whole answer —
  what was shown out of what there is.  A total that is a *bound* rather than a count
  says so, since the alternative to over-counting is a walk whose whole point was not to
  be taken; a window that is not in name order says that too, since fifty
  alphabetically-first is a different claim from fifty of them.

  **The cap is `describe`'s** (`vaelii.core/default-describe-limit`), not one applied
  again here: the read that decides how much to sort is the read that has to decide how
  much to return, and a second cap on top of it could only ever disagree with `:total`."
  [view label {:keys [terms total exact? sorted?]}]
  (when (seq terms)
    [:div
     [:p label ": " (interpose ", " (map #(term-link view %) terms))]
     (when (> total (count terms))
       (elided (count terms)
               (str (when-not exact? "up to ") (or (commas total) total))
               (when-not sorted? "in index order")))]))

(defn term-page
  "A term's page: the concept graph, the three type lines, the sentexes grouped by the
  index root that reaches them, and the proposal panel.

  **The three type lines are `describe`'s**, not a second computation beside it.  One
  call answers the supertype, subtype and disjointness closures, each already windowed at
  `vaelii.core/default-describe-limit` with `:total` beside it and `:exact?` / `:sorted?`
  saying what kind of window it is — so the page and `vaelii.core/describe` cannot come to
  disagree about what a term is, and against a remote daemon the three lines cost one round
  trip rather than a read apiece (docs/api.md).  Everything else on the page keeps its own
  budget: the index groups are bounded in rows (`group-cap`) and the graph in reads
  (`graph-side-budget`), neither of which is a question about terms."
  [{:keys [kb] :as view} term]
  (let [about  (v/describe kb term '?ctx)
        gls    (:terms (:genls about))
        sps    (:terms (:specs about))
        djs    (:disjoint about)
        text   (term-text view term)
        groups (vec (term-index-groups kb term text))]
    ;; one belief read for the whole page: every group's first page of rows, **and** the
    ;; sentexes the graph reads its ego edges out of, in the same batch
    (prime-belief! view (concat (mapcat #(map :id (take group-cap (group-order (:sentexes %)))) groups)
                                (flank-handles groups)))
    (render view (str "term " text)
            [:h2 "Term " (term-link view term)]
            ;; the picture goes above everything the page says in prose, and the prose
            ;; below is unchanged: the type lines are the accessible equivalent and the
            ;; exact answer this approximates
            (term-graph view term gls sps groups)
            [:p [:a.action {:href (str "/assert?q=" (url-enc (pr-str term)))} "Assert a sentex"]
             [:span.muted " — the form opens with this term already in it."]]
            (when (or (seq gls) (seq sps) (seq (:terms djs)))
              [:div
               (type-line view "Supertypes" (:genls about))
               (type-line view "Subtypes" (:specs about))
               (type-line view "Disjoint with" djs)])
            [:h3 "Sentexes by index "
             [:span.muted "(grouped by the index root that reaches the term, most direct "
              "first — a dimmed badge is not believed, and its pill says why)"]]
            (if (seq groups)
              (map-indexed #(index-group view term [%1 %2]) groups)
              [:p.muted "none"])
            ;; last on the page, and deliberately: what the KB holds is the page, and
            ;; what a model would add is a question to ask after reading it
            (propose-panel view term nil {:remote? (nil? (v/local-kb kb))}))))

(defn term-rows-page
  "One more page of rows for index group `g` of `term` — what a group's continuation
  sentinel fetches.  The groups are recomputed and indexed the same way the page built
  them, so `g` names the same group it did then."
  [{:keys [kb] :as view} term g offset]
  (let [groups (vec (term-index-groups kb term))]
    (frag (if-let [grp (get groups g)]
            (group-rows view term g offset (:count grp) (:sentexes grp))
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
  by `:match :substring` and no regex is compiled at all.  That is the type-ahead path,
  and it is the common one."
  (set "\\^$.|?*+()[]{}"))

(defn- term-hits
  "The terms matching `q`, from the index's **term roster** (`v/find-terms`) — the size
  of the vocabulary, never a walk of the sentexes.  `re-find` semantics either way: a
  literal query is a substring match, and only a query that actually carries regex
  syntax compiles a pattern.  Answers `::bad` for an unusable pattern.

  `limit` bounds the answer, so a page of results costs a page of results."
  [kb q limit]
  (let [regex? (some regex-metacharacters q)]
    (cond
      (and regex? (> (count q) pattern-cap)) ::bad
      :else
      (try
        (v/find-terms kb q {:match (if regex? :regex :substring)
                            :case-sensitive? true :limit limit})
        ;; `Throwable`, as the namespace's other untrusted-input reads: a
        ;; catastrophic pattern can raise `StackOverflowError` out of the regex
        ;; engine, this handler stack has no exception middleware to make a page of
        ;; it, and an unusable pattern is this function's ordinary `::bad` answer
        ;; rather than a 500
        (catch Throwable _ ::bad)))))

(defn- find-list
  "The result list for a search: one page of hits and the sentinel that fetches the
  next.  `hits` is one longer than the page when there is more to come."
  [view q offset hits]
  (let [page (take find-cap hits)]
    (list (for [t page] [:li (term-link view t)])
          (when (> (count hits) find-cap)
            (more-rows (str "/find/rows?q=" (url-enc q) "&offset=" (+ offset find-cap))
                       "show more")))))

(defn find-page
  "Term search over the KB's vocabulary: list every term whose name matches `q`, each
  linking to its term page.  `q` reads as `re-find` does — a bare `dog` finds every term
  containing it, `^parent` anchors — and it filters the index's term roster, so the cost
  is the number of distinct terms rather than the number of sentexes.

  **A pattern that resolves to a single term jumps straight to that term's page** —
  either because it is the only match, or because the query names a term *exactly*
  (so `parentOf` jumps even though it is a substring of `grandparentOf`).  The jump
  renders the term page and sets `HX-Push-Url` so the address bar reflects it.  An
  unusable pattern or an empty query reports gently."
  [{:keys [kb] :as view} q]
  (let [hits (when-not (str/blank? q) (term-hits kb q (inc find-cap)))]
    (cond
      (str/blank? q)
      (render view "find"
              [:h2 "Find terms"]
              [:p.muted "Type a regular expression to match term names — e.g. "
               [:code "^parent"] ", " [:code "Of$"] ", or " [:code "(?i)dog"] "."])
      (= ::bad hits)
      (render view (str "find " (pr-str q))
              [:h2 "Find terms " [:span.muted "matching /" q "/"]]
              [:p.muted "Not a valid regular expression: " [:code q] "."])
      :else
      (let [exact  (first (filter #(= q (str %)) hits))
            target (or exact (when (= 1 (count hits)) (first hits)))]
        (if target
          ;; jump: render the term page, and tell htmx to show the term URL
          (assoc-in (term-page view target) [:headers "HX-Push-Url"] (term-href target))
          (render view (str "find " (pr-str q))
                  [:h2 "Find terms " [:span.muted "matching /" q "/"]]
                  (if (empty? hits)
                    [:p.muted "No terms match " [:code q] "."]
                    [:div
                     [:p.muted (if (> (count hits) find-cap)
                                 (str "More than " find-cap " matching terms")
                                 (str (count hits) " matching terms")) "."]
                     [:ul.find-hits (find-list view q 0 hits)]])))))))

(defn find-rows-page
  "One more page of search hits — what the result list's continuation sentinel fetches."
  [{:keys [kb] :as view} q offset]
  (let [hits (term-hits kb q (+ offset find-cap 1))]
    (frag (if (= ::bad hits) "" (find-list view q offset (drop offset hits))))))

(defn sentex-page [{:keys [kb] :as view} h]
  (if-let [s (v/sentex kb h)]
    (let [premise? (v/premise? kb h)]
      (render view (str "sentex #" h)
              [:h2 "Sentex " (badge view s) [:span.muted "#" h]]
              [:p (render-form view (readable s)) " @ " (term-link view (:context s))
               (state-tag view h)
               (when premise? [:span.tag.tag-premise "premise"])
               ;; a rule is exactly a sentex with a decomposed antecedent — read off the
               ;; record `v/sentex` returned, rather than re-deriving it from the sentence
               (when (:antecedent s) [:span.tag "rule"])
               (when-let [st (:strength s)] [:span.tag (str "assumed " (name st))])
               (when-let [dc (v/defeat-class kb h)] [:span.tag (str "class " (name dc))])]
              ;; when the sentex is stored but not believed, say why — the states
              ;; docs/equality.md and docs/nmtms.md describe: superseded / defeated /
              ;; unsupported.  A believed sentex's proof is the "Supported by" list below.
              (when-not (believed? view h) (belief-detail view h))
              [:h3 "Supported by " [:span.muted "(justifications concluding it)"]]
              (if premise?
                [:p.muted "asserted as a premise"]
                (justification-list view (v/supporting-justifications kb h)))
              ;; one hop up there; the whole way down to the premises is the why page
              [:p [:a.action {:href (str "/why/" h)} "Why is this believed?"]
               [:span.muted " — the full proof tree, not just the first hop."]]
              [:h3 "Dependents " [:span.muted "(justifications using it as an argument)"]]
              (justification-list view (v/dependent-justifications kb h))
              [:h3 "Subterms " [:span.muted "(each findable individually)"]]
              [:p (interpose " · " (map #(term-link view %) (by-print-key (v/indexable-terms s))))]
              [:p [:a {:href (str "/levels?q=" (url-enc (pr-str (readable s)))
                                  "&ctx=" (url-enc (pr-str (:context s))))}
                   "Trace through the stack"]
               [:span.muted " — which level of machinery reaches this sentence."]]))
    (render view "not found" [:p "No sentex #" h])))

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
  [{:keys [kb] :as view} goal ctx lvl offset]
  (let [rs   (into [] (comp (drop offset) (take (inc result-cap)))
                   (v/lookup kb lvl goal ctx))
        page (take result-cap rs)]
    (prime-belief! view (keep :handle page))
    (list page (when (> (count rs) result-cap)
                 (str "/levels/rows?q=" (url-enc (pr-str goal)) "&ctx=" (url-enc (pr-str ctx))
                      "&level=" lvl "&offset=" (+ offset result-cap))))))

(defn- bindings-str [view b]
  (interpose ", " (for [[k val] (by-print-key b)]
                    [:span (render-form view k) " = " (render-form view val)])))

(defn- result-item
  "One result.  A level that reads the store gives a handle, so the answer links to
  its sentex; levels 5-7 derive, so the sentence is rendered inline and tagged."
  [view r]
  [:li
   (if-let [h (:handle r)]
     ;; a storage level (0-1) can return a sentex the KB does not believe — the badge
     ;; already dims, the reason pill says why (superseded / defeated).  Cache hit:
     ;; level-rows primed these handles.
     (list (handle-ref view h)
           (when-not (believed? view h) (list " " (state-tag view h))))
     [:span (render-form view (:sentence r)) [:span.tag "derived"]])
   (when-let [c (:context r)] [:span " @ " (term-link view c)])
   (when (seq (:bindings r)) [:span.muted " — " (bindings-str view (:bindings r))])])

(defn- result-list
  "A level's rows and, when the level has more, the continuation sentinel."
  [view [page more-href]]
  (list (map #(result-item view %) page)
        (when more-href (more-rows more-href "show more"))))

(defn- level-section [view goal ctx {lvl :level nm :name adds :adds}]
  (let [[page :as rows] (level-rows view goal ctx lvl 0)]
    [:div
     [:h3 lvl " " [:span.tag (name nm)] " " [:span.muted adds]]
     (if (seq page)
       [:ul (result-list view rows)]
       [:p.muted "nothing"])]))

(defn levels-rows-page
  "One more page of results for a single level — what a level's continuation sentinel
  fetches."
  [view goal ctx lvl offset]
  (frag (result-list view (level-rows view goal ctx lvl offset))))

;; ---- the query plan ------------------------------------------------------
;;
;; The levels below say what each mechanism *answers*; this says what the engine would
;; *do* — which provers bear on the goal, what each expects to cost, which one actually
;; runs and why, and for a conjunction the order the join was put in and the counts that
;; decided it.  It takes the same two inputs the levels take, so it sits on the same
;; page rather than behind a second form asking for the same thing.

(defn- prover-plan
  "The provers applicable to a single goal.  Applicable is not the same as consulted:
  when one prover is *complete* for the goal the engine runs it alone and every other
  entry is shadowed, so the table says which ran as well as what each would cost."
  [rows]
  (list
   [:p.muted "One prover runs alone when it is complete for the goal; otherwise the "
    "applicable ones union, cheapest cost tier first. Cost is a tier — is the answer "
    "something you look up, compute, or search for — not a predicted duration."]
   [:div.qcn-scroll
    [:table.stats-table
     [:thead [:tr [:th "Prover"] [:th.num "est. bindings"] [:th "cost"]
              [:th.num "completeness"] [:th "runs?"]]]
     [:tbody
      (for [{:keys [prover est-bindings cost completeness runs? shadowed-by]} rows]
        [:tr
         [:td (if runs? [:b prover] [:span.muted prover])]
         [:td.num est-bindings]
         [:td [:span.tag (name (or cost :unknown))]]
         [:td.num completeness (when (= 100 completeness)
                                 [:span.muted " — the sole complete method"])]
         [:td (if runs?
                [:span.tag.tag-in "runs"]
                [:span.muted "shadowed by " shadowed-by])]])]]]))

(defn- join-plan
  "The order a conjunction's literals will actually run in, with the three numbers the
  order was decided on.  `est. matches` is the sound upper bound on one literal's
  fan-out under the bindings the rows above produce — sideways information passing, and
  why the column does not read as sorted.  `rows` is the literal's own expected size,
  and `plan rows` the expected size of everything up to and including it, which is the
  number a join was actually costed in and the one to read a surprising order against."
  [view rows]
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
         [:td (render-form view goal)]
         [:td.num est-matches]
         [:td.num est-rows]
         [:td.num est-prefix]
         [:td.num (if block (inc (long block)) [:span.muted "—"])]
         [:td (if (seq bound-before)
                (interpose ", " (for [b (by-print-key bound-before)] (render-form view b)))
                [:span.muted "—"])]
         [:td (cond
                deferred?  [:span.tag {:title "consumes bindings rather than producing them"}
                            "pinned: evaluable"]
                recursive? [:span.tag {:title "reordering could turn right-recursion into left"}
                            "pinned: recursive"]
                isolated?  [:span.tag {:title "shares no variable with the rest and matches more than once, so it multiplies whatever follows it"}
                            "deferred: cartesian"]
                :else      [:span.muted "costed"])]])]]]
   [:p.legend "A " [:b "pinned"] " literal keeps the order it was written in, because "
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
    "A block number that jumps back and forth down the table is the pins threading "
    "evaluables in where they became ready."]))

(defn- plan-section
  "How the engine would answer this goal — the join plan for a conjunction, the prover
  table for a single sentence."
  [{:keys [kb] :as view} goal ctx]
  (let [rows (v/query-plan kb goal ctx)]
    [:div
     [:h3 "How it would be answered"]
     (cond
       (empty? rows) [:p.muted "No prover bears on this goal."]
       (vector? goal) (join-plan view rows)
       :else          (prover-plan rows))]))

(defn levels-page
  "The lookup-to-query stack over a goal: what each of the eight levels answers, so
  the level at which results first appear is the mechanism the answer depends on.
  With no goal, the stack itself.

  A **vector** goal is the conjunctive query `prove` takes, and the levels do not take
  one — they answer about a literal.  So a conjunction gets the join plan and stops
  there, rather than being rendered through eight sections that cannot address it."
  [{:keys [kb] :as view} goal ctx]
  (let [table (v/levels)]
    (render view (if goal (str "levels " (pr-str goal)) "levels")
            [:h2 "Lookup-to-query stack"]
            [:p.muted "Eight levels of escalating machinery over one goal. Each adds exactly "
             "one mechanism to the one below, so a result that appears at level n and not "
             "at n-1 is attributable to that mechanism."]
            [:form.q {:method "get" :action "/levels"}
             [:input {:type "text" :name "q" :size 44 :placeholder "(animal ?x)"
                      :value (when goal (pr-str goal))}]
             [:input {:type "text" :name "ctx" :size 18 :placeholder "?ctx"
                      :value (when (and ctx (not= '?ctx ctx)) (pr-str ctx))}]
             [:button {:type "submit"} "run"]]
            (cond
              (not (sequential? goal))
              [:div
               (when goal [:p.muted "A goal is a sentence, e.g. " [:code "(animal ?x)"]
                           " — or a vector of them, e.g. "
                           [:code "[(bird ?x) (hasCapability ?x flying)]"] ", which is a conjunctive "
                           "query and gets a join plan."])
               [:h3 "The levels"]
               [:ul (for [{lvl :level nm :name adds :adds} table]
                      [:li lvl " " [:span.tag (name nm)] " — " adds])]]

              ;; a conjunction is `prove`'s goal shape, not a literal — the levels
              ;; answer about one literal, so there is nothing for them to say here
              ;; a vector whose members are not sentences is not a conjunction — it is
              ;; the sentence spelling `query-plan` refuses, and asking for its plan
              ;; would throw where the page has no exception middleware to render it.
              ;; Refused here in the same voice as the guidance above, since a plan for
              ;; a goal `prove` will not answer is a fiction either way.
              (and (vector? goal) (not-every? seq? goal))
              [:div
               [:h2 "Not a goal @ " (term-link view ctx)]
               [:p.muted "A vector goal is a conjunction, so each member has to be a "
                "sentence — e.g. " [:code "[(bird ?x) (hasCapability ?x flying)]"] ". "
                "One sentence is written as a list: " [:code "(animal ?x)"] ", not "
                [:code "[animal ?x]"] "."]]

              (vector? goal)
              [:div
               [:h2 "Conjunctive goal @ " (term-link view ctx)]
               [:ul (for [g goal] [:li (render-form view g)])]
               (plan-section view goal ctx)
               [:p [:a {:href (str "/inference?q=" (url-enc (pr-str goal))
                                   (when (not= '?ctx ctx) (str "&ctx=" (url-enc (pr-str ctx)))))}
                    "Step through the search for this goal →"]]
               [:p.legend "The eight levels answer about a single literal, so they are "
                "not shown for a conjunction. Ask one conjunct on its own to see them."]]

              :else
              (let [esc (v/escalate kb goal ctx)]
                [:div
                 [:h2 "Goal " (render-form view goal) " @ " (term-link view ctx)]
                 (if-let [lvl (:level esc)]
                   [:p "Answered at level " [:b lvl] " " [:span.tag (name (:name esc))] " "
                    [:span.muted (:adds (nth table lvl))]]
                   [:p.muted "No level answers this goal."])
                 [:p.legend "Escalation starts at level 2 — levels 0 and 1 answer about "
                  "storage rather than truth, so either can claim a goal it cannot verify."]
                 [:p [:a {:href (str "/inference?q=" (url-enc (pr-str goal))
                                     (when (not= '?ctx ctx) (str "&ctx=" (url-enc (pr-str ctx)))))}
                      "Step through the search for this goal →"]]
                 (plan-section view goal ctx)
                 (map #(level-section view goal ctx %) table)])))))

;; ---- the inference debugger ----------------------------------------------
;;
;; `/levels` shows the *plan*; this shows the *run* that plan predicted — the search tree
;; the node engine actually built for a goal (every node the frontier reached, not only
;; the path that answered), and the same goal under several tacticians side by side.  Both
;; read through `search-tree` / `compare-tacticians`, which bound their own work (a node
;; budget and a wall-clock), so the page holds no session between requests and works under
;; `--attach` exactly like every other read here.

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
  [view literals]
  [:div.qcn-scroll
   [:table.stats-table
    [:thead [:tr [:th "literal (join order)"] [:th.num "est. matches"] [:th.num "block"] [:th "pin"]]]
    [:tbody
     (for [{:keys [sentence cost block isolated? deferred? recursive?]} literals]
       [:tr
        [:td (render-form view sentence)]
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
  [view {:keys [id tree-depth rewrite results estimate]}]
  (let [n (count results)]
    [:summary {:id (str "node-" id)}
     [:span.node-tag "#" id]
     [:span.muted "depth " tree-depth " · "]
     (if rewrite
       (list (render-form view (:goal rewrite))
             [:span.muted " via "]
             (if-let [rh (:rule rewrite)]
               ;; dim the link when the rule is OUT — a search that expanded an
               ;; unbelieved rule reads as such (belief is primed for these handles)
               [:a (cond-> {:href (str "/sentex/" rh)}
                     (not (believed? view rh))
                     (assoc :class "muted" :title "this rule is not currently believed"))
                "rule #" rh]
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
  [view children-of {:keys [id tree-depth estimate rewrite results guards] :as node}]
  [:details.node (cond-> {:id (str "detail-" id)} (< (long tree-depth) 1) (assoc :open true))
   (node-summary view node)
   [:div.node-body
    ;; goal → answers → children read first; the cost decomposition and per-literal
    ;; estimates are internal tuning, one click away rather than in the default path
    [:details.cost-breakdown
     [:summary [:span.muted "cost breakdown"]]
     (estimate-line estimate)
     (node-literals view (:literals estimate))]
    (when rewrite
      [:p.muted "Rewrote " (render-form view (:goal rewrite)) " through "
       (if-let [rh (:rule rewrite)] (handle-ref view rh) [:span "a rule"])])
    (when (pos? (long guards))
      [:p.muted guards " guard" (when (> (long guards) 1) "s") " carried here (an "
       [:code "exceptWhen"] ", asked when the conjunction completes)."])
    (when (seq results)
      [:div
       [:p.muted "Answers off this node:"]
       [:ul (for [b results]
              [:li (if (seq b) (bindings-str view b) [:span.muted "(ground — the conjunction holds)"])])]])
    (for [k (get children-of id)] (render-node view children-of k))]])

(defn- status-tag
  [status]
  (let [cls (case status :complete "tag-in" :bounded "tag" :timeout "tag-defeated" "tag")]
    [:span {:class (str "tag " cls)} (name status)]))

(defn- tactician-table
  "The same goal under several tacticians, tabled by the work each did and the answers each
  found, with the identity property **verified** below rather than asserted: every
  tactician is complete, so the answer sets must match, and a row that differs is a bug the
  completeness sweep exists to catch."
  [_view rows]
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
  [view {:keys [answers]}]
  (let [n (count answers)]
    [:div
     [:h3 (commas n) " answer" (when (not= 1 n) "s")]
     (if (seq answers)
       (list
        [:ul (for [a (take 50 answers)]
               [:li (if (seq (:bindings a))
                      (bindings-str view (:bindings a))
                      [:span.muted "(ground — the goal holds)"])
                [:span.muted " · from "] [:a {:href (str "#node-" (:node a))} "node #" (:node a)]])]
        (when (> n 50) [:p.muted "… " (commas (- n 50)) " more."]))
       [:p.muted "No answer within the depth bound. A derivation deeper than the bound is "
        "not found — the depth a query needs is a property of the data, so raise it and re-run."])]))

(defn- search-tree-summary
  "One line of what the run cost, and — this is the honest part — whether the tree shown is
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
  [{:keys [kb] :as view} goal ctx depth]
  (render view (if goal (str "search " (pr-str goal)) "search")
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
             [:h2 "Not a goal @ " (term-link view ctx)]
             [:p.muted "A vector goal is a conjunction, so each member has to be a sentence — "
              "e.g. " [:code "[(edgeOf ?x ?y) (anc ?y ?z)]"] ". One sentence is a list: "
              [:code "(anc ?x ?z)"] ", not " [:code "[anc ?x ?z]"] "."]]

            (not (or (seq? goal) (vector? goal)))
            [:div
             [:h2 "Not a goal @ " (term-link view ctx)]
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
                (prime-belief! view (keep #(get-in % [:rewrite :rule]) capped))
                [:div
                 [:p [:a {:href (str "/levels?q=" (url-enc (pr-str goal)) ctx-q)}
                      "See the plan and the eight levels for this goal →"]]

                 [:h3 "Tacticians, side by side"]
                 [:p.muted "Each ordering run to completion over the same goal, timed on its "
                  "own. A latency measurement over a fixed answer set — the fast column is fast "
                  "because it reached the answers sooner, not because it found fewer."]
                 (tactician-table view rows)

                 (search-answers view tree)

                 [:h3 "The search tree"]
                 (search-tree-summary tree)
                 [:p.legend "Nodes are written in the search's own "
                  [:span.t-var "?var0"] "/" [:span.t-var "?var1"] " names; two questions "
                  "equal up to variable names are one node."]
                 [:div.search-tree (when root (render-node view children-of root))]
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
  either way; this bounds only the render, and the pinned pairs are listed instead."
  16)

(defn- relation-cell
  "One constraint: the base relations still possible between two nodes.  A singleton is
  a pinned arrangement and reads as the one name; the whole universe is ignorance and
  reads as a dot, because a matrix saying `unknown` in every cell is noise."
  [rels base]
  (let [n (count rels)]
    (cond
      (nil? rels)      [:span.muted {:title "unknown"} "·"]
      (zero? n)        [:span.tag.tag-defeated {:title "no relation possible"} "∅"]
      (= n (count base)) [:span.muted {:title "unknown"} "·"]
      (= n 1)          [:b {:title "pinned"} (name (first rels))]
      :else            [:span.muted {:title (str n " still possible")}
                        (str/join " " (map name (sort rels)))])))

(defn- network-matrix
  "The tightened network as a table — row *r*, column *c* is what still holds of
  `(r c)`.  Not symmetric: the cell below the diagonal is the converse of the one
  above, which is what makes a directional relation legible."
  [view {:keys [nodes constraints]} base]
  [:div.qcn-scroll
   [:table.stats-table.qcn-matrix
    [:thead [:tr [:th] (for [c nodes] [:th (term-link view c)])]]
    [:tbody
     (for [r nodes]
       [:tr [:th (term-link view r)]
        (for [c nodes]
          [:td (if (= r c)
                 [:span.muted {:title "the diagonal is the identity"} "—"]
                 (relation-cell (get constraints [r c]) base))])])]]])

(defn- pinned-list
  "The pairs path consistency pinned to a single relation — the matrix's content when
  the matrix itself would be too wide to read."
  [view {:keys [constraints]}]
  (let [pinned (sort-by (comp print-key key)
                        (filter (fn [[_ rels]] (= 1 (count rels))) constraints))]
    (if (seq pinned)
      [:ul (for [[[a b] rels] pinned]
             [:li (term-link view a) " " [:b (name (first rels))] " " (term-link view b)])]
      [:p.muted "No pair is pinned to a single relation."])))

(defn network-page
  "The constraint network a calculus computes over one context: which terms it relates,
  what still holds of every pair, whether the believed facts are satisfiable at all, and
  one concrete arrangement consistent with them.

  Every calculus is offered whether or not its prover is registered — a network is a
  property of the stored facts, and `add-prover` only decides whether `ask` consults it."
  [{:keys [kb] :as view} ctx calc]
  (let [table    (v/calculi)
        sized    (when ctx
                   (for [{nm :calculus :as c} table]
                     (assoc c :net (v/qualitative-network kb nm ctx))))
        by-name  (into {} (map (juxt :calculus identity)) (or sized []))
        chosen   (or (get by-name calc)
                     (->> sized (filter #(seq (:nodes (:net %)))) first))
        net      (:net chosen)
        base     (:base chosen)]
    (render view (if ctx (str "network " (pr-str ctx)) "network")
            [:h2 "Qualitative constraint network"]
            [:p.muted "A relation algebra reads every fact of its own vocabulary in a "
             "context into one network and tightens it by composition, so a relation "
             "nobody stated is entailed by the ones that were."]
            [:form.q {:method "get" :action "/network"}
             [:input {:type "text" :name "ctx" :size 24 :placeholder "CxWell"
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
               [:table.stats-table
                [:thead [:tr [:th "calculus"] [:th.num "base"] [:th.num "predicates"]
                         [:th "vocabulary"]]]
                [:tbody
                 (for [{nm :calculus b :base preds :predicates} table]
                   [:tr [:th (name nm)]
                    [:td.num (count b)] [:td.num (count preds)]
                    [:td.muted (str/join ", " (map str (take 6 preds)))
                     (when (> (count preds) 6) " …")]])]]]
              [:div
               [:h3 "Contexts and calculi"]
               [:p.legend "How many terms each calculus relates in " (term-link view ctx)
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
                 [:p.muted "This calculus relates nothing in " (term-link view ctx) "."]

                 :else
                 [:div
                  [:h3 (name (:calculus chosen)) " in " (term-link view ctx)]
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
                                          [:span (term-link view a) "/" (term-link view b)]))]
                       [:p.legend "No single pair is to blame — composition is what "
                        "emptied a constraint, so the clash is a property of the set."])])
                  (if (<= (count (:nodes net)) matrix-node-limit)
                    (network-matrix view net base)
                    [:div [:p.legend "Too many nodes to draw the matrix; the pinned "
                           "pairs are:"]
                     (pinned-list view net)])
                  [:p.legend "A cell is what still holds of (row, column): "
                   [:b "one name"] " is pinned, several are still open, "
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
                            [:li (term-link view a) " " [:b (name rel)] " "
                             (term-link view b)])]
                         [:p.muted "Nothing to arrange."])]))])]))))

(defn justification-page [{:keys [kb] :as view} jid]
  (if-let [d (v/justification kb jid)]
    (let [antes    (:antecedents d)
          conc     (:consequence d)
          ;; one batched read; sentex-list below re-uses the same primed cache
          _        (prime-belief! view (conj (vec antes) conc))
          out      (into [] (remove #(believed? view %)) antes)
          ;; the JTMS ruled this justification blocked — its rule's `exceptWhen` holds —
          ;; so it supports nothing even when every argument is IN; a separate condition
          ;; from an argument being OUT, and stated separately below
          excepted? (contains? (blocked-justifications view) jid)
          valid?   (and (empty? out) (not excepted?))
          conc-in? (believed? view conc)]
      (render view (str "justification #" jid)
              [:h2 "Justification " [:span.muted "#" jid]]
              [:p "Rule / informant: "
               (if (number? (:informant d))
                 (handle-ref view (:informant d))
                 [:code (pr-str (:informant d))])
               " · strength " [:code (name (:strength d :monotonic))]]
              ;; is this justification currently carrying its conclusion?  It supports iff
              ;; every argument is IN *and* the JTMS has not blocked it.  The conclusion being
              ;; IN is a separate question — a second justification may carry it — so both are
              ;; stated.  Handles are linked (not re-fetched with handle-ref) to avoid
              ;; re-reading what the lists below read.
              [:div.belief
               (cond
                 valid?
                 [:p [:span.tag.tag-in "valid"] " — every argument is believed, so this "
                  "justification currently supports its conclusion "
                  [:a.ref {:href (str "/sentex/" conc)} "#" conc] " "
                  (if conc-in? [:span.tag.tag-in "IN"]
                      (list (state-tag view conc)
                            [:span.muted " (carried, if at all, by another justification)"])) "."]

                 ;; blocked by its rule's exception: every argument is IN, yet the JTMS
                 ;; confers nothing.  Said apart from the OUT-argument case, whose "N of M
                 ;; arguments are OUT" would read "0 of M" here and mislead.
                 excepted?
                 [:p [:span.tag.tag-out "not supporting"] " — this rule's exception holds, so "
                  "the truth-maintenance network blocks this justification: it confers "
                  "nothing even though every argument is believed. Its conclusion "
                  [:a.ref {:href (str "/sentex/" conc)} "#" conc] " is "
                  (if conc-in? [:span.tag.tag-in "IN"] (state-tag view conc))
                  (when conc-in? [:span.muted " (carried by another justification)"]) "."]

                 :else
                 (list
                  [:p [:span.tag.tag-out "not supporting"] " — " (count out) " of "
                   (count antes) " arguments are OUT, so this justification confers nothing "
                   "right now. Its conclusion "
                   [:a.ref {:href (str "/sentex/" conc)} "#" conc] " is "
                   (if conc-in? [:span.tag.tag-in "IN"] (state-tag view conc)) "."]
                  [:ul (for [h out]
                         [:li [:a.ref {:href (str "/sentex/" h)} "#" h] " " (state-tag view h)])]))]
              [:h3 "Supports " [:span.muted "(arguments)"]]
              (sentex-list view (keep #(v/sentex kb %) antes))
              [:h3 "Dependent sentex " [:span.muted "(conclusion)"]]
              (sentex-list view (keep #(v/sentex kb %) [conc]))))
    (render view "not found" [:p "No justification #" jid])))

;; ---- why: the proof tree ------------------------------------------------
;;
;; The sentex page shows one hop — the justifications that conclude a handle.
;; `vaelii.core/why` walks the whole way down to premises, cycle-guarded, with rule
;; sentences read back in the author's variable names, and that whole tree is what
;; "why does the KB believe this?" actually asks.  Rendering it is a fold over the
;; recursive map: one `<details>` per derived node, its justifications as branches and
;; their arguments as the next level, terminating at a premise, a cycle back-edge, or a
;; node that is not believed (which `why-not` — the sentex page — answers instead).

(def ^:private why-open-depth
  "How deep the tree opens by default.  A proof's shape is the point, so the first
  levels are open; deeper branches are one click away rather than a wall of text."
  3)

(defn- why-head
  "One node's line: its handle, its sentence, and the context it holds in."
  [view {:keys [handle sentence context]}]
  (list [:a.ref {:href (str "/sentex/" handle)} "#" handle] " "
        (render-form view sentence)
        (when context (list " @ " (term-link view context)))))

(defn- why-node
  "One node of the proof tree.  A derived node is a `<details>` whose branches are its
  justifications; every other node is a leaf, and says which kind:

    premise       asserted, with the assumption strength it was asserted at
    cycle         already on this branch — the graph may cycle, and `why` reports the
                  back-edge rather than expanding it again
    not believed  stored but OUT; `why-not` (the sentex page) is where the reason is
    not stored    the handle names nothing"
  [view depth {:keys [handle stored? truncated? cycle? believed? premise? strength defeat-class support]
               :as node}]
  (let [head (why-head view node)]
    (cond
      (false? stored?)   [:li head " " [:span.tag.tag-not-stored "not stored"]]
      truncated?         [:li head " " [:span.tag.tag-out "depth bound"]
                          [:span.muted " — proof continues below the depth shown"]]
      cycle?             [:li head " " [:span.tag.tag-out "cycle"]
                          [:span.muted " — already on this branch"]]
      (false? believed?) [:li head " " [:span.tag.tag-out "not believed"] " "
                          [:a {:href (str "/sentex/" handle)} "why not"]]
      premise?           [:li head " " [:span.tag.tag-premise "premise"]
                          (when strength [:span.tag (str "assumed " (name strength))])]
      :else
      [:li [:details (cond-> {} (< depth why-open-depth) (assoc :open "open"))
            [:summary head " "
             ;; every <details> node is believed (why expands only believed nodes),
             ;; so IN is a constant — no KB read
             [:span.tag.tag-in "IN"] " "
             (when defeat-class [:span.tag (str "class " (name defeat-class))])
             [:span.muted " · " (count support)
              (if (= 1 (count support)) " justification" " justifications")]]
            [:ul.why
             (let [blocked (blocked-justifications view)]
               (for [{:keys [justification informant rule strength because]} support
                     ;; a justification is currently supporting iff every argument is IN
                     ;; *and* the JTMS has not blocked it (its rule's `exceptWhen` holds —
                     ;; invalid, so it supports nothing even with every argument IN).  The
                     ;; first is read straight off the child nodes; the second off the
                     ;; network's blocked set, which belief alone cannot see.
                     :let [args-out? (some #(or (false? (:believed? %))
                                                (false? (:stored? %))) because)
                           excepted? (contains? blocked justification)]]
                 [:li (justification-link justification) " "
                  (if rule
                    [:span "via " (render-form view rule)]
                    [:span.muted "via " (pr-str informant)])
                  " " [:span.tag (name (or strength :monotonic))] " "
                  (if (or args-out? excepted?)
                    [:span.tag.tag-out
                     {:title (if excepted?
                               "this rule's exception holds, so the JTMS blocks this justification — it supports nothing even though its arguments are IN"
                               "an argument is OUT, so this justification is not currently supporting")}
                     "blocked"]
                    [:span.tag.tag-in {:title "every argument is IN and no exception blocks it, so this justification currently supports the conclusion"} "supporting"])
                  (when (seq because)
                    [:ul.why (map #(why-node view (inc depth) %) because)])]))]]])))

(defn why-page
  "The whole proof tree for a handle — `vaelii.core/why` rendered, collapsible.  Linked
  from the sentex page, which shows only the first hop."
  [{:keys [kb] :as view} h]
  (if-let [s (v/sentex kb h)]
    (let [tree (v/why kb h)]
      (render view (str "why #" h)
              [:h2 "Why " (badge view s) [:span.muted "#" h]]
              [:p (render-form view (readable s)) " @ " (term-link view (:context s))]
              (if (:believed? tree)
                (let [sup     (:support tree)
                      blocked (blocked-justifications view)
                      ;; a top-level justification supports iff every argument is IN *and*
                      ;; the JTMS has not blocked it — the same two conditions the tree's
                      ;; pills show, so the count and the pills agree
                      ok  (count (remove (fn [j] (or (some #(or (false? (:believed? %))
                                                                (false? (:stored? %)))
                                                           (:because j))
                                                     (contains? blocked (:justification j))))
                                         sup))]
                  (list
                   [:p.muted "The proof, down to the premises it rests on. Each branch is a "
                    "justification; the rule that licensed it is named beside it."]
                   (when (> (count sup) 1)
                     [:p.legend ok " of " (count sup) " justifications currently support this; "
                      "the rest are shown " [:span.tag.tag-out "blocked"] "."])))
                [:p.muted "This sentex is not believed, so there is no proof to show — "
                 [:a {:href (str "/sentex/" h)} "the sentex page"] " reports why not."])
              [:ul.why (why-node view 0 tree)]))
    (render view "not found" [:p "No sentex #" h])))

;; ---- the non-monotonicity demo ------------------------------------------
;;
;; The one thing here that no database does, in three clicks.  `(hasCapability Pingu flying)` is
;; believed; the KB then learns `(penguin Pingu)` and stops believing it — nobody
;; deleted anything and nobody overrode anything, the flight rule's own exception simply
;; stopped licensing the conclusion — and retracting the penguin claim brings it back.
;; Every step is an ordinary `edit` against the reader's own sandbox, and every handle on
;; the page links to the record it names: the claim being made is precisely that this is
;; the engine and not a story about one, so it has to be checkable line by line.
;;
;; The conclusion that comes back is a **different sentex**.  `exceptWhen` blocks rather
;; than rebuts, so a blocked justification is invalid, groundability goes with it, and the
;; dependency-directed sweep deletes the conclusion along with everything resting on it
;; (docs/exceptions.md).  Revival is therefore a re-derivation: the same proof by the same
;; rule, at a handle that never existed before, while step 1's handle now resolves to
;; nothing.  The page says so rather than re-showing the old id — the engine did not hide
;; the conclusion and put it back, it forgot it and re-earned it, and the record changing
;; while the proof does not is the sharpest evidence on the page.

(def ^:private demo-subject
  "Who the walkthrough is about.  One individual, in the reader's own sandbox, so two
  readers of one process never collide and the sandbox reset takes every trace away."
  'Pingu)

(defn- demo-claim
  "`(<pred> Pingu)` — a sentence the demo makes, or asks about."
  [pred] (list pred demo-subject))

(defn- demo-cap
  "`(hasCapability Pingu <capability>)` — what the walkthrough's conclusion is about.
  Flight is a capability rather than a one-place property, so the conclusion under test is
  a binary sentence and the demo builds it apart from `demo-claim`."
  [capability] (list 'hasCapability demo-subject capability))

(def ^:private demo-script
  "The three steps.  `:from` is the state the KB has to be in for a step to be the next
  one, so which button the page offers is a fact about the KB rather than a counter the
  page keeps."
  [{:n 1 :from :before   :op "start"
    :button "Assert (bird Pingu)"
    :does   "Tell the KB that Pingu is a bird. Say nothing whatever about flying."
    :then   "(hasCapability Pingu flying) becomes believed"}
   {:n 2 :from :believed :op "except"
    :button "Assert (penguin Pingu)"
    :does   "Tell it Pingu is a penguin. Retract nothing, delete nothing, override nothing."
    :then   "(hasCapability Pingu flying) stops being believed"}
   {:n 3 :from :blocked  :op "restore"
    :button "Retract (penguin Pingu)"
    :does   "Take the penguin claim back."
    :then   "(hasCapability Pingu flying) is believed again — as a new record"}])

(def ^:private demo-watched
  "The five sentences the walkthrough touches, in the order they make sense in: the two
  the reader asserts, the conclusion under test, the thing resting on it, and the
  positive claim a penguin carries.  All five are rendered at every step, because the
  cascade is the part worth seeing — the conclusion does not go alone, and the KB does
  not merely fail to conclude flight, it concludes flightlessness, which is a different
  statement."
  [{:form (demo-claim 'bird)
    :note "asserted — step 1"}
   {:form (demo-claim 'penguin)
    :note "asserted — step 2, taken back in step 3"}
   {:form (demo-cap 'flying)
    :note "derived — the conclusion under test"}
   {:form (demo-cap 'travelling)
    :note "derived from the flight — it goes when that goes"}
   {:form (list 'not (demo-cap 'flying))
    :note "derived from (penguin Pingu) — a positive claim, not the absence of one"}])

(defn- demo-state
  "Where the walkthrough stands, read off the KB rather than remembered.  `first-h` is
  the handle the flight conclusion carried the first time round, threaded through the step
  forms: it is the one thing the KB cannot answer, because by the time it matters the
  record it names has been swept."
  [{:keys [kb sandbox] :as view} first-h]
  (let [live?   (boolean (and sandbox @(:sandbox-live? view)))
        at      #(when live? (v/handle-of kb % sandbox))
        bird    (at (demo-claim 'bird))
        penguin (at (demo-claim 'penguin))
        flight  (at (demo-cap 'flying))
        stage   (cond (nil? bird)                        :before
                      penguin                            :blocked
                      (and first-h (not= first-h flight)) :returned
                      :else                              :believed)]
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
  Blocked: `why-not`'s sentence arity — the arity that exists precisely because a blocked
  conclusion has no handle left to ask about."
  [{:keys [kb sandbox] :as view} {:keys [stage flight first]}]
  (case stage
    :before
    [:div.belief
     [:p [:b "Not stored, not believed."] " Your sandbox holds nothing about Pingu yet."]]

    :blocked
    (let [{:keys [reason rule exception via]} (v/why-not kb (demo-cap 'flying) sandbox)]
      [:div.belief
       [:p [:b "Not believed"] " — and nobody said so. "
        (if (= :excepted reason)
          (list "The flight rule " (handle-ref view rule) " states its own exception, "
                [:span.sx (pr-str exception)] ", and that now holds of Pingu"
                (when (seq via)
                  (list " — from " (interpose ", " (map #(handle-ref view %) via))))
                ", so it does not conclude.")
          (list "why-not reports " [:code (str reason)] "."))]
       [:p "There is no handle to ask about, either. A blocked justification is "
        [:i "invalid"] ", not merely outvoted, so the dependency-directed sweep deleted "
        "the conclusion outright"
        (when first
          (list " — " [:a {:href (str "/sentex/" first)} (str "#" first)]
                " was it, and that page now reports nothing"))
        ", and took what rested on it along."]])

    ;; :believed / :returned
    (let [tree (v/why kb flight)]
      [:div.belief
       [:p [:b "Believed"] " — and nobody asserted it. " (handle-ref view flight)
        " is a conclusion; the rule that reached it is one line down."]
       [:ul.why (why-node view 0 tree)]
       (when (= :returned stage)
         [:p.demo-point
          [:b "Look at the handle."] " Step 1 concluded " [:code (str "#" first)]
          "; this is " [:code (str "#" flight)] ". Reviving a blocked conclusion is a "
          [:i "re-derivation"] ", not a flag being flipped: the old record was swept and "
          "is gone" (when first
                      (list " (" [:a {:href (str "/sentex/" first)} (str "#" first)]
                            " resolves to nothing)")) ", and the rule earned this one "
          "again from scratch. Identical proof, different record — which is the part a "
          "slideshow could not fake."])
       [:p.muted [:a {:href (str "/why/" flight)} "The whole proof"] " · "
        [:a {:href (str "/sentex/" flight)} "the record"]]])))

(defn- demo-fact-row
  "One watched sentence and what the KB says about it right now: the record and its
  belief pill when it is stored, and plainly *not stored* when it is not — which on this
  page is half the point, the interesting transitions deleting records rather than
  relabelling them."
  [{:keys [kb sandbox] :as view} {:keys [form note]}]
  (let [h (when sandbox (v/handle-of kb form sandbox))
        s (when h (v/sentex kb h))]
    [:li.demo-fact
     (if s
       (list (sentex-ref view s) " " (state-tag view h))
       (list [:span.demo-absent (render-form view form)] " "
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
  ([view] (demo-page view nil))
  ([{:keys [sandbox] :as view} first-h]
   (let [st (demo-state view first-h)]
     (render view "belief that changes"
             [:h2 "Believed, then not, then believed again"]
             [:p.muted "A rule concludes that Pingu flies. Learning one more true thing "
              "stops the KB believing it — without deleting it, without contradicting it, "
              "and without anyone ranking one claim over another — and un-learning that "
              "thing brings it back. Each step below is a real write to "
              [:a {:href "/assert"} "your own sandbox"] "."]
             (demo-ledger st)
             [:h3 "The conclusion under test " [:span.muted "(hasCapability Pingu flying)"]]
             (demo-verdict view st)
             (demo-controls st)
             [:h3 "Everything about Pingu " [:span.muted "as the KB holds it right now"]]
             [:ul.demo-facts (for [w demo-watched] (demo-fact-row view w))]
             [:p.legend "Everything here is in " [:code (str sandbox)] ", your own sandbox. "
              [:b "Start over"] " discards it whole."]))))

(defn demo-apply
  "Do one step's write, and answer the `first`-handle to carry forward.

  Split from the rendering because the page has to be built from a view taken *after*
  the write: whether the sandbox exists is a per-request read, and step 1 is the request
  that brings it into being.

  Both adding steps open the sandbox first.  Without its `genlCx` edge the sandbox
  sees no shipped context, so CxBiology's flight rule would not be visible from it
  and the write would derive nothing at all — the demo would quietly do nothing rather
  than fail."
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
  "The new-sentex form: one sentence per line, a context, and the known-true switch.
  `state` carries back what the reader typed and whatever `check` said about it."
  [{:keys [text ctx monotonic? problems sandbox]}]
  [:form.assert-form {:method "post" :action "/assert"
                      :hx-post "/assert" :hx-target "#main" :hx-select "#main"
                      :hx-swap "outerHTML"}
   (when (seq problems)
     [:ul.edit-errors (map problem-line problems)])
   [:label {:for "assert-text"} "Sentences " [:span.muted "(one per line)"]]
   [:textarea#assert-text {:name "text" :rows 6 :spellcheck "false"
                           :placeholder "(dog Muffet)"} text]
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
    [:code "(implies (dog ?x) (animal ?x))"] ". Every line is checked before anything "
    "is written, and the whole form is one settle — one bad line stores none of it."]
   [:div.editor-actions [:button.primary {:type "submit"} "Assert"]]])

(defn- assert-seed
  "The form as a term page opens it.  A **context** seeds the context field; anything
  else seeds the first line where its role belongs — a predicate or a type as the
  functor, an individual as an argument.  A starting point, not a submission: the line
  is deliberately incomplete, and `check` will say so if it is saved that way.

  A reified term seeds as the **expression** it denotes (`term-text`), which matters
  more here than anywhere else on the page: a textarea is content on its way back in, and
  `assert` reifies a ground NAT to the constant it already minted — so the expression
  writes about the very term the page is about, where a hand-typed `nat/` constant would
  be a reader asserting about an opaque identity."
  [view term]
  (let [role (when term (v/term-role term))
        text (when term (term-text view term))]
    (cond
      (nil? term)                            {}
      (= :context role)                      {:ctx text}
      (v/reified-term? term)                 {:text (str "( " text ")")}
      (contains? #{:predicate :type} role)   {:text (str "(" text " )")}
      :else                                  {:text (str "( " text ")")})))

(defn- sandbox-note
  "What a reset did, in the shape the assert form shows a message in.  A teardown is
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
  [{:keys [kb sandbox] :as view}]
  (when sandbox
    (let [n (if @(:sandbox-live? view) (count (sandbox/extent kb sandbox)) 0)]
      [:div#sbx-panel.sbx-panel
       [:p [:b "Your sandbox"] " "
        [:span.muted "— a context of your own, below everything shipped. It sees the whole "
         "KB; nothing shipped can see it, so you cannot break anything from here."]]
       [:p.muted [:code (str sandbox)] " · "
        (if (pos? n)
          (list n (if (= 1 n) " sentex" " sentexes")
                [:span.muted " (what you wrote, and what the rules concluded from it)"])
          "empty")]
       (when (pos? n)
         [:form {:hx-post "/sandbox/reset" :hx-target "#main" :hx-select "#main"
                 :hx-swap "outerHTML"}
          [:button {:type "submit"}
           "Reset — discard all " n]])])))

(defn assert-page
  "The new-sentex page: the form, and — after a save — what it stored."
  ([view] (assert-page view {} nil))
  ([{:keys [kb sandbox] :as view} state result]
   (render view "assert"
           [:h2 "Assert"]
           [:p.muted "Add knowledge the KB does not hold yet. "
            "The " [:a {:href "/levels"} "levels page"] " is for asking; this is for telling."]
           (sandbox-panel view)
           ;; the context field defaults to this session's sandbox, so writing somewhere
           ;; safe is what happens when the reader changes nothing
           (assert-form (cond-> (assoc state :sandbox sandbox)
                          (str/blank? (str (:ctx state))) (assoc :ctx (str sandbox))))
           (when-let [added (seq (flatten (:added result)))]
             (let [ss (keep #(v/sentex kb %) added)]
               (prime-belief! view (map :id ss))
               [:div
                [:h3 "Stored " [:span.muted "(" (count ss) " in one settle)"]]
                (sentex-list view ss)
                (derived-callout view result ss)])))))

;; ---- the reasoning gallery ----------------------------------------------
;;
;; `/demo` argues one thing at length.  This is the breadth: every kind of inference the
;; shipped ontology actually performs, each as a question with a live answer.
;;
;; Two properties keep it from being a brochure.  Each example **names the sentexes it
;; rests on** and those are looked up before anything is claimed, so switching to a
;; corpus that does not hold them greys the example out rather than answering from
;; vocabulary that is not there.  And each declares what the ontology is supposed to
;; answer, which `examples_test` asserts against the real KB — so a rule edited out from
;; under this page turns a test red instead of leaving a card that lies.
;;
;; Most of the cards cost no write at all.  The starter ships schema — types, taxonomy,
;; metadata, rules — so every question asked *about kinds* is answerable on render.  The
;; ones that need individuals bring their own and write them into the reader's own
;; sandbox, one click at a time.

(defn- example-dependency
  "One sentex an example rests on: the record itself where the KB holds it, and plainly
  missing where it does not.  This is the line that makes the card checkable — every
  claim above it is about these handles."
  [view [sentence context h]]
  [:li (if h
         (list (handle-ref view h) " " [:span.muted (str context)])
         (list [:span.muted (render-form view sentence)] " "
               [:span.tag.tag-out "not in this KB"]))])

(defn- example-verdict
  "What the KB answered, and by what machinery.  `escalate` stops at the first level
  that answers, so the level names the mechanism: 3 is context inheritance, 5 a cached
  closure, 7 the rule chainers.  A closure answer carries **no handle** — the engine
  never materialized a sentex for it — and the card says so rather than leaving a gap
  where a proof would be."
  [view {:keys [expect]} {:keys [answered? level level-name handle why refused? problems]}]
  (cond
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
              [:ul.why (why-node view 0 why)]]
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
  [{:keys [kb] :as view} {:keys [id title shows premises goal refuse kind] :as ex}
   result established? available?]
  [:section.ex-card {:id (str "ex-" id)}
   [:h3 title]
   [:p.muted (str/replace shows #"\s+" " ")]
   [:ul.ex-deps (map #(example-dependency view %) (ex/dependencies kb ex))]
   (when (seq premises)
     [:div.ex-premises
      [:p.muted (if established? "Written into your sandbox:" "This one needs individuals:")]
      [:ul.ex-given (for [p premises] [:li (render-form view p)])]])
   [:p.ex-ask
    [:span.muted (if (= :refusal kind) "Try to assert " "Ask ")]
    (render-form view (or goal refuse))]
   (cond
     (not available?)
     [:div.ex-verdict [:p.muted "Not available in this KB — the sentexes above are what "
                       "it would reason from, and they are not stored here."]]
     ;; availability is asked of the KB and the verdict of the sandbox, so they are
     ;; separate answers: a card whose premises are not established yet is available and
     ;; unrun, which is a button rather than a shrug
     (and (seq premises) (not established?))
     (example-run-form id "Run it in my sandbox")
     :else
     (example-verdict view ex result))])

(defn reasoning-page
  "The gallery.  Every card is computed from the live KB on render; the ones with
  premises are computed from the sandbox once the reader has established them, and show
  a button until then."
  [{:keys [kb sandbox] :as view}]
  (let [live?  (boolean @(:sandbox-live? view))
        ctx-of (fn [{:keys [premises context]}]
                 (if (seq premises) sandbox (or context 'CxWell)))
        rows   (for [ex ex/examples
                     :let [ctx   (ctx-of ex)
                           avail (ex/available? kb ex)
                           est?  (and live? (ex/established? kb ex ctx))
                           run?  (and avail (or est? (empty? (:premises ex))))]]
                 [ex (when run? (ex/run kb ex ctx)) est? avail])]
    (render view "reasoning"
            [:h2 "What this ontology can work out"]
            [:p.muted "Every card is a question put to this KB, answered when the page "
             "loaded. Each names the sentexes it reasons from; a card whose sentexes this "
             "KB does not hold says so instead of answering."]
            [:p [:a.action {:href "/demo"} "Watch belief change"]
             [:span.muted " — the one below at length, in three clicks."] " · "
             [:a {:href "/levels"} "Trace a goal through the eight levels"] " · "
             [:a {:href "/network"} "Qualitative constraint networks"]]
            (when (some (comp seq :premises first) rows)
              [:p.legend "The examples that need individuals write them into "
               (if live? (list [:code (str sandbox)] ", ") "a context of this browser session's own, ")
               "which sees the whole shipped ontology and which nothing shipped can see "
               "into. "
               (when live?
                 (demo-step-form {:op "reset" :label "Discard my sandbox"}))])
            (for [g ex/groups]
              (list [:h2.ex-group g]
                    (for [[ex result est? avail] rows :when (= g (:group ex))]
                      (example-card view ex result est? avail)))))))

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
  "The believed sentexes that would go **besides** the selection, computed to a
  fixpoint from the justification graph — the same criterion the dependency-directed
  sweep applies: a datum goes when it is not a premise in its own right and every
  justification concluding it has an argument that is going.

  Answers `{:handles [...] :capped? bool}`.  It is an estimate in exactly one
  direction: a datum re-derivable through a witness the sweep finds and this walk did
  not is reported here and survives there, so the preview never *under*-states."
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
                                       (every? #(some doomed (:antecedents %))
                                               (v/supporting-justifications kb c)))))
                       (v/dependent-justifications kb h))]
        (recur (into doomed gone) (into (pop frontier) gone) (into extra gone))))))

(defn- retract-panel
  "The confirmation the Retract button opens: what is selected, what the sweep would
  take with it, and the button that actually does it.  A GET renders this and writes
  nothing; only its POST retracts."
  [{:keys [kb] :as view} handles]
  (let [ss (keep #(v/sentex kb %) handles)]
    (if (empty? ss)
      [:span]
      (let [{swept :handles capped? :capped?} (swept-by view (map :id ss))
            swept-ss (keep #(v/sentex kb %) swept)]
        (prime-belief! view (concat (map :id ss) swept))
        [:div.editor
         [:h3 "Retract " (count ss) " sentex" (when (not= 1 (count ss)) "es")]
         [:p.hint "Retraction is " [:b "dependency-directed"] ": it removes premise "
          "support and then sweeps every datum that has no witness left, so it can take "
          "conclusions the selection does not name. Anything still derivable another way "
          "stays."]
         [:h4 "Selected"]
         [:ul.retract-list (for [s ss] [:li (sentex-ref view s) " @ " (term-link view (:context s))])]
         (if (seq swept-ss)
           [:div
            [:h4 "And these lose their last witness "
             [:span.muted "(" (count swept-ss) (when capped? "+") " derived)"]]
            [:ul.retract-list
             (for [s swept-ss] [:li (sentex-ref view s) " @ " (term-link view (:context s))])]
            (when capped?
              [:p.muted "The walk stops at " sweep-cap " — there may be more behind it."])]
           [:p.muted "Nothing else rests on them."])
         [:form {:hx-post "/retract" :hx-target "#editor" :hx-select "unset"
                 :hx-swap "innerHTML"}
          [:input {:type "hidden" :name "handles" :value (str/join "," (map :id ss))}]
          [:div.editor-actions
           [:button.danger {:type "submit"} "Retract " (count ss)]
           [:button#sx-cancel {:type "button"} "Cancel"]]]]))))

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
  "Forward chaining as a job, and return its id.  A fixpoint over a corpus is minutes of
  this process's one writer with nothing on screen, which is what makes it a job rather
  than a request: `forward-chain` reports `{:derived :pending}` about four times a second,
  and a report is where a cancel lands.

  **Cancelling one is safe, and the page says so.**  The conclusions are placed as they
  are made, so an aborted fixpoint leaves a KB holding a *prefix* of the run rather than a
  corrupt one — the same open-world condition a cancelled load leaves.

  `cap` bounds it (`:max-derivations`).  `in-monitor` runs the work inside this process's
  write monitor, on the job's own thread.

  **A daemon's fixpoint reports nothing, and the bar says so** rather than pretending: an
  `:on-progress` is a function and functions do not cross an EDN wire (`serve.clj` says the
  same of the export's), so a remote target gets the bound and no callback.  The job is
  still a job — it runs off the request, it is on the screen, and it settles with the
  daemon's own answer — it just cannot be watched arriving."
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
            kb (cond-> {}
                 cap    (assoc :max-derivations cap)
                 local? (assoc :on-progress
                               (fn [{:keys [derived pending]}]
                                 (progress! {:phase :chaining :total nil
                                             :done (or derived 0)
                                             :note (note pending)}))))))))))))

;; ---- the chaining funnel -------------------------------------------------
;;
;; `/stats` says how many conclusions a run derived; this says *which rules* did the
;; deriving, which refused, and which never fired — the per-rule breakdown behind the
;; headline, and the ontological engineer's "which of my rules earn their place".  It reads
;; `chain-report` (placed / refused / silent, off the ledger and the justification graph)
;; and folds in the `violations` that carry each rule's handle.  No engine change and no
;; per-run counters: the stored ledger answers the funnel (docs/exceptions.md).

(def ^:private funnel-render-cap 200)

(defn- funnel-status-tag
  [status]
  (let [cls (case status :fires "tag-in" :blocked "tag-superseded" :silent "tag-out" "tag-out")]
    [:span {:class (str "tag " cls)} (name status)]))

(defn- funnel-run-form
  "Run forward chaining to a fixpoint and land back here, so the funnel fills in front of
  the reader.  The same job `/chain` runs — bounded by `max-derivations`, watchable and
  cancellable on `/jobs` — only its result page is this one rather than `/stats`."
  [_view]
  [:form.chain-form {:method "post" :action "/funnel"
                     :hx-post "/funnel" :hx-target "#main" :hx-select "#main" :hx-swap "outerHTML"}
   [:span "Run forward chaining "]
   [:input {:type "number" :name "max-derivations" :min 1 :placeholder "to a fixpoint"
            :title "an optional derivation bound"}]
   [:button {:type "submit"} "run"]])

(defn- funnel-why
  "Why a rule placed nothing — the reasons its refusals cluster on, which is what separates
  'never completed an antecedent set' from 'completes them and every one is blocked'.  A
  rule an exception blocks names the exception query too, not only the category."
  [view {:keys [status refused refusals excepts]}]
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
                (when (seq excepts)
                  [:span.muted " by "
                   (interpose ", " (for [e excepts] (render-form view e)))])
                (when (= :overflow refused) [:span.tag.tag-superseded " overflow"])
                (when (pos? freed) [:span.muted (str " (" freed " since freed)")])
                (when (and (empty? by) (not= :overflow refused) (zero? freed))
                  [:span.muted "blocked"])])
    [:span.muted "—"]))

(defn- funnel-violation
  [view {:keys [violation sentence context]}]
  [:div [:span.tag.tag-defeated (name violation)]
   (when sentence [:span " " (render-form view sentence)])
   (when context [:span.muted " @ " (term-link view context)])])

(defn- funnel-refused-rank
  [{:keys [refused]}]
  (if (= :overflow refused) Long/MAX_VALUE (long (or refused 0))))

(defn- funnel-row
  "One rule as a card, not a table row: the sentence on its own full-width line (so it
  wraps at spaces rather than being crushed into a column), then a compact metrics line.
  The reason is shown for a `:blocked` rule (its cluster) or a `:silent` one (the single
  reason it has); a `:fires` status pill already says everything its reason would repeat."
  [view {:keys [rule placed refused] :as row} viols]
  [:div.funnel-row
   [:div.funnel-sx (handle-ref view rule) " " (funnel-status-tag (:status row))]
   [:div.funnel-meta
    [:span.funnel-metric [:span.muted "placed "]
     (if (pos? (long placed)) (commas placed) [:span.muted "—"])]
    [:span.funnel-metric [:span.muted "refused "]
     (cond (= :overflow refused)        [:span.tag.tag-superseded "overflow"]
           (pos? (long (or refused 0))) (commas refused)
           :else                        [:span.muted "—"])]
    (when (contains? #{:blocked :silent} (:status row))
      [:span.funnel-metric.funnel-why (funnel-why view row)])]
   (when (seq viols)
     [:div.funnel-viols (for [v viols] (funnel-violation view v))])])

(defn funnel-page
  "Every forward rule and what chaining did with it — placed, refused (and why), or silent
  — ranked by what is wrong: no-placement rules first, by refusals descending, firing rules
  last.  A run form on `32`'s job registry populates it live."
  [{:keys [kb] :as view}]
  (let [rows   (v/chain-report kb)
        viols  (group-by :rule (v/violations kb))
        ;; **The last key is what the rule says, never its handle.**  Every silent rule
        ;; placed nothing and refused nothing, so the first two keys tie across the whole
        ;; silent block — and the list is capped at `funnel-render-cap`, which turns that
        ;; tie from a cosmetic order into *which rules a reader is shown*.  A handle is
        ;; allocated in assertion order, so the page would answer "which rules were
        ;; written first".  Keyed once per row rather than once per comparison (the row
        ;; already carries its `:sentence`, so this costs no fetch), and printed with the
        ;; print bounds released so no ambient `*print-length*` collapses two long rules
        ;; to one prefix and drops the tie back where it came from.
        ranked (binding [*print-length* nil *print-level* nil]
                 (->> rows
                      (mapv (fn [r] [[(if (pos? (long (:placed r))) 1 0)
                                      (- (funnel-refused-rank r))
                                      (pr-str (:sentence r))]
                                     r]))
                      (sort-by first)
                      (mapv second)))
        shown  (into [] (take funnel-render-cap) ranked)
        freq   (frequencies (map :status rows))]
    (prime-belief! view (map :rule shown))
    (render view "funnel"
            [:h2 "The chaining funnel"]
            [:p.muted "Every forward rule in the KB and what it does when chaining runs — "
             "what it placed, what it refused and why, or whether it never fired at all. "
             "The question " [:a {:href "/stats"} "the headline counts"] " cannot answer: "
             [:i "which"] " of the rules earn their place."]
            (funnel-run-form view)
            [:div.stats-grid
             [:div.stat [:span.stat-n (commas (count rows))] [:span.stat-l "forward rules"]]
             [:div.stat [:span.stat-n (commas (:fires freq 0))] [:span.stat-l "fire"]]
             [:div {:class (str "stat" (when (pos? (:blocked freq 0)) " stat-warn"))}
              [:span.stat-n (commas (:blocked freq 0))] [:span.stat-l "blocked"]]
             [:div.stat [:span.stat-n (commas (:silent freq 0))] [:span.stat-l "silent"]]]
            (if (empty? rows)
              [:p.muted "No forward rules in this KB. Forward chaining has nothing to run."]
              (list
               [:div.funnel-list (for [row shown] (funnel-row view row (get viols (:rule row))))]
               (when (> (count ranked) funnel-render-cap)
                 [:p.legend "Showing " funnel-render-cap " of " (commas (count ranked))
                  " rules held, no-placement first."])))
            [:p.legend "A " [:b "silent"] " rule never completed an antecedent set — nothing "
             "it needs is believed. A " [:b "blocked"] " one completes firings and cannot "
             "place them: an " [:span.tag "exception"] " holds, a " [:span.tag "naf"] " literal "
             "is contradicted, a " [:span.tag "post-join"] " literal had no answer, or an "
             "antecedent is " [:span.tag "hidden"] " in the placement context. A reason "
             "shown still holds against current belief — retract what blocks it and the "
             "rule is owed its conclusion."])))

;; ---- multi-sentex editing (drag-select → textarea → one settle) ---------
;; Selection is client-side (select.js, the one bit of JS); the server renders the
;; editable text for a set of handles and applies the save.  Save is `vaelii.core/edit!`
;; reached through the access facade, so it retracts the changed/removed sentexes and
;; asserts the new lines in **one settle**, in-process or against a live daemon alike.

(defn- ->long [s] (try (Long/parseLong (str s)) (catch Exception _ nil)))

(defn- ->form
  "Read a `?q=` / `?ctx=` query param as EDN, or nil when it is not readable.  Every
  route that takes a term or a goal parses through this: the value is whatever a URL
  carried, so `(` is as likely as `(dog Muffet)` and an unguarded read throws a 500
  rather than rendering a page.

  `Throwable`, not `Exception`, for the reason the daemon's reader carries: a deeply
  nested form overflows the reader's stack with a `StackOverflowError`, which is an
  `Error` — and one that escapes here is a 500 from Jetty rather than the nil this
  exists to return.  A URL is long enough to carry the nesting."
  [s]
  (try (edn/read-string (str s)) (catch Throwable _ nil)))

;; The editable line format is `vaelii.impl.llm.selection`'s, not a second copy of it:
;; the model's proposal lands back in this editor's textarea and is diffed against these
;; lines by content, so a byte of drift between the two spellings turns every unchanged
;; line into a retract plus an assert of the same fact.

(defn- parse-handles [csv]
  (->> (str/split (str csv) #",") (map str/trim) (remove str/blank?) (keep ->long) distinct vec))

(defn- edit-panel
  "The editor form for a set of handles: a textarea seeded with one editable
  `[sentence context]` line per still-present handle, above Save / Cancel.  `problems`
  and `text` are supplied when re-rendering after a save that would not have gone
  through — each problem naming the line it is about."
  [{:keys [kb]} handles & [{:keys [text problems]}]]
  (let [entries (for [h handles :let [s (v/sentex kb h)] :when s]
                  {:h h :line (selection/edit-line s)})]
    (if (empty? entries)
      [:span]
      [:div.editor
       [:h3 "Edit " (count entries) " sentex" (when (not= 1 (count entries)) "es")]
       (when (seq problems) [:ul.edit-errors (map problem-line problems)])
       [:form {:hx-post "/edit" :hx-target "#editor" :hx-select "unset" :hx-swap "innerHTML"}
        [:input {:type "hidden" :name "handles" :value (str/join "," (map :h entries))}]
        [:textarea {:name "text" :rows (max 4 (inc (count entries))) :spellcheck "false"}
         (or text (str/join "\n" (map :line entries)))]
        [:p.hint "One " [:code "[sentence context]"] " per line, checked before anything is "
         "written. Save retracts what you changed and asserts the new lines in one settle; "
         "an unchanged line touches nothing. Editing a rule drops any "
         [:code "exceptWhen"] " guard it carries."]
        [:div.editor-actions
         [:button.primary {:type "submit"} "Save"]
         [:button#sx-cancel {:type "button"} "Cancel"]]]])))

(defn- parse-edit-line
  "Parse one edited line to `{:key [sentence context] :entry [sentence context opts?]}`,
  or `{:error <msg>}` — the `:key` is the content used to diff against what is stored."
  [line]
  ;; `Throwable` for `->form`'s reason: a nested-enough line is a `StackOverflowError`,
  ;; and an unreadable line is this function's ordinary answer rather than a 500
  (let [v (try (edn/read-string line) (catch Throwable e {::bad (.getMessage e)}))]
    (cond
      (and (map? v) (::bad v)) {:error (str "unparseable: " (::bad v) " — " line)}
      (and (vector? v) (<= 2 (count v) 3) (some? (first v)) (some? (second v)))
      {:key [(first v) (second v)] :entry (vec v)}
      :else {:error (str "expected [sentence context] — got " (pr-str v))})))

(defn- oob
  "Mark a rendered element as an out-of-band swap addressing every row for `handle`.
  Rows are addressed by their `data-h` attribute rather than by an id because one
  handle can appear in more than one index group on a term page, and htmx's selector
  form of `hx-swap-oob` swaps **all** the matches — so every copy of a row moves."
  [style handle element]
  (assoc-in element [1 :hx-swap-oob] (str style ":[data-h='" handle "']")))

(defn- saved-rows
  "The out-of-band swaps a successful save sends in place of reloading the page: each
  retracted handle's row is replaced by the row its line became, or deleted when the
  line was deleted.

  A line and its handle are paired **by position** — the textarea is seeded one line per
  selected handle, so the n-th line is the n-th handle's, and a line rewritten in place
  retracts at that position and asserts at it.  Only that exact coincidence pairs; a
  line the reader appended, or one whose handle has no line left, is unpaired and shows
  up in the result panel instead of pretending to replace a row."
  [{:keys [kb] :as view} removals by-line]
  (for [{:keys [h line]} removals
        :let [replacement (some->> (get by-line line) (v/sentex kb))]]
    (if replacement
      (oob "outerHTML" h (sentex-row view replacement))
      (oob "delete" h [:li {:data-h h}]))))

(defn- save-result
  "What lands in the editor panel after a save: the tally, the sentexes that were added
  without replacing a row (a line the reader appended has no row to swap, so this is
  where it becomes visible and linkable), and a Close button — `#sx-cancel`, which
  select.js already wires to close the editor."
  [view unpaired n-added n-removed]
  [:div.editor
   [:h3 "Saved"]
   [:p.muted n-added " asserted · " n-removed " retracted · one settle."]
   ;; plain rows, not `sentex-row`: these sit in the editor panel rather than in a
   ;; listing, so they are not part of the page's selectable set
   (when (seq unpaired)
     [:ul (for [s unpaired]
            [:li (sentex-ref view s) " @ " (term-link view (:context s))])])
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

(defn- edit-post
  "Apply a save: diff the edited lines against the selected handles **by content**,
  check the batch that diff produces, then `edit` — retract the handles whose line
  changed or was deleted, assert the lines that are new; an unchanged line touches
  nothing (no handle churn).

  The answer **re-renders what changed** rather than reloading: the rows of the
  retracted handles are swapped out of band (replaced by their new row, or deleted),
  the selection chrome is corrected the same way, and the editor panel reports the
  save.  A line that does not parse, or a batch `check` refuses, writes nothing and
  comes back as a message beside the line with the user's text intact."
  [{:keys [kb] :as view} handles-csv text]
  (let [handles (parse-handles handles-csv)
        lines   (->> (str/split-lines (str text)) (map str/trim) (remove str/blank?))
        parsed  (vec (map-indexed (fn [i p] (assoc (parse-edit-line p) :line i)) lines))
        unread  (for [{:keys [error line]} parsed :when error]
                  {:line line :type :unreadable :message error})]
    (if (seq unread)
      (frag (edit-panel view handles {:text text :problems unread}))
      (let [orig      (vec (for [[i h] (map-indexed vector handles)
                                 :let  [s (v/sentex kb h)] :when s]
                             {:h h :line i :key [(selection/wrapped-sentence s) (:context s)]}))
            orig-keys (set (map :key orig))
            new-keys  (set (map :key parsed))
            removals  (vec (remove #(new-keys (:key %)) orig))
            additions (vec (remove #(orig-keys (:key %)) parsed))
            batch     {:add (mapv :entry additions) :remove (mapv :h removals)}
            problems  (vec (batch-problems kb batch additions))]
        (if (seq problems)
          (frag (edit-panel view handles {:text text :problems problems}))
          (let [{:keys [added]} (v/edit! kb batch)
                ;; line index -> the handle the line became, for the positional pairing.
                ;; An entry is `assert`-shaped, so a line concluding a conjunction became
                ;; a *vector* of handles — no single row replaces the old one, so it
                ;; stays unpaired and surfaces in the result panel like an appended line
                by-line   (into {} (map-indexed (fn [k a]
                                                  (let [h (nth added k nil)]
                                                    [(:line a) (when-not (vector? h) h)])))
                                additions)
                stored    (flatten added)
                paired    (set (keep #(get by-line (:line %)) removals))
                unpaired  (into [] (comp (remove paired) (keep #(v/sentex kb %))) stored)
                remaining (- (count handles) (count removals))]
            (prime-belief! view (concat stored (map :id unpaired)))
            (frag (list (save-result view unpaired (count stored) (count removals))
                        (saved-rows view removals by-line)
                        ;; the selection chrome: the retracted handles are gone from the
                        ;; page, so the count they were part of is stale
                        [:span#sx-count {:hx-swap-oob "innerHTML"} remaining " selected"]))))))))

;; ---- the assert / retract / chain writes --------------------------------
;; Each goes through `vaelii.core/edit!` (or `forward-chain`) via the access facade, so
;; a browser attached to a daemon writes through the daemon's single-writer lock, and
;; every one of them is one settle.

(defn- assert-lines
  "Read the new-sentex textarea: one **sentence** per line (the context is its own
  field), as `[{:line i :entry [sentence context opts]}]` or a problem per unreadable
  line."
  [text ctx opts]
  (let [lines (->> (str/split-lines (str text)) (map str/trim) (remove str/blank?))]
    (reduce (fn [acc [i line]]
              ;; `Throwable` for `->form`'s reason: a nested-enough line overflows the
              ;; reader's stack, and that line is a problem to report, not a 500
              (let [form (try {:ok (edn/read-string line)}
                              (catch Throwable e {:bad (.getMessage e)}))]
                (if (:bad form)
                  (update acc :problems conj
                          {:line i :type :unreadable
                           :message (str "does not read as EDN: " (:bad form))})
                  (update acc :entries conj
                          {:line i :entry (if opts
                                            [(:ok form) ctx opts]
                                            [(:ok form) ctx])}))))
            {:entries [] :problems []}
            (map-indexed vector lines))))

(defn assert-post
  "Assert what the new-sentex form holds: read the lines, check them all against the
  KB, and — only when every one is admissible — apply them in one `edit`.  Nothing
  partial is ever written: a form with one bad line stores none of it, which is what
  makes the page safe to retry."
  [{:keys [kb sandbox] :as view} {:keys [text ctx monotonic?] :as state}]
  (let [ctx-sym (->form ctx)
        ;; the first write is what creates the sandbox, and it has to happen *before*
        ;; the checks: they are context-scoped, so a sandbox with no `genlCx` edge
        ;; yet would see none of the shipped vocabulary they are checked against
        _       (when (and sandbox (= ctx-sym sandbox)) (sandbox/open kb sandbox))
        opts    (when monotonic? {:strength :monotonic})
        {:keys [entries problems]} (assert-lines text ctx-sym opts)
        ctx-problem (when-not (symbol? ctx-sym)
                      [{:type :shape
                        :message (str "the context must be a bare symbol, got "
                                      (if (str/blank? (str ctx)) "nothing" (pr-str ctx)))}])
        batch    {:add (mapv :entry entries)}
        checked  (when-not (or (seq problems) ctx-problem)
                   (for [p (v/check-edit kb batch)]
                     (cond-> (select-keys p [:type :message])
                       (= :add (:in p)) (assoc :line (:line (nth entries (:index p) nil))))))
        all      (vec (concat ctx-problem problems checked))]
    (cond
      (empty? entries)
      (assert-page view (assoc state :problems
                               (or (seq all)
                                   [{:type :shape :message "nothing to assert — write a sentence"}]))
                   nil)
      (seq all) (assert-page view (assoc state :problems all) nil)
      :else     (assert-page view (assoc state :text nil)
                             (v/edit-with-consequences! kb batch)))))

(defn- retract-apply
  "Apply a checked retraction batch and render what went."
  [{:keys [kb] :as view} handles]
  (let [doomed  (into (vec handles) (:handles (swept-by view handles)))
        {:keys [removed]} (v/edit! kb {:remove handles})
        gone    (into [] (remove #(v/sentex kb %)) doomed)]
    (frag (list [:div.editor
                 [:h3 "Retracted"]
                 [:p.muted (:removed-sentexes removed) " sentexes · "
                  (:removed-justifications removed) " justifications · one settle."]
                 (when (> (count gone) (count handles))
                   [:p.muted "The sweep took " (- (count gone) (count handles))
                    " derived sentexes with them."])
                 [:div.editor-actions [:button#sx-cancel.primary {:type "button"} "Close"]]]
                (for [h gone] (oob "delete" h [:li {:data-h h}]))
                [:span#sx-count {:hx-swap-oob "innerHTML"} "0 selected"]))))

(defn retract-post
  "Retract the selected handles through `edit` — one settle for the whole selection,
  the same write path the editor's save takes.  The answer deletes every row that is
  actually gone out of band (the selection *and* whatever the dependency-directed sweep
  took with it), so the page corrects itself instead of reloading.

  The write is preceded by the `check-edit` round-trip every other write post makes
  (docs/operations.md): a stale handle — retracted out from under the page since it
  rendered — comes back as the problem panel rather than reaching `edit`, which
  refuses an unknown `:remove` handle outright."
  [{:keys [kb] :as view} handles-csv]
  (let [handles  (parse-handles handles-csv)
        problems (seq (for [p (v/check-edit kb {:remove handles})]
                        (select-keys p [:type :message])))]
    (if problems
      (frag [:div.editor
             [:h3 "Not retracted"]
             [:ul.edit-errors (map problem-line problems)]
             [:p.muted "Nothing was written."]
             [:div.editor-actions [:button#sx-cancel.primary {:type "button"} "Close"]]])
      (retract-apply view handles))))

;; ---- knowledge bases: the catalog page ----------------------------------
;;
;; Every other page is about one KB.  This one is about *which* — it lists what this
;; process can load (`catalog/sources`), what it has loaded (`catalog/entries`), and
;; drives the transitions between them.  A load takes minutes, so it runs on the
;; catalog's own thread and this page watches it: the loaded panel re-fetches itself once
;; a second **while a load is running** and stops asking the moment none is, which is the
;; whole of the polling logic (the server decides by including or omitting the trigger).

(defn- slider-pos
  "Where a knob's default sits on its 0–1000 track.  A count that ranges to millions is
  useless on a linear track — every interesting value is in the first pixel — so those
  knobs are marked `:scale :log` and mapped logarithmically here and in select.js, which
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
  sliders are `vaelii.impl.io.generate/knobs` rendered, so the page cannot disagree with
  the generator about a parameter's range or default."
  [{:keys [key type label default help choices min max step scale unit]}]
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
               [:input {:type "number" :name k :value default
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
;;
;; Two numbers of different kinds, and the panel keeps them visibly apart: the **heap**
;; is measured and belongs to the whole process (every KB, the browser, and uncollected
;; garbage in one figure), while a KB's **footprint** is estimated from its stored sentex
;; count.  Attributing heap to one of several resident KBs would mean unloading it and
;; diffing, which is not something a page may do to a KB somebody is reading — so the
;; estimate is the only per-KB answer there is, and it says so.

(defn- est-bytes
  "An estimated byte count, marked as one.  Everything the panel shows about a KB is an
  estimate, and a figure that reads like a measurement is worse than no figure."
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

(defn- entry-card
  "One loaded (or loading, or failed) KB.  Its footprint is read live rather than off the
  entry's load-time stats, so it tracks a KB that has been asserted into since — and a
  KB still loading, whose bar is then two readings of the same thing: how far the load has
  got, and what it is costing."
  [{:keys [key name status stats progress error elapsed-ms summary kb? job]} active?]
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
     (when error [:p.kb-error error])
     (when (and stats (= :done status))
       [:p.muted (commas (:sentexes stats)) " sentexes · " (commas (:terms stats)) " terms · "
        (commas (:types stats)) " types · " (commas (:contexts stats)) " contexts"
        (when (pos? (:derived summary 0)) (str " · " (commas (:derived summary)) " derived"))
        (when (pos? (:refused summary 0)) (str " · " (commas (:refused summary)) " refused"))
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
  Asked of `catalog/sources` rather than assumed, which is also what makes the partial
  case honest: `classify` keys on `meta.edn` and `export!` writes it last, so a cancelled
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
    [:label.kb-opt [:span "Destination directory "]
     [:input {:type "text" :name "dir" :size 40 :placeholder "/path/to/new-dump"}]
     [:span.muted " — a path on this machine; must be empty or not exist yet"]]
    [:label.kb-opt [:span "Variant "]
     [:select {:name "variant"}
      [:option {:value "records" :selected true} "Records — the whole KB"]
      [:option {:value "records+index"} "Records and index — larger, loads faster"]]]
    [:label.kb-opt [:span "Compression "]
     [:select {:name "compression"}
      [:option {:value "gzip" :selected true} "gzip"]
      [:option {:value "xz"} "xz — smaller, slower to write"]
      [:option {:value "none"} "none"]]]]
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
  ([view] (kbs-page view nil))
  ([view note]
   (let [loaded (into #{} (map (comp :id :source)) (catalog/entries))
         busy?  (catalog/loading?)]
     (render view "knowledge bases"
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
             (entries-panel (:fragment? view))
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
;;
;; Three operations here take minutes rather than milliseconds — a load, an export, and a
;; chaining run — and they are one mechanism (`vaelii.impl.jobs`) with one status
;; vocabulary.  This screen is that registry rendered: every job this process has run
;; recently, what it is doing, and the one control that stops it.  The `/kbs` panels are
;; the same registry filtered to the two kinds that belong beside a KB, which is why
;; nothing here is a second list of anything.
;;
;; A job **outlives the request that started it**, and that is the point: closing the tab
;; cancels nothing, and reopening this page finds the run still going.  The poll is the
;; self-terminating htmx one every other watching panel uses — it survives a reload, which
;; a socket does not.

(defn- job-card
  "One job: what it is, where it has got to, and what it left behind.  A running one offers
  the cancel; a finished one offers the page its result is on, since a job that ran while
  the reader was elsewhere is exactly the case a result link is for."
  [{:keys [id label kind status progress error elapsed-ms summary result-url writes?]}]
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
    (when (= :running status) (kb-action "Cancel" "/jobs/cancel" {:id id}))
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

(defn- jobs-page
  "The jobs screen.  `note` is what the registry said about the action that led here — a
  cancel of a job that has already finished is a state to report, not an error."
  ([view] (jobs-page view nil))
  ([view note]
   (render view "jobs"
           [:h2 "Jobs"]
           (when note [:p.problem note])
           [:p.muted "Loading a KB, writing one out and running the rules to a fixpoint all "
            "take longer than a request should, so each runs as a job. Closing this tab "
            "does not stop one — come back and it is still here. A finished job's report "
            "stays for an hour."]
           [:p.muted "Watching one and wondering what it costs: "
            [:a {:href "/caches"} "the caches page"] " says what this process is holding "
            "while it runs, and its numbers move as the job does."]
           (jobs-panel (:fragment? view)))))

;; ---- what this process is holding: caches, heap, and the profiler -------
;;
;; This is the **programmer's** screen, and the one page here about the process rather
;; than about the knowledge.  `/kbs` measures heap honestly and says so; nothing measured
;; what the engine holds *beside* the store — a dozen derived structures whose whole
;; purpose is that a repeated question is not recomputed, and no way to see whether that
;; is happening.  A hit rate is the cost model's report card: "the second query was fast"
;; is a demo, and "the second query was fast because it was served from a cache, and here
;; is the rate" is evidence.
;;
;; The reads are `v/caches`, which is O(1) per row by construction — a count off a map
;; the engine already holds, never a walk of the KB — so the panel polls like every other
;; watching panel here.  It reuses the heap strip rather than redrawing one, and inherits
;; that strip's distinction between a measurement and an estimate along with it.

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
  "Start the sampling profiler's UI when the operator asked for one (`VAELII_PROFILER`)
  and the class resolves.  A no-op otherwise, and a logged line when the operator asked
  and it is absent — a switch that reads as set and does nothing is the failure the
  `config` namespace exists to prevent.

  **One UI, whoever asks.**  The claim is a `compare-and-set!` onto `::starting`, so the
  two ways a second one could be started are both closed: a namespace reload calling this
  again (the `defonce` remembers the running server across it) and two threads calling it
  at once (a test-then-act on the same state would let both past the test and race for the
  port).  A start that *fails* puts the state back, since nothing then holds the port and a
  later call should be free to try again.

  Bare, not `!`: it starts a server and destroys nothing.  Called by both entry points,
  so the variable means the same thing to `lein browser` as to `lein run -m
  vaelii.impl.web`; only the first has the dependency, which is what the second one's
  log line says."
  []
  (when (and (config/profiler?) (compare-and-set! profiler-state nil ::starting))
    (if-let [serve-ui (profiler-serve-ui)]
      (let [port (config/profiler-port)]
        (try
          (serve-ui port)
          (reset! profiler-state {:port port})
          (trove/log! {:level :info :id ::profiler
                       :msg (str "profiler UI on http://localhost:" port)})
          (catch Throwable t
            (reset! profiler-state nil)
            (trove/log! {:level :warn :id ::profiler
                         :msg (str "profiler UI would not start on port "
                                   (config/profiler-port) ": " (.getMessage t))}))))
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
  disagree, both.  The literal cache is exactly that case: its entries are this KB's and
  its hit counters are global `AtomicLong`s across every KB in the process, since they
  measure the mechanism rather than a store. Rendering the second as though it were the
  first is how a page attributes another KB's work to this one."
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

(defn- caches-page
  "The cache screen.  `note` is what a clear reported, above the numbers it changed."
  ([view] (caches-page view nil))
  ([{:keys [kb] :as view} note]
   (let [rows      (v/caches kb)
         permanent (->> rows (remove :clearable?) (map :label) sort)
         ;; the rows whose *rates* are the process's: clearing one of those from here
         ;; zeroes what every other KB's page is reading, which a control offered as a
         ;; per-KB one has to say before it is pressed rather than after
         shared    (->> rows
                        (filter #(and (:clearable? %) (= :process (:counters %))))
                        (map :label) sort)]
     (render view "caches"
             [:h2 "Caches"]
             (when note [:p.problem note])
             [:p.muted "What this process is holding beside the stores. Every row is a "
              "structure the engine keeps so a repeated question is not recomputed, and "
              "the hit rate is the only evidence that it is working."]
             (memory-panel false)
             [:h3 "What is cached"]
             (caches-panel rows)
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
  not offer it (`:unknown-option`, the type every other option door throws).

  Both sides are read through `(comp keyword name)`, because a `:choices` entry spells its
  value either way — the dump's are keywords, the generator's and the corpus's are
  strings — and `option-control` builds the `<option value>` the browser sends out of the
  same `name`.  So the roster the page rendered and the roster checked here cannot be two
  rosters.

  Refused rather than coerced, for `opts/check!`'s reason at every other option door: a
  keyword no reader's arm matches falls to that reader's own default, silently and at a
  setting nobody chose.  `:belief?` is the sharp case — its unmatched arm is the
  records-only load, which never opens the justification stream — and a load is the one
  action here nobody watches finish.  A non-string value refuses the same way rather than
  reaching `keyword` as a cast error the page cannot render."
  [{:keys [key label choices]} raw]
  (let [legal (into #{} (map (comp keyword name first)) choices)
        v     (when (string? raw) (keyword raw))]
    (if (contains? legal v)
      v
      (throw (ex-info (str "no such " (name key) ": " (pr-str raw) " — "
                           (or label (name key)) " offers "
                           (str/join ", " (map (comp name first) choices)))
                      {:type :unknown-option :option key :value raw
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

  The view is built **after** the action, not before: activating changes which KB the
  page reads, and rendering the one it was reading a moment ago would show the switch as
  not having happened.  What the catalog refuses — a second concurrent load, a source
  already loaded, an entry whose loader has not yet stopped — comes back as a note on the
  page."
  [act make-view]
  (let [note (try (act) nil
                  (catch clojure.lang.ExceptionInfo e (.getMessage e)))]
    (kbs-page (make-view) note)))

(defn kbs-load
  "Start loading source `id` with the options the form submitted."
  [id params]
  (when-let [src (catalog/source id)]
    ;; the one KB write that does not go through this namespace's write monitor, and
    ;; deliberately: a loader opens brand-new stores nothing else can name yet, so there is
    ;; no KB on screen for it to interleave with.  Its `:writes` claim in the job registry
    ;; is what keeps it the only writing job, which is the exclusion that actually matters
    (catalog/load-source id (option-params src params))))

(defn- export-opts
  "The writer options the export form submitted, as `export!`'s own keywords — and only
  the ones actually named, so the defaults stay the writer's rather than being restated
  by whoever renders the form."
  [params]
  (cond-> {}
    (seq (get params "variant"))     (assoc :variant (keyword (get params "variant")))
    (seq (get params "compression")) (assoc :compression (keyword (get params "compression")))))

;; ---- routing ------------------------------------------------------------

;; The origin check lives in `vaelii.impl.guard`, shared with the daemon: both servers
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
  the value quoted, and what would have been legal.

  A rendered page rather than the plain text the two refusals above answer with, because
  the caller *is* one of our own readers — a `?d=` that does not parse is a URL somebody
  edited by hand, and the chrome is how they get back to a page that works.

  A refusal rather than a fallback, which is the whole point.  Every silent reading of an
  unreadable parameter is worse than a stop: a bound that does not parse runs the work
  **unbounded**, a depth that does not parse takes the default, and a calculus name
  nothing answers to draws a *different* calculus — each of them a page that looks
  exactly like the one that was asked for."
  [view param value legal]
  (assoc (render view "bad request"
                 [:h2 "Bad request"]
                 [:p "The " [:code param] " parameter is not readable: "
                  [:code (pr-str value)] "."]
                 [:p.muted legal])
         :status 400))

(defn- unsupported-context
  "The 400 a page owes for a `?ctx=` naming a **query context** it cannot resolve.

  `CxEverything` / `CxInference` / `CxNothing` are readings rather than places
  (docs/contexts.md), and only the four reads that resolve one take them — the
  levels and the plan above them go through doors that do not, so the engine refuses with
  `:unsupported-context` where this handler stack has no exception middleware to make a
  page of it.  That is a 500 on a value the page's *own* context box will send, which is
  why it is checked here rather than caught.

  `bad-parameter`'s shape and its reason, in different words: the parameter reads
  perfectly well, it just names something this page cannot ask about, and answering for a
  context nobody asked about would look exactly like the page that was asked for."
  [view ctx]
  (assoc (render view "bad request"
                 [:h2 "Bad request"]
                 [:p "The " [:code "ctx"] " parameter names a reading rather than a place: "
                  [:code (pr-str ctx)] "."]
                 [:p.muted "This page asks what a context holds, so it needs a context that "
                  "holds something. " (str/join ", " (sort (map str nm/query-contexts)))
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

  Read for *presence* alone — the shape a checkbox invites — any value at all asserts
  `{:strength :monotonic}`, `strength=default` included, which is the one value a reader
  could reasonably send meaning the opposite."
  [raw]
  (cond
    (nil? raw)                                                nil
    (and (string? raw) (strength/assertable? (keyword raw)))  (keyword raw)
    :else                                                     unreadable))

(defonce ^:private ^Object write-monitor
  ;; Jetty serves the write routes on a thread pool, so two POSTs are two writers, and
  ;; the storage layer is written on the promise that they are not: `disk/kv.clj`'s
  ;; `apply-ops!` folds the ops against a `@data` read outside its lock and publishes
  ;; with a `reset!` outside it too, saying in its own docstring that single-writer is
  ;; what makes the read-compute-publish race-free.  Interleave two and the WAL holds
  ;; both frames while the RAM map holds one, so the running index and the one replayed
  ;; on the next open disagree.  `write-blocked?` does not close this: it asks whether a
  ;; *loader* is filling the KB, which is a different question from whether another
  ;; request is writing.  Process-wide rather than per-KB — the operator is one person
  ;; and the contention is nil, where sharing a store between two catalog entries is not
  ;; something the monitor could see.  The daemon holds its own (`serve.clj`).
  (Object.))

(defn- after-writes-drain
  "Run `work` once any synchronous write already past the doors has finished — a
  **barrier**, where `writing-job` gives a KB write the monitor's exclusion.

  An export walks the records and writes the *filesystem*, so what it cannot survive is
  the KB moving under the walk — and that is already refused for the walk's whole
  duration from both sides: `exporting-kb?` is true from the moment the job is submitted,
  which is what `write-refusal` turns the content routes back on, and `unload!` makes its
  own `exporting-kb?` check under the catalog's start monitor.  What neither refuses is
  the write that slipped past a door in the moment *before* the job was submitted, and
  that is the one thing this waits for.

  Holding the monitor across the walk instead — which is what the route did, against a
  comment saying it drained a write before the walk *started* — parks every later
  `/kbs/unload` on a Jetty worker for the length of a multi-minute dump, with no page and
  no progress, on ring-jetty's default pool of 50."
  [work]
  (locking write-monitor nil)
  (work))

(defn- write-refusal
  "Nil when this request may write `target`'s KB, and the **page** saying why not when it
  may not: the origin check, whether a job holds this process's writer, and whether the
  KB is one whose belief was never built.

  A KB can be read while a job fills it, which is what makes an arriving corpus browsable
  — but it cannot be *written* while one does.  A store mutation lands atomically so a
  reader beside the job sees a consistent prefix; two interleaved writers are not
  serializable at all (docs/storage.md, the single-writer contract), and the job is
  already this process's writer.  So the reads stay open and the writes are refused.

  **The last arm is the same sentence about a different clock.**  A KB stored without its
  derived state is readable — with the banner saying what is missing — and unwritable for
  as long as it stays that way, which can be days: the definitional checks all read
  `jtms/in?`, so over an empty network they match nothing and pass, and the store keeps
  what they would have refused.  The engine's own doors throw `:unrecovered-kb` for it, so
  this arm is not what makes the write fail; it is what makes it fail *on this page*.

  The refusal is a page, not an error status, for the reason `kbs-page` renders one: the
  reader is still somewhere sensible and is owed a sentence about why nothing happened.
  An error status would leave htmx not swapping at all, which is a silent no-op — the
  worst possible answer to \"why did my assert vanish?\".  It **names the job that holds
  the writer** and links to it, because \"something else is writing\" is not an answer a
  reader can act on.

  The question is asked of the KB this request would actually write, not of whichever
  entry is active — so a second KB loading in the background never blocks a write to the
  one on screen, and a browser serving a KB the catalog never heard of is never blocked
  at all.  `kb` is that KB, **already resolved**: the caller (`writing` / `writing-job`)
  derefs the holder once and hands the same value here and to the write, so the KB
  judged is the KB written.

  And **named**: every arm below calls it `(kb-name kb)` rather than `(active-kb-name)`.
  The premise of resolving once is that `/kbs/activate` can re-point the holder between
  the deref and the render — so the active entry at render time is the one KB this page
  can be sure it did *not* judge."
  [kb req]
  (cond
    (not (same-origin? req))
    (cross-origin-refusal)

    (catalog/write-blocked? kb)
    (let [holder (jobs/writer)]
      (render (view kb req) "still writing"
              [:h2 "Nothing was written"]
              [:p [:b (kb-name kb)] " is being written by "
               (if holder
                 (list [:a {:href "/jobs"} (:label holder) " (job " (:id holder) ")"])
                 "a job")
               ", and that job is this process's one writer — so this KB can be read while "
               "it changes, but not changed."]
              [:p.muted "Wait for it to finish, cancel it on the "
               [:a {:href "/jobs"} "jobs"] " page, or switch to another KB on the "
               [:a {:href "/kbs"} "knowledge bases"] " page."]))

    ;; the reciprocal of `export-entry!`'s still-loading refusal: the dump walks the
    ;; records with no snapshot, so while it runs the KB can be read but not changed —
    ;; the export claims no writer (a load of another KB is none of its business), so
    ;; the job registry cannot answer for it and the catalog is asked directly
    (catalog/exporting-kb? kb)
    (render (view kb req) "still exporting"
            [:h2 "Nothing was written"]
            [:p [:b (kb-name kb)] " is being exported, and the dump walks the "
             "records one by one with no snapshot — a write landing mid-walk would "
             "leave it a dump of no single state."]
            [:p.muted "Wait for it to finish or cancel it on the "
             [:a {:href "/kbs"} "knowledge bases"] " page."])

    ;; ...and the caveat banner's second condition, seen from this side.  The banner
    ;; explains an *answer*; this is the same state refusing a *write*, which the engine
    ;; door would throw for (`:unrecovered-kb`) — refused here so it renders as the page
    ;; the two refusals above render rather than as an exception htmx cannot swap.
    ;; Asked only of an in-process KB: an attached daemon has none of this to report,
    ;; exactly as `catalog/active-caveat` has nothing to say about one.
    :else
    (when-let [hz (when (:records kb) (not-empty (kb/write-hazards kb)))]
      (render (view kb req) "not recovered"
              [:h2 "Nothing was written"]
              [:p [:b (kb-name kb)] " is stored but not built: "
               (if (:no-index hz)
                 "neither its belief network nor its index was rebuilt from the records"
                 "its belief network was never rebuilt from the records")
               " — so every definitional check would match nothing and pass, and this KB "
               "would keep a fact it would otherwise refuse."]
              [:p.muted "Reading it is fine, which is what the banner above is about. To "
               "make it writable, run "
               [:code (if (:no-index hz) "(reindex kb)" "(recover kb)")]
               " against it, or load it again with belief on from the "
               [:a {:href "/kbs"} "knowledge bases"] " page."]))))

(defn- writing
  "The guard every synchronous write to a KB's *content* goes through: `write-refusal`,
  and the monitor that makes this process's own writes one at a time.

  **The holder is dereferenced once**, and `f` is handed the KB that deref yielded.
  `/kbs/activate` can re-point the holder at any moment — it takes no monitor, and an
  entry still loading is activatable by design — so a write that resolved the holder
  again after the refusal could land on a KB the refusal never judged, one whose loader
  is this process's writer.  `f` takes the KB as its argument for that reason; nothing
  past the refusal resolves the target.

  Not for `/kbs/load` `/kbs/unload` `/kbs/activate`: those write this process's registry
  rather than a KB, and cancelling a load has to stay reachable *because* one is running.
  Not for a **job** either, which is `writing-job` below — a job takes the monitor on its
  own thread, and a request that waited for it inside the monitor would hold the very lock
  the job needs and time out every time."
  [target req f]
  (let [kb (current target)]
    (or (write-refusal kb req)
        (locking write-monitor (f kb)))))

(defn- writing-job
  "The same guard for a write that runs as a **job**: refuse for the same reasons, then
  hand `f` the KB the refusal judged and a wrapper it runs the work in.  The wrapper is
  the write monitor, taken on the job's own thread — so a synchronous write that slipped
  past the refusal in the moment before the job claimed the writer waits for it rather
  than interleaving with it.

  The refusal is what stops two writing jobs; this is what stops a job and a request."
  [target req f]
  (let [kb (current target)]
    (or (write-refusal kb req)
        (f kb (fn [work] (locking write-monitor (work)))))))

(defn- job-answer
  "Start a job (`start`, returning its id) and answer for it.

  **The 250 ms fast path**, which is the whole reason a job is not always a progress page:
  a job that settles inside `jobs/fast-path-ms` is answered with its result (`done`, given
  the finished job), and only one still running is answered with the jobs screen.  Without
  it every small operation acquires a spinner and a second round trip, and the tool feels
  slower than the thing it replaced.  A job that settled by *failing* goes to the screen
  too, since that is where its error is written down.

  And when the registry **refuses** the job — another job holds this process's writer —
  the answer is that screen carrying the refusal as a note, naming the job that holds it.
  A refusal is a state to show rather than an error status, exactly as `kbs-post` treats
  the catalog's."
  [view start done]
  (try
    (let [j (jobs/wait (start) jobs/fast-path-ms)]
      (if (= :done (:status j))
        (done j)
        (jobs-page view)))
    (catch clojure.lang.ExceptionInfo e
      (jobs-page view (.getMessage e)))))

(defn- cached
  "Stamp a static asset's answer with the cache policy `dev?` chose.  A miss (nil) is
  passed straight through, so it still falls to the next handler."
  [handler]
  (letfn [(stamp [r] (cond-> r
                       (= 200 (:status r))
                       (assoc-in [:headers "Cache-Control"] static-cache-control)))]
    (fn
      ([req] (some-> (handler req) stamp))
      ([req respond raise] (handler req #(respond (some-> % stamp)) raise)))))

(def ^:private offset-cap
  "The largest `&offset=` any continuation is read at.  A billion rows past the start of
  a list nobody scrolled to, so it truncates no cursor this page ever writes — every one
  of them is a multiple of a page cap and bounded by what the KB holds.

  It exists because the offset is *arithmetic*: `find-rows-page` asks the term roster for
  `offset + find-cap + 1` names, and `Long/MAX_VALUE` — which a hand-edited URL may
  perfectly well carry — overflows that addition into an `ArithmeticException` the handler
  stack has no exception middleware to make a page of.  Capped rather than refused,
  because an offset past the end is not a bad request: it is a cursor pointing past the
  last row, and the honest answer to that is the empty page it already gives."
  1000000000)

(defn- ->offset
  "An `&offset=` param as a non-negative long in `[0 offset-cap]` — a continuation cursor
  arrives in a URL, so anything unreadable is the start and anything past the ceiling is
  the ceiling."
  [s]
  (-> (or (->long s) 0) (max 0) (min offset-cap)))

(defn- ->seq
  "A repeated form field.  Ring hands back a bare string for one occurrence and a vector
  for several, and a caller iterating the first gets its characters — so every repeated
  field is read through this."
  [v]
  (cond (nil? v) [] (sequential? v) (vec v) :else [v]))

(def ^:private loopback
  "The interface the browser binds unless told otherwise.  It is an operator tool with
  a write route (`POST /edit`) and no authentication, so it answers only the machine it
  runs on; exposing it is an explicit choice (`--listen`), and one that **requires**
  `VAELII_API_TOKEN` (`guard/require-token!`, and `-main` below).

  Loopback says *which machine*, not which page: a page the operator visits runs on
  that machine too, which is what the guards in `vaelii.impl.guard` are for."
  "127.0.0.1")

(defn- with-token
  "The handler a **public** bind serves: `served` behind the shared bearer token, with
  the browser's own 401 — `text/plain`, since what is on the other end of a public bind
  is a browser or the proxy in front of one, and an EDN body would render as a download.

  Only a public bind, and that is deliberate: `--listen` with an address is the one
  configuration the token is *required* for, so wrapping the loopback default as well
  would take a variable a daemon on the same machine already needs and make it a
  password on the operator's own browser.  Nothing is served open on an address —
  `guard/require-token!` has already refused that start."
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

(defn app
  "The ring handler for a KB.  Pure `request -> response`.

  `target` is what each page reads: a KB, an access value (`v/local` / `v/remote`), or a
  **holder** — anything deref-able, yielding whichever of those is current
  (`vaelii.impl.catalog/holder`).  A holder is what makes the KB switchable: every
  handler resolves it per request, so activating another entry re-points the whole
  browser without rebuilding the handler.

  This is the routing half only.  What gets *served* is `handler`, which adds the
  `Host` allowlist — a test drives `app` directly and supplies no `Host` at all."
  [target]
  (-> (ring/ring-handler
       (ring/router
        [["/"           {:get (fn [req] (default-page (view (current target) req)))}]
         ["/stats"      {:get (fn [req]
                                (stats-page (view (current target) req) nil
                                            (some? (get-in req [:query-params "clashes"]))))}]
         ;; forward chaining is a *write* (it derives and places conclusions), so it is
         ;; POST-only and guarded like any other; it runs as a **job**, so a fixpoint over
         ;; a corpus is watchable and stoppable rather than a request nobody can see
         ;; inside.  A run that settles inside the fast path answers with the stats page it
         ;; changed, exactly as it did when it was synchronous.
         ;; the job is labelled `(kb-name kb)` and not `(active-kb-name)`, for the reason
         ;; `write-refusal` names its arms that way: `writing-job` resolved the holder
         ;; once and `/kbs/activate` may have re-pointed it since, so the active entry is
         ;; the one KB this job can be sure it is *not* writing — and the label is what a
         ;; reader on the jobs screen decides to cancel from
         ["/chain"      {:post (fn [req]
                                 (let [raw (get-in req [:params "max-derivations"])
                                       cap (param-long raw 1 Long/MAX_VALUE)]
                                   (if (= unreadable cap)
                                     (bad-parameter (view (current target) req)
                                                    "max-derivations" raw derivations-legal)
                                     (writing-job
                                      target req
                                      (fn [kb in-monitor]
                                        (job-answer
                                         (view kb req)
                                         #(chain-job kb (kb-name kb) cap in-monitor)
                                         #(stats-page (view kb req)
                                                      (chain-note (:summary %)))))))))}]
         ;; the per-rule breakdown behind the chain headline: which forward rules placed,
         ;; which refused (and why), which never fired.  GET reads the standing ledger;
         ;; POST runs the same chaining job as /chain but lands back here, so the funnel
         ;; fills in front of the reader
         ["/funnel"     {:get  (fn [req] (funnel-page (view (current target) req)))
                         :post (fn [req]
                                 (let [raw (get-in req [:params "max-derivations"])
                                       cap (param-long raw 1 Long/MAX_VALUE)]
                                   (if (= unreadable cap)
                                     (bad-parameter (view (current target) req)
                                                    "max-derivations" raw derivations-legal)
                                     (writing-job
                                      target req
                                      (fn [kb in-monitor]
                                        (job-answer
                                         (view kb req)
                                         #(chain-job kb (kb-name kb) cap in-monitor "/funnel")
                                         (fn [_] (funnel-page (view kb req)))))))))}]
         ;; what this process is holding beside the store: the caches, the heap strip
         ;; `/kbs` already draws, and the profiler.  The clear is origin-checked like
         ;; every other POST and is deliberately **not** behind `writing`: it changes no
         ;; belief, holds no writer, and a reader most wants it while a load runs.  The
         ;; holder is dereferenced **once** all the same, for `write-refusal`'s reason:
         ;; `/kbs/activate` re-points it between two derefs and takes no monitor, so a
         ;; page rendered off a second one would report a clear of one KB over another
         ;; KB's rows
         ["/caches"       {:get (fn [req] (caches-page (view (current target) req)))}]
         ["/caches/rows"  {:get (fn [_] (frag (caches-panel (v/caches (current target)))))}]
         ["/caches/clear" {:post (fn [req]
                                   (if (same-origin? req)
                                     (let [kb (current target)
                                           r  (v/clear-caches kb)]
                                       (caches-page (view kb req)
                                                    (caches-clear-note r)))
                                     (cross-origin-refusal)))}]
         ;; the jobs screen: every long run this process has made recently, and the one
         ;; control that stops one.  The list is a self-terminating poll like the KB panels
         ;; — it stops asking the moment nothing is running — and the cancel is a write to
         ;; this process's registry rather than to a KB, so it is origin-checked and not
         ;; behind `writing` (cancelling a job has to stay reachable *because* one runs)
         ["/jobs"        {:get (fn [req] (jobs-page (view (current target) req)))}]
         ["/jobs/rows"   {:get (fn [_] (frag (jobs-panel true)))}]
         ;; `cancel!` answers whether there was a run to stop, which is not the same as
         ;; whether the registry still holds the id: a settled job keeps its report for an
         ;; hour, and the reader who clicks stop the moment it finishes is owed "nothing
         ;; happened" rather than a cancellation over work already done.  Both falses read
         ;; the same way, so the note names both
         ["/jobs/cancel" {:post (fn [req]
                                  (if (same-origin? req)
                                    (let [id (get-in req [:params "id"])]
                                      (jobs-page (view (current target) req)
                                                 (when-not (jobs/cancel! id)
                                                   (str "No job " id " to stop — it has "
                                                        "already finished, or its report has "
                                                        "aged out of the registry."))))
                                    (cross-origin-refusal)))}]
         ;; the knowledge bases themselves: what is loaded, what can be, and which one
         ;; every other page is reading.  The three writes change this process's state
         ;; rather than a KB's content, and are origin-checked like any other write; the
         ;; view is rebuilt *after* each of them, since activating changes what it reads.
         ["/kbs"          {:get (fn [req] (kbs-page (view (current target) req)))}]
         ["/kbs/rows"     {:get (fn [_] (frag (entries-panel true)))}]
         ;; the provisional-KB strip, re-read on its own while a load runs.  It says what
         ;; is true of the *active* KB rather than of a page, so like the memory strip it
         ;; takes no view and swaps only itself — and it answers with the empty element
         ;; once there is nothing to say, which is what stops the polling.
         ["/kbs/banner"   {:get (fn [_] (frag (caveat-banner)))}]
         ;; the memory strip, collapsed or expanded — a read of this process rather than
         ;; of a KB, so it takes no view and swaps only itself
         ["/kbs/memory"   {:get (fn [req]
                                  (frag (memory-panel
                                         (some? (get-in req [:query-params "detail"])))))}]
         ["/kbs/load"     {:post (fn [req]
                                   (if (same-origin? req)
                                     (kbs-post #(kbs-load (get-in req [:params "id"]) (:params req))
                                               #(view (current target) req))
                                     (cross-origin-refusal)))}]
         ;; the monitor goes in for the reason the export route hands one: unloading is a
         ;; registry write, but *releasing* is the end of a KB's stores, and a synchronous
         ;; write already past the write doors has to drain before they go rather than
         ;; interleave with the clear
         ["/kbs/unload"   {:post (fn [req]
                                   (if (same-origin? req)
                                     (kbs-post #(some-> (get-in req [:params "key"])
                                                        (catalog/unload!
                                                         {:run-in (fn [work]
                                                                    (locking write-monitor (work)))}))
                                               #(view (current target) req))
                                     (cross-origin-refusal)))}]
         ["/kbs/activate" {:post (fn [req]
                                   (if (same-origin? req)
                                     (kbs-post #(some-> (get-in req [:params "key"]) catalog/activate)
                                               #(view (current target) req))
                                     (cross-origin-refusal)))}]
         ;; writing the active KB out.  A write to the *filesystem* rather than to a KB,
         ;; so it does not go through `writing` — a load fills some other KB and is no
         ;; reason to refuse this one; what an export cannot survive is the KB it is
         ;; walking being written.  `export-entry!` refuses to start while a loader
         ;; writes, `write-refusal`'s exporting arm refuses writes while the walk runs,
         ;; and the wrapper handed in below drains a synchronous write already past that
         ;; refusal before the walk starts (`after-writes-drain`) — a barrier rather than
         ;; the exclusion `writing-job` gives a chain, since the walk writes no KB and
         ;; holding the monitor across it would park every `/kbs/unload` behind the dump.
         ["/kbs/export"        {:post (fn [req]
                                        (if (same-origin? req)
                                          (kbs-post #(catalog/export-entry!
                                                      (catalog/active)
                                                      (get-in req [:params "dir"])
                                                      (assoc (export-opts (:params req))
                                                             :run-in after-writes-drain))
                                                    #(view (current target) req))
                                          (cross-origin-refusal)))}]
         ["/kbs/export/cancel" {:post (fn [req]
                                        (if (same-origin? req)
                                          (kbs-post catalog/cancel-export!
                                                    #(view (current target) req))
                                          (cross-origin-refusal)))}]
         ["/kbs/export/rows"   {:get (fn [_] (frag (export-panel)))}]
         ["/vaelii.css" {:get (fn [_]
                                {:status  200
                                 :headers {"Content-Type"  "text/css; charset=utf-8"
                                           "Cache-Control" static-cache-control}
                                 :body    (stylesheet)})}]
         ["/term"       {:get (fn [req]
                                (let [q (get-in req [:query-params "q"])
                                      w (view (current target) req)]
                                  (cond
                                    (str/blank? q)
                                    (render w "term" [:p "Pass ?q=<term>"])
                                    (some? (->form q))
                                    (term-page w (->form q))
                                    :else
                                    (render w "term"
                                            [:h2 "Term"]
                                            [:p.muted "Not a readable term: " [:code q] "."]))))}]
         ;; the continuation routes: a capped list ends in a sentinel that fetches its
         ;; next page from here, so every long list is walkable without loading it whole
         ["/term/rows"  {:get (fn [req]
                                (let [q (->form (get-in req [:query-params "q"]))
                                      g (->long (get-in req [:query-params "g"]))]
                                  (if (and (some? q) (some? g))
                                    (term-rows-page (view (current target) req) q g
                                                    (->offset (get-in req [:query-params "offset"])))
                                    (frag ""))))}]
         ["/find"       {:get (fn [req]
                                (find-page (view (current target) req)
                                           (or (get-in req [:query-params "q"]) "")))}]
         ["/find/rows"  {:get (fn [req]
                                (find-rows-page (view (current target) req)
                                                (or (get-in req [:query-params "q"]) "")
                                                (->offset (get-in req [:query-params "offset"]))))}]
         ;; one level of a hierarchy, fetched when its node is opened.  `rel` is one of
         ;; the two transitivity relations and nothing else — it reaches the index as a
         ;; functor, so it is checked rather than trusted.
         ["/tree/rows"  {:get (fn [req]
                                (let [rel  (->form (get-in req [:query-params "rel"]))
                                      node (->form (get-in req [:query-params "node"]))]
                                  (if (and (subsumption-relations rel) (symbol? node))
                                    (tree-rows-page (view (current target) req) rel node
                                                    (->offset (get-in req [:query-params "offset"])))
                                    (frag ""))))}]
         ["/front/rows" {:get (fn [req]
                                (front-rows-page (view (current target) req)
                                                 (get-in req [:query-params "section"])
                                                 (->offset (get-in req [:query-params "offset"]))))}]
         ["/stats/rows" {:get (fn [req]
                                (stats-rows-page (view (current target) req)
                                                 (get-in req [:query-params "section"])
                                                 (->offset (get-in req [:query-params "offset"]))))}]
         ;; the one page whose context box can send a value the engine refuses: the levels
         ;; and the plan read through doors that do not resolve a query context, so
         ;; `CxEverything` typed into that box would leave `:unsupported-context` for Jetty
         ;; to answer as a 500.  Checked before the read, in the shape `bad-parameter`
         ;; answers a `?d=` that does not parse
         ["/levels"     {:get (fn [req]
                                (let [q   (get-in req [:query-params "q"])
                                      ctx (or (when-let [c (get-in req [:query-params "ctx"])]
                                                (when (seq c) (->form c)))
                                              '?ctx)]
                                  (if (nm/query-context? ctx)
                                    (unsupported-context (view (current target) req) ctx)
                                    (levels-page (view (current target) req)
                                                 (when (seq q) (->form q))
                                                 ctx))))}]
         ["/network"    {:get (fn [req]
                                (let [ctx   (get-in req [:query-params "ctx"])
                                      calc  (get-in req [:query-params "calc"])
                                      known (into #{} (map :calculus) (v/calculi))]
                                  (if (and (seq calc) (not (known (keyword calc))))
                                    ;; checked rather than fallen back from: the fallback
                                    ;; below picks the first calculus with a populated
                                    ;; network, and reaching it on a name no algebra
                                    ;; answers to draws a *different* matrix with nothing
                                    ;; on the page to say it is not the one asked for
                                    (bad-parameter (view (current target) req) "calc" calc
                                                   (str "one of "
                                                        (str/join ", " (sort (map name known)))))
                                    (network-page (view (current target) req)
                                                  (when (seq ctx) (->form ctx))
                                                  (when (seq calc) (keyword calc))))))}]
         ;; the same refusal, since the continuation reads through the same doors.  A 400
         ;; rather than the empty fragment an unreadable goal gets: htmx swaps only a 2xx,
         ;; so the reader keeps the list they were scrolling instead of watching it blank
         ["/levels/rows" {:get (fn [req]
                                 (let [q   (->form (get-in req [:query-params "q"]))
                                       ctx (or (->form (get-in req [:query-params "ctx"])) '?ctx)
                                       lvl (->long (get-in req [:query-params "level"]))]
                                   (cond
                                     (nm/query-context? ctx)
                                     (unsupported-context (view (current target) req) ctx)

                                     (and (sequential? q) (some? lvl))
                                     (levels-rows-page (view (current target) req) q ctx lvl
                                                       (->offset (get-in req [:query-params "offset"])))

                                     :else (frag ""))))}]
         ["/inference"  {:get (fn [req]
                                (let [q   (get-in req [:query-params "q"])
                                      ctx (get-in req [:query-params "ctx"])
                                      raw (get-in req [:query-params "d"])
                                      d   (param-long raw 1 debug-depth-max)]
                                  (if (= unreadable d)
                                    (bad-parameter (view (current target) req) "d" raw
                                                   (str "a depth bound from 1 to "
                                                        debug-depth-max ", the range the "
                                                        "form on this page offers"))
                                    (inference-page (view (current target) req)
                                                    (when (seq q) (->form q))
                                                    (or (when (seq ctx) (->form ctx)) '?ctx)
                                                    (or d debug-depth-default)))))}]
         ["/sentex/:id" {:get (fn [req] (sentex-page (view (current target) req)
                                                     (->long (get-in req [:path-params :id]))))}]
         ["/why/:id"    {:get (fn [req] (why-page (view (current target) req)
                                                  (->long (get-in req [:path-params :id]))))}]
         ["/justification/:id" {:get (fn [req] (justification-page (view (current target) req)
                                                                   (->long (get-in req [:path-params :id]))))}]
         ;; the editor: GET renders the textarea for the selected handles, POST applies
         ;; the save (both htmx fragments swapped into #editor).  POST is the one route
         ;; that writes, so it is the one that checks the caller's origin.
         ["/edit" {:get  (fn [req]
                           (let [hs (parse-handles (get-in req [:params "handles"]))]
                             (if (seq hs) (frag (edit-panel (view (current target) req) hs)) (frag ""))))
                   :post (fn [req]
                           (writing target req
                                    (fn [kb]
                                      (edit-post (view kb req)
                                                 (get-in req [:params "handles"])
                                                 (get-in req [:params "text"])))))}]
         ;; the way in for knowledge the KB does not hold: GET renders the form (with
         ;; `?q=` seeding it from a term page), POST checks every line and, only if all
         ;; of them pass, applies them in one `edit`
         ["/assert" {:get  (fn [req]
                             (let [q   (get-in req [:query-params "q"])
                                   ctx (get-in req [:query-params "ctx"])
                                   vw  (view (current target) req)]
                               (assert-page vw
                                            (cond-> (assert-seed vw (when (seq q) (->form q)))
                                              (seq ctx) (assoc :ctx ctx))
                                            nil)))
                     :post (fn [req]
                             (let [raw (get-in req [:params "strength"])
                                   s   (param-strength raw)]
                               (if (= unreadable s)
                                 (bad-parameter (view (current target) req) "strength" raw
                                                (str "one of "
                                                     (str/join ", " (sort (map name strength/assertable)))
                                                     " — the classes an assertion may carry"))
                                 (writing target req
                                          (fn [kb]
                                            (assert-post (view kb req)
                                                         {:text       (get-in req [:params "text"])
                                                          :ctx        (get-in req [:params "ctx"])
                                                          :monotonic? (= :monotonic s)}))))))}]
         ;; the non-monotonicity walkthrough: GET renders where the reader's sandbox
         ;; stands, POST runs one step.  Every step writes, so every step is a POST and
         ;; origin-checked; the answer is rendered from a view taken *after* the write,
         ;; since step 1 is the request that creates the sandbox
         ["/demo" {:get  (fn [req]
                           (demo-page (view (current target) req)
                                      (->long (get-in req [:params "first"]))))
                   :post (fn [req]
                           (writing target req
                                    (fn [kb]
                                      (let [f (demo-apply kb (:sandbox (view kb req))
                                                          (get-in req [:params "do"])
                                                          (->long (get-in req [:params "first"])))]
                                        (demo-page (view kb req) f)))))}]
         ;; the worked examples: GET computes every read-only card from the live KB, POST
         ;; establishes one example's premises in the reader's sandbox.  Same split as
         ;; `/demo` and for the same reason — the page has to be built from a view taken
         ;; after the write, since the first run is what creates the sandbox
         ["/reasoning" {:get  (fn [req] (reasoning-page (view (current target) req)))
                        :post (fn [req]
                                (writing target req
                                         (fn [kb]
                                           (reasoning-run kb (:sandbox (view kb req))
                                                          (get-in req [:params "id"]))
                                           (reasoning-page (view kb req)))))}]
         ;; discarding a sandbox: the one control that destroys knowledge on purpose, so
         ;; POST-only and origin-checked like every other write, and answering with the
         ;; page it emptied
         ["/sandbox/reset" {:post (fn [req]
                                    (writing target req
                                             (fn [kb]
                                               (let [w (view kb req)
                                                     r (sandbox/reset! kb (:sandbox w))]
                                                 (assert-page (view kb req)
                                                              {:problems (sandbox-note r)} nil)))))}]
         ;; the proposal panel: GET renders it (asking no model), POST runs one turn and
         ;; swaps its answer in.  The turn writes nothing — but it is a POST because it
         ;; *spends* something (a model, and on a local host a GPU), and it is
         ;; origin-checked for the same reason every other POST here is: a page on
         ;; another site must not be able to make this browser's KB do work.
         ["/propose" {:get  (fn [req]
                              (let [q   (->form (get-in req [:params "q"]))
                                    ctx (->form (get-in req [:params "ctx"]))
                                    kb  (current target)]
                                (if (symbol? q)
                                  (frag (propose-panel (view kb req) q ctx
                                                       {:remote? (nil? (v/local-kb kb))}))
                                  (frag ""))))
                      :post (fn [req]
                              (if (same-origin? req)
                                (let [q   (->form (get-in req [:params "q"]))
                                      ctx (->form (get-in req [:params "ctx"]))]
                                  (if (symbol? q)
                                    (let [vw (view (current target) req)]
                                      (propose-post vw q ctx
                                                    (get-in req [:params "message"])
                                                    (level-of vw (get-in req [:params "level"]) ctx)))
                                    (frag [:p.muted "No term to propose about."])))
                                (cross-origin-refusal)))}]
         ;; one row, re-rendered on the shape the reader picked.  A read (it re-checks a
         ;; sentence and writes nothing) but a POST, since it is the row's own form
         ;; posting itself back; origin-checked like its siblings.
         ["/propose/line" {:post (fn [req]
                                   (if (same-origin? req)
                                     (let [from (->form (get-in req [:params "from"]))
                                           ctx  (->form (get-in req [:params "ctx"]))
                                           i    (->long (get-in req [:params "i"]))
                                           n    (->long (get-in req [:params "n"]))]
                                       (if (and (some? from) (symbol? ctx))
                                         (let [vw (view (current target) req)]
                                           (propose-line-post
                                            vw from ctx i n
                                            (level-of vw (get-in req [:params "at-level"]) ctx)))
                                         (frag "")))
                                     (cross-origin-refusal)))}]
         ;; the same proposal at another density.  A read that writes nothing, POSTed
         ;; because it is the list's own form posting itself back with its originals —
         ;; which is what lets it re-render without asking the model a second time.
         ["/propose/level" {:post (fn [req]
                                    (if (same-origin? req)
                                      (let [vw    (view (current target) req)
                                            froms (map ->form (->seq (get-in req [:params "from"])))
                                            ctxs  (map ->form (->seq (get-in req [:params "ctx"])))
                                            lvl   (level-of vw (get-in req [:params "level"]) nil)]
                                        ;; the sibling's guard, over a list: a sentence
                                        ;; that does not read and a context that is not a
                                        ;; symbol are refused here rather than reviewed.
                                        ;; The counts are checked too, because the two
                                        ;; fields are zipped — a list posted with fewer
                                        ;; contexts than sentences would re-render the
                                        ;; shorter of them and drop the rest silently,
                                        ;; which reads as a proposal that lost lines
                                        (if (and (= (count froms) (count ctxs))
                                                 (every? some? froms)
                                                 (every? symbol? ctxs))
                                          (propose-level-post vw froms ctxs lvl)
                                          (frag "")))
                                      (cross-origin-refusal)))}]
         ;; what accepting would do, before it is done.  `v/preview` hands the KB back at
         ;; the same handles, but it gets there by really asserting and rolling back — so
         ;; it is a writer for the duration and goes through `writing` like the apply it
         ;; previews, not merely origin-checked.
         ["/propose/preview" {:post (fn [req]
                                      (writing target req
                                               (fn [kb]
                                                 (propose-preview-post (view kb req)
                                                                       (get-in req [:params "line"])))))}]
         ;; the panel's one write: the accepted lines, checked whole and applied in one
         ;; settle through the same `edit` every other write here goes through
         ["/propose/apply" {:post (fn [req]
                                    (writing target req
                                             (fn [kb]
                                               (propose-apply-post (view kb req)
                                                                   (get-in req [:params "line"])))))}]
         ;; retraction: GET only **previews** the teardown (it writes nothing, so it is
         ;; safe to reach by navigation); the POST is the destructive half, and goes
         ;; through `writing` like every other write
         ["/retract" {:get  (fn [req]
                              (let [hs (parse-handles (get-in req [:params "handles"]))]
                                (if (seq hs) (frag (retract-panel (view (current target) req) hs)) (frag ""))))
                      :post (fn [req]
                              (writing target req
                                       (fn [kb]
                                         (retract-post (view kb req)
                                                       (get-in req [:params "handles"])))))}]])
       ;; static assets (the fonts, the logo, vendored htmx, the favicons) live under
       ;; resources/public and fall through to here — anything the router did not match.
       (ring/routes
        (cached (ring/create-resource-handler {:path "/" :root "public"}))
        (ring/create-default-handler)))
      wrap-params
      ;; Outside `wrap-params`, so it runs first: that middleware slurps a form body
      ;; itself and has no ceiling, and this server authenticates nobody — an anonymous
      ;; caller streaming a body is heap it would otherwise spend.  The daemon holds the
      ;; same limit from the same variable (`guard/max-body-bytes`).
      (guard/wrap-body-limit body-too-large-refusal)
      ;; every request carries a session token, minted into a cookie the first time.  It
      ;; only *names* a sandbox — nothing is created until something is written there.
      sandbox/wrap-session))

(defn- with-host
  "Wrap a built handler in the `Host` allowlist for the interface it is bound to.

  It wraps **every** route rather than only the writes.  `same-origin?` guards a
  cross-site POST, but it folds under DNS rebinding — where the attacker's page is
  genuinely same-origin with this one — and a rebound page reads the KB as happily as
  it writes to it.  Reading it is what an attacker came for."
  [h host]
  (guard/wrap-host-allowed
   h
   (guard/allowed-hosts host)
   (fn [_] {:status  400
            :headers {"Content-Type" "text/plain; charset=utf-8"}
            :body    "unrecognized Host header"})))

(defn handler
  "What the browser actually serves: `app` behind the `Host` allowlist."
  ([target] (handler target {}))
  ([target {:keys [host] :or {host loopback}}]
   (with-host (app target) host)))

(defn- reloading-handler
  "The handler a REPL session serves: what `app` answers, rebuilt whenever the **var**
  `app` changes and reused whenever it does not.

  A ring handler is a value, and Jetty holds the one it was started with — so
  `(require 'vaelii.impl.web :reload)` would redefine every var on this page and change
  nothing about what is served, which is the failure mode that looks like the reload
  silently not working.  Reading `#'app` per request is what closes it: a reload gives
  the var a new function object, the identity check misses once, the routes are rebuilt
  from the reloaded namespace, and every request after that is the new code.  A
  namespace this one merely *calls* needs no help at all — those calls already go
  through vars, so reloading `vaelii.impl.svg` takes effect on the next request with
  nothing rebuilt.

  `start` uses it only when asked.  A handler that re-resolves a var per request is
  paying, forever, for a reload that a served process will never do."
  [target]
  (let [built (atom nil)]                                   ; [the app fn, the handler it made]
    (fn [req]
      (let [f @#'app]
        (when-not (identical? f (first @built))
          (reset! built [f (f target)]))
        ((second @built) req)))))

(defn- hot-reloading
  "Wrap a dev handler so editing a source file under `src` shows on the next request with
  no REPL and no restart: ring/ring-devel's `wrap-reload` reloads the changed namespaces
  from disk, and `reloading-handler`'s per-request `#'app` read then serves the rebuilt
  routes.  Resolved lazily — ring-devel ships in the `:dev`/`:repl` profiles only, never in
  the standalone jar, exactly like the profiler.

  Absent — a served/uberjar classpath with `VAELII_DEV` set — the `requiring-resolve`
  throws `FileNotFoundException`.  A hot-reload switch that read as set and killed the
  start would be the very failure the `config` namespace exists to prevent (as
  `start-profiler` avoids for its own dependency), so it degrades to `h` and logs the
  reason: `reloading-handler` needs no ring-devel of its own — it re-reads `#'app` — so
  live routes survive, and only `wrap-reload`'s file-watching is lost."
  [h]
  (try ((requiring-resolve 'ring.middleware.reload/wrap-reload) h {:dirs ["src"]})
       (catch Throwable t
         (trove/log! {:level :warn :id ::hot-reload
                      :msg (str "VAELII_DEV is set but ring-devel is not on the classpath — "
                                "serving without hot reload (it ships in the :dev/:repl "
                                "profiles, which `lein browser` activates and a served jar "
                                "does not): " (.getMessage t))})
         h)))

(defn start
  "Start a Jetty server for `target` (a KB, an access value, or a catalog holder).
  Returns the server (non-blocking).  `:host` defaults to loopback; pass an address
  (`\"0.0.0.0\"`) to bind publicly.  `:reload?` serves through `reloading-handler`, so a
  namespace reload reaches the running server — what `lein browser` starts with."
  [target {:keys [port host reload?] :or {port 3000 host loopback}}]
  (jetty/run-jetty (with-host (if reload? (hot-reloading (reloading-handler target)) (app target)) host)
                   {:port port :host host :join? false}))

(defn warm-model
  "Ask the configured backend to make itself ready, on a thread of its own.

  Measured: the latency of a local turn is model **load**, not generation — three
  identical page turns took 11.33 s, then 0.39 s, then 0.30 s.  Warming at start moves
  that eleven seconds off the first reader's question.  It is fire-and-forget by
  construction: it must not delay the server coming up, and a host that is down is the
  ordinary case (`provider/warm` answers nil and the panel falls back to the stub)."
  []
  (let [kind (or (llm-provider/configured) :stub)]
    (when (not= :stub kind)
      (doto (Thread.
             (fn []
               (let [r (llm-provider/warm kind)]
                 (trove/log! {:level :info :id ::warm
                              :msg (str "llm backend " (name kind)
                                        (if (:loaded? r) " warmed" " not reachable"))
                              :data (assoc r :kind kind)})))
             "vaelii-llm-warm")
        (.setDaemon true)
        (.start)))))

(defn fresh-starter-kb!
  "A KB freshly loaded with the starter ontology.  Flushes the record + index
  stores first, so a repeated run (or one over data from an earlier code version)
  starts from a clean, deterministic state rather than re-asserting over stale
  handles.  For a persistent KB, construct one and call `core/recover` instead."
  ([] (fresh-starter-kb! {}))
  ([opts]
   ;; :recover? false — the stores are cleared on the next two lines, so the
   ;; unrecovered-store warning would fire about data this fn exists to discard
   (let [kb (v/open-kb (merge {:recover? false} opts))]
     (v/clear! kb)                                        ; empty the stores before reloading
     (starter/load-into kb)
     kb)))

(defn- opening-kb
  "The KB the browser opens on, **registered with the catalog** and made active: the
  starter it starts with is not a special case, it is entry number one.  `attach` (a
  `[host port]`) points it at a running daemon instead.

  Answers `{:kb :entry :target}`, and the `:target` is the catalog **holder** rather than
  the KB — the browser reads whichever entry is active, so loading another one in the UI
  and switching to it re-points every page with no restart.  Shared by `-main` and
  `dev-repl` so the two cannot open on different things."
  [attach]
  (let [kb    (if attach (apply v/remote attach) (fresh-starter-kb!))
        entry (if attach
                (catalog/register! "daemon" (str "Daemon " (first attach) ":" (second attach)) kb)
                (catalog/register! "starter" "Starter ontology" kb
                                   {:source (catalog/source "starter")}))]
    {:kb kb :entry entry :target (catalog/holder kb)}))

(defn- default-port
  "The port to bind when nothing on the command line names one: `VAELII_WEB_PORT`, else
  the `vaelii.web.port` system property, else 3000.  Read by `-main` and `dev-repl`
  alike, so the variable means the same thing to `lein run -m vaelii.impl.web` as it does
  to `lein browser` — a variable that moved the page for one and was ignored by the other
  is one that reads as set and lands on 3000 anyway.

  The property is the same env-then-property shape `vaelii.kb.path` uses
  (docs/catalog.md), and for the same reason: a JVM cannot change its own environment,
  so it is what a test sets.

  An unparseable value falls through to the next source rather than failing startup — a
  typo in a convenience variable should not be the thing that stops the browser coming
  up."
  []
  (let [num (fn [s] (try (some-> s Long/parseLong int)
                         (catch NumberFormatException _ nil)))]
    (or (num (System/getenv "VAELII_WEB_PORT"))
        (num (System/getProperty "vaelii.web.port"))
        3000)))

(defn- parse-args
  "`-main`'s options, in any order:

    --listen HOST            interface to bind (default loopback)
    --port N                 web port (default VAELII_WEB_PORT, else 3000)
    --attach HOST PORT [WEBPORT]   read a running daemon instead of an in-process KB

  `--attach`'s third argument is optional and positional, so it is taken only when it
  is a bare number — otherwise it is the next flag.

  A flag missing its value, a non-numeric number, or a token this table does not know
  is refused (`:unknown-option`).  The stakes are not symmetric with a mere typo: a
  truncated `--listen` read as a nil host would bind **every** interface with the Host
  allowlist off — Jetty treats a nil host as the wildcard address — on a server whose
  write routes nothing authenticates, while logging the public-bind warning as though
  the operator had asked for it."
  [args]
  (let [need (fn [flag v]
               (or v (throw (ex-info (str flag " needs a value and the line ends after it"
                                          " — write --listen <address>, --port <n>, or"
                                          " --attach <host> <port> [<webport>]")
                                     {:type :unknown-option :flag flag}))))
        num  (fn [flag v]
               (let [v (need flag v)]
                 (try (Integer/parseInt ^String v)
                      (catch NumberFormatException _
                        (throw (ex-info (str flag " wants a number, got " (pr-str v)
                                             " — write " flag " <n>")
                                        {:type :unknown-option :flag flag :value v}))))))]
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
                        {:type :unknown-option :flag a}))))))

;; ---- the browser, inside a REPL -----------------------------------------
;;
;; `lein browser` is `lein repl` with the browser already running: a prompt, a page, and
;; a **reload channel** — nREPL's, on loopback, so an editor or another process can
;; reload a namespace into the running server through `.nrepl-port`.  `lein run -m
;; vaelii.impl.web` gives no such channel: it starts no nREPL, and even attached to one
;; it serves a handler value Jetty already holds, which is why `start` takes `:reload?`.
;;
;; Both halves bind the **loopback interface**.  The browser has a write route and no
;; authentication, and an nREPL is arbitrary code execution by design — the pair on a
;; reachable interface is a remote shell.  Exposing the browser stays the deliberate
;; `--listen` on `-main`; the REPL is not exposable from here at all.

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

(defn dev-repl
  "Start the browser for a REPL session and hand the prompt straight back.

  What `lein browser` calls, and the only thing `project.clj` names.  Port from
  `VAELII_WEB_PORT`, else 3000 — the same read `-main` does; loopback only.  A port
  already in use is **reported, not thrown** — you asked for a REPL and you get one
  either way, which is the difference between a busy port being an inconvenience and
  being a failed startup."
  []
  (dev-stop)
  (let [port (default-port)
        {:keys [target]} (opening-kb nil)]
    (warm-model)
    ;; the profiler ships in the `:repl` profile, which is the one `lein browser`
    ;; activates — so this is the entry point where `VAELII_PROFILER` can actually find
    ;; the class, and the caches page links to whatever it started
    (start-profiler)
    (try
      (reset! dev-instance (start target {:port port :reload? true}))
      (println (str "\n  vaelii browser  http://" loopback ":" port
                    "  (loopback only)\n"
                    "  edit any source file and refresh — the change is served,"
                    " no restart\n"
                    "  stop it with    (vaelii.impl.web/dev-stop)\n"))
      (catch java.io.IOException e
        (println (str "\n  the browser did not start on " loopback ":" port
                      " — " (ex-message e) "\n"
                      "  the REPL is yours regardless; retry with"
                      " (vaelii.impl.web/dev-repl) on a free port"
                      " (VAELII_WEB_PORT).\n"))
        nil))))

(defn -main
  "Serve the browser.

    lein run -m vaelii.impl.web                            ; a fresh starter-loaded in-process KB
    lein run -m vaelii.impl.web --port 8080
    lein run -m vaelii.impl.web --listen 0.0.0.0           ; reachable off-machine (opt-in)
    lein run -m vaelii.impl.web --attach HOST PORT [WEBPORT]

  `--attach` points the browser at a running daemon (`vaelii.impl.serve`) and renders
  the KB it owns *over the API* — the way to inspect a live daemon whose single-writer
  lock forbids opening its store directly (docs/operations.md).  Every page reads the
  same, since `app` is written against the access facade (`v`), which dispatches each
  read to the local KB or the remote daemon.

  The KB it reads and the interface it binds are independent axes: `--listen` says who
  may reach the browser, `--attach` says whose KB it shows.  The default is loopback,
  and what it binds decides what it requires — the daemon's rule, on the daemon's
  reasoning (`guard/require-token!`):

  - `--listen` names a **non-loopback** address ⇒ `VAELII_API_TOKEN` is **required**,
    and every request then presents it as `Authorization: Bearer <token>`.  Without one
    it is a line on stderr and exit **2**, a code of its own so a supervisor tells a
    missing credential from the configuration typos above.
  - **Loopback** — the default, and `--listen 127.0.0.1` said out loud — is unchanged:
    no token, no header, no 401.

  Whichever KB it starts on is **registered with the catalog** and made active, so it
  appears in `/kbs` beside the ones that can be loaded — the starter it opens with is not
  a special case, it is entry number one."
  [& args]
  (let [{:keys [host port attach]} (try (parse-args args)
                                        (catch clojure.lang.ExceptionInfo e
                                          (binding [*out* *err*] (println (ex-message e)))
                                          (System/exit 1)))
        token (guard/api-token)
        ;; before the KB is opened, which takes a directory's single-writer lock: a
        ;; server that is going to refuse to serve must not first take a lock off the
        ;; process that could have.  The daemon orders it the same way, for the same
        ;; reason (`vaelii.impl.serve`).
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
                                ;; `--listen localhost` reads as the loopback bind it is
                                :exposed? (guard/public-bind? host)
                                :kb-search-path (catalog/search-path)}
                         (not attach) (assoc :record-store (type (:records kb))
                                             :index-store  (type (:index kb))))})
    ;; said out loud, as the daemon says it: a public bind reaches write routes — two of
    ;; which (/kbs/export, /kbs/load) write the host filesystem at a path the request
    ;; names — over a plaintext wire, and it drops the Host allowlist unless
    ;; `VAELII_ALLOWED_HOSTS` names one.  The token this start required is what stands
    ;; in front of the routes; it is not TLS and it is not a Host allowlist, so the line
    ;; names what it still does not cover.
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
    ;; the proposal panel's model, loaded while the reader is still finding a term page
    (warm-model)
    ;; the same call `dev-repl` makes, so the variable means one thing to both entry
    ;; points.  Here the class is normally absent — it ships in the `:repl` profile — and
    ;; `start-profiler` says so in the log rather than failing the start
    (start-profiler)
    ;; a development server (`VAELII_DEV`) serves through the hot-reload path — an edit to
    ;; any source file shows on the next refresh with no restart; a plain served process
    ;; pays nothing for a reload it will never do, so it keeps the static handler.
    (let [served (if (config/web-dev?)
                   (hot-reloading (reloading-handler target))
                   (app target))]
      (jetty/run-jetty (with-token (with-host served host) host token)
                       {:port port :host host :join? true}))))
