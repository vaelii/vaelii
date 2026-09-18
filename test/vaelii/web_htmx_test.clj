;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.web-htmx-test
  "htmx's **inheritance**, checked over the markup we actually render.

  Most htmx attributes are resolved by walking *up* the DOM until one is found, so an
  attribute put on `<body>` for one purpose reaches every request on the page, and one
  put on a form reaches every request inside it.  That is what makes `hx-boost` on the
  body work at all — and it is a trap with the same reach: an attribute set for the
  element that needs it silently changes the behaviour of every request underneath.

  So this is a lint rather than a feature test.  It rebuilds htmx's own resolution — the
  inherited set below, `hx-disinherit`, and `unset` — over each page's rendered HTML, and
  asks of every request site what it *effectively* carries.  A fragment is checked under
  the ancestors it swaps into, since that is where htmx resolves it.

  Kept honest against the vendored `resources/public/htmx.min.js` (2.0.9): the inherited
  set is the attributes it reads through `getClosestAttributeValue`."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.catalog :as catalog]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.host.llm.stub :as stub]
            [vaelii.test-util :as tu]))

(def ^:dynamic *app* nil)

(use-fixtures :once
  (fn [f]
    (let [kb (tu/load-starter! (tu/fresh))]
      (binding [tu/*kb* kb, *app* (web/app kb)] (f))
      (tu/clear-kb! kb))))
(use-fixtures :each (tu/neutral))

(defn- GET [uri & [qs]]
  (*app* (cond-> {:request-method :get :uri uri} qs (assoc :query-string qs))))

;; ---- htmx's resolution, rebuilt ----------------------------------------

(def ^:private inherited
  "The attributes htmx resolves by walking up the DOM, so an ancestor's value reaches
  every request below it.  Everything else — the verbs, `hx-trigger`, `hx-swap-oob`,
  `hx-vals` — is read off the element itself."
  #{"hx-boost" "hx-confirm" "hx-encoding" "hx-params" "hx-prompt" "hx-push-url"
    "hx-replace-url" "hx-select" "hx-select-oob" "hx-swap" "hx-sync" "hx-target"
    "hx-indicator" "hx-disabled-elt" "hx-include"})

(def ^:private verbs ["hx-get" "hx-post" "hx-put" "hx-patch" "hx-delete"])

(def ^:private void-tags
  #{"area" "base" "br" "col" "embed" "hr" "img" "input" "link" "meta" "param" "source"
    "track" "wbr"})

(defn- scannable
  "Comments, the doctype and script bodies out of the way: a `<` inside JavaScript is not
  a tag, and the pre-paint theme script is inline."
  [html]
  (-> html
      (str/replace #"(?s)<!--.*?-->" "")
      (str/replace #"(?s)<script\b[^>]*>.*?</script>" "")
      (str/replace #"(?si)<!doctype[^>]*>" "")))

(defn- unescape
  "An attribute value as the DOM would hold it — htmx matches on the parsed value, so a
  selector written `find button[type='submit']` must read back that way and not as the
  `&apos;` the serializer wrote."
  [s]
  (-> s (str/replace "&apos;" "'") (str/replace "&quot;" "\"")
      (str/replace "&lt;" "<") (str/replace "&gt;" ">") (str/replace "&amp;" "&")))

(defn- attrs-of [s]
  (into {} (for [[_ k vl] (re-seq #"([a-zA-Z][\w:.-]*)=\"([^\"]*)\"" s)] [k (unescape vl)])))

(def ^:private element-re
  "A start or end tag.  Attribute values may hold `>`, so they are matched as quoted runs."
  #"<(/?)([a-zA-Z][\w-]*)((?:\"[^\"]*\"|[^>\"])*)>")

(defn- elements
  "Every start tag as `{:tag :own}`, ancestors ignored — for the checks that are about
  one element rather than what it inherits."
  [html]
  (for [[_ close tag raw] (re-seq element-re (scannable html)) :when (empty? close)]
    {:tag (str/lower-case tag) :own (attrs-of raw)}))

(defn- visible-below
  "What an element's children inherit from it: its own attributes, minus whatever its
  `hx-disinherit` withholds — which blocks its own value *and* anything above it."
  [acc own]
  (let [dis (some-> (get own "hx-disinherit") (str/split #"\s+") set)]
    (cond-> (merge acc (select-keys own inherited))
      dis (as-> m (if (dis "*") (apply dissoc m inherited) (apply dissoc m dis))))))

(defn- sites
  "Every request-issuing element in `html`, as `{:tag :own :eff :trigger}` — `eff` the
  attributes htmx would resolve for it, `unset` read as absent.  `seed` is what the
  markup hangs under (empty for a whole document, the ancestors of the target for a
  fragment).  A tolerant scan with a tag stack, which is enough for markup we generated."
  [html & [seed]]
  (let [tags (re-seq element-re (scannable html))]
    (loop [[[_ close tag raw] & more] tags, stack [(or seed {})], out []]
      (if-not tag
        out
        (let [tag (str/lower-case tag)]
          (if (seq close)
            (recur more (cond-> stack (> (count stack) 1) pop) out)
            (let [own  (attrs-of raw)
                  eff  (->> (merge (peek stack) (select-keys own inherited))
                            (remove (comp #{"unset"} val))
                            (into {}))
                  verb (some #(when (own %) %) verbs)
                  out  (cond-> out
                         verb (conj {:tag tag :verb verb :own own :eff eff
                                     :trigger (get own "hx-trigger" "")}))]
              (recur more
                     (cond-> stack
                       (not (or (void-tags tag) (str/ends-with? raw "/")))
                       (conj (visible-below (peek stack) own)))
                     out))))))))

(defn- under
  "What a fragment swapped into `#id` inherits: the attributes visible at that element in
  a whole document.  A fragment's behaviour is decided by where it lands, not by what the
  server sent."
  [html id]
  (let [tags (re-seq element-re (scannable html))]
    (loop [[[_ close tag raw] & more] tags, stack [{}]]
      (cond
        (nil? tag) nil
        (seq close) (recur more (cond-> stack (> (count stack) 1) pop))
        :else (let [own (attrs-of raw)]
                (if (= id (get own "id"))
                  (visible-below (peek stack) own)
                  (recur more
                         (cond-> stack
                           (not (or (void-tags (str/lower-case tag))
                                    (str/ends-with? raw "/")))
                           (conj (visible-below (peek stack) own))))))))))

(defn- describe [{:keys [tag own verb]}]
  (str "<" tag (when-let [i (own "id")] (str " id=" i))
       (when-let [c (own "class")] (str " class=" c))
       " " verb "=" (own verb) ">"))

;; ---- the rules ---------------------------------------------------------

(defn- complaints
  "Every way a request site's *inherited* attributes are wrong for it.  Each rule is one
  we have actually been bitten by."
  [site]
  (let [{:keys [own eff trigger]} site
        inherits? (fn [k] (and (eff k) (not (own k))))]
    (cond-> []
      ;; the body says a boosted navigation lands at the top of the document.  A swap
      ;; *inside* a page is not a navigation and must leave the scroll where it is.
      (and (inherits? "hx-swap") (str/includes? (eff "hx-swap") "show:"))
      (conj (str "inherits a page-moving swap: " (eff "hx-swap")))

      ;; the body selects #main out of every navigation's answer.  A response that is not
      ;; a page has no #main, so an inherited select would swap nothing at all.
      (and (not= "#main" (eff "hx-target")) (= "#main" (eff "hx-select")))
      (conj (str "selects #main out of a response targeted at " (eff "hx-target")))

      ;; the body points every request at the page indicator.  A poll is not a request
      ;; the reader made, and sweeping the bar every second says the page is loading.
      (and (str/includes? trigger "every ") (inherits? "hx-indicator"))
      (conj (str "polls (" trigger ") on the inherited indicator " (eff "hx-indicator")))

      ;; `find`/`closest` resolve from the *requesting* element, so a selector inherited
      ;; from an ancestor is being resolved somewhere it was never written for.
      (some (fn [k] (and (inherits? k) (re-find #"^(find|closest) " (eff k))))
            ["hx-disabled-elt" "hx-include"])
      (conj (str "inherits a relative selector: "
                 (str/join ", " (for [k ["hx-disabled-elt" "hx-include"]
                                      :when (and (inherits? k)
                                                 (re-find #"^(find|closest) " (eff k)))]
                                  (str k "=" (eff k)))))))))

(defn- audit [label html & [seed]]
  (for [s (sites html seed), c (complaints s)]
    (str label " " (describe s) " " c)))

;; htmx addresses by id — a target, an out-of-band swap, an include.  Two elements
;; answering to one id is not an HTML nicety here: `#kb-label` resolves to whichever
;; comes first in the document, so a duplicate silently decides which one a swap lands
;; in.  And a target that is not on the page at all is a request whose answer goes
;; nowhere, which htmx reports only to the console.

(defn- ids-of [html]
  (keep #(get (:own %) "id") (elements html)))

(defn- id-problems [label html]
  (let [ids (ids-of html)
        dup (for [[id n] (frequencies ids) :when (> n 1)]
              (str label " duplicate id=" id " (" n " elements answer to it)"))
        present (set ids)]
    (concat dup
            (for [s     (sites html)
                  [k t] (select-keys (:eff s) ["hx-target" "hx-include" "hx-disabled-elt"])
                  :when (and (str/starts-with? t "#") (not (present (subs t 1))))]
              (str label " " (describe s) " " k "=" t " is on no element of the page")))))

;; ---- every page we serve ------------------------------------------------

(def ^:private pages
  [["/" nil] ["/stats" nil] ["/levels" "q=%28genl+dog+%3Fx%29"] ["/assert" nil]
   ["/demo" nil] ["/network" nil] ["/kbs" nil] ["/reasoning" nil]
   ["/term" "q=dog"] ["/find" "q=dog"]])

(deftest no-request-inherits-an-attribute-meant-for-something-else
  (let [found (mapcat (fn [[uri qs]] (audit uri (:body (GET uri qs)))) pages)]
    (is (empty? found) (str/join "\n" found))))

(deftest every-id-htmx-addresses-is-on-exactly-one-element
  (let [found (mapcat (fn [[uri qs]] (id-problems uri (:body (GET uri qs)))) pages)]
    (is (empty? found) (str/join "\n" found))))

(deftest the-out-of-band-header-label-rides-answers-and-not-documents
  ;; the entries panel refreshes the header's KB name out of band, because the header is
  ;; outside every region a swap replaces — but a document ships its own header
  (let [doc  (:body (GET "/kbs"))
        frag (:body (GET "/kbs/rows"))]
    (is (= 1 (count (filter #{"kb-label"} (ids-of doc)))) "one label in the document")
    (is (some #(and (= "kb-label" (get (:own %) "id")) (get (:own %) "hx-swap-oob"))
              (elements frag))
        "and the answer carries the swap")))

(deftest a-record-page-is-clean-too
  ;; the justification audit is pinned to a **derived** sentex, built here rather than
  ;; picked out of an enumeration: a premise carries no supporting justification, so a
  ;; backend whose enumeration led with one would leave this audit unrun — and unrun is
  ;; indistinguishable from clean, since it moves the assertion count by nothing
  (tu/with-terms [Rufus]
    (v/assert tu/*kb* (list 'living_thing Rufus) 'CxBiology)
    (let [stored         (:id (first (v/sort-by-content (juxt :sentence :context)
                                                        (v/sentexes-with-functor tu/*kb* 'genl))))
          [concl & more] (v/sentexes-matching tu/*kb* (list 'mortal Rufus) '?ctx)
          derived        (:id concl)
          j              (:id (first (v/supporting-justifications tu/*kb* derived)))]
      (is (nil? more) "one placement for the fresh individual, so the audit is pinned to it")
      (is (some? derived) "the shipped rule concluded, so there is a derived sentex to audit")
      (is (some? j) "and it rests on the justification the /justification page shows")
      (let [found (concat (audit "/sentex" (:body (GET (str "/sentex/" stored))))
                          (audit "/why" (:body (GET (str "/why/" stored))))
                          (audit "/sentex (derived)"
                                 (:body (GET (str "/sentex/" derived))))
                          (audit "/why (derived)" (:body (GET (str "/why/" derived))))
                          (audit "/justification"
                                 (:body (GET (str "/justification/" j)))))]
        (is (empty? found) (str/join "\n" found))))))

;; The panels that watch a running job only render their poll *while* one runs, so the
;; page a reader sees during a load is not the page a GET returns.  That is exactly where
;; the indicator was wrong, so the lint has to reach it.

(deftest a-page-watching-a-running-load-is-clean
  (with-redefs [catalog/active-caveat (fn [] {:name "corpus" :status :running
                                              :progress {:phase :records :done 5}})
                catalog/loading?      (constantly true)
                catalog/exporting?    (constantly true)]
    (let [found (mapcat (fn [[uri qs]] (audit (str uri " (loading)")
                                              (:body (GET uri qs))))
                        [["/" nil] ["/kbs" nil] ["/term" "q=dog"]])]
      (is (empty? found) (str/join "\n" found)))))

(deftest every-self-refreshing-panel-says-so-the-same-way
  ;; one helper renders all four, so they cannot drift apart
  (with-redefs [catalog/active-caveat (fn [] {:name "corpus" :status :running})
                catalog/loading?      (constantly true)
                catalog/exporting?    (constantly true)]
    (let [body  (:body (GET "/kbs"))
          polls (filter #(str/includes? (:trigger %) "every ") (sites body))]
      (is (= 4 (count polls)) "the caveat, the memory strip, the entries and the export")
      (doseq [p polls]
        (is (= "unset" (get (:own p) "hx-indicator")) (describe p))
        (is (= "this" (get (:own p) "hx-target")) (describe p))))))

;; A fragment inherits from wherever it lands, so the review form — which only exists
;; after a proposal — is checked under the term page's `#propose-result`.

(tu/deftest-kb the-proposal-review-form-is-clean-where-it-lands
  (let [t    (tu/tmp-type "quokka")
        ctx  (tu/tmp-ctx "Marsupial")
        _    (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse)
        _    (v/assert kb (list 'genl t 'animal) ctx)
        doc  (:body (GET "/term" (str "q=" t)))
        frag (binding [web/*proposer*
                       {:kind :stub
                        :provider (stub/provider
                                   {:script [{:assertions [(list 'genl t 'bird)]}]})}]
               (:body (*app* {:request-method :post :uri "/propose"
                              :params {"q" (pr-str t) "ctx" (pr-str ctx)
                                       "message" "what is it"}})))
        seed (under doc "propose-result")]
    (is (some? seed) "the term page has the region the answer swaps into")
    (is (re-find #"class=\"propose-apply\"" frag) "and the answer is a review form")
    (let [found (audit "/propose" frag seed)]
      (is (empty? found) (str/join "\n" found)))
    (testing "the form keeps the attribute it withholds from its children"
      (let [f (first (filter #(= "/propose/apply" (get (:own %) "hx-post"))
                             (sites frag seed)))]
        (is (= "find button[type='submit']" (get (:own f) "hx-disabled-elt")))))))

;; ---- the lint itself has to be wrong-detecting --------------------------

(deftest the-lint-catches-what-it-is-for
  (testing "an inherited indicator on a poll"
    (is (seq (audit "x" (str "<body hx-indicator=\"#page-indicator\">"
                             "<div hx-get=\"/p\" hx-trigger=\"every 2s\"></div></body>")))))
  (testing "an inherited page-moving swap"
    (is (seq (audit "x" "<body hx-swap=\"outerHTML show:window:top\"><b hx-get=\"/p\"></b></body>"))))
  (testing "an inherited #main select on a fragment target"
    (is (seq (audit "x" (str "<body hx-select=\"#main\" hx-target=\"#main\">"
                             "<b hx-get=\"/p\" hx-target=\"#side\"></b></body>")))))
  (testing "an inherited relative selector"
    (is (seq (audit "x" (str "<form hx-post=\"/a\" hx-disabled-elt=\"find button\">"
                             "<b hx-post=\"/b\"></b></form>")))))
  (testing "and clears each of them when the element says otherwise"
    (is (empty? (audit "x" (str "<body hx-indicator=\"#page-indicator\" hx-swap=\"outerHTML show:top\">"
                                "<div hx-get=\"/p\" hx-trigger=\"every 2s\""
                                " hx-indicator=\"unset\" hx-swap=\"outerHTML\"></div></body>"))))
    (is (empty? (audit "x" (str "<form hx-post=\"/a\" hx-disabled-elt=\"find button\""
                                " hx-disinherit=\"hx-disabled-elt\">"
                                "<b hx-post=\"/b\"></b></form>"))))))
