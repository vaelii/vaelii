;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.web-test
  "Exercises the web handlers as pure request -> response (no live server)."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.access :as acc]
            [vaelii.impl.catalog :as cat]
            [vaelii.impl.guard :as guard]
            [vaelii.impl.starter :as starter]
            [vaelii.impl.svg :as svg]
            [vaelii.impl.web :as web]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(def ^:dynamic *app* nil)

(use-fixtures :once
  (fn [f]
    (let [kb (tu/fresh)]
      (-> kb starter/load-into world/load-into)
      (binding [tu/*kb* kb, *app* (web/app kb)] (f))
      (tu/clear-kb! kb))))
(use-fixtures :each (tu/neutral))

(defn- GET [uri & [qs headers]]
  (*app* (cond-> {:request-method :get :uri uri}
           qs      (assoc :query-string qs)
           headers (assoc :headers headers))))

(def ^:private htmx {"hx-request" "true"})

(deftest default-page-shows-upper-ontology
  (let [r (GET "/")]
    (is (= 200 (:status r)))
    (testing "the type tree, contexts, predicates, and disjointness render"
      (is (re-find #"thing" (:body r)))
      (is (re-find #"animal" (:body r)))
      (is (re-find #"CoreContext" (:body r)))
      (is (re-find #"Core predicates" (:body r)))
      (is (re-find #"⊥" (:body r))))
    (testing "the header carries a menubar to the top-level tools"
      (is (re-find #"class=\"menubar\"" (:body r)))
      (is (re-find #">Ontology<" (:body r)))
      (is (re-find #">Query<" (:body r)))
      (is (re-find #"href=\"/stats\"" (:body r))))))

;; ---- the front page is bounded ------------------------------------------
;;
;; It is the first page anyone opens against a KB whose size they did not choose, and
;; the catalog will load an ontology with hundreds of thousands of genl edges.  So the
;; trees open a level at a time and every list is paged — and each of those is a claim
;; the tests have to hold, since a page that quietly renders everything looks identical
;; on the shipped schema and dies on a real one.

(defn- section
  "One `<h2>` section of a page, so an assertion about the type tree is not satisfied by
  a term that happens to appear in the disjointness list below it."
  [body heading]
  (let [i (str/index-of body heading)
        j (when i (str/index-of body "<h2>" (+ i (count heading))))]
    (when i (subs body i (or j (count body))))))

(deftest the-type-tree-opens-one-level-at-a-time
  (let [body (section (:body (GET "/")) "Types <span")]
    (testing "the stated root is on the page, open"
      (is (re-find #"<details open=\"open\"><summary><a[^>]*href=\"/term\?q=thing\"" body)))
    (testing "a node with subtypes is a disclosure that fetches its own children"
      ;; `physical_object` is a direct subtype of `thing`, so it is on the first level
      (is (re-find #"<details[^>]*hx-get=\"/tree/rows\?rel=genl&amp;node=physical_object" body)))
    (testing "and it selects nothing out of what it fetches"
      ;; `hx-select="#main"` is on the body and inherited; against a fragment of bare
      ;; rows it selects nothing, so an open would swap in nothing.  This is invisible
      ;; to a handler test — the swap is the client's — so the attribute is the assertion
      (is (re-find #"<details[^>]*hx-select=\"unset\"[^>]*hx-get=\"/tree/rows|<details[^>]*hx-get=\"/tree/rows[^>]*hx-select=\"unset\"" body)))
    (testing "and what is below it is not in the page until it is opened"
      ;; `animal` is under `physical_object` and `bird` under that — the eager tree
      ;; rendered the whole hierarchy, this one renders one level and a placeholder
      (is (not (re-find #"href=\"/term\?q=bird\"" body)))
      (is (re-find #"tree-kids" body) "the placeholder a fetch will replace"))))

(deftest tree-rows-answers-one-node-and-checks-its-relation
  (testing "a node's children come back as bare rows"
    (let [r (GET "/tree/rows" "rel=genl&node=animal")]
      (is (= 200 (:status r)))
      (is (re-find #"href=\"/term\?q=bird\"" (:body r)) "a direct subtype is there")
      (is (not (re-find #"<html" (:body r))) "a fragment, not a document")))
  (testing "the fetch reaches only that node — a grandchild is behind its own request"
    (let [b (:body (GET "/tree/rows" "rel=genl&node=animal"))]
      ;; `penguin` is under `bird`, which is under `animal`
      (is (not (re-find #"href=\"/term\?q=penguin\"" b)))
      (is (re-find #"hx-get=\"/tree/rows\?rel=genl&amp;node=bird" b)
          "the child carries the request that would reach it")))
  (testing "the context lattice reads through the same route"
    (is (= 200 (:status (GET "/tree/rows" "rel=genlContext&node=CoreContext")))))
  (testing "a relation that is not one of the two is refused, not looked up"
    ;; `rel` reaches the index as a functor, so it is checked rather than trusted
    (let [r (GET "/tree/rows" "rel=parentOf&node=Tom")]
      (is (= 200 (:status r)))
      (is (str/blank? (str/trim (:body r)))))))

(deftest a-capped-list-says-so-and-continues
  (let [body (:body (GET "/"))]
    (testing "the core-predicate list ends in a sentinel naming what is left"
      (is (re-find #"show \d+ more" body))
      (is (re-find #"/front/rows\?section=predicates&amp;offset=50" body)))
    (testing "the types heading reports the edge count it did not draw"
      (is (re-find #"\d+ genl edges" body))))
  (testing "the continuation returns the next page and nothing else"
    (let [r (GET "/front/rows" "section=predicates&offset=50")]
      (is (= 200 (:status r)))
      (is (not (re-find #"<html" (:body r))))
      (is (re-find #"<li>" (:body r)))))
  (testing "an unknown section is empty rather than an error"
    (is (str/blank? (str/trim (:body (GET "/front/rows" "section=nonsense&offset=0")))))))

(deftest the-front-page-survives-a-type-disjoint-from-itself
  ;; `wff` refuses `(disjoint A A)` outright, so nothing this KB's *own* assert path stored
  ;; can be one.  An **import** is the other way in: it stores re-canonicalized records
  ;; without re-running those checks, and an imported ontology does say a type is disjoint
  ;; from itself — that is how it says the type has no instances.  The browser reads what
  ;; is **stored**, not what would be admitted, so the front page has to render it rather
  ;; than 500 on it, and has to render *both* sides.
  ;; injected at the **access** facade, which is the var the browser calls and the one an
  ;; import would have filled: nothing in this KB's own assert path can produce one
  (let [real acc/sentexes-with-functor
        self {:id -1 :sentence '(disjoint nothing nothing) :context 'UniverseContext
              :truth :true :strength :monotonic}]
    (with-redefs [acc/sentexes-with-functor
                  (fn [target pred & args]
                    (cond-> (apply real target pred args)
                      (= 'disjoint pred) (conj self)))]
      (let [r (GET "/")]
        (is (= 200 (:status r)))
        (is (re-find #">nothing</a> ⊥ <a[^>]*>nothing</a>" (:body r))
            "both sides, not one term with the other silently missing"))
      (testing "and so does the continuation that pages the same list"
        (is (= 200 (:status (GET "/front/rows" "section=disjoint&offset=0"))))))))

(deftest a-term-page-survives-a-compound-in-the-taxonomy
  ;; The second half of the same story as the test above: a **type node need not be a
  ;; symbol**.  An imported ontology names a collection it has no atomic name for with a
  ;; function term — a NAT — and that is a `PersistentList`, which `compare` throws on
  ;; instead of ordering.  So every list the browser sorts is sorted by *name*: it is what
  ;; the list is read in, and it is the one ordering that exists for every term a KB can
  ;; hold.  Injected at the access facade because nothing pure's own assert path stores is
  ;; one.
  (let [nat        '(QuantityFn 5 Meter)
        real-types acc/types
        real-specs acc/specs]
    (with-redefs [acc/types (fn [target & args] (conj (vec (apply real-types target args)) nat))
                  acc/specs (fn [target t & args]
                              (cond-> (apply real-specs target t args)
                                (= 'cat t) (conj nat)))]
      (let [r (GET "/term" "q=dog")]                        ; dog ⊥ cat, so cat's specs are read
        (is (= 200 (:status r)))
        (is (re-find #"Disjoint with" (:body r)))
        (is (re-find #"QuantityFn" (:body r))
            "and the compound is listed rather than being what killed the page")))))

(tu/deftest-kb the-front-page-does-not-grow-with-the-taxonomy
  ;; the acceptance criterion, asserted rather than measured: adding a wide band of
  ;; types must not add rows to the page.  It is the whole point — an eager tree renders
  ;; every one of them.
  (tu/with-terms [wide_root]
    (let [before (count (:body (GET "/")))]
      (v/assert kb (list 'genl wide_root 'thing) 'UniverseContext {:chain? false})
      (doseq [i (range 120)]
        (v/assert kb (list 'genl (symbol (str (name wide_root) "_kid" i)) wide_root)
                  'UniverseContext {:chain? false}))
      (let [after (count (:body (GET "/")))]
        (is (< (- after before) 2000)
            (str "120 new types added " (- after before) " bytes to the page")))
      (testing "and the new node's children are one fetch away, capped, with a sentinel"
        (let [b (:body (GET "/tree/rows" (str "rel=genl&node=" (name wide_root))))]
          (is (= 50 (count (re-seq #"<li>" (str/replace b #"<li class" "<li-c class")))))
          (is (re-find #"show \d+ more" b)))))))

(deftest stats-page-reports-kb-wide-counts
  (let [r (GET "/stats")]
    (is (= 200 (:status r)))
    (testing "headline stat cards and the contexts-by-size table render"
      (is (re-find #"Statistics" (:body r)))
      (is (re-find #"Contexts" (:body r)))
      (is (re-find #"Types" (:body r)))
      (is (re-find #"Sentexes" (:body r)))
      (is (re-find #"Contexts by size" (:body r))))
    (testing "a context that actually holds facts shows up with a count"
      (is (re-find #"NaturalWorldContext" (:body r)))
      (is (re-find #"stat-n" (:body r))))))

(deftest the-front-page-opens-with-what-the-kb-is
  ;; A reader landing on an unfamiliar corpus asks how big it is before they ask anything
  ;; about its contents, so the answer belongs here and not only on /stats.  Four O(1) reads.
  (let [body (:body (GET "/"))]
    (doseq [label ["Sentexes" "Types" "Contexts" "Terms"]]
      (is (re-find (re-pattern (str "stat-l\">" label "<")) body) label))
    (is (re-find #"class=\"stat-n\">\d" body) "with a number over each")))

;; ---- what a page shows when the list is too long to be a list -----------
;;
;; The whole rework: fifty of 13,196 contexts alphabetically, or fifty of 27,196 separated
;; pairs, is not a short answer but an arbitrary sample of a long one.  Where a cheap
;; ranking exists the page shows the top of it; where it does not, the list is capped and
;; continues on scroll.  These drive the large-KB branches, which the shipped schema is
;; three orders of magnitude too small to reach.

(defn- segment
  "The slice of `body` starting at `marker`, clipped to the body — a section, without a
  substring that runs off the end when the page is shorter than the window."
  [body marker n]
  (when-let [i (str/index-of body marker)]
    (subs body i (min (count body) (+ i n)))))

(tu/deftest-kb the-contexts-section-ranks-by-size-when-it-cannot-draw-a-lattice
  ;; 28,998 genlContext edges is past `lattice-cap`, so there is no lattice to draw and the
  ;; question changes from "how do these nest" to "where is the knowledge".  Alphabetically
  ;; first-fifty answered neither.
  (tu/with-terms [heldBy BiggestContext]
    ;; a context is a node of the genlContext lattice, so an edge is what puts one in
    ;; `contexts` at all — a context nothing names holds sentexes but is not a node
    (v/assert kb (list 'genlContext BiggestContext 'UniverseContext) 'UniverseContext
              {:chain? false})
    (v/assert-many kb (for [i (range 400)] (list heldBy (symbol (str "TmpBig" i))))
                   BiggestContext {:chain? false})
    (let [cap  (ns-resolve 'vaelii.impl.web 'lattice-cap)
          body (with-redefs-fn {cap 0}                  ; no lattice to draw, at any size
                 #(:body (GET "/")))
          seg  (segment body "holding the most" 4000)
          ns'  (mapv #(Long/parseLong (second %)) (re-seq #" — (\d+) sentexes" seg))]
      (is (some? seg) "the fallback says what it is showing instead")
      (is (re-find (re-pattern (str ">" BiggestContext "</a><span class=\"muted\"> — 400 sentexes"))
                   seg)
          "the biggest context, named with what it holds")
      (is (seq ns') "and it is a list of counts, not of names alone")
      (is (= ns' (vec (reverse (sort ns')))) (str "largest first: " ns'))
      (is (= 400 (first ns')) "the ranking is the point, not the cap")
      (is (re-find #"contexts hold something" seg) "and how many there are in all"))))

(tu/deftest-kb disjointness-too-wide-to-list-is-summarised-by-what-separates-most
  (tu/with-terms [hub_type]
    (v/assert kb (list 'genl hub_type 'thing) 'UniverseContext {:chain? false})
    (v/assert-many kb (for [i (range 60)]
                        (list 'disjoint hub_type (symbol (str (name hub_type) "_other" i))))
                   'UniverseContext {:chain? false})
    (let [body (:body (GET "/"))
          seg  (segment body "Disjointness" 3000)]
      (is (some? seg) "past the cap the section is a summary, not a page of pairs")
      (is (re-find #"separated pairs, declared and metatype-induced, over \d+ types" seg))
      (is (re-find (re-pattern (str ">" hub_type "</a><span class=\"muted\"> — disjoint from 60 types"))
                   seg)
          "the most-separated type, named with its count and linking to its own page")
      (is (not (re-find #" ⊥ " seg)) "and no pair list — sorting 27,196 of them cost 4.5s"))))

(tu/deftest-kb the-ledgers-are-capped-and-continue-on-scroll
  ;; A ledger row is not a name — it is one or two whole sentences with every subterm
  ;; linked — so fifty of them was 60 KB and the bulk of the stats page.  The count is on
  ;; the card above; the list is for seeing what one looks like.
  (tu/with-terms [wobbles DilemmaContext]
    ;; two represented dilemmas: a default and its negation at the same strength, which
    ;; `settle` leaves both believed and reports as a pair rather than arbitrating
    (doseq [i (range 2) :let [x (symbol (str "TmpWob" i))]]
      (v/assert kb (list wobbles x) DilemmaContext)
      (v/assert kb (list 'not (list wobbles x)) DilemmaContext))
    (is (<= 2 (count (v/contradictions kb))) "the KB holds more dilemmas than the cap below")
    (let [cap  (ns-resolve 'vaelii.impl.web 'ledger-cap)
          body (with-redefs-fn {cap 1} #(:body (GET "/stats")))
          seg  (segment body "<h3>Contradictions" 2000)]   ; the section, not the stat card
      (is (= 1 (count (re-seq #"⇄" seg))) "one row, not the whole disagreement")
      (is (re-find #"/stats/rows\?section=contradictions&amp;offset=1" seg)
          "and a sentinel htmx fires on scroll")
      (testing "the continuation is bare rows from the offset, re-read at the same order"
        (let [r (with-redefs-fn {cap 1} #(GET "/stats/rows" "section=contradictions&offset=1"))]
          (is (= 200 (:status r)))
          (is (not (re-find #"<html" (:body r))))
          (is (re-find #"⇄" (:body r))))))))

(tu/deftest-kb the-contexts-table-is-capped-and-continues-on-scroll
  (tu/with-terms [heldBy]
    ;; 40 contexts holding something: past the 25-row cap.  Each needs a genlContext edge
    ;; to be a node of the lattice `contexts` enumerates
    (doseq [i (range 40)
            :let [c (symbol (str "TmpTable" i "Context"))]]
      (v/assert kb (list 'genlContext c 'UniverseContext) 'UniverseContext {:chain? false})
      (v/assert kb (list heldBy (symbol (str "TmpRow" i))) c {:chain? false}))
    (let [body (:body (GET "/stats"))
          tbl  (subs body (str/index-of body "Contexts by size"))
          rows (count (re-seq #"<tr><td>" tbl))]
      (is (= 25 rows) "the table is one screen, not every context in the KB")
      (testing "and ends in a sentinel htmx fires on scroll, shaped as a table row"
        (is (re-find #"<tr class=\"more\"[^>]*hx-trigger=\"revealed" tbl))
        (is (re-find #"/stats/rows\?section=contexts&amp;offset=25" tbl))
        (is (re-find #"<td class=\"more-td\" colspan=\"2\"" tbl)
            "a tbody may hold nothing but rows, so the sentinel is one"))
      (testing "the continuation is bare rows, in the same order, from the offset"
        (let [r (GET "/stats/rows" "section=contexts&offset=25")]
          (is (= 200 (:status r)))
          (is (not (re-find #"<html" (:body r))))
          (is (re-find #"<tr><td>" (:body r)))))
      (testing "an unknown section is empty rather than an error"
        (is (str/blank? (str/trim (:body (GET "/stats/rows" "section=nonsense&offset=0")))))))))

;; ---- the query plan ------------------------------------------------------
;;
;; `query-plan` had no screen at all: the join order `plan/order` picks and the reason
;; one prover displaces another were reachable only from a REPL.  For the reader
;; deciding whether this is a reasoner rather than a lookup table, that is the evidence.

(deftest a-single-goal-shows-every-prover-and-which-one-runs
  (let [r (GET "/levels" "q=%28flies%20%3Fx%29&ctx=BiologyContext")]
    (is (= 200 (:status r)))
    (is (re-find #"How it would be answered" (:body r)))
    (testing "the provers bearing on the goal, with their estimates"
      (is (re-find #"FactProver" (:body r)))
      (is (re-find #"est. bindings" (:body r)))
      (is (re-find #"completeness" (:body r))))
    (testing "and the rule the engine actually follows, stated rather than implied"
      (is (re-find #"complete for the goal" (:body r))))))

(deftest a-complete-prover-shadows-the-rest-and-the-page-says-so
  ;; `genl` is answered from the closure, which is complete for it — so every other
  ;; applicable prover is shadowed, and "applicable" stops meaning "consulted"
  (let [body (:body (GET "/levels" "q=%28genl%20dog%20thing%29&ctx=OrganismContext"))]
    (is (re-find #"TransitivityProver" body))
    (is (re-find #"shadowed by" body))
    (is (re-find #"the sole complete method" body))))

(deftest a-conjunction-shows-its-join-order-and-what-decided-it
  (let [r (GET "/levels" "q=%5B%28bird%20%3Fx%29%20%28flies%20%3Fx%29%5D&ctx=BiologyContext")]
    (is (= 200 (:status r)))
    (is (re-find #"Conjunctive goal" (:body r)))
    (testing "the literals in the order they will run, with the fan-out each was picked on"
      (is (re-find #"est. matches" (:body r)))
      (is (re-find #"bound before" (:body r))))
    (testing "sideways information passing is visible — a later literal is bound already"
      (is (re-find #"\?x" (:body r))))
    (testing "the levels are not rendered for a conjunction, and the page says why"
      (is (re-find #"answer about a single literal" (:body r))))))

(deftest the-stats-violations-carry-the-run-that-dropped-them
  ;; the ledger accumulates across runs, so which run dropped a conclusion is part of
  ;; the entry — the world KB has a rule with no placement context, which drops one
  (let [body (:body (GET "/stats"))]
    (when (re-find #"Violations" body)
      (is (re-find #"· run \d+" body) "each dropped conclusion names its run"))))

(deftest the-standing-disjointness-question-is-asked-not-assumed
  (testing "it is behind a control, because it is computed rather than filed"
    (let [body (:body (GET "/stats"))]
      (is (re-find #"Standing disjointness clashes" body))
      (is (re-find #"href=\"/stats\?clashes=1\"" body) "an offer, not an answer")
      (is (not (re-find #"Computed just now" body)))))
  (testing "asking runs the pass and says that is what happened"
    (let [r (GET "/stats" "clashes=1")]
      (is (= 200 (:status r)))
      (is (re-find #"Computed just now|holds" (:body r)))
      (is (not (re-find #"href=\"/stats\?clashes=1\"" (:body r)))
          "the offer is replaced by its answer"))))

(deftest find-does-regex-over-term-names
  (testing "a substring pattern lists the matching terms"
    (let [r (GET "/find" "q=parent")]
      (is (= 200 (:status r)))
      (is (re-find #"Find terms" (:body r)))
      (is (re-find #"parentOf" (:body r)))
      (is (re-find #"grandparentOf" (:body r)))))          ; both contain "parent"
  (testing "^ anchors — proof it is a real regex, not a literal substring"
    ;; a literal search for the string "^grandparent" would match nothing; finding
    ;; grandparentOf proves the ^ was applied as an anchor
    (is (re-find #"grandparentOf" (:body (GET "/find" "q=%5Egrandparent")))))
  (testing "an invalid regex is reported, not thrown"
    (is (re-find #"Not a valid regular expression" (:body (GET "/find" "q=%28")))))
  (testing "a pattern that matches nothing says so"
    (is (re-find #"No terms match" (:body (GET "/find" "q=zzzznope"))))))

(deftest a-pattern-that-blows-the-matcher-stack-reads-as-unusable
  ;; A catastrophic pattern can raise StackOverflowError out of the regex engine —
  ;; past Exception — and this handler stack has no exception middleware, so an
  ;; uncaught one is a bare 500 on a route the browser hits per keystroke.  The
  ;; matcher's failure, whatever its class, is `term-hits`' ordinary ::bad answer.
  (with-redefs [acc/find-terms (fn [& _] (throw (StackOverflowError.)))]
    (is (= :vaelii.impl.web/bad (#'web/term-hits tu/*kb* "a{2}" 10))
        "the sentinel, not a throw")
    (let [r (GET "/find" "q=a%7B2%7D")]
      (is (= 200 (:status r)))
      (is (re-find #"Not a valid regular expression" (:body r))))))

(deftest find-jumps-straight-to-a-single-or-exact-term
  (testing "an exact term name jumps to its page — even though it is a substring of another"
    (let [r (GET "/find" "q=parentOf")]                    ; also a substring of grandparentOf
      (is (re-find #"Sentexes by index" (:body r)))        ; the term page, not the results list
      (is (not (re-find #"Find terms" (:body r))))
      (is (= "/term?q=parentOf" (get-in r [:headers "HX-Push-Url"])))))  ; url reflects the jump
  (testing "a broad pattern with several matches stays a list"
    (let [r (GET "/find" "q=parent")]
      (is (re-find #"Find terms" (:body r)))
      (is (nil? (get-in r [:headers "HX-Push-Url"])))
      (is (re-find #"grandparentOf" (:body r))))))

(deftest term-page-lists-sentexes-and-taxonomy
  (let [r (GET "/term" "q=dog")]
    (is (= 200 (:status r)))
    (testing "taxonomy info and containing sentexes"
      (is (re-find #"Supertypes" (:body r)))            ; dog is a type
      (is (re-find #"Disjoint with" (:body r)))         ; dog ⊥ cat
      (is (re-find #"Muffet" (:body r)))))                ; (dog Muffet)
  (testing "an individual's sentexes are found by term"
    (is (re-find #"parentOf" (:body (GET "/term" "q=Bob"))))))

(deftest term-page-groups-sentexes-by-index
  (testing "a predicate's facts are grouped under its functor root, arguments under [:argument-root]"
    (let [r (GET "/term" "q=dog")]
      (is (= 200 (:status r)))
      (is (re-find #"Sentexes by index" (:body r)))
      (is (re-find #"As predicate" (:body r)))            ; (dog Muffet) is a functor-root fact
      (is (re-find #"\[:functor-root dog\]" (:body r)))
      (is (re-find #"stored" (:body r)))                  ; the O(1) stored count is shown
      (is (re-find #"Muffet" (:body r)))))                  ; still reachable, now under a group
  (testing "an individual is grouped by the argument position it fills"
    (let [r (GET "/term" "q=Bob")]
      (is (re-find #"argument position" (:body r)))
      (is (re-find #"\[:argument-slot" (:body r)))
      (is (re-find #"parentOf" (:body r))))))

;; ---- the concept graph at the top of a term page ------------------------
;;
;; It renders **live** — no route, no click, no state — so the claims to hold are that it
;; is correct (every arrow ends on a drawn node), bounded (the *read* is bounded, not only
;; the render), honest (it says what it left out), and never the reason a page fails.

(defn- svg-of
  "The one `<svg>` on a page, or nil.  Everything below reads the markup rather than the
  scene, because the markup is what a reader gets."
  [body]
  (when-let [i (str/index-of body "<svg")]
    (subs body i (+ 6 (str/index-of body "</svg>" i)))))

(defn- drawn-terms
  "The terms the picture actually drew, from the node titles (which carry the whole term,
  not the cut label)."
  [svg]
  (set (map second (re-seq #"<title>([^<]*)</title>" (or svg "")))))

(defn- rects
  "Every node box, as `[x y w h]`."
  [svg]
  (for [[_ w h x y] (re-seq #"<rect class=\"g-pill\" height=\"(\d+)\" rx=\"\d+\" width=\"(\d+)\" x=\"(-?\d+)\" y=\"(-?\d+)\"" (or svg ""))]
    (mapv #(Long/parseLong %) [x y h w])))

(defn- segments
  "Every edge, as `[x1 y1 x2 y2]`."
  [svg]
  (for [[_ x1 x2 y1 y2] (re-seq #"<line marker-end=\"[^\"]*\"(?: marker-start=\"[^\"]*\")? x1=\"(-?\d+)\" x2=\"(-?\d+)\" y1=\"(-?\d+)\" y2=\"(-?\d+)\"" (or svg ""))]
    (mapv #(Long/parseLong %) [x1 y1 x2 y2])))

(deftest the-taxonomy-view-draws-where-a-term-sits
  (let [body (:body (GET "/term" "q=animal"))
        svg  (svg-of body)]
    (is (some? svg) "a term with subsumption structure gets a picture")
    (testing "the term itself is the centre and is never capped out of its own view"
      (is (re-find #"class=\"g-node t-type g-centre\"" svg))
      (is (contains? (drawn-terms svg) "animal")))
    (testing "a supertype above it and a subtype below it are both drawn"
      (let [ts (drawn-terms svg)]
        (is (contains? ts "living_thing"))
        (is (contains? ts "bird"))))
    (testing "every node is a link to that term's page — the graph is navigation"
      (is (re-find #"<a href=\"/term\?q=living_thing\"><g class=\"g-node" svg))
      (is (= (count (drawn-terms svg)) (count (re-seq #"<a href=\"/term\?q=" svg)))))
    (testing "and it says which claim the vertical axis is"
      (is (re-find #"class=\"g-edge g-genl\"" svg))
      (is (re-find #"arrows point at the more general type" body)))
    (testing "the prose the picture approximates is still there, unchanged"
      (is (re-find #"Supertypes: " body))
      (is (re-find #"Subtypes: " body))
      (is (re-find #"Sentexes by index" body)))))

(deftest a-context-page-draws-the-relation-a-context-has
  ;; `genl` says nothing about contexts, so the three type lines are empty on this page and
  ;; the picture is the only thing on it that shows the lattice at all
  (let [svg (svg-of (:body (GET "/term" "q=NaturalWorldContext")))]
    (is (some? svg))
    (is (re-find #"class=\"g-edge g-genlContext\"" svg)
        "drawn distinguishably: a context edge must not read as a type edge")
    (is (not (re-find #"class=\"g-edge g-genl\"" svg)))
    (is (contains? (drawn-terms svg) "WellContext"))))

(tu/deftest-kb the-radial-view-is-for-a-term-with-relations-and-no-taxonomy
  (tu/with-terms [likesThing TmpA TmpB TmpC EgoContext]
    (v/assert kb (list likesThing TmpA TmpB) EgoContext {:chain? false})
    (v/assert kb (list likesThing TmpB TmpC) EgoContext {:chain? false})
    (let [body (:body (GET "/term" (str "q=" TmpA)))
          svg  (svg-of body)]
      (is (some? svg))
      (is (not (re-find #"g-genl" svg)) "no subsumption structure, so no rows")
      (is (contains? (drawn-terms svg) (str TmpA)))
      (is (contains? (drawn-terms svg) (str TmpB)) "the inner ring")
      (is (contains? (drawn-terms svg) (str TmpC)) "and the second hop, off TmpB")
      (is (re-find #"two hops out" body)))))

(tu/deftest-kb a-term-with-nothing-to-draw-gets-no-frame
  (tu/with-terms [lonely_type Lonely QuietContext]
    ;; mentioned, and by exactly one unary fact: no subsumption, no binary relation
    (v/assert kb (list lonely_type Lonely) QuietContext {:chain? false})
    (let [body (:body (GET "/term" (str "q=" Lonely)))]
      (is (= 200 (:status (GET "/term" (str "q=" Lonely)))))
      (is (nil? (svg-of body)) "no picture")
      (is (not (re-find #"kb-graph" body)) "and no empty frame or no-graph box either")
      (is (re-find #"Sentexes by index" body) "the page is otherwise exactly the page"))))

(deftest every-arrow-ends-on-a-node
  ;; A picture that draws an arrow into empty space is worse than one that draws less.
  ;; Checked structurally rather than trusted: each endpoint must land on some drawn box.
  (doseq [q ["animal" "dog" "Bob" "thing" "NaturalWorldContext"]]
    (when-let [svg (svg-of (:body (GET "/term" (str "q=" q))))]
      (let [boxes (rects svg)
            on?   (fn [[x y]]
                    (some (fn [[bx by bw bh]]
                            (and (<= (- bx 2) x (+ bx bw 2)) (<= (- by 2) y (+ by bh 2))))
                          boxes))]
        (is (seq boxes) q)
        (doseq [[x1 y1 x2 y2] (segments svg)]
          (is (on? [x1 y1]) (str q ": edge tail at " [x1 y1] " is not on a node"))
          (is (on? [x2 y2]) (str q ": edge head at " [x2 y2] " is not on a node")))))))

;; ---- the three type lines are bounded too -------------------------------
;;
;; Same claim as the front page's, in the one place it was still missing.  Unbounded they
;; are what makes a term page of an imported ontology unusable rather than slow: `thing`
;; has 110,128 subtypes there and one NAT collection is disjoint from 79,638 types, which
;; renders as 14 MB of links a browser cannot even be clicked through afterwards.

(defn- type-line-of
  "The links in one of the three type lines, and the elision note that follows it."
  [body label]
  (let [i (str/index-of body (str "<p>" label ": "))
        j (when i (str/index-of body "</div>" i))
        s (when i (subs body i (or j (count body))))]
    {:links (count (re-seq #"href=\"/term\?q=" (or s "")))
     :note  (second (re-find #"showing (\d+ of [^<]*)" (or s "")))}))

(defn- wide-type!
  "A type with `n` direct subtypes, all temporaries the fixture takes back."
  [kb t n]
  (v/assert kb (list 'genl t 'thing) 'UniverseContext {:chain? false})
  (v/assert-many kb (for [i (range n)] (list 'genl (symbol (str (name t) "_kid" i)) t))
                 'UniverseContext {:chain? false}))

(tu/deftest-kb a-compound-type-node-colours-as-a-type-not-a-number
  ;; An imported ontology names a type it has no atomic name for with a function term, so a
  ;; type node need not be a symbol — and the non-symbol fallback is the *number* colour.
  ;; 17,211 of OpenCyc's 132,352 types are compounds, so getting this order wrong is a page
  ;; of red.
  (tu/with-terms [CollectionFn base_type member_type]
    (let [nat (list CollectionFn base_type)]
      (v/assert kb (list 'genl nat 'thing) 'UniverseContext {:chain? false})
      (v/assert kb (list 'genl member_type nat) 'UniverseContext {:chain? false})
      (let [body (:body (GET "/term" (str "q=" (java.net.URLEncoder/encode (pr-str nat) "UTF-8"))))]
        (is (re-find #"<h2>Term <a class=\"sx t-type\"" body))
        (is (not (re-find #"<h2>Term <a class=\"sx t-num\"" body)))))))

(tu/deftest-kb a-type-line-shows-its-cap-and-says-what-it-left-out
  (tu/with-terms [wide_type]
    (wide-type! kb wide_type 400)
    (let [body (:body (GET "/term" (str "q=" wide_type)))
          subs (type-line-of body "Subtypes")]
      (is (= 50 (:links subs)) "capped — 400 subtypes are not 400 links")
      (is (= "50 of 400" (:note subs)) "with the exact count, which a cached closure gives free")
      (testing "a line that fits is untouched — the shipped schema reads exactly as it did"
        (let [sup (type-line-of body "Supertypes")]
          (is (pos? (:links sup)))
          (is (nil? (:note sup))))))))

(tu/deftest-kb a-separation-too-wide-to-union-is-capped-on-a-bound
  ;; The line is the union of the partners' spec closures, and building it to show fifty is
  ;; the "capping the render is not bounding the read" defect: 43 partners spanning 290,000
  ;; subtypes took 1.5s of union to produce a list nobody can read.  Past `sortable-cap` the
  ;; sum of the closure sizes — free, every closure being a cached set — is taken as the
  ;; bound and only the window is walked.
  (tu/with-terms [left_type right_type]
    (v/assert kb (list 'genl left_type 'thing) 'UniverseContext {:chain? false})
    (wide-type! kb right_type 400)
    (v/assert kb (list 'disjoint left_type right_type) 'UniverseContext {:chain? false})
    (let [cap  (ns-resolve 'vaelii.impl.web 'sortable-cap)
          body (with-redefs-fn {cap 100}
                 #(:body (GET "/term" (str "q=" left_type))))
          djs  (type-line-of body "Disjoint with")]
      (is (= 50 (:links djs)) "capped")
      (is (re-find #"^50 of up to \d" (:note djs))
          "and the total is worded as the bound it is — a sum of closures over-counts an overlap")
      (testing "under the budget it is the exact answer, sorted, as before"
        (let [exact (type-line-of (:body (GET "/term" (str "q=" left_type))) "Disjoint with")]
          (is (= 50 (:links exact)))
          (is (= "50 of 401" (:note exact))))))))

(tu/deftest-kb a-hub-draws-its-cap-and-says-what-it-left-out
  (tu/with-terms [hub_type]
    (v/assert kb (list 'genl hub_type 'thing) 'UniverseContext {:chain? false})
    (v/assert-many kb (for [i (range 400)]
                        (list 'genl (symbol (str (name hub_type) "_kid" i)) hub_type))
                   'UniverseContext {:chain? false})
    (let [body (:body (GET "/term" (str "q=" hub_type)))
          svg  (svg-of body)]
      (testing "the row is capped — 400 subtypes are not 400 nodes"
        (is (= 8 (count (filter #(str/includes? % "_kid") (drawn-terms svg))))))
      (testing "and the caption says so, with the count and the fact that it is a bound"
        (is (re-find #"showing 8 of up to 40[01] direct subtypes" body)))
      (testing "the centre is still in its own view"
        (is (contains? (drawn-terms svg) (str hub_type)))))))

;; ---- the read is bounded, not just the render ---------------------------

(def ^:private facade-read-ops
  "Every read op the browser can reach, taken from the daemon's own allowlist rather than
  listed here — so an op added to the surface is counted by this the day it exists.  These
  are exactly the calls that are an HTTP round-trip under `--attach`."
  (into [] (filter #(ns-resolve 'vaelii.impl.access %)) (map symbol (keys @(resolve 'vaelii.impl.serve/ops)))))

(defn- read-counts
  "Run `f` with every facade read counted, and answer `{op n}`."
  [f]
  (let [counts (atom {})
        vars   (mapv (fn [op] [op (ns-resolve 'vaelii.impl.access op)]) facade-read-ops)
        orig   (into {} (map (fn [[_ vr]] [vr @vr])) vars)]
    (try
      (doseq [[op vr] vars]
        (let [g (orig vr)]
          (alter-var-root vr (constantly (fn [& args]
                                           (swap! counts update op (fnil inc 0))
                                           (apply g args))))))
      (f)
      (finally (doseq [[_ vr] vars] (alter-var-root vr (constantly (orig vr))))))
    @counts))

(def ^:private graph-read-budget
  "What the picture may cost a term page, in facade reads.  Twelve expansions — six a side
  — plus, only where a row was actually elided, one O(1) count each; the radial view spends
  six.  Stated here and asserted below, because a graph that renders without a click may
  never be the reason a term page is slow."
  24)

(tu/deftest-kb the-graph-costs-a-bounded-number-of-reads-whatever-the-fan-out
  ;; The defect this exists to catch is the one a render cap hides: capping what is *drawn*
  ;; is not capping what is *read*, and a page that draws eight of forty thousand subtypes
  ;; by reading forty thousand looks identical on the shipped schema.
  (tu/with-terms [tiny_type mid_type big_type]
    (doseq [[t n] [[tiny_type 3] [mid_type 40] [big_type 400]]]
      (v/assert kb (list 'genl t 'thing) 'UniverseContext {:chain? false})
      (v/assert-many kb (for [i (range n)] (list 'genl (symbol (str (name t) "_kid" i)) t))
                     'UniverseContext {:chain? false}))
    (let [gvar  (ns-resolve 'vaelii.impl.web 'term-graph)
          drawn (fn [t] (read-counts #(GET "/term" (str "q=" t))))
          plain (fn [t] (with-redefs-fn {gvar (fn [& _] nil)}
                          #(read-counts (fn [] (GET "/term" (str "q=" t))))))
          added (fn [t] (- (reduce + (vals (drawn t))) (reduce + (vals (plain t)))))
          [tiny mid big] (map added [tiny_type mid_type big_type])]
      (testing "the graph stays inside its stated budget at every width"
        (doseq [[label n] [["tiny" tiny] ["mid" mid] ["big" big]]]
          (is (<= 0 n graph-read-budget) (str label " hub added " n))))
      (testing "and does not grow with the fan-out — 400 subtypes cost exactly what 40 do"
        (is (= mid big) (str mid " vs " big)))
      (testing "the wide ones pay for their caption, the narrow one has nothing to caption"
        (is (re-find #"showing 8 of up to" (:body (GET "/term" (str "q=" big_type)))))
        (is (not (re-find #"showing " (:body (GET "/term" (str "q=" tiny_type)))))))
      (testing "and the belief it needs rides the page's one batched read, not a read a node"
        (is (= 1 (get (drawn big_type) 'believed))))
      (testing "every read it makes is one the daemon serves, so --attach renders the same"
        (is (every? (set facade-read-ops) (keys (drawn big_type))))))))

(tu/deftest-kb the-graph-renders-the-same-through-the-access-facade
  ;; the browser is written against `vaelii.impl.access`, not `vaelii.core`; driving it
  ;; through an access value rather than a raw KB is the in-process half of that claim
  (tu/with-terms [nearBy TmpP TmpQ FacadeContext]
    (v/assert kb (list nearBy TmpP TmpQ) FacadeContext {:chain? false})
    (let [via (web/app (acc/local kb))
          get* (fn [app] (:body (app {:request-method :get :uri "/term"
                                      :query-string (str "q=" TmpP)})))]
      (is (= (svg-of (get* *app*)) (svg-of (get* via)))))))

;; ---- belief, and failure ------------------------------------------------

(tu/deftest-kb a-defeated-edge-leaves-the-graph-and-stays-in-the-list
  (tu/with-terms [worksWith TmpX TmpY DefeatContext]
    (let [h (v/assert kb (list worksWith TmpX TmpY) DefeatContext)]
      (is (some? (svg-of (:body (GET "/term" (str "q=" TmpX))))) "drawn while believed")
      (v/assert kb (list 'not (list worksWith TmpX TmpY)) DefeatContext {:strength :monotonic})
      (is (false? (v/in? kb h)) "the default is defeated by the known-true negation")
      (let [body (:body (GET "/term" (str "q=" TmpX)))]
        (is (nil? (svg-of body))
            "the only edge is gone, so the node it reached is gone, so there is nothing to draw")
        (is (re-find #"badge-out" body)
            "and the row is still listed, dimmed — the page does not disagree with itself")))))

(deftest a-picture-that-cannot-be-drawn-costs-only-the-picture
  ;; this is the one part of the page that does arithmetic on KB-derived numbers, so it is
  ;; wrapped — a term page that 500s because its graph could not be drawn would be strictly
  ;; worse than the page without one
  (with-redefs [svg/scene (fn [& _] (throw (ex-info "boom" {})))]
    (let [r (GET "/term" "q=animal")]
      (is (= 200 (:status r)))
      (is (nil? (svg-of (:body r))))
      (is (re-find #"Supertypes: " (:body r)))
      (is (re-find #"Disjoint with" (:body r)))
      (is (re-find #"Sentexes by index" (:body r)))
      (is (re-find #"In argument position 1" (:body r))))))

;; ---- reified terms: the constant is never what a reader sees ------------
;;
;; A ground `(F a…)` under a `reifiableFunction` is stored as an opaque `nat/` constant
;; (docs/nat.md).  It is term *identity*, not a name anybody wrote, so no page shows one:
;; every rendering is the expression it was minted from, with bold parens and the opening
;; one linking to the constant's page.  These drive real minting through `assert` rather
;; than hand-writing a `nat/` symbol, so what is asserted is what the engine stores.

(defn- with-nat-kb
  "Run `f` with a reifiable function declared and `body` asserted, and answer what it
  returns.  Everything minted is a premise the neutral fixture retracts."
  [kb f]
  (tu/with-terms [FruitFn BestTreeIn AppleTree Orchard1 fruit colorOf NatContext]
    (v/assert kb (list 'reifiableFunction FruitFn) 'UniverseContext {:chain? false})
    (v/assert kb (list 'reifiableFunction BestTreeIn) 'UniverseContext {:chain? false})
    (v/assert kb (list 'resultIsa FruitFn fruit) 'UniverseContext {:chain? false})
    (let [h (v/assert kb (list colorOf (list FruitFn AppleTree) 'Red) NatContext {:chain? false})
          n (v/assert kb (list colorOf (list FruitFn (list BestTreeIn Orchard1)) 'Green)
                      NatContext {:chain? false})]
      (f {:k (second (:sentence (v/sentex kb h)))
          :outer (second (:sentence (v/sentex kb n)))
          :handle h :nested n
          :FruitFn FruitFn :BestTreeIn BestTreeIn :AppleTree AppleTree
          :Orchard1 Orchard1 :fruit fruit :colorOf colorOf :ctx NatContext}))))

(defn- visible-nats
  "Every reified constant a reader can actually *see* in `body` — the raw text with the
  attributes a machine reads back stripped out.  A constant legitimately appears in the
  `href` of the link to its own page and in the hidden form value the proposal panel
  posts; anywhere else is the leak these tests exist to catch.

  The pattern is the shape `nat/fresh-constant` mints (a gensym), not a bare `nat/`,
  which a search page's own `matching /nat/` heading would answer to."
  [body]
  (re-seq #"nat/g\d" (str/replace body #"(href|value)=\"[^\"]*\"" "")))

(defn- linked-nats
  "The distinct reified constants `body` links to — how many the page actually rendered,
  as against how many times it rendered one."
  [body]
  (set (map second (re-seq #"/term\?q=nat%2F(g\d+)" body))))

(tu/deftest-kb a-reified-term-reads-as-the-expression-it-denotes
  (with-nat-kb kb
    (fn [{:keys [k colorOf FruitFn AppleTree]}]
      (let [body (:body (GET "/term" (str "q=" colorOf)))]
        (testing "the expression is what the sentence says, and the constant is nowhere in it"
          (is (re-find (re-pattern (str ">" FruitFn "</a> <a[^>]*>" AppleTree "</a>")) body))
          (is (empty? (visible-nats body))))
        (testing "bold parens are the notation, and the first one links to the reified term"
          (is (re-find (re-pattern (str "<a class=\"nat-paren\" href=\"/term\\?q=nat%2F"
                                        (name k) "\"[^>]*>\\(</a>"))
                       body))
          (is (re-find #"<span class=\"nat-paren\">\)</span>" body)))
        (testing "each term inside it is separately linked, so the expression is navigable"
          (is (re-find (re-pattern (str "href=\"/term\\?q=" FruitFn "\"")) body))
          (is (re-find (re-pattern (str "href=\"/term\\?q=" AppleTree "\"")) body)))))))

(tu/deftest-kb a-nested-reified-term-nests-and-every-level-is-addressable
  (with-nat-kb kb
    (fn [{:keys [outer colorOf BestTreeIn Orchard1]}]
      (let [body  (:body (GET "/term" (str "q=" colorOf)))
            inner (second (v/term-expression kb outer))]
        (is (v/reified-term? inner) "the outer expression holds the inner constant, one hop")
        (testing "the inner NAT is drawn inside the outer one, not flattened away"
          (is (re-find (re-pattern (str "nat-paren\" href=\"/term\\?q=nat%2F" (name outer)
                                        "\"[^>]*>\\(</a>[^!]{0,200}nat-paren\" href=\"/term\\?q=nat%2F"
                                        (name inner) "\""))
                       body)))
        (testing "and both levels are links, so either reified term can be opened"
          (is (re-find (re-pattern (str "q=" BestTreeIn "\"")) body))
          (is (re-find (re-pattern (str "q=" Orchard1 "\"")) body)))
        (is (empty? (visible-nats body)))))))

(tu/deftest-kb the-reified-terms-own-page-is-about-the-expression
  (with-nat-kb kb
    (fn [{:keys [k FruitFn AppleTree]}]
      (let [body (:body (GET "/term" (str "q=" (java.net.URLEncoder/encode (str k) "UTF-8"))))
            expr (str "(" FruitFn " " AppleTree ")")]
        (is (= 200 (:status (GET "/term" (str "q=" (java.net.URLEncoder/encode (str k) "UTF-8"))))))
        (testing "the tab, the heading and the index keys all name the expression"
          (is (str/includes? body (str "<title>vaelii · term " expr "</title>")))
          (is (str/includes? body (str "[:argument-slot 1 " expr "]"))))
        (testing "so does the picture — its label and the description a screen reader gets"
          (is (str/includes? (svg-of body) (str "<title>" expr "</title>")))
          (is (str/includes? body (str "concept graph for " expr))))
        (testing "and the assert form opens on the expression, which is what re-reifies"
          ;; a textarea is content on its way *back in*: `assert` resolves the ground NAT to
          ;; the constant already minted, where a hand-typed constant would be a reader
          ;; writing about an opaque identity
          (is (str/includes? (:body (GET "/assert" (str "q=" (java.net.URLEncoder/encode (str k) "UTF-8"))))
                             (str "( " expr ")"))))
        (is (empty? (visible-nats body)))))))

(tu/deftest-kb no-page-shows-a-reified-constant
  (with-nat-kb kb
    (fn [{:keys [k handle colorOf fruit ctx]}]
      (let [enc (java.net.URLEncoder/encode (str k) "UTF-8")]
        (doseq [[uri qs] [["/" nil] ["/stats" nil] ["/find" "q=nat"]
                          ["/term" (str "q=" enc)] ["/term" (str "q=" colorOf)]
                          ["/term" (str "q=" fruit)] ["/term" (str "q=" ctx)]
                          [(str "/sentex/" handle) nil] [(str "/why/" handle) nil]
                          ["/assert" (str "q=" enc)]
                          ["/levels" (str "q=" (java.net.URLEncoder/encode
                                                (str "(" colorOf " ?x Red)") "UTF-8")
                                          "&ctx=" ctx)]]]
          (let [r (GET uri qs)]
            (is (= 200 (:status r)) uri)
            (is (empty? (visible-nats (:body r))) (str uri " leaked a reified constant"))))))))

(tu/deftest-kb one-read-per-reified-term-however-often-it-is-rendered
  ;; The map is `(termOfUnit K ?e)`, one probe per constant — there is no batched read for
  ;; it — so the per-request cache is the whole budget.  A page listing a reified NAT in a dozen
  ;; rows must not be a dozen round-trips under `--attach`.
  (with-nat-kb kb
    (fn [{:keys [k colorOf ctx]}]
      (dotimes [i 12] (v/assert kb (list colorOf k (symbol (str "Shade" i))) ctx {:chain? false}))
      (let [counts (read-counts #(GET "/term" (str "q=" colorOf)))
            body   (:body (GET "/term" (str "q=" colorOf)))]
        (is (< 12 (count (re-seq #"class=\"nat\"" body))) "the constant is rendered many times")
        (is (= (count (linked-nats body)) (get counts 'term-expression))
            "and read once per *distinct* constant on the page, not once per render")
        (is (every? (set facade-read-ops) (keys counts))
            "through the daemon's own allowlist, so --attach renders the same")))))

;; What is stored need not be what `assert` would admit (docs/web.md): a dump restores
;; whatever it holds, so the display cannot assume a constant has a believed expression
;; or that the map is acyclic.  Both are injected at the access facade, since by
;; construction no `assert` produces them.

(tu/deftest-kb a-constant-with-no-believed-expression-still-is-not-spelled-out
  (with-nat-kb kb
    (fn [{:keys [colorOf]}]
      (with-redefs [acc/term-expression (fn [& _] nil)]
        (let [body (:body (GET "/term" (str "q=" colorOf)))]
          (is (= 200 (:status (GET "/term" (str "q=" colorOf)))))
          (is (re-find #"<span class=\"muted\" title=\"no believed expression[^\"]*\">…</span>" body)
              "it says it cannot say, rather than falling back to the raw symbol")
          (is (empty? (visible-nats body))))))))

(tu/deftest-kb a-self-referential-map-costs-the-expansion-and-not-the-page
  (with-nat-kb kb
    (fn [{:keys [k colorOf FruitFn]}]
      ;; `(termOfUnit K (FruitFn K))` — the write path cannot build it (inner NATs mint
      ;; first), a restored dump can, and an unguarded walk over it is a stack overflow
      (with-redefs [acc/term-expression (fn [_ t] (when (= t k) (list FruitFn k)))]
        (let [r (GET "/term" (str "q=" colorOf))]
          (is (= 200 (:status r)))
          (is (re-find #"class=\"nat\"" (:body r)) "the expansion is drawn as far as it goes")
          (is (empty? (visible-nats (:body r)))))))))

(tu/deftest-kb sentex-page-shows-a-believed-sentex-as-in
  (let [bob (:id (first (v/sentexes-matching kb '(parentOf Tom Bob) 'NaturalWorldContext)))
        r   (GET (str "/sentex/" bob))]
    (is (re-find #"tag-in" (:body r)))))                  ; the IN belief pill

(tu/deftest-kb sentex-page-shows-a-superseded-spelling
  (tu/with-terms [bornIn Chicago NameContext]
    (tu/with-terms [Pref Dep]
      (let [h (v/assert kb (list bornIn Dep Chicago) NameContext)]
        (v/assert kb (list 'rewriteOf Pref Dep) NameContext)
        (is (false? (v/in? kb h)) "the deprecated spelling is stored but not believed")
        (let [r (GET (str "/sentex/" h))]
          (is (= 200 (:status r)))
          (is (re-find #"tag-superseded" (:body r)))      ; the belief pill
          (is (re-find #"Superseded" (:body r)))          ; the why-not detail block
          (is (re-find #"restated under its class representative" (:body r))))))))

(tu/deftest-kb sentex-page-shows-a-defeated-default
  (tu/with-terms [flies Tweety NestContext]
    (let [pos (v/assert kb (list flies Tweety) NestContext {:strength :default})]
      (v/assert kb (list 'not (list flies Tweety)) NestContext {:strength :monotonic})
      (is (false? (v/in? kb pos)) "the default loses to the monotonic negation")
      (let [r (GET (str "/sentex/" pos))]
        (is (re-find #"tag-defeated" (:body r)))
        (is (re-find #"Defeated" (:body r)))
        (is (re-find #"contradicted by" (:body r)))))))

(deftest levels-page-without-a-goal-documents-the-stack
  (let [r (GET "/levels")]
    (is (= 200 (:status r)))
    (testing "every level is named, with what it adds"
      (doseq [nm ["raw" "extent" "local" "visible" "typed" "closed" "solved" "proved"]]
        (is (re-find (re-pattern nm) (:body r)))))
    (testing "and there is a box to enter a goal"
      (is (re-find #"<form" (:body r))))))

(deftest levels-page-traces-a-goal-through-the-stack
  (let [r (GET "/levels" "q=(animal%20%3Fx)&ctx=NaturalWorldContext")]
    (is (= 200 (:status r)))
    (testing "the goal and the level that answers it are reported"
      (is (re-find #"Answered at level" (:body r)))
      (is (re-find #"typed" (:body r))))                ; the genl spec walk answers it
    (testing "an answer from the starter's animals is listed"
      (is (re-find #"Sam" (:body r))))                  ; (eagle Sam), reached via genl
    (testing "the levels below it report nothing"
      (is (re-find #"nothing" (:body r))))))

(deftest levels-page-survives-a-malformed-goal
  (testing "an unparseable goal falls back to the stack description, not a 500"
    (let [r (GET "/levels" "q=%28%28%28")]
      (is (= 200 (:status r)))
      (is (re-find #"The levels" (:body r)))))
  (testing "a goal that is a bare term is not run as a sentence"
    (let [r (GET "/levels" "q=dog")]
      (is (= 200 (:status r)))
      (is (re-find #"A goal is a sentence" (:body r))))))

(tu/deftest-kb sentex-page-links-into-the-stack
  (let [bob (:id (first (v/sentexes-matching kb '(parentOf Tom Bob) 'NaturalWorldContext)))
        r   (GET (str "/sentex/" bob))]
    (is (= 200 (:status r)))
    (is (re-find #"Trace through the stack" (:body r)))
    (is (re-find #"/levels\?q=" (:body r)))))

(tu/deftest-kb sentex-page-shows-supports-and-dependents
  (let [gp (:id (first (v/sentexes-matching kb '(grandparentOf Tom Ann) 'NaturalWorldContext)))
        r  (GET (str "/sentex/" gp))]
    (is (= 200 (:status r)))
    (is (re-find #"grandparentOf" (:body r)))
    (is (re-find #"Supported by" (:body r)))
    (is (re-find #"justification #" (:body r))))            ; it was derived
  (testing "a premise fact shows its dependents"
    (let [bob (:id (first (v/sentexes-matching kb '(parentOf Tom Bob) 'NaturalWorldContext)))
          r   (GET (str "/sentex/" bob))]
      (is (re-find #"premise" (:body r)))
      (is (re-find #"Dependents" (:body r))))))

(tu/deftest-kb a-rule-renders-with-the-authors-variable-names
  ;; rules are stored with canonical variables (?var0, …); the page restores the
  ;; author's names from the sentex :varmap so it reads as it was written.
  (let [rule (first (filter :antecedent (v/find-sentexes kb 'grandparentOf)))
        r    (GET (str "/sentex/" (:id rule)))]
    (is (some? rule) "the starter's grandparentOf rule is stored")
    (is (= 200 (:status r)))
    (testing "the canonical names are not what the reader sees"
      (is (not (re-find #"\?var0" (:body r)))))
    (testing "the author's names are"
      (is (re-find #"\?x" (:body r))))))

(tu/deftest-kb justification-page-shows-supports-and-conclusion
  (let [gp  (:id (first (v/sentexes-matching kb '(grandparentOf Tom Ann) 'NaturalWorldContext)))
        ded (first (v/supporting-justifications kb gp))
        r   (GET (str "/justification/" (:id ded)))]
    (is (= 200 (:status r)))
    (is (re-find #"Supports" (:body r)))
    (is (re-find #"parentOf" (:body r)))                ; its arguments
    (is (re-find #"grandparentOf" (:body r)))))         ; its conclusion

;; ---- reading a KB that is not finished ----------------------------------
;;
;; The banner is the whole of what makes browsing an unfinished KB honest, so what is
;; under test is that it reaches *every* page — it rides `#main`, which is what both a
;; document and a navigation fragment carry — and that it stays away when there is
;; nothing to say.

(deftest a-provisional-kb-says-so-at-the-top-of-every-page
  ;; a KB reopened over stores it already filled: every record and index entry present,
  ;; a fresh and empty TMS.  What a `:store` opened without `:recover?` is, and the
  ;; dangerous shape — `:ready`, so nothing about its status hints that every query
  ;; comes back empty.
  (let [spaces {:backend :memory :space 62 :recover? false}
        built  (v/open-kb spaces)]
    (try
      (v/assert built '(dog Muffet) 'UniverseContext {})
      (let [reopened (v/open-kb spaces)]
        (cat/register! "wt-beliefless" "Reopened without recover" reopened)
        (is (cat/activate "wt-beliefless"))
        (let [app  (web/app (cat/holder reopened))
              body (:body (app {:request-method :get :uri "/stats"}))]
          (is (str/includes? body "kb-caveat-"))
          (is (str/includes? body "Belief and the taxonomy are not built"))
          (testing "a navigation fragment carries it too — it rides #main, not the chrome"
            (is (str/includes? (:body (app {:request-method :get :uri "/term"
                                            :query-string "q=dog" :headers htmx}))
                               "kb-caveat-")))
          (testing "and it has its own endpoint, which is how the strip refreshes itself"
            (is (str/includes? (:body (app {:request-method :get :uri "/kbs/banner"}))
                               "Belief and the taxonomy are not built")))))
      (finally
        (cat/reset-registry!)
        (v/clear! built)))))

(deftest a-kb-still-loading-can-be-read-but-not-written
  ;; the load is far too big to finish and is cancelled the moment the assertions are
  ;; made — the unfinished state is the whole point, so waiting for it would be waiting
  ;; for the one thing that must not happen
  (let [key (cat/load-source "generated"
                             {:types 500 :individuals 20000 :facts 500000 :rules 200})
        got (loop [n 0]
              (cond (:kb (cat/entry key)) (:kb (cat/entry key))
                    (> n 3000)            nil
                    :else                 (do (Thread/sleep 10) (recur (inc n)))))]
    (try
      (is (some? got))
      (is (cat/activate key))
      (let [app  (web/app (cat/holder got))
            post (fn [uri params]
                   (app {:request-method :post :uri uri :scheme :http :params params
                         :headers {"host" "x" "origin" "http://x"}}))]
        (testing "reads are open — that is the point of activating it"
          (is (= 200 (:status (app {:request-method :get :uri "/stats"})))))
        (testing "and the banner says both what it is and what it costs"
          (let [body (:body (app {:request-method :get :uri "/stats"}))]
            (is (str/includes? body "kb-caveat-loading"))
            (is (str/includes? body "Writing is on hold"))))
        (testing "but a write is refused — a loader is already this process's one writer"
          (doseq [[uri params] [["/assert"  {"text" "(dog Rex)" "ctx" "UniverseContext"}]
                                ["/chain"   {}]
                                ["/retract" {"handles" "1"}]]]
            (let [r (post uri params)]
              (is (= 200 (:status r)) (str uri " answers a page, not a silent error status"))
              (is (str/includes? (:body r) "Nothing was written") (str uri " says so")))))
        (testing "cancelling stays reachable — it is the way out"
          (is (= 200 (:status (post "/kbs/unload" {"key" key}))))))
      (finally
        (cat/cancel! key)
        (let [deadline (+ (System/currentTimeMillis) 120000)]
          (while (and (cat/loading?) (< (System/currentTimeMillis) deadline))
            (Thread/sleep 20)))
        (cat/reset-registry!)))))

(tu/deftest-kb a-finished-kb-carries-no-banner-at-all [kb]
  (try
    (cat/register! "wt-ready" "Loaded and believed" kb)
    (is (cat/activate "wt-ready"))
    (let [body (:body ((web/app (cat/holder kb)) {:request-method :get :uri "/stats"}))]
      (is (not (str/includes? body "kb-caveat-")))
      (is (not (str/includes? body "Belief and the taxonomy are not built"))))
    (finally (cat/reset-registry!))))

(deftest the-stylesheet-is-a-real-file-served-from-resources
  (let [r (GET "/vaelii.css")]
    (is (= 200 (:status r)))
    (is (= "text/css; charset=utf-8" (get-in r [:headers "Content-Type"])))
    (testing "it is the file on the classpath, not a string in the namespace"
      (is (re-find #"t-context" (:body r)))
      (is (= (slurp (io/resource web/stylesheet-resource)) (:body r)))))
  (testing "pages link it instead of inlining a <style> block"
    (let [body (:body (GET "/"))]
      (is (re-find #"<link[^>]*vaelii\.css" body))
      (is (not (re-find #"<style" body))))))

(deftest unknown-ids-render-not-found
  (is (re-find #"No sentex" (:body (GET "/sentex/999999"))))
  (is (re-find #"No justification" (:body (GET "/justification/999999")))))

;; ---- multi-sentex editing (drag-select → textarea → one settle) -------
;; Selection is client-side; these exercise the server side — GET /edit seeds the
;; textarea for a set of handles, POST /edit applies the save through `core/edit!`.

(defn- POST
  ;; wrap-params only fills :params from a real body/query-string, so hand it :params
  ;; directly (it merge-preserves an existing one) — the values a form POST would carry
  ([uri params] (POST uri params nil))
  ([uri params headers]
   (*app* (cond-> {:request-method :post :uri uri :scheme :http :params params}
            headers (assoc :headers headers)))))

(tu/deftest-kb edit-form-seeds-a-textarea-for-the-selected-handles
  (tu/with-terms [likesOf Alice Bob EditContext]
    (let [h1 (v/assert kb (list likesOf Alice Bob) EditContext)
          h2 (v/assert kb (list likesOf Bob Alice) EditContext)
          r  (GET "/edit" (str "handles=" h1 "," h2))]
      (is (= 200 (:status r)))
      (is (re-find #"<textarea" (:body r)))
      (is (re-find (re-pattern (name Alice)) (:body r)))     ; the sentences are seeded
      (is (re-find (re-pattern (name Bob)) (:body r)))
      (is (re-find (re-pattern (str "value=\"" h1 "," h2)) (:body r))))))  ; hidden handles

(tu/deftest-kb editing-retracts-changed-lines-and-asserts-new-ones
  (tu/with-terms [likesOf Alice Bob Carol EditContext]
    (let [h1   (v/assert kb (list likesOf Alice Bob) EditContext)
          h2   (v/assert kb (list likesOf Bob Alice) EditContext)
          ;; keep line 1 verbatim, rewrite line 2's object Alice -> Carol
          text (str (pr-str [(list likesOf Alice Bob) EditContext]) "\n"
                    (pr-str [(list likesOf Bob Carol) EditContext]))
          r    (POST "/edit" {"handles" (str h1 "," h2) "text" text})]
      (testing "it re-renders the changed row in place instead of reloading the page"
        (is (nil? (get-in r [:headers "HX-Refresh"])))
        (is (re-find (re-pattern (str "outerHTML:\\[data-h=&apos;" h2 "&apos;\\]")) (:body r)))
        (is (re-find (re-pattern (name Carol)) (:body r))))
      (testing "and corrects the selection count out of band"
        (is (re-find #"id=\"sx-count\"" (:body r)))
        (is (re-find #"hx-swap-oob=\"innerHTML\"" (:body r))))
      (testing "the unchanged line keeps its handle — no churn"
        (is (v/in? kb h1)))
      (testing "the changed line's old sentex is retracted"
        (is (nil? (v/sentex kb h2))))
      (testing "and the edited sentence is asserted"
        (is (seq (v/sentexes-matching kb (list likesOf Bob Carol) EditContext)))
        (is (empty? (v/sentexes-matching kb (list likesOf Bob Alice) EditContext)))))))

(tu/deftest-kb a-parse-error-blocks-the-save-and-leaves-the-kb-intact
  (tu/with-terms [likesOf Alice Bob EditContext]
    (let [h1 (v/assert kb (list likesOf Alice Bob) EditContext)
          r  (POST "/edit" {"handles" (str h1) "text" "(this is not a vector)"})]
      (is (= 200 (:status r)))
      (is (nil? (get-in r [:headers "HX-Refresh"])) "no refresh on a parse error")
      (is (re-find #"expected \[sentence context\]" (:body r)))
      (is (v/in? kb h1) "nothing was written"))))

;; ---- htmx asks for a fragment, a browser asks for a page ---------------
;; The client swaps #main and discards the rest, so an htmx request is answered with
;; #main alone.  Without htmx (or restoring a history entry) the whole document is
;; still what comes back, which is what keeps the browser working with no JavaScript.

(deftest an-htmx-request-is-answered-with-the-main-fragment
  (let [full (:body (GET "/term" "q=dog"))
        part (:body (GET "/term" "q=dog" htmx))]
    (testing "the fragment is the #main element and its title, nothing else"
      (is (re-find #"<main id=\"main\"" part))
      (is (re-find #"<title>vaelii · term dog</title>" part))
      (is (not (re-find #"(?i)<!DOCTYPE" part)))
      (is (not (re-find #"<header" part)))
      (is (not (re-find #"htmx.min.js" part))))
    (testing "the page it replaces has all of that"
      (is (re-find #"(?i)<!DOCTYPE" full))
      (is (re-find #"<header" full))
      (is (re-find #"<main id=\"main\"" full)))
    (testing "and the content that actually lands is the same"
      (is (re-find #"Sentexes by index" part))
      (is (< (count part) (count full))))))

(deftest every-page-answers-a-fragment-and-a-document
  (doseq [[uri qs] [["/" nil] ["/stats" nil] ["/find" "q=parent"] ["/levels" nil]
                    ["/term" "q=dog"]]]
    (let [part (GET uri qs htmx)]
      (is (= 200 (:status part)) uri)
      (is (re-find #"<main id=\"main\"" (:body part)) uri)
      (is (not (re-find #"(?i)<!DOCTYPE" (:body part))) uri))))

(deftest a-boosted-navigation-lands-at-the-top-of-the-document
  ;; A boosted swap whose target is not the body scrolls that target into view, and the
  ;; target here is `#main` — so without a landing point every navigation would arrive
  ;; with the header scrolled off the top of a page nobody had scrolled.
  (let [body (:body (GET "/term" "q=dog"))]
    (is (re-find #"<body[^>]*hx-swap=\"outerHTML show:window:top\"" body)
        "the boosted swap says where to land: the top of the document")
    (testing "a continuation replaces itself in place and moves the page not at all"
      (let [cap (ns-resolve 'vaelii.impl.web 'group-cap)
            row (-> (with-redefs-fn {cap 1} #(:body (GET "/term" "q=dog")))
                    (->> (re-find #"<li class=\"more\"[^>]*>")))]
        (is row "a capped index group ends in a sentinel")
        (is (re-find #"hx-swap=\"outerHTML\"" row))
        (is (not (re-find #"show:" row)))))))

(deftest a-history-restore-gets-the-whole-document-back
  ;; htmx repopulating a history entry replaces the whole history element, so the
  ;; fragment it would otherwise get would be missing the chrome
  (let [r (GET "/term" "q=dog" (assoc htmx "hx-history-restore-request" "true"))]
    (is (re-find #"(?i)<!DOCTYPE" (:body r)))
    (is (re-find #"<header" (:body r)))))

(deftest the-single-match-jump-answers-in-the-shape-it-was-asked-in
  (let [r (GET "/find" "q=parentOf" htmx)]
    (is (= "/term?q=parentOf" (get-in r [:headers "HX-Push-Url"])))
    (is (re-find #"Sentexes by index" (:body r)))
    (is (not (re-find #"(?i)<!DOCTYPE" (:body r))))))

;; ---- continuation: a capped list is walkable, not truncated -------------

(tu/deftest-kb a-capped-group-ends-in-a-sentinel-that-fetches-the-rest
  (tu/with-terms [manyOf ManyContext]
    ;; one more than a group renders at a time, so the group is capped and continues
    (doseq [i (range 61)]
      (v/assert kb (list manyOf (symbol (str "Thing" i))) ManyContext {:chain? false}))
    (let [r (GET "/term" (str "q=" (name manyOf)))]
      (is (= 200 (:status r)))
      (is (re-find #"61 stored" (:body r)))
      (testing "the list ends in a continuation row rather than a dead count"
        (is (re-find #"class=\"more\"" (:body r)))
        (is (re-find #"hx-trigger=\"revealed, click" (:body r)))
        (is (re-find #"/term/rows\?q=" (:body r))))
      (testing "and it is a row of the grid it ends, reachable and firable by keyboard"
        (is (re-find #"<li class=\"more\"[^>]*role=\"row\"" (:body r)))
        (is (re-find #"keyup\[key==&apos;Enter&apos;\]" (:body r)))
        (is (re-find #"class=\"more-cell\"[^>]*tabindex=\"0\"" (:body r))))
      (testing "the first page is the cap, and Thing9 (last by context+handle) is not on it"
        (is (= 60 (count (re-seq #"class=\"sx-item\"" (:body r)))))))
    (testing "the sentinel's target answers the tail as bare rows"
      (let [r (GET "/term/rows" (str "q=" (name manyOf) "&g=0&offset=60"))]
        (is (= 200 (:status r)))
        (is (= 1 (count (re-seq #"class=\"sx-item\"" (:body r)))))
        (is (not (re-find #"<main" (:body r))))
        (testing "and stops — a tail with nothing after it carries no sentinel"
          (is (not (re-find #"class=\"more\"" (:body r)))))))
    (testing "a group index that names no group answers empty, not a 500"
      (is (= "" (:body (GET "/term/rows" (str "q=" (name manyOf) "&g=99&offset=0"))))))))

(deftest a-term-with-thousands-of-sentexes-is-walkable-to-the-end
  ;; The term page caps a group at 60 rows and ends it with a continuation sentinel;
  ;; there is no other pagination.  So the claim to check at scale is that following
  ;; the sentinel repeatedly reaches **every** row and then stops — no page is skipped,
  ;; none is served twice, and the walk terminates.  On the isolated db pair, so
  ;; flushing it cannot pull the scratch space out from under this namespace's :once KB.
  (tu/with-cleared-kb [kb tu/isolated-fresh]
    (let [app  (web/app kb)
          n    2400                                          ; 40 pages of 60
          pred 'manyOf
          get* (fn [uri qs] (app (cond-> {:request-method :get :uri uri}
                                   qs (assoc :query-string qs))))
          rows #(count (re-seq #"class=\"sx-item\"" %))
          next-url (fn [body]
                     (when-let [href (second (re-find #"hx-get=\"([^\"]*/term/rows[^\"]*)\"" body))]
                       (let [[uri qs] (str/split (str/replace href "&amp;" "&") #"\?" 2)]
                         [uri qs])))]
      (v/assert-many kb (for [i (range n)] (list pred (symbol (str "Thing" i))))
                     'ManyContext {:chain? false})
      (let [first-body (:body (get* "/term" (str "q=" pred)))]
        (is (re-find (re-pattern (str n " stored")) first-body)
            "the O(1) count reports the whole extent, however long it is")
        (is (= 60 (rows first-body)) "and the first page is the cap, not the extent")
        (loop [[uri qs] (next-url first-body), seen 60, pages 1]
          (cond
            (> pages 200) (is false "the continuation walk did not terminate")
            (nil? uri)    (do (is (= n seen) "every row is reachable by following the sentinel")
                              (is (= 40 pages) "in pages of the group cap, none skipped or repeated"))
            :else
            (let [body (:body (get* uri qs))]
              (recur (next-url body) (long (+ seen (rows body))) (inc pages)))))))))

(deftest levels-results-continue-the-same-way
  (let [r (GET "/levels/rows" "q=(animal%20%3Fx)&ctx=NaturalWorldContext&level=4&offset=0")]
    (is (= 200 (:status r)))
    (is (not (re-find #"<main" (:body r))))
    (is (re-find #"Sam" (:body r))))
  (testing "a malformed continuation is empty, not an error"
    (is (= "" (:body (GET "/levels/rows" "q=%28%28%28&level=4"))))))

(deftest find-results-continue-the-same-way
  (let [r (GET "/find/rows" "q=parent&offset=0")]
    (is (= 200 (:status r)))
    (is (not (re-find #"<main" (:body r))))
    (is (re-find #"parentOf" (:body r))))
  (testing "past the end there is simply nothing left"
    (is (not (re-find #"<li" (:body (GET "/find/rows" "q=parent&offset=9999")))))))

;; ---- search reads the vocabulary, not every sentex ---------------------

(deftest find-only-compiles-a-pattern-that-is-one
  (testing "a literal query is a substring match — re-find semantics, no regex compiled"
    (is (re-find #"grandparentOf" (:body (GET "/find" "q=parent")))))
  (testing "a pattern too long to be typed by hand is refused rather than compiled"
    (let [r (GET "/find" (str "q=" (java.net.URLEncoder/encode
                                    (str "(" (apply str (repeat 200 "a?")) ")") "UTF-8")))]
      (is (= 200 (:status r)))
      (is (re-find #"Not a valid regular expression" (:body r))))))

;; ---- static assets are cached (and re-read only in dev) ----------------

(deftest static-assets-carry-a-cache-policy
  (doseq [uri ["/vaelii.css" "/select.js" "/htmx.min.js"]]
    (let [r (GET uri)]
      (is (= 200 (:status r)) uri)
      (is (some? (get-in r [:headers "Cache-Control"])) uri))))

;; ---- escaping: markup never reaches the page verbatim ------------------
;; Rendering is hiccup2, which escapes strings in body position as well as in
;; attributes.  Both halves matter: a query param is attacker-supplied, and so is KB
;; *content* — a Clojure symbol may legally contain < and >, and a comment carries
;; free text.  Each case asserts the raw payload is absent and the escaped form present,
;; so a page that merely dropped the text would not pass.

(defn- escaped? [body raw escaped]
  (and (not (re-find (re-pattern (java.util.regex.Pattern/quote raw)) body))
       (re-find (re-pattern (java.util.regex.Pattern/quote escaped)) body)))

(deftest a-script-tag-in-a-query-param-is-escaped
  (let [r (GET "/find" (str "q=" (java.net.URLEncoder/encode "<script>alert(1)</script>" "UTF-8")))]
    (is (= 200 (:status r)))
    (testing "neither the <title> nor the reported pattern emits a live tag"
      (is (escaped? (:body r) "<script>alert(1)" "&lt;script&gt;alert(1)")))))

(deftest markup-inside-a-goal-symbol-is-escaped
  ;; a symbol may contain < and >, so a *readable* goal can still carry a tag
  (let [r (GET "/levels" (str "q=" (java.net.URLEncoder/encode "(<img/onerror=x> ?y)" "UTF-8")))]
    (is (= 200 (:status r)))
    (is (escaped? (:body r) "<img/onerror" "&lt;img/onerror"))))

(defn- predicate-page-holding
  "The front page's core-predicate list is bounded and paged, so a term added by a test
  is somewhere in the continuation rather than necessarily on the first page.  Walk the
  pages the reader would and answer the body the term is actually rendered in."
  [term]
  (let [pat (re-pattern (name term))]
    (loop [offset 0, pages 0]
      (let [body (:body (if (zero? offset)
                          (GET "/")
                          (GET "/front/rows" (str "section=predicates&offset=" offset))))]
        (cond
          (re-find pat body)                  body
          (or (> pages 40) (not (re-find #"section=predicates&amp;offset=" body))) nil
          :else (recur (+ offset 50) (inc pages)))))))

(tu/deftest-kb markup-in-kb-content-is-escaped
  ;; the home page prints `comment` text — KB content, which an importer or an agent
  ;; writes, so it is as untrusted as a query param
  (tu/with-terms [evilPred]
    (v/assert kb (list 'comment evilPred "doc <script>alert('kb')</script> text") 'CoreContext)
    (let [body (predicate-page-holding evilPred)]
      (is (some? body) "the comment is on one of the list's pages")
      (is (escaped? body "<script>alert('kb')" "&lt;script&gt;alert(&apos;kb&apos;)")))))

(tu/deftest-kb the-editor-textarea-is-escaped-exactly-once
  ;; a sentence carrying a free-text string is the shape that puts markup in the
  ;; textarea; it must be escaped once, so the user edits the text they wrote
  (tu/with-terms [notedPred]
    (let [h (v/assert kb (list 'comment notedPred "a <b> tag") 'CoreContext)
          r (GET "/edit" (str "handles=" h))]
      (is (re-find #"&lt;b&gt;" (:body r)) "the markup in the sentence is escaped")
      (is (not (re-find #"&amp;lt;" (:body r))) "and not escaped a second time"))))

(deftest the-theme-script-survives-as-executable-javascript
  ;; the pre-paint <head> script is the one node rendered raw — escaping it would
  ;; print the source instead of running it
  (let [body (:body (GET "/"))]
    (is (re-find #"localStorage" body))
    ;; a fragment carrying the characters escaping would eat: an apostrophe becomes
    ;; &apos; and the comparison stops being code
    (is (re-find #"\Qt==='light'||t==='dark'\E" body))
    (is (not (re-find #"&lt;/script" body)))))

(deftest the-theme-script-pins-only-a-value-the-stylesheet-answers-to
  ;; The media query is scoped by `:not([data-theme])`, so *any* attribute value
  ;; satisfies it away — write one no rule matches and the page sits on the light
  ;; base, deaf to the OS.  The script therefore checks what it read rather than
  ;; trusting it: localStorage is shared ground, and only `light` or `dark` means
  ;; anything here.
  (let [body (:body (GET "/"))]
    (is (re-find #"\Qif(t==='light'||t==='dark')\E" body)
        "an unrecognised stored theme is ignored, leaving the page on the OS default")
    (is (re-find #"\Q/^(violet|red|green|rainbow)$/\E" body)
        "and an unrecognised palette falls back to the default one")))

(deftest the-header-carries-both-colour-dots
  (let [body (:body (GET "/"))]
    (is (re-find #"id=\"palette-dot\"" body))
    (is (re-find #"id=\"theme-dot\"" body))))

;; ---- malformed input renders a page, never a 500 -----------------------

(deftest an-unreadable-term-renders-a-message
  (testing "an unbalanced paren is reported, not thrown"
    (let [r (GET "/term" "q=%28")]
      (is (= 200 (:status r)))
      (is (re-find #"Not a readable term" (:body r)))))
  (testing "a missing or empty ?q= asks for one"
    (is (re-find #"Pass \?q=" (:body (GET "/term"))))
    (is (re-find #"Pass \?q=" (:body (GET "/term" "q=")))))
  (testing "a readable term still renders its page"
    (is (re-find #"Sentexes by index" (:body (GET "/term" "q=dog"))))))

;; ---- the write route refuses a cross-origin caller ---------------------
;; POST /edit writes to the KB and nothing authenticates it, so the origin the
;; browser stamps on the request is what separates our own page from any other tab.

(tu/deftest-kb a-same-origin-post-edits-the-kb
  (tu/with-terms [likesOf Alice Bob Carol EditContext]
    (let [h    (v/assert kb (list likesOf Alice Bob) EditContext)
          text (pr-str [(list likesOf Alice Carol) EditContext])
          r    (POST "/edit" {"handles" (str h) "text" text}
                 {"host" "localhost:3000" "origin" "http://localhost:3000"})]
      (is (= 200 (:status r)))
      (is (re-find #"Saved" (:body r)))
      (is (seq (v/sentexes-matching kb (list likesOf Alice Carol) EditContext)) "the write went through"))))

(tu/deftest-kb a-cross-origin-post-is-refused-and-writes-nothing
  (tu/with-terms [likesOf Alice Bob Carol EditContext]
    (let [h    (v/assert kb (list likesOf Alice Bob) EditContext)
          text (pr-str [(list likesOf Alice Carol) EditContext])]
      (doseq [[label hdrs] [["another site"  {"host" "localhost:3000" "origin" "http://evil.example"}]
                            ;; a sandboxed frame sends Origin: null — an origin claim
                            ;; that matches nothing, not an absent header
                            ["an opaque origin" {"host" "localhost:3000" "origin" "null"}]
                            ["a cross-site referer"
                             {"host" "localhost:3000" "referer" "http://evil.example/x"}]]]
        (let [r (POST "/edit" {"handles" (str h) "text" text} hdrs)]
          (is (= 403 (:status r)) label)))
      (is (v/in? kb h) "the original is untouched")
      (is (empty? (v/sentexes-matching kb (list likesOf Alice Carol) EditContext)) "and nothing was asserted"))))

(tu/deftest-kb a-same-origin-referer-is-accepted
  (tu/with-terms [likesOf Alice Bob EditContext]
    (let [h (v/assert kb (list likesOf Alice Bob) EditContext)
          r (POST "/edit" {"handles" (str h) "text" (pr-str [(list likesOf Alice Bob) EditContext])}
              {"host" "localhost:3000" "referer" "http://localhost:3000/term?q=x"})]
      (is (= 200 (:status r))))))

;; ---- the write route refuses an oversized body -------------------------
;; Nothing authenticates this server either, so an anonymous caller streaming a body is
;; heap it would otherwise spend — and `wrap-params`, which is what reads a form here,
;; slurps whatever arrives with no ceiling of its own.  `guard/wrap-body-limit` sits
;; outside it (`vaelii.guard-test` pins the reading; this is the browser's 413).  Driven
;; with a **real encoded body** rather than a `:params` map, since a limit on the body is
;; invisible to a request that has none.

(tu/deftest-kb an-oversized-post-is-a-413-that-writes-nothing
  (tu/with-terms [likesOf Alice Bob Carol EditContext]
    (let [h    (v/assert kb (list likesOf Alice Bob) EditContext)
          form (str "handles=" h "&text="
                    (java.net.URLEncoder/encode
                     (pr-str [(list likesOf Alice Carol) EditContext]) "UTF-8"))
          post (fn []
                 (*app* {:request-method :post :uri "/edit" :scheme :http
                         :headers {"host"         "localhost:3000"
                                   "origin"       "http://localhost:3000"
                                   "content-type" "application/x-www-form-urlencoded"}
                         :body (java.io.ByteArrayInputStream. (.getBytes form "UTF-8"))}))]
      (testing "past the ceiling: a plain-text 413, and the KB is untouched"
        (let [n (v/sentex-count kb)
              r (with-redefs [guard/max-body-bytes 8] (post))]
          (is (= 413 (:status r)))
          (is (str/includes? (:body r) "exceeds"))
          (is (= n (v/sentex-count kb)) "the write never ran")
          (is (v/in? kb h) "and the handle the edit named is untouched")))
      (testing "under it the same body edits as usual — which is also what says the
                buffered copy the limit leaves behind is what wrap-params reads"
        (let [r (post)]
          (is (= 200 (:status r)))
          (is (seq (v/sentexes-matching kb (list likesOf Alice Carol) EditContext))
              "the form really was parsed out of the body"))))))

;; ---- selection: the rows carry what the keyboard and a screen reader need ----
;; Selection is client-side (select.js), so what the server owes it is the markup it
;; drives: a grid of rows, each with an addressable handle, a selected state, a place
;; in the roving tabindex, and a visible toggle target — plus the per-group control.

(deftest sentex-rows-are-a-selectable-aria-grid
  (let [body (:body (GET "/term" "q=dog"))]
    (testing "the list is a multi-selectable grid, not a bare ul"
      (is (re-find #"class=\"sx-list\"" body))
      (is (re-find #"role=\"grid\"" body))
      (is (re-find #"aria-multiselectable=\"true\"" body)))
    (testing "each row is an addressable row with a selected state and a tab position"
      (is (re-find #"class=\"sx-item\"" body))
      (is (re-find #"aria-selected=\"false\"" body))
      (is (re-find #"role=\"row\"" body))
      (is (re-find #"tabindex=\"-1\"" body))
      (is (re-find #"role=\"gridcell\"" body)))
    (testing "and carries the click affordance that makes the toggle target unambiguous"
      (is (re-find #"class=\"sx-check\"" body)))
    (testing "every group offers to select the whole of itself"
      (is (re-find #"data-select-all" body))
      (is (re-find #">Select all<" body)))
    (testing "the count is a live region, so a change announces"
      (is (re-find #"id=\"sx-count\"" body))
      (is (re-find #"aria-live=\"polite\"" body)))))

(deftest the-selection-bar-offers-both-writes
  (let [body (:body (GET "/"))]
    (is (re-find #"hx-get=\"/edit\"" body))
    (is (re-find #"hx-get=\"/retract\"" body))
    (testing "the destructive one is a preview by GET; only its POST retracts"
      (is (not (re-find #"hx-get=\"/retract\"[^>]*hx-post" body))))))

;; ---- why: the whole proof tree, not one hop ----------------------------

(tu/deftest-kb the-why-page-renders-the-proof-down-to-the-premises
  (let [gp (:id (first (v/sentexes-matching kb '(grandparentOf Tom Ann) 'NaturalWorldContext)))
        r  (GET (str "/why/" gp))]
    (is (= 200 (:status r)))
    (testing "the goal, the justification that concluded it, and the rule that licensed it"
      (is (re-find #"grandparentOf" (:body r)))
      (is (re-find #"justification #" (:body r)))
      (is (re-find #"parentOf" (:body r))))
    (testing "it recurses to the premises the derivation rests on"
      (is (re-find #"tag-premise" (:body r)))
      (is (re-find #"Tom" (:body r)))
      (is (re-find #"Ann" (:body r))))
    (testing "and is collapsible rather than one flat wall"
      (is (re-find #"<details" (:body r)))
      (is (re-find #"<summary" (:body r))))))

(tu/deftest-kb the-sentex-page-links-to-the-proof-tree
  (let [gp (:id (first (v/sentexes-matching kb '(grandparentOf Tom Ann) 'NaturalWorldContext)))
        r  (GET (str "/sentex/" gp))]
    (is (re-find (re-pattern (str "/why/" gp)) (:body r)))
    (is (re-find #"Why is this believed" (:body r)))))

(tu/deftest-kb the-why-page-of-a-premise-terminates-at-it
  (let [bob (:id (first (v/sentexes-matching kb '(parentOf Tom Bob) 'NaturalWorldContext)))
        r   (GET (str "/why/" bob))]
    (is (= 200 (:status r)))
    (is (re-find #"tag-premise" (:body r)))))

(deftest an-unknown-handle-has-no-proof-tree
  (is (re-find #"No sentex" (:body (GET "/why/999999")))))

;; ---- assert: the way in for knowledge the KB does not hold -------------

(deftest the-assert-form-is-reachable-and-not-buried
  (testing "from the menubar, the home page, and a term page"
    (is (re-find #"href=\"/assert\"" (:body (GET "/"))))
    (is (re-find #"Assert a sentex" (:body (GET "/"))))
    (is (re-find #"/assert\?q=" (:body (GET "/term" "q=dog")))))
  (testing "the form itself takes a sentence, a context, and the known-true switch"
    (let [body (:body (GET "/assert"))]
      (is (re-find #"<textarea" body))
      (is (re-find #"name=\"ctx\"" body))
      (is (re-find #"name=\"strength\"" body))
      (is (re-find #":strength :monotonic" body))))
  (testing "opened from a term page it arrives with the term already in it"
    (is (re-find #"\(dog " (:body (GET "/assert" "q=dog"))))
    (is (re-find #"value=\"CoreContext\"" (:body (GET "/assert" "q=CoreContext"))))))

(tu/deftest-kb asserting-through-the-form-stores-the-sentence
  (tu/with-terms [likesOf Alice Bob NewContext]
    (let [r (POST "/assert" {"text" (str (pr-str (list likesOf Alice Bob)) "\n"
                                         (pr-str (list likesOf Bob Alice)))
                             "ctx"  (str NewContext)
                             "strength" "monotonic"}
              {"host" "localhost:3000" "origin" "http://localhost:3000"})]
      (is (= 200 (:status r)))
      (is (re-find #"Stored" (:body r)))
      (testing "both lines landed, known-true, in one settle"
        (is (seq (v/sentexes-matching kb (list likesOf Alice Bob) NewContext)))
        (is (seq (v/sentexes-matching kb (list likesOf Bob Alice) NewContext)))
        (is (= :monotonic (:strength (v/sentex kb (v/handle-of kb (list likesOf Alice Bob)
                                                               NewContext)))))))))

(tu/deftest-kb the-assert-form-checks-before-it-writes
  (tu/with-terms [likesOf Alice NewContext]
    (testing "a line that assert would refuse is reported with its type, and stores nothing"
      (let [r (POST "/assert" {"text" (str (pr-str (list likesOf Alice 'Carol)) "\n"
                                           (pr-str (list likesOf Alice '?x)))
                               "ctx"  (str NewContext)}
                {"host" "localhost:3000" "origin" "http://localhost:3000"})]
        (is (= 200 (:status r)))
        (is (re-find #"not-ground" (:body r)))
        (is (re-find #"line 2" (:body r)) "the problem points at the line it came from")
        (testing "and the good line on the same form was not written either"
          (is (empty? (v/sentexes-matching kb (list likesOf Alice 'Carol) NewContext))))))
    (testing "an unreadable line is reported, not thrown"
      (let [r (POST "/assert" {"text" "(((" "ctx" (str NewContext)}
                {"host" "localhost:3000" "origin" "http://localhost:3000"})]
        (is (= 200 (:status r)))
        (is (re-find #"unreadable" (:body r)))))
    (testing "a context that is not a symbol at all is refused before anything is read"
      (let [r (POST "/assert" {"text" "(dog Muffet)" "ctx" "42"}
                {"host" "localhost:3000" "origin" "http://localhost:3000"})]
        (is (re-find #"shape" (:body r)))
        (is (re-find #"the context must be a bare symbol" (:body r)))))
    (testing "a context that is a symbol but not a context name fails the naming invariant"
      (let [r (POST "/assert" {"text" "(dog Muffet)" "ctx" "wrong"}
                {"host" "localhost:3000" "origin" "http://localhost:3000"})]
        (is (re-find #"naming" (:body r)))))))

(tu/deftest-kb the-editor-shows-a-check-problem-beside-the-line
  (tu/with-terms [likesOf Alice Bob EditContext]
    (let [h (v/assert kb (list likesOf Alice Bob) EditContext)
          ;; a syntactically fine `[sentence context]` that `assert` would still refuse
          r (POST "/edit" {"handles" (str h)
                           "text" (pr-str [(list likesOf Alice '?x) EditContext])})]
      (is (= 200 (:status r)))
      (is (re-find #"not-ground" (:body r)))
      (is (re-find #"line 1" (:body r)))
      (is (v/in? kb h) "the save was refused, so the original is untouched"))))

(tu/deftest-kb a-cross-origin-assert-is-refused
  (tu/with-terms [likesOf Alice Bob NewContext]
    (let [r (POST "/assert" {"text" (pr-str (list likesOf Alice Bob)) "ctx" (str NewContext)}
              {"host" "localhost:3000" "origin" "http://evil.example"})]
      (is (= 403 (:status r)))
      (is (empty? (v/sentexes-matching kb (list likesOf Alice Bob) NewContext))))))

;; ---- retract: what will go, said before it goes ------------------------

(tu/deftest-kb the-retract-preview-names-the-consequences-and-writes-nothing
  (tu/with-terms [aP cP X RetractContext]
    (v/assert-rule kb [(list aP '?x)] (list cP '?x) RetractContext)
    (let [fa (v/assert kb (list aP X) RetractContext)
          ch (v/handle-of kb (list cP X) RetractContext)
          r  (GET "/retract" (str "handles=" fa))]
      (is (some? ch) "the rule derived the consequent")
      (is (= 200 (:status r)))
      (testing "the panel says what is selected and what the sweep would take with it"
        (is (re-find #"Retract 1 sentex" (:body r)))
        (is (re-find #"lose their last witness" (:body r)))
        (is (re-find (re-pattern (name cP)) (:body r))))
      (testing "dependency-directedness is stated, not assumed"
        (is (re-find #"dependency-directed" (:body r))))
      (testing "and the GET wrote nothing"
        (is (v/in? kb fa))
        (is (v/in? kb ch))))))

(tu/deftest-kb retracting-the-selection-takes-its-consequences-with-it
  (tu/with-terms [aP cP X RetractContext]
    (v/assert-rule kb [(list aP '?x)] (list cP '?x) RetractContext)
    (let [fa (v/assert kb (list aP X) RetractContext)
          ch (v/handle-of kb (list cP X) RetractContext)
          r  (POST "/retract" {"handles" (str fa)}
               {"host" "localhost:3000" "origin" "http://localhost:3000"})]
      (is (= 200 (:status r)))
      (is (re-find #"Retracted" (:body r)))
      (testing "both the premise and its solely-supported conclusion are gone"
        (is (nil? (v/sentex kb fa)))
        (is (nil? (v/sentex kb ch))))
      (testing "and every row that is actually gone is deleted out of band"
        (is (re-find (re-pattern (str "delete:\\[data-h=&apos;" fa "&apos;\\]")) (:body r)))
        (is (re-find (re-pattern (str "delete:\\[data-h=&apos;" ch "&apos;\\]")) (:body r))))
      (testing "and the selection count is corrected"
        (is (re-find #"id=\"sx-count\"" (:body r)))))))

(tu/deftest-kb a-cross-origin-retract-is-refused
  (tu/with-terms [aP X RetractContext]
    (let [fa (v/assert kb (list aP X) RetractContext)
          r  (POST "/retract" {"handles" (str fa)}
               {"host" "localhost:3000" "origin" "http://evil.example"})]
      (is (= 403 (:status r)))
      (is (v/in? kb fa) "nothing was torn down"))))

(deftest retraction-is-not-reachable-by-a-get
  (testing "the GET route previews only — a KB-changing verb is never a navigation"
    (let [r (GET "/retract" "handles=1")]
      (is (= 200 (:status r)))
      (is (not (re-find #"Retracted<" (:body r)))))))

(tu/deftest-kb a-stale-retract-answers-the-problem-not-a-success-panel
  ;; The page rendered while the handle was live and somebody else retracted it — the
  ;; POST then names a handle the KB no longer stores.  The write is preceded by the
  ;; `check-edit` round-trip every other write post makes, so the answer is the problem
  ;; (`:unknown-handle`) rather than a success-styled "Retracted 0 sentexes" — and
  ;; rather than `edit`'s own refusal, which the browser has no middleware to catch.
  (tu/with-terms [aP X RetractContext]
    (let [fa (v/assert kb (list aP X) RetractContext)]
      (v/retract! kb fa)
      (let [r (POST "/retract" {"handles" (str fa)}
                {"host" "localhost:3000" "origin" "http://localhost:3000"})]
        (is (= 200 (:status r)) "a refusal is a panel, not an error status")
        (testing "the panel reports the problem in check-edit's vocabulary"
          (is (re-find #"Not retracted" (:body r)))
          (is (re-find #"unknown-handle" (:body r)))
          (is (re-find #"Nothing was written" (:body r)))
          (is (not (re-find #"Retracted<" (:body r)))))))
    (testing "a live selection still retracts as before"
      (let [fb (v/assert kb (list aP X) RetractContext)
            r  (POST "/retract" {"handles" (str fb)}
                 {"host" "localhost:3000" "origin" "http://localhost:3000"})]
        (is (= 200 (:status r)))
        (is (re-find #"Retracted" (:body r)))
        (is (nil? (v/sentex kb fb)))))))

;; ---- forward chaining, and what a load did ----------------------------

(deftest the-stats-page-reports-and-triggers-forward-chaining
  (let [body (:body (GET "/stats"))]
    (is (re-find #"Forward chaining" body))
    (is (re-find #"run" body))
    (is (re-find #"dropped for a definitional breach" body))
    (testing "the trigger is a POST form, never a link"
      (is (re-find #"hx-post=\"/chain\"" body))
      (is (not (re-find #"href=\"/chain\"" body))))))

(tu/deftest-kb running-forward-chaining-reports-what-it-derived
  (let [r (POST "/chain" {} {"host" "localhost:3000" "origin" "http://localhost:3000"})]
    (is (= 200 (:status r)))
    (is (re-find #"Forward chaining derived" (:body r)))
    (is (re-find #"Statistics" (:body r)) "and answers with the stats it changed")))

(deftest a-cross-origin-chain-is-refused
  (is (= 403 (:status (POST "/chain" {} {"host" "localhost:3000"
                                         "origin" "http://evil.example"})))))

;; ---- the served handler: the Host allowlist wraps every route ------------
;;
;; `web/app` is the routing half and what every other test here drives — what gets
;; *served* is `web/handler`, which adds the `Host` allowlist.  These build the
;; wrapped value, because the wrap is what they are about: `same-origin?` folds under
;; DNS rebinding (the attacker's page is genuinely same-origin with a domain that
;; re-resolved to 127.0.0.1), and `host-allowed?` is the check that does not.

(tu/deftest-kb the-served-handler-refuses-a-rebound-host-on-every-route
  (let [served (web/handler kb)]
    (testing "a GET under a rebound Host is refused — reading the KB is what rebinding is for"
      (let [r (served {:request-method :get :uri "/"
                       :headers {"host" "evil.example.com"}})]
        (is (= 400 (:status r)))
        (is (re-find #"unrecognized Host" (:body r)))))
    (testing "a write route is refused the same way, before it writes — and with a
              matching Origin, which is precisely the header pair rebinding forges"
      (let [n (v/sentex-count kb)
            r (served {:request-method :post :uri "/chain" :scheme :http
                       :headers {"host"   "evil.example.com"
                                 "origin" "http://evil.example.com"}})]
        (is (= 400 (:status r)))
        (is (= n (v/sentex-count kb)) "forward chaining never ran")))
    (testing "the browser's own names still pass"
      (doseq [h ["localhost:3000" "127.0.0.1:3000" "[::1]:3000"]]
        (is (= 200 (:status (served {:request-method :get :uri "/"
                                     :headers {"host" h}})))
            h)))
    (testing "no Host at all passes by design — a non-browser client, and what makes
              driving bare `web/app` elsewhere in this namespace equivalent"
      (is (= 200 (:status (served {:request-method :get :uri "/"})))))))

;; ---- -main's argument grammar --------------------------------------------

(deftest a-truncated-listen-flag-is-refused-not-bound-wide
  ;; The stake: `run-jetty` treats a nil `:host` as the wildcard address, and
  ;; `guard/allowed-hosts` treats a nil listen host as `::any` — so a `--listen`
  ;; whose address was lost to a truncated command line would bind the browser's
  ;; unauthenticated write routes on every interface with the rebinding guard off,
  ;; while the public-bind warning reads as though the operator asked for it.
  (testing "absent, the browser binds loopback"
    (is (= "127.0.0.1" (:host (#'web/parse-args [])))))
  (testing "present with an address, it binds that address"
    (is (= "0.0.0.0" (:host (#'web/parse-args ["--listen" "0.0.0.0"])))))
  (testing "present with nothing after it, it is refused"
    (let [e (is (thrown? clojure.lang.ExceptionInfo (#'web/parse-args ["--listen"])))]
      (is (= :unknown-option (:type (ex-data e))))
      (is (= "--listen" (:flag (ex-data e))))))
  (testing "--port with no value, or a non-number, is refused the same way"
    (is (thrown? clojure.lang.ExceptionInfo (#'web/parse-args ["--port"])))
    (let [e (is (thrown? clojure.lang.ExceptionInfo (#'web/parse-args ["--port" "eighty"])))]
      (is (= :unknown-option (:type (ex-data e))))))
  (testing "a token the table does not know is refused, not skipped"
    (let [e (is (thrown? clojure.lang.ExceptionInfo (#'web/parse-args ["--liste" "0.0.0.0"])))]
      (is (= :unknown-option (:type (ex-data e))))
      (is (= "--liste" (:flag (ex-data e))))))
  (testing "--attach still parses, with and without the optional web port"
    ;; the bare-default port is whatever `default-port` reads, not a literal: a
    ;; developer with VAELII_WEB_PORT set in their shell must not fail this suite.
    (let [dflt (#'web/default-port)]
      (is (= {:host "127.0.0.1" :port dflt :attach ["h" 4200]}
             (select-keys (#'web/parse-args ["--attach" "h" "4200"]) [:host :port :attach])))
      (is (= {:host "127.0.0.1" :port 8080 :attach ["h" 4200]}
             (select-keys (#'web/parse-args ["--attach" "h" "4200" "8080"]) [:host :port :attach])))
      (is (= {:host "0.0.0.0" :port dflt :attach ["h" 4200]}
             (select-keys (#'web/parse-args ["--attach" "h" "4200" "--listen" "0.0.0.0"])
                          [:host :port :attach]))))))

(deftest the-web-port-variable-moves-main-and-not-only-the-repl-browser
  ;; `dev-repl` read VAELII_WEB_PORT and `-main` did not, while the docs said the
  ;; variable moves "it" off 3000 without saying which.  A variable that is honoured
  ;; by one entry point and ignored by the other reads as set and lands on 3000 —
  ;; which is how an operator asking for a spare port takes the default one instead.
  ;; A JVM cannot set its own environment, so the property is the testable half of
  ;; the same read (docs/catalog.md's `vaelii.kb.path` shape).
  (let [prop "vaelii.web.port"
        prior (System/getProperty prop)]
    (try
      (System/clearProperty prop)
      (testing "nothing set anywhere, and the port is 3000"
        (when-not (System/getenv "VAELII_WEB_PORT")
          (is (= 3000 (#'web/default-port)))
          (is (= 3000 (:port (#'web/parse-args []))))))
      (testing "the default source moves the port -main takes"
        (System/setProperty prop "3311")
        (is (= 3311 (#'web/default-port)))
        (is (= 3311 (:port (#'web/parse-args []))))
        (is (= 3311 (:port (#'web/parse-args ["--listen" "0.0.0.0"])))))
      (testing "an explicit --port still wins over it"
        (System/setProperty prop "3311")
        (is (= 8080 (:port (#'web/parse-args ["--port" "8080"]))))
        (is (= 8080 (:port (#'web/parse-args ["--attach" "h" "4200" "8080"])))))
      (testing "a value that does not parse falls through rather than failing startup"
        (System/setProperty prop "notanumber")
        (when-not (System/getenv "VAELII_WEB_PORT")
          (is (= 3000 (#'web/default-port)))))
      (finally
        (if prior (System/setProperty prop prior) (System/clearProperty prop))))))

(deftest the-kbs-page-renders-its-available-list-and-says-when-it-was-cut
  ;; The Available list is built from `catalog/sources`, whose search-path probe caps
  ;; at `max-discovered`.  A cap nobody is told about reads as "this machine has no
  ;; other KBs" — the one answer a KB list must not give by accident — so the note is
  ;; the half worth pinning, and the page rendering at all is the half that was
  ;; previously untested.
  (testing "the page renders, with a card per source"
    (let [r (GET "/kbs")]
      (is (= 200 (:status r)))
      (is (str/includes? (:body r) "Available"))
      (is (str/includes? (:body r) "Knowledge bases"))))
  (testing "an uncut probe says nothing about a cut"
    (with-redefs [cat/sources (fn [] (with-meta [] {:truncated []}))]
      (is (not (str/includes? (:body (GET "/kbs")) "are not shown")))))
  (testing "a cut probe names the directory and the number passed over"
    ;; `sources` is a plain var the page derefs, so redefining it reaches the call
    (with-redefs [cat/sources (fn [] (with-meta []
                                       {:truncated [{:dir "/some/kbs"
                                                     :passed-over 51
                                                     :probed cat/max-discovered}]}))]
      (let [body (:body (GET "/kbs"))]
        (is (str/includes? body "/some/kbs"))
        (is (str/includes? body "51 more are not shown"))
        (is (str/includes? body (str "first " cat/max-discovered " entries")))))))
