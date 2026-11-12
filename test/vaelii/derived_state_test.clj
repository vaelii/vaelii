;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.derived-state-test
  "The derived-state register (`caches/register-derived`, docs/caches.md) checked against
  what the writes move.  Each event's vars (`caches/events`) are wrapped; every row is read
  at each wrapped call's entry and exit, and a row that moved between two reads is charged
  to the innermost event open at the time.  The test fails on a row that moved under an
  event its `:retired-by` does not name."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.pprint :as pprint]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [deftest is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.starter :as starter]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.reasoning-image :as ri]
            [vaelii.impl.recovery :as recovery]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.stp]
            [vaelii.test-util :as tu])
  (:import [java.io File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]
           [vaelii.impl.observe HeldAtom]))

(use-fixtures :each (tu/neutral-fresh tu/empty-kb))

(def ^:private U 'CxUniverse)
(def ^:private mono {:strength :monotonic})

;; ---- the instrument --------------------------------------------------------

(defn- observed-rows
  "Every registered row a value can be read from: all but the `:pass` rows."
  []
  (remove #(= :pass (:kind %)) (:rows (caches/derived-state))))

(defn- instrumented
  "Run `(f)` under `caches/with-tally` over `kb` (or the first KB an event is handed, when
  `kb` is nil), and answer what it recorded: the events fired, the `[row event]` pairs
  seen moving, the moves no event is charged to, and the violations."
  [kb f]
  (let [obs (atom {:seen #{} :violations [] :read-moves #{}})
        out (caches/with-tally
              kb {:observe (fn [{:keys [id retired-by]} charged]
                             (let [hit (set/intersection charged (set (keys retired-by)))]
                               (swap! obs update :seen into (map #(vector id %)) hit)
                               (when (empty? charged)
                                 (swap! obs update :read-moves conj id))
                               (when (and (seq charged) (empty? hit))
                                 (swap! obs update :violations conj
                                        {:row id :charged charged
                                         :declared (sort (keys retired-by))}))))}
              f)]
    (assoc @obs :fired (set (keys (:fired out))) :retired (:retired out))))

(defn- report
  "The violations, each as one line."
  [{:keys [violations]}]
  (->> violations
       (map (fn [{:keys [row charged declared]}]
              (str (name row) " moved under " (str/join " " (map name (sort charged)))
                   ", which its :retired-by (" (str/join " " (map name declared))
                   ") does not name")))
       distinct
       (str/join "\n")))

;; ---- the drivers -----------------------------------------------------------

(defn- default-rule [antes conseq]
  (list 'set/defaultRule (list 'set/forwardRule (list 'implies (cons 'and antes) conseq))))

(defn- scenario!
  "Drive every write event except the image install on `kb`, which it closes."
  [kb]
  (tu/with-terms [dog animal Rex aa bb hi lo pp qq rr Zed CxA CxB likes cat_kind feline
                  carriesLoad hauler_kind cart_kind on_kind on_dog bRel Amy]
    (let [fact  (v/assert kb (list dog Rex) U)
          edge  (v/assert kb (list 'genl dog animal) U)]
      (v/assert kb (list 'genlCx CxA U) U mono)
      (v/assert kb (list 'genlCx CxB CxA) U mono)
      (v/assert kb (list 'disjoint aa bb) U)
      (v/assert kb (list 'sameAs hi lo) U)
      ;; a rule whose guard a later fact moves, read at a reader below its placement
      (v/assert kb (list 'exceptWhen (list qq '?x)
                         (list 'set/forwardRule (list 'implies (list pp '?x) (list rr '?x))))
                CxA)
      (v/assert kb (list pp Zed) CxA)
      (v/assert kb (list qq Zed) CxB)
      (v/ask? kb (list rr Zed) CxB)
      ;; an except of a rule, arriving and leaving
      (let [rh (v/assert kb (default-rule [(list cat_kind '?x)] (list feline '?x)) U)
            eh (v/assert kb (list 'except (sx/sentex-handle rh)) U)]
        (v/retract! kb eh))
      (v/assert kb (list 'forced_monotonic_predicate likes) U)
      ;; an inherited clash
      (v/assert kb (list 'binary_predicate carriesLoad) U)
      (v/assert kb (list 'transitiveInArgInverse carriesLoad 1 'genl) U mono)
      (v/assert kb (list 'genl hauler_kind animal) U)
      (v/assert kb (list 'genl cart_kind hauler_kind) U)
      (v/assert kb (list carriesLoad hauler_kind 'Bone1) U mono)
      (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) U)
      (v/conflicts kb)
      ;; a withdrawal at its own context
      (v/assert kb (list 'genl on_kind on_dog) U)
      (v/assert kb (list 'not (list 'genl on_kind on_dog)) U mono)
      ;; a late symmetric mark re-spells a stored row
      (v/assert kb (list bRel 'TmpZed Amy) U)
      (v/assert kb (list 'symmetric bRel) U)
      (v/retract! kb edge)
      (v/retract! kb fact)
      (v/clear-caches kb)
      (v/recover kb)
      (v/reindex kb)
      (v/clear! kb)
      (v/close! kb))))

(defn- scenario-kb []
  (v/open-kb {:backend :memory :space [::scenario] :recover? false}))

;; ---- the claims ------------------------------------------------------------

(deftest every-row-declares-closed-values
  (let [{:keys [rows events]} (caches/derived-state)
        ids (set (map :id rows))]
    (is (<= 61 (count rows)))
    (is (= [] (for [{:keys [id reads]} rows r reads
                    :when (not (or (ids r) (caches/stores r)))]
                [id r]))
        "a row reads only rows and stores")
    (is (= (range 1 (inc (count events))) (map :n events)))))

(deftest the-image-carries-the-fields-the-register-images
  (is (= (set (ri/state-atoms)) (caches/image-fields :state)))
  (is (empty? (caches/image-fields :cache))))

(deftest the-image-reads-the-register-at-the-call-and-not-at-load
  ;; a row registers when its namespace loads, so a read at load misses a later namespace:
  ;; `reasoning-image` required alone holds 2 of the 7 fields.
  (with-redefs [caches/image-fields (constantly #{:a-field-registered-later})]
    (is (= [:a-field-registered-later] (ri/state-atoms)))
    (is (not (contains? (ri/unimaged-atoms) :a-field-registered-later)))))

(deftest a-row-moves-only-under-an-event-it-declares
  (let [{:keys [fired seen] :as st} (let [kb (scenario-kb)] (instrumented kb #(scenario! kb)))
        declared (set (for [r (observed-rows) e (keys (:retired-by r))] [(:id r) e]))]
    (is (= "" (report st)))
    (is (= (disj (set (keys caches/events)) :image-install) fired)
        "the scenario drives every event but the image install")
    (println "derived-state: declared pairs no event moved:"
             (count (set/difference declared seen)) "of" (count declared))))

;; ---- the keys of a keyed map -----------------------------------------------

(defn- keyed-fields
  "The `Reasoning` fields some row locates by a key inside them: each such field's map
  holds the entries of several rows, told apart by key."
  []
  (set (for [r (:rows (caches/derived-state)) [f :as at] (:at r) :when (next at)] f)))

(defn- key-shape
  "Key `k` with every symbol in it, a reader, written `::caches/reader`, as a location
  writes it."
  [k]
  (cond (symbol? k) ::caches/reader
        (vector? k) (mapv key-shape k)
        :else       k))

(def ^:private not-derived-keys
  "`{[field key] reason}`: the keys of a keyed map that hold no derived state."
  {[:taxonomy :supporter-filter-active?] "a callback `tax/install-supporter-visibility!` sets"
   [:taxonomy :supporter-visible?]       "a callback `tax/install-supporter-visibility!` sets"
   [:taxonomy :network-filter-active?]   "a callback `tax/install-supporter-visibility!` sets"
   [:taxonomy :network-visible?]         "a callback `tax/install-supporter-visibility!` sets"
   [:taxonomy :supporter-reaches?]       "a callback `tax/install-supporter-visibility!` sets"
   [:taxonomy :supporter-sentence]       "a callback `tax/install-supporter-visibility!` sets"
   [:taxonomy :index]                    "the index store the supporter families live in, which `tax/install-index!` sets"
   [:taxonomy :raw?]                     "whether `:index` is a raw taxonomy's own store, which `tax/install-index!` clears"})

(defn- uncovered
  "`{field #{shape}}` cut to the shapes no row's `:at` names as `[field shape …]` and
  `not-derived-keys` does not name."
  [seen]
  (let [named (into (set (keys not-derived-keys))
                    (for [r (:rows (caches/derived-state)) [f k :as at] (:at r) :when (next at)]
                      [f k]))]
    (into {} (keep (fn [[f shapes]]
                     (let [u (into (sorted-set-by #(compare (str %1) (str %2)))
                                   (remove #(named [f %])) shapes)]
                       (when (seq u) [f u]))))
          seen)))

(defn- watching-keys
  "Run `(f)`, collecting into `seen` the key shapes every map at a keyed field of `kb`
  holds after each of its writes.  A held field is watched through the atom it writes
  to, and the field atoms of the `Reasoning` value a recover installs in turn.
  Every watch is removed when `(f)` returns."
  [kb seen f]
  (let [fields  (keyed-fields)
        watched (atom #{})
        note    (fn note [field _ _ _ m]
                  (when (map? m)
                    (swap! seen update field (fnil into #{}) (map key-shape (keys m)))))
        attach  (fn []
                  (doseq [field fields
                          :let [x (get @(:reasoning kb) field)
                                a (if (instance? clojure.lang.IRef x) x (.-a ^HeldAtom x))]]
                    (swap! watched conj a)
                    (note field nil nil nil @a)
                    (add-watch a ::keys (partial note field))))
        install @#'recovery/install-rebuilt!]
    (attach)
    (try
      (with-redefs [recovery/install-rebuilt! (fn [& args]
                                                (let [out (apply install args)] (attach) out))]
        (f))
      (finally (doseq [a @watched] (remove-watch a ::keys))))))

(deftest every-key-of-a-keyed-map-belongs-to-a-row
  (let [seen (atom {})
        kb   (scenario-kb)]
    (is (= #{:mint-queues :nogood-candidates :taxonomy} (keyed-fields)))
    (watching-keys kb seen #(scenario! kb))
    (is (= {} (uncovered @seen))
        "each key shape a scenario write left in a keyed map is a location of a row")
    (is (< 50 (reduce + (map count (vals @seen)))) "the watches saw the scenario's writes")))

(tu/deftest-kb an-unregistered-key-in-a-keyed-map-is-reported
  (let [seen (atom {})]
    (watching-keys kb seen #(swap! (:nogood-candidates @(:reasoning kb)) assoc ::sabotage 1))
    (swap! (:nogood-candidates @(:reasoning kb)) dissoc ::sabotage)
    (is (= {:nogood-candidates #{::sabotage}} (uncovered @seen)))))

(deftest an-image-install-moves-only-what-it-declares
  (tu/with-snapshot-platform
    (let [dir (str (Files/createTempDirectory "vaelii-derived-state-" (into-array FileAttribute [])))]
      (try
        (let [kb (v/open-kb {:backend :disk-snapshot :dir dir})]
          (tu/with-terms [dog animal Rex]
            (v/assert kb (list 'genl dog animal) U mono)
            (v/assert kb (list dog Rex) U))
          (v/close! kb))
        (let [st (instrumented nil #(v/close! (v/open-kb {:backend :disk-snapshot :dir dir})))]
          (is (= "" (report st)))
          (is (contains? (:fired st) :image-install)))
        (finally
          (doseq [f (reverse (file-seq (io/file dir)))] (.delete ^File f)))))))

;; ---- the counters ----------------------------------------------------------

(defn- counts [kb id] (caches/tally-map (caches/row-tally kb id)))

(defn- delta [before after k] (- (long (get after k 0)) (long (get before k 0))))

(tu/deftest-kb a-repeated-read-hits-and-a-write-it-does-not-name-misses-spuriously
  (tu/with-terms [likes Amy Bob Cy sky_blue]
    (v/assert kb (list likes Amy Bob) U)
    (let [ask #(doall (v/prove kb (list likes Amy '?x) U))
          _   (ask)
          a   (counts kb :R1)
          _   (ask)
          b   (counts kb :R1)]
      (is (pos? (delta a b :hits)) "a repeated read hits")
      (is (zero? (delta a b :misses)))
      (caches/with-tally
        kb nil
        (fn []
          (let [c (counts kb :R1)
                _ (v/assert kb (list likes Amy Cy) U)
                _ (ask)
                d (counts kb :R1)
                _ (v/assert kb (list sky_blue Amy) U)
                _ (ask)
                e (counts kb :R1)]
            (is (pos? (delta c d :misses)) "a write naming the key misses")
            (is (pos? (delta c d :recompute-ns)))
            (is (< (delta c d :spurious) (delta c d :compared))
                "and its recompute differs from what it replaced")
            (is (pos? (delta d e :spurious)) "a write not naming it misses spuriously")
            (is (= (delta d e :spurious) (delta d e :compared))
                "and every recompute it forced returned the value it replaced"))))
      (let [f (counts kb :R1)]
        (v/assert kb (list likes Bob Cy) U)
        (ask)
        (is (= (:compared f) (:compared (counts kb :R1)))
            "with the instrument off, no miss is compared")))))

(tu/deftest-kb an-event-s-retirement-count-is-the-entries-it-dropped
  (tu/with-terms [dog animal likes Amy Bob CxA CxB]
    (v/assert kb (list 'genlCx CxA U) U mono)
    (v/assert kb (list 'genlCx CxB CxA) U mono)
    (v/assert kb (list 'genl dog animal) CxA)
    (v/assert kb (list likes Amy Bob) CxA)
    (v/ask? kb (list 'genl dog animal) CxB)
    (doall (v/prove kb (list likes Amy '?x) CxB))
    (let [live (count (caches/derived-value kb :R1))
          r1   (:retired (counts kb :R1))
          out  (caches/with-tally kb nil #(v/clear-caches kb))]
      (is (pos? live))
      (is (= 1 (get-in out [:fired :caches-cleared])))
      (is (= live (get-in out [:retired [:caches-cleared :R1]]))
          "a clear retires every literal entry current under the clock")
      (is (= live (- (:retired (counts kb :R1)) r1))
          "and the row's own tally counts the same entries"))))

(tu/deftest-kb the-instrument-wraps-only-the-events-it-is-given
  (tu/with-terms [likes Amy Bob]
    (let [out (caches/with-tally kb {:events [:caches-cleared]}
                #(do (v/assert kb (list likes Amy Bob) U)
                     (v/clear-caches kb)))]
      (is (= {:caches-cleared 1} (:fired out))))))

(tu/deftest-kb the-ranking-orders-rows-by-spurious-cost-and-by-hit-rate
  (tu/with-terms [likes Amy Bob sky_blue]
    (v/assert kb (list likes Amy Bob) U)
    (caches/with-tally kb nil
      #(dotimes [_ 3]
         (doall (v/prove kb (list likes Amy '?x) U))
         (v/assert kb (list sky_blue (gensym "TmpSky")) U)))
    (let [{:keys [by-spurious-cost by-hit-rate]} (caches/tally-ranking kb)
          costs (keep :spurious-cost by-spurious-cost)
          rates (keep :hit-rate by-hit-rate)]
      (is (some #(= :R1 (:row %)) by-spurious-cost))
      (is (pos? (:spurious-fraction (first (filter #(= :R1 (:row %)) by-spurious-cost)))))
      (is (= costs (sort > costs)))
      (is (= rates (sort rates)))
      (is (= (set (map :row by-spurious-cost)) (set (map :row by-hit-rate)))))))

;; ---- the generated table ---------------------------------------------------

(def ^:private doc-file "docs/caches.md")
(def ^:private begin-mark "<!-- derived-state register: generated by `lein regen-goldens` -->")
(def ^:private end-mark "<!-- end of the generated register -->")

(defn- ev-id [event] (str "E" (:n (caches/events event))))

(defn- retired-cell
  "A row's `:retired-by` as `E7 K, E8 G`, or `every other event G*` for the code it
  gives most events when that is all of them but a few.  An empty one reads `P` for a
  pass row and `C` for any other: nothing but its scope or its bound retires it."
  [kind retired-by]
  (let [n        (count caches/events)
        [c k]    (when (seq retired-by)
                   (apply max-key val (frequencies (vals retired-by))))
        common?  (and c (< (- n 5) k) (= n (count retired-by)))
        listed   (->> retired-by
                      (remove (fn [[_ code]] (and common? (= code c))))
                      (sort-by (comp :n caches/events key))
                      (map (fn [[e code]] (str (ev-id e) " " (name code)))))]
    (if (empty? retired-by)
      (if (= :pass kind) "P" "C")
      (str/join ", " (cond-> (vec listed)
                       common? (conj (str (if (seq listed) "every other event " "every event ")
                                          (name c))))))))

(defn- cell [x] (str/replace (str x) "|" "\\|"))

(defn markdown
  "The register as the two tables of docs/caches.md's generated section: the rows, then
  the events with the rows each one retires."
  []
  (let [{:keys [rows events]} (caches/derived-state)
        by-event (reduce (fn [m {:keys [id retired-by]}]
                           (reduce #(update %1 %2 (fnil conj []) (name id)) m (keys retired-by)))
                         {} rows)]
    (str/join
     "\n"
     (concat
      ["| id | structure | owner | keyed by | reads | retired by | computed | kind | image | cache | content |"
       "|---|---|---|---|---|---|---|---|---|---|---|"]
      (for [{:keys [id label owner keyed-by reads retired-by computed kind imaged? cache
                    holds-content?]} rows]
        (str "| " (name id) " | " (cell label) " | `" (str/replace owner "vaelii.impl." "")
             "` | " (name keyed-by) " | " (str/join " " (map name reads)) " | "
             (retired-cell kind retired-by) " | " (name computed) " | " (name kind) " | "
             (if imaged? (name imaged?) "no") " | " (if cache (str "`" cache "`") "") " | "
             (if holds-content? "yes" "") " |"))
      [""
       "| id | event | choke points | names | rows it retires |"
       "|---|---|---|---|---|"]
      (for [{:keys [event at names]} events]
        (str "| " (ev-id event) " | `" (name event) "` | "
             (str/join ", " (map #(str "`" (str/replace (str %) "vaelii.impl." "") "`") at))
             " | " (cell names) " | " (str/join " " (by-event event)) " |"))))))

(defn- doc-block
  "The generated section of docs/caches.md as it stands, or nil."
  []
  (let [doc (slurp doc-file)
        a   (str/index-of doc begin-mark)
        b   (str/index-of doc end-mark)]
    (when (and a b) (str/trim (subs doc (+ a (count begin-mark)) b)))))

(defn regenerate-golden!
  "Rewrite docs/caches.md's generated section from the register."
  []
  (let [doc (slurp doc-file)
        a   (str/index-of doc begin-mark)
        b   (str/index-of doc end-mark)]
    (spit doc-file (str (subs doc 0 (+ a (count begin-mark))) "\n\n" (markdown) "\n\n"
                        (subs doc b)))))

(deftest the-caches-doc-holds-the-register
  (is (= (markdown) (doc-block))
      "docs/caches.md's register section is generated: run `lein regen-goldens`"))

;; ---- the export the dependency graph is drawn from ------------------------

(def ^:private export-row-keys
  #{:id :label :owner :kind :holds-content? :keyed-by :reads :retired-by :computed :imaged?
    :cache :bound :note :var})

(def ^:private export-event-keys #{:event :n :names})

(defn- count-map?
  "A map of ids to numbers: a counter per event or per row."
  [x]
  (and (map? x) (seq x) (every? keyword? (keys x)) (every? number? (vals x))))

(defn- keep-fields
  "`m` cut to `allowed` keys plus every number and every `count-map?`, so a counter a
  row or event gains is carried and nothing else is."
  [allowed m]
  (into {} (filter (fn [[k x]] (or (allowed k) (number? x) (count-map? x)))) m))

(defn- registration-site
  "`path:line` of the `register-derived` call that declares row `id` in namespace `owner`."
  [owner id]
  (let [path (str (-> owner (str/replace "-" "_") (str/replace "." "/")) ".clj")
        re   (re-pattern (str "\\{:id " id "(?![0-9])"))]
    (when-let [r (io/resource path)]
      (some (fn [[i line]] (when (re-find re line) (str path ":" (inc i))))
            (map-indexed vector (str/split-lines (slurp r)))))))

(defn- held
  "How many entries a row holds in `kb`: the count of its value, summed over its
  locations where the value is one per location, or nil for a row whose value is not a
  collection or cannot be read."
  [kb {:keys [id at]}]
  (let [x (try (caches/derived-value kb id) (catch Throwable _ nil))
        n #(when (coll? %) (count %))]
    (if (and (next at) (vector? x))
      (let [counts (keep n x)] (when (seq counts) (reduce + counts)))
      (n x))))

(defn- locations [at] (mapv #(str/join " " (map pr-str %)) at))

(defn- git-revision
  "`{:revision short-hash :dirty n}`: n counts the files under `REVISION_PATHS`
  (`scripts/lib/revision.sh`) that differ from that revision."
  []
  (let [git #(str/trim (:out (apply shell/sh "git" %&)))]
    {:revision (let [h (git "rev-parse" "--short" "HEAD")] (if (str/blank? h) "no-git" h))
     :dirty    (->> ["src" "test" "resources" "bench" "project.clj" "project-env.clj"]
                    (apply git "status" "--porcelain" "--")
                    str/split-lines (remove str/blank?) count)}))

(defn export
  "The register over `kb` as the dependency graph reads it: row ids, event ids, codes,
  each row's registration site, and the numbers a row or event carries (`:entries`,
  `:held`, and any counter).  Every other value is dropped, so the export holds no handle
  and no sentence.  `source` names the run the KB holds."
  [kb source]
  (let [{:keys [rows events edges]} (caches/derived-state kb)]
    (merge (git-revision)
           {:format 1
            :taken  (str (java.time.Instant/now))
            :source source
            :codes  caches/codes
            :kinds  (vec (sort caches/kinds))
            :stores (vec (sort caches/stores))
            :rows   (mapv (fn [r]
                            (let [h (held kb r)]
                              (cond-> (assoc (keep-fields export-row-keys r)
                                             :site (registration-site (:owner r) (:id r)))
                                (:at r) (assoc :at (locations (:at r)))
                                h       (assoc :held h))))
                          rows)
            :events (mapv (fn [e] (assoc (keep-fields export-event-keys e) :at (mapv str (:at e))))
                          events)
            :edges  edges})))

(defn- starter-export
  "The export over a private memory KB holding the starter ontology."
  []
  (let [kb (v/open-kb {:backend :memory :space [::export] :recover? false})]
    (try (starter/load-into kb)
         (export kb "the starter ontology on a memory KB (lein derived-state)")
         (finally (v/clear! kb) (v/close! kb)))))

(deftest the-export-holds-ids-codes-and-counts
  (let [kb (v/open-kb {:backend :memory :space [::export-test] :recover? false})]
    (try
      (tu/with-terms [dog animal Rex]
        (v/assert kb (list 'genl dog animal) U)
        (v/assert kb (list dog Rex) U)
        (let [ex     (export kb "test")
              leaves (remove coll? (tree-seq coll? seq ex))]
          (is (= ex (edn/read-string (pr-str ex))))
          (is (empty? (filter #(or (symbol? %) (seq? %)) (tree-seq coll? seq ex)))
              "no symbol and no list: a sentence is a list of symbols")
          (is (not-any? #(and (string? %) (str/includes? % (str Rex))) leaves))
          (is (every? #(re-matches #"vaelii/.+\.clj:\d+" (str (:site %))) (:rows ex)))))
      (finally (v/clear! kb) (v/close! kb)))))

(defn -main
  "Print the register: the two tables as markdown.  `--edn` prints the export of a
  starter KB (`export`), and `--edn <path>` writes it to `path`, which
  `scripts/derived-state-graph.py` draws."
  [& args]
  (case (first args)
    "--edn" (let [ex (starter-export)]
              (if-let [path (second args)]
                (do (spit path (with-out-str (pprint/pprint ex)))
                    (println "derived-state: wrote" path "at" (:revision ex) "-"
                             (count (:rows ex)) "rows," (count (:events ex)) "events"))
                (pprint/pprint ex)))
    (println (markdown)))
  (shutdown-agents)
  (System/exit 0))
