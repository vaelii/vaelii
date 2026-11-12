;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.koinii-surface-test
  "koinii's surface, frozen against `test/golden/koinii-surface.edn`, apart from the
  engine's goldens: every public var of every `vaelii.koinii.*` namespace with its
  arglists (as `api_surface_test` freezes the API), every refusal `:type` the koinii
  sources raise (read as `type_contract_test` reads the engine's), and the arity of every
  term the seed contexts CxRegistry, CxSpeechActs and CxDisputes declare.

  A removed var, keyword-set member, refusal type or seed term, a changed arglist or a
  changed arity is Breaking (CONTRIBUTING §3.8) with a `*Breaks:*` line naming it; an
  addition is Additive. Both move the golden: write the changelog entry, then run `lein
  regen-goldens` and commit the golden with the change. See docs/koinii.md."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.pprint :as pprint]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.api-surface-test :as api]
            [vaelii.type-contract-test :as tc])
  (:import [java.io File]))

(def ^:private golden-file "test/golden/koinii-surface.edn")

(def ^:private seed-contexts '[CxDisputes CxRegistry CxSpeechActs])

(defn- koinii-files []
  (->> (file-seq (io/file "src/vaelii/koinii"))
       (filter #(.isFile ^File %))
       (map #(str/replace (.getPath ^File %) \\ \/))
       (filter #(str/ends-with? % ".clj"))
       sort))

(defn- koinii-namespaces []
  (map #(-> % (subs (count "src/")) (str/replace #"\.clj$" "")
            (str/replace "/" ".") (str/replace "_" "-") symbol)
       (koinii-files)))

(def ^:private fixed-arity
  "The arity each `*_predicate` arity type in `core.txt` declares."
  '{unary_predicate 1 binary_predicate 2 ternary_predicate 3
    quaternary_predicate 4 quinary_predicate 5})

(def ^:private variable-arity
  '#{variable_arity_predicate variable_arity_function
     unbounded_arity_predicate unbounded_arity_function})

(defn- declared-arities
  "`{term arity}` for one seed file: an integer for a fixed arity, a sorted map of
  `:min`/`:max` for a variable one. A type (a `genl` subject spelled snake_case) has
  arity 1. Throws for a commented term the file gives no arity, so a declaration this
  reader does not know cannot drop a term from the golden."
  [cx]
  (let [forms (edn/read-string (str "[" (slurp (io/resource (str "kb/koinii/" cx ".txt"))) "]"))
        forms (map #(if (and (seq? %) (= 'set/monotonic (first %))) (second %) %) forms)
        arity (reduce
               (fn [m [p t n]]
                 (cond
                   (fixed-arity p)                 (assoc m t (fixed-arity p))
                   (= 'arity p)                    (assoc m t n)
                   (variable-arity p)              (update m t #(or % (sorted-map)))
                   (= 'arityMin p)                 (update m t (fnil assoc (sorted-map)) :min n)
                   (= 'arityMax p)                 (update m t (fnil assoc (sorted-map)) :max n)
                   (and (= 'genl p) (str/includes? (name t) "_")) (assoc m t 1)
                   :else m))
               (sorted-map)
               (filter #(and (seq? %) (symbol? (second %))) forms))
        undeclared (remove arity (keep #(when (= 'comment (first %)) (second %)) forms))]
    (when (seq undeclared)
      (throw (ex-info (str cx " comments " (vec undeclared) " with no arity this reader knows")
                      {:context cx :terms (vec undeclared)})))
    arity))

(defn current-surface
  "`{:vars {ns {var arglists}} :refusal-types [type …] :vocabulary {context {term arity}}}`
  as the tree publishes it today."
  []
  {:vars          (into (sorted-map) (map (juxt identity api/surface-of)) (koinii-namespaces))
   :refusal-types (vec (sort (into #{} (mapcat (comp tc/refusal-types slurp)) (koinii-files))))
   :vocabulary    (into (sorted-map) (map (juxt identity declared-arities)) seed-contexts)})

(defn regenerate-golden!
  "Rewrite `test/golden/koinii-surface.edn` from the tree. Run `lein regen-goldens` after a
  deliberate koinii change, with its changelog entry written first."
  []
  (let [surface (current-surface)]
    (spit golden-file
          (str ";; Frozen koinii surface — the vars of vaelii.koinii.*, the refusal :types its\n"
               ";; sources raise, and the arity of each term its seed contexts declare.\n"
               ";; Regenerate: `lein regen-goldens`, after the changelog entry\n"
               ";; (vaelii.koinii-surface-test).\n"
               (with-out-str (pprint/pprint surface))))))

(defn- golden [] (edn/read-string (slurp golden-file)))

(defn- entries
  "`{path value}` over a surface: one entry per var, refusal type and seed term."
  [s]
  (merge (into {} (for [[n vars] (:vars s), [v a] vars] [[:vars n v] a]))
         (into {} (for [t (:refusal-types s)] [[:refusal-types t] t]))
         (into {} (for [[cx terms] (:vocabulary s), [t a] terms] [[:vocabulary cx t] a]))))

(defn- moved
  "What moved from surface `was` to surface `now`, each a sorted vector of paths.
  `:breaking` holds a removed entry, a keyword set that lost a member, and any other changed
  value; `:added` holds a new entry and a keyword set that only gained members."
  [was now]
  (let [w (entries was), n (entries now)
        grown? (fn [k] (let [a (w k) b (n k)]
                         (and (vector? a) (vector? b) (set/subset? (set a) (set b)))))
        changed (filter #(and (contains? n %) (not= (w %) (n %))) (keys w))
        sorted (fn [ks] (vec (sort-by pr-str ks)))]
    {:breaking (sorted (concat (remove #(contains? n %) (keys w)) (remove grown? changed)))
     :added    (sorted (concat (remove #(contains? w %) (keys n)) (filter grown? changed)))}))

(deftest the-koinii-surface-is-the-golden
  (let [{:keys [breaking added]} (moved (golden) (current-surface))]
    (is (empty? breaking)
        (str "BREAKING for a caller of vaelii.koinii.*: " breaking ". Restore it, or write the"
             " CONTRIBUTING §3.8 Breaking entry with `*Breaks:*` and `*Migration:*` lines,"
             " then `lein regen-goldens` in the same commit."))
    (is (empty? added)
        (str "koinii's surface grew: " added ". Write the Additive changelog entry, then"
             " `lein regen-goldens` in the same commit."))))

(deftest a-removed-var-a-renamed-type-and-a-changed-arity-are-breaking
  (let [s   (golden)
        ns1 (first (keys (:vars s)))
        v1  (first (keys (get-in s [:vars ns1])))
        t1  (first (:refusal-types s))]
    (is (= [[:vars ns1 v1]] (:breaking (moved s (update-in s [:vars ns1] dissoc v1)))))
    (is (= {:breaking [[:refusal-types t1]] :added [[:refusal-types :koinii/renamed]]}
           (moved s (update s :refusal-types #(replace {t1 :koinii/renamed} %)))))
    (is (= [[:vocabulary 'CxSpeechActs 'disputes]]
           (:breaking (moved s (assoc-in s [:vocabulary 'CxSpeechActs 'disputes] 3)))))))

(deftest the-golden-covers-every-koinii-namespace-and-seed-context
  (let [s (golden)]
    (testing "a derivation that found nothing would compare empty to empty"
      (is (= (set (koinii-namespaces)) (set (keys (:vars s)))))
      (is (seq (koinii-namespaces)))
      (is (< 10 (count (:refusal-types s))))
      (is (= (into (sorted-set) (comp (mapcat #(re-seq #":type (:koinii/[a-z-]+)" (slurp %)))
                                      (map (comp keyword #(subs % 1) second)))
                   (koinii-files))
             (into (sorted-set) (filter #(= "koinii" (namespace %))) (:refusal-types s)))
          "every :koinii/ type a source writes, plain map or ex-info, is frozen")
      (is (= (set seed-contexts) (set (keys (:vocabulary s)))))
      (is (every? seq (vals (:vocabulary s)))))))
