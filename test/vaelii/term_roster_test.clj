;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.term-roster-test
  "The term roster: `terms` / `term-count` / `find-terms` — the KB's vocabulary read
  off the index instead of scavenged from the records.

  The oracle is the scan the roster replaces: walk every stored sentex, take its
  indexable subterms plus its context, keep the symbols.  Whatever that produces, the
  roster must produce — after a load, after a retraction, after a `reindex`, and after
  a restart over the same durable store.  Everything here runs on whichever backend the
  suite is configured for, so the on-disk parity gate covers it too."
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]))

(defn- starter-kb [] (doto (tu/fresh) (starter/load-into)))

(defn- scanned-terms
  "The oracle: every symbol term reachable by walking the records — what a client with
  no roster has to do (and what a browser search does per keystroke without one)."
  [kb]
  (into (sorted-set)
        (comp (keep #(p/get-sentex (:records kb) %))
              (mapcat (fn [sx] (conj (v/indexable-terms sx) (:context sx))))
              (filter symbol?))
        (p/sentex-ids (:records kb))))

(defn- context-scanned-terms
  "The same oracle a *public-API-only* client can write: every sentex in every known
  context.  It can miss a context the taxonomy does not know, so the roster is a
  superset of this, never a subset."
  [kb]
  (into (sorted-set)
        (comp (mapcat #(v/sentexes-in-context kb %))
              (mapcat v/indexable-terms)
              (filter symbol?))
        (v/contexts kb)))

;; ---- enumeration --------------------------------------------------------

(deftest an-empty-kb-has-an-empty-vocabulary
  (tu/with-cleared-kb [kb tu/fresh]
    (is (= [] (v/terms kb)))
    (is (zero? (v/term-count kb)))
    (is (= [] (v/find-terms kb "anything")))))

(deftest enumeration-matches-a-full-scan
  (tu/with-neutral-kb [kb starter-kb]
    (testing "the roster is exactly what a record scan produces"
      (is (= (vec (scanned-terms kb)) (v/terms kb))))
    (testing "and a superset of what a context walk can reach"
      (is (set/subset? (context-scanned-terms kb) (set (v/terms kb)))))
    (testing "the count is the cardinality, and the vocabulary is not the KB"
      (is (= (count (v/terms kb)) (v/term-count kb)))
      (is (pos? (v/term-count kb))))
    (testing "the answer is sorted and distinct"
      (let [ts (v/terms kb)]
        (is (= ts (vec (sort ts))))
        (is (= (count ts) (count (set ts))))))
    (testing "every rostered term is a symbol — a ground compound is a fragment, not a name"
      (is (every? symbol? (v/terms kb))))
    (testing "known vocabulary is in there"
      (is (every? (set (v/terms kb)) '[genl thing CoreContext argIsa])))))

;; ---- maintenance: a name arrives with the first mention, leaves with the last ----

(deftest a-term-arrives-and-leaves-with-its-postings
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Muffet Rex StoryContext]
      (let [before (set (v/terms kb))
            n0     (v/term-count kb)
            h1     (v/assert kb (list dog Muffet) StoryContext)]
        (testing "asserting introduces every name the sentex mentions, once"
          (is (set/subset? #{dog Muffet StoryContext} (set (v/terms kb))))
          (is (= (+ n0 3) (v/term-count kb))))
        (let [h2 (v/assert kb (list dog Rex) StoryContext)]
          (testing "a second sentex over the same names adds only the new one"
            (is (= (+ n0 4) (v/term-count kb))))
          (testing "retracting one keeps the names the other still mentions"
            (v/retract! kb h1)
            (is (= #{dog Rex StoryContext}
                   (set/intersection #{dog Muffet Rex StoryContext} (set (v/terms kb)))))
            (is (= (+ n0 3) (v/term-count kb))))
          (testing "retracting the last mention retires them all"
            (v/retract! kb h2)
            (is (= before (set (v/terms kb))))
            (is (= n0 (v/term-count kb)))))))))

(deftest a-term-survives-in-another-context
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [likes Ann Bob OneContext TwoContext]
      (let [h1 (v/assert kb (list likes Ann Bob) OneContext)]
        (v/assert kb (list likes Ann Bob) TwoContext)
        (is (set/subset? #{likes Ann Bob OneContext TwoContext} (set (v/terms kb))))
        (v/retract! kb h1)
        (let [ts (set (v/terms kb))]
          (is (set/subset? #{likes Ann Bob TwoContext} ts) "the shared names stay")
          (is (not (ts OneContext)) "the emptied context's name goes"))))))

(deftest a-rules-terms-are-rostered
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [parentOf ancestorOf RuleContext]
      (let [h (v/assert-rule kb [(list parentOf '?x '?y)] (list ancestorOf '?x '?y) RuleContext)]
        (is (set/subset? #{parentOf ancestorOf RuleContext} (set (v/terms kb)))
            "a rule's antecedent/consequent predicates are names like any other")
        (is (not-any? #{'?x '?y '?var0 '?var1} (v/terms kb)) "variables are not names")
        (v/retract! kb h)
        (is (not-any? #{parentOf ancestorOf RuleContext} (v/terms kb)))))))

(deftest numbers-and-strings-are-not-terms
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [bornIn Tom DataContext]
      (v/assert kb (list bornIn Tom 1970) DataContext)
      (is (every? symbol? (v/terms kb)))
      (is (= (vec (scanned-terms kb)) (v/terms kb))))))

;; ---- rebuild + restart --------------------------------------------------

(deftest reindex-reproduces-the-roster
  (tu/with-neutral-kb [kb starter-kb]
    (tu/with-terms [cat Felix HouseContext]
      (v/assert kb (list cat Felix) HouseContext)
      (let [before (v/terms kb)]
        (v/reindex kb)
        (is (= before (v/terms kb)) "a wholesale index rebuild reproduces the vocabulary")
        (is (= (count before) (v/term-count kb)))
        (is (= (vec (scanned-terms kb)) (v/terms kb)))))))

(deftest the-roster-survives-a-restart
  ;; a second KB over the same durable store, recovered — the index is derived state
  ;; that lives beside the records, so the vocabulary must read the same either side.
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [wolf Lupo WildContext]
      (v/assert kb (list wolf Lupo) WildContext)
      (let [before (v/terms kb)
            kb2    (doto (tu/test-kb) (v/recover))]
        (is (= before (v/terms kb2)))
        (is (= (count before) (v/term-count kb2)))
        (is (set/subset? #{wolf Lupo WildContext} (set (v/terms kb2))))))))

;; ---- search -------------------------------------------------------------

(deftest find-terms-filters-the-roster
  (tu/with-neutral-kb [kb tu/fresh]
    ;; the generated names share the prefix `tmpParent` and differ at the next
    ;; character, so the sorted answer is [parentOf parentTo] whatever the gensym
    (tu/with-terms [parentOf parentTo Ann PrefixContext]
      (let [pre  (subs (str parentOf) 0 9)              ; "tmpParent"
            both [parentOf parentTo]]
        (v/assert kb (list parentOf Ann Ann) PrefixContext)
        (v/assert kb (list parentTo Ann Ann) PrefixContext)
        (testing "prefix is the default, and case-insensitive"
          (is (= both (v/find-terms kb pre)))
          (is (= both (v/find-terms kb (str/upper-case pre))))
          (is (= [] (v/find-terms kb (str/upper-case pre) {:case-sensitive? true})))
          (is (= both (v/find-terms kb pre {:case-sensitive? true}))))
        (testing "a symbol query works like its name"
          (is (= both (v/find-terms kb (symbol pre)))))
        (testing "substring matches inside the name, where a prefix does not"
          (is (= [] (v/find-terms kb "Parent")))
          (is (= both (v/find-terms kb "Parent" {:match :substring})))
          (is (= [] (v/find-terms kb "parent" {:match :substring :case-sensitive? true}))))
        (testing "regex is `re-find`, so the pattern says where it anchors"
          (is (= both (v/find-terms kb (str "^" pre) {:match :regex})))
          (is (= [parentOf] (v/find-terms kb (str "^" pre "Of") {:match :regex})))
          (is (= both (v/find-terms kb "(?i)PARENT" {:match :regex})))
          (is (= [parentOf] (v/find-terms kb (re-pattern (str pre "Of")) {:match :regex}))
              "a compiled pattern is taken as-is (in-process)"))
        (testing ":limit keeps a stable prefix of the sorted answer"
          (is (= [parentOf] (v/find-terms kb pre {:limit 1})))
          (is (= (vec (take 1 (v/find-terms kb pre))) (v/find-terms kb pre {:limit 1})))
          (is (= both (v/find-terms kb pre {:limit 50}))))
        (testing "it agrees with filtering the enumeration"
          (is (= (vec (filter #(str/starts-with? (str %) pre) (v/terms kb)))
                 (v/find-terms kb pre))))
        (testing "a bad :match is refused"
          (is (thrown? clojure.lang.ExceptionInfo (v/find-terms kb pre {:match :fuzzy}))))
        (testing "a retracted term stops matching"
          (v/retract! kb (v/handle-of kb (list parentTo Ann Ann) PrefixContext))
          (is (= [parentOf] (v/find-terms kb pre))))))))

(deftest find-terms-over-the-starter-vocabulary
  (tu/with-neutral-kb [kb starter-kb]
    (testing "a prefix search is the enumeration, filtered"
      (is (= (vec (filter #(str/starts-with? (str %) "genl") (v/terms kb)))
             (v/find-terms kb "genl")))
      (is (some #{'genlContext} (v/find-terms kb "genl"))))
    (testing "a regex reaches what a prefix cannot"
      (is (seq (v/find-terms kb "Context$" {:match :regex})))
      (is (every? #(str/ends-with? (str %) "Context")
                  (v/find-terms kb "Context$" {:match :regex}))))
    (testing "an empty query matches everything, and :limit bounds it"
      (is (= (v/terms kb) (v/find-terms kb "")))
      (is (= 10 (count (v/find-terms kb "" {:limit 10})))))))

(deftest find-terms-refuses-a-limit-that-is-not-a-positive-integer
  ;; `:limit` reaches `take`, so a string limit raises a bare cast error — over the
  ;; daemon's `:find-terms` op, a 500 with no `:type` to discriminate on.  Refused as
  ;; `:unknown-option`, the vocabulary of the `:match` refusal beside it: a known key holding
  ;; a value it cannot mean.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [parentOf Ann LimitContext]
      (v/assert kb (list parentOf Ann Ann) LimitContext)
      (doseq [bad ["5" 0 -1 5.0 :ten]]
        (let [e (is (thrown? clojure.lang.ExceptionInfo
                             (v/find-terms kb "tmp" {:limit bad}))
                    (str (pr-str bad) " is refused"))]
          (is (= :unknown-option (:type (ex-data e))))
          (is (re-find #"positive integer" (ex-message e)))))
      (testing "a positive integer still bounds, and an explicit nil is no limit"
        (is (= 1 (count (v/find-terms kb (subs (str parentOf) 0 3) {:limit 1}))))
        (is (= (v/find-terms kb "tmp") (v/find-terms kb "tmp" {:limit nil})))))))

(tu/deftest-kb a-find-terms-key-nothing-reads-is-refused
  ;; a misspelt `:mtch` silently ran the default prefix search, and a prefix answer
  ;; where substring was asked for reads as "no such term" — in the browser's own
  ;; search box, over the wire.
  (doseq [opts [{:mtch :substring} {:case-sensitve? true} {:limit 3 :mach :regex}]]
    (let [e (try (v/find-terms kb "x" opts) nil
                 (catch clojure.lang.ExceptionInfo e (ex-data e)))]
      (is (= :unknown-option (:type e)) (pr-str opts)))))
