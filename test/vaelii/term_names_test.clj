;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.term-names-test
  "The term-name set: `terms` / `term-count` / `find-terms` — the KB's vocabulary read
  off the index instead of scavenged from the records.

  The oracle is the scan the term-name set replaces: walk every stored sentex, take its
  indexable subterms plus its context, keep the symbols.  Whatever that produces, the
  term-name set must produce — after a load, after a retraction, after a `reindex`, and after
  a restart over the same durable store.  Everything here runs on whichever backend the
  suite is configured for, so the on-disk parity run covers it too."
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.protocols :as p]
            [vaelii.test-util :as tu]))

(defn- starter-kb [] (doto (tu/empty-kb) (tu/load-starter!)))

(defn- scanned-terms
  "The oracle: every symbol term reachable by walking the records — what a client with
  no term-name set has to do (and what a browser search does per keystroke without one)."
  [kb]
  (into (sorted-set)
        (comp (keep #(p/get-sentex (:records kb) %))
              (mapcat (fn [sx] (conj (v/indexable-terms sx) (:context sx))))
              (filter symbol?))
        (p/sentex-ids (:records kb))))

(defn- context-scanned-terms
  "The same oracle a *public-API-only* client can write: every sentex in every known
  context.  It can miss a context the taxonomy does not know, so the term-name set is a
  superset of this, never a subset."
  [kb]
  (into (sorted-set)
        (comp (mapcat #(v/sentexes-in-context kb %))
              (mapcat v/indexable-terms)
              (filter symbol?))
        (v/contexts kb)))

;; ---- enumeration --------------------------------------------------------

(deftest case-only-term-names-are-distinct
  (tu/with-cleared-kb [kb tu/fresh]
    (let [h (v/assert kb '(foo Foo) 'CxUniverse {:chain? false})]
      (is (= '(foo Foo) (:sentence (v/sentex kb h))))
      (is (= ['Foo 'foo] (v/find-terms kb "foo")))
      (is (= ['foo] (v/find-terms kb "foo" {:case-sensitive? true})))
      (is (= ['Foo] (v/find-terms kb "Foo" {:case-sensitive? true})))
      (is (not= 'foo 'Foo)))))

(deftest an-empty-kb-has-an-empty-vocabulary
  (tu/with-cleared-kb [kb tu/empty-kb]
    (is (= [] (v/terms kb)))
    (is (zero? (v/term-count kb)))
    (is (= [] (v/find-terms kb "anything")))))

(deftest enumeration-matches-a-full-scan
  (tu/with-neutral-kb [kb starter-kb]
    (testing "the term-name set is exactly what a record scan produces"
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
    (testing "every listed term is a symbol — a ground compound is a fragment, not a name"
      (is (every? symbol? (v/terms kb))))
    (testing "known vocabulary is in there"
      (is (every? (set (v/terms kb)) '[genl thing CxUniverse arg])))))

;; ---- maintenance: a name arrives with the first mention, leaves with the last ----

(deftest a-term-arrives-and-leaves-with-its-postings
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Muffet Rex CxStory]
      (let [before (set (v/terms kb))
            n0     (v/term-count kb)
            h1     (v/assert kb (list dog Muffet) CxStory)]
        (testing "asserting introduces every name the sentex mentions, once"
          (is (set/subset? #{dog Muffet CxStory} (set (v/terms kb))))
          (is (= (+ n0 3) (v/term-count kb))))
        (let [h2 (v/assert kb (list dog Rex) CxStory)]
          (testing "a second sentex over the same names adds only the new one"
            (is (= (+ n0 4) (v/term-count kb))))
          (testing "retracting one keeps the names the other still mentions"
            (v/retract! kb h1)
            (is (= #{dog Rex CxStory}
                   (set/intersection #{dog Muffet Rex CxStory} (set (v/terms kb)))))
            (is (= (+ n0 3) (v/term-count kb))))
          (testing "retracting the last mention retires them all"
            (v/retract! kb h2)
            (is (= before (set (v/terms kb))))
            (is (= n0 (v/term-count kb)))))))))

(deftest a-term-survives-in-another-context
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [likes Ann Bob CxOne CxTwo]
      (let [h1 (v/assert kb (list likes Ann Bob) CxOne)]
        (v/assert kb (list likes Ann Bob) CxTwo)
        (is (set/subset? #{likes Ann Bob CxOne CxTwo} (set (v/terms kb))))
        (v/retract! kb h1)
        (let [ts (set (v/terms kb))]
          (is (set/subset? #{likes Ann Bob CxTwo} ts) "the shared names stay")
          (is (not (ts CxOne)) "the emptied context's name goes"))))))

(deftest a-rules-terms-are-listed
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [parentOf ancestorOf CxRule]
      (let [h (v/assert-rule kb [(list parentOf '?x '?y)] (list ancestorOf '?x '?y) CxRule)]
        (is (set/subset? #{parentOf ancestorOf CxRule} (set (v/terms kb)))
            "a rule's antecedent/consequent predicates are names like any other")
        (is (not-any? #{'?x '?y '?var0 '?var1} (v/terms kb)) "variables are not names")
        (v/retract! kb h)
        (is (not-any? #{parentOf ancestorOf CxRule} (v/terms kb)))))))

(deftest numbers-and-strings-are-not-terms
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [bornIn Tom CxData]
      (v/assert kb (list bornIn Tom 1970) CxData)
      (is (every? symbol? (v/terms kb)))
      (is (= (vec (scanned-terms kb)) (v/terms kb))))))

;; ---- rebuild + restart --------------------------------------------------

(deftest reindex-reproduces-the-term-name-set
  (tu/with-neutral-kb [kb starter-kb]
    (tu/with-terms [cat Felix CxHouse]
      (v/assert kb (list cat Felix) CxHouse)
      (let [before (v/terms kb)]
        (v/reindex kb)
        (is (= before (v/terms kb)) "a wholesale index rebuild reproduces the vocabulary")
        (is (= (count before) (v/term-count kb)))
        (is (= (vec (scanned-terms kb)) (v/terms kb)))))))

(deftest the-term-name-set-survives-a-restart
  ;; a second KB over the same durable store, recovered — the index is derived state
  ;; that lives beside the records, so the vocabulary must read the same either side.
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [wolf Lupo CxWild]
      (v/assert kb (list wolf Lupo) CxWild)
      (let [before (v/terms kb)
            kb2    (doto (tu/test-kb) (v/recover))]
        (is (= before (v/terms kb2)))
        (is (= (count before) (v/term-count kb2)))
        (is (set/subset? #{wolf Lupo CxWild} (set (v/terms kb2))))))))

;; ---- search -------------------------------------------------------------

(deftest find-terms-filters-the-term-name-set
  (tu/with-neutral-kb [kb tu/fresh]
    ;; the generated names share the prefix `tmpparent` and differ at the next
    ;; character, so the sorted answer is [parentOf parentTo] whatever the gensym
    (tu/with-terms [parentOf parentTo Ann CxPrefix]
      (let [pre  (subs (str parentOf) 0 9)              ; "tmpparent"
            both [parentOf parentTo]]
        (v/assert kb (list parentOf Ann Ann) CxPrefix)
        (v/assert kb (list parentTo Ann Ann) CxPrefix)
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
          (is (= [] (v/find-terms kb "PARENT" {:match :substring :case-sensitive? true}))))
        (testing "regex is `re-find`, so the pattern says where it anchors"
          (is (= both (v/find-terms kb (str "^" pre) {:match :regex})))
          (is (= [parentOf] (v/find-terms kb (str "^" pre "of") {:match :regex})))
          (is (= both (v/find-terms kb "(?i)PARENT" {:match :regex})))
          (is (= [parentOf] (v/find-terms kb (re-pattern (str pre "of")) {:match :regex}))
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
          (v/retract! kb (v/handle-of kb (list parentTo Ann Ann) CxPrefix))
          (is (= [parentOf] (v/find-terms kb pre))))))))

(deftest find-terms-over-the-starter-vocabulary
  (tu/with-neutral-kb [kb starter-kb]
    (testing "a prefix search is the enumeration, filtered"
      (is (= (vec (filter #(str/starts-with? (str %) "genl") (v/terms kb)))
             (v/find-terms kb "genl")))
      (is (some #{'genlCx} (v/find-terms kb "genl"))))
    (testing "a regex reaches what a prefix cannot"
      (is (seq (v/find-terms kb "^Cx" {:match :regex})))
      (is (every? #(str/starts-with? (str %) "Cx")
                  (v/find-terms kb "^Cx" {:match :regex}))))
    (testing "an empty query matches everything, and :limit bounds it"
      (is (= (v/terms kb) (v/find-terms kb "")))
      (is (= 10 (count (v/find-terms kb "" {:limit 10})))))
    (testing "a bounded answer is the unbounded one's prefix at every limit and match mode —
              the bound is a selection, never a different order"
      (doseq [[q opts] [["" nil] ["g" nil] ["Cx" nil] ["a" {:case-sensitive? true}]
                        ["e" {:match :substring}] ["^[a-z]+Of$" {:match :regex}]]
              n        [1 2 3 7 50 201 100000]]
        (is (= (vec (take n (v/find-terms kb q opts)))
               (v/find-terms kb q (assoc opts :limit n)))
            (str (pr-str q) " " (pr-str opts) " at limit " n))))))

(deftest find-terms-refuses-a-limit-that-is-not-a-positive-integer
  ;; `:limit` reaches `take`, so a string limit raises a bare cast error — over the
  ;; daemon's `:find-terms` op, a 500 with no `:type` to discriminate on.  Refused as
  ;; `:unknown-option`, the vocabulary of the `:match` refusal beside it: a known key holding
  ;; a value it cannot mean.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [parentOf Ann CxLimit]
      (v/assert kb (list parentOf Ann Ann) CxLimit)
      (doseq [bad ["5" 0 -1 5.0 :ten]]
        (let [e (is (thrown? clojure.lang.ExceptionInfo
                             (v/find-terms kb "tmp" {:limit bad}))
                    (str (pr-str bad) " is refused"))]
          (is (= :unknown-option (:type (ex-data e))))
          (is (re-find #"positive integer" (ex-message e)))))
      (testing "a positive integer still bounds, and an explicit nil is no limit"
        (is (= 1 (count (v/find-terms kb (subs (str parentOf) 0 3) {:limit 1}))))
        (is (= (v/find-terms kb "tmp") (v/find-terms kb "tmp" {:limit nil}))))
      (testing "a limit past Integer/MAX_VALUE allocates nothing and answers unbounded"
        ;; the selection heap's initial capacity is a floor rather than the caller's
        ;; `:limit`, so a bound nothing can reach is a bound and not an array
        (doseq [huge [2147483648 4294967296 Long/MAX_VALUE]]
          (is (= (v/find-terms kb "tmp") (v/find-terms kb "tmp" {:limit huge}))
              (str (pr-str huge) " answers what no limit answers"))
          (is (= (v/find-terms kb "tmp" {:match :substring})
                 (v/find-terms kb "tmp" {:match :substring :limit huge})))))
      (testing "a limit past Long/MAX_VALUE is the typed refusal, not a cast error"
        ;; an arbitrary-precision integer satisfies `integer?` and would reach the `long`
        ;; the selection narrows through — an untyped `ArithmeticException` no list of
        ;; refusal types can see, and over the daemon a 500 with nothing to key on
        (doseq [bad [9223372036854775808N (biginteger 9223372036854775808N) (bigint 1e30)]]
          (let [e (is (thrown? clojure.lang.ExceptionInfo
                               (v/find-terms kb "tmp" {:limit bad}))
                      (str (pr-str bad) " is refused"))]
            (is (= :unknown-option (:type (ex-data e))))
            (is (re-find #"positive integer" (ex-message e)))))))))

(tu/deftest-kb a-find-terms-key-nothing-reads-is-refused
  ;; a misspelt `:mtch` silently ran the default prefix search, and a prefix answer
  ;; where substring was asked for reads as "no such term" — in the browser's own
  ;; search box, over the wire.
  (doseq [opts [{:mtch :substring} {:case-sensitve? true} {:limit 3 :mach :regex}]]
    (let [e (try (v/find-terms kb "x" opts) nil
                 (catch clojure.lang.ExceptionInfo e (ex-data e)))]
      (is (= :unknown-option (:type e)) (pr-str opts)))))

(deftest a-pathological-regex-is-refused-not-a-spin
  ;; `:find-terms` runs over the daemon's single-writer monitor, so an unbounded regex
  ;; there wedges every write behind it.  A super-linear pattern over a long term blows
  ;; the per-term step budget and is refused `:pattern-too-costly`; a linear one answers.
  (tu/with-neutral-kb [kb tu/fresh]
    (let [evil-term (symbol (str (apply str (repeat 2000 \a)) "b"))]   ; a long run of a's
      (v/assert kb (list 'genl evil-term 'thing) 'CxUniverse)
      (testing "a nested-quantifier pattern over a long term is refused, not run out"
        (is (= :pattern-too-costly
               (try (v/find-terms kb "(a*)*$" {:match :regex}) nil
                    (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))))
      (testing "a well-formed anchored pattern over the same term still answers"
        (is (= [evil-term] (v/find-terms kb "^a+b$" {:match :regex})))))))

(deftest a-regex-scan-over-the-whole-vocabulary-is-bounded-too
  ;; The per-candidate budget catches a pattern that backtracks; this one catches a
  ;; pattern that is merely asked over more vocabulary than one call may read — on the
  ;; daemon that read is taken holding the single writer.  Set low through the var so
  ;; the test does not need a six-figure vocabulary; the shipped budget answers the same
  ;; linear pattern over the same terms.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [gen_a gen_b gen_c CxScan]
      (doseq [t [gen_a gen_b gen_c]] (v/assert kb (list 'genl t 'thing) CxScan))
      (with-redefs-fn {#'v/regex-scan-budget 20}
        (fn []
          (let [d (try (v/find-terms kb "gen" {:match :regex}) nil
                       (catch clojure.lang.ExceptionInfo e (ex-data e)))]
            (is (= :pattern-too-costly (:type d)))
            (is (= :scan (:scope d)) "refused for the scan, not for any one candidate"))))
      (is (= 3 (count (filter #{gen_a gen_b gen_c} (v/find-terms kb "gen" {:match :regex}))))
          "the shipped budget admits a linear pattern over the whole vocabulary"))))
