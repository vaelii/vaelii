;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.reindex-test
  "The index is derived state: `reindex` must rebuild all of it — trie, roots, term
  index, rule index — from the records alone, such that every read answers as it
  did before the index was destroyed."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.columnar :as columnar]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.reindex :as reindex]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu])
  (:import (com.sun.management ThreadMXBean)
           (java.io File)
           (java.lang.management ManagementFactory)))

(deftest reindex-rebuilds-a-destroyed-index
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [dog animal barksAt growls Muffet Rex]
      (v/assert kb (list 'genl dog animal) 'CxUniverse)
      (v/assert kb (list dog Muffet) 'CxUniverse)
      (v/assert kb (list barksAt Muffet Rex) 'CxUniverse)
      (v/assert-rule kb [(list dog '?x)] (list growls '?x) 'CxUniverse {:direction :forward})
      (let [snap (fn []
                   {:dog-extent    (count (v/sentexes-matching kb (list dog '?x) 'CxUniverse))
                    :functor-count (v/count-with-functor kb barksAt)
                    :arg-count     (v/count-with-arg kb 1 Muffet)
                    :term-find     (count (v/find-sentexes kb Muffet))
                    :isa?          (v/isa? kb Muffet animal)
                    :derived?      (boolean (seq (v/sentexes-matching kb (list growls Muffet) 'CxUniverse)))
                    :backward?     (v/provable? kb (list growls Muffet) 'CxUniverse)})
            before (snap)]
        (testing "the content is really there before the damage"
          (is (:derived? before) "the rule fired forward")
          (is (:isa? before)))
        (p/clear-index! (:index kb))
        (testing "the damage is real: an empty index answers nothing"
          (is (zero? (v/count-with-functor kb barksAt))))
        (reindex/reindex kb)
        (v/recover kb)
        (testing "every read answers as before the index was destroyed"
          (is (= before (snap))))))))

(deftest reindex-rebuilds-a-variable-consequent-rule
  ;; A rule concluding `(?p ?x ?y)` (reasoning/27's consequent half) files its consequent
  ;; under the `p/var-consequent-key` catch-all rather than a canonical `?var0`.  `reindex`
  ;; must rebuild that posting from the record so a backward goal still reaches the rule.
  ;; A `set/backwardRule` isolates the backward path: it never fires forward, so the
  ;; conclusion is reachable only by expanding the rule from `concluding-rule-handles`.
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [holds loves Tom Ann]
      (v/assert kb (list 'set/backwardRule
                         (list 'implies (list holds '?p '?x '?y) (list '?p '?x '?y)))
                'CxUniverse)
      (v/assert kb (list holds loves Tom Ann) 'CxUniverse)
      (let [var0?  (fn [t] (re-find #"var0" (str t)))
            snap   (fn [] {:backward? (v/provable? kb (list loves Tom Ann) 'CxUniverse)
                           :names-clean? (not-any? var0? (reads/stored-terms-global (:index kb)))})
            before (snap)]
        (testing "the backward goal reaches the var-consequent rule, and ?var0 never enters the term-name set"
          (is (:backward? before))
          (is (:names-clean? before)))
        (p/clear-index! (:index kb))
        (reindex/reindex kb)
        (v/recover kb)
        (testing "and both survive a rebuild from the records alone"
          (is (= before (snap))))))))

;; ---- the allocation of an index write ----------------------------------------

(def ^:private ^ThreadMXBean thread-mx (ManagementFactory/getThreadMXBean))

(defn- bytes-per-sentex
  "Bytes this thread allocates per sentex over `index-one!` of every `[sentex handle]` in
  `sxs` into a cleared `store`, after four unmeasured passes.  The store is cleared again
  before the result returns, so the test leaves its space as it found it."
  [store sxs]
  (let [pass (fn []
               (p/clear-index! store)
               (let [a (.getCurrentThreadAllocatedBytes thread-mx)]
                 (doseq [[s h] sxs] (reindex/index-one! store s h))
                 (- (.getCurrentThreadAllocatedBytes thread-mx) a)))]
    (try
      (dotimes [_ 4] (pass))
      (quot (long (pass)) (count sxs))
      (finally (p/clear-index! store)))))

(deftest a-reindexed-sentex-allocates-no-op-vector-per-family
  ;; `flat-family-adds` conjes each family's ops onto the store's one transient batch, so
  ;; a write allocates no vector per family.  Bytes per sentex over this corpus are
  ;; 27.5 KB on `KvIndexStore` over the memory backend and 18.6 KB on the columnar store
  ;; on JDK 25 (compact object headers, project.clj), and 29.3 KB and 20.6 KB on JDK 17.
  ;; The budgets are 34000 and 24000; a per-family vector costs 37.0 KB and 27.5 KB on
  ;; JDK 25, over both.
  (let [n   600
        ind #(symbol (str "Ind" %))
        sxs (into []
                  (map-indexed (fn [i s] [s (inc i)]))
                  (for [i (range n)
                        s (cond-> [(sx/sentex (list 'dog (ind i)) 'CxUniverse)
                                   (sx/sentex (list 'parentOf (ind i) (ind (mod (* 7 i) n))) 'CxUniverse)
                                   (sx/sentex (list 'likes (ind i) (list 'friendOf (ind (inc i)))) 'CxUniverse)]
                            (zero? (mod i 5)) (conj (sx/sentex (list 'not (list 'dog (ind i))) 'CxUniverse)))]
                    s))]
    (when-not (tu/instrumented?)
      (is (< (long (bytes-per-sentex (mem/memory-index-store {:space 83}) sxs)) 34000)
          "KvIndexStore, bytes per sentex")
      (is (< (long (bytes-per-sentex (columnar/columnar-index-store {:space 83}) sxs)) 24000)
          "ColumnarIndexStore, bytes per sentex"))))

;; ---- the re-check index ------------------------------------------------------

(defn- rebuilt
  "`(f target)` over `kb` as `path` leaves it: `kb` itself under `:live` and `:reindex`
  (after `v/reindex`), else a KB on the isolated space holding `kb`'s dump, imported with
  belief (`:import`) or records-only and recovered (`:import-records`)."
  [kb path f]
  (case path
    :live    (f kb)
    :reindex (do (v/reindex kb) (f kb))
    (let [dir (File/createTempFile "vaelii-recheck-" "")]
      (try
        (.delete dir)
        (v/export! kb (.getPath dir) {:compression :none})
        (tu/cleared-kb* tu/isolated-fresh
                        (fn [k]
                          (if (= :import path)
                            (v/import! k (.getPath dir))
                            (do (v/import! k (.getPath dir) {:belief? false})
                                (v/recover k)))
                          (f k)))
        (finally (run! #(.delete ^File %) (reverse (file-seq dir))))))))

(deftest a-rebuilt-index-withdraws-a-conclusion-a-taxonomy-read-condition-blocks
  ;; per row: a rule whose condition the taxonomy reads, its conclusion believed, then a
  ;; fact that defeats the condition arrives after the index was rebuilt or imported
  (doseq [row  [:closed-extent :separation :negates]
          path [:live :reindex :import :import-records]]
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [month candidate not_a_month cat_t dog_t pet_t maybe_cat
                      scorns admires person maybe_admires Smarch Rex Ann Bob CxCal]
        (let [U 'CxUniverse
              [setup goal fact]
              (case row
                :closed-extent
                [[[(list 'genlCx CxCal U) U] [(list 'closed_extent_predicate month) CxCal]
                  [(list 'implies (list 'and (list candidate '?m) (list 'not (list month '?m)))
                         (list not_a_month '?m)) CxCal]
                  [(list candidate Smarch) CxCal]]
                 [(list not_a_month Smarch) CxCal] [(list month Smarch) CxCal]]
                :separation
                [[[(list 'genlCx CxCal U) U] [(list pet_t Rex) CxCal]
                  [(list 'disjoint cat_t dog_t) U {:strength :monotonic}]
                  [(list 'implies (list 'and (list pet_t '?x) (list 'unknown (list 'not (list cat_t '?x))))
                         (list maybe_cat '?x)) CxCal]]
                 [(list maybe_cat Rex) CxCal] [(list dog_t Rex) CxCal {:strength :monotonic}]]
                :negates
                [[[(list 'genlCx CxCal U) U] [(list person Ann) CxCal]
                  [(list 'negates scorns admires) U]
                  [(list 'implies (list 'and (list person '?x) (list 'unknown (list 'not (list admires '?x Bob))))
                         (list maybe_admires '?x)) CxCal]]
                 [(list maybe_admires Ann) CxCal] [(list scorns Ann Bob) CxCal]])]
          (doseq [[s c o] setup]
            (v/assert kb s c (merge (when (= 'implies (first s)) {:direction :forward}) o)))
          (is (= [true false]
                 (rebuilt kb path (fn [k]
                                    (let [before (apply v/ask? k goal)]
                                      (apply v/assert k fact)
                                      [before (apply v/ask? k goal)]))))
              (str (name row) " " (name path))))))))

(defn- recheck-postings
  "`{key handles}`: each of `ks` and `:rules` that the re-check index holds a rule handle
  under, with the handles."
  [ks kb]
  (let [idx (:index kb)]
    (into {} (keep (fn [k] (when-let [hs (not-empty (set (p/family-leaf idx :exception-index [k])))]
                             [k hs])))
          (conj ks :rules))))

(deftest reindex-and-import-post-the-recheck-keys-a-write-posts
  ;; one world holding every key kind: a rule's `unknown`, closed-extent, separation and
  ;; negates keys, and an exceptWhen's query, separation, negates and closed-extent keys
  (doseq [path [:reindex :import :import-records]]
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [month cat_t dog_t pet_t scorns admires flagged a_b a_c a_d a_e a_f a_g
                      Bob CxCal]
        (let [U  'CxUniverse
              fw {:direction :forward}
              r  (fn [ante c] (list 'implies (list 'and (list pet_t '?x) ante) (list c '?x)))
              ew (fn [q c] (list 'exceptWhen q (list 'set/forwardRule
                                                     (list 'implies (list pet_t '?x) (list c '?x)))))]
          (v/assert kb (list 'genlCx CxCal U) U)
          (v/assert kb (list 'closed_extent_predicate month) CxCal)
          (v/assert kb (list 'disjoint cat_t dog_t) U {:strength :monotonic})
          (v/assert kb (list 'negates scorns admires) U)
          (v/assert kb (r (list 'unknown (list flagged '?x)) a_b) CxCal fw)
          (v/assert kb (r (list 'not (list month '?x)) a_c) CxCal fw)
          (v/assert kb (r (list 'unknown (list 'not (list cat_t '?x))) a_d) CxCal fw)
          (v/assert kb (r (list 'unknown (list 'not (list admires '?x Bob))) a_e) CxCal fw)
          (v/assert kb (ew (list flagged '?x) a_f) CxCal)
          (v/assert kb (ew (list 'and (list 'not (list cat_t '?x)) (list 'not (list admires '?x Bob))
                                 (list 'not (list month '?x)))
                           a_g)
                    CxCal)
          (let [ks   ['not month cat_t dog_t pet_t scorns admires flagged a_b a_c a_d a_e a_f a_g Bob]
                live (recheck-postings ks kb)]
            (is (every? #(seq (live %)) [flagged month dog_t scorns])
                "the world posts a key of each kind")
            (is (= live (rebuilt kb path (partial recheck-postings ks))) (name path))))))))
