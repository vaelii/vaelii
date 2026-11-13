;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.tuple-marks-rebuild-test
  "A rebuild reads each functor's tuple marks once.

  `rebuild-candidates!` offers every stored tuple to `note-tuple!`, which reads the
  `functional`, `functionalInArg` and `anti_transitive` marks on the tuple's functor and
  above it (`tuple/det-marks`, `tax/props-over`), each a walk of the functor's
  supertypes.  The replay holds the taxonomy still, so it keeps each functor's marks
  (`tuple/*functor-marks*`): on a large KB's recover the walk per tuple rebuilt the same
  few thousand closures millions of times.  The determinants and chains it finds must be
  the ones a rebuild reading the marks per tuple finds.

  The placement reads the `genl` lower ends under a mark without a closure per end
  (`tuple/under-marks`), and finds the ends `props-over` and `functional-in-arg-over`
  find per end."
  (:require [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.tuple :as tuple]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(defn- tuple-half
  "The determinant and chain entries of `kb`'s candidate index."
  [kb]
  (select-keys @(reasoning/nogood-candidates kb) [::tuple/det ::tuple/chains]))

(deftest predicate-extents-accept-a-structural-specialization
  (doseq [edge-first? [true false]]
    (tu/with-neutral-kb [kb tu/fresh]
      (tu/with-terms [relation QualifierFn A B]
        (let [compound (list QualifierFn relation)
              edge     (list 'genl compound relation)
              fact     (list relation A B)]
          (doseq [sentence (if edge-first? [edge fact] [fact edge])]
            (v/assert kb sentence 'CxUniverse))
          (let [w (decide/unscoped-closures (reasoning/taxonomy kb))
                h (v/handle-of kb fact 'CxUniverse)]
            (is (= #{relation compound} ((:specs-global w) relation)))
            (is (= #{h} (set (#'tuple/marked-facts kb w [relation]))))))))))

(defn- per-tuple-rebuild!
  "`rebuild-candidates!` reading every tuple's marks afresh."
  [kb]
  (with-redefs [tuple/functor-marks (fn [_ f] (f))]
    (decide/rebuild-candidates! kb)))

(defn- random-world!
  "Six predicates under `genl` edges, marks of each kind on some, and binary and ternary
  tuples over a few terms, so determinants and chains form under sub-predicates."
  [kb ^java.util.Random rnd]
  (let [preds (vec (repeatedly 6 #(tu/fresh-term :predicate 'rel)))
        terms (vec (repeatedly 4 #(tu/fresh-term :individual 'Thing)))
        pick  (fn [v] (v (.nextInt rnd (count v))))
        try!  (fn [s] (try (v/assert kb s 'CxUniverse) (catch clojure.lang.ExceptionInfo _)))]
    (dotimes [_ 5]
      (let [i (.nextInt rnd 5), j (+ i 1 (.nextInt rnd (- 5 i)))]
        (try! (list 'genl (preds i) (preds j)))))
    (try! (list 'functional (pick preds)))
    (try! (list 'functionalInArg (pick preds) (inc (.nextInt rnd 3))))
    (try! (list 'anti_transitive (pick preds)))
    (dotimes [_ 30]
      (try! (if (zero? (.nextInt rnd 3))
              (list (pick preds) (pick terms) (pick terms) (pick terms))
              (list (pick preds) (pick terms) (pick terms)))))))

(deftest a-rebuild-keeping-the-marks-finds-what-reading-them-per-tuple-finds
  (let [rnd  (java.util.Random. 3301)
        seen (atom 0)]
    (dotimes [trial 12]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (random-world! kb rnd)
        (per-tuple-rebuild! kb)
        (let [ref (tuple-half kb)]
          (decide/rebuild-candidates! kb)
          (swap! seen + (count (::tuple/det ref)) (count (::tuple/chains ref)))
          (is (= ref (tuple-half kb)) (str "trial " trial)))))
    (is (pos? @seen) "the worlds hold determinants or chains")))

(deftest a-rebuild-reads-a-functor-s-marks-once
  ;; `k` tuples of one functor under a functional super-predicate, and the two kinds
  ;; `found-for` reads of it (other families read other kinds)
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [k     20
          [q p] (repeatedly 2 #(tu/fresh-term :predicate 'rel))]
      (v/assert kb (list 'genl q p) 'CxUniverse)
      (v/assert kb (list 'functional p) 'CxUniverse)
      (dotimes [_ k]
        (v/assert kb (list q (tu/fresh-term :individual 'Thing) (tu/fresh-term :individual 'Thing))
                  'CxUniverse))
      (let [reads (atom 0)
            real  tax/props-over]
        ;; the context-free arity reads through the var, so every read ends in the
        ;; four-argument one
        (with-redefs [tax/props-over (fn [& args]
                                       (when (and (= 4 (count args)) (= q (nth args 2))
                                                  (#{:functional :anti-transitive} (nth args 1)))
                                         (swap! reads inc))
                                       (apply real args))]
          (decide/rebuild-candidates! kb))
        (is (<= @reads 2) (str @reads " reads of " q "'s marks for " k " tuples"))))))

(deftest a-rebuild-reads-the-marks-above-each-functor-off-the-props-set-cut
  ;; a chain of predicates, the top `functional` and `anti_transitive`, and a tuple of
  ;; each: the marks above every functor are read off one memo per kind, where a
  ;; closure per functor costs the sum of the closures
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [ps (vec (repeatedly 12 #(tu/fresh-term :predicate 'rel)))]
      (doseq [[a b] (partition 2 1 ps)] (v/assert kb (list 'genl a b) 'CxUniverse))
      (v/assert kb (list 'functional (peek ps)) 'CxUniverse)
      (v/assert kb (list 'anti_transitive (peek ps)) 'CxUniverse)
      (doseq [p ps]
        (v/assert kb (list p (tu/fresh-term :individual 'Thing) (tu/fresh-term :individual 'Thing))
                  'CxUniverse))
      (let [closures (atom 0)
            real     @#'tax/closure-of
            before   (tuple-half kb)]
        (with-redefs [tax/closure-of (fn [& args]
                                       (when (= [:genl :fwd] (take 2 (rest args))) (swap! closures inc))
                                       (apply real args))]
          (decide/rebuild-candidates! kb))
        (is (zero? @closures) "no functor's whole closure is built")
        (is (= before (tuple-half kb)) "and the rebuild finds what the writes found")))))

(deftest the-props-set-cut-reads-the-marks-props-over-reads
  ;; random predicate hierarchies, some edges closing a cycle, marks of both kinds on
  ;; some predicates: one memo per kind across every predicate answers `props-over`
  (let [rnd  (java.util.Random. 9127)
        seen (atom 0)]
    (dotimes [trial 12]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (let [ps   (vec (repeatedly 8 #(tu/fresh-term :predicate 'rel)))
              try! (fn [s] (try (v/assert kb s 'CxUniverse) (catch clojure.lang.ExceptionInfo _)))]
          (dotimes [_ 10]
            (let [i (.nextInt rnd 8) j (.nextInt rnd 8)]
              (when (and (not= i j) (or (< i j) (zero? (.nextInt rnd 5))))
                (try! (list 'genl (ps i) (ps j))))))
          (dotimes [_ 3]
            (try! (list 'functional (ps (.nextInt rnd 8))))
            (try! (list 'anti_transitive (ps (.nextInt rnd 8)))))
          (let [tax (reasoning/taxonomy kb)]
            (doseq [kind [:functional :anti-transitive]
                    :let [memo (volatile! {})]
                    p    (shuffle ps)
                    :let [want (tax/props-over tax kind p)]]
              (swap! seen + (count want))
              (is (= want (tax/props-over-among tax kind p memo))
                  (str "trial " trial " " kind " " p)))))))
    (is (pos? @seen) "the hierarchies carry marks over some predicates")))

(deftest the-ends-under-a-mark-are-those-props-over-reads-per-end
  ;; random hierarchies of predicates and of types, some edges closing a cycle, a mark of
  ;; each kind or a `functionalInArg` declaration on a few predicates at varied depths, and
  ;; one top marked over a chain of twelve: every `genl` lower end, asked together and three
  ;; at a time in shuffled orders (the two sides of `under-marks`), against the reads per end
  (let [rnd   (java.util.Random. 4901)
        kinds [:irreflexive :anti-symmetric :asymmetric :functional :anti-transitive]
        marks '[irreflexive anti_symmetric asymmetric functional anti_transitive]
        seen  (atom 0)]
    (dotimes [trial 12]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (let [ps    (vec (repeatedly 10 #(tu/fresh-term :predicate 'rel)))
              ts    (vec (repeatedly 10 #(tu/fresh-term :type 'kind)))
              chain (vec (repeatedly 12 #(tu/fresh-term :predicate 'link)))
              try!  (fn [s] (try (v/assert kb s 'CxUniverse) (catch clojure.lang.ExceptionInfo _)))]
          (doseq [xs [ps ts]]
            (dotimes [_ 14]
              (let [i (.nextInt rnd 10) j (.nextInt rnd 10)]
                (when (and (not= i j) (or (< i j) (zero? (.nextInt rnd 5))))
                  (try! (list 'genl (xs i) (xs j)))))))
          (doseq [[a b] (partition 2 1 chain)] (try! (list 'genl a b)))
          (try! (list 'genl (ps (.nextInt rnd 10)) (chain 0)))
          (try! (list (marks (.nextInt rnd 5)) (peek chain)))
          (dotimes [_ 2]
            (try! (list (marks (.nextInt rnd 5)) (ps (.nextInt rnd 10)))))
          (when (zero? (.nextInt rnd 2))
            (try! (list 'functionalInArg (ps (.nextInt rnd 10)) (inc (.nextInt rnd 2)))))
          (let [tax  (reasoning/taxonomy kb)
                ends (into [] (comp (map :sentence) (map second) (filter symbol?) (distinct))
                           (v/sentexes-with-functor kb 'genl))
                want (into #{} (filter (fn [q] (or (some #(seq (tax/props-over tax % q)) kinds)
                                                   (seq (tax/functional-in-arg-over tax q)))))
                           ends)]
            (swap! seen + (count want))
            (is (= want (tuple/under-marks tax (shuffle ends))) (str "trial " trial))
            (is (= want (into #{} (mapcat #(tuple/under-marks tax %)) (partition-all 3 (shuffle ends))))
                (str "trial " trial ", three ends at a time"))))))
    (is (pos? @seen) "the hierarchies hold ends under a mark")))
