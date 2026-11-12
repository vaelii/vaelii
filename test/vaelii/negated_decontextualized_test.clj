;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.negated-decontextualized-test
  "A negated literal of a `decontextualized_predicate` stated in an ordinary context.
  `(decontextualized_predicate P)` lifts every `(P ...)` and every `(not (P ...))` into
  CxUniverse, so a clash between the two is decided or reported at CxUniverse for every
  context that reads the copies.  A copy takes the weaker of its source's and its
  declaration's strengths, so a `:monotonic` statement decides CxUniverse only under a
  `:monotonic` declaration.  The rows are vaelii#256's.  See docs/contexts.md."
  (:require [clojure.set :as set]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(defn- contexts [kb homes]
  (doseq [home homes]
    (v/assert kb (list 'genlCx home 'CxUniverse) 'CxUniverse)))

(defn- reading
  "What `context` answers about `s`: `:true`, `:false`, `:both` or `:unknown`."
  [kb s context]
  (let [p (v/ask? kb s context)
        n (v/ask? kb (list 'not s) context)]
    (cond (and p n) :both p :true n :false :else :unknown)))

;; Both copies are stored in CxUniverse, so the dilemma between them is placed there and
;; every context that sees CxUniverse reports it, the uninvolved sibling CxC included.
(tu/deftest-kb a-sibling-denial-of-a-decontextualized-fact-is-a-dilemma-every-reader-sees
  (tu/with-terms [CxA CxB CxC S M liftedRel]
    (contexts kb [CxA CxB CxC])
    (v/assert kb (list 'decontextualized_predicate liftedRel) 'CxUniverse)
    (let [s (list liftedRel S M)]
      (v/assert kb s CxA)
      (v/assert kb (list 'not s) CxB)
      (testing "the denial's own context reports it"
        (is (seq (v/contradictions kb CxB))))
      (testing "the dilemma is visible from CxUniverse and from an uninvolved sibling"
        (is (seq (v/contradictions kb 'CxUniverse)))
        (is (seq (v/contradictions kb CxC)))))))

;; A CxUniverse rule over the negative literal fires on the denial's copy and places its
;; conclusion in CxUniverse, as the same rule over the positive literal does.
(tu/deftest-kb a-denial-of-a-decontextualized-predicate-is-read-from-every-context
  (tu/with-terms [CxA CxB CxC S T M liftedRel flagNeg flagPos]
    (contexts kb [CxA CxB CxC])
    (v/assert kb (list 'decontextualized_predicate liftedRel) 'CxUniverse)
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list 'not (list liftedRel '?x M)) (list flagNeg '?x)))
              'CxUniverse)
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list liftedRel '?x M) (list flagPos '?x)))
              'CxUniverse)
    (v/assert kb (list liftedRel T M) CxA)
    (v/assert kb (list 'not (list liftedRel S M)) CxB)
    (testing "the positive half reaches every context, and so does its rule's conclusion"
      (is (= :true (reading kb (list liftedRel T M) CxC)))
      (is (v/ask? kb (list flagPos T) CxC)))
    (testing "the negative half reaches every context too"
      (is (= :false (reading kb (list liftedRel S M) 'CxUniverse)))
      (is (= :false (reading kb (list liftedRel S M) CxC))))
    (testing "and so does its rule's conclusion"
      (is (v/ask? kb (list flagNeg S) CxC)))))

(def ^:private rows
  "Where each of vaelii#256's rows 1-4 states the positive and the denial, at what strength."
  {1 {:pos [:A :default] :neg [:B :default]}
   2 {:pos [:A :default] :neg [:B :monotonic]}
   3 {:pos [:A :default] :neg [:A :monotonic]}
   4 {:pos [:A :monotonic] :neg [:B :monotonic]}})

(defn- assert-row
  "Assert `row` over a row's terms (`:cx` maps `:A` `:B` `:C` to contexts, `:s` is the
  positive literal, `:p` its predicate), the declaration at `decl`, the three statements in
  `order`.  Returns their handles by step."
  [kb {:keys [cx s p]} row decl order]
  (into {}
        (map (fn [step]
               [step (case step
                       :decl (v/assert kb (list 'decontextualized_predicate p) 'CxUniverse
                                       {:strength decl})
                       :pos  (let [[c st] (:pos (rows row))] (v/assert kb s (cx c) {:strength st}))
                       :neg  (let [[c st] (:neg (rows row))]
                               (v/assert kb (list 'not s) (cx c) {:strength st})))]))
        order))

(defn- outcome
  "What every context reads and reports about a row's terms once `assert-row` ran, in role
  names: `:readings` per context, `:dilemmas` per context and `:conflicts`, each report the
  set of its sides' `[literal context defeat-class]`.  A report naming neither literal is
  left out."
  [kb {:keys [cx s]}]
  (let [cx    (assoc cx :U 'CxUniverse)
        role  (merge (set/map-invert cx) {s :pos (list 'not s) :neg})
        named (fn [rs]
                (into #{}
                      (comp (filter #(some (comp #{:pos :neg} role :sentence) (:sides %)))
                            (map (fn [r]
                                   (into #{} (map (fn [d] [(role (:sentence d)) (role (:context d))
                                                           (:defeat-class d)]))
                                         (:sides r)))))
                      rs))
        ks    [:U :A :B :C]]
    {:readings  (into (sorted-map) (map (fn [k] [k (reading kb s (cx k))])) ks)
     :dilemmas  (into (sorted-map) (map (fn [k] [k (named (v/contradictions kb (cx k)))])) ks)
     :conflicts (named (v/conflicts kb))}))

(defn- with-contexts
  "Call `f` on `{:A :B :C}`, three fresh sibling contexts under CxUniverse."
  [kb f]
  (tu/with-terms [CxA CxB CxC]
    (contexts kb [CxA CxB CxC])
    (f {:A CxA :B CxB :C CxC})))

(defn- row-terms
  "Call `f` on fresh terms for one row over the contexts `cx`: `{:cx :s :p}`."
  [cx f]
  (tu/with-terms [S M liftedRel]
    (f {:cx cx :s (list liftedRel S M) :p liftedRel})))

(defn- row-outcome [kb cx row decl order]
  (row-terms cx (fn [t]
                  (assert-row kb t row decl order)
                  (outcome kb t))))

;; Row 2.  Under a `:default` declaration the copies are a dilemma at CxUniverse, and CxB
;; alone reads its own `:monotonic` denial.
(tu/deftest-kb a-monotonic-sibling-denial-decides-every-context-under-a-monotonic-declaration
  (doseq [[decl expected dilemma?]
          [[:monotonic {:U :false :A :false :B :false :C :false} false]
           [:default   {:U :both :A :both :B :false :C :both} true]]]
    (let [o (with-contexts kb #(row-outcome kb % 2 decl [:decl :pos :neg]))]
      (is (= expected (:readings o)) (str decl))
      (is (= dilemma? (boolean (seq (get-in o [:dilemmas :U])))) (str decl)))))

;; Row 3.  Under a `:default` declaration the copies are a dilemma at CxUniverse, which
;; every context but CxA reports.
(tu/deftest-kb a-fact-its-own-context-defeats-is-defeated-at-its-copy-under-a-monotonic-declaration
  (doseq [[decl expected dilemma?]
          [[:monotonic {:U :false :A :false :B :false :C :false} false]
           [:default   {:U :both :A :false :B :both :C :both} true]]]
    (let [o (with-contexts kb #(row-outcome kb % 3 decl [:decl :pos :neg]))]
      (is (= expected (:readings o)) (str decl))
      (is (= dilemma? (boolean (seq (get-in o [:dilemmas :C])))) (str decl)))))

;; Row 4.  Under a `:default` declaration both copies are `:default`: a dilemma at
;; CxUniverse, with each stating context deciding for its own statement.
(tu/deftest-kb two-monotonic-statements-in-siblings-are-a-conflict-under-a-monotonic-declaration
  (let [[m d] (with-contexts kb (fn [cx] (mapv #(row-outcome kb cx 4 % [:decl :pos :neg])
                                               [:monotonic :default])))]
    (testing "a :monotonic declaration"
      (is (seq (:conflicts m))))
    (testing "a :default declaration"
      (is (empty? (:conflicts d)))
      (is (= #{#{[:pos :U :default] [:neg :U :default]}} (get-in d [:dilemmas :U])))
      (is (= {:U :both :A :true :B :false :C :both} (:readings d))))))

(defn- order-check
  "Assert that each `[row decl]` of `groups` has one outcome over `orders`."
  [kb groups orders]
  (with-contexts kb
    (fn [cx]
      (doseq [[row decl] groups]
        (is (= 1 (count (into #{} (map #(row-outcome kb cx row decl %)) orders)))
            (str "row " row " under a " decl " declaration"))))))

(tu/deftest-kb ^:slow arrival-order-changes-no-answer-and-no-report
  ;; Rows 1-4 under either declaration strength, in all six orders.
  (order-check kb (for [row (sort (keys rows)) decl [:default :monotonic]] [row decl])
               (tu/permutations [:decl :pos :neg])))

(tu/deftest-kb arrival-order-changes-no-answer-and-no-report-sampled
  ;; The declaration first and last, over a defeat at a copy and a dilemma.
  (order-check kb [[3 :monotonic] [4 :default]] [[:decl :pos :neg] [:neg :pos :decl]]))

(tu/deftest-kb retracting-a-source-or-the-declaration-withdraws-its-copy-and-every-clash-with-it
  ;; A dilemma (row 1) and a conflict (row 4), each of the three statements retracted.
  (with-contexts kb
    (fn [cx]
      (doseq [[row decl] [[1 :default] [4 :monotonic]]
              gone        [:pos :neg :decl]]
        (row-terms
         cx
         (fn [t]
           (let [hs     (assert-row kb t row decl [:decl :pos :neg])
                 copy?  #(seq (v/sentexes-matching kb % 'CxUniverse))
                 before (outcome kb t)
                 why    (str "row " row ", " gone " retracted")]
             (is (or (seq (get-in before [:dilemmas :U])) (seq (:conflicts before))) why)
             (v/retract! kb (hs gone))
             (let [after (outcome kb t)]
               (is (every? empty? (vals (:dilemmas after))) why)
               (is (empty? (:conflicts after)) why))
             (is (= (= gone :neg) (boolean (copy? (:s t)))) why)
             (is (= (= gone :pos) (boolean (copy? (list 'not (:s t))))) why))))))))

(tu/deftest-kb an-exception-in-the-universe-reads-a-lifted-denial
  ;; The denial is stated in a context the rule does not see; its copy's arrival
  ;; re-checks the exception, as a positive copy's does.
  (tu/with-terms [CxA bird flies S M liftedRel]
    (contexts kb [CxA])
    (v/assert kb (list 'decontextualized_predicate liftedRel) 'CxUniverse)
    (v/assert kb (list 'exceptWhen (list 'not (list liftedRel '?x M))
                       (list 'set/defaultRule
                             (list 'set/forwardRule
                                   (list 'implies (list 'and (list bird '?x)) (list flies '?x)))))
              'CxUniverse)
    (v/assert kb (list bird S) 'CxUniverse)
    (is (v/ask? kb (list flies S) 'CxUniverse) "nothing denies it yet")
    (let [h (v/assert kb (list 'not (list liftedRel S M)) CxA)]
      (is (not (v/ask? kb (list flies S) 'CxUniverse)) "the copy satisfies the exception")
      (v/retract! kb h)
      (is (v/ask? kb (list flies S) 'CxUniverse) "and its retraction releases the rule"))))
