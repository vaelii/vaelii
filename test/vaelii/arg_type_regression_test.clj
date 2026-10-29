;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.arg-type-regression-test
  "Argument-type declarations read in the role they play.

  The load-order tests state a handful of sentences over fresh terms, load them in one
  order and in another, and compare what the KB stores, what it believes, and every
  justification by content: the same sentences in two orders leave a fresh KB holding the
  same records, belief and justifications.

  The reading tests build the smallest KB that shows a declared argument type read as a
  demand where it is a conclusion, or as a narrower type than the predicate declares."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.impl.protocols :as p]
            [vaelii.test-util :as tu]))

(def ^:private U 'CxUniverse)

(defn- content [kb h]
  (when-let [sx (v/sentex kb h)] [(v/sentence-of sx) (:context sx)]))

(defn- held
  "What `kb` stores, as a multiset of printed `[sentence context believed?]`."
  [kb]
  (frequencies
   (for [h (p/sentex-ids (:records kb))
         :let [sx (p/get-sentex (:records kb) h)]]
     [(str/replace (pr-str (:sentence sx)) #"\(sentexHandle \d+\)" "(sentexHandle _)")
      (str (:context sx))
      (v/in? kb h)])))

(defn- reasons
  "Every justification in `kb` as `[informant conclusion antecedents subsumptions]`, by
  content, with the number of justifications each names.  A rule informant reads as its
  sentence."
  [kb]
  (frequencies
   (for [h (v/handles kb), j (v/supporting-justifications kb h)]
     (let [inf (:informant j)]
       [(if (integer? inf) (first (content kb inf)) inf)
        (content kb h)
        (into #{} (map #(content kb %)) (:antecedents j))
        (:subsumptions j)]))))

(defn- load-in
  "Assert each `[sentence context]` of `steps` in order at `:monotonic` on a fresh KB with
  subsumed mints pruned; what the KB holds and the reasons.  With `recover?`, the reading
  is `[live recovered]`, the second taken after `recover` rebuilds belief from the store."
  ([steps] (load-in steps false))
  ([steps recover?]
   (tu/with-neutral-kb [kb tu/fresh]
     (binding [argument/*assertive-arg-types?*  true
               checks/*prune-subsumed-mints?* true]
       (doseq [[s cx] steps] (v/assert kb s cx {:strength :monotonic}))
       (let [read #(hash-map :held (held kb) :reasons (reasons kb))
             live (read)]
         (if recover? [live (do (v/recover kb) (read))] live))))))

(defn- both-orders
  "`[(load-in a) (load-in b)]`, each with `recover?` as `load-in` takes it."
  ([a b] (both-orders a b false))
  ([a b recover?] [(load-in a recover?) (load-in b recover?)]))

(deftest ^{:red true
           :doc "rests-on? walks a premise subsumer's justifications, so withdrawable-mint keeps a mint the premise subsumes."}
  a-premise-subsumer-withdraws-a-mint-made-before-its-edge
  ;; `(arg pType 1 aType)` mints `(aType Rex)` off the premise `(pType Rex)`, and the
  ;; rule (an intersection's membership rule, spelled out) concludes `(pType Rex)` again
  ;; over the mint.  `(genl pType aType)` makes the premise subsume the mint.
  (tu/with-terms [pType aType bType Rex]
    (let [setup [[(list 'genl aType 'thing) U] [(list 'genl bType 'thing) U]
                 [(list bType Rex) U]
                 [(list 'set/forwardRule
                        (list 'implies (list 'and (list aType '?x) (list bType '?x))
                              (list pType '?x)))
                  U]]
          fact  [[(list pType Rex) U] [(list 'arg pType 1 aType) U]]
          edge  [[(list 'genl pType aType) U]]
          [edge-last edge-first] (both-orders (concat setup fact edge)
                                              (concat setup edge fact))]
      (is (= edge-first edge-last)
          "the edge after the fact and declaration, and before them"))))

(deftest a-mint-made-after-a-decontextualized-declaration-is-lifted
  ;; `(arg pType 1 aType)` mints `(aType Rex)` in CxWorld off `(pType Rex)` there, and
  ;; `(decontextualized_predicate aType)` lifts `(aType ...)` into CxUniverse.
  (tu/with-terms [pType aType Rex CxWorld]
    (let [setup [[(list 'genlCx CxWorld U) U] [(list 'genl aType 'thing) U]
                 [(list 'genl pType 'thing) U] [(list 'arg pType 1 aType) U]]
          decl  [[(list 'decontextualized_predicate aType) U]]
          fact  [[(list pType Rex) CxWorld]]
          [decl-last decl-first] (both-orders (concat setup fact decl)
                                              (concat setup decl fact) true)]
      (is (= decl-first decl-last)
          "the declaration after the fact, and before it, live and recovered")
      (is (= (first decl-first) (second decl-first))
          "the declaration first, live and recovered")
      (is (contains? (:held (first decl-first)) [(pr-str (list aType Rex)) (str U) true])
          "the mint is lifted into CxUniverse"))))

(deftest ^{:red true
           :doc "rule-clash reads a consequent's own declared arg type as a :declared demand, so arg-type-conflicted? drops a reachable disjoint pair."}
  a-conclusion-s-declared-arg-type-does-not-hide-a-disjoint-clash
  ;; `(cat_kind ?x)` and `(dog_kind ?x)` are separated through `feline_kind` and
  ;; `canine_kind`.  `(arg cat_kind 1 feline_kind)` is what the cat conclusion entails
  ;; about ?x, not a precondition on it, so anything that meows and barks is a clash.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [feline_kind canine_kind cat_kind dog_kind meows barks]
      (doseq [s [(list 'genl feline_kind 'thing) (list 'genl canine_kind 'thing)
                 (list 'genl cat_kind feline_kind) (list 'genl dog_kind canine_kind)
                 (list 'disjoint feline_kind canine_kind) (list 'arg cat_kind 1 feline_kind)]]
        (v/assert kb s U))
      (v/assert-rule kb [(list meows '?x)] (list cat_kind '?x) U {:direction :forward})
      (v/assert-rule kb [(list barks '?x)] (list dog_kind '?x) U {:direction :forward})
      (is (= [:disjoint] (mapv :kind (:pairs (:clashes (v/kb-quality kb)))))
          "the two conclusions are one disjoint clash in waiting"))))

(deftest a-genl-over-a-binary-predicate-class-is-not-an-inert-rule
  ;; `genl` relates predicates of any arity, and `(genl seenBy targetRel)` is a binary
  ;; edge.  A rule binding ?r a `pair_kind` (whose instances are `pair_type`, disjoint
  ;; from `unary_predicate`) and an argument of `genl` can fire.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [pair_type pair_kind steady_kind seenBy targetRel]
      (doseq [s [(list 'type_relation_predicate 'genl)
                 (list 'genl pair_type 'predicate) (list 'disjoint pair_type 'unary_predicate)
                 (list 'genl pair_kind 'thing) (list 'genl steady_kind 'thing)
                 (list 'arg pair_kind 1 pair_type)]]
        (v/assert kb s U))
      (let [form (list 'implies (list 'and (list pair_kind '?r) (list 'genl '?r targetRel))
                       (list steady_kind '?r))
            h    (v/assert kb form U)]
        (is (= [] (filter #(= h (v/handle-of kb (:sentence %) (:context %)))
                          (filter #(= :inert-rule (:violation %)) (v/violations kb))))
            "the rule is not reported inert")
        (is (true? (v/in? kb h)) "and it is believed")))))
