;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.orthogonal-test
  "`(orthogonal A B)`: the two types are not disjoint and neither is a `genl` of the other.
  It does not say that anything is an instance of both, and it exempts the pair from no
  separation.  The declared spelling of the `:orthogonal` subsumption status.  A
  `siblingDisjointException` is a `genl` of it."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [clojure.walk :as walk]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.clashes :as clashes]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.order-independence-test :as oi]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

;; `true?` around each read, so a failure prints the answer rather than the KB.

;; ---- the declaration ------------------------------------------------------

(tu/deftest-kb orthogonal-is-a-declared-term-of-the-grammar
  (is (some? (v/interpreted 'orthogonal))
      "CxUniverse declares orthogonal, and the vocabulary classification answers for it")
  (is (true? (v/ask? kb '(binary_predicate orthogonal))))
  (is (true? (v/ask? kb '(symmetric orthogonal))))
  (is (true? (v/ask? kb '(type_relation_predicate orthogonal)))))

(tu/deftest-kb its-length-is-checked-by-its-own-arm-not-a-stated-class
  ;; `symmetric` and `type_relation_predicate` are each `genl binary_predicate`, so the
  ;; class is derived without stating it, and the well-formedness arm, which reads the
  ;; sentence alone, refuses any other length.
  (is (not-any? #(v/premise? kb (:id %)) (v/sentexes-matching kb '(binary_predicate orthogonal) '?ctx))
      "no (binary_predicate orthogonal) is stated")
  (is (true? (v/ask? kb '(binary_predicate orthogonal))))
  (is (= 2 (:arity (v/describe kb 'orthogonal))))
  (tu/with-terms [alphaKind betaKind gammaKind]
    (doseq [t [alphaKind betaKind gammaKind]]
      (v/assert kb (list 'genl t 'thing) 'CxUniverse))
    (doseq [s [(list 'orthogonal alphaKind betaKind gammaKind) (list 'orthogonal alphaKind)]]
      (is (= :not-well-formed
             (try (v/assert kb s 'CxUniverse) :ok
                  (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))
          (str (pr-str s) " is refused")))))

(tu/deftest-kb orthogonal-is-symmetric
  (tu/with-terms [spatialKind temporalKind]
    (v/assert kb (list 'genl spatialKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl temporalKind 'thing) 'CxUniverse)
    (v/assert kb (list 'orthogonal temporalKind spatialKind) 'CxUniverse)
    (is (true? (v/ask? kb (list 'orthogonal spatialKind temporalKind) 'CxUniverse))
        "either spelling answers the one stored declaration")
    (is (true? (v/ask? kb (list 'orthogonal temporalKind spatialKind) 'CxUniverse)))))

;; ---- the subsumption status -------------------------------------------------

(tu/deftest-kb a-declared-pair-is-orthogonal-without-a-shared-instance
  (tu/with-terms [spatialKind temporalKind]
    (v/assert kb (list 'genl spatialKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl temporalKind 'thing) 'CxUniverse)
    (is (= :unknown (v/subsumption-status kb spatialKind temporalKind))
        "no relation and no shared instance yet")
    (v/assert kb (list 'orthogonal temporalKind spatialKind) 'CxUniverse)
    (is (= #{:orthogonal} (v/subsumption-statuses kb spatialKind temporalKind))
        "the declaration is the witness, whichever order it was written in")
    (is (= :orthogonal (v/subsumption-status kb temporalKind spatialKind)))))

(tu/deftest-kb a-declaration-a-narrower-context-holds-is-read-from-that-vantage
  (tu/with-terms [spatialKind temporalKind]
    (let [cx (tu/tmp-ctx)]
      (v/assert kb (list 'genlCx cx 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genl spatialKind 'thing) 'CxUniverse)
      (v/assert kb (list 'genl temporalKind 'thing) 'CxUniverse)
      (v/assert kb (list 'orthogonal spatialKind temporalKind) cx)
      (is (= :unknown (v/subsumption-status kb spatialKind temporalKind))
          "CxUniverse does not see a declaration stated below it")
      (is (= :orthogonal (v/subsumption-status kb spatialKind temporalKind cx))))))

(tu/deftest-kb a-declared-pair-that-is-also-genl-related-is-inconsistent
  (tu/with-terms [alphaKind betaKind]
    (v/assert kb (list 'genl alphaKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl betaKind alphaKind) 'CxUniverse)
    (v/assert kb (list 'orthogonal alphaKind betaKind) 'CxUniverse {:strength :monotonic})
    (is (= #{:spec :orthogonal} (v/subsumption-statuses kb alphaKind betaKind)))
    (is (= :inconsistent (v/subsumption-status kb alphaKind betaKind)))))

(tu/deftest-kb a-declared-pair-under-a-separated-pair-is-inconsistent
  ;; overlap propagates upward: two subtypes that could share an instance put it in both
  ;; separated supertypes, so the declaration does not exempt the pair it names
  (tu/with-terms [upperA upperB subA subB]
    (v/assert kb (list 'genl upperA 'thing) 'CxUniverse)
    (v/assert kb (list 'genl upperB 'thing) 'CxUniverse)
    (v/assert kb (list 'genl subA upperA) 'CxUniverse)
    (v/assert kb (list 'genl subB upperB) 'CxUniverse)
    (v/assert kb (list 'disjoint upperA upperB) 'CxUniverse)
    (v/assert kb (list 'orthogonal subA subB) 'CxUniverse)
    (is (= #{:disjoint :orthogonal} (v/subsumption-statuses kb subA subB)))
    (is (= :inconsistent (v/subsumption-status kb subB subA)))))

(tu/deftest-kb the-separation-and-the-declaration-are-read-from-one-vantage
  (tu/with-terms [parentkind alphakind betakind]
    (let [cx (tu/tmp-ctx)]
      (v/assert kb (list 'genlCx cx 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genl parentkind 'thing) 'CxUniverse)
      (v/assert kb (list 'genl alphakind parentkind) 'CxUniverse)
      (v/assert kb (list 'genl betakind parentkind) 'CxUniverse)
      (v/assert kb (list 'sibling_disjoint parentkind) 'CxUniverse)
      (v/assert kb (list 'siblingDisjointException alphakind betakind) cx)
      (is (= #{:disjoint} (v/subsumption-statuses kb alphakind betakind))
          "CxUniverse reads the mark and not the exception below it")
      (is (= #{:orthogonal} (v/subsumption-statuses kb alphakind betakind cx))))))

(tu/deftest-kb a-declared-pair-under-a-stated-disjoint-is-inconsistent
  (tu/with-terms [alphakind betakind]
    (v/assert kb (list 'genl alphakind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl betakind 'thing) 'CxUniverse)
    (v/assert kb (list 'disjoint alphakind betakind) 'CxUniverse)
    (v/assert kb (list 'orthogonal alphakind betakind) 'CxUniverse)
    (is (= #{:disjoint :orthogonal} (v/subsumption-statuses kb alphakind betakind)))))

(tu/deftest-kb the-audit-counts-a-declared-pair-as-known
  (tu/with-terms [spatialKind temporalKind]
    (v/assert kb (list 'genl spatialKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl temporalKind 'thing) 'CxUniverse)
    (let [row (fn [] (first (filter #(= #{spatialKind temporalKind} (hash-set (:a %) (:b %)))
                                    (:pairs-data (v/disjointness-audit kb)))))
          before (row)]
      (is (= :unknown (:status before)))
      (v/assert kb (list 'orthogonal spatialKind temporalKind) 'CxUniverse)
      (is (= :orthogonal (:status (row)))
          "a declared pair leaves the audit's unknown candidates"))))

;; ---- the clash: a possible overlap stated over a subsumed pair -----------------
;;
;; A `disjoint` over two `genl`-related types is a one-member hard clash of the
;; declaration (docs/nmtms.md, "Declarations over related types"), stored and reported by
;; `conflicts` rather than refused.  An `orthogonal` over two `genl`-related types, over
;; one type twice, or over a pair a separation holds apart is the same family's clash, of
;; the `orthogonal` declaration.

(defn- clashes
  "The member sentence sets of the `:orthogonal` clashes `conflicts` lists."
  [kb]
  (into #{} (comp (filter #(= :orthogonal (:kind %)))
                  (map (fn [r] (into #{} (map :sentence) (:sides r)))))
        (v/conflicts kb)))

(tu/deftest-kb a-consistent-declaration-is-no-clash
  (tu/with-terms [spatialKind temporalKind]
    (v/assert kb (list 'genl spatialKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl temporalKind 'thing) 'CxUniverse)
    (v/assert kb (list 'orthogonal spatialKind temporalKind) 'CxUniverse {:strength :monotonic})
    (is (= #{} (clashes kb)))))

(tu/deftest-kb an-orthogonal-over-a-genl-related-pair-is-a-clash-in-either-order
  (tu/with-terms [alphaKind betaKind]
    (v/assert kb (list 'genl alphaKind 'thing) 'CxUniverse)
    (let [orth (list 'orthogonal alphaKind betaKind)]
      (testing "the edge first"
        (let [e (v/assert kb (list 'genl betaKind alphaKind) 'CxUniverse)
              o (v/assert kb orth 'CxUniverse {:strength :monotonic})]
          (is (= #{#{orth}} (clashes kb)))
          (v/retract! kb o)
          (v/retract! kb e)))
      (testing "the orthogonal first"
        (v/assert kb (list 'genl betaKind 'thing) 'CxUniverse)
        (let [o (v/assert kb orth 'CxUniverse {:strength :monotonic})]
          (is (= #{} (clashes kb)))
          (let [e (v/assert kb (list 'genl alphaKind betaKind) 'CxUniverse)]
            (is (= #{#{orth}} (clashes kb)) "the later edge convicts the stored declaration")
            (v/retract! kb e))
          (is (= #{} (clashes kb)))
          (v/retract! kb o))))))

(tu/deftest-kb an-orthogonal-under-a-separated-pair-is-a-clash-in-either-order
  ;; The exemption is read against the separated pair of supertypes, so (orthogonal subA
  ;; subB) does not lift (disjoint upperA upperB): an instance of both subtypes would be an
  ;; instance of both separated supertypes.  The report names the separation it was
  ;; convicted through.
  (tu/with-terms [upperA upperB subA subB]
    (v/assert kb (list 'genl upperA 'thing) 'CxUniverse)
    (v/assert kb (list 'genl upperB 'thing) 'CxUniverse)
    (v/assert kb (list 'genl subA upperA) 'CxUniverse)
    (v/assert kb (list 'genl subB upperB) 'CxUniverse)
    (let [orth (list 'orthogonal subA subB)
          dj   (list 'disjoint upperA upperB)]
      (testing "the separation first"
        (let [d (v/assert kb dj 'CxUniverse)
              o (v/assert kb orth 'CxUniverse)]
          (is (= #{#{orth}} (clashes kb)))
          (is (= [dj] (map :sentence (:grounds (first (filter #(= :orthogonal (:kind %))
                                                              (v/conflicts kb)))))))
          (v/retract! kb o)
          (v/retract! kb d)))
      (is (= #{} (clashes kb)))
      (testing "the orthogonal first"
        (let [o (v/assert kb orth 'CxUniverse)]
          (is (= #{} (clashes kb)))
          (let [d (v/assert kb dj 'CxUniverse)]
            (is (= #{#{orth}} (clashes kb)) "the later separation convicts the declaration")
            (v/retract! kb d))
          (is (= #{} (clashes kb)) "the separation leaving takes the clash")
          (v/retract! kb o))))))

(tu/deftest-kb an-orthogonal-under-two-partition-parts-is-a-clash
  (tu/with-terms [wholeKind alphaKind betaKind subA subB]
    (v/assert kb (list 'genl wholeKind 'thing) 'CxUniverse)
    (v/assert kb (list 'partition wholeKind alphaKind betaKind) 'CxUniverse)
    (v/assert kb (list 'genl subA alphaKind) 'CxUniverse)
    (v/assert kb (list 'genl subB betaKind) 'CxUniverse)
    (v/assert kb (list 'orthogonal subA subB) 'CxUniverse)
    (is (= #{#{(list 'orthogonal subA subB)}} (clashes kb)))))

(tu/deftest-kb orthogonal-is-forced-monotonic
  (is (true? (v/has-prop? kb :forced-monotonic 'orthogonal)))
  (is (= :unforced-definitional-declaration
         (get checks/uncleared-forcing ['forced_monotonic_predicate 'orthogonal]))
      "held on every KB, as disjoint is, and its declaration is not retracted"))

(tu/deftest-kb a-default-declaration-the-taxonomy-contradicts-is-a-hard-clash
  ;; `orthogonal` is forced-monotonic, so a declaration written at `:default`
  ;; keeps that strength and is never the loser: its one-member nogood is a hard clash
  ;; `conflicts` lists, every member stays believed, and the pair reads both statuses.
  (tu/with-terms [alphaKind betaKind]
    (v/assert kb (list 'genl alphaKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl betaKind alphaKind) 'CxUniverse)
    (let [o (v/assert kb (list 'orthogonal alphaKind betaKind) 'CxUniverse {:strength :default})]
      (is (= :default (v/defeat-class kb o)))
      (is (= #{#{(list 'orthogonal alphaKind betaKind)}} (clashes kb)))
      (is (true? (v/ask? kb (list 'orthogonal alphaKind betaKind) 'CxUniverse)))
      (is (= :inconsistent (v/subsumption-status kb alphaKind betaKind))))))

(tu/deftest-kb the-clash-is-read-where-the-separation-is-seen
  (tu/with-terms [upperA upperB subA subB]
    (let [cx (tu/tmp-ctx)]
      (v/assert kb (list 'genlCx cx 'CxUniverse) 'CxUniverse)
      (doseq [[s t] [[upperA 'thing] [upperB 'thing] [subA upperA] [subB upperB]]]
        (v/assert kb (list 'genl s t) 'CxUniverse))
      (v/assert kb (list 'orthogonal subA subB) 'CxUniverse)
      (v/assert kb (list 'disjoint upperA upperB) cx)
      (is (= #{#{(list 'orthogonal subA subB)}} (clashes kb)))
      (is (= [#{cx}] (keep #(when (= :orthogonal (:kind %)) (clashes/report-vantages %))
                           (v/conflicts kb)))
          "read where the disjoint is seen, and not above it"))))

(defn- orth-vantages
  "The vantage sets of the `:orthogonal` clashes over `orth` that `conflicts` lists."
  [kb orth]
  (set (keep #(when (and (= :orthogonal (:kind %)) (= [orth] (map :sentence (:sides %))))
                (clashes/report-vantages %))
             (v/conflicts kb))))

(tu/deftest-kb a-genl-edge-below-a-separation-clash-adds-its-placement-in-either-order
  ;; Two routes convict the declaration: the separation in CxUniverse and the edge in cx.
  (doseq [edge-first? [true false]]
    (tu/with-terms [uppera upperb suba subb]
      (let [cx (tu/tmp-ctx)]
        (v/assert kb (list 'genlCx cx 'CxUniverse) 'CxUniverse)
        (doseq [[s t] [[uppera 'thing] [upperb 'thing] [suba uppera] [subb upperb]]]
          (v/assert kb (list 'genl s t) 'CxUniverse))
        (when edge-first? (v/assert kb (list 'genl subb suba) cx))
        (v/assert kb (list 'disjoint uppera upperb) 'CxUniverse)
        (v/assert kb (list 'orthogonal suba subb) 'CxUniverse)
        (when-not edge-first? (v/assert kb (list 'genl subb suba) cx))
        (is (true? (v/disjoint? kb suba subb 'CxUniverse)))
        (is (= #{#{'CxUniverse}} (orth-vantages kb (list 'orthogonal suba subb)))
            (if edge-first? "the edge first" "the edge last"))))))

(tu/deftest-kb an-exception-exempting-the-separation-below-the-placement-reads-no-clash-there
  ;; (siblingDisjointException uppera upperb) in ce exempts the separated pair from the
  ;; partition there, so ce reads suba, subb apart and believes neither the orthogonal's
  ;; placement nor the two memberships' placement CxUniverse holds.
  (doseq [exemption-first? [true false]]
    (tu/with-terms [parenta uppera upperb suba subb Both]
      (let [ce   (tu/tmp-ctx)
            orth (list 'orthogonal suba subb)
            mems #{(list suba Both) (list subb Both)}
            exc  (list 'siblingDisjointException uppera upperb)
            placed-at (fn [ctx]
                        (into (set (for [b (v/query kb '(contradicts ?x) ctx)]
                                     (:sentence (v/sentex kb (v/handle-id (get b '?x))))))
                              (for [b (v/query kb '(contradicts ?x ?y) ctx)]
                                (set (map #(:sentence (v/sentex kb (v/handle-id (get b %))))
                                          '[?x ?y])))))]
        (v/assert kb (list 'genlCx ce 'CxUniverse) 'CxUniverse)
        (v/assert kb (list 'genl parenta 'thing) 'CxUniverse)
        (doseq [[s t] [[suba uppera] [subb upperb]]]
          (v/assert kb (list 'genl s t) 'CxUniverse {:strength :monotonic}))
        (when exemption-first? (v/assert kb exc ce))
        (v/assert kb (list 'partition parenta uppera upperb) 'CxUniverse)
        (v/assert kb orth 'CxUniverse)
        (doseq [m mems] (v/assert kb m 'CxUniverse {:strength :monotonic}))
        (when-not exemption-first? (v/assert kb exc ce))
        (is (false? (v/disjoint? kb suba subb ce)))
        (is (every? (placed-at 'CxUniverse) [orth mems]))
        (is (not-any? (placed-at ce) [orth mems])
            (if exemption-first? "the exemption first" "the exemption last"))
        (is (= #{#{'CxUniverse}} (orth-vantages kb orth)))))))

(tu/deftest-kb a-type-is-not-orthogonal-to-itself
  (tu/with-terms [alphaKind]
    (v/assert kb (list 'genl alphaKind 'thing) 'CxUniverse)
    (v/assert kb (list 'orthogonal alphaKind alphaKind) 'CxUniverse {:strength :monotonic})
    (is (= #{#{(list 'orthogonal alphaKind alphaKind)}} (clashes kb))
        "a type subsumes itself")))

;; ---- an orthogonal exempts nothing --------------------------------------------
;;
;; A stated `disjoint` and every separation mark contradict an `orthogonal` over the pair
;; they separate.  The exemption from the marks is `siblingDisjointException`'s alone
;; (sibling_disjoint_test), and the `genl` edge from it to `orthogonal` lends nothing upward.

(defn- placed-orthogonals
  "Each stored `contradicts` of one member stating an `orthogonal`, as `[member-sentence
  context #{ground-sentence}]`: the member resolved, and the antecedents of its
  justifications other than the member read back as sentences."
  [kb]
  (into #{}
        (for [c (v/sentexes-with-functor kb 'contradicts)
              :let [ms (map v/handle-id (rest (:sentence c)))]
              :when (= 1 (count ms))
              :let [m (first ms)]]
          [(:sentence (v/sentex kb m)) (:context c)
           (into #{} (comp (mapcat :antecedents) (remove #{m}) (map #(:sentence (v/sentex kb %))))
                 (v/supporting-justifications kb (:id c)))])))

(defn- every-order
  "The set of what `observe` reads, once per arrival order of the writes `build` names.
  `build` takes a map of each of `terms` to a fresh term and returns `[setup ops]`: the
  sentences asserted first, then each of `ops` (a map of op to sentence) in the order,
  all in CxUniverse.  Each order runs on fresh terms and is taken back after, and the
  reading is returned with the fresh terms renamed back to `terms`."
  [kb terms build observe]
  (into #{}
        (for [order (oi/permutations (sort (keys (second (build (zipmap terms terms))))))]
          (tu/with-neutral-kb [k (constantly kb)]
            (let [fresh (zipmap terms (map #(tu/fresh-term (tu/term-role %) (name %)) terms))
                  [setup ops] (build fresh)]
              (doseq [s setup] (v/assert k s 'CxUniverse))
              (doseq [op order] (v/assert k (get ops op) 'CxUniverse))
              (walk/postwalk-replace (zipmap (vals fresh) (keys fresh)) (observe k)))))))

(tu/deftest-kb a-stated-disjoint-beside-an-orthogonal-places-one-contradicts-of-it
  (is (= #{#{['(orthogonal alphaKind betaKind) 'CxUniverse '#{(disjoint alphaKind betaKind)}]}}
         (every-order kb '[alphaKind betaKind]
                      (fn [{:syms [alphaKind betaKind]}]
                        [[(list 'genl alphaKind 'thing) (list 'genl betaKind 'thing)]
                         {:dj   (list 'disjoint alphaKind betaKind)
                          :orth (list 'orthogonal alphaKind betaKind)}])
                      placed-orthogonals))
      "one contradicts, of the orthogonal, with the disjoint as its ground, in both orders"))

(def ^:private marks
  "Each separation mark over `alphaKind` and `betaKind`, as the declarations that state it."
  {:sibling    (fn [{:syms [wholeKind alphaKind betaKind]}]
                 [(list 'genl alphaKind wholeKind) (list 'genl betaKind wholeKind)
                  (list 'sibling_disjoint wholeKind)])
   :partition  (fn [{:syms [wholeKind alphaKind betaKind]}]
                 [(list 'partition wholeKind alphaKind betaKind)])
   :separating (fn [{:syms [wholeKind alphaKind betaKind]}]
                 [(list 'separating wholeKind alphaKind betaKind)])
   :metatype   (fn [{:syms [kind_type alphaKind betaKind]}]
                 [(list 'genl alphaKind 'thing) (list 'genl betaKind 'thing)
                  (list kind_type alphaKind) (list kind_type betaKind)
                  (list 'disjoint_metatype kind_type)])})

(tu/deftest-kb an-orthogonal-over-a-pair-a-mark-separates-is-a-clash-of-it
  (doseq [[mark decls] marks]
    (tu/with-neutral-kb [k (constantly kb)]
      (tu/with-terms [wholeKind kind_type alphaKind betaKind]
        (let [env {'wholeKind wholeKind 'kind_type kind_type 'alphaKind alphaKind
                   'betaKind betaKind}]
          (v/assert k (list 'genl wholeKind 'thing) 'CxUniverse)
          (doseq [d (decls env)] (v/assert k d 'CxUniverse))
          (v/assert k (list 'orthogonal alphaKind betaKind) 'CxUniverse)
          (is (true? (v/disjoint? k alphaKind betaKind 'CxUniverse))
              (str mark ": the pair stays apart"))
          (is (= #{#{(list 'orthogonal alphaKind betaKind)}} (clashes k))
              (str mark ": the orthogonal is the clash")))))))

(tu/deftest-kb a-sibling-mark-clashes-with-an-orthogonal-until-an-exception-exempts-the-pair
  ;; every arrival order of the mark, the orthogonal and two memberships, then of those
  ;; and the exception
  (let [terms '[parentKind alphaKind betaKind Both]
        build (fn [{:syms [parentKind alphaKind betaKind Both]}]
                [[(list 'genl parentKind 'thing) (list 'genl alphaKind parentKind)
                  (list 'genl betaKind parentKind)]
                 {:mark (list 'sibling_disjoint parentKind)
                  :orth (list 'orthogonal alphaKind betaKind)
                  :a    (list alphaKind Both)
                  :b    (list betaKind Both)}])
        with-exc (fn [env]
                   (update (build env) 1 assoc :exc
                           (list 'siblingDisjointException (get env 'alphaKind) (get env 'betaKind))))
        kinds (fn [k] (into #{} (map :kind) (concat (v/conflicts k) (v/contradictions k))))]
    (is (= #{#{:orthogonal :disjoint}} (every-order kb terms build kinds))
        "without the exception the orthogonal is a clash and the memberships a nogood")
    (is (= #{#{}} (every-order kb terms with-exc kinds))
        "with the exception neither forms")))

(tu/deftest-kb an-exception-alone-answers-the-orthogonal-it-entails
  (tu/with-terms [alphaKind betaKind]
    (v/assert kb (list 'genl alphaKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl betaKind 'thing) 'CxUniverse)
    (v/assert kb (list 'siblingDisjointException alphaKind betaKind) 'CxUniverse)
    (is (true? (v/ask? kb (list 'orthogonal alphaKind betaKind) 'CxUniverse)))
    (is (true? (v/ask? kb (list 'orthogonal betaKind alphaKind) 'CxUniverse)))
    (is (= #{betaKind} (set (map #(get % '?y) (v/query kb (list 'orthogonal alphaKind '?y) 'CxUniverse))))
        "matched as well as asked")
    (is (= #{:orthogonal} (v/subsumption-statuses kb alphaKind betaKind))
        "the exception is the status's witness")))

(tu/deftest-kb an-exception-over-a-genl-related-pair-is-a-clash-of-the-orthogonal-it-entails
  (is (= #{#{['(siblingDisjointException alphaKind betaKind) 'CxUniverse
              '#{(genl betaKind alphaKind) (genl siblingDisjointException orthogonal)}]}}
         (every-order kb '[alphaKind betaKind]
                      (fn [{:syms [alphaKind betaKind]}]
                        [[(list 'genl alphaKind 'thing)]
                         {:edge (list 'genl betaKind alphaKind)
                          :exc  (list 'siblingDisjointException alphaKind betaKind)}])
                      placed-orthogonals))))

(tu/deftest-kb a-stated-disjoint-beside-an-exception-of-the-pair-is-a-clash-of-the-exception
  (is (= #{#{['(siblingDisjointException alphaKind betaKind) 'CxUniverse
              '#{(disjoint alphaKind betaKind) (genl siblingDisjointException orthogonal)}]}}
         (every-order kb '[alphaKind betaKind]
                      (fn [{:syms [alphaKind betaKind]}]
                        [[(list 'genl alphaKind 'thing) (list 'genl betaKind 'thing)]
                         {:dj  (list 'disjoint alphaKind betaKind)
                          :exc (list 'siblingDisjointException alphaKind betaKind)}])
                      placed-orthogonals))))

(tu/deftest-kb a-predicate-a-later-edge-puts-under-orthogonal-states-one
  (tu/with-terms [alphaKind betaKind overlapsWith]
    (v/assert kb (list 'genl alphaKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl betaKind 'thing) 'CxUniverse)
    (v/assert kb (list 'disjoint alphaKind betaKind) 'CxUniverse)
    (v/assert kb (list overlapsWith alphaKind betaKind) 'CxUniverse)
    (is (empty? (placed-orthogonals kb)))
    (let [e (v/assert kb (list 'genl overlapsWith 'orthogonal) 'CxUniverse)]
      (is (= #{(list overlapsWith alphaKind betaKind)}
             (into #{} (map first) (placed-orthogonals kb)))
          "the edge reads the predicate's stored facts")
      (v/retract! kb e)
      (is (empty? (placed-orthogonals kb)) "and taking it back takes the clash"))))

;; ---- not preserved along genl --------------------------------------------------
;;
;; That two types could overlap says nothing about a subtype or a supertype of either: a
;; subtype of one may be disjoint from the other, and a supertype of one may subsume the
;; other.  CxUniverse denies both directions of preservation along genl at both positions.
;;
;; Neither `transitiveInArg` nor `transitiveInArgInverse` is forced-monotonic,
;; so the four denials are stored and believed alike.  Nothing concludes any of the four
;; preservations, so orthogonal is inherited neither way.

(def ^:private preservation-denials
  '[(not (transitiveInArgInverse orthogonal 1 genl))
    (not (transitiveInArgInverse orthogonal 2 genl))
    (not (transitiveInArg orthogonal 1 genl))
    (not (transitiveInArg orthogonal 2 genl))])

(tu/deftest-kb cxuniverse-denies-preserving-orthogonal-along-genl
  (doseq [s preservation-denials
          :let [h (v/handle-of kb s 'CxUniverse)]]
    (is (some? h) (str (pr-str s) " is stated in CxUniverse"))
    (is (true? (v/in? kb h)) (str (pr-str s) " is believed")))
  (doseq [s preservation-denials]
    (is (false? (v/ask? kb (second s) 'CxUniverse))
        (str (pr-str (second s)) " does not hold"))))

(tu/deftest-kb orthogonal-is-not-inherited-down-or-up-genl
  (tu/with-terms [alphaKind betaKind subAlpha superAlpha]
    (v/assert kb (list 'genl superAlpha 'thing) 'CxUniverse)
    (v/assert kb (list 'genl alphaKind superAlpha) 'CxUniverse)
    (v/assert kb (list 'genl subAlpha alphaKind) 'CxUniverse)
    (v/assert kb (list 'genl betaKind 'thing) 'CxUniverse)
    (v/assert kb (list 'orthogonal alphaKind betaKind) 'CxUniverse)
    (is (true? (v/ask? kb (list 'orthogonal alphaKind betaKind) 'CxUniverse)))
    (is (false? (v/ask? kb (list 'orthogonal subAlpha betaKind) 'CxUniverse))
        "a subtype of one side is not thereby orthogonal to the other")
    (is (false? (v/ask? kb (list 'orthogonal superAlpha betaKind) 'CxUniverse))
        "nor is a supertype")
    (is (false? (v/ask? kb (list 'orthogonal betaKind subAlpha) 'CxUniverse))
        "in either argument position")))

;; ---- the related-terms links ---------------------------------------------------

(tu/deftest-kb cxuniverse-links-orthogonal-to-its-neighbours
  (doseq [s '[(termsRelated sibling_disjoint disjoint_metatype disjoint siblingDisjointException)
              (seeAlso sibling_disjoint genl)
              (termsRelated genl disjoint orthogonal)
              (genl siblingDisjointException orthogonal)]]
    (is (some? (v/handle-of kb s 'CxUniverse)) (str (pr-str s) " is stated in CxUniverse")))
  (is (nil? (v/handle-of kb '(termsRelated disjoint orthogonal) 'CxUniverse))
      "the pairwise link the two termsRelated lists cover is gone"))

;; ---- the upper ontology's axes ---------------------------------------------------

(def ^:private upper-axes
  "The pairs of upper-ontology types CxUniverse states orthogonal: parts of the three
  partitions of `thing` (by location in space, by location in time, by mass) that cut
  across one another."
  '[[spatial temporal] [aspatial atemporal] [spatial atemporal] [aspatial temporal]
    [intangible spatial] [intangible temporal] [intangible spatiotemporal]])

(tu/deftest-kb cxuniverse-states-the-upper-axes-orthogonal
  (let [tx (reasoning/taxonomy kb)]
    (doseq [[a b] upper-axes
            :let [s (list 'orthogonal a b)]]
      (testing (pr-str s)
        (is (some? (v/handle-of kb s 'CxUniverse)) "stated in CxUniverse")
        (is (true? (v/ask? kb s 'CxUniverse)) "believed")
        (is (true? (v/ask? kb (list 'orthogonal b a) 'CxUniverse)) "in either spelling")
        (is (= :orthogonal (v/subsumption-status kb a b))
            "the two may overlap and neither subsumes the other")
        (is (false? (v/genl? kb a b)))
        (is (false? (v/genl? kb b a)))
        (is (false? ((tax/disjointness-test tx a nil (constantly false)) b))
            "no stated separation divides the pair, even with no orthogonal read")))))

(tu/deftest-kb the-upper-axes-load-with-no-clash
  (is (empty? (v/conflicts kb)) "no conflict")
  (is (empty? (v/contradictions kb)) "no contradiction"))
