;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.constraint-nogood-test
  "Definitional violations (disjointness, functionality, asymmetry, anti-transitivity,
  a refuted cover) as nogoods: stored at the entry point whatever the members' classes,
  the weaker side defeated, an equal defeasible pair a dilemma, an equal known-true pair
  a conflict (docs/nmtms.md, \"What a refusal may rest on\").  Also pinned: what stays a
  refusal, a malformed sentence and an argument constraint.  `arity`'s refusal is
  `constraint_vocabulary_test`'s."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.clashes :as clashes]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- fwd [antes conseq]
  (list 'set/forwardRule (vr/rule-sentence antes conseq)))

(defn- permutations [coll]
  (if (<= (count coll) 1)
    (list (seq coll))
    (for [i (range (count coll))
          p (permutations (concat (take i coll) (drop (inc i) coll)))]
      (cons (nth coll i) p))))

;;; ── asymmetry: a relation declared not to hold both ways ──────────────

(tu/deftest-kb an-asymmetric-pair-at-default-is-a-represented-dilemma
  (tu/with-terms [typLarger dog_t cat_t]
    (v/assert kb (list 'asymmetric typLarger) 'CxUniverse)
    (v/assert kb (list typLarger dog_t cat_t) 'CxUniverse)
    (testing "the converse is admitted: neither claim outranks the other"
      (is (v/assert kb (list typLarger cat_t dog_t) 'CxUniverse)))
    (testing "and the pair is reported"
      (let [cs (v/contradictions kb)]
        (is (= 1 (count cs)) "the pair is reported exactly once")
        (is (= #{(v/handle-of kb (list typLarger dog_t cat_t) 'CxUniverse)
                 (v/handle-of kb (list typLarger cat_t dog_t) 'CxUniverse)}
               (:nogood (first cs))))
        (is (= 2 (count (:sides (first cs))))
            "both sides' justifications, which is what an application ranks with")))
    (testing "and both stay believed — a dilemma is represented, not decided"
      (is (v/ask? kb (list typLarger dog_t cat_t) 'CxUniverse))
      (is (v/ask? kb (list typLarger cat_t dog_t) 'CxUniverse)))))

(tu/deftest-kb an-asymmetric-converse-of-known-true-content-is-stored-and-loses
  (tu/with-terms [typLarger dog_t cat_t]
    (v/assert kb (list 'asymmetric typLarger) 'CxUniverse)
    (v/assert kb (list typLarger dog_t cat_t) 'CxUniverse {:strength :monotonic})
    (is (v/assert kb (list typLarger cat_t dog_t) 'CxUniverse))
    (is (v/ask? kb (list typLarger dog_t cat_t) 'CxUniverse))
    (is (not (v/ask? kb (list typLarger cat_t dog_t) 'CxUniverse)))
    (is (empty? (v/conflicts kb)))))

;;; ── the entry point stores every clash that names its members ─────────

(tu/deftest-kb a-disjoint-clash-on-the-assert-path-is-stored-and-a-default-pair-is-a-dilemma
  (tu/with-terms [dog_t cat_t Muffet]
    (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
    (v/assert kb (list dog_t Muffet) 'CxUniverse)
    (is (v/assert kb (list cat_t Muffet) 'CxUniverse))
    (testing "and the pair is a represented dilemma, both believed"
      (is (v/ask? kb (list dog_t Muffet) 'CxUniverse))
      (is (v/ask? kb (list cat_t Muffet) 'CxUniverse))
      (is (= 1 (count (v/contradictions kb)))))))

(defn- clash-shapes
  "One row per definitional family whose clash names the other stored member:
  `[label setup opposing arriving grounds]`, where `setup` writes the
  declarations and the `genl` edges the conviction reads (all `:monotonic`), the two
  memberships or tuples are the nogood's members, and `grounds` are the declarations of
  `setup` the report names."
  [{:keys [dog_t cat_t root_t species animal_t ageOf measureOf ageOfSub Muffet]}]
  (let [m {:strength :monotonic}]
    [["disjoint"
      #(v/assert % (list 'disjoint dog_t cat_t) 'CxUniverse m)
      (list dog_t Muffet) (list cat_t Muffet)
      [(list 'disjoint dog_t cat_t)]]
     ["disjoint_metatype"
      #(do (v/assert % (list 'disjoint_metatype species) 'CxUniverse m)
           (v/assert % (list species dog_t) 'CxUniverse m)
           (v/assert % (list species cat_t) 'CxUniverse m))
      (list dog_t Muffet) (list cat_t Muffet)
      [(list 'disjoint_metatype species) (list species dog_t) (list species cat_t)]]
     ["sibling_disjoint"
      #(do (v/assert % (list 'sibling_disjoint root_t) 'CxUniverse m)
           (v/assert % (list 'genl dog_t root_t) 'CxUniverse m)
           (v/assert % (list 'genl cat_t root_t) 'CxUniverse m))
      (list dog_t Muffet) (list cat_t Muffet)
      [(list 'sibling_disjoint root_t)]]
     ["partition"
      #(v/assert % (list 'partition animal_t dog_t cat_t) 'CxUniverse m)
      (list dog_t Muffet) (list cat_t Muffet)
      [(list 'partition animal_t dog_t cat_t)]]
     ["functional"
      #(do (v/assert % (list 'binary_predicate ageOf) 'CxUniverse m)
           (v/assert % (list 'functional ageOf) 'CxUniverse m))
      (list ageOf Muffet 3) (list ageOf Muffet 4)
      [(list 'functional ageOf)]]
     ["functional read down a genl edge"
      #(do (v/assert % (list 'binary_predicate measureOf) 'CxUniverse m)
           (v/assert % (list 'binary_predicate ageOfSub) 'CxUniverse m)
           (v/assert % (list 'functional measureOf) 'CxUniverse m)
           (v/assert % (list 'genl ageOfSub measureOf) 'CxUniverse m))
      (list ageOfSub Muffet 3) (list ageOfSub Muffet 4)
      [(list 'functional measureOf)]]]))

(deftest a-known-true-clash-is-stored-and-reported-in-either-arrival-order
  ;; decisions 8 and 15 of docs/reference.md: no clash is refused, and an all-monotonic
  ;; one is a hard clash, both members believed and the pair in `conflicts`
  (doseq [row-index (range 6)
          opposing-first? [true false]]
    (tu/with-kb [kb]
      (tu/with-terms [dog_t cat_t root_t species animal_t ageOf measureOf ageOfSub Muffet]
        (let [[label setup opposing arriving grounds]
              (nth (clash-shapes {:dog_t dog_t :cat_t cat_t :root_t root_t :species species
                                  :animal_t animal_t :ageOf ageOf :measureOf measureOf
                                  :ageOfSub ageOfSub :Muffet Muffet})
                   row-index)
              order (if opposing-first? [opposing arriving] [arriving opposing])]
          (setup kb)
          (doseq [s order] (v/assert kb s 'CxUniverse {:strength :monotonic}))
          (let [hs   (set (map #(v/handle-of kb % 'CxUniverse) order))
                ;; the fixture's KB is shared by the rows, so each row reads its own pair
                mine (fn [rs] (filterv #(some hs (:nogood %)) rs))]
            (is (every? some? hs) (str label ": both members are stored"))
            (is (every? #(v/ask? kb % 'CxUniverse) order) (str label ": both are believed"))
            (is (= [hs] (mapv :nogood (mine (v/conflicts kb))))
                (str label ": the pair is one conflict"))
            (is (= [(set (map #(v/handle-of kb % 'CxUniverse) grounds))]
                   (mapv #(set (map :handle (:grounds %))) (mine (v/conflicts kb))))
                (str label ": the conflict names the declarations it convicts through"))
            (is (empty? (mine (v/contradictions kb))) (str label ": and not a dilemma"))))))))

(deftest a-default-member-of-a-clash-against-known-true-content-is-stored-and-loses
  (doseq [row-index (range 6)]
    (tu/with-kb [kb]
      (tu/with-terms [dog_t cat_t root_t species animal_t ageOf measureOf ageOfSub Muffet]
        (let [[label setup opposing arriving]
              (nth (clash-shapes {:dog_t dog_t :cat_t cat_t :root_t root_t :species species
                                  :animal_t animal_t :ageOf ageOf :measureOf measureOf
                                  :ageOfSub ageOfSub :Muffet Muffet})
                   row-index)]
          (setup kb)
          (v/assert kb opposing 'CxUniverse {:strength :monotonic})
          (is (v/assert kb arriving 'CxUniverse) (str label ": stored"))
          (is (v/ask? kb opposing 'CxUniverse) (str label ": the known-true member stands"))
          (is (not (v/ask? kb arriving 'CxUniverse)) (str label ": the default one loses")))))))

(deftest try-assert-refuses-each-clash-assert-stores
  ;; The last row's arriving sentence is a `forced_decontextualized_predicate` declaration,
  ;; and the clash forms when it moves a premise stored in an unwired context into
  ;; CxUniverse.  `kept` is that premise, which stays where it was stored.
  (doseq [row-index (range 7)]
    (tu/with-kb [kb]
      (tu/with-terms [dog_t cat_t root_t species animal_t ageOf measureOf ageOfSub Muffet CxElse]
        (let [m {:strength :monotonic}
              [label setup opposing arriving _grounds kept]
              (nth (conj (clash-shapes {:dog_t dog_t :cat_t cat_t :root_t root_t :species species
                                        :animal_t animal_t :ageOf ageOf :measureOf measureOf
                                        :ageOfSub ageOfSub :Muffet Muffet})
                         ["functional, through a premise the forced declaration moves"
                          #(do (v/assert % (list 'binary_predicate ageOf) 'CxUniverse m)
                               (v/assert % (list 'functional ageOf) 'CxUniverse m)
                               (v/assert % (list ageOf Muffet 4) CxElse))
                          (list ageOf Muffet 3)
                          (list 'forced_decontextualized_predicate ageOf)
                          [(list 'functional ageOf)]
                          [(list ageOf Muffet 4) CxElse]])
                   row-index)]
          (setup kb)
          (let [h (v/assert kb opposing 'CxUniverse)
                e (try (v/try-assert kb arriving 'CxUniverse)
                       (catch clojure.lang.ExceptionInfo e (ex-data e)))]
            (is (= [:definitional-clash (if (< row-index 4) :disjoint :functional)
                    [{:handle h :sentence opposing :context 'CxUniverse}]]
                   [(:type e) (:violation e) (:clashes-with e)])
                label)
            (is (nil? (v/handle-of kb arriving 'CxUniverse)) (str label ": nothing stored"))
            (when-let [[s ctx] kept]
              (is (= [ctx] (v/contexts-of kb s)) (str label ": the premise is not moved")))))))))

(tu/deftest-kb try-assert-stores-a-sentence-that-opens-no-clash
  (tu/with-terms [dog_t cat_t Muffet Rex]
    (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
    (v/assert kb (list dog_t Muffet) 'CxUniverse)
    (let [h (v/try-assert kb (list cat_t Rex) 'CxUniverse)]
      (is (integer? h))
      (is (= h (v/handle-of kb (list cat_t Rex) 'CxUniverse))))))

;;; ── a verdict lives as long as its grounds ────────────────────────────

(tu/deftest-kb retracting-the-separation-revives-the-loser-decided-or-not
  ;; a reader decides the pair from current state on every read, so no verdict taken
  ;; while the declaration was believed outlives it; a `disjoint` is on the engine's
  ;; baseline roster, so retraction is what takes it away, and the retraction drops the
  ;; flat-cache entry before the settle runs
  (doseq [dog-strength [:monotonic :default]]
    (testing (str "with the pair " (if (= :monotonic dog-strength) "decided" "a dilemma"))
      (tu/with-kb [kb]
        (tu/with-terms [dog_t cat_t Muffet]
          (let [d (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)]
            (v/assert kb (list cat_t Muffet) 'CxUniverse)
            (v/assert kb (list dog_t Muffet) 'CxUniverse {:strength dog-strength})
            (v/retract! kb d))
          (is (not (v/disjoint? kb dog_t cat_t)))
          (is (v/ask? kb (list dog_t Muffet) 'CxUniverse))
          (is (v/ask? kb (list cat_t Muffet) 'CxUniverse)
              "the loser comes back with the separation that convicted it")
          (is (empty? (v/contradictions kb)))
          (is (:believed? (v/why-not kb (list cat_t Muffet) 'CxUniverse))
              "and nothing is left defeated by a pair no reader can name"))))))

(tu/deftest-kb defeating-the-edge-a-separation-is-read-over-revives-the-loser
  ;; an edge denied in its own context is a global defeat; `scoped_defeat_test` covers
  ;; the vantage below it
  (tu/with-kb [kb]
    (tu/with-terms [chi_t dog_t cat_t Kit]
      (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'genl chi_t dog_t) 'CxUniverse)
      (v/assert kb (list chi_t Kit) 'CxUniverse)
      (v/assert kb (list cat_t Kit) 'CxUniverse {:strength :monotonic})
      (is (not (v/ask? kb (list chi_t Kit) 'CxUniverse)) "decided against the membership")
      (v/assert kb (list 'not (list 'genl chi_t dog_t)) 'CxUniverse {:strength :monotonic})
      (is (not (v/disjoint? kb chi_t cat_t 'CxUniverse)))
      (is (v/ask? kb (list chi_t Kit) 'CxUniverse))
      (is (v/ask? kb (list cat_t Kit) 'CxUniverse)))))

(tu/deftest-kb retracting-a-functionality-revives-the-filler-it-convicted
  (tu/with-kb [kb]
    (tu/with-terms [ageOfs Af]
      (v/assert kb (list 'binary_predicate ageOfs) 'CxUniverse)
      (let [f (v/assert kb (list 'functional ageOfs) 'CxUniverse)]
        (v/assert kb (list ageOfs Af 3) 'CxUniverse {:strength :monotonic})
        (v/assert kb (list ageOfs Af 4) 'CxUniverse)
        (is (not (v/ask? kb (list ageOfs Af 4) 'CxUniverse)))
        (v/retract! kb f))
      (is (v/ask? kb (list ageOfs Af 3) 'CxUniverse))
      (is (v/ask? kb (list ageOfs Af 4) 'CxUniverse)))))

;;; ── what stays a refusal ──────────────────────────────────────────────

(tu/deftest-kb a-malformed-sentence-throws
  ;; no second believed sentex, so nothing to arbitrate
  (tu/with-kb [kb]
    (tu/with-terms [dog_t Muffet]
      (testing "a genl cycle"
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list 'genl dog_t dog_t) 'CxUniverse))))
      (testing "a genl of an individual"
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list 'genl Muffet dog_t) 'CxUniverse))))
      (testing "a non-ground fact"
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list dog_t '?x) 'CxUniverse)))))))

(tu/deftest-kb an-argument-constraint-is-not-a-nogood
  ;; convicted by the absence of a path, so there is no pair.  Pinned to the constraint
  ;; reading; the entailing one mints instead (docs/argtypes.md)
  (tu/without-entailing
   (tu/with-kb [kb]
     (tu/with-terms [person_t rock_t parentOf Boulder Muffet]
       (v/assert kb (list 'genl person_t 'thing) 'CxUniverse)
       (v/assert kb (list 'genl rock_t 'thing) 'CxUniverse)
       (v/assert kb (list 'arg parentOf 1 person_t) 'CxUniverse)
       (v/assert kb (list rock_t Boulder) 'CxUniverse)
       (is (thrown? clojure.lang.ExceptionInfo
                    (v/assert kb (list parentOf Boulder Muffet) 'CxUniverse))
           "refused at the entry point")
       (is (empty? (v/contradictions kb)))))))

;;; ── the loser has a reason ────────────────────────────────────────────

(tu/deftest-kb an-arbitrated-loser-is-stored-and-has-a-why-not
  ;; a dropped conclusion would leave `why-not` only `:not-stored`
  (tu/with-terms [dog_t fish_t Rex]
    (v/assert kb (list 'disjoint dog_t fish_t) 'CxUniverse)
    (v/assert kb (list dog_t Rex) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence [(list dog_t '?x)] (list fish_t '?x))))
              'CxUniverse)
    (let [h (v/handle-of kb (list fish_t Rex) 'CxUniverse)]
      (is (integer? h) "the conclusion is placed, not discarded")
      (is (not (v/in? kb h)))
      (is (= :defeated (:reason (v/why-not kb h)))))))

;;; ── what the report says ──────────────────────────────────────────────

(tu/deftest-kb a-definitional-dilemma-names-the-constraint-it-violated
  (tu/with-terms [dog_t cat_t Muffet]
    (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
    (v/assert kb (list dog_t Muffet) 'CxUniverse)
    (v/assert kb (fwd [(list dog_t '?x)] (list cat_t '?x)) 'CxUniverse)
    (testing "a definitional clash names its constraint"
      (is (= [:disjoint] (mapv :kind (v/contradictions kb)))))
    (testing "and ranks above a rebuttal"
      (is (every? #(<= 3 (:priority %)) (v/contradictions kb))))))

(tu/deftest-kb a-rebuttal-dilemma-has-no-constraint-to-name
  (tu/with-terms [flies Opus]
    (v/assert kb (list flies Opus) 'CxUniverse)
    (v/assert kb (list 'not (list flies Opus)) 'CxUniverse)
    (testing "a rebuttal names none"
      (is (= [nil] (mapv :kind (v/contradictions kb))))
      (is (= [[]] (mapv :grounds (v/contradictions kb)))))
    (testing "and ranks below a definitional clash"
      (is (every? #(<= (:priority %) 2) (v/contradictions kb))))))

(tu/deftest-kb a-dilemma-is-stored-as-one-contradicts-naming-its-members
  ;; the membership nogood is placed where both memberships and the separation are seen:
  ;; one `contradicts` naming the two members, and no `defeat`, since both are `:default`
  (tu/with-terms [dog_t cat_t Muffet]
    (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
    (let [dog    (v/assert kb (list dog_t Muffet) 'CxUniverse)
          before (v/sentex-count kb)]
      (v/assert kb (fwd [(list dog_t '?x)] (list cat_t '?x)) 'CxUniverse)
      (let [cat (v/handle-of kb (list cat_t Muffet) 'CxUniverse)
            [c] (v/sentexes-matching kb (list 'contradicts '?a '?b) '?ctx)]
        (is (= (set (map sx/sentex-handle [dog cat])) (set (rest (:sentence c)))))
        (is (= 'CxUniverse (:context c)))
        (is (= 'contradicts (first (:sentence (first (v/contradictions kb)))))
            "the report names the clash in the stored form's functor")
        (is (empty? (v/sentexes-with-functor kb 'defeat)))
        (is (= (+ 3 before) (v/sentex-count kb))
            "the rule, its conclusion and the contradicts")))))

(def ^:private report-keys
  "Every key a standing clash is reported with, whichever reading found it."
  #{:nogood :priority :sentence :handles :kind :sides :grounds})

(tu/deftest-kb an-irreducible-conflict-reports-the-full-shape
  (tu/with-terms [dog_t fish_t Rex]
    (v/assert kb (list 'disjoint dog_t fish_t) 'CxUniverse)
    (v/assert kb (list dog_t Rex) 'CxUniverse {:strength :monotonic})
    (v/assert-rule kb [(list dog_t '?x)] (list fish_t '?x) 'CxUniverse {:direction :forward})
    (let [c (first (v/conflicts kb))]
      (is (some? c) "an irreducible known-true clash")
      (is (= report-keys (into #{} (keys c))))
      (is (= :disjoint (:kind c)))
      (is (= 2 (count (:sides c))))
      (is (every? #(contains? % :justifications) (:sides c))
          "including what each side rests on — the material an application acts on")
      (is (= [:monotonic :monotonic] (mapv :defeat-class (:sides c)))))))

(tu/deftest-kb a-dilemma-reports-the-same-shape-as-a-conflict
  (tu/with-terms [dog_t cat_t Muffet]
    (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
    (v/assert kb (list dog_t Muffet) 'CxUniverse)
    (v/assert kb (fwd [(list dog_t '?x)] (list cat_t '?x)) 'CxUniverse)
    (is (= report-keys (into #{} (keys (first (v/contradictions kb)))))
        "the two readings differ in why the pair stands, not in what is reported")))

;;; ── the grounds: the declarations a report convicts through ─────────────

(defn- canonical
  "The sentence `s` is stored as in `CxUniverse`."
  [kb s]
  (v/sentence-of (v/sentex kb (v/handle-of kb s 'CxUniverse))))

(defn- grounds-of
  "The grounds' sentences of each conflict holding member `s` of `CxUniverse`: a KB the
  rows of one test share holds the other rows' conflicts too."
  [kb s]
  (let [h (v/handle-of kb s 'CxUniverse)]
    (into [] (comp (filter #(contains? (:nogood %) h)) (map #(mapv :sentence (:grounds %))))
          (v/conflicts kb))))

(deftest the-grounds-name-every-declaration-in-content-order-in-every-arrival-order
  (doseq [order (permutations [:d1 :d2 :m1 :m2])]
    (tu/with-kb [kb]
      (tu/with-terms [dog_t cat_t animal_t Muffet]
        (let [ws {:d1 (list 'disjoint dog_t cat_t) :d2 (list 'disjoint animal_t cat_t)
                  :m1 (list dog_t Muffet) :m2 (list cat_t Muffet)}]
          (v/assert kb (list 'genl dog_t animal_t) 'CxUniverse {:strength :monotonic})
          (doseq [k order] (v/assert kb (ws k) 'CxUniverse {:strength :monotonic}))
          (is (= [(sort nm/compare-form [(canonical kb (ws :d1)) (canonical kb (ws :d2))])]
                 (grounds-of kb (ws :m1)))
              (str order ": both separations, and not the edge one is read over")))))))

(tu/deftest-kb the-grounds-name-the-declaration-of-each-family
  (tu/with-terms [biggerThan parentOf priceIn typeLargerThan atOrAbove animal dog cat Ann Bob Cid Rex
                  Shop]
    (let [m {:strength :monotonic}]
      (doseq [[label decl members]
              [["asymmetric" (list 'asymmetric biggerThan)
                [(list biggerThan Ann Bob) (list biggerThan Bob Ann)]]
               ["anti_transitive" (list 'anti_transitive parentOf)
                [(list parentOf Ann Bob) (list parentOf Bob Cid) (list parentOf Ann Cid)]]
               ["covering" (list 'covering animal dog cat)
                [(list 'not (list dog Rex)) (list 'not (list cat Rex)) (list animal Rex)]]
               ["functionalInArg" (list 'functionalInArg priceIn 3)
                [(list priceIn Ann Shop 3) (list priceIn Ann Shop 4)]]
               ["irreflexive" (list 'irreflexive typeLargerThan) [(list typeLargerThan Ann Ann)]]
               ["anti_symmetric" (list 'anti_symmetric atOrAbove)
                [(list atOrAbove 1 2) (list atOrAbove 2 1)]]]]
        (tu/with-kb [kb]
          (v/assert kb decl 'CxUniverse m)
          (doseq [s members] (v/assert kb s 'CxUniverse m))
          (is (= [[(canonical kb decl)]] (grounds-of kb (first members))) label))))))

(tu/deftest-kb the-grounds-follow-a-retracted-declaration
  (tu/with-terms [dog_t cat_t animal_t Muffet]
    (let [m {:strength :monotonic}]
      (v/assert kb (list 'genl dog_t animal_t) 'CxUniverse m)
      (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse m)
      (v/assert kb (list 'disjoint animal_t cat_t) 'CxUniverse m)
      (v/assert kb (list dog_t Muffet) 'CxUniverse m)
      (v/assert kb (list cat_t Muffet) 'CxUniverse m)
      (is (= [2] (mapv (comp count :grounds) (v/conflicts kb))))
      (v/retract! kb (v/handle-of kb (list 'disjoint animal_t cat_t) 'CxUniverse))
      (is (= [[(canonical kb (list 'disjoint dog_t cat_t))]]
             (mapv #(mapv :sentence (:grounds %)) (v/conflicts kb)))
          "the clash stands on the one left, and names it alone"))))

(tu/deftest-kb a-declaration-no-vantage-sees-is-not-a-ground
  (tu/with-terms [CxAside dog_t cat_t Muffet]
    (let [m {:strength :monotonic}]
      (v/assert kb (list 'disjoint dog_t cat_t) CxAside m)
      (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse m)
      (v/assert kb (list dog_t Muffet) 'CxUniverse m)
      (v/assert kb (list cat_t Muffet) 'CxUniverse m)
      (is (= [[['CxUniverse (v/handle-of kb (list 'disjoint dog_t cat_t) 'CxUniverse)]]]
             (mapv #(mapv (juxt :context :handle) (:grounds %)) (v/conflicts kb)))))))

;;; ── the candidate set does not grow without bound ─────────────────────

(defn- live-memberships
  "The members of the membership nogoods the candidate index keeps, the settle's and the
  readers' (`decide`'s `::ngs`)."
  [kb]
  (into #{} (comp (mapcat val) (mapcat :members))
        (:vaelii.impl.decide.membership/ngs @(reasoning/nogood-candidates kb))))

(tu/deftest-kb a-pair-that-stops-clashing-leaves-the-candidate-set
  (tu/with-kb [kb]
    (tu/with-terms [dog_t cat_t Muffet]
      (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
      (v/assert kb (list dog_t Muffet) 'CxUniverse)
      (v/assert kb (list cat_t Muffet) 'CxUniverse)
      (is (= 2 (count (live-memberships kb))) "both members are candidates")
      (testing "retracting the separation retires them"
        (v/retract! kb (v/handle-of kb (list 'disjoint dog_t cat_t) 'CxUniverse))
        (is (empty? (v/contradictions kb)))
        (is (empty? (live-memberships kb))
            "both members still stored and believed, and they no longer clash"))
      (testing "and re-declaring it finds the pair again through the region"
        (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
        (is (= 1 (count (v/contradictions kb))))))))

(tu/deftest-kb retracting-one-functional-in-arg-position-retires-a-pair-the-other-does-not-hold
  (tu/with-kb [kb]
    (tu/with-terms [linkPred Shared]
      (v/assert kb (list 'functionalInArg linkPred 1) 'CxUniverse)
      (v/assert kb (list 'functionalInArg linkPred 2) 'CxUniverse)
      ;; numbers in the constrained slot (argument 1) are unmergeable, so a shared
      ;; determinant (argument 2) is a real clash rather than a merge; the determinants
      ;; differ under position 2, so only position 1 convicts this pair
      (v/assert kb (list linkPred 1 Shared) 'CxUniverse)
      (v/assert kb (list linkPred 2 Shared) 'CxUniverse)
      (is (= 1 (count (v/contradictions kb))) "position 1 convicts the pair")
      (testing "retracting position 1 retires it, though position 2 keeps linkPred marked"
        (v/retract! kb (v/handle-of kb (list 'functionalInArg linkPred 1) 'CxUniverse))
        (is (empty? (v/contradictions kb))
            "the constraint that convicted the pair is gone")))))

(tu/deftest-kb an-unrelated-membership-leaves-the-candidates-as-they-were
  ;; pinned by object identity: a term holding one membership is no candidate, so the
  ;; set the last write left is the set the next one reads
  (tu/with-kb [kb]
    (tu/with-terms [dog_t cat_t Muffet Rex]
      (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
      (v/assert kb (list dog_t Muffet) 'CxUniverse)
      (v/assert kb (list cat_t Muffet) 'CxUniverse)
      (let [before (:vaelii.impl.decide.membership/ngs @(reasoning/nogood-candidates kb))]
        (is (= 2 (count (live-memberships kb))))
        (testing "a membership of another term moves nothing"
          (v/assert kb (list dog_t Rex) 'CxUniverse)
          (is (identical? before (:vaelii.impl.decide.membership/ngs @(reasoning/nogood-candidates kb)))))
        (testing "and the separation leaving retires the pair"
          (v/retract! kb (v/handle-of kb (list 'disjoint dog_t cat_t) 'CxUniverse))
          (is (empty? (live-memberships kb)))
          (is (empty? (v/contradictions kb))))))))

(tu/deftest-kb a-pair-with-a-defeated-member-is-kept
  (tu/with-terms [dog_t fish_t Rex]
    (v/assert kb (list 'disjoint dog_t fish_t) 'CxUniverse)
    (v/assert kb (list dog_t Rex) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence [(list dog_t '?x)] (list fish_t '?x))))
              'CxUniverse)
    (let [h (v/handle-of kb (list fish_t Rex) 'CxUniverse)]
      (is (not (v/in? kb h)) "the derived side lost")
      (is (contains? (live-memberships kb) h)
          "and it stays a candidate, so the clash is read again if it revives"))))

(tu/deftest-kb a-carried-report-still-names-a-side-s-second-derivation
  ;; a redundant justification relabels nothing but still notes its conclusion touched;
  ;; `nmtms_test` pins the same for a rebuttal
  (tu/with-kb [kb]
    (tu/with-terms [dog_t cat_t Rex markA markB]
      (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
      (v/assert kb (list dog_t Rex) 'CxUniverse)
      (v/assert kb (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence [(list markA '?x)] (list cat_t '?x))))
                'CxUniverse)
      (v/assert kb (list markA Rex) 'CxUniverse)
      (let [h (v/handle-of kb (list cat_t Rex) 'CxUniverse)]
        (is (= 1 (count (v/contradictions kb))) "a default/default clash is a dilemma")
        (is (v/in? kb h))
        ;; a second rule reaching the same conclusion: belief is unmoved, so no relabel
        (v/assert kb (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence [(list markB '?x)] (list cat_t '?x))))
                  'CxUniverse)
        (v/assert kb (list markB Rex) 'CxUniverse)
        (is (= 2 (count (v/supporting-justifications kb h))))
        (let [side (some (fn [c] (some #(when (= h (:handle %)) %) (:sides c)))
                         (v/contradictions kb))]
          (is (some? side))
          (is (= :disjoint (:kind (first (v/contradictions kb)))))
          (is (= (count (v/supporting-justifications kb h))
                 (count (:justifications side)))
              "the report names both derivations, not the one it named last settle"))))))

(tu/deftest-kb an-equal-known-true-clash-is-a-conflict-not-a-dilemma
  ;; the third branch of `decide/verdict`: neither side can be defeated, so it is
  ;; irreducible and reported by `conflicts` — never thrown from inside the fixpoint
  (tu/with-terms [dog_t fish_t Rex]
    (v/assert kb (list 'disjoint dog_t fish_t) 'CxUniverse)
    (v/assert kb (list dog_t Rex) 'CxUniverse {:strength :monotonic})
    ;; a bare rule confers :monotonic and is capped by its antecedent, so the
    ;; conclusion is known-true too and ties with the membership
    (v/assert-rule kb [(list dog_t '?x)] (list fish_t '?x) 'CxUniverse {:direction :forward})
    (let [cs (v/conflicts kb)]
      (is (= 1 (count cs)))
      (is (= :disjoint (:kind (first cs))))
      (is (= #{(v/handle-of kb (list dog_t Rex)  'CxUniverse)
               (v/handle-of kb (list fish_t Rex) 'CxUniverse)}
             (:nogood (first cs)))))
    (is (empty? (v/contradictions kb)) "an irreducible clash is not a dilemma")))

(deftest a-membership-beside-a-denial-of-a-supertype-of-its-type-is-a-nogood-in-every-order
  ;; (dog Rex), dog ⊑ mammal ⊑ animal and (not (animal Rex)) cannot all hold, and no cover
  ;; is stored: a known-true pair is a `:supertype` conflict, and a default membership
  ;; loses to the known-true denial, taking the reached (animal Rex) with it.
  (doseq [[member expect] [[:monotonic :conflict] [:default :loses]]
          order           (permutations [:edge :member :deny])]
    (tu/with-kb [kb]
      (tu/with-terms [dog mammal animal Rex]
        (let [m      {:strength :monotonic}
              denial (list 'not (list animal Rex))
              writes {:edge   #(v/assert kb (list 'genl mammal animal) 'CxUniverse m)
                      :member #(v/assert kb (list dog Rex) 'CxUniverse {:strength member})
                      :deny   #(v/assert kb denial 'CxUniverse m)}]
          (v/assert kb (list 'genl dog mammal) 'CxUniverse m)
          (doseq [w order] ((writes w)))
          (let [hs   #{(v/handle-of kb (list dog Rex) 'CxUniverse)
                       (v/handle-of kb denial 'CxUniverse)}
                mine (fn [rs] (filterv #(= hs (:nogood %)) rs))]
            (testing [member order]
              (case expect
                :conflict (is (= [:supertype] (mapv :kind (mine (v/conflicts kb)))))
                :loses    (is (= [false false true]
                                 (mapv #(v/ask? kb % 'CxUniverse)
                                       [(list dog Rex) (list animal Rex) denial])))))))))))

;;; ── recomputed, never accumulated ─────────────────────────────────────

(tu/deftest-kb a-dilemma-goes-when-its-ingredient-does-and-comes-back-with-it
  (tu/with-kb [kb]
    (tu/with-terms [dog_t cat_t Muffet]
      (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
      (v/assert kb (list dog_t Muffet) 'CxUniverse)
      (v/assert kb (list cat_t Muffet) 'CxUniverse)
      (is (= 1 (count (v/contradictions kb))))
      (testing "retracting one membership retires the pair"
        (v/retract! kb (v/handle-of kb (list cat_t Muffet) 'CxUniverse))
        (is (empty? (v/contradictions kb)))
        (is (seq (v/sentexes-matching kb (list dog_t Muffet) 'CxUniverse))
            "and leaves the survivor alone"))
      (testing "and asserting it again brings the pair back"
        (v/assert kb (list cat_t Muffet) 'CxUniverse)
        (is (= 1 (count (v/contradictions kb)))))
      (testing "retracting the *declaration* retires it too — nothing separates them now"
        (v/retract! kb (v/handle-of kb (list 'disjoint dog_t cat_t) 'CxUniverse))
        (is (empty? (v/contradictions kb)))))))

(tu/deftest-kb an-arbitration-survives-a-rebuild
  (tu/with-terms [dog_t fish_t Rex]
    (v/assert kb (list 'disjoint dog_t fish_t) 'CxUniverse)
    (v/assert kb (list dog_t Rex) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence [(list dog_t '?x)] (list fish_t '?x))))
              'CxUniverse)
    (let [h (v/handle-of kb (list fish_t Rex) 'CxUniverse)]
      (is (not (v/in? kb h)) "defeated before the rebuild")
      (v/recover kb)
      (is (not (v/in? kb h)) "and still defeated after it"))))

(tu/deftest-kb a-dilemma-survives-a-rebuild
  (tu/with-terms [dog_t cat_t Muffet]
    (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
    (v/assert kb (list dog_t Muffet) 'CxUniverse)
    (v/assert kb (fwd [(list dog_t '?x)] (list cat_t '?x)) 'CxUniverse)
    (is (= 1 (count (v/contradictions kb))) "a dilemma before the rebuild")
    (v/recover kb)
    (is (= 1 (count (v/contradictions kb))) "and the same dilemma after it")))

;;; ── a declaration reaching content stored before it ───────────────────

(tu/deftest-kb a-functional-declaration-arriving-last-is-arbitrated
  ;; the `predicate-sentexes` sweep: the two values were admissible when written,
  ;; because nothing said the predicate was functional yet
  (tu/with-kb [kb]
    (tu/with-terms [birthYearOf Tom]
      (v/assert kb (list birthYearOf Tom 1980) 'CxUniverse)
      (v/assert kb (list birthYearOf Tom 1990) 'CxUniverse)
      (is (empty? (v/contradictions kb)) "nothing says one value only, yet")
      (v/assert kb (list 'functional birthYearOf) 'CxUniverse)
      (is (= [:functional] (mapv :kind (v/contradictions kb)))))))

(tu/deftest-kb a-genl-edge-arriving-last-is-arbitrated
  ;; the `instances-below` sweep: the held types were not themselves separated until an
  ;; edge put one of them under a separated type
  (tu/with-kb [kb]
    (tu/with-terms [dog_t canine_t cat_t Rex]
      (v/assert kb (list 'genl canine_t 'thing) 'CxUniverse)
      (v/assert kb (list 'genl cat_t 'thing) 'CxUniverse)
      (v/assert kb (list 'genl dog_t 'thing) 'CxUniverse)
      (v/assert kb (list 'disjoint canine_t cat_t) 'CxUniverse)
      (v/assert kb (list dog_t Rex) 'CxUniverse)
      (v/assert kb (list cat_t Rex) 'CxUniverse)
      (is (empty? (v/contradictions kb)) "a dog-cat is odd but nothing separates them")
      (v/assert kb (list 'genl dog_t canine_t) 'CxUniverse)
      (is (= [:disjoint] (mapv :kind (v/contradictions kb)))))))

(tu/deftest-kb a-disjoint-metatype-arriving-last-is-arbitrated
  ;; the `disjoint_metatype` sweep: the clique is a property of the code rather than
  ;; stored pairs, so the members have to be reached through `tax/metatype-members`
  (tu/with-kb [kb]
    (tu/with-terms [animal_species dog_t cat_t Muffet]
      (v/assert kb (list 'genl dog_t 'thing) 'CxUniverse)
      (v/assert kb (list 'genl cat_t 'thing) 'CxUniverse)
      (v/assert kb (list animal_species dog_t) 'CxUniverse)
      (v/assert kb (list animal_species cat_t) 'CxUniverse)
      (v/assert kb (list dog_t Muffet) 'CxUniverse)
      (v/assert kb (list cat_t Muffet) 'CxUniverse)
      (is (empty? (v/contradictions kb)) "the metatype is not disjoint yet")
      (v/assert kb (list 'disjoint_metatype animal_species) 'CxUniverse)
      (is (= [:disjoint] (mapv :kind (v/contradictions kb))))
      (testing "and dropping the metatype releases the pair, as it releases the clique"
        (v/retract! kb (v/handle-of kb (list 'disjoint_metatype animal_species) 'CxUniverse))
        (is (empty? (v/contradictions kb)))))))

(tu/deftest-kb a-metatype-member-arriving-last-is-arbitrated
  ;; the `metatype-member-reach` sweep: the trigger only the taxonomy identifies
  (tu/with-kb [kb]
    (tu/with-terms [animal_species dog_t cat_t Muffet]
      (v/assert kb (list 'genl dog_t 'thing) 'CxUniverse)
      (v/assert kb (list 'genl cat_t 'thing) 'CxUniverse)
      (v/assert kb (list animal_species dog_t) 'CxUniverse)
      (v/assert kb (list 'disjoint_metatype animal_species) 'CxUniverse)
      (v/assert kb (list dog_t Muffet) 'CxUniverse)
      (v/assert kb (list cat_t Muffet) 'CxUniverse)
      (is (empty? (v/contradictions kb))
          "cat_t is not a member yet, so the metatype separates nothing from dog_t")
      (v/assert kb (list animal_species cat_t) 'CxUniverse)
      (is (v/disjoint? kb dog_t cat_t) "the clique closed over the arriving member")
      (is (= [:disjoint] (mapv :kind (v/contradictions kb)))
          "the pair the new member separates is exposed but never arbitrated"))))

(tu/deftest-kb a-genlcx-edge-arriving-last-is-arbitrated
  ;; the `members-in-ancestors` sweep: neither writer could see the other, so both
  ;; memberships were admissible — until a visibility edge put them in one ancestor set
  (tu/with-kb [kb]
    (tu/with-terms [CxA CxB t1 t2 Pip]
      (v/assert kb (list 'genl t1 'thing) 'CxUniverse)
      (v/assert kb (list 'genl t2 'thing) 'CxUniverse)
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'disjoint t1 t2) 'CxUniverse)
      (v/assert kb (list t1 Pip) CxA)
      (v/assert kb (list t2 Pip) CxB)
      (is (not (v/sees? kb CxB CxA)))
      (is (empty? (v/contradictions kb))
          "each is admissible where it was written — neither context sees the other")
      (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)
      (is (= [:disjoint] (mapv :kind (v/contradictions kb)))
          "the visibility edge is what makes them a pair"))))

(tu/deftest-kb a-descended-functional-declaration-arriving-last-is-arbitrated
  ;; the `subtree-facts` sweep: `measureOf` holds no facts of its own
  (tu/with-kb [kb]
    (tu/with-terms [birthYearOf measureOf Tom]
      (v/assert kb (list birthYearOf Tom 1980) 'CxUniverse)
      (v/assert kb (list birthYearOf Tom 1990) 'CxUniverse)
      (v/assert kb (list 'genl birthYearOf measureOf) 'CxUniverse)
      (is (empty? (v/contradictions kb)) "nothing above birthYearOf is marked, yet")
      (v/assert kb (list 'functional measureOf) 'CxUniverse)
      (is (= [:functional] (mapv :kind (v/contradictions kb)))))))

(tu/deftest-kb a-descended-asymmetric-declaration-arriving-last-is-arbitrated
  ;; the same sweep for the other mark: the converse probe fans down the hierarchy and
  ;; the mark is read up it, so both halves of the question descend or neither does
  (tu/with-kb [kb]
    (tu/with-terms [muchLargerThan typeLargerThan Rex Pip]
      (v/assert kb (list muchLargerThan Rex Pip) 'CxUniverse)
      (v/assert kb (list muchLargerThan Pip Rex) 'CxUniverse)
      (v/assert kb (list 'genl muchLargerThan typeLargerThan) 'CxUniverse)
      (is (empty? (v/contradictions kb)))
      (v/assert kb (list 'asymmetric typeLargerThan) 'CxUniverse)
      (is (= [:asymmetric] (mapv :kind (v/contradictions kb)))))))

(tu/deftest-kb a-genl-edge-carrying-a-mark-down-is-arbitrated
  ;; the second reach a `genl` edge has, beside the memberships its type reading
  ;; implicates: a standing mark descends to a subtree that never carried one, so a pair
  ;; nothing separated a moment ago is a pair now, with neither fact relabelled
  (tu/with-kb [kb]
    (tu/with-terms [birthYearOf measureOf Tom]
      (v/assert kb (list 'functional measureOf) 'CxUniverse)
      (v/assert kb (list birthYearOf Tom 1980) 'CxUniverse)
      (v/assert kb (list birthYearOf Tom 1990) 'CxUniverse)
      (is (empty? (v/contradictions kb)) "the mark is above nothing they are under")
      (v/assert kb (list 'genl birthYearOf measureOf) 'CxUniverse)
      (is (= [:functional] (mapv :kind (v/contradictions kb)))))))

(tu/deftest-kb a-descended-pair-joins-the-candidate-set-and-is-re-derived
  ;; a pair the sweep never reaches never enters `:clashes`, so a third filler arriving
  ;; through the entry point would report two of the slot's three pairs
  (tu/with-kb [kb]
    (tu/with-terms [birthYearOf measureOf Tom Pip]
      (v/assert kb (list birthYearOf Tom 1980) 'CxUniverse)
      (v/assert kb (list birthYearOf Tom 1990) 'CxUniverse)
      (v/assert kb (list 'genl birthYearOf measureOf) 'CxUniverse)
      (v/assert kb (list 'functional measureOf) 'CxUniverse)
      (is (= 1 (count (v/contradictions kb))) "the sweep found it")
      (testing "an unrelated settle re-derives it rather than losing it"
        (v/assert kb (list birthYearOf Pip 2000) 'CxUniverse)
        (is (= 1 (count (v/contradictions kb)))))
      (testing "and a third filler adds its two pairs beside the first, not instead of it"
        (v/assert kb (list birthYearOf Tom 2000) 'CxUniverse)
        (is (= #{:functional} (set (mapv :kind (v/contradictions kb)))))
        (is (= 3 (count (v/contradictions kb)))
            "three values of one slot are three pairs")
        (is (contains? (set (map :sentence (v/contradictions kb)))
                       (list 'contradicts (list birthYearOf Tom 1980)
                             (list birthYearOf Tom 1990)))
            "the originally-missed pair among them")))))

;;; ── the pair only one context can see ─────────────────────────────────

;; docs/nmtms.md, "A defeat is scoped to its vantage".

(defn- straddle-kb
  "A general context, one that sees it, and the declaration in `CxUniverse` — the
  lattice every kind below is exercised over."
  [kb gen spec]
  (v/assert kb (list 'genlCx gen 'CxUniverse) 'CxUniverse)
  (v/assert kb (list 'genlCx spec gen) 'CxUniverse))

;; Each written general-last, the order the general side's own check cannot answer.

(tu/deftest-kb a-separation-across-a-visibility-edge-is-arbitrated
  (tu/with-terms [CxGen CxSpec dog_t cat_t Muffet]
    (straddle-kb kb CxGen CxSpec)
    (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
    (v/assert kb (list cat_t Muffet) CxSpec)
    (v/assert kb (list dog_t Muffet) CxGen)
    (is (= [:disjoint] (mapv :kind (v/contradictions kb))))))

(tu/deftest-kb a-functional-slot-filled-across-a-visibility-edge-is-arbitrated
  (tu/with-terms [CxGen CxSpec ageOf Tom]
    (straddle-kb kb CxGen CxSpec)
    (v/assert kb (list 'functional ageOf) 'CxUniverse)
    (v/assert kb (list ageOf Tom 6) CxSpec)
    (v/assert kb (list ageOf Tom 5) CxGen)
    (is (= [:functional] (mapv :kind (v/contradictions kb))))))

(tu/deftest-kb an-asymmetric-converse-across-a-visibility-edge-is-arbitrated
  (tu/with-terms [CxGen CxSpec biggerThan Ann Bob]
    (straddle-kb kb CxGen CxSpec)
    (v/assert kb (list 'asymmetric biggerThan) 'CxUniverse)
    (v/assert kb (list biggerThan Bob Ann) CxSpec)
    (v/assert kb (list biggerThan Ann Bob) CxGen)
    (is (= [:asymmetric] (mapv :kind (v/contradictions kb))))))

(tu/deftest-kb a-cover-refuted-across-a-visibility-edge-is-arbitrated
  (tu/with-terms [CxGen CxSpec animal dog cat Rex]
    (straddle-kb kb CxGen CxSpec)
    (v/assert kb (list 'covering animal dog cat) 'CxUniverse)
    (v/assert kb (list 'not (list dog Rex)) CxSpec)
    (v/assert kb (list 'not (list cat Rex)) CxSpec)
    (v/assert kb (list animal Rex) CxGen)
    (is (= [:cover] (mapv :kind (v/contradictions kb))))))

(tu/deftest-kb known-true-content-does-not-coexist-with-a-default-that-denies-it
  (tu/with-kb [kb]
    (tu/with-terms [CxGen CxSpec animal_t plant_t Ox]
      (straddle-kb kb CxGen CxSpec)
      (v/assert kb (list 'disjoint animal_t plant_t) 'CxUniverse)
      (v/assert kb (list plant_t Ox) CxSpec)
      (v/assert kb (list animal_t Ox) CxGen {:strength :monotonic})
      (is (v/ask? kb (list animal_t Ox) CxGen))
      (is (not (v/ask? kb (list plant_t Ox) CxSpec))
          "the default loses to known-true content it could not see when it was written")
      (is (empty? (v/contradictions kb)) "decided, so there is no dilemma left to report"))))

(tu/deftest-kb a-membership-stated-in-two-visible-contexts-forms-two-pairs
  (tu/with-kb [kb]
    (tu/with-terms [CxGen CxSpec dog_t cat_t Muffet]
      (straddle-kb kb CxGen CxSpec)
      (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
      (v/assert kb (list dog_t Muffet) CxGen)
      (v/assert kb (list dog_t Muffet) CxSpec)
      (v/assert kb (list cat_t Muffet) CxSpec)
      (is (= 2 (count (v/contradictions kb)))
          "one pair per opposing sentex, not one per opposing type")
      (is (= #{#{(v/handle-of kb (list cat_t Muffet) CxSpec)
                 (v/handle-of kb (list dog_t Muffet) CxGen)}
               #{(v/handle-of kb (list cat_t Muffet) CxSpec)
                 (v/handle-of kb (list dog_t Muffet) CxSpec)}}
             (into #{} (map :nogood) (v/contradictions kb)))))))

(tu/deftest-kb a-pair-reachable-from-several-viewers-is-one-entry
  ;; two maximal common descendants, so the check runs from each
  (tu/with-terms [CxA CxB CxK CxL t1 t2 Pip]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (doseq [k [CxK CxL]]
      (v/assert kb (list 'genlCx k CxA) 'CxUniverse)
      (v/assert kb (list 'genlCx k CxB) 'CxUniverse))
    (v/assert kb (list 'disjoint t1 t2) 'CxUniverse)
    (v/assert kb (list t1 Pip) CxA)
    (is (not (v/sees? kb CxB CxA)))
    (v/assert kb (list t2 Pip) CxB)
    (let [cs (v/contradictions kb)]
      (is (= 1 (count cs)) "one clash, however many contexts can see it")
      (is (= #{(v/handle-of kb (list t1 Pip) CxA)
               (v/handle-of kb (list t2 Pip) CxB)}
             (:nogood (first cs))))
      (is (= :disjoint (:kind (first cs)))))))

(tu/deftest-kb a-retraction-that-splits-the-visibility-releases-the-pair
  (tu/with-kb [kb]
    (tu/with-terms [CxGen CxSpec dog_t cat_t Muffet]
      (straddle-kb kb CxGen CxSpec)
      (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
      (v/assert kb (list cat_t Muffet) CxSpec)
      (v/assert kb (list dog_t Muffet) CxGen)
      (is (= 1 (count (v/contradictions kb))))
      (testing "the edge leaving takes the joint view with it"
        (v/retract! kb (v/handle-of kb (list 'genlCx CxSpec CxGen)
                                    'CxUniverse))
        (is (not (v/sees? kb CxSpec CxGen)))
        (is (empty? (v/contradictions kb))
            "both members still believed, and no context sees them together")
        (is (v/ask? kb (list dog_t Muffet) CxGen))
        (is (v/ask? kb (list cat_t Muffet) CxSpec)))
      (testing "and the edge returning brings the pair back"
        (v/assert kb (list 'genlCx CxSpec CxGen) 'CxUniverse)
        (is (= 1 (count (v/contradictions kb))))))))

;;; ── more than two ─────────────────────────────────────────────────────

(deftest ^:slow three-mutually-disjoint-memberships-report-all-three-pairs
  ;; a check stopping at its first violation would pick each membership's partner in
  ;; handle order; the permutation compares the set, which a count would not
  (let [ops [#(v/assert % '(disjoint za zb) 'CxUniverse)
             #(v/assert % '(disjoint zb zc) 'CxUniverse)
             #(v/assert % '(disjoint za zc) 'CxUniverse)
             #(v/assert % '(za Pip) 'CxUniverse)
             #(v/assert % '(zb Pip) 'CxUniverse)
             #(v/assert % '(zc Pip) 'CxUniverse)]
        observe (fn [kb]
                  ;; the *set* of clashing sentence pairs, keyed on content — handles
                  ;; differ between orderings, so comparing them would prove nothing
                  {:pairs (into #{}
                                (map (fn [c]
                                       (into #{} (map :sentence) (:sides c))))
                                (v/contradictions kb))
                   :believed (count (filter #(seq (v/sentexes-matching kb (list % 'Pip) 'CxUniverse))
                                            '[za zb zc]))})
        os (into #{} (map (fn [ordering]
                            (let [kb (tu/fresh)]
                              (doseq [op ordering] (op kb))
                              (observe kb))))
                 (permutations ops))]
    (is (= 1 (count os))
        (str "three-way clash: " (count os) " distinct outcomes across 720 orderings — "
             (pr-str os)))
    (testing "all three pairs, and all three memberships still believed"
      (is (= 3 (count (:pairs (first os)))))
      (is (= 3 (:believed (first os)))))
    (tu/clear-kb! (tu/test-kb))))

(deftest an-antitransitive-triple-settles-the-same-way-in-every-arrival-order
  ;; the mark and the three tuples in all 24 orders
  (let [ops [#(v/assert % '(anti_transitive zprecedes) 'CxUniverse)
             #(v/assert % '(zprecedes Za Zb) 'CxUniverse)
             #(v/assert % '(zprecedes Zb Zc) 'CxUniverse)
             #(v/assert % '(zprecedes Za Zc) 'CxUniverse)]
        observe (fn [kb]
                  {:believed (into #{} (filter #(seq (v/sentexes-matching kb % 'CxUniverse)))
                                   '[(zprecedes Za Zb) (zprecedes Zb Zc) (zprecedes Za Zc)])
                   :clashes  (into #{}
                                   (map (fn [c] [(:kind c)
                                                 (into #{} (map :sentence) (:sides c))]))
                                   (v/contradictions kb))
                   :conflicts (count (v/conflicts kb))})
        os (into #{} (map (fn [ordering]
                            (let [kb (tu/fresh)]
                              (doseq [op ordering] (op kb))
                              (observe kb))))
                 (permutations ops))]
    (is (= 1 (count os))
        (str "anti-transitive triple: " (count os) " distinct outcomes across 24 orderings — "
             (pr-str os)))
    (testing "one clash naming all three, and all three still believed"
      (is (= 3 (count (:believed (first os)))))
      (is (= 1 (count (:clashes (first os)))))
      (is (= [:anti-transitive] (mapv first (:clashes (first os)))))
      (is (= 3 (count (second (first (:clashes (first os)))))))
      (is (zero? (:conflicts (first os)))))
    (tu/clear-kb! (tu/test-kb))))

;;; ── a refuted cover: the membership and every part denied ─────────────

(deftest a-refuted-cover-settles-the-same-way-in-every-arrival-order
  ;; the declaration, the membership and the two denials in all 24 orders, per row of
  ;; strengths; the declaration arriving last is the retroactive sweep's case
  (let [sens {:decl '(covering zanimal zdog zcat)
              :memb '(zanimal ZRex)
              :n1   '(not (zdog ZRex))
              :n2   '(not (zcat ZRex))}
        observe (fn [kb]
                  {:believed  (into #{} (filter #(v/ask? kb (sens %) 'CxUniverse)) (keys sens))
                   :clashes   (into #{}
                                    (map (fn [c] [(:kind c)
                                                  (into #{} (map :sentence) (:sides c))]))
                                    (v/contradictions kb))
                   :conflicts (count (v/conflicts kb))})]
    (doseq [[strong expected]
            [[#{}
              {:believed  #{:decl :memb :n1 :n2}
               :clashes   #{[:cover #{(sens :memb) (sens :n1) (sens :n2)}]}
               :conflicts 0}]
             [#{:memb :n1}
              {:believed #{:decl :memb :n1} :clashes #{} :conflicts 0}]]]
      (let [os (into #{} (map (fn [ordering]
                                (let [kb (tu/fresh)]
                                  (doseq [k ordering]
                                    (v/assert kb (sens k) 'CxUniverse
                                              {:strength (if (strong k) :monotonic :default)}))
                                  (observe kb))))
                     (permutations (keys sens)))]
        (is (= #{expected} os) (str "known-true " (pr-str strong)))))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-cover-refutation-is-stored-whatever-the-classes
  ;; the last denial, written `:default` against a membership and a denial of `content`
  ;; class; `:via` puts the membership under the whole through a `genl` edge of that
  ;; strength.  The declaration and the edge are read through and never weighed.
  (doseq [[decl content via] [[:default   :default   nil]
                              [:monotonic :default   nil]
                              [:default   :monotonic nil]
                              [:monotonic :monotonic nil]
                              [:monotonic :monotonic :default]
                              [:monotonic :monotonic :monotonic]]]
    (tu/with-kb [kb]
      (tu/with-terms [animal mammal dog cat Rex]
        (v/assert kb (list 'covering animal dog cat) 'CxUniverse {:strength decl})
        (when via
          (v/assert kb (list 'genl mammal animal) 'CxUniverse {:strength via}))
        (v/assert kb (list (if via mammal animal) Rex) 'CxUniverse {:strength content})
        (v/assert kb (list 'not (list dog Rex)) 'CxUniverse {:strength content})
        (is (v/assert kb (list 'not (list cat Rex)) 'CxUniverse) (pr-str [decl content via]))
        (is (= (= :default content) (v/ask? kb (list 'not (list cat Rex)) 'CxUniverse))
            (str (pr-str [decl content via])
                 ": the default denial loses to known-true members and ties with default ones"))))))

(tu/deftest-kb a-derived-closing-step-is-placed-and-defeated-with-a-why-not
  ;; the firing row of docs/nmtms.md's table, for the three-member nogood
  (tu/with-terms [zprec zhints Qa Qb Qc]
    (v/assert kb (list 'anti_transitive zprec) 'CxUniverse)
    (v/assert kb (list zprec Qa Qb) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list zprec Qb Qc) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'set/defaultRule
                       (list 'set/forwardRule (vr/rule-sentence [(list zhints '?x '?y)] (list zprec '?x '?y))))
              'CxUniverse)
    (v/assert kb (list zhints Qa Qc) 'CxUniverse)
    (let [h (v/handle-of kb (list zprec Qa Qc) 'CxUniverse)]
      (is (some? h) "the conclusion is stored rather than dropped")
      (is (not (v/in? kb h)) "and defeated, being the one defeasible member")
      (is (= :defeated (:reason (v/why-not kb h))))
      (is (every? #(v/ask? kb % 'CxUniverse) [(list zprec Qa Qb) (list zprec Qb Qc)])
          "the known-true chain is untouched"))))

(tu/deftest-kb an-antitransitive-triple-survives-a-rebuild
  (tu/with-terms [zprec Ra Rb Rc]
    (v/assert kb (list 'anti_transitive zprec) 'CxUniverse)
    (v/assert kb (list zprec Ra Rb) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list zprec Rb Rc) 'CxUniverse)
    (v/assert kb (list zprec Ra Rc) 'CxUniverse {:strength :monotonic})
    (let [h (v/handle-of kb (list zprec Rb Rc) 'CxUniverse)]
      (is (not (v/in? kb h)) "the one defeasible step is defeated before the rebuild")
      (v/recover kb)
      (is (not (v/in? kb h)) "and still defeated after it"))))

(deftest an-antitransitive-declaration-arriving-last-is-arbitrated
  (tu/with-kb [kb]
    (tu/with-terms [zprec Pa Pb Pc]
      (v/assert kb (list zprec Pa Pb) 'CxUniverse)
      (v/assert kb (list zprec Pb Pc) 'CxUniverse)
      (v/assert kb (list zprec Pa Pc) 'CxUniverse)
      (is (empty? (v/contradictions kb)))
      (v/assert kb (list 'anti_transitive zprec) 'CxUniverse)
      (let [cs (v/contradictions kb)]
        (is (= 1 (count cs)) "the declaration convicts what was already stored")
        (is (= :anti-transitive (:kind (first cs))))
        (is (= 3 (count (:sides (first cs)))))))))

(tu/deftest-kb a-functional-clash-on-the-assert-path-is-stored
  (tu/with-kb [kb]
    (tu/with-terms [birthYearOf Tom]
      (v/assert kb (list 'functional birthYearOf) 'CxUniverse)
      (v/assert kb (list birthYearOf Tom 1980) 'CxUniverse)
      (is (v/assert kb (list birthYearOf Tom 1990) 'CxUniverse))
      (is (= [:functional] (mapv :kind (v/contradictions kb)))))))

;;; ── order independence, tested directly ───────────────────────────────

(deftest a-violating-set-settles-the-same-way-in-every-arrival-order
  ;; every order of the two memberships and the declaration lands on
  ;; one belief set and one dilemma.  24 orderings.
  (let [ops [#(v/assert % '(genl zdog thing) 'CxUniverse)
             #(v/assert % '(disjoint zdog zfish) 'CxUniverse)
             #(v/assert % '(zdog Rex) 'CxUniverse)
             #(v/assert % '(zfish Rex) 'CxUniverse)]
        observe (fn [kb]
                  {:dog        (boolean (seq (v/sentexes-matching kb '(zdog Rex) 'CxUniverse)))
                   :fish       (boolean (seq (v/sentexes-matching kb '(zfish Rex) 'CxUniverse)))
                   :dilemmas   (count (v/contradictions kb))
                   :conflicts  (count (v/conflicts kb))})
        os (into #{} (map (fn [ordering]
                            (let [kb (tu/fresh)]
                              (doseq [op ordering] (op kb))
                              (observe kb))))
                 (permutations ops))]
    (is (= 1 (count os))
        (str "disjointness clash: " (count os) " distinct outcomes across 24 orderings — "
             (pr-str os)))
    (testing "and the one outcome represents the clash rather than hiding it"
      (is (= {:dog true :fish true :dilemmas 1 :conflicts 0} (first os))))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-clash-across-a-visibility-edge-settles-the-same-way-in-every-arrival-order
  ;; belief and storage both agree.  120 orderings.
  (let [ops [#(v/assert % '(genlCx CxZGen CxUniverse) 'CxUniverse)
             #(v/assert % '(genlCx CxZSpec CxZGen) 'CxUniverse)
             #(v/assert % '(disjoint zoanimal zoplant) 'CxUniverse)
             #(v/assert % '(zoanimal OX) 'CxZGen {:strength :monotonic})
             #(v/assert % '(zoplant OX) 'CxZSpec)]
        observe (fn [kb]
                  {:known-true (v/ask? kb '(zoanimal OX) 'CxZGen)
                   :default    (v/ask? kb '(zoplant OX) 'CxZSpec)
                   :stored     (some? (v/handle-of kb '(zoplant OX) 'CxZSpec))
                   :dilemmas   (count (v/contradictions kb))
                   :conflicts  (count (v/conflicts kb))})
        os (into #{} (map (fn [ordering]
                            (let [kb (tu/fresh)]
                              (doseq [op ordering] (op kb))
                              (observe kb))))
                 (permutations ops))]
    (is (= 1 (count os))
        (str "clash across a visibility edge: " (count os)
             " distinct outcomes across 120 orderings — " (pr-str os)))
    (testing "and the one outcome defeats the default rather than leaving it beside content that denies it"
      (is (= {:known-true true :default false :stored true :dilemmas 0 :conflicts 0}
             (first os))))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-self-tuple-under-an-asymmetric-predicate-asserts-idempotently
  ;; `(P a a)` is its own converse, so a re-assert must not convict it against its own
  ;; stored copy.  Asymmetry does not imply irreflexivity (docs/taxonomy.md).
  (let [kb (tu/fresh)]
    (v/assert kb '(binary_predicate zSelfLarger) 'CxUniverse)
    (v/assert kb '(asymmetric zSelfLarger) 'CxUniverse)
    (let [h1 (v/assert kb '(zSelfLarger zrock zrock) 'CxUniverse {:strength :monotonic})
          h2 (v/assert kb '(zSelfLarger zrock zrock) 'CxUniverse {:strength :monotonic})]
      (is (= h1 h2) "the re-assert dedups to the handle the first one minted")
      (is (v/ask? kb '(zSelfLarger zrock zrock) 'CxUniverse)))
    (testing "and the mirror pair it is not a case of is a conflict"
      (v/assert kb '(zSelfLarger zbig zsmall) 'CxUniverse {:strength :monotonic})
      (is (v/assert kb '(zSelfLarger zsmall zbig) 'CxUniverse {:strength :monotonic}))
      (is (= [:asymmetric] (mapv :kind (v/conflicts kb)))))
    (testing "and a self tuple under a sub-predicate the mark descends to is the same case"
      (v/assert kb '(genl zSelfSmaller zSelfLarger) 'CxUniverse)
      (let [h1 (v/assert kb '(zSelfSmaller zpebble zpebble) 'CxUniverse {:strength :monotonic})
            h2 (v/assert kb '(zSelfSmaller zpebble zpebble) 'CxUniverse {:strength :monotonic})]
        (is (= h1 h2) "the descended mark convicts a pair, not a sentence against itself")))
    (tu/clear-kb! (tu/test-kb))))

(deftest an-asymmetric-violating-set-settles-the-same-way-in-every-arrival-order
  ;; the declaration may arrive before or after either direction of the relation
  (let [ops [#(v/assert % '(asymmetric zTypLarger) 'CxUniverse)
             #(v/assert % '(zTypLarger zdog zcat) 'CxUniverse)
             #(v/assert % '(zTypLarger zcat zdog) 'CxUniverse)]
        observe (fn [kb]
                  {:fwd      (v/ask? kb '(zTypLarger zdog zcat) 'CxUniverse)
                   :bwd      (v/ask? kb '(zTypLarger zcat zdog) 'CxUniverse)
                   :dilemmas (count (v/contradictions kb))})
        os (into #{} (map (fn [ordering]
                            (let [kb (tu/fresh)]
                              (doseq [op ordering] (op kb))
                              (observe kb))))
                 (permutations ops))]
    (is (= 1 (count os))
        (str "asymmetric pair: " (count os) " distinct outcomes across 6 orderings — "
             (pr-str os)))
    (is (= {:fwd true :bwd true :dilemmas 1} (first os)))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-report-orders-its-sides-by-content-not-by-arrival
  ;; `(first (:sides c))` follows content, as `:sentence` does
  (let [shape (fn [ops]
                (let [kb (tu/fresh)]
                  (doseq [op ops] (op kb))
                  (mapv (fn [r] [(:sentence r) (mapv :sentence (:sides r)) (:handles r)])
                        (v/contradictions kb))))
        strip (fn [rs] (mapv (fn [[s sides _]] [s sides]) rs))
        dog #(v/assert % '(zdog Rex) 'CxUniverse)
        cat #(v/assert % '(zcat Rex) 'CxUniverse)
        sep #(v/assert % '(disjoint zdog zcat) 'CxUniverse)
        pos #(v/assert % '(zbird Tweety) 'CxUniverse)
        neg #(v/assert % '(not (zbird Tweety)) 'CxUniverse)]
    (testing "a definitional clash"
      (is (= (strip (shape [sep dog cat])) (strip (shape [sep cat dog])))
          "the two sides swap places when the two memberships swap arrival order"))
    (testing "a plain rebuttal"
      (is (= (strip (shape [pos neg])) (strip (shape [neg pos])))))
    (testing "and `:handles` names the sides in the order `:sides` reports them"
      (let [[[_ sides handles]] (shape [sep dog cat])
            [[_ sides' handles']] (shape [sep cat dog])]
        (is (= sides sides'))
        (is (= 2 (count handles) (count handles')))))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-metatype-clique-settles-the-same-way-in-every-arrival-order
  ;; the metatype mark, the two type memberships of the clique and the clashing pair.
  ;; 120 orderings.
  (let [ops [#(v/assert % '(disjoint_metatype z_species) 'CxUniverse)
             #(v/assert % '(z_species zdog) 'CxUniverse)
             #(v/assert % '(z_species zcat) 'CxUniverse)
             #(v/assert % '(zdog Rex) 'CxUniverse)
             #(v/assert % '(zcat Rex) 'CxUniverse)]
        observe (fn [kb]
                  {:dog       (boolean (seq (v/sentexes-matching kb '(zdog Rex) 'CxUniverse)))
                   :cat       (boolean (seq (v/sentexes-matching kb '(zcat Rex) 'CxUniverse)))
                   :dilemmas  (count (v/contradictions kb))
                   :conflicts (count (v/conflicts kb))})
        os (into #{} (map (fn [ordering]
                            (let [kb (tu/fresh)]
                              (doseq [op ordering] (op kb))
                              (observe kb))))
                 (permutations ops))]
    (is (= 1 (count os))
        (str "metatype clique: " (count os) " distinct outcomes across 120 orderings — "
             (pr-str os)))
    (is (= {:dog true :cat true :dilemmas 1 :conflicts 0} (first os)))
    (tu/clear-kb! (tu/test-kb))))

;;; ── one entry point, whatever arrives first ───────────────────────────

(deftest the-constraints-option-is-refused-with-its-migration
  (let [e (try (v/open-kb (assoc (tu/scratch-space) :constraints :refuse)) nil
               (catch clojure.lang.ExceptionInfo e e))]
    (is (= :unknown-option (:type (ex-data e))))
    (is (= [:constraints] (:unknown (ex-data e))))
    (is (re-find #"conflicts" (ex-message e)) "the message names the reading that replaces it")))

(deftest a-declaration-arriving-last-reaches-back
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog_t cat_t Muffet]
      (v/assert kb (list dog_t Muffet) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list cat_t Muffet) 'CxUniverse)
      (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
      (is (v/ask? kb (list dog_t Muffet) 'CxUniverse))
      (is (not (v/ask? kb (list cat_t Muffet) 'CxUniverse))
          "the default loses to known-true content it was stored before")
      (is (not-any? #{:disjoint} (map :violation (v/violations kb)))
          "decided, so not also filed as exposed"))))

(deftest belief-and-storage-agree-whichever-arrived-first
  (doseq [strength [:default :monotonic]]
    (let [read (fn [ops]
                 (tu/with-neutral-kb [kb tu/fresh]
                   (tu/with-terms [dog_t cat_t Muffet]
                     (doseq [op (ops dog_t cat_t Muffet)] (op kb))
                     {:stored    (some? (v/handle-of kb (list cat_t Muffet) 'CxUniverse))
                      :known     (v/ask? kb (list dog_t Muffet) 'CxUniverse)
                      :arriving  (v/ask? kb (list cat_t Muffet) 'CxUniverse)
                      :conflicts (count (v/conflicts kb))})))
          facts-first  (read (fn [d c F]
                               [#(v/assert % (list d F) 'CxUniverse {:strength :monotonic})
                                #(v/assert % (list c F) 'CxUniverse {:strength strength})
                                #(v/assert % (list 'disjoint d c) 'CxUniverse)]))
          schema-first (read (fn [d c F]
                               [#(v/assert % (list 'disjoint d c) 'CxUniverse)
                                #(v/assert % (list d F) 'CxUniverse {:strength :monotonic})
                                #(v/assert % (list c F) 'CxUniverse {:strength strength})]))]
      (is (= facts-first schema-first) (str strength))
      (is (= (if (= :monotonic strength)
               {:stored true :known true :arriving true :conflicts 1}
               {:stored true :known true :arriving false :conflicts 0})
             facts-first)
          (str strength)))))

(deftest a-restart-agrees-with-the-live-kb
  ;; A namespaced-vector space collides with no concurrent run.
  (let [spaces {:space [::restart]}
        build! (fn [kb dog_t cat_t Muffet]
                 (v/assert kb (list dog_t Muffet) 'CxUniverse {:strength :monotonic})
                 (v/assert kb (list cat_t Muffet) 'CxUniverse)
                 (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse))
        believed (fn [kb dog_t cat_t Muffet]
                   [(v/in? kb (v/handle-of kb (list dog_t Muffet) 'CxUniverse))
                    (v/in? kb (v/handle-of kb (list cat_t Muffet) 'CxUniverse))])]
    (tu/with-terms [dog_t cat_t Muffet]
      (let [kb (doto (v/open-kb (assoc spaces :recover? false)) (tu/clear-kb!))]
        (try
          (build! kb dog_t cat_t Muffet)
          (is (= [true false] (believed kb dog_t cat_t Muffet))
              "the late declaration's clash is decided as it arrives")
          (is (not-any? #{:disjoint} (map :violation (v/violations kb))))
          (testing "recovered, the answer is the same"
            (let [re (v/open-kb (assoc spaces :recover? :auto))]
              (is (= [true false] (believed re dog_t cat_t Muffet)))))
          (finally (tu/clear-kb! kb)))))))

;;; ── declarations over related types ──────────────────────────────────

(tu/deftest-kb a-disjoint-over-related-types-is-reported-while-the-edge-and-the-cover-stand
  ;; The index keeps the related `disjoint`s under the `genl` generation and the cover
  ;; pairs at the store and removal choke points, so an edge or a cover leaving takes its
  ;; report with it, and a context that does not see the edge reads no clash.  The KB
  ;; loads no roster, so the declarations are asserted `:monotonic` as CxUniverse forces them.
  (tu/with-terms [animal_w dog_w cat_w CxRelSide]
    (let [clashes #(into #{} (map (fn [r] (into #{} (map :sentence) (:sides r)))) (v/conflicts kb))
          decl    (list 'disjoint dog_w animal_w)
          cover   (list 'covering animal_w dog_w cat_w)]
      (v/assert kb (list 'genl animal_w 'thing) 'CxUniverse)
      (v/assert kb (list 'genlCx CxRelSide 'CxUniverse) 'CxUniverse)
      (v/assert kb decl 'CxUniverse {:strength :monotonic})
      (is (= #{} (clashes)) "unrelated types")
      (let [e (v/assert kb (list 'genl dog_w animal_w) CxRelSide)]
        (is (= #{#{decl}} (clashes)) "an edge relates them")
        (is (= [#{CxRelSide}] (map clashes/report-vantages (v/conflicts kb)))
            "read where the edge is seen, and not above it")
        (v/retract! kb e))
      (is (= #{} (clashes)) "the edge leaving takes the clash")
      (let [c (v/assert kb cover 'CxUniverse {:strength :monotonic})]
        (is (= #{#{decl} #{cover decl}} (clashes)) "the cover states the part's edge")
        (v/retract! kb c))
      (is (= #{} (clashes)) "the cover leaving takes both"))))

;;; ── placed membership and related-types nogoods ──────────────────────

(defn- placed
  "The stored `contradicts` and `defeat` sentexes, each as `[sentence context]` with its
  `sentexHandle` arguments resolved."
  [kb]
  (into #{} (for [f '[contradicts defeat]
                  s (v/sentexes-with-functor kb f)]
              (tu/handle-free kb [(:sentence s) (:context s)]))))

(tu/deftest-kb a-membership-nogood-is-placed-and-no-reader-decides-it
  ;;   CxUniverse  (genl mammal_t thing) (genl dog_t mammal_t) (disjoint mammal_t reptile_t)
  ;;     ├─ CxL    (reptile_t Rex) default
  ;;     └─ CxR    (dog_t Rex) monotonic
  ;;   CxJ sees CxL and CxR
  (tu/with-terms [mammal_t dog_t reptile_t Rex CxL CxR CxJ]
    (doseq [[c up] [[CxL 'CxUniverse] [CxR 'CxUniverse] [CxJ CxL] [CxJ CxR]]]
      (v/assert kb (list 'genlCx c up) 'CxUniverse))
    (v/assert kb (list 'genl mammal_t 'thing) 'CxUniverse)
    (let [edge (v/assert kb (list 'genl dog_t mammal_t) 'CxUniverse)
          decl (v/assert kb (list 'disjoint mammal_t reptile_t) 'CxUniverse)
          los  (v/assert kb (list reptile_t Rex) CxL)
          win  (v/assert kb (list dog_t Rex) CxR {:strength :monotonic})
          L    [(list reptile_t Rex) CxL]
          W    [(list dog_t Rex) CxR]]
      (testing "the contradicts and the defeat of the default member are stored at CxJ"
        (is (= #{[(list 'contradicts W L) CxJ] [(list 'defeat L) CxJ]} (placed kb))))
      (testing "the declaration and the genl edge the reading climbed are grounds"
        (let [[c] (v/sentexes-with-functor kb 'contradicts)]
          (is (every? (set (mapcat :antecedents (v/supporting-justifications kb (:id c))))
                      [los win decl edge]))))
      (testing "no reader decides the pair, and the defeat hides the loser at CxJ alone"
        (is (false? (v/believed? kb los CxJ)))
        (is (true? (v/believed? kb los CxL))))
      (testing "retracting the edge the reading climbed takes the placed sentexes out"
        (v/retract! kb edge)
        (is (empty? (placed kb)))
        (is (true? (v/believed? kb los CxJ)))))))

(def ^:private merge-orders
  "The merge first, the merge last, and two interleavings of the four writes."
  [[:merge :pos :neg :rule] [:pos :neg :rule :merge] [:pos :merge :neg :rule] [:rule :neg :merge :pos]])

(defn- merged-membership-reading
  "In a fresh KB where CxB sees CxA, CxA sees CxUniverse and CxUniverse states
  (disjoint dog_t cat_t), the writes `ops` in order: `:pos` (dog_t Zz) default in CxA,
  `:neg` (cat_t Zz) monotonic in N, `:rule` (dog_t ?x) => (barks ?x) forward in CxA, and
  `:merge` (rewriteOf Aa Zz) monotonic in N, where N is CxA for `:same` and CxB for
  `:split`.  Returns the placed sentences and the belief at N of (dog_t Zz) in CxA,
  (dog_t Aa) in N and (barks Aa) in N (nil when not stored)."
  [{:keys [dog_t cat_t barks Zz Aa CxA CxB]} shape ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse {:strength :monotonic})
    (let [n (if (= shape :split) CxB CxA)]
      (doseq [op ops]
        (case op
          :pos   (v/assert kb (list dog_t Zz) CxA)
          :neg   (v/assert kb (list cat_t Zz) n {:strength :monotonic})
          :rule  (v/assert kb (list 'implies (list dog_t '?x) (list barks '?x)) CxA {:direction :forward})
          :merge (v/assert kb (list 'rewriteOf Aa Zz) n {:strength :monotonic})))
      (let [bel (fn [s c] (when-let [h (v/handle-of kb s c)] (v/believed? kb h n)))]
        {:placed    (placed kb)
         :at-reader [(bel (list dog_t Zz) CxA) (bel (list dog_t Aa) n) (bel (list barks Aa) n)]}))))

(deftest a-membership-nogood-with-a-superseded-member-is-placed-alike-in-every-arrival-order
  (tu/with-terms [dog_t cat_t barks Zz Aa CxA CxB]
    (let [terms {:dog_t dog_t :cat_t cat_t :barks barks :Zz Zz :Aa Aa :CxA CxA :CxB CxB}]
      (doseq [shape [:same :split]]
        (testing shape
          (let [rs (mapv #(merged-membership-reading terms shape %) merge-orders)]
            (is (= 1 (count (into #{} (map :placed) rs))) "the placed sentences")
            (is (= 1 (count (into #{} (map :at-reader) rs))) "belief at the merging reader")
            (is (every? #(some #{Zz} (tree-seq coll? seq (:placed %))) rs)
                "the superseded spelling's nogood stays placed")
            (is (= [false false false] (:at-reader (first rs))) "the defeat of (dog_t Zz) hides (barks Aa)")))))))

(defn- unmerged-reader-reading
  "In a fresh KB where CxB sees CxA and CxA sees CxUniverse, CxA states (genl dog mammal),
  (genl mammal animal), (disjoint animal plant) and (canine ?x) => (dog ?x), and the
  writes `ops` arrive in order: `:merge` (sameAs CI1 CI5) monotonic in CxA with an
  `except` of it in CxB, `:plant` (plant CI5) default in CxA, `:canine` (canine CI5)
  default in CxA.  Returns what CxB, which does not believe the merge, answers about CI5
  and CI1, and the sides of the clashes it reports."
  [{:keys [canine dog mammal animal plant CI1 CI5 CxA CxB]} ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (let [m {:strength :monotonic}]
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse m)
      (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse m)
      (v/assert kb (list 'genl dog mammal) CxA m)
      (v/assert kb (list 'genl mammal animal) CxA m)
      (v/assert kb (list 'disjoint animal plant) CxA m)
      (v/assert kb (list 'implies (list canine '?x) (list dog '?x)) CxA {:direction :forward})
      (doseq [op ops]
        (case op
          :merge  (let [h (v/assert kb (list 'sameAs CI1 CI5) CxA m)]
                    (v/assert kb (list 'except (list 'sentexHandle h)) CxB m))
          :plant  (v/assert kb (list plant CI5) CxA)
          :canine (v/assert kb (list canine CI5) CxA)))
      {:asks    (mapv #(v/ask? kb % CxB)
                      [(list canine CI5) (list dog CI5) (list animal CI5) (list plant CI5) (list dog CI1)])
       :reports (into #{} (map #(into #{} (map (juxt :sentence :context)) (:sides %)))
                      (v/contradictions kb CxB))})))

(deftest a-context-that-excepts-the-merge-reads-the-superseded-spelling-alike-in-both-orders
  ;; CxA supersedes the CI5 spellings, and only the merge-last order stores (dog CI5) in
  ;; CxA, fired before the merge; CxB restates CI5 for itself in both orders
  (tu/with-terms [canine dog mammal animal plant CI1 CI5 CxA CxB]
    (let [terms {:canine canine :dog dog :mammal mammal :animal animal :plant plant
                 :CI1 CI1 :CI5 CI5 :CxA CxA :CxB CxB}
          early (unmerged-reader-reading terms [:merge :plant :canine])
          late  (unmerged-reader-reading terms [:canine :plant :merge])]
      (is (= early late))
      (is (= [true true true true false] (:asks early)))
      (is (= #{#{[(list dog CI5) CxB] [(list plant CI5) CxB]}} (:reports early))))))

(tu/deftest-kb a-disjoint-over-related-types-is-placed-as-a-contradicts
  ;; the declaration is its nogood's one member and the edge its ground; the declaration is
  ;; on the forced-monotonic roster, so nothing is defeated
  (tu/with-terms [animal_w dog_w CxRelSide]
    (v/assert kb (list 'genl animal_w 'thing) 'CxUniverse)
    (v/assert kb (list 'genlCx CxRelSide 'CxUniverse) 'CxUniverse)
    (let [decl (list 'disjoint dog_w animal_w)
          _    (v/assert kb decl 'CxUniverse {:strength :monotonic})
          e    (v/assert kb (list 'genl dog_w animal_w) CxRelSide)]
      (is (= #{[(list 'contradicts [decl 'CxUniverse]) CxRelSide]} (placed kb)))
      (v/retract! kb e)
      (is (empty? (placed kb))))))

(tu/deftest-kb a-separated-pair-among-many-types-gives-one-nogood-in-every-arrival-order
  ;; the pair's two memberships arrive first, last and apart among 200 memberships of
  ;; types no separation reaches, in both orders; each order is retracted before the next
  (tu/with-terms [dog_t cat_t Rex]
    (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse {:strength :monotonic})
    (let [rest  (mapv (fn [_] [(list (tu/tmp-type "other") Rex) {}]) (range 200))
          pair  [[(list dog_t Rex) {:strength :monotonic}] [(list cat_t Rex) {}]]
          ;; members in content order: tmp_cat… before tmp_dog…
          want  #{[(list 'contradicts [(list cat_t Rex) 'CxUniverse] [(list dog_t Rex) 'CxUniverse])
                   'CxUniverse]
                  [(list 'defeat [(list cat_t Rex) 'CxUniverse]) 'CxUniverse]}
          order (fn [[p q] [a b]]
                  (concat (subvec rest 0 p) [a] (subvec rest p q) [b] (subvec rest q)))
          seen  (for [pq [[0 0] [0 200] [100 100] [200 200] [1 150]]
                      ab [pair (rseq pair)]]
                  (let [hs (mapv (fn [[s o]] (v/assert kb s 'CxUniverse o)) (order pq ab))
                        got (placed kb)]
                    (run! #(v/retract! kb %) (rseq hs))
                    [got (placed kb)]))]
      (is (= [[want #{}]] (distinct (doall seen)))))))

;;; ── the reports read the placed sentexes ─────────────────────────────

(defn- reports-nogood?
  "Does one of `reports` name the members `hs`?"
  [reports hs]
  (boolean (some #(= (set hs) (:nogood %)) reports)))

(tu/deftest-kb a-reader-reports-no-dilemma-whose-ground-it-excepts
  ;;   CxUniverse   (disjoint dog cat)
  ;;     ├─ CxA     (cat Rex) default
  ;;     └─ CxB     (dog Rex) default
  ;;   CxW sees CxA and CxB: the dilemma's placement
  ;;   CxR sees CxW and excepts the declaration
  (tu/with-terms [CxA CxB CxW CxR cat dog Rex]
    (doseq [t [cat dog]] (v/assert kb (list 'genl t 'thing) 'CxUniverse))
    (doseq [[k up] [[CxA 'CxUniverse] [CxB 'CxUniverse] [CxW CxA] [CxW CxB] [CxR CxW]]]
      (v/assert kb (list 'genlCx k up) 'CxUniverse))
    (let [c (v/assert kb (list cat Rex) CxA)
          d (v/assert kb (list dog Rex) CxB)
          j (v/assert kb (list 'disjoint dog cat) 'CxUniverse {:strength :monotonic})]
      (v/assert kb (list 'except (sx/sentex-handle j)) CxR {:strength :monotonic})
      (is (reports-nogood? (v/contradictions kb CxW) [c d]))
      (testing "the reader excepting the separation believes both members and reads no dilemma"
        (is (not (reports-nogood? (v/contradictions kb CxR) [c d])))
        (is (true? (v/believed? kb c CxR)))
        (is (true? (v/believed? kb d CxR)))))))

(tu/deftest-kb a-conflict-a-reader-s-excepts-lower-to-a-tie-is-its-dilemma
  ;;   CxUniverse   (disjoint dog cat)
  ;;     ├─ CxA     (cat Rex) default, and monotonic through (cat_src Rex)
  ;;     ├─ CxB     (dog Rex) default, and monotonic through (dog_src Rex)
  ;;     └─ CxHide  (except (cat_src Rex)), (except (dog_src Rex))
  ;;   CxW sees CxA and CxB: the placement, a conflict there
  ;;   CxZ sees CxW and CxHide: both members are defaults there, and tie
  (tu/with-terms [CxA CxB CxHide CxW CxZ cat dog cat_src dog_src Rex]
    (doseq [t [cat dog]] (v/assert kb (list 'genl t 'thing) 'CxUniverse))
    (doseq [[k up] [[CxA 'CxUniverse] [CxB 'CxUniverse] [CxHide 'CxUniverse]
                    [CxW CxA] [CxW CxB] [CxZ CxW] [CxZ CxHide]]]
      (v/assert kb (list 'genlCx k up) 'CxUniverse))
    (let [M   {:strength :monotonic}
          c   (v/assert kb (list cat Rex) CxA)
          d   (v/assert kb (list dog Rex) CxB)
          srcs (for [[t src cx] [[cat cat_src CxA] [dog dog_src CxB]]]
                 (do (v/assert kb (fwd [(list src '?x)] (list t '?x)) cx M)
                     (v/assert kb (list src Rex) cx M)))]
      (doseq [s srcs] (v/assert kb (list 'except (sx/sentex-handle s)) CxHide M))
      (v/assert kb (list 'disjoint dog cat) 'CxUniverse M)
      (is (reports-nogood? (v/conflicts kb) [c d]) "a conflict where it is placed")
      (is (not (reports-nogood? (v/contradictions kb CxW) [c d])))
      (testing "the reader below reads two defaults, believes both, and reports the tie"
        (is (true? (v/believed? kb c CxZ)))
        (is (true? (v/believed? kb d CxZ)))
        (is (reports-nogood? (v/contradictions kb CxZ) [c d]))))))

(tu/deftest-kb a-dilemma-over-a-member-resting-on-a-loser-is-not-reported-where-the-member-is-not-believed
  ;;   CxUniverse   (disjoint dog cat)
  ;;     ├─ CxA     (feline Rex) default, and (feline ?x) ⇒ (cat ?x): (cat Rex) rests on it
  ;;     ├─ CxB     (dog Rex) default
  ;;     └─ CxN     (not (feline Rex)) monotonic
  ;;   CxAB sees CxA and CxB: the dilemma {(cat Rex), (dog Rex)} is placed there
  ;;   CxAN sees CxA and CxN: the negation pair is placed there, defeating (feline Rex)
  ;;   CxZ sees CxAB and CxAN: (cat Rex) rests on a loser there
  (tu/with-terms [CxA CxB CxN CxAB CxAN CxZ cat dog feline Rex]
    (doseq [t [cat dog feline]] (v/assert kb (list 'genl t 'thing) 'CxUniverse))
    (doseq [[k up] [[CxA 'CxUniverse] [CxB 'CxUniverse] [CxN 'CxUniverse]
                    [CxAB CxA] [CxAB CxB] [CxAN CxA] [CxAN CxN] [CxZ CxAB] [CxZ CxAN]]]
      (v/assert kb (list 'genlCx k up) 'CxUniverse))
    (v/assert kb (fwd [(list feline '?x)] (list cat '?x)) CxA)
    (v/assert kb (list feline Rex) CxA)
    (v/assert kb (list 'not (list feline Rex)) CxN {:strength :monotonic})
    (v/assert kb (list dog Rex) CxB)
    (v/assert kb (list 'disjoint dog cat) 'CxUniverse {:strength :monotonic})
    (let [c (v/handle-of kb (list cat Rex) CxA)
          d (v/handle-of kb (list dog Rex) CxB)]
      (testing "the placement context believes both members and reports the dilemma"
        (is (reports-nogood? (v/contradictions kb CxAB) [c d]))
        (is (reports-nogood? (v/contradictions kb) [c d])))
      (testing "below the defeat, the member resting on the loser is not believed"
        (is (false? (v/believed? kb c CxZ)))
        (is (true? (v/believed? kb d CxZ)))
        (is (not (reports-nogood? (v/contradictions kb CxZ) [c d])))))))
