;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.late-route-test
  "A shorter `genl` route arriving after a firing leaves belief and the justifications the
  same as the order that brings it first.

  A firing that climbs a `genl` path names one route to it (`checks/edge-support`,
  `taxonomy/reach-support`).  A route the witness rule names later replaces the one the
  firing named before (`special/drop-replaced-routes!`), so the two arrival orders store
  the same justifications, route edges included, and retracting the late route
  re-derives the firing over the one that survives.

  Four shapes, each stated in CxUniverse at `:monotonic`: an argument-type entailment
  down a predicate chain, a forward rule over a type chain, the same rule over an edge a
  `genlArg` mints, and a `transitiveInArgInverse` preservation.  Then the upper layer and the
  starter, authored order against the content order their own text export reloads in."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.order-independence-test :as oi]
            [vaelii.test-util :as tu])
  (:import [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(def ^:private U 'CxUniverse)

(defn- content [kb h]
  (when-let [sx (v/sentex kb h)] [(v/sentence-of sx) (:context sx)]))

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

(defn- shapes
  "`[label base late goal]` over fresh terms: `late` is the shorter route."
  []
  (tu/with-terms [animal parentOf fatherOf midParent Ann Mary dog mammal noted Rex kindUnder Zoo
                  chi mid cat typeLargerThan]
    (let [chain [(list 'genl dog mammal) (list 'genl mammal animal) (list 'genl animal 'thing)
                 (list dog Rex)
                 (list 'set/forwardRule (list 'implies (list animal '?x) (list noted '?x)))]]
      [[:argtype
        [(list 'genl animal 'thing) (list 'arg parentOf 1 animal)
         (list 'genl fatherOf midParent) (list 'genl midParent parentOf) (list fatherOf Ann Mary)]
        [(list 'genl fatherOf parentOf)]
        (list animal Ann)]
       [:rule chain [(list 'genl dog animal)] (list noted Rex)]
       [:minted chain [(list 'genlArg kindUnder 1 animal) (list kindUnder dog Zoo)] (list noted Rex)]
       [:preservation
        [(list 'genl chi mid) (list 'genl mid dog) (list 'genl dog 'thing)
         (list typeLargerThan dog cat) (list 'transitiveInArgInverse typeLargerThan 1 'genl)
         (list 'set/forwardRule (list 'implies (list typeLargerThan '?x '?y) (list noted '?x '?y)))]
        [(list 'genl chi dog)]
        (list noted chi cat)]])))

(defn- build
  "Assert `steps` in order, then retract `retracted`; the goal's belief and the reasons."
  ([steps goal] (build steps goal []))
  ([steps goal retracted]
   (tu/with-neutral-kb [kb tu/fresh]
     (binding [checks/*assertive-arg-types?* true]
       (doseq [s steps] (v/assert kb s U {:strength :monotonic}))
       (doseq [s retracted] (v/retract! kb (v/handle-of kb s U)))
       {:believed (boolean (some-> (v/handle-of kb goal U) (#(v/believed? kb % U))))
        :reasons  (reasons kb)}))))

(deftest a-late-shorter-route-leaves-belief-and-justifications-as-the-early-one-does
  (doseq [[label base late goal] (shapes)]
    (testing (name label)
      (let [late-last  (build (concat base late) goal)
            late-first (build (concat late base) goal)]
        (is (:believed late-last))
        (is (= late-first late-last))))))

(deftest retracting-the-late-route-re-derives-over-the-one-that-survives
  (doseq [[label base late goal] (shapes)]
    (testing (name label)
      (let [kept (butlast late)
            gone (build (concat base late) goal [(last late)])]
        (is (:believed gone))
        (is (= (build (concat base kept) goal) gone))))))

(deftest a-stated-route-withdrawing-a-mint-keeps-the-firings-the-mint-carried
  ;; A firing that climbed a minted edge loses its justification when a stated route makes
  ;; the mint redundant and the settle withdraws it.  Its conclusion stands on a second
  ;; firing here, and the firing over the minted edge is still owed: the order that states
  ;; the route first draws it over the route, so this one draws it again over the route
  ;; rather than keep only the firing that happened not to climb the mint.
  (tu/with-terms [animal mammal dog cat kindUnder noted Rex Zoo]
    (let [base [(list 'genl animal 'thing) (list 'genl cat animal)
                (list 'set/forwardRule (list 'implies (list animal '?x) (list noted '?x)))
                (list cat Rex) (list dog Rex)
                (list 'genlArg kindUnder 1 animal) (list kindUnder dog Zoo)]
          late [(list 'genl mammal animal) (list 'genl dog mammal)]
          goal (list noted Rex)
          late-last  (build (concat base late) goal)
          late-first (build (concat late base) goal)]
      (is (:believed late-last))
      (is (= late-first late-last)))))

;; ---- two firings over the same facts, the literals swapped --------------------------
;;
;; `(kind Xa)` and `(sort Xa)` each reach both literals of `(inspace ?x) ∧ (intime ?x)`, so
;; four firings conclude `(noted Xa)`: both literals through `kind`, both through `sort`,
;; and two that pair the two facts with the literals swapped.  The swapped pair share
;; informant, bindings and facts and differ only in `genl` edges.

(defn- pairing-steps
  "`[edges facts goal]` over fresh terms; `edges` route each type to both literals."
  [kind sort inspace intime noted Xa]
  [[(list 'genl kind inspace) (list 'genl kind intime)
    (list 'genl sort inspace) (list 'genl sort intime)]
   [(list kind Xa) (list sort Xa)
    (list 'set/forwardRule (list 'implies (list 'and (list inspace '?x) (list intime '?x))
                                 (list noted '?x)))]
   (list noted Xa)])

(defn- support-of
  "The justifications of `goal` as `{antecedent-sentences id}`."
  [kb goal]
  (into {} (map (fn [j] [(into #{} (map #(first (content kb %))) (:antecedents j)) (:id j)]))
        (v/supporting-justifications kb (v/handle-of kb goal U))))

(deftest two-firings-that-swap-the-literals-are-both-stored-in-every-order
  (tu/with-terms [kind sort inspace intime noted Xa]
    (let [[edges facts goal] (pairing-steps kind sort inspace intime noted Xa)
          [k s]    (map #(list % Xa) [kind sort])
          mixed    #{#{k s (list 'genl kind inspace) (list 'genl sort intime)}
                     #{k s (list 'genl sort inspace) (list 'genl kind intime)}}
          readings (for [order (oi/permutations facts)]
                     (tu/with-neutral-kb [kb tu/fresh]
                       (doseq [x (concat edges order)] (v/assert kb x U {:strength :monotonic}))
                       [(support-of kb goal) (reasons kb)]))]
      (is (= 6 (count readings)))
      (is (every? #(= 4 (count (first %))) readings))
      (is (every? #(every? (set (keys (first %))) mixed) readings))
      (is (apply = (map second readings))))))

(deftest a-genlCx-round-trip-leaves-the-justifications-of-swapped-firings-as-they-were
  ;; the teardown of the edge re-joins the facts under it (`settle-after-teardown!`), which
  ;; re-derives each firing over `(kind Xa)` and `(sort Xa)`
  (doseq [flip [identity reverse]]
    (tu/with-terms [kind sort inspace intime noted Xa Yb CxLeft]
      (let [[edges [kx sx rule]] (pairing-steps kind sort inspace intime noted Xa)]
        (tu/with-neutral-kb [kb tu/fresh]
          (doseq [x (concat [(list 'genl inspace 'thing) (list 'genl intime 'thing)] edges [rule]
                            (flip [kx sx]))]
            (v/assert kb x U {:strength :monotonic}))
          (let [before (tu/justification-ids kb)
                edge   (v/assert kb (list 'genlCx CxLeft U) U)]
            (v/assert kb (list kind Yb) CxLeft)
            (v/retract! kb edge)
            (v/retract! kb (v/handle-of kb (list kind Yb) CxLeft))
            (is (= before (tu/justification-ids kb)))))))))

(deftest a-late-shorter-route-replaces-only-the-firing-with-the-same-pairing
  ;; `kind` reaches `inspace` through `mid` until the direct edge arrives: the firing pairing
  ;; `(kind Xa)` with `inspace` moves to the direct edge, and the firing pairing `(sort Xa)`
  ;; with `inspace` keeps its justification
  (tu/with-terms [kind sort mid inspace intime noted Xa]
    (let [[edges facts goal] (pairing-steps kind sort inspace intime noted Xa)
          direct (list 'genl kind inspace)
          chain  (into [(list 'genl kind mid) (list 'genl mid inspace)] (remove #{direct}) edges)
          [k s]  (map #(list % Xa) [kind sort])
          other  #{k s (list 'genl sort inspace) (list 'genl kind intime)}
          longer #{k s (list 'genl kind mid) (list 'genl mid inspace) (list 'genl sort intime)}]
      (tu/with-neutral-kb [kb tu/fresh]
        (doseq [x (concat chain facts)] (v/assert kb x U {:strength :monotonic}))
        (let [early (support-of kb goal)]
          (v/assert kb direct U {:strength :monotonic})
          (let [late (support-of kb goal)]
            (is (some? (early longer)))
            (is (some? (early other)))
            (is (= (early other) (late other)))
            (is (some? (late #{k s direct (list 'genl sort intime)})))
            (is (nil? (late longer)))))))))

(defn- round-trip
  "The reasons `load!` leaves in a cleared KB, and those its own text export reloads."
  [load!]
  (let [dir (.toFile (Files/createTempDirectory "late-route" (make-array FileAttribute 0)))]
    (try
      [(tu/with-cleared-kb [kb tu/isolated-fresh]
         (load! kb)
         (v/export-text! kb (.getPath dir))
         (reasons kb))
       (tu/with-cleared-kb [kb tu/isolated-fresh]
         (v/load-text! kb (.getPath dir))
         (reasons kb))]
      (finally
        (run! #(io/delete-file % true) (reverse (file-seq dir)))))))

(deftest core-in-authored-and-content-order-holds-the-same-justifications
  ;; `load-core!` restores the upper layer as `core-context/load-into` asserts it, in
  ;; authored order; its own text export reloads the same sentences in content order.
  ;; The floor is one both argument-declaration readings clear: the upper layer holds 1,806
  ;; justifications with the entailment and 1,018 without it (VAELII_ASSERTIVE_ARG_TYPES=0).
  (let [[authored reloaded] (round-trip tu/load-core!)]
    (is (< 900 (reduce + (vals authored))))
    (is (= authored reloaded))))

(deftest ^:slow the-starter-in-authored-and-content-order-holds-the-same-justifications
  ;; the starter holds 1,954 justifications with the entailment and 1,101 without it
  (let [[authored reloaded] (round-trip tu/load-starter!)]
    (is (< 1000 (reduce + (vals authored))))
    (is (= authored reloaded))))

(deftest two-pairings-over-one-antecedent-set-are-two-justifications
  ;; `kind` and `sort` reach both literals through one `mid`, so the two firings that swap
  ;; the literals name the same four edges and the same two facts; the dedup key holds
  ;; them apart by their subsumptions, and the direct edge arriving last replaces only the
  ;; firing that pairs `(kind Xa)` with `inspace`
  (tu/with-terms [kind sort mid inspace intime noted Xa]
    (let [[_ facts goal] (pairing-steps kind sort inspace intime noted Xa)
          edges    [(list 'genl kind mid) (list 'genl sort mid)
                    (list 'genl mid inspace) (list 'genl mid intime)]
          direct   (list 'genl kind inspace)
          reading  (fn [steps]
                     (tu/with-neutral-kb [kb tu/fresh]
                       (doseq [x steps] (v/assert kb x U {:strength :monotonic}))
                       [(count (v/supporting-justifications kb (v/handle-of kb goal U)))
                        (reasons kb)]))
          readings (map #(reading (concat edges %)) (oi/permutations facts))]
      (is (every? #(= 4 (first %)) readings))
      (is (apply = readings))
      (is (= (reading (concat [direct] edges facts)) (reading (concat edges facts [direct])))))))
