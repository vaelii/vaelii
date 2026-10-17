;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.ref.believe-test
  "Unit tests of the belief reference (`vaelii.ref.believe`) on hand-built worlds, and of
  the world model (`vaelii.ref.world`) against a KB.

  Every expected answer is the one the docs give for the per-context reading, not the one
  the engine gives; the lattice of each world is written in a comment above it. The
  definitional families belong to `vaelii.ref.nogoods`; the tests here that need a
  disjointness clash pass `disjoint-double`, a test double that reads one declaration
  shape and is not the spec of the family. The tests that need the covering, functional
  or inherited family read `vaelii.ref.nogoods/families` and print a SKIP line when that
  namespace is absent. A test pinning a maintainer decision names it as
  docs/reference.md does, D1 to D17."
  (:require [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.ref.believe :as b]
            [vaelii.ref.world :as w]
            [vaelii.test-util :as tu]))

(defn- world
  "A world of `[sentence context strength]` triples; strength defaults to `:default`."
  [& triples]
  (w/from-writes (for [[s c st] triples] (w/write s c (or st :default)))))

(defn- disjoint-double
  "A test double for the disjoint family: two believed unary memberships of one
  individual whose types reach the two sides of a believed `(disjoint a b)` through the
  view's `:genl`. The declaration is the ground."
  [{:keys [believed genl]}]
  (let [members (filter #(and (seq? %) (= 2 (count %)) (not= 'not (first %))) believed)]
    (for [d believed
          :when (and (seq? d) (= 'disjoint (first d)))
          :let [[_ t1 t2] d]
          m1 members
          m2 members
          :when (and (not= m1 m2) (= (second m1) (second m2))
                     (contains? (genl (first m1)) t1) (contains? (genl (first m2)) t2))]
      {:kind :disjoint :members #{m1 m2} :ground #{d}})))

(defn- believed-at [result c] (get-in result [c :believed]))

(defn- unsupported?
  "Does `f` throw `ex-info` with `:type :unsupported`."
  [f]
  (try (f) false
       (catch clojure.lang.ExceptionInfo e (= :unsupported (:type (ex-data e))))))

;; ---- derivation -------------------------------------------------------------

(deftest a-forward-rule-derives-its-consequent-at-the-strongest-class-its-grounds-allow
  ;; CxA: (dog Fido) :monotonic, (dog Rex) :default, a bare forward rule dog ⇒ barks,
  ;;      and a default forward rule dog ⇒ loyal
  (let [v (b/view (world ['(dog Fido) 'CxA :monotonic]
                         ['(dog Rex) 'CxA]
                         ['(set/forwardRule (implies (dog ?x) (barks ?x))) 'CxA :monotonic]
                         ['(set/defaultRule (set/forwardRule (implies (dog ?x) (loyal ?x))))
                          'CxA :monotonic])
                  'CxA [])]
    (is (= '#{(dog Fido) (dog Rex) (barks Fido) (barks Rex) (loyal Fido) (loyal Rex)}
           (:believed v)))
    (is (= [:monotonic :default :default :default]
           (mapv (:class v) '[(barks Fido) (barks Rex) (loyal Fido) (loyal Rex)])))))

(deftest a-guarded-firing-confers-default-on-monotonic-grounds
  ;; D14. CxA: (pp Zed) :monotonic and one forward rule pp ⇒ rr, bare, guarded by
  ;; unknown(qq), or wrapped exceptWhen(qq). Nothing blocks the guard, and the rule is
  ;; not a set/defaultRule.
  (let [class-of (fn [rule]
                   ((:class (b/view (world ['(pp Zed) 'CxA :monotonic] [rule 'CxA :monotonic])
                                    'CxA []))
                    '(rr Zed)))]
    (is (= [:monotonic :default :default]
           (mapv class-of
                 '[(set/forwardRule (implies (pp ?x) (rr ?x)))
                   (set/forwardRule (implies (and (pp ?x) (unknown (qq ?x))) (rr ?x)))
                   (exceptWhen (qq ?x) (set/forwardRule (implies (pp ?x) (rr ?x))))])))))

(deftest a-rule-written-at-default-strength-does-not-cap-its-conclusions
  ;; CxA: (dog Fido) :monotonic, a bare forward rule written :default
  (let [v (b/view (world ['(dog Fido) 'CxA :monotonic]
                         ['(set/forwardRule (implies (dog ?x) (barks ?x))) 'CxA :default])
                  'CxA [])]
    (is (= :monotonic ((:class v) '(barks Fido))))))

(deftest a-rule-on-a-supertype-fires-on-a-subtype-fact-capped-by-the-edge-it-climbs
  ;; CxA: (dog Fido) :monotonic, (genl dog animal) :default,
  ;;      a forward rule animal ⇒ alive
  (let [v (b/view (world ['(dog Fido) 'CxA :monotonic]
                         ['(genl dog animal) 'CxA]
                         ['(set/forwardRule (implies (animal ?x) (alive ?x))) 'CxA :monotonic])
                  'CxA [])]
    (is (contains? (:believed v) '(alive Fido)))
    (is (= :default ((:class v) '(alive Fido))))
    (is (not (contains? (:believed v) '(animal Fido))) "a subsumed membership is not stored")))

(deftest a-denial-pattern-is-met-by-the-denial-of-a-supertype-and-not-of-a-subtype
  ;; CxA: (genl dog animal) (not (animal Tom)) (not (dog Rex)) all :monotonic,
  ;;      a forward rule ¬dog ⇒ notDog; a forward rule ¬animal ⇒ notAnimal
  (let [v (b/view (world ['(genl dog animal) 'CxA :monotonic]
                         ['(not (animal Tom)) 'CxA :monotonic]
                         ['(not (dog Rex)) 'CxA :monotonic]
                         ['(set/forwardRule (implies (not (dog ?x)) (not_dog ?x))) 'CxA]
                         ['(set/forwardRule (implies (not (animal ?x)) (not_animal ?x))) 'CxA])
                  'CxA [])]
    (is (= '#{(not_dog Tom) (not_dog Rex) (not_animal Tom)}
           (into #{} (filter #(#{'not_dog 'not_animal} (first %))) (:believed v))))))

(deftest a-join-binds-a-variable-across-two-antecedents
  ;; CxA: (parentOf Ann Bob) (parentOf Bob Cy), a forward grandparent rule
  (let [v (b/view (world ['(parentOf Ann Bob) 'CxA]
                         ['(parentOf Bob Cy) 'CxA]
                         ['(set/forwardRule (implies (and (parentOf ?x ?y) (parentOf ?y ?z))
                                                     (grandparentOf ?x ?z))) 'CxA])
                  'CxA [])]
    (is (= '#{(grandparentOf Ann Cy)}
           (into #{} (filter #(= 'grandparentOf (first %))) (:believed v))))))

(deftest a-covering-installs-an-edge-from-each-part-to-the-whole
  ;; CxA: (covering vehicle car boat) :monotonic, (car Herbie) :monotonic,
  ;;      a forward rule vehicle ⇒ registered
  (let [v (b/view (world ['(covering vehicle car boat) 'CxA :monotonic]
                         ['(car Herbie) 'CxA :monotonic]
                         ['(set/forwardRule (implies (vehicle ?x) (registered ?x))) 'CxA])
                  'CxA [])]
    (is (= [true :monotonic #{'car 'vehicle}]
           [(contains? (:believed v) '(registered Herbie))
            ((:class v) '(registered Herbie))
            ((:genl v) 'car)]))
    (is (not (contains? (:believed v) '(genl car vehicle))) "no genl sentence is stated")))

;; ---- visibility -------------------------------------------------------------

(deftest a-context-sees-what-its-genlCx-edges-reach-and-nothing-else
  ;; CxC sees CxA; CxB is a sibling CxC does not see
  (let [r (b/believe (world ['(dog Fido) 'CxA]
                            ['(cat Tom) 'CxB]
                            ['(genlCx CxC CxA) 'CxC :monotonic])
                     [])]
    (is (= '#{(dog Fido) (genlCx CxC CxA)} (believed-at r 'CxC)))
    (is (= #{'(cat Tom)} (believed-at r 'CxB)))
    (is (= #{'(dog Fido)} (believed-at r 'CxA)))
    (is (= #{'CxA 'CxB 'CxC} (set (keys r))))))

(deftest a-genlCx-edge-brings-a-rule-and-its-facts-into-view
  ;; without the edge CxC sees only itself; with (genlCx CxC CxA) it sees CxA's rule
  (let [base   [['(dog Fido) 'CxA :monotonic]
                ['(set/forwardRule (implies (dog ?x) (barks ?x))) 'CxC]
                ['(dog Rex) 'CxC :monotonic]]
        before (b/believe (apply world base) [])
        after  (b/believe (apply world (conj base ['(genlCx CxC CxA) 'CxUniverse :monotonic]))
                          [])]
    (is (= '#{(dog Rex) (barks Rex)} (believed-at before 'CxC)))
    (is (= '#{(dog Rex) (barks Rex) (dog Fido) (barks Fido)}
           (disj (believed-at after 'CxC) '(genlCx CxC CxA))))))

(deftest a-genlCx-edge-is-monotonic-and-its-denial-inert
  ;; D1: a :default genlCx write is stored :monotonic, and a denial of one is set aside
  ;; as inert
  (is (= [[:monotonic] [[] 1] false]
         [(mapv :strength (:writes (w/check-world (world ['(genlCx CxC CxA) 'CxUniverse
                                                          :default]))))
          (let [c (w/check-world (world ['(not (genlCx CxC CxA)) 'CxUniverse :monotonic]))]
            [(:writes c) (count (:inert c))])
          (unsupported? #(w/check-world (world ['(genlCx CxC CxA) 'CxUniverse
                                                :monotonic])))])))

(deftest a-derivation-over-two-genl-routes-takes-the-widest-bottleneck
  ;; D9. CxA: (genl dog animal) :default; (genl dog mammal) (genl mammal animal)
  ;; (dog Fido) :monotonic; a forward rule animal ⇒ alive. The one-edge route is
  ;; :default and the two-edge route :monotonic.
  (let [v (b/view (world ['(genl dog animal) 'CxA :default]
                         ['(genl dog mammal) 'CxA :monotonic]
                         ['(genl mammal animal) 'CxA :monotonic]
                         ['(dog Fido) 'CxA :monotonic]
                         ['(set/forwardRule (implies (animal ?x) (alive ?x))) 'CxA])
                  'CxA [])]
    (is (= :monotonic ((:class v) '(alive Fido))))))

;; ---- negation and decision --------------------------------------------------

(deftest a-default-and-a-monotonic-denial-are-decided-only-where-one-context-sees-both
  ;; CxC sees CxA and CxB; CxA: (flies Tweety) :default; CxB: (not (flies Tweety)) :monotonic
  (let [r (b/believe (world ['(flies Tweety) 'CxA]
                            ['(not (flies Tweety)) 'CxB :monotonic]
                            ['(genlCx CxC CxA) 'CxUniverse :monotonic]
                            ['(genlCx CxC CxB) 'CxUniverse :monotonic])
                     [])]
    (is (= [false true #{'(flies Tweety)}]
           [(contains? (believed-at r 'CxC) '(flies Tweety))
            (contains? (believed-at r 'CxC) '(not (flies Tweety)))
            (get-in r ['CxC :out])]))
    (is (= [true #{} []]
           [(contains? (believed-at r 'CxA) '(flies Tweety))
            (get-in r ['CxA :out]) (get-in r ['CxA :nogoods])]))
    (is (= [:defeat '(flies Tweety)]
           ((juxt :verdict :loser) (first (get-in r ['CxC :nogoods])))))))

(deftest two-default-denials-are-a-dilemma-and-two-monotonic-ones-a-hard-clash
  ;; CxA: (pacifist Nixon) and its denial, both :default
  ;; CxB: (quaker Nixon) and its denial, both :monotonic
  (let [r (b/believe (world ['(pacifist Nixon) 'CxA]
                            ['(not (pacifist Nixon)) 'CxA]
                            ['(quaker Nixon) 'CxB :monotonic]
                            ['(not (quaker Nixon)) 'CxB :monotonic])
                     [])]
    (is (= [2 :dilemma #{}]
           [(count (believed-at r 'CxA))
            (:verdict (first (get-in r ['CxA :nogoods]))) (get-in r ['CxA :out])]))
    (is (= [2 :hard #{}]
           [(count (believed-at r 'CxB))
            (:verdict (first (get-in r ['CxB :nogoods]))) (get-in r ['CxB :out])]))))

(deftest a-declaration-written-default-keeps-its-strength-and-two-monotonic-memberships-clash-hard
  ;; D11. CxA: (disjoint dog cat) written :default; (dog Rex) (cat Rex) :monotonic.
  ;; The declaration is a ground, not a member, so it is not weighed.
  (let [v (b/view (world ['(disjoint dog cat) 'CxA :default]
                         ['(dog Rex) 'CxA :monotonic]
                         ['(cat Rex) 'CxA :monotonic])
                  'CxA [disjoint-double])]
    (is (= [:hard #{} :default]
           [(:verdict (first (:nogoods v))) (:out v) ((:class v) '(disjoint dog cat))]))))

(deftest a-sentence-taken-out-takes-its-consequences-with-it
  ;; CxA: (flies Tweety) :default, (not (flies Tweety)) :monotonic,
  ;;      a forward rule flies ⇒ airborne
  (let [v (b/view (world ['(flies Tweety) 'CxA]
                         ['(not (flies Tweety)) 'CxA :monotonic]
                         ['(set/forwardRule (implies (flies ?x) (airborne ?x))) 'CxA])
                  'CxA [])]
    (is (= '#{(not (flies Tweety))} (:believed v)))))

;; ---- unknown and exceptWhen -------------------------------------------------

(deftest an-unknown-rule-is-blocked-once-its-exception-arrives
  ;; CxA: (bird Opus), a forward rule bird ∧ unknown(flies) ⇒ walks; then (flies Opus)
  (let [rule   ['(set/forwardRule (implies (and (bird ?x) (unknown (flies ?x))) (walks ?x)))
                'CxA]
        before (b/view (world ['(bird Opus) 'CxA] rule) 'CxA [])
        after  (b/view (world ['(bird Opus) 'CxA] rule ['(flies Opus) 'CxA]) 'CxA [])]
    (is (= [true false]
           [(contains? (:believed before) '(walks Opus))
            (contains? (:believed after) '(walks Opus))]))))

(deftest an-exceptWhen-blocks-the-binding-its-query-holds-of
  ;; CxA: (bird Opus) (bird Tweety) (penguin Opus), a forward rule bird ⇒ flies
  ;;      excepted when penguin
  (let [v (b/view (world ['(bird Opus) 'CxA]
                         ['(bird Tweety) 'CxA]
                         ['(penguin Opus) 'CxA]
                         ['(exceptWhen (penguin ?b)
                                       (set/forwardRule (implies (bird ?b) (flies ?b)))) 'CxA])
                  'CxA [])]
    (is (= '#{(flies Tweety)} (into #{} (filter #(= 'flies (first %))) (:believed v))))))

(deftest an-unknown-reads-its-condition-through-the-subtypes
  ;; CxA: (genl penguin flightless), (bird Opus) (penguin Opus),
  ;;      a forward rule bird ∧ unknown(flightless) ⇒ flies
  (let [v (b/view (world ['(genl penguin flightless) 'CxA :monotonic]
                         ['(bird Opus) 'CxA]
                         ['(penguin Opus) 'CxA]
                         ['(set/forwardRule (implies (and (bird ?x) (unknown (flightless ?x)))
                                                     (flies ?x))) 'CxA])
                  'CxA [])]
    (is (not (contains? (:believed v) '(flies Opus))))))

(deftest an-unknown-is-asked-at-every-reader-below-the-placement
  ;; D4: CxB sees CxA. CxA: the rule and (pp Zed); CxB: (qq Zed).
  ;; CxA fires; CxB reads (qq Zed) and does not believe (rr Zed).
  (let [r (b/believe (world ['(set/forwardRule (implies (and (pp ?x) (unknown (qq ?x))) (rr ?x)))
                             'CxA]
                            ['(pp Zed) 'CxA]
                            ['(qq Zed) 'CxB]
                            ['(genlCx CxB CxA) 'CxUniverse :monotonic])
                     [])]
    (is (= [true false]
           [(contains? (believed-at r 'CxA) '(rr Zed))
            (contains? (believed-at r 'CxB) '(rr Zed))]))))

;; ---- the review scenarios (2026-09-28) --------------------------------------

(deftest scenario-a-a-defeat-releases-an-unknown-rule-in-a-later-round
  ;; CxA: (disjoint happy sad) (pp Zed) (sad Zed) :monotonic, (happy Zed) :default,
  ;;      a forward rule pp ∧ unknown(happy) ⇒ rr
  (let [v (b/view (world ['(disjoint happy sad) 'CxA :monotonic]
                         ['(set/forwardRule (implies (and (pp ?x) (unknown (happy ?x))) (rr ?x)))
                          'CxA :monotonic]
                         ['(pp Zed) 'CxA :monotonic]
                         ['(happy Zed) 'CxA :default]
                         ['(sad Zed) 'CxA :monotonic])
                  'CxA [disjoint-double])]
    (is (= [true false #{'(happy Zed)}]
           [(contains? (:believed v) '(rr Zed)) (contains? (:believed v) '(happy Zed))
            (:out v)]))))

(deftest a-roster-declaration-forces-its-predicate-only-where-it-is-seen
  ;; CxA sees CxU and states (forced_monotonic_predicate ta); CxU holds a dilemma and a
  ;; denial beside a default membership
  (let [r (b/believe (world ['(genlCx CxA CxU) 'CxUniverse :monotonic]
                            ['(forced_monotonic_predicate ta) 'CxA]
                            ['(disjoint ta tb) 'CxU :monotonic]
                            ['(ta Ind) 'CxU] ['(tb Ind) 'CxU]
                            ['(not (ta Jay)) 'CxU :monotonic] ['(ta Jay) 'CxU])
                     [disjoint-double])
        at (fn [c] (mapv #(contains? (believed-at r c) %)
                         '[(ta Ind) (tb Ind) (ta Jay) (not (ta Jay))]))]
    (is (= [true false true false] (at 'CxA)) "CxA: the rival loses and the denial is inert")
    (is (= [true true false true] (at 'CxU)) "CxU: a dilemma, and the denial defeats (ta Jay)")))

(deftest scenario-b-a-released-edge-leaves-no-clash-at-the-context-that-reads-the-release
  ;; CxB sees CxA and CxD. CxA: (genl chi dog) :default; CxD: (not (genl chi dog))
  ;; :monotonic; CxB: (chi Kit) :default, (cat Kit) :monotonic, (disjoint dog cat)
  (let [r (b/believe (world ['(genl chi dog) 'CxA :default]
                            ['(not (genl chi dog)) 'CxD :monotonic]
                            ['(chi Kit) 'CxB :default]
                            ['(cat Kit) 'CxB :monotonic]
                            ['(disjoint dog cat) 'CxB :monotonic]
                            ['(genlCx CxB CxA) 'CxUniverse :monotonic]
                            ['(genlCx CxB CxD) 'CxUniverse :monotonic])
                     [disjoint-double])]
    (is (= [true true false #{'(genl chi dog)}]
           [(contains? (believed-at r 'CxB) '(chi Kit))
            (contains? (believed-at r 'CxB) '(cat Kit))
            (contains? (believed-at r 'CxB) '(genl chi dog))
            (get-in r ['CxB :out])]))
    (is (contains? (believed-at r 'CxA) '(genl chi dog)))))

(deftest scenario-b-in-one-context-the-edge-is-decided-before-the-clash-read-through-it
  ;; CxA holds all five: (genl chi dog) :default, (not (genl chi dog)) :monotonic,
  ;; (chi Kit) :default, (cat Kit) :monotonic, (disjoint dog cat)
  (let [v (b/view (world ['(genl chi dog) 'CxA :default]
                         ['(not (genl chi dog)) 'CxA :monotonic]
                         ['(chi Kit) 'CxA :default]
                         ['(cat Kit) 'CxA :monotonic]
                         ['(disjoint dog cat) 'CxA :monotonic])
                  'CxA [disjoint-double])]
    (is (= [true #{'(genl chi dog)}]
           [(contains? (:believed v) '(chi Kit)) (:out v)]))))

(deftest a-verdict-does-not-bind-a-context-below-that-reads-the-clash-released
  ;; D3: CxC sees CxB. CxB: (genl chi dog) :default, (disjoint dog cat),
  ;; (chi Kit) :default, (cat Kit) :monotonic; CxC: (not (genl chi dog)) :monotonic.
  ;; CxB takes (chi Kit) OUT; CxC takes the edge OUT, reads no clash, believes it.
  (let [r (b/believe (world ['(genl chi dog) 'CxB :default]
                            ['(disjoint dog cat) 'CxB :monotonic]
                            ['(chi Kit) 'CxB :default]
                            ['(cat Kit) 'CxB :monotonic]
                            ['(not (genl chi dog)) 'CxC :monotonic]
                            ['(genlCx CxC CxB) 'CxUniverse :monotonic])
                     [disjoint-double])]
    (is (= [false true]
           [(contains? (believed-at r 'CxB) '(chi Kit))
            (contains? (believed-at r 'CxC) '(chi Kit))]))))

(deftest scenario-c-a-context-seeing-the-separation-decides-where-the-joint-view-does-not
  ;; CxW sees CxA and CxB; CxH sees CxDecl; CxZ sees CxW and CxH.
  ;; CxA: (a_t Pip) :monotonic; CxB: (b_t Pip) :default; CxDecl: (disjoint a_t b_t)
  (let [r (b/believe (world ['(a_t Pip) 'CxA :monotonic]
                            ['(b_t Pip) 'CxB :default]
                            ['(disjoint a_t b_t) 'CxDecl :monotonic]
                            ['(genlCx CxW CxA) 'CxUniverse :monotonic]
                            ['(genlCx CxW CxB) 'CxUniverse :monotonic]
                            ['(genlCx CxH CxDecl) 'CxUniverse :monotonic]
                            ['(genlCx CxZ CxW) 'CxUniverse :monotonic]
                            ['(genlCx CxZ CxH) 'CxUniverse :monotonic])
                     [disjoint-double])]
    (is (= [true false #{'(b_t Pip)}]
           [(contains? (believed-at r 'CxZ) '(a_t Pip))
            (contains? (believed-at r 'CxZ) '(b_t Pip))
            (get-in r ['CxZ :out])]))
    (is (= [true true]
           [(contains? (believed-at r 'CxW) '(a_t Pip))
            (contains? (believed-at r 'CxW) '(b_t Pip))]))))

(def ^:private reference-families
  "`vaelii.ref.nogoods/families` when that namespace loads, nil otherwise."
  (delay (try @(requiring-resolve 'vaelii.ref.nogoods/families)
              (catch Exception _ nil))))

(deftest scenario-d-a-cover-refuted-through-a-supertype-denial-takes-the-whole-out
  ;; CxA: (genl p1 w) (genl p2 w) (genl p1 q) (covering w p1 p2) :monotonic,
  ;;      (w X) :default, (not (q X)) (not (p2 X)) :monotonic
  (tu/with-requirement @reference-families "vaelii.ref.nogoods/families is not loadable"
    (let [v (b/view (world ['(genl p1 w) 'CxA :monotonic]
                           ['(genl p2 w) 'CxA :monotonic]
                           ['(genl p1 q) 'CxA :monotonic]
                           ['(covering w p1 p2) 'CxA :monotonic]
                           ['(w X) 'CxA :default]
                           ['(not (q X)) 'CxA :monotonic]
                           ['(not (p2 X)) 'CxA :monotonic])
                    'CxA @reference-families)]
      (is (not (contains? (:believed v) '(w X)))))))

(deftest scenario-e-an-own-denial-under-a-vantage-claim-is-out-with-and-without-a-second-path
  ;; CxLeft sees CxU. CxU :monotonic: (transitiveInArgInverse pP 1 genl) (genl hauler animal)
  ;; (genl vehicle animal); CxU :default: (genl cart hauler) (not (pP cart Bone1));
  ;; CxLeft :monotonic: (genl cart vehicle) (pP vehicle Bone1). The second world adds
  ;; (pP hauler Bone1) :monotonic in CxU.
  (tu/with-requirement @reference-families "vaelii.ref.nogoods/families is not loadable"
    (let [base  [['(transitiveInArgInverse pP 1 genl) 'CxU :monotonic]
                 ['(genl hauler animal) 'CxU :monotonic]
                 ['(genl vehicle animal) 'CxU :monotonic]
                 ['(genl cart hauler) 'CxU :default]
                 ['(not (pP cart Bone1)) 'CxU :default]
                 ['(genl cart vehicle) 'CxLeft :monotonic]
                 ['(pP vehicle Bone1) 'CxLeft :monotonic]
                 ['(genlCx CxLeft CxU) 'CxUniverse :monotonic]]
          at    (fn [triples]
                  (contains? (:believed (b/view (apply world triples) 'CxLeft
                                                @reference-families))
                             '(not (pP cart Bone1))))]
      (is (= [false false]
             [(at base) (at (conj base ['(pP hauler Bone1) 'CxU :monotonic]))])))))

;; ---- the rounds (D2) -------------------------------------------------------

(deftest a-guarded-conclusion-a-defeat-releases-ties-with-a-default-edge-instead-of-defeating-it
  ;; D2 and D14. CxA: (genl chi dog) (chi Kit) :default; (disjoint dog cat) (cat Kit)
  ;; (pp Kit) (transitiveInArgInverse pP 1 genl) (pP dog Bone) :monotonic; a forward rule
  ;; pp ∧ unknown(chi) ⇒ ¬(pP chi Bone). Round 1 takes (chi Kit) OUT and the rule fires.
  ;; The conclusion is :default (D14), so round 2's inherited nogood ties it with the
  ;; :default edge. Before D14 the conclusion was :monotonic, round 2 took the edge OUT,
  ;; and a from-scratch re-decision alternated between the two states.
  (tu/with-requirement @reference-families "vaelii.ref.nogoods/families is not loadable"
    (let [v (b/view (world ['(genl chi dog) 'CxA :default]
                           ['(chi Kit) 'CxA :default]
                           ['(disjoint dog cat) 'CxA :monotonic]
                           ['(cat Kit) 'CxA :monotonic]
                           ['(pp Kit) 'CxA :monotonic]
                           ['(transitiveInArgInverse pP 1 genl) 'CxA :monotonic]
                           ['(pP dog Bone) 'CxA :monotonic]
                           ['(set/forwardRule (implies (and (pp ?x) (unknown (chi ?x)))
                                                       (not (pP chi Bone)))) 'CxA])
                    'CxA @reference-families)]
      (is (= ['#{(chi Kit)} true false #{:dilemma}]
             [(:out v) (contains? (:believed v) '(not (pP chi Bone)))
              (contains? (:believed v) '(pP chi Bone))
              (into #{} (comp (filter #(= :inherited (:kind %))) (map :verdict)) (:nogoods v))])))))

;; ---- the forced-monotonic roster (D7) ---------------------------------------

(deftest a-roster-member-keeps-its-strength-and-its-denial-is-inert
  ;; D7, D10, D11: each mark, declaration and predicate genl edge written :default keeps
  ;; its strength, and a denial of one is set aside as inert; a genl edge between types
  ;; may be :default and may be denied
  (let [roster  '[(irreflexive likes) (anti_symmetric likes) (asymmetric likes)
                  (functional likes) (functionalInArg likes 2) (anti_transitive likes)
                  (disjoint dog cat)
                  (covering vehicle car boat) (genl tangiblePartOf nearTo)]
        n       (count roster)
        refused (fn [triple] (unsupported? #(w/check-world (world triple))))
        stored  (fn [triple] (mapv :strength (:writes (w/check-world (world triple)))))
        inert   (fn [triple] (count (:inert (w/check-world (world triple)))))]
    (is (= [(vec (repeat n [:default])) (vec (repeat n 1)) (vec (repeat n false))]
           [(mapv #(stored [% 'CxA :default]) roster)
            (mapv #(inert [(list 'not %) 'CxA :monotonic]) roster)
            (mapv #(refused [% 'CxA :monotonic]) roster)]))
    (is (= [[:default] [:default] 0]
           [(stored ['(genl dog animal) 'CxA :default])
            (stored ['(not (genl dog animal)) 'CxA :default])
            (inert ['(not (genl dog animal)) 'CxA :default])]))
    (is (refused ['(transitiveInArgInverse likes 1 tangiblePartOf) 'CxA :monotonic])
        "a transitiveInArgInverse over a relation other than genl")))

(deftest a-mark-reaches-a-sub-predicate-over-a-predicate-edge-written-default
  ;; D7, D10. CxA: (functional ageOf) (ageAtDeath Bob 5) :monotonic; (genl ageAtDeath
  ;; ageOf) and (ageOf Bob 6) written :default. The edge keeps its strength and carries
  ;; the mark, so (ageOf Bob 6) is the unique weakest member. A denial of the edge is
  ;; inert and leaves the verdict as it is.
  (tu/with-requirement @reference-families "vaelii.ref.nogoods/families is not loadable"
    (let [base  [['(functional ageOf) 'CxA :monotonic]
                 ['(ageAtDeath Bob 5) 'CxA :monotonic]
                 ['(genl ageAtDeath ageOf) 'CxA :default]
                 ['(ageOf Bob 6) 'CxA :default]]
          reach (b/view (apply world base) 'CxA @reference-families)]
      (is (= [:monotonic :default #{'(ageOf Bob 6)} true]
             [((:class reach) '(functional ageOf)) ((:class reach) '(genl ageAtDeath ageOf))
              (:out reach) (contains? (:believed reach) '(ageAtDeath Bob 5))]))
      (is (= [(:out reach) (:believed reach)]
             ((juxt :out :believed)
              (b/view (apply world (conj base ['(not (genl ageAtDeath ageOf)) 'CxA :monotonic]))
                      'CxA @reference-families)))))))

;; ---- inherited claims (D5) --------------------------------------------------

(def ^:private carrier
  "A load claim on `hauler` and the declaration that carries position 1 down `genl`."
  [['(transitiveInArgInverse carriesLoad 1 genl) 'CxA :monotonic]
   ['(carriesLoad hauler Bone1) 'CxA :monotonic]])

(defn- claim-at
  "`[believed? class inherited?]` of `(carriesLoad cart Bone1)` at CxA of the world of
  `triples`, with `families` decided."
  [triples families]
  (let [wd (apply world triples)
        v  (b/view wd 'CxA families)
        s  '(carriesLoad cart Bone1)]
    [(b/believed? wd s 'CxA families) ((:class v) s) (contains? (:inherited v) s)]))

(deftest a-claim-is-inherited-down-a-believed-genl-edge-at-the-edge-s-class
  ;; D5. CxA: (transitiveInArgInverse carriesLoad 1 genl) (carriesLoad hauler Bone1)
  ;; :monotonic, and (genl cart hauler) :monotonic, then :default
  (is (= [[true :monotonic true] [true :default true]]
         [(claim-at (conj carrier ['(genl cart hauler) 'CxA :monotonic]) [])
          (claim-at (conj carrier ['(genl cart hauler) 'CxA :default]) [])])))

(deftest an-inherited-claim-over-two-routes-takes-the-widest-bottleneck
  ;; D9. CxA: the carrier, (genl cart hauler) :default; (genl cart wagon)
  ;; (genl wagon hauler) :monotonic
  (is (= [true :monotonic true]
         (claim-at (into carrier [['(genl cart hauler) 'CxA :default]
                                  ['(genl cart wagon) 'CxA :monotonic]
                                  ['(genl wagon hauler) 'CxA :monotonic]])
                   []))))

(deftest a-denial-at-least-as-strong-as-the-reading-blocks-the-inherited-claim
  ;; D5. CxA: the carrier; a :monotonic edge under a :monotonic denial, and a :default
  ;; edge under a :default denial. The denial stays believed; the claim does not.
  (let [strict  (conj carrier ['(genl cart hauler) 'CxA :monotonic]
                      ['(not (carriesLoad cart Bone1)) 'CxA :monotonic])
        typical (conj carrier ['(genl cart hauler) 'CxA :default]
                      ['(not (carriesLoad cart Bone1)) 'CxA :default])
        denial  (fn [triples] (contains? (:believed (b/view (apply world triples) 'CxA []))
                                         '(not (carriesLoad cart Bone1))))]
    (is (= [[false nil false] [false nil false] true true]
           [(claim-at strict []) (claim-at typical []) (denial strict) (denial typical)]))
    (is (contains? (b/believed-candidates (apply world strict) 'CxA [])
                   '(carriesLoad cart Bone1))
        "a blocked reach is a candidate the engine must answer false")))

(deftest a-weaker-denial-loses-to-a-monotonic-reading-through-the-inherited-family
  ;; D5. CxA: the carrier, (genl cart hauler) :monotonic, (not (carriesLoad cart Bone1))
  ;; :default
  (tu/with-requirement @reference-families "vaelii.ref.nogoods/families is not loadable"
    (let [triples (conj carrier ['(genl cart hauler) 'CxA :monotonic]
                        ['(not (carriesLoad cart Bone1)) 'CxA :default])]
      (is (= [[true :monotonic true] '#{(not (carriesLoad cart Bone1))}]
             [(claim-at triples @reference-families)
              (:out (b/view (apply world triples) 'CxA @reference-families))])))))

(deftest a-stored-claim-is-not-marked-inherited
  ;; CxA: the carrier, (genl cart hauler) :monotonic, and (carriesLoad cart Bone1)
  ;; :default stored. The stored sentence takes the stronger class and is not in
  ;; :inherited; the per-context map of believe carries the key.
  (let [wd (apply world (conj carrier ['(genl cart hauler) 'CxA :monotonic]
                              ['(carriesLoad cart Bone1) 'CxA :default]))
        r  (b/believe wd [])]
    (is (= [#{} true :monotonic]
           [(get-in r ['CxA :inherited])
            (contains? (get-in r ['CxA :believed]) '(carriesLoad cart Bone1))
            ((:class (b/view wd 'CxA [])) '(carriesLoad cart Bone1))]))))

;; ---- the merge verdict (D6) -------------------------------------------------

(deftest an-all-monotonic-symbol-collision-merges-and-every-other-is-weighed
  ;; D6: decide on hand-built nogoods, with the classes given as a map
  (let [mono    (constantly :monotonic)
        verdict (fn [class kind members]
                  (:verdict (b/decide class {:kind kind :members members :ground #{}})))]
    (is (= [:merge :merge :merge :hard :hard :defeat :hard]
           [(verdict mono :functional '#{(fatherOf Ann Bob) (fatherOf Ann Cy)})
            (verdict mono :functional-in-arg '#{(bornIn Ann Oslo) (bornIn Ann Rome)})
            (verdict mono :anti-symmetric '#{(tangiblePartOf Hub Rim) (tangiblePartOf Rim Hub)})
            (verdict mono :functional '#{(ageOf Bob 5) (ageOf Bob 6)})
            (verdict mono :disjoint '#{(dog Rex) (cat Rex)})
            (verdict {'(fatherOf Ann Bob) :monotonic '(fatherOf Ann Cy) :default}
                     :functional '#{(fatherOf Ann Bob) (fatherOf Ann Cy)})
            (verdict mono :negation '#{(flies Tweety) (not (flies Tweety))})]))))

;; ---- determinism and order --------------------------------------------------

(defn- permutations [xs]
  (if (empty? xs)
    [[]]
    (for [x xs, more (permutations (remove #{x} xs))] (cons x more))))

(deftest the-reference-reads-no-write-order
  ;; scenario (b)'s seven writes, in every seventh of their 5040 orders
  (let [writes  (:writes (world ['(genl chi dog) 'CxA :default]
                                ['(not (genl chi dog)) 'CxD :monotonic]
                                ['(chi Kit) 'CxB :default]
                                ['(cat Kit) 'CxB :monotonic]
                                ['(disjoint dog cat) 'CxB :monotonic]
                                ['(genlCx CxB CxA) 'CxUniverse :monotonic]
                                ['(genlCx CxB CxD) 'CxUniverse :monotonic]))
        results (into #{} (map #(b/believe (w/from-writes %) [disjoint-double]))
                      (take-nth 7 (permutations writes)))]
    (is (= 1 (count results)))))

;; ---- the fragment -------------------------------------------------------------

(deftest parse-rule-reads-the-wrappers-the-joins-the-unknowns-and-the-exception
  (is (= {:rule        '(implies (and (bird ?b) (unknown (and (sick ?b) (old ?b)))) (flies ?b))
          :direction   :forward
          :defeasible? true
          :antecedents '[(bird ?b)]
          :unknowns    '[[(sick ?b) (old ?b)]]
          :consequent  '(flies ?b)
          :exceptions  '[[(penguin ?b)]]
          :inert?      false}
         (w/parse-rule '(exceptWhen (penguin ?b)
                                    (set/defaultRule
                                     (set/forwardRule
                                      (implies (and (bird ?b) (unknown (and (sick ?b) (old ?b))))
                                               (flies ?b)))))))))

(deftest a-rule-concluding-a-roster-predicate-is-inert
  ;; D17: a declaration, a mark and a predicate genl edge as a consequent parse as
  ;; inert, and the world check sets such a rule aside rather than refusing it
  (let [forms '[(set/forwardRule (implies (dog ?x) (disjoint ?x cat)))
                (set/forwardRule (implies (dog ?x) (not (disjoint ?x cat))))
                (set/forwardRule (implies (likes ?x ?y) (functional likes)))
                (set/forwardRule (implies (dog ?x) (genl tangiblePartOf nearTo)))]]
    (is (= [true true true true] (mapv #(:inert? (w/parse-rule %)) forms)))
    (is (= [[] 4] (let [c (w/check-world (apply world (map #(vector % 'CxA) forms)))]
                    [(:writes c) (count (:inert c))])))
    (is (not (:inert? (w/parse-rule '(set/forwardRule (implies (dog ?x) (barks ?x)))))))))

(deftest the-world-check-refuses-every-shape-outside-v1
  (let [refused
        {:backward-only   '(implies (dog ?x) (barks ?x))
         :inert           '(set/inertRule (implies (dog ?x) (barks ?x)))
         :genl-antecedent '(set/forwardRule (implies (genl ?a animal) (kind ?a)))
         :genl-conclusion '(set/forwardRule (implies (dog ?x) (genl ?x animal)))
         :open-conclusion '(set/forwardRule (implies (dog ?x) (likes ?x ?y)))
         :negated-unknown '(set/forwardRule (implies (and (dog ?x) (unknown (not (cat ?x))))
                                                     (barks ?x)))
         :symmetric       '(symmetric marriedTo)
         :partition       '(partition animal dog cat)
         :except          '(except Foo)
         :equality        '(sameAs Fido Rex)
         :open-fact       '(dog ?x)
         :nat-argument    '(likes Tom (fatherFn Tom))}
        results (into {} (for [[k s] refused]
                           [k (unsupported? #(w/check-world (world [s 'CxA])))]))]
    (is (= (zipmap (keys refused) (repeat true)) results))
    (is (unsupported? #(w/check-world (world ['(genlCx CxA CxB) 'CxUniverse]
                                             ['(genlCx CxB CxA) 'CxUniverse])))
        "a genlCx cycle")
    (is (unsupported? #(w/check-world
                        (world ['(transitiveInArgInverse pP 1 genl) 'CxA :monotonic]
                               ['(set/forwardRule (implies (pP ?x Bone) (qq ?x))) 'CxA])))
        "a rule reading a preserved predicate")
    (is (unsupported? #(w/check-world
                        (world ['(transitiveInArgInverse pP 1 genl) 'CxA :monotonic]
                               ['(genl pP qQ) 'CxA :monotonic]
                               ['(set/forwardRule (implies (qQ ?x Bone) (qq ?x))) 'CxA])))
        "a rule reading a predicate above a preserved one")
    (is (unsupported? #(b/believe
                        (world ['(set/forwardRule (implies (and (pp ?x) (unknown (qq ?x)))
                                                           (rr ?x))) 'CxA]
                               ['(set/forwardRule (implies (and (pp ?x) (unknown (rr ?x)))
                                                           (qq ?x))) 'CxA])
                        []))
        "a cycle through negation")))

;; ---- extraction from a KB ---------------------------------------------------

(deftest world-of-reads-the-premises-and-no-derivation
  (tu/with-neutral-kb [kb #(tu/fresh)]
    (tu/with-terms [dog barks sick Fido CxA CxB]
      (let [rule (list 'set/forwardRule (list 'implies (list dog '?x) (list barks '?x)))]
        (v/assert kb (list 'genlCx CxB CxA) CxB {:strength :monotonic})
        (v/assert kb (list dog Fido) CxA {:strength :monotonic})
        (v/assert kb (list 'exceptWhen (list sick '?x) rule) CxA)
        (let [wd     (w/world-of kb)
              by-s   (group-by :sentence (:writes wd))
              kinds  (frequencies (map (comp w/write-kind :sentence) (:writes wd)))
              exc    (first (filter #(= 'exceptWhen (first (:sentence %))) (:writes wd)))]
          (is (= {:fact 1 :genlCx 1 :rule 2} kinds))
          (is (= [{:sentence (list dog Fido) :context CxA :strength :monotonic}]
                 (get by-s (list dog Fido))))
          (is (= [CxB] (map :context (get by-s (list 'genlCx CxB CxA)))))
          (is (nil? (get by-s (list barks Fido))) "a derived sentex is not a write")
          (is (= [CxA [[(list sick '?var0)]]]
                 [(:context exc) (:exceptions (w/parse-rule (:sentence exc)))]))
          (is (= #{CxA CxB} (set (:contexts wd)))))))))

(deftest world-of-refuses-a-kb-holding-content-outside-v1
  (tu/with-neutral-kb [kb #(tu/fresh)]
    (tu/with-terms [marriedTo CxA]
      (v/assert kb (list 'symmetric marriedTo) CxA)
      (is (unsupported? #(w/world-of kb))))))
