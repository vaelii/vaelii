;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.starter-test
  "The starter schema loads and, with the test-world's cast beneath it, its rules and
  taxonomy behave."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.host.seed :as seed]
            [vaelii.host.starter :as starter]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.special :as special]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(def ^:private starter-violations
  "The violations ledger as the starter load leaves it, read by the `:once` fixture
  before the test-world loads beneath it."
  (atom ::unread))

(use-fixtures :once (tu/loaded (fn [kb]
                                 (starter/load-into kb)
                                 (reset! starter-violations (v/violations kb))
                                 (world/load-into kb))))
(use-fixtures :each (tu/neutral))

(deftest the-starter-loads-with-no-violation
  ;; The browser opens on the starter, so `/stats` shows this ledger to every first-time
  ;; reader.  A cut notice here says a sweep of the shipped ontology left clashes
  ;; unreported or content undecided.  The starter load closes on one deferred settle
  ;; whose region names every stored sentex, one of them a denial, and both retroactive
  ;; sweeps skip such a region
  ;; (`exposure_test/a-settle-over-the-whole-store-sweeps-nothing-and-files-no-cut`).
  ;; Swept, they reach 66,054 and 57,767 instances against the 8,192 budget.  Any other
  ;; entry is a defect the shipped files carry.
  (is (not= ::unread @starter-violations) "the fixture read the ledger")
  (is (empty? @starter-violations)
      (str "the starter load files violations: " (pr-str @starter-violations))))

(tu/deftest-kb the-loaded-starter-holds-every-argument-type-derivation
  ;; `record-arg-types` records the derivations a store loaded around `assert` lacks.  The
  ;; starter and the test-world load through `assert`, so it records nothing over them: the
  ;; loaders draw every derivation, a decontextualized lift's copy included.
  (is (= 0 (:recorded (v/record-arg-types kb)))))

(tu/deftest-kb ^:slow the-constraint-only-reading-proves-every-sentence-the-entailment-derives
  ;; Each record the argument entailment alone holds up in the fixture is asked in its
  ;; context of the same starter and test-world loaded under the constraint-only reading,
  ;; which derives nothing.  Under that reading the fixture holds no such record.
  (let [mint-only? #'special/mint-only?
        derived    (sort-by pr-str
                            (for [h     (p/sentex-ids (:records kb))
                                  :when (mint-only? kb h)
                                  :let  [{:keys [sentence context]} (p/get-sentex (:records kb) h)]]
                              [context sentence]))
        off        (doto (v/open-kb (tu/isolated-space)) (tu/clear-kb!))]
    (try
      (binding [checks/*assertive-arg-types?* false]
        (-> off starter/load-into world/load-into)
        (is (empty? (remove (fn [[c s]] (v/ask? off s c)) derived))))
      (finally (tu/clear-kb! off)))))

(defn- authored-sentences
  "Every sentence the shipped ontology's own source files contain, paired with the context
  whose file holds it — `CxCore.txt` plus every discovered file under `kb/upper/` and
  `kb/middle/`.  Read from the classpath the way the starter reads them, so a file added
  to a layer is swept with no edit here."
  []
  (concat (for [s (seed/read-sentences 'CxCore nil)] ['CxCore s])
          (for [dir ["upper" "middle"]
                c   (seed/layer-contexts dir)
                s   (seed/read-sentences c dir)]
            [c s])))

(tu/deftest-kb every-sentence-the-starter-ships-is-well-formed-once-it-is-all-loaded
  ;; **Loading is not checking**, and the gap between the two is where the shipped
  ;; ontology can go wrong quietly.  `seed/load-sentences` asserts in file order and
  ;; retries, so a sentence is judged against whatever had arrived when its turn came —
  ;; and the argument checks are open-world, abstaining on a term the KB cannot yet place.
  ;; `(hasCapability bird flying)` was admitted exactly that way: `arg … 1 animal` had
  ;; nothing to say about `bird` before `(genl bird animal)` landed, and once it landed
  ;; nothing went back to look.  There is no retroactive `:arg-type` report, so
  ;; `violations` stayed empty and the KB shipped seven facts its own checker convicts.
  ;;
  ;; This is the check that closes it: every sentence an author wrote, put to `check`
  ;; against the FULLY loaded KB, where every declaration and every placement is in.  The
  ;; ordering that admitted it cannot hide it here.
  ;;
  ;; Authored sentences rather than stored ones, which is what lets this cover the rules:
  ;; a rule reaches the store split into slots and an `exceptWhen` as a `sentexHandle`
  ;; reference, both engine encodings that no `.txt` contains.  The stored side is swept
  ;; by `ontology-test/every-fact-the-starter-ships-satisfies-the-declarations-it-ships`,
  ;; which catches what a rule *derives* — six of those seven facts — and the two together
  ;; cover what either alone would miss.
  (let [authored (authored-sentences)
        guilty   (for [[c s] authored
                       :let  [ps (try (v/check kb s c)
                                      (catch clojure.lang.ExceptionInfo e
                                        [{:type (:type (ex-data e) :threw)
                                          :message (ex-message e)}]))]
                       :when (seq ps)]
                   [s c (mapv :type ps) (:message (first ps))])]
    (is (< 1000 (count authored))
        "the sweep found the shipped files — an empty read would pass vacuously")
    (is (empty? guilty)
        (str "shipped sentences their own KB convicts: " (vec guilty)))))

(def ^:private defining-functors
  "The functors whose sentence *defines or extends* the term it names, as opposed to
  merely using it.  A `(comment T …)` or `(arity T 2)` defines `T`; a `(genl sub super)`
  defines `sub` and **extends** `super`, since it adds to what the supertype's extent
  holds; a `disjoint` extends both sides.  An `(arg P 1 T)` defines `P` and only uses
  `T` — a constraint naming a type says nothing new about the type.

  Read as a roster rather than as \"every functor\": a use is the common case and the
  test below is about the rare one."
  '#{comment unary_predicate binary_predicate ternary_predicate arity arg genlArg quotedArg
     arg1 arg2 arg3 interArg symmetric transitive asymmetric anti_symmetric anti_transitive
     reflexive irreflexive functional functionalInArg injection surjection bijection
     equivalence_relation variable_arity abducible_predicate closed_extent_predicate
     modal_predicate decontextualized_predicate forced_decontextualized_predicate
     instance_relation_predicate type_relation_predicate target_following_predicate
     reifiable_function unreifiable_function quoting_function context_denoting_function
     result genlResult transitiveInArgInverse transitiveInArg inverse relation_kind})

(defn- touched-terms
  "`term -> #{context}` over `sentences`, for the terms each one defines or extends."
  [pairs]
  (reduce (fn [acc [ctx s]]
            (if-not (seq? s)
              acc
              (let [[f & args] s]
                (cond
                  (= 'genl f)
                  (reduce #(update %1 %2 (fnil conj #{}) ctx) acc (filter symbol? (take 2 args)))
                  (contains? '#{disjoint sibling_disjoint orthogonal} f)
                  (reduce #(update %1 %2 (fnil conj #{}) ctx) acc (filter symbol? args))
                  (and (contains? defining-functors f) (symbol? (first args)))
                  (update acc (first args) (fnil conj #{}) ctx)
                  :else acc))))
          {}
          pairs))

(deftest a-term-two-spindle-members-touch-is-defined-in-the-head
  ;; A spindle is a **head** every member sees, **members** that see the head and not
  ;; each other, and a **collector** that sees every member (docs/contexts.md).  So a
  ;; term defined in one member and extended from a second is a term the extending
  ;; member cannot see, and that is a defect rather than untidiness: with `organism`
  ;; defined in CxAbstract, `(genl animal organism)` written in CxOrganism left
  ;; `animal` unable to reach `thing` FROM CxOrganism, so every `arg` constraint written
  ;; there convicted nothing in its own context and `isa?` answered false about a type
  ;; the file defines.
  ;;
  ;; The rule, and what this holds: a term more than one member of a spindle defines or
  ;; extends belongs at or above that spindle's head — CxCore for the upper spindle, and
  ;; for the middle spindle CxUniverse or anything CxUniverse sees, which is the whole
  ;; upper spindle it collects.  Using another member's term is not caught here and is a
  ;; separate question; *extending* one is what breaks a closure.
  (let [pairs      (authored-sentences)
        from       (fn [ctxs] (fn [[c _]] (contains? ctxs c)))
        members    (fn [dir] (set (seed/layer-contexts dir)))
        upper      (members "upper")
        middle     (members "middle")
        in-head    (set (keys (touched-terms (filter (from #{'CxCore}) pairs))))
        in-upper   (set (keys (touched-terms (filter (from upper) pairs))))]
    (is (seq upper) "the spindles were read")
    (doseq [[spindle ctxs visible]
            [["upper" upper in-head] ["middle" middle (into in-head in-upper)]]]
      (let [shared (for [[t cs] (touched-terms (filter (from ctxs) pairs))
                         :when  (and (< 1 (count cs)) (not (contains? visible t)))]
                     [t (sort cs)])]
        (is (empty? (sort shared))
            (str "two members of the " spindle " spindle define or extend these, and no"
                 " context at or above their head defines the term — push it up to the"
                 " head: " (pr-str (sort shared))))))))

(tu/deftest-kb starter-loads-and-reasons
  (testing "the universal rule fires on natural-world facts, landing in CxNaturalWorld"
    (is (seq (v/sentexes-matching kb '(grandparentOf Tom Ann) 'CxNaturalWorld)))
    (is (empty? (v/sentexes-matching kb '(grandparentOf Tom Ann) 'CxUniverse))))
  (testing "the genl taxonomy answers isa? queries"
    (is (v/isa? kb 'Muffet 'animal))
    (is (v/isa? kb 'Tom 'thing))
    (is (v/isa? kb 'Tweety 'animal))                  ; penguin -> bird -> animal
    (is (not (v/isa? kb 'Tom 'dog)))))

(tu/deftest-kb starter-common-sense-reasoning
  (testing "defeasible flight: eagles fly by default, penguins (flightless birds) do not"
    (is (seq   (v/sentexes-matching kb '(hasCapability Sam flying) 'CxNaturalWorld)))
    (is (empty? (v/sentexes-matching kb '(hasCapability Tweety flying) 'CxNaturalWorld)))
    (is (seq   (v/sentexes-matching kb '(not (hasCapability Tweety flying)) 'CxNaturalWorld)))
    (is (empty? (v/conflicts kb))))                   ; the strict exception resolves cleanly
  (testing "the mortality default reaches every living individual"
    (is (seq (v/sentexes-matching kb '(mortal Tom) 'CxNaturalWorld)))
    (is (seq (v/sentexes-matching kb '(mortal Muffet) 'CxNaturalWorld))))
  (testing "predicate metadata answers via the generic provers"
    (is (v/ask? kb '(ancestorOf Tom Ann)))            ; transitive closure of parentOf
    (is (v/ask? kb '(childOf Bob Tom)))               ; inverse of parentOf
    (is (v/ask? kb '(siblingOf Carol Ann)))           ; symmetric
    (is (v/ask? kb '(partOf Piston1 Car1))))          ; transitive
  (testing "functional birthYearOf makes a second, different value a clash"
    (is (tu/stored-in-clash? kb '(birthYearOf Tom 1971) 'CxSocialWorld))))

(tu/deftest-kb every-stored-sentence-satisfies-the-naming-invariants
  ;; `nm/problems` checks a functor per *literal*, so tightening it can invalidate
  ;; content that passes at the top level and not below it.  This is the gate on that: the
  ;; shipped schema (`resources/kb/**`) plus the whole test-world, every sentex the
  ;; load actually stored — **derived** conclusions included, which `assert` never
  ;; name-checks because they come out of the chainer rather than from a caller.
  (let [offenders (for [h  (p/sentex-ids (:records kb))
                        :let [sx (p/get-sentex (:records kb) h)
                              ps (nm/problems (:sentence sx) (:context sx))]
                        :when (seq ps)]
                    [h (:sentence sx) (:context sx) (vec ps)])]
    (is (< 500 (count (p/sentex-ids (:records kb)))) "the load is the size it should be")
    (is (= [] (vec offenders)))))

(tu/deftest-kb starter-documents-its-vocabulary
  (testing "every ontology type carries exactly one comment"
    (doseq [t '[thing intangible tangible temporal
                substance made natural formation body_part food organism vehicle tool building
                animal plant mammal bird fish reptile insect person human dog cat
                lion mouse hare wolf tortoise ant grasshopper
                penguin eagle sparrow tree flower]]
      (is (= 1 (count (core-context/comment-of kb t))) (str "type " t))))
  (testing "every domain relation is documented"
    (doseq [p '[parentOf grandparentOf childOf ancestorOf siblingOf marriedTo
                motherOf fatherOf
                likes eats owns partOf locatedIn hasCapability capabilityType
                mortal birthYearOf olderThan
                weightOf heightOf heavierThan tallerThan
                signOf trendOf derivativeOf greaterInMagnitudeThan
                qualitativeSum qualitativeDifference qualitativeProduct]]
      (is (seq (core-context/comment-of kb p)) (str "relation " p)))))

(tu/deftest-kb every-shipped-unit-converts-to-a-base-in-its-own-dimension
  ;; The unit table is the one place the schema ships individuals, and a half-stated
  ;; unit is worse than an absent one: the provers read `dimensionOf` to decide
  ;; comparability and `conversionFactor` to normalize, so a unit with one and not the
  ;; other silently answers nothing rather than failing.  This is the gate on that.
  (let [dimension  (into {} (map (fn [sx] (let [[_ u d] (:sentence sx)] [u d])))
                         (v/sentexes-with-functor kb 'dimensionOf {:believed? true}))
        conversion (into {} (map (fn [sx] (let [[_ u b f] (:sentence sx)] [u [b f]])))
                         (v/sentexes-with-functor kb 'conversionFactor {:believed? true}))]
    (is (seq dimension) "the table is not empty")
    (is (= (set (keys dimension)) (set (keys conversion)))
        "every unit states both its dimension and its factor")
    (doseq [[unit [base factor]] conversion]
      (is (= (dimension unit) (dimension base))
          (str unit " converts to a base of another dimension"))
      (is (number? factor) (str unit "'s factor is a number"))
      (is (pos? factor) (str unit "'s factor is positive")))
    (testing "each dimension's base unit is its own base, at factor 1"
      (doseq [[_ [base _]] conversion]
        (is (= [base 1] (conversion base))
            (str base " is a base unit, so it converts to itself unchanged"))))))

(tu/deftest-kb a-unit-table-entry-types-its-unit-and-its-dimension
  ;; `(dimensionOf Kilogram Mass)` proves `(unit_of_measure Kilogram)` and
  ;; `(physical_dimension Mass)` from CxMeasure's declarations under either reading, and
  ;; stores no `(thing Kilogram)`
  (let [entries (v/sentexes-with-functor kb 'dimensionOf {:believed? true})]
    (is (seq entries))
    (doseq [{[_ unit dimension] :sentence c :context} entries]
      (is (v/ask? kb (list 'unit_of_measure unit) c) (str unit))
      (is (v/ask? kb (list 'physical_dimension dimension) c) (str dimension))
      (is (nil? (v/handle-of kb (list 'thing unit) c)) (str unit)))))

(deftest no-shipped-declaration-makes-an-argument-a-thing
  ;; `genlArg … thing` is not in the roster: it says the position holds a type
  (let [declares #{'arg 'arg1 'arg2 'arg3 'arg4 'arg5 'args 'argAndRest 'quotedArg}
        bare     #(if (and (seq? %) (= 'set/monotonic (first %))) (second %) %)]
    (is (empty? (for [[c s] (authored-sentences)
                      :let  [s (bare s)]
                      :when (and (seq? s) (declares (first s)) (= 'thing (last s)))]
                  [c s])))))
