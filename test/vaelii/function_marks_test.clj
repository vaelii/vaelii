;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.function-marks-test
  "`injection`, `surjection` and `bijection`, the three composite function marks shipped
  in CxCore: no engine code, eight CxCore forward rules derive what the engine already
  enforces and audits — `equivalence_relation`'s pattern, over the functional family and
  the `predAll` audit pair.

  Each mark splits into two halves, and the split is the design. The **enforced** half is
  `(functional P)` and `(functionalInArg P 1)`, refused or merged at the assert entry
  point. The **audited** half is the binary `(predAllSpecified P D)` for totality and
  `(predSpecifiedAll P R)` for ontoness, reported by `specified-violations` when a
  caller asks. Each rule reads only the ONE arg declaration naming its quantified
  collection — `(arg P 1 D)` for totality, `(arg P 2 R)` for ontoness — and the
  filler's own type is derived by the audit from the predicate's slot contract at read
  time. A predicate whose quantified side is untyped concludes no requirement; one
  whose filler side is untyped concludes it, and the audit reports the missing slot
  contract as an explicit gap.

  | mark | functional | one-to-one | total | onto |
  |---|---|---|---|---|
  | `injection`  | yes | yes | yes | no  |
  | `surjection` | yes | no  | yes | yes |
  | `bijection`  | yes | yes | yes | yes |

  The merge/refuse rule itself is `functional`'s and is tested exhaustively in
  `functional-in-arg-test`; the audit is `predAllSpecified`'s and is tested in
  `predall-test`. What is tested here is that the SHIPPED declarations wire both halves,
  that the wiring is belief-following, and that the audit half follows the `arg`
  declarations it reads.

  A CxCore-loaded KB throughout, like `relation-properties-test`: the shipped
  declarations are what is tested, not a hand-built fixture that could drift from the
  file."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (core-context/load-into))))

(defn- ex-type
  "The `:type` on the ex-info a thunk throws, or nil if it does not throw."
  [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(def ^:private U 'CxUniverse)

(defn- typed-relation!
  "Declare `pred` a binary predicate from `d` to `r`, both types under `thing`, and return
  the handle of the domain `arg` declaration so a test can retract it."
  [kb pred d r]
  (v/assert kb (list 'genl d 'thing) U)
  (v/assert kb (list 'genl r 'thing) U)
  (v/assert kb (list 'binary_predicate pred) U)
  (let [dom (v/assert kb (list 'arg pred 1 d) U)]
    (v/assert kb (list 'arg pred 2 r) U)
    dom))

;;; ── the shipped declarations ──────────────────────────────────────────

(tu/deftest-kb cxcore-declares-the-three-function-marks
  (doseq [term '[injection surjection bijection]]
    (testing (str term " carries its comment sentex like any other CxCore entry")
      (is (= 1 (count (core-context/comment-of kb term))) (str "comment for " term))
      (is (string? (first (core-context/comment-of kb term)))))
    (testing (str "and the classification half: a " term " is a binary_predicate")
      (tu/with-terms [capitalCityOf]
        (v/assert kb (list term capitalCityOf) U)
        (is (v/ask? kb (list 'binary_predicate capitalCityOf) U))))))

(tu/deftest-kb a-bijection-is-an-injection-and-a-surjection
  (tu/with-terms [capitalCityOf]
    (v/assert kb (list 'bijection capitalCityOf) U)
    (is (v/ask? kb (list 'injection capitalCityOf) U))
    (is (v/ask? kb (list 'surjection capitalCityOf) U))))

;;; ── the enforced half: marks the engine already refuses against ───────

(tu/deftest-kb each-mark-derives-the-enforced-marks-it-stands-in-for
  (testing "an injection is single-valued and one-to-one"
    (tu/with-terms [capitalCityOf]
      (v/assert kb (list 'injection capitalCityOf) U)
      (is (v/ask? kb (list 'functional capitalCityOf) U))
      (is (v/ask? kb (list 'functionalInArg capitalCityOf 1) U))))
  (testing "a surjection is single-valued, and says nothing about one-to-one"
    (tu/with-terms [pRel]
      (v/assert kb (list 'surjection pRel) U)
      (is (v/ask? kb (list 'functional pRel) U))
      (is (not (v/ask? kb (list 'functionalInArg pRel 1) U))
          "two domain members may share one range member under a surjection")))
  (testing "a bijection is both, through the two marks it derives"
    (tu/with-terms [pRel]
      (v/assert kb (list 'bijection pRel) U)
      (is (v/ask? kb (list 'functional pRel) U))
      (is (v/ask? kb (list 'functionalInArg pRel 1) U)))))

(tu/deftest-kb a-bijection-refuses-two-unmergeable-fillers-in-either-direction
  (tu/with-terms [pRel Ruritania]
    (v/assert kb (list 'bijection pRel) U)
    (testing "a second number at argument 2 for one argument 1 is refused"
      (v/assert kb (list pRel Ruritania 1980) U)
      (is (= :functional (ex-type #(v/assert kb (list pRel Ruritania 1990) U)))
          "no merge can make 1980 and 1990 one thing"))
    (testing "and a second number at argument 1 for one argument 2 is refused the same"
      (tu/with-terms [Zenda]
        (v/assert kb (list pRel 7 Zenda) U)
        (is (= :functional (ex-type #(v/assert kb (list pRel 8 Zenda) U)))
            "the mirrored refusal, via the derived (functionalInArg P 1)")))))

(tu/deftest-kb a-surjection-admits-the-pair-an-injection-refuses
  ;; The one behavioural difference between the two marks, at the entry point: a
  ;; surjection is not one-to-one, so two domain members sharing a range member stand.
  (tu/with-terms [pSur pInj Fredopolis]
    (v/assert kb (list 'surjection pSur) U)
    (v/assert kb (list pSur 7 Fredopolis) U)
    (is (nil? (ex-type #(v/assert kb (list pSur 8 Fredopolis) U)))
        "two first arguments for one second are what a surjection permits")
    (v/assert kb (list 'injection pInj) U)
    (v/assert kb (list pInj 7 Fredopolis) U)
    (is (= :functional (ex-type #(v/assert kb (list pInj 8 Fredopolis) U)))
        "and what an injection refuses")))

(tu/deftest-kb a-bijection-merges-two-symbol-fillers-in-either-direction
  (tu/with-terms [capitalCityOf]
    (v/assert kb (list 'bijection capitalCityOf) U)
    (testing "a shared first argument merges its two symbol fillers — the functional half"
      (tu/with-terms [Freedonia]
        (let [[lo hi] (sort [(tu/tmp-ind "Fredville") (tu/tmp-ind "Fredville")])]
          (v/assert kb (list capitalCityOf Freedonia lo) U)
          (v/assert kb (list capitalCityOf Freedonia hi) U)
          (is (v/same-class? kb lo hi)
              "two names for one capital are one thing, as under (functional P)"))))
    (testing "a shared second argument merges its two — the functionalInArg 1 half"
      (tu/with-terms [Fredopolis]
        (let [[lo hi] (sort [(tu/tmp-ind "Sylvania") (tu/tmp-ind "Sylvania")])]
          (v/assert kb (list capitalCityOf lo Fredopolis) U)
          (v/assert kb (list capitalCityOf hi Fredopolis) U)
          (is (v/same-class? kb lo hi)
              "two names for one country are one thing, via (functionalInArg P 1)"))))))

;;; ── the audited half: totality and ontoness, off the arg declarations ─

(tu/deftest-kb the-audit-requirements-are-derived-from-the-arg-declarations
  (tu/with-terms [capitalCityOf country capital_city]
    (typed-relation! kb capitalCityOf country capital_city)
    (testing "an injection requires totality and says nothing about ontoness"
      (v/assert kb (list 'injection capitalCityOf) U)
      (is (v/ask? kb (list 'predAllSpecified capitalCityOf country) U))
      (is (not (v/ask? kb (list 'predSpecifiedAll capitalCityOf capital_city) U))
          "a capital no country has is not an injection's problem")))
  (testing "a surjection requires both"
    (tu/with-terms [pSur country capital_city]
      (typed-relation! kb pSur country capital_city)
      (v/assert kb (list 'surjection pSur) U)
      (is (v/ask? kb (list 'predAllSpecified pSur country) U))
      (is (v/ask? kb (list 'predSpecifiedAll pSur capital_city) U)))))

(tu/deftest-kb a-mark-on-a-predicate-with-no-arg-pair-derives-no-audit
  ;; The honest degradation: totality and ontoness name a domain and a range, and a
  ;; predicate whose arguments are undeclared states neither, so the requirements are not
  ;; derived rather than derived against `thing`.
  (tu/with-terms [pRel]
    (v/assert kb (list 'bijection pRel) U)
    (is (v/ask? kb (list 'functional pRel) U)
        "the enforced half lands with no argument declarations")
    (is (empty? (v/all-specified-violations kb U))
        "and the sweep has nothing to audit")))

(tu/deftest-kb the-sweep-reports-a-domain-member-with-no-filler
  (tu/with-terms [capitalCityOf country capital_city Freedonia Fredopolis]
    (typed-relation! kb capitalCityOf country capital_city)
    (v/assert kb (list 'bijection capitalCityOf) U)
    (v/assert kb (list country Freedonia) U)
    (testing "a country with no capital breaks totality"
      (is (= {['predAllSpecified capitalCityOf country]
              {:status :audited :violations #{Freedonia}}}
             (v/all-specified-violations kb U))))
    (testing "and stating its capital clears the sweep"
      (v/assert kb (list capital_city Fredopolis) U)
      (v/assert kb (list capitalCityOf Freedonia Fredopolis) U)
      (is (empty? (v/all-specified-violations kb U))))))

(tu/deftest-kb the-sweep-reports-a-range-member-nothing-reaches
  (tu/with-terms [capitalCityOf country capital_city Fredopolis]
    (typed-relation! kb capitalCityOf country capital_city)
    (v/assert kb (list 'bijection capitalCityOf) U)
    (v/assert kb (list capital_city Fredopolis) U)
    (testing "a capital that is the capital of nothing breaks ontoness"
      (is (= {['predSpecifiedAll capitalCityOf capital_city]
              {:status :audited :violations #{Fredopolis}}}
             (v/all-specified-violations kb U))
          "the sweep keys the declaration [functor pred indep]"))))

(tu/deftest-kb an-injection-is-audited-for-totality-and-not-for-ontoness
  ;; The discriminating case for the whole family. capitalCityOf is one-to-one and total
  ;; over `city`, and is not onto it: most cities are no country's capital.
  (tu/with-terms [capitalCityOf country city Freedonia Fredopolis Sylvania]
    (typed-relation! kb capitalCityOf country city)
    (v/assert kb (list 'injection capitalCityOf) U)
    (v/assert kb (list country Freedonia) U)
    (v/assert kb (list city Fredopolis) U)
    (v/assert kb (list city Sylvania) U)
    (v/assert kb (list capitalCityOf Freedonia Fredopolis) U)
    (is (empty? (v/all-specified-violations kb U))
        "Sylvania being nobody's capital is no violation of an injection")))

;;; ── belief-following, in both halves ──────────────────────────────────

(tu/deftest-kb retracting-the-declaration-drops-every-derived-mark
  (tu/with-terms [capitalCityOf country capital_city]
    (typed-relation! kb capitalCityOf country capital_city)
    (let [decl (v/assert kb (list 'bijection capitalCityOf) U)]
      (is (v/ask? kb (list 'functional capitalCityOf) U))
      (v/retract! kb decl)
      (testing "the derived marks rested on the declaration and go with it"
        (is (not (v/ask? kb (list 'injection capitalCityOf) U)))
        (is (not (v/ask? kb (list 'surjection capitalCityOf) U)))
        (is (not (v/ask? kb (list 'functional capitalCityOf) U)))
        (is (not (v/ask? kb (list 'functionalInArg capitalCityOf 1) U)))
        (is (not (v/ask? kb (list 'predAllSpecified capitalCityOf country) U)))
        (is (not (v/ask? kb (list 'predSpecifiedAll capitalCityOf capital_city) U)))))))

(tu/deftest-kb retracting-an-arg-declaration-drops-its-audit-and-gaps-the-twin
  ;; Each audit rule rests on the ONE arg declaration naming its quantified side, and the
  ;; enforced half rests on neither. Withdrawing the domain type drops the totality
  ;; requirement outright; the ontoness requirement still stands on the range declaration,
  ;; but its filler side is now untyped, so the audit reports it as an explicit gap
  ;; rather than auditing unconstrained.
  (tu/with-terms [capitalCityOf country capital_city]
    (let [dom (typed-relation! kb capitalCityOf country capital_city)]
      (v/assert kb (list 'bijection capitalCityOf) U)
      (v/retract! kb dom)
      (is (not (v/ask? kb (list 'predAllSpecified capitalCityOf country) U))
          "totality rested on the domain declaration and goes with it")
      (is (v/ask? kb (list 'predSpecifiedAll capitalCityOf capital_city) U)
          "ontoness rests on the range declaration and stands")
      (is (= {:status :gap :gap :missing-slot-typing :pred capitalCityOf :position 1}
             (get (v/all-specified-violations kb U)
                  ['predSpecifiedAll capitalCityOf capital_city]))
          "and its audit reports the withdrawn filler typing as a gap")
      (is (v/ask? kb (list 'functional capitalCityOf) U)
          "single-valued does not rest on the domain being declared")
      (is (v/ask? kb (list 'functionalInArg capitalCityOf 1) U)))))

;;; ── the declaration reaches back over content already stored ──────────

(tu/deftest-kb a-bijection-declared-after-an-unmergeable-pair-convicts-that-pair
  ;; The arrival order the mark family gets wrong when a spelling reaches the sweep
  ;; through only some of its readers (#45): the pair is stored first and the
  ;; declaration second, so nothing refuses at the entry point and what has to convict
  ;; is the retroactive pass. Every mark here is derived rather than written, so the pass
  ;; runs against a conclusion of a rule.
  (tu/with-terms [pRel Ruritania]
    (v/assert kb (list pRel Ruritania 1980) U)
    (v/assert kb (list pRel Ruritania 1990) U)
    (v/assert kb (list 'bijection pRel) U)
    (is (= [:functional] (mapv :violation (v/violations kb)))
        "the stored pair sharing argument 1 is convicted by the derived (functional P)")))

(tu/deftest-kb a-late-bijection-convicts-a-stored-pair-sharing-argument-2
  (tu/with-terms [pRev Zenda]
    (v/assert kb (list pRev 7 Zenda) U)
    (v/assert kb (list pRev 8 Zenda) U)
    (v/assert kb (list 'bijection pRev) U)
    (is (= [:functional] (mapv :violation (v/violations kb)))
        "the mirrored conviction, by the derived (functionalInArg P 1)")))

(tu/deftest-kb a-late-bijection-merges-two-mergeable-fillers-in-either-direction
  (testing "a stored pair sharing argument 1"
    (tu/with-terms [pRel Freedonia]
      (let [[lo hi] (sort [(tu/tmp-ind "Fredville") (tu/tmp-ind "Fredville")])]
        (v/assert kb (list pRel Freedonia lo) U)
        (v/assert kb (list pRel Freedonia hi) U)
        (v/assert kb (list 'bijection pRel) U)
        (is (v/same-class? kb lo hi)))))
  (testing "and a stored pair sharing argument 2"
    (tu/with-terms [pRev Fredopolis]
      (let [[lo hi] (sort [(tu/tmp-ind "Sylvania") (tu/tmp-ind "Sylvania")])]
        (v/assert kb (list pRev lo Fredopolis) U)
        (v/assert kb (list pRev hi Fredopolis) U)
        (v/assert kb (list 'bijection pRev) U)
        (is (v/same-class? kb lo hi))))))

(tu/deftest-kb an-arg-declaration-arriving-after-the-mark-derives-the-audit
  ;; The other arrival order for the audit half: the mark is stated of a predicate whose
  ;; arguments are undeclared, and the domain and range are declared afterwards.
  (tu/with-terms [capitalCityOf country capital_city]
    (v/assert kb (list 'bijection capitalCityOf) U)
    (is (not (v/ask? kb (list 'predAllSpecified capitalCityOf country) U)))
    (typed-relation! kb capitalCityOf country capital_city)
    (is (v/ask? kb (list 'predAllSpecified capitalCityOf country) U))
    (is (v/ask? kb (list 'predSpecifiedAll capitalCityOf capital_city) U))))

;;; ── the enforced marks descend the predicate hierarchy ────────────────

(tu/deftest-kb a-bijection-on-a-super-predicate-convicts-a-sub-predicate-pair
  ;; Both enforced marks are read up the predicate hierarchy, as every constraint mark
  ;; is, so the declaration is written once at the general predicate. The query does not
  ;; descend — `(functional fatherOf)` is false — and the enforcement does, which is the
  ;; distinction taxonomy.md draws between a mark's classification and its reach.
  (tu/with-terms [parentOf fatherOf Ann Bob]
    (v/assert kb (list 'bijection parentOf) U)
    (v/assert kb (list 'genl fatherOf parentOf) U)
    (is (not (v/ask? kb (list 'functional fatherOf) U))
        "the sub-predicate is not itself classified functional")
    (v/assert kb (list fatherOf Ann 1980) U)
    (is (= :functional (ex-type #(v/assert kb (list fatherOf Ann 1990) U)))
        "and is enforced anyway, at argument 2")
    (v/assert kb (list fatherOf 7 Bob) U)
    (is (= :functional (ex-type #(v/assert kb (list fatherOf 8 Bob) U)))
        "and at argument 1")))

;;; ── the declarations are decontextualized ─────────────────────────────

(tu/deftest-kb a-mark-stated-in-one-theory-is-the-whole-kb-s-claim
  ;; The three are `decontextualized_predicate`s, so a declaration is the KB's claim
  ;; about the predicate rather than the theory's — and the marks derived from it reach
  ;; CxUniverse with it.
  (tu/with-terms [pRel CxStory]
    (v/assert kb (list 'genlCx CxStory U) U)
    (v/assert kb (list 'bijection pRel) CxStory)
    (doseq [s [(list 'bijection pRel) (list 'injection pRel) (list 'surjection pRel)
               (list 'functional pRel) (list 'functionalInArg pRel 1)]]
      (is (v/ask? kb s U) (str s " reaches CxUniverse")))))
