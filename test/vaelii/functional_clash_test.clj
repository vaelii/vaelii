;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.functional-clash-test
  "A second, distinct value of a `functional` predicate: what `try-assert` refuses and
  what plain `assert` leaves behind.

  The setting throughout is `(functional statusOf)` declared in CxUniverse and the facts
  written in a child context below it.  Two numbers can never be one thing, so
  `try-assert` refuses the second as a `:functional` definitional clash.  Two symbols
  can be — `functional` reconciles a pair of `:monotonic` symbol values by deriving
  `(equals V1 V2)` and merging them (docs/equality.md), and leaves a `:default` pair as
  a dilemma — so today `try-assert` stores the second symbol, whether or not the KB
  states the two values distinct, by a `(not (equals …))` or by disjoint types.

  The `^:red` tests hold the intended behaviour: `try-assert` refuses a second, distinct
  symbol value as a `:functional` clash, and plain `assert` does not merge two values
  the KB states distinct without reporting it.  The green tests check what plain `assert`
  does today where that is the intended reading."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(defn- kb-with-starter
  "A fresh starter KB per arm, so each strength is compared on the same baseline."
  [] (doto (tu/empty-kb) (tu/load-starter!)))

(defn- held?
  "Is `sentence` stored in `context` and believed?"
  [kb sentence context]
  (boolean (some->> (v/handle-of kb sentence context) (v/in? kb))))

(defn- reports
  "Every reported clash, dilemmas and conflicts alike, as `{:kind … :sentences #{…}}`."
  [kb]
  (for [c (concat (v/contradictions kb) (v/conflicts kb))]
    {:kind (:kind c) :sentences (into #{} (map :sentence) (:sides c))}))

(defn- reported-naming?
  "Does some reported clash name `sentence` as one of its sides?"
  [kb sentence]
  (boolean (some #(contains? (:sentences %) sentence) (reports kb))))

(defmacro ^:private with-functional-slot
  "Bind `kb` to a fresh starter KB holding `(functional statusOf)` in CxUniverse and
  `CxThe` below it, and the gensym'd terms to their names, for `body`."
  [[kb] & body]
  `(tu/with-neutral-kb [~kb kb-with-starter]
     (tu/with-terms [~'statusOf ~'Pr ~'Draft ~'Open ~'CxThe]
       (v/assert ~kb (list '~'genlCx ~'CxThe '~'CxUniverse) '~'CxUniverse)
       (v/assert ~kb (list '~'functional ~'statusOf) '~'CxUniverse)
       ~@body)))

;; ---- 1. two numbers --------------------------------------------------------

(deftest try-assert-refuses-a-second-number-value-of-a-functional-predicate
  (with-functional-slot [kb]
    (v/try-assert kb (list statusOf Pr 1) CxThe)
    (let [r (tu/refusal-data #(v/try-assert kb (list statusOf Pr 2) CxThe))]
      (is (= :definitional-clash (:type r)))
      (is (= :functional (:violation r)))
      (is (= [(list statusOf Pr 1)] (mapv :sentence (:clashes-with r)))
          "the refusal names the stored value it clashes with")
      (is (nil? (v/handle-of kb (list statusOf Pr 2) CxThe)) "and stores nothing"))))

(deftest assert-stores-a-second-number-value-as-a-functional-dilemma
  ;; no merge can make two numbers one thing, so plain assert keeps both default facts
  ;; and reports the pair as a :functional dilemma
  (with-functional-slot [kb]
    (v/assert kb (list statusOf Pr 1) CxThe)
    (v/assert kb (list statusOf Pr 2) CxThe)
    (is (true? (held? kb (list statusOf Pr 1) CxThe)))
    (is (true? (held? kb (list statusOf Pr 2) CxThe)))
    (is (some #(= {:kind :functional :sentences #{(list statusOf Pr 1) (list statusOf Pr 2)}} %)
              (reports kb)))))

;; ---- 2. two symbols --------------------------------------------------------

(deftest assert-keeps-two-default-symbol-values-apart-as-a-functional-dilemma
  ;; a merge rests on :monotonic evidence alone, so two :default symbol values are not
  ;; merged: both stay believed and the pair is reported as a :functional dilemma
  (with-functional-slot [kb]
    (v/assert kb (list statusOf Pr Draft) CxThe)
    (v/assert kb (list statusOf Pr Open) CxThe)
    (is (true? (held? kb (list statusOf Pr Draft) CxThe)))
    (is (true? (held? kb (list statusOf Pr Open) CxThe)))
    (is (false? (v/same-class? kb Draft Open CxThe)))
    (is (true? (v/ask? kb (list 'different Draft Open) CxThe)))
    (is (some #(= {:kind :functional :sentences #{(list statusOf Pr Draft) (list statusOf Pr Open)}} %)
              (reports kb)))))

(deftest assert-merges-two-monotonic-symbol-values
  ;; functional's documented reconciliation: two :monotonic symbol values derive
  ;; (equals Draft Open) and merge, with nothing left to report
  (with-functional-slot [kb]
    (v/assert kb (list statusOf Pr Draft) CxThe {:strength :monotonic})
    (v/assert kb (list statusOf Pr Open) CxThe {:strength :monotonic})
    (is (true? (v/same-class? kb Draft Open CxThe)))
    (is (true? (held? kb (list 'equals Draft Open) CxThe)))
    (is (empty? (reports kb)))))

(deftest ^:red try-assert-refuses-a-second-symbol-value-of-a-functional-predicate
  ;; Today try-assert stores the second symbol at either strength: at :default the pair
  ;; becomes a :functional dilemma, at :monotonic Draft and Open merge.  The refusing
  ;; entry point should refuse it as a :functional clash, as it does a second number.
  (doseq [strength [:default :monotonic]]
    (testing (str "both values " strength)
      (with-functional-slot [kb]
        (v/try-assert kb (list statusOf Pr Draft) CxThe {:strength strength})
        (let [r (tu/refusal-data #(v/try-assert kb (list statusOf Pr Open) CxThe {:strength strength}))]
          (is (= :definitional-clash (:type r)))
          (is (= :functional (:violation r)))
          (is (nil? (v/handle-of kb (list statusOf Pr Open) CxThe)))
          (is (false? (v/same-class? kb Draft Open CxThe))))))))

;; ---- 3. values stated distinct by (not (equals …)) -------------------------
;; `different` is a query operator and its assert is refused, so the distinctness is
;; stated as `(not (equals Draft Open))`, which assert accepts at either strength.
;; `equals` is forced-monotonic, and a denial of a forced-monotonic literal loses to the
;; literal at either strength: when two :monotonic values derive (equals Draft Open),
;; the stated denial goes OUT and the merge stands, with nothing reported.

(defn- denial [Draft Open] (list 'not (list 'equals Draft Open)))

(defn- distinctness-stated
  "The behaviour `(not (equals Draft Open))` written at `denial-strength` leaves intact
  today: the denial is stored and believed, and two :default values beside it stay
  apart, reported as a :functional dilemma."
  [denial-strength]
  (with-functional-slot [kb]
    (v/assert kb (denial Draft Open) CxThe {:strength denial-strength})
    (is (true? (held? kb (denial Draft Open) CxThe)) "the denial is accepted and believed")
    (v/assert kb (list statusOf Pr Draft) CxThe)
    (v/assert kb (list statusOf Pr Open) CxThe)
    (is (true? (held? kb (list statusOf Pr Open) CxThe)))
    (is (false? (v/same-class? kb Draft Open CxThe)))
    (is (true? (held? kb (denial Draft Open) CxThe)))
    (is (true? (reported-naming? kb (list statusOf Pr Open))))))

(defn- distinctness-expected
  "What a stated `(not (equals Draft Open))` at `denial-strength` should do to a second
  value: `try-assert` refuses it, and plain `assert` of two :monotonic values neither
  merges them silently nor drops the denial unreported."
  [denial-strength]
  (doseq [strength [:default :monotonic]]
    (testing (str "values " strength ", via try-assert")
      (with-functional-slot [kb]
        (v/assert kb (denial Draft Open) CxThe {:strength denial-strength})
        (v/try-assert kb (list statusOf Pr Draft) CxThe {:strength strength})
        (let [r (tu/refusal-data #(v/try-assert kb (list statusOf Pr Open) CxThe {:strength strength}))]
          (is (= :definitional-clash (:type r)))
          (is (nil? (v/handle-of kb (list statusOf Pr Open) CxThe)))))))
  (testing "values :monotonic, via assert"
    (with-functional-slot [kb]
      (v/assert kb (denial Draft Open) CxThe {:strength denial-strength})
      (v/assert kb (list statusOf Pr Draft) CxThe {:strength :monotonic})
      (v/assert kb (list statusOf Pr Open) CxThe {:strength :monotonic})
      (is (or (and (false? (v/same-class? kb Draft Open CxThe))
                   (held? kb (denial Draft Open) CxThe))
              (reported-naming? kb (denial Draft Open))
              (reported-naming? kb (list statusOf Pr Open)))
          "the stated distinctness either holds or its defeat is reported"))))

(deftest a-default-denial-of-equality-keeps-two-default-values-apart
  (distinctness-stated :default))

(deftest a-monotonic-denial-of-equality-keeps-two-default-values-apart
  (distinctness-stated :monotonic))

(deftest ^:red a-default-denial-of-equality-makes-a-second-value-a-clash
  ;; Today: try-assert stores the second value at either strength; plain assert of two
  ;; :monotonic values merges Draft and Open, the denial goes OUT, nothing is reported.
  (distinctness-expected :default))

(deftest ^:red a-monotonic-denial-of-equality-makes-a-second-value-a-clash
  ;; Today: as for the :default denial — the :monotonic denial also goes OUT under the
  ;; derived (equals Draft Open), and neither conflicts nor contradictions name it.
  (distinctness-expected :monotonic))

;; ---- 4. values in disjoint types ---------------------------------------------

(defmacro ^:private with-disjoint-values
  "`with-functional-slot`, plus `(disjoint draft_state open_state)` :monotonic in
  CxUniverse and Draft and Open each a :default member of one of them in CxThe."
  [[kb] & body]
  `(with-functional-slot [~kb]
     (tu/with-terms [~'draft_state ~'open_state]
       (v/assert ~kb (list '~'disjoint ~'draft_state ~'open_state) '~'CxUniverse {:strength :monotonic})
       (v/assert ~kb (list ~'draft_state ~'Draft) ~'CxThe)
       (v/assert ~kb (list ~'open_state ~'Open) ~'CxThe)
       ~@body)))

(deftest assert-keeps-two-default-values-of-disjoint-types-apart
  (with-disjoint-values [kb]
    (v/assert kb (list statusOf Pr Draft) CxThe)
    (v/assert kb (list statusOf Pr Open) CxThe)
    (is (true? (held? kb (list statusOf Pr Open) CxThe)))
    (is (false? (v/same-class? kb Draft Open CxThe)))
    (is (some #(= {:kind :functional :sentences #{(list statusOf Pr Draft) (list statusOf Pr Open)}} %)
              (reports kb)))))

(deftest ^:red values-of-disjoint-types-are-never-merged-by-a-functional-collision
  ;; Today: try-assert stores the second value at either strength.  With :monotonic
  ;; values plain assert merges Draft and Open, and the merge surfaces only afterwards
  ;; as a :disjoint dilemma between (draft_state Draft) and the migrated (open_state
  ;; Draft) — the functional collision itself is not reported.
  (doseq [strength [:default :monotonic]]
    (testing (str "values " strength ", via try-assert")
      (with-disjoint-values [kb]
        (v/try-assert kb (list statusOf Pr Draft) CxThe {:strength strength})
        (let [r (tu/refusal-data #(v/try-assert kb (list statusOf Pr Open) CxThe {:strength strength}))]
          (is (= :definitional-clash (:type r)))
          (is (nil? (v/handle-of kb (list statusOf Pr Open) CxThe)))))))
  (testing "values :monotonic, via assert"
    (with-disjoint-values [kb]
      (v/assert kb (list statusOf Pr Draft) CxThe {:strength :monotonic})
      (v/assert kb (list statusOf Pr Open) CxThe {:strength :monotonic})
      (is (false? (v/same-class? kb Draft Open CxThe)))
      (is (true? (reported-naming? kb (list statusOf Pr Open)))))))
