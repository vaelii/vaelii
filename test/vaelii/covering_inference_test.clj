;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.covering-inference-test
  "The one inference a cover licenses: for an n-part cover, n−1 explicit negations prove
  the nth part.  Nothing fires on absence — a whole instance with no part known stays
  unknown, which is what keeps a coverage axiom apart from negation as failure."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb ruling-out-every-part-but-one-proves-the-one-that-is-left
  (tu/with-terms [animal dog cat Rex]
    (v/assert kb (list 'covering animal dog cat) 'CxUniverse)
    (v/assert kb (list animal Rex) 'CxUniverse)
    (v/assert kb (list 'not (list dog Rex)) 'CxUniverse)
    (is (v/ask? kb (list cat Rex) 'CxUniverse))
    (testing "and the symmetric case, which is the same declaration read the other way"
      (tu/with-terms [Muffet]
        (v/assert kb (list animal Muffet) 'CxUniverse)
        (v/assert kb (list 'not (list cat Muffet)) 'CxUniverse)
        (is (v/ask? kb (list dog Muffet) 'CxUniverse))))))

(tu/deftest-kb a-whole-instance-with-no-part-known-stays-unknown
  (tu/with-terms [animal dog cat Rex]
    (v/assert kb (list 'covering animal dog cat) 'CxUniverse)
    (v/assert kb (list animal Rex) 'CxUniverse)
    (testing "the cover invents no membership and picks no part"
      (is (not (v/ask? kb (list dog Rex) 'CxUniverse)))
      (is (not (v/ask? kb (list cat Rex) 'CxUniverse))))
    (testing "and an incomplete KB is not a counterexample to the cover"
      (is (empty? (v/conflicts kb))))))

(tu/deftest-kb an-n-part-cover-needs-n-minus-one-negations
  (tu/with-terms [animal dog cat bird Rex]
    (v/assert kb (list 'covering animal dog cat bird) 'CxUniverse)
    (v/assert kb (list animal Rex) 'CxUniverse)
    (v/assert kb (list 'not (list dog Rex)) 'CxUniverse)
    (testing "one negation of a three-part cover leaves two parts open"
      (is (not (v/ask? kb (list cat Rex) 'CxUniverse)))
      (is (not (v/ask? kb (list bird Rex) 'CxUniverse))))
    (v/assert kb (list 'not (list cat Rex)) 'CxUniverse)
    (testing "the second negation leaves one, and proves it"
      (is (v/ask? kb (list bird Rex) 'CxUniverse)))))

(tu/deftest-kb a-term-outside-the-whole-is-under-no-obligation
  (tu/with-terms [animal dog cat Tweety]
    (v/assert kb (list 'covering animal dog cat) 'CxUniverse)
    (v/assert kb (list 'not (list dog Tweety)) 'CxUniverse)
    (testing "the cover speaks about instances of the whole and about nothing else"
      (is (not (v/ask? kb (list cat Tweety) 'CxUniverse)))
      (is (empty? (v/conflicts kb))))))

(tu/deftest-kb the-inference-follows-the-negation-it-rests-on
  (tu/with-terms [animal dog cat Rex]
    (v/assert kb (list 'covering animal dog cat) 'CxUniverse)
    (v/assert kb (list animal Rex) 'CxUniverse)
    (let [h (v/assert kb (list 'not (list dog Rex)) 'CxUniverse)]
      (is (v/ask? kb (list cat Rex) 'CxUniverse))
      (v/retract! kb h)
      (is (not (v/ask? kb (list cat Rex) 'CxUniverse))
          "retracting the evidence withdraws the conclusion"))))

(tu/deftest-kb the-inference-follows-the-declaration-it-rests-on
  (tu/with-terms [animal dog cat Rex]
    (let [h (v/assert kb (list 'covering animal dog cat) 'CxUniverse)]
      (v/assert kb (list animal Rex) 'CxUniverse)
      (v/assert kb (list 'not (list dog Rex)) 'CxUniverse)
      (is (v/ask? kb (list cat Rex) 'CxUniverse))
      (v/retract! kb h)
      (is (not (v/ask? kb (list cat Rex) 'CxUniverse))))))

(tu/deftest-kb a-whole-instance-reached-through-a-subtype-is-covered-too
  (tu/with-terms [animal mammal dog cat Rex]
    (v/assert kb (list 'covering animal dog cat) 'CxUniverse)
    (v/assert kb (list 'genl mammal animal) 'CxUniverse)
    (v/assert kb (list mammal Rex) 'CxUniverse)
    (v/assert kb (list 'not (list dog Rex)) 'CxUniverse)
    (is (v/ask? kb (list cat Rex) 'CxUniverse)
        "membership in the whole is read through the closure, as every membership is")))

(tu/deftest-kb a-partition-licenses-the-same-inference-its-coverage-half-does
  (tu/with-terms [animal dog cat Rex]
    (v/assert kb (list 'partition animal dog cat) 'CxUniverse)
    (v/assert kb (list animal Rex) 'CxUniverse)
    (v/assert kb (list 'not (list dog Rex)) 'CxUniverse)
    (is (v/ask? kb (list cat Rex) 'CxUniverse))))

(tu/deftest-kb a-cover-answers-where-its-declaration-is-visible
  (tu/with-terms [animal dog cat Rex CxTheory CxBelow CxOther]
    (v/assert kb (list 'genlCx CxBelow CxTheory) 'CxUniverse)
    (v/assert kb (list 'covering animal dog cat) CxTheory)
    (v/assert kb (list animal Rex) CxTheory)
    (v/assert kb (list 'not (list dog Rex)) CxTheory)
    (testing "a reader of the declaring context sees the conclusion"
      (is (v/ask? kb (list cat Rex) CxTheory)))
    (testing "and so does a context below it, which sees the declaration"
      (is (v/ask? kb (list cat Rex) CxBelow)))
    (testing "a context that cannot see the declaration does not"
      (is (not (v/ask? kb (list cat Rex) CxOther))))))

;; ---- denying every part refutes the cover itself ------------------------

(defn- outcome
  "`:ok`, or the `:type` of the refusal, so a case is compared as a value rather than as
  the presence or absence of a throw."
  [kb sentence context]
  (try (v/assert kb sentence context) :ok
       (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(tu/deftest-kb denying-every-part-of-a-cover-refutes-the-cover
  (tu/with-terms [animal dog cat Rex]
    (v/assert kb (list 'covering animal dog cat) 'CxUniverse)
    (v/assert kb (list animal Rex) 'CxUniverse)
    (v/assert kb (list 'not (list dog Rex)) 'CxUniverse)
    (testing "the negation that leaves no part standing is refused where it is written"
      (is (= :cover (outcome kb (list 'not (list cat Rex)) 'CxUniverse))))))

(tu/deftest-kb a-partly-denied-cover-is-no-violation
  (tu/with-terms [animal dog cat bird Rex]
    (v/assert kb (list 'covering animal dog cat bird) 'CxUniverse)
    (v/assert kb (list animal Rex) 'CxUniverse)
    (v/assert kb (list 'not (list dog Rex)) 'CxUniverse)
    (is (= :ok (outcome kb (list 'not (list cat Rex)) 'CxUniverse))
        "one part is still open, so the cover is not refuted")))

(tu/deftest-kb a-term-the-whole-does-not-hold-denies-every-part-freely
  (tu/with-terms [animal dog cat Tweety]
    (v/assert kb (list 'covering animal dog cat) 'CxUniverse)
    (v/assert kb (list 'not (list dog Tweety)) 'CxUniverse)
    (is (= :ok (outcome kb (list 'not (list cat Tweety)) 'CxUniverse))
        "the cover obliges instances of the whole and nobody else")))

(tu/deftest-kb the-membership-arriving-last-is-refused-too
  (tu/with-terms [animal dog cat Rex]
    (v/assert kb (list 'covering animal dog cat) 'CxUniverse)
    (v/assert kb (list 'not (list dog Rex)) 'CxUniverse)
    (v/assert kb (list 'not (list cat Rex)) 'CxUniverse)
    (testing "the same contradiction, reached in the other order"
      (is (= :cover (outcome kb (list animal Rex) 'CxUniverse))))))

(tu/deftest-kb a-refuted-cover-names-the-evidence-it-is-against
  (tu/with-terms [animal dog cat Rex]
    (v/assert kb (list 'covering animal dog cat) 'CxUniverse)
    (let [m (v/assert kb (list animal Rex) 'CxUniverse)
          n (v/assert kb (list 'not (list dog Rex)) 'CxUniverse)
          d (try (v/assert kb (list 'not (list cat Rex)) 'CxUniverse) nil
                 (catch clojure.lang.ExceptionInfo e (ex-data e)))]
      (is (= :cover (:type d)))
      (testing "the membership and the other negation, so arbitration can weigh them"
        (is (contains? (set (:opposing-handles d)) m))
        (is (contains? (set (:opposing-handles d)) n))))))
