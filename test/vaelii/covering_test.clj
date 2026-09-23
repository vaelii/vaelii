;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.covering-test
  "covering and partition — named parts that exhaust a whole.

  The declaration half: what a cover states about the taxonomy, what a partition
  separates, and what each is refused for.  The coverage inference itself — n−1 explicit
  negations proving the nth part — is in `covering_inference_test`."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- outcome
  "`:ok`, or the `:type` of the refusal, so a case is compared as a value rather than as
  the presence or absence of a throw."
  [kb sentence context]
  (try (v/assert kb sentence context) :ok
       (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

;; ---- what a cover states -------------------------------------------------

(tu/deftest-kb a-cover-states-the-specialization-it-rests-on
  (tu/with-terms [animal dog cat Rex]
    (v/assert kb (list 'covering animal dog cat) 'CxUniverse)
    (testing "each part is a subtype of the whole, with no genl edge written by hand"
      (is (v/ask? kb (list 'genl dog animal) 'CxUniverse))
      (is (v/ask? kb (list 'genl cat animal) 'CxUniverse)))
    (testing "so a part's member is the whole's member"
      (v/assert kb (list dog Rex) 'CxUniverse)
      (is (v/ask? kb (list animal Rex) 'CxUniverse)))))

(tu/deftest-kb a-cover-asserted-before-its-parts-answers-what-one-asserted-after-them-does
  (tu/with-terms [animal dog cat Rex]
    (v/assert kb (list dog Rex) 'CxUniverse)
    (v/assert kb (list 'covering animal dog cat) 'CxUniverse)
    (is (v/ask? kb (list animal Rex) 'CxUniverse)
        "the membership stored first still reaches the whole")))

(tu/deftest-kb retracting-a-cover-drops-the-edges-it-installed
  (tu/with-terms [animal dog cat]
    (let [h (v/assert kb (list 'covering animal dog cat) 'CxUniverse)]
      (is (v/ask? kb (list 'genl dog animal) 'CxUniverse))
      (v/retract! kb h)
      (testing "the specialization goes with the declaration that stated it"
        (is (not (v/ask? kb (list 'genl dog animal) 'CxUniverse)))
        (is (not (v/ask? kb (list 'genl cat animal) 'CxUniverse)))))))

(tu/deftest-kb a-hand-written-edge-survives-the-cover-that-restated-it
  (tu/with-terms [animal dog cat]
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (let [h (v/assert kb (list 'covering animal dog cat) 'CxUniverse)]
      (v/retract! kb h)
      (testing "two supporters, and dropping one leaves the other"
        (is (v/ask? kb (list 'genl dog animal) 'CxUniverse))
        (is (not (v/ask? kb (list 'genl cat animal) 'CxUniverse)))))))

;; ---- what a partition separates, and what a bare cover does not ----------

(tu/deftest-kb a-bare-cover-leaves-its-parts-free-to-overlap
  (tu/with-terms [animal dog cat Rex]
    (v/assert kb (list 'covering animal dog cat) 'CxUniverse)
    (is (not (v/disjoint? kb dog cat)) "covering claims no separation")
    (v/assert kb (list dog Rex) 'CxUniverse)
    (is (= :ok (outcome kb (list cat Rex) 'CxUniverse))
        "so a term may hold two parts of one cover")))

(tu/deftest-kb a-partition-separates-its-parts-without-a-disjoint-sentex
  (tu/with-terms [animal dog cat Rex]
    (v/assert kb (list 'partition animal dog cat) 'CxUniverse)
    (testing "every pair of parts is disjoint"
      (is (v/disjoint? kb dog cat))
      (is (v/disjoint? kb cat dog)))
    (testing "and no (disjoint …) sentex was written to say so"
      (is (empty? (v/find-sentexes kb {:pattern (list 'disjoint dog cat)}))))
    (testing "the second membership is refused where it is written"
      (v/assert kb (list dog Rex) 'CxUniverse)
      (is (not= :ok (outcome kb (list cat Rex) 'CxUniverse))))))

(tu/deftest-kb a-partition-separates-the-subtypes-of-its-parts
  (tu/with-terms [animal dog cat poodle Rex]
    (v/assert kb (list 'partition animal dog cat) 'CxUniverse)
    (v/assert kb (list 'genl poodle dog) 'CxUniverse)
    (is (v/disjoint? kb poodle cat)
        "disjointness is inherited downward through genl, as every other arm's is")
    (is (not (v/disjoint? kb poodle dog))
        "and a part is not separated from its own subtype")))

(tu/deftest-kb dropping-a-partition-releases-every-pair-at-once
  (tu/with-terms [animal dog cat bird]
    (let [h (v/assert kb (list 'partition animal dog cat bird) 'CxUniverse)]
      (is (v/disjoint? kb dog cat))
      (is (v/disjoint? kb cat bird))
      (v/retract! kb h)
      (is (not (v/disjoint? kb dog cat)))
      (is (not (v/disjoint? kb cat bird))))))

(tu/deftest-kb an-exception-exempts-one-pair-of-parts
  (tu/with-terms [perception reading touch Braille]
    (v/assert kb (list 'partition perception reading touch) 'CxUniverse)
    (is (v/disjoint? kb reading touch))
    (v/assert kb (list 'siblingDisjointException reading touch) 'CxUniverse)
    (testing "the roster is read by the same test the metatype clique is"
      (is (not (v/disjoint? kb reading touch)))
      (v/assert kb (list reading Braille) 'CxUniverse)
      (is (= :ok (outcome kb (list touch Braille) 'CxUniverse))))))

;; ---- what the declaration is refused for --------------------------------

(tu/deftest-kb a-cover-naming-fewer-than-two-parts-states-nothing
  (tu/with-terms [animal dog]
    (is (= :not-well-formed (outcome kb (list 'covering animal dog) 'CxUniverse)))))

(tu/deftest-kb a-cover-is-refused-for-a-shape-no-edge-could-be-installed-for
  (tu/with-terms [animal dog cat plant Rex]
    (testing "a part named twice"
      (is (= :not-well-formed (outcome kb (list 'covering animal dog dog) 'CxUniverse))))
    (testing "an individual in any position"
      (is (= :not-well-formed (outcome kb (list 'covering animal dog Rex) 'CxUniverse)))
      (is (= :not-well-formed (outcome kb (list 'covering Rex dog cat) 'CxUniverse))))
    (testing "the whole named as one of its own parts"
      (is (= :not-well-formed (outcome kb (list 'covering animal animal dog) 'CxUniverse))))
    (testing "a part the closure already places above the whole"
      (v/assert kb (list 'genl animal plant) 'CxUniverse)
      (is (= :not-well-formed (outcome kb (list 'covering animal plant dog) 'CxUniverse))))))

(tu/deftest-kb a-part-a-sibling-context-places-above-the-whole-is-refused
  ;; The edge the cover installs closes the cycle whichever context holds the edge above
  ;; it, so the cover is refused where the bare `genl` is.
  (tu/with-terms [animal dog plant]
    (let [left (tu/tmp-ctx) right (tu/tmp-ctx)]
      (v/assert kb (list 'genlCx left 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx right 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genl animal plant) right)
      (is (= :not-well-formed (outcome kb (list 'genl plant animal) left))
          "the bare edge is a cycle from either sibling")
      (is (= :not-well-formed (outcome kb (list 'covering animal plant dog) left)))
      (is (not (v/genl? kb plant animal)) "and nothing closed the cycle"))))

(tu/deftest-kb a-part-disjoint-from-the-whole-is-refused
  (tu/with-terms [animal dog plant]
    (v/assert kb (list 'disjoint animal plant) 'CxUniverse)
    (is (= :not-well-formed (outcome kb (list 'covering animal plant dog) 'CxUniverse)))))

;; ---- the roster is one key, whatever order it is written in -------------

(tu/deftest-kb a-part-roster-written-in-another-order-is-one-declaration
  (tu/with-terms [animal dog cat]
    (let [tx (reasoning/taxonomy kb)]
      (v/assert kb (list 'covering animal dog cat) 'CxUniverse)
      (v/assert kb (list 'covering animal cat dog) 'CxUniverse)
      (is (= 1 (count (tax/covers-of tx animal)))
          "one roster, whichever order the parts arrived in"))))

;; ---- separating: the separation without the coverage --------------------

(tu/deftest-kb separating-separates-its-parts-and-claims-no-coverage
  (tu/with-terms [animal dog cat Rex]
    (v/assert kb (list 'separating animal dog cat) 'CxUniverse)
    (testing "every pair of parts is disjoint, as a partition's are"
      (is (v/disjoint? kb dog cat))
      (is (empty? (v/find-sentexes kb {:pattern (list 'disjoint dog cat)}))))
    (testing "and each part is a subtype of the whole, as a cover's are"
      (is (v/ask? kb (list 'genl dog animal) 'CxUniverse)))
    (testing "a whole instance belonging to no part violates nothing"
      (v/assert kb (list animal Rex) 'CxUniverse)
      (is (empty? (v/conflicts kb))))))

(tu/deftest-kb separating-licenses-no-coverage-inference
  (tu/with-terms [animal dog cat Rex]
    (v/assert kb (list 'separating animal dog cat) 'CxUniverse)
    (v/assert kb (list animal Rex) 'CxUniverse)
    (v/assert kb (list 'not (list dog Rex)) 'CxUniverse)
    (testing "ruling out one part proves nothing about the other"
      (is (not (v/ask? kb (list cat Rex) 'CxUniverse))))
    (testing "and ruling out both refutes nothing"
      (is (= :ok (outcome kb (list 'not (list cat Rex)) 'CxUniverse))))))

(deftest the-two-claims-are-what-the-three-spellings-are-made-of
  (testing "the kinds are closed, and each spelling is one of them"
    (is (= #{:covering :separating :partition} tax/cover-kinds)))
  (testing "and the two readings a cache arm takes of a kind partition them"
    (is (= #{:covering :partition} (set (filter tax/covering-kind? tax/cover-kinds))))
    (is (= #{:separating :partition} (set (filter tax/separating-kind? tax/cover-kinds))))))

(tu/deftest-kb the-three-spellings-are-three-declarations-over-one-roster
  (tu/with-terms [animal dog cat]
    (let [c (v/assert kb (list 'covering animal dog cat) 'CxUniverse)]
      (is (not (v/disjoint? kb dog cat)) "covering alone separates nothing")
      (v/assert kb (list 'separating animal dog cat) 'CxUniverse)
      (is (v/disjoint? kb dog cat) "the separating roster does")
      (v/retract! kb c)
      (is (v/disjoint? kb dog cat)
          "and dropping the coverage claim leaves the separation standing"))))

;; ---- what reads the separation a cover makes -----------------------------

(tu/deftest-kb a-cover-separated-clash-is-weighed-like-any-other
  ;; The separation a `partition` makes is the fourth spelling of disjointness, and a KB
  ;; declaring no other is the case that says whether every reader knows about it.  The
  ;; settle's gate takes four set-emptiness reads for this reason: shutting on a cover
  ;; leaves the pair stored and never weighed, while `disjoint?` goes on answering true.
  (binding [checks/*arbitrate-constraints?* true]
    (testing "two defeasible memberships are a dilemma, as they are under (disjoint A B)"
      (tu/with-kb [kb]
        (tu/with-terms [animal dog cat Rex]
          (v/assert kb (list 'partition animal dog cat) 'CxUniverse)
          (v/assert kb (list dog Rex) 'CxUniverse)
          (v/assert kb (list cat Rex) 'CxUniverse)
          (is (v/disjoint? kb dog cat))
          (is (= 1 (count (v/contradictions kb))))
          (is (v/ask? kb (list dog Rex) 'CxUniverse))
          (is (v/ask? kb (list cat Rex) 'CxUniverse)))))
    (testing "and the known-true side wins where one of them is known-true"
      (tu/with-kb [kb]
        (tu/with-terms [animal dog cat Rex]
          (v/assert kb (list 'partition animal dog cat) 'CxUniverse)
          (v/assert kb (list dog Rex) 'CxUniverse {:strength :monotonic})
          (v/assert kb (list cat Rex) 'CxUniverse)
          (is (v/ask? kb (list dog Rex) 'CxUniverse))
          (is (not (v/ask? kb (list cat Rex) 'CxUniverse))))))))

(tu/deftest-kb a-cover-separated-clash-has-a-witness-and-so-a-standing-reading
  ;; `exposed-clashes` answers about every jointly-visible pair, decided or not, and it
  ;; reads the derivation enumeration to say which contexts see one.  An enumeration with
  ;; no cover arm returns nothing for a cover-separated pair, which a caller reads as *not
  ;; disjoint* — the one answer `disjoint?` is already giving the other way.
  (tu/with-terms [animal dog cat Rex]
    (v/assert kb (list 'partition animal dog cat) 'CxUniverse)
    (is (seq (tax/disjointness-witnesses (reasoning/taxonomy kb) dog cat))
        "the pair has at least one complete derivation")
    (binding [checks/*arbitrate-constraints?* true]
      (v/assert kb (list dog Rex) 'CxUniverse)
      (v/assert kb (list cat Rex) 'CxUniverse)
      (is (= 1 (count (v/exposed-clashes kb)))))))
