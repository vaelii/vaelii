;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.tokens-test
  "The in-memory token dictionary (`vaelii.impl.tokens`) the columnar index labels its
  edges with.  It is exercised heavily but only *indirectly* — through
  `columnar_index_oracle_test`, which would catch a wrong id as a wrong lookup answer
  without saying that the dictionary was why.  These pin its contract directly.

  The contract that matters is what a trie path token can be.  `sentex/path` yields
  symbols, numbers, the `:false` / `:rule` keywords, `nil` for a rule's empty slots,
  `[::subterm k]` arity markers, and whole literal lists — so the dictionary must intern
  every one of those **as-is**, since re-canonicalizing a marker vector into a list would
  break `sentex/subterm-mark?` and silently mis-key the trie."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.tokens :as tok]))

(deftest interning-is-content-keyed-and-first-writer-wins
  (let [d (tok/token-dict)]
    (let [a (tok/intern-token! d 'dog)
          b (tok/intern-token! d 'dog)
          c (tok/intern-token! d 'cat)]
      (is (= a b) "the same token interns to the same id, forever")
      (is (not= a c) "different tokens get different ids")
      (is (= 0 a) "ids count up from 0 — they index arrays")
      (is (= 1 c))
      (is (= 2 (tok/token-count d))))
    (testing "equal-but-not-identical tokens are the same token"
      (is (= (tok/intern-token! d 'dog)
             (tok/intern-token! d (symbol "dog")))))
    (testing "the inverse decodes what was interned"
      (is (= 'dog (tok/id-token d 0)))
      (is (= 'cat (tok/id-token d 1))))))

(deftest every-shape-a-path-level-can-be-round-trips
  ;; each of these is a real `sentex/path` level; nil in particular is a legal *token*
  ;; (a rule's empty assumption/constraint slot), not an absent one
  (let [d      (tok/token-dict)
        tokens ['parentOf 'Muffet 'dog 'WellContext '?0
                1970 -3 3.5 :false :rule nil
                (sx/subterm-mark 2) '(dog ?0) '[(dog ?0) (cat ?1)] "a string"]]
    (doseq [t tokens]
      (testing (pr-str t)
        (let [id (tok/intern-token! d t)]
          (is (= t (tok/id-token d id)) "decodes to an equal token")
          (is (= id (tok/intern-token! d t)) "and re-interning is idempotent"))))
    (is (= (count tokens) (tok/token-count d))
        "every one of them is a distinct token — none collapsed into another")))

(deftest a-marker-vector-is-not-canonicalized-into-a-list
  ;; the specific hazard: `sentex/canon` turns any sequential into a PersistentList, and
  ;; a dictionary that applied it would return a marker as a list, which
  ;; `subterm-mark?` does not recognize
  (let [d      (tok/token-dict)
        marker (sx/subterm-mark 2)
        back   (tok/id-token d (tok/intern-token! d marker))]
    (is (vector? back) "a marker comes back a VECTOR")
    (is (sx/subterm-mark? back) "and is still recognized as a subterm mark")))

(deftest a-token-id-is-not-a-lookup-of-an-absent-one
  (let [d (tok/token-dict)]
    (tok/intern-token! d 'dog)
    (is (= -1 (tok/token-id d 'cat)) "an absent token reports -1 rather than allocating")
    (is (= 1 (tok/token-count d)) "and the probe left the dictionary alone")
    (is (= 0 (tok/token-id d 'dog)) "a present one reports its id")))

(deftest clearing-empties-the-dictionary
  (let [d (tok/token-dict)]
    (tok/intern-token! d 'dog)
    (tok/intern-token! d 'cat)
    (tok/clear-tokens! d)
    (is (zero? (tok/token-count d)))
    (is (= -1 (tok/token-id d 'dog)))
    (is (= 0 (tok/intern-token! d 'mouse)) "ids restart from 0 over an empty dictionary")))
