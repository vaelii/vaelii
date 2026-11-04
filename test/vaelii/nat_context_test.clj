;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.nat-context-test
  "An object reified NAT, a `nat/` constant, is not a context — docs/context-nat.md, The
  `cx/` namespace carries the context role.  `wff/genlCx-problems` refuses it as a
  `genlCx` argument (`:not-well-formed`), and the naming check refuses it as a context
  slot (`:naming`).  With `:naming :off` the store holds a sentex in it, and `genlCx`
  still refuses to wire it.  A context-slot application reifies to a `cx/` constant
  instead (`context_nat_test`)."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(def ^:private refusal
  (fn [f] (tu/refusal-type f ::stored)))

(defn- mint
  "Assert an ordinary fact carrying the ground NAT `E`, and return the reified constant
  `k` it minted — the atomic term now standing in `E`'s argument slot."
  [kb E]
  (let [Red (tu/fresh-term :individual 'Red)
        h   (v/assert kb (list 'color E Red) 'CxUniverse)]
    (second (:sentence (v/sentex kb h)))))

;; ---- classification: a reified NAT is not a context ----------------------

(tu/deftest-kb a-reified-nat-classifies-as-a-term-not-a-context
  ;; a minted constant's name opens with the lowercase scheme letter, so `term-role`
  ;; classifies it as a predicate-shaped term, never as a context
  (tu/with-terms [MtFn Story1]
    (v/assert kb (list 'reifiable_function MtFn) 'CxUniverse)
    (let [k (mint kb (list MtFn Story1))]
      (is (nat-read/reified-nat-symbol? k))
      (is (not= :context (v/term-role k)))
      (is (not (contains? (set (v/contexts kb)) k))
          "a minted constant is no node of the context hierarchy"))))

;; ---- check 1: genlCx refuses a reified NAT as a context edge --------------

(tu/deftest-kb genlCx-refuses-a-reified-nat-node
  ;; the compound is reified to its constant before wff reads it
  (tu/with-terms [MtFn Story1]
    (v/assert kb (list 'reifiable_function MtFn) 'CxUniverse)
    (let [k (mint kb (list MtFn Story1))]
      (testing "the NAT compound spelling — reified first, then refused"
        (is (= :not-well-formed
               (refusal #(v/assert kb (list 'genlCx (list MtFn Story1) 'CxUniverse) 'CxUniverse)))))
      (testing "the pre-minted constant spelling"
        (is (= :not-well-formed
               (refusal #(v/assert kb (list 'genlCx k 'CxUniverse) 'CxUniverse)))))
      (testing "and as the super, either way round"
        (is (= :not-well-formed
               (refusal #(v/assert kb (list 'genlCx 'CxUniverse k) 'CxUniverse))))))))

;; ---- check 2: a reified NAT cannot name the context a sentex is in --------

(tu/deftest-kb a-reified-nat-cannot-name-a-context-slot
  (tu/with-terms [MtFn Story1 likes Tom Ann]
    (v/assert kb (list 'reifiable_function MtFn) 'CxUniverse)
    (let [k (mint kb (list MtFn Story1))]
      (testing "a NAT compound in the context slot reifies to a cx/ constant, never to the
                nat/ constant the argument position minted"
        (let [c (:context (v/sentex kb (v/assert kb (list likes Tom Ann) (list MtFn Story1))))]
          (is (nat-read/reified-context-symbol? c))
          (is (not= k c))))
      (testing "the minted constant as the context slot is refused by naming (strict)"
        (is (= :naming
               (refusal #(v/assert kb (list likes Tom Ann) k)))))
      (testing "(ist Ctx S) reifies its context argument, so directing a fact into a NAT
                context is the same refusal"
        (is (= :naming
               (refusal #(v/assert kb (list 'ist (list MtFn Story1)
                                            (list likes Tom Ann))))))))))

;; ---- where the refusal lives: a policy, not a store limit -----------------

(tu/deftest-kb naming-off-stores-into-a-nat-symbol-but-it-is-no-node
  ;; the refusal is the naming check's, and the `genlCx` refusal is wff's, which
  ;; `:naming :off` does not reach
  (tu/with-terms [MtFn Story1 likes Tom Ann]
    (v/assert kb (list 'reifiable_function MtFn) 'CxUniverse)
    (let [k      (mint kb (list MtFn Story1))
          kb-off (assoc kb :naming :off)]
      (is (= ::stored (refusal #(v/assert kb-off (list likes Tom Ann) k)))
          "with naming off the store accepts the symbol as a context")
      (testing "and the fact reads back from that symbol"
        (is (= [{'?x Ann}] (v/ask kb-off (list likes Tom '?x) k))))
      (testing "but the symbol is no node of the hierarchy, and sees CxUniverse alone"
        (is (not (contains? (set (v/contexts kb)) k)))
        (is (v/sees? kb k 'CxUniverse) "the implicit edge, which a stored edge does not name")
        (is (= #{k 'CxUniverse} (set (v/context-up kb k))))))))
