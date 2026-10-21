;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.quasiquote-test
  "Quasiquotation — the metalinguistic constructor (docs/nat.md, the plan).

  `(Quasiquote T)` builds the syntactic term `T` with each `(Unquote v)` hole filled and
  names the result as syntax — a `Quote` mention reified to a constant.  A ground template
  reduces on the write path; an open one reduces at rule-firing time once the antecedent
  binds its holes, deterministically (content-addressed dedup) so a re-derivation converges."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.quasiquote :as quasiquote]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(defn- qq [& xs] (apply list 'Quasiquote xs))
(defn- unq [x] (list 'Unquote x))

(tu/deftest-kb a-ground-quasiquote-reduces-to-a-reified-mention
  (tu/with-terms [Tom Fido Dog isa believes]
    (quasiquote/ensure-quasiquote-functions kb)
    (let [h (v/assert kb (list believes Tom (qq (list isa Fido Dog))) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (testing "the quasiquote is constructed and reified to a mention constant"
        (is (nat/reified-nat-symbol? k) "arg 2 is now an opaque constant, not a compound")
        (is (= (list 'Quote (list isa Fido Dog)) (nat/nat-expression kb k))
            "which mentions the constructed sentence"))
      (testing "a query naming the same construction resolves to it"
        (is (v/ask? kb (list believes Tom (qq (list isa Fido Dog))) 'CxUniverse))))))

(tu/deftest-kb a-rule-constructs-a-mention-from-its-antecedent-binding
  (tu/with-terms [Tom Fido Rex Dog dog isa believes]
    (quasiquote/ensure-quasiquote-functions kb)
    (v/assert-rule kb [(list dog '?x)]
                   (list believes Tom (qq (list isa (unq '?x) Dog)))
                   'CxUniverse {:direction :forward})
    (v/assert kb (list dog Fido) 'CxUniverse)
    (testing "the rule fired and constructed (isa Fido Dog) as a mention"
      (is (some? (nat/dedup-constant kb (list 'Quote (list isa Fido Dog)))))
      (is (v/ask? kb (list believes Tom (qq (list isa Fido Dog))) 'CxUniverse)))
    (testing "a second binding constructs a distinct mention"
      (v/assert kb (list dog Rex) 'CxUniverse)
      (is (not= (nat/dedup-constant kb (list 'Quote (list isa Fido Dog)))
                (nat/dedup-constant kb (list 'Quote (list isa Rex Dog))))))))

(tu/deftest-kb the-same-binding-converges-to-one-constant
  ;; Determinism is content-addressed: E is its own key, so two firings on the same binding
  ;; reify to the one constant — no digest/frontier needed, unlike a skolem witness.
  (tu/with-terms [Tom Fido Dog dog friend isa believes]
    (quasiquote/ensure-quasiquote-functions kb)
    ;; two rules whose heads construct the identical mention from the same binding
    (v/assert-rule kb [(list dog '?x)]
                   (list believes Tom (qq (list isa (unq '?x) Dog))) 'CxUniverse {:direction :forward})
    (v/assert-rule kb [(list friend '?x)]
                   (list believes Tom (qq (list isa (unq '?x) Dog))) 'CxUniverse {:direction :forward})
    (v/assert kb (list dog Fido) 'CxUniverse)
    (v/assert kb (list friend Fido) 'CxUniverse)
    (is (= 1 (count (v/sentexes-matching kb (list 'natFormula '?k (list 'Quote (list isa Fido Dog)))
                                         'CxUniverse)))
        "one expression, one constant, however many firings construct it")))

(tu/deftest-kb an-unenabled-kb-pays-nothing-and-leaves-the-quasiquote-alone
  ;; The gate: without `ensure-quasiquote-functions`, `any-quasiquote?` is false, the reducer
  ;; is a no-op, and `(Quasiquote …)` is an ordinary stored compound (nothing reifies it).
  (tu/with-terms [Tom Fido Dog isa believes]
    (is (false? (quasiquote/any-quasiquote? kb)))
    (let [h (v/assert kb (list believes Tom (qq (list isa Fido Dog))) 'CxUniverse)]
      (is (= (list believes Tom (qq (list isa Fido Dog))) (:sentence (v/sentex kb h)))
          "stored verbatim, un-reduced"))))

(tu/deftest-kb a-nested-quasiquote-is-left-literal-and-round-trips
  ;; a Quasiquote nested inside a construction is its own mention level — left whole, not
  ;; reduced.  The write path re-asserts (natFormula K E) through full assert, so without
  ;; holding the mention payload opaque the nested construction would be reduced a second
  ;; time and the exact form asserted would be unretrievable.
  (tu/with-terms [Tom foo bar Fido believes]
    (quasiquote/ensure-quasiquote-functions kb)
    (let [construction (list believes Tom (qq (list foo (qq (list bar Fido)))))
          h (v/assert kb construction 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (testing "the inner Quasiquote stays literal in the constructed mention"
        (is (= (list 'Quote (list foo (qq (list bar Fido)))) (nat/nat-expression kb k))))
      (testing "and the exact construction is retrievable"
        (is (v/ask? kb construction 'CxUniverse))))))
