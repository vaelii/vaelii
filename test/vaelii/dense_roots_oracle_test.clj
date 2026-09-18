;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.dense-roots-oracle-test
  "Differential oracle for the key-interning roots backend (`vaelii.impl.dense-roots`):
  the same random op sequence hits `MemoryKvBackend` and `DenseRoots`, and every read must
  agree.

  What is exercised, in the **key shapes `vaelii.impl.kv` actually writes**:

    * the int-routed families — `:context-root`, `:functor-root`, `:term-index`,
      `:rule-index` (both arms), `:exception-index` — with symbol *and* ground-compound
      terms, plus the `:exception-index :rules` roster, which is the one key packed
      whole rather than through the dictionary;
    * the **argument roots**, `[:argument-root pred pos term]` — four parts, the
      predicate included (index layout 2, `kv/arg-key`).  They are the interesting case
      because they are the one key with two names in it against a packed long with one
      term field: the `(pred, pos)` scope is interned to a dense id of its own and rides
      the `pos` field (`dense-roots`' `argfam-id`), so a read has two dictionaries to
      miss in rather than one.  This is the oracle that says the packed path answers
      what the memory backend answers.  `dense_routing_test` is what pins the routing
      decision itself, which no behavioural test can see;
    * the `[:argument-slot pos term]` roster beside them, whose members are
      **predicates rather than handles** and which stays in the fallback;
    * multi-family `kv-intersect`, and the fallback for unrecognized keys (counters /
      scalars — where the contract-test keyspace lives)."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.dense-roots :as dr]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.tokens :as tok]
            [vaelii.impl.types.dense-roots :as dense-roots-types]))

(defn- pick [^java.util.Random rng v] (nth v (.nextInt rng (count v))))

;; a keyspace spanning every routed family plus fallback keys (counters / plain sets)
(def ^:private index-keys
  (vec (concat (for [c '[C0 C1]]            [:context-root c])
               (for [p '[p0 p1 p2]]         [:functor-root p])
               ;; four parts, the predicate first — `kv/arg-key`'s own shape.  Written
               ;; as three (`[:argument-root pos term]`) this whole family would still
               ;; agree, because both sides answer such a key from the generic map;
               ;; what it would stop testing is the family the index writes.
               (for [p '[p0 p1] pos [1 2] t '[A0 A1 (fatherOf A0)]]
                 [:argument-root p pos t])
               (for [t '[A0 A1 dog (fatherOf A0)]]         [:term-index t])
               (for [p '[p0 p1]]            [:rule-index :antecedent p])
               (for [p '[p0 p2]]            [:rule-index :consequent p])
               (for [p '[flies penguin]]    [:exception-index p])
               [[:exception-index :rules]])))
(def ^:private fallback-keys (vec (for [n [:n0 :n1]] [:ctr n])))   ; not a routed family

(deftest dense-roots-set-equal
  (let [rng (java.util.Random. 7)
        m   (mem/->MemoryKvBackend (atom {}))
        d   (dr/dense-roots (tok/token-dict))]
    (dotimes [_ 9000]
      (let [r (.nextInt rng 100)]
        (cond
          (< r 55) (let [k (pick rng index-keys) h (.nextInt rng 400)]
                     (p/kv-add-to-set m k h) (p/kv-add-to-set d k h))
          (< r 75) (let [k (pick rng index-keys) h (.nextInt rng 400)]
                     (p/kv-remove-from-set m k h) (p/kv-remove-from-set d k h))
          (< r 85) (let [k (pick rng fallback-keys)]           ; fallback counter
                     (is (= (p/kv-increment m k) (p/kv-increment d k)) "incr reply"))
          (< r 92) (let [k (pick rng fallback-keys)]
                     (is (= (p/kv-decrement m k) (p/kv-decrement d k)) "decr reply"))
          :else    (let [ks (vec (take (inc (.nextInt rng 3)) (shuffle index-keys)))]
                     (is (= (p/kv-intersect m ks) (p/kv-intersect d ks)) (str "sinter " ks))))))
    ;; members + cardinality agree for every key
    (doseq [k index-keys]
      (is (= (p/kv-members m k) (p/kv-members d k)) (str "smembers " k))
      (is (= (p/kv-count    m k) (p/kv-count    d k)) (str "scard "    k)))
    (doseq [k fallback-keys]
      (is (= (p/kv-get m k) (p/kv-get d k)) (str "counter " k)))
    ;; a read of a never-interned term is empty, not an error, and doesn't grow the dict
    (is (= #{} (p/kv-members d [:term-index 'NeverSeen])))
    (is (= 0   (p/kv-count    d [:term-index 'NeverSeen])))
    ;; the argument roots are keyed by predicate, so two predicates at one (pos, term)
    ;; are two postings — a key that dropped the predicate would merge them, and the
    ;; merged answer is what both sides would then agree on
    (testing "an argument root is per predicate, not per (position, term)"
      (doseq [b [m d]]
        (p/kv-add-to-set b [:argument-root 'q0 1 'B0] 11)
        (p/kv-add-to-set b [:argument-root 'q1 1 'B0] 22))
      (is (= #{11} (p/kv-members d [:argument-root 'q0 1 'B0])))
      (is (= (p/kv-members m [:argument-root 'q0 1 'B0])
             (p/kv-members d [:argument-root 'q0 1 'B0])))
      (is (= (p/kv-members m [:argument-root 'q1 1 'B0])
             (p/kv-members d [:argument-root 'q1 1 'B0]))))
    ;; the slot roster beside them: same generic path, but its members are predicate
    ;; *names* rather than handles, so a backend that assumed int postings everywhere
    ;; would fail here and nowhere else
    (testing "the argument-slot roster holds predicates, not handles"
      (doseq [b [m d]]
        (p/kv-add-to-set b [:argument-slot 1 'B0] 'q0)
        (p/kv-add-to-set b [:argument-slot 1 'B0] 'q1)
        (p/kv-add-to-set b [:argument-slot 2 '(fatherOf A0)] 'q0)
        (p/kv-remove-from-set b [:argument-slot 1 'B0] 'q1))
      (doseq [k '[[:argument-slot 1 B0] [:argument-slot 2 (fatherOf A0)]]]
        (is (= (p/kv-members m k) (p/kv-members d k)) (str "smembers " k))
        (is (= (p/kv-count   m k) (p/kv-count   d k)) (str "scard "    k)))
      (is (= #{'q0} (p/kv-members d [:argument-slot 1 'B0]))))))

(deftest route-and-unpack-are-inverses-over-every-family
  ;; `route` and `unpack` are each other's inverse over every family the index writes, and
  ;; the oracle cannot see it: a key that decoded to the wrong shape would still answer
  ;; set-equal, since both sides went through the same router.  So the pair is checked
  ;; directly, on one key per family, argument roots included — theirs is the key with two
  ;; names in it, and the scope dictionary is the half that has to survive the round trip.
  (let [dict   (tok/token-dict)
        argfam (tok/token-dict)
        keys   ['[:context-root C0]
                '[:functor-root p0]
                '[:argument-root p0 2 A0]
                '[:argument-root p0 3 A0]      ; same predicate, another position
                '[:argument-root q1 2 A0]      ; same position, another predicate
                '[:argument-root p0 2 (fatherOf A0)]   ; a compound term
                '[:term-index A0]
                '[:rule-index :antecedent p0]
                '[:rule-index :consequent p0]
                '[:exception-index p0]
                [:exception-index :rules]]]
    (doseq [k keys]
      (let [pk (#'dense-roots-types/route dict argfam k true)]
        (is (instance? Long pk) (str k " routes to a packed long"))
        (is (= k (#'dense-roots-types/unpack dict argfam pk)) (str "round trip " k))))
    (testing "distinct keys take distinct packed longs"
      (is (= (count keys)
             (count (into #{} (map #(#'dense-roots-types/route dict argfam % true)) keys)))))
    (testing "a read of a pair nothing has scoped finds no posting to look for"
      (is (= :absent (#'dense-roots-types/route dict argfam '[:argument-root neverSeen 2 A0] false))))
    (testing "a read of a scoped pair at an uninterned term is absent for the term"
      (is (= :absent (#'dense-roots-types/route dict argfam '[:argument-root p0 2 NeverSeen] false))))))

(deftest the-argument-scope-dictionary-refuses-to-overflow
  ;; The pair rides 24 bits, and the bound is (distinct predicates × their arities) rather
  ;; than the fact count — so it holds on any KB anyone has measured.  It is asserted
  ;; anyway: a ceiling that throws is a fact, one that wraps is two families sharing a key
  ;; and answering each other's postings.
  (with-redefs-fn {#'dense-roots-types/argfam-ceiling 3}
    (fn []
      (let [dict   (tok/token-dict)
            argfam (tok/token-dict)]
        (doseq [pos [1 2 3]]
          (is (instance? Long (#'dense-roots-types/route dict argfam [:argument-root 'p0 pos 'A0] true))))
        (let [e (is (thrown? clojure.lang.ExceptionInfo
                             (#'dense-roots-types/route dict argfam '[:argument-root p0 4 A0] true)))
              d (ex-data e)]
          (is (= :argument-family-ceiling (:type d)))
          (is (= 3 (:ceiling d)))
          (is (= 4 (:pairs d)))
          (is (= 'p0 (:pred d)) "naming the pair it could not scope")
          (is (= 4 (:position d)))
          (is (= {:index :memory} (:remedy d)) "and what to take instead"))))))

(deftest a-refused-scope-is-never-minted
  ;; The refusal has to land *before* the pair is interned, and this is the test that says
  ;; so.  Minting the id and throwing afterwards leaves it in the dictionary, and the read
  ;; path never reaches the ceiling — `argfam-id` consults it only when it allocates — so
  ;; a caller that swallows the throw gets a routed read over a scope id past 24 bits,
  ;; which `packed` puts in a 24-bit field.  `argfam-table` would write the entry into an
  ;; image too, and `load-argfam!` counts it back in agreement.
  (with-redefs-fn {#'dense-roots-types/argfam-ceiling 3}
    (fn []
      (let [dict   (tok/token-dict)
            argfam (tok/token-dict)]
        (doseq [pos [1 2 3]] (#'dense-roots-types/route dict argfam [:argument-root 'p0 pos 'A0] true))
        (is (thrown? clojure.lang.ExceptionInfo
                     (#'dense-roots-types/route dict argfam '[:argument-root p0 4 A0] true)))
        (testing "the dictionary holds the scopes it granted and no more"
          ;; `argfam-table`'s length is this count, so a clean dictionary is a clean table
          (is (= 3 (tok/token-count argfam)))
          (is (neg? (tok/token-id argfam '[p0 4])) "the refused pair has no id"))
        (testing "so a later read of the refused pair finds no posting to look for"
          ;; the assertion the swallowed throw turns on: `:absent`, not a packed long
          (is (= :absent (#'dense-roots-types/route dict argfam '[:argument-root p0 4 A0] false))))
        (testing "and a scope already granted still answers while the dictionary is full"
          (is (instance? Long (#'dense-roots-types/route dict argfam '[:argument-root p0 2 A0] true))))))))

(deftest no-packed-field-carries-into-the-next
  ;; `unpack` is the exact inverse of `route` only while every field stays inside its own
  ;; width, so `packed` masks rather than trusting its callers.  A scope id one past the
  ;; 24 bits would otherwise set bit 56, and the argument key would decode as
  ;; `[:term-index …]` — a routed read answering another family's posting with nothing to
  ;; signal it.  Asserted on `packed` directly, because reaching it through `route` means
  ;; minting 16.7M pairs and the ceiling above refuses at the first one.
  (let [family #(bit-shift-right % 56)
        pos    #(bit-and (bit-shift-right % 32) 0xffffff)]
    (testing "a scope past its field cannot reach the family tag"
      (is (= 2 (family (#'dense-roots-types/packed 2 (bit-shift-left 1 24) 0)))))
    (testing "a term id past its field cannot reach the scope"
      (is (= 2 (family (#'dense-roots-types/packed 2 0 (bit-shift-left 1 32)))))
      (is (zero? (pos (#'dense-roots-types/packed 2 0 (bit-shift-left 1 32))))))
    (testing "and the fields the engine does pass are untouched"
      (let [pk (#'dense-roots-types/packed 2 7 9)]
        (is (= 2 (family pk)))
        (is (= 7 (pos pk)))
        (is (= 9 (bit-and pk 0xffffffff)))))))

(deftest dense-roots-batch-and-clear
  (let [m (mem/->MemoryKvBackend (atom {}))
        d (dr/dense-roots (tok/token-dict))
        ops [[:add-to-set [:functor-root 'p0] 1] [:add-to-set [:functor-root 'p0] 2]
             [:add-to-set [:argument-root 'p0 2 'A0] 9]
             [:add-to-set [:argument-slot 2 'A0] 'p0]
             [:add-to-set [:term-index '(fatherOf A0)] 5] [:add-to-set [:exception-index :rules] 7]
             [:increment [:ctr :n]] [:remove-from-set [:functor-root 'p0] 1] [:decrement [:ctr :n]]]]
    (is (= (p/kv-batch m ops) (p/kv-batch d ops)) "batch replies aligned")
    (doseq [k '[[:functor-root p0] [:argument-root p0 2 A0] [:argument-slot 2 A0]
                [:term-index (fatherOf A0)] [:exception-index :rules]]]
      (is (= (p/kv-members m k) (p/kv-members d k)) (str "post-batch " k)))
    (is (= (p/kv-get m [:ctr :n]) (p/kv-get d [:ctr :n])) "fallback counter after batch")
    (p/kv-clear! m) (p/kv-clear! d)
    (doseq [k '[[:functor-root p0] [:exception-index :rules] [:ctr :n]]]
      (is (= (p/kv-members m k) (p/kv-members d k)) (str "cleared " k)))))
