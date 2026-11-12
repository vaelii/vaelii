;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.dense-routing-test
  "Which index family lands in which *representation*, in the two dense backends.

  The dense backends exist for one reason — density — and density is the one property
  their oracles cannot see.  `dense_kv_oracle_test` and `dense_roots_oracle_test` prove
  set-equality against `MemoryKvBackend`, and both backends keep a **fallback** for keys
  they don't route: a family the router fails to recognize is stored as an ordinary
  boxed set, answers every read identically, and passes every oracle while buying
  nothing.  The projection tests can't see it either, since the fallback returns the
  entries verbatim.  So a misrouted family is invisible everywhere except here.

  The keys are never spelled by hand.  A hand-spelled key tests the router against the
  test's idea of a key name, which is exactly the agreement that can drift — this
  namespace builds a real KB, reads back the keys `vaelii.impl.kv` actually wrote, and
  checks each one's stored representation against its family.  A family nobody has
  declared fails as `:unclassified`, so adding an index family forces a routing decision
  rather than silently taking the fallback."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.dense-roots :as dense-roots]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu])
  (:import (vaelii.impl.types.postings IntPostings)))

;;; ── the families ──────────────────────────────────────────────────────

(defn- family
  "The family `k` belongs to — the granularity a routing decision is made at.  Keyed on
  the shape rather than the whole key, since a family has one entry per term."
  [k]
  (if-not (vector? k)
    [:unclassified k]
    (case (nth k 0)
      :trie            [:trie (nth k 1)]
      (:argument-root :predicate-extent :rule-antecedent :rule-consequent :rule-extent
                      :opposed :tax-support :mint :mint-in :self-tuple :arity-binding :shape-tuple
                      :calendar :nat-argument)
      [(nth k 0) (nth k 1)]
      :exception-index (if (= :rules (nth k 1)) [:exception-index :rules] [:exception-index :predicate])
      (:context-root :argument-slot :unary-slot :term-index :term-names :rule-antecedent-keys
                     :opposed-in :opposed-bodies :opposed-functor :opposed-between
                     :tax-installs :mint-terms :mint-rules :unary-multi
                     :unary-kept :unary-kept-types :unary-denied :unary-denied-types
                     :shape-lengths :arity-binding-kinds :arity-bound :calendar-buckets)
      [(nth k 0)]
      [:unclassified k])))

(def ^:private handle-families
  "Families whose value is a set of **handles** — the ones a dense backend must pack into
  int postings.  Handles fit an `int`, which is what makes packing possible at all."
  #{[:trie :handles] [:argument-root :handles] [:predicate-extent :handles]
    [:context-root] [:term-index]
    [:rule-antecedent :handles] [:rule-consequent :handles] [:rule-extent :handles]
    [:opposed :handles] [:opposed-in] [:self-tuple :handles] [:arity-binding :handles]
    [:shape-tuple :handles] [:calendar :handles] [:nat-argument :handles]
    [:tax-support :handles] [:mint :handles] [:mint-in :handles]
    [:exception-index :predicate] [:exception-index :rules]})

(def ^:private count-families
  "Families whose value is a subtree count — an integer, a plain counter where a backend
  stores it.  `dense-roots` stores no argument-node count and answers it from the node's
  leaves, so on the columnar store it is read through `kv-get` and found in neither the
  packed map nor the fallback.  The other three count tries' counts, one per predicate or
  rule key, are counters in its fallback."
  #{[:trie :count] [:argument-root :count] [:predicate-extent :count]
    [:rule-antecedent :count] [:rule-consequent :count] [:rule-extent :count]
    [:opposed :count] [:tax-support :count] [:mint :count] [:mint-in :count]
    [:self-tuple :count] [:arity-binding :count] [:shape-tuple :count] [:calendar :count]
    [:nat-argument :count]})

(def ^:private other-families
  "Families whose value is deliberately *not* a handle set, so packing them as handles
  would be wrong rather than merely unrealized: the counts, the trie's child labels (path
  tokens — numbers among them, which is the case a value-type dispatch would
  misclassify), an argument node's children (contexts), the term-name set (term *names*), and
  the two slot predicate sets (*predicates* present at a slot, and those a term is the lone
  argument of — names, like the term-name set's members)."
  (into #{[:trie :children] [:argument-root :children] [:predicate-extent :children]
          [:rule-antecedent :children] [:rule-consequent :children] [:rule-extent :children]
          [:opposed :children] [:self-tuple :children] [:term-names] [:argument-slot] [:unary-slot]
          [:rule-antecedent-keys] [:opposed-bodies] [:opposed-functor] [:opposed-between]
          [:tax-support :children] [:tax-installs]
          [:mint :children] [:mint-in :children] [:mint-terms] [:mint-rules] [:unary-multi]
          [:unary-kept]
          [:unary-kept-types] [:unary-denied] [:unary-denied-types] [:shape-lengths]
          [:arity-binding :children] [:arity-binding-kinds] [:arity-bound]
          [:shape-tuple :children] [:calendar :children] [:calendar-buckets]
          [:nat-argument :children]}
        count-families))

(def ^:private fallback-families
  "The families the columnar roots keep in their fallback: the counters keyed by a
  predicate, functor, rule key or kind, and the one `:mint-in` node's children.  Every
  other family packs — a handle set as handles, a node's children and a name set as ids in
  the shared token dictionary — and a node count the roots read off the node's leaves is
  stored nowhere (`counted-families`)."
  #{[:predicate-extent :count] [:rule-antecedent :count] [:rule-consequent :count]
    [:rule-extent :count] [:self-tuple :count] [:mint-in :count] [:mint-in :children]})

(def ^:private counted-families
  "The node counts the columnar roots answer from the node's leaves: `kv-get` computes
  them, and no entry holds them."
  #{[:argument-root :count] [:opposed :count] [:mint :count] [:tax-support :count]
    [:arity-binding :count] [:shape-tuple :count] [:calendar :count] [:nat-argument :count]})

;;; ── the KB, and the backends under test ───────────────────────────────

;; Own db numbers, outside the suite's block: this namespace opens whole KBs on named
;; backends rather than running on whichever one `VAELII_TEST_BACKEND` selected.
(defn- open-kb! [backend space]
  (doto (v/open-kb {:backend backend :space space
                    :recover? false})
    (tu/clear-kb!)))

(defn- build!
  "One KB touching every index family: a ragged trie (a numeric token, a negative fact),
  the context root, the argument trie and the predicate extent, both rule indexes, both halves of the exception index, the
  term index and the term-name set, and the mint family, which an argument declaration's mint
  writes with the entailment forced on.  A family the fixture never writes cannot be checked, so the
  completeness assertion below fails when the fixture misses a family."
  [kb]
  (tu/with-terms [bird penguin animal flies feathered parentOf grandparentOf relatesTo
                  Tweety Opus Ann Bob Cid CxRouting PairFn]
    (v/assert kb (list 'genl penguin bird) CxRouting {:strength :monotonic})
    (v/assert kb (list 'genl bird animal) CxRouting {:strength :monotonic})
    (v/assert kb (list 'genl animal 'thing) CxRouting {:strength :monotonic})
    (v/assert kb (list 'arg parentOf 1 animal) CxRouting {:strength :monotonic})
    ;; a rule with an exception — the rule index and both exception-index halves
    (v/assert kb (list 'exceptWhen (list penguin '?b)
                       (list 'set/defaultRule
                             (vr/rule-sentence [(list bird '?b)] (list flies '?b))))
              CxRouting)
    (v/assert kb (vr/rule-sentence [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                                   (list grandparentOf '?x '?z))
              CxRouting {:direction :forward})
    (v/assert kb (list bird Tweety) CxRouting {:strength :monotonic})
    (v/assert kb (list feathered Tweety) CxRouting)
    (v/assert kb (list bird Opus) CxRouting)
    (v/assert kb (list penguin Opus) CxRouting)
    (tu/with-entailing
      (v/assert kb (list parentOf Ann Bob) CxRouting)
      (v/assert kb (list parentOf Bob Cid) CxRouting))
    (v/assert kb (list 'bornInYear Tweety 1970) CxRouting)   ; a numeric trie token
    (v/assert kb (list 'not (list feathered Opus)) CxRouting)
    ;; a body stored in both polarities: the opposed family, filed by functor
    (v/assert kb (list feathered Opus) CxRouting)
    ;; and one between predicates, spelled camelCase as `tu/with-terms` does not spell them
    (let [between (list relatesTo (gensym "tmpFatherOf") (gensym "tmpKinOf"))]
      (v/assert kb between CxRouting)
      (v/assert kb (list 'not between) CxRouting))
    ;; a ground binary self tuple: the self-tuple trie
    (v/assert kb (list parentOf Cid Cid) CxRouting)
    ;; a length binding: the arity-binding trie
    (v/assert kb (list 'binary_predicate grandparentOf) CxRouting {:strength :monotonic})
    (v/assert kb (list 'hatchedIn Tweety '(DayFn 1970 1 15)) CxRouting)
    (v/assert kb (list 'natFormula Cid (list PairFn Ann Bob)) CxRouting)))   ; the `:nat-argument` trie

(defn- families-present
  "The families the built index actually holds, with one representative key each."
  [kb]
  (reduce (fn [m [k _]] (assoc m (family k) k)) {} (p/index-entries (:index kb))))

;;; ── every family is classified ────────────────────────────────────────

(deftest the-fixture-writes-every-declared-family-and-no-other
  ;; The required half of this namespace: a family that exists but is declared
  ;; nowhere would otherwise be checked by nothing at all, and would take the fallback
  ;; in both dense backends without a single test noticing.
  (let [kb    (open-kb! :memory 82)
        _     (build! kb)
        found (set (keys (families-present kb)))]
    (is (empty? (filter #(= :unclassified (first %)) found))
        (str "an index family nobody has classified: "
             (pr-str (filter #(= :unclassified (first %)) found))
             " — declare it a handle family or not, and route it accordingly"))
    (is (= (set/union handle-families other-families) found)
        (str "declared families and written families disagree — "
             (pr-str {:declared-but-unwritten (set/difference (set/union handle-families other-families) found)
                      :written-but-undeclared (set/difference found (set/union handle-families other-families))})))
    (tu/clear-kb! kb)))

;;; ── :memory-dense — the value is packed ───────────────────────────────

(deftest the-dense-backend-packs-every-handle-family
  ;; `kv-get` on `TieredKvBackend` hands back the stored value as it is held, so the
  ;; representation is readable without reaching into the backend's state.
  (let [kb      (open-kb! :memory-dense 82)
        _       (build! kb)
        backend (:backend (:index kb))
        present (families-present kb)]
    (doseq [[fam k] (sort-by (comp str key) present)]
      (testing (pr-str fam)
        (let [v (p/kv-get backend k)]
          (cond
            (handle-families fam)
            (is (instance? IntPostings v)
                (str fam " is a handle family but " (pr-str k) " is stored as "
                     (some-> v class .getSimpleName)
                     " — the router does not recognize the key, so it took the fallback"))

            (count-families fam)
            (is (number? v) (str fam " should be a plain counter"))

            :else
            (is (and (set? v) (not (instance? IntPostings v)))
                (str fam " is not a handle family and must stay an ordinary set"))))))
    (is (seq (filter handle-families (keys present))) "no handle family in the fixture")
    (tu/clear-kb! kb)))

;;; ── :memory-columnar — the key is interned too ────────────────────────

(deftest the-columnar-roots-intern-every-non-trie-handle-family
  ;; `DenseRoots` splits differently: a routed key lives in the packed long map and a
  ;; fallback key in an embedded plain backend.  `kv-get` reads *only* the fallback, so
  ;; "has members but `kv-get` is nil" is exactly "this key was int-routed" — no reach
  ;; into the deftype's fields required.
  (let [kb      (open-kb! :memory-columnar 82)
        _       (build! kb)
        roots   (:roots (:index kb))
        present (families-present kb)]
    (doseq [[fam k] (sort-by (comp str key) present)
            :when   (not= :trie (first fam))]      ; the columnar trie is native; no [:trie …] key reaches the roots
      (testing (pr-str fam)
        (cond
          (counted-families fam)
          (do (is (pos? (long (p/kv-get roots k))) (str fam " answers the node's count"))
              (is (not-any? #(= k (first %)) (dense-roots/fallback-entries roots))
                  (str fam " is read off the leaves, so the fallback holds no entry for it")))

          (count-families fam)
          (is (pos? (long (p/kv-get roots k))) (str fam " answers the node's count"))

          (fallback-families fam)
          (do (is (seq (p/kv-members roots k)) (str fam " is missing from the roots backend"))
              (is (some? (p/kv-get roots k)) (str fam " stays in the fallback")))

          :else
          (do (is (seq (p/kv-members roots k)) (str fam " is missing from the roots backend"))
              (is (nil? (p/kv-get roots k))
                  (str fam " is a packed family but " (pr-str k) " is readable through `kv-get`"
                       " — it sits in the fallback backend, un-interned and boxed"))))))
    ;; and the trie families really are elsewhere — the roots hold no path keys at all
    (doseq [[fam k] present :when (= :trie (first fam))]
      (is (empty? (p/kv-members roots k))
          (str fam " reached the roots backend; the columnar trie is supposed to own it")))
    (tu/clear-kb! kb)))

;;; ── the fallback is vocabulary-scaled ─────────────────────────────────

(defn- fallback-size
  "How many entries the columnar roots' fallback holds after `n` individuals, each a member
  of two types, related to the next, and each the type of one `genl` edge, over a
  vocabulary that does not grow with `n`."
  [n]
  (let [kb (open-kb! :memory-columnar 83)]
    (tu/with-terms [bird pet likes CxScale]
      (dotimes [i n]
        (let [x (symbol (str "Scale" i)) y (symbol (str "Scale" (inc i)))
              t (symbol (str "scale" i))]
          (v/assert kb (list bird x) CxScale)
          (v/assert kb (list pet x) CxScale)
          (v/assert kb (list likes x y) CxScale)
          (v/assert kb (list 'genl t bird) CxScale {:strength :monotonic})))
      (let [size (count (dense-roots/fallback-entries (:roots (:index kb))))]
        (tu/clear-kb! kb)
        size))))

(deftest the-columnar-roots-fallback-holds-no-entry-per-fact
  ;; The terms, their slots, their memberships and the taxonomy's supporters all grow with
  ;; the facts, and each packs; what stays behind is keyed by the vocabulary, which is the
  ;; same at both sizes.
  (is (= (fallback-size 8) (fallback-size 32))))
