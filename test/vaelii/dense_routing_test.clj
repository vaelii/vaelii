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
      :rule-index      [:rule-index (nth k 1)]
      :exception-index (if (= :rules (nth k 1)) [:exception-index :rules] [:exception-index :predicate])
      (:context-root :functor-root :argument-root :argument-slot :term-index :term-roster)
      [(nth k 0)]
      [:unclassified k])))

(def ^:private handle-families
  "Families whose value is a set of **handles** — the ones a dense backend must pack into
  int postings.  Handles fit an `int`, which is what makes packing possible at all."
  #{[:trie :handles]
    [:context-root] [:functor-root] [:argument-root] [:term-index]
    [:rule-index :antecedent] [:rule-index :consequent]
    [:exception-index :predicate] [:exception-index :rules]})

(def ^:private other-families
  "Families whose value is deliberately *not* a handle set, so packing them would be
  wrong rather than merely unrealized: a subtree count (an integer), the trie's child
  labels (path tokens — numbers among them, which is the case a value-type dispatch
  would misclassify), the roster (term *names*), and the argument-slot roster
  (*predicates* present at a slot — names, like the term roster's members)."
  #{[:trie :count] [:trie :children] [:term-roster] [:argument-slot]})

(def ^:private unpackable-handle-families
  "Handle families the dense layout cannot int-route, and why.

  Empty, and that is a claim worth checking rather than a blank: **every** handle family
  packs. The one that carries two names — `[:argument-root pred pos term]`, index layout
  2 in `kv.clj` — packs because its `(pred, pos)` scope is interned to a dense id of its
  own and rides the `pos` field (`dense-roots`' `argfam-id`), so the packed long spends
  family 8 bits | scope 24 | term id 32 and no family is left keyed by a boxed vector.

  A family added here must state which of the two it lacks: a term the shared dictionary
  can intern, or a field in the packed long to put it in."
  #{})

;;; ── the KB, and the backends under test ───────────────────────────────

;; Own db numbers, outside the suite's block: this namespace opens whole KBs on named
;; backends rather than running on whichever one the suite's gate selected.
(defn- open-kb! [backend space]
  (doto (v/open-kb {:backend backend :space space
                    :recover? false})
    (tu/clear-kb!)))

(defn- build!
  "One KB touching every index family: a ragged trie (a numeric token, a negative fact),
  all three roots, both halves of the rule index, both halves of the exception index, the
  term index and the roster.  A family the fixture never writes cannot be checked, so the
  completeness assertion below is what keeps this honest."
  [kb]
  (tu/with-terms [bird penguin animal flies feathered parentOf grandparentOf
                  Tweety Opus Ann Bob Cid CxRouting]
    (v/assert kb (list 'genl penguin bird) CxRouting {:strength :monotonic})
    (v/assert kb (list 'genl bird animal) CxRouting {:strength :monotonic})
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
    (v/assert kb (list parentOf Ann Bob) CxRouting)
    (v/assert kb (list parentOf Bob Cid) CxRouting)
    (v/assert kb (list 'bornInYear Tweety 1970) CxRouting)   ; a numeric trie token
    (v/assert kb (list 'not (list feathered Opus)) CxRouting)))

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

            (= [:trie :count] fam)
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
        (is (seq (p/kv-members roots k)) (str fam " is missing from the roots backend"))
        (if (and (handle-families fam) (not (unpackable-handle-families fam)))
          (is (nil? (p/kv-get roots k))
              (str fam " is a handle family but " (pr-str k) " is readable through `kv-get`"
                   " — it sits in the fallback backend, un-interned and boxed"))
          (is (some? (p/kv-get roots k))
              (str fam " must stay in the fallback — it is either not a handle family"
                   " or one the packed layout cannot carry (see"
                   " `unpackable-handle-families`)")))))
    ;; and the trie families really are elsewhere — the roots hold no path keys at all
    (doseq [[fam k] present :when (= :trie (first fam))]
      (is (empty? (p/kv-members roots k))
          (str fam " reached the roots backend; the columnar trie is supposed to own it")))
    (tu/clear-kb! kb)))
