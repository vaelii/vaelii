;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.overlay-test
  "The `:overlay` backend — a private writable fork over a shared read-only base.

  Two claims carry the whole thing, and everything below is one of them:

  * **The base is never written.**  A fork asserts, derives, retracts and clears, and the
    base's records, premises and index come back byte-identical.  That is what lets any
    number of forks in one JVM share one frozen base with no protocol between them.
  * **The merged view is the KB.**  A fork over an *empty* base behaves exactly like a
    plain backend (the `KvBackend` contract, and the suite-parity gate — see
    `scripts/test-backends.sh`), and over a populated one the engine reasons across the
    protocol without knowing it is there: an inherited fact matches, an inherited rule fires
    over a fork-local fact, and retracting an inherited premise in the fork sweeps what
    it derived — in the fork only."
  (:require [clojure.test :refer [deftest is testing]]
            [taoensso.trove :as trove]
            [vaelii.core :as v]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.disk.backend :as disk]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.overlay.frozen :as frozen]
            [vaelii.impl.overlay.kv :as okv]
            [vaelii.impl.overlay.mount :as mount]
            [vaelii.impl.protocols :as p]
            [vaelii.kv-backend-test :as kvt]
            [vaelii.test-util :as tu])
  (:import [java.io File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

;; Own space numbers, outside the suite's block, so a fork never shares a store with
;; another test — and one per role, since a fork is two KBs' worth of stores.
(defn- base-opts  [n] {:backend :memory :space [::base n]})
(defn- fork-opts  [n] {:backend :memory :space [::fork n]})

(defn- tmpdir ^String []
  (str (Files/createTempDirectory "vaelii-overlay-" (into-array FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (java.io.File. dir)))] (.delete ^java.io.File f)))

;; ---- what a base looks like, so a change to it is visible -----------------

(defn- base-snapshot
  "Everything a base holds, in a form that compares by value: its records, its premise
  marks and its whole index.  Handles are included deliberately — the point is that the
  base is *unchanged*, not merely equivalent."
  [kb]
  {:sentexes       (into {} (map (juxt identity #(p/get-sentex (:records kb) %)))
                         (p/sentex-ids (:records kb)))
   :justifications (into {} (map (juxt identity #(p/get-justification (:records kb) %)))
                         (p/justification-ids (:records kb)))
   :premises       (set (p/premise-ids (:records kb)))
   :index          (set (p/kv-entries (:backend (:index kb))))})

(defn- populate!
  "A small base: a taxonomy edge, a forward rule, and two facts — so a fork inherits
  something to match, something to subsume through, and something to fire."
  [kb]
  (v/assert kb '(genl dog animal) 'CxOverlay {:strength :monotonic})
  (v/assert-rule kb '[(dog ?x)] '(mammal ?x) 'CxOverlay {:direction :forward})
  (v/assert kb '(dog Muffet) 'CxOverlay {:strength :monotonic})
  (v/assert kb '(ownerOf Ann Muffet) 'CxOverlay {:strength :monotonic})
  kb)

(defn- fresh-base
  "A populated base KB on its own space, cleared first."
  [n]
  (populate! (doto (v/open-kb (assoc (base-opts n) :recover? false)) (v/clear!))))

(defn- sentences [solutions] (set (map :sentence solutions)))

;; ---- the adapter contract -------------------------------------------------

(deftest the-overlay-kv-satisfies-the-backend-contract
  ;; A fork of nothing is the thing it forked: with an empty base, every merge rule
  ;; degenerates and the decorator has to answer the one spec every adapter answers.
  (let [base (doto (mem/memory-kv-backend {:space [::kv-base]}) (p/kv-clear!))
        ov   (doto (mem/memory-kv-backend {:space [::kv-fork]}) (p/kv-clear!))]
    (kvt/check-backend (okv/overlay-kv ov (frozen/frozen-kv base)))
    (is (empty? (p/kv-entries base)) "and the base stayed empty throughout")))

(deftest a-frozen-base-refuses-every-write
  (testing "the index half"
    (let [b (frozen/frozen-kv (mem/memory-kv-backend {:space [::frozen]}))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"mounted read-only"
                            (p/kv-add-to-set b [:x] 1)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"mounted read-only" (p/kv-clear! b)))
      (is (nil? (p/kv-get b [:x])) "and reads still work")))
  (testing "the record half"
    (let [r (frozen/frozen-records (mem/memory-record-store {:space [::frozen]}))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"mounted read-only"
                            (p/put-sentex r {:sentence '(dog Muffet)})))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"mounted read-only"
                            (p/clear-records! r)))
      (is (set? (p/sentex-ids r)) "and reads still work"))))

(deftest an-index-with-no-kv-backend-is-refused-rather-than-half-forked
  ;; The columnar index is a native `IndexStore` — its trie is int-id nodes in parallel
  ;; arrays, with no backend underneath — so a KvBackend decorator would fork its roots
  ;; and silently leave the trie behind.  Say so instead.
  (let [base (doto (v/open-kb {:backend :memory-columnar
                               :space [::col] :recover? false})
               (v/clear!))]
    (is (nil? (mount/kv-backend-of (:index base))))
    ;; Matched on what the caller can act on — the backend named and the ones that
    ;; would work — rather than on the mechanism, which the message now states after
    ;; the actionable clause instead of before it.
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cannot fork a :columnar index"
                          (v/fork base)))
    (is (= :unforkable-index
           (:type (try (v/fork base) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))))
    (v/clear! base)))

(deftest a-fork-of-a-fork-is-refused
  ;; `docs/overlay.md` states one overlay over one base.  `core/fork` passes
  ;; `:base-stores` and names no backend, so the opts check has nothing to match on and
  ;; the stores are asked directly (`mount/forked?`) — which is the only place a second
  ;; layer is visible.
  (let [base (doto (v/open-kb {:backend :memory
                               :space [::stk] :recover? false})
               (v/clear!))
        one  (v/fork base)]
    (is (true? (mount/forked? one)) "the first fork is a fork — `forked?` reads the pair")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"fork" (v/fork one)))
    (is (= :stacked-fork
           (:type (try (v/fork one) nil (catch clojure.lang.ExceptionInfo e (ex-data e)))))
        "and it says which refusal it is, rather than failing somewhere downstream")
    (v/clear! base)))

;; ---- fall-through, override, isolation ------------------------------------

(deftest a-fork-whose-own-half-is-its-base-is-refused
  ;; both halves naming one store — one `:disk` directory, or here one memory space —
  ;; is base immutability off with no error: `FrozenRecords` guards only the
  ;; calls routed through it, and the fork's writes go to the same instance direct.
  (let [spaces {:backend :memory :space [::selffork] :recover? false}
        base   (doto (v/open-kb spaces) (v/clear!))]
    (try
      (is (= :base-is-overlay
             (:type (try (v/open-kb {:backend :overlay :base spaces :overlay spaces
                                     :recover? false})
                         nil
                         (catch clojure.lang.ExceptionInfo e (ex-data e))))))
      (finally (v/clear! base)))))

(deftest a-fork-reads-through-to-its-base
  (let [base (fresh-base 1)
        f    (v/fork base)]
    (testing "stored content, belief and the taxonomy all arrive"
      (is (= '#{(dog Muffet)} (sentences (v/sentexes-matching f '(dog ?x) 'CxOverlay))))
      (is (= '#{(ownerOf Ann Muffet)} (sentences (v/sentexes-matching f '(ownerOf ?who Muffet) 'CxOverlay))))
      (is (= '#{(mammal Muffet)} (sentences (v/sentexes-matching f '(mammal ?x) 'CxOverlay)))
          "including what the base's rule derived")
      (is (v/isa? f 'Muffet 'animal) "and the genl closure the base's edge licenses"))
    (testing "the term index and the roots read through too"
      (is (seq (v/find-sentexes f 'Muffet)))
      (is (= (v/count-with-functor base 'dog) (v/count-with-functor f 'dog)))
      (is (= (v/sentex-count base) (v/sentex-count f))))
    (v/clear! base)))

(deftest a-fork-inherits-the-bases-preservation
  ;; The preservation reads — the declaration gates, the claim, the licence — cross
  ;; the protocol like every other read: a fork-local `genl` edge fires the base's rule
  ;; through the base's declaration and claim, fork-side only, and the base comes
  ;; back byte-identical.
  (let [base (doto (v/open-kb {:backend :memory :space [::preserve-base] :recover? false})
               (v/clear!))]
    (v/assert base '(transitiveInArg tmpLargerThan 1 genl) 'CxUniverse)
    (v/assert base '(tmpLargerThan tmp_dog tmp_cat) 'CxUniverse)
    (v/assert base '(implies (tmpLargerThan ?x ?y) (tmpOutweighs ?x ?y)) 'CxUniverse {:direction :forward})
    (let [before (base-snapshot base)
          f      (v/fork base)]
      (v/assert f '(genl tmp_chi tmp_dog) 'CxUniverse)
      (is (seq (v/sentexes-matching f '(tmpOutweighs tmp_chi tmp_cat) 'CxUniverse))
          "the fork-local edge fired the base's rule through the base's declaration")
      (is (empty? (v/sentexes-matching base '(tmpOutweighs tmp_chi tmp_cat) 'CxUniverse))
          "and the base derived nothing")
      (is (= before (base-snapshot base)) "byte-identical, not merely equivalent")
      (testing "retracting the fork-local edge withdraws what it licensed"
        (v/retract! f (v/handle-of f '(genl tmp_chi tmp_dog) 'CxUniverse))
        (is (empty? (v/sentexes-matching f '(tmpOutweighs tmp_chi tmp_cat)
                                         'CxUniverse)))))
    (v/clear! base)))

(deftest a-fork-writes-only-to-itself
  (let [base   (fresh-base 2)
        before (base-snapshot base)
        f      (v/fork base)]
    (v/assert f '(dog Rex) 'CxOverlay {:strength :monotonic})
    (testing "the fork sees its own write joined to what it inherited"
      (is (= '#{(dog Muffet) (dog Rex)} (sentences (v/sentexes-matching f '(dog ?x) 'CxOverlay))))
      (is (= '#{(mammal Muffet) (mammal Rex)} (sentences (v/sentexes-matching f '(mammal ?x) 'CxOverlay)))
          "the base's rule fired over the fork's fact"))
    (testing "and the base saw none of it"
      (is (= '#{(dog Muffet)} (sentences (v/sentexes-matching base '(dog ?x) 'CxOverlay))))
      (is (= before (base-snapshot base)) "the base is byte-identical"))
    (v/clear! base)))

(deftest two-forks-naming-the-default-storage-stay-independent
  ;; `{:backend :memory}` — the docstring's own spelling of the default — is not a
  ;; remount: fork opts naming neither a `:space` nor a `:dir` take a fresh fork
  ;; space, where they once landed on the shared process default (space 0) and two
  ;; such forks saw each other's writes
  (let [base (fresh-base 12)
        f1   (v/fork base {:backend :memory})
        f2   (v/fork base {:backend :memory})]
    (v/assert f1 '(dog Rex) 'CxOverlay {:strength :monotonic})
    (is (seq (v/sentexes-matching f1 '(dog Rex) 'CxOverlay)) "the writer sees it")
    (is (empty? (v/sentexes-matching f2 '(dog Rex) 'CxOverlay))
        "its sibling, taken with the same spelled-out default, does not")
    (v/clear! base)))

(deftest a-dense-overlay-half-projects-its-entries
  ;; the merged projection reads its pairs with `first`: the tiered backend's
  ;; kv-entries yields plain vectors where the map-backed ones yield MapEntrys, so a
  ;; fork whose own index is `:dense` threw ClassCastException on any walk of the
  ;; merged view — an export of such a fork died before its first frame
  (let [base (fresh-base 10)
        f    (v/fork base {:index :dense})]
    (v/assert f '(dog Rex) 'CxOverlay {:strength :monotonic})
    (is (seq (doall (p/kv-entries (:backend (:index f)))))
        "the merged projection realizes")
    (v/clear! base)))

(deftest retracting-an-inherited-premise-in-a-fork-leaves-the-base-alone
  (let [base   (fresh-base 3)
        before (base-snapshot base)
        f      (v/fork base)
        h      (v/handle-of f '(dog Muffet) 'CxOverlay)]
    (is (some? h) "the inherited premise is reachable by handle")
    (v/retract! f h)
    (testing "gone in the fork, with what it derived"
      (is (empty? (v/sentexes-matching f '(dog ?x) 'CxOverlay)))
      (is (empty? (v/sentexes-matching f '(mammal ?x) 'CxOverlay)) "the sweep reached the conclusion")
      (is (nil? (v/handle-of f '(dog Muffet) 'CxOverlay)) "the tombstone hides it from lookup"))
    (testing "present in the base"
      (is (= '#{(dog Muffet)} (sentences (v/sentexes-matching base '(dog ?x) 'CxOverlay))))
      (is (= '#{(mammal Muffet)} (sentences (v/sentexes-matching base '(mammal ?x) 'CxOverlay))))
      (is (= before (base-snapshot base))))
    (v/clear! base)))

(deftest a-fork-mints-handles-above-the-base-and-can-override-below-it
  (let [base   (fresh-base 4)
        before (base-snapshot base)
        top    (apply max (p/sentex-ids (:records base)))
        f      (v/fork base)
        recs   (:records f)]
    (testing "a new record gets a handle no base record holds"
      (let [h (v/assert f '(dog Rex) 'CxOverlay {:strength :monotonic})]
        (is (> (long h) (long top)) (str "minted " h " over a base topping out at " top))))
    (testing "a record written at a base handle overrides it, in the fork only"
      (let [h  (v/handle-of f '(ownerOf Ann Muffet) 'CxOverlay)
            sx (p/get-sentex recs h)]
        (is (<= (long h) (long top)) "the handle is in the base's range")
        (p/put-sentex recs (assoc sx :sentence '(ownerOf Bob Muffet)))
        (is (= '(ownerOf Bob Muffet) (:sentence (p/get-sentex recs h))) "the override wins in the fork")
        (is (= '(ownerOf Ann Muffet) (:sentence (p/get-sentex (:records base) h)))
            "and the base record is untouched")))
    (is (= before (base-snapshot base)))
    (v/clear! base)))

(deftest a-fork-can-be-cleared-back-to-empty-without-emptying-the-base
  (let [base   (fresh-base 5)
        before (base-snapshot base)
        f      (v/fork base)]
    (v/assert f '(dog Rex) 'CxOverlay {:strength :monotonic})
    (v/clear! f)
    (testing "the fork reads empty"
      (is (zero? (v/sentex-count f)))
      (is (empty? (p/sentex-ids (:records f))))
      (is (empty? (v/sentexes-matching f '(dog ?x) 'CxOverlay))))
    (testing "and is usable again, at handles nothing claims"
      (v/assert f '(cat Tom) 'CxOverlay {:strength :monotonic})
      (is (= '#{(cat Tom)} (sentences (v/sentexes-matching f '(cat ?x) 'CxOverlay)))))
    (is (= before (base-snapshot base)) "the base survived the fork's clear")
    (v/clear! base)))

(deftest reindexing-a-fork-rebuilds-the-merged-index-from-the-merged-records
  ;; `reindex` throws the whole index away and rebuilds it from the records, and on a
  ;; fork both of those are the merged view — which is what the O(1) `kv-clear!` marker
  ;; is for: without it the base's entries would survive the wipe and be counted twice.
  (let [base   (fresh-base 11)
        before (base-snapshot base)
        f      (v/fork base)]
    (v/assert f '(dog Rex) 'CxOverlay {:strength :monotonic})
    (let [{:keys [sentexes]} (v/reindex f)]
      (is (= sentexes (v/sentex-count f)) "every merged record was re-indexed, once")
      (is (= '#{(dog Muffet) (dog Rex)} (sentences (v/sentexes-matching f '(dog ?x) 'CxOverlay))))
      (is (= 2 (v/count-with-functor f 'dog)) "and no posting was double-counted")
      (is (v/isa? f 'Muffet 'animal) "the taxonomy came back with it"))
    (is (= before (base-snapshot base)) "and the base was not rebuilt into")
    (v/clear! base)))

;; ---- counts ---------------------------------------------------------------

(deftest merged-counts-are-exact-across-adds-deletes-and-overrides
  (let [base (fresh-base 6)
        f    (v/fork base)
        n0   (v/sentex-count base)]
    (is (= n0 (v/sentex-count f)) "a fresh fork counts what its base counts")
    (v/assert f '(dog Rex) 'CxOverlay {:strength :monotonic})
    (testing "an add moves the fork's counts and not the base's"
      ;; (dog Rex) plus the (mammal Rex) the inherited rule derived from it
      (is (= (+ 2 (long n0)) (long (v/sentex-count f))))
      (is (= n0 (v/sentex-count base)))
      (is (= 2 (v/count-with-functor f 'dog)))
      (is (= 1 (v/count-with-functor base 'dog)))
      (is (= 2 (v/count-with-arg f 1 'Rex)) "the argument root counts the merged view"))
    (testing "a delete of an inherited record moves them back"
      (v/retract! f (v/handle-of f '(dog Muffet) 'CxOverlay))
      (is (= 1 (v/count-with-functor f 'dog)))
      (is (= 1 (v/count-with-functor base 'dog)))
      (is (= n0 (v/count-in-context f 'CxOverlay))
          "the context root too — two records added, two swept, back where it started")
      (is (= (count (p/sentexes-in-context (:index f) 'CxOverlay))
             (v/count-in-context f 'CxOverlay))
          "a count never disagrees with the extent it counts"))
    (v/clear! base)))

(deftest count-children-answers-the-same-on-both-roads-through-the-merge
  ;; `p/count-children` is the trie's fan-out at a prefix off a *cardinality*, where
  ;; `(count (children …))` builds the child set to answer at all — and the planner's cost
  ;; model divides by it once per literal per plan (docs/indexing.md, docs/inference.md).
  ;;
  ;; On a fork it has two roads.  An **inherited** prefix — one the fork has neither added
  ;; a child under nor removed one from — hands the base's own `kv-count` straight back,
  ;; which is O(1) and is nearly every prefix a fork reads.  One the fork *has* written
  ;; under is counted off the merged set instead, a union minus a removal set having no
  ;; cardinality shortcut.  The two cost differently and that is documented; what they may
  ;; never do is *answer* differently, because a fork would then plan every query touching
  ;; its own writes against a fan-out the matcher does not see.  So each prefix below is
  ;; checked against the child set it counts, and pinned to a number that says which road
  ;; it took.
  (let [base (fresh-base 12)]
    (doseq [o '[Bob Cid]]
      (v/assert base (list 'ownerOf o 'Rex) 'CxOverlay {:strength :monotonic}))
    (let [f     (v/fork base)
          ix    (:index f)
          bx    (:index base)
          agree (fn [prefix]
                  (is (= (count (p/children ix prefix)) (p/count-children ix prefix))
                      (str "count-children disagrees with the child set it counts at " prefix)))]
      (doseq [o '[Dee Eve]]
        (v/assert f (list 'ownerOf o 'Rex) 'CxOverlay {:strength :monotonic}))
      (v/retract! f (v/handle-of f '(ownerOf Bob Rex) 'CxOverlay))
      (v/assert f '(likes Ann Rex) 'CxOverlay {:strength :monotonic})
      (testing "an inherited interior prefix is the base's own answer"
        ;; the fork asserted no `dog`, so nothing was written under this prefix at all
        (agree '[dog])
        (is (= (p/count-children bx '[dog]) (p/count-children ix '[dog]))))
      (testing "a prefix the fork both added children to and removed one from"
        ;; the merged road, and the one that has to take a difference: Ann and Cid
        ;; inherited, Dee and Eve added, Bob tombstoned
        (agree '[ownerOf])
        (is (= 4 (p/count-children ix '[ownerOf])))
        (is (= 3 (p/count-children bx '[ownerOf])) "and the base is untouched — Ann, Bob, Cid"))
      (testing "a prefix only the fork has"
        (agree '[likes])
        (is (= 1 (p/count-children ix '[likes])))
        (is (zero? (p/count-children bx '[likes])) "the base has never heard of it"))
      (testing "the root, where the fork's new functor widens what the base had"
        (agree [])
        (is (= (inc (long (p/count-children bx []))) (p/count-children ix []))))
      (testing "a whole sentence is one level above the leaf, and the level below it is the context"
        ;; the trie key ends with the context, so `[ownerOf Dee Rex]` is an interior node
        ;; whose children are the contexts the sentence is stored in — the form a merge
        ;; could most easily get wrong, since the fork's write and the base's live at
        ;; different depths under one predicate
        (agree '[ownerOf Dee Rex])
        (is (= 1 (p/count-children ix '[ownerOf Dee Rex]))))
      (testing "a leaf, an absent prefix and an absent predicate are zero, not a phantom"
        ;; the shapes `index_test` holds the two reads to on a plain backend, asked again
        ;; through the merge — a leaf has a handle under it and no children, and a merge
        ;; must turn neither absence into a count
        (doseq [prefix ['[ownerOf Dee Rex CxOverlay]
                        '[ownerOf Dee Rex CxNoSuch]
                        '[ownerOf Nobody]
                        '[noSuchPredicate]]]
          (agree prefix)
          (is (zero? (p/count-children ix prefix)) (str prefix)))))
    (v/clear! base)))

;; ---- the portable projection ----------------------------------------------

(deftest the-index-projection-of-a-fork-is-the-merged-view
  ;; `index-entries` is what an export of a fork writes, and it is the one read at which
  ;; a posting has to be merged without knowing any backend's private representation —
  ;; the contract says entries arrive as Clojure sets, which is what makes it possible.
  (let [base (fresh-base 10)
        f    (v/fork base)]
    (v/assert f '(dog Rex) 'CxOverlay {:strength :monotonic})
    (v/retract! f (v/handle-of f '(ownerOf Ann Muffet) 'CxOverlay))
    (let [entries (into {} (p/index-entries (:index f)))
          fork-h  (v/handle-of f '(dog Rex) 'CxOverlay)
          base-h  (v/handle-of base '(dog Muffet) 'CxOverlay)]
      (testing "a root inherited from the base and extended by the fork comes out merged"
        (is (= #{fork-h base-h} (get entries '[:functor-root dog]))))
      (testing "and one the fork emptied of its inherited member is simply gone"
        (is (nil? (get entries '[:functor-root ownerOf]))))
      (testing "the bookkeeping keys are the overlay's own and never project"
        (is (empty? (filter (fn [k] (or (keyword? k) (and (vector? k) (keyword? (first k))
                                                          (namespace (first k)))))
                            (keys entries)))))
      (testing "the term roster merges too — inherited names, plus and minus the fork's"
        (let [terms (set (v/terms f))]
          (is (contains? terms 'Muffet) "a name the fork inherited and left alone")
          (is (contains? terms 'Rex)  "one the fork introduced")
          (is (not (contains? terms 'Ann))
              "and one the fork's retraction retired — the roster is derived from the
               merged postings, so it is not merely the base's plus more"))))
    (v/clear! base)))

;; ---- several forks over one base ------------------------------------------

(deftest several-forks-over-one-base-evolve-independently
  (let [base   (fresh-base 7)
        before (base-snapshot base)
        forks  (mapv (fn [_] (v/fork base)) (range 3))]
    (doseq [[i f] (map-indexed vector forks)]
      (v/assert f (list 'dog (symbol (str "Fork" i))) 'CxOverlay {:strength :monotonic}))
    ;; the middle fork also drops what it inherited, so the three differ in both directions
    (v/retract! (nth forks 1) (v/handle-of (nth forks 1) '(dog Muffet) 'CxOverlay))
    (testing "each fork sees its own edit over the base and nobody else's"
      (is (= '#{(dog Muffet) (dog Fork0)} (sentences (v/sentexes-matching (nth forks 0) '(dog ?x) 'CxOverlay))))
      (is (= '#{(dog Fork1)}            (sentences (v/sentexes-matching (nth forks 1) '(dog ?x) 'CxOverlay))))
      (is (= '#{(dog Muffet) (dog Fork2)} (sentences (v/sentexes-matching (nth forks 2) '(dog ?x) 'CxOverlay)))))
    (testing "and the base is what it was"
      (is (= '#{(dog Muffet)} (sentences (v/sentexes-matching base '(dog ?x) 'CxOverlay))))
      (is (= before (base-snapshot base))))
    (v/clear! base)))

;; ---- durability -----------------------------------------------------------

(deftest a-durable-fork-remounts-onto-the-same-merged-view
  ;; The record-level bookkeeping — the tombstones and released premise marks — is not
  ;; derivable from the overlay's own records (nothing there records the *absence* of an
  ;; inherited one), so it has to be as durable as the fork is.  Close the fork's stores
  ;; and mount them again: a deleted inherited record must stay deleted.
  (let [base (fresh-base 8)
        dir  (tmpdir)]
    (try
      (let [f (v/fork base {:backend :disk-log :dir dir})]
        (v/assert f '(dog Rex) 'CxOverlay {:strength :monotonic})
        (v/retract! f (v/handle-of f '(dog Muffet) 'CxOverlay))
        (is (= '#{(dog Rex)} (sentences (v/sentexes-matching f '(dog ?x) 'CxOverlay)))))
      (disk/close-dir! dir)
      (testing "remounted over the same base, the fork is where it was left"
        (let [f2 (v/fork base {:backend :disk-log :dir dir})]
          (is (= '#{(dog Rex)} (sentences (v/sentexes-matching f2 '(dog ?x) 'CxOverlay)))
              "the inherited premise stayed retracted and the fork's own fact came back")
          (is (empty? (v/sentexes-matching f2 '(mammal Muffet) 'CxOverlay))
              "and so did what the retraction swept")
          (is (= '#{(mammal Rex)} (sentences (v/sentexes-matching f2 '(mammal ?x) 'CxOverlay)))
              "the base's rule still fires over the fork's own fact")))
      (testing "while the base never learned any of it"
        (is (= '#{(dog Muffet)} (sentences (v/sentexes-matching base '(dog ?x) 'CxOverlay)))))
      (finally
        (disk/close-dir! dir)
        (rm-rf! dir)
        (v/clear! base)))))

(deftest close-releases-a-durable-forks-own-directory-and-never-the-bases
  ;; `v/close!` on the fork, not `disk/close-dir!` on the path — the fork's writable half
  ;; takes the same exclusive lock and holds the same handles as any durable KB, so
  ;; without a `:dir` of its own the directory could not be handed on short of exiting
  ;; the JVM.  A second open of the same directory is the proof the lock came back.
  (let [base (fresh-base 9)
        dir  (tmpdir)]
    (try
      (let [f (v/fork base {:backend :disk-log :dir dir})]
        (v/assert f '(dog Rex) 'CxOverlay {:strength :monotonic})
        ;; canonical both sides — the store canonicalizes, so `/var` arrives as `/private/var`
        (is (= (.getCanonicalPath (File. (str dir)))
               (.getCanonicalPath (File. (str (:dir f)))))
            "a durable fork carries its own directory")
        (v/close! f))
      (testing "the directory is free, so it mounts again"
        (let [f2 (v/fork base {:backend :disk-log :dir dir})]
          (is (= '#{(dog Muffet) (dog Rex)}
                 (sentences (v/sentexes-matching f2 '(dog ?x) 'CxOverlay)))
              "with both halves of the merged view intact")
          (v/close! f2)))
      (testing "and the base is untouched — it is mounted read-only and shared"
        (is (= '#{(dog Muffet)} (sentences (v/sentexes-matching base '(dog ?x) 'CxOverlay)))))
      (finally
        (disk/close-dir! dir)
        (rm-rf! dir)
        (v/clear! base)))))

;; ---- the empty-base degeneracy, at KB level -------------------------------

(deftest a-fork-of-an-empty-base-is-an-ordinary-kb
  ;; The suite-parity gate in miniature: with nothing to merge, every code path above
  ;; must reduce to the plain backend's.  (`VAELII_TEST_BACKEND=overlay` runs the whole
  ;; suite this way — see scripts/test-backends.sh.)
  (let [base (doto (v/open-kb (assoc (base-opts 9) :recover? false)) (v/clear!))
        f    (v/fork base (fork-opts 9))]
    (tu/with-terms [dog Muffet CxThis]
      (v/assert f (list 'genl dog 'thing) CxThis {:strength :monotonic})
      (v/assert-rule f [(list dog '?x)] (list 'mammal '?x) CxThis {:direction :forward})
      (v/assert f (list dog Muffet) CxThis {:strength :monotonic})
      (is (= 1 (count (v/sentexes-matching f (list dog '?x) CxThis))))
      (is (seq (v/sentexes-matching f (list 'mammal '?x) CxThis)))
      (is (v/isa? f Muffet 'thing))
      (v/retract! f (v/handle-of f (list dog Muffet) CxThis))
      (is (empty? (v/sentexes-matching f (list 'mammal '?x) CxThis)) "and retraction sweeps"))
    (is (zero? (v/sentex-count base)) "the empty base stayed empty")
    (v/clear! f)))

(deftest a-fork-inherits-the-entry-point-policies
  ;; A fork is a hypothesis over the base's own content, so it has to hold that content
  ;; to the base's conventions.  A fork that quietly refused a clash the base would have
  ;; arbitrated — or held a lenient corpus to `:strict` — answers a different question
  ;; from the one the caller asked, and nothing in the call says so.
  (let [base (doto (v/open-kb (assoc (base-opts 10) :naming :warn :constraints :arbitrate
                                     :recover? false))
               (v/clear!))]
    (try
      (let [f (v/fork base (fork-opts 10))]
        (is (= :warn (:naming f)))
        (is (= :arbitrate (:constraints f)))
        (testing "and the inherited policy is the one that acts"
          (tu/with-terms [dog_t cat_t Muffet CxThis]
            (v/assert f (list 'disjoint dog_t cat_t) CxThis)
            (v/assert f (list dog_t Muffet) CxThis)
            (is (v/assert f (list cat_t Muffet) CxThis)
                "the base arbitrates, so the fork admits the clash rather than refusing")
            (is (= 1 (count (v/contradictions f))))))
        (v/clear! f))
      (testing "and the fork's own opts still win"
        (let [g (v/fork base (assoc (fork-opts 11) :naming :strict :constraints :refuse))]
          (is (= :strict (:naming g)))
          (is (= :refuse (:constraints g)))
          (v/clear! g)))
      (finally (v/clear! base)))))

(deftest defaulting-onto-the-shared-ram-space-twice-is-noticed
  ;; Naming the space is the ordinary way to say which store a KB is on; naming
  ;; *neither* it nor a directory is the default — and doing that twice
  ;; is one store behind two KB values, which is what `(def kb2 (open-kb {}))` looks
  ;; like when a REPL means "start clean".  The second KB recovers the first's records,
  ;; and thereafter a write through either is invisible to the other, since belief is
  ;; per-KB.  Both answers are legitimate values, so only a warning can say it.
  ;;
  ;; The counter rather than the log line: nothing in this suite captures trove output,
  ;; and the guard's whole decision is which opts maps it counts.  Space 0 is never
  ;; opened here — it is outside the suite's block (testing.md).
  (let [counter  @#'kb/default-ram-space-opens
        note!    #'kb/note-default-ram-space!
        counted? (fn [opts rkind]
                   (let [before @counter]
                     (note! opts rkind)
                     (not= before @counter)))
        prior    @counter]
    (try
      (testing "an in-RAM open naming no space is counted"
        (reset! counter 0)
        (is (counted? {} :memory))
        (is (counted? {:backend :memory} :memory))
        (is (= 2 @counter)))
      (testing "naming it is deliberate sharing and is not"
        (reset! counter 0)
        (is (not (counted? {:space 2} :memory)))
        (is (not (counted? {:space 0} :memory))
            "writing the default out is how a caller says the sharing is meant")
        (is (zero? @counter)))
      (testing "durable records are keyed by directory and take a lock, so not those"
        (reset! counter 0)
        (is (not (counted? {:dir "/tmp/whatever"} :disk)))
        (is (zero? @counter)))
      (testing "counting continues past the second, so the line stays a one-off"
        ;; the warning is keyed to the count reaching exactly 2: a line per open
        ;; would be noise in a process that legitimately opens many
        (reset! counter 0)
        (dotimes [_ 5] (note! {} :memory))
        (is (= 5 @counter)))
      (finally (reset! counter prior)))))

(deftest a-durable-fork-own-index-is-stamped-and-gated
  ;; The fork's own `:disk-log` index half carries the layout sentinel like any plain
  ;; `:disk-log` index: unstamped, the next `index-layout-version` bump would replay its
  ;; keys cleanly and miss every read whose shape moved — the base gets a clean
  ;; `:stale-index-layout` refusal, and without this the fork got silence.  The half
  ;; is the fork's own to rebuild, so a stale stamp rebuilds from the fork's own
  ;; records rather than refusing.
  (let [base (fresh-base 9)
        dir  (tmpdir)]
    (try
      (let [f (v/fork base {:backend :disk-log :dir dir})]
        (v/assert f '(dog Rex) 'CxOverlay {:strength :monotonic})
        (is (.isFile (java.io.File. (str dir "/index/layout.edn")))
            "the fork's own index half is stamped at open"))
      (disk/close-dir! dir)
      ;; a stamp from another key layout: the shape an old build's fork leaves behind
      (spit (str dir "/index/layout.edn")
            (pr-str {:index-layout (dec kv/index-layout-version)}))
      (testing "remounted under a moved layout, the fork's own half is rebuilt"
        (let [f2 (v/fork base {:backend :disk-log :dir dir})]
          (is (= '#{(dog Muffet) (dog Rex)}
                 (sentences (v/sentexes-matching f2 '(dog ?x) 'CxOverlay)))
              "the fork-local fact is findable again")
          (is (= (pr-str {:index-layout kv/index-layout-version})
                 (slurp (str dir "/index/layout.edn")))
              "and the stamp is current")))
      (finally
        (disk/close-dir! dir)
        (rm-rf! dir)
        (v/clear! base)))))

(deftest a-durable-base-under-a-moved-key-layout-is-refused-rather-than-mounted
  ;; `open-kb`'s layout gate reads the *fork's* directory, so a base named by `:base` opts
  ;; slips past it — and a mounted index whose key shape moved reads as populated while
  ;; every query whose keys moved answers nothing.  The repair the gate makes elsewhere is
  ;; a clear-and-rebuild, which is a write, and a base is mounted read-only: so this arm
  ;; refuses and names the directory to open as a KB of its own first.
  (let [dir    (tmpdir)
        forked (fn []
                 (try (let [f (v/open-kb {:backend  :overlay
                                          :base     {:backend :disk-log :dir dir}
                                          :overlay  (fork-opts 31)
                                          :recover? false})]
                        (v/clear! f)
                        :mounted)
                      (catch clojure.lang.ExceptionInfo e (ex-data e))))]
    (try
      (let [b (v/open-kb {:backend :disk-log :dir dir :recover? false})]
        (v/assert b '(dog Muffet) 'CxOverlay {:strength :monotonic})
        (is (.isFile (java.io.File. (str dir "/index/layout.edn")))
            "the base's own open stamped it"))
      (disk/close-dir! dir)
      (is (= :mounted (forked)) "a current stamp is what a fork mounts over")
      (disk/close-dir! dir)
      ;; the stamp an older build's key layout leaves behind
      (spit (str dir "/index/layout.edn")
            (pr-str {:index-layout (dec kv/index-layout-version)}))
      (let [d (forked)]
        (is (= :stale-index-layout (:type d)))
        (is (= (str dir "/index") (:dir d))
            "naming the directory whose index only its own KB may rebuild"))
      (testing "and opening that directory as a KB is what repairs it"
        (disk/close-dir! dir)
        (v/open-kb {:backend :disk-log :dir dir :recover? :auto})
        (disk/close-dir! dir)
        (is (= (pr-str {:index-layout kv/index-layout-version})
               (slurp (str dir "/index/layout.edn"))))
        (is (= :mounted (forked)) "after which the fork mounts"))
      (finally (disk/close-dir! dir) (rm-rf! dir)))))

(deftest a-durable-fork-remount-keeps-its-removals-and-its-merged-counts
  ;; The fork's own index half is its *delta* over the base — copy-on-write counters
  ;; holding base+net, and removal records for the inherited postings it took out — so
  ;; the coverage gate reads it through the merged mount, against the merged records:
  ;; the own half's counters against the fork's own record count disagree on every
  ;; healthy fork that has written anything, and an own-half rebuild would drop the
  ;; removals and leave own-only counters shadowing the base's.  So a remount under
  ;; `:recover? :auto` — the opts spelling, which runs the gate where `fork` passes
  ;; `:recover? false` — rebuilds nothing, the inherited fact the fork retracted stays
  ;; retracted, and the root count is the merged one.
  (let [base   (fresh-base 10)
        dir    (tmpdir)
        owned  '(ownerOf Ann Muffet)
        logged (atom [])
        rebuilt #{::kb/fork-index-coverage-rebuilt ::kb/fork-index-layout-rebuilt}
        remount! (fn []
                   (reset! logged [])
                   (binding [trove/*log-fn* (fn [_ _ _ id _] (swap! logged conj id))]
                     (v/open-kb {:backend  :overlay
                                 :base     (base-opts 10)
                                 :overlay  {:backend :disk-log :dir dir}
                                 :recover? :auto})))
        check!  (fn [f]
                  (is (nil? (v/handle-of f owned 'CxOverlay))
                      "the inherited fact the fork retracted stays retracted")
                  (is (= '#{(dog Muffet) (dog Rex)}
                         (sentences (v/sentexes-matching f '(dog ?x) 'CxOverlay)))
                      "the inherited and the fork-local fact are both served")
                  (is (= (count (p/sentex-ids (:records f))) (v/sentex-count f))
                      "the root count is the merged record count, not the own half's")
                  (is (= (inc (v/sentex-count base)) (v/sentex-count f))
                      "base, plus (dog Rex) and its mammal conclusion, minus the retracted owner")
                  (is (not-any? rebuilt @logged)
                      "a healthy own half is not rebuilt"))]
    (try
      (let [f (v/fork base {:backend :disk-log :dir dir})]
        (v/assert f '(dog Rex) 'CxOverlay {:strength :monotonic})
        (v/retract! f (v/handle-of f owned 'CxOverlay))
        (is (nil? (v/handle-of f owned 'CxOverlay)) "the fork took the inherited fact out")
        (is (some? (v/handle-of base owned 'CxOverlay)) "and the base still holds it"))
      (disk/close-dir! dir)
      (testing "the first remount"
        (check! (remount!)))
      (disk/close-dir! dir)
      (testing "and the second — a remount writes nothing the gate would then misread"
        (check! (remount!)))
      (finally
        (disk/close-dir! dir)
        (rm-rf! dir)
        (v/clear! base)))))

;; ---- what the capability entry points read off a fork ----------------------------
;; A fork's record store is a decorator over two others, so the two OPTIONAL capabilities
;; a base may carry have to reach it or be lost at the protocol: the `Tallying` samplers
;; `open-kb` asks before the KB has answered anything, and the `Prefetching` hint a
;; recovery walk gives a store whose fetch is a round trip.  Both are exercised against a
;; base that carries them, since none of the stores the engine ships does.

(defn- watched-base
  "`inner`, carrying the two capabilities a base may have and the engine's own stores do
  not: every prefetch hint recorded into `hints` by kind, and — when `pin` is non-nil — a
  sampler that always names that one handle, so a test can put the base's sample on
  exactly the handle the fork is about to take out rather than hoping it lands there.

  A `reify` rather than a `with-redefs`: a protocol method dispatches on the value's type
  and never reads the var root, so a redef of one intercepts nothing and the test would
  pass for the buggy and the fixed code alike."
  [inner hints pin]
  (reify
    p/RecordStore
    (put-sentex [_ sx] (p/put-sentex inner sx))
    (get-sentex [_ id] (p/get-sentex inner id))
    (delete-sentex! [_ id] (p/delete-sentex! inner id))
    (put-justification [_ d] (p/put-justification inner d))
    (get-justification [_ id] (p/get-justification inner id))
    (delete-justification! [_ id] (p/delete-justification! inner id))
    (next-id [_] (p/next-id inner))
    (put-provenance [_ id prov] (p/put-provenance inner id prov))
    (get-provenance [_ id] (p/get-provenance inner id))
    (delete-provenance! [_ id] (p/delete-provenance! inner id))
    (sentex-ids [_] (p/sentex-ids inner))
    (justification-ids [_] (p/justification-ids inner))
    (mark-premise [_ id st] (p/mark-premise inner id st))
    (unmark-premise! [_ id] (p/unmark-premise! inner id))
    (premise-ids [_] (p/premise-ids inner))
    (premise-strength [_ id] (p/premise-strength inner id))
    (clear-records! [_] (p/clear-records! inner))

    p/Tallying
    (sentex-tally        [_] (cap/count-sentexes inner))
    (justification-tally [_] (cap/count-justifications inner))
    (a-sentex-id         [_] (or pin (cap/some-sentex-id inner)))
    (a-justification-id  [_] (cap/some-justification-id inner))
    (a-premise-id        [_] (or pin (cap/some-premise-id inner)))

    p/Prefetching
    (prefetch-sentexes!       [_ ids] (swap! hints update :sentexes (fnil into []) ids) nil)
    (prefetch-justifications! [_ ids] (swap! hints update :justifications (fnil into []) ids) nil)))

(defn- fork-over
  "A fork whose base records are `store` — the `:base-stores` road `core/fork` takes,
  spelled out so a test can hand in a wrapped base."
  [base store n]
  (v/open-kb {:backend :overlay
              :base-stores {:records store :index (:index base)}
              :overlay (fork-opts n)
              :recover? :auto}))

(deftest a-forks-sampler-never-names-a-handle-the-merged-view-dropped
  ;; `Tallying`'s samplers are how `open-kb`'s recovery branch and `kb/write-hazards` ask
  ;; *does this store hold anything* without materializing `base u overlay - tombstoned`.
  ;; So the answer has to be a handle `get-sentex` answers for, and `nil` has to mean
  ;; empty: a fork that deleted the one record its base happened to sample is not an
  ;; empty fork, and reading it as one would skip the recovery that fork needs.
  (let [base    (fresh-base 21)
        before  (base-snapshot base)
        victim  (v/handle-of base '(dog Muffet) 'CxOverlay)
        watched (watched-base (:records base) (atom {}) victim)]
    (testing "the pin holds, so the fallback is under test rather than a coincidence"
      (is (= victim (p/a-sentex-id watched)))
      (is (= victim (p/a-premise-id watched))))

    (testing "a tombstoned base handle is never the sample"
      (let [f    (fork-over base watched 21)
            recs (:records f)]
        (is (= victim (cap/some-sentex-id recs)) "before the retraction it is the sample")
        (v/retract! f victim)
        (let [h (cap/some-sentex-id recs)
              p (cap/some-premise-id recs)]
          (is (some? h) "a fork that deleted one record still holds the rest")
          (is (not= victim h) "and never names the handle it tombstoned")
          (is (contains? (set (p/sentex-ids recs)) h) "the sample is in the merged roster")
          (is (some? (p/get-sentex recs h)) "and it fetches")
          (is (some? p) "the premise sampler survives the same deletion")
          (is (contains? (set (p/premise-ids recs)) p)))))

    (testing "nor is a released one"
      (let [f    (fork-over base watched 23)
            recs (:records f)]
        (p/unmark-premise! recs victim)
        (let [p (cap/some-premise-id recs)]
          (is (some? p) "releasing one inherited mark does not empty the premise set")
          (is (not= victim p) "and the released handle is not the sample")
          (is (contains? (set (p/premise-ids recs)) p)))))

    (testing "an empty fork over an empty base samples nil, which is what nil means"
      (let [e     (doto (v/open-kb (assoc (base-opts 24) :recover? false)) (v/clear!))
            f     (fork-over e (watched-base (:records e) (atom {}) nil) 24)
            recs  (:records f)]
        (is (nil? (cap/some-sentex-id recs)))
        (is (nil? (cap/some-justification-id recs)))
        (is (nil? (cap/some-premise-id recs)))
        (is (zero? (cap/count-sentexes recs)) "and the merged tally agrees")
        (v/clear! e)))

    (is (= before (base-snapshot base)) "and none of it wrote the base")
    (v/clear! base)))

(deftest a-forks-recovery-walk-hints-the-base-that-can-use-one
  ;; A fork gets its own belief by `recover`ing over the MERGED view, so it walks every
  ;; record and justification it inherits — which over a base whose fetch is a network
  ;; round trip is the one place `Prefetching` pays for itself.  The decorators are the
  ;; only thing between that walk and the base, so a hint they swallowed would be lost
  ;; with nothing to show it.
  (let [base   (fresh-base 25)
        before (base-snapshot base)
        hints  (atom {})
        f      (fork-over base (watched-base (:records base) hints nil) 25)]
    (testing "the entry point sees the capability through both decorators"
      (is (some? (cap/prefetcher (:records f)))
          "a frozen base's hint is forwarded, not refused at the protocol")
      (is (some? (cap/justification-prefetcher (:records f)))))
    (testing "and the open's own recover used it"
      (is (seq (:justifications @hints))
          "recover walks the merged justifications and hints the base's chunk")
      (is (every? #(contains? (set (p/justification-ids (:records base))) %)
                  (:justifications @hints))
          "every hinted handle is one the base actually holds"))
    (testing "so does the record walk a reindex makes"
      (reset! hints {})
      (v/reindex f)
      (is (seq (:sentexes @hints)) "reindex fetches every live record and hints them")
      (is (= (set (p/sentex-ids (:records f))) (set (:sentexes @hints)))
          "the hint covers the merged roster, which is what the walk consumes"))
    (is (= before (base-snapshot base)) "and hinting wrote nothing")
    (v/clear! base)))

(deftest every-write-op-on-a-frozen-base-is-refused-by-name
  ;; `a-frozen-base-refuses-every-write` above takes one op per half.  This takes the
  ;; whole roster, because invariant 1 of docs/overlay.md is structural rather than
  ;; reviewed: a base shared by N forks is only shared if *nothing* can write it, and a
  ;; single method that forwarded to the base instead of refusing is exactly the hole
  ;; that claim rules out.  Each refusal names the op in `:op`, which is what a caller
  ;; reading the ex-data can act on, so that is what is asserted.
  (let [b   (frozen/frozen-kv (mem/memory-kv-backend {:space [::frozen-roster]}))
        r   (frozen/frozen-records (mem/memory-record-store {:space [::frozen-roster]}))
        ops [["kv-put"               #(p/kv-put b [:x] 1)]
             ["kv-delete"            #(p/kv-delete b [:x])]
             ["kv-increment"         #(p/kv-increment b [:x])]
             ["kv-decrement"         #(p/kv-decrement b [:x])]
             ["kv-add-to-set"        #(p/kv-add-to-set b [:x] 1)]
             ["kv-remove-from-set"   #(p/kv-remove-from-set b [:x] 1)]
             ["kv-batch"             #(p/kv-batch b [[:kv-put [:x] 1]])]
             ["kv-load"              #(p/kv-load b [[[:x] 1]])]
             ["kv-clear!"            #(p/kv-clear! b)]
             ["put-sentex"           #(p/put-sentex r {:sentence '(dog Muffet)})]
             ["delete-sentex!"       #(p/delete-sentex! r 1)]
             ["put-justification"    #(p/put-justification r {:consequent 1})]
             ["delete-justification!" #(p/delete-justification! r 1)]
             ["put-provenance"       #(p/put-provenance r 1 {:informant :test})]
             ["delete-provenance!"   #(p/delete-provenance! r 1)]
             ["mark-premise"         #(p/mark-premise r 1 :default)]
             ["unmark-premise!"      #(p/unmark-premise! r 1)]
             ["clear-records!"       #(p/clear-records! r)]]
        ;; one `is` over the whole roster, not one per op: the count of assertions a
        ;; test makes is a gate, and it must not read the length of this vector
        outcome (into {} (map (fn [[op f]]
                                [op (try (f)
                                         :no-refusal
                                         (catch clojure.lang.ExceptionInfo e (ex-data e)))]))
                      ops)]
    (is (= (into #{} (map first) ops)
           (into #{} (comp (filter (fn [[_ d]] (= :frozen-base (:type d)))) (map key))
                 outcome))
        "every write op on either half refuses as :frozen-base, and none forwards")
    (is (= (into {} (map (fn [[op _]] [op op])) ops)
           (into {} (map (fn [[op d]] [op (:op d)])) outcome))
        "and each refusal names the op the caller called")
    (is (and (nil? (p/kv-get b [:x])) (set? (p/sentex-ids r)))
        "while the reads on both halves still answer")))

(deftest an-overlay-with-nothing-to-fork-is-refused-by-name
  ;; The one mistake the fork API invites: `:overlay` names a decorator, and a decorator
  ;; with nothing under it is not an empty KB — it is a request with a required half
  ;; missing.  Answered with a plain backend it would be a KB that reads and writes
  ;; correctly and forks nothing, which nothing downstream can tell from a fork whose base
  ;; was empty, so the refusal names both ways the base can be given instead.
  (let [d (try (v/open-kb {:backend :overlay :overlay (fork-opts 30) :recover? false})
               nil
               (catch clojure.lang.ExceptionInfo e (ex-data e)))]
    (is (= :no-base (:type d)) "a fork with no base is refused rather than answered")))
