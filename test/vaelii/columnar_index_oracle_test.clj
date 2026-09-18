;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.columnar-index-oracle-test
  "Differential oracle for the dense columnar index (`vaelii.impl.columnar`): the *same*
  sentex/handle op sequence is applied to the reference `KvIndexStore` (over an in-memory
  backend) and to the `ColumnarIndexStore`, and every read of the `IndexStore` protocol
  must agree — set-for-set and count-for-count.  Proving the two stores answer every
  `lookup` / `count-at` / `children` / root / rule / exception / term query identically
  proves `:memory-columnar` set-equal to `:memory` at the storage protocol; the whole test
  suite run under `VAELII_TEST_BACKEND=memory-columnar` proves it end-to-end.

  Exercised on purpose: the native trie's ragged paths (a fact's path a proper prefix of
  another's), **number** argument tokens (`1970` — a trie token, never a handle), nested
  compound arguments (the `[::subterm k]` markers the `lookup` walk must skip), negative
  facts (`[:false …]`), variable-pattern fan-out (every argument position blanked), node
  pruning on `unindex-sentex!`, and `clear-index!` back to empty.

  A node's child edges change *shape* past `trie-types/promote-at` children, and both shapes
  have to answer identically — so `columnar-wide-node-tiers` drives one node across that
  width in both directions with the threshold turned down, asserting the representation as
  well as the answers.

  The same oracle covers the **mapped snapshot** (`vaelii.impl.disk.index-snapshot`): the
  compacted store is written to disk, read back into a *different* columnar store, and
  every read re-checked against the reference that was never snapshotted.  Reusing this
  comparison rather than writing a second one is what makes an image cheap to trust — a
  round trip is one more representation of the same index, not a new subsystem."
  (:require [clojure.test :refer [deftest is]]
            [vaelii.impl.columnar :as columnar]
            [vaelii.impl.disk.index-snapshot :as snap]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.types.trie :as trie-types])
  (:import [it.unimi.dsi.fastutil.ints Int2IntOpenHashMap]))

;; ---- a small, collision-prone vocabulary --------------------------------

(def ^:private preds  '[p0 p1 p2 likes bornIn])
(def ^:private inds   '[A0 A1 A2 A3 B0 B1])
(def ^:private types  '[t0 t1 t2])
(def ^:private ctxs   '[C0 C1 C2])

(defn- pick [^java.util.Random rng v] (nth v (.nextInt rng (count v))))

(defn- rand-arg [^java.util.Random rng depth]
  (let [r (.nextInt rng 100)]
    (cond
      (< r 55) (pick rng inds)
      (< r 75) (long (* 1900 (inc (.nextInt rng 4))))          ; a number token
      (and (< r 90) (pos? depth))                              ; a nested compound argument
      (list (pick rng preds) (rand-arg rng (dec depth)) (rand-arg rng (dec depth)))
      :else    (pick rng inds))))

(defn- rand-sentence [^java.util.Random rng]
  (let [r (.nextInt rng 100)]
    (cond
      (< r 25) (list (pick rng types) (pick rng inds))                        ; unary type
      (< r 50) (list (pick rng preds) (pick rng inds) (pick rng inds))        ; binary
      (< r 65) (list (pick rng preds) (pick rng inds) (pick rng inds) (pick rng inds)) ; ternary
      (< r 80) (list (pick rng preds) (pick rng inds) (rand-arg rng 2))       ; nested arg
      (< r 90) (list 'not (list (pick rng preds) (pick rng inds) (pick rng inds))) ; negative
      :else    (list (pick rng preds) (pick rng inds) (long (.nextInt rng 3000)))))) ; numeric

;; ---- comparison ----------------------------------------------------------

(defn- both [f a b] (is (= (f a) (f b))))

(defn- prefixes [path]
  (map #(subvec path 0 %) (range (inc (count path)))))

(defn- var-patterns
  "The stored path, plus patterns blanking each token in turn and one blanking all —
  the variable fan-out the walk must reproduce."
  [path]
  (let [n (count path)]
    (cons path
          (cons (vec (repeat n '?v))
                (for [i (range n)] (assoc path i '?v))))))

(defn- compare-all [mem col sentexes]
  (let [paths  (mapv sx/path sentexes)
        pfxs   (into #{} (mapcat prefixes) paths)
        terms  (into #{} (mapcat #(conj (sx/index-terms %) (:context %)) sentexes))
        args   (into #{} (for [s sentexes
                               :let [b (sx/body s)]
                               :when (and (sequential? b) (symbol? (first b)))
                               [i a] (map-indexed vector (rest b))]
                           [(inc i) a]))]
    ;; every stored path and its variable fan-out patterns
    (doseq [path paths, pat (var-patterns path)]
      (both #(p/lookup % pat) mem col))
    ;; count-at + children over every prefix that occurs anywhere
    (doseq [pfx pfxs]
      (both #(p/count-at % pfx) mem col)
      (both #(set (p/children % pfx)) mem col))
    ;; the secondary roots
    (doseq [c ctxs]
      (both #(p/sentexes-in-context % c) mem col)
      (both #(p/count-in-context % c) mem col))
    (doseq [pr preds]
      (both #(p/sentexes-with-functor % pr) mem col)
      (both #(p/count-with-functor % pr) mem col))
    (doseq [[pos t] args]
      (both #(p/sentexes-with-arg % pos t) mem col)
      (both #(p/count-with-arg % pos t) mem col))
    ;; multi-column narrowing + the inverted term index
    (doseq [s sentexes :let [b (sx/body s)]
            :when (and (sequential? b) (symbol? (first b)) (>= (count b) 3))]
      (both #(p/sentexes-with-args % (first b) [[1 (nth b 1)] [2 (nth b 2)]]) mem col))
    (doseq [t terms] (both #(p/sentexes-with-term % t) mem col))
    (doseq [ts (partition-all 2 (seq terms))]
      (both #(p/sentexes-with-terms % (vec ts)) mem col))
    ;; the term roster — the vocabulary must be the same set and the same count, so a
    ;; name retired by the last unindex on one store is retired on the other
    (both p/terms mem col)
    (both p/term-count mem col)))

;; ---- the oracle ----------------------------------------------------------

(deftest ^:slow columnar-index-set-equal
  (let [rng (java.util.Random. 20260724)
        mem (mem/memory-index-store  {:space 71})
        col (columnar/columnar-index-store {:space 71})]
    (p/clear-index! mem) (p/clear-index! col)
    ;; build one op stream and apply the identical (sentex, handle) to both stores
    (let [ops (vec (for [i (range 1200)]
                     [(sx/sentex (rand-sentence rng) (pick rng ctxs)) (inc i)]))]
      (doseq [[s h] ops]
        (p/index-sentex mem s h)
        (p/index-sentex col s h))
      (compare-all mem col (map first ops))

      ;; remove a third of them (interleaved handles) and re-compare — exercises node
      ;; pruning + the parent-detach path
      (let [removed (take-nth 3 ops)
            live    (remove (set removed) ops)]
        (doseq [[s h] removed]
          (p/unindex-sentex! mem s h)
          (p/unindex-sentex! col s h))
        (compare-all mem col (map first live))

        ;; a wipe leaves both empty and equal
        (p/clear-index! mem) (p/clear-index! col)
        (is (zero? (p/count-at col [])))
        (is (zero? (p/term-count col)) "the roster is wiped with the index")
        (doseq [[s _] ops] (is (empty? (p/lookup col (sx/path s)))))
        (both #(p/count-at % []) mem col)))))

;; ---- CSR compaction: frozen reads must equal the mutable reference -------

(deftest ^:slow columnar-compaction-equivalent
  (let [rng (java.util.Random. 999)
        mem (mem/memory-index-store      {:space 73})
        col (columnar/columnar-index-store {:space 73})]
    (p/clear-index! mem) (p/clear-index! col)
    (let [ops (vec (for [i (range 800)]
                     [(sx/sentex (rand-sentence rng) (pick rng ctxs)) (inc i)]))]
      (doseq [[s h] ops] (p/index-sentex mem s h) (p/index-sentex col s h))
      ;; freeze the columnar trie into CSR; every frozen read must equal the mutable ref
      (columnar/compact! col)
      (compare-all mem col (map first ops))

      ;; a write thaws it back to mutable — still equal
      (let [removed (take-nth 4 ops)
            live    (remove (set removed) ops)]
        (doseq [[s h] removed]
          (p/unindex-sentex! mem s h) (p/unindex-sentex! col s h))
        (compare-all mem col (map first live))

        ;; re-freeze after churn (compaction also reclaims the freed node ids) — still equal
        (columnar/compact! col)
        (compare-all mem col (map first live))

        ;; an insert after freezing thaws and lands correctly
        (let [s (sx/sentex (rand-sentence rng) (pick rng ctxs))]
          (p/index-sentex mem s 90001) (p/index-sentex col s 90001)
          (compare-all mem col (map first (conj (vec live) [s 90001]))))))))

;; ---- the width tier: a node's two child shapes, in both directions -------

(defn- node-at
  "The trie node id at a decoded path prefix, negative when the prefix is absent."
  [trie prefix]
  (#'trie-types/-node-at trie prefix))

(defn- child-rep
  "Which shape the trie is holding node `id`'s child edges in — `:none`, `:array` (the
  sorted `int[]` pair) or `:map` (the primitive hash map).  Read straight off the
  deftype's own field, because the tier is invisible to every answer the store gives: no
  comparison of reads can tell a promotion that happened from one that did not, nor a
  removal that maintained one shape and forgot the other."
  [trie ^long id]
  (let [^java.lang.reflect.Field f (doto (.getDeclaredField (class trie) "toks")
                                     (.setAccessible true))
        ^objects tk (.get f trie)
        ch (aget tk (int id))]
    (cond (nil? ch)                          :none
          (instance? Int2IntOpenHashMap ch)  :map
          :else                              :array)))

(deftest columnar-wide-node-tiers
  ;; One predicate, one context, n distinct first arguments — so a single node holds one
  ;; child edge per fact and is the only thing in the trie that grows.  `promote-at` is
  ;; turned down to 8 (so it demotes at 4) rather than building a node of 65: the tier is
  ;; a threshold, and what has to be exercised is the crossing, not the width.
  (with-redefs [trie-types/promote-at 8]
    (let [mem  (mem/memory-index-store       {:space 74})
          col  (columnar/columnar-index-store {:space 74})
          trie (:trie col)]
      (p/clear-index! mem) (p/clear-index! col)
      (let [sent   (fn [i] (sx/sentex (list 'pwide (symbol (str "W" i))) 'CxWide))
            ops    (mapv (fn [i] [(sent i) (inc i)]) (range 40))
            wide   (subvec (sx/path (first (first ops))) 0 1)   ; holds one child per W
            apply! (fn [f xs] (doseq [[s h] xs] (f mem s h) (f col s h)))
            rep    (fn [] (child-rep trie (node-at trie wide)))]

        ;; at the threshold exactly, still the dense pair
        (apply! p/index-sentex (subvec ops 0 8))
        (is (= :array (rep)))
        (compare-all mem col (map first (subvec ops 0 8)))

        ;; one child more promotes it, and the answers do not move
        (apply! p/index-sentex (subvec ops 8 9))
        (is (= :map (rep)))
        (compare-all mem col (map first (subvec ops 0 9)))

        (apply! p/index-sentex (subvec ops 9))
        (is (= :map (rep)))
        (compare-all mem col (map first ops))

        ;; frozen reads of a wide node go through a CSR run built from the map, and the
        ;; frozen `-get-child` binary-searches it — so an unsorted freeze would answer
        ;; nothing here rather than answer it differently
        (columnar/compact! col)
        (compare-all mem col (map first ops))

        ;; the write thaws, and a node that is still wide comes back as a map rather than
        ;; splicing its way back up to one
        (let [extra [(sent 400) 401]]
          (apply! p/index-sentex [extra])
          (is (= :map (rep)))
          (compare-all mem col (map first (conj ops extra)))

          ;; shrink it back under half the threshold: the dense pair returns, and every
          ;; read of the demoted node still agrees
          (apply! p/unindex-sentex! (conj (subvec ops 3) extra))
          (is (= :array (rep)))
          (compare-all mem col (map first (subvec ops 0 3))))

        ;; and it promotes again afterwards — the tier is a function of the current width,
        ;; not a one-way entry point
        (apply! p/index-sentex (subvec ops 3))
        (is (= :map (rep)))
        (compare-all mem col (map first ops))

        ;; and emptying it prunes the node out of the trie altogether
        (apply! p/unindex-sentex! ops)
        (is (neg? (node-at trie wide)) "the node is gone, not merely empty")
        (is (zero? (p/count-at col [])))
        (both #(p/count-at % []) mem col)
        (both p/terms mem col)))))

;; ---- a number token is one token however it was boxed -------------------

(deftest columnar-number-tokens-key-by-clojure-equality
  ;; The flat map keys its trie on a `PersistentHashMap`, where `(= 2 (int 2))` is true;
  ;; the columnar dictionary keys on a `java.util.HashMap`, where
  ;; `Integer(2).equals(Long(2))` is false.  Both boxings genuinely reach a path — an
  ;; `agg/count` conclusion carries an `Integer` and the same sentence asked as a question
  ;; carries a `Long` — so a dictionary keyed by Java equality answers one fewer, silently.
  ;; This is the read the random oracle above cannot make: it generates one boxing.
  (let [mem (mem/memory-index-store       {:space 78})
        col (columnar/columnar-index-store {:space 78})
        as-int  (sx/sentex (list 'nCount 'NAnn (int 2)) 'CxNCount)
        as-long (sx/sentex (list 'nCount 'NAnn (long 2)) 'CxNCount)]
    (p/clear-index! mem) (p/clear-index! col)
    (is (= (sx/path as-int) (sx/path as-long)) "the two paths are Clojure-equal")
    (doseq [store [mem col]] (p/index-sentex store as-int 4242))
    (doseq [[label pth] [["stored boxing" (sx/path as-int)] ["asked boxing" (sx/path as-long)]]]
      (is (= #{4242} (p/lookup col pth)) label)
      (both #(p/lookup % pth) mem col))
    (both #(p/count-at % (subvec (sx/path as-long) 0 2)) mem col)
    (both #(set (p/children % (subvec (sx/path as-long) 0 2))) mem col)
    (both #(p/sentexes-with-arg % 2 (long 2)) mem col)
    ;; and the removal has to find it under the other boxing too, or the node is orphaned
    (doseq [store [mem col]] (p/unindex-sentex! store as-long 4242))
    (both #(p/lookup % (sx/path as-int)) mem col)
    (is (zero? (p/count-at col [])))))

(deftest a-stray-unindex-takes-nothing-with-it
  ;; The trie's counters come down without looking, and a node that reaches zero is
  ;; deleted with every handle at its leaf — so an unindex of a handle that is not at
  ;; the leaf (never indexed, or already removed) is gated on one membership probe and
  ;; touches nothing.  Otherwise one stray call would take a live sibling's nodes, and
  ;; the sibling with them, out of the trie.
  (doseq [[label store] [["flat"     (mem/memory-index-store       {:space 79})]
                         ["columnar" (columnar/columnar-index-store {:space 79})]]]
    (p/clear-index! store)
    (let [kept   (sx/sentex '(sLikes SAnn SBob) 'CxStray)
          ghost  (sx/sentex '(sLikes SAnn SCat) 'CxStray)     ; shares the prefix, never indexed
          pth    (sx/path kept)]
      (p/index-sentex store kept 7)
      (p/unindex-sentex! store ghost 8)                       ; a handle never stored
      (p/unindex-sentex! store kept 9)                        ; the right path, the wrong handle
      (is (= #{7} (p/lookup store pth)) (str label ": the stored handle is still at its leaf"))
      (is (= 1 (p/count-at store [])) (str label ": the root count is untouched"))
      (is (= 1 (p/count-at store (subvec pth 0 2))) (str label ": the shared prefix's count is untouched"))
      (is (= #{7} (p/sentexes-with-term store 'SAnn)) (str label ": the term index is untouched"))
      (p/unindex-sentex! store kept 7)
      (p/unindex-sentex! store kept 7)                        ; a second removal of the same handle
      (is (empty? (p/lookup store pth)) (str label ": the real removal took"))
      (is (zero? (p/count-at store [])) (str label ": and the counts are back at zero, not below")))))

;; ---- the mapped snapshot: a round trip is one more representation --------

(defn- tmpdir ^String []
  (str (java.nio.file.Files/createTempDirectory
        "vaelii-snap-oracle-" (into-array java.nio.file.attribute.FileAttribute []))))

(defn- rm-rf! [^String d]
  (doseq [f (reverse (file-seq (java.io.File. d)))] (.delete ^java.io.File f)))

;; The stamp is the *records'* fingerprint, and this oracle has no record store — so it
;; hands over a constant.  What the round trip has to prove is that a mapped index answers
;; what the store it was written from answered; that the stamp catches a KB which moved
;; underneath one is `index_snapshot_test`'s question, against real records.
(def ^:private constant-stamp (constantly {:count 1 :max-handle 1 :digest 42}))

(deftest ^:slow columnar-snapshot-round-trip
  (let [dir (tmpdir)]
    (try
      (let [rng (java.util.Random. 5150)
            mem (mem/memory-index-store        {:space 75})
            src (columnar/columnar-index-store {:space 76})
            dst (columnar/columnar-index-store {:space 77})]
        (doseq [s [mem src dst]] (p/clear-index! s))
        (let [ops (vec (for [i (range 900)]
                         [(sx/sentex (rand-sentence rng) (pick rng ctxs)) (inc i)]))]
          (doseq [[s h] ops] (p/index-sentex mem s h) (p/index-sentex src s h))
          (doseq [store [mem src]]
            (p/index-rule store 7001 '[p0 p1] 'p2)
            (p/index-exception store 7001 '[penguin flies]))

          ;; write, read into a store that has never seen a sentex, and re-check
          ;; everything against the reference that was never snapshotted
          (is (= :saved (:index (snap/save! dir src constant-stamp))))
          (is (= :mapped (:index (snap/load! dir dst constant-stamp))))
          (compare-all mem dst (map first ops))
          (is (= (p/rules-by-antecedent mem 'p0) (p/rules-by-antecedent dst 'p0)))
          (is (= (p/rules-by-consequent mem 'p2) (p/rules-by-consequent dst 'p2)))
          (is (= (p/rules-with-exception-on mem 'penguin) (p/rules-with-exception-on dst 'penguin)))
          (is (= (p/exception-rules mem) (p/exception-rules dst)))
          (is (true? (p/exception-rule? dst 7001)))

          ;; a mapped store is written to exactly like any other — the trie thaws its leaf
          ;; run out of the mapping and the roots thaw wholesale
          (let [removed (take-nth 5 ops)
                live    (remove (set removed) ops)
                extra   (sx/sentex (rand-sentence rng) (pick rng ctxs))]
            (doseq [[s h] removed]
              (p/unindex-sentex! mem s h) (p/unindex-sentex! dst s h))
            (p/index-sentex mem extra 99001) (p/index-sentex dst extra 99001)
            (compare-all mem dst (map first (conj (vec live) [extra 99001])))

            ;; and the churned store round-trips again, back into the first one
            (is (= :saved (:index (snap/save! dir dst constant-stamp))))
            (is (= :mapped (:index (snap/load! dir src constant-stamp))))
            (compare-all mem src (map first (conj (vec live) [extra 99001]))))))
      (finally (rm-rf! dir)))))

;; ---- the rule / exception index (delegated to the shared backend) --------

(deftest columnar-rule-and-exception-index
  (let [mem (mem/memory-index-store  {:space 72})
        col (columnar/columnar-index-store {:space 72})]
    (p/clear-index! mem) (p/clear-index! col)
    (doseq [store [mem col]]
      (p/index-rule store 10 '[p0 p1] 'p2)
      (p/index-rule store 11 '[p1] 'p0)
      (p/index-exception store 10 '[penguin flies])
      (p/index-exception store 11 '[t0]))
    (doseq [pr '[p0 p1 p2 penguin flies t0]]
      (both #(p/rules-by-antecedent % pr) mem col)
      (both #(p/rules-by-consequent % pr) mem col)
      (both #(p/rules-with-exception-on % pr) mem col))
    (both p/exception-rules mem col)
    (doseq [h [10 11 12]] (both #(p/exception-rule? % h) mem col))
    ;; retract one rule + its exception and re-compare
    (doseq [store [mem col]]
      (p/unindex-rule! store 10 '[p0 p1] 'p2)
      (p/unindex-exception! store 10 '[penguin flies]))
    (doseq [pr '[p0 p1 p2 penguin flies t0]]
      (both #(p/rules-by-antecedent % pr) mem col)
      (both #(p/rules-with-exception-on % pr) mem col))
    (both p/exception-rules mem col)))

;; ---- the frozen layout is a layout, so it has to be fixed ---------------

(defn- sections
  "A frozen store's CSR as comparable values (the arrays as vectors)."
  [store]
  (let [c (columnar/csr store)]
    (reduce (fn [m k] (update m k #(into [] %))) c
            [:counts :offsets :edge-tok :edge-tgt :leaf-off :handles])))

(deftest a-frozen-leaf-run-is-ascending-by-handle
  ;; `t-compact!` fills each node's handle run from its postings, and filling it from the
  ;; Clojure **set** those postings build put the run in hash order — an ordering that is
  ;; a function of how the set was assembled as well as of what is in it, and one nothing
  ;; downstream asks for.  This is a byte layout rather than a belief question (every
  ;; reader takes a run as a whole set; none reads its order for meaning), so handle order
  ;; is the right one to fix on — and it is the order the postings already hold.
  (let [rng  (java.util.Random. 4242)
        ops  (vec (for [i (range 400)]
                    [(sx/sentex (rand-sentence rng) (pick rng ctxs)) (inc i)]))
        load (fn [space entries]
               (let [col (columnar/columnar-index-store {:space space})]
                 (p/clear-index! col)
                 (doseq [[s h] entries] (p/index-sentex col s h))
                 (columnar/compact! col)
                 col))
        a    (load 81 ops)
        b    (load 82 ops)
        {:keys [nodes leaf-off handles]} (sections a)]
    (is (pos? (count handles)) "there are runs to be wrong about")
    (doseq [i (range nodes)
            :let [run (subvec handles (nth leaf-off i) (nth leaf-off (inc i)))]
            :when (seq run)]
      (is (= (vec (sort run)) run) (str "node " i "'s leaf run is ascending")))
    ;; the freeze is a function of the op sequence and nothing else — two stores given
    ;; the same ops produce the same bytes, section for section.  (Not of the *content*
    ;; alone: the token dictionary numbers terms in first-seen order, so a different
    ;; arrival order is a different trie and legitimately a different image.)
    (is (= (sections a) (sections b)))))
