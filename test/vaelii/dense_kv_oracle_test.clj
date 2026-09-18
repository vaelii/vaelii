;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.dense-kv-oracle-test
  "Differential oracle for the dense index backend (vaelii.impl.dense-kv): the same random
  op sequence is applied to `MemoryKvBackend` and `TieredKvBackend`, and every read must
  agree.  `KvIndexStore` (the trie/roots/index logic) is identical over both, so proving the
  backend set-equal proves the whole `:memory-dense` index set-equal to `:memory`.

  Exercised on purpose: handle keys (int postings) vs the trie label set `[:trie :children]` — which
  holds **number** tokens, the case a member-type dispatch would misclassify — vs counters;
  the int[]→RoaringBitmap promotion (a key grown past the threshold); srem-to-empty (key
  drops); and multi-key kv-intersect.

  `kv-intersect` gets a second test of its own because it narrows in the postings' stored
  representation: the tier pairings are five separate arms (the cold pair splits again on
  length ratio, merged against searched), and one of them is only reachable through a
  posting that promoted and then shrank, which no random stream is likely to build.  That
  test also pins the *read-only* half — an arm that used the mutating `RoaringBitmap.and`
  would answer every intersection correctly and silently shrink the index behind it."
  (:require [clojure.test :refer [deftest is]]
            [vaelii.impl.dense-kv :as dense]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.types.postings :as postings]))

(defn- pick [^java.util.Random rng v] (nth v (.nextInt rng (count v))))

(deftest kv-backend-set-equal
  (let [rng   (java.util.Random. 42)
        mem   (mem/memory-kv-backend  {:space 91})
        den   (dense/dense-kv-backend {:space 91})
        _     (do (p/kv-clear! mem) (p/kv-clear! den))
        ;; few handle keys + a big value range ⇒ some cross the promotion threshold to Roaring
        hkeys (vec (for [i (range 6)] [:functor-root (symbol (str "pr" i))]))
        lkeys (vec (for [i (range 3)] [:trie :children [(symbol (str "pr" i))]]))
        ckeys (vec (for [i (range 3)] [:trie :count [(symbol (str "pr" i))]]))]
    (dotimes [_ 8000]
      (let [r (.nextInt rng 100)]
        (cond
          (< r 45) (let [k (pick rng hkeys) m (.nextInt rng 500)]
                     (p/kv-add-to-set mem k m) (p/kv-add-to-set den k m))
          (< r 60) (let [k (pick rng hkeys) m (.nextInt rng 500)]
                     (p/kv-remove-from-set mem k m) (p/kv-remove-from-set den k m))
          ;; label set: mix symbol and NUMBER tokens (the misclassification trap)
          (< r 75) (let [k (pick rng lkeys)
                         m (if (< (.nextDouble rng) 0.5)
                             (symbol (str "s" (.nextInt rng 40)))
                             (long (.nextInt rng 2000)))]
                     (p/kv-add-to-set mem k m) (p/kv-add-to-set den k m))
          (< r 85) (let [k (pick rng lkeys) m (symbol (str "s" (.nextInt rng 40)))]
                     (p/kv-remove-from-set mem k m) (p/kv-remove-from-set den k m))
          (< r 95) (let [k (pick rng ckeys)]
                     (is (= (p/kv-increment mem k) (p/kv-increment den k)) "incr reply"))
          :else    (let [k (pick rng ckeys)]
                     (is (= (p/kv-decrement mem k) (p/kv-decrement den k)) "decr reply")))))
    ;; every handle / label key: members and cardinality agree
    (doseq [k (concat hkeys lkeys)]
      (is (= (p/kv-members mem k) (p/kv-members den k)) (str "smembers " k))
      (is (= (p/kv-count    mem k) (p/kv-count    den k)) (str "scard "    k)))
    ;; counters agree
    (doseq [k ckeys]
      (is (= (p/kv-get mem k) (p/kv-get den k)) (str "counter " k)))
    ;; at least one key promoted to a RoaringBitmap (else the test is not exercising it)
    (is (some #(> (p/kv-count den %) postings/promote) hkeys)
        "expected a hot posting past the promotion threshold")
    ;; kv-intersect over random handle-key subsets agrees
    (dotimes [_ 40]
      (let [ks (vec (take (inc (.nextInt rng 4)) (shuffle hkeys)))]
        (is (= (p/kv-intersect mem ks) (p/kv-intersect den ks)) (str "sinter " ks))))))

(deftest intersect-tiers-and-leaves-the-postings-alone
  (let [den (dense/dense-kv-backend {:space 93})
        k   (fn [n] [:functor-root n])
        add (fn [n xs] (doseq [x xs] (p/kv-add-to-set den (k n) x)))]
    (p/kv-clear! den)
    (add 'hot  (range 400))                      ; past `promote`, so a bitmap
    (add 'even (range 0 400 2))                  ; 200 — a bitmap too
    (add 'odd  (range 1 400 2))                  ; 200 — disjoint from `even`
    (add 'cold (range 0 400 40))                 ; 10 — an int[]
    (add 'half (range 100))                      ; 100 — an int[], just under the bound
    (add 'tiny [0 40 401])                       ; 3 — lopsided enough against `half` that
                                                 ;   the merge gives way to a binary search
    ;; a posting that promoted and then shrank: still a bitmap, and now the *smaller* side,
    ;; so it seeds the accumulator and the other side arrives as a raw int[]
    (add 'shrunk (range 200))
    (doseq [x (range 200) :when (pos? (mod x 50))] (p/kv-remove-from-set den (k 'shrunk) x))
    (is (> (p/kv-count den (k 'even)) postings/promote) "bitmap ∧ bitmap needs two bitmaps")
    (is (= 4 (p/kv-count den (k 'shrunk)))          "the shrunk posting is small but still hot")
    (let [names '[hot even odd cold half shrunk tiny]
          snap  (fn [] (into {} (map (fn [n] [n (p/kv-members den (k n))])) names))
          before (snap)]
      (is (= (set (range 0 400 2))  (p/kv-intersect den [(k 'hot) (k 'even)]))    "bitmap ∧ bitmap")
      (is (= (set (range 0 400 40)) (p/kv-intersect den [(k 'hot) (k 'cold)]))    "int[] acc ∧ bitmap")
      (is (= #{0 50}                (p/kv-intersect den [(k 'half) (k 'shrunk)])) "bitmap acc ∧ int[]")
      (is (= #{0 40 80}             (p/kv-intersect den [(k 'cold) (k 'half)]))   "int[] ∧ int[], merged")
      (is (= #{0 40}                (p/kv-intersect den [(k 'tiny) (k 'half)]))   "int[] ∧ int[], searched")
      (is (= #{0} (p/kv-intersect den [(k 'hot) (k 'even) (k 'cold) (k 'shrunk)]))
          "four keys, three tier pairings in one fold")
      (is (= #{} (p/kv-intersect den [(k 'cold) (k 'odd) (k 'hot)]))
          "an accumulator that empties stops the fold")
      (is (= #{} (p/kv-intersect den [(k 'shrunk) (k 'nothing)])) "a key holding nothing")
      (is (= before (snap)) "no read mutated a posting"))))

(deftest kv-batch-agrees
  (let [mem (mem/memory-kv-backend  {:space 92})
        den (dense/dense-kv-backend {:space 92})]
    (p/kv-clear! mem) (p/kv-clear! den)
    (let [ops [[:add-to-set [:functor-root 'p] 1] [:add-to-set [:functor-root 'p] 2] [:increment [:trie :count ['p]]]
               [:add-to-set [:trie :children ['p]] 'tok] [:add-to-set [:trie :children ['p]] 1970]
               [:remove-from-set [:functor-root 'p] 1] [:decrement [:trie :count ['p]]] [:increment [:trie :count ['p]]]]]
      (is (= (p/kv-batch mem ops) (p/kv-batch den ops)) "batch replies aligned")
      (is (= (p/kv-members mem [:functor-root 'p]) (p/kv-members den [:functor-root 'p])))
      (is (= (p/kv-members mem [:trie :children ['p]]) (p/kv-members den [:trie :children ['p]])))
      (is (= (p/kv-get mem [:trie :count ['p]]) (p/kv-get den [:trie :count ['p]]))))))
