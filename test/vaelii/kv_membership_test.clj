;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.kv-membership-test
  "`kv-member?` against `kv-members`, on every `KvBackend` — the differential the set
  oracles structurally cannot run.

  Every adapter returns the same *sets*, and `dense_kv_oracle_test`,
  `dense_roots_oracle_test` and `overlay_test` prove it.  A membership probe that
  disagreed with the set it probes would pass all three: the two ops answer different
  questions and nothing compares them.  And the probe is a genuinely separate code path
  per backend — a hash lookup, a binary search over an `int[]`, a `RoaringBitmap` test, an
  interned-key route, a three-way merge across the overlay protocol — because that is the
  point of having it: `exception-rule?` is taken once per candidate rule per new datum, so
  answering it by materializing the roster makes forward chaining a product of two
  KB-sized quantities.  The property below is the whole specification, over a spread of
  keys, members and families:

      (kv-member? b k m)  =  (contains? (kv-members b k) m)

  The overlay arm carries a second property.  A fork's `kv-count`, `kv-members` and
  `kv-intersect` take a fast path when the merged answer *is* the base's — the structure of
  nearly every key a fork reads, and the one that decides what its query plans cost — so
  all three are checked against
  the merge rule transcribed independently here from the overlay's own bookkeeping keys,
  over every shape that rule distinguishes: inherited untouched, extended, partially
  removed, emptied of everything inherited, removed-then-restored, tombstoned, deleted and
  re-added fresh, overlay-only, absent from both, and wholesale-cleared."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing]]
            [vaelii.impl.dense-kv :as dense]
            [vaelii.impl.dense-roots :as dr]
            [vaelii.impl.disk.kv :as dkv]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.overlay.frozen :as frozen]
            [vaelii.impl.overlay.kv :as okv]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.tokens :as tok]
            [vaelii.impl.types.postings :as postings])
  (:import [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

;; ---- the property ---------------------------------------------------------

(defn- probe-agrees
  "The property, for one backend over `ks` × `ms`."
  [b label ks ms]
  (doseq [k ks]
    (let [s (p/kv-members b k)]
      (doseq [m ms]
        (is (= (contains? s m) (boolean (p/kv-member? b k m)))
            (str label ": " (pr-str k) " ∋ " (pr-str m)
                 " — members says " (contains? s m)))))))

;; Keys are grouped by what a member of theirs may *be*, not by tag: a handle family is an
;; `IntPostings` on the dense backends and holds ints only, so probing it with a symbol is
;; a type error there and not an interesting disagreement.  The label families hold tokens
;; and names and take anything.
(def ^:private handle-keys
  (vec (concat (for [p '[p0 p1 p2]] [:functor-root p])
               (for [c '[C0 C1]]    [:context-root c])
               (for [t '[A0 A1]]    [:term-index t])
               [[:argument-root 'p0 1 'A0]
                [:rule-index :antecedent 'p0]
                [:rule-index :consequent 'p2]
                [:exception-index 'flies]
                [:exception-index :rules]        ; the roster the gate probes
                [:trie :handles '[p0 A0]]
                [:functor-root 'never-written]])))

(def ^:private label-keys
  (vec (concat (for [p '[p0 p1]] [:trie :children [p]])
               [[:term-roster] [:trie :children '[never]]])))

(def ^:private handle-probes (vec (concat (range 0 24) [199 400 999])))
(def ^:private label-probes  (vec (concat '[s0 s7 s39 never] [17 1970 8888])))

(defn- churn!
  "The same random add/remove sequence on each of `backends`, so every key ends up
  somewhere interesting — populated, emptied back to absent, or (on the dense backends)
  grown past the `int[]` → `RoaringBitmap` promotion."
  [backends seed n]
  (let [rng (java.util.Random. seed)
        pick (fn [v] (nth v (.nextInt rng (count v))))]
    (dotimes [_ n]
      (let [r (.nextInt rng 100)]
        (cond
          (< r 50) (let [k (pick handle-keys) m (.nextInt rng 300)]
                     (doseq [b backends] (p/kv-add-to-set b k m)))
          (< r 70) (let [k (pick handle-keys) m (.nextInt rng 300)]
                     (doseq [b backends] (p/kv-remove-from-set b k m)))
          (< r 90) (let [k (pick label-keys)
                         m (if (< (.nextDouble rng) 0.5)
                             (symbol (str "s" (.nextInt rng 40)))
                             (long (.nextInt rng 2000)))]
                     (doseq [b backends] (p/kv-add-to-set b k m)))
          :else    (let [k (pick label-keys) m (symbol (str "s" (.nextInt rng 40)))]
                     (doseq [b backends] (p/kv-remove-from-set b k m))))))))

(defn- check-probe
  "Churn `b` and then hold it to the property on both key families."
  [b label]
  (p/kv-clear! b)
  (churn! [b] 4242 6000)
  (probe-agrees b label handle-keys handle-probes)
  (probe-agrees b label label-keys  label-probes)
  (testing (str label ": an emptied key holds nothing")
    (doseq [m (p/kv-members b [:functor-root 'p0])]
      (p/kv-remove-from-set b [:functor-root 'p0] m))
    (is (not (p/kv-member? b [:functor-root 'p0] 1))))
  (testing (str label ": and a cleared store holds nothing")
    (p/kv-clear! b)
    (probe-agrees b label handle-keys [0 1 199])))

;; ---- the plain backends ---------------------------------------------------

(deftest memory-backend-probe-agrees-with-its-sets
  (check-probe (mem/memory-kv-backend {:space [::member-memory]}) "memory"))

(deftest dense-backend-probe-agrees-with-its-sets
  ;; the one where the two ops are genuinely different code: a handle set is an
  ;; `IntPostings`, so the probe is a binary search or a bitmap test and `kv-members`
  ;; builds a Clojure set
  (let [b (dense/dense-kv-backend {:space [::member-dense]})]
    (check-probe b "dense")
    (p/kv-clear! b)
    (testing "past the int[] → RoaringBitmap promotion, where the probe switches structure"
      (dotimes [i (* 4 postings/promote)] (p/kv-add-to-set b [:functor-root 'hot] (* 2 i)))
      (is (> (p/kv-count b [:functor-root 'hot]) postings/promote) "the posting is a bitmap")
      (probe-agrees b "dense/roaring" [[:functor-root 'hot]]
                    (vec (range 0 (* 8 postings/promote) 7))))
    (p/kv-clear! b)))

(deftest dense-roots-probe-agrees-with-its-sets
  ;; every routed family, plus the fallback the label keys land in — and a term the shared
  ;; dictionary has never interned, which has no posting to probe at all
  (let [b (dr/dense-roots (tok/token-dict))]
    (check-probe b "dense-roots")
    (is (not (p/kv-member? b [:term-index 'NeverInterned] 1))
        "an unknown term is a false, not a lookup")))

(deftest disk-backend-probe-agrees-with-its-sets
  (let [dir (str (Files/createTempDirectory "vaelii-member-" (into-array FileAttribute [])))]
    (try
      (let [b (dkv/open-kv-backend dir)]
        (check-probe b "disk")
        (dkv/close! b))
      (finally
        (doseq [f (reverse (file-seq (java.io.File. dir)))] (.delete ^java.io.File f))))))

;; ---- the overlay ----------------------------------------------------------
;; The merge rule, read off the overlay's raw bookkeeping rather than out of the decorator
;; — an oracle that shares no code with what it is checking.  The reserved keys are spelled
;; in full because they are private to `vaelii.impl.overlay.kv`, and a test that reached for
;; them through the ns would be reading the implementation it is meant to be independent of.

(def ^:private cleared-key      :vaelii.impl.overlay.kv/cleared)
(def ^:private deleted-keys-key :vaelii.impl.overlay.kv/deleted-keys)
(defn- removed-key [k] [:vaelii.impl.overlay.kv/removed k])

(defn- ref-members
  "`(base(K) ∪ overlay(K)) − removed(K)`, with `base(K)` empty when K is tombstoned or the
  whole overlay is cleared."
  [ov base k]
  (let [own (p/kv-members ov k)]
    (if (or (some? (p/kv-get ov cleared-key))
            (contains? (p/kv-members ov deleted-keys-key) k))
      own
      (set/difference (into (p/kv-members base k) own)
                      (p/kv-members ov (removed-key k))))))

(def ^:private base-content
  '{[:functor-root untouched]  #{1 2 3}          ; inherited whole, never touched by the fork
    [:functor-root extended]   #{10 11}          ; inherited and added to
    [:functor-root partial]    #{20 21 22}       ; inherited, one member recorded as removed
    [:functor-root emptied]    #{30 31}          ; inherited, every member removed
    [:functor-root tombed]     #{40 41}          ; whole key deleted in the fork
    [:functor-root readded]    #{50 51}          ; deleted, then repopulated fresh
    [:functor-root roundtrip]  #{60 61}          ; a member removed and then put back
    [:functor-root shareda]    #{1 20 40 60}     ; two keys that actually overlap, so an
    [:functor-root sharedb]    #{20 40 99}       ;   intersection over them is not vacuous
    [:exception-index :rules]  #{70 71}          ; the roster, edited across the protocol
    [:trie :children [p0]]     #{tok0 tok1}})    ; a non-handle family

(def ^:private fork-keys
  (vec (concat (keys base-content)
               '[[:functor-root forkonly]        ; the overlay's alone
                 [:functor-root absent]])))      ; neither side ever held it

(defn- edit-fork!
  "One edit of every shape the merge rule distinguishes."
  [f]
  (p/kv-add-to-set      f '[:functor-root extended] 12)
  (p/kv-remove-from-set f '[:functor-root partial] 21)
  (doseq [m [30 31]] (p/kv-remove-from-set f '[:functor-root emptied] m))
  (p/kv-delete          f '[:functor-root tombed])
  (p/kv-delete          f '[:functor-root readded])
  (p/kv-add-to-set      f '[:functor-root readded] 55)
  (p/kv-remove-from-set f '[:functor-root roundtrip] 60)
  (p/kv-add-to-set      f '[:functor-root roundtrip] 60)   ; the removal record empties again
  (p/kv-remove-from-set f '[:functor-root shareda] 20)     ; narrows the overlap to {40}
  (p/kv-add-to-set      f '[:functor-root sharedb] 60)     ; and widens it back to {40 60}
  (p/kv-add-to-set      f '[:functor-root forkonly] 80)
  (p/kv-remove-from-set f '[:exception-index :rules] 70)
  (p/kv-add-to-set      f '[:exception-index :rules] 72)
  (p/kv-add-to-set      f '[:trie :children [p0]] 'tok2)
  (p/kv-remove-from-set f '[:trie :children [p0]] 'tok0))

(def ^:private intersect-combos
  "Key groups a fork narrows over — `sentexes-with-args` intersects the
  predicate-scoped argument roots — picked to span what the fast path splits on.  The
  `shareda`/`sharedb` pair carries it: every key inherited before `edit-fork!`, both edited
  after, so the same combos take the base's own narrowing on one pass and the merged fold
  on the next.  Beside it, the shapes that must not take the fast path — a tombstoned side,
  an overlay-only side, a key neither side holds — plus a cross-family pair whose members
  cannot even be the same *kind* of thing, a three-key fold, and the pair reversed, since
  the narrowing reorders by size and must not depend on the caller's order."
  '[[[:functor-root shareda] [:functor-root sharedb]]
    [[:functor-root shareda] [:functor-root sharedb] [:functor-root untouched]]
    [[:functor-root sharedb] [:functor-root shareda]]
    [[:functor-root shareda] [:functor-root roundtrip]]
    [[:functor-root tombed] [:functor-root shareda]]
    [[:functor-root forkonly] [:functor-root extended]]
    [[:functor-root shareda] [:functor-root absent]]
    [[:exception-index :rules] [:functor-root shareda]]
    [[:trie :children [p0]] [:functor-root shareda]]
    [[:functor-root shareda]]])

(defn- check-intersections
  "`kv-intersect` on the fork against the same independent rule.  Its own check because a
  fork whose keys are *all* inherited hands the whole narrowing to the base — a different
  path from the merged fold, and the one nearly every read on a fork takes."
  [f ov base label]
  (doseq [combo intersect-combos]
    (is (= (reduce set/intersection (map #(ref-members ov base %) combo))
           (p/kv-intersect f combo))
        (str label ": intersect " (pr-str combo)))))

(defn- check-merged
  "Members, cardinality and membership on the fork, each against the independent rule."
  [f ov base label ks]
  (doseq [k ks]
    (let [expect (ref-members ov base k)]
      (is (= expect (p/kv-members f k)) (str label ": members " (pr-str k)))
      (is (= (count expect) (p/kv-count f k)) (str label ": count " (pr-str k)))
      (doseq [m (if (= '[:trie :children [p0]] k)
                  '[tok0 tok1 tok2 tok9]
                  [1 2 3 10 11 12 20 21 22 30 31 40 41 50 51 55 60 61 70 71 72 80 99])]
        (is (= (contains? expect m) (boolean (p/kv-member? f k m)))
            (str label ": " (pr-str k) " ∋ " (pr-str m)))))))

(defn- run-overlay-arm [raw-base label]
  (p/kv-clear! raw-base)
  (doseq [[k ms] base-content, m ms] (p/kv-add-to-set raw-base k m))
  (let [ov   (doto (mem/memory-kv-backend {:space [::member-fork]}) (p/kv-clear!))
        base (frozen/frozen-kv raw-base)
        f    (okv/overlay-kv ov base)]
    (testing (str label ": a fork that has written nothing is its base, exactly")
      (check-merged f ov base label fork-keys)
      (check-intersections f ov base label))
    (edit-fork! f)
    (testing (str label ": and every shape the merge rule distinguishes")
      (check-merged f ov base label fork-keys)
      (check-intersections f ov base label))
    (testing (str label ": a wholesale clear hides the base without emptying it")
      (p/kv-clear! f)
      (check-merged f ov base label fork-keys)
      (p/kv-add-to-set f '[:functor-root untouched] 7)      ; usable again, base still hidden
      (p/kv-add-to-set f '[:exception-index :rules] 73)
      (check-merged f ov base label fork-keys)
      (check-intersections f ov base label))
    (p/kv-clear! ov)
    (p/kv-clear! raw-base)))

(deftest a-fork-over-a-flat-map-base-merges-and-probes-by-the-rule
  (run-overlay-arm (mem/memory-kv-backend {:space [::member-ovbase]}) "overlay/memory"))

(deftest a-fork-over-a-dense-base-merges-and-probes-by-the-rule
  ;; The configuration the fast path exists for: the base's `kv-members` builds a Clojure
  ;; set out of an `IntPostings`, so a fork that merged in order to count would pay for the
  ;; whole inherited posting on every selectivity read.  Correctness must be identical to
  ;; the flat-map arm, which is what running the same rule over both says.
  (run-overlay-arm (dense/dense-kv-backend {:space [::member-ovdense]}) "overlay/dense"))

(deftest a-fork-inherits-its-bases-answers-without-merging-them
  ;; The fast-path claim itself, stated behaviourally: on a key the fork has never touched
  ;; the merged answer is the base's own, member for member and count for count — including
  ;; the roster, which is what `exception-rule?` probes through the protocol.
  (let [raw  (doto (dense/dense-kv-backend {:space [::member-inherit]}) (p/kv-clear!))
        _    (doseq [i (range 400)] (p/kv-add-to-set raw [:functor-root 'wide] i))
        _    (doseq [i (range 5)]   (p/kv-add-to-set raw [:exception-index :rules] i))
        ov   (doto (mem/memory-kv-backend {:space [::member-inherit-fork]}) (p/kv-clear!))
        base (frozen/frozen-kv raw)
        f    (okv/overlay-kv ov base)]
    (is (= 400 (p/kv-count f [:functor-root 'wide])))
    (is (= (p/kv-members raw [:functor-root 'wide]) (p/kv-members f [:functor-root 'wide])))
    (is (p/kv-member? f [:exception-index :rules] 3))
    (is (not (p/kv-member? f [:exception-index :rules] 9)))
    (testing "and one write to the key does not change any of those answers"
      (p/kv-add-to-set f [:functor-root 'wide] 1000)
      (is (= 401 (p/kv-count f [:functor-root 'wide])))
      (is (p/kv-member? f [:functor-root 'wide] 1000))
      (is (p/kv-member? f [:functor-root 'wide] 399)))
    (p/kv-clear! ov)
    (p/kv-clear! raw)))
