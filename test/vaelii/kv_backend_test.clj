;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.kv-backend-test
  "The `KvBackend` contract: one behavioral spec every adapter must satisfy, so a
  new backend (disk, SQL, overlay) is a drop-in the moment it passes this.

  `KvIndexStore` (`vaelii.impl.kv`) is written once over this protocol, so its
  behavior is exactly as portable as the ops below are.  Two arms run the same
  `check-backend` spec: the in-memory adapter directly, and whatever backend the
  suite is configured for (memory by default, the on-disk WAL under
  `VAELII_TEST_BACKEND=disk-log`), reached through a real KB so the clear teardown is
  handled for us.  Green on both is the proof both satisfy the contract."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(defn check-backend
  "The full spec, run against one `KvBackend`.  Uses its own keyspace and clears it
  at both ends, so it is safe on a shared store.

  Public because it is *the* adapter contract: `overlay_test` runs it against the
  overlay decorator over an empty base, which is the claim that a fork of nothing
  behaves exactly like the thing it forked."
  [b]
  (p/kv-clear! b)
  (testing "scalar upsert — set, overwrite, read, delete"
    (is (nil? (p/kv-get b [:s :a])) "absent scalar reads nil")
    (p/kv-put b [:s :a] {:x 1})
    (is (= {:x 1} (p/kv-get b [:s :a])) "a Clojure value round-trips")
    (p/kv-put b [:s :a] {:x 2})
    (is (= {:x 2} (p/kv-get b [:s :a])) "a second set overwrites")
    (p/kv-delete b [:s :a])
    (is (nil? (p/kv-get b [:s :a])) "delete removes it"))

  (testing "counters — incr/decr return the post-op value"
    (is (= 1 (p/kv-increment b [:c :n])) "first incr from absent is 1")
    (is (= 2 (p/kv-increment b [:c :n])))
    (is (= 1 (p/kv-decrement b [:c :n])) "decr returns the new value")
    (is (= 0 (p/kv-decrement b [:c :n])))
    ;; Every counter key this index writes is a cardinality — how many sentexes live
    ;; under a trie prefix — and `plan/prefix-estimate` divides by them, so the floor is
    ;; part of the contract rather than an accident of one adapter's arithmetic.  An
    ;; adapter that lets one go negative passes every other line here and hands the
    ;; planner a number that means nothing.
    (testing "a decrement at zero holds the floor rather than going negative"
      (is (= 0 (p/kv-decrement b [:c :n])) "at zero it stays at zero")
      (is (= 0 (p/kv-decrement b [:c :never])) "and an absent counter decrements to zero")
      (is (= 1 (p/kv-increment b [:c :n])) "the floor is a floor, not a stuck key")
      (p/kv-delete b [:c :never])))

  (testing "sets — add/remove/members/card, every member type intact"
    (p/kv-add-to-set b [:put 1] 1970)          ; a number, not "1970"
    (p/kv-add-to-set b [:put 1] :rule)         ; a keyword, not "rule"
    (p/kv-add-to-set b [:put 1] 'foo)          ; a symbol
    (is (= #{1970 :rule 'foo} (p/kv-members b [:put 1])) "types survive the round trip")
    (is (= 3 (p/kv-count b [:put 1])))
    (p/kv-add-to-set b [:put 1] 1970)          ; re-add is idempotent (set semantics)
    (is (= 3 (p/kv-count b [:put 1])))
    (p/kv-remove-from-set b [:put 1] :rule)
    (is (= #{1970 'foo} (p/kv-members b [:put 1])))
    (testing "membership — the same answer as the set, one probe instead of a set"
      ;; nothing above compares the two ops, and on a backend that packs a posting they
      ;; are different code paths entirely; `kv_membership_test` is the differential
      (is (p/kv-member? b [:put 1] 1970))
      (is (p/kv-member? b [:put 1] 'foo))
      (is (not (p/kv-member? b [:put 1] :rule))  "a member that was removed")
      (is (not (p/kv-member? b [:put 1] 'bar))   "one that was never there")
      (is (not (p/kv-member? b [:never] 1970))   "and a key that was never written"))
    (testing "an emptied set is indistinguishable from an absent one"
      (p/kv-remove-from-set b [:put 1] 1970)
      (p/kv-remove-from-set b [:put 1] 'foo)
      (is (= #{} (p/kv-members b [:put 1])))
      (is (zero? (p/kv-count b [:put 1])))
      (is (not (p/kv-member? b [:put 1] 1970)))))

  (testing "N-key intersection"
    (doseq [m '[a b c]] (p/kv-add-to-set b [:i 1] m))
    (doseq [m '[b c d]] (p/kv-add-to-set b [:i 2] m))
    (doseq [m '[b c e]] (p/kv-add-to-set b [:i 3] m))
    (is (= '#{b c} (p/kv-intersect b [[:i 1] [:i 2]])) "two-key intersect")
    (is (= '#{b c} (p/kv-intersect b [[:i 1] [:i 2] [:i 3]])) "three-key intersect")
    (is (= '#{a b c} (p/kv-intersect b [[:i 1]])) "single-key intersect is the set itself")
    (is (= #{} (p/kv-intersect b [])) "no keys intersect to empty"))

  (testing "batch — mixed writes as one unit, one reply per op in order"
    (let [replies (p/kv-batch b [[:increment [:b :n]]          ; 0 -> 1
                                 [:increment [:b :n]]          ; 1 -> 2
                                 [:add-to-set [:b :s] 7]        ; (non-counter reply ignored)
                                 [:decrement [:b :n]]          ; 2 -> 1
                                 [:put  [:b :v] :hello]
                                 [:remove-from-set [:b :s] 7]])]     ; empties the set
      (is (= 6 (count replies)) "one reply per op")
      (is (= 1 (long (nth replies 0))) "first incr reply is the new value")
      (is (= 2 (long (nth replies 1))))
      (is (= 1 (long (nth replies 3))) "decr reply is the new value, positionally aligned"))
    (testing "every op in the batch actually took effect"
      (is (= :hello (p/kv-get b [:b :v])) "the :put landed")
      (is (zero? (p/kv-count b [:b :s])) "the :add-to-set then :remove-from-set cancelled to empty")
      (is (= 2 (long (p/kv-increment b [:b :n]))) "the counter settled at 1 (incr,incr,decr)"))
    ;; An op no adapter recognizes is `:unknown-frame` on **every** adapter, and it is a
    ;; contract rather than an implementation detail: on the disk backend a write op is
    ;; also a WAL frame, so an unreadable one is a log written by some other build and a
    ;; build that cannot read a log has to be able to say so by name rather than delete
    ;; it.  `case`'s own IllegalArgumentException carries no `:type`, and a caller
    ;; discriminating on one must not have to know which adapter it reached.
    (testing "an op no fold recognizes is refused by name, not by `case`"
      (let [e (is (thrown? clojure.lang.ExceptionInfo
                           (p/kv-batch b [[:frobnicate [:b :v] 1]])))]
        (is (= :unknown-frame (:type (ex-data e))))
        (is (= :frobnicate (:op (ex-data e))) "and names the op it could not read"))))

  (testing "entries out, entries back in — the projection a dump is written from"
    ;; The one operation whose *shape* is shared rather than private: a backend may hold
    ;; a set as int postings or a key as an interned long, and `kv-entries` has to undo
    ;; both.  So the property is a round trip through a cleared store, not a peek at the
    ;; representation — and afterwards ordinary writes must still work, which is what a
    ;; `kv-put` of a raw set would break on a backend that packs them.
    (p/kv-clear! b)
    (p/kv-add-to-set b [:term-index 'foo] 11)
    (p/kv-add-to-set b [:term-index 'foo] 12)
    (p/kv-add-to-set b [:context-root 'CxA] 11)
    (p/kv-put b [:trie :count []] 2)
    (let [snapshot (into #{} (p/kv-entries b))]
      (is (= 3 (count snapshot)) "every key, once")
      (is (contains? snapshot [[:term-index 'foo] #{11 12}])
          (str "a handle set does not come back as a set: " (pr-str snapshot)))
      (p/kv-clear! b)
      (is (empty? (p/kv-entries b)))
      (p/kv-load b snapshot)
      (is (= snapshot (into #{} (p/kv-entries b))) "and back in unchanged")
      (is (= #{11 12} (p/kv-members b [:term-index 'foo])) "readable through the ordinary reads")
      (is (= 2 (long (p/kv-get b [:trie :count []]))))
      (testing "a loaded entry is in the backend's own representation, not a foreign value"
        (p/kv-add-to-set b [:term-index 'foo] 13)
        (is (= #{11 12 13} (p/kv-members b [:term-index 'foo]))))))

  ;; The predicate-scoped argument roots are the one key family an adapter may hold
  ;; hierarchically rather than as a flat key→set entry (`vaelii.impl.memory`'s counted
  ;; `::arg` trie, which the dense and columnar roots delegate to).  So every op on this
  ;; family has **two** folds — the protocol method and the `kv-batch` arm — and the
  ;; contract is that they agree with each other and with what a flat map answers.  A
  ;; whole-posting `:put` and a `:delete` are the two that only the hierarchical layout
  ;; has to think about, and the two the index's own writes never issue on this family,
  ;; so nothing else in the suite would notice one adapter refusing them.
  (testing "argument roots — the hierarchical family answers the flat contract"
    (p/kv-clear! b)
    (let [k1 [:argument-root 'p 1 'A]
          k2 [:argument-root 'q 1 'A]]                 ; same (pos, term), another predicate
      (p/kv-add-to-set b k1 11)
      (p/kv-add-to-set b k1 12)
      (p/kv-add-to-set b k2 13)
      (is (= #{11 12} (p/kv-members b k1)))
      (testing "kv-delete drops the whole scoped posting and nothing beside it"
        (p/kv-delete b k1)
        (is (= #{} (p/kv-members b k1)))
        (is (zero? (p/kv-count b k1)))
        (is (not (p/kv-member? b k1 11)))
        (is (nil? (p/kv-get b k1)))
        (is (= #{} (p/kv-intersect b [k1 k2])))
        (is (empty? (filter #(= k1 (first %)) (p/kv-entries b)))
            "and leaves no dangling posting for a dump or a snapshot to carry")
        (is (= #{13} (p/kv-members b k2))
            "the predicate beside it under the same (pos, term) keeps its handles"))
      (testing "the same delete inside a batch is the same delete"
        (p/kv-add-to-set b k1 11)
        (p/kv-batch b [[:delete k1]])
        (is (= #{} (p/kv-members b k1)))
        (is (= #{13} (p/kv-members b k2))))
      (testing "a whole-posting put installs exactly that posting, in either fold"
        (p/kv-put b k1 #{21 22})
        (is (= #{21 22} (p/kv-members b k1)))
        (p/kv-batch b [[:put k1 #{31}]])
        (is (= #{31} (p/kv-members b k1)) "the second put replaces rather than unions")
        (is (= #{13} (p/kv-members b k2))))
      (testing "and writing under a deleted key again is an ordinary write"
        (p/kv-delete b k1)
        (p/kv-add-to-set b k1 41)
        (is (= #{41} (p/kv-members b k1)))
        (is (= #{41} (p/kv-intersect b [k1]))
            "the posting is back, and every read of it agrees"))))

  (p/kv-clear! b)
  (is (nil? (p/kv-get b [:c :n])) "clear wipes everything"))

(deftest memory-backend-satisfies-the-contract
  ;; a dedicated db number, isolated from the KB registries the suite uses
  (check-backend (mem/memory-kv-backend {:space 991})))

(deftest a-bulk-load-takes-only-its-own-backend-s-writes
  ;; `with-bulk-writes` binds a transient for ONE backend on the current thread.  A
  ;; write this thread makes to another MemoryKvBackend while the load runs — a second
  ;; KB's index, a chaining callback asserting elsewhere — must land on that backend's
  ;; own atom, visible at once, rather than on the loaded backend's transient, where it
  ;; would be persisted into the wrong map at the end of the load.
  (let [loaded (doto (mem/memory-kv-backend {:space 993}) (p/kv-clear!))
        other  (doto (mem/memory-kv-backend {:space 994}) (p/kv-clear!))]
    (try
      (mem/with-bulk-writes loaded
        (p/kv-put loaded [:s :mine] 1)
        (p/kv-add-to-set loaded [:set :mine] 7)
        (p/kv-put other [:s :theirs] 2)
        (p/kv-add-to-set other [:set :theirs] 8)
        (p/kv-increment other [:c :theirs])
        (testing "the other backend's writes are on its own atom, mid-load"
          (is (= 2 (p/kv-get other [:s :theirs])))
          (is (= #{8} (p/kv-members other [:set :theirs])))
          (is (= 1 (p/kv-get other [:c :theirs]))))
        (testing "and none of them leaked into the loaded backend's reads"
          (is (nil? (p/kv-get loaded [:s :theirs])))))
      (testing "after the load, each backend holds exactly what was written to it"
        (is (= 1 (p/kv-get loaded [:s :mine])))
        (is (= #{7} (p/kv-members loaded [:set :mine])))
        (is (nil? (p/kv-get loaded [:s :theirs])) "the other backend's scalar did not persist here")
        (is (empty? (p/kv-members loaded [:set :theirs])))
        (is (= 2 (p/kv-get other [:s :theirs])))
        (is (nil? (p/kv-get other [:s :mine]))))
      (finally
        (p/kv-clear! loaded)
        (p/kv-clear! other)))))

(deftest a-bulk-load-refuses-to-discard-a-write-that-landed-under-it
  ;; The accumulator is a transient taken off an atom held per **space**, which every
  ;; index store over that space shares — so installing it with a `reset!` writes over
  ;; whatever reached the atom while the batch was accumulating, and the loss is silent.
  ;; A second bulk load stacked over this one is the way to get there with no second
  ;; thread: its install lands on the atom, and the outer batch, which snapshotted before
  ;; it started, wipes it.  The install is a compare-and-set against that snapshot, so the
  ;; batch says the state moved instead of discarding it.
  (let [b (doto (mem/memory-kv-backend {:space 995}) (p/kv-clear!))]
    (try
      (let [d (try (mem/with-bulk-writes b
                     (p/kv-put b [:s :batch] 1)
                     ;; something else reaches the shared atom mid-batch
                     (reset! (:state b) {[:s :other] 2}))
                   nil
                   (catch clojure.lang.ExceptionInfo e (ex-data e)))]
        (is (= :stacked-batch (:type d))
            "the batch reports the collision rather than installing over it"))
      (testing "and what landed under the batch is still there"
        (is (= 2 (p/kv-get b [:s :other])))
        (is (nil? (p/kv-get b [:s :batch]))
            "the refused batch installed nothing, so neither map is half applied"))
      (finally (p/kv-clear! b)))))

(deftest suite-backend-satisfies-the-contract
  ;; whatever the suite runs on — the in-memory backend by default, the on-disk WAL
  ;; under VAELII_TEST_BACKEND=disk-log — reached through a real KB so the clear teardown
  ;; is handled.  Redundant with the arm above under the default memory run, which is
  ;; the point: it never demands infrastructure the run does not have.
  (tu/with-cleared-kb [kb tu/fresh]
    ;; a `KvIndexStore` exposes its backend as `:backend`; the columnar index keeps its
    ;; native trie and delegates the flat families to a key-interning backend under
    ;; `:roots` — either way the suite reaches a real `KvBackend` and runs the contract.
    (let [b (or (:backend (:index kb)) (:roots (:index kb)))]
      (is (satisfies? p/KvBackend b) "the index rests on a KvBackend")
      (check-backend b))))

(deftest deleting-a-stored-sentexs-argument-root-leaves-the-store-consistent
  ;; The argument roots are a **derived** family: `[:argument-root pred pos term] →
  ;; handles`, written beside the trie and read by the multi-column probe.  Losing one is
  ;; not hypothetical — a crash inside the index write persists a prefix of the batch, and
  ;; `vaelii.impl.reindex` repairs by dropping and rewriting postings — so the claim worth
  ;; pinning is what the store answers in between: the probe under that column answers
  ;; *nothing*, never a handle whose posting is gone, and every other family the sentex is
  ;; filed under still answers.  Then the ordinary write path puts it back.
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [rel A B CxCtx]
      (let [idx (:index kb)
            bk  (or (:backend idx) (:roots idx))
            h   (v/assert kb (list rel A B) CxCtx)]
        (is (= #{h} (set (p/sentexes-with-args idx rel [[1 A]])))
            "the argument-root probe answers before the delete")
        (p/kv-delete bk [:argument-root rel 1 A])
        (testing "the probe answers empty rather than a handle with no posting"
          (is (= #{} (set (p/sentexes-with-args idx rel [[1 A]]))))
          (is (= #{} (set (p/sentexes-with-args idx rel [[1 A] [2 B]])))
              "and the multi-column probe intersects to empty, not to the surviving column"))
        (testing "every other family the sentex is filed under still answers"
          (is (= #{h} (set (p/sentexes-with-args idx rel [[2 B]])))
              "the other argument column")
          (is (contains? (set (p/sentexes-with-functor idx rel)) h) "the functor root")
          (is (contains? (p/leaf-at idx (sx/path (v/sentex kb h))) h) "the trie leaf")
          (is (some? (v/sentex kb h)) "and the record itself"))
        (testing "and an ordinary retract-and-assert rebuilds the posting"
          (v/retract! kb h)
          (let [h2 (v/assert kb (list rel A B) CxCtx)]
            (is (= #{h2} (set (p/sentexes-with-args idx rel [[1 A]]))))
            (is (= #{h2} (set (p/sentexes-with-args idx rel [[1 A] [2 B]])))
                "both columns, so the delete left nothing stale to intersect against")))))))

;; ---- pipelining: the index write is one batch, args is one sinter -------
;; A KvBackend decorator counting the two required ops.  The count is at the
;; protocol, so it is backend-independent: a backend is free to make `kv-batch`
;; one round trip and `kv-intersect` one server-side intersection, so one call = one
;; round trip.  Proving KvIndexStore issues exactly one of each is what keeps the hot
;; path off a round-trip-per-op regression.

(defrecord CountingBackend [inner counts]
  p/KvBackend
  (kv-batch  [_ ops] (swap! counts update :batch inc)  (p/kv-batch inner ops))
  (kv-intersect [_ ks]  (swap! counts update :sinter inc) (p/kv-intersect inner ks))
  (kv-get      [_ k]   (p/kv-get inner k))
  (kv-put      [_ k v] (p/kv-put inner k v))
  (kv-delete      [_ k]   (p/kv-delete inner k))
  (kv-increment     [_ k]   (p/kv-increment inner k))
  (kv-decrement     [_ k]   (p/kv-decrement inner k))
  (kv-add-to-set     [_ k m] (p/kv-add-to-set inner k m))
  (kv-remove-from-set     [_ k m] (p/kv-remove-from-set inner k m))
  (kv-members [_ k]   (p/kv-members inner k))
  (kv-member? [_ k m] (p/kv-member? inner k m))
  (kv-count    [_ k]   (p/kv-count inner k))
  (kv-entries  [_]     (p/kv-entries inner))
  (kv-load     [_ es]  (p/kv-load inner es))
  (kv-clear!   [_]     (p/kv-clear! inner)))

(deftest the-index-write-is-one-batch-and-args-is-one-sinter
  (tu/with-neutral-kb [kb tu/fresh]        ; only to build real sentexes; nothing stored
    (let [inner  (doto (mem/memory-kv-backend {:space 992}) (p/kv-clear!))
          counts (atom {:batch 0 :sinter 0})
          store  (kv/->KvIndexStore (->CountingBackend inner counts))]
      (tu/with-terms [rel A B C Ctx]
        (let [sx (res/kb-sentex kb (list rel A B C) Ctx)]
          (testing "index-sentex — the whole path, roots, and term index in one batch"
            (p/index-sentex store sx 42)
            (is (= 1 (:batch @counts))))
          (testing "sentexes-with-args — one intersection of the functor and argument roots"
            (p/sentexes-with-args store rel [[1 A] [2 B]])
            (is (= 1 (:sinter @counts))))
          (testing "unindex-sentex — two batches (decrement pass, then the delete pass)"
            (p/unindex-sentex! store sx 42)
            (is (= 3 (:batch @counts)) "one index + two unindex batches")))))))

;; ---- the exact leaf, and what asking for a match instead costs -----------

(deftest leaf-at-reads-the-node-the-path-names-where-lookup-matches
  ;; `lookup` reads a variable in the path as a wildcard, so an α-renamed key — which is
  ;; what every non-ground sentex is stored under — matches the whole extent of its shape.
  ;; `leaf-at` reads the one node instead.  The two agree exactly on a ground path, which
  ;; is what lets `find-sentex-handle` take the cheap one unconditionally.
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [rel A B C D CxCtx]
      (let [idx  (:index kb)
            sxs  (mapv #(res/kb-sentex kb (list rel (first %) (second %)) CxCtx)
                       [[A B] [C D]])]
        (doseq [[i sx] (map-indexed vector sxs)] (p/index-sentex idx sx (+ 900 i)))
        (try
          (testing "a ground path: the leaf is the match, handle for handle"
            (let [pth (sx/path (first sxs))]
              (is (= #{900} (p/leaf-at idx pth)))
              (is (= (p/lookup idx pth) (p/leaf-at idx pth)))))
          (testing "an open path: the match fans the shape, the leaf holds only its own"
            (let [pth (sx/path (res/kb-sentex kb (list rel '?x '?y) CxCtx))]
              (is (= #{900 901} (p/lookup idx pth)) "both facts match the pattern")
              (is (= #{} (p/leaf-at idx pth))
                  "and neither is stored at the pattern's own α-renamed key")))
          (finally
            (doseq [[i sx] (map-indexed vector sxs)]
              (p/unindex-sentex! idx sx (+ 900 i)))))))))

;; A RecordStore decorator counting the fetches a call makes.  The count is at the
;; protocol, so it says the same thing on a RAM store and on a paged one — where
;; each fetch is a positional read and a nippy thaw past the LRU.
(defrecord CountingRecords [inner fetches]
  p/RecordStore
  (get-sentex [_ id] (swap! fetches inc) (p/get-sentex inner id))
  (put-sentex [_ sx] (p/put-sentex inner sx))
  (delete-sentex! [_ id] (p/delete-sentex! inner id))
  (put-justification [_ d] (p/put-justification inner d))
  (get-justification [_ id] (p/get-justification inner id))
  (delete-justification! [_ id] (p/delete-justification! inner id))
  (next-id [_] (p/next-id inner))
  (put-provenance [_ id pv] (p/put-provenance inner id pv))
  (get-provenance [_ id] (p/get-provenance inner id))
  (delete-provenance! [_ id] (p/delete-provenance! inner id))
  (sentex-ids [_] (p/sentex-ids inner))
  (justification-ids [_] (p/justification-ids inner))
  (mark-premise [_ id s] (p/mark-premise inner id s))
  (unmark-premise! [_ id] (p/unmark-premise! inner id))
  (premise-ids [_] (p/premise-ids inner))
  (premise-strength [_ id] (p/premise-strength inner id))
  (clear-records! [_] (p/clear-records! inner)))

(deftest a-dedup-probe-costs-one-leaf-read-and-not-the-extent
  ;; `handle-of` and `why-not` are public — and RPC ops and CLI commands — so the pattern
  ;; is the caller's to choose.  Asking the trie for a *match* of an open one fans over
  ;; every stored sentex of that shape and reads the record of each to tell them apart;
  ;; asking for the leaf the key names reads the one node and nothing else.
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [rel CxCtx]
      (dotimes [i 40]
        (v/assert kb (list rel (symbol (str "Tmpleft" i)) (symbol (str "Tmpright" i))) CxCtx))
      (let [fetches (atom 0)
            counted (assoc kb :records (->CountingRecords (:records kb) fetches))]
        (testing "an open pattern nothing is stored under reads no records at all"
          (reset! fetches 0)
          (is (nil? (v/handle-of counted (list rel '?x '?y) CxCtx)))
          (is (zero? @fetches)
              "one leaf read answered it — a match would have read all forty"))
        (testing "and a ground sentence is still found, off the same leaf"
          (reset! fetches 0)
          (is (some? (v/handle-of counted (list rel 'Tmpleft7 'Tmpright7) CxCtx))))))))
