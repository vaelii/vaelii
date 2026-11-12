;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bulk-sink-test
  "`protocols/BulkLoading` — the protocol an `import!` writes its records through, so a store
  with an ingest path faster than a record at a time can use it.

  The engine's own stores do not implement it: a `put-sentex` on the RAM and disk
  backends is already a map assoc or a batched WAL append, and there is nothing a bulk
  path could save.  So the capability is tested here against a **wrapper that defers every
  write to its `close`**, which is what makes the two properties that matter provable
  without a database in the room:

  - **the KB is the same one.**  The same dump, imported into a store that bulk-loads and
    one that does not, in all three `:belief?` modes — compared as knowledge, not as calls;
  - **nothing is read back before the close.**  A sink owns its buffer until then, so a
    loader that fetched a record it had just written would see a hole.  The wrapper's
    `get-sentex` **throws** on a handle still buffered, which turns that contract from a
    docstring into a failing test.

  A store with no capability is the third property and the default one: the sink is
  `put-sentex` per record and the premise mark the caller would have made, which is the
  loop the import paths ran before this protocol was in the world."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.io.export :as export]
            [vaelii.impl.io.import :as imp]
            [vaelii.impl.protocols :as p]
            [vaelii.test-util :as tu]))

;;; ── scaffolding ───────────────────────────────────────────────────────

;;; ── a store that bulk-loads ───────────────────────────────────────────

(defn- deferred-sink
  "A `RecordSink` that holds every record until `close` and only then writes it to
  `inner` — the visibility a real bulk sink has (a `COPY` lands when the copy ends), made
  absolute so a read-back would fail rather than merely be slow.

  It mints and returns the handle itself, which is the half of the protocol that lets the
  import path index a record it has not stored yet."
  [inner log buffered kind {:keys [premises?] :or {premises? true}}]
  (let [pending (atom [])]
    (reify
      p/RecordSink
      (write-record! [_ rec]
        (let [id  (long (or (:id rec) (p/next-id inner)))
              rec (assoc rec :id id)]
          (swap! pending conj rec)
          (swap! buffered conj id)
          (swap! log update kind (fnil conj []) id)
          id))

      java.io.Closeable
      (close [_]
        (doseq [rec @pending]
          (if (= kind :sentex)
            (do (p/put-sentex inner rec)
                (when (and premises? (:strength rec))
                  (p/mark-premise inner (:id rec) (:strength rec))))
            (p/put-justification inner rec)))
        (swap! buffered #(reduce disj % (map :id @pending)))
        (reset! pending [])
        nil))))

(defn- bulk-store
  "`inner` with `BulkLoading` and `BulkAnnotating` bolted on, logging every handle each
  sink was handed and every batch annotate it was asked for.  A reify rather than a redef,
  for `prefetch_test`'s reason: a protocol method dispatches on the value's type, so only a
  real implementation is in a compiled caller's path."
  [inner log]
  (let [buffered (atom #{})]
    (reify
      p/RecordStore
      (put-sentex [_ sx] (p/put-sentex inner sx))
      (get-sentex [_ id]
        (when (contains? @buffered id)
          (throw (ex-info (str "read of handle " id " while a sink still held it")
                          {:type :read-through-an-open-sink :handle id})))
        (p/get-sentex inner id))
      (delete-sentex! [_ id] (p/delete-sentex! inner id))
      (put-justification [_ d] (p/put-justification inner d))
      (get-justification [_ id]
        (when (contains? @buffered id)
          (throw (ex-info (str "read of handle " id " while a sink still held it")
                          {:type :read-through-an-open-sink :handle id})))
        (p/get-justification inner id))
      (delete-justification! [_ id] (p/delete-justification! inner id))
      (next-id [_] (p/next-id inner))
      (put-provenance [_ id prov] (p/put-provenance inner id prov))
      (get-provenance [_ id] (p/get-provenance inner id))
      (delete-provenance! [_ id] (p/delete-provenance! inner id))
      (sentex-ids [_] (p/sentex-ids inner))
      (justification-ids [_] (p/justification-ids inner))
      (mark-premise [_ id s] (p/mark-premise inner id s))
      (unmark-premise! [_ id] (p/unmark-premise! inner id))
      (premise-ids [_] (p/premise-ids inner))
      (premise-strength [_ id] (p/premise-strength inner id))
      (clear-records! [_] (p/clear-records! inner))

      p/BulkLoading
      (open-sentex-sink [_ opts] (deferred-sink inner log buffered :sentex opts))
      (open-justification-sink [_ opts] (deferred-sink inner log buffered :justification opts))

      p/BulkAnnotating
      (mark-premise-batch [_ id->strength]
        (swap! log update :mark-batches (fnil conj []) (into (sorted-map) id->strength))
        (doseq [[id st] id->strength] (p/mark-premise inner id st))
        nil)
      (put-provenance-batch [_ entries]
        (swap! log update :prov-batches (fnil conj []) (mapv first entries))
        (doseq [[id prov] entries] (p/put-provenance inner id prov))
        nil))))

;;; ── the content, and what is observed of it ───────────────────────────

(defn- load!
  "Facts at two strengths, a rule that derives from them, a defeasible pair a monotonic
  fact defeats, and a retraction — so the dump under import carries premises,
  derivations, justifications and a handle whose record is gone."
  [kb]
  (v/assert kb '(isa Muffet DomesticCat) 'CxBulk {:strength :monotonic})
  (v/assert kb '(isa Tom DomesticCat) 'CxBulk {:strength :monotonic})
  (v/assert kb '(genls DomesticCat Cat) 'CxBulk {:strength :monotonic})
  (v/assert-rule kb ['(isa ?x DomesticCat)] '(likes ?x Milk) 'CxBulk {})
  (v/assert kb '(isa Rex Dog) 'CxBulk)
  (let [h (v/assert kb '(isa Spot Dog) 'CxBulk)]
    (v/retract! kb h))
  kb)

(defn- observation
  "What this KB knows, by content — a handle is a number the loader minted and only the
  preservation test is about those."
  [kb]
  (let [hs (v/handles kb)]
    {:count     (count hs)
     :sentences (set (for [h hs] [(:sentence (v/sentex kb h))
                                  (:context (v/sentex kb h))
                                  (:strength (v/sentex kb h))]))
     :believed  (set (for [h hs :when (v/in? kb h)]
                       [(:sentence (v/sentex kb h)) (:context (v/sentex kb h))]))
     :milk      (set (v/ask kb '(likes ?x Milk) 'CxBulk))
     :cats      (set (v/ask kb '(isa ?x Cat) 'CxBulk))
     :terms     (set (v/terms kb))
     :premises  (set (for [h (p/premise-ids (:records kb))]
                       [(:sentence (v/sentex kb h)) (p/premise-strength (:records kb) h)]))
     :prov      (set (for [h hs :when (v/provenance kb h)]
                       [(:sentence (v/sentex kb h)) (set (keys (v/provenance kb h)))]))}))

(defn- fresh [] (v/open-kb {:backend :memory :space (gensym "bulksink")}))

(defn- with-dump
  "Build a KB, export it, and call `(f dump)`."
  [f]
  (let [dir (tu/temp-dir "vaelii-bulk-" "dump" "-")]
    (tu/rm-rf! dir)                                    ; export! makes its own directory
    (try
      (let [source (load! (fresh))]
        (export/export! source dir {:compression :none})
        (f dir source))
      (finally (tu/rm-rf! dir)))))

;;; ── the engine cannot tell ────────────────────────────────────────────

(deftest a-store-that-bulk-loads-imports-the-same-kb
  (doseq [belief [true :stored false]]
    (testing (str ":belief? " (pr-str belief))
      (with-dump
        (fn [dump _source]
          (let [plain  (fresh)
                log    (atom {})
                bulked (let [kb (fresh)] (assoc kb :records (bulk-store (:records kb) log)))
                s-p    (imp/import-dump plain dump {:belief? belief})
                s-b    (imp/import-dump bulked dump {:belief? belief})]
            (is (= (dissoc s-p :duration-ms) (dissoc s-b :duration-ms))
                "the same summary — the same records read, stored and refused")
            (is (= (observation plain) (observation bulked))
                "and the same knowledge, however the records got there")
            (testing "every record went through a sink and none through put-sentex"
              (is (= (set (v/handles bulked)) (set (:sentex @log)))
                  "every stored sentex handle was one a sink was handed")
              (is (= (count (v/handles bulked)) (count (:sentex @log)))
                  "and handed exactly once")
              (when (not= false belief)
                (is (= (set (p/justification-ids (:records bulked)))
                       (set (:justification @log)))
                    "and every justification too")))
            (testing "the sink took the premise marks and the annotate call the provenance"
              (is (nil? (:mark-batches @log))
                  "no premise batch: the marks rode the records, and a dump with no
                   collapse leaves no handle whose strength differs from its record's")
              (if (= false belief)
                (is (nil? (:prov-batches @log))
                    "the records-only path reads no provenance")
                (is (seq (:prov-batches @log))
                    "and the provenance stream went through the batch, chunked")))))))))

(deftest a-sink-owns-its-records-until-it-closes
  ;; The wrapper throws on a read of a handle a sink still holds, so this passing is the
  ;; assertion: no import path fetches a record back inside the pass that wrote it.  It
  ;; is the property the protocol is a *sink* for — a loader that had to read back could not
  ;; use one, and would want a batched put whose handles it waits for instead.
  (doseq [belief [true :stored false]]
    (testing (str ":belief? " (pr-str belief))
      (with-dump
        (fn [dump _source]
          (let [log    (atom {})
                bulked (let [kb (fresh)] (assoc kb :records (bulk-store (:records kb) log)))]
            (is (map? (imp/import-dump bulked dump {:belief? belief}))
                "the import ran without reading through an open sink")))))))

(deftest the-handles-come-back-through-a-sink-too
  ;; A dump of ours numbers its records, and preserving those numbers is what lets an
  ;; index be replayed rather than rebuilt.  The handle is decided caller-side and the
  ;; sink is told, so it survives — which is the reason the protocol can be a sink at all.
  (with-dump
    (fn [dump source]
      (let [log    (atom {})
            bulked (let [kb (fresh)] (assoc kb :records (bulk-store (:records kb) log)))
            s      (imp/import-dump bulked dump {:belief? true})]
        (is (= :preserved (:handle-policy s)))
        (is (= (set (v/handles source)) (set (v/handles bulked)))
            "the same numbers, not merely the same knowledge")
        (is (= (into (sorted-map) (for [h (v/handles source)] [h (:sentence (v/sentex source h))]))
               (into (sorted-map) (for [h (v/handles bulked)] [h (:sentence (v/sentex bulked h))])))
            "and each number naming what it named")))))

(deftest the-annotate-helpers-fall-back-to-one-write-at-a-time
  ;; `BulkAnnotating`'s two helpers are called unconditionally by the import path, so on a
  ;; store that implements nothing they have to be the loop they replace — the same guard
  ;; and the same end state, including the refusal to mark a handle with no record.
  (let [kb (fresh)
        rs (:records kb)]
    (is (not (satisfies? p/BulkAnnotating rs)) "the RAM record store annotates one at a time")
    (let [a (p/put-sentex rs {:sentence '(rel A) :context 'CxBulk})
          b (p/put-sentex rs {:sentence '(rel B) :context 'CxBulk})]
      (cap/mark-premises rs {a :monotonic, b :default, 99999 :default})
      (is (= #{a b} (set (p/premise-ids rs)))
          "a handle with no record is not marked, exactly as `mark-premise` refuses it")
      (is (= [:monotonic :default] [(p/premise-strength rs a) (p/premise-strength rs b)]))
      (cap/put-all-provenance rs [[a {:by "ann"}] [b {:by "bob"}]])
      (is (= [{:by "ann"} {:by "bob"}] [(p/get-provenance rs a) (p/get-provenance rs b)]))
      (testing "and an empty batch is a no-op rather than an error"
        (cap/mark-premises rs {})
        (cap/put-all-provenance rs [])
        (is (= #{a b} (set (p/premise-ids rs))))))))

(deftest the-delete-helpers-fall-back-to-one-write-at-a-time
  (let [rs (:records (fresh))]
    (is (not (satisfies? p/BulkDeleting rs)) "the RAM record store deletes one at a time")
    (let [[a b c] (mapv #(p/put-sentex rs {:sentence (list 'rel %) :context 'CxBulk}) '[A B C])
          j       (p/put-justification rs {:informant :premise :consequence a :antecedents []})]
      (cap/delete-sentexes rs [a b 99999])
      (is (= [nil nil] [(p/get-sentex rs a) (p/get-sentex rs b)]))
      (is (some? (p/get-sentex rs c)) "a handle not named stays")
      (cap/delete-justifications rs [j])
      (is (nil? (p/get-justification rs j)))
      (testing "and an empty batch is a no-op rather than an error"
        (cap/delete-sentexes rs [])
        (cap/delete-justifications rs [])
        (is (some? (p/get-sentex rs c)))))))

(deftest a-store-without-the-capability-loads-through-the-loop
  ;; The default half of the protocol, and the one every backend the engine ships takes: no
  ;; `BulkLoading`, so `sentex-sink` answers `put-sentex` per record and the premise mark
  ;; the caller would have made.  Asserted here rather than left to the other tests,
  ;; because it is the path a store takes on the day it implements nothing.
  (let [kb (fresh)]
    (is (not (satisfies? p/BulkLoading (:records kb)))
        "the RAM record store bulk-loads nothing")
    (with-open [^java.io.Closeable sink (cap/sentex-sink (:records kb) {:premises? true})]
      (let [h (p/write-record! sink {:sentence '(rel A) :context 'CxBulk :strength :default})]
        (is (integer? h))
        (is (= '(rel A) (:sentence (p/get-sentex (:records kb) h)))
            "and a record written through it is readable at once, since there is no buffer")
        (is (contains? (set (p/premise-ids (:records kb))) h)
            "`:premises? true` adds the record to the premise set")))
    (testing ":premises? false leaves the mark to the caller"
      (with-open [^java.io.Closeable sink (cap/sentex-sink (:records kb) {:premises? false})]
        (let [h (p/write-record! sink {:sentence '(rel B) :context 'CxBulk :strength :default})]
          (is (not (contains? (set (p/premise-ids (:records kb))) h))))))))
