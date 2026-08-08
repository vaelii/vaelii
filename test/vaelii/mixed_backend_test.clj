;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.mixed-backend-test
  "The mixed modes — durable records with a **derived** index in RAM (`:disk-memory`,
  `:disk-dense`, `:disk-columnar`) — and the record/index axis split they fall out of.

  The claim under test is that the index need not be persisted at all: it is a function
  of the records, `reindex` recomputes every entry of it, and a KB that recomputes it on
  open answers exactly as one that read it back off disk.  So the tests here are about
  the *seam* rather than about either store: what the two axes resolve to, that a
  records-only open writes no index, that reopening rebuilds, and that the rebuild
  happens before the recovery that reads it.

  Engine-level parity across every mode is `backend_parity_test`'s job (it runs the same
  scripted session on all seven), and the thorough gate is the whole suite under
  `VAELII_TEST_BACKEND=disk-memory` / `=disk-dense` / `=disk-columnar`."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.disk.backend :as backend]
            [vaelii.impl.disk.index-snapshot :as snap]
            [vaelii.impl.kb :as kb])
  (:import [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(defn- tmpdir ^String []
  (str (Files/createTempDirectory "vaelii-mixed-" (into-array FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (java.io.File. dir)))] (.delete ^java.io.File f)))

(defn- with-tmp
  "Run `(f dir)` in a fresh temp directory, closing whatever disk stores were opened on
  it and deleting it afterwards."
  [f]
  (let [dir (tmpdir)]
    (try (f dir)
         (finally (backend/close-dir! dir) (rm-rf! dir)))))

(defn- copy-dir!
  "Copy every file under `from` into a fresh temp directory, and return it."
  ^String [^String from]
  (let [to   (tmpdir)
        root (.toPath (io/file from))]
    (doseq [^java.io.File f (file-seq (io/file from)) :when (.isFile f)]
      (let [dst (io/file to (str (.relativize root (.toPath f))))]
        (io/make-parents dst)
        (io/copy f dst)))
    to))

(defn- with-restart
  "Build a KB in a fresh directory with `(build! dir)`, close it, **copy the directory**,
  and run `(check! copy built)` against the copy.

  The copy is what makes this a real restart.  A derived index is shared for the life of
  the JVM under the identity of the records it belongs to, so reopening the same
  directory in-process finds the RAM index still populated and would prove nothing about
  rebuilding it; a copied directory shares no in-process state, which is exactly what a
  new process finds.  It also tests the stronger claim directly: the bytes in that
  directory are the whole KB."
  [build! check!]
  (with-tmp
    (fn [dir]
      (let [built (build! dir)]
        (backend/close-dir! dir)
        (let [copy (copy-dir! dir)]
          (try (check! copy built)
               (finally (backend/close-dir! copy) (rm-rf! copy))))))))

(defn- populate!
  "A small KB exercising every derived structure the index holds: the trie (facts), the
  taxonomy roots (genl edges), the rule index (a forward rule, and the conclusion it
  derives), the argument roots and the term index."
  [kb]
  (v/assert kb '(genl dog animal) 'MixedContext {:strength :monotonic})
  (v/assert kb '(genl animal thing) 'MixedContext {:strength :monotonic})
  (v/assert-rule kb '[(dog ?x)] '(mammal ?x) 'MixedContext)
  (v/assert kb '(dog Muffet) 'MixedContext {:strength :monotonic})
  (v/assert kb '(cat Tom) 'MixedContext {:strength :monotonic})
  (v/assert kb '(ownerOf Ann Muffet) 'MixedContext {:strength :monotonic})
  kb)

(defn- observations
  "Everything a reopened KB must answer identically — handle-free, since handles are an
  allocation order.  Spans storage (the term index), belief (the TMS), the taxonomy, and
  derivation (the rule's conclusion and its proof)."
  [kb]
  {:dogs      (set (map :sentence (v/sentexes-matching kb '(dog ?x) 'MixedContext)))
   :owner     (set (map :sentence (v/sentexes-matching kb '(ownerOf ?who Muffet) 'MixedContext)))
   :mammals   (set (map :sentence (v/sentexes-matching kb '(mammal ?x) 'MixedContext)))
   :isa       [(v/isa? kb 'Muffet 'animal) (v/isa? kb 'Muffet 'thing) (v/isa? kb 'Tom 'animal)]
   :specs     (v/specs kb 'animal)
   :terms     (set (map :sentence (v/find-sentexes kb 'Muffet)))
   :count     (v/sentex-count kb)
   :ask       (set (map #(dissoc % :handle) (v/ask kb '(animal ?x) 'MixedContext)))
   :why-rule  (-> (v/why kb (v/handle-of kb '(mammal Muffet) 'MixedContext))
                  :support first :rule)})

;; ---- the axis split -------------------------------------------------------

(deftest the-two-axes-are-selectable-independently
  (testing ":records / :index name the halves directly, with no :backend sugar"
    (let [kb (v/open-kb {:records :memory :index :columnar
                         :space 88 :recover? false})]
      (v/clear! kb)
      (populate! kb)
      (is (= #{'(dog Muffet)} (:dogs (observations kb))))
      (v/clear! kb)))
  (testing "an explicit axis opt overrides its half of the sugar"
    (let [kb (v/open-kb {:backend :memory-columnar :index :memory
                         :space 88 :recover? false})]
      (v/clear! kb)
      (is (instance? vaelii.impl.memory.MemoryKvBackend (:backend (:index kb)))
          ":index :memory won over :memory-columnar's columnar half"))))

(deftest an-unknown-selection-names-the-axis-it-belongs-to
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unknown KB backend"
                        (v/open-kb {:backend :nonesuch})))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unknown record backend .* :memory or :disk"
                        (v/open-kb {:records :nonesuch :index :memory})))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo
                        #"unknown index backend .* :memory, :dense, :columnar, or :disk"
                        (v/open-kb {:records :memory :index :nonesuch}))))

(deftest one-number-names-both-of-a-KBs-stores
  ;; The index is a function of the records, so the two are shared or separate as one
  ;; thing: `:space` keys both, and each backend keys a registry of its own, so there is
  ;; no spelling for a private index over shared records — the arrangement in which a
  ;; second KB's open finds a populated index over records it does not hold, drops it as
  ;; stale, and leaves the first KB unable to find sentexes it is still holding.
  (let [a (doto (v/open-kb {:space 289 :recover? false}) v/clear!)]
    (try
      (let [h (v/assert a '(dog Muffet) 'MixedContext {:strength :monotonic})
            b (v/open-kb {:space 289 :recover? false})]
        (is (= h (v/handle-of b '(dog Muffet) 'MixedContext))
            "the second KB reads the first's postings, because it holds the records too")
        (is (= h (v/handle-of a '(dog Muffet) 'MixedContext))
            "and the first still finds its own sentex — nothing was dropped under it")
        (is (= h (v/assert a '(dog Muffet) 'MixedContext {:strength :monotonic}))
            "so asserting it again finds that sentex rather than minting a second handle")
        (is (= 1 (v/sentex-count a))))
      (finally (v/clear! a)))))

(deftest two-space-numbers-are-two-stores
  ;; What every other KB in one process depends on:
  ;; a KB named by its own space holds its own records, and flushing one leaves the
  ;; other whole.  That is what makes a second KB usable for holding one relation apart
  ;; from the KB it came out of — the flush that empties it runs while the first is full.
  (let [a (v/open-kb {:space 88 :recover? false})
        b (v/open-kb {:space 188 :recover? false})]
    (try
      (v/clear! a)
      (v/clear! b)
      (populate! a)
      (v/assert b '(cat Tom) 'MixedContext {:strength :monotonic})
      (let [held (v/sentex-count a)]
        (is (pos? held))
        (is (= 1 (v/sentex-count b)) "b holds its own one fact, not a's as well")
        (v/clear! b)
        (is (zero? (v/sentex-count b)))
        (is (= held (v/sentex-count a)) "b's flush emptied b, and only b")
        (is (= #{'(dog Muffet)} (:dogs (observations a)))))
      (finally (v/clear! a) (v/clear! b)))))

(deftest an-option-nothing-reads-is-refused-rather-than-ignored
  ;; The one class of wrong opt that cannot announce itself downstream.  An unknown
  ;; `:backend` throws and an impossible axis pair throws, but a *misspelt* key is one
  ;; nothing looks at: the KB would open on the default space, and the test above would
  ;; then be two names for one store — a's records flushed by b's construction, every
  ;; read after it answering out of a store the caller never meant to touch.  A KB that
  ;; took the default reads identically to one that asked for it, so the opts map is the
  ;; last place the mistake is still legible.
  (testing "the key is named, and so is every key that would have been read"
    (let [e (is (thrown? clojure.lang.ExceptionInfo
                         (v/open-kb {:backend :memory :record-db 188 :index-db 189})))]
      (is (= :unknown-option (:type (ex-data e))))
      (is (= [:index-db :record-db] (:unknown (ex-data e))) "both, not just the first")
      (is (re-find #":space" (ex-message e))
          "the message lists what open-kb does read, so the right spelling is in it")))
  (testing "a near-miss on a flag is refused too — nothing here is optional"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unknown open-kb option :recovery\?"
                          (v/open-kb {:space 88 :recovery? false}))))
  (testing "a fork's own storage opts are held to the same set"
    (let [base (v/open-kb {:space 88 :recover? false})]
      (try
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unknown :overlay option :record-db"
                              (v/fork base {:record-db 7})))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unknown :base option :record-db"
                              (v/open-kb {:backend :overlay
                                          :base    {:backend :memory :record-db 7}
                                          :overlay {:backend :memory :space 188}})))
        (finally (v/clear! base)))))
  ;; A key added to the constructor and not to the roster is refused, which says so at
  ;; once; a key left in the roster after nothing reads it is accepted and ignored, which
  ;; is the bug this whole test is about.  So the roster is pinned: it shrinks on purpose.
  (testing "and the roster is exactly the vocabulary"
    (is (= #{:backend :records :index :space :dir :tms :recover?
             :naming :constraints :base :base-stores :overlay}
           kb/opt-keys))))

(deftest a-mount-or-durability-key-without-its-axis-is-refused
  ;; All four keys are in the roster, so `check-opts!` passes them — but each is read
  ;; only under the axis selection it belongs to.  `{:backend :memory :base-stores …}`
  ;; opens a plain RAM KB with nothing mounted, and `{:backend :memory :dir …}` names
  ;; a directory nothing writes: the caller who asked for durability loses the store
  ;; at JVM exit, behind an open that looked exactly like the durable one.
  (testing ":base / :base-stores / :overlay need an :overlay axis"
    (doseq [extra [{:base-stores {}} {:base {:backend :memory}} {:overlay {}}]]
      (let [e (is (thrown? clojure.lang.ExceptionInfo
                           (v/open-kb (merge {:backend :memory :space 88}
                                             extra)))
                  (str (pr-str extra) " is refused"))]
        (is (= :unknown-option (:type (ex-data e))))
        (is (= (vec (keys extra)) (:unknown (ex-data e))))
        (is (re-find #":overlay" (ex-message e)) "the message names the fix"))))
  (testing ":dir needs a :disk half"
    (let [e (is (thrown? clojure.lang.ExceptionInfo
                         (v/open-kb {:backend :memory :space 88
                                     :dir "/tmp/vaelii-nowhere"})))]
      (is (= :unknown-option (:type (ex-data e))))
      (is (= [:dir] (:unknown (ex-data e))))
      (is (re-find #":disk" (ex-message e)) "the message says how durability is asked for"))
    (testing "and an :overlay half is held to its own axes"
      (let [base (v/open-kb {:space 88 :recover? false})]
        (try
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"no half is :disk"
                                (v/fork base {:dir "/tmp/vaelii-nowhere"}))
              "an ephemeral fork naming a directory is the same silent evaporation")
          (finally (v/clear! base))))))
  (testing "the selections that do read the keys still open"
    (with-tmp
      (fn [dir]
        (let [kb (v/open-kb {:backend :disk-memory :dir dir :recover? false})]
          (is (some? kb))
          (v/clear! kb))))))

(deftest recover-takes-one-of-four-settings-and-refuses-the-rest
  ;; The key is in the roster, so `check-opts!` passes it — the *value* is the check,
  ;; and it has to be a refusal.  Reading an unnamed setting as the warn branch hands
  ;; back an empty TMS over a store that is not empty, which answers [] to everything:
  ;; a wrong answer where a refusal is owed.
  (testing "the four the roster names all open"
    (doseq [mode [:auto true :warn false]]
      (let [kb (v/open-kb {:space 88 :recover? mode})]
        (is (some? kb) (str (pr-str mode) " opens"))
        (v/clear! kb))))
  (testing "and anything else is refused, naming what it does read"
    (doseq [bad [:yes :recover "auto" 1]]
      (let [e (is (thrown? clojure.lang.ExceptionInfo
                           (v/open-kb {:space 88 :recover? bad}))
                  (str (pr-str bad) " is refused"))]
        (is (= :unknown-option (:type (ex-data e))))
        (is (re-find #":warn" (ex-message e)) "the message carries the roster"))))
  (testing "an explicit nil is refused too, and says it is not the default"
    (let [e (is (thrown? clojure.lang.ExceptionInfo
                         (v/open-kb {:space 88 :recover? nil})))]
      (is (= :unknown-option (:type (ex-data e))))
      (is (re-find #"omit the key" (ex-message e))
          "since :or does not fire on a present nil, the message has to say so"))))

(deftest ram-records-cannot-take-the-durable-index
  ;; The one pairing of the eight the axes admit that is refused rather than named: the
  ;; index is derived from the records, so persisting it over a store that empties at JVM
  ;; exit leaves index files describing records that are gone — and the next open answers
  ;; every query out of them.  Refused on both spellings, since `backend-axes` is the one
  ;; place either arrives at a pair.
  (testing "spelled on the axes"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"the :disk index needs :disk records"
                          (v/open-kb {:records :memory :index :disk}))))
  (testing "spelled as a half-override of a name"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"the :disk index needs :disk records"
                          (v/open-kb {:backend :memory :index :disk})))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"the :disk index needs :disk records"
                          (v/open-kb {:backend :disk :records :memory}))))
  (testing "and no name spells it"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unknown KB backend"
                          (v/open-kb {:backend :memory-disk})))))

;; ---- records durable, index derived ---------------------------------------

(deftest a-derived-index-writes-nothing-and-rebuilds-on-restart
  (doseq [mode [:disk-memory :disk-dense :disk-columnar]]
    (testing (str mode)
      (with-restart
        (fn [dir]
          (let [before (observations (populate! (v/open-kb {:backend mode :dir dir :recover? false})))]
            (testing "the durable directory holds records and nothing else"
              (is (.isDirectory (io/file dir "records")) "the records are on disk")
              ;; unless the mapped image is on, which writes one `index/` directory and
              ;; is a *cache* of the derived index rather than a second ground truth —
              ;; that it can be deleted at any moment and the KB still answers is
              ;; `index_snapshot_test`'s question, not this file's
              (when-not (snap/enabled?)
                (is (not (.exists (io/file dir "index")))
                    "and no index was written — it is derived state")))
            before))
        (fn [dir before]
          (testing "reopening rebuilds the index from the records and answers identically"
            (let [kb (v/open-kb {:backend mode :dir dir :recover? :auto})]
              (is (= before (observations kb)))
              (when-not (snap/enabled?)
                (is (not (.exists (io/file dir "index")))
                    "still nothing written on the index side")))))))))

(deftest a-restart-is-recoverable-only-because-the-reindex-runs-first
  ;; This is the ordering the mixed modes turn on.  `recover` rebuilds the TMS and
  ;; taxonomy *by reading the index* (`rebuild-taxonomy` reads the functor root), so over
  ;; a derived index that opened empty it recovers an empty KB and reports nothing wrong.
  (with-restart
    (fn [dir] (observations (populate! (v/open-kb {:backend :disk-memory :dir dir :recover? false}))))
    (fn [dir before]
      (let [kb (v/open-kb {:backend :disk-memory :dir dir :recover? false})]
        (testing "recover alone, over an index that opened empty, recovers nothing"
          (v/recover kb)
          (is (empty? (v/sentexes-matching kb '(dog ?x) 'MixedContext)))
          (is (not (v/isa? kb 'Muffet 'animal))))
        (testing "reindex-then-recover — what :recover? :auto runs — restores it whole"
          (v/reindex kb)
          (is (= before (observations kb))))))))

(deftest the-records-stay-writable-after-a-rebuilt-open
  ;; A reindexed KB is not merely readable: the handle counter, the premise set and the
  ;; rule index all came back, so the next write chains and retracts like any other.
  (with-restart
    (fn [dir] (populate! (v/open-kb {:backend :disk-memory :dir dir :recover? false})) nil)
    (fn [dir _]
      (let [kb (v/open-kb {:backend :disk-memory :dir dir :recover? :auto})]
        (v/assert kb '(dog Rex) 'MixedContext {:strength :monotonic})
        (is (seq (v/sentexes-matching kb '(mammal Rex) 'MixedContext))
            "the recovered rule fired over the new fact")
        (is (= 2 (count (v/sentexes-matching kb '(dog ?x) 'MixedContext)))
            "and the new record did not land on an existing handle")
        (v/retract! kb (v/handle-of kb '(dog Muffet) 'MixedContext))
        (is (empty? (v/sentexes-matching kb '(mammal Muffet) 'MixedContext))
            "retraction reaches a conclusion the rebuilt justification graph carries")))))

;; ---- crossing between a durable and a derived index -----------------------

(deftest a-disk-kb-restarts-as-disk-memory
  (with-restart
    (fn [dir] (observations (populate! (v/open-kb {:backend :disk :dir dir :recover? false}))))
    (fn [dir before]
      (testing "the durable index is simply ignored; the RAM one is rebuilt from the records"
        (let [kb (v/open-kb {:backend :disk-memory :dir dir :recover? :auto})]
          (is (= before (observations kb)))
          (is (= #{:records} (backend/opened dir))
              "and the disk index was never opened"))))))

(deftest a-disk-memory-kb-restarted-as-disk-needs-an-explicit-reindex
  ;; The reverse crossing is not symmetric, and deliberately so — under `:recover?
  ;; false`, which is what this test opens with.  That setting is a caller asking to read
  ;; what is stored and do no work on open, so the durable side keeps its contract and
  ;; the one-time migration is their explicit `reindex`.  Under `:auto` the same short
  ;; index is repaired instead: the record count tells an index that was never written
  ;; apart from one that is merely empty, and a torn `kv.log` tail arrives at the same
  ;; state with no crossing and no caller to know a `reindex` is owed.
  (with-restart
    (fn [dir] (observations (populate! (v/open-kb {:backend :disk-memory :dir dir :recover? false}))))
    (fn [dir before]
      (let [kb (v/open-kb {:backend :disk :dir dir :recover? false})]
        (is (empty? (v/sentexes-matching kb '(dog ?x) 'MixedContext))
            "the disk index for these records was never written")
        (v/reindex kb)
        (is (= before (observations kb)) "and one reindex populates it")
        (testing "durably — a further restart of the same directory rebuilds nothing"
          (backend/close-dir! dir)
          (let [kb2 (v/open-kb {:backend :disk :dir dir :recover? :auto})]
            (is (= before (observations kb2)))))))))

(deftest a-derived-index-outliving-its-records-is-dropped
  ;; The hazard the identity above creates: the RAM index is keyed by the directory, so
  ;; emptying that directory out from under it (closing, deleting and reopening in one
  ;; JVM) would otherwise leave an index describing records that no longer exist.
  (with-tmp
    (fn [dir]
      (populate! (v/open-kb {:backend :disk-memory :dir dir :recover? false}))
      (backend/close-dir! dir)
      (rm-rf! dir)
      (let [kb (v/open-kb {:backend :disk-memory :dir dir :recover? :auto})]
        (is (zero? (v/sentex-count kb)) "the stale index went with the records")
        (is (empty? (v/sentexes-matching kb '(dog ?x) 'MixedContext)))
        ;; and the store is usable, at handles nothing else claims
        (v/assert kb '(dog Muffet) 'MixedContext {:strength :monotonic})
        (is (= 1 (count (v/sentexes-matching kb '(dog ?x) 'MixedContext))))))))

(deftest one-directory-opened-both-ways-shares-records-and-not-the-index
  ;; The registry is keyed by directory *and component*: a second KB over the same dir
  ;; must reuse the record store (one lock, one set of file handles, one ground truth)
  ;; while a RAM-index mode must not be handed the durable index the other opened.
  (with-tmp
    (fn [dir]
      (let [kb1 (populate! (v/open-kb {:backend :disk :dir dir :recover? false}))
            kb2 (v/open-kb {:backend :disk-memory :dir dir :recover? :auto})]
        (is (identical? (:records kb1) (:records kb2)) "one record store")
        (is (not (identical? (:index kb1) (:index kb2))) "two index stores")
        (is (instance? vaelii.impl.memory.MemoryKvBackend (:backend (:index kb2)))
            "and the second KB's is the RAM one it asked for")
        (is (= (observations kb1) (observations kb2))
            "which the reindex-on-open filled to say the same thing")))))
