;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.mixed-backend-test
  "The mixed modes — durable records with a **derived** index in RAM (`:disk-memory`,
  `:disk-dense`, `:disk-columnar`) — and the record/index axis split they fall out of.

  The claim under test is that the index need not be persisted at all: it is a function
  of the records, `reindex` recomputes every entry of it, and a KB that recomputes it on
  open answers exactly as one that read it back off disk.  So the tests here are about
  the *protocol* rather than about either store: what the two axes resolve to, that a
  records-only open writes no index, that reopening rebuilds, and that the rebuild
  happens before the recovery that reads it.

  Engine-level parity across every mode is `backend_parity_test`'s job (it runs the same
  scripted session on every name `kb/backend-names` carries, or says what covers the one
  it skips), and the thorough regression test is the whole suite under
  `VAELII_TEST_BACKEND=disk-memory` / `=disk-dense` / `=disk-columnar`.

  The **backend list's other two readers** are tested at the bottom of this namespace: the
  suite's configuration list, which is bash, and docs/storage.md's table, which is prose.
  Neither can be reached from `kb`'s own load-time validator, and a backend missing from
  either ships untested or undocumented without a single test going red."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [are deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.disk.backend :as backend]
            [vaelii.impl.disk.files :as dfiles]
            [vaelii.impl.disk.lock :as lock]
            [vaelii.impl.kb :as kb]
            [vaelii.test-util :as tu]))

(defn- with-tmp
  "Run `(f dir)` in a fresh temp directory, closing whatever disk stores were opened on
  it and deleting it afterwards."
  [f]
  (let [dir (tu/tmpdir "vaelii-mixed-")]
    (try (f dir)
         (finally (backend/close-dir! dir) (tu/rm-rf! dir)))))

(defn- copy-dir!
  "Copy every file under `from` into a fresh temp directory, and return it."
  ^String [^String from]
  (let [to   (tu/tmpdir "vaelii-mixed-")
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
               (finally (backend/close-dir! copy) (tu/rm-rf! copy))))))))

(defn- populate!
  "A small KB exercising every derived structure the index holds: the trie (facts), the
  taxonomy roots (genl edges), the rule index (a forward rule, and the conclusion it
  derives), the argument roots and the term index."
  [kb]
  (v/assert kb '(genl dog animal) 'CxMixed {:strength :monotonic})
  (v/assert kb '(genl animal thing) 'CxMixed {:strength :monotonic})
  (v/assert-rule kb '[(dog ?x)] '(mammal ?x) 'CxMixed {:direction :forward})
  (v/assert kb '(dog Muffet) 'CxMixed {:strength :monotonic})
  (v/assert kb '(cat Tom) 'CxMixed {:strength :monotonic})
  (v/assert kb '(ownerOf Ann Muffet) 'CxMixed {:strength :monotonic})
  kb)

(defn- observations
  "Everything a reopened KB must answer identically — handle-free, since handles are an
  allocation order.  Spans storage (the term index), belief (the TMS), the taxonomy, and
  derivation (the rule's conclusion and its proof)."
  [kb]
  {:dogs      (set (map :sentence (v/sentexes-matching kb '(dog ?x) 'CxMixed)))
   :owner     (set (map :sentence (v/sentexes-matching kb '(ownerOf ?who Muffet) 'CxMixed)))
   :mammals   (set (map :sentence (v/sentexes-matching kb '(mammal ?x) 'CxMixed)))
   :isa       [(v/isa? kb 'Muffet 'animal) (v/isa? kb 'Muffet 'thing) (v/isa? kb 'Tom 'animal)]
   :specs     (v/specs kb 'animal)
   :terms     (set (map :sentence (v/find-sentexes kb 'Muffet)))
   :count     (v/sentex-count kb)
   :ask       (set (map #(dissoc % :handle) (v/ask kb '(animal ?x) 'CxMixed)))
   :why-rule  (let [w (v/why kb (v/handle-of kb '(mammal Muffet) 'CxMixed))]
                (-> w :nodes (get (:root w)) :support first :rule))})

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

(defn- adapters-failing
  "Run `f` with each sibling adapter's namespace failing to load by throwing `(thrown)`.
  A `checkouts/` link or a `+with-` profile can put an adapter on this classpath, so an
  absence claim states the absence instead of reading it off the classpath."
  [thrown f]
  (let [resolve requiring-resolve]
    (with-redefs [requiring-resolve
                  (fn [sym]
                    (if (#{"vaelii.sqlite.record-store" "vaelii.postgres.record-store"}
                         (namespace sym))
                      (throw (thrown))
                      (resolve sym)))]
      (f))))

(defn- absent []
  (java.io.FileNotFoundException. "Could not locate vaelii/x/record_store__init.class"))

(deftest an-unknown-selection-names-the-axis-it-belongs-to
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unknown KB backend"
                        (v/open-kb {:backend :nonesuch})))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unknown record backend .* :memory, :disk, :sqlite or :pg"
                        (v/open-kb {:records :nonesuch :index :memory})))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo
                        #"unknown index backend .* :memory, :dense, :columnar, :snapshot or :disk-log"
                        (v/open-kb {:records :memory :index :nonesuch}))))

(deftest a-backend-refusal-names-the-axis-and-the-kind-under-fixed-keys
  ;; Eleven throws share `:unknown-backend`, and which key held the offending value used
  ;; to be the axis's own name — so a caller read four keys to find the one that was
  ;; there, and had to know all four.  `:axis` and `:kind` are on every throw;
  ;; `:mismatch` says which kind of wrong it is, so a fallback can tell a name nothing
  ;; implements from a pairing that is refused on purpose.
  (testing "a name nothing implements, on each of the four axes"
    (are [opts axis kind] (= {:mismatch :unknown-name :axis axis :kind kind}
                             (select-keys (tu/refusal-data #(v/open-kb opts)) [:mismatch :axis :kind]))
      {:backend :nonesuch}                  :backend :nonesuch
      {:records :nonesuch :index :memory}   :records :nonesuch
      {:records :memory :index :nonesuch}   :index   :nonesuch
      {:backend :memory :tms :nonesuch}     :tms     :nonesuch))
  (testing "a reserved spelling, which names the pairing to take instead"
    (is (= {:mismatch :reserved-name :axis :backend :kind :disk :instead :disk-log}
           (select-keys (tu/refusal-data #(v/open-kb {:backend :disk}))
                        [:mismatch :axis :kind :instead]))))
  (testing "and a pairing both halves of which are legal apart"
    (is (= {:mismatch :illegal-pair :axis :index :kind :disk-log}
           (select-keys (tu/refusal-data #(v/open-kb {:records :memory :index :disk-log}))
                        [:mismatch :axis :kind]))))
  (testing "a fork on one axis alone, which names the other half and :overlay for it"
    (are [opts axis kind]
         (= {:mismatch :illegal-pair :axis axis :kind kind :instead :overlay}
            (select-keys (tu/refusal-data #(v/open-kb opts)) [:mismatch :axis :kind :instead]))
      {:records :overlay :index :memory
       :base {:backend :memory} :overlay {:backend :memory}}  :index   :memory
      {:records :overlay :index :disk-log}                    :index   :disk-log
      {:records :memory :index :overlay}                      :records :memory)))

(deftest a-legal-backend-whose-adapter-is-absent-is-not-an-unknown-one
  ;; `:sqlite` and `:pg` records live in Apache-2.0 siblings the SSPL engine does not
  ;; depend on, so selecting one without the sibling on the classpath refused as
  ;; `:unknown-backend` — and a caller catching that to fall back on `:memory` did the
  ;; wrong thing twice over: the name is legal, and the fix is a coordinate in the
  ;; project rather than a different backend.
  (adapters-failing
   absent
   #(do (are [opts records coord]
             (= {:type :missing-adapter :records records :coordinate coord}
                (select-keys (tu/refusal-data (fn [] (v/open-kb opts))) [:type :records :coordinate]))
          {:backend :sqlite}                                :sqlite "com.vaelii/sqlite"
          {:backend :pg-memory :pg "jdbc:postgresql://h/d"} :pg     "com.vaelii/postgres")
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"com\.vaelii/sqlite"
                              (v/open-kb {:backend :sqlite}))
            "and the message names the coordinate to add")))
  (testing "an adapter whose source loads without its dependencies"
    ;; a `checkouts/` link adds the adapter's source and none of its dependencies
    (adapters-failing
     #(clojure.lang.Compiler$CompilerException.
       "vaelii/postgres/record_store.clj" 1 1
       (java.io.FileNotFoundException. "Could not locate next/jdbc__init.class"))
     #(let [e (is (thrown-with-msg? clojure.lang.ExceptionInfo #"loading it failed .*next/jdbc"
                                    (v/open-kb {:backend :pg-memory :pg "jdbc:postgresql://h/d"})))]
        (is (= {:type :missing-adapter :records :pg :coordinate "com.vaelii/postgres"}
               (select-keys (ex-data e) [:type :records :coordinate])))))))

(deftest one-number-names-both-of-a-KBs-stores
  ;; The index is a function of the records, so the two are shared or separate as one
  ;; thing: `:space` keys both, and each backend keys a registry of its own, so there is
  ;; no spelling for a private index over shared records — the arrangement in which a
  ;; second KB's open finds a populated index over records it does not hold, drops it as
  ;; stale, and leaves the first KB unable to find sentexes it is still holding.
  (let [a (doto (v/open-kb {:space 289 :recover? false}) v/clear!)]
    (try
      (let [h (v/assert a '(dog Muffet) 'CxMixed {:strength :monotonic})
            b (v/open-kb {:space 289 :recover? false})]
        (is (= h (v/handle-of b '(dog Muffet) 'CxMixed))
            "the second KB reads the first's postings, because it holds the records too")
        (is (= h (v/handle-of a '(dog Muffet) 'CxMixed))
            "and the first still finds its own sentex — nothing was dropped under it")
        (is (= h (v/assert a '(dog Muffet) 'CxMixed {:strength :monotonic}))
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
      (v/assert b '(cat Tom) 'CxMixed {:strength :monotonic})
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
  ;; A key added to the constructor and not to the key set is refused, which says so at
  ;; once; a key left in the key set after nothing reads it is accepted and ignored, which
  ;; is the bug this whole test is about.  So the key set is frozen here: it shrinks on purpose.
  (testing "and the key set is exactly the vocabulary"
    (is (= #{:backend :records :index :space :dir :pg :tms :recover?
             :naming :base :base-stores :overlay :oplog? :reasoners :fork-dirs}
           kb/opt-keys))))

(deftest a-store-value-outside-its-domain-is-refused
  ;; The key set above settles which keys are read; this is the value of the three that
  ;; pick the store.  Unchecked, a string space would share the directory of the number
  ;; it prints as, a nil space would key a RAM store apart from space 0, a blank directory
  ;; would put the store in the JVM's working directory, and a :dir or :base-stores of the
  ;; wrong type would reach a protocol call and throw a bare IllegalArgumentException.
  ;; Each is refused before anything opens.
  (letfn [(refused [opts]
            (try (v/close! (v/open-kb opts)) nil
                 (catch clojure.lang.ExceptionInfo e
                   (select-keys (ex-data e) [:type :mismatch :option :value]))))]
    (testing "every value outside a domain is :unknown-option :bad-value, naming the key"
      (doseq [[k opts] [[:space {:space "3"}]
                        [:space {:space nil}]
                        [:space {:space -1}]
                        [:space {:space 1.5}]
                        [:space {:space 3N}]
                        [:space {:space {:a 1}}]
                        [:dir {:backend :disk-log :dir ""}]
                        [:dir {:backend :disk-log :dir "  "}]
                        [:dir {:backend :disk-log :dir (io/file "")}]
                        [:dir {:backend :disk-log :dir 42}]
                        [:dir {:backend :disk-log :dir nil}]
                        [:base-stores {:backend :overlay :base-stores :bogus}]
                        [:base-stores {:backend :overlay :base-stores {:records 1 :index 2}}]]]
        (is (= {:type :unknown-option :mismatch :bad-value :option k :value (get opts k)}
               (refused opts))
            (pr-str opts))))
    (testing "a fork's own halves are held to it too"
      (let [base (v/open-kb {:space 88 :recover? false})]
        (try
          (is (= :space (:option (refused {:backend :overlay
                                           :base-stores {:records (:records base)
                                                         :index   (:index base)}
                                           :overlay {:backend :memory :space "7"}}))))
          (is (= :space (:option (try (v/fork base {:space nil}) nil
                                      (catch clojure.lang.ExceptionInfo e (ex-data e))))))
          (is (= :dir (:option (refused {:backend :overlay
                                         :base    {:backend :disk-log :dir ""}
                                         :overlay {:backend :memory :space 188}}))))
          (finally (v/clear! base)))))
    (testing "a keyword, a symbol or a vector names a private space, and a File a directory"
      (doseq [space [(keyword (str (gensym "h43-space"))) (gensym "h43-space") [::h43 (gensym)]]]
        (let [kb (v/open-kb {:space space :recover? false})]
          (try (is (some? (v/assert kb '(dog Muffet) 'CxMixed)) (pr-str space))
               (finally (v/clear! kb)))))
      (with-tmp
        (fn [dir]
          (let [kb (v/open-kb {:backend :disk-log :dir (io/file dir) :recover? false})]
            (try (is (some? (v/assert kb '(dog Muffet) 'CxMixed)))
                 (finally (v/close! kb)))))))))

(deftest a-mount-or-durability-key-without-its-axis-is-refused
  ;; All four keys are in the key set, so `check-opts!` passes them — but each is read
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
  (testing ":dir needs a durable half"
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
  ;; The key is in the key set, so `check-opts!` passes it — the *value* is the check,
  ;; and it has to be a refusal.  Reading an unnamed setting as the warn branch hands
  ;; back an empty TMS over a store that is not empty, which answers [] to everything:
  ;; a wrong answer where a refusal is owed.
  (testing "the four the check accepts all open"
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
        (is (re-find #":warn" (ex-message e)) "the message carries the accepted settings"))))
  (testing "an explicit nil is refused too, and says it is not the default"
    (let [e (is (thrown? clojure.lang.ExceptionInfo
                         (v/open-kb {:space 88 :recover? nil})))]
      (is (= :unknown-option (:type (ex-data e))))
      (is (re-find #"omit the key" (ex-message e))
          "since :or does not fire on a present nil, the message has to say so"))))

(deftest ram-records-cannot-take-the-log-index
  ;; The log index is derived from the records, so persisting it over a store that
  ;; empties at JVM exit leaves index files describing records that are gone — and the
  ;; next open answers every query out of them.  Refused on both spellings, since
  ;; `backend-axes` is the one place either arrives at a pair.
  (testing "spelled on the axes"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"the :disk-log index needs durable records"
                          (v/open-kb {:records :memory :index :disk-log}))))
  (testing "spelled as a half-override of a name"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"the :disk-log index needs durable records"
                          (v/open-kb {:backend :memory :index :disk-log})))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"the :disk-log index needs durable records"
                          (v/open-kb {:backend :disk-log :records :memory}))))
  (testing "and :sqlite records, whose durable pairing is spelled :disk-log"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"the :disk-log index needs durable records"
                          (v/open-kb {:records :sqlite :index :disk-log}))))
  (testing "and no name spells it"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unknown KB backend"
                          (v/open-kb {:backend :memory-disk})))))

(deftest the-reserved-names-are-refused-and-say-what-to-take
  ;; `:disk` and `:pg-disk` read as *both halves out of core*, which no pairing here is:
  ;; the log index holds its whole map in RAM and the log buys durability.  So they name
  ;; nothing, and are refused rather than pointed at the pairing they sound like — an
  ;; index axis names a directory layout, and a name that answers to two of them opens a
  ;; store in a layout its caller did not ask for.
  (testing "the pairing names"
    (doseq [[nm want] {:disk ":disk-log" :pg-disk ":pg-disk-log"}]
      (let [e (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unknown KB backend"
                                    (v/open-kb {:backend nm}))
                  (str (pr-str nm) " is refused"))]
        (is (= :unknown-backend (:type (ex-data e))))
        (is (re-find (re-pattern want) (ex-message e))
            "the message names the pairing to take instead"))))
  (testing "and the index axis, on either spelling"
    (doseq [opts [{:index :disk} {:backend :disk-memory :index :disk} {:records :disk :index :disk}]]
      (let [e (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unknown index backend :disk"
                                    (v/open-kb opts))
                  (str (pr-str opts) " is refused"))]
        (is (= :disk-log (:instead (ex-data e)))))))
  (testing "and the pairing each refusal names does open"
    (is (= {:records :disk :index :disk-log} (kb/backend-axes {:backend :disk-log})))
    (is (= {:records :disk :index :disk-log} (kb/backend-axes {:records :disk :index :disk-log})))))

(deftest the-pg-axis-needs-a-database-named
  ;; `:pg` is the one axis whose store is not derivable from the KB's own options: a
  ;; directory falls out of `:space`, a database does not.  Both halves of that are
  ;; refused at the entry point rather than discovered from a KB whose records went somewhere
  ;; nobody named.
  (testing ":pg records with no :pg opt"
    (let [e (is (thrown-with-msg? clojure.lang.ExceptionInfo #"needs :pg to name a database"
                                  (v/open-kb {:backend :pg-memory})))]
      (is (= [:pg] (:missing (ex-data e))))))
  (testing "and a :pg that names none — a present nil, an empty map, an empty string"
    ;; `:or` does not fire on a present nil, so silence here would be the default server
    ;; this option exists to refuse.
    (doseq [pg [nil {} ""]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"needs :pg to name a database"
                            (v/open-kb {:backend :pg-memory :pg pg}))
          (str "refused: " (pr-str pg)))))
  (testing "and one that cannot be identified"
    ;; an opaque DataSource names a database the index cannot be keyed by, and both index
    ;; halves are keyed by which database the records are in
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"needs :pg to name a database"
                          (v/open-kb {:backend :pg-memory
                                      :pg (reify javax.sql.DataSource)}))))
  (testing ":pg-disk-log with no :dir"
    ;; the durable index is files on this host describing records on a server; a derived
    ;; default directory is one two KBs over two databases would share
    (let [e (is (thrown-with-msg? clojure.lang.ExceptionInfo #"named no :dir"
                                  (v/open-kb {:backend :pg-disk-log
                                              :pg {:dbtype "postgresql" :dbname "nope"}})))]
      (is (= [:dir] (:missing (ex-data e))))))
  (testing ":pg opt with records that are not :pg"
    (let [e (is (thrown-with-msg? clojure.lang.ExceptionInfo #"nothing connects to that database"
                                  (v/open-kb {:backend :memory :pg {:dbname "nope"}})))]
      (is (= [:pg] (:unknown (ex-data e))))))
  (testing "the adapter is not the engine's to carry"
    ;; selecting :pg reaches the lazy resolve, which finds no adapter — the
    ;; missing-adapter error, not a FileNotFoundException.  The adapter's own suite is
    ;; where a live :pg KB is exercised.
    (adapters-failing
     absent
     #(is (thrown-with-msg? clojure.lang.ExceptionInfo #"needs the vaelii-postgres adapter"
                            (v/open-kb {:backend :pg-memory
                                        :pg {:dbtype "postgresql" :dbname "nope"}}))))))

(deftest a-pg-directory-names-its-server
  ;; a :pg-* directory records the server its index was built against (index/records.edn),
  ;; so a reopen with no :pg reads the server off it and reaches the adapter — made absent,
  ;; so the missing-adapter error rather than the needs-:pg refusal.  A directory with no
  ;; records identity names nothing, and is refused.
  (let [root (.toFile (java.nio.file.Files/createTempDirectory
                       "vaelii-pg-identity" (make-array java.nio.file.attribute.FileAttribute 0)))
        dir  (str root)]
    (try
      (doseq [backend [:pg-snapshot :pg-disk-log]]
        (testing (str backend " with no records identity")
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"needs :pg to name a database"
                                (v/open-kb {:backend backend :dir dir})))))
      (dfiles/write-records-identity! (str dir "/index") ["localhost" 5432 "vaelii" "kb_one"])
      (adapters-failing
       absent
       #(doseq [backend [:pg-snapshot :pg-disk-log]]
          (testing (str backend " over a directory holding a records identity")
            (is (thrown-with-msg? clojure.lang.ExceptionInfo #"needs the vaelii-postgres adapter"
                                  (v/open-kb {:backend backend :dir dir}))))))
      (finally
        (doseq [f (reverse (file-seq root))] (.delete ^java.io.File f))))))

(deftest the-pg-pairings-name-a-records-axis-and-an-index-axis
  (is (= {:records :pg :index :memory} (kb/backend-axes {:backend :pg-memory})))
  (is (= {:records :pg :index :disk-log} (kb/backend-axes {:backend :pg-disk-log})))
  (testing "and the durable index takes :pg records, where it refuses RAM ones"
    (is (= {:records :pg :index :disk-log} (kb/backend-axes {:records :pg :index :disk-log})))))

;; ---- records durable, index derived ---------------------------------------

(deftest a-derived-index-writes-nothing-and-rebuilds-on-restart
  (doseq [mode [:disk-memory :disk-dense :disk-columnar]]
    (testing (str mode)
      (with-restart
        (fn [dir]
          (let [before (observations (populate! (v/open-kb {:backend mode :dir dir :recover? false})))]
            (testing "the durable directory holds records and nothing else"
              (is (.isDirectory (io/file dir "records")) "the records are on disk")
              ;; Unconditionally, for all three: the `index/` directory belongs to the
              ;; mapped image, and an image is what `{:index :snapshot}` names
              ;; (`kb/backend-axes`).  These three modes name `:memory` / `:dense` /
              ;; `:columnar`, so none of them has one to write however the platform
              ;; answers — and a derived-index backend that started writing an index
              ;; directory would be writing a second ground truth nothing reads back.
              ;; What an image costs and what it is allowed to lose is
              ;; `index_snapshot_test`'s question, not this file's.
              (is (not (.exists (io/file dir "index")))
                  "and no index was written — it is derived state"))
            before))
        (fn [dir before]
          (testing "reopening rebuilds the index from the records and answers identically"
            (let [kb (v/open-kb {:backend mode :dir dir :recover? :auto})]
              (is (= before (observations kb)))
              (is (not (.exists (io/file dir "index")))
                  "still nothing written on the index side"))))))))

(deftest a-restart-is-recoverable-only-because-the-reindex-runs-first
  ;; This is the ordering the mixed modes turn on.  `recover` rebuilds the TMS and
  ;; taxonomy *by reading the index* (`rebuild-taxonomy` reads the predicate extents), so over
  ;; a derived index that opened empty it recovers an empty KB and reports nothing wrong.
  (with-restart
    (fn [dir] (observations (populate! (v/open-kb {:backend :disk-memory :dir dir :recover? false}))))
    (fn [dir before]
      (let [kb (v/open-kb {:backend :disk-memory :dir dir :recover? false})]
        (testing "recover alone, over an index that opened empty, recovers nothing"
          (v/recover kb)
          (is (empty? (v/sentexes-matching kb '(dog ?x) 'CxMixed)))
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
        (v/assert kb '(dog Rex) 'CxMixed {:strength :monotonic})
        (is (seq (v/sentexes-matching kb '(mammal Rex) 'CxMixed))
            "the recovered rule fired over the new fact")
        (is (= 2 (count (v/sentexes-matching kb '(dog ?x) 'CxMixed)))
            "and the new record did not land on an existing handle")
        (v/retract! kb (v/handle-of kb '(dog Muffet) 'CxMixed))
        (is (empty? (v/sentexes-matching kb '(mammal Muffet) 'CxMixed))
            "retraction reaches a conclusion the rebuilt justification graph carries")))))

;; ---- crossing between a durable and a derived index -----------------------

(deftest a-disk-log-kb-restarts-as-disk-memory
  (with-restart
    (fn [dir] (observations (populate! (v/open-kb {:backend :disk-log :dir dir :recover? false}))))
    (fn [dir before]
      (testing "the durable index is simply ignored; the RAM one is rebuilt from the records"
        (let [kb (v/open-kb {:backend :disk-memory :dir dir :recover? :auto})]
          (is (= before (observations kb)))
          (is (= #{:records} (backend/opened dir))
              "and the disk index was never opened"))))))

(deftest a-disk-memory-kb-restarted-as-disk-log-needs-an-explicit-reindex
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
      (let [kb (v/open-kb {:backend :disk-log :dir dir :recover? false})]
        (is (empty? (v/sentexes-matching kb '(dog ?x) 'CxMixed))
            "the disk index for these records was never written")
        (v/reindex kb)
        (is (= before (observations kb)) "and one reindex populates it")
        (testing "durably — a further restart of the same directory rebuilds nothing"
          (backend/close-dir! dir)
          (let [kb2 (v/open-kb {:backend :disk-log :dir dir :recover? :auto})]
            (is (= before (observations kb2)))))))))

(deftest a-derived-index-outliving-its-records-is-dropped
  ;; The hazard the identity above creates: the RAM index is keyed by the directory, so
  ;; emptying that directory out from under it (closing, deleting and reopening in one
  ;; JVM) would otherwise leave an index describing records that no longer exist.
  (with-tmp
    (fn [dir]
      (populate! (v/open-kb {:backend :disk-memory :dir dir :recover? false}))
      (backend/close-dir! dir)
      (tu/rm-rf! dir)
      (let [kb (v/open-kb {:backend :disk-memory :dir dir :recover? :auto})]
        (is (zero? (v/sentex-count kb)) "the stale index went with the records")
        (is (empty? (v/sentexes-matching kb '(dog ?x) 'CxMixed)))
        ;; and the store is usable, at handles nothing else claims
        (v/assert kb '(dog Muffet) 'CxMixed {:strength :monotonic})
        (is (= 1 (count (v/sentexes-matching kb '(dog ?x) 'CxMixed))))))))

(deftest one-directory-opened-both-ways-shares-records-and-not-the-index
  ;; The registry is keyed by directory *and component*: a second KB over the same dir
  ;; must reuse the record store (one lock, one set of file handles, one ground truth)
  ;; while a RAM-index mode must not be handed the durable index the other opened.
  (with-tmp
    (fn [dir]
      (let [kb1 (populate! (v/open-kb {:backend :disk-log :dir dir :recover? false}))
            kb2 (v/open-kb {:backend :disk-memory :dir dir :recover? :auto})]
        (is (identical? (:records kb1) (:records kb2)) "one record store")
        (is (not (identical? (:index kb1) (:index kb2))) "two index stores")
        (is (instance? vaelii.impl.memory.MemoryKvBackend (:backend (:index kb2)))
            "and the second KB's is the RAM one it asked for")
        (is (= (observations kb1) (observations kb2))
            "which the reindex-on-open filled to say the same thing")))))

(deftest one-database-keys-one-index-however-it-is-spelled
  ;; The derived index is shared exactly when the records are, so two spellings of one
  ;; database must key alike — otherwise two KBs over one store get two indexes and mint
  ;; two handles for one sentence, which no reindex can merge afterwards.
  (let [ident #'kb/pg-identity]
    (testing "a JDBC URL and the component spelling of the same database"
      (is (= (ident "jdbc:postgresql://db.example:5432/kb")
             (ident {:dbtype "postgresql" :host "db.example" :port 5432 :dbname "kb"}))))
    (testing "the default port, stated or omitted"
      (is (= (ident {:host "h" :dbname "kb"}) (ident {:host "h" :dbname "kb" :port 5432}))))
    (testing "and the host's case"
      (is (= (ident {:host "DB.example" :dbname "kb"}) (ident {:host "db.example" :dbname "kb"}))))
    (testing "but a different database, schema or server is a different key"
      (is (not= (ident {:host "h" :dbname "kb"}) (ident {:host "h" :dbname "other"})))
      (is (not= (ident {:host "h" :dbname "kb"}) (ident {:host "h2" :dbname "kb"})))
      (is (not= (ident {:host "h" :dbname "kb"})
                (ident {:host "h" :dbname "kb" :schema "prod"}))))))

(deftest a-directory-does-not-make-two-record-stores-one
  ;; `:sqlite` records and `:disk` records in one directory are two different stores, so
  ;; the derived index each gets must be keyed apart — a shared one answers each KB out of
  ;; records it does not hold.
  (let [space #'kb/derived-index-space]
    (is (not= (space :sqlite {:dir "/tmp/one"}) (space :disk {:dir "/tmp/one"})))
    ;; and the directory is the whole key on that axis: a `:space` number beside it is
    ;; the in-RAM axis's key and must not split one file's records across two indexes
    (is (= (space :sqlite {:dir "/tmp/one"}) (space :sqlite {:dir "/tmp/one" :space 7})))))

(deftest a-fork-cannot-put-its-own-records-on-a-server
  ;; Refused at the entry point, and the reason is what a later refusal would cost: `open-kb`
  ;; builds a fork's own record store (a live pool) and its index half (which takes the
  ;; directory's exclusive lock) before the overlay bookkeeping is asked for, and a throw
  ;; after that returns no KB — so neither is closeable and the directory is unopenable for
  ;; the life of the JVM.
  (let [dir (tu/tmpdir "vaelii-mixed-")]
    (try
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"fork's own records cannot be :pg"
                            (v/open-kb {:backend :overlay
                                        :base {:backend :memory :space 992}
                                        :overlay {:records :pg :index :disk-log :dir dir
                                                  :pg {:dbtype "postgresql" :dbname "nope"}}})))
      (is (not (lock/held? (backend/canonical-dir dir)))
          "and nothing took the directory's lock on the way out")
      (finally (tu/rm-rf! dir)))))

;; ---- the backend list's readers outside this process ---------------------

(def ^:private suite-config-file "scripts/lib/suite-configs.sh")
(def ^:private storage-doc "docs/storage.md")

(defn- suite-backends
  "The `ALL_BACKENDS` array of `scripts/lib/suite-configs.sh`, as keywords.  Read out of
  the file rather than duplicated here: that file calls itself \"one table, three
  readers\", and a fourth copy in a test would be the drift it was written against."
  []
  (let [body (second (re-find #"(?s)ALL_BACKENDS=\(([^)]*)\)" (slurp suite-config-file)))]
    (into #{} (map keyword) (str/split (str/trim body) #"\s+"))))

(def ^:private unswept
  "Backends `ALL_BACKENDS` leaves out, and why.  All three for one reason, stated once
  per name so a name cannot inherit another's excuse."
  {:sqlite      "the com.vaelii/sqlite adapter is an Apache-2.0 sibling and is not on this repository's classpath, so no configuration here can select it"
   :pg-memory   "the com.vaelii/postgres adapter is an Apache-2.0 sibling, and it wants a server the suite does not stand up"
   :pg-disk-log "the com.vaelii/postgres adapter is an Apache-2.0 sibling, and it wants a server the suite does not stand up"
   :pg-snapshot "the com.vaelii/postgres adapter is an Apache-2.0 sibling, and it wants a server the suite does not stand up"})

(deftest every-backend-is-swept-or-excused
  ;; `test-backends.sh`, `test-sweeps.sh` and `test-matrix.sh` all read one bash array, so
  ;; the list has one place to be wrong in — and it is in another language, which is
  ;; exactly why nothing in the engine notices when it goes short.  A backend added to
  ;; `kb/backend-modes` and not to that array runs under no configuration at all: the
  ;; matrix goes green on fifteen rows that never touched it.
  (let [swept  (suite-backends)
        names  (set kb/backend-names)]
    (is (= names (into swept (keys unswept)))
        (str suite-config-file "'s ALL_BACKENDS plus `unswept` must be exactly"
             " kb/backend-names"))
    (is (empty? (filter swept (keys unswept)))
        "a backend cannot be both swept and excused")
    (is (empty? (remove names (keys unswept)))
        "an excuse for a name that is not a backend has outlived what it excused")))

(defn- documented-backends
  "The `:backend` column of docs/storage.md's backend table, as keywords.  Scoped to the
  rows under that table's header, so the file's several other tables — the throughput
  figures name `:sqlite` and `:pg-memory` too — are not read as claims about which
  backends exist."
  []
  (->> (str/split-lines (slurp storage-doc))
       (drop-while #(not (re-find #"^\|\s*`:backend`" %)))
       rest
       (take-while #(str/starts-with? % "|"))
       (keep #(second (re-find #"^\|\s*`:([a-z-]+)`" %)))
       (into #{} (map keyword))))

(deftest every-backend-has-a-row-in-the-table
  ;; The table is how a caller finds out a pairing exists at all — `:records` / `:index`
  ;; are for overriding a half, and the names are what say which halves go together.  A
  ;; backend with no row is one nobody can be told about, and the omission reads from
  ;; inside as a complete table.
  (is (= (set kb/backend-names) (documented-backends))
      (str storage-doc "'s backend table must have one row per name on"
           " kb/backend-names, and no row for a name that is not one")))

;; ---- and the validator that joins the two halves ------------------------

(deftest the-backend-validator-refuses-a-half-declared-table
  ;; `check-backends!` runs at `kb`'s load, over one set of tables that agree — so every
  ;; branch it has taken is the one that throws nothing.  Its whole argument is that its
  ;; rules are about backends the suite does not have; that argument also means nothing
  ;; here has ever seen one of them fire, and a rule that cannot fire reads from inside
  ;; exactly like a table with nothing wrong.  These drive it over tables that ARE wrong.
  (let [check   @#'kb/check-backends!
        tables  @#'kb/backend-tables
        refusal (fn [m] (try (check (merge tables m)) nil
                             (catch clojure.lang.ExceptionInfo e (ex-data e))))
        arm     (fn [& _] nil)]
    (testing "the live tables pass, which is what the namespace load asserts"
      (is (nil? (check tables))))
    (testing "an axis declared with nothing to open it"
      (let [data (refusal {:record-axes (assoc (:record-axes tables) :tape {:durable? true})})]
        (is (= :bad-table-entry (:type data)))
        (is (= :unarmed-axis (:mismatch data)))
        (is (= :tape (:axis data)))))
    (testing "an arm for an axis no row declares, which reads nil for every field"
      (is (= :undeclared-arm
             (:mismatch (refusal {:record-arms (assoc (:record-arms tables) :tape arm)})))))
    (testing "a record axis claiming the image that may not persist an index beside it"
      (is (= :image-axis
             (:mismatch (refusal {:record-axes (assoc-in (:record-axes tables)
                                                         [:sqlite :image?] true)})))))
    (testing "a name for an axis nothing declares, which refuses at the first open"
      (is (= :unknown-axis
             (:mismatch (refusal {:backend-modes (assoc (:backend-modes tables)
                                                        :tape-memory {:records :tape :index :memory})}))))
      (is (= [:unknown-axis :tape]
             ((juxt :mismatch :index)
              (refusal {:backend-modes (assoc (:backend-modes tables)
                                              :memory-tape {:records :memory :index :tape})})))
          "and on the index axis"))
    (testing "a name for a pair the pair checks reject, where the refusal never mentions the name"
      (is (= :illegal-pair
             (:mismatch (refusal {:backend-modes (assoc (:backend-modes tables)
                                                        :ram-snapshot {:records :memory :index :snapshot})})))))
    (testing "a reserved name whose remedy is a second refusal"
      (is (= :reserved-name
             (:mismatch (refusal {:reserved-backend-names
                                  (assoc (:reserved-backend-names tables) :tape :tape-log)})))))
    (testing "a legal pair over the core axes with no name, which no caller can be told about"
      (is (= :unnamed-pair
             (:mismatch (refusal {:backend-modes (dissoc (:backend-modes tables) :disk-columnar)})))))))
