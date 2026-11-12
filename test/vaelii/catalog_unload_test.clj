;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.catalog-unload-test
  "The KB catalog from a load that has not finished to an unload: reading a KB still
  arriving, releasing what an unload held without destroying an on-disk store, the loads
  that fail, and the heap reading.  The fixture and helpers are `catalog-fixture`'s."
  (:require [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.catalog :as cat]
            [vaelii.browser.jobs :as jobs]
            [vaelii.catalog-fixture :as cf :refer [beside-the-block wait-for]]
            [vaelii.core :as v]
            [vaelii.impl.disk.backend :as disk]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :each cf/empty-registry)

;; ---- reading a KB that is not finished -----------------------------------
;;
;; The load is deliberately far too big to complete and is cancelled the moment the
;; assertions are made: what is under test is the *unfinished* state, so waiting for it
;; would be waiting for the one thing that must not happen.

(defn- wait-for-kb
  "Block until entry `key` has opened its KB — `note-kb!` fires before anything is loaded
  into it, so this is a short wait even for a corpus that will never finish."
  [key]
  (let [deadline (+ (System/currentTimeMillis) 30000)]
    (while (and (nil? (:kb (cat/entry key))) (< (System/currentTimeMillis) deadline))
      (Thread/sleep 10))
    (:kb (cat/entry key))))

(deftest a-kb-can-be-read-while-it-is-still-arriving
  (let [key    (cat/load-source "generated"
                                {:types 500 :individuals 20000 :facts 500000 :rules 200})
        holder (cat/holder ::fallback)]
    (try
      (is (some? (wait-for-kb key)) "the KB exists before the load has filled it")
      (testing "activating it is allowed, and every page then reads it"
        (is (cat/activate key))
        (is (= key (cat/active)))
        (is (= (:kb (cat/entry key)) @holder)))
      (testing "and the reader is told, rather than the catalog refusing"
        (let [c (cat/active-caveat)]
          (is (= :running (:status c)))
          (is (= key (:key c)))
          (is (some? (:progress c)))))
      (finally
        (cat/cancel! key)
        (is (wait-for))))
    (testing "a load stopped part-way stays readable — inspecting what landed is the
              reason to stop one"
      (is (= :cancelled (:status (first (filter #(= key (:key %)) (cat/entries))))))
      (is (= (:kb (cat/entry key)) @holder))
      (is (= :cancelled (:status (cat/active-caveat)))))))

(deftest a-finished-kb-with-belief-has-nothing-to-caveat
  (cat/load-source "core")
  (wait-for)
  (is (nil? (cat/active-caveat))))

(deftest a-kb-whose-belief-was-never-built-says-so-though-it-is-ready
  ;; exactly the state a store opened without `:recover?` is left in, reproduced without
  ;; a disk fixture: the memory stores are shared per space number, so a second `open-kb`
  ;; over the same pair sees every record and index entry and a *fresh*, empty TMS
  (let [spaces {:backend :memory :space (beside-the-block ::beliefless) :recover? false}
        built  (v/open-kb spaces)]
    (try
      (v/assert built '(dog Muffet) 'CxUniverse {})
      (let [reopened (v/open-kb spaces)]
        (cat/register! "beliefless" "Reopened without recover" reopened)
        (is (cat/activate "beliefless"))
        (let [c (cat/active-caveat)]
          (is (= :done (:status c)) "it is not loading — that is what makes it a trap")
          (is (false? (:belief? c)))))
      (finally (v/clear! built)))))

(deftest a-kb-whose-nodes-are-all-out-says-so-though-every-handle-has-one
  ;; The other beliefless state, and the one a probe for *any* node reads as healthy:
  ;; `recover` gives every stored record but an inert one a node, so a store
  ;; whose records ground nothing recovers into a full network with all of it OUT.  The
  ;; result is a KB that is `:done`, has a node per handle, and believes not one thing —
  ;; every belief-filtered read empty, which is exactly what the caveat exists to name.
  (let [spaces {:backend :memory :space (beside-the-block ::all-out) :recover? false}
        kb     (v/open-kb spaces)]
    (try
      ;; an inert sentex with its `:inert` mark taken off is the cheap way to a record
      ;; nothing grounds: stored and indexed, never a premise, so the rebuild has a node
      ;; to build and no strength to build it from
      (let [h (v/assert-inert kb '(dog Muffet) 'CxUniverse)]
        (p/put-provenance (:records kb) h (dissoc (p/get-provenance (:records kb) h) :inert)))
      (v/recover kb)
      (is (seq (jtms/datums (reasoning/tms kb))) "the rebuild gave the stored record a node")
      (is (empty? (jtms/in-datums (reasoning/tms kb))) "and nothing grounds it, so it is OUT")
      (cat/register! "all-out" "Recovered from a store that grounds nothing" kb)
      (is (cat/activate "all-out"))
      (let [c (cat/active-caveat)]
        (is (= :done (:status c)) "it is not loading — that is what makes it a trap")
        (is (false? (:belief? c))))
      (finally (v/clear! kb)))))

(deftest unloading-clears-a-memory-kb-and-hands-the-browser-another
  (let [a (cat/load-source "core")
        _ (wait-for)
        b (cat/load-source "generated" {:types 8 :individuals 8 :facts 8 :rules 2})
        _ (wait-for)
        kb (:kb (cat/entry b))]
    (cat/activate b)
    (cat/unload! b)
    (testing "the entry is gone and the stores it held are empty — a memory KB is keyed
              by space number and would otherwise hold its corpus for the life of the JVM"
      (is (nil? (cat/entry b)))
      (is (zero? (reduce + 0 (map #(v/count-in-context kb %) (v/contexts kb))))))
    (testing "and the active KB falls back to one that is still loaded"
      (is (= a (cat/active))))))

(deftest unloading-an-on-disk-kb-leaves-the-directory-alone
  (let [dir (str (System/getProperty "java.io.tmpdir") "/vaelii-catalog-disk-" (System/nanoTime))]
    (try
      (cat/load-source "core" {:dir dir})
      (is (wait-for))
      (let [e (first (cat/entries))]
        (is (= :done (:status e)))
        (is (= :disk-log (get-in e [:where :backend])))
        ;; The claim is that closing *removes* nothing a reopen needs — not that the
        ;; directory is byte-identical.  A clean close legitimately writes: `counters.nippy`
        ;; (the id counter) and `clean.nippy` (the log lengths that let the next open skip
        ;; its torn-tail walk).  And it legitimately *deletes* `dirty.marker` — that
        ;; removal is precisely how it records having closed cleanly, so the marker is
        ;; excluded rather than counted as a loss.
        ;;
        ;; The compaction scratch — `<log>.compact` and `<log>.compact-commit` — is
        ;; excluded for a related reason, and this one is a *race* rather than a rule.
        ;; Unload is not the only writer here: the durability daemon fsyncs every
        ;; registrant on a 3 s tick and fires a background compaction on any that has
        ;; passed the dead ratio, which a freshly loaded KB has (0.59 on `core`, against
        ;; a 0.50 threshold).  So a compaction runs on its own thread while this test is
        ;; merely holding the KB open, and those two files exist only between its start
        ;; and its finish.  A `before` snapshot that lands inside that race window records
        ;; scratch that the compaction then deletes, and the diff reads it as an unload
        ;; having destroyed a file — which is how this failed on one backend and no
        ;; other, the backend deciding only how long the preceding namespaces took and
        ;; hence where the snapshot fell against the tick.  Neither file is one a reopen
        ;; needs: `compact!` deletes both on the way out, and `recover-compaction!`
        ;; deletes any a crash left behind, before the log opens.
        (let [data   (fn [] (set (->> (file-seq (io/file dir))
                                      (filter #(.isFile ^java.io.File %))
                                      (map #(.getPath ^java.io.File %))
                                      (remove #(re-find #"[/\\]dirty\.marker$" %))
                                      (remove #(re-find #"\.compact(-commit)?$" %)))))
              before (data)]
          (is (seq before))
          (cat/unload! (:key e))
          (testing "closed, not cleared: the files are still there, so the same directory
                    can be loaded again or opened by another process"
            (is (empty? (set/difference before (data)))
                (str "unload deleted " (pr-str (set/difference before (data)))))))
        (testing "and it can be picked up again, with its content intact"
          (let [kb (v/open-kb {:backend :disk-log :dir dir :recover? :auto})]
            (is (= (:sentexes (:stats e)) (v/sentex-count kb)))
            ((requiring-resolve 'vaelii.impl.disk.backend/close-dir!) dir))))
      (finally
        (doseq [f (reverse (file-seq (io/file dir)))] (.delete ^java.io.File f))))))

(deftest unloading-closes-a-store-on-a-backend-the-catalog-does-not-name
  ;; The store arm attaches with whatever backend `v/store-backend` reads off the
  ;; directory, and that includes the adapters' `:sqlite` and `:pg-disk-log`, which live
  ;; outside this repo.  `v/close!` releases such a store by closing a record store that is
  ;; `Closeable` (the SQLite adapter's JDBC connection), so a stand-in KB whose record store
  ;; counts its closes is the witness, filed under each adapter's backend name and under
  ;; one no backend has yet.
  (tu/with-cleared-kb [kb tu/fresh]
    (doseq [backend [:sqlite :pg-disk-log :a-backend-added-later]]
      (let [closes (atom 0)
            stub   {:records (reify java.io.Closeable (close [_] (swap! closes inc)))}]
        (cat/register! "attached" "An attached store" kb)
        (#'cat/put-entry! "attached" #(assoc % :kb stub :where {:backend backend :dir "/a/store"}))
        (is (true? (cat/unload! "attached")))
        (testing (str backend " — the entry is gone and its store is closed, not left open")
          (is (nil? (cat/entry "attached")))
          (is (= 1 @closes))
          (is (cat/released? stub)))))
    (testing "an entry filed with no :where is not this catalog's to release"
      (let [closes (atom 0)
            stub   {:records (reify java.io.Closeable (close [_] (swap! closes inc)))}]
        (cat/register! "daemon" "A daemon" kb)
        (#'cat/put-entry! "daemon" #(assoc % :kb stub))
        (is (true? (cat/unload! "daemon")))
        (is (zero? @closes))
        (is (not (cat/released? stub)))))))

(deftest a-release-that-did-not-happen-is-not-reported-as-one
  ;; The half of unloading nobody sees until it goes wrong: the release can fail — an
  ;; index that will not fsync, a component that throws on close — and the directory is
  ;; then in whatever state that left.  Logging it and dropping the entry would tell the
  ;; operator it had released a KB it had not.
  (let [dir (str (System/getProperty "java.io.tmpdir") "/vaelii-catalog-unclean-" (System/nanoTime))]
    (try
      (let [key (cat/load-source "core" {:dir dir})]
        (is (wait-for))
        (cat/activate key)
        (with-redefs [disk/close-dir! (fn [_] (throw (ex-info "the index would not fsync" {})))]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"did not release cleanly"
                                (cat/unload! key))))
        (testing "the entry keeps its place, and says what happened to it"
          (let [e (cat/entry key)]
            (is (some? e) "dropping it would be the report that it released")
            (is (= :unreleased (:status e)))
            (is (re-find #"would not fsync" (:error e)))))
        (testing "and it is not what the browser reads — a KB whose stores half-closed is
                  the one thing here nobody can vouch for"
          (is (not= key (cat/active))))
        (testing "unloading it again retries the release, and this time it takes"
          (is (true? (cat/unload! key)))
          (is (nil? (cat/entry key)))))
      (finally
        (try (disk/close-dir! dir) (catch Exception _))
        (doseq [f (reverse (file-seq (io/file dir)))] (.delete ^java.io.File f))))))

(deftest an-unload-whose-loader-has-not-stopped-refuses-rather-than-releasing
  ;; The refusal is for the entry a release cannot be safe on: its loader is still this
  ;; process's writer, and clearing or closing the stores under one leaves a KB two
  ;; things had a hand in.  A job the registry has already dropped — one still running
  ;; six hours later is presumed wedged — answers no status at all, which is not a
  ;; settled one either, so it refuses on the same ground and asks to be tried again.
  (tu/with-cleared-kb [kb tu/fresh]
    (v/assert kb '(genl tmp_still_stopping_type thing) 'CxUniverse)
    (let [key    (cat/register! "mine" "My KB" kb)
          before (v/sentex-count kb)]
      (#'cat/put-entry! key #(assoc % :status :running :job "a-job-the-registry-dropped"))
      (is (= :running (:status (cat/entry key))) "the entry reads as one still loading")
      (let [e (is (thrown? clojure.lang.ExceptionInfo (cat/unload! key)))]
        (is (= :still-stopping (:type (ex-data e))))
        (is (= key (:key (ex-data e)))))
      (testing "and nothing was taken: the entry is whole, and says what it waits on"
        (is (some? (cat/entry key)))
        (is (re-find #"still stopping" (:error (cat/entry key))))
        (is (= before (v/sentex-count kb))))
      (testing "settled, the same unload takes"
        (#'cat/put-entry! key #(-> (dissoc % :job :error) (assoc :status :done)))
        (is (true? (cat/unload! key)))
        (is (nil? (cat/entry key)))))))

(defn- held-writer
  "Submit a job that claims `kb` as its writer, as a chaining run does, and hold it inside
  `monitor` until `latch` is delivered.  Returns the job id once the job holds the monitor."
  [kb monitor latch]
  (let [held (promise)
        id   (jobs/submit {:label "Chain mine" :kind :chain :writes kb}
                          (fn [_] (locking monitor (deliver held true) (deref latch 60000 nil))))]
    (deref held 10000 nil)
    id))

(deftest an-unload-of-a-kb-a-job-writes-refuses-without-waiting-for-the-job
  ;; A chaining job holds the browser's write monitor for its whole run, and the browser
  ;; hands `unload!` that monitor as `:run-in`.  Asked only inside it, the unload waits for
  ;; the chain; asked of nothing, it releases the stores the chain is writing.
  (tu/with-cleared-kb [kb tu/fresh]
    (v/assert kb '(genl tmp_still_writing_type thing) 'CxUniverse)
    (cat/register! "mine" "My KB" kb {:where {:backend :memory}})
    (let [monitor (Object.)
          latch   (promise)
          id      (held-writer kb monitor latch)]
      (try
        (testing "with the write monitor as `:run-in`, the refusal answers while the job
                  still holds the monitor"
          (let [u (future (try (cat/unload! "mine" {:run-in (fn [work] (locking monitor (work)))})
                               (catch clojure.lang.ExceptionInfo e (ex-data e))))
                r (deref u 5000 ::parked)]
            (is (= :still-writing (:type r)) (str "answered " (pr-str r)))
            (is (= id (:holder r)) "and it names the job that holds the KB")))
        (testing "without `:run-in`, as `reset-registry!` calls it, nothing is released
                  under the job"
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"being written by Chain mine"
                                (cat/unload! "mine")))
          (is (some? (cat/entry "mine")))
          (is (pos? (v/sentex-count kb))))
        (finally (deliver latch true)))
      (jobs/wait id)
      (testing "once the job has settled the unload takes"
        (is (true? (cat/unload! "mine")))
        (is (nil? (cat/entry "mine")))))))

(deftest a-reset-stops-a-writing-job-before-it-releases-the-kb
  (tu/with-cleared-kb [kb tu/fresh]
    (v/assert kb '(genl tmp_reset_writer_type thing) 'CxUniverse)
    (cat/register! "mine" "My KB" kb {:where {:backend :memory}})
    (let [stopped-at (promise)
          running    (promise)]
      ;; a job that writes until it is cancelled, as a fixpoint does, and records what the
      ;; KB held at the moment it stopped
      (jobs/submit {:label "Chain mine" :kind :chain :writes kb}
                   (fn [progress!]
                     (try (loop []
                            (deliver running true)
                            (progress! {:phase :chaining :done 0})
                            (Thread/sleep 5)
                            (recur))
                          (finally (deliver stopped-at (v/sentex-count kb))))))
      (deref running 10000 nil)
      (cat/reset-registry!)
      (is (pos? (deref stopped-at 10000 -1))
          "the job stopped before the release, so it never wrote into an emptied KB")
      (testing "and the release still happened, after the job stopped"
        (is (nil? (cat/entry "mine")))
        (is (zero? (v/sentex-count kb)))))))

(deftest a-failed-load-says-why-and-can-still-be-cleaned-up
  (let [root (io/file (System/getProperty "java.io.tmpdir")
                      (str "vaelii-catalog-bad-" (System/nanoTime)))
        dump (io/file root "broken-dump")
        prop (System/getProperty "vaelii.kb.path")]
    (try
      (.mkdirs dump)
      ;; a dump whose format version this build does not read: found and offered like any
      ;; other, and refused by the importer when it is actually loaded
      (spit (io/file dump "meta.edn") (pr-str {:format-version 2 :variant :records}))
      (System/setProperty "vaelii.kb.path" (.getAbsolutePath root))
      (let [key (cat/load-source "dump:broken-dump")]
        (is (wait-for))
        (let [e (cat/entry key)]
          (is (= :failed (:status e)))
          (is (string? (:error e)))
          (testing "and it still says so once the job's report has aged out — a load files
                    its terminal status onto the entry from both of its ends, or the
                    fallback an hour later is the `:running` it registered with"
            (jobs/reset-registry!)
            (is (= :failed (:status (cat/entry key))))
            (is (string? (:error (cat/entry key)))))
          (testing "the KB it opened before failing is still on the entry, so unloading
                    releases it rather than stranding a space"
            (is (some? (:where e)))
            (is (cat/unload! key))
            (is (nil? (cat/entry key))))))
      (finally
        (if prop (System/setProperty "vaelii.kb.path" prop) (System/clearProperty "vaelii.kb.path"))
        (doseq [f (reverse (file-seq root))] (.delete ^java.io.File f))))))

(deftest a-store-this-build-cannot-read-is-refused-rather-than-opened-empty
  ;; The refusal is for the one failure that otherwise reads as success: a record frozen
  ;; with a class name this build does not resolve thaws to nippy's placeholder, so every
  ;; read answers and every answer is empty — a KB that looks loaded and holds nothing.
  ;; One record settles it, and a store holding none has nothing to disagree about.
  ;;
  ;; A `reify` rather than a redef, because `p/get-sentex` dispatches on the store's own
  ;; type and never reads the var root.
  (tu/with-cleared-kb [kb tu/fresh]
    (v/assert kb '(genl tmp_unreadable_type thing) 'CxUniverse)
    (let [real (:records kb)
          unthawable #_{:clj-kondo/ignore [:missing-protocol-method]}
          (reify p/RecordStore
            (sentex-ids [_] (p/sentex-ids real))
            (premise-ids [_] #{})
            (justification-ids [_] #{})
            (get-sentex [_ _id]
              {:nippy/unthawable {:type :record
                                  :class-name "vaelii.impl.types.sentex.LiteralSentex"}}))
          nothing-stored #_{:clj-kondo/ignore [:missing-protocol-method]}
          (reify p/RecordStore
            (sentex-ids [_] #{})
            (premise-ids [_] #{})
            (justification-ids [_] #{})
            (get-sentex [_ _id] nil))]
      (is (nil? (#'cat/check-readable! kb "/a/store/this/build/reads"))
          "the KB's own records come back as sentexes")
      (is (nil? (#'cat/check-readable! {:records nothing-stored} "/an/empty/store"))
          "and an empty store is nothing to disagree about")
      (let [e (is (thrown? clojure.lang.ExceptionInfo
                           (#'cat/check-readable! {:records unthawable}
                                                  "/a/store/from/another/build")))]
        (is (= :unreadable-store (:type (ex-data e))))
        (is (= "/a/store/from/another/build" (:path (ex-data e)))
            "and it names the directory, which is what an operator has to act on")))))

(deftest a-search-path-entry-is-probed-to-a-cap-that-says-so
  ;; `sources` is recomputed per `/kbs` request, and every candidate under a
  ;; search-path entry costs a `classify` — so an uncapped probe is an unbounded
  ;; per-request scan, and the one list in the browser that did not cap
  ;; (docs/web.md, "Long lists continue").  The cap is not the interesting half:
  ;; a cap nobody is told about reads as "this machine has no other KBs", which
  ;; is the one answer a KB list must not give by accident.
  (let [root (io/file (System/getProperty "java.io.tmpdir")
                      (str "vaelii-catalog-many-" (System/nanoTime)))
        prop (System/getProperty "vaelii.kb.path")
        n    (+ cat/max-discovered 5)
        ;; every candidate is a real corpus, so none is skipped for being unreadable
        ;; and the count reflects the cap alone
        ;; `:context-order` is the marker `classify` reads for a corpus — the context
        ;; order it was written in.  Anything else is not a KB and is passed over,
        ;; which would make this measure the fixture rather than the cap.
        mk!  (fn [i] (let [d (io/file root (format "kb%04d" i))]
                       (.mkdirs d)
                       (spit (io/file d "meta.edn")
                             (pr-str {:context-order ['CxUniverse]}))))]
    (try
      (.mkdirs root)
      (dotimes [i n] (mk! i))
      (System/setProperty "vaelii.kb.path" (.getAbsolutePath root))
      (let [srcs      (cat/sources)
            truncated (:truncated (meta srcs))
            ;; every one of the n candidates is a readable corpus, so the number that
            ;; comes back is the cap itself and not an artefact of some being skipped.
            ;; Scoped to this fixture's own directory: the machine running the suite
            ;; may have a catalog file of its own, and those entries are never capped.
            corpora   (filter #(and (= :corpus (:kind %))
                                    (str/starts-with? (str (:path %)) (.getAbsolutePath root)))
                              srcs)]
        (testing "the probe stops at the cap"
          (is (= cat/max-discovered (count corpora))
              (str "probed " (count corpora) " of " n " candidates"))
          (is (= 1 (count truncated)) "and the entry that was cut is named"))
        (testing "what was passed over is counted, not merely elided"
          (let [{:keys [dir passed-over probed]} (first truncated)]
            (is (= (.getAbsolutePath root) dir))
            (is (= cat/max-discovered probed))
            (is (= 5 passed-over)))))
      (testing "an entry under the cap reports no truncation at all"
        (let [small (io/file (System/getProperty "java.io.tmpdir")
                             (str "vaelii-catalog-few-" (System/nanoTime)))]
          (try
            (.mkdirs small)
            (System/setProperty "vaelii.kb.path" (.getAbsolutePath small))
            (is (empty? (:truncated (meta (cat/sources)))))
            (finally (doseq [f (reverse (file-seq small))] (.delete ^java.io.File f))))))
      (finally
        (if prop (System/setProperty "vaelii.kb.path" prop) (System/clearProperty "vaelii.kb.path"))
        (doseq [f (reverse (file-seq root))] (.delete ^java.io.File f))))))

;; ---- memory --------------------------------------------------------------

(deftest the-heap-reading-is-a-measurement-and-the-footprint-is-an-estimate
  (tu/with-cleared-kb [kb tu/fresh]
    (testing "the heap is read off the JVM, so every figure is a real byte count"
      (let [{:keys [used committed max]} (cat/heap)]
        (is (pos? used))
        (is (<= used committed))
        (is (or (nil? max) (<= committed max)))))
    (cat/register! "mine" "My KB" kb {:where {:backend :memory}})
    (let [f (cat/footprint "mine")]
      (is (:estimated? f) "a footprint says of itself that it is not measured")
      (is (= (v/sentex-count kb) (:sentexes f)) "keyed on what the KB actually holds")
      (is (= (:total f) (+ (:index f) (:records f) (:tms f))))
      (testing "it grows with the KB, since it is read live rather than at load time"
        (v/assert kb '(genl tmp_footprint_type thing) 'CxUniverse)
        (is (> (:sentexes (cat/footprint "mine")) (:sentexes f)))
        (is (> (:total (cat/footprint "mine")) (:total f))))
      (testing "and the whole picture sums the entries it lists"
        (let [{:keys [entries total]} (cat/memory)]
          (is (= 1 (count entries)))
          (is (= total (:total (cat/footprint "mine")))))))
    (testing "nothing to estimate for an entry with no in-process KB"
      (is (nil? (cat/footprint "no-such-entry"))))
    (testing "a source that knows its own size says what loading it would cost"
      (is (= (long (* 1000 (reduce + 0 (vals cat/resident-bytes-per-sentex))))
             (cat/predicted-footprint {:total 1000})))
      (is (nil? (cat/predicted-footprint {})) "and one that does not, says nothing"))
    (cat/unload! "mine")))
