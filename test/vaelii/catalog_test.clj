;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.catalog-test
  "The KB catalog: what it offers, what a load does to the registry, and the two
  properties an operator's tool has to get right — unloading releases what it held, and
  unloading an on-disk KB does not destroy it."
  (:require [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.catalog :as cat]
            [vaelii.test-util :as tu]))

;; The catalog is process-global (one registry, one active KB), so every test starts and
;; ends with it empty — and the loads below run on the catalog's own spaces, well
;; clear of the block the suite owns.
(use-fixtures :each (fn [f] (cat/reset-registry!) (try (f) (finally (cat/reset-registry!)))))

(defn- wait-for
  "Block until no load is running (or the deadline passes) — the tests drive an API that
  is deliberately asynchronous."
  []
  (let [deadline (+ (System/currentTimeMillis) 120000)]
    (while (and (cat/loading?) (< (System/currentTimeMillis) deadline))
      (Thread/sleep 20))
    (not (cat/loading?))))

;; ---- sources -------------------------------------------------------------

(deftest the-shipped-sources-are-always-offered
  (let [by-id (into {} (map (juxt :id identity)) (cat/sources))]
    (is (contains? by-id "core"))
    (is (contains? by-id "starter"))
    (is (contains? by-id "generated"))
    (testing "a source describes its own form controls, so the page renders from data"
      (is (seq (:options (by-id "generated"))))
      (is (some #(= :types (:key %)) (:options (by-id "generated"))))
      (is (some #(= :seed  (:key %)) (:options (by-id "generated")))))
    (testing "ids are unique — the registry keys entries by them"
      (is (apply distinct? (map :id (cat/sources)))))))

(deftest a-directory-is-classified-by-the-marker-its-writer-left
  (let [root (io/file (System/getProperty "java.io.tmpdir")
                      (str "vaelii-catalog-test-" (System/nanoTime)))]
    (try
      (let [corpus (io/file root "a-corpus")
            dump   (io/file root "a-dump")
            store  (io/file root "a-store")
            plain  (io/file root "not-a-kb")]
        (doseq [^java.io.File d [corpus dump store plain]] (.mkdirs d))
        (spit (io/file corpus "meta.edn") (pr-str {:context-order '[OneContext]}))
        (spit (io/file dump "meta.edn")   (pr-str {:format-version 8 :sentex-count 42}))
        (.mkdirs (io/file store "records"))
        (.mkdirs (io/file store "index"))
        (is (= :corpus (cat/classify corpus)))
        (is (= :dump   (cat/classify dump)))
        (is (= :store  (cat/classify store)))
        (is (nil? (cat/classify plain)))
        (testing "an unreadable meta.edn makes a directory no KB rather than an error"
          (spit (io/file plain "meta.edn") "{not edn")
          (is (nil? (cat/classify plain)))))
      (finally
        (doseq [f (reverse (file-seq root))] (.delete ^java.io.File f))))))

;; ---- the lifecycle -------------------------------------------------------

(deftest loading-registers-an-entry-and-activates-the-first-one
  (let [key (cat/load-source "core")]
    (is (some #(= key (:key %)) (cat/entries)))
    (is (wait-for))
    (let [e (first (filter #(= key (:key %)) (cat/entries)))]
      (is (= :ready (:status e)))
      (is (= :done (get-in e [:progress :phase])))
      (testing "the entry carries the counts the page shows"
        (is (pos? (:sentexes (:stats e))))
        (is (pos? (:terms (:stats e)))))
      (testing "the first KB loaded becomes the one the browser reads"
        (is (= key (cat/active)))
        (is (some? (cat/active-kb)))))))

(deftest a-view-is-safe-to-render-and-send
  (cat/load-source "core")
  (wait-for)
  (let [e (first (cat/entries))]
    (testing "the KB itself, the thread, and the cancel flag stay out of the view"
      (is (not (contains? e :kb)))
      (is (not (contains? e :future)))
      (is (not (contains? e :cancel))))
    (is (number? (:elapsed-ms e)))))

(deftest ^:slow one-load-at-a-time
  (cat/load-source "generated" {:types 200 :individuals 4000 :facts 20000 :rules 100})
  (testing "a second load while one is running is refused, not queued: two at once make
            each other's timings meaningless and each other's memory unpredictable"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"already running"
                          (cat/load-source "core"))))
  (is (wait-for)))

(deftest a-source-is-not-loaded-twice-over
  (cat/load-source "core")
  (wait-for)
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"already loaded" (cat/load-source "core")))
  (testing "unless it is one a second copy makes sense of — the generator, at another shape"
    (let [a (cat/load-source "generated" {:types 5 :individuals 5 :facts 5 :rules 1})]
      (wait-for)
      (let [b (cat/load-source "generated" {:types 6 :individuals 6 :facts 6 :rules 1 :seed 2})]
        (wait-for)
        (is (not= a b))
        (is (= 3 (count (cat/entries))))))))

(deftest activating-switches-what-the-holder-yields
  (let [a (cat/load-source "core")
        _ (wait-for)
        b (cat/load-source "generated" {:types 8 :individuals 8 :facts 8 :rules 2})
        _ (wait-for)
        holder (cat/holder ::fallback)]
    (is (= a (cat/active)))
    (is (= (:kb (cat/entry a)) @holder))
    (is (cat/activate b))
    (is (= (:kb (cat/entry b)) @holder))
    (testing "an entry that holds no KB is the one thing activate refuses"
      (is (nil? (cat/activate "no-such-entry")))
      (is (= b (cat/active))))
    (testing "the holder falls back when nothing is loaded at all"
      (cat/reset-registry!)
      (is (= ::fallback @holder)))))

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
          (is (= :loading (:status c)))
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
  (let [spaces {:backend :memory :space 60 :recover? false}
        built  (v/open-kb spaces)]
    (try
      (v/assert built '(dog Muffet) 'UniverseContext {})
      (let [reopened (v/open-kb spaces)]
        (cat/register! "beliefless" "Reopened without recover" reopened)
        (is (cat/activate "beliefless"))
        (let [c (cat/active-caveat)]
          (is (= :ready (:status c)) "it is not loading — that is what makes it a trap")
          (is (false? (:belief? c)))))
      (finally (v/clear! built)))))

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
        (is (= :ready (:status e)))
        (is (= :disk (get-in e [:where :backend])))
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
        ;; and its finish.  A `before` snapshot that lands inside that window records
        ;; scratch that the compaction then deletes, and the diff reads it as an unload
        ;; having destroyed a file — which is how this failed on one backend and no
        ;; other, the backend deciding only how long the preceding namespaces took and
        ;; hence where the snapshot fell against the tick.  Neither file is one a reopen
        ;; needs: `compact!` deletes both on the way out, and `recover-log-compaction!`
        ;; deletes any a crash left behind, before the log opens.
        (let [data   (fn [] (set (->> (file-seq (io/file dir))
                                      (filter #(.isFile ^java.io.File %))
                                      (map #(.getPath ^java.io.File %))
                                      (remove #(re-find #"/dirty\.marker$" %))
                                      (remove #(re-find #"\.compact(-commit)?$" %)))))
              before (data)]
          (is (seq before))
          (cat/unload! (:key e))
          (testing "closed, not cleared: the files are still there, so the same directory
                    can be loaded again or opened by another process"
            (is (empty? (set/difference before (data)))
                (str "unload deleted " (pr-str (set/difference before (data)))))))
        (testing "and it can be picked up again, with its content intact"
          (let [kb (v/open-kb {:backend :disk :dir dir :recover? :auto})]
            (is (pos? (v/sentex-count kb)))
            ((requiring-resolve 'vaelii.impl.disk.backend/close-dir!) dir))))
      (finally
        (doseq [f (reverse (file-seq (io/file dir)))] (.delete ^java.io.File f))))))

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
          (testing "the KB it opened before failing is still on the entry, so unloading
                    releases it rather than stranding a space"
            (is (some? (:where e)))
            (is (cat/unload! key))
            (is (nil? (cat/entry key))))))
      (finally
        (if prop (System/setProperty "vaelii.kb.path" prop) (System/clearProperty "vaelii.kb.path"))
        (doseq [f (reverse (file-seq root))] (.delete ^java.io.File f))))))

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
                             (pr-str {:context-order ['UniverseContext]}))))]
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
        (v/assert kb '(genl tmp_footprint_type thing) 'UniverseContext)
        (is (> (:sentexes (cat/footprint "mine")) (:sentexes f)))
        (is (> (:total (cat/footprint "mine")) (:total f))))
      (testing "and the whole picture sums the entries it lists"
        (let [{:keys [entries total]} (cat/memory)]
          (is (= 1 (count entries)))
          (is (= total (:total (cat/footprint "mine")))))))
    (testing "nothing to estimate for an entry with no in-process KB"
      (is (nil? (cat/footprint "no-such-entry"))))
    (testing "a source that knows its own size says what loading it would cost"
      (is (pos? (cat/predicted-footprint {:total 1000})))
      (is (nil? (cat/predicted-footprint {})) "and one that does not, says nothing"))
    (cat/unload! "mine")))

;; ---- and back out again --------------------------------------------------

(defn- wait-for-export
  "Block until no export is running, or the deadline passes."
  []
  (let [deadline (+ (System/currentTimeMillis) 120000)]
    (while (and (cat/exporting?) (< (System/currentTimeMillis) deadline))
      (Thread/sleep 20))
    (not (cat/exporting?))))

(deftest exporting-a-loaded-kb-closes-the-loop-back-to-a-source
  (let [root (io/file (System/getProperty "java.io.tmpdir")
                      (str "vaelii-catalog-export-" (System/nanoTime)))
        dump (io/file root "a-written-dump")
        prop (System/getProperty "vaelii.kb.path")]
    (try
      (.mkdirs root)
      (System/setProperty "vaelii.kb.path" (.getAbsolutePath root))
      (tu/with-cleared-kb [kb tu/fresh]
        (v/assert kb '(genl tmp_export_type thing) 'UniverseContext)
        (cat/register! "mine" "My KB" kb {:where {:backend :memory}})
        (testing "the job runs on its own thread and reports where it went"
          (is (= :running (:status (cat/export-entry! "mine" (.getPath dump) {:compression :none}))))
          (is (wait-for-export))
          (let [j (cat/export-job)]
            (is (= :done (:status j)))
            (is (= "My KB" (:name j)))
            (is (pos? (:sentexes (:summary j))))
            (is (pos? (:bytes (:summary j))))
            (is (nil? (:cancel j)) "the cancel flag is not something to render")
            (is (nil? (:future j)))))
        (testing "and what it wrote is a source this catalog offers — the loop, closed
                  without leaving the process"
          (let [card (first (filter #(= "a-written-dump" (:name %)) (cat/sources)))]
            (is (some? card))
            (is (= :dump (:kind card)))
            (is (= :vaelii (:dialect card)))))
        (testing "a directory holding no meta.edn is not a dump, however much else is in
                  it — which is what makes a cancelled export unloadable rather than
                  loadable and short"
          (let [partial (io/file root "a-partial-dump")]
            (.mkdirs partial)
            (spit (io/file partial "sentexes.nippy.stream") "not a stream")
            (is (nil? (cat/classify partial)))
            (is (not-any? #(= "a-partial-dump" (:name %)) (cat/sources)))))
        (cat/unload! "mine"))
      (finally
        (if prop (System/setProperty "vaelii.kb.path" prop) (System/clearProperty "vaelii.kb.path"))
        (doseq [f (reverse (file-seq root))] (.delete ^java.io.File f))))))

(deftest an-export-refuses-what-it-cannot-be-a-dump-of
  (tu/with-cleared-kb [kb tu/fresh]
    (cat/register! "mine" "My KB" kb {:where {:backend :memory}})
    ;; how `vaelii.impl.web`'s `--attach` files a daemon: an entry like any other, whose
    ;; KB is in another process
    (cat/register! "daemon" "Daemon host:4200" {:mode :remote :conn ::stub})
    (testing "a destination is not optional — there is nowhere for a dump to go"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"destination"
                            (cat/export-entry! "mine" "" {}))))
    (testing "an entry that is not here cannot be written from here"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"nothing is loaded"
                            (cat/export-entry! nil "/tmp/vaelii-nowhere" {})))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"no loaded KB"
                            (cat/export-entry! "absent" "/tmp/vaelii-nowhere" {}))))
    (testing "and a KB served by a daemon is written on that daemon's host, not this one"
      (is (false? (cat/in-process? "daemon")))
      (is (true? (cat/in-process? "mine")))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"daemon's own host"
                            (cat/export-entry! "daemon" "/tmp/vaelii-nowhere" {}))))
    (testing "none of that started anything"
      (is (false? (cat/exporting?)))
      (is (nil? (cat/export-job))))
    (cat/unload! "mine")
    (cat/unload! "daemon")))

(deftest registering-an-existing-kb-files-it-beside-the-loadable-ones
  (tu/with-cleared-kb [kb tu/fresh]
    (cat/register! "mine" "My KB" kb {:source (cat/source "starter")})
    (let [e (cat/entry "mine")]
      (is (= :ready (:status e)))
      (is (= "mine" (cat/active)))
      (testing "it is not this catalog's to release — unloading forgets it and leaves the
                KB alone"
        (cat/unload! "mine")
        (is (nil? (cat/entry "mine")))))))
