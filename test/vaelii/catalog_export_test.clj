;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.catalog-export-test
  "The KB catalog writing a loaded KB back out: exports, the refusals an export answers
  with, and the sync a load runs over its shipped contexts.  The fixture and helpers are
  `catalog-fixture`'s."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.catalog :as cat]
            [vaelii.browser.jobs :as jobs]
            [vaelii.catalog-fixture :as cf :refer [beside-the-block wait-for]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each cf/empty-registry)

;; ---- and back out again --------------------------------------------------

(defn- wait-for-export
  "Block until no export is running, or the deadline passes."
  []
  (let [deadline (+ (System/currentTimeMillis) (tu/load-budget-ms))]
    (while (and (cat/exporting?) (< (System/currentTimeMillis) deadline))
      (Thread/sleep 20))
    (not (cat/exporting?))))

(deftest a-durable-load-and-a-blank-export-go-under-the-write-root-by-the-servers-name
  (let [root (io/file (System/getProperty "java.io.tmpdir")
                      (str "vaelii-write-root-" (System/nanoTime)))
        prop (System/getProperty "vaelii.kb.path")]
    (try
      (System/setProperty "vaelii.kb.path" (.getAbsolutePath root))
      (is (= (.getAbsoluteFile root) (.getAbsoluteFile (cat/write-root))))
      (let [k (cat/load-source "core" {:durable? true})
            _ (is (wait-for))
            d (get-in (cat/entry k) [:where :dir])]
        (is (= :disk-log (get-in (cat/entry k) [:where :backend])))
        (is (= (.getAbsolutePath root) (.getParent (io/file d))))
        (is (str/starts-with? (.getName (io/file d)) "core-"))
        (cat/export-entry! k "" {:compression :none})
        (is (wait-for-export))
        (let [dump (:dir (jobs/latest :export))]
          (is (= (.getAbsolutePath root) (.getParent (io/file dump))))
          (is (str/starts-with? (.getName (io/file dump)) "core-export-"))
          (is (= :dump (cat/classify (io/file dump)))))
        (cat/unload! k))
      (finally
        (if prop (System/setProperty "vaelii.kb.path" prop) (System/clearProperty "vaelii.kb.path"))
        (doseq [f (reverse (file-seq root))] (.delete ^java.io.File f))))))

(deftest exporting-a-loaded-kb-closes-the-loop-back-to-a-source
  (let [root (io/file (System/getProperty "java.io.tmpdir")
                      (str "vaelii-catalog-export-" (System/nanoTime)))
        dump (io/file root "a-written-dump")
        prop (System/getProperty "vaelii.kb.path")]
    (try
      (.mkdirs root)
      (System/setProperty "vaelii.kb.path" (.getAbsolutePath root))
      (tu/with-cleared-kb [kb tu/fresh]
        (v/assert kb '(genl tmp_export_type thing) 'CxUniverse)
        (cat/register! "mine" "My KB" kb {:where {:backend :memory}})
        (testing "the job runs on its own thread and reports where it went"
          (let [walk-held (promise)
                job       (cat/export-entry! "mine" (.getPath dump)
                                             {:compression :none
                                              :run-in      (fn [work] @walk-held (work))})]
            (is (= :running (:status job)))
            (deliver walk-held true))
          (is (wait-for-export))
          (let [j (jobs/latest :export)]
            (is (= :done (:status j)))
            (is (= "My KB" (:name j)))
            (is (= (v/sentex-count kb) (:sentexes (:summary j))))
            (is (pos? (:bytes (:summary j))))
            (is (false? (:writes? j))
                "a dump is written to the filesystem, so it claims no writer and a load
                 may run beside it")
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

(deftest unloading-gives-way-to-the-walk-it-would-have-emptied
  (let [root (io/file (System/getProperty "java.io.tmpdir")
                      (str "vaelii-catalog-unload-export-" (System/nanoTime)))
        dump (io/file root "a-dump")]
    (try
      (.mkdirs root)
      (tu/with-cleared-kb [kb tu/fresh]
        (v/assert kb '(genl tmp_unload_type thing) 'CxUniverse)
        (cat/register! "mine" "My KB" kb {:where {:backend :memory}})
        ;; `:run-in` is the wrapper the walk runs inside, so holding it here holds the
        ;; export at exactly the point an in-flight reader sits: the job is running and
        ;; the KB is spoken for.
        (let [latch  (promise)
              before (v/sentex-count kb)]
          (cat/export-entry! "mine" (.getPath dump)
                             {:compression :none :run-in (fn [work] @latch (work))})
          (is (true? (cat/exporting-kb? kb)))
          (testing "the unload gives way — the walk fetches record by record with no
                    snapshot, so a release landing mid-walk would leave it a dump of a KB
                    that stopped existing halfway through"
            (is (thrown-with-msg? clojure.lang.ExceptionInfo #"being exported"
                                  (cat/unload! "mine"))))
          (testing "and nothing was taken: the entry is whole and the KB is still live"
            (is (some? (cat/entry "mine")))
            (is (= before (v/sentex-count kb))))
          (deliver latch true)
          (is (wait-for-export)))
        (testing "once the walk is done the unload takes, as it always did"
          (is (true? (cat/unload! "mine")))
          (is (nil? (cat/entry "mine")))))
      (finally
        (doseq [f (reverse (file-seq root))] (.delete ^java.io.File f))))))

(deftest an-unload-and-an-export-asked-for-at-once-do-not-both-take-the-kb
  ;; The two checks read different registries — the unload asks the job registry whether a
  ;; walk is running, the export asks the catalog whether a loader is — so nothing but the
  ;; shared monitor orders them.  Both requests are held inside their own check until both
  ;; have arrived; under the monitor that never happens, since the second cannot enter
  ;; until the first has claimed.  Without it both pass, the release lands, and the walk
  ;; then dumps a KB that was emptied under it and reports a clean export of nothing.
  (let [root (io/file (System/getProperty "java.io.tmpdir")
                      (str "vaelii-catalog-unload-race-" (System/nanoTime)))
        dump (io/file root "a-dump")]
    (try
      (.mkdirs root)
      (tu/with-cleared-kb [kb tu/fresh]
        (v/assert kb '(genl tmp_race_type thing) 'CxUniverse)
        (cat/register! "mine" "My KB" kb {:where {:backend :memory}})
        (let [before  (v/sentex-count kb)
              arrived (java.util.concurrent.CountDownLatch. 2)
              latch   (promise)
              rendez  (fn [r]
                        (.countDown arrived)
                        (.await arrived 300 java.util.concurrent.TimeUnit/MILLISECONDS)
                        r)
              any?    cat/exporting?
              this?   cat/exporting-kb?]
          (is (pos? before))
          (with-redefs [cat/exporting?    (fn [] (rendez (any?)))
                        cat/exporting-kb? (fn [k] (rendez (this? k)))]
            (let [unload (future (try (cat/unload! "mine")
                                      (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))
                  export (future (try (cat/export-entry! "mine" (.getPath dump)
                                                         {:compression :none
                                                          :run-in (fn [work] @latch (work))})
                                      :started
                                      (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))
                  [u x]  [@unload @export]]
              (is (or (and (true? u) (= :unknown-entry x))
                      (and (= :still-exporting u) (= :started x)))
                  (str "exactly one takes the KB — unload " (pr-str u) ", export " (pr-str x)))
              (deliver latch true)
              (is (wait-for-export))
              ;; Which side reaches the monitor first is a scheduling race, and both
              ;; outcomes are legal — so each arm states the three things ITS winner is
              ;; owed, rather than one arm asserting and the other standing aside.  The
              ;; assertion count is a check, so a loaded box resolving the race the other
              ;; way would read as a run that skipped something rather than as the other
              ;; legal outcome.
              (if (= :started x)
                (testing "and the walk it let through dumped a KB that was still there"
                  (is (= before (v/sentex-count kb)))
                  (is (= :done (:status (jobs/latest :export))))
                  (is (= before (:sentexes (:summary (jobs/latest :export))))
                      "the dump is of the KB, not of what was left of it"))
                (testing "and the unload it let through took the KB whole, dumping nothing"
                  (is (zero? (v/sentex-count kb))
                      "a memory-backed KB is cleared by the unload that claimed it")
                  (is (nil? (cat/entry "mine")) "and the entry went with it")
                  (is (not (.exists dump))
                      "the export lost inside the monitor, before it opened a directory"))))))
        (when (cat/entry "mine") (cat/unload! "mine")))
      (finally
        (doseq [f (reverse (file-seq root))] (.delete ^java.io.File f))))))

(deftest cancelling-an-export-that-already-finished-cancels-nothing-and-says-so
  ;; The panel keeps the last export's report for an hour after it settles, so the newest
  ;; export of *any* status is one that finished this morning — and `jobs/cancel!` answers
  ;; true for any job the registry still holds.  Asked of the running set instead.
  (let [root (io/file (System/getProperty "java.io.tmpdir")
                      (str "vaelii-catalog-cancel-settled-" (System/nanoTime)))]
    (try
      (.mkdirs root)
      (tu/with-cleared-kb [kb tu/fresh]
        (v/assert kb '(genl tmp_settled_type thing) 'CxUniverse)
        (cat/register! "mine" "My KB" kb {:where {:backend :memory}})
        (testing "with nothing ever exported there is nothing to cancel"
          (is (false? (cat/cancel-export!))))
        (cat/export-entry! "mine" (.getPath (io/file root "a-dump")) {:compression :none})
        (is (wait-for-export))
        (testing "and once the walk has settled its report stays, but cancelling it does not"
          (is (some? (jobs/latest :export)) "the panel still has its report")
          (is (= :done (:status (jobs/latest :export))))
          (is (false? (cat/cancel-export!))))
        (cat/unload! "mine"))
      (finally
        (doseq [f (reverse (file-seq root))] (.delete ^java.io.File f))))))

(deftest two-exports-asked-for-at-once-start-exactly-one
  ;; the export claims no writer, so the registry's own claim cannot refuse a second one;
  ;; the one-at-a-time check and the submit are one step under the catalog's monitor
  ;; instead.  Both requests are held inside `exporting?` until both have arrived there —
  ;; which under the monitor never happens, since the second cannot enter until the
  ;; first has submitted: the first times out of the hold and starts, the second then
  ;; finds it running.  Without the monitor both arrive, both read false, both start.
  (let [root (io/file (System/getProperty "java.io.tmpdir")
                      (str "vaelii-catalog-two-exports-" (System/nanoTime)))]
    (try
      (.mkdirs root)
      (tu/with-cleared-kb [kb tu/fresh]
        (v/assert kb '(genl tmp_twice_type thing) 'CxUniverse)
        (cat/register! "mine" "My KB" kb {:where {:backend :memory}})
        (let [arrived (java.util.concurrent.CountDownLatch. 2)
              latch   (promise)
              asked   cat/exporting?
              start   (fn [dir]
                        (future
                          (try (cat/export-entry! "mine" (.getPath (io/file root dir))
                                                  {:compression :none
                                                   :run-in (fn [work] @latch (work))})
                               :started
                               (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))]
          (with-redefs [cat/exporting? (fn []
                                         (let [r (asked)]
                                           (.countDown arrived)
                                           (.await arrived 300 java.util.concurrent.TimeUnit/MILLISECONDS)
                                           r))]
            (is (= #{:started :export-busy} (set (map deref [(start "a") (start "b")])))))
          (is (= 1 (count (filter #(= :export (:kind %)) (jobs/running))))
              "one walk is running, not two")
          (deliver latch true)
          (is (wait-for-export)))
        (cat/unload! "mine"))
      (finally
        (doseq [f (reverse (file-seq root))] (.delete ^java.io.File f))))))

(deftest an-export-refuses-what-it-cannot-be-a-dump-of
  (tu/with-cleared-kb [kb tu/fresh]
    (cat/register! "mine" "My KB" kb {:where {:backend :memory}})
    ;; how `vaelii.browser.web`'s `--attach` files a daemon: an entry like any other, whose
    ;; KB is in another process
    (cat/register! "daemon" "Daemon host:4200" {:mode :remote :conn ::stub})
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
      (is (nil? (jobs/latest :export))))
    (cat/unload! "mine")
    (cat/unload! "daemon")))

(deftest the-export-refusals-name-themselves-in-the-type-a-caller-catches
  ;; Three things an export cannot be correct in the face of, each read off the `:type`
  ;; rather than off the prose, because the keyword is what a caller discriminates on:
  ;; nowhere for the dump to go, a KB whose records are on another host, and a KB
  ;; something is still writing — a walk of which is a dump of no single state.
  (tu/with-cleared-kb [kb tu/fresh]
    (v/assert kb '(genl tmp_export_refusal_type thing) 'CxUniverse)
    (cat/register! "mine" "My KB" kb {:where {:backend :memory}})
    ;; how `vaelii.browser.web`'s `--attach` files a daemon: an entry like any other, whose
    ;; KB is in another process
    (cat/register! "daemon" "Daemon host:4200" {:mode :remote :conn ::stub})
    ;; a directory no walk reaches: every refusal below runs before the destination is
    ;; touched, so nothing is created and nothing needs cleaning up
    (let [nowhere "/vaelii-export-that-is-never-written"]
      (let [kb-dir (io/file (System/getProperty "java.io.tmpdir")
                            (str "vaelii-every-entry-a-kb-" (System/nanoTime)))
            prop   (System/getProperty "vaelii.kb.path")]
        (try
          ;; every search-path entry is itself a KB, so there is no write root
          (.mkdirs kb-dir)
          (spit (io/file kb-dir "meta.edn") (pr-str {:format-version 1}))
          (System/setProperty "vaelii.kb.path" (.getAbsolutePath kb-dir))
          (let [e (is (thrown? clojure.lang.ExceptionInfo (cat/export-entry! "mine" "" {})))]
            (is (= :no-destination (:type (ex-data e)))))
          (finally
            (if prop (System/setProperty "vaelii.kb.path" prop) (System/clearProperty "vaelii.kb.path"))
            (doseq [f (reverse (file-seq kb-dir))] (.delete ^java.io.File f)))))
      (let [e (is (thrown? clojure.lang.ExceptionInfo (cat/export-entry! "daemon" nowhere {})))]
        (is (= :not-in-process (:type (ex-data e))))
        (is (= "daemon" (:key (ex-data e)))))
      (testing "and a KB a job holds the writer of — the walk fetches record by record
                with no snapshot to take instead, so it gives way rather than dumping
                around the writer"
        (let [latch (promise)
              job   (jobs/submit {:label "a chaining run" :kind :chain :writes kb}
                                 (fn [_progress!] @latch nil))]
          (try
            (is (true? (cat/write-blocked? kb)))
            (let [e (is (thrown? clojure.lang.ExceptionInfo
                                 (cat/export-entry! "mine" nowhere {})))]
              (is (= :still-loading (:type (ex-data e)))))
            (finally
              (deliver latch true)
              (jobs/wait job 30000)))))
      (is (false? (cat/write-blocked? kb)) "the writer let go, so the refusal was its doing")
      (is (nil? (jobs/latest :export)) "and none of the three started a walk"))
    (cat/unload! "mine")
    (cat/unload! "daemon")))

(deftest registering-an-existing-kb-files-it-beside-the-loadable-ones
  (tu/with-cleared-kb [kb tu/fresh]
    (cat/register! "mine" "My KB" kb {:source (cat/source "starter")})
    (let [e (cat/entry "mine")]
      (is (= :done (:status e)))
      (is (= "mine" (cat/active)))
      (testing "it is not this catalog's to release — unloading forgets it and leaves the
                KB alone"
        (cat/unload! "mine")
        (is (nil? (cat/entry "mine")))))))

(def ^:private retired-note
  "A CxUniverse premise this engine does not ship that names only shipped terms, so the
  sync retracts it (`sync/vocabulary`)."
  '(comment mammal "a note this engine does not ship"))

(deftest every-loaded-kb-is-synced-by-one-job
  ;; what the development browser submits when a shipped KB file changes on disk
  (let [kb (doto (v/open-kb {:backend :memory :space (beside-the-block ::sync-loaded)
                             :recover? false})
             (tu/clear-kb!)
             (tu/load-starter!))]
    (try
      (v/assert kb retired-note 'CxUniverse)
      (cat/register! "mine" "My KB" kb {:source (cat/source "starter")})
      (let [job (cat/sync-loaded!)]
        (is (some? job))
        (jobs/wait job (tu/load-budget-ms))
        (is (= {:added 0 :removed 1 :refused []} (:sync (cat/entry "mine"))))
        (is (nil? (v/handle-of kb retired-note 'CxUniverse))))
      (cat/unload! "mine")
      (testing "no entry, no job"
        (is (nil? (cat/sync-loaded!))))
      (finally (tu/clear-kb! kb)))))

(deftest a-loaded-store-is-synced-only-when-asked
  ;; A sync is an edit and a settle over the whole KB.  On a large store a settle stopped
  ;; part-way leaves the records it wrote in the store and both images stale, so the next
  ;; open rebuilds the index and recovers belief from scratch.
  (let [kb      (doto (v/open-kb {:backend :memory :space (beside-the-block ::sync-asked)
                                  :recover? false})
                  (tu/clear-kb!)
                  (tu/load-starter!))
        retired #(some? (v/handle-of kb retired-note 'CxUniverse))]
    (try
      (v/assert kb retired-note 'CxUniverse)
      (cat/register! "mine" "My KB" kb {:source {:kind :store}})
      (testing "a load that did not ask leaves it as it was"
        (is (nil? (#'cat/sync-shipped "mine" {:kind :store} {:recover? true} (fn [_]))))
        (is (retired)))
      (testing "a shipped file edit passes it by"
        (is (nil? (cat/sync-loaded!)))
        (is (retired)))
      (testing "a load that asked for it follows the files"
        (swap! @#'cat/state assoc-in [:entries "mine" :params] {:sync? true})
        (let [job (cat/sync-loaded!)]
          (is (some? job))
          (jobs/wait job (tu/load-budget-ms)))
        (is (= {:added 0 :removed 1 :refused []} (:sync (cat/entry "mine"))))
        (is (not (retired))))
      (testing "sync-entry! brings it current on purpose, whatever its load asked"
        (swap! @#'cat/state assoc-in [:entries "mine" :params] {})
        (v/assert kb retired-note 'CxUniverse)
        (jobs/wait (cat/sync-entry! "mine") (tu/load-budget-ms))
        (is (= {:added 0 :removed 1 :forwarded 0 :refused []} (:sync (cat/entry "mine"))))
        (is (not (retired))))
      (is (= :unknown-source (:type (ex-data (try (cat/sync-entry! "nobody")
                                                  (catch clojure.lang.ExceptionInfo e e))))))
      (finally
        (cat/unload! "mine")
        (tu/clear-kb! kb)))))

(deftest a-loaded-dump-has-its-shipped-contexts-brought-to-this-engine
  ;; a starter KB whose CxUniverse holds a premise this engine does not ship, exported the
  ;; way an older build's KB would arrive: the load syncs it while the entry is running
  (let [dir (str (System/getProperty "java.io.tmpdir") "/vaelii-catalog-shipped-" (System/nanoTime))
        kb  (doto (v/open-kb {:backend :memory :space (beside-the-block ::shipped) :recover? false})
              (tu/clear-kb!)
              (tu/load-starter!))]
    (try
      (v/assert kb retired-note 'CxUniverse)
      (v/export! kb dir {})
      (let [key (cat/load-dir dir {:belief? :rebuild :sync? true})]
        ;; 15 min: the load imports a starter-sized dump and rebuilds its belief, and the
        ;; sync loads the starter again into a scratch KB (`sync/premises`)
        (is (wait-for 900000))
        (let [e      (cat/entry key)
              loaded (:kb e)]
          (is (= :done (:status (#'cat/with-job e))))
          (is (= {:added 0 :removed 1 :forwarded 0 :refused []} (:sync e)))
          (is (nil? (v/handle-of loaded retired-note 'CxUniverse)))
          (cat/unload! key)))
      (finally
        (tu/clear-kb! kb)
        (doseq [f (reverse (file-seq (io/file dir)))] (io/delete-file f true))))))

(deftest a-store-open-files-what-the-engine-logs-as-its-progress
  ;; a store's open takes no `:on-progress`; the lines it logs are the card's only account
  ;; of an hour-long recover or image install
  (let [notes  (atom [])
        passed (atom [])
        lf     (#'cat/noting-log-fn #(swap! notes conj %)
                                    (fn [_ _ level _ payload] (swap! passed conj [level (:msg (force payload))])))]
    (lf "ns" nil :info ::step (delay {:msg "recover: step 3/9"}))
    (lf "ns" nil :debug ::detail {:msg "too fine to show"})
    (lf "ns" nil :warn ::no-msg {:data {:n 1}})
    (is (= [{:phase :open :note "recover: step 3/9"}] @notes))
    (testing "and every call still reaches the backend that was installed"
      (is (= [[:info "recover: step 3/9"] [:debug "too fine to show"] [:warn nil]] @passed))))
  (testing "a progress report that throws — a cancel — never unwinds the log site"
    (let [lf (#'cat/noting-log-fn (fn [_] (throw (ex-info "stop" {}))) nil)]
      (is (nil? (lf "ns" nil :info ::step {:msg "x"}))))))
