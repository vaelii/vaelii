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
            [vaelii.impl.disk.backend :as disk]
            [vaelii.impl.io.import :as import]
            [vaelii.impl.jobs :as jobs]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.test-util :as tu]))

;; The catalog is process-global (one registry, one active KB), so every test starts and
;; ends with it empty — and the loads below run on the catalog's own spaces, well
;; clear of the block the suite owns.
(use-fixtures :each (fn [f] (cat/reset-registry!) (try (f) (finally (cat/reset-registry!)))))

(defn- beside-the-block
  "A memory space of this namespace's own, **derived from the block the run owns** rather
  than fixed.  Two tests below open a KB directly (they need a second `open-kb` over the
  same stores, which is what makes an unrecovered store reproducible without a disk
  fixture) and the in-memory backend keys its process-global registry by this value — so a
  literal number is a store two runs on different blocks would share, and
  `scripts/test-backends.sh` moves the block with `VAELII_TEST_SPACE` precisely so two runs
  can proceed at once.

  Spelled as `[::name block]`, which is `tu/plain-memory-space`'s own idiom: the block is
  read back off that map because it is the only *public* spelling of what
  `VAELII_TEST_SPACE` was parsed and range-checked into, and re-parsing the variable here
  would be a second reading of it to keep in step."
  [tag]
  [tag (second (:space tu/plain-memory-space))])

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

(deftest a-source-nothing-offers-is-refused-by-its-id
  ;; The refusal is for a caller naming a KB this machine does not have — a bookmarked
  ;; key, a catalog entry whose directory moved.  Registered as an entry that then loads
  ;; nothing, it would sit in the list saying `:running` with no loader behind it.
  (let [e (is (thrown? clojure.lang.ExceptionInfo (cat/load-source "no-such-source")))]
    (is (= :unknown-source (:type (ex-data e)))))
  (is (empty? (cat/entries)) "and no entry was registered for it")
  (testing "and the loader's own arm, for a source whose kind nothing here reads: the
            key is claimed by the time `run-load` is reached, so the refusal has to be
            one the entry can be dropped on"
    (let [e (is (thrown? clojure.lang.ExceptionInfo
                         (#'cat/run-load {:kind :not-a-kind :path "/nowhere"} {}
                                         (fn [_] nil) (fn [_ _] nil))))]
      (is (= :unknown-source (:type (ex-data e))))
      (is (= :not-a-kind (:kind (ex-data e))) "and it names the kind it could not read"))))

(deftest a-directory-is-classified-by-the-marker-its-writer-left
  (let [root (io/file (System/getProperty "java.io.tmpdir")
                      (str "vaelii-catalog-test-" (System/nanoTime)))]
    (try
      (let [corpus  (io/file root "a-corpus")
            dump    (io/file root "a-dump")
            store   (io/file root "a-store")
            derived (io/file root "a-derived-index-store")
            bare    (io/file root "records-but-no-store")
            plain   (io/file root "not-a-kb")]
        (doseq [^java.io.File d [corpus dump store derived bare plain]] (.mkdirs d))
        (spit (io/file corpus "meta.edn") (pr-str {:context-order '[CxOne]}))
        (spit (io/file dump "meta.edn")   (pr-str {:format-version 8 :sentex-count 42}))
        (.mkdirs (io/file store "records"))
        (.mkdirs (io/file store "index"))
        (spit (io/file store "records" "format.edn") (pr-str {:format-version 1}))
        (is (= :corpus (cat/classify corpus)))
        (is (= :dump   (cat/classify dump)))
        (is (= :store  (cat/classify store)))
        (is (nil? (cat/classify plain)))
        (testing "a store whose index is DERIVED writes no index/ at all and is a store
                  all the same — :disk-columnar, :disk-dense and :disk-memory each look
                  like this, which is every backend a corpus past a few million records
                  is loaded into"
          (.mkdirs (io/file derived "records"))
          (spit (io/file derived "records" "format.edn") (pr-str {:format-version 1}))
          (is (= :store (cat/classify derived))))
        (testing "and the marker is the record writer's own stamp rather than the
                  directory's name, so an empty records/ is still nothing"
          (.mkdirs (io/file bare "records"))
          (is (nil? (cat/classify bare))))
        (testing "an unreadable meta.edn makes a directory no KB rather than an error"
          (spit (io/file plain "meta.edn") "{not edn")
          (is (nil? (cat/classify plain)))))
      (finally
        (doseq [f (reverse (file-seq root))] (.delete ^java.io.File f))))))

(deftest a-blank-search-path-is-unset-rather-than-no-directories-at-all
  ;; A blank value is *unset* everywhere else this build reads a switch
  ;; (`vaelii.impl.config`, `guard/api-token`).  Read as a value here it splits to
  ;; nothing and discovery walks **no** directory at all, so `/kbs` offers the built-ins
  ;; and reports nothing found — which reads as a machine holding no KBs rather than as
  ;; a variable somebody exported empty.  The catalog file's name is the same shape: a
  ;; blank one named the empty path, which is no file, so every entry in it went missing.
  (let [path (System/getProperty "vaelii.kb.path")
        cat  (System/getProperty "vaelii.kb.catalog")]
    (try
      (System/setProperty "vaelii.kb.path" "  ")
      (System/setProperty "vaelii.kb.catalog" "")
      (is (seq (cat/search-path))
          "a blank value falls through, so discovery still has somewhere to walk")
      (is (not-any? str/blank? (cat/search-path))
          "and no entry of what it walks is the empty path")
      (is (not (str/blank? (str (#'cat/catalog-file))))
          "the catalog file falls through to a name rather than to the empty path")
      (finally
        (if path
          (System/setProperty "vaelii.kb.path" path)
          (System/clearProperty "vaelii.kb.path"))
        (if cat
          (System/setProperty "vaelii.kb.catalog" cat)
          (System/clearProperty "vaelii.kb.catalog"))))))

(deftest a-misspelt-belief-choice-reaches-the-importer-rather-than-defaulting
  ;; The form speaks in verbs and `import-dump` speaks in `true` / `:stored` / `false`,
  ;; so the catalog widens one into the other.  What it must not do is *swallow* the
  ;; importer's own refusal: defaulted here, `{:belief? :store}` — one letter off
  ;; `:stored` — reads as the records-only load, which never opens the justification
  ;; stream, so what the typo dropped is dropped for good and nothing says so.
  (let [mode #'cat/belief-mode]
    (testing "the three verbs, and the importer's own vocabulary, translate"
      (is (= true    (mode :rebuild)))
      (is (= :stored (mode :stored)))
      (is (false?    (mode :skip)))
      (is (= true    (mode true)))
      (is (false?    (mode false)))
      (is (false?    (mode nil)) "no choice submitted is the form's own default")
      (is (every? #(contains? import/belief-modes (mode %))
                  [:rebuild :stored :skip true false nil])))
    (testing "and anything else is handed on, so import-dump refuses it by name"
      (is (= :store (mode :store)))
      (is (not (contains? import/belief-modes (mode :store)))))))

;; ---- the lifecycle -------------------------------------------------------

(deftest loading-registers-an-entry-and-activates-the-first-one
  (let [key (cat/load-source "core")]
    (is (some #(= key (:key %)) (cat/entries)))
    (is (wait-for))
    (let [e (first (filter #(= key (:key %)) (cat/entries)))]
      (is (= :done (:status e)))
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
    (testing "the KB itself stays out of the view, and the thread and the cancel flag are
              not the entry's to hold in the first place — they belong to its job"
      (is (not (contains? e :kb)))
      (is (not (contains? e :future)))
      (is (not (contains? e :cancel))))
    (testing "the status, the progress and the elapsed time are read off that job, so the
              panel and the loader cannot tell two stories"
      (is (string? (:job e)))
      (is (= :done (:status e)))
      (is (= :done (:status (jobs/job (:job e))))))
    (is (number? (:elapsed-ms e)))))

(deftest an-entry-outlives-its-jobs-report-and-still-says-what-became-of-it
  ;; A settled job ages out of the registry after an hour, and the entry stays — so the
  ;; status the entry keeps *of its own* has to be the settled one.  While it was still the
  ;; placeholder a load registered with, an hour was all it took for a finished KB to become
  ;; permanently unwritable (`write-blocked?`) and permanently un-unloadable
  ;; (`:still-stopping`), with nothing running and no job to point at.
  (let [key (cat/load-source "core")]
    (is (wait-for))
    (let [kb (:kb (cat/entry key))]
      ;; the sweep, without the hour: the registry forgets, the entry does not
      (jobs/reset-registry!)
      (is (nil? (jobs/job (:job (cat/entry key)))) "the job's report is gone")
      (let [e (cat/entry key)]
        (is (= :done (:status e)) "and the entry answers for itself")
        (is (= :done (get-in e [:progress :phase])))
        (is (number? (:finished e)) "so elapsed time stops growing"))
      (is (false? (cat/write-blocked? kb)) "the KB is writable, as it was an hour ago")
      (is (true? (cat/unload! key)) "and it can still be taken down"))))

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

(deftest a-key-the-registry-already-holds-is-not-loaded-over
  ;; The refusal is for a second load under one key.  It would open a second set of
  ;; stores, file them over the first, and leave that one resident for the life of the
  ;; JVM with nothing pointing at it.  A KB `register!` filed under a source's own id is
  ;; that key taken — how a browser started on one files it — so asking for the source
  ;; is asking for it twice.
  (tu/with-cleared-kb [kb tu/fresh]
    (cat/register! "core" "My KB" kb {:source (cat/source "core")})
    (let [e (is (thrown? clojure.lang.ExceptionInfo (cat/load-source "core")))]
      (is (= :already-loaded (:type (ex-data e))))
      (is (= "core" (:key (ex-data e))) "the refusal names the entry that is in the way"))
    (is (= 1 (count (cat/entries))) "and nothing was registered beside it")
    (is (false? (cat/loading?)) "nor was a loader started")
    (cat/unload! "core")))

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
  ;; `recover` gives every stored record a node before it labels anything, so a store
  ;; whose records ground nothing recovers into a full network with all of it OUT.  The
  ;; result is a KB that is `:done`, has a node per handle, and believes not one thing —
  ;; every belief-filtered read empty, which is exactly what the caveat exists to name.
  (let [spaces {:backend :memory :space (beside-the-block ::all-out) :recover? false}
        kb     (v/open-kb spaces)]
    (try
      ;; an inert sentex is the cheap way to a record nothing grounds: stored and
      ;; indexed, never a premise, so the rebuild has a node to build and no strength
      ;; to build it from
      (v/assert-inert kb '(dog Muffet) 'CxUniverse)
      (v/recover kb)
      (is (seq (jtms/datums (:tms kb))) "the rebuild gave the stored record a node")
      (is (empty? (jtms/in-datums (:tms kb))) "and nothing grounds it, so it is OUT")
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
        ;; and its finish.  A `before` snapshot that lands inside that window records
        ;; scratch that the compaction then deletes, and the diff reads it as an unload
        ;; having destroyed a file — which is how this failed on one backend and no
        ;; other, the backend deciding only how long the preceding namespaces took and
        ;; hence where the snapshot fell against the tick.  Neither file is one a reopen
        ;; needs: `compact!` deletes both on the way out, and `recover-compaction!`
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
          (let [kb (v/open-kb {:backend :disk-log :dir dir :recover? :auto})]
            (is (pos? (v/sentex-count kb)))
            ((requiring-resolve 'vaelii.impl.disk.backend/close-dir!) dir))))
      (finally
        (doseq [f (reverse (file-seq (io/file dir)))] (.delete ^java.io.File f))))))

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
    (let [key (cat/register! "mine" "My KB" kb)]
      (#'cat/put-entry! key #(assoc % :status :running :job "a-job-the-registry-dropped"))
      (is (= :running (:status (cat/entry key))) "the entry reads as one still loading")
      (let [e (is (thrown? clojure.lang.ExceptionInfo (cat/unload! key)))]
        (is (= :still-stopping (:type (ex-data e))))
        (is (= key (:key (ex-data e)))))
      (testing "and nothing was taken: the entry is whole, and says what it waits on"
        (is (some? (cat/entry key)))
        (is (re-find #"still stopping" (:error (cat/entry key))))
        (is (pos? (v/sentex-count kb))))
      (testing "settled, the same unload takes"
        (#'cat/put-entry! key #(-> (dissoc % :job :error) (assoc :status :done)))
        (is (true? (cat/unload! key)))
        (is (nil? (cat/entry key)))))))

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
            (get-sentex [_ _id]
              {:nippy/unthawable {:type :record
                                  :class-name "vaelii.impl.sentex.LiteralSentex"}}))
          nothing-stored #_{:clj-kondo/ignore [:missing-protocol-method]}
          (reify p/RecordStore
            (sentex-ids [_] #{})
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
        (v/assert kb '(genl tmp_export_type thing) 'CxUniverse)
        (cat/register! "mine" "My KB" kb {:where {:backend :memory}})
        (testing "the job runs on its own thread and reports where it went"
          (is (= :running (:status (cat/export-entry! "mine" (.getPath dump) {:compression :none}))))
          (is (wait-for-export))
          (let [j (jobs/latest :export)]
            (is (= :done (:status j)))
            (is (= "My KB" (:name j)))
            (is (pos? (:sentexes (:summary j))))
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
        (let [gate (promise)]
          (cat/export-entry! "mine" (.getPath dump)
                             {:compression :none :run-in (fn [work] @gate (work))})
          (is (true? (cat/exporting-kb? kb)))
          (testing "the unload gives way — the walk fetches record by record with no
                    snapshot, so a release landing mid-walk would leave it a dump of a KB
                    that stopped existing halfway through"
            (is (thrown-with-msg? clojure.lang.ExceptionInfo #"being exported"
                                  (cat/unload! "mine"))))
          (testing "and nothing was taken: the entry is whole and the KB is still live"
            (is (some? (cat/entry "mine")))
            (is (pos? (v/sentex-count kb))))
          (deliver gate true)
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
              gate    (promise)
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
                                                          :run-in (fn [work] @gate (work))})
                                      :started
                                      (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))
                  [u x]  [@unload @export]]
              (is (or (and (true? u) (= :unknown-entry x))
                      (and (= :still-exporting u) (= :started x)))
                  (str "exactly one takes the KB — unload " (pr-str u) ", export " (pr-str x)))
              (deliver gate true)
              (is (wait-for-export))
              ;; Which side reaches the monitor first is a scheduling race, and both
              ;; outcomes are legal — so each arm states the three things ITS winner is
              ;; owed, rather than one arm asserting and the other standing aside.  The
              ;; assertion count is a gate, so a loaded box resolving the race the other
              ;; way would read as a run that skipped something rather than as the other
              ;; legal outcome.
              (if (= :started x)
                (testing "and the walk it let through dumped a KB that was still there"
                  (is (= before (v/sentex-count kb)))
                  (is (= :done (:status (jobs/latest :export))))
                  (is (pos? (:sentexes (:summary (jobs/latest :export)) 0))
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
              gate    (promise)
              asked   cat/exporting?
              start   (fn [dir]
                        (future
                          (try (cat/export-entry! "mine" (.getPath (io/file root dir))
                                                  {:compression :none
                                                   :run-in (fn [work] @gate (work))})
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
          (deliver gate true)
          (is (wait-for-export)))
        (cat/unload! "mine"))
      (finally
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
    ;; how `vaelii.impl.web`'s `--attach` files a daemon: an entry like any other, whose
    ;; KB is in another process
    (cat/register! "daemon" "Daemon host:4200" {:mode :remote :conn ::stub})
    ;; a directory no walk reaches: every refusal below runs before the destination is
    ;; touched, so nothing is created and nothing needs cleaning up
    (let [nowhere "/vaelii-export-that-is-never-written"]
      (let [e (is (thrown? clojure.lang.ExceptionInfo (cat/export-entry! "mine" "" {})))]
        (is (= :no-destination (:type (ex-data e)))))
      (let [e (is (thrown? clojure.lang.ExceptionInfo (cat/export-entry! "daemon" nowhere {})))]
        (is (= :not-in-process (:type (ex-data e))))
        (is (= "daemon" (:key (ex-data e)))))
      (testing "and a KB a job holds the writer of — the walk fetches record by record
                with no snapshot to take instead, so it gives way rather than dumping
                around the writer"
        (let [gate (promise)
              job  (jobs/submit {:label "a chaining run" :kind :chain :writes kb}
                                (fn [_progress!] @gate nil))]
          (try
            (is (true? (cat/write-blocked? kb)))
            (let [e (is (thrown? clojure.lang.ExceptionInfo
                                 (cat/export-entry! "mine" nowhere {})))]
              (is (= :still-loading (:type (ex-data e)))))
            (finally
              (deliver gate true)
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
