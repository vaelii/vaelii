;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.core-store-reads-test
  "The `vaelii.core` reads the browser calls instead of the engine namespaces it called
  before: `store-state`, `switch-value`, `read-manifest`, `load-foreign!`,
  `install-memory-guard!`'s option check, and the pure `negative?` and `rests-on`.  Each
  test drives the public fn and checks the answer or the refusal a caller receives."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.config :as config]
            [vaelii.impl.foreign :as foreign]
            [vaelii.impl.io.import :as io-import]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(defn- refusal
  "The ex-data `f` throws, or nil when it returns."
  [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))

;; ---- store-state ------------------------------------------------------------

(deftest store-state-reports-an-empty-store-and-then-a-believed-fact
  (tu/with-cleared-kb [kb tu/fresh]
    (testing "an empty store is readable and holds no belief and nothing to recover from"
      (is (= {:readable? true :network? false :believes? false :recoverable? false}
             (v/store-state kb))))
    (v/assert kb '(genl tmp_store_state_type thing) 'CxUniverse)
    (testing "a stored premise is readable, believed, and gives recover a premise mark"
      (is (= {:readable? true :network? true :believes? true :recoverable? true}
             (v/store-state kb))))))

(deftest store-state-computes-only-the-keys-asked-for
  (tu/with-cleared-kb [kb tu/fresh]
    (v/assert kb '(genl tmp_store_state_subset thing) 'CxUniverse)
    (is (= {:network? true} (v/store-state kb #{:network?})))
    (is (= {:believes? true :recoverable? true}
           (v/store-state kb #{:believes? :recoverable?})))
    (is (= {} (v/store-state kb #{})))))

(deftest store-state-refuses-a-key-it-does-not-answer
  (tu/with-cleared-kb [kb tu/fresh]
    (let [d (refusal #(v/store-state kb #{:network? :indexed?}))]
      (is (= :unknown-option (:type d)))
      (is (= [:indexed?] (:unknown d)) "the refusal names the key it does not answer"))))

(deftest store-state-reads-a-kb-value-with-no-belief-network-as-having-none
  (tu/with-cleared-kb [kb tu/fresh]
    (is (= {:network? false :believes? false}
           (v/store-state (assoc kb :reasoning (volatile! (assoc (reasoning/of kb) :tms nil)))
                          #{:network? :believes?})))))

;; ---- switch-value ------------------------------------------------------------

(deftest switch-value-reads-a-rostered-switch-through-its-reader
  (is (= (config/profiler-port) (v/switch-value "VAELII_PROFILER_PORT")))
  (is (= (config/web-dev?) (v/switch-value "VAELII_DEV"))))

(deftest switch-value-refuses-a-name-the-build-reads-no-switch-under
  (let [d (refusal #(v/switch-value "VAELII_NO_SUCH_SWITCH"))]
    (is (= :unknown-option (:type d)))
    (is (= :unknown-key (:mismatch d)))
    (is (= "VAELII_NO_SUCH_SWITCH" (:switch d) (:property d))
        "the name is under :switch, and under :property, the older key")
    (is (some #{"VAELII_DEV"} (:options d)) "the refusal lists the names the build reads")))

;; ---- read-manifest -----------------------------------------------------------

(defn- temp-file
  "A temporary file holding `text`, deleted on JVM exit."
  ^java.io.File [text]
  (doto (java.io.File/createTempFile "vaelii-manifest" ".edn")
    (.deleteOnExit)
    (spit text)))

(deftest read-manifest-reads-edn-and-refuses-by-name
  (testing "a readable manifest comes back as the map it holds"
    (is (= {:format-version 1} (v/read-manifest (temp-file "{:format-version 1}")))))
  (testing "a manifest cut mid-form is refused as malformed"
    (is (= :malformed-manifest
           (:type (refusal #(v/read-manifest (temp-file "{:format-version")))))))
  (testing "a manifest past the byte bound is refused before it is read whole"
    (with-redefs [io-import/manifest-bytes 8]
      (is (= :manifest-too-large
             (:type (refusal #(v/read-manifest (temp-file "{:format-version 1 :pad \"xxxxxxxx\"}")))))))))

;; ---- load-foreign! -----------------------------------------------------------

(def no-directory-reader
  "A reader map declaring no `:load-dir!` — registered by the test below."
  {:name "a test reader that loads no directory"})

(deftest load-foreign-refuses-a-kind-it-cannot-load-a-directory-for
  (tu/with-cleared-kb [kb tu/fresh]
    (testing "a kind no plugin declares"
      (let [d (refusal #(v/load-foreign! kb :tmp-no-such-kind (io/file "/nowhere") {}))]
        (is (= :no-foreign-reader (:type d)))
        (is (= :tmp-no-such-kind (:kind d)))))
    (testing "a reader that declares no :load-dir!"
      (foreign/register :tmp-no-dir-kind `no-directory-reader)
      (try
        (let [d (refusal #(v/load-foreign! kb :tmp-no-dir-kind (io/file "/nowhere") {}))]
          (is (= :no-foreign-reader (:type d)))
          (is (= :tmp-no-dir-kind (:kind d))))
        (finally (foreign/unregister :tmp-no-dir-kind))))))

;; ---- store-backend -----------------------------------------------------------

(defn- with-layout
  "`f` called on a temporary directory holding an empty file at each path in `paths`, the
  directory deleted with its contents when `f` returns."
  [paths f]
  (let [d (.toFile (java.nio.file.Files/createTempDirectory
                    "vaelii-layout" (make-array java.nio.file.attribute.FileAttribute 0)))]
    (try
      (doseq [p paths]
        (let [x (apply io/file d p)]
          (io/make-parents x)
          (spit x "")))
      (f d)
      (finally (doseq [^java.io.File x (reverse (file-seq d))] (.delete x))))))

(deftest store-backend-reads-the-backend-off-the-files-beside-the-records
  (testing "a directory with no records/format.edn holds no store"
    (is (nil? (with-layout [] v/store-backend)))
    (is (nil? (with-layout [["index" "trie.csr"]] v/store-backend))
        "an index file with no records beside it is no store"))
  (testing "the index file beside the records names the backend"
    (is (= :disk-snapshot (with-layout [["records" "format.edn"] ["index" "trie.csr"]] v/store-backend)))
    (is (= :disk-log (with-layout [["records" "format.edn"] ["index" "kv.log"]] v/store-backend)))
    (is (= :disk-columnar (with-layout [["records" "format.edn"]] v/store-backend))
        "records with no index file rebuild the index on open")))

;; ---- install-memory-guard! ---------------------------------------------------

(deftest install-memory-guard-refuses-an-option-it-does-not-read
  ;; the refusal lands before the listener is attached, so this installs nothing
  (is (= :unknown-option (:type (refusal #(v/install-memory-guard! {:kbs (constantly nil)
                                                                    :interval-ms 5}))))))

;; ---- the pure reads ----------------------------------------------------------

(deftest negative-reads-the-sentence-head-of-a-record-or-a-wire-map
  (is (true? (v/negative? {:sentence '(not (flies Tweety))})))
  (is (false? (v/negative? {:sentence '(flies Tweety)})))
  (is (false? (v/negative? {:antecedent ['(bird ?x)] :consequent '(flies ?x)}))
      "a rule holds no sentence, so it is not a negative literal"))

(deftest rests-on-adds-the-informant-only-when-it-is-a-rule-handle
  (is (= [3 5 9] (v/rests-on {:antecedents [3 5] :informant 9})))
  (is (= [3 5] (v/rests-on {:antecedents [3 5] :informant :premise}))))
