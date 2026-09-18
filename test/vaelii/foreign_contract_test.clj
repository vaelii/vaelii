;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.foreign-contract-test
  "The plugin contract for `vaelii.impl.foreign`.

  A foreign reader is a bridge to knowledge that predates this build, and every one of
  them is finished the day its corpus has been converted once into the format we write.
  So none of them ships here: this engine reads its own dump format, and a bridge is a
  **separate artifact** that declares itself on the classpath.  Two halves to pin, and
  this namespace is the one that can only be tested from a build with no plugin in it:

    * nothing in this tree names a reader, carries one, or declares a format — so the
      readers are somebody else's dependency and adding or dropping one changes no file
      here;
    * a build with nothing registered refuses a foreign dump or corpus **by name**
      instead of half-reading it, and the extension point is what does the refusing.

  The complement — with a plugin present, every format it declares is found — is
  `vaelii.foreign.plugin-test`, over in the artifact that has one.  Discovery itself is
  testable from here, by putting a manifest on the classpath and taking it away again.

  Part of this is a claim about the *source tree* rather than about a running KB, which
  is why some of these tests read files."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.impl.foreign :as foreign]
            [vaelii.impl.io.import :as io-import])
  (:import [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

;; A dump reader map that omits a documented field, for the refusal test below.  A dump
;; reader offers `{:name :versions :decode-frame :replay-belief!}` (docs/foreign.md); this
;; one has `:decode-frame` and no `:versions` / `:replay-belief!`.
;; not `^:private`: it is referenced only through a quoted symbol by `foreign/register`
;; below (`requiring-resolve`), which a static unused-var check cannot see.
(def versionless-dump-reader {:decode-frame identity})

(def ^:private plugin-file "src/vaelii/impl/foreign.clj")

(defn- clj-files
  "Every Clojure source file under `dir`, as `[path text]`."
  [dir]
  (for [^java.io.File f (file-seq (io/file dir))
        :when (and (.isFile f) (str/ends-with? (.getName f) ".clj"))]
    [(.getPath f) (slurp f)]))

;;; ── nothing here reads a foreign format ───────────────────────────────

(deftest no-reader-ships-in-this-tree
  (testing "no reader directory"
    (is (not (.exists (io/file "src/vaelii/impl/foreign")))
        (str "a reader has moved back in-tree.  A bridge is a plugin: it lives in its "
             "own artifact and declares itself in resources/vaelii/foreign.edn there")))
  (testing "and no manifest, so this build declares no format of its own"
    (is (not (.exists (io/file "resources" foreign/manifest-resource)))
        (str "a manifest here would make the engine's own build read a foreign format, "
             "which is the coupling the extension point exists to avoid"))))

(deftest nothing-outside-the-extension-point-names-a-reader
  ;; The contract, stated as a grep: a plugin's namespaces are named in *its* manifest and
  ;; nowhere in this repo, so no file here breaks when one is dropped.  The extension point's own
  ;; docstring shows a manifest by way of example, and this test names one to register.
  (let [offenders (for [[path text] (concat (clj-files "src") (clj-files "test"))
                        :when (not (or (str/ends-with? path plugin-file)
                                       (str/ends-with? path "foreign_contract_test.clj")))
                        :when (re-find #"vaelii\.foreign\.|vaelii\.impl\.foreign\." text)]
                    path)]
    (is (empty? offenders)
        (str "these name a reader namespace directly, so a plugin is no longer optional "
             "— route them through vaelii.impl.foreign instead: " (pr-str (vec offenders))))))

(deftest the-extension-point-holds-no-compile-time-reference
  (let [text (slurp plugin-file)]
    (testing "a format is named as a symbol, resolved at runtime"
      (is (re-find #"requiring-resolve" text))
      (is (not (re-find #":require[^)]*vaelii\.foreign" text))
          "a :require here would put a plugin back in the compile-time graph"))
    (testing "and the manifest is data, so a plugin declares a name and cannot run code"
      (is (re-find #"edn/read" text)))))

;;; ── an absent reader is a refusal, not a crash ────────────────────────

(deftest an-unregistered-format-is-refused-by-name
  (testing "asking is simply nil"
    (is (nil? (foreign/reader :no-such-format)))
    (is (false? (foreign/available? :no-such-format))))
  (testing "and insisting names the kind, and what this build does read"
    (let [e (is (thrown? clojure.lang.ExceptionInfo (foreign/reader! :no-such-format)))]
      (is (= :no-foreign-reader (:type (ex-data e))))
      (is (= :no-such-format (:kind (ex-data e))))
      (is (set? (:available (ex-data e)))))))

(deftest a-registration-the-extension-point-cannot-look-up-is-refused-rather-than-stored
  ;; The refusal is for an entry that would sit in the registry answering nothing: a kind
  ;; that is not a keyword never matches the kind a loader asks for, and an unqualified
  ;; symbol names no var for `requiring-resolve` to reach.  Both read from the outside
  ;; exactly like a plugin nobody installed, so they are refused at the call — and as an
  ;; `ex-info` rather than a `:pre`, since `*assert*` false would store them in silence.
  (testing "the kind is what a loader asks for, so it has to be a keyword"
    (let [e (is (thrown? clojure.lang.ExceptionInfo
                         (foreign/register "test-bad-arg" 'some.plugin.ns/reader)))]
      (is (= :bad-arg (:type (ex-data e))))
      (is (= :kind (:arg (ex-data e))) "and it names which argument was wrong")))
  (testing "and the symbol has to name a var, which an unqualified one does not"
    (let [e (is (thrown? clojure.lang.ExceptionInfo
                         (foreign/register :test-bad-arg 'reader)))]
      (is (= :bad-arg (:type (ex-data e))))
      (is (= :sym (:arg (ex-data e))))))
  (testing "neither reached the registry, under either spelling of the kind"
    (is (nil? (get (foreign/formats) :test-bad-arg)))
    (is (nil? (get (foreign/formats) "test-bad-arg")))))

(deftest a-registered-format-whose-plugin-is-absent-reads-the-same-way
  ;; The state of a build that declares a format and does not have the jar: the symbol
  ;; resolves to nothing, and that is a clean refusal rather than a missing-namespace
  ;; stack trace out of the importer.
  (try
    (foreign/register :cyc-corpus 'vaelii.foreign.not-installed/reader)
    (is (contains? (foreign/formats) :cyc-corpus))
    (is (nil? (foreign/reader :cyc-corpus)))
    (is (false? (foreign/available? :cyc-corpus)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"does not read cyc-corpus"
                          (foreign/reader! :cyc-corpus)))
    (finally (foreign/unregister :cyc-corpus))))

(deftest a-dump-reader-missing-a-required-field-is-refused-by-name
  ;; A resolved `:engine-dump` reader whose map omits a documented field is refused with
  ;; `:no-foreign-reader` at the engine's own call site — the graceful treatment
  ;; `frame-decoder` already gives `:decode-frame` — rather than dereferenced as nil into
  ;; an NPE several frames into the import.  `:versions` gates the version check and
  ;; `:replay-belief!` reads the belief stream; both go through `dump-reader-field`.
  (let [field #'io-import/dump-reader-field]
    (try
      (foreign/register :engine-dump 'vaelii.foreign-contract-test/versionless-dump-reader)
      (testing "a field the map does not declare is a named refusal, not an NPE"
        (doseq [missing [:versions :replay-belief!]]
          (let [e (is (thrown? clojure.lang.ExceptionInfo (field missing)))]
            (is (= :no-foreign-reader (:type (ex-data e))))
            (is (= missing (:missing (ex-data e)))))))
      (testing "a field the map does declare is returned"
        (is (= identity (field :decode-frame))))
      (finally (foreign/unregister :engine-dump)))))

;;; ── discovery ─────────────────────────────────────────────────────────

(defn- with-manifest-on-classpath
  "Write `content` as the manifest resource in a fresh directory, put that directory on
  the classpath, and run `f`.  A `DynamicClassLoader` holding one more URL is what a
  plugin jar amounts to as far as the scan is concerned, so this exercises the real
  discovery path rather than a stub of it.

  The loader goes on `Compiler/LOADER` — a *binding*, so it is undone on the way out and
  no temporary directory is left on a loader somebody else keeps using.  Which var to
  push is not a choice: `RT/baseLoader` reads that one first and the thread's context
  loader only when it is unbound, and it is bound throughout an `eval`."
  [content f]
  (let [dir  (.toFile (Files/createTempDirectory "foreign-manifest" (make-array FileAttribute 0)))
        file (io/file dir foreign/manifest-resource)
        cl   (clojure.lang.DynamicClassLoader. (clojure.lang.RT/baseLoader))]
    (io/make-parents file)
    (spit file content)
    (.addURL cl (.toURL (.toURI dir)))
    (try
      (with-bindings {clojure.lang.Compiler/LOADER cl}
        (foreign/rescan)
        (f))
      (finally
        (foreign/rescan)
        (run! io/delete-file (reverse (file-seq dir)))))))

(deftest a-manifest-on-the-classpath-is-what-registers-a-format
  (with-manifest-on-classpath
    "{:test-format some.plugin.ns/reader}"
    (fn []
      (is (= 'some.plugin.ns/reader (get (foreign/formats) :test-format))
          "the scan did not pick the manifest up")
      ;; declared and not installed: the namespace is not here, so it reads as absent
      (is (false? (foreign/available? :test-format)))))
  (testing "and it is gone once the classpath no longer holds it"
    (is (nil? (get (foreign/formats) :test-format)))))

(deftest registration-in-code-wins-over-a-manifest
  ;; For an embedding application that has the reader in hand: more specific than a
  ;; manifest that happens to be on the path.
  (with-manifest-on-classpath
    "{:test-format some.plugin.ns/reader}"
    (fn []
      (try
        (foreign/register :test-format 'my.own/reader)
        (is (= 'my.own/reader (get (foreign/formats) :test-format)))
        (finally (foreign/unregister :test-format)))
      (is (= 'some.plugin.ns/reader (get (foreign/formats) :test-format))
          "unregister undoes the call, not the classpath"))))

(deftest a-malformed-manifest-says-so
  ;; A plugin that declares itself wrongly is a bug in the plugin, and reads exactly like
  ;; a format nobody shipped unless the scan complains.  The message names the file.
  (doseq [bad ["[:test-format some.ns/reader]"      ; not a map
               "{\"test-format\" some.ns/reader}"   ; kind is not a keyword
               "{:test-format reader}"]]            ; reader is not qualified
    (testing (pr-str bad)
      (with-manifest-on-classpath
        bad
        (fn []
          ;; `let`, not `when-let`: `is` answers nil when nothing throws, and a
          ;; `when-let` would then drop the two assertions below along with the one
          ;; that failed — an assertion count that moves with the outcome, which is
          ;; the one thing a suite-wide count gate cannot read.  `(ex-data nil)` is
          ;; nil, so both fail cleanly instead of disappearing.
          (let [e (is (thrown? clojure.lang.ExceptionInfo (foreign/formats)))]
            (is (= :bad-foreign-manifest (:type (ex-data e))))
            (is (str/includes? (str (:url (ex-data e))) foreign/manifest-resource))))))))

(deftest two-plugins-claiming-one-format-tie-break-on-content
  ;; Two bridges declaring the same kind is a misconfiguration rather than an error — one
  ;; of them still reads the format — so the scan warns and keeps going.  What must not
  ;; depend on the classpath is *which* one it keeps: the entries arrive in whatever order
  ;; `getResources` enumerated the jars, and a winner picked by arrival would make the
  ;; reader this build uses a property of how the jars were laid out.  So the tie-break is
  ;; on the symbol, and the same two manifests answer the same way in either order.
  (let [merge*  #'foreign/merge-manifests
        from-a  "jar:file:/aardvark.jar!/vaelii/foreign.edn"
        from-z  "jar:file:/zebra.jar!/vaelii/foreign.edn"
        early   [:test-format 'aa.foreign.reader/reader from-a]
        late    [:test-format 'zz.foreign.reader/reader from-z]]
    (is (= (merge* [early late]) (merge* [late early]))
        "the same two manifests in either classpath order pick the same reader")
    (is (= {:test-format 'aa.foreign.reader/reader} (merge* [late early]))
        "and it is the lexicographically smaller symbol, not the one that arrived first")
    (is (= {:test-format 'aa.foreign.reader/reader
            :other-format 'zz.foreign.reader/reader}
           (merge* [early (assoc late 0 :other-format)]))
        "a kind only one plugin claims is kept whatever it sorts against")))
