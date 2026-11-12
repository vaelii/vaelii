;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.untrusted-files-test
  "The two entry points on a file the engine is handed: what a frame may **name**, and how much
  a manifest may **hold**.

  A store directory and a dump are input from wherever an operator copied them, and both
  are read before anything about them has been checked.  A nippy frame can name a class,
  and reading one resolves the name and builds an instance of it; an EDN manifest is read
  by name, so a gigabyte called `meta.edn` is a gigabyte in the heap on the strength of a
  filename.  `vaelii.impl.io.thaw` closes the first and `vaelii.impl.disk.files`'
  `read-edn-manifest` the second.  A text KB file is read form by form, and a form that
  does not read is refused by file and line without its text.

  The *truncation* half of the same question — a file cut at an arbitrary byte — is
  `vaelii.truncation-fuzz-test`."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [taoensso.nippy :as nippy]
            [vaelii.browser.catalog :as catalog]
            [vaelii.core :as v]
            [vaelii.impl.disk.backend :as backend]
            [vaelii.impl.disk.files :as dfiles]
            [vaelii.impl.io.frames :as frames]
            [vaelii.impl.io.import :as import]
            [vaelii.impl.io.thaw :as safe]
            [vaelii.test-util :as tu])
  (:import (java.io File)))

;; ---- scaffolding ---------------------------------------------------------

(defrecord Probe [a])

(defn- ex-data-of
  "The `ex-data` of the `ExceptionInfo` `f` throws, or `::none`."
  [f]
  (try (f) ::none (catch clojure.lang.ExceptionInfo e (ex-data e))))

(defn- rename-class
  "`bs` with the class name `from` replaced by `to`, which must be the same length so the
  frame's own length prefix stays true.  ISO-8859-1 round-trips every byte through a
  string unchanged, which is what makes this a byte edit rather than a re-encode."
  ^bytes [^bytes bs ^String from ^String to]
  (assert (= (count from) (count to)))
  (.getBytes (.replace (String. bs "ISO-8859-1") from to) "ISO-8859-1"))

;; ---- the class-name check -------------------------------------------------

(deftest a-frame-that-names-a-class-is-refused-by-name
  (let [bs (nippy/freeze (->Probe 1))]
    (testing "the bytes are good: nippy on its own builds the record from them"
      (is (= (->Probe 1) (nippy/thaw bs))
          "the frame is well-formed, so what refuses it below is the entry point and not damage"))
    (testing "and the engine's own thaw refuses the name instead"
      (let [d (ex-data-of #(safe/thaw bs))]
        (is (= :disallowed-class (:type d)))
        (is (= "vaelii.untrusted_files_test.Probe" (:class d))
            "the refusal names the class, which is the whole of what it knows about it")
        (is (= :record (:reader d)))))))

(deftest a-class-name-is-refused-before-it-is-resolved
  ;; The discriminator: a frame naming a class that is **not on this classpath**.  nippy
  ;; on its own gets as far as resolving it and reports the failure as a placeholder —
  ;; which is the step this entry point exists to happen before.  Under the guard there is no
  ;; resolution to fail: the refusal carries the name and nothing was loaded.
  (let [absent (rename-class (nippy/freeze (->Probe 1) {:compressor nil})
                             "vaelii.untrusted_files_test.Probe"
                             "vaelii.untrusted_files_test.Absnt")]
    (testing "nippy alone reaches the class loader and reports what it found there"
      (let [r (nippy/thaw absent)]
        (is (= :record (get-in r [:nippy/unthawable :type])))
        (is (= :exception (get-in r [:nippy/unthawable :cause]))
            "the placeholder is nippy having tried the name and failed")))
    (testing "the guarded thaw never gets there"
      (let [d (ex-data-of #(safe/thaw absent))]
        (is (= :disallowed-class (:type d)))
        (is (= "vaelii.untrusted_files_test.Absnt" (:class d)))))))

(deftest the-serializable-fallback-is-refused-by-the-same-entry-point
  ;; nippy's `Serializable` path is allowlisted, but by a **dynamic var** an embedding
  ;; application is invited to widen — so the engine binds its own rather than inheriting
  ;; whatever the host left there.  A `java.time.LocalDate` is on nippy's default list
  ;; and is not on this one: it round-trips only through an `ObjectInputStream`, and a
  ;; stored value whose only durable form is that is a store every later read has to open
  ;; one for.
  (let [bs (nippy/freeze (java.time.LocalDate/of 2000 1 1))]
    (is (instance? java.time.LocalDate (nippy/thaw bs))
        "nippy on its own deserializes it, which is what the bound allowlist overrides")
    (let [d (ex-data-of #(safe/thaw bs))]
      (is (= :disallowed-class (:type d)))
      (is (= "java.time.LocalDate" (:class d)))
      (is (= :serializable (:reader d))))))

(deftest the-entry-point-refuses-what-the-readers-would-refuse
  ;; The two halves are one decision.  `check-encodable` probes a leaf's class through
  ;; the same thaw the durable readers run, so a value that would not read back off disk
  ;; never gets stored — rather than storing here and refusing one restart later, which
  ;; is the by-backend asymmetry that check exists to close.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [bornOn Fido weighs]
      (testing "a leaf nippy has a type id for stores"
        (v/assert kb (list weighs Fido 12.5) 'CxUniverse)
        (is (some? (v/handle-of kb (list weighs Fido 12.5) 'CxUniverse))))
      (testing "one only Java serialization round-trips is refused, by type"
        (let [d (ex-data-of #(v/assert kb (list bornOn Fido (java.time.LocalDate/of 2000 1 1))
                                       'CxUniverse))]
          (is (= :not-encodable (:type d)))
          (is (instance? java.time.LocalDate (:value d))
              "and names the value it could not store"))))))

(deftest a-host-applications-own-thaw-is-untouched
  ;; The entry point is armed for the duration of the engine's own reads and no longer: the
  ;; checked readers stand in for nippy's process-wide, so a library that closed one
  ;; globally would break a host that thaws its own records in the same JVM.
  (is (= (->Probe 7) (nippy/thaw (nippy/freeze (->Probe 7))))
      "a bare nippy thaw still builds the record")
  (is (= {:a 1} (safe/thaw (nippy/freeze {:a 1})))
      "and the guarded one still reads everything a vaelii frame is made of"))

(deftest a-stream-frame-naming-a-class-is-refused-on-the-way-in
  ;; The entry point where a dump is actually read: `read-chunked-seq` over a stream file whose
  ;; second frame names a class.  The first frame is ordinary, so the refusal is the
  ;; frame's and not the file's.
  (let [d (tu/temp-dir "vaelii-untrusted-" "stream" "-")]
    (try
      (let [f (str (.getPath d) "/hostile.nippy.stream")]
        (frames/write-frames! f [{:handle 1} (->Probe 2)]
                              {:compression :none :chunk-size 10})
        (let [e (ex-data-of #(doall (frames/read-chunked-seq f :none)))]
          (is (= :disallowed-class (:type e)))
          (is (= "vaelii.untrusted_files_test.Probe" (:class e)))))
      (finally (tu/rm-rf! d)))))

(deftest what-a-dump-and-a-store-carry-is-nothing-the-entry-point-refuses
  ;; The allowlist is empty because the formats state no class — the export's own
  ;; non-negotiable rule, and the disk codec's positional frames.  This is that claim
  ;; exercised rather than restated: a KB out to a dump and back, and a durable store
  ;; closed and reopened, with the entry point armed throughout.
  (let [d (tu/temp-dir "vaelii-untrusted-" "roundtrip" "-")]
    (try
      (let [store (str (.getPath d) "/store")
            dump  (str (.getPath d) "/dump")]
        (.mkdirs (io/file store))
        (let [kb (v/open-kb {:backend :disk-log :dir store :recover? false})]
          (try
            (tu/with-terms [dog Fido animal]
              (v/assert kb (list dog Fido) 'CxUniverse)
              (v/assert kb (list 'genl dog animal) 'CxUniverse)
              (v/assert-rule kb [(list dog '?x)] (list animal '?x) 'CxUniverse {:direction :forward}))
            (is (= 4 (v/sentex-count kb)) "three asserts, and the rule's own conclusion")
            (v/export! kb dump {:compression :none})
            (finally (v/close! kb))))
        (let [reopened (v/open-kb {:backend :disk-log :dir store :recover? :auto})]
          (try (is (= 4 (v/sentex-count reopened))
                   "the store reads back with the entry point armed")
               (finally (v/close! reopened))))
        (let [into-kb (v/open-kb {:space [::untrusted 1] :recover? false})]
          (is (= 4 (:sentexes (v/import! into-kb dump)))
              "and so does the dump")))
      (finally (tu/rm-rf! d)))))

;; ---- the expected nippy version behind the attachment points -----------

(deftest the-expected-version-names-the-nippy-that-is-actually-on-the-classpath
  ;; The expected version is only worth its ceremony if it is read from the resolved dependency rather
  ;; than restated by hand, so this asserts the two agree — and that the descriptor the
  ;; reading depends on is there at all, in a checkout and in whatever jar this runs from.
  (is (some? (safe/resolved-nippy-version))
      "nippy's own META-INF/maven descriptor is readable, which is what the check reads")
  (is (= safe/expected-nippy-version (safe/resolved-nippy-version))
      "the release the class-name check was written against is the one on the classpath")
  (is (= safe/expected-nippy-version (safe/check-nippy-version! safe/expected-nippy-version))
      "and the check passes, returning the version it agreed on"))

(deftest a-moved-nippy-refuses-the-load-rather-than-narrowing-in-silence
  ;; The version check exercised rather than trusted: the failure it exists for is a bump that keeps
  ;; `read-record` / `read-deftype` and stops routing a class name through them, which
  ;; nothing else in the tree can see.  So the one thing to prove is that a version other
  ;; than the expected one throws — the same throw a real bump would meet at load.
  (let [d (ex-data-of #(safe/check-nippy-version! "0.0.0-not-the-expected-one"))]
    (is (= :nippy-version-moved (:type d))
        "a nippy other than the expected one refuses, which fails the namespace and the build")
    (is (= "0.0.0-not-the-expected-one" (:expected d)))
    (is (= (safe/resolved-nippy-version) (:found d))
        "and the refusal names both versions, so the reader knows which way the ground moved"))
  (testing "the message says what a bumper is supposed to do, not merely that it stopped"
    (let [msg (try (safe/check-nippy-version! "0.0.0-not-the-expected-one")
                   (catch clojure.lang.ExceptionInfo e (.getMessage e)))]
      (doseq [point ["taoensso.nippy.io/read-record"
                     "taoensso.nippy.io/read-deftype"
                     "taoensso.nippy.impl/serializable-allowed?"]]
        (is (.contains ^String msg point)
            (str "the refusal names the attachment point to re-read: " point))))))

(deftest a-nippy-that-cannot-be-identified-refuses-too
  ;; Unreadable is not "probably fine".  An entry point that cannot say which nippy it stands in
  ;; front of has no claim to be guarding anything, so the two ways of being wrong refuse
  ;; alike and only their kind differs.
  (with-redefs [safe/resolved-nippy-version (constantly nil)]
    (is (= :nippy-version-unreadable
           (:type (ex-data-of #(safe/check-nippy-version! safe/expected-nippy-version)))))))

;; ---- the manifest bound --------------------------------------------------

(defn- write-manifest!
  "A file at `path` holding `n` bytes of EDN — the form `head` (a dump's marker by
  default), padded with a comment when `n` is large, so what refuses a big one is its
  size rather than its shape."
  ([path n] (write-manifest! path n "{:format :vaelii/export :format-version 1}"))
  ([^String path ^long n ^String head]
   (let [head (str head " ;")
         pad  (apply str (repeat (max 0 (- n (count head))) \x))]
     (spit path (str head pad)))))

(deftest a-manifest-over-the-bound-is-refused-by-name
  (let [d (tu/temp-dir "vaelii-untrusted-" "manifest" "-")]
    (try
      (let [small (.getPath (io/file d "small.edn"))
            big   (.getPath (io/file d "meta.edn"))]
        (write-manifest! small 64)
        (write-manifest! big (+ dfiles/manifest-bytes 4096))
        (testing "an ordinary manifest reads"
          (is (= 1 (:format-version (import/read-edn-manifest small)))))
        (testing "one past the bound is refused, naming the file and the bound"
          (let [e (ex-data-of #(import/read-edn-manifest big))]
            (is (= :manifest-too-large (:type e)))
            (is (= big (:file e)))
            (is (= dfiles/manifest-bytes (:max e)))))
        (testing "and the dump reader is held to it, since meta.edn is read first"
          (is (= :manifest-too-large (:type (ex-data-of #(import/read-meta (.getPath d)))))))
        (testing "so is discovery, which reads the manifest of every directory it walks"
          (is (= :manifest-too-large (:type (ex-data-of #(catalog/classify d)))))))
      (finally (tu/rm-rf! d)))))

(deftest a-store-sentinel-over-the-bound-is-refused-at-open-kb
  ;; The padded form states a supported version, so the size is the only thing refused.
  (let [d   (tu/temp-dir "vaelii-untrusted-" "sentinel" "-")
        fmt (io/file d "records" "format.edn")]
    (try
      (.mkdirs (.getParentFile fmt))
      (write-manifest! (.getPath fmt) (+ dfiles/manifest-bytes 4096) "{:format-version 1}")
      (let [e (ex-data-of #(v/open-kb {:backend :disk-log :dir (.getPath d)}))]
        (is (= :manifest-too-large (:type e)))
        (is (= (.getCanonicalFile fmt) (.getCanonicalFile (io/file (str (:file e)))))))
      (finally (try (backend/close-dir! (.getPath d)) (catch Throwable _ nil))
               (tu/rm-rf! d)))))

(deftest an-index-sentinel-over-the-bound-is-read-under-the-bound
  ;; Both sentinels state a value the reader would accept, padded past the bound.  The
  ;; layout version is a cache's, so past the bound it proves nothing and reads `:stale`
  ;; (a rebuild), as a torn one does; the records identity decides which store an index
  ;; answers for, so it is refused by name.
  (let [d (tu/temp-dir "vaelii-untrusted-" "index-sentinels" "-")]
    (try
      (write-manifest! (.getPath (io/file d "layout.edn")) (+ dfiles/manifest-bytes 4096)
                       "{:index-layout 7}")
      (write-manifest! (.getPath (io/file d "records.edn")) (+ dfiles/manifest-bytes 4096)
                       "{:records :a-store}")
      (is (= :stale (dfiles/index-layout-decision (.getPath d) 7 true)))
      (is (= :manifest-too-large
             (:type (ex-data-of #(dfiles/records-identity (.getPath d))))))
      (finally (tu/rm-rf! d)))))

(deftest a-manifest-cut-mid-form-is-refused-by-name
  (let [d (tu/temp-dir "vaelii-untrusted-" "manifest-cut" "-")]
    (try
      (let [cut (.getPath (io/file d "meta.edn"))]
        (spit cut "{:format :vaelii/export :format-version")
        (testing "the reader names the refusal and the file rather than raising the reader's EOF"
          (let [e (ex-data-of #(import/read-edn-manifest cut))]
            (is (= :malformed-manifest (:type e)))
            (is (= cut (:file e))))))
      (testing "a text KB's digests file is read through the same reader"
        (let [digests (.getPath (io/file d "digests.edn"))]
          (spit (io/file d "CxA.txt") "(genl dog animal)\n")
          (spit digests "{\"CxA.txt\" {0 [")
          (let [e (ex-data-of #(v/load-text! (tu/fresh) (.getPath d)))]
            (is (= :malformed-manifest (:type e)))
            (is (= digests (:file e))))))
      (finally (tu/rm-rf! d)))))

(deftest a-malformed-manifest-is-still-not-a-kb-rather-than-an-error
  ;; The bound is the one thing discovery treats as an error.  Garbage under the right
  ;; filename stays what it was: a directory that is not a source.
  (let [d (tu/temp-dir "vaelii-untrusted-" "malformed" "-")]
    (try
      (spit (str (.getPath d) "/meta.edn") "{:format :vaelii/export ")
      (is (nil? (catalog/classify d))
          "an unreadable manifest makes the directory not a KB, and says so by absence")
      (finally (tu/rm-rf! d)))))

(deftest a-text-kb-form-that-does-not-read-is-refused-by-file-and-line
  ;; `kb-diff` sends a refusal's message over the wire, so the message names the file
  ;; and the line and quotes nothing the file holds (`zzSecret` stands for that content).
  (let [d (tu/temp-dir "vaelii-untrusted-" "text" "-")
        f (io/file d "CxA.txt")]
    (try
      (doseq [[label line] [["an unknown tag" "(weighs Fido #zzSecret \"x\")"]
                            ["read-eval" "(weighs Fido #=(zzSecret))"]
                            ["an unbalanced form" "(dog zzSecret"]]]
        (spit f (str ";; a comment\n(genl dog animal)\n\n" line "\n"))
        (testing label
          (let [e (try (v/load-text! (tu/fresh) (.getPath d)) nil
                       (catch clojure.lang.ExceptionInfo e e))]
            (is (= {:type :unreadable :file (.getPath f) :line 4} (ex-data e)))
            (is (not (str/includes? (str (ex-message e)) "zzSecret"))))))
      (finally (tu/rm-rf! d)))))

(deftest every-thaw-in-the-engine-goes-through-the-entry-point
  ;; The reasoning image's two sections were thawed with bare nippy, so a class named
  ;; in `state.nippy` was resolved on the next open.  `io/frames` thaws raw inside the
  ;; `guarded` its caller opens; every other call goes through `vaelii.impl.io.thaw`.
  (let [raw  #"nippy/(thaw|thaw-from-in!|fast-thaw)(?![\w-])"
        held #{"src/vaelii/impl/io/thaw.clj" "src/vaelii/impl/io/frames.clj"}]
    (is (= []
           (for [^File f (file-seq (io/file "src"))
                 :when (and (.isFile f) (.endsWith (.getName f) ".clj"))
                 :let [path (str/replace (.getPath f) \\ \/)]
                 :when (and (not (held path)) (re-find raw (slurp f)))]
             path)))))
