;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.config-test
  "The build's switches (`vaelii.impl.config`), held to the rule the options maps
  already keep: a switch that is read has a domain, and a value outside it is refused.

  Every test here asserts the **refusal**, not the behaviour it would have selected:
  `-Dvaelii.disk.auto-compact=disabled` throws, and what it must not do is compact.
  The other half — every documented spelling still reads, and no property set at all is
  the documented default — is what catches a domain drawn too tight, which would refuse
  a working operator's setup rather than a typo.

  Three switches read the *environment* (`VAELII_ARBITRATE_CONSTRAINTS`,
  `VAELII_ASSERTIVE_ARG_TYPES`, `VAELII_DEV`) and a JVM cannot set its own, so they are
  covered where the coverage is honest: through `prop-bool`, which is the whole of each
  accessor's body."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.browser.catalog :as catalog]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.host.guard :as guard]
            [vaelii.host.llm.ollama :as ollama]
            [vaelii.host.llm.provider :as provider]
            [vaelii.impl.config :as config]
            [vaelii.impl.disk.backend :as backend]
            [vaelii.impl.disk.files :as f]))

(def ^:private switched
  "Every *property* `config/check!` reads, so a test can clear the lot and see the
  defaults — a run with nothing set must be indistinguishable from one with the
  properties absent.  The environment variables it also reads are not here: a JVM cannot
  clear its own environment, and `prop-bool` is where they are covered.

  **Read off `config/switch-names`, not written out.**  A hand-kept copy of a roster
  drifts, and this one drifted: it stood one short of the build's, missing
  `vaelii.index.snapshot-drift`, so `with-nothing-set` left that property set and the
  defaults it claims to show were whatever the run carried.  That is `config/switches`'
  own failure one layer out, and it takes the same fix."
  (into [] (remove #(re-find #"^[A-Z]" %)) config/switch-names))

(defn- with-properties*
  "Run `f` with each `[name value]` set (nil clears), restoring every one afterwards —
  including the ones the JVM was started with, since a `test-backends.sh` run sets some
  of these on the command line."
  [pairs f]
  (let [prev (mapv (fn [[nm _]] [nm (System/getProperty nm)]) pairs)]
    (doseq [[nm v] pairs]
      (if v (System/setProperty nm v) (System/clearProperty nm)))
    (try (f)
         (finally
           (doseq [[nm v] prev]
             (if v (System/setProperty nm v) (System/clearProperty nm)))))))

(defmacro ^:private with-property [nm value & body]
  `(with-properties* [[~nm ~value]] (fn [] ~@body)))

(defmacro ^:private with-nothing-set [& body]
  `(with-properties* (mapv (fn [nm#] [nm# nil]) switched) (fn [] ~@body)))

;; ---- one row per switch: the wrong value is an error, not the other branch ----

(def ^:private wrong-values
  "A plausible wrong value per switch, and what each one did when the read was a
  membership test: the comment is the reason the row exists."
  [;; negated membership — `=disabled` was compaction ON
   ["vaelii.disk.auto-compact" "disabled"]
   ["vaelii.disk.auto-compact" "never"]
   ;; membership in three spellings of one word — `=always` was the 3-second tick, which
   ;; is the durability level the operator was trying to leave
   ["vaelii.disk.fsync" "always"]
   ["vaelii.disk.fsync" "sync"]
   ["vaelii.disk.fsync" "true"]
   ;; a `case` whose default arm was nil — every misspelling was no compression at all
   ["vaelii.disk.compress" "gzip"]
   ["vaelii.disk.compress" "zstdd"]
   ;; `(= "true" …)` — everything else was off
   ["vaelii.disk.tokens" "enabled"]
   ;; a switch this build reads no value of: the mapped index image is an index
   ;; representation and is named in the opts map (`{:backend :disk-snapshot}`), so every
   ;; spelling is refused — `true` as much as `enabled`, since a property that silently
   ;; did nothing is the failure the refusal exists to close
   ["vaelii.index.snapshot" "enabled"]
   ["vaelii.index.snapshot" "true"]
   ;; likewise the reasoning image, which a `{:backend :disk-snapshot}` KB writes and installs
   ;; with no switch, so every spelling is refused
   ["vaelii.belief.snapshot" "enabled"]
   ["vaelii.belief.snapshot" "true"]
   ["vaelii.asp.solver" "clingoo"]
   ;; `Long/parseLong` with no catch, in a top-level `def`
   ["vaelii.disk.cache" "64k"]
   ["vaelii.disk.cache" "-1"]
   ["vaelii.disk.sync-ms" "3s"]
   ["vaelii.disk.compact-min-interval-ms" "5m"]
   ;; a ratio outside 0–1 is a threshold that never fires or fires on every tick
   ["vaelii.disk.compact-dead-ratio" "half"]
   ["vaelii.disk.compact-dead-ratio" "2"]
   ;; `(= "false" …)` — the one that failed safe, and still says so
   ["vaelii.disk.lock" "no-thanks"]])

(deftest every-switch-refuses-the-value-nothing-reads
  (doseq [[nm value] wrong-values]
    (testing (str nm "=" value)
      (with-property nm value
        (let [e (is (thrown? clojure.lang.ExceptionInfo (config/check!))
                    (str nm "=" value " is refused"))
              d (ex-data e)]
          (is (= :unknown-option (:type d)))
          (is (= nm (:property d)) "the refusal names the switch")
          (is (= nm (:switch d)) "under :switch as well as the older :property")
          (is (= value (:value d)) "and the value it was given")
          (is (re-find (re-pattern (str nm "=" value)) (ex-message e))
              "the message names both, since a log line is all an operator has"))))))

(deftest a-switch-nothing-reads-fails-the-open
  (testing "the refusal lands at open-kb — the earliest entry point, before a record moves"
    (with-property "vaelii.disk.fsync" "always"
      (let [e (is (thrown? clojure.lang.ExceptionInfo
                           (v/open-kb {:space 88 :recover? false})))]
        (is (= :unknown-option (:type (ex-data e))))
        (is (re-find #"dsync" (ex-message e)) "and names the mode there is")))
    (testing "on a RAM KB as much as a durable one: the process is one directory away"
      (with-property "vaelii.disk.compress" "gzip"
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/open-kb {:backend :memory :space 88
                                 :recover? false}))))))
  (testing "and a KB whose switches are all legal still opens"
    (with-property "vaelii.disk.fsync" "dsync"
      (let [kb (v/open-kb {:space 88 :recover? false})]
        (is (some? kb))
        (v/clear! kb)))))

(deftest the-image-property-is-refused-with-the-pairing-that-replaces-it
  ;; The row above covers the throw at two spellings.  What an operator needs out of it
  ;; is the REMEDY, and this is the one switch where that is the whole answer: there is
  ;; no value of it that works, so a refusal naming only the value would leave a unit
  ;; file with nothing to become.  `check!` runs it at every `open-kb`, and
  ;; `docs/operations.md` carries the row saying so — a refusal naming a switch no
  ;; document admits to leaves an operator reading the source for it.
  (with-property "vaelii.index.snapshot" "true"
    (let [e (is (thrown? clojure.lang.ExceptionInfo (config/check!)))]
      (is (= {:backend :disk-snapshot} (:remedy (ex-data e)))
          "the refusal carries the pairing to take instead")
      (is (re-find #":disk-snapshot" (ex-message e))
          "and names it in the message, which is all a log line has")))
  (testing "blank is unset here as everywhere — an exported-but-empty -D is not a value"
    (with-property "vaelii.index.snapshot" ""
      (is (nil? (config/index-snapshot?))))))

;; ---- the other half: every documented spelling still reads ---------------

(deftest every-documented-spelling-still-reads
  (testing "one boolean vocabulary, whichever switch"
    (doseq [on ["true" "1" "on" "yes" "TRUE" "On"]]
      (with-property "vaelii.disk.tokens" on
        (is (true? (config/disk-tokens?)) on)))
    (doseq [off ["false" "0" "off" "no" "FALSE" "Off"]]
      (with-property "vaelii.disk.auto-compact" off
        (is (false? (config/disk-auto-compact?)) off))))
  (testing "the fsync mode, in the three spellings the write path already accepted"
    (doseq [s ["dsync" "DSYNC" "Dsync"]]
      (with-property "vaelii.disk.fsync" s
        (is (= :dsync (config/disk-fsync-mode)) s))))
  (testing "the compressors, and the three ways to ask for none"
    (with-property "vaelii.disk.compress" "zstd" (is (= :zstd (config/disk-compress))))
    (with-property "vaelii.disk.compress" "lz4"  (is (= :lz4  (config/disk-compress))))
    (doseq [none ["none" "off" "false"]]
      (with-property "vaelii.disk.compress" none
        (is (nil? (config/disk-compress)) none))))
  (testing "the counts, including the bounds themselves"
    (with-property "vaelii.disk.cache" "0"    (is (= 0 (config/disk-cache-capacity))))
    (with-property "vaelii.disk.cache" "1000" (is (= 1000 (config/disk-cache-capacity))))
    (with-property "vaelii.disk.sync-ms" "0"  (is (= 0 (config/disk-sync-ms))))
    (with-property "vaelii.disk.compact-min-interval-ms" "60000"
      (is (= 60000 (config/disk-compact-min-interval-ms))))
    (doseq [r ["0" "0.25" "1"]]
      (with-property "vaelii.disk.compact-dead-ratio" r
        (is (= (Double/parseDouble r) (config/disk-compact-dead-ratio)) r))))
  (testing "a blank value is unset, not a spelling: an exported-but-empty variable"
    (with-property "vaelii.disk.fsync" ""
      (is (= :tick (config/disk-fsync-mode))))))

(deftest nothing-set-is-the-documented-default
  (with-nothing-set
    (is (nil? (config/check!)) "a run with no switch set passes the entry point")
    (is (true?  (config/disk-auto-compact?)))
    (is (= :tick (config/disk-fsync-mode)))
    (is (nil?   (config/disk-compress)))
    (is (false? (config/disk-tokens?)))
    (is (= 65536 (config/disk-cache-capacity)))
    (is (= 3000  (config/disk-sync-ms)))
    (is (= 0.5   (config/disk-compact-dead-ratio)))
    (is (= 300000 (config/disk-compact-min-interval-ms)))
    (is (true?  (config/disk-lock?)))
    ;; not a default: unset is the only state `vaelii.index.snapshot` has, since the
    ;; mapped index image is selected by name (`{:backend :disk-snapshot}`) rather than
    ;; by a property.  Checked here anyway, because `check!` calls it on every open and a
    ;; reader that threw on the unset case would fail every KB in the process.
    (is (nil?   (config/index-snapshot?)))))

(def ^:private switched-elsewhere
  "The properties cleared before the defaults below are read, so a `-D` on this box
  cannot answer for one.  The disk directory, the browser's port and KB discovery hold
  their default at their own call site rather than going through a `prop-*` reader; the
  solver and the model host each name a **registry member**, so unset is the absence of
  a choice rather than a default to check — `vaelii.asp.solver` still reads through
  `config/asp-solver`, and refuses a name outside the roster like every other switch
  here."
  ["vaelii.disk.dir" "vaelii.web.port" "vaelii.kb.path" "vaelii.kb.catalog"
   "vaelii.asp.solver" "vaelii.llm.provider"])

(def ^:private env-spelled-defaults
  "The variable-spelled switches whose default this test can only read as the
  environment leaves it, with the reader and what `docs/operations.md` promises."
  [["VAELII_API_TOKEN"              #(guard/api-token)                   nil]
   ["VAELII_KB_PATH"                #(count (catalog/search-path))       2]
   ["VAELII_LLM_PROVIDER"           #(provider/configured)               nil]
   ["VAELII_OLLAMA_MODEL"           #(ollama/configured-model)           "phi4:14b"]
   ["VAELII_OLLAMA_GENERATION_MODEL" #(ollama/configured-generation-model) "qwen3-coder:30b"]
   ["VAELII_OLLAMA_NUM_CTX"         #(ollama/configured-num-ctx)         8192]
   ["VAELII_OLLAMA_KEEP_ALIVE"      #(ollama/configured-keep-alive)      "30m"]])

(deftest nothing-set-is-the-documented-default-outside-this-namespace
  ;; `config_surface_test` pins every switch's *name* and its citation; this is the
  ;; **Default** column of the same table, for the two-thirds of the surface whose
  ;; reader lives somewhere other than `vaelii.impl.config`.  Without it that column is
  ;; prose: a changed default is a doc nobody updated and a test nobody failed.
  (with-properties* (mapv (fn [nm] [nm nil]) switched-elsewhere)
    (fn []
      (testing "the servers"
        (is (= 16777216 guard/max-body-bytes))
        (is (= 3000 (#'web/default-port))))
      (testing "the durable store's directory"
        (is (= (str (System/getProperty "java.io.tmpdir") "/vaelii-disk/space-0")
               (backend/disk-dir {}))))
      (testing "finding a KB"
        (is (= 200 catalog/max-discovered))
        (is (= [(str (System/getProperty "user.dir") "/kbs")
                (str (System/getProperty "user.home") "/.vaelii/kbs")]
               (vec (catalog/search-path)))))
      (testing "the log level, whose reader is here but whose row is not with the disk"
        (is (nil? (config/log-level))))
      ;; A JVM cannot clear its own environment, so these are read as this machine
      ;; leaves them — the same reading when unset, and skipped rather than wrongly
      ;; failed on a developer box that exports one (`OLLAMA_HOST` is the likely one).
      (testing "the variable-spelled switches this environment leaves unset"
        (let [unset (remove (fn [[nm _ _]] (System/getenv nm)) env-spelled-defaults)]
          (is (seq unset)
              "every variable-spelled switch is set here, so this test checked none")
          (doseq [[nm reader expected] unset]
            (is (= expected (reader)) (str nm " unset must read its documented default"))))))))

(deftest the-environment-switches-read-the-one-vocabulary
  ;; `prop-bool` is the whole body of `arbitrate-constraints?`, `assertive-arg-types?`
  ;; and `web-dev?`; a JVM cannot set its own environment, so the reader is exercised
  ;; under a property name and the accessors are one line over it.
  (with-property "vaelii.test.bool" "1"
    (is (true? (config/prop-bool "vaelii.test.bool" false))
        "=1 is on — read as `(= \"1\" …)` it was off for VAELII_DEV's neighbours"))
  (with-property "vaelii.test.bool" "0"
    (is (false? (config/prop-bool "vaelii.test.bool" true))
        "=0 is off — read as mere presence it was on"))
  (with-property "vaelii.test.bool" "maybe"
    (is (thrown? clojure.lang.ExceptionInfo (config/prop-bool "vaelii.test.bool" false))))
  (with-property "vaelii.test.bool" nil
    (is (false? (config/prop-bool "vaelii.test.bool" false)) "unset is the default")
    (is (true? (config/prop-bool "vaelii.test.bool" true)))))

;; ---- the write path the fsync switch decides ----------------------------

(deftest the-dsync-reader-still-drives-the-write-path
  (testing "the log mode is decided by the same three spellings as before"
    (doseq [s ["dsync" "DSYNC" "Dsync"]]
      (with-property "vaelii.disk.fsync" s
        (is (true? (#'f/dsync?)) s)))
    (with-property "vaelii.disk.fsync" nil
      (is (false? (#'f/dsync?)) "unset is the tick, not the append"))
    (with-property "vaelii.disk.fsync" "always"
      (is (thrown? clojure.lang.ExceptionInfo (#'f/dsync?)))))
  (testing "and a record written under dsync reads back"
    (with-property "vaelii.disk.fsync" "dsync"
      (let [path (str (System/getProperty "java.io.tmpdir") "/vaelii-config-test-"
                      (System/nanoTime) ".log")
            raf  (f/open-log path)]
        (try
          (let [off (f/append-record! raf {:hello 'world})]
            (is (= {:hello 'world} (f/read-record raf off))))
          (finally (f/close! raf) (.delete (java.io.File. path))))))))
