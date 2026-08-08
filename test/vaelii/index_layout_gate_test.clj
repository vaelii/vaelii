;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.index-layout-gate-test
  "The durable index's key-layout sentinel (`dfiles/index-layout-decision`).

  A `:disk` index log written under another `kv/index-layout-version` replays
  cleanly and then misses every read whose key shape moved — counts look populated
  while ground asks answer false — so `open-kb` clears such an index and rebuilds it
  from the records, stamping `layout.edn` only after the rebuild.  An absent
  sentinel over a populated log is the same case: that is what an index written
  before the sentinel existed looks like.  Each test asserts the repair *and* that
  the KB answers afterwards — the disease this gate exists for is precisely a store
  that looks healthy and answers nothing."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.disk.backend :as backend]
            [vaelii.impl.disk.files :as dfiles]
            [vaelii.impl.kv :as kv])
  (:import [java.io File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(defn- tmpdir ^String []
  (str (Files/createTempDirectory "vaelii-layout-" (into-array FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (File. dir)))] (.delete ^File f)))

(defn- layout-file ^File [^String dir] (File. (str dir "/index") "layout.edn"))

(defn- built-kb!
  "A fresh `:disk` KB at `dir` holding one monotonic fact, closed after building —
  the store a later open gets to repair."
  [^String dir]
  (let [kb (v/open-kb {:backend :disk :dir dir :recover? false})]
    (v/assert kb '(fish LayoutNemo) 'UniverseContext {:strength :monotonic})
    (backend/close-dir! dir)))

(defn- answers? [^String dir]
  (let [kb  (v/open-kb {:backend :disk :dir dir :recover? :auto})
        ok? (v/ask? kb '(fish LayoutNemo) 'UniverseContext)]
    (backend/close-dir! dir)
    ok?))

(deftest a-fresh-durable-index-is-stamped-on-open
  (let [dir (tmpdir)]
    (try
      (built-kb! dir)
      (is (.exists (layout-file dir)) "the sentinel exists after the first open")
      (is (= kv/index-layout-version
             (:index-layout (read-string (slurp (layout-file dir)))))
          "and names the current layout")
      (finally (rm-rf! dir)))))

(deftest an-absent-sentinel-over-a-populated-log-rebuilds
  (testing "the pre-sentinel store: bytes present, stamp missing"
    (let [dir (tmpdir)]
      (try
        (built-kb! dir)
        (.delete (layout-file dir))
        (is (true? (answers? dir)) "the open cleared, rebuilt from the records, and answers")
        (is (= kv/index-layout-version
               (:index-layout (read-string (slurp (layout-file dir)))))
            "and the sentinel is re-stamped at the current layout")
        (finally (rm-rf! dir))))))

(deftest a-stale-sentinel-rebuilds
  (testing "an index stamped by another layout"
    (let [dir (tmpdir)]
      (try
        (built-kb! dir)
        (spit (layout-file dir) (pr-str {:index-layout (dec kv/index-layout-version)}))
        (is (true? (answers? dir)) "the open cleared, rebuilt from the records, and answers")
        (is (= kv/index-layout-version
               (:index-layout (read-string (slurp (layout-file dir)))))
            "and the sentinel is re-stamped at the current layout")
        (finally (rm-rf! dir))))))

(deftest a-current-sentinel-is-left-alone
  (let [dir (tmpdir)]
    (try
      (built-kb! dir)
      (let [before (.lastModified (layout-file dir))]
        (is (true? (answers? dir)) "a clean store answers without repair")
        (is (= before (.lastModified (layout-file dir)))
            "and the sentinel was not rewritten"))
      (finally (rm-rf! dir)))))

(deftest the-decision-fn-names-each-case
  (let [dir (tmpdir)
        root (str dir "/index")]
    (try
      (.mkdirs (File. root))
      (is (= :unstamped (dfiles/index-layout-decision root 2 false))
          "absent + empty needs the stamp, and says so rather than writing one")
      (is (false? (.exists (layout-file dir)))
          "and it wrote nothing — the caller owns that write, since a base is read-only")
      (dfiles/stamp-index-layout! root 2)
      (is (= :current (dfiles/index-layout-decision root 2 true))
          "the stamp the caller wrote matches")
      (is (= :stale (dfiles/index-layout-decision root 3 true))
          "a mismatched stamp is stale")
      (dfiles/stamp-index-layout! root 3)
      (is (= :current (dfiles/index-layout-decision root 3 true))
          "the rebuild's stamp commits the new layout")
      (.delete (File. root "layout.edn"))
      (is (= :stale (dfiles/index-layout-decision root 3 true))
          "absent over a populated log is stale, not adoptable")
      (finally (rm-rf! dir)))))

(deftest the-gate-reads-the-index-kind-and-so-never-fires-on-a-fork
  ;; `index-durable?` is not the discriminant: on the `:overlay` axis it says only that
  ;; the *merged view holds something*.  A fork inherits no `:dir`, so `disk/disk-dir`
  ;; synthesizes the default `<tmpdir>/vaelii-disk/space-0` — the same directory a bare
  ;; `{:backend :disk}` uses — and a gate keyed on the flag would clear the fork's merged
  ;; index (permanently hiding the base's) and stamp a directory it never read.
  (let [dir  (tmpdir)
        ;; a real durable KB at the default location, carrying no sentinel: the state a
        ;; machine has after any 0.2.0-era `{:backend :disk}` open
        base (doto (v/open-kb {:backend :memory
                               :space [::fork]
                               :recover? false})
               (v/clear!))]
    (try
      (v/assert base '(dog Muffet) 'UniverseContext {:strength :monotonic})
      (let [default-index (File. (str (backend/disk-dir {}) "/index"))
            stamp-before  (when (.isDirectory default-index)
                            (.exists (File. default-index "layout.edn")))
            f (v/fork base)]
        (is (= '#{(dog Muffet)}
               (set (map :sentence (v/sentexes-matching f '(dog ?x) 'UniverseContext))))
            "the fork sees its base through an index the gate left alone")
        (v/assert f '(dog Rex) 'UniverseContext {:strength :monotonic})
        (is (= 2 (count (v/sentexes-matching f '(dog ?x) 'UniverseContext)))
            "and still answers over both halves after a fork-local write")
        (testing "and it wrote no sentinel into the default disk directory"
          (is (= stamp-before
                 (when (.isDirectory default-index)
                   (.exists (File. default-index "layout.edn"))))
              "a fork must not stamp a directory it never gated")))
      (finally (rm-rf! dir) (v/clear! base)))))

(deftest a-crash-mid-rebuild-reads-as-stale-and-not-as-a-fresh-directory
  ;; the window the mark exists for: an absent stamp over an index the rebuild just
  ;; cleared is empty, which without the mark reads as `:unstamped` — a fresh
  ;; directory needing no rebuild, over records that are all still there
  (let [dir (tmpdir)
        root (str dir "/index")]
    (try
      (.mkdirs (File. root))
      (dfiles/mark-index-rebuilding! root)
      (is (= :stale (dfiles/index-layout-decision root 3 false))
          "the cleared index is empty, and the mark is what keeps it from reading fresh")
      (is (= :stale (dfiles/index-layout-decision root 3 true))
          "and populated reads the same")
      (dfiles/stamp-index-layout! root 3)
      (is (= :current (dfiles/index-layout-decision root 3 true))
          "the rebuild's own stamp is what clears the mark")
      (finally (rm-rf! dir)))))
