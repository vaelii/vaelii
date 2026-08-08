;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.export-test
  "Writing a KB out as a portable export dump (`vaelii.impl.io.export`).

  The format's whole claim is that a dump outlives the build that wrote it, so these
  tests are about what a frame *is* rather than about how fast one is written: a frame
  is a plain field map (never a frozen record, whose class name is what made a `:disk`
  store unreadable across a rename), the same KB exports to the same frames whichever
  backend holds it, and the shapes a translation layer quietly drops — a negative fact,
  a defeasible rule with an `exceptWhen`, a merged term, a defeated datum, a datum with
  two justifications, provenance — all survive.

  Streams are read back with the **importer's own** chunked reader, so a framing our
  reader cannot walk fails here rather than in a year's time."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.catalog :as catalog]
            [vaelii.impl.disk.backend :as backend]
            [vaelii.impl.io.export :as export]
            [vaelii.impl.io.import :as imp]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu])
  (:import (java.io File)
           (java.nio.file Files)
           (java.nio.file.attribute FileAttribute)))

;;; ── temp directories ──────────────────────────────────────────────────

(defn- temp-dir ^File [nm]
  (.toFile (Files/createTempDirectory (str "vaelii-export-" nm "-")
                                      (into-array FileAttribute []))))

(defn- rm-rf! [^File d]
  (doseq [^File f (reverse (file-seq d))] (.delete f)))

(defn- with-dirs*
  "Run `(f dir…)` on `n` fresh temp directories, deleting them afterwards.  An export
  destination is `rm-rf!`'d by the test before use, since the ordinary case is a
  directory that does not exist yet and that is the one exercising `mkdirs`."
  [n nm f]
  (let [dirs (mapv #(temp-dir (str nm "-" %)) (range n))]
    (try (apply f dirs)
         (finally (doseq [d dirs] (rm-rf! d))))))

;;; ── reading a dump back ───────────────────────────────────────────────

(defn- frames
  "The frames of one dump stream, or nil when the dump has no such file.  Read with
  `import/read-chunked-seq` — the reader the format is written for."
  [^File dir file compression]
  (let [f (io/file dir file)]
    (when (.exists f) (vec (#'imp/read-chunked-seq f compression)))))

(defn- dump
  "A whole dump read back: `{:meta :sentexes :justifications :provenance}`."
  [^File dir]
  (let [m (imp/read-meta dir)
        c (:compression m)]
    {:meta           m
     :sentexes       (frames dir "sentexes.nippy.stream" c)
     :justifications (frames dir "justifications.nippy.stream" c)
     :provenance     (frames dir "provenance.nippy.stream" c)}))

;;; ── the KB under test ─────────────────────────────────────────────────

(defn- fresh-terms
  "One set of gensym'd temporaries, so two KBs can be built from *the same* names —
  which is what makes their dumps comparable."
  []
  (tu/with-terms [bird penguin flies feathered happy Tweety Opus Rex Preferred Deprecated
                  ExportContext]
    {:bird bird :penguin penguin :flies flies :feathered feathered :happy happy
     :Tweety Tweety :Opus Opus :Rex Rex
     :Preferred Preferred :Deprecated Deprecated :ctx ExportContext}))

(defn- build!
  "Assert the awkward shapes into `kb`.  Everything an export can quietly drop is here:
  a known-true premise, a negative fact, a defeasible rule that states its own exception
  (a rule sentex *plus* the meta-sentex naming it by handle), a datum two rules
  independently derive, a defeated-but-stored default, and a `rewriteOf` that retires a
  spelling and migrates what mentioned it.

  The clock is pinned because `assert` stamps `:created` into provenance from it, and
  two builds a millisecond apart would then disagree about content neither KB considers
  content."
  [kb {:keys [bird penguin flies feathered happy Tweety Opus Rex Preferred Deprecated ctx]}]
  (binding [v/*clock*   (constantly 1750000000000)
            v/*creator* "export-test"]
    ;; a known-true premise — the `:strength` that rides along as the premise mark
    (v/assert kb (list bird Tweety) ctx {:strength :monotonic})
    ;; a defeasible rule stating its own exception, and a second rule concluding the
    ;; same literal, so `(flies Tweety)` ends up with two independent justifications
    (v/assert kb (list 'exceptWhen (list penguin '?b)
                       (list 'set/defaultRule
                             (vr/rule-sentence [(list bird '?b)] (list flies '?b))))
              ctx)
    (v/assert kb (vr/rule-sentence [(list feathered '?f)] (list flies '?f)) ctx)
    (v/assert kb (list feathered Tweety) ctx)
    ;; a bird the exception blocks — the rule fires for Tweety and not for Opus
    (v/assert kb (list bird Opus) ctx)
    (v/assert kb (list penguin Opus) ctx)
    ;; a negative fact, defeated by the known-true positive: stored, not believed
    (v/assert kb (list 'not (list happy Rex)) ctx)
    (v/assert kb (list happy Rex) ctx {:strength :monotonic})
    ;; a merged term: the retired spelling stays stored and superseded, and what
    ;; mentioned it gets a derived twin under the representative
    (v/assert kb (list bird Deprecated) ctx)
    (v/assert kb (list 'rewriteOf Preferred Deprecated) ctx)))

;;; ── the destination ───────────────────────────────────────────────────

(deftest export-refuses-a-non-empty-directory
  (tu/with-neutral-kb [kb tu/fresh]
    (with-dirs* 1 "nonempty"
      (fn [dir]
        (spit (io/file dir "something.txt") "not a dump")
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"not empty"
                              (export/export! kb dir))
            "a dump merged into another dump is not a dump")
        (is (not (.exists (io/file dir "sentexes.nippy.stream")))
            "and nothing was written into it")))))

(deftest export-refuses-a-codec-it-cannot-write-before-touching-the-directory
  (tu/with-neutral-kb [kb tu/fresh]
    (with-dirs* 1 "codec"
      (fn [dir]
        (rm-rf! dir)
        ;; :zstd is a codec the importer *reads* and the writer does not write
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unknown compression"
                              (export/export! kb dir {:compression :zstd})))
        (is (not (.exists ^File dir)) "a refused export leaves nothing to clean up")))))

;;; ── what a frame is ───────────────────────────────────────────────────

(deftest every-record-is-a-frame-and-every-frame-is-a-plain-field-map
  (tu/with-neutral-kb [kb tu/fresh]
    (let [t (fresh-terms)]
      (build! kb t)
      (with-dirs* 1 "shapes"
        (fn [dir]
          (rm-rf! dir)
          (let [summary (export/export! kb dir {:compression :none :chunk-size 3})
                {:keys [meta sentexes justifications provenance]} (dump dir)]

            (testing "the counts agree with the KB, the streams, and meta.edn"
              (is (= (v/sentex-count kb) (:sentexes summary) (count sentexes)
                     (:sentex-count meta)))
              (is (= (count (tu/justification-ids kb)) (:justifications summary)
                     (count justifications) (:justification-count meta)))
              (is (= (count provenance) (:provenance summary) (:provenance-count meta)))
              (is (pos? (:bytes summary))))

            (testing "meta.edn announces the format rather than leaving it to be inferred"
              (is (= :vaelii/export (:format meta)))
              (is (= 1 (:format-version meta)))
              (is (= {:variant :records :dialect :vaelii :frames :field-map
                      :framing :chunked :handle-policy :preserved}
                     (select-keys meta [:variant :dialect :frames :framing :handle-policy])))
              (is (string? (:written-at meta)))
              (is (re-find #"^vaelii " (:writer meta)))
              (is (= :dump (catalog/classify dir)) "and it is what the catalog offers"))

            (testing "a frame carries no class name — the rule the whole format exists for"
              (is (every? map? sentexes))
              (is (not-any? record? sentexes))
              (is (not-any? #(contains? % :nippy/unthawable) sentexes))
              (is (not-any? record? justifications)))

            (testing "every stored handle is in the dump, at its own handle, in order"
              (is (= (tu/sentex-ids kb) (set (map :id sentexes))))
              (is (= (tu/justification-ids kb) (set (map :id justifications))))
              (is (= (sort (map :id sentexes)) (map :id sentexes))
                  "a dump is a function of the KB, not of map iteration order"))

            (testing "each frame is exactly its record's field map"
              (doseq [frame sentexes]
                (is (= (into {} (v/sentex kb (:id frame))) frame)))
              (doseq [frame justifications]
                (is (= (into {} (v/justification kb (:id frame))) frame))))

            (testing "and carries the key the importer keys our dialect off"
              ;; the discrimination is `:sentence` present on the frame; that the whole
              ;; dump then reads back is `round_trip_test`'s subject, not this one
              (is (every? #(contains? % :sentence) sentexes))
              (is (every? #(and (contains? % :consequence) (contains? % :antecedents))
                          justifications)))))))))

(deftest the-awkward-shapes-survive
  (tu/with-neutral-kb [kb tu/fresh]
    (let [{:keys [bird flies happy Tweety Rex Preferred Deprecated ctx] :as t} (fresh-terms)]
      (build! kb t)
      (with-dirs* 1 "awkward"
        (fn [dir]
          (rm-rf! dir)
          (export/export! kb dir {:compression :gzip})
          (let [{:keys [sentexes justifications provenance]} (dump dir)
                by-id (into {} (map (juxt :id identity)) sentexes)
                terms-of (fn [frame] (set (filter symbol? (tree-seq seq? seq (:sentence frame)))))]

            (testing "a premise carries its assumption strength — that IS the premise mark"
              (is (= :monotonic (:strength (by-id (v/handle-of kb (list bird Tweety) ctx)))))
              (is (= (set (p/premise-ids (:records kb)))
                     (set (keep #(when (:strength %) (:id %)) sentexes)))
                  "and a purely-derived datum carries none"))

            (testing "a negative fact is a frame at :truth :false"
              (let [h (v/handle-of kb (list 'not (list happy Rex)) ctx)]
                (is (some? h))
                (is (= :false (:truth (by-id h))))
                (is (not (v/in? kb h)) "defeated — stored without being believed")))

            (testing "a defeasible rule is a frame with its decomposition and its varmap"
              (let [rule (first (filter :defeasible sentexes))]
                (is (some? rule))
                (is (seq (:antecedent rule)))
                (is (some? (:consequent rule)))
                (is (map? (:varmap rule))
                    "the author's variable names, or every rule renders as ?var0")
                (is (= :both (:direction rule))
                    "a bare implication's direction, canonicalized into the record")))

            (testing "an exceptWhen rides as its own meta-sentex, naming the rule by handle"
              (let [meta-sx (first (filter #(and (seq? (:sentence %))
                                                 (= 'exceptWhen (first (:sentence %))))
                                           sentexes))]
                (is (some? meta-sx))
                (is (some sx/sentex-handle? (tree-seq seq? seq (:sentence meta-sx)))
                    "a handle inside stored content — why handles are preserved")))

            (testing "a datum two rules derive keeps both justifications"
              (let [h     (v/handle-of kb (list flies Tweety) ctx)
                    mine  (filter #(= h (:consequence %)) justifications)]
                (is (= 2 (count (v/supporting-justifications kb h))))
                (is (= 2 (count mine)))
                (is (every? #(and (seq (:antecedents %)) (every? integer? (:antecedents %)))
                            mine)
                    "each names its antecedents by handle, the rule among them")))

            (testing "a merged term keeps both spellings and the twin that migrated"
              (is (v/deprecated? kb Deprecated))
              (is (= Preferred (v/representative kb Deprecated)))
              (is (seq (filter #(contains? (terms-of %) Deprecated) sentexes))
                  "the superseded spelling is still stored")
              (is (seq (filter #(contains? (terms-of %) Preferred) sentexes))
                  "and so is the twin under the representative"))

            (testing "provenance is a [handle map] frame per annotated handle"
              (is (seq provenance))
              (is (every? #(and (vector? %) (= 2 (count %)) (map? (second %))) provenance))
              (doseq [[h prov] provenance]
                (is (= (v/provenance kb h) prov)))
              (is (= "export-test"
                     (get-in (into {} provenance)
                             [(v/handle-of kb (list bird Tweety) ctx) :creator]))))))))))

(deftest every-codec-writes-the-same-frames
  ;; Compression is a stream wrapper around a whole chunk, orthogonal to the nippy
  ;; encoding of the frames inside it — so the codec must change the bytes on disk and
  ;; nothing else, and each chunk must stay independently decompressible.
  (tu/with-neutral-kb [kb tu/fresh]
    (let [t (fresh-terms)]
      (build! kb t)
      (with-dirs* 3 "codecs"
        (fn [& dirs]
          (let [by-codec (into {}
                               (map (fn [codec dir]
                                      (rm-rf! dir)
                                      ;; several chunks, so a per-chunk container is exercised
                                      (export/export! kb dir {:compression codec :chunk-size 4})
                                      [codec (dump dir)])
                                    [:none :gzip :xz] dirs))]
            (doseq [codec [:gzip :xz]]
              (testing (str codec " round-trips through the importer's own reader")
                (is (= codec (:compression (:meta (by-codec codec))))
                    "and says so in meta.edn, since a reader must never infer it")
                (is (= (:sentexes       (by-codec :none)) (:sentexes       (by-codec codec))))
                (is (= (:justifications (by-codec :none)) (:justifications (by-codec codec))))
                (is (= (:provenance     (by-codec :none)) (:provenance     (by-codec codec))))))))))))

(deftest a-kb-with-no-provenance-writes-no-provenance-file
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [likes Ann Bob PlainContext]
      ;; the bulk path stamps no provenance, which is the case the optional file is for
      (v/bulk-assert-facts! kb [(list likes Ann Bob)] PlainContext)
      (with-dirs* 1 "noprov"
        (fn [dir]
          (rm-rf! dir)
          (let [summary (export/export! kb dir {:compression :none})]
            (is (zero? (:provenance summary)))
            (is (not (.exists (io/file dir "provenance.nippy.stream")))
                "an empty stream file is not written at all")
            (is (= 0 (:provenance-count (imp/read-meta dir))))))))))

(deftest provenance-can-be-declined-and-what-is-left-is-a-whole-kb
  ;; Provenance is an open per-handle map with no size bound of its own, so it can
  ;; dominate the records it annotates — 57% of the converted engine KB's dump.  Declining
  ;; it must therefore be possible, and must cost nothing but the annotation: the same
  ;; records, the same justifications, and a dump that still imports.
  (tu/with-neutral-kb [kb tu/fresh]
    (let [t (fresh-terms)]
      (build! kb t)
      (with-dirs* 3 "declineprov"
        (fn [with-dir without-dir store-dir]
          (rm-rf! with-dir) (rm-rf! without-dir)
          (let [with*    (export/export! kb with-dir {:compression :none})
                without  (export/export! kb without-dir {:compression :none
                                                         :provenance? false})
                a        (dump with-dir)
                b        (dump without-dir)]

            (testing "the KB does carry provenance, so the decline is what removes it"
              (is (pos? (:provenance with*)))
              (is (zero? (:provenance without)))
              (is (not (.exists (io/file without-dir "provenance.nippy.stream")))
                  "declined means no file, not an empty one")
              (is (= 0 (:provenance-count (:meta b)))))

            (testing "nothing else changes — the records are the records"
              (is (= (:sentexes with*) (:sentexes without)))
              (is (= (:justifications with*) (:justifications without)))
              (is (= (:sentexes a) (:sentexes b)))
              (is (= (:justifications a) (:justifications b)))
              (is (< (:bytes without) (:bytes with*))
                  "and the dump is smaller, which is the point"))

            ;; the destination is its own `:disk` store in a temp directory rather than
            ;; the shared scratch space, which the outer KB is still holding
            (testing "what is left still imports, into the same KB minus the annotation"
              (let [target (v/open-kb {:backend :disk :dir (.getPath ^File store-dir)
                                       :recover? false})]
                (try
                  (tu/clear-kb! target)
                  (let [summary (imp/import-dump target without-dir)]
                    (is (= (:sentexes without) (:sentexes summary)))
                    (is (= (:justifications without) (:justifications summary)))
                    (is (= (v/sentex-count kb) (v/sentex-count target)))
                    (is (every? #(nil? (v/provenance target %))
                                (p/sentex-ids (:records target)))
                        "no handle carries provenance, and none of them needed it"))
                  (finally (backend/close-dir! (.getPath ^File store-dir))))))))))))

;;; ── backend agnosticism ───────────────────────────────────────────────

(deftest the-same-kb-exports-to-the-same-frames-on-either-backend
  (let [t (fresh-terms)]
    (with-dirs* 3 "parity"
      (fn [mem-dir disk-dir store-dir]
        (rm-rf! mem-dir)
        (rm-rf! disk-dir)
        (tu/with-cleared-kb [mem-kb #(doto (v/open-kb tu/plain-memory-space)
                                       (tu/clear-kb!))]
          (let [store-path (.getPath ^File store-dir)
                disk-kb    (v/open-kb {:backend :disk :dir store-path :recover? false})]
            (try
              (build! mem-kb  t)
              (build! disk-kb t)
              (export/export! mem-kb  mem-dir  {:compression :none})
              (export/export! disk-kb disk-dir {:compression :none})
              (let [a (dump mem-dir) b (dump disk-dir)]
                (testing "the same KB, held two ways, is the same three streams"
                  (is (= (:sentexes a)       (:sentexes b)))
                  (is (= (:justifications a) (:justifications b)))
                  (is (= (:provenance a)     (:provenance b))))
                (testing "and the same meta, but for when it was written"
                  (is (= (dissoc (:meta a) :written-at) (dissoc (:meta b) :written-at))))
                (testing "byte-identically, which is what follows when a frame is a literal"
                  ;; Not the claim — frame equality is — but it holds today, and losing it
                  ;; means a backend handed back an equal-but-differently-typed value (a
                  ;; vector where the other has a list), which is worth knowing about.
                  (doseq [f ["sentexes.nippy.stream" "justifications.nippy.stream"
                             "provenance.nippy.stream"]]
                    (is (java.util.Arrays/equals
                         ^bytes (Files/readAllBytes (.toPath (io/file mem-dir f)))
                         ^bytes (Files/readAllBytes (.toPath (io/file disk-dir f))))
                        (str f " differs byte-for-byte between the backends")))))
              (finally
                (backend/close-dir! store-path)))))))))

;;; ── streaming ─────────────────────────────────────────────────────────

(def ^:private synthetic-scale
  "How many records the streaming test walks.  Big enough that realizing the corpus
  would be a visible mistake, small enough to stay a unit test."
  200000)

(defn- synthetic-store
  "A `RecordStore` that *mints* a sentex per handle instead of holding one, counting
  the fetches.  Only what `export!` reads is implemented — a missing method throws,
  which is the honest way to find out the writer reads more than it says it does."
  [n fetches]
  ;; deliberately partial: an unimplemented method throws `AbstractMethodError`, which
  ;; is the assertion — the writer must read nothing but these four.
  #_{:clj-kondo/ignore [:missing-protocol-method]}
  (reify p/RecordStore
    (sentex-ids        [_] (into #{} (range 1 (inc n))))
    (justification-ids [_] #{})
    (get-sentex [_ id]
      (vswap! fetches inc)
      (sx/->AtomicSentex (list 'synthetic (symbol (str "Ind" id))) 'SyntheticContext
                         id :true nil))
    (get-provenance [_ _] nil)))

(deftest ^:slow the-writer-never-runs-more-than-a-chunk-ahead-of-what-it-has-written
  ;; The constant-memory claim, made checkable: at every chunk boundary the writer has
  ;; fetched at most the frames it has written plus the chunk it is filling.  A `doall`
  ;; or a `vec` over the handle seq fetches all 200k before the first boundary.
  (with-dirs* 1 "stream"
    (fn [dir]
      (rm-rf! dir)
      (let [fetches    (volatile! 0)
            boundaries (volatile! 0)
            chunk-size 1000
            kb         {:records (synthetic-store synthetic-scale fetches)}
            summary    (export/export!
                        kb dir
                        {:compression :none :chunk-size chunk-size
                         :on-progress (fn [{:keys [phase done]}]
                                        (when (= :sentexes phase)
                                          (vswap! boundaries inc)
                                          (is (<= @fetches (+ done chunk-size))
                                              (str "fetched " @fetches " records having written "
                                                   done))))})]
        (is (= synthetic-scale (:sentexes summary)))
        (is (= synthetic-scale @fetches) "every record fetched exactly once")
        (is (= (quot synthetic-scale chunk-size) @boundaries) "one report per chunk")
        (is (= synthetic-scale (:sentex-count (imp/read-meta dir))))))))

(deftest a-cancelled-export-is-not-a-loadable-dump
  ;; `meta.edn` is written last and is the completion marker, so a callback that throws
  ;; (which is how a caller cancels) leaves a directory the catalog does not offer.
  (tu/with-neutral-kb [kb tu/fresh]
    (let [t (fresh-terms)]
      (build! kb t)
      (with-dirs* 1 "cancel"
        (fn [dir]
          (rm-rf! dir)
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cancelled"
                                (export/export! kb dir
                                                {:chunk-size 1
                                                 :on-progress (fn [_] (throw (ex-info "cancelled" {})))})))
          (is (not (.exists (io/file dir "meta.edn"))))
          (is (nil? (catalog/classify dir))
              "and the catalog does not classify what it left behind as a dump"))))))

;;; ── the opts rosters ──────────────────────────────────────────────────

(deftest an-export-or-import-option-nothing-reads-is-refused
  ;; `check-compression!` and `check-variant!` hold the *values* of two known keys;
  ;; the key roster is the check beside them, against a quieter failure: a misspelt
  ;; `:varient` or `:provenence?` takes its default in silence and writes a dump other
  ;; than the one asked for — no index where one was ordered, the unbounded provenance
  ;; stream where it was dropped — under a summary that looks exactly right.
  (tu/with-neutral-kb [kb tu/fresh]
    (with-dirs* 1 "roster"
      (fn [^File dir]
        (rm-rf! dir)
        (testing "export! refuses the misspelt key before the directory exists"
          (let [e (is (thrown? clojure.lang.ExceptionInfo
                               (export/export! kb dir {:varient :records+index})))]
            (is (= :unknown-option (:type (ex-data e))))
            (is (= [:varient] (:unknown (ex-data e))))
            (is (re-find #":variant" (ex-message e)) "the right spelling is in it"))
          (is (not (.exists ^File dir)) "a refused export leaves nothing to clean up"))
        (testing "and a non-map opts the same"
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"must be a map"
                                (export/export! kb dir :gzip))))))
    (with-dirs* 1 "import-roster"
      (fn [^File dir]
        (rm-rf! dir)
        (tu/with-terms [dog Muffet Rex RosterContext]
          (v/assert kb (list dog Muffet) RosterContext)
          (v/assert kb (list dog Rex) RosterContext))
        (export/export! kb dir {:compression :none})
        (tu/with-cleared-kb [target #(tu/isolated-fresh)]
          (testing "import-dump refuses the misspelt flag before reading anything"
            (let [e (is (thrown? clojure.lang.ExceptionInfo
                                 (imp/import-dump target (str dir) {:beleif? false})))]
              (is (= :unknown-option (:type (ex-data e))))
              (is (= [:beleif?] (:unknown (ex-data e))))
              (is (re-find #":belief\?" (ex-message e)))
              (is (zero? (:sentexes (tu/content-count target))) "nothing landed")))
          (testing "and :report-every is a real option, in the roster"
            (let [seen (atom 0)
                  s    (imp/import-dump target (str dir)
                                        {:belief? false :report-every 1
                                         :on-progress (fn [_] (swap! seen inc))})]
              (is (map? s))
              (is (pos? @seen) "the callback ran at the named cadence"))))))))
