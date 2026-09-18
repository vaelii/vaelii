;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.snapshot-sink-test
  "The snapshot **sink** protocol (`vaelii.impl.io.snapshot`): one image format, many targets.

  A snapshot is a set of named sections plus a manifest, written through a sink that knows
  only how to stream a section and commit a manifest, and read back through a source.  The
  projection (the index's `[key value]`), the validity check and the install live above the
  sink; the file / memory targets live below it.  Two claims, pulling opposite ways, exactly
  as the index dump has:

  * **portable** — a section written to one sink installs from another, and installs to the
    same index a `reindex` rebuilds from the records;
  * **never trusted** — every way the image could describe other records than the store now
    holds discards the whole image, with a named reason, and the caller rebuilds.  Discarding
    is always safe, which is what makes the cache an optimization rather than a risk."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.io.export :as exp]
            [vaelii.impl.io.fingerprint :as fp]
            [vaelii.impl.io.frames :as frames]
            [vaelii.impl.io.snapshot :as snap]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.types.snapshot :as snapshot-types]
            [vaelii.test-util :as tu])
  (:import (java.io File)
           (java.nio.file Files)
           (java.nio.file.attribute FileAttribute)))

;;; ── scaffolding ───────────────────────────────────────────────────────

(defn- temp-dir ^File [nm]
  (.toFile (Files/createTempDirectory (str "vaelii-snap-" nm "-") (into-array FileAttribute []))))

(defn- rm-rf! [^File d] (doseq [^File f (reverse (file-seq d))] (.delete f)))

(defn- terms []
  (tu/with-terms [bird penguin animal flies feathered parentOf grandparentOf
                  Tweety Opus Ann Bob Cid CxSnap]
    {:bird bird :penguin penguin :animal animal :flies flies :feathered feathered
     :parentOf parentOf :grandparentOf grandparentOf
     :Tweety Tweety :Opus Opus :Ann Ann :Bob Bob :Cid Cid :ctx CxSnap}))

(defn- build!
  "One KB touching every index family: the trie (ragged paths, a numeric token, a negative
  fact), all three roots, the rule index, the exception index and the term index.  A
  snapshot that dropped a family would pass on the ones it kept."
  [kb {:keys [bird penguin animal flies feathered parentOf grandparentOf
              Tweety Opus Ann Bob Cid ctx]}]
  (v/assert kb (list 'genl penguin bird) ctx {:strength :monotonic})
  (v/assert kb (list 'genl bird animal) ctx {:strength :monotonic})
  (v/assert kb (list 'exceptWhen (list penguin '?b)
                     (list 'set/defaultRule
                           (vr/rule-sentence [(list bird '?b)] (list flies '?b))))
            ctx)
  (v/assert kb (vr/rule-sentence [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                                 (list grandparentOf '?x '?z))
            ctx {:direction :forward})
  (v/assert kb (list bird Tweety) ctx {:strength :monotonic})
  (v/assert kb (list feathered Tweety) ctx)
  (v/assert kb (list bird Opus) ctx)
  (v/assert kb (list penguin Opus) ctx)
  (v/assert kb (list parentOf Ann Bob) ctx)
  (v/assert kb (list parentOf Bob Cid) ctx)
  (v/assert kb (list 'bornInYear Tweety 1970) ctx)
  (v/assert kb (list 'not (list feathered Opus)) ctx))

(defn- entries-of [kb] (into #{} (p/index-entries (:index kb))))

(defn- records-stamp
  "The records fingerprint a derived image is valid against, folded over the sentex records
  the way `export!` does.  Commutative and additive, so id order is immaterial — this is
  the portable stamp a `:memory` store computes; a `:disk` store would hash its slots and a
  SQL store would answer a count, all against the same manifest number."
  [kb]
  (let [records (:records kb)
        acc     (fp/accumulator)]
    (doseq [id (p/sentex-ids records)] (acc id (p/get-sentex records id)))
    (acc)))

(defn- answers
  "What the KB retrieves — the belief that reaches a reader *through* the index.  Equal
  before and after a rebuild iff the index is complete either way."
  [kb {:keys [bird flies grandparentOf Tweety Opus Ann Cid ctx]}]
  {:flies-tweety (count (v/sentexes-matching kb (list flies Tweety) ctx))
   :flies-opus   (count (v/sentexes-matching kb (list flies Opus) ctx))
   :grandparent  (count (v/sentexes-matching kb (list grandparentOf Ann Cid) ctx))
   :birds        (count (v/sentexes-matching kb (list bird '?x) ctx))
   :ask-flies    (boolean (seq (v/ask kb (list flies Tweety) ctx)))
   :isa          (v/isa? kb Opus bird)
   :terms        (count (v/terms kb))})

;;; ── the projection installs the same index a rebuild does ──────────────

(deftest a-replayed-image-and-a-rebuilt-index-are-the-same-index
  ;; The required test: save the index through a sink, install it into an emptied
  ;; index, and compare — the entries the index projects, and the answers the KB gives —
  ;; against a `reindex` that rebuilt from the same records.
  (tu/with-cleared-kb [kb tu/fresh]
    (let [t     (terms)
          _     (build! kb t)
          stamp (records-stamp kb)
          medium (snap/memory-medium)]
      (snap/save-index! medium (:index kb) stamp)
      (p/clear-index! (:index kb))
      (is (empty? (entries-of kb)) "the fixture for the replay is a genuinely empty index")
      (let [r (snap/load-index! medium (:index kb) stamp)]
        (is (= :replayed (:index r)) "the sink's image was used, not rebuilt")
        (is (pos? (long (:entries r))))
        (let [replayed-entries (entries-of kb)
              replayed-answers (answers kb t)]
          (p/clear-index! (:index kb))
          (v/reindex kb)
          (is (= replayed-entries (entries-of kb))
              "a replayed index projects a different set than a rebuilt one")
          (is (= replayed-answers (answers kb t))
              "and the KB itself retrieves differently through the two"))))))

;;; ── one image, two sinks ───────────────────────────────────────────────

(deftest an-image-written-to-one-sink-loads-from-another
  ;; Portability is the whole reason for the protocol: the file sink and the memory sink carry
  ;; the same projection, so both install to the index a rebuild produces.  This is the
  ;; sink-level echo of `index_dump_test`'s "every backend exports the same entries".
  (let [dir (temp-dir "cross")]
    (try
      (tu/with-cleared-kb [kb tu/fresh]
        (let [t      (terms)
              _      (build! kb t)
              stamp  (records-stamp kb)
              oracle (entries-of kb)                 ; the entries a rebuild produces
              mem    (snap/memory-medium)]
          (snap/save-index! (snap/file-sink (.getPath dir)) (:index kb) stamp)
          (snap/save-index! mem (:index kb) stamp)
          (doseq [[label source] [["file"   (snap/file-source (.getPath dir))]
                                  ["memory" mem]]]
            (testing label
              (p/clear-index! (:index kb))
              (is (= :replayed (:index (snap/load-index! source (:index kb) stamp))))
              (is (= oracle (entries-of kb))
                  (str "the " label " sink installed a different index than a rebuild"))))))
      (finally (rm-rf! dir)))))

;;; ── one image format, not two ──────────────────────────────────────────

(deftest the-dump-and-the-image-carry-one-index-format
  ;; Step 4's claim, pinned directly: the export dump's index section and a standalone
  ;; snapshot image are one projection through one framing, not two serializations that
  ;; drift.  Both route through `snapshot/index-frames` and `io/frames`, so a dump's on-disk
  ;; index stream reads back as the very seq a fresh `save-index!` writes — a guard against a
  ;; later edit re-forking the copy this refactor removed.  Framed `:none` on both sides so
  ;; the comparison is of the sections themselves, not of a codec.
  (let [dir (temp-dir "one-format")]
    (try
      (tu/with-cleared-kb [kb tu/fresh]
        (let [t     (terms)
              _     (build! kb t)
              stamp (records-stamp kb)
              proj  (vec (snap/index-frames (:index kb)))]   ; the projection both must carry
          (testing "the export dump's index section is the snapshot projection"
            (exp/export! kb (.getPath (File. dir "dump"))
                         {:variant :records+index :compression :none})
            (is (= proj (vec (frames/read-chunked-seq
                              (io/file dir "dump" "index" "entries.nippy.stream") :none)))))
          (testing "and so is the file image's — one format, read back the same way"
            (snap/save-index! (snap/file-sink (.getPath (File. dir "image")) {:compression :none})
                              (:index kb) stamp)
            (is (= proj (vec (snapshot-types/read-section
                              (snap/file-source (.getPath (File. dir "image")))
                              snap/index-section)))))))
      (finally (rm-rf! dir)))))

;;; ── every way the image is doubted, it is discarded ────────────────────

(deftest a-fresh-source-with-no-committed-manifest-is-absent
  (tu/with-cleared-kb [kb tu/fresh]
    (build! kb (terms))
    (let [stamp (records-stamp kb)]
      (is (= {:index :rebuild :reason :absent}
             (snap/load-index! (snap/memory-medium) (:index kb) stamp))
          "a sink that never committed offers no image"))))

(deftest a-file-image-missing-its-manifest-is-absent
  (let [dir (temp-dir "no-manifest")]
    (try
      (tu/with-cleared-kb [kb tu/fresh]
        (build! kb (terms))
        (let [stamp (records-stamp kb)]
          (snap/save-index! (snap/file-sink (.getPath dir)) (:index kb) stamp)
          (is (.delete (File. dir "manifest.edn")) "removed the completion marker")
          (p/clear-index! (:index kb))
          (is (= {:index :rebuild :reason :absent}
                 (snap/load-index! (snap/file-source (.getPath dir)) (:index kb) stamp))
              "sections with no manifest read as no image")))
      (finally (rm-rf! dir)))))

(deftest a-layout-this-build-does-not-key-in-is-discarded
  ;; The sharpest class: an index in another layout would read as *empty* rather than as
  ;; wrong, so nothing downstream would notice.  Both halves of the layout stamp — the
  ;; snapshot format and `kv/index-layout-version` — are checked.
  (tu/with-cleared-kb [kb tu/fresh]
    (build! kb (terms))
    (let [stamp (records-stamp kb)]
      (testing "kv/index-layout-version"
        (let [m (snap/memory-medium)]
          (snap/save-index! m (:index kb) stamp)
          (swap! (:state m) update :manifest assoc :index-layout (inc kv/index-layout-version))
          (is (= {:index :rebuild :reason :layout-changed}
                 (snap/load-index! m (:index kb) stamp)))))
      (testing "the snapshot format version"
        (let [m (snap/memory-medium)]
          (snap/save-index! m (:index kb) stamp)
          (swap! (:state m) update :manifest assoc :format (inc snap/format-version))
          (is (= {:index :rebuild :reason :layout-changed}
                 (snap/load-index! m (:index kb) stamp))))))))

(deftest an-image-for-a-different-store-is-discarded
  ;; The records stamp is what ties an image to the KB it describes.  A bumped digest and a
  ;; genuinely different KB both fail the same way, which is the point — the check does not
  ;; care *why* the records differ, only that they do.
  (tu/with-cleared-kb [kb tu/fresh]
    (build! kb (terms))
    (let [stamp (records-stamp kb)
          m     (snap/memory-medium)]
      (snap/save-index! m (:index kb) stamp)
      (testing "a tampered digest"
        (is (= {:index :rebuild :reason :records-differ}
               (snap/load-index! m (:index kb) (update stamp :digest inc)))))
      (testing "a genuinely different store"
        (tu/with-cleared-kb [other tu/fresh]
          (tu/with-terms [rel Aye Bee CxOther]
            (v/assert other (list rel Aye Bee) CxOther))
          (is (= {:index :rebuild :reason :records-differ}
                 (snap/load-index! m (:index kb) (records-stamp other)))))))))

(deftest a-truncated-section-is-discarded-and-installs-nothing-of-itself
  ;; A torn nippy chunk is indistinguishable from a clean EOF, so truncation shows only as a frame count
  ;; below what the manifest recorded — caught while installing, not in `decision`.
  (let [dir (temp-dir "truncated")]
    (try
      (tu/with-cleared-kb [kb tu/fresh]
        (let [t     (terms)
              _     (build! kb t)
              stamp (records-stamp kb)
              sink  (snap/file-sink (.getPath dir) {:compression :none})]
          (snap/save-index! sink (:index kb) stamp)
          ;; drop the last frame from the section, leaving the manifest's count too high
          (let [^File f  (File. dir "index.nippy.stream")
                existing (vec (frames/read-chunked-seq f :none))]
            (is (> (count existing) 1) "need at least two frames to truncate one away")
            (frames/write-frames! f (butlast existing) {:compression :none :chunk-size 10000}))
          (p/clear-index! (:index kb))
          (let [r (snap/load-index! (snap/file-source (.getPath dir)) (:index kb) stamp)]
            (is (= {:index :rebuild :reason :entries-truncated} r)))
          (testing "and the KB is whole after the caller rebuilds — discarding is always safe"
            (v/reindex kb)
            (is (pos? (count (v/sentexes-matching kb (list (:bird t) '?x) (:ctx t))))
                "a rebuild after a discarded image left the KB unqueryable"))))
      (finally (rm-rf! dir)))))

(deftest a-frame-that-is-not-a-key-value-pair-is-refused-rather-than-installed
  ;; An index image is several entries per record, so the install checks a batch rather
  ;; than realizing the stream to inspect it — and the check is what stands between a
  ;; stream some other tool wrote and an index quietly holding whatever `index-load` made
  ;; of it.  Both places an index arrives from a file take this one install, so both
  ;; refuse alike.
  (tu/with-cleared-kb [kb tu/fresh]
    (let [index   (:index kb)
          refused (fn [frames]
                    (try (snap/install-entries! index frames)
                         nil
                         (catch clojure.lang.ExceptionInfo e (ex-data e))))]
      (is (= :malformed-entry (:type (refused [:not-a-pair]))) "a frame that is not a pair")
      (is (= :malformed-entry (:type (refused [[:k 1 2]]))) "a triple is not a pair either")
      (testing "the whole batch is checked before any of it is installed"
        (is (= :malformed-entry (:type (refused [[[:functor-root 'dog] #{1}] :not-a-pair]))))
        (is (empty? (entries-of kb))
            "a refused batch left nothing behind for the caller's rebuild to double")))))

;;; ── constant memory ────────────────────────────────────────────────────

(defn- unchunked
  "A deliberately unchunked lazy seq of `n` frames — Clojure's `map` realizes 32 at a
  time, which would mask the per-chunk property this test is about.  `on-realize` fires as
  each element is produced."
  [i n on-realize]
  (lazy-seq
   (when (< (long i) (long n))
     (on-realize i)
     (cons {:k i :v i} (unchunked (inc i) n on-realize)))))

(deftest the-writer-holds-one-chunk-not-the-corpus
  ;; The property that makes the sink usable at 100M: the writer never realizes more than a
  ;; chunk ahead of what it has already flushed.  `write-frames!` builds a chunk, flushes
  ;; it, and only then pulls the next — so at the moment frame `i` is realized the frames
  ;; already written number `⌊i/chunk⌋·chunk`.  `partition-all` peeks exactly one element
  ;; into the next chunk to find the boundary, so the realized-ahead figure tops out at one
  ;; whole `chunk` and never approaches the corpus.  Were the writer buffering everything,
  ;; this would climb toward `n`.  Asserted on the shared framing the file sink writes
  ;; through.
  (let [dir     (temp-dir "constant")
        chunk   4
        n       40
        flushed (volatile! 0)
        peak    (volatile! 0)]
    (try
      (let [^File f (File. dir "section.nippy.stream")
            src (unchunked 0 n (fn [i]
                                 (vswap! peak max (- (long i) (long @flushed)))))
            written (frames/write-frames!
                     f src {:compression :none :chunk-size chunk
                            :on-chunk (fn [done] (vreset! flushed done))})]
        (is (= n written) "every frame was written")
        (is (<= (long @peak) chunk)
            (str "the writer realized " @peak " frames ahead of the flush — more than the "
                 chunk "-frame chunk, so it is not streaming a chunk at a time"))
        (is (< (long @peak) (quot n 2))
            "the writer's footprint tracks the corpus, not the chunk")
        (is (= n (count (vec (frames/read-chunked-seq f :none))))
            "and the file round-trips to the whole corpus"))
      (finally (rm-rf! dir)))))

(deftest a-reader-dropped-early-releases-its-file
  ;; The chunked reader is a lazy seq over an open file, and a consumer that stops
  ;; before the end — an install refusing a frame, a `take` — cannot be seen by the seq.
  ;; `close-frames!` closes the stream on request; a failure inside the seq closes it
  ;; before the throw travels; and the file is released when the seq is dropped.
  (let [dir (temp-dir "release")]
    (try
      (let [^File f (File. dir "section.nippy.stream")
            n      40]
        (frames/write-frames! f (map (fn [i] [i (str "v" i)]) (range n))
                              {:compression :none :chunk-size 4})
        (testing "closed on request, mid-read, the rest of the seq is refused rather than read"
          (let [s (frames/read-chunked-seq f :none)]
            (is (= [0 "v0"] (first s)))
            (frames/close-frames! s)
            (frames/close-frames! s)                     ; idempotent
            (is (thrown? java.io.IOException (dorun (drop 4 s)))
                "the chunk after the one already thawed needs the stream, and it is closed")))
        (testing "a full read closes the stream itself, and a second close is harmless"
          (let [s (frames/read-chunked-seq f :none)]
            (is (= n (count s)))
            (frames/close-frames! s)))
        (testing "a torn chunk closes the stream before the failure travels"
          (let [^File torn (File. dir "torn.nippy.stream")]
            (io/copy f torn)
            ;; overwrite the second chunk's payload with bytes no thaw accepts, keeping
            ;; its length prefix intact so the reader asks the stream for it
            (with-open [raf (java.io.RandomAccessFile. torn "rw")]
              (let [len (.readInt raf)]
                (.seek raf (+ 4 len 4))
                (.write raf (byte-array 16 (byte 0x7f)))))
            (let [s (frames/read-chunked-seq torn :none)]
              (is (= [0 "v0"] (first s)) "the first chunk thaws")
              (is (thrown? Exception (dorun (drop 4 s))) "the second does not")
              (frames/close-frames! s)))))                   ; closed under the failure; a no-op
      (finally (rm-rf! dir)))))

;;; ── the record hash across builds ─────────────────────────────────────

;; An index dump carries the fingerprint of the records it was derived from, and the reader
;; recomputes that fingerprint with the running build.  The two digests are literals, so a
;; change to what `record-hash` reads of a rule or of a negative literal fails here instead
;; of discarding the index of every dump already written.
(deftest a-record-hash-is-the-same-in-every-build
  (let [kb   (v/open-kb {:backend :memory :space (gensym "recordhash")})
        recs (:records kb)
        rule (p/get-sentex recs (v/assert kb '(set/forwardRule
                                               (implies (and (likes ?x ?y) (not (sells ?x ?y)))
                                                        (keeps ?x ?y)))
                                          'CxTest))
        lit  (p/get-sentex recs (v/assert kb '(not (sells Muffet Tom)) 'CxTest))]
    (is (= 4125258215038561605 (fp/record-hash 1 rule)) "a rule hashes its implies form")
    (is (= 3244354055351357446 (fp/record-hash 1 lit))
        "a negative literal hashes its sentence and its sign")))
