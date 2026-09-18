;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.disk.tokens
  "A **durable** token dictionary for a disk store: `symbol/keyword ↔ int`, append-only,
  ids assigned in append order and never reused.  It is what lets a record frame spell
  its sentence as ids rather than names (`vaelii.impl.disk.codec`), which is 2.6× smaller
  than the positional frame it replaces — the vocabulary is written once here instead of
  once per frame in all 100M of them.

  **The ordering that makes it safe.**  A frame referencing an id the dictionary cannot
  decode is unreadable data, so the dictionary must never lag the records that cite it.
  Two rules give that, and neither costs a write:

  - a token is appended **before** the record frame citing it (`emit!` interns as it
    encodes, which happens before the frame is written), so the token log leads the
    record log in *write* order at all times;
  - `fsync` fsyncs this log **first, holding the sentexes kind lock**, so nothing is
    appended between the two fsyncs.  Every record durable after a tick therefore has
    its tokens durable too.

  fsyncing *per new token* would also give the ordering, and is what this did first —
  but it makes a cold load fsync-bound (measured: ~217 records/s, since a new token is
  not rare during one).  Between ticks the two logs can still skew on a machine crash,
  exactly as the record log and its idx can; `open-record-store` repairs it the same way
  it repairs those, by tombstoning a record whose ids the dictionary does not hold.

  **Only symbols and keywords are interned.**  Those are bounded by the ontology.
  Numbers and strings are not — a KB of measurements would mint a dictionary entry per
  distinct value — so `codec` carries them beside the id stream as literals instead.

  Ids are **content-keyed and first-writer-wins**, so they are stable for the life of the
  store; the id *value* depends on first-encounter order, which nothing above this reads.
  Tokens are never deleted (an id must keep decoding), so the log has no dead frames and
  needs no compaction; only a whole-store `clear-records!` empties it.

  Writes take the log's lock (there is one writer, and the append must not interleave);
  the *reverse* map is an atom holding a vector, so a decode — which runs on every fetch,
  under a different lock — reads it without one and still sees a safely published entry."
  (:require [vaelii.impl.disk.files :as f]
            [vaelii.impl.sentex :as sx]
            vaelii.impl.tokens
            [vaelii.impl.types.store :as store-types])
  (:import [java.util HashMap]
           [vaelii.impl.tokens Key]))

;; The forward map is keyed on `tokens/Key`, the same wrapper the in-RAM `TokenDict`
;; keys on, so the two dictionaries agree on what one token is: `hasheq`/`equiv`, under
;; which `2` and `(int 2)` are one entry, where a bare `HashMap` on the token reads them
;; as two.  The record codec only ever interns symbols and keywords, which either keying
;; reads alike; the index snapshot (`vaelii.impl.disk.index-snapshot`) interns every trie
;; token through this same log — numbers and whole compound terms included — and a
;; second durable id for an integral pair leaves the reloaded dictionary one entry short
;; of the log, the `:torn-snapshot` mismatch, on every later open.
;;
;; A log **already holding** such a pair is a different question from writing another
;; one, and it is `duplicate-count` / `repair-duplicates!` below that answer it: the
;; forward map is what collapses the pair, so the two counts differ by exactly the number
;; of frames the log holds twice, and a rewrite is what makes the dictionary reloadable
;; again.  Which caller may rewrite is not this namespace's call — an id is cited by
;; whatever cited it — so the repair is offered and never taken here.

(defn open-token-log
  "Open `dir/tokens.log` and rebuild the in-memory maps from it: frame *i* holds the
  token with id *i*.  A torn trailing frame is truncated exactly as a record log's is,
  which retires the one id it held and leaves every earlier id where it was.  The
  record frames citing that id are the other half of the same cross-file skew, and the
  open repairs them the way it repairs a slot pointing past its log's end: the walk in
  `record-store`'s `rebuild-premises!` tombstones a record whose ids the dictionary
  does not hold, and it runs before anything can mint the retired id again."
  [dir]
  (let [path (str dir "/tokens.log")
        log  (f/open-log path)
        fwd  (HashMap.)
        rev  (volatile! (transient []))]
    ;; the handle is this replay's until the record takes it: a decode that throws
    ;; here propagates to a caller that answers a failed open by releasing the
    ;; directory lock, and a released lock over a handle this JVM still holds is the
    ;; one state `close-dir!` exists to prevent
    (try
      (f/truncate-log! log (f/log-tail-offset log))
      ;; a reloaded token is pooled, so every record decoded through the dictionary shares
      ;; the one vocabulary object per name with the in-memory store — as it did before the
      ;; restart, when the token came from a canonicalized sentence
      (f/scan-log log (fn [_ tok]
                        (let [tok (sx/intern-sym tok)]
                          (.put fwd (Key. tok) (Integer/valueOf (count @rev)))
                          (vswap! rev conj! tok))))
      (store-types/->TokenLog log path fwd (atom (persistent! @rev)) (Object.))
      (catch Throwable t
        (try (f/close! log) (catch Throwable _ nil))
        (throw t)))))

(defn intern!
  "The id for `tok`, allocating (and durably recording) a fresh one if it is new."
  ^long [{:keys [^HashMap fwd rev lock log]} tok]
  (locking lock
    (if-let [id (.get fwd (Key. tok))]
      (long id)
      (let [id (count @rev)]
        ;; written before the frame that cites it; `record-store/fsync` is what orders
        ;; the two fsyncs, holding the sentexes kind lock across them
        (f/append-record! log tok)
        (.put fwd (Key. tok) (Integer/valueOf id))
        (swap! rev conj tok)
        (long id)))))

(defn token
  "The token id `id` decodes to.  An id outside the dictionary means a frame referencing
  a token the dictionary never recorded — unreadable data rather than a nil field, so it
  throws instead of decoding to something plausible."
  [{:keys [rev]} ^long id]
  (let [v @rev]
    (if (< -1 id (count v))
      (nth v id)
      (throw (ex-info (str "token id " id " is not in the dictionary, which holds "
                           (count v) " token(s) — the frame cites an id no entry answers"
                           " to, so the frame or the dictionary is damaged")
                      {:type :damaged-dictionary :id id :dictionary-size (count v)})))))

(defn token-count ^long [{:keys [rev]}] (count @rev))

(defn duplicate-count
  "How many of the log's frames hold a token some earlier frame already holds — Java-unequal
  but Clojure-equal, an integral pair such as `2` and `(int 2)`.

  Zero for a log this build wrote: `intern!` looks the token up under `Key`, so the pair
  never gets a second frame.  A log written before the forward map was keyed that way can
  hold one, and the arithmetic is exact rather than a scan — the reverse vector is one
  entry per frame and the forward map one per *distinct* token, so their difference is
  the number of frames that collapse.

  It is the difference between a dictionary that reloads whole and one that does not, and
  so between an index snapshot that maps and one that is rebuilt on every open forever:
  `index-snapshot/load-dictionary!` re-interns the log in id order, and a collapsing pair
  shifts every id after it — which is what the mapped edges cite."
  ^long [{:keys [^HashMap fwd rev]}]
  (- (count @rev) (.size fwd)))

(defn repair-duplicates!
  "Rewrite the log with each Clojure-equal token once, keeping first-encounter order, and
  return the new entry count.  A no-op returning the current count when there is nothing
  to repair.

  **The ids move**, which is the whole reason this is a separate call rather than
  something `open-token-log` does for itself.  Every id past the first duplicate shifts
  down, so this is only ever legal for a caller whose citations are derived state it is
  about to rebuild — the index snapshot's dictionary, whose ids are cited by the mapped
  trie edges and nothing else, and only once that image is already condemned.  The record
  store's log is the opposite case: its ids are cited by every frame it holds, and there
  is no pair to repair in it anyway (only symbols and keywords are interned there, and
  those are Java-equal exactly when they are Clojure-equal).

  Durable before it returns, because the caller's next act is to trust the new numbering."
  ^long [{:keys [^HashMap fwd rev lock log]}]
  (locking lock
    (let [kept (vec (distinct @rev))]                ; `distinct` is Clojure equality — the pair collapses
      (when (< (count kept) (count @rev))
        (f/truncate! log)
        (.clear fwd)
        (dotimes [i (count kept)]
          (let [tok (nth kept i)]
            (f/append-record! log tok)
            (.put fwd (Key. tok) (Integer/valueOf i))))
        (reset! rev kept)
        (f/force! log true))
      (count kept))))

(defn clear!
  "Empty the dictionary and its log — only for a whole-store wipe, since it invalidates
  every id any surviving frame holds."
  [{:keys [^HashMap fwd rev lock log]}]
  (locking lock
    (f/truncate! log)
    (.clear fwd)
    (reset! rev [])
    nil))

(defn fsync [{:keys [log lock]}]
  (locking lock (f/force! log false)))

(defn close! [{:keys [log lock]}] (locking lock (f/close! log)))
