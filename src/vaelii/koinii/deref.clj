;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.koinii.deref
  "Koinii cross-seat dereference: the DISTRIBUTED topology, where
  independent *seats* — separate processes, each holding its own copy of the KB — stay
  in sync by **content-addressed commits** rather than by sharing one live daemon.  A
  seat asserts a sentence and commits; another seat pulls the same commit and resolves
  the same sentence **from its own KB**.  The locator travels over a transport; the
  proof comes from the KB, and neither seat trusts the marker.

  A different deployment shape from koinii's default (N agents funnelling writes through
  one single-writer daemon — `docs/koinii.md`, *The deployment shape*).  There the
  daemon IS the shared KB and dereference is a plain read; here each seat is its own
  reader with its own store, and the shared reference point is a commit, not a socket.
  Complements, not rivals: the daemon for live co-writing, this for disconnected or
  independently-replicated seats.

  The spike's vocabulary, mapped to real primitives:

  - **seat** — an independent KB-holding process.  In this layer a seat is just a `kb`;
    every function takes one, exactly as the other koinii modules do.
  - **locator / marker** — a content-addressed reference to a canonical assertion (the
    `locator`), plus the untrusted transport payload that carries it (the `marker`).
  - **transport** — any byte-faithful channel that carries a marker.  A marker is a
    plain Clojure map, so any transport that ships EDN ships one.
  - **the KB** — the sole authority for *meaning*.  A marker is never trusted, only
    resolved: `dereference` finds the sentence in the seat's own store, reads its
    provenance, and hands off to `why` for the proof.

  Three ideas, each grounded on a primitive that ships:

  - **The locator is content-addressed, not handle-addressed.**  A handle is a number
    one store minted and does not travel; a locator is a **self-describing** digest — the
    literal `\"sha256:\"` followed by 64 lowercase hex chars — over a sentex's **canonical
    identity** (its context, polarity, and canonicalized sentence,
    `docs/canonicalization.md`).  Three best-practice commitments live in that one string:
      * **SHA-256, not SHA-1.**  A locator is a tamper-detection boundary — `dereference`
        rehashes the *resolved* form and compares — and SHA-1 has practical chosen-prefix
        collisions, so it is the wrong primitive for this job.
      * **Self-describing.**  The `\"sha256:\"` multihash-style tag names the algorithm in
        the value itself, so a later migration to another primitive is unambiguous rather
        than a silent reinterpretation of 64 anonymous hex chars.
      * **A spec'd canonical encoding, not `pr-str`.**  The digest input is the explicit,
        type-tagged, self-delimiting byte encoding `vaelii.core/digest` hashes — independent of
        ambient `*print-*` vars and injective across the value space a sentence holds, so
        a symbol never digests as the like-spelled string and `(a b)` never as `(a (b))`.
    Two seats holding the same assertion compute the **same** locator, because `v/import!`
    re-canonicalizes every record through the reading build's own constructor.
  - **The commit is a Merkle function of belief.**  `commit-id` is the RFC-6962-style
    **Merkle root** over the seat's *sorted* per-sentex leaf digests — leaf hashing
    domain-separated with a `0x00` byte and internal-node hashing with `0x01`, so a leaf
    can never be forged as an internal node — prefixed `\"sha256:\"`.  The leaves are the
    records the seat **believes**, not everything it stores: a defeated default is retained
    on purpose and is no part of what the seat holds, so two seats that agree on every
    belief compute one id however differently their stores were built.  Order- and
    handle-independent, so two seats that reached the same beliefs by different routes
    compute the same commit id (belief and storage are order-independent —
    `docs/nmtms.md`), and a KB exported, pulled and recovered on another seat carries the
    id across.  A sentence that names a sentex by `(sentexHandle n)` — every koinii
    response act — digests the named record's own identity in place of `n`
    (`v/digest`), so a reply is located by its target and two seats that built one
    conversation in different orders agree on it.  The Merkle shape buys pure auditability:
    `inclusion-proof` yields an audit path and `verify-inclusion` recomputes the root from
    just a `(locator, proof)` pair — no KB — which a flat digest cannot.  `commit-id` fingerprints **knowledge** (what two seats compare to agree they
    hold the same thing); `state-root` is a second root whose leaves fold each record's
    provenance (`:creator` + `:created` + identity), a full **snapshot** identity like a
    git commit (covers who/when), so it moves when provenance moves even when content does
    not.  `publish!` / `pull!` move the bytes (via `v/export!` / `v/import!`); the roots
    are what say two seats hold the same knowledge (and the same snapshot).
  - **The marker is untrusted.**  `dereference` finds the sentence in the seat's own KB
    and rehashes what it found; a stale or tampered marker fails that check and is
    rejected, and a marker the seat cannot resolve means the commit was not received —
    never that the marker's payload should be believed.  Resolution is scoped to BELIEF
    for the reason the commit is: a record the seat stores but does not believe is no part
    of what it holds, so `dereference` declines it exactly as `inclusion-proof` declines to
    prove it.  A locator alone resolves nothing: the marker's sentence and context find the
    record, and the locator checks it.  `dereference` also **fails closed on a malformed
    payload**, as `verify-inclusion` does on a malformed proof: a marker that is not a
    map, whose `:locator` is not this format, or whose sentence the engine declines to be
    asked about is ANSWERED `:malformed` rather than allowed to throw the engine's
    refusal out of the resolve path — a peer must not be able to crash a receiving seat by
    sending garbage.  Attribution is trustworthy only as far as the identity model makes
    it: a distributed KB inherits the same cooperative-vs-proof-tier question.

  Additive, like the other koinii modules: only the public core API — the record walk
  is `handles` / `sentex`, and the locator is `digest` / `digests`, so a seat digests
  what the store itself would.  Beside it, koinii `types`.  Nothing under
  `vaelii.impl`, and nothing in core loads it."
  (:require [clojure.walk :as walk]
            [vaelii.core :as v]
            [vaelii.koinii.identity :as id]
            [vaelii.koinii.types :as koinii-types])
  (:import (java.security MessageDigest)))

;; ---- the locator: `vaelii.core/digest` ---------------------------------------

(def ^:private locator-prefix
  "The algorithm tag a locator and a Merkle root carry."
  "sha256:")

(def ^:private sha256-hex-re
  "The body of every digest this module reads: 64 lowercase hex characters."
  #"[0-9a-f]{64}")

(defn- sha256
  "The raw 32-byte SHA-256 of `data`."
  ^bytes [^bytes data]
  (.digest (MessageDigest/getInstance "SHA-256") data))

(defn- hex
  "Lowercase hex of a byte array."
  [^bytes b]
  (apply str (map #(format "%02x" %) b)))

(defn- unhex
  "The inverse of `hex`: a lowercase-hex string back to its byte array.  For
  `verify-inclusion`, which must rebuild sibling digests from a transported proof."
  ^bytes [^String s]
  (let [n (quot (count s) 2)
        b (byte-array n)]
    (dotimes [i n]
      (aset-byte b i (unchecked-byte (Integer/parseInt (subs s (* 2 i) (+ 2 (* 2 i))) 16))))
    b))

(defn- sign-of
  "`:negative` when `sx` is a negative literal — its sentence a `(not S)` — and
  `:positive` otherwise: the `:polarity` a resolution reports."
  [sx]
  (let [s (:sentence sx)]
    (if (and (nil? (:antecedent sx)) (sequential? s) (= 2 (count s)) (= 'not (first s)))
      :negative
      :positive)))

(defn- digesting
  "`(f)`, with the engine's `:not-encodable` refusal of a value the locator encoding does
  not cover rethrown as `:koinii/uncanonical-value`, naming the value's `:class`."
  [f]
  (try (f)
       (catch clojure.lang.ExceptionInfo e
         (let [d (ex-data e)]
           (if (= :not-encodable (:type d))
             (throw (ex-info (str "koinii: " (ex-message e))
                             (assoc d :type :koinii/uncanonical-value
                                    :class (or (:class d) (class (:value d))))
                             e))
             (throw e))))))

(defn- locators
  "`v/digests` over `handles`, under `digesting`."
  ([kb handles] (digesting #(v/digests kb handles)))
  ([kb handles opts] (digesting #(v/digests kb handles opts))))

(defn locator-of
  "The locator of the stored sentex at `handle` (`v/digest`): independent of the handle,
  so reproducible on any seat that holds the same assertion.  nil if the handle names no
  record."
  [kb handle]
  (koinii-types/needs-kb! `locator-of kb)
  (digesting #(v/digest kb handle)))

(defn locate
  "The locator `sentence` in `context` **would** have, computed without requiring it be
  stored (`v/digest`'s three-arity): `(locate kb S C)` equals `(locator-of kb h)` for the
  handle `h` that `S`/`C` resolves to."
  [kb sentence context]
  (koinii-types/needs-kb! `locate kb)
  (digesting #(v/digest kb sentence context)))

;; ---- the Merkle commit: an auditable, domain-separated tree over the state -

;; RFC-6962-style hashing: a leaf digest is over `0x00 || data` and an internal node over
;; `0x01 || left || right`.  The domain-separating prefix is what stops a leaf digest from
;; being replayed as an internal node (or vice versa) — the classic Merkle second-preimage
;; hole — so an inclusion proof cannot be forged by presenting a leaf as a subtree.

(defn- leaf-hash
  "The RFC-6962 leaf digest of a locator string: SHA-256(0x00 || utf8(locator)).  Keyed on
  the locator alone (not the sentex), so `verify-inclusion` can rebuild it without the KB."
  ^bytes [^String locator]
  (let [lb  (.getBytes locator "UTF-8")
        buf (byte-array (inc (alength lb)))]
    (aset-byte buf 0 0)                         ; 0x00 — leaf domain
    (System/arraycopy lb 0 buf 1 (alength lb))
    (sha256 buf)))

(defn- internal-hash
  "The RFC-6962 internal-node digest: SHA-256(0x01 || left || right)."
  ^bytes [^bytes l ^bytes r]
  (let [buf (byte-array (+ 1 (alength l) (alength r)))]
    (aset-byte buf 0 1)                          ; 0x01 — internal domain
    (System/arraycopy l 0 buf 1 (alength l))
    (System/arraycopy r 0 buf (inc (alength l)) (alength r))
    (sha256 buf)))

(def ^:private empty-tree-root
  "The explicit empty-tree root: MTH({}) = SHA-256 of the empty input, prefixed.  A KB
  with no records has this `commit-id`, a defined value rather than an accident of the
  fold."
  (str locator-prefix (hex (sha256 (byte-array 0)))))

(defn- sorted-leaves
  "The sorted vector of leaf digests for `locators` — leaf-hash each, then order by
  unsigned lexicographic byte comparison, which over equal-width digests is exactly hex
  order.  Sorting is what makes the root a function of the *set*: two seats at the same
  state build the identical tree.  Compared as bytes rather than by a hex key:
  `sort-by` runs its keyfn inside the comparator, so a `(sort-by hex …)` would rebuild
  the 64-char key ~2·n·log₂n times — 32 Formatter allocations each — on the path
  `commit-id` folds every believed sentex through."
  [locators]
  (->> locators
       (map leaf-hash)
       (sort (fn [^bytes a ^bytes b] (java.util.Arrays/compareUnsigned a b)))
       vec))

(defn- largest-pow2-below
  "The largest power of two strictly less than `n` (`n` > 1) — RFC-6962's split point."
  [n]
  (loop [k 1] (if (< (* 2 k) n) (recur (* 2 k)) k)))

(defn- merkle-node
  "The RFC-6962 Merkle Tree Hash of a non-empty vector of leaf digests: a single leaf is
  itself; otherwise SHA-256(0x01 || MTH(left) || MTH(right)) over the largest-power-of-two
  split.  Rebuilt from scratch each call, O(n log n) in the leaf count."
  ^bytes [leaves]
  (case (count leaves)
    1 (nth leaves 0)
    (let [n (count leaves)
          k (largest-pow2-below n)]
      (internal-hash (merkle-node (subvec leaves 0 k))
                     (merkle-node (subvec leaves k n))))))

(defn- merkle-root
  "The self-describing Merkle root over `locators` — `\"sha256:\"` + hex of the tree hash,
  or the empty-tree root for none."
  [locators]
  (let [leaves (sorted-leaves locators)]
    (if (empty? leaves)
      empty-tree-root
      (str locator-prefix (hex (merkle-node leaves))))))

(defn- audit-path
  "The RFC-6962 audit path for the leaf at index `m` in `leaves`: a vector of
  `{:hash <sibling-hex> :side :left|:right}` ordered leaf→root, `:side` naming which side
  the sibling sits on.  Folding these into the leaf digest reproduces the root."
  [m leaves]
  (if (= 1 (count leaves))
    []
    (let [n (count leaves)
          k (largest-pow2-below n)]
      (if (< m k)
        (conj (audit-path m (subvec leaves 0 k))
              {:hash (hex (merkle-node (subvec leaves k n))) :side :right})
        (conj (audit-path (- m k) (subvec leaves k n))
              {:hash (hex (merkle-node (subvec leaves 0 k))) :side :left})))))

(defn- leaf?
  "Does the seat's commit hold `h`: believed (`v/believed?`), and not a `contradicts` or
  `defeat` the engine placed for a nogood, which names its members by this seat's
  handles and records a clash among the beliefs rather than a belief of its own."
  [kb h]
  (and (v/believed? kb h)
       (not (and (contains? '#{contradicts defeat} (first (:sentence (v/sentex kb h))))
                 (not (v/premise? kb h))))))

(defn- believed-handles
  "The handles this seat **believes**: `v/handles` (storage) narrowed by `leaf?`, the belief
  filter the extent readers spell `{:believed? true}`.  Every commit identity is built from
  this enumeration, since two seats compare a commit id to agree they hold the same thing,
  and a seat holds what it believes.  A stored-but-defeated sentex or a conclusion whose
  support was withdrawn (`docs/nmtms.md`) would make the id a function of a seat's
  *retraction history*."
  [kb]
  (filter #(leaf? kb %) (v/handles kb)))

(defn commit-id
  "A content-addressed fingerprint of the seat's **believed knowledge**: the RFC-6962 Merkle
  root over its sorted per-sentex content locators, prefixed `\"sha256:\"`.  Order- and
  handle-independent, so two seats believing the same records compute the same id (a
  `(sentexHandle n)` inside a sentence digests the record it names, `v/digest`), and a KB
  exported, pulled and recovered on another seat carries it across.

  Scope is every BELIEVED sentex, premises and forward-derived alike, read as CONTENT
  (context/polarity/sentence, not provenance).  A stored-but-defeated sentex is **not** a
  leaf, so two seats agree exactly when their believed sets match: the pull flow guarantees
  that, and independently built seats meet it only if they derived to the same extent (same
  rules, same `*max-depth*`).  For attribution-sensitive identity, see `state-root`."
  [kb]
  (koinii-types/needs-kb! `commit-id kb)
  (merkle-root (locators kb (vec (believed-handles kb)))))

(defn state-root
  "A content-addressed **snapshot** identity of the seat's believed records: the Merkle
  construction of `commit-id` over the same believed set, with leaves that fold each
  record's provenance (`:creator` + `:created`) in with its identity.  It moves when
  provenance moves even if `commit-id` does not.  Two seats compare `commit-id` to agree on
  *knowledge* and `state-root` to agree on the *snapshot*.  It is belief-scoped for
  `commit-id`'s reason, so the two roots cover one set of records."
  [kb]
  (koinii-types/needs-kb! `state-root kb)
  (merkle-root (locators kb (vec (believed-handles kb)) {:provenance? true})))

(defn inclusion-proof
  "The audit path proving `locator` is a leaf of this seat's `commit-id` tree: a vector of
  `{:hash <sibling-hex> :side :left|:right}` ordered leaf→root, or nil if the seat does not
  BELIEVE a record with that locator.  A verifier fed this path, the leaf `locator` and the
  published root confirms inclusion via `verify-inclusion` **without** the KB.  It folds
  the same believed leaves as `commit-id`, so a stored-but-defeated record answers nil."
  [kb locator]
  (koinii-types/needs-kb! `inclusion-proof kb)
  (let [leaves (sorted-leaves (locators kb (vec (believed-handles kb))))
        target (hex (leaf-hash locator))
        m      (first (keep-indexed (fn [i l] (when (= target (hex l)) i)) leaves))]
    (when m (audit-path m leaves))))

(defn- valid-sibling?
  "A well-formed audit-path step: a 64-hex sibling digest (a SHA-256, so exactly 64
  lowercase hex) and a `:left`/`:right` side.  A proof arrives over the UNTRUSTED
  transport, so `verify-inclusion` checks each step and fails closed — a malformed
  `:hash` must make verification return false, not throw out of `unhex`."
  [step]
  (and (map? step)
       (string? (:hash step))
       (re-matches sha256-hex-re (:hash step))
       (contains? #{:left :right} (:side step))))

(defn verify-inclusion
  "PURE verification that `locator` is included under `root` given `proof`: recompute the
  Merkle root from the leaf digest of `locator` and the audit path's sibling hashes, and
  compare to `root`.  Takes no KB.  Domain separation (`0x00` leaf / `0x01` node) is
  enforced on both sides.  **Fails closed on a malformed proof**: a non-hex sibling, a
  missing `:hash`/`:side`, or a non-sequential proof returns `false`, not a throw."
  [locator proof root]
  (and (string? locator)
       (sequential? proof)
       (every? valid-sibling? proof)
       (let [node (reduce (fn [^bytes acc {:keys [hash side]}]
                            (let [sib (unhex hash)]
                              (if (= :right side)
                                (internal-hash acc sib)
                                (internal-hash sib acc))))
                          (leaf-hash locator)
                          proof)]
         (= root (str locator-prefix (hex node))))))

;; ---- publish / pull: the git-distributable serialization -----------------

(defn publish!
  "Write the seat's KB out as a portable export dump in `dir`, the form a git host carries:
  `v/export!` with `:compression :none`, so the record streams are a byte-stable function
  of the KB (gzip writes a header timestamp).  `dir` must be absent or empty.  Returns
  `export!`'s summary; the commit the other seats pull is this directory.
  **`:compression` is fixed**: anything but `:none` is refused
  (`:koinii/compression-fixed`); a caller that wants a compressed dump wants `v/export!`.
  Every other `export!` option passes through."
  ([kb dir] (publish! kb dir {}))
  ([kb dir opts]
   (koinii-types/needs-kb! `publish! kb)
   (when-let [c (:compression opts)]
     (when-not (= :none c)
       (throw (ex-info (str "koinii: publish! requires :compression :none — a published commit's"
                            " record streams are a byte-stable function of the KB, and "
                            (pr-str c) " writes bytes that are not; export! takes it directly")
                       {:type :koinii/compression-fixed :compression c}))))
   (v/export! kb dir (assoc opts :compression :none))))

(defn pull!
  "Open a pulled commit into the seat `kb`: `v/import!` the dump at `dir`, which
  re-canonicalizes every record through this build's constructor and recovers belief, so
  this seat computes the same locators as the publisher.  A seat that is a fork takes the
  dump as its base and keeps its own writes and their attestations over it
  (`identity/rebase!`); any other seat must be empty (`:not-empty`).  Every provenance
  `:principal` is dropped (`:drop-principal?`).  A seat registering a reasoner set other
  than the publisher's is refused (`:reasoner-mismatch`); `{:reasoners :stored}` registers
  the publisher's set.  Returns `import!`'s summary."
  ([kb dir] (pull! kb dir {}))
  ([kb dir opts]
   (koinii-types/needs-kb! `pull! kb)
   (id/rebase! kb dir (assoc opts :drop-principal? true))))

;; ---- the marker: the untrusted transport payload -------------------------

(defn- named-handles
  "The distinct handle numbers `sentence` names by `(sentexHandle n)`, in walk order."
  [sentence]
  (into [] (comp (filter v/sentex-handle?) (map v/handle-id) (distinct))
        (tree-seq sequential? seq sentence)))

(defn- marker-at
  "`marker`'s body, with `path` the handles whose markers are being built around this one:
  a handle on it is left out of `:targets`, so a record that names itself, or names a
  record naming it back, yields a finite marker."
  [kb handle path]
  (let [sx (v/sentex kb handle)]
    (when (nil? sx)
      (throw (ex-info (str "koinii: no sentex at handle " (pr-str handle)
                           " — it names no record in this KB")
                      {:type :koinii/no-such-handle :handle handle})))
    (let [path'   (conj path handle)
          targets (into {}
                        (keep (fn [n]
                                (when (and (not (some #{n} path')) (v/sentex kb n))
                                  [n (marker-at kb n path')])))
                        (named-handles (v/sentence-of sx)))]
      (cond-> {:locator  (locator-of kb handle)
               ;; the stored `:sentence` IS the asserted form for BOTH signs — a negative
               ;; sentex keeps its `(not …)` in `:sentence` (docs/storage.md), and the sign
               ;; is read off that head — so `handle-of` finds it by this field unchanged.
               ;; The field travels raw: it is not re-wrapped in `not`, which would
               ;; double-negate a negative fact into a positive one that resolves to
               ;; nothing (`:not-received`).
               :sentence (v/sentence-of sx)
               :context  (:context sx)
               :seat     (:creator (v/provenance kb handle))}
        (seq targets) (assoc :targets targets)))))

(defn marker
  "The transportable marker for the assertion at `handle`, which a seat sends over a
  transport so another seat can dereference it:

      {:locator <sha256:hex>  :sentence <asserted form>  :context <ctx>  :seat <claimed>
       :targets {n <marker> …}}

  The `:locator` decides it; `:sentence` / `:context` are a lookup payload the receiver does
  NOT trust (it resolves against its own KB and rehashes), and `:seat` is the *claimed*
  asserter, the real one coming off the resolved sentex's provenance.  Throws if `handle`
  names no record.  **`:targets` carries the marker of every record the sentence names**:
  a reply's sentence holds `(sentexHandle n)` with this seat's number, which a seat that
  built the same conversation itself numbers differently.  `dereference` resolves each target
  on its own seat first and substitutes the handle it finds.  The key is absent when the
  sentence names no stored record; a handle already on the chain being built is left out
  (`marker-at`)."
  [kb handle]
  (koinii-types/needs-kb! `marker kb)
  (marker-at kb handle []))

;; ---- dereference: resolve a marker against the seat's OWN KB --------------

(defn- malformed
  "The answer an untrusted payload gets when it is not the thing it claims to be:
  `:reason :malformed`, `:problem` naming the part that failed, and the `:locator`
  echoed back exactly as it arrived (nil when none did).

  A distinct reason from `:not-received` on purpose.  \"I do not hold that\" and \"that is
  not a marker\" are different facts about a peer — one is out of sync and will catch up
  with the next pull, the other is sending garbage and never will — and folding them
  together loses the only signal a seat has for telling them apart."
  [problem locator]
  {:resolved? false :reason :malformed :problem problem :locator locator})

(defn- marker-problem
  "The `:problem` keyword a malformed `marker` earns, or nil when it is shaped like one.
  Three commitments: it is a **map**; its `:locator` is the string format `v/digest?`
  checks; and it carries **both** `:sentence` and `:context`, since a bare locator names no
  record (`docs/storage.md`, \"Content digests\").  What is *in* those keys is not judged
  here: `handle-lookup` asks the engine.  `:seat` is not required, since `dereference`
  never reads it."
  [marker]
  (cond
    (not (map? marker))                       :not-a-map
    (not (v/digest? (:locator marker))) :locator
    (not (contains? marker :sentence))        :no-sentence
    (not (contains? marker :context))         :no-context))

(def ^:private request-refusals
  "The `ex-info` `:type`s `v/handle-of` raises about the **request**, not the knowledge:
  `:shape` (a payload the engine will not read as one sentence) and `:unsupported-context`
  (a query context, which names no stored sentex).  Any OTHER exception out of that read is
  this seat's problem and is re-thrown, since reporting a broken store as a hostile peer
  would launder a real failure."
  #{:shape :unsupported-context})

(defn- handle-lookup
  "`v/handle-of` as a value: `{:handle h-or-nil}` when the engine consents to the question,
  `{:refused <type>}` when it declines the request outright.  A marker's `:sentence` is
  untrusted and judged by the ENGINE's grammar, not a copy here.  `v/check` is the wrong
  entry point: it runs `assert`'s whole pipeline against the CURRENT KB, so a sentence
  stored before an `argIsa` was declared would fail it while the seat holds and believes
  that record.  So ask the entry point the resolution goes through: where `handle-of`
  consents, its nil stands as \"I do not hold that\".  Nothing a seat can STORE trips the
  refusal, so a genuine marker never reads as malformed."
  [kb sentence context]
  (try
    {:handle (v/handle-of kb sentence context)}
    (catch clojure.lang.ExceptionInfo e
      (let [t (:type (ex-data e))]
        (if (request-refusals t)
          {:refused t}
          (throw e))))))

(def ^:private max-target-depth
  "How deep a chain of `:targets` markers `dereference` follows before it answers
  `:malformed` with `:problem :targets`.  Each level is one reply naming the level below,
  and the chain arrives over an untrusted transport, so its depth is bounded before the
  recursion reads it."
  64)

(defn- targets-problem
  "True when `marker`'s `:targets` is present and not a map of integer handle numbers to
  maps.  The values are judged as markers when `local-handle` resolves them."
  [marker]
  (let [t (:targets marker)]
    (and (contains? marker :targets)
         (not (and (map? t) (every? (fn [[k m]] (and (integer? k) (map? m))) t))))))

(defn- local-handle
  "The handle of `marker`'s sentence in THIS seat's store, as `{:handle h}`, or the failure
  map `dereference` answers with.  Each `:targets` marker is resolved here first, and every
  `(sentexHandle n)` in the sentence is rewritten to the handle its target has on this
  seat.  A target is looked up in storage, not belief, and its locator is not compared: the
  reply's locator digests each target's identity.  A failing target fails the reply with its
  reason, and `:target` names the sender's number."
  [kb marker depth]
  (let [locator (when (map? marker) (:locator marker))]
    (if-let [problem (marker-problem marker)]
      (malformed problem locator)
      (if (or (targets-problem marker) (> depth max-target-depth))
        (malformed :targets locator)
        (let [resolved (reduce (fn [acc [n tm]]
                                 (let [r (local-handle kb tm (inc depth))]
                                   (if (:handle r)
                                     (assoc acc n (:handle r))
                                     (reduced (assoc (dissoc r :handle) :target n)))))
                               {} (:targets marker))]
          (if (:reason resolved)
            (assoc resolved :locator locator)
            (let [sentence (if (seq resolved)
                             (walk/prewalk-replace
                              (into {} (map (fn [[n h]] [(v/sentex-handle n) (v/sentex-handle h)]))
                                    resolved)
                              (:sentence marker))
                             (:sentence marker))
                  {:keys [refused] h :handle} (handle-lookup kb sentence (:context marker))]
              (cond
                refused  (malformed refused locator)
                (nil? h) {:resolved? false :reason :not-received :locator locator}
                :else    {:handle h}))))))))

(defn dereference
  "Resolve `marker` against the seat's OWN KB, where the marker's untrustedness is enforced.
  Returns, on success:

      {:resolved? true  :handle h  :locator <sha256:hex>  :sentence S  :context C
       :polarity t  :seat <asserter>  :provenance <map>}

  and on failure `{:resolved? false :reason … :locator <sha256:hex>}`:

  - `:malformed`: not a marker, with `:problem` naming the part: `:not-a-map`, a `:locator`
    that is not `\"sha256:\"` + 64 hex, `:no-sentence` / `:no-context`, or the engine's
    refusal type (`:shape`, `:unsupported-context`).  **Fails closed**: a hostile marker is
    answered, never allowed to throw out of the resolve path.  Distinct from
    `:not-received`: one peer is out of sync, the other sends garbage.
  - `:not-received`: the sentence is not in this seat's store; the marker's payload is not
    trusted instead.
  - a target's reason, with `:target` naming the sender's handle number: a `:targets` record
    this seat does not resolve, or a malformed target marker (`local-handle`).  A `:targets`
    value that is not a map of integers to markers, or a chain deeper than
    `max-target-depth`, is `:malformed` with `:problem :targets`.
  - `:not-believed`: the sentence is stored and not believed (`docs/nmtms.md`).  The record
    has no leaf in the `commit-id` tree, so resolving it would hand back a record the seat
    can produce no proof of.
  - `:locator-mismatch`: stored and believed, but the locator this seat computes differs:
    the marker is stale or tampered.

  Meaning, attribution and (via `why-marker`) proof all come from this seat's KB."
  [kb marker]
  (koinii-types/needs-kb! `dereference kb)
  (let [r (local-handle kb marker 0)
        h (:handle r)]
    (if-not h
      r
      (cond
        ;; `handle-of` is a STORAGE read and the commit family enumerates BELIEF — so
        ;; without this arm a defeated record resolves here while answering no inclusion
        ;; proof, and the two halves of one seat disagree about what it holds
        (not (leaf? kb h))
        {:resolved? false :reason :not-believed :locator (:locator marker) :handle h}

        (not= (:locator marker) (locator-of kb h))
        {:resolved? false :reason :locator-mismatch
         :locator (:locator marker) :actual (locator-of kb h) :handle h}

        :else
        (let [sx   (v/sentex kb h)
              prov (v/provenance kb h)]
          {:resolved?  true
           :handle     h
           :locator    (locator-of kb h)
           :sentence   (v/sentence-of sx)
           :context    (:context sx)
           :polarity   (sign-of sx)
           :seat       (:creator prov)
           :provenance prov})))))

(defn why-marker
  "Dereference `marker` and, when it resolves, attach the proof `v/why` builds for it —
  the extension point a cross-seat proof-identity layer grows into.  The marker names WHAT to
  prove by content; the proof itself is the seat's own, drawn from its own justification
  graph.  Returns the `dereference` map, with `:why` added on success."
  [kb marker]
  (koinii-types/needs-kb! `why-marker kb)
  (let [r (dereference kb marker)]
    (if (:resolved? r)
      (assoc r :why (v/why kb (:handle r)))
      r)))
