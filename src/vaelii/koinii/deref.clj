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
        type-tagged, self-delimiting byte encoding of `canonical-bytes` — independent of
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
    handle-independent for every sentence that names no handle, so two seats that reached
    the same beliefs by different routes compute the same commit id (belief and storage
    are order-independent — `docs/nmtms.md`), and a KB exported, pulled and recovered on
    another seat carries the id across.  A sentence that names a sentex by
    `(sentexHandle n)` — every koinii response act — digests the number `n`: its locator
    survives a pull, which keeps handles, and differs between two seats that built the
    same conversation in different orders.  The Merkle shape buys pure auditability:
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
    of what it holds, so `dereference` and `resolve-by-locator` decline it exactly as
    `inclusion-proof` declines to prove it.  Both entry points also **fail closed on a malformed
    payload**, as `verify-inclusion` does on a malformed proof: a marker that is not a
    map, whose `:locator` is not this format, or whose sentence the engine declines to be
    asked about is ANSWERED `:malformed` rather than allowed to throw the engine's
    refusal out of the resolve path — a peer must not be able to crash a receiving seat by
    sending garbage.  Attribution is trustworthy only as far as the identity model makes
    it: a distributed KB inherits the same cooperative-vs-proof-tier question.

  Additive, like the other koinii modules: only the public core API — the record walk
  is `handles` / `sentex`, and the canonicalization is `canonical-sentex`, so a seat
  digests what the store itself would.  Nothing under `vaelii.impl`, and nothing in core
  loads it."
  (:require [vaelii.core :as v])
  (:import (java.io ByteArrayOutputStream DataOutputStream)
           (java.math BigDecimal BigInteger)
           (java.security MessageDigest)))

;; ---- the canonical wire format: a deterministic, injective byte encoding ---

;; NOTE: sentences reaching here are already engine-canonicalized (canonical variables,
;; sorted symmetric arguments, folded comparisons — `docs/canonicalization.md`), so this
;; encoder only needs DETERMINISM and INJECTIVITY, not a canonicalization of its own.  It
;; must not, however, lean on `pr-str`: a printed form depends on ambient `*print-*` vars
;; and cannot type-tag, so two distinct values could print (and thus digest) alike.

(defn- write-len-bytes!
  "Write a length-prefixed byte payload — a 4-byte big-endian count then the bytes — so a
  variable-width field is self-delimiting and cannot run into its neighbour."
  [^DataOutputStream out ^bytes b]
  (.writeInt out (alength b))
  (.write out b 0 (alength b)))

(defn- write-str!
  "Write a string as its length-prefixed UTF-8 bytes.  Fixed encoding (UTF-8) so the
  bytes never depend on a platform default charset."
  [^DataOutputStream out ^String s]
  (write-len-bytes! out (.getBytes s "UTF-8")))

(defn- write-optstr!
  "Write an *optional* string (a symbol/keyword namespace, absent for an unqualified
  name): a presence byte then, if present, the string.  Distinguishes a nil namespace
  from the empty-string one, so `(symbol nil \"a\")` and `(symbol \"\" \"a\")` cannot collide."
  [^DataOutputStream out s]
  (if (nil? s)
    (.writeByte out 0)
    (do (.writeByte out 1) (write-str! out s))))

(defn- write-bigint!
  "Write a `BigInteger` as its length-prefixed minimal two's-complement big-endian bytes
  (`.toByteArray`) — a bijection with the integer, so distinct values never share bytes."
  [^DataOutputStream out ^BigInteger bi]
  (write-len-bytes! out (.toByteArray bi)))

(defn- encode!
  "Emit the canonical bytes of `x` onto `out`.  **The wire-format spec:** every value is
  one type-tag byte then a self-delimiting payload —

      nil      0x00
      boolean  0x01 (false) | 0x02 (true)
      integer  0x03  int64 big-endian                          ; Long/Integer/Short/Byte
      bignum   0x04  len:int32  two's-complement bytes          ; BigInteger / clojure BigInt
      double   0x05  int64 big-endian of (Double/doubleToLongBits d)
      ratio    0x06  <bignum numerator> <bignum denominator>
      bigdec   0x07  <bignum unscaled> scale:int32
      string   0x08  len:int32  UTF-8 bytes
      keyword  0x09  <optstr namespace> <str name>
      symbol   0x0A  <optstr namespace> <str name>
      sequence 0x0B  count:int32  then each element encoded
      char     0x0C  int32 codepoint                          ; legal sentence content (naming/form-rank)

  The tag makes each type its own space (a symbol, a string and a keyword with the same
  characters take tags 0x0A / 0x08 / 0x09 and so differ); the length/count prefixes make
  every composite self-delimiting (so `(a b)` — count 2 — and `(a (b))` — count 2 with a
  nested count-1 sequence — differ); and a double is fixed by its IEEE-754 bits, never by
  a textual form, so `-0.0`, `1.0` and `1.0000000000000002` stay distinct and stable.  An
  unrecognised type throws rather than fall through to a lossy default — a silent
  collision is exactly what a content address must never permit."
  [^DataOutputStream out x]
  (cond
    (nil? x)              (.writeByte out 0x00)
    (instance? Boolean x) (.writeByte out (if x 0x02 0x01))
    (instance? clojure.lang.Ratio x)
    (do (.writeByte out 0x06)
        (write-bigint! out (.numerator ^clojure.lang.Ratio x))
        (write-bigint! out (.denominator ^clojure.lang.Ratio x)))
    (instance? BigDecimal x)
    (let [bd ^BigDecimal x]
      (.writeByte out 0x07)
      (write-bigint! out (.unscaledValue bd))
      (.writeInt out (.scale bd)))
    (float? x)   (do (.writeByte out 0x05) (.writeLong out (Double/doubleToLongBits (double x))))
    (instance? clojure.lang.BigInt x)
    (do (.writeByte out 0x04) (write-bigint! out (.toBigInteger ^clojure.lang.BigInt x)))
    (instance? BigInteger x)
    (do (.writeByte out 0x04) (write-bigint! out ^BigInteger x))
    (integer? x) (do (.writeByte out 0x03) (.writeLong out (long x)))
    (string? x)  (do (.writeByte out 0x08) (write-str! out x))
    (keyword? x) (do (.writeByte out 0x09)
                     (write-optstr! out (namespace x))
                     (write-str! out (name x)))
    (symbol? x)  (do (.writeByte out 0x0A)
                     (write-optstr! out (namespace x))
                     (write-str! out (name x)))
    ;; a char is legal sentence content (`naming/form-rank` ranks it), so it must encode
    ;; rather than reach the `:else` throw — one poison record would otherwise disable
    ;; commit-id/locate for the WHOLE seat, since commit-id folds every sentex.
    (char? x)    (do (.writeByte out 0x0C) (.writeInt out (int ^Character x)))
    (sequential? x) (do (.writeByte out 0x0B)
                        (.writeInt out (count x))
                        (doseq [e x] (encode! out e)))
    :else (throw (ex-info (str "koinii: non-canonical value in sentence identity: "
                               (pr-str (class x))
                               " — the encoding takes nil, a boolean, an integer, a"
                               " double, a ratio, a BigDecimal, a string, a keyword, a"
                               " symbol, a char, and a sequence of those")
                          {:type :koinii/uncanonical-value :value x :class (class x)}))))

(defn- canonical-bytes
  "The canonical byte encoding of `x` per `encode!`'s spec — the digest input, computed
  with no reliance on ambient print vars or platform charset."
  ^bytes [x]
  (let [bos (ByteArrayOutputStream.)
        out (DataOutputStream. bos)]
    (encode! out x)
    (.flush out)
    (.toByteArray bos)))

;; ---- SHA-256, hex, and the self-describing locator prefix -----------------

(def ^:private locator-prefix
  "The multihash-style algorithm tag every locator/root string carries, so the primitive
  is explicit in the value and a future migration is unambiguous."
  "sha256:")

(def ^:private sha256-hex-re
  "The body of every digest this module mints or reads: exactly 64 lowercase hex
  characters, which is a SHA-256 written out."
  #"[0-9a-f]{64}")

(def ^:private locator-re
  "A well-formed locator string: the algorithm tag then the digest body.  Built from
  `locator-prefix` and `sha256-hex-re` so the format has ONE source — the entry points that read
  a locator off an untrusted transport must accept exactly what `content-locator` mints,
  and a second spelling of the pattern is a second thing to keep in step."
  (re-pattern (str locator-prefix sha256-hex-re)))

(defn- locator-string?
  "Is `x` the self-describing locator string this module specifies — `\"sha256:\"` then 64
  lowercase hex?

  The one shape test the untrusted entry points can make on their OWN authority, because the
  locator format is this module's (the module docstring specifies it), unlike a sentence,
  whose grammar belongs to the engine.  So `dereference` and `resolve-by-locator` check it
  themselves and fail closed, exactly as `verify-inclusion` checks a proof's siblings."
  [x]
  (and (string? x) (some? (re-matches locator-re x))))

(defn- sha256
  "The raw 32-byte SHA-256 of `data`.  SHA-256, not SHA-1: the locator is a
  tamper-detection boundary and SHA-1's chosen-prefix collisions make it unfit here."
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

(defn- content-locator
  "The self-describing locator of value `x`: `\"sha256:\"` + hex SHA-256 of its canonical
  bytes.  The one place the format is minted, so every locator-producing function agrees."
  [x]
  (str locator-prefix (hex (sha256 (canonical-bytes x)))))

;; ---- the locator: a content hash of a sentex's canonical identity --------

(defn- sign-of
  "`:negative` when `sx` is a negative literal — its sentence a `(not S)` — and
  `:positive` otherwise.  A sentex map carries its sign in its sentence's head, and the
  locator digests this keyword beside the sentence, so every seat computes one locator
  for one sentex."
  [sx]
  (let [s (:sentence sx)]
    (if (and (nil? (:antecedent sx)) (sequential? s) (= 2 (count s)) (= 'not (first s)))
      :negative
      :positive)))

(defn- identity-of
  "A sentex's canonical **identity** as a value: its context, sign (`sign-of`), and
  canonicalized sentence — everything the store keys a sentex on EXCEPT the per-store
  handle.  The fields come off the constructor already canonical (canonical
  variables, sorted symmetric arguments, folded comparisons), so digesting them is
  digesting the same form on every seat."
  [sx]
  [(:context sx) (sign-of sx) (v/sentence-of sx)])

(defn locator-of
  "The locator of the stored sentex at `handle` — `\"sha256:\"` + hex SHA-256 of its
  canonical identity.  Independent of the handle, so it is reproducible on any seat that
  holds the same assertion.  nil if the handle names no record."
  [kb handle]
  (when-let [sx (v/sentex kb handle)]
    (content-locator (identity-of sx))))

(defn locate
  "The locator `sentence` in `context` **would** have, computed without requiring it be
  stored: `sentence` is canonicalized through the store's own constructor
  (`v/canonical-sentex`, which sorts a symmetric predicate's arguments against this KB's
  taxonomy) and its identity digested.  So `(locate kb S C)` equals `(locator-of kb h)`
  for the handle `h` that `S`/`C` resolves to — the content-address is a function of the
  assertion, not of whether or where it was stored, and not of the number it landed on."
  [kb sentence context]
  (content-locator (identity-of (v/canonical-sentex kb sentence context))))

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

(defn- believed-handles
  "The handles this seat **believes** — `v/handles` (storage) narrowed by `v/in?` (the JTMS
  label), which is the belief filter the extent readers spell `{:believed? true}`.

  The one enumeration every commit identity is built from, and the reason is what a commit
  id is FOR: two seats compare it to agree they hold the same thing, and what a seat holds
  is what it believes.  Storage is a wider set — a defeated default and a conclusion whose
  support was withdrawn are both retained on purpose (`docs/nmtms.md`) — and folding those
  in would make the id a function of a seat's *retraction history* as well as its knowledge,
  so two seats agreeing on every belief but differing in what they had once stored would
  compute different ids and read as disagreeing."
  [kb]
  (filter #(v/in? kb %) (v/handles kb)))

(defn commit-id
  "A content-addressed fingerprint of the seat's **believed knowledge** — the RFC-6962
  Merkle root over its sorted per-sentex content locators, prefixed `\"sha256:\"`.
  Order-independent and handle-independent for every sentence that names no handle, so two
  seats believing the same records compute the same commit id whatever order they were built
  in (a `(sentexHandle n)` inside a sentence digests `n` — the module docstring), and a KB
  exported, pulled and recovered on another seat carries it across — the flow the
  distributed topology uses: 'pull the same commit' is a git operation, 'agree on the
  commit id' is this.

  Scope is every BELIEVED sentex — premises AND anything forward-derived — read as CONTENT
  (context/polarity/sentence, not provenance).  A stored-but-defeated sentex is **not** a leaf:
  belief is what a seat holds, so a default this seat defeated and one it never heard of
  are the same knowledge and hash alike.  So it fingerprints the materialized *belief*, not
  the store: two seats agree exactly when their believed sets match, which the pull flow
  guarantees (pull replicates the store and recovers belief) but which independently-built
  seats meet only if they also derived to the same extent (same rules, same `*max-depth*`).
  For attribution-sensitive snapshot identity, see `state-root`."
  [kb]
  (merkle-root (map #(locator-of kb %) (believed-handles kb))))

(defn- record-locator
  "The provenance-scoped locator of the record at `handle`: content-locator of
  `[creator created identity]`.  A `state-root` leaf — identity as `commit-id`'s leaf sees
  it, plus who asserted it and when."
  [kb handle]
  (let [sx   (v/sentex kb handle)
        prov (v/provenance kb handle)]
    (content-locator [(:creator prov) (:created prov) (identity-of sx)])))

(defn state-root
  "A content-addressed **snapshot** identity of the seat's believed records — the same
  Merkle construction as `commit-id`, over the same believed set, but with leaves that fold
  each record's provenance (`:creator` + `:created`) in with its identity.  Git-commit-like:
  it covers who and when, so it moves when provenance moves even if the content (and thus
  `commit-id`) does not.  Two seats compare `commit-id` to agree they hold the same
  *knowledge*; they compare `state-root` to agree they hold the same *snapshot* — a clone
  that pulled and recovered identical provenance matches here too.

  Belief-scoped for `commit-id`'s reason: the two roots answer about one set of records
  seen two ways, so a leaf in one and not the other would make them roots of different
  trees."
  [kb]
  (merkle-root (map #(record-locator kb %) (believed-handles kb))))

(defn inclusion-proof
  "The audit path proving `locator` is a leaf of this seat's `commit-id` tree — a vector of
  `{:hash <sibling-hex> :side :left|:right}` ordered leaf→root, or nil if the seat does not
  BELIEVE a record with that locator.  The point of the Merkle shape: a verifier fed this
  path plus the leaf `locator` and the published root can confirm inclusion via
  `verify-inclusion` **without** the KB.

  Over the same believed leaves `commit-id` folds, which is what makes the proof check out
  against the published root: a stored-but-defeated record is absent from the tree, so
  asking for its proof answers nil rather than a path that verifies against nothing."
  [kb locator]
  (let [leaves (sorted-leaves (map #(locator-of kb %) (believed-handles kb)))
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
  "PURE verification that `locator` is included under `root` given `proof` — recompute the
  Merkle root from the leaf digest of `locator` and the audit path's sibling hashes, and
  compare to `root`.  Takes no KB: `(root, proof, locator)` is all a verifier needs, which
  is the whole reason `commit-id` is a tree and not a flat digest.  Domain separation
  (`0x00` leaf / `0x01` node) is enforced on both sides, so a sibling cannot be forged
  across leaf/internal roles.

  **Fails closed on a malformed proof.**  The proof is untrusted transport data, so a
  non-hex sibling, a missing `:hash`/`:side`, or a non-sequential proof returns `false`
  rather than throwing — an unverifiable proof is not a valid one."
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
  "Write the seat's KB out as a portable export dump in `dir`, the form a git host
  carries: `v/export!` with `:compression :none` so the record streams are a
  byte-stable function of the KB — gzip stamps a header timestamp, which would make the
  same state export to different bytes.  `dir` must be absent or empty.  Returns
  `export!`'s summary; the commit the other seats pull is this directory.

  **`:compression` is pinned, not defaulted.**  Byte-stability is the property this
  function exists to provide — it is what lets two publishes of one state be compared as
  bytes — so a caller asking for `:gzip` here is asking for something `publish!` cannot be.
  Passing anything but `:none` is refused (`:koinii/compression-pinned`) rather than
  quietly honoured; a caller that wants a compressed dump wants `v/export!` directly, which
  makes no byte-stability claim.  Every other `export!` option passes through."
  ([kb dir] (publish! kb dir {}))
  ([kb dir opts]
   (when-let [c (:compression opts)]
     (when-not (= :none c)
       (throw (ex-info (str "koinii: publish! pins :compression :none — a published commit's"
                            " record streams are a byte-stable function of the KB, and "
                            (pr-str c) " stamps bytes that are not; export! takes it directly")
                       {:type :koinii/compression-pinned :compression c}))))
   (v/export! kb dir (assoc opts :compression :none))))

(defn pull!
  "Open a pulled commit into the (empty) seat `kb`: `v/import!` the dump at `dir`, which
  re-canonicalizes every record through this build's constructor and recovers belief —
  the property that makes this seat compute the same locators as the seat that published.
  Returns `import!`'s summary."
  ([kb dir] (pull! kb dir {}))
  ([kb dir opts] (v/import! kb dir opts)))

;; ---- the marker: the untrusted transport payload -------------------------

(defn marker
  "The transportable marker for the assertion at `handle` — what a seat sends over a
  transport so another seat can dereference it:

      {:locator <sha256:hex>  :sentence <asserted form>  :context <ctx>  :seat <claimed>}

  The `:locator` is the part that decides it; `:sentence` / `:context` are a lookup payload
  the receiver does NOT trust for meaning (it resolves against its own KB and rehashes
  what it finds), and `:seat` is the *claimed* asserter — the real one comes off the
  resolved sentex's provenance.  Throws if `handle` names no record."
  [kb handle]
  (let [sx (v/sentex kb handle)]
    (when (nil? sx)
      (throw (ex-info (str "koinii: no sentex at handle " (pr-str handle)
                           " — it names no record in this KB")
                      {:type :koinii/no-such-handle :handle handle})))
    {:locator  (locator-of kb handle)
     ;; the stored `:sentence` IS the asserted form for BOTH signs — a negative sentex
     ;; keeps its `(not …)` in `:sentence` (docs/storage.md), and the sign is read off
     ;; that head — so `handle-of` finds it by this field unchanged.  The
     ;; field travels raw: it is not re-wrapped in `not`, which would double-negate a
     ;; negative fact into a positive one that resolves to nothing (`:not-received`).
     :sentence (v/sentence-of sx)
     :context  (:context sx)
     :seat     (:creator (v/provenance kb handle))}))

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

  Exactly three commitments, and no more: it is a **map**; its `:locator` is the string
  format this module specifies (`locator-string?`); and it carries **both halves of the
  lookup payload**, `:sentence` and `:context`, since a marker with no sentence is not a
  marker but a bare locator, which `resolve-by-locator` is the entry point for.  What is *in*
  those two keys is not judged here — that is the engine's grammar, and `handle-lookup`
  asks the engine rather than copying it.

  `:seat` is deliberately not required.  It is the CLAIMED asserter, which `dereference`
  never reads: the real one comes off the resolved sentex's provenance."
  [marker]
  (cond
    (not (map? marker))                       :not-a-map
    (not (locator-string? (:locator marker))) :locator
    (not (contains? marker :sentence))        :no-sentence
    (not (contains? marker :context))         :no-context))

(def ^:private request-refusals
  "The `ex-info` `:type`s `v/handle-of` raises about the **request** rather than about the
  knowledge — the engine's own \"I cannot be asked that\", which is precisely what a
  malformed marker earns.  `:shape` is a payload the engine will not read as one sentence
  (a vector spelling, a disjunctive goal); `:unsupported-context` is a query context,
  which names no stored sentex and would answer empty.

  Any OTHER exception out of that read is this seat's problem and not the peer's, so it is
  re-thrown: laundering a real failure into a verdict about the marker would report a
  broken store as a hostile peer."
  #{:shape :unsupported-context})

(defn- handle-lookup
  "`v/handle-of` as a value: `{:handle h-or-nil}` when the engine consents to the question,
  `{:refused <type>}` when it declines the request outright.

  **Why the engine's own refusal, and not a well-formedness checker here.**  A marker's
  `:sentence` is untrusted transport data and has to be judged before the seat acts on it
  — but the grammar of a sentence is the ENGINE's, and a copy of it in this module would
  drift from the one that actually decides.  `v/check` is the public validate-without-
  writing entry point (`docs/api.md`), and it is the wrong entry point for *this* question twice over:
  it runs `assert`'s whole pipeline — naming, groundness, the definitional constraints —
  against the CURRENT KB, so a sentence stored before an `argIsa` was declared would fail
  it while the seat genuinely holds and believes that record, and refusing to dereference
  a record the seat has is a worse answer than the throw this closes; and it re-reads the
  taxonomy on every marker, which the resolution then reads again.

  So ask the entry point the resolution actually goes through and let its typed refusal be the
  answer: `handle-of` either consents to the question or it does not, and where it
  consents its nil stands unedited as \"I do not hold that\".  Nothing a seat can STORE
  trips the refusal — a bare disjunction is not assertable and a rule's `or` is
  polycanonicalized away before storage — so an honest marker never reads as malformed."
  [kb sentence context]
  (try
    {:handle (v/handle-of kb sentence context)}
    (catch clojure.lang.ExceptionInfo e
      (let [t (:type (ex-data e))]
        (if (request-refusals t)
          {:refused t}
          (throw e))))))

(defn dereference
  "Resolve `marker` against the seat's OWN KB — the whole point of the distributed
  model, and where the marker's untrustedness is enforced.  Returns, on success:

      {:resolved? true  :handle h  :locator <sha256:hex>  :sentence S  :context C
       :polarity t  :seat <asserter>  :provenance <map>}

  and on failure `{:resolved? false :reason … :locator <sha256:hex>}`:

  - `:malformed` — the payload is not a marker at all, with `:problem` naming the part
    that failed: `:not-a-map`, a `:locator` that is not this module's `\"sha256:\"` + 64
    hex string, a missing `:sentence` / `:context` (`:no-sentence` / `:no-context`), or
    the engine's own refusal type when the sentence or context is something it will not
    be asked about (`:shape`, `:unsupported-context`).  **Fails closed, like
    `verify-inclusion` on a malformed proof**: a marker arrives over an untrusted
    transport, so a garbage or hostile one is ANSWERED, never allowed to throw the
    engine's refusal out of the resolve path — a peer must not be able to crash the
    receiving seat's dereference by sending a sentence the engine declines to read.
    Distinct from `:not-received` because the two say different things about the peer:
    one is out of sync and the next pull fixes it, the other is sending garbage.
  - `:not-received` — the marker's sentence is not in this seat's store.  The seat has
    not pulled the commit that carries it; it does **not** fall back to trusting the
    marker's payload.
  - `:not-believed` — the sentence IS stored, and this seat does not believe it (a
    defeated default, or a conclusion whose support was withdrawn — both retained on
    purpose, `docs/nmtms.md`).  What a seat *holds* is what it believes, which is the
    scope every commit identity is computed over, so a record outside that scope has no
    leaf in the `commit-id` tree and `inclusion-proof` answers nil for it: resolving it
    would hand back a record the seat can produce no proof of.
  - `:locator-mismatch` — the sentence IS stored and believed, but the locator this seat
    computes for it does not match the marker's.  The marker is stale or tampered: the
    locator is self-verifying (rehash the *resolved* canonical form and compare), and it
    is the marker's payload, not the KB, that is rejected.

  So the marker is never required: meaning, attribution and (via `why-marker`) proof
  all come from what this seat's KB actually holds."
  [kb marker]
  (if-let [problem (marker-problem marker)]
    (malformed problem (:locator marker))
    (let [{:keys [refused] h :handle} (handle-lookup kb (:sentence marker) (:context marker))]
      (cond
        refused
        (malformed refused (:locator marker))

        (nil? h)
        {:resolved? false :reason :not-received :locator (:locator marker)}

        ;; `handle-of` is a STORAGE read and the commit family enumerates BELIEF — so
        ;; without this arm a defeated record resolves here while answering no inclusion
        ;; proof, and the two halves of one seat disagree about what it holds
        (not (v/in? kb h))
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
  (let [r (dereference kb marker)]
    (if (:resolved? r)
      (assoc r :why (v/why kb (:handle r)))
      r)))

;; ---- the pure content-addressed path: resolve a bare locator -------------

(defn locator-index
  "A `{locator → handle}` index over the seat's own KB — the reverse of `locator-of`,
  built by one walk of the handles the seat **believes**.  Injective: two sentexes share a
  locator only if they share a canonical identity, which the store already deduped to one
  handle.  This is what lets a **bare** locator (a marker with no payload) resolve at all,
  so it witnesses that the payload `marker` carries is a convenience, not a trust anchor.
  Keyed on the full `\"sha256:\"`-prefixed locator string.

  **Belief, not storage** — `believed-handles`, the same enumeration `commit-id` and
  `inclusion-proof` fold.  The index is that commit tree's leaf set read backwards, so a
  locator resolves here exactly when it has a leaf to prove."
  [kb]
  (persistent!
   (reduce (fn [m h] (assoc! m (locator-of kb h) h))
           (transient {}) (believed-handles kb))))

(defn resolve-by-locator
  "Resolve a bare `locator` string against the seat's own KB via `index` (default: a
  freshly built `locator-index`) — the pure content-addressed dereference, with no payload
  to distrust.  Same success/failure shape as `dereference`; a locator absent from the
  index is `:not-received`.

  **`:not-received` covers both absences here**, because a bare locator carries no
  sentence to look up: a locator the seat never received and one whose record it stores
  but does not believe are equally not in the believed index, and nothing in the argument
  tells them apart.  `dereference`, which is handed the sentence, does tell them apart
  (`:not-believed`).

  **A string that is not a locator is `:malformed`, not `:not-received`.**  This argument
  comes off the same untrusted transport a marker does, so it gets the same treatment:
  the format is one this module specifies, `locator-string?` decides it, and a peer
  sending garbage is told so rather than told the seat does not hold it.  The 2-arity
  checks BEFORE it builds the index, so a garbage locator costs no walk of the believed
  handles — a peer spamming unparseable strings would otherwise re-digest the whole seat
  once per string.

  **The 2-arity builds a fresh index per call** — one walk of the believed handles, one
  `locator-of` each — so a caller resolving several locators against one state builds it
  once and passes it.  There is no cache: a KB is mutable, and an index held across a
  write would resolve a locator to a record the seat has since retracted or stopped
  believing, which is the one answer this function must not give."
  ([kb locator]
   (if (locator-string? locator)
     (resolve-by-locator kb locator (locator-index kb))
     (malformed :locator locator)))
  ([kb locator index]
   (if-not (locator-string? locator)
     (malformed :locator locator)
     (if-let [h (get index locator)]
       (let [sx   (v/sentex kb h)
             prov (v/provenance kb h)]
         {:resolved?  true
          :handle     h
          :locator    locator
          :sentence   (v/sentence-of sx)
          :context    (:context sx)
          :polarity   (sign-of sx)
          :seat       (:creator prov)
          :provenance prov})
       {:resolved? false :reason :not-received :locator locator}))))
