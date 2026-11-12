;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.protocols
  "Storage protocols so the record store and index store each have swappable
  implementations (in-memory by default, on-disk for durability, or an alternate KV
  store later).  The rest of the system programs against these protocols and never
  against a concrete backend.

  **Declarations only, no code.**  The fallbacks that go with the optional capabilities
  — `count-sentexes`, `sentex-sink`, `hinting` and the rest — are in the adjacent namespace in
  `vaelii.impl.capabilities`, because `IndexStore` below is large enough that
  re-evaluating the form (as cloverage does, form by form, to instrument a namespace)
  overflows the JVM's 64 KB per-method bytecode limit.  This namespace is therefore
  loaded but not instrumented (scripts/coverage.sh); a protocol carries nothing to
  cover, so the split costs the measurement nothing and keeps those fallbacks in it.
  `vaelii.impl.jtms-protocol` is split from `vaelii.impl.jtms` for the same reason.

  A held namespace (`vaelii.impl.types.prover` states what that means): it defines protocols and requires no vaelii namespace, so the development browser's reloader never re-evaluates it, and an edit to it takes a restart.")

(defprotocol RecordStore
  "The record store — canonical sentexes and justifications, keyed by integer handle.
  The durable ground truth: everything else the KB holds is derived from it.

  **Every read method is counted** (`vaelii.impl.profile`'s `:fetches`), because a
  record read is not an index read and no index tally can stand in for one: a probe that
  narrows to a single `lookup` and then pages a record per candidate handle costs almost
  nothing by `:reads` and everything by this.  Every implementation tallies its own kind
  on the protocol method, so the number counts what a *caller* asked for and not what a
  backend does internally."
  (put-sentex      [store sentex] "Persist a sentex; return its handle.")
  (get-sentex       [store id]     "Fetch a sentex by handle, or nil.")
  (delete-sentex!   [store id]     "Remove a sentex record.")
  (put-justification   [store d]      "Persist a justification; return its handle.")
  (get-justification    [store id]     "Fetch a justification by handle, or nil.")
  (delete-justification! [store id]    "Remove a justification record.")
  (next-id         [store]        "Allocate the next monotonic handle — one above every
                                    handle the store holds, including one that arrived as
                                    an explicit `:id` on a put rather than from here.  A
                                    handle is an identity, so no store may issue one twice.")
  ;; provenance — an open bookkeeping map per handle (creator, creation date, and
  ;; whatever else an application layers on), kept *beside* the record rather than as
  ;; fields on it, so the sentex/justification shape never grows.  Never read by belief,
  ;; so it cannot affect order independence; torn down with the record it annotates.
  (put-provenance    [store id prov] "Persist the provenance map for handle `id` (overwrites).")
  (get-provenance    [store id]      "The provenance map for handle `id`, or nil.")
  (delete-provenance! [store id]     "Remove the provenance for handle `id`.")
  ;; enumeration + premise tracking, for recovery of the in-memory graph.
  ;;
  ;; **A `java.util.Set` of handles, and not necessarily an `IPersistentSet`.**  What the
  ;; three promise is what the engine actually does to them — `contains?`, `count`, `seq`,
  ;; `sort`, and `=` against another set — and a caller wanting `conj`, `disj` or
  ;; `clojure.set` converts with `(set …)`, which is the copy, taken at the call site that
  ;; needs it rather than by every store on every enumeration.  The memory store answers a
  ;; `PersistentHashSet<Long>`, because that is what its own state already is.  The disk
  ;; store, and any store large enough for the shape to be the cost, answers
  ;; `vaelii.impl.handle-set`'s compressed one instead, at 0.2 bytes a handle against 48–75.
  ;;
  ;; The **tally** questions — how many, is there one at all — do not need the set and are
  ;; asked through `Tallying`'s helpers below, which fall back to these.
  (sentex-ids       [store]           "Every live sentex handle, as a set.")
  (justification-ids    [store]           "Every live justification handle, as a set.")
  (mark-premise    [store id strength] "Record a handle as an asserted premise at `strength`.")
  (unmark-premise!  [store id]        "Record that a handle is no longer a premise.")
  (premise-ids      [store]           "Every handle currently marked a premise, as a set.")
  (premise-strength [store id]        "The recorded assumption strength of a premise handle.")
  (clear-records!   [store]           "Remove every stored record (wipe the whole store)."))

(defprotocol Prefetching
  "**Optional**, and beside `RecordStore` rather than an op in it: a store that keeps a
  cache in front of a fetch expensive enough to be worth avoiding implements this, and one
  whose fetch is already a page touch does not — in which case a caller runs exactly the
  code it ran without this protocol in the world.

  `prefetch-sentexes!` is a **hint, never an answer.**  It returns nothing, and every
  record still comes back through `get-sentex`, so it cannot change what a query matches
  on any backend however wrong its guess about what is worth fetching.  That is the whole
  reason the capability is shaped this way rather than as a batched read returning
  records: a batched read has to be *proven* equal to the per-handle loop on every
  implementation, and a cache warmed ahead of that loop is equal to it by construction.

  **The store decides whether to act**, and it is the only party that can: it is handed
  the handles a caller is about to walk and it knows which of them its own cache already
  holds, so \"is one query cheaper than these fetches\" is answered from the actual set
  rather than from a setting somebody tuned."
  (prefetch-sentexes! [store ids]
    "Warm this store's cache for the sentexes at `ids` if that is cheaper than the fetches
     it saves.  Returns nil.  Never required — a caller may skip it entirely and read the
     same records at the same handles.")
  (prefetch-justifications! [store ids]
    "The same for justifications.  A separate op rather than a kind argument, mirroring
     `get-sentex` / `get-justification`: the two are different rows in every store that
     has rows, and a caller always knows which it is about to walk."))

(defprotocol Tallying
  "**Optional**, and beside `RecordStore` for the same reason as `Prefetching`: the two
  questions a caller asks an enumeration that do not need the enumeration.

  `(count (sentex-ids store))` is how the engine asks *how many records is this*, and
  `(first (sentex-ids store))` is how it asks *is this store empty* — `open-kb` asks both
  before the KB has answered anything, and `import` asks the first again to report what it
  loaded.  On a store whose enumeration is a read of its own state those added no work.  On
  one whose enumeration is a **query** they cost the whole table: every handle over the
  wire and a handle set built out of it, to answer with one number.

  A store implements this when it can answer without enumerating — a `SELECT count(*)`, a
  `LIMIT 1` — and callers go through the helpers below, which fall back to the enumeration
  and so read identically on a store that does not.

  There is no premise tally and no sentex-by-sentex sampling here: only the questions the
  engine asks are on the protocol, so an implementer knows every one of them is worth a
  statement."
  (sentex-tally [store]
    "How many live sentexes, without building the handle set.")
  (justification-tally [store]
    "How many live justifications, without building the handle set.")
  (a-sentex-id [store]
    "Some live sentex handle, or nil when the store holds none.  *Which* one is the
     store's choice — every caller either tests it for nil or reads the record to prove
     the store is readable at all, and none of them depends on which handle came back.")
  (a-justification-id [store]
    "Some live justification handle, or nil.")
  (a-premise-id [store]
    "Some handle marked a premise, or nil."))

(defprotocol HandleReserving
  "**Optional**: a record store whose `next-id` can skip handle ranges that durable forks
  of it hold, so a base rebuilt in a later process issues none of them
  (`open-kb`'s `:fork-dirs`, docs/overlay.md).  A store without it refuses that option."
  (reserve-handles! [store ranges]
    "Add `ranges`, a seq of `[lo hi)` handle pairs, to the handles `next-id` skips from now
     on.  Returns nil.  A handle written with an explicit `:id` is unaffected."))

(defprotocol ImageFingerprinting
  "**Optional**: a record store that fingerprints its records for an index image or a
  reasoning image.  Each image is written with the fingerprint its records answered at the
  time, and installed only while they still answer the same one, so a fingerprint has to
  move whenever a record is added, deleted or re-stored — a premise mark included — and
  differ between two unrelated stores.  It is read at every open and close of a KB keeping
  images, so it has to cost no walk of the records.

  The `:disk` store answers off its slot files (`record-store/slot-fingerprint`,
  `reasoning-fingerprint`); the `:pg` adapter answers one row a trigger moves in the same
  transaction as each write.  A store that does not implement it keeps no image, and
  `open-kb` refuses the `:snapshot` index over it."
  (index-fingerprint [store]
    "The fingerprint an index image is validated against: any value, compared with `=`,
     that moves when a sentex is added, deleted or re-stored.")
  (belief-fingerprint [store]
    "The fingerprint a reasoning image is validated against: as `index-fingerprint`, and
     moving when a justification does too."))

(defprotocol RecordSink
  "An open bulk write.  A caller opens one with `capabilities/sentex-sink` /
  `justification-sink`, writes a stream of records to it, and **closes it**
  (`java.io.Closeable`, so `with-open`).

  **Do not read a record back before that close.**  A sink may hold everything it was
  given until then — a `COPY` stream lands when the copy ends — so a fetch of a handle
  just written may find nothing there.  This is a restriction on the caller and not a
  promise about visibility: an implementation is free to make a write readable at once,
  and the loop the default sink runs does.

  The **handle is the caller's**, decided before the write and returned rather than
  computed: a record carrying an `:id` lands at it, and one without gets `next-id`.  That
  is what makes a sink usable where a batched put is not — the import path indexes each
  record from the copy already in hand and needs the handle *now*, and a `COPY` returns
  nothing per row."
  (write-record! [sink rec]
    "Write `rec` to the sink and return its handle — `(:id rec)` when it carries one, a
     freshly minted one when it does not.  Not readable until the sink is closed."))

(defprotocol BulkLoading
  "**Optional**, and beside `RecordStore` for the same reason as `Prefetching` and
  `Tallying`: a store with an ingest path faster than a record at a time implements it,
  and one whose `put-sentex` is already a map assoc does not — in which case a bulk
  loader runs `loop-sink`'s put-per-record loop and pays nothing for the capability.

  The `RecordSink` protocol is a **sink and not a batched put**, and the difference is the handle.  A
  batched put returning handles makes its caller wait for a batch to land before it can do
  anything with any of it, and the import path's whole shape is that it indexes each
  record from the copy already in hand rather than reading it back (`import`'s
  records-only pass says why: on a durable store the read-back re-pages every record).  So
  the handle is decided caller-side and the sink is *told*, which is also what lets a dump
  preserve its own numbering through one.

  `opts` is `{:premises? bool}` for a sentex sink — whether a record carrying a
  `:strength` joins the premise set by the write.  It is an option because the engine's
  two import paths differ on it: the records-only pass marks inline, and the belief pass
  aggregates the marks afterwards over dump ids that collapsed onto one handle, where the
  record's own strength is the first frame's and the mark is the strongest.  A justification
  sink has no such question."
  (open-sentex-sink [store opts]
    "A `RecordSink` writing sentexes in bulk.")
  (open-justification-sink [store opts]
    "A `RecordSink` writing justifications in bulk."))

(defprotocol BulkAnnotating
  "**Optional**, and beside `BulkLoading` rather than in it: the two per-handle writes
  that follow a record rather than being part of it — the premise mark and the provenance
  map.  Separate because a store may bulk-load records without being able to bulk-update
  what is already there, and a partly-implemented protocol is worse than two.

  Both exist because the import path writes them in a **loop over handles it already
  holds**.  The premise marks are decided only once the whole sentex stream is read (a
  dump id that collapses onto a stored handle keeps the strongest strength), and the
  provenance stream is read after the records; so neither can ride the record write, and
  both are `n` writes on a store where a write is a round trip.  On a corpus import over a
  server that is the largest remaining block of round trips by a wide margin.

  Neither op changes what the per-handle version does — same guard, same end state.  A
  handle with no sentex is still not marked."
  (mark-premise-batch [store id->strength]
    "Mark every handle in `id->strength` a premise at its strength, in as few writes as
     this store can manage.  Returns nil.")
  (put-provenance-batch [store entries]
    "Persist every `[id prov]` pair in `entries`, overwriting, in as few writes as this
     store can manage.  Returns nil."))

(defprotocol BulkDeleting
  "**Optional**, beside `BulkAnnotating`: the deletes a record surgery makes in a loop over
  handles it already holds (`record-edit/apply!`).  On a store where a write is a round
  trip that loop costs one a record, and a surgery removes records by the million.

  Neither op changes what the per-handle version does — same guard, same end state."
  (delete-sentex-batch [store ids]
    "Remove every sentex record in `ids`, in as few writes as this store can manage.
     Returns nil.")
  (delete-justification-batch [store ids]
    "Remove every justification record in `ids`, likewise.  Returns nil."))

(def var-consequent-key
  "The `rules/index-rule` consequent slot's catch-all for a rule whose consequent functor
  is a **variable** — a rule with concrete antecedents concluding `(?p …)`, which
  `rules/check-indexable-functors` allows (the antecedent binds `?p`, so a forward firing
  is ground, and the range check guarantees it).  Filed under this one bucket rather than
  the canonical `?var0` no goal can spell, and unioned into every concrete-goal answer by
  `resolution/concluding-rule-handles`.  Written via `rules/consequent-index-pred`; a
  keyword can never collide with a predicate, which is always a symbol."
  :var-pred)

(def every-context
  "The `ctxs` a family read passes to read every context.  A `family-*` method given nil
  for `ctxs` throws, so a read past a reader's ancestor set is spelled where a lint can see
  it (docs/storage.md, \"The family methods\")."
  ::every-context)

(def any-context
  "The last token of a `family-apply!` retire's leaf path when the writer does not know the
  context: the retire takes the handle out of whichever context's leaf holds it."
  ::any-context)

(defprotocol IndexStore
  "The index store — the count-aware trie, the secondary root indexes, the
  rule predicate index, the exception re-check index, and the inverted term index.
  Every entry is derived from the records, so it can be thrown away and rebuilt
  (`vaelii.impl.reindex`); it needs no durability of its own."
  (index-sentex    [store sentex handle] "Insert a ground sentex handle into the trie.")
  (unindex-sentex!  [store sentex handle] "Remove a sentex handle from the trie.")
  ;; A path's last token is the context, so `contexts`, a set or nil, ranges that level:
  ;; a set keeps only the children in it, iterating the smaller of the two, and nil keeps
  ;; every child.
  (lookup    [store pattern] [store pattern contexts]
    "Handles whose path matches a full pattern, stated in one of `contexts` when it is a set.")
  ;; The **exact leaf**, where `lookup` is a match.  A path carrying a variable is a
  ;; wildcard to `lookup` — the token fans over every child at that level — so asking it
  ;; for one sentex's own key costs the whole extent of that shape.  This asks the node
  ;; the path names and nothing else: no walk, no fan, one read.
  ;;
  ;; That is what **dedup** wants and the only thing it wants.  A stored sentex's key is
  ;; α-renamed (`sentex/key-tokens`), so two sentences that differ only in variable names
  ;; land on one leaf and the record decides between them (`kb/find-sentex-handle`); a
  ;; sentence stored under a *different* key is by construction not the same sentence, so
  ;; a wildcard's extra candidates could never have been the answer.  Retrieval is the
  ;; other question and stays `lookup`'s: a pattern is asked there to find what it
  ;; matches, not to find itself.
  (leaf-at   [store path]          "Handles stored exactly at `path`'s leaf — an exact read, never a wildcard match.")
  (count-at  [store prefix]        "Sentex count under a path prefix.")
  (children  [store prefix]        "Child tokens registered under an interior prefix.")
  ;; secondary roots — the trie is ordered [pred args… ctx], so it can only narrow
  ;; left-to-right.  These give extent *and* cardinality from the other directions —
  ;; by functor and by argument position — without a walk of the trie.  Cardinality is
  ;; one stored count on a base store and the merge above on a fork.
  (sentexes-with-functor [store pred]     "Handles of fact sentexes whose functor is `pred` (any arity, either polarity).")
  (count-with-functor    [store pred]     "How many fact sentexes have functor `pred`.")
  ;; multi-column narrowing: one intersection of every named argument root, so a query
  ;; that knows several terms narrows on all of them at once instead of one column with
  ;; the rest deferred to a post-fetch filter.  `pred` may be nil (a variable-functor
  ;; pattern); `pos-terms` is a seq of `[pos term]`, and empty reads `pred`'s predicate
  ;; extent.  `contexts`, a set or nil, scopes the read to the handles stated in those
  ;; contexts: the argument roots and the predicate extent end in the context, so a
  ;; reader passes its ancestor set and no leaf it cannot see is read.  Nil reads every
  ;; context.
  (sentexes-with-args    [store pred pos-terms] [store pred pos-terms contexts]
    "Handles with functor `pred` AND each `[pos term]`, stated in one of `contexts` when it is a set.")
  ;; term (inverted) index: every sentex is findable by any term it contains.  The keys
  ;; are `sentex/index-terms` — every *symbol*, at every depth, plus each ground compound
  ;; between `sentex/*min-indexed-depth*` and `sentex/max-indexed-compound`.  So this is
  ;; exact for a symbol and, for a compound outside those bounds, holds only the sentexes
  ;; that nest it deep enough; `kb/find-sentexes` is the exact read for a compound, which
  ;; it gets from the atoms' postings plus a verify against the record.
  (sentexes-with-terms [store terms] "Handles of sentexes keyed by all `terms` — one intersection.")
  ;; the portable projection.  Every index — the flat-map one, the dense one, the
  ;; columnar one with a native int-token trie — answers this protocol, so the
  ;; `[structured-key value]` entry shape is what they have in *common* rather than what
  ;; any one of them holds.  That is what a dump writes and reads back
  ;; (`vaelii.impl.io.export` / `.import`), and it is why an index written by one backend
  ;; loads into another.  A backend's own resident layout is a different artifact
  ;; entirely, and not this.
  ;;
  ;; `index-load` is bare, not `!`: it installs derived state into an *empty* index and
  ;; destroys no knowledge.  Loading over a populated one merges rather than replaces,
  ;; so the caller owes the emptiness.
  ;; the family methods: every family `vaelii.impl.kv/index-families` names, read and
  ;; written by its tag `f` and a token `path` from the family's root.  In a trie or count
  ;; trie a node is the path above the context and a leaf the node plus the context; in a
  ;; flat set the path is the key's tail.  `ctxs` is a set, or `every-context`; nil throws.
  ;; docs/storage.md, "The family methods", gives each method per shape.
  (family-count [store f path ctxs]
    "The node's count with `every-context`, else the summed leaf sizes over its children in `ctxs`.")
  (family-children [store f path ctxs]
    "The child tokens under `path`: a set with `every-context`, else a vector of those in `ctxs`.")
  (family-child-count [store f path] "How many child tokens sit under `path`, with no set built.")
  (family-leaf [store f path] "The set stored at exactly `path`.")
  (family-member? [store f path x] "Is `x` in the set at exactly `path`?  No set built.")
  (family-handles [store f node ctxs]
    "The union of the leaves under `node` over its children in `ctxs`; one context answers its leaf as stored.")
  (family-apply! [store ops]
    "Apply `[:post f leaf-path h]` / `[:retire f leaf-path h]` as one batch equal to the
     ops applied one at a time in order; reply per op the node's count after it, or nil
     when it changed nothing.  A count-trie retire's leaf path may end in `any-context`;
     a flat set's throws `:bad-args`.")
  (index-entries [store]         "Every index entry as a lazy `[key value]` seq — the portable projection.")
  (index-load    [store entries] "Install `[key value]` entries into an empty index, in this store's own representation.")
  (clear-index!        [store]       "Remove every index entry (wipe the store — `reindex` rebuilds)."))

(defprotocol KvBackend
  "The key-value operations `KvIndexStore` bottoms out on.  Keys are structured
  vectors; set members are bare values.  Each adapter maps those onto its store.

  **No op here names an index family.**  A scalar, a counter, a set and an intersection
  are the whole vocabulary, and which families a KB indexes, how their keys are spelled
  and which reads descend them are `vaelii.impl.kv`'s — the index layer, above this one.
  A backend is free to hold any family in a representation of its own (a counted trie,
  packed longs) and answer these ops off it; that is a representation, and it stays
  invisible here."
  ;; scalars / counters
  (kv-get  [b k]   "The value at `k`, or nil.")
  (kv-put  [b k v] "Set `k` to `v`.")
  (kv-delete  [b k]   "Delete `k`.")
  (kv-increment [b k]   "Increment the counter at `k`; return the new value.")
  ;; **Clamped at zero**, and the counters are why.  Every counter key this index writes
  ;; is a *cardinality* — how many sentexes live under a trie prefix — and a cardinality
  ;; is not negative.  `plan/prefix-estimate` returns these as match bounds, and a
  ;; negative one there is not a wrong estimate but a meaningless one; `unindex-present!`
  ;; reads the reply to decide which nodes died, and `<= 0` is what it asks, so the floor
  ;; changes no decision on the ordinary path.  It is free: the fold has the new value in
  ;; hand either way.
  ;;
  ;; A backend that answers 0 to a decrement of an absent key is therefore telling the
  ;; truth rather than rounding: the key holds no sentexes, and it held none before.
  (kv-decrement [b k]   "Decrement the counter at `k`, floored at 0; return the new value.")
  ;; sets
  (kv-add-to-set     [b k member] "Add `member` to the set at `k`.")
  (kv-remove-from-set     [b k member] "Remove `member` from the set at `k` (dropping the key when it empties).")
  (kv-members [b k]        "The members of the set at `k`, as a set (empty when absent).")
  (kv-member? [b k member] "Is `member` in the set at `k`? — answered without building the set.")
  (kv-count    [b k]        "The cardinality of the set at `k` (0 when absent).")
  ;; set intersection — one operation over N keys
  (kv-intersect [b ks] "The intersection of the sets at `ks`, as a set.")
  ;; batch — a sequence of write ops applied as one unit; returns one reply per op
  (kv-batch [b ops] "Apply the write ops `[op key & args]` as one unit; return the replies in order.")
  ;; the portable projection, both ways.  `kv-entries` is the only way to ask a backend
  ;; for everything it holds; `kv-load` puts an entry back **in the backend's own
  ;; representation**, which a bare `kv-put` cannot do — a backend that packs handle sets
  ;; into int postings would take a plain set from `kv-put` and then fail the next
  ;; `kv-add-to-set` against it.
  (kv-entries [b]         "Every entry as a lazy `[key value]` seq; set values as Clojure sets, counters as longs.")
  (kv-load    [b entries] "Install `[key value]` entries into an empty backend, in this backend's representation.")
  ;; wholesale wipe (the whole index)
  (kv-clear! [b] "Remove every entry."))

(defn unknown-op!
  "Refuse a write op no adapter recognizes.  **One throw for every one of them**, because
  which fold a write went through is not something the op's readability depends on: the
  persistent `apply-op` and the transient twin a bulk load takes (`vaelii.impl.memory`),
  the dense backends' own `kv-batch` (`vaelii.impl.dense-kv`, `vaelii.impl.dense-roots`)
  and the fork decorator's (`vaelii.impl.overlay.kv`) all bottom out here.  So a caller
  discriminating on `:type` reads `:unknown-frame` whatever backend it reached, which is
  the shape `kv_backend_test`'s adapter contract holds every one of them to.

  `:unknown-frame` and not `case`'s bare `IllegalArgumentException`, because on the disk
  side it is not a programming error at all — it is a log written by some other build,
  and a build that cannot read a log must be able to say so by name rather than delete
  it."
  [op]
  (throw (ex-info (str "unknown index write op " (pr-str op) " — a batch op is :put,"
                       " :delete, :increment, :decrement, :add-to-set or"
                       " :remove-from-set")
                  {:type :unknown-frame :op op})))
