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

  **The three fetches are counted** (`vaelii.impl.profile`'s `:fetches`), because a
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
  ;; `vaelii.impl.roster`'s compressed one instead, at 0.2 bytes a handle against 48–75.
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
  wire and a roster built out of it, to answer with one number.

  A store implements this when it can answer without enumerating — a `SELECT count(*)`, a
  `LIMIT 1` — and callers go through the helpers below, which fall back to the enumeration
  and so read identically on a store that does not.

  There is no premise tally and no sentex-by-sentex sampling here: only the questions the
  engine asks are on the protocol, so an implementer knows every one of them is worth a
  statement."
  (sentex-tally [store]
    "How many live sentexes, without building the roster.")
  (justification-tally [store]
    "How many live justifications, without building the roster.")
  (a-sentex-id [store]
    "Some live sentex handle, or nil when the store holds none.  *Which* one is the
     store's choice — every caller either tests it for nil or reads the record to prove
     the store is readable at all, and none of them depends on which handle came back.")
  (a-justification-id [store]
    "Some live justification handle, or nil.")
  (a-premise-id [store]
    "Some handle marked a premise, or nil."))

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
  `:strength` is rostered as a premise by the write.  It is an option because the engine's
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

(def var-consequent-key
  "The `index-rule` consequent slot's catch-all for a rule whose consequent functor is a
  **variable** — a rule with concrete antecedents concluding `(?p …)`, which
  `rules/check-indexable-functors` allows (the antecedent binds `?p`, so a forward firing
  is ground, and the range check guarantees it).  Filed under this one bucket rather than
  the canonical `?var0` no goal can spell, and unioned into every concrete-goal answer by
  `resolution/concluding-rule-handles`.  Written via `rules/consequent-index-pred`; a
  keyword can never collide with a predicate, which is always a symbol."
  :var-pred)

(defprotocol IndexStore
  "The index store — the count-aware trie, the secondary root indexes, the
  rule predicate index, the exception re-check index, and the inverted term index.
  Every entry is derived from the records, so it can be thrown away and rebuilt
  (`vaelii.impl.reindex`); it needs no durability of its own."
  (index-sentex    [store sentex handle] "Insert a ground sentex handle into the trie.")
  (unindex-sentex!  [store sentex handle] "Remove a sentex handle from the trie.")
  (lookup    [store pattern]       "Handles whose path matches a full pattern.")
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
  ;; How *many* children, without building them.  This is the trie's own distinct-value
  ;; count at a position — what the query planner's cost model divides by
  ;; (`vaelii.impl.plan`) — and it is asked once per literal per plan, so it must not
  ;; scale with the KB.  `(count (children …))` does: both implementations materialize
  ;; the child set to answer `children`, which turns planning a fixed conjunction into
  ;; work proportional to how many distinct values sit at that position.  Every *storage*
  ;; backend answers the cardinality without building the members — a set's count, or a
  ;; node's edge-array span — so the count is its own read rather than a projection of
  ;; them.  The **fork decorator is the exception, and knowingly**: a key the fork has
  ;; written under is no longer inherited, so its count is `(count merged-members)` and
  ;; the base's set is materialized after all (docs/overlay.md).  A fork trades this op
  ;; for the protocol, on the nodes it writes.
  (count-children [store prefix]   "How many child tokens sit under an interior prefix.")
  ;; secondary roots — the trie is ordered [pred args… ctx], so it can only narrow
  ;; left-to-right.  These give extent *and* cardinality from the other directions —
  ;; by context, by functor, and by argument position — without a walk of the trie.
  ;; Cardinality is one stored count on a base store and the merge above on a fork.
  (sentexes-in-context   [store context]  "Handles of sentexes asserted in `context`.")
  (count-in-context      [store context]  "How many sentexes are in `context`.")
  (sentexes-with-functor [store pred]     "Handles of fact sentexes whose functor is `pred` (any arity, either polarity).")
  (count-with-functor    [store pred]     "How many fact sentexes have functor `pred`.")
  (sentexes-with-arg     [store pos term] "Handles of fact sentexes with `term` at 1-based argument `pos`.")
  (count-with-arg        [store pos term] "How many fact sentexes have `term` at `pos`.")
  ;; ...and the **unary** slice of that read, which is a separate op because the argument
  ;; root cannot narrow to it: `(T x)` and `(P x y)` share the `[1 x]` node and the trie
  ;; level below it, so telling them apart meant fetching the record behind every fact at
  ;; the node and reading its arity.  `kb/types-of` — the retrieval every definitional
  ;; check bottoms out on — wants exactly the unary ones, so a term at argument 1 of n
  ;; binary facts cost n record fetches on every assert about it, to find the handful of
  ;; types it holds.
  ;;
  ;; A **superset** is a legal answer, and `(sentexes-with-arg store 1 term)` is the
  ;; simplest one: the caller filters by arity and by the argument on the records it was
  ;; going to read anyway, so over-answering costs a posting read and under-answering
  ;; would lose a membership.  It is an op here rather than an optional protocol beside
  ;; this one because every index can answer it and no caller branches on whether it
  ;; does — a capability nothing tests for is not a capability, it is this protocol with
  ;; a second name.
  (unary-sentexes-with-arg [store term] "Handles of arity-1 fact sentexes whose lone argument is `term` — a superset is legal; the caller filters it exact.")
  ;; multi-column narrowing: one intersection of the functor root and every named argument
  ;; root, so a query that knows several terms narrows on all of them at once instead
  ;; of one column with the rest deferred to a post-fetch filter.  `pred` may be nil
  ;; (a variable-functor pattern); `pos-terms` is a seq of `[pos term]`.
  (sentexes-with-args    [store pred pos-terms] "Handles with functor `pred` AND each `[pos term]` — one set intersection.")
  ;; rule index: rules are sentexes indexed additionally by their predicates.  Both
  ;; predicate sets are *complete* — every rule, whatever its direction — so "what
  ;; could conclude P?" is answerable for a forward-only rule.  A rule whose consequent
  ;; functor is a variable files its consequent under `var-consequent-key` (above), not
  ;; under a canonical `?var0`, so "what could conclude P?" for a *concrete* P is the P
  ;; bucket unioned with that catch-all — see `resolution/concluding-rule-handles`.
  ;; Direction and defeasibility are NOT mirrored here: they live on the sentex record
  ;; (the `set/*Rule` wrapper canonicalizes into it), and chaining reads them from there.
  (index-rule   [store handle ante-preds conseq-pred] "Register a rule handle by its predicates.")
  (unindex-rule! [store handle ante-preds conseq-pred] "Deregister a rule handle.")
  (rules-by-antecedent [store pred] "Handles of rules with an antecedent on pred.")
  (rules-by-consequent [store pred] "Handles of rules concluding pred.")
  ;; exception (re-check) index: a rule carrying an `exceptWhen` is posted under every
  ;; predicate its exception query mentions, and into a roster of all such rules.  It is
  ;; at *rule* granularity, never per firing — a rule handle is already an antecedent of
  ;; every justification it licenses, so each conclusion it produced is reachable through
  ;; the existing consequence links.  It stores **no truth value**: it answers "which
  ;; rules might need re-checking", never "does the exception hold", so unlike a cached
  ;; closure it has nothing that can drift from belief.  The predicates are passed in
  ;; rather than read off the sentex, so the index does not depend on how a rule spells
  ;; its exception.
  (index-exception    [store handle preds] "Register a rule handle under each predicate its exception mentions.")
  (unindex-exception!  [store handle preds] "Deregister a rule handle from its exception predicates.")
  (rules-with-exception-on [store pred] "Handles of rules whose exception mentions pred.")
  (exception-rules         [store]      "Handles of every rule carrying an exception.")
  (exception-rule?         [store handle] "Is `handle` in the exception/watched-rule roster? (O(1) membership — the firing-path gate.)")
  ;; term (inverted) index: every sentex is findable by any term it contains.  The keys
  ;; are `sentex/index-terms` — every *symbol*, at every depth, plus each ground compound
  ;; between `sentex/*min-indexed-depth*` and `sentex/max-indexed-compound`.  So this is
  ;; exact for a symbol and, for a compound outside those bounds, holds only the sentexes
  ;; that nest it deep enough; `kb/find-sentexes` is the exact read for a compound, which
  ;; it gets from the atoms' postings plus a verify against the record.
  (sentexes-with-term  [store term]  "Handles of sentexes the term index keys by `term`.")
  (sentexes-with-terms [store terms] "Handles of sentexes keyed by all `terms` — one intersection.")
  ;; the term roster: the *names* the term index is keyed by, held as one set beside the
  ;; postings so the vocabulary can be listed and counted without walking the records.
  ;; A name enters when the first sentex mentions it and leaves with the last, derived
  ;; from the postings themselves, so the roster cannot drift from what is indexed.
  (terms      [store] "Every symbol term the index is keyed by — the KB's vocabulary, unordered.")
  (term-count [store] "How many distinct symbol terms the index is keyed by (the roster's own count, no walk).")
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
  ;; is not negative.  `plan/prefix-estimate` divides its selectivity by these, and a
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
