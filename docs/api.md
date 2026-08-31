# Public API (`vaelii.core`)

- **Covers:** every function on `vaelii.core`, what it takes and returns, and which query
  function to reach for.
- **Not here:** the CLI and daemon that call this API from outside the process →
  [operations.md](operations.md); the naming invariants `assert` enforces →
  [naming.md](naming.md).
- **Assumes:** sentex, handle, context, strength → [glossary.md](glossary.md).

`vaelii.core` is the engine's whole API. Five thin entry points are public beside it —
`vaelii.client`, `vaelii.starter`, `vaelii.web`, `vaelii.serve`, `vaelii.cli` — and
those six namespaces are the compatibility boundary. Everything else is `vaelii.impl.*`
and free to change: the engine internals, the ontology content, and the browser. Tests
reach into `impl` freely, which is what unit tests are for; nothing outside this repo
should. The file map is [namespaces.md](namespaces.md). Entry points are `lein run` (→
`vaelii.core`) and `lein run -m vaelii.web`.

```clojure
(def kb (open-kb {}))                         ; or {:space 15}
                                              ; :backend names a <records>-<index> pair —
                                              ; :memory :memory-dense :memory-columnar
                                              ; :disk-memory :disk-dense :disk-columnar
                                              ; :disk-log :sqlite :pg-memory :pg-disk-log — or
                                              ; :records / :index override a half of one
                                              ; (docs/storage.md)
                                              ; :sqlite and :pg records come from Apache-2.0
                                              ; siblings, resolved lazily, so the engine loads
                                              ; no JDBC driver unless one is named; :pg is a
                                              ; next.jdbc db-spec or a JDBC URL string and is
                                              ; required, since nothing derives a server
                                              ; :dir is the directory for :disk / :sqlite, and
                                              ; for :pg-disk-log, whose durable index is files on
                                              ; this host describing records on a server
                                              ; :naming and :constraints are this KB's two
                                              ; front-door policies (docs/naming.md, nmtms.md)
                                              ; :recover? is :auto (or true) / :warn / false —
                                              ; :auto is the default and anything else is
                                              ; refused (:unknown-option), since a value read
                                              ; as :warn hands back an empty TMS over a store
                                              ; that is not empty (docs/storage.md)
(fork kb opts?)                                ; a private writable KB over this one's stores,
                                               ; frozen: reads fall through, writes stay in the
                                               ; fork, the base is never written (docs/overlay.md)
(assert kb sentence context opts)              ; premise: check + store + index + chain + settle -> handle,
                                               ; or the VECTOR of them when the rule
                                               ; polycanonicalized (docs/canonicalization.md)
                                               ; opts: {:strength :monotonic|:default :chain? bool :max-depth n}
                                               ; `assert-opt-keys` is the roster; a key off it is refused
(assert-rule kb antecedents consequent context opts)  ; opts as `assert` (:direction included)
                                               ; (:forward | :backward | :inert | :both, default :both) —
                                               ; the programmatic spelling of a set/*Rule wrapper
(assert-inert kb sentence context)              ; stored, indexed and durable, but NOT a premise:
                                                ; never believed, never chained, never scanned for
                                                ; contradictions — a recorded truth value
                                                ; (docs/solving.md).  Drop it with `retract!`.
                                                ; A rule is refused (`:not-indexable`): nothing
                                                ; would index it, so nothing could fire it.
                                                ; The other inertness is `set/inertRule` — a
                                                ; believed, indexed rule that fires neither way
(with-deferred-settle kb & body)                ; run a batch, settle belief ONCE at the end
(assert-many kb sentences context opts)         ; the collection form -> vector of handles
(bulk-assert-facts! kb facts context opts?)     ; a trusted corpus's ground facts on the fast path:
                                                ; no per-fact checks, no dedup, no provenance, no
                                                ; chaining, one settle.  The caller owns the two
                                                ; preconditions — well-formed, pairwise-distinct.
                                                ; `:on-progress` reports the load's facts/sec
(edit! kb {:add [[sentence context opts?] ...] :remove [handle ...]}) ; add-then-remove, one settle
(check kb sentence context opts)                ; would assert succeed? -> [] or [{:type :message …}]
(check-edit kb {:add […] :remove […]})          ; the same over an edit batch, each problem naming its entry
(preview kb {:add […] :remove […]} opts)        ; what the batch would BELIEVE -> the diff, then rolled back
(edit-with-consequences! kb batch opts?)        ; `edit!`, plus what it turned out to mean — the same diff, after
(watch kb f)                                    ; call `f` with that same diff whenever belief moves -> token
(watch kb goal context f)                       ; ...only for what `goal` answers, entries + :bindings
(unwatch kb token) / (watchers kb)              ; drop one -> bool / what is registered, without the fns
(forward-chain kb opts)                         ; {:derived n :truncated? bool}
default-chain-opts                              ; the bounds a chain run takes when opts omit them —
                                                ; max-depth (productive recursion) and max-derivations
(conflicts kb)                                  ; irreducible clashes among known-true content —
                                               ; same entry shape as contradictions; both sides stay believed
(contradictions kb)                            ; coexisting pairs at :default — represented dilemmas:
                                               ; a rebuttal (P/not-P), a definitional clash
                                               ; (:kind :disjoint|:functional|:asymmetric
                                               ;  |:anti-transitive), or a stored claim against a
                                               ; known-true claim reached by argument preservation
                                               ; (:kind :inherited, which adds an :inherited map —
                                               ;  {:sentence :context :claim handle :via [handle …]} —
                                               ;  naming the claim nobody stored, docs/inherit.md)
                                               ; both lists are ordered by CONTENT, entries and sides
                                               ; alike, so (first (contradictions kb)) is stable
(settle-stats kb) / (reset-settle-stats! kb)     ; the exceptWhen fixpoint's iteration instrumentation
(chain-stats kb)                               ; {:runs n :last {:derived n :truncated? bool}} — a capped run is visible
(chain-report kb)                              ; the per-rule breakdown behind chain-stats: per forward rule
                                               ; {:rule :sentence :believed? :placed :refused :refusals
                                               ; :status} — :fires / :blocked (with the reason) /
                                               ; :silent.  O(rules), off the ledger
(violations kb) / (clear-violations! kb)         ; accumulating ledger of dropped derived conclusions (run-stamped, capped)
(kb-quality kb opts)                            ; the seven readings about the *knowledge* —
                                                ; {:rules :extents :chains :taxonomy :declarations
                                                ;  :subsumption :clashes}, opts :limit /
                                                ; :on-progress (which may throw to cancel).
                                                ; :subsumption names the rules another rule already
                                                ; covers, :clashes the rule pairs that would
                                                ; contradict each other if both fired
(quality-report quality)                        ; that map as Markdown; takes the map, not the KB
(caches kb)                                     ; what the *process* holds beside the stores: one row per
                                                ; cache — :entries :limit :unit :hits :misses :hit-rate,
                                                ; :scope for what the entries count and :counters for what
                                                ; the rates do (they differ), :note for what retires one,
                                                ; :error where a row's own read threw. O(1) per row, so it
                                                ; can be polled
(clear-caches kb)                               ; drop the derived ones and say what went. Bare, not `!`:
                                                ; every entry is derived and no belief moves, which is what
                                                ; makes it a measuring instrument. Scoped to `kb`: no other
                                                ; KB loses an entry or a belief. {:counters? true} is the one
                                                ; thing that reaches wider — it zeroes the :process hit/miss
                                                ; rates every KB in the JVM reports, and names what it
                                                ; touched under :counters-reset
(exposed-clashes kb)                            ; the standing cross-context disjointness clashes, asked
                                                ; of the whole KB — settle files what a change newly
                                                ; exposes, this answers what the KB holds now
(last-program kb)                              ; the last edge Program solved — the tie, before belief erased it
(set-solver kb :asp)                           ; the real answer-set backend, by name (:stub is the default)
(set-solver kb solver)                         ; or any vaelii.impl.solve/Solver value
;; The context argument on the seven reads below — sentexes-matching, query, prove, ask
;; and the ? variants of the last three — takes a real Cx… context, a ?var, or one
;; of the three QUERY CONTEXTS — names for a way of reading rather than a place
;; (docs/contexts.md).  Nothing is asserted into one and no genlCx edge may name one.
;;   CxEverything  every stored sentex, belief IGNORED — a syntactic read of the store
;;   CxInference   only what one reader's genlCx cone sees over the WHOLE derivation,
;;                 that reader bound to ?ctx in the answer.  A variable context reads
;;                 the same way, so neither joins two facts no one context sees
;;   CxNothing     no fact at all: whatever the provers alone can compute
;; A VARIABLE context (?ctx, the default of every short arity, or any name) is the same
;; joint reading as CxInference — the witness is unified into that variable instead of
;; arriving as :context.  So the default read requires one reader to see the whole
;; derivation; the union is CxEverything.
;; Exception: a goal whose every literal is computed (different / evaluate / unknown)
;; names no context, so it is read whole-KB with no witness — a fanned (unknown X) would
;; be satisfied by the most ignorant reader in the KB.  A mixed goal needs no exception.
;; A door that does not resolve one refuses it (:unsupported-context) rather than
;; answering empty.
(sentexes-matching kb sentence context)        ; believed literal match (context defaults to ?ctx)
(query kb goal context opts)                   ; THE FRONT DOOR -> solutions.  No :max-depth and it
(query? kb goal context opts)                  ; expands no rule; a :max-depth and it is the node
                                               ; engine, bounded at that many rule rewrites.  There
                                               ; is no default depth — name the smallest that works
                                               ; goal = a sentence, or a VECTOR of them, at any depth
                                               ; opts: {:max-depth n :proof? true} + the node engine's
                                               ; :strategy :portfolio? :auto? :racers — the whole
                                               ; roster is `query-opt-keys`; a key off it is refused
(prove kb goal context opts)                   ; recur DFS backward chaining -> [solutions].  With no
                                               ; opts the UNBOUNDED one: terminates on the data,
                                               ; facts+rules
                                               ; goal = a sentence, or a VECTOR of them = a
                                               ; conjunctive query (shared vars join; cost-ordered)
                                               ; opts: `prove-opt-keys` — {:max-ms n :max-depth n}.
                                               ; :max-depth PRUNES (the answer is complete for that
                                               ; depth); :max-ms SUSPENDS, and a deadline reached is
                                               ; `:budget-exhausted`, never a short answer
(provable? kb goal context opts)               ; boolean (same single-or-vector goal, same opts).
                                               ; Stops at the first solution; an exhausted :max-ms
                                               ; is `:budget-exhausted`, never `false`
(ask kb goal context opts)                     ; the prover registry -> solutions / boolean.  Expands
(ask? kb goal context opts)                    ; NO rule, so it opens no proof search
                                               ; opts: `ask-opt-keys` — {:max-ms n} and nothing else,
                                               ; there being no rule expansion to bound.  Naming one
                                               ; realizes the stream under it and refuses on the
                                               ; deadline; `ask-within` hands the prefix back instead
(ask-within kb goal context budget)             ; anytime ask: bound {:max-ms :max-results :max-cost}
(prove-within kb goal context budget)           ; anytime prove: bound {:max-ms :max-results :max-depth
                                                ;   :max-term-growth} — the last a termination guard, so
                                                ;   leaving it out keeps the shipped ceiling
                                               ; both -> {:results :status :count :elapsed-ms :resume}
(resume partial budget)                        ; continue a :timeout/:capped partial result
(abduce kb goal context opts)                   ; what would have to be true for the goal to follow:
                                               ; hypotheses minted as :default premises in a scratch
                                               ; context -> {:solutions :hypotheses :refused
                                               ; :context :status}.  Torn down before it returns
                                               ; unless {:keep? true}; only (abduciblePredicate P)
                                               ; makes a predicate assumable (docs/abduction.md)
(abduce-discard! kb result)                     ; discard a kept abduction's context and everything in it
(query-plan kb goal context)                    ; a sentence -> applicable provers: est-bindings + cost
                                               ; tier + completeness.  A VECTOR -> the join plan: the
                                               ; conjuncts in the order they run, each with :est-matches
                                               ; (the sound bound) :est-rows :est-prefix :block and why
                                               ; it sits there (docs/inference.md)
(search-tree kb goal context {:max-depth n})    ; the run that plan predicts: the search TREE as data
                                               ; -> {:goals :context :strategy :status :bounded? :answers
                                               ; :nodes :stats}, every node
                                               ; the frontier reached with its itemized estimate and the
                                               ; rewrite that produced it.  Needs a depth; bounded by a
                                               ; node budget + :max-ms (docs/inference.md, docs/web.md)
                                               ; opts: `search-tree-opt-keys` — :max-depth :strategy
                                               ; :node-budget :max-ms, and nothing else
(compare-tacticians kb goal context {:max-depth n}) ; the same goal under each tactician -> one row per
                                               ; ordering: its tree-stats, wall-clock :ms, and :answers
                                               ; SET.  Every complete tactician returns the same set —
                                               ; the rows let you verify it, not trust it
                                               ; opts: `compare-tacticians-opt-keys` — the same three
                                               ; bounds + :tacticians, and NOT :strategy (set per row)
(add-prover kb prover)                         ; register a custom prover
(add-evaluatable kb pred f opts)               ; wrap a plain fn as a computed predicate -> kb.
                                               ; A check (all args ground, truthy holds) or, with
                                               ; {:result :first|:last|n}, a value bound into that
                                               ; slot.  A fn value, never eval of data
                                               ; (docs/inference.md)
(register-modal-predicate kb pred [context])    ; grant `pred` belief-style projection:
                                               ; `(pred agent sentence)` is answered by proving
                                               ; `sentence` in the agent's context, as `believes`
                                               ; is.  A convenience over asserting
                                               ; `(modalPredicate pred)`, so the grant follows
                                               ; retraction and is scoped by the context holding
                                               ; it — `CxCore` by default (docs/belief.md) -> kb
(add-reasoner kb :allen :rcc8)                 ; register shipped ones by name -> kb
(reasoners)                                    ; the roster: the six algebras + :duration :metric-time
                                               ;   :sign :calendar
(reasoner :allen)                              ; one as a value, for a registry of your own
(lookup kb level goal context)                 ; the lookup-to-query stack, levels 0-7
(escalate kb goal context [floor])             ; cheapest level that answers (floor defaults to 2)
(explain-levels kb goal context)               ; what every level yields -> per-level counts
(levels)                                       ; the level table as data
;; qualitative constraint reasoning (docs/qcn.md).  Reads: a network is a property of
;; the stored facts, so these answer whether or not the calculus's prover is registered.
;; A variable context is not a reader at these four: it reads every context's facts into
;; ONE network, where two incomparable contexts compose for nobody — a diagnostic view of
;; everything stored, off which no goal is answered.  A goal fans over the readers.
(calculi)                                      ; the shipped calculi: base relations + vocabulary
(qualitative-network kb calculus context)      ; the tightened network + :consistent? (+ :unsatisfiable)
(possible-relations kb calculus context a b)   ; the base relations still possible between two terms
(qualitative-scenario kb calculus context)     ; one consistent arrangement, {[a b] -> relation}, or nil
(qualitative-scenarios kb calculus context n)  ; up to n of them (the count is exponential, so n is required)
(recover kb)                                   ; rebuild taxonomy + JTMS from the durable stores
(reindex kb)                                   ; rebuild the index (trie/roots/rule/term) from the records, then recover
(clear! kb)                                    ; empty both durable stores — `recover`'s counterpart,
                                               ; and irreversible, which is what the `!` says
(close! kb)                                    ; release a durable KB's directory: flush + close the
                                               ; stores, drop the file lock.  A durable fork releases
                                               ; its own writable directory, never the base's — that
                                               ; is mounted read-only and shared.  A no-op on a KB
                                               ; with no :dir (every in-memory backend, an ephemeral
                                               ; fork), so it is safe in a `finally`; the KB must not
                                               ; be used after — open-kb the directory to read again
(export-text! kb dir opts?)                    ; write its PREMISES out as a text KB — one
                                               ; <Context>.txt per context, the format the shipped
                                               ; ontology is authored in; opts {:context C} or
                                               ; {:cone C} to narrow.  Content-ordered and free of
                                               ; anything about the run, so the same knowledge
                                               ; always writes the same bytes
(load-text! kb path)                           ; read one back — a directory of Cx*.txt, or one
                                               ; such file.  The file name is the context, and
                                               ; every form goes through `assert`, so this is
                                               ; export-text!'s inverse and NOT import!'s
(export! kb dir opts?)                         ; write it out as a portable dump — field-map frames,
                                               ; no class names; opts {:variant :records|:records+index
                                               ; :compression :gzip|:xz|:none :chunk-size n
                                               ; :provenance? bool :on-progress f} — 10000 records a
                                               ; frame, provenance written by default
(import! kb dir opts?)                         ; read a dump back into the (empty) kb — export!'s
                                               ; inverse.  opts {:belief? true|:stored|false
                                               ; :report-every n :on-progress f}:
                                               ; true (the default) recovers belief too; :stored
                                               ; stores every justification and premise mark and
                                               ; leaves the recover for later; false reads no
                                               ; justification stream at all — browsable, not
                                               ; belief-queryable, the path past what an in-RAM
                                               ; JTMS scales to.  The summary counts two
                                               ; disagreements with the dump and stops for
                                               ; neither: :naming, stored but not re-assertable,
                                               ; and :refused, not constructible at all and so
                                               ; skipped with whatever rested on it.  A
                                               ; remapped load also reports what its own
                                               ; deletions cost, apart because they are
                                               ; different facts: :orphaned-ids, dump ids the
                                               ; load left naming nothing, and
                                               ; :dropped-justifications-orphaned, the
                                               ; deductions that went with them — as against
                                               ; the deductions a dump simply hangs off
                                               ; sentexes it never carried
(isa? kb individual type [context])            ; transitive type membership (context-scoped)
(types-of kb x [context])                      ; the believed types asserted of an individual
                                               ; — the matcher's own three filters:
                                               ; believed, visible, not `except`-hidden
(disjoint? kb type-a type-b [context])         ; provable disjointness (scoped with a context)
(disjoint-metatypes kb) / (metatype-members kb m) ; the declared `disjointMetatype` cliques and one
                                               ; clique's members — consulted, never materialized,
                                               ; so no `(disjoint a b)` pair is stored to read back
;; the taxonomy, read (thin delegations to vaelii.impl.taxonomy — reads only, since
;; edges and metadata are maintained by assert / retract! from the sentexes stating them)
(genls kb t [context]) / (specs kb t [context])         ; genl up/down closure (scoped with a context)
(genl? kb sub super [context])                          ; subtype test, scoped the same way
(types kb) / (contexts kb)                              ; the nodes of each hierarchy
(context-up kb c) / (context-down kb c) / (sees? kb k y); genlCx closures + visibility test
(context-of-agent agent) / (agent-of-context ctx)       ; the Alice <-> CxAgentAlice agent
                                                        ; context bijection (docs/belief.md)
(has-prop? kb kind pred [context]) / (props kb kind)              ; :transitive :symmetric :asymmetric :reflexive
                                                        ; :functional :irreflexive :anti-symmetric
                                                        ; :anti-transitive :decontextualized
                                                        ; :forced-decontextualized :abducible
                                                        ; :closed-extent :modal :target-following
                                                        ; :reifiable :unreifiable :quoting
                                                        ; :context-denoting, and the four :declares-*
                                                        ; that name a predicate as the SUBJECT of an
                                                        ; argument constraint (:declares-arg-isa
                                                        ; :declares-arg-genl :declares-quoted-arg
                                                        ; :declares-inter-arg-isa)
(inverse-of kb pred [context])                                    ; the declared inverse, or nil
;; what the engine does with its own grammar — declared *and enforced* against declared
;; and ignored, which no naming or wff check can tell apart
(interpreted term)                             ; {:enforced "where"} | {:inert "why"} | nil
(vocabulary-audit kb)                          ; the whole picture, incl. :unclassified
(term-role term)                               ; the naming role a spelling declares: :variable :number
                                               ; :lexeme :context :individual :predicate :sense
                                               ; :type, or nil — decided most-specific first
(describe kb term [context] [opts])            ; EVERYTHING the KB holds about one term, in one map,
                                               ; keyed by the term's role — "what can I ask about X?"
                                               ; every shape: :term :role :context :comment and the
                                               ; three closure lines :genls :specs :disjoint
                                               ; :predicate adds :arity :arg-declarations :props
                                               ;   :inverse :extent-count and the four grants
                                               ;   :closed-extent? :abducible? :modal?
                                               ;   :decontextualized?
                                               ; :type adds :predicates-for-type :instance-count
                                               ; :individual adds :types :predicates (with counts)
                                               ; :context adds :up :down :sentex-count, and
                                               ;   :computed-spec-of for a reified one
                                               ; Every declaration, grant and comment is read from
                                               ; `context`'s genlCx UP-CONE, so two vantages give two
                                               ; correct answers; `?ctx` (the default) reads every
                                               ; context.  Every list is a window with its size beside
                                               ; it — {:terms|:rows … :total :exact? :sorted?} —
                                               ; capped at :limit (`default-describe-limit`, 50);
                                               ; `describe-opt-keys` is the roster
(kb-diff a b)                                  ; what two KBs disagree about, as CONTENT ->
                                               ; {:added :removed :moved :belief-changed}.  Each side
                                               ; is a KB or a STRING naming a text KB (read with
                                               ; load-text! into an in-RAM KB of its own).  Keyed on
                                               ; the canonical sentence + context + strength, never on
                                               ; a handle, so a KB reloaded from its own export diffs
                                               ; empty; premises and derived alike, told apart by
                                               ; :premise? on every row.  Justifications, provenance
                                               ; and handles are not compared
(readable-sentence sx)                         ; a sentex's sentence with the author's variable names
                                               ; put back — a rule is stored numbered (?var0, ?var1)
(representative kb term [context]) / (same-class? kb a b [context])  ; the equality
(equiv-class kb term [context]) / (deprecated? kb term)  ; partition, read — scoped by
                                                         ; context like genls / specs
(find-sentexes kb term) / (find-sentexes-all kb terms)  ; inverted term index
(indexable-terms sentex)                                ; the terms that make a sentex findable —
                                                        ; exactly the keys it is posted under
;; the content order — the engine's own, so an application ranking its answers breaks the
;; tie the way the engine does.  Key on content, never on a handle: handles are allocated
;; in assertion order, so a keyfn returning one makes the ranking a fact about how the KB
;; was loaded.  The key is built once per element, and the default comparator walks a key
;; instead of printing it (9 before 10, and no *print-* var can elide two keys to one).
(sort-by-content keyfn [cmp] coll)              ; coll ordered by (keyfn element)
;; reified non-atomic terms (docs/nat.md).  The constant is term *identity*, not a name
;; anybody wrote, so a display shows the expression: `reified-term?` is a pure test on
;; the symbol and gates the read, `term-expression` is one hop (an argument that is
;; itself reified comes back as its constant, so a caller rendering each term keeps
;; every level addressable)
(reified-term? term)                            ; is this an opaque nat/ constant?
(term-expression kb term)                       ; the (F a…) it was minted from, or nil
;; the vocabulary — the terms themselves, read off the index's term roster, so the cost
;; is the number of distinct terms and never the number of sentexes.
(terms kb)                                      ; every indexed term, sorted by name
(term-count kb)                                 ; how many — one O(1) set-size read
(sentex-count kb)                               ; how many sentexes in total — the trie's
                                                ; own root count, O(1).  NOT the sum of
                                                ; count-in-context over contexts: that misses
                                                ; a context no genlCx edge names.
(find-terms kb q [opts])                        ; the terms matching q, sorted
                                                ; opts: {:match :prefix|:substring|:regex
                                                ;        :case-sensitive? bool :limit n}
;; extents and counts.  The count-* trio is an O(1) set-size read of what is **stored** — a
;; defeated sentex included — so it can disagree with belief-filtering `sentexes-matching`.  The
;; extent fns take {:believed? true} to filter, which is O(n); there is no O(1)
;; believed count and none is pretended.
(sentexes-in-context kb ctx [opts]) / (count-in-context kb ctx)              ; context root
(sentexes-with-functor kb pred [opts]) / (count-with-functor kb pred)    ; functor root
(sentexes-with-arg kb pos term [opts]) / (count-with-arg kb pos term)    ; argument-position root
                                                ; each extent is a LAZY seq over live state:
                                                ; records fetched as it is walked, so (take n …)
                                                ; costs n; a seq held across a write yields what
                                                ; is stored when walked — `vec` it for a snapshot
(ist kb Ctx sentence)                           ; ist: find or create sentence in Ctx -> handle
                                                ; `(ist Ctx S)` is also a READ goal — every read
                                                ; taking a sentence and a context takes one, Ctx
                                                ; winning over the argument (query family, above)
(handle-of kb sentence context)                 ; find WITHOUT creating -> handle or nil (ist's counterpart)
(contexts-of kb sentence)                       ; contexts a sentence is asserted in
(handles kb)                                     ; every live sentex handle — the whole-KB
                                                ; enumeration a content/audit pass folds over
(canonical-sentex kb sentence context)          ; the canonical sentex for a sentence WITHOUT
                                                ; storing it — same map shape as `sentex`, no
                                                ; `:id`; a stable content key / address
;; the meta-sentex handle term: `(sentexHandle H)` names a stored sentex so a meta can
;; predicate about it — `except` / `exceptWhen` and a `targetFollowingPredicate` reply
(sentex-handle n)                               ; the (sentexHandle n) term naming handle n
(sentex-handle? form) / (handle-id form)        ; is it one? / the id it names, or nil
(provenance kb handle)                          ; the per-handle bookkeeping map, or nil
(add-provenance kb handle m)                     ; merge application fields into it
(retract! kb handle)                            ; teardown -> {:removed-sentexes n :removed-justifications n}
(in? kb handle)                                 ; raw structural JTMS IN, before contextual exceptions
(believed? kb handle context)                   ; IN after exceptions visible from context, before
                                                ; assertion-context inheritance
(belief-status kb handle context)               ; deterministic diagnostic map:
                                                ; {:handle :view-context :stored? :in?
                                                ;  :assertion-context :exceptions :excepted?
                                                ;  :inherited-path :believed? :visible?}
                                                ; :exceptions is context/content ordered; every node
                                                ; is {:handle :in? :in-force? :excepted-by}
(believed kb handles)                           ; in? in batch -> the set of raw-IN handles
(why kb handle opts?)                           ; proof tree: support -> rule + recursive antecedents,
                                                ; terminating at premises, cycle-guarded, originalized
                                                ; opts {:max-depth n} (default 256); a branch at the
                                                ; cap reads {:truncated? true} — re-ask deeper.  The
                                                ; walk spends no JVM stack (explicit work stack), so
                                                ; the cap bounds the tree returned, not the depth a
                                                ; read can reach without overflowing
(why-not kb handle)                             ; stored but OUT: :defeated (+ what contradicts it)
                                                ; / :superseded (+ the restatement that displaced it)
                                                ; / :unsupported (+ the missing antecedents) / :not-stored
(why-not kb sentence context)                   ; the same four, plus the two only this arity
                                                ; can reach: :excepted (+ the exceptWhen that blocks
                                                ; it) and :closed-extent (a closedExtentPredicate
                                                ; grant says the extent is complete and this is not
                                                ; in it) — neither is ever stored, so
                                                ; there is no handle to pass.  A stored sentence
                                                ; delegates to the handle arity, except that a
                                                ; stored-but-disbelieved one is checked for an
                                                ; exception first
(why-not kb sentence context opts)              ; {:nearest n} runs a BOUNDED backward search and
                                                ; adds :nearest — the n rules that came closest, each
                                                ; {:rule :rule-sentence :satisfied :missing :bindings}
                                                ; — plus :nearest-search, saying which bound bit.
                                                ; OFF by default (it costs a search); bounds are
                                                ; :max-depth (`default-nearest-depth`, 3) and :max-ms
                                                ; (`default-nearest-ms`, 2000).  Attached to
                                                ; :not-stored alone; `why-not-opt-keys` is the roster
(argue kb asent context opts)                   ; four-valued epistemic status of one ground sentence:
                                                ; :true / :false / :unknown / :contradiction, with the
                                                ; results and justifications of BOTH sides.  No opts
                                                ; and it is `ask` (no rule expands); {:max-depth n} and
                                                ; it is `query`.  There is no default depth here either
                                                ; opts: `query-opt-keys`, checked at THIS door — a
                                                ; misspelt depth checked downstream is never checked at
                                                ; all, and answers :unknown for a derivable sentence
                                                ; :for-why / :against-why are `why`'s JTMS map, for a
                                                ; side the store holds; :for-derivation /
                                                ; :against-derivation are `query`'s {:proof? true} tree,
                                                ; for a side a rule derived instead.  A side carries at
                                                ; most one — the derivation is the fallback, and needs a
                                                ; positive depth and a ground sentence
;; introspection: sentex, justification, supporting-justifications, dependent-justifications, premise?, defeat-class
;;   both justification listings are ordered by CONTENT — the informant's own sentence,
;;   then the antecedent sentences — and so is the antecedent vector inside each
;;   justification, which is what `why`'s :because and `why-not`'s :missing print.  So
;;   the same knowledge reports identically whatever order it was loaded in (nmtms.md)
(blocked-justifications kb)                     ; the ids a rule exception currently blocks —
                                                ; every antecedent IN and supporting nothing.
                                                ; The one justification property belief does
                                                ; not report, so a proof tree reads it beside
                                                ; belief rather than instead of it
                                                ; (exceptions.md).  The whole set: the caller
                                                ; is rendering a tree and wants one read
                                                ; rather than one per justification

;; the log dial — process-wide, since one JVM has one `taoensso.trove/*log-fn*`, and
;; turnable on a process that is already running (docs/operations.md)
(set-log-level :debug)                          ; :error :warn :info :debug :trace, quietest
                                                ; first -> the level.  Anything else is refused
                                                ; (:unknown-option) rather than read as the
                                                ; nearest legal one
(log-level)                                     ; what it reads now — nil when the engine has
                                                ; installed no backend, which is what
                                                ; VAELII_LOG_LEVEL unset leaves: a KB you opened
                                                ; must not replace the logging of the
                                                ; application that opened it

;; the six public dynamic vars — process- or thread-scoped settings, `binding`-shaped
;; because they are about a whole batch rather than one call
*bulk-load?*                                    ; false: `assert` in bulk-load mode — the per-fact
                                                ; validation and dedup off for a caller-guaranteed
                                                ; well-formed, pairwise-distinct premise load
*write-unrecovered?*                            ; false: accept a write into a KB whose belief (or
                                                ; index) was never built over the store it opened,
                                                ; which the write doors otherwise refuse by name
                                                ; (:unrecovered-kb).  Its docstring lists what
                                                ; binding it gives up (docs/storage.md)
*creator*                                       ; nil: the creator stamped into provenance when opts
                                                ; names none.  Bind per session / import / user
*clock*                                         ; a 0-arg fn giving the `:created` stamp (epoch ms).
                                                ; Belief never reads provenance, so a wall clock here
                                                ; cannot touch order independence
*query-engine*                                  ; :dfs (default) | :inference | :hybrid — which backward
                                                ; executor `prove` / `prove-within` run
*query-options*                                 ; how the node engine searches: {:strategy …}
                                                ; {:portfolio? true} {:auto? true}.  Ignored by the DFS,
                                                ; which has one order and no choice to make
```

## Choosing a query function

Five entry points answer a goal, and the axis that separates them is **how much rule
expansion each will do**.  Pick by what you are asking, not by habit:

| Reach for | When you want | Machinery | Returns |
|-----------|---------------|-----------|---------|
| **`query` / `query?`** | **the default** — one door, one dial: how deep to expand rules | no `:max-depth` and the registry answers alone; a `:max-depth` and the node engine expands rules that deep.  Either way a **conjunctive** join (vector goal) | binding maps `{?x v}` |
| `ask` / `ask?` | an answer from what the KB stores or has cached, at a cost that does not depend on the rule graph | the prover registry (facts, transitivity, disjointness, inverse/symmetric metadata, evaluable arithmetic, NAF, arg) — **no rule expansion** | binding maps `{?x v}` |
| `sentexes-matching` | *stored, believed* literals matching a pattern — retrieval, not reasoning | belief-filtered index read; no inference, no subtype expansion | **sentex maps** |
| `prove` / `provable?` | backward chaining with **no depth to pick**: it terminates on the data | the recursive chainer, facts + rules only; a **conjunctive** join (vector goal) | a vector of binding maps, **one per derivation** — equal maps repeat, so `distinct` for an answer set |
| `lookup` / `escalate` / `explain-levels` | *diagnostics* — which level of machinery reaches this, and how dear | one explicit level of the 8-level stack | level maps |

**Result shapes differ by family.** `sentexes-matching` and the extent/term readers
(`find-sentexes`, `sentexes-in-context`, …) return **sentex maps**; `query` / `ask` /
`prove` return **binding maps**; `lookup` returns **level-result maps**
(`{:level :handle :sentence :context :bindings}`).

**Every read above takes an `(ist Ctx S)` goal**, asking `S` in `Ctx` with the named
context winning over the `context` argument — the resolution `assert` makes, so the form
means one thing on both sides of the KB.  So do `handle-of` and `why-not`'s sentence
arity.  Retrieval answers the sentexes stored in `Ctx`; the reasoning doors answer from
everything `Ctx` inherits.  A wrong arity is refused `:shape`, and an `(ist …)` standing as
a **conjunct** of a vector goal is refused `:not-well-formed` — a join's conjuncts share
their bindings, so there is no per-literal context to honor; ask the whole conjunction in
`Ctx`.  There is no `ist` on a rule's antecedent side (docs/contexts.md).

A **sentex map** has the stable keys `:id` (the handle), `:sentence`, `:context`,
`:truth`, and for a rule `:antecedent` / `:consequent` / `:direction` / `:defeasible`.
Key into it.
The concrete record class behind it (`vaelii.impl.sentex/LiteralSentex` / `RuleSentex`) is an
`impl` detail and not part of the contract — never `instance?`-test it.

**The sentex-map readers are lazy, over live state.**  `sentexes-matching` and the three
extent readers fetch records as their seq is walked, which is what lets a consumer bound
an open read — the browser shows fifty of an imported ontology's hundred thousand
`comment`s a page by taking fifty, not by fetching them all — and it means a seq held
across a write yields what is stored when it is walked, not when it was asked for.
`vec` one for a snapshot.  Over the daemon wire every answer is realized before it is
sent (`wire-safe`), so a remote caller always holds a snapshot.

## Batched assertion

A plain `assert` settles belief before returning, so a bulk load pays that
reconciliation once per fact.  `with-deferred-settle` runs a whole batch and settles
**once** at the end (chaining still runs per assert; only the settle is deferred) —
same belief for one reconciliation instead of N, since belief is order-independent.
`assert-many` is the collection form.  Only the assert path is deferred; a `retract!`
inside a batch settles eagerly, and nesting composes (only the outermost settles).

A read taken **inside** the batch reads it unsettled, and that is the contract rather
than a gap: deferring the settle defers the belief computation, so there is nothing yet
to read the batch's belief off.  `ask?`, `isa?` and `disjoint?` mid-batch can answer
through a fact, a `genl` edge or a conclusion the closing settle then defeats, blocks or
sweeps — the exception sweep is the visible half of it (`deferred_settle_test`).  Ask
once the batch has closed.

The taxonomy's depth potential is deferred with it, so a batch that adds `genl` /
`genlCx` edges does not pay the per-edge repair either (`docs/taxonomy.md`).

**Neither is a transaction, and that is on purpose.**  `with-deferred-settle` runs an
arbitrary body and `assert-many` a bare collection of sentences; a throw part-way through
either leaves what was already stored in place with belief unsettled.  That is the
documented state — the KB is consistent, only the settle did not run, so re-running or
settling by hand recovers it — and it is what an order-insensitive loader is built on:
`seed/load-sentences` asserts what it can, retries what a later sentence would have
admitted, and needs the sentences that *did* land to stay landed.  Rolling a bulk load
back would also cost an audit entry per premise mark, on the one path whose whole reason
for existing is that it is the fast one.  The depth potential is repaired on the way out
even so, since nothing else would ever repair it and every later reachability read would
pay for that.  **Where a batch must be all-or-nothing, use `edit!`** — the atomic door,
and the one with a `:remove` half.

**`bulk-assert-facts!`** is `assert-many` with the machinery a *trusted* corpus does not
need turned off as well: the per-fact definitional checks (the `arg` store query
above all), the dedup trie-walk, provenance, and forward chaining. What is left is the
write path itself, and the door reports what it costs — `:on-progress` is handed
`{:phase :loading :done n :elapsed-ms ms :facts-per-sec r}` every 100,000 facts and
`{:phase :done :total n …}` once the closing settle has run, so the last event is a rate
for the whole load and is comparable between runs and between corpus sizes. Where that
time goes, phase by phase: [storage.md](storage.md), "What a bulk load costs".

`edit!` batches assertions **and** retractions into one settle — `{:add [[sentence
context opts?] …] :remove [handle …]}`.  The adds land **before** the removes, so a
conclusion the removed premises solely-supported but an added one re-derives keeps a
witness through the dependency-directed sweep: it is not swept and rebuilt, and never
flickers OUT and back.  The final belief equals running the asserts and retracts
singly — `edit!` skips the intermediate tear-down and the N per-op settles.  Use it to
*replace* knowledge (a rule by a refined rule, a fact by a corrected one) without the
conclusions resting on it going dark in between.

**A batch is all-or-nothing.**  `check-edit` refuses a malformed entry or an unknown
removal handle before anything is applied, but it judges each `:add` against the KB **as
it stands** — so an entry admissible alone and refused once an earlier entry in the same
batch has landed (a `disjoint` clash, an `arg` violation, a `functional` slot, a naming
policy, a stratification refusal) is raised by the engine two entries in.  `edit!` then
takes the batch back **at the handles it wrote**: every add retracted, which collects
what it derived through the ordinary dependency-directed sweep; every premise mark undone
and every strength it raised restored; the violations ledger, the program and the refusal
record put back.  Belief and the handle roster are then exactly what they were before the
call.  The **handle counter** is the one thing that moves, since handles are minted in
assertion order and never reissued — the same thing a `preview` leaves behind, and
nothing reads a handle as a fact about the KB ([defenses.md](defenses.md)).

The refusal is rethrown carrying its own `ex-data` plus `:rolled-back true` and
`:in` / `:index` / `:entry` naming the line that raised it — `check-edit`'s vocabulary —
with the original hung off it as the cause.  A throw that is not an `ex-info` is rethrown
exactly as raised; the rollback ran the same.  A rolled-back batch emits **no** change-feed
event ([feed.md](feed.md)), and `edit-with-consequences!` is `edit!` and inherits all of
it.  The rollback is the one `preview` uses ([preview.md](preview.md)); a removal is the
half no rollback can put back, so every `:remove` is asked for its refusal after the adds
and before the first teardown, and past that point the batch is committed.

## Three formats, and which question each answers

A KB moves in three shapes, and they are separate doors because they answer different
questions:

| | what it holds | written by | read by |
|---|---|---|---|
| **the store** | the live KB | the engine | the engine |
| an **export dump** | every record and justification, at its own handle | `export!` | `import!` |
| a **text KB** | premises only, in the author's own spelling, at no handles | `export-text!` | `load-text!` |

A dump is a KB's **state**; a text KB is its **content**. Only the second survives a
re-derivation, a rename, or an engine that concludes something new — which is what an
author who edits an ontology wants, and what a dump deliberately is not. The shipped
ontology (`resources/kb/`) *is* a text KB, so `export-text!` is the writer for a format
the engine already reads.

`export-text!` writes one `<Context>.txt` per context: **the file name is the context**,
and a sentence for another one says so with `(ist Cx S)` as it would anywhere else. Each
premise keeps its `:strength` — `:monotonic` as a `(set/monotonic S)` wrapper, `:default`
as nothing, since that is the door's own fallback — and each rule its `set/*Rule` /
`set/defaultRule` wrappers and its `exceptWhen`, so a reload yields the same canonical
sentexes at the same strengths and the same beliefs. An `exceptWhen` is **two** premises
at two strengths, and the wrapper's position says which: outside, it is the assertion's
own option and reaches both halves; on the query, `(exceptWhen (set/monotonic Q) R)`, it
is the exception's alone ([exceptions.md](exceptions.md)). `{:context C}` narrows to one file
and `{:cone C}` to `C` plus every context it sees.

**Premises only, and no handles.** A derived sentex is what the engine concluded, so
writing it would store as a premise what the KB believes as a conclusion; chaining puts it
back at load. A premise that names a sentex *by handle* — an `(except H)`, a
`targetFollowingPredicate` meta — has no text form at all and is counted in `:skipped`:
the number is a fact about this store. For those, and for handle identity in general, the
door is `export!`.

**Deterministic.** Forms are ordered by content and the text carries nothing about the run
that wrote it, so two KBs holding the same knowledge write byte-identical files whatever
order they were built in ([defenses.md](defenses.md)).

`load-text!` reads a directory (or one file) in **one order-insensitive pass**: a form
refused because content further down has not arrived yet is retried, and the context
topology goes in first whatever order it arrived in — a firing with no placement context
is *dropped* rather than refused, so a `genlCx` edge arriving after the fact it would have
placed is the one thing retrying cannot fix. Every form goes through the ordinary write
path, so the KB it lands in need not be empty. `lein cli load` is this door
([operations.md](operations.md)).

## Validating without writing

`assert` answers "would this store?" by *doing* it: the first failing check throws and
nothing lands.  A caller that wants the answer rather than the effect — an editor
validating a line, a critic grading a proposed batch, an importer triaging a corpus —
asks **`check`** instead.

`(check kb sentence context opts)` runs `assert`'s own checks, in `assert`'s order, for
their answer: naming, groundness, structural well-formedness, edge stratification, then
the three definitional constraints; for a rule, the imperative ban, range-restriction,
naming and rule-set stratification, per rule the polycanonicalization stores — one per
conjunct of a conjunctive consequent times one per alternative of a disjunctive
antecedent.  It
follows `assert`'s dispatch into `(ist Ctx S)`, a `set/*Rule` wrapper, and an
`exceptWhen`.  **Nothing is stored** — no sentex, no index entry, no taxonomy edge, no
chaining, no settle.

The naming stage checks **every literal** the sentence contains, not its outermost
functor alone, so a rule's antecedents and consequent are reported by frame and
spelling — `functor lives_in in rule consequent (lives_in ?x cold_place) is snake_case
… write it camelCase as livesIn` (docs/naming.md).

It returns a **vector of problems**, empty when the sentence is admissible.  Each is a
map with the `:type` keyword `assert` would have thrown — `:naming`, `:not-ground`,
`:not-well-formed`, `:not-range-restricted`, `:not-indexable`, `:disjunction-too-wide`, `:not-stratified`,
`:not-assertible`, `:exception-not-closed`, `:arg-type`, `:arg-genl`, `:arg-position`, `:inter-arg-type`,
`:arg-constraint-kind`, `:arg-variable`, `:arity`, `:disjoint`, `:functional`, `:asymmetric`,
`:anti-transitive`, `:irreflexive`, `:anti-symmetric` — a readable
`:message`, and whatever else that check knows (`:arg` / `:expected` / `:position` for an
arg breach, plus `:trigger` and `:trigger-position` for the `interArg` form, which
names the argument whose type made the constraint fire; `:cycle` for a stratification
one).  Three further types are about the *request* rather than the
knowledge: `:shape` (the context is not a symbol, the sentence is not an
s-expression, or it is a **vector** — below), `:unknown-option` (a non-map `opts`, an `opts` key `assert` does not read, a
`:strength` that is not an assertable class, or a `:direction` that is unknown, on a
non-rule, or contradicting the wrapper the sentence already carries — below) and
`:not-checkable` (a top-level
`do/` imperative, which `check` will not run to find out what it does).  One more is
about neither the request nor the knowledge but the **KB**: `:unrecovered-kb`, which
every write door refuses before it reads the sentence at all, so `check` reports it
alone and first — and not at all under `*write-unrecovered?*`, where `assert` lands the
write.  The stages stop
at the first that finds anything, since each later one reads the KB assuming the earlier
ones held.

`check-edit` is the same over an `edit!` batch, and each problem additionally carries
`:in` (`:add` / `:remove`), `:index` and `:entry`, so a caller can point at the line
rather than at the batch.  An `:add` is judged against the KB **as it stands**, and a
`:remove` for naming an actually stored handle (`:unknown-handle`).

Two things `assert` does that `check` deliberately does not: it does not reify a ground
reifiable NAT (that mints a constant, which is a write), and it does not evaluate an
imperative.

## Previewing the consequences

`check` answers whether a batch would be *admitted*.  **`preview`** answers what it
would *mean*: `(preview kb {:add […] :remove […]} opts)` returns the belief the batch
would add and the belief it would take away, and then puts the KB back exactly as it
found it.

**`edit-with-consequences!`** is the same question after the fact — `edit!`'s
`{:added :removed}` with `:believed-added` / `:believed-removed` **and `:bounded?`**
merged in, in `preview`'s entry shapes, so a caller renders a promise and its outcome
with one renderer — and knows when a cap bit, since a capped diff read as complete is
a consequence silently unreported.  `edit!`
alone reports the handles it stored, which is what the caller already said; this reports
what followed, and `:premise?` on each entry is what separates the two.  Its removed half
omits what the sweep *deleted* (there is no record left to describe) — for that, ask
`preview`, which suspends rather than retracts.  See [preview.md](preview.md).

## Being told, instead of asking again

**`watch`** turns that same diff into a feed.  `(watch kb f)` calls `f` with
`{:believed-added :believed-removed}` — `preview`'s entry shapes — after every settle that
moved belief; `(watch kb goal context f)` is a **standing query**, calling `f` only for the
entries `goal` answers and carrying the `:bindings` that answered.  Both return a token for
`unwatch`; `watchers` lists what is registered.

A batch settles once, so a batch is one call, and its halves are what
`edit-with-consequences!` reports for the same batch.  A `preview` and a `recover` are
silent, a mutation that moved no belief is silent, and a goal whose truth is not a function
of the moved region — a conjunction, an aggregate, `unknown`, `thereExists`, an evaluable,
an `ist` — is **refused** (`:not-watchable`) rather than watched for nothing, and so is
an `or`: no stored sentence unifies with a disjunction, so a watch on one would fire
never.  The read doors refuse the same goal at the shape guard (`:shape`), a read
normalizing to one conjunction rather than a union
([canonicalization.md](canonicalization.md)).  A listener
runs after the settle, so it may write; one that throws loses its own event and nothing
else.  See [feed.md](feed.md).

## Three reads for a reader rather than a program

Everything above answers a question somebody already knows how to ask.  These three are
for the reader who does not yet: what is here, why is it not, and what changed.

**`describe` — what can I ask about `X`?**  A term's arity, the types that bind its
arguments, its relation properties, its inverse, its place in the hierarchy, its extent
count and the KB's own comment on it are nine separate reads, and the risk in taking
them one at a time is not that one is wrong but that the assembly is.  `(describe kb term
context)` is that assembly, keyed by the term's own role — predicate, type, individual or
context — so what comes back is shaped like what the term *is*.  The browser's term page
renders exactly this and computes none of it a second time ([web.md](web.md)).

Two properties are worth stating on their own.  **It is scoped**, and that is not a
detail: an `arg` declaration, an `abduciblePredicate` grant and a `comment` are each a
policy of the context that states them, so `describe` reads them from the asking context's
`genlCx` up-cone and two vantages give two different, both-correct answers.  A read that
answered from the whole KB would report a declaration to a reader for whom it does not
bind, and nothing in the answer would say so.  And **every list is a window with its size
beside it** — `{:terms :total :exact? :sorted?}` for terms, `{:rows …}` for maps — because
on an imported ontology one type has 110,000 subtypes and a reader who is handed a
truncated list without its total has been told something false.

The role is `term-role`'s with one override: a term the `genl` hierarchy holds as a node is
described as a **type**, since a type *is* a unary predicate and no spelling separates the
two ([naming.md](naming.md)).

**`why-not` `{:nearest n}` — why doesn't my rule fire?**  `:not-stored` is the emptiest
answer the door has, and it is the one that arrives when a rule was supposed to conclude
the goal: nothing is stored, so there is no handle, no support and no defeat to report.
`{:nearest n}` runs a bounded backward search and reports the rules that came closest, each
with the antecedents the KB *can* satisfy, the ones it cannot, and the bindings the goal
forced on the rule.  `:missing` is the line to read — it is the fact nobody has asserted.

It is **off by default** and that is deliberate: `why-not` is cheap enough to call in a
loop over a conflict list, and a backward search per call is not.  The bounds are
`:max-depth` (3) and `:max-ms` (2000), both overridable, and `:nearest-search` reports
which of them bit — `:complete`, `:bounded`, `:timeout`, or `:refused` where the search
would not start.  The frontier is the **node engine's** whatever `*query-engine*` is bound
to: the DFS holds its unfinished proofs on the JVM stack and unwinds them as it fails, so
there is nothing left to read, while the node engine's state is a value that outlives the
search ([inference.md](inference.md)).  A rule needing more rewrites than `:max-depth`
allows is therefore not reported, and the bound in the answer is what says so.

**`kb-diff` — what changed?**  Two KBs holding identical knowledge share not one handle:
handles are allocated in assertion order, so a reload renumbers everything and a diff keyed
on one reports a KB loaded from its own export as wholly changed.  `(kb-diff a b)` keys on
**content** — the canonical sentence, its context, its strength — and sorts every bucket
the same way, so a KB and its own text export diff empty and two runs of one comparison
print the same thing.

The four buckets are the four ways two KBs differ about one sentence: `:added`, `:removed`,
`:moved` (the same sentence at the same strength in a different context) and
`:belief-changed` (stored in both, believed in one) — the last being the difference a
comparison of stored records alone cannot see, and the one a defeated default makes.
Premises and derived sentexes are compared alike, told apart by `:premise?` on every row: a
conclusion that stopped following is a difference between two KBs even though nobody wrote
it either time.  Either side may be a **string** naming a text KB, read with `load-text!`
into an in-RAM KB of its own, which is what `lein cli diff <a> <b>` is.

What it does not compare, stated so nobody reads more into an empty answer: **justifications**
(which rule concluded a derived sentex, and from what), **provenance** (creator, timestamps,
application fields) and **handles**.  Two KBs can diff empty and differ in every one of
them; `why` is the read for the first and `provenance` for the second.

## Argument-shape contracts

**A sentence is a list; a vector is a query's conjunction.**  Both doors are
`sequential?`, and only one of them means "one sentence": a vector goal is what `query`
and `prove` spell a **join** with (above), so the two doors read the same brackets two
different ways.  So the write door refuses a top-level vector (`:shape`), which is the
one shape it could otherwise take and answer differently for — `[likes Tom Ann]` stored
the sentence `(likes Tom Ann)` and handed back to `prove` asked for a three-goal join of
`likes`, `Tom` and `Ann`, which is no solutions and no error.  `assert`, `check`,
`check-edit` and `assert-inert` share the guard; nested vectors are untouched, since the
reading that collides is the top-level one.  Write the list.

**The read doors refuse it too**, and for the mirror reason: a door that answers a
*single goal* has the same two readings of one bracket, so `[likes Tom Ann]` handed to
`ask` asked about a three-goal join written where one sentence was meant, and answered
nothing rather than saying so.  `ask`, `ask?`, `ask-within`, `sentexes-matching`,
`handle-of`, `prove`, `provable?`, `prove-within`, `query`, `query?`, `query-plan`,
`search-tree`, `compare-tacticians` and
`abduce` refuse a top-level vector by name (`:shape`), carrying `:goal` — or `:conjunct`
where the vector sits *inside* a conjunction, naming which element of the join it was.
The doors that take a conjunction on purpose still take one; what is refused is a vector
where a sentence goes.

**`assert-opt-keys`** is the roster of every key `assert` / `assert-rule` reads, and a
key off it is **refused** (`:unknown-option`) rather than ignored — as is a `:strength`
outside `{:default :monotonic}`, and a non-map `opts` altogether.  The failures are
otherwise silent in the same way: the sentence lands, at a defeat class the caller did
not ask for, and a stored sentex carries no record of the class it was meant to have.
`{:strenth :monotonic}` makes known-true content defeasible; `{:strength 0.7}` names a
class the KB does not have; `(assert kb s ctx :monotonic)` names nothing at all.
`check` reports all of them (the non-map `opts` under `:unknown-option`), so a batch
critic catches them before anything is written.  `why` holds its own `opts` to the same
standard: it reads `:max-depth` alone, and a non-map `opts`, an unknown key, or a
`:max-depth` that is not a natural number is refused (`:unknown-option`).

**`edit-batch-keys`** is the same answer for the other batch door: every key an `edit`
batch may carry, which is `#{:add :remove}` and is read by `edit`, `check-edit`,
`preview` and `edit-with-consequences` alike — so the four cannot disagree about what a
batch is.  Public for the reason `assert-opt-keys` is: a caller that can ask "is this a
real key?" does not have to find out from a wrong answer.

**Every door holds a roster, not just these two.**  An option map is a request, and a key
a door does not read is a request it cannot honour — so it is refused rather than
dropped, at `forward-chain`, the extent readers (`sentexes-in-context` /
`-with-functor` / `-with-arg`), `query`, `search-tree`, `compare-tacticians`, `argue`,
`preview`, `edit-with-consequences!`, `export!`,
`import!`, `find-terms`, `abduce`, the anytime budget maps, and `open-kb`.  The failure a
roster exists to stop is not a crash but a *different answer*: `{:max-derivation n}` at
`forward-chain` ran unbounded, `{:believed true}` at an extent reader answered the stored
extent with defeated defaults in it, and an `open-kb` mount or durability key naming no
axis opened a KB other than the one asked for.  Each of those is a plausible answer to a
question nobody asked, which is the shape of failure hardest to notice from the outside.

`query`'s roster is **`query-opt-keys`**: its own dial plus the node engine's keys, which
is where everything but `:max-depth` and `:proof?` goes — and the engine reads what it
knows and ignores the rest, so an open roster there would let `{:max-deph 3}` answer
facts-only with nothing to say it had.

**A roster is what its door reads, never a superset.**  The two debugger reads run
`query`'s search in a fixed mode, so each holds its own: **`search-tree-opt-keys`**
(`:max-depth :strategy :node-budget :max-ms`) drops the keys that door overwrites or never
looks at, and **`compare-tacticians-opt-keys`** trades `:strategy` for `:tacticians`,
because that door sets the ordering per row.  A roster wider than its door is a key
accepted and then discarded — the same silent default a roster exists to refuse, one
level in.

The four backward-search doors read the same rule the other way.  **`prove-opt-keys`**
(`:max-ms :max-depth`) is what `prove` and `provable?` take; **`ask-opt-keys`**
(`:max-ms`) is what `ask` and `ask?` take, and the missing `:max-depth` is the door
saying what it is — nothing in the prover registry expands a rule, so there is no
transformation depth to bound there and a `:max-depth` would be accepted and never
consulted.

### What an exhausted bound answers

The two bounds on those doors are not the same kind of thing, and the answers differ
because of it.

`:max-depth` **prunes**: the space under the depth is genuinely exhausted, so what comes
back is the whole of what that depth admits. `(prove kb g ctx {:max-depth 2})` is a
complete answer to a smaller question, and `(provable? kb g ctx {:max-depth 2})` answering
`false` means *no derivation within two rewrites*, which is a real thing to be told.

`:max-ms` **suspends**: the search stops where it is, and what it has is a *prefix* of the
answer set. So these doors refuse rather than return it — `:type :budget-exhausted`,
carrying `:door`, the `:bound` it was given, the `:status` (`:timeout`) and `:elapsed-ms`.
A prefix handed back as an answer set is indistinguishable from the whole of a KB that
knows less, and on `ask?` / `provable?` it would be a `false` that means *we stopped
looking* rather than *the KB does not say so*. A caller who wants the prefix asks through
[`ask-within` / `prove-within`](anytime.md), which return it with a `:status` saying
exactly what it is, and `resume` continues from there.

Everywhere a key off the roster is
`:unknown-option`, and `check` reports what the writing door would throw.  The CLI keeps a roster of its own —
its `--` flags, refused the same way and for the same reason — since a command line is
not an option map.

**Every handle-taking fn holds one contract.**  `nil` is a question with an answer —
`handle-of` answers nil for a sentence the KB does not hold, so `(in? kb (handle-of kb
s ctx))` is an ordinary composition — and each fn answers it gracefully: `in?` and
`premise?` false, `sentex` / `justification` / `defeat-class` / `provenance` nil,
`supporting-justifications` / `dependent-justifications` empty, `why` `{:stored?
false}`, `why-not` `:not-stored`, `add-provenance` a no-op, `retract!` a no-op.
Anything else that is not an integer handle is **refused** (`:bad-handle`), a vector
of handles included — `assert` returns a vector for a rule that polycanonicalized (a
conjunctive consequent, a disjunctive antecedent, or both), so
`(retract! kb (assert kb rule ctx))` would otherwise be a silent no-op that reads as
"there was nothing to do".  The contract covers `retract!`, `in?`,
`premise?`, `believed?`, `belief-status`, `why`, `why-not`, `provenance`,
`add-provenance`, `sentex`,
`justification`, `defeat-class`, `supporting-justifications`,
`dependent-justifications`, and `edit!`'s `:remove` entries; `check-edit` reports the
same refusal as a problem (`:bad-handle`) rather than throwing it.

`vaelii.impl.spec` carries opt-in `clojure.spec` `fdef`s for the whole shape-carrying
surface (every entry point taking a handle, context, level, strength/direction, or an
option/budget map) — the shapes *inside* an option the roster admits, plus a string
where a millisecond count belongs.  Nothing runs until a caller
`(clojure.spec.test.alpha/instrument vaelii.impl.spec/public-syms)`.  They double as
machine-checked documentation.

**A trailing `!` marks an operation that is not easily reversible** — one the KB cannot
take back. Usually that means destroying or removing stored knowledge, and on
`vaelii.core` the whole roster is:

| | |
|---|---|
| `retract!` | tears down premise support and everything solely resting on it |
| `edit!` | its `:remove` half runs the same teardown `retract!` does, so a batch that adds and removes is as irreversible as its removals |
| `edit-with-consequences!` | the same write, reporting what it turned out to mean |
| `clear!` | wipes every record and index entry |
| `clear-violations!` | empties the dropped-conclusion ledger (the drops are final either way) |
| `abduce-discard!` | drops an abduction's scratch context and everything it licensed |
| `reset-settle-stats!` | clears the settle instrumentation and its histogram |
| `bulk-assert-facts!` | only adds — but on a fast path whose two preconditions the *caller* owns, so a violated one is a store the checks would have refused |
| `export!` | writes a directory tree outside the process |
| `export-text!` | the same — a directory of text files outside the process |
| `load-text!` | asserts a whole text KB; the undo is `retract!` per handle, as for any assert |
| `import!` | fills the store wholesale, at the dump's own handles and bypassing the assert path; the only undo is `clear!` |
| `close!` | destroys nothing — but the KB value in hand, and every KB sharing the directory, is dead afterwards; reopening yields a new KB, not the one you held |

Inside `vaelii.impl.*` the same convention runs — `delete-sentex!`, `unindex-sentex!`,
`del-genl!`, `unmark-prop!`, `clear-records!`, `clear-index!`.

Everything that *adds* or *recomputes* is bare even though it mutates: `assert`,
`assert-rule`, `add-premise`, `register-modal-predicate`, `index-sentex`, `mark-prop`,
`forward-chain`, `settle`,
`recover`. So the `!` is a warning about not being able to undo, not a note that a
function has effects — which is why `vaelii.core` excludes `clojure.core/assert` and
callers write `v/assert`. A `set-` that installs a value is bare for the same reason:
`set-solver` and `set-log-level` both name a setting the next call replaces, and
`log-level` reads the one in force, so turning either back is one call.

Assert known-true facts with `{:strength :monotonic}`; the default is `:default`
(most of a common-sense KB), and a default is defeasible at the edges.

`opts` on assert: `{:chain? false}` skips forward chaining, `{:max-depth n}`
bounds it. `vaelii.impl.core-context/load-into` asserts the CxCore vocabulary — every special
predicate the engine interprets (types/contexts, arg/genlArg/interArg,
disjoint/disjointMetatype,
implies + the `set/*Rule` wrappers, the transitive/symmetric/reflexive/functional/
inverse/decontextualizedPredicate metadata, `not`, `contradicts`, `ist`, and the
predicate meta-ontology (`predicate` ⊃ unary/binary/ternary + the algebraic
subtypes)), each documented by a `(comment <term> "...")` sentex so the KB
documents itself in its own representation (`core-context/comment-of` reads them back),
plus the metadata⇒predicate-type rules. `vaelii.impl.starter/load-into` builds a
**schema-only** common-sense KB on top — types, relation definitions, and theory
rules, but **no individuals or facts**. Its declarative content lives as plain text
under `resources/kb/`, one file per context, read by `vaelii.impl.seed`
(`read-sentences` / `load-context`, via `clojure.edn`, so a KB file is data and can
never run code). Every sentence about a term is grouped **term-centrically** (blocks in
natural sort order), and every context file is **discovered on the classpath and loaded
on kb start** (`seed/layer-contexts`), so adding a KB is dropping a `Cx<Name>.txt`
file — no code change. What stays in `starter.clj` is the *order the layers* load in
and the one computed batch (every type is a `unaryPredicate`, placed in CxCore).
The context topology is a **five-layer spindle**, most general (top) to most specific
(bottom): **CxCore** (the vocabulary head, every context sees it) → the **upper**
definitional band (`resources/kb/upper/`: `CxAbstract` = the abstract type skeleton, body
parts and substances, `partOf`/`locatedIn`/`madeOf`, and the two **type-level**
relations `largerThan`/`partType`; `CxOrganism` = the biological taxonomy +
disjointness; `CxLife` = organism relations and states; `CxSociety` = social
relations; `CxMeasure` = the theory of measurement; `CxSpace` = RCC-8 region
relations and cardinal directions; `CxTime` = Allen's interval relations, the point
algebra, the calendar constructors and the event/fluent vocabulary) →
**CxUniverse** (the mid anchor, free for lifted universal facts) → the **middle**
theory band (`kb/middle/`: `CxKinship`, `CxMereology`, `CxBiology`, `CxChange`,
`CxSocial` — the rules; `CxAnatomy` and `CxSize` — claims about kinds) →
**CxWell** (the bottom anchor, transitively seeing the whole ontology).
upper is *definitional* (what things **are**, always true, like `genl`); middle is
*theory* (how they **interrelate**, where several overlapping accounts can coexist).
Each upper/middle file wires itself into the axis, so the topology is data; a
CxCore-only KB is just the vocabulary head, and a user adds a sibling in either band.
The middle theories are the defeasible defaults that state their own exception with
`exceptWhen` (birds fly except penguins; animals breathe air except fish; living things
are alive until they are dead and awake until they are asleep — four rules of one shape,
differing in whether the exception names a species, a whole class, or a state that
changes) and the rules with **connected conjunctive antecedents** (antecedents sharing
a variable so they join — grandparentOf, part-location, owns-parts).

**A binary predicate says which level it relates at, unless its two ends disagree.**
`relationKind` is a `disjointMetatype` over `instanceRelationPredicate` and
`typeRelationPredicate`: `parentOf`, `northOf` and `madeOf` relate individuals; `genl`,
`disjoint`, `largerThan`, `partType`, `capabilityType` and `siblingDisjointException`
relate kinds. *At most* one, not
exactly one — the unmarked are those whose two ends sit at different levels, or at no
level at all (`implies` is a connective; `rewriteOf` takes either role so long as its two
sides agree; `result` and `genlResult` relate a function to a type;
`functionCorrespondingPredicate` relates a function to a predicate; `hasCapability`
relates one animal to a capability kind). The mark is not decoration: it decides which
argument-check family the predicate may use, one for **every** position, which is why a
mixed predicate cannot carry one — `arg` on a `typeRelationPredicate` and `genlArg` on
an `instanceRelationPredicate` are both refused `:arg-constraint-kind`. The distinction is
what `typeToInstancePred` is stated over, and it is the difference between `(largerThan
dog cat)` — dogs are bigger than cats — and a claim about two particular animals.

**Contingent data lives in the tests.** The starter ships no cast: individuals, facts,
and the worked fables hang **below CxWell** in the test-world. `test/vaelii/world.clj`
loads a cast (type memberships + natural-world facts in `CxNaturalWorld`, social
facts in a sibling `CxSocialWorld`); `test/vaelii/world_fables.clj` adds four Aesop
fables as contexts under `CxStories` (`CxLionMouse`, `CxTortoiseHare`,
`CxAntGrasshopper`, `CxCriedWolf`), each *deriving* its moral by joined
inference; `test/vaelii/world_narrative.clj` layers a **story-understanding ontology**
(types agent/event/action/goal/mental_state and relations
wants/does/brings/achieves/causes/beforeEvent/afterEvent with metadata — `causes`,
`beforeEvent` transitive; `beforeEvent`/`afterEvent` inverse — and arg, plus a forward
goal-achievement rule `wants + brings + achieves ⇒ achievesGoal`) on a new fable
`CxFoxCrow` and retrofitted onto `CxTortoiseHare`. Because `sentexes-matching` is
exact-context and a middle theory is seen by every CxWell descendant, a rule firing
over cast facts in `CxNaturalWorld` places its conclusion back there. `afterEvent`
inverts a transitively-derived `beforeEvent` as well as a direct one: `InverseProver`
hands the swapped goal back to the engine (minus itself and backchaining) rather than
matching raw facts, so an inverse composes with its partner's transitivity.
