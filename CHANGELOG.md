# Changelog

Notable changes to `vaelii`, newest first. Versions follow
[semantic versioning](https://semver.org/spec/v2.0.0.html); pre-1.0, a **Breaking**
entry raises the minor. What each class means, and why a **Refusal** is patch-eligible,
is [CONTRIBUTING.md §3](CONTRIBUTING.md).

**Releases before 0.21.0 are summarized rather than reproduced.** Each one
keeps its title, its class census and every `*Breaks:*` token, so an upgrade across
several releases is still a grep for the name you call. The full entry prose for a
released version is in this file's git history, at the tag of the release that shipped
it — `git show v0.16.0:CHANGELOG.md`.

## 0.21.0 — 2026-09-23 — "a definitional clash is decided at the context that sees it whole, and a relation can state that its arguments commute"

- **`:refuse` weighs a definitional clash at its vantage, so `violations` is no longer
  where such a clash ends up.** A pair whose halves sit in two contexts is admissible to
  both writers — neither sees the other half — and the context that does see it whole now
  decides it under `:refuse` exactly as under `:arbitrate`:

  ```
  CxUniverse   (disjoint dog cat)
   ├─ CxA      (cat Rex)   :default
   │   └─ CxD  (dog Rex)   :monotonic     ← the vantage
   ├─ CxB      (cat Rex)   :default
   └─ CxC      (dog Rex)   :monotonic     ← CxE sees CxB and CxC, and is their vantage
  ```

  Before this change `(cat Rex)` written into CxA last was admitted and filed in
  `violations`, with CxD believing both memberships, while `(dog Rex)` written into CxD
  last was refused — so the same knowledge landed on different belief according to which
  half arrived last. Both orders reach one answer at CxD now, and the two sibling
  contexts reach it at CxE.
  The write entry point keeps its policy: `:refuse` still turns away a writer whose own
  context sees the far half. What makes this safe is scoped defeat — the decision reaches
  the vantage and below and no context that reads one half alone — which is why it was
  not done before.

  The cross-context `functional` / `asymmetric` / `anti-transitive` reporting pass is
  gone with the gap it covered, and with it the `:constraint-exposure-truncated` entry
  kind; a reader takes those clashes off `contradictions` and `conflicts`. The
  `:disjoint` exposure entry stays, for the pair no vantage convicted: the vantage is the
  *maximal* common descendant, so a separation derivable only from a context below it is
  reported and not decided. `:partner-sweep-truncated` stays too, now filed for the
  settle rather than for that pass, and now meaning a vantage the arbitration never asked
  from. *Class:* **Breaking** (under `:refuse`, a cross-context definitional clash moves
  belief and leaves `violations`). *Migration:* read these clashes off `contradictions`
  and `conflicts` rather than `violations`; a reader that branched on
  `:constraint-exposure-truncated` reads `:arbitration-truncated`, which is the same
  budget with `undecided` in place of `unreported`. A KB that wants both halves of such a
  pair believed states the weaker one in the vantage as well.
  [docs/nmtms.md](docs/nmtms.md#who-asks-the-pairs-question),
  [docs/contexts.md](docs/contexts.md)

  *Breaks:* `violations`, `contradictions`

- **A refusal reads the grounds of a clash, not only what it opposes.** `assert` refused a
  `disjoint` or `functional` clash under `:arbitrate` whenever the sentex it opposed was
  known-true, reading nothing of the derivation that made the two a pair. A pair reached
  over a `:default` `genl` edge is one a denial of that edge retires, so the sentence was
  thrown away on the strength of what had not been written yet — and the same three
  sentences in another order stored and believed it:

  ```
  CxUniverse   (genl chi thing) (genl dog thing) (genl cat thing)  (disjoint dog cat)
   └─ CxA      (genl chi dog)                 :default
        └─ CxB (not (genl chi dog))           :monotonic
               (chi Kit)  (cat Kit)
  ```

  Six write orders of CxB's three sentences, `(cat Kit)` at either strength: under
  `:arbitrate` one of the six refused `(chi Kit)` at `:monotonic`, and all six now leave
  one store and one set of beliefs — both memberships believed at CxB, nothing reported.
  The refusal now needs both halves known-true, the opposition and the derivation:
  `checks/grounds-class` reads the separating declaration and the `genl` steps it is read
  over (`taxonomy/disjointness-class`, built on the new `taxonomy/key-class` and the
  existing `taxonomy/reach-strength`), and the functionality mark with the predicate hierarchy it
  descends. A clash every link of which is known-true refuses exactly as before.
  `lein perf` gains `refusal-grounds-reading`, which holds the opposing membership
  `:monotonic` so the grounds read runs — every other arbitrating check stopped at the
  first read — over a diamond ladder of `genl` edges whose ancestor paths double per
  level: 1.71× against a 3.0× bound, where the same answer taken one witness per ancestor
  path (`taxonomy/disjointness-witnesses`) reads 4155× and 482 ms for one entry-point
  decision. `constraint_nogood_test` pins the property the ratio rests on:
  `reach-strength` takes the **strongest** route rather than the first, so a defeasible
  route beside a known-true one still refuses.
  `asymmetric` and `anti_transitive` read the opposing class under either policy and are
  not narrowed here. *Class:* **Breaking**. *Migration:* the shipped upper ontology now
  declares its own separations and functionalities known-true
  (`(set/monotonic (disjoint …))` in `resources/kb/`, 64 declarations), so a KB built on it
  refuses what it refused before; a KB with its own `(disjoint A B)` or `(functional P)`
  written at the default strength gets the clash **stored and weighed** rather than a
  throw, and restores the refusal by asserting that declaration with
  `{:strength :monotonic}`. Belief is unchanged in every case: the arbitration gives the
  known-true side the answer a refusal would have. *Breaks:* `assert` under
  `:constraints :arbitrate`, for a `:disjoint` or `:functional` clash whose declaration or
  whose `genl` path is defeasible; `check` predicts the admission there and returns empty.
  `refuses-assert?` takes the asserting context as a second argument.

- **A preserved claim's witness is the route that places the conclusion highest, so a
  firing over it no longer depends on which route arrived first.** A claim inherited over
  `transitiveInArg` names one path in the justification of every firing it feeds, and that
  path decides where the conclusion is placed. The path named was a shortest one:

  ```
  CxUniverse   (genl mid dog) (genl chi mid)      the long route
               (largerThan dog cat)  (transitiveInArg largerThan 1 genl)
               forward rule (largerThan ?x ?y) ⇒ (noted ?x ?y)
   └─ CxA      (genl chi dog)                     the short route
  ```

  A one-edge route stated in CxA beat a two-edge route stated in CxUniverse, so
  `(noted chi cat)` was stored in CxA — and whether CxUniverse held it as well came down
  to arrival order: the rule firing before the short edge arrived left a CxUniverse firing
  standing, and the short edge arriving first left none, which is the same knowledge
  giving two answers. The route chosen is now the one whose **most specific asserting
  context is the most general** available, with length breaking a tie between two routes at
  the same floor, so the conclusion is placed in CxUniverse in either order and every
  reader of either route holds it. `taxonomy/general-reach-support` is the walk for the two
  virtual relations and `inherit/fact-path` is its counterpart over a declared-transitive
  fact relation; both name the most general supporter per edge exactly as before, so what
  moved is which route is taken and not which supporter of an edge it names. The
  subsumption witness a match climbs and the `genlCx` sighting witness are unchanged: the
  first is asked per placement candidate and the second has one supporter per edge, and
  `lein bench-witness` measures 3,960 and 4,182 of them over the starter and the test world
  without one placing below a route another context has. *Class:* **Breaking** (a firing
  over an inherited claim is stored in a more general context than before). *Migration:*
  a caller reading such a conclusion out of the context the short route was stated in —
  `sentexes-matching` and `sentexes-in-context` are exact-context — reads it from the
  context the general route is stated in, or asks `ask` / `believed?` from its own context,
  which answered true before and answers true now. No reader loses a belief.
  [docs/inherit.md](docs/inherit.md), [docs/taxonomy.md](docs/taxonomy.md),
  [docs/nmtms.md](docs/nmtms.md)

  *Breaks:* `sentexes-matching`, `sentexes-in-context`

- **A membership question reads a term's types, not everything ever said about it.**
  `kb/types-of` — the retrieval `isa?` and every definitional check bottom out on, and one
  every unary assert makes — answered "what types does this term hold" by reading the
  term's whole argument-1 posting and fetching the record behind each to keep the arity-1
  ones. The argument root cannot narrow further: `(dog Muffet)` and `(likes Muffet Tom)`
  both put `Muffet` at argument 1, share the slot-roster entry and share the trie node
  below it. So an individual with n facts about it paid n record fetches on every assert
  of a type for it, to find the handful of types it holds — and with one separation
  anywhere in the KB, that is what opened the disjointness arm and made the read happen.
  Measured on a term holding 8x the binary facts, a `check` of one membership about it
  went from **5.57x to 1.43x**, and the retrieval itself from 9.31x and 0.41 ms/op to
  0.84x and 0.0008 ms/op. `lein perf`'s `membership-read-under-busy-term` is the gate:
  **0.74x** flat against a 2.0x bound, where the old read measures **4.77x** on the same
  workload.

  `IndexStore` grew one op for it, `unary-sentexes-with-arg`, answered off a new
  `[:unary-slot term]` roster holding the predicates a term is the lone argument of. The
  roster's members are predicates, so it is vocabulary-scaled beside the slot roster
  rather than a second copy of the postings, and it costs one `:add-to-set` per unary
  assert and no extra read (`assert_cost_test`'s `membership` and `deep-membership` slot
  budgets, 100 -> 200; `plain`'s are unmoved). It is a deliberate superset — written by
  every unary fact rather than reference-counted, since the count that reference-counts
  the other rosters is raised by binary facts of the same predicate too — and
  `types-of`'s existing arity and argument filters are what make the answer exact.
  `kv/index-layout-version` is **3**; an index written under 2 is repaired by `reindex`,
  which every store already runs on a layout change.

  *Class:* **Breaking**. *Migration:* an in-tree index needs nothing — both implementations
  ship here. An **out-of-tree `IndexStore`** adds `unary-sentexes-with-arg`, and a
  superset is a legal answer, so `(fn [store term] (sentexes-with-arg store 1 term))` is a
  complete and correct implementation: the caller filters by arity and by the argument on
  the records it reads anyway. An index that can narrow to arity-1 facts should, because
  this is the read a membership question makes on every assert. It is an op on
  `IndexStore` rather than an optional protocol beside it because every index can answer
  it and no caller branches on whether it does — a capability nothing tests for is not a
  capability, it is the same protocol with a second name.
  [docs/storage.md](docs/storage.md), [docs/indexing.md](docs/indexing.md)

  *Breaks:* `IndexStore`, `unary-sentexes-with-arg`

- **`KvBackend` names no index family, and the in-memory backend holds the argument roots
  as flat entries.** The predicate-scoped argument roots are the index's one hierarchical
  family — `pos → term → pred → handles` — and 0.20.0 read its subtrees through
  `ArgColumns`, a protocol beside `KvBackend` whose four methods named that family: a
  scoped leaf, the predicate-agnostic union at a `(pos, term)` node, that node's
  cardinality, and a multi-column narrowing. `IndexStore` already named all four reads —
  `sentexes-with-arg`, `count-with-arg`, `sentexes-with-args` and
  `unary-sentexes-with-arg` — so `KvIndexStore` answers them itself now over the eight
  generic ops: `kv-members` for a scoped leaf, `kv-intersect` for the narrowing, and a
  union over the `[:argument-slot pos term]` roster for the two agnostic reads
  (`roster-union` and `roster-tally`). The family's three key shapes sit in
  `vaelii.impl.kv` beside the families it already spells.

  The in-memory backend held the family under a reserved key as a counted
  `pos → term → pred` trie whose nodes carried a `:union` of the handles at each
  `(pos, term)` — a second copy of every argument posting, on the backend most KBs run
  on. The trie, its four folds, the op router, the transient twin's extra arm and twelve
  `arg-root-key?` branches are deleted: `MemoryKvBackend` is one map keyed by the
  structured vectors, its resident shape its portable one, and `memory.clj` is 233 lines
  shorter. The argument point-query memo, `kv/*arg-point-cache*`, is deleted too — nothing
  in the tree bound it but the bench that measured it — so the three hottest argument
  reads lose a dynamic-var deref and a branch each.

  No key shape moves here; `kv/index-layout-version` **3** is the membership entry's.

  *Class:* **Breaking**. *Migration:* an in-tree backend needs nothing, and an out-of-tree
  `KvBackend` needs nothing either — every op it implements is unchanged. `ArgColumns` no
  longer exists; a backend that implemented it deletes those bodies, since `KvIndexStore`
  does that reading over the generic ops now.
  [docs/storage.md](docs/storage.md), [docs/indexing.md](docs/indexing.md)

  *Breaks:* `ArgColumns`, `arg-scoped-members`, `arg-scoped-intersect`,
  `arg-agnostic-members`, `arg-agnostic-count`

- **`watch` refuses a conjunction in both its spellings.** A watch goal whose answer is
  not a function of the relabelled region is refused by name (`:not-watchable`), and the
  roster named a conjunction — but read only the vector one, `[(dog ?x) (cat ?x)]`. The
  same goal written with the connective, `(and (dog ?x) (cat ?x))`, registered: no stored
  sentence has `and` for a functor, so the subscription fired never and the caller had a
  live token and an empty feed to show for it. That is the silent-nothing the arm beside
  it refuses an `or` for, in the same words. The `(and …)` spelling is now refused
  wherever it appears in the goal, nested included, and the daemon's `:watch` refuses it
  identically, since the daemon's subscription runs `core/watch`.
  *Class:* **Refusal** (an `(and …)` watch goal, registered before, is refused).
  *Migration:* register one watch per conjunct and join their events, which is what the
  vector spelling has always been told to do; no working caller exists, since the
  registered watch delivered nothing.
  [docs/feed.md](docs/feed.md)

  *Breaks:* `watch`

- **One CLI argument is one form.** `read-arg` read each argv string with
  `edn/read-string`, which answers the first form and drops the rest — so `lein cli assert
  '(dog Muffet) (cat Felix)' CxWell` stored the dog, printed its handle and exited 0 with
  nothing said about the cat: a write that did less than the line asked for and reported
  success. A second form in one argument is now refused (`:bad-args`, carrying the command
  as its `:op` like the operand-count refusal beside it), and a string that
  reads as no form at all is still the path it already was, which is what `/var/lib/vaelii`
  is. *Class:* **Refusal** (a second form in one argument, dropped before, is refused).
  *Migration:* quote each argument separately, which is what the usage line already says;
  no working caller exists, since the dropped form never reached the KB.
  [docs/operations.md](docs/operations.md#cli--vaeliicli)

  *Breaks:* `lein cli`, `read-arg`

- **`lein cli export --format` takes `text` or nothing.** The arm tested for `text` and
  took the dump branch for every other value, so `--format yaml` — or `--format texr` —
  was **dropped**: the command wrote a records dump, printed the writer's summary and
  exited 0, which from the outside reads exactly like the text KB that was asked for. An
  operator scripting a nightly `export --format text` past a typo kept a dump where the
  premises should be, and found out when `load` was handed a directory it does not read.
  `--variant` and `--compression` were never droppable this way, because both reach the
  writer and the writer refuses an unknown one by name; `--format` is the flag the writer
  never sees. It is now refused in the driver, `{:type :unknown-option :mismatch
  :bad-value :flag "--format" :value f :takes ["text"]}`, before any KB is opened.
  *Class:* **Refusal** (an unknown `--format` value, accepted and dropped before, is
  refused). *Migration:* nothing — no working caller exists, since the flag never did what
  whoever passed it believed; a script that meant the dump writes no `--format` at all.
  [docs/operations.md](docs/operations.md#cli--vaeliicli)

  *Breaks:* `--format`

- **A relation can state that its arguments commute.** `symmetric` said it of the two
  arguments of a binary predicate and nothing else, so a variable-arity relation whose
  arguments are unordered could not be stated at all. Three marks say it at any arity:

  ```clojure
  (commutative P)                    ; every argument, at each arity P is applied at
  (commutativeInArgs P 1 2)          ; exactly the named positions; the rest stay put
  (commutativeInArgAndRest P 2)      ; position 2 through the application's own end
  ```

  Every permitted permutation of a ground fact stores as **one sentex and one handle**,
  so queries, rule matching, context visibility and retraction all follow from the
  sentence being stored once. `(covering Engine Piston Rod Valve)` answers a goal naming
  the parts in any order, off the one stored row. A tail is closed by the literal's own
  arity, so `(covering W A B)` and `(covering W A B C)` stay two claims and no
  permutation moves an argument between them; repeats keep their multiplicity;
  overlapping marks merge into one component rather than applying in sequence, which
  would make the stored form depend on which was applied first. A declaration arriving
  after the facts re-spells what is already stored, as a late `symmetric` does.

  Each of the three installs its permutation group at its own arm, so no spelling is
  derived from another and the canonicalizer reads one table whichever was written. The
  equivalence between `(commutative P)` and `(commutativeInArgAndRest P 1)` stays in
  CxCore as two `set/inertRule`s, believed and queryable but run by neither engine.
  `(genl symmetric commutative)` classifies, and `(commutative P)` with `(arity P 2)`
  concludes `(symmetric P)` — commutativity at two arguments is symmetry, where
  commutativity at any other arity implies neither symmetry nor arity 2 — as a
  `set/forwardOnlyRule`.

  Those three directions are what the vocabulary costs a backward search. `set/forwardRule`
  adds forward chaining **without** taking the backward use away, so written that way each
  of the three answers goals as well; and each concludes a mark another of them needs —
  the equivalence directly, the arity bridge because `(genl symmetric commutative)` makes
  its conclusion a spec of `commutative`, which `provers/candidate-rules` offers as a
  candidate for the supertype goal its own antecedent poses. No ancestor-goal guard stops
  the descent, the depth bound turns the cycle into an exponential frontier rather than a
  refusal, and `(genl commutative relation)` puts `(commutative ?p)` under every open
  `(relation ?x)` query. Any KB that loaded CxCore and read through the inference engine
  stalled, whether or not it asked about commutativity.
  A late mark also re-joins the forward rules over `P` and the predicates above it
  (`chain/permuting-rejoin-rules`) and moves the preserved predicates above `P`
  (`inherit/moved-predicates`), so a rule reading a permuted fact fires whichever arrived
  last. A bulk load keeps its dedup probe for a commuting relation, as it does for a
  symmetric one, so a permutation of a stored row is not stored a second time; and the
  rete alpha matcher (`VAELII_RETE=1`) fans a commuting literal's arrangements as the
  default retrieval path does.
  *Class:* **Additive**.
  [#55](https://github.com/vaelii/vaelii/issues/55),
  [docs/canonicalization.md](docs/canonicalization.md)

- **Named subtypes can state that they exhaust their parent.** Two independent claims
  about a named roster of parts, and three spellings that make them: `(covering Whole
  Part1 Part2 …)` says every instance of the whole is an instance of at least one named
  part, `(separating Whole Part1 Part2 …)` says no two parts share an instance, and
  `(partition Whole Part1 Part2 …)` says both. `separating` is the roster-shaped spelling
  of what `disjoint_metatype` and `sibling_disjoint` say about a metatype's members and a
  parent's every specialization — the same separation over a named few, with no metatype
  term to invent. All three are variable-arity with the whole in position 1 and a
  commuting part roster, so a roster written in another order is one sentex. A cover *states* the specialization it rests on:
  the integrate arm installs a `genl` edge per part against the covering sentex's own
  handle, so a cover asserted before its parts answers what one asserted after them does,
  and retracting it drops the edges with it. A partition's roster is recorded the way a
  `disjoint_metatype`'s member set is — consulted by `disjointness-test`, never written
  out as a `(disjoint …)` sentex per pair — so `siblingDisjointException` exempts a pair
  of parts exactly as it exempts a pair of metatype members. `disjoint_metatype` keeps its
  own meaning and claims no coverage. Coverage is actionable on explicit negation alone:
  for an n-part cover, n−1 believed `(not (Part X))` prove the nth, and a whole instance
  with no part known stays unknown rather than being assigned one. Denying *every* part
  of a cover a term holds the whole of is a contradiction, refused as `:cover` and
  arbitrated like any other definitional clash.
  A cover's cycle check reads the global closure, as `genl-problems` does, so a part a
  sibling context places above the whole is refused rather than closing a two-type cycle
  in the global closure; the disjointness check stays scoped to the asserting context.
  The parts of a `partition` or `separating` roster are separated for every reader: the
  emptiness gate every disjointness pass sits behind (`settle/separations?`), the
  clash-vocabulary fingerprint and `taxonomy/disjointness-witnesses` all read the roster
  (`taxonomy/separating-covers`), so under `:constraints :arbitrate` a pair stored across
  a cover is reported and weighed as one across `(disjoint A B)` is.
  *Class:* **Additive**.
  [docs/taxonomy.md](docs/taxonomy.md)

- **`interArgs` and `interArgAndRest` refuse an application that mixes a type with
  arguments outside it.** `(interArgs R T)` demands a `T` of every argument of an `R`
  application once one argument is known to be a `T`; `(interArgAndRest R n T)` makes the
  same demand of positions `n` onward and leaves the earlier positions free. `interArgs`
  is `interArgAndRest` at start 1, and CxCore's two forward rules derive each spelling from
  the other. The refusal is `interArg`'s `:inter-arg-type`: the forms convict as
  `interArg` does and do not entail, so an untyped argument is neither convicted nor given
  a type. A declaration on a super-predicate binds a sub-predicate's tuples, and
  `ask` answers a declaration at its stated type and start. A zero or negative start is
  refused `:not-well-formed`. `inter_args_test` covers the forms at two, three and five
  arguments. [argtypes.md](docs/argtypes.md#suffix-homogeneity-interargs-and-interargandrest)
  *Class:* **Additive**. *Migration:* none.

- **A remote refusal carries the HTTP status it came back under.** `vaelii.client` read
  the daemon's reply body and dropped the status line, so the coarse
  client-fault/server-fault split that `docs/operations.md` puts under the one `:type`
  vocabulary was a fact only a caller writing its own HTTP could read — a `:type` outside
  the daemon's request-refusal roster is answered 500 and reached this client looking
  exactly like one answered 400. The reply that has no `:type` at all was worse: a
  proxy's error page in place of the daemon is `:bad-reply`, the case `read-reply` was
  written for, and a 502 from a dead upstream was indistinguishable from a truncated 200
  off the daemon itself. `call`'s `ex-info` now carries `:status`, and so does
  `:bad-reply` from either entry point. *Class:* **Additive**.
  [docs/operations.md](docs/operations.md#client--vaeliiclient)

- **`describe` answers what a term was declared, beside the closures that follow from
  it.** `:genls-direct` and `:specs-direct` are the one-step `genl` edges — the parents
  and children, not reflexive — and `:disjoint-maximal` is the types a separation was
  declared between. The difference is the reason: `dog` reaches seven supertypes and was
  told one, `thing`'s subtype closure is 110,128 names on an imported ontology, and one
  collection in the OpenCyc import is disjoint from 79,638 types and separated from 43 of
  them. `:genls`, `:specs` and `:disjoint` are unchanged and are still what a subsumption
  or membership check reads. `:disjoint` now reads `tax/separating-partners`, the
  enumeration `disjoint?` is the membership test of, rather than two pattern reads per
  supertype: `describe` on `dog` went from 7.75 ms to 2.10 ms, and `:disjoint` gains the
  separations a `(sibling_disjoint C)` parent induces, which store no pair for a probe to
  find. *Class:* **Additive**.
  [docs/api.md](docs/api.md), [docs/web.md](docs/web.md)

- **A minted argument type can give way to the membership that says it more specifically
  (`VAELII_PRUNE_SUBSUMED_MINTS=1`, off).** `(arg parentOf 1 animal)` over
  `(parentOf Fred Mary)` mints `(animal Fred)`, and a KB that also believes `(dog Fred)`
  stores the same claim twice — once as a record nobody wrote and once as the membership
  an author did. With the switch on, the general one is withheld while the specific one is
  believed: withheld before the record is written where the membership arrived first, and
  blocked and swept where it arrived last, so both arrival orders leave the same KB. It
  comes back when the membership that displaced it is retracted, swept or defeated.
  Answers are untouched — subsumption reaches `animal` from `dog` with or without a record
  between them — and storage shrinks: CxCore holds 1,256 sentexes against 1,544 and the
  starter 3,702 against 4,142. Off by default for what it costs rather than for what it does: every settle that
  moves a membership asks what that membership displaces, measured at +42% on a
  settle-dense qualitative workload.
  *Class:* **Additive** (the default reading stores every mint, as before).
  [docs/argtypes.md](docs/argtypes.md), [docs/exceptions.md](docs/exceptions.md)

- **A term page reads from what the term is to what uses it, in one fixed group order.**
  "Argument position 1", 2, … N; then "Rule conclusion" and "Rule condition" (two groups
  where "In rules" was one, because a rule's two halves say different things); then
  "Nested elsewhere"; then "Predicate extent" and "Context extent". The page opened on the
  functor extent, so `dog` began with every instance ever asserted and the sentences that
  *declare* it — its comment, its `genl` edge, its argument constraints — sat below them.
  The two extents are ordered **largest-last**, the one place size decides rather than
  directness: the bottom of the page is where a list goes on loading as a reader scrolls,
  so an extent of millions there is a list they walk into, where the same list above a
  short one is a wall to get past. Inside a group the term's own `(comment …)` sorts
  first: it is part of the sort key rather than a row lifted out, because paging
  re-slices that sequence at an offset. The headings drop their prepositions, and the
  `[edit]` beside a heading opens on the declarations rather than the extent.
  *Class:* **Additive**. [docs/web.md](docs/web.md)

- **A term page can leave out what the engine concluded.** **hide derived**, beside the
  "Sentexes by index" heading, lists only what the KB was told — on a settled ontology
  most of a term's rows are conclusions drawn from a handful of premises. One query
  parameter, one cookie (persistent, so the choice carries to the next term) and a
  re-render: no script and no per-row state. No belief moves and no count changes; the
  heading still says how many sentexes are stored in the group, and the discriminant is
  the one the badge already draws a ring for — a `:strength` on the record — so a row the
  reader sees as derived is a row the filter leaves out. The filter walks at most
  `derived-scan` (5,000) records per page, and an offset indexes the group's records
  rather than the rows that survived, so a reader who toggles part way down a list
  neither sees a row twice nor steps over one. *Class:* **Additive**.
  [docs/web.md](docs/web.md)

- **A rule renders across lines, one antecedent literal to a line, on the page and in the
  editor.**

  ```
  (implies (and (weightOf ?x ?wx)
                (weightOf ?y ?wy)
                (quantityGreaterThan ?wx ?wy))
           (heavierThan ?x ?y))
  ```

  A rule read as one line is a rule read by counting parentheses: which literals are the
  conditions and which one is the conclusion is what a single line runs together. The
  indent is counted in characters, which is exact because a sentence is set in the
  monospace face and the span holding the newlines is `white-space: pre-wrap`. A sentex
  row is a circle and a sentence, and the sentence is its own block, so every line after
  the first starts under `(implies` rather than under the badge, and the context and
  `[edit]` no longer ride up beside the first line; the badge's reading is its `title`.
  The editor opens a rule the same way, aligned through the `(set/backwardRule …)`
  wrapper that carries its direction. The whitespace is not read back — the editor reads
  EDN forms and the save diffs by content — so the sentence reaching the KB is the one
  that was there. *Class:* **Additive**. [docs/web.md](docs/web.md)

- **A term page shows where a term sits rather than restating it.** The three prose lines
  it opened with — Supertypes, Subtypes, Disjoint with — are gone. A supertype line
  rendered `genl` sentexes the argument groups already list, so the page said twice what
  it says once; the one reading of a taxonomy those rows cannot give is position, and that
  is what the concept graph above them draws. On an imported ontology the lines were also
  the largest thing on the page: `thing` has 110,128 subtypes there and one collection is
  disjoint from 79,638 types. `vaelii.core/describe` still answers all six readings — the
  three closures and the three declarations — for a caller that wants them.
  *Class:* **Additive**.
  [docs/web.md](docs/web.md)

- **A concept-graph node is a box.** The nodes were pills — fully rounded ends — which
  ate the width a long term name needs and let two adjacent nodes read as one capsule.
  They are rectangles with a 3px corner (`.g-box`), same colours, same layout arithmetic.
  *Class:* **Additive**.
  [docs/web.md](docs/web.md)

- **A definitional verdict is let go when its grounds are defeated.** Denying the
  separation, the functionality or the `genl` edge a clash convicted through left the loser
  JTMS-OUT for as long as both records stood, with `disjoint?` answering false, the
  taxonomy's `:disjoint` empty, `contradictions` empty and `why-not` reporting
  `:reason :defeated` with an empty `:contradicted-by` — a verdict no reader could account
  for:

  ```clojure
  (v/assert kb '(disjoint dog_t cat_t) 'CxUniverse)                        ; :default
  (v/assert kb '(cat_t Muffet) 'CxUniverse)
  (v/assert kb '(dog_t Muffet) 'CxUniverse {:strength :monotonic})         ; decides the pair
  (v/assert kb '(not (disjoint dog_t cat_t)) 'CxUniverse {:strength :monotonic})
  (v/ask? kb '(cat_t Muffet) 'CxUniverse)   ; => false, and the separation is gone
  ```

  Both defeats were taken in one resolution round: the declaration lost to the denial and
  the membership lost to the declaration, so the membership was convicted on content the
  same round disbelieved. `jtms/clear-defeats!` re-believes the declaration at the top of
  every settle, which is why the verdict was re-taken rather than merely stale. A round now
  applies a defeat that **withdraws grounds** before, and apart from, the verdicts resting
  on them — the generalization of the rule that already took a scoped defeat first and
  alone — and re-entering puts `reads-clash?` in front of every other verdict.
  `tax/derives-from?` is the reading: does this handle assert an edge of a cached relation
  or a flat-cache entry, in three O(1) lookups off the reverse indexes the belief reconcile
  already walks. The loser revives whether the pair had been decided or was still a
  dilemma; retracting the declaration, which always worked, is unchanged. *Class:* **Fix**.

- **A definitional clash is decided on the hierarchy the deciding vantage reads.** A
  settle empties the scoped defeats before it discovers, so its discovery reads the
  relation as the KB holds it globally, and the verdict it took could rest on a separation
  no context could read back:

  ```
  CxUniverse   (genl chi thing) (genl dog thing) (genl cat thing)  (disjoint dog cat)
   └─ CxA      (genl chi dog)                 :default
        └─ CxB (not (genl chi dog))           :monotonic   ← the vantage
               (chi Kit)  (cat Kit)
  ```

  From CxB, `chi` is not a `dog`, so the two memberships of `Kit` clash with nothing, and
  no other context holds both. `(chi Kit)` was defeated anyway — in the network, since the
  vantage is its own context — for violating a separation CxB reads as absent, that
  `contradictions` did not report and `why-not` could not name; with both memberships
  defeasible the pair stayed believed and `contradictions` reported it, from a reader whose
  own `disjoint?` answered false. The resolution decides on the vantage's own reading now:
  a scoped defeat is applied before a global one and alone, since it changes what a vantage
  *reads* rather than what the network holds, and from the second round on each
  definitional nogood is re-asked at each of its vantages through the entry point the
  discovery asked (`checks/arbitrable-violations`). A vantage that no longer reads the
  clash decides nothing. The first round is the one the discovery ran for, so a settle that
  resolves in one round re-asks nothing. *Class:* **Fix**. *Migration:* none for the
  shipped ontology, which denies no taxonomy edge. A KB that denies one below the context
  stating it reads differently at and below that vantage: a membership convicted through
  the denied edge is believed there, and a clash that vantage cannot read is reported to
  no reader. The entry point is
  unchanged and still reads the KB the sentence is written into: `(chi Kit)` offered while
  `(cat Kit)` is known-true and the denial is not yet written is refused, and offered again
  after the denial it is stored — one arrival order of the twelve measured, with belief the
  same in the other eleven.

- **A context that disbelieves a `genl` or `genlCx` edge stops reaching over it.** A
  scoped defeat withdrew a supporter from the network's reading of belief and from every
  belief-filtered read that asks `res/hidden-fn` — and not from the taxonomy's closures,
  which asked a predicate that reads the JTMS label and the `except` roster alone:

  ```
  CxUniverse   (genl chi thing) (genl dog thing) (chi Rex)
               (transitiveInArg largerThan 1 genl)  (largerThan dog cat)
   └─ CxA      (genl chi dog)                 :default
        └─ CxB (not (genl chi dog))           :monotonic   ← the vantage
  ```

  From CxB, `believed?` of the edge answered false while `ask?` of `(genl chi dog)`,
  `genl? chi dog`, `isa? Rex dog` and the preserved `(largerThan chi cat)` all answered
  true — two halves of the engine disagreeing about one KB from one context, which is the
  disagreement `res/believed-at?` exists to prevent. A scoped-defeated supporter is IN in
  the network by construction, and with no `except` stored the whole-KB gate in
  `res/supporter-believed?` short-circuited before the context-sensitive read, so the
  filtered walk ran and could not see the defeat. It applies both withdrawal kinds now,
  and all five reads answer false from CxB, true from CxA, and unchanged from a sibling
  that sees neither the denial nor the vantage. The `genlCx` twin goes with it: a context
  that disbelieves an edge above it stops inheriting from what the edge reached. The
  recursion that shape invites does not close, because every ancestor-set read inside the
  withdrawal answer takes `tax/context-up-global` and the region walk reads
  justifications alone. `relation-filter-active?` stays the gate in front of it, so a KB
  with neither roster reaching the relation being read pays nothing.
  `res/clear-withdrawn!` also moves the supporter-visibility generation when the settle
  that calls it has already emptied the roster, as a lift of the last scoped defeat
  leaves it: the scoped closures are memoized under a key carrying that generation.
  *Class:* **Fix**. *Migration:* none for the shipped ontology, which holds no scoped
  defeat. A KB whose own content denies a taxonomy edge below the context that states it
  reads differently at and below that vantage: denying `(genl penguin bird)` there takes
  `genls penguin` to `(penguin)` and `isa? Tweety thing` to false, where both answered
  over the denied edge before. Every other reader is unmoved — measured over all 163
  specs of `thing`, `isa?` across 400 types, and `context-up`, from three readers outside
  the vantage, with one unrelated scoped defeat standing.

- **A defeated witness edge re-derives a forward firing over a second route, at every
  reader that still reaches.** A forward firing names one path per reachability it rests
  on — the `genl` path a subsumed match climbed, the route a claim preserved over `genl`
  or a fact relation took, the `genlCx` path its placement is seen over. A retraction of
  an edge on that path re-joins the facts under it, so a second route re-derives the
  conclusion. A defeat swept nothing and started no re-join, and a scoped defeat or an
  `except` withdrew the firing from the readers at and below it while the edge stayed
  believed in the network. So belief turned on arrival order: with
  `(genl dog mammal) (genl mammal animal)` in CxUniverse, `(genl dog animal)` in CxA,
  `(dog Fido)` and a forward rule `(animal ?x) ⇒ (alive ?x)`, a monotonic
  `(not (genl dog mammal))` — in CxUniverse, or in CxA as a scoped defeat — left
  `(alive Fido)` false at CxA in one arrival order and true in another. The settle now
  re-joins the facts under a `genl` or `genlCx` edge that lost belief with a firing
  resting on it, and re-derives a firing a scoped defeat or `except` withdrew at each
  reader that still reaches, asking every witness search from that reader; a firing's
  placement path is searched from the placement's own view, so an edge excepted there is
  not named when another path reaches. A firing re-derived for a reader stays stored
  after the defeat lifts. `lein perf` gains `lost-firing-scan`, which bounds the
  per-settle scan while a scoped defeat stands.
  *Class:* **Fix** (a conclusion's belief depended on arrival order).
  [docs/nmtms.md](docs/nmtms.md)

- **A route stated in a sibling context places its own forward firing.** A preserved claim
  reached over two routes stated in contexts neither of which sees the other named one
  route, so the other sibling read the conclusion only in the orders where the rule fired
  over its route first: a claim in CxA with a route in CxA and a shorter one in CxB held in
  CxA in 6 of 24 orders. The witness searches now return every route that no other route
  covers, and the join fires once per route, for a `genl` route, a fact-relation route, one
  edge or one declaration or one `(transitive R)` or one claim stated in two siblings, and a subsumed match whose
  placement descends below the rule and the facts. Every order now yields the same belief
  at every reader. `second_route_test` gains sibling lattices crossed with its four knocks
  and an every-order test per shape. [inherit.md](docs/inherit.md#forward-chaining-on-a-claim-nobody-stored),
  [nmtms.md](docs/nmtms.md#where-the-layer-stops),
  [defenses.md](docs/defenses.md#routes-in-sibling-contexts-each-carry-a-firing).
  *Class:* **Fix** (belief at a sibling context depended on the order its routes arrived in).

- **A derivation refused for a type that had not arrived yet is placed when it arrives.**
  An argument constraint convicts a rule conclusion when the argument's types have no path
  to the declared one, and a declaration mints nothing while its type has no path to
  `thing`. Both read the taxonomy as it stood, so the missing `genl` edge or membership
  arriving later changed nothing: the conclusion, the decontextualized copy or the mint
  was lost for good. Loading the shipped starter in shuffled orders lost between 2 and 93
  conclusions per order (`(arg1 asleep animal)`, `(genl instance_relation_predicate
  predicate)` and the like), none of them answered by `ask`. Each is now kept in the
  refusal record and re-asked by the settle that can have supplied the type; the ledger
  entry its drop filed is withdrawn once it is placed. Fifty shuffled starter loads now
  hold the sentexes the shipped order holds.
  A firing dropped on a constraint that convicts several arguments waits on whichever
  argument the conviction names at each re-ask, where it had kept watching the first:
  under `(interArgs rel animal)`, or two `interArg` declarations with different targets,
  typing `P` and then `Q` as animals left `(rel A P Q)` dropped and the reverse order
  placed it. A lifted `decontextualized_predicate` copy waiting on a conviction does the
  same, and `inter_args_test` runs both lifting orders for both declaration shapes.
  *Class:* **Fix** (belief depended on arrival order).
  [docs/exceptions.md](docs/exceptions.md)

- **A `genl` edge an argument declaration mints fires the rules it connects.**
  `(genlArg kindUnder 1 animal)` over `(kindUnder wolf Zoo)` mints `(genl wolf animal)`,
  and a stored `(wolf Rex)` then matches a forward rule on `(animal ?x)`. The mint went on
  the agenda as a datum, which fires the rules keyed on `genl`, and never through
  `subsumption-seeds`, which re-joins the facts under an arriving edge. So the rule fired
  only where the mint arrived before the member and the rule: 72 of the 120 orders of the
  five ingredients derived nothing. Every mint is now seeded as an asserted edge is, on
  `assert`, on a rule conclusion and on the settle that releases a waiting declaration.
  The shipped CxCore also states `(at_least_metatype metatype)` and
  `(at_least_metatype meta_metatype)`, which `(arg typeGenl 1 at_least_metatype)` had
  only minted, so under `VAELII_ASSERTIVE_ARG_TYPES=0` the starter no longer fails its own
  declarations.
  *Class:* **Fix** (belief depended on arrival order).
  [docs/argtypes.md](docs/argtypes.md)

- **A relation property reads the same from every path, in either arrival order.** Two
  defects, one per reading. A `(symmetric P)` or commutativity mark stated in one context
  was read globally by the store, which keys a sentex once for every context, and from
  the stating context by `has-prop?`, the symmetric prover and the supporter an inherited
  mirror names; on a KB without CxCore, which declares no lift, a sibling read the mirror
  through the store and denied it through the rest. The engine now lifts the four
  permuting marks into CxUniverse on every KB. And a `(functional P)` or
  `(anti_symmetric P)` stated in a theory after `P`'s facts merged them below that theory
  alone, where stated before them it merged at CxUniverse: the lifted copy of a mark now
  runs the merges the assert entry point runs (`special/copy-merges`). `inherit_test`,
  `second_route_test` and `relation_properties_test` each gain the sibling case.
  [contexts.md](docs/contexts.md#where-a-relation-property-is-read-from).
  *Class:* **Fix** (a merge depended on whether its mark arrived before the facts, and a
  permuting mark answered two ways from one context).

- **A forward firing made over a fact's mirror goes with the mark that licensed it.** A
  rule whose antecedent the join, the trigger or a rete run satisfied by reading a stored
  fact in another argument order recorded the fact and the rule and nothing else, so
  `(noted Bb Aa)` fired over `(pr Aa Bb)` under `(symmetric pr)` stayed believed after the
  mark was retracted, where a KB that never held the mark never derived it. The firing now
  names the mark statements that license the rearrangement, one justification per minimal
  set of them, so a fact under both `symmetric` and `commutative` keeps the firing until
  both go. `order_independence_test` gains the case per permuting mark and the two-mark
  case, and `second_route_test` reads the plain firing beside the inherited one.
  [inference.md](docs/inference.md#forward-chaining).
  *Class:* **Fix** (belief depended on whether a mark had once been stated).

- **Every `genlCx` edge and every `forced_decontextualized_predicate` fact is stored in
  CxUniverse, whatever arrived first.** The declaration sets the storage context of each
  `(P …)` asserted after it, and one asserted before it stayed where it was written,
  drawing the `(context …)` entailments a fact there draws. `core-context/load-into`
  asserted the bootstrap `(genlCx CxUniverse CxCore)` before reading the file that
  declares `genlCx` decontextualized, so that one edge stayed in CxCore, and asserting it
  again — a second `load-text!` of an exported KB, or a caller writing it — stored a
  second sentex in CxUniverse. `load-text!` puts the context topology first, so every
  `genlCx` edge a text load read landed ahead of the declaration the same way. The loader
  now asserts the declaration ahead of the edge, and a declaration re-asserts each
  earlier premise in CxUniverse at its strength and retracts the original. CxCore and the
  starter each hold two sentexes fewer, and the same count from the shipped loader, from
  text and in shuffled orders alike.
  *Class:* **Fix** (storage depended on arrival order).
  [docs/contexts.md](docs/contexts.md)

- **An open query under the node engine converges on a rule graph containing a cycle.**
  A node is a conjunction of literals, and `children` rewrites one literal through one
  rule by splicing the rule's antecedents in where that literal stood. The splice kept a
  conjunct the conjunction already held. Conjunction is idempotent, so `A ∧ B ∧ B` and
  `A ∧ B` are one question under two `node-key`s, and the claimed-key set could not
  recognize the state as one it had already expanded: each turn of the cycle added a
  conjunct instead of returning to a claimed key. A repeat now collapses onto the first
  copy, which takes the largest depth of the copies folded onto it, so no rewrite a copy
  admitted is refused; the rewrite window reopens at the position a copy folded onto,
  which is what makes that depth reachable. `(relation ?x)` over CxCore with three bridge
  rules chaining forward expanded 192,971 nodes at depth 5 and did not finish depth 6
  within 411 s; the same query expands 710 nodes and 1,843, and completes at depth 8 —
  the bound the suite runs under — in 11,446 nodes and 4.1 s. The answers are the same
  121 at every depth. *Class:* **Fix**.
  [docs/inference.md](docs/inference.md)

- **`assert-rule` takes `{:direction :both}`.** It wrapped the sentence in the direction's
  `set/*Rule` wrapper and handed `assert` the same opt, which read `:both` against the
  `:forward` wrapper as two conflicting statements and refused `:unknown-option`. The opt
  now reaches `assert` through the wrapper alone, so `:both` stores the rule `:forward`
  stores, as the docstring and [inference.md](docs/inference.md) state.
  *Class:* **Fix** (a documented option refused).

- **An arity declared after its facts reports the same facts in every order.** The
  retroactive sweep's `:arity` violation named the first disagreeing fact and a sample of
  three in the order the functor's postings returned them, which is the order they were
  asserted: four facts forward and reversed named `(arpq Dd Ee Ff)` and `(arpq Gg Hh Ii)`.
  The convicted facts are now ordered by sentence and context before the entry takes its
  sentence and sample. `order_independence_test` gains the case over every order.
  *Class:* **Fix** (a violation report depended on arrival order).

- **A model's prompt lists two argument declarations on one position in content order.**
  The whole-KB predicate section and the selection card sorted `[position type]` pairs by
  position alone, so two `arg` declarations on one position kept the order the index
  returned them in. They now sort on the whole pair.
  *Class:* **Fix** (prompt text depended on arrival order).

- **The exposure sweep budget is 8192.** `tax/*exposure-instance-budget*` bounds a sweep
  against a large extent, and 4096 was not doing that: the shipped ontology plus a
  200-fact generated corpus exhausted it with the threshold measured between 4096 and
  4224, so any three terms added to `CxCore` cut five triggers short and left the
  clashes they implicate unreported for that settle. Which sweeps the cap refuses is
  unchanged, and so is every KB that never came near it. *Class:* **Fix**.
  [docs/nmtms.md](docs/nmtms.md)

- **koinii's stale sweep ages a derived dispute from its premises.** `sweep-stale`
  flags a dispute that has stayed live past `*timeout-ms*`, counting from the latest
  `:created` stamp on its sides. A side a rule derived carries no provenance, so an
  emergent clash — two rules concluding `S` and `¬S` from facts each agent stated —
  read as stamped at 0 and went `:stale` at the first tick, however recent. The age now
  counts from the latest stamp across the sides and everything they rest on.
  *Class:* **Fix** (a fresh dispute reported as timed out).
  [docs/koinii.md](docs/koinii.md)

- **A `genl` edge re-joins only the rules whose preserved claims can cross it.** Every
  `transitiveInArg` declaration may preserve along `genl`, and an arriving `genl` edge, or
  its denial, re-joined in full the forward rules on every one of them, whatever the
  edge's terms were. K denials over K preserved predicates cost K² re-joins: 25 s at
  K = 200. An edge now moves a predicate only when a claim on it or on a sub-predicate,
  in either polarity, has its preserved argument below the edge's lower term or above
  its upper one (`inherit/crossing-claim?`), read at every position the claim's own
  `symmetric`, `commutative`, `commutativeInArgs` or `commutativeInArgAndRest` mark lets
  it hold that argument at. An edge whose closure holds more than
  `inherit/crossing-closure-cap` terms (512) is not narrowed and moves every predicate
  preserved along `genl`. The reads start from the closure's terms, one slot-roster read
  each per preserved position, so what an edge reads does not grow with the
  declarations: the selection for one denial costs 0.01 ms at K = 64 and at K = 2,048,
  and an edge over 20,000 subtypes arrives in 30 ms. That corpus now takes 2.0 s, with 6
  re-joins per denial at every K. The re-join check reads the `:preserving` roster
  instead of two cardinality reads per datum, so `assert_cost_test` and
  `firing_cost_test` re-pin their `:functor-root` budgets down by 2 to 8 reads per assert,
  and `assert_cost_test` gains `:preserved-edges-4` and `:preserved-edges-32`, one budget
  for both. `lein perf` gains `genl-defeat-rejoin`, `genl-crossing-many` and
  `genl-crossing-wide`.
  Recover's first settle does not narrow at all: its region holds every stored sentex, so
  the extents a moved predicate adds are already in it, and asking
  `inherit/moved-predicates` of each stored sentex per defeat round took a cold recover
  of a 12.4M-sentex store past four hours. Elsewhere an edge is narrowed only where the
  answer changes what its reader does — the chainer's re-join when a predicate the edge
  would move carries a forward rule, the settle when one has a stored claim and is not
  already moved by another member of its region — and the settle's pass stops once every
  declared predicate is moved. A recover over 40,000 leaves under a 300-deep `genl` chain
  takes 0.94 s where it took 8.3 s. `moved_predicates_test` gains the case, and the
  `preserved-edges` pair re-pins `:functor-root` +100 and `:rule-index` +200, the one read
  each check makes before it stops.
  *Class:* **Fix** (a cost that grew with the square of the preserved predicates).
  [docs/inherit.md](docs/inherit.md)

- **`store-backend` names a store an adapter wrote, so the daemon and the CLI open it.**
  `lein serve <dir>` and `lein cli --dir <dir>` open the backend `store-backend` names,
  and a new `:disk-log` store when it names none. It named only the three disk layouts,
  so a directory an `:sqlite` KB wrote read as empty: the daemon served nothing, and
  every write landed in a second store beside the untouched `records.sqlite`. A
  `:pg-disk-log` directory (a local index over records on a server) read the same way,
  and opening it as `:disk-log` rebuilt its index in place from zero records. It now
  answers `:sqlite` and `:pg-disk-log`, and the open that follows is the adapter's, or
  the refusal `open-kb` gives without one (`:missing-adapter`, or `:missing-companion`
  for a `:pg-disk-log` with no `:pg`).
  *Class:* **Fix** (a directory read as holding no store).
  [docs/api.md](docs/api.md)

- **The CLI's stdout carries the answer and nothing else.** `err!` kept refusals on
  stderr, and the engine's own log lines went to stdout beside the data: the engine logs
  through Trove's console backend, which prints to `*out*`, and with the dial unset
  nothing is installed and Trove's own backend is in effect at `:info`. So with no
  variable set at all, `export` put its `::exported` line, and a `--starter` load its two
  `::dropped-conclusion` warnings, inside the value a script redirects — thirteen of the
  130 invocations in a full sweep of the command table. `-main` installs a wrapper over
  `taoensso.trove/*log-fn*` that writes the engine's lines to stderr for the CLI process:
  `alter-var-root` rather than a `binding`, since the durable store's compaction line
  comes off the durability scheduler's own thread. Same lines, same levels, other stream.
  The daemon and the browser keep theirs where they are, neither writing data to stdout.
  In the same change, `--depth` and `--nearest` refuse a non-numeric value by name
  (`--depth takes a whole number, given "twice"`) rather than reporting
  `Long/parseLong`'s `For input string: "twice"`, which named neither the flag nor the
  command. [docs/operations.md](docs/operations.md#logging--a-dial-and-what-is-behind-it)

  *Class:* **Fix**.

- **A blank operator switch outside `vaelii.impl.config` is unset, and an impossible
  browser port falls through.** `docs/operations.md` holds every switch to "blank is
  unset", and four readers took the empty string as a value:
  `VAELII_MAX_BODY_BYTES=` refused `vaelii.host.guard`'s load, so neither server nor the
  browser started; `-Dvaelii.disk.dir=` put every derived disk store at `/space-<n>`, the
  filesystem root; `vaelii.build` / `VAELII_BUILD` stamped a dump's writer `"vaelii "`.
  `VAELII_WEB_PORT=99999999999` threw `ArithmeticException` out of the browser's start,
  and `70000` or `-5` reached Jetty; a number outside 0–65535 now falls through to the
  property, as an unparseable one does. The body-ceiling refusal carries `:switch`, as
  `config`'s do.
  *Class:* **Fix** (switch values the doc reads as unset).
  [docs/operations.md](docs/operations.md)

- **A cache scale past the range of a long no longer stops every query.** A counted
  cache's bound is its shipped default times the scale, converted to a long on every
  cache store, and `(long ##Inf)` throws. `set-cache-scale` admits any number 0 or more,
  so `##Inf`, or `1e300`, or `VAELII_CACHE_SCALE=Infinity`, or the browser's
  `POST /caches/scale` with `scale=Infinity`, left every query in the process throwing
  `IllegalArgumentException: Value out of range for long` until the scale was set back,
  and the cache rows reporting an error in place of a bound. The bound now saturates at
  `Long/MAX_VALUE`.
  *Class:* **Fix** (a scale the refusal admits).
  [docs/caches.md](docs/caches.md)

- **Every proposal turn carries a token cap again, sized to what the backend spends its
  tokens on.** The cap is the panel's runaway guard — two of eight models measured
  degenerate into runaway generation, one writing 8138 lines over 474 seconds, and a
  wall-clock timeout does not stop a host that is still generating — and it had been
  narrowed to Ollama, which left every other backend sending a turn with no cap at all.
  It rides on every turn once more, sized per backend: 2048 for a local turn, whose
  tokens all go into what it writes, and 16000 for an API turn, which reasons against the
  same ceiling before its first assertion and would truncate at a writing budget.
  *Class:* **Fix**.
  [docs/web.md](docs/web.md), [docs/llm.md](docs/llm.md)

- **The standalone jar carries every dependency's licence and notice.** `lein uberjar`
  keeps the first jar's entry at a path and drops the rest silently, and many
  dependencies put their text at the same `META-INF/LICENSE` or `META-INF/NOTICE`: the
  jar the Docker image ships had lost commons-codec's, both Jackson dataformats', JNA's
  and both SLF4J jars'. The `:uberjar` profile now merges those paths, concatenating the
  distinct texts. The library jar was unaffected; it bundles no dependency.
  *Class:* **Fix** (build; the standalone jar's contents).
  [project.clj](project.clj)

- **`/kbs` draws a KB loaded from a dump.** The loaded-KB card counts what a load
  refused, and read the count as a number; an import's summary accounts for its refused
  frames as a map, `{:checked n :skipped n :by-type {…}}`. So once any dump was loaded,
  from the page or from `VAELII_KB_DIR`, `/kbs`, `/kbs/rows` and the five `/kbs/*`
  controls answered 500 for as long as it stayed loaded. The card now reads the skipped
  count off the map.
  *Class:* **Fix** (the browser's knowledge-bases page).
  [docs/web.md](docs/web.md)

- **`/network` and `/levels/rows` answer two refusals with a page, not a 500.**
  `/network?ctx=CxEverything` reached `qualitative-network`, which resolves no query
  context, and its `:unsupported-context` left the handler as a 500; it is now the 400
  page `/levels` already answers it with. `/levels/rows` with a `level` outside the
  stack's 0-7 reached `lookup`'s `:bad-level` the same way; it now answers the empty
  fragment an unreadable `level` gets.
  *Class:* **Fix** (two browser routes).
  [docs/web.md](docs/web.md)

- **Term and context pages count a large extent instead of reading it.** Every group on a
  term page comes off an index read bounded by its answer except the two extents, and
  reading a root materializes every handle under it before one record can be taken off
  it — 0.9 s for `genl`'s 2,381,749 on a 12.26M-sentex corpus, 4.6 s for a context's
  9,040,392 — to render sixty rows. Past `extent-defer-cap` (20,000) the group renders
  its O(1) stored count and fetches its first page of rows on the same `revealed` trigger
  its later pages use; a smaller extent is read with the page as before. A context page's
  remainder walk skips a walk bound to be truncated by a lower bound on the term index,
  and left the context root out of that bound on the reasoning that a sentex does not
  mention its context. The term index is keyed on `kv/sentex-terms`, a sentex's
  indexable terms **plus its context**, so the context's extent bounds it now.
  `/term?q=genl` went from 1.04 s to 0.09 s, `/term?q=CxWell` from 4.2 s to 0.07 s, and
  every term page of that corpus renders under 100 ms. *Class:* **Fix**.
  [docs/web.md](docs/web.md)

- **A handle inside a sentence renders as the sentence it names.** The browser printed
  `(except (sentexHandle 41))` verbatim, which tells a reader that a sentex is hidden and
  not which one — and the handle is the one thing on the page they could not look up
  without leaving it. It now renders the referenced sentence, badged and linked, wherever
  a meta-sentex is printed: a term-page row, the sentex page, a proposal's `excepts` line.
  The expansion carries the ids already on the path, because the browser reads what is
  stored and a stored sentence naming a handle that reaches back to it was a stack
  overflow rather than a page. *Class:* **Fix**.
  [docs/web.md](docs/web.md)

- **Parens are coloured by how deep they are nested.** A sentence is a tree printed as a
  line and the parens are the only thing saying where a subterm ends, but every subterm
  was already coloured by its role and the structure had no colour at all. The depth now
  counts along the nine-step spectrum from `--rb1` and wraps at nine, so a matching pair
  is one colour and no pair is the colour of the one inside it. The palette and the
  classes were both named for this and neither was ever wired to the other — vaelii.com's
  stylesheet has described these nine as "the engine's browser draws them" since before
  the browser drew any. *Class:* **Fix**. [docs/web.md](docs/web.md)

- **A second `Set-Cookie` no longer replaces the browser's session cookie.** The sandbox
  middleware wrote the header with an `assoc`, so a response that already carried a
  cookie lost one of the two. Both now go through an append, which Ring serves as a
  repeated header. Nothing set a second cookie before this release, so no session was
  affected. *Class:* **Fix**.

- **The write paths' NAT maintenance is sequenced below `vaelii.core`.** Reifying a
  non-atomic term on assert, reconciling the `genlCx` edge it licenses, and sweeping the
  constants a retract orphaned are engine steps, and `vaelii.core` — the public API — ran
  all three inline. `vaelii.impl.nat-maintenance` holds that sequencing now: it sits above
  both `vaelii.impl.nat` and `vaelii.impl.context-nat`, since the assert path spans the
  two and `context-nat` already requires `nat`. Core calls one entry point per site and
  passes its own `retract!` in as an argument, so the engine still requires no part of
  `vaelii.core`. Four `nat` vars stopped being public, `core.clj` is 140 lines shorter,
  and no public name, arglist or docstring moved.

  *Class:* **Fix**.

- **One protocol for snapshot participation.** The compacted trie and the dense roots are
  both written into the durable index image and mapped back out of it, and each answered
  the same three questions under its own name: `t-mapped?` / `t-csr` / `t-install-csr!` on
  one, `mapped?` / `snapshot-columns` / `install-mapped!` on the other, with the install
  taking a section map on one side and four positional arguments on the other. The trie
  was reached through a three-function shim in `vaelii.impl.columnar` and the roots
  directly, so the two participants were not even the same distance from the writer.

  `SnapshotSections` — `snapshot-mapped?`, `snapshot-read`, `snapshot-install!` — is in
  `vaelii.impl.types.snapshot` beside `SnapshotSink` and `SnapshotSource`, and both
  structures implement it directly. The shim is gone, `vaelii.impl.disk.index-snapshot`
  asks both participants the same way and no longer requires the dense roots at all, and
  the residency measurement `sections` stays where it was, since it reports what a running
  KB holds rather than what a snapshot writes.

  *Class:* **Fix**.

- **The non-trie index write is built once for both index stores.** `KvIndexStore` and
  `ColumnarIndexStore` each assembled the same thing: the term index, the secondary roots,
  the two rosters, and the five-count profile tally, differing only in the trie half that
  is native in one and keyed in the other. `kv/flat-family-adds` and `kv/flat-family-retires`
  return those ops with their counts, each store concats its own trie ops around them and
  adds its own `:levels` and `:dead`, and the tally can no longer drift between the two.
  `vaelii.impl.columnar` reaches into `vaelii.impl.kv` for two names now rather than seven.

  *Class:* **Fix**.

- **`lein lint` runs its eleven checks in three concurrent lanes, and cljfmt runs at C2:
  159 s to 29 s.** cljfmt and then reflect run in one lane, clj-kondo's two passes
  (`kondo`, `unused`) share a second so they never write its cache at once, and the rest
  run in the third, so the three finish within a few seconds of each other. Rows print in
  roster order, and `LINT_SERIAL=1` runs the lanes one after another. cljfmt is a plugin,
  so it formatted inside leiningen's own JVM, which the `lein` launcher caps at
  `-XX:TieredStopAtLevel=1`; project.clj's `:jvm-opts` reaches only the JVMs leiningen
  forks. `lein fix`, `lein lint-cljfmt` and the lint row start a second lein with
  `LEIN_JVM_OPTS=-XX:+TieredCompilation`, which names no cap, and `:cljfmt` sets
  `:parallel? true`: the check takes 11 s, down from 69-95 s. Every other task keeps the
  cap on leiningen's JVM, where it shortens startup. The drift row closes its
  parenthesis, the unused row names a stale baseline entry in full rather than `vaelii`,
  the drift checker reads `asp/` as a KB prefix (six false warnings), `clingo/solve`
  leaves the unused baseline since a test calls it, and CONTRIBUTING drops a `ruff` check
  the roster does not have.
  *Class:* **Fix** (lint tooling: a serial roster, a formatter compiled at C1 alone, and
  two truncated summaries).

- **The suite restores its per-test theory KBs from a dump, and every dump carries its
  index.** Sixteen namespaces (the qualitative-reasoning ones: `stp`, `qcn-*`,
  `duration`, `calendar`, `space`, `sign` and the rest) built CxCore and one or two
  `kb/upper` or `kb/middle` files through the full write path before every test,
  600-1,200 ms a test and 229 s of a 760 s single-JVM `:default` run.
  `tu/load-core-with!` restores that KB from a dump built once per JVM for each
  combination of theory files, and those fixtures now cost 27 s. `tu/load-dumped!` does
  the same for any fixture KB under a key, and the eight koinii namespaces' fixtures
  take 7 s, down from 46 s. The starter and CxCore dumps, and the new ones, export the
  `:records+index` variant, so an import replays the index instead of rebuilding it: a
  warm starter restore takes 94 ms, down from 135 ms, and a CxCore one 44 ms, down from
  57 ms. Belief was already installed from the dump's reasoning image.
  *Class:* **Fix** (test tooling: fixtures that bypassed the dump cache).

- **The heaviest `:default` sweeps walk a sample, and a `^:slow` twin walks the whole.**
  `fan-and-post-hoc-agree-over-generated-lattices` generates 4 of its 14 worlds, still
  192 answers, and `fan-and-post-hoc-agree-over-many-generated-lattices` generates all
  14; it took 12.4 s and takes 2.2 s. The two permuting-mark tests in
  `order_independence_test` walk `ordering-sample` orderings of each scenario rather
  than up to 720, 3.7 s and 2.5 s down to 0.15 s and 1.6 s, and each has an
  `every-ordering-of-…` twin. `starter-in-any-order` reads the shipped order from the
  restored starter dump rather than asserting it, 8.7 s down to 6.2 s.
  *Class:* **Fix** (test tooling: exhaustive sweeps in the per-commit suite).

- **`lein test-matrix --owed` owes the configurations the held types and the belief image
  swap, and runs when it owes every one.** The trie, the dense roots, the postings, the
  snapshot protocols, the durable record slot and the reference TMS's justification moved
  into `vaelii.impl.types.*` so a reload keeps them, and the map in
  `scripts/lib/suite-configs.sh` owed those files nothing. It also owed nothing for the
  belief image, `recover`, `reindex` or the observers rete installs, `hier-off` for
  `chain.clj`'s set-algebra lead, or `tms-reference` for `kb.clj`, where `:tms` is read.
  Each now has a row with its reason. And the roster read the configurations sitting out
  with `"${SAT_OUT[@]}"`, which bash 3.2 — what macOS ships — treats as unbound under
  `set -u` when the array is empty, so a change owing all fifteen exited `1` before
  running anything.
  *Class:* **Fix** (developer tooling; the matrix's `--owed` roster).
  [scripts/test-matrix.sh](scripts/test-matrix.sh)

- **`lein gate` reads the test tree's reflection warnings from every shard.** `lein
  test-parallel` keeps each shard's compile output in that shard's log and writes only the
  summary to `test.log`, and the gate's test-stage reflection check read `test.log` alone.
  So it passed with 17 warnings in `test/` (25 lines across four shards). It now reads
  every shard log, and the 17 call sites carry type hints.
  *Class:* **Fix** (a gate check that read a log holding none of what it checks).

- **`scripts/coverage.sh` measures every test namespace, and instruments `kv` and
  `asp.clingo`.** Cloverage runs the test namespaces in name order in one JVM, and
  `reload-test` reloads nearly the whole engine from disk, uninstrumented, so every test
  namespace after it — settle, special, taxonomy, the web tests — counted for nothing: the
  script reported 80.35% of forms where the suite reaches 88.59% on the same basis. It now
  skips `reload-test`, and runs `order-independence-test`, which takes about 75 s
  instrumented. `vaelii.impl.kv` and `vaelii.impl.asp.clingo` instrument and pass on
  lein-cloverage 1.2.4, so the default exclusion is the two protocol namespaces that still
  compile past the JVM's method-size limit.
  *Class:* **Fix** (an instrument that under-read coverage by eight points).

- **`VAELII_TEST_NS_COUNTS=0` leaves the per-namespace counts off.** The test profile
  turned them on when the variable was present at all, so `=0` printed them. It now reads
  the variable through `config/prop-bool`, as the harness's other switches are read.
  *Class:* **Fix** (a false value enabled the switch).

- **`lein bench-witness` asks about a witness path's ends, and counts two new corpora.**
  `above` and `lost` asked whether a reader reaches a witness *edge's* two terms, so a
  surviving route that bypassed the edge read as none and `lost` read 0 on a KB where every
  reader answered wrong. They ask per path now. The corpora gain a short-route-first order
  and a `generated-defeated` arm, and a count of firings stored below a copy of themselves.
  The reading moved to `vaelii.witness-reading` in the test tree, which
  `witness_shortfall_test` holds at zero.
  *Class:* **Fix** (an instrument that read zero over a defect).

- **vaelii-top moves out of this repository, to `vaelii-tools`.** It reads a checkout from
  outside — `git`, `ps`, `logs/runs.tsv` and the matrix run directories — and imports
  nothing from the engine, so it no longer sits in the engine's tree. `tools/` is gone,
  and with it `lein lint`'s `tools` check and the `lein lint-tools` alias, which ran ruff
  over that one package: `lein lint` is eleven checks, and the `prose` check no longer
  reads `tools/`. The run ledger, the matrix's `summary.tsv` and `configs.tsv`, and the
  `test.plan` progress file are unchanged, and they are what vaelii-top reads, so a
  change to one of their formats owes a matching change there.
  *Class:* **Fix** (developer tooling; no public function moves).
  *Migration:* reinstall from the new tree, `pipx install --force --editable
  <vaelii-tools>/vaelii-top`; an editable install pointed at `tools/vaelii-top` runs
  nothing once that directory is gone.

- **The run ledger states its format on every row.** `logs/runs.tsv` gains a twelfth
  column, `format`, holding `RUNLOG_FORMAT` from `scripts/lib/runlog.sh`: 1 now, raised
  when a column is renamed or dropped or a value changes meaning, and left alone when one
  is appended, since a reader keys on column names. vaelii-top reads the ledger from the
  `vaelii-tools` repository, so nothing here would fail when its shape moved;
  `runlog_format_test` now pins the header, the field count and the format. A ledger
  with the eleven-column header has that header replaced once, in place, the first time
  the writer appends to it; its rows are kept as written and read as format 1.
  *Class:* **Additive** (developer tooling; a ledger column). *Migration:* none.
  [scripts/lib/runlog.sh](scripts/lib/runlog.sh)

## 0.20.0 — 2026-09-17 — "a defeated fact stays believed outside the context that decided the clash, and the belief record is renamed Reasoning"

**42 entries** — 6 Breaking, 1 Refusal, 15 Additive, 20 Fix. A clash's defeated member is
disbelieved only at the vantage that sees the clash and below it, a conclusion follows its
reader so an `except` subtracts what rests on what it hides, `contradictions` takes a
reader, and `do/labeling` commits inside its context so two labelings stand side by side.
The record holding a KB's network, taxonomy and derived atoms is renamed `Reasoning`, its
durable image moves to `<dir>/reasoning/`, and seven extension-point protocols move to
held namespaces the development reloader never re-evaluates. A rule is refused an
`(ist Ctx S)` consequent; `open-kb` takes `:recover? :background`, `belief-status` reports
`:withdrawn?` and `:scoped-vantages`, and `lein cli upgrade` brings a store's images up to
the running build. `store-backend` names the backend a directory was written by, the
daemon, the CLI and the browser open a store under it, and only
`scripts/start-vaelii-dev.sh` turns hot reload on.

*Breaks:* `in?`, `believed?`, `except`, `sentexHandle`, `do/labeling`, `contradictions`,
`belief-image`, `:belief-image`, `belief_image`, `types.belief`, `map->Belief`,
`derived-state`, `belief-fingerprint`, `register-belief-image!`, `:belief-fp`, `Prover`,
`SupportingProver`, `Solver`, `SnapshotSink`, `SnapshotSource`, `KvBackend`, `kv-get`,
`:reload?`, `assert`, `assert-rule`, `check`

## 0.19.1 — 2026-09-14 — "five readers repaired after rules lost their sentence field, and the source digest re-parses only files that changed"

**3 entries** — 3 Fix, each a regression 0.19.0 shipped. Five readers that still asked a
rule record for the `sentence` slot 0.19.0 dropped — the NAT teardown, the index
fingerprint, the retired-spelling filter, the vantage supporter check and the QCN
refuted-pair read — take the `implies` form from `sentence-of` instead, so an index dump's
fingerprint over rules is again the digest earlier releases wrote. The source identity
memoizes each engine namespace's parse and re-reads only a file whose stat and digest
moved, taking a call from 1.1 s to 9 ms. The shipped `CxBiology` stores no
`(hasCapability ?x travelling)` record: the capability hierarchy answers it at retrieval,
where a forward rule had stored a second record and justification per flyer.

## 0.19.0 — 2026-09-13 — "stores reopen from a saved belief image instead of recomputing it, and records drop the fields that repeated their own sentence"

**23 entries** — 5 Breaking, 4 Refusal, 4 Additive, 9 Fix, 1 neither label. A
`:disk-snapshot` KB installs a stored belief image at open in place of a full `recover`,
keyed on the records fingerprint, the source identity and the policies, and declines to an
ordinary recover when any of the three moved. The sentex records stop restating what the
store already holds: a rule map carries no `:sentence` and a literal no `:polarity`, a
justification names its rule once as `:informant` and carries no `:out`, and `sentence-of`
reconstructs each form. `bravely` and `cautiously` classify a labeling's dilemmas with no
ASP backend, a `genlCx` cycle is refused at assert as a `genl` cycle already was, and three
write paths that stored a record no belief-filtered read could find now refuse. Seven hot
paths drop work that changes no answer, an operation log records a `:disk-snapshot` KB's
public writes behind a seal, and a settle-phase instrument splits a settle's wall clock
into four cost centres. The engine's `project.clj` names no `vaelii-foreign` coordinate,
so an engine release no longer forces a plugin release.

*Breaks:* `:refuse`, `violations`, `sentex`, `sentexes-matching`, `canonical-sentex`,
`:sentence`, `:polarity`, `bravely`, `cautiously`, `justification`,
`supporting-justifications`, `dependent-justifications`, `vaelii.belief.snapshot`,
`genlCx`, `assert-inert`, `cardAtMost`, `cardAtLeast`

## 0.18.1 — 2026-09-11 — "every entry point refuses an out-of-range value by name, and the upper ontology splits things into spatial and temporal"

**14 entries** — 2 Refusal, 4 Additive, 6 Fix. Every bounded entry point refuses a value
outside its domain by name, reading one shared domain table, and `assert-inert` refuses an
open sentence. The upper ontology divides `thing` by space and time, renames
`spatial_thing` and `temporal_thing` to `spatial` and `temporal`, and adds a `CxUniverse`
collector context. A process-wide cache profile scales every derived cache's bound, and a
memory-pressure guard the servers install shrinks the caches as the old generation fills
and grows them back as it drains. A reified NAT or context constant is named by the
SHA-256 of its expression, so the same expression reifies to the same constant across
processes, and the one-shot clingo solve injects its ground program through the backend
accessors rather than a temp file.

*Breaks:* `:counters?`, `:believed?`, `:max-cost`, `:max-depth`, `:max-term-growth`, `add-evaluatable`, `assert-inert`, `describe`, `why-not`, `spatial_thing`, `temporal_thing`

## 0.18.0 — 2026-09-09 — "argument-type declarations create the types they constrain, and rules forward-chain only when asked to"

**16 entries** — 3 Breaking, 1 Refusal, 9 Additive, 3 Fix. Assertive argument types become
the default reading: an `arg` / `genlArg` / `interArg` declaration mints the type it
constrains rather than only testing for it. A bare `implies` rule defaults to `:backward`
and materializes nothing, and `set/forwardRule` adds forward chaining to the backward use
rather than replacing it, so a rule forward-chains only where its author asks. The arity
vocabulary gains a runtime floor — a variable-arity application below its `arityMin` is
refused — and `admitsArgnum` answers a position query from the declared arity. New
declaration vocabulary types a whole variable-arity tail (`args`, `argsGenl`, `argAndRest`,
`argAndRestGenl`) and names an `intersection` kind that derives its taxonomy edges, and new
readers report the brave and cautious status of a labeling dilemma, a cardinality bound over
ASP choice heads, and the subsumption status of every type pair. A state-of-affairs and
causality cluster joins the upper ontology in CxAbstract.

*Breaks:* `VAELII_ASSERTIVE_ARG_TYPES`, `(implies` asserted bare, `set/forwardRule`,
`arityMin`, `(lessThan`, `(greaterThan`, `(termsRelated`, `(functionCorrespondingPredicate`,
`vaelii.impl.llm.protocol/Provider` (now `vaelii.host.llm.protocol/Provider`; the
entry was added after the release)

## 0.17.0 — 2026-09-06 — "arity becomes declared vocabulary on every relation, and declarations stop restating what they already imply"

**14 entries** — 1 Breaking, 4 Refusal, 4 Additive, 5 Fix. A declaration that restates
what the taxonomy already concludes turns that conclusion into a precondition, so the
arrival order of two assertions decides which facts a KB holds. Four entries retire such a
declaration — on `genl`, on fifteen unary marks, on six arity marks, and in the `predAll`
pair's third argument — and the arity vocabulary underneath is rebuilt so `relation` is
the common parent of `predicate` and `function` and every relation lands in exactly one
arity policy. `predAllSpecified` and `predSpecifiedAll` go binary and derive the filler
type from the predicate's own slot contract. Three composite function marks — `injection`,
`surjection` and `bijection` — arrive as one declaration each, a `genlCx` edge's merge
sweep stops growing with the KB, and a late `symmetric` declaration folds a mirrored pair
no earlier version could fold.

*Breaks:* `(predAllSpecified`, `(predSpecifiedAll`, `specified-violations`,
`all-specified-violations`, `(binary_predicate P)` beside `(variable_arity P)`,
`:arg-type`, `*assertive-arg-types?*`, `VAELII_ASSERTIVE_ARG_TYPES`,
`(genlArg genl 1 thing)`, `(arg symmetric 1 predicate)`, `(arg functional 1 predicate)`

## 0.16.0 — 2026-09-04 — "the predAll quantifier family, refusals that carry a type, and declarations that apply to facts already stored"

**18 entries** — 3 Breaking, 1 Refusal, 7 Additive, 7 Fix. The `predAll` quantifier
family lands in all eight cells. Three refusals stop answering with the wrong keyword:
an unpinned indeterminate term is not provably `different` from anything, a missing
adapter is not an unknown backend, and a wrong operand count is not an unknown option.
Declarations arriving after the facts now reach them — a `(symmetric P)` mark folds
records already stored, a computed `genlCx` edge runs the reconcilers a stated one runs,
and `quotedArg` is answered along the `genl` closure. Every refusal declares what its
`ex-data` carries, and a throw that drops a key fails the build.

*Breaks:* `(different`, `indeterminate_term`, `:unknown-backend`, `:sqlite`, `:pg`,
`:unknown-option`, `:not-stratified`

## 0.15.0 — 2026-09-01 — "definitions that compute their own answer, and two renames"

**7 entries** — 2 Breaking, 5 Additive. Definitional membership is answered at query
time rather than only by a forward rule. Two renames: the sentex polarity slot is
`:polarity`, and the `AtomicSentex` record is `LiteralSentex`. A unary predicate is
snake_case and `assert` enforces the spelling in both directions, which retired the
camelCase marks. CxCore names the expression kinds and gains a curation vocabulary.

*Breaks:* `unaryPredicate`, `reifiableFunction`, `abduciblePredicate`,
`closedExtentPredicate`, `disjointMetatype`, `siblingDisjoint`, `warmBlooded`, `:truth`

## 0.14.0 — 2026-08-29 — "the index image becomes a storage backend, and the heap it no longer needs"

**10 entries** — 1 Refusal, 1 Additive, 5 Fix. The mapped index image becomes a backend
of its own, `:disk-snapshot`, rather than a property of the disk store, and stops
carrying the argument roots into heap. The disk store's live-handle sets become
compressed bitmaps. The writer refreshes a drifted image mid-life and can be told not
to. A `functionalInArg` declaration arriving after the facts it convicts is reported
rather than silently late. Neither adapter shipped at this version; both stayed at
0.13.0.

*Breaks:* `vaelii.index.snapshot`, `:argument-family-ceiling`

## 0.13.0 — 2026-08-25 — "calendar time, joined queries, and entry points that refuse invalid input"

**95 entries** — 5 Breaking, 14 Refusal, 32 Additive, 22 Fix. The largest release:
calendar time, joined queries and a sweep through the entry points that refuse.
`CxChange` ships an event calculus, calendar constructors give a date its own endpoints
so it orders itself, and a metric constraint narrows an interval relation. `or` is
accepted in a rule antecedent, stored as one rule per alternative, and refused as a
goal. Every search entry point takes a bound and the daemon holds them to its ceiling.
Fourteen refusals close inputs whose acceptance stored junk, and the `:disk` and
`:pg-disk` pairings are renamed to say that both halves are out of core.

*Breaks:* `:disk`, `:pg-disk`, `VAELII_TEST_BACKEND=disk`, `edit!`,
`edit-with-consequences!`, `apply-proposal!`, `contexts`, `count-in-context`,
`contextDenotingFunction`, `lein cli load`, `prove`, `provable?`, `query`, `argue`,
`forward-chain`, `ask`, `ask?`, `query-plan`, `abduce`, `sentexes-matching`,
`handle-of`, `assert`, `load-text!`, `lein cli assert`, `unaryPredicate`,
`binaryPredicate`, `ternaryPredicate`, `/kbs`, `lein serve --listen <flag>`,
`vaelii.client/client`, `:timeout-ms`, `:token`, `dereference`, `resolve-by-locator`,
`set-trust!`, `trust-of`, `display-name-of`, `:reserved-family` (a dense index past its
`(predicate, position)` ceiling is `:argument-family-ceiling`), `do/label` over an
`assumptionRule` with a negated head (`:choice-head-not-positive`); these two entries
were added after the release

## 0.12.0 — 2026-08-23 — "query contexts, bulk loading, and types for literal values"

**99 entries** — 3 Breaking, 3 Refusal, 7 Additive, 5 Fix. Query contexts, bulk loading,
and a literal's type. `resultIsa` and `resultGenl` become `result` and `genlResult`; the
four function marks classify what they mark, and the reifiability criterion is written
down. A records read stays lazy, and a proof's witness is one of its bindings. Three
reads that could not answer the question stop answering empty. First release of the two
adapters, `com.vaelii/postgres` and `com.vaelii/sqlite`, each at this version.

*Breaks:* `resultIsa`, `resultGenl`, `reifiableFunction`, `unreifiableFunction`,
`quotingFunction`, `contextDenotingFunction`, `ist`, `:proof?`, `?ctx`,
`qualitative-network`, `possible-relations`, `:arg-type`, `:quoted-arg-type`, `result`,
`genlResult`, `:arg-genl`, `character_string`, `:pg-disk`, `:dir`,
`:stale-index-records`, `register-modal-predicate!`

## 0.11.0 — 2026-08-22 — "contradiction solving, arrival order, and the durable log"

**67 entries** — 2 Breaking, 4 Additive. Contradiction solving, arrival order, and the
durable log. `antiTransitive` convicts the chain it forbids rather than being declared
and deferred. Definitional collection relations tie membership to a defining condition,
and sibling disjointness lets a collection's specializations separate themselves, with
an escape hatch for a pair that must overlap. A computed predicate or function is
registered in one line.

## 0.10.0 — 2026-08-20 — "more than one agent over one knowledge base"

**9 entries** — 4 Additive. Koinii: several agents coordinate over one shared knowledge
base, with belief projection for what each agent holds true. A context can be a reified
function application whose `genlCx` edges compute themselves. Mention-opacity arrives —
a quoting function reads its argument by spelling — and `quotedArg` types an argument
against a syntactic type. The `argIsa`, `argGenl` and `interArgIsa` spellings become
`arg`, `genlArg` and `interArg`.

## 0.9.0 — 2026-08-17 — "the truth-maintenance network defaults to dense"

**15 entries** — 5 Breaking, 8 Additive. The dense truth-maintenance network becomes the
default and gives a concurrent reader a consistent view. Four relation properties are
enforced rather than documented. A subsumption rests on its strongest route rather than
its shortest. An algebraic property becomes one predicate instead of a mark and a twin,
which retired the `...Predicate` spellings.

*Breaks:* `defeat-class`

## 0.8.0 — 2026-08-14 — "predicates inherit down the hierarchy"

**50 entries** — 1 Breaking, 1 Additive. Predicates inherit down the hierarchy. A KB
whose declared hazards are unresolved refuses writes rather than accepting them
unchecked, and a derived record's teardown is refused where belief was never built.
`check` and `check-edit` answer for the entry point they mirror. Five refusals close
recovery paths that believed records the store did not hold.

*Breaks:* `:unrecovered-kb`, `write-hazards`, `note-hazards!`, `contradictions`,
`violations`, `:constraint-exposure`

## 0.7.0 — 2026-08-12 — "contexts get a single naming convention"

**2 entries.** Contexts get one spelling. A context name is `Cx`-prefixed rather than
`Context`-suffixed, and the context-transitivity predicate is `genlCx`.

## 0.6.0 — 2026-08-12 — "stored rules become first-class"

**22 entries** — 2 Breaking, 4 Refusal, 2 Additive. Stored rules become first-class: a
rule can conclude a rule, and a rule carries a handle, TMS support and retraction with
no rule-specific machinery. A capability claim about a kind is `capabilityType` and
about a member is `hasCapability`. A NAF guard written as a conjunction now guards, and
the strictest policy stops being the leakiest.

## 0.5.1 — 2026-08-11 — "faster writes, and more of the engine exposed to monitoring"

**15 entries.** Faster writes, more to watch. A settle pays for the region it moved
rather than for what the KB holds. The arbitrating half of a bounded pass says when its
budget stopped it. Four places where arrival order decided an answer are closed.

## 0.5.0 — 2026-08-07 — "operating the engine as a service"

**23 entries.** Operating the engine as a service. The daemon authenticates and refuses
to bind an address without a token. One space number names a KB's stores, `:space`,
replacing the separate record and index spellings. `context-size` becomes
`count-in-context`, `different` descends into compound arguments, and a name can carry a
sense and a lexeme.

*Breaks:* `:record-space`, `:index-space`, `docs/storage.md`

## 0.4.0 — 2026-08-05 — "correctness fixes against the invariants"

**33 entries.** Correctness fixes against the four invariants. A conjunctive query could
answer nothing while each of its conjuncts answered, and no longer does. `assert`
refuses a sentence that is not an s-expression, an `exceptWhen` query's literals are
held to the naming invariants, and an `edit!` batch key nothing reads is refused.

## 0.3.0 — 2026-08-04 — "a type on every refusal"

**29 entries.** A type on every refusal: every `ex-info` the engine throws carries a
`:type`, and the daemon's refusal keywords become plain. Both servers hold one
request-body ceiling, and the browser serializes its writes. An `ist` form must have
exactly three elements.

## 0.2.0 — 2026-08-03 — "the public API boundary is drawn"

**17 entries.** The public API boundary is drawn — six public namespaces, everything
else `vaelii.impl.*` and free to change. Every handle-taking function refuses a
non-handle. `close!` releases a durable KB's directory, an argument-constraint refusal
names its convicting declaration in content order, and the five sweeps start running in
CI.

## 0.1.0 — 2026-07-31 — "the first release"

The first public release.

## 2026-07-19 .. 2026-07-30 — the pre-release dailies

Twelve dated entries before versioning began, one per day of the initial build: the
whole stack on day one (2026-07-19), then order independence made an invariant, equality
and a sudoku solved, sound negation as failure, performance fixes and an operational
surface, denser storage measured first, OpenCyc in the engine's own format, reads scoped
to the asking context, aggregation over query results, the gate (lint, suite and
scaling), one entry point for backward chaining, and declarations that re-check what
they change (2026-07-30).
