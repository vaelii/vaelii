;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.jtms-protocol
  "The representation boundary of the truth-maintenance system: the `Tms` protocol
  alone, with no implementation.

  It lives in its own namespace, apart from `vaelii.impl.jtms` (the reference
  network) and `vaelii.impl.dense-jtms` (the dense one), for two reasons.  Both
  implementations depend on it, and the reference depends on nothing of the dense one, so
  the boundary is the one thing they share; the dense network also calls two helpers of
  the reference namespace (`graph-just`, `dissoc-all`).  And it is large — forty-odd methods, each documented — which
  makes the generated protocol map big enough that re-evaluating the form (as
  cloverage does, form by form, to instrument a namespace) overflows the JVM's
  64 KB per-method bytecode limit; isolated here, the protocol is loaded but not
  instrumented while the whole of `vaelii.impl.jtms` still is (scripts/coverage.sh).

  A held namespace (`vaelii.impl.types.prover` states what that means): it defines the `Tms` protocol and requires no vaelii namespace, so the development browser's reloader never re-evaluates it, and an edit to it takes a restart.")

(defprotocol Tms
  "What a truth-maintenance network must answer, independent of how it stores the
  graph.  Two implementations ship: `RefTms` in `vaelii.impl.jtms` — an atom over one
  persistent map, the reference — and `vaelii.impl.dense-jtms`, which holds the same
  graph in bitmaps and primitive-keyed maps.  Selected per KB (`open-kb`'s `:tms` opt),
  dense by default since 0.9.0, and proven to answer identically by `jtms_dense_oracle_test`.

  The boundary is at the *representation*, not at the algorithm: both implementations
  run the same least-fixpoint relabel over the same affected region, because that is
  the semantics, not an implementation detail.  What differs is where a node's
  premise flag, depth and adjacency live.

  ## What the network computes

  One function, and every method below either supplies an argument to it, reads a
  result of it, or edits its domain:

      label(graph, attributes, blocked, defeated) -> (in, groundable, classes)
      believed                                     = in - superseded

  `graph` is the nodes and justifications.  `attributes` are the per-element strengths
  the class fixpoint reads.  `blocked`, `defeated` and `superseded` are three sets the
  **caller** computes and replaces whole every settle — the network is pure and holds no
  KB, so it can run none of the three queries that decide them.  `in`, `groundable` and
  `classes` are what a relabel writes.

  The three overrides enter belief at three different points, and a method that confuses
  two of them is wrong in a way no label comparison catches:

  | override | enters at | moves |
  |---|---|---|
  | `blocked` | inside `valid?`, so a blocked justification supports nothing | `in` **and** `groundable` |
  | `defeated` | inside the fixpoint, as a datum forced OUT | `in` only, so a defeated datum can revive |
  | `superseded` | subtracted at the read, after both fixpoints | neither — the datum stays in `in` so its rewritten twin keeps its justification |

  `vaelii.impl.jtms` states each of the three at length under *the state*.

  ## The seven roles

  `roles` below assigns every method exactly one, and `jtms_protocol_test` fails on a
  method in none or in two.  The roles are a division of **what a method touches**, not
  of what it may be implemented without: every mutation relabels, so every role's
  mutators write the output role's state, and no partition of these methods is closed
  under writes.

  | role | what it holds | what supplies it |
  |---|---|---|
  | `:graph` | nodes, justifications, depth, adjacency | `-ensure-node`, the two `-add-*`, `-retract`, `-sweep` |
  | `:attribute` | a premise's and a justification's strength | written with the element, and by `-restrength-informant` |
  | `:blocked` | the blocked justification-id set | the caller's exception query |
  | `:defeated` | the forced-OUT datum set | the caller's contradiction decision |
  | `:superseded` | the `datum -> reason` map | the caller's equality closure |
  | `:output` | `in`, `groundable`, `classes` | every relabel |
  | `:window` | the touched sets | every relabel |

  **A fourth place belief is decided is not on this protocol.**  A scoped defeat and a
  visibility `except` are applied per reading context by `vaelii.impl.resolution`, over
  `vaelii.impl.jtms/grounded-in-region` — which is built on the reads here and is
  therefore not a method at all, so both representations answer it without implementing
  anything.  The network's labels do not move for either, and `-believed?` answers the
  same before and after one.

  ## What an implementation owes

  Four obligations.  Miss one and a network is *wrong*, not slow — belief is the last
  thing in the engine that may drift silently, since a bad label does not throw, it
  just answers a query differently.  Each names the gate that holds it, because an
  obligation with no gate is a comment.

  1. **The same fixpoint over the same region.**  Binds `:output`, and through it
     `:blocked` and `:defeated`, which are the fixpoint's two override arguments.  A
     datum is believed when it is a premise or has a valid justification (all
     antecedents believed), minus the defeated set; the label is recomputed over the forward consequence closure of
     whatever changed, with the rest held fixed as boundary.  That is the *semantics*
     of belief here (docs/nmtms.md), not a strategy an implementation may improve on:
     the region fixpoint is equal to the global one because a least fixpoint with the
     boundary fixed is unique, and uniqueness is also the whole of why locality costs
     no order independence.  An implementation may move where the graph lives; it may
     not move what is believed.  Gate: `jtms_dense_oracle_test`, which compares the
     entire `-snapshot` after **every** step of a randomized operation stream — not a
     sampled read, because a divergence in `:groundable` is invisible to `-believed?`
     until a retraction three operations later collects the wrong node.

  2. **A mutation is atomic to a concurrent reader.**  Binds every role.  A reader
     sees the state wholly
     before or wholly after a relabel, never half of one — the single-writer contract
     owes the incidental reader that much (a web browser over a REPL's KB,
     docs/storage.md).  *How* is not the obligation and the two differ: the reference
     by compare-and-set on its state atom, the dense network by taking its
     `StampedLock` for writing.  Gate: `jtms_atomicity_test`, whose atomicity half runs
     against both networks for exactly this reason.

  3. **The flips are inside the published window, and the window inside the region.**
     Binds `:window`.  `-touched` is not diagnostics: `preview`, the consequence report and the change
     feed all read it instead of diffing the believed set, which would be O(KB) per
     write (docs/preview.md, docs/feed.md).  A window that missed a flip serves a stale
     report; one that outran its own region would say the operation was not local after
     all.  The containment is deliberately one-way — the window is a **superset** of
     the flip set (defenses.md) — so this obligation is containment and never equality.
     Gate: the oracle test checks both containments on both networks after every
     step, and `jtms_locality_test` measures the published window across graph sizes
     on both — a region widened back to the whole graph answers identically, so a
     comparison of labels alone would pass it.

  4. **No store, by construction.**  Binds every role, and its second half binds
     `:attribute` in particular.  Every method here takes the network plus integers
     and plain values.  Nothing crossing the boundary can carry a record store, an index or a KB,
     and no implementation may acquire one.  Two things rest on that and neither is
     optional.  A node holds **no reference to the sentex it labels** — the network is
     always resident, so a strong reference would pin every record in RAM and defeat a
     paging backend entirely (measured: the nodes reached 50% of the record store).
     And `-premise-strength`, which the class fixpoint reads per in-region node, is a
     *memory* read on every representation, which is what makes locality a claim about all of them rather than
     about the one whose reads happen to be free — on a disk store that read would be a
     lock and a slot decode, on a server store a round trip, per in-region node per
     worklist pop.  Gate: the structure of this protocol, plus both implementations' `ns`
     forms, which name no store.  A store-backed network would break the structural
     guarantee and inherit an obligation nothing here gates: it would owe a
     read-counting one of its own.

  One claim is deliberately **not** on that list, because nothing at this boundary can hold
  it: the cost of the in-region work itself.  Obligation 3 says a small region was asked
  for and obligation 4 says nothing was paid per boundary node, and neither says the
  small region was *cheap* — a structure whose every write rebuilds a whole container
  satisfies both and still grows with the KB, at a scale no unit test reaches
  (docs/defenses.md argues it under *Locality is a claim about every representation*).
  It is held by `lein bench-jtms` and by review.  It is written down here anyway,
  because an implementation that is never told about a claim cannot be held to it.

  Every method is named with a leading `-`; the plain names (`in?`, `add-premise`, …)
  are the public functions in `vaelii.impl.jtms`, which dispatch here.  Callers use those."
  ;; ---- :graph — the nodes and justifications the fixpoint runs over ----------
  (-node?            [tms datum] "Is there a node for `datum`?")
  (-datums           [tms]       "Seq of every datum with a node.")
  (-any-node?        [tms]       "Is there any node at all?  A boolean that must not
    materialize the datum seq — `(first (-datums …))` drains the whole dense bitmap
    into boxed Longs, so callers on a render/poll path use this instead.")
  (-depth            [tms datum] "Derivation depth, 0 when unknown.")
  (-premise?         [tms datum] "Is `datum` a premise?")
  (-supports         [tms datum] "Justification ids concluding `datum`.")
  (-dependents       [tms datum] "Justification ids using `datum` as an antecedent.")
  (-justification    [tms jid]   "The graph justification (`graph-just` — no bindings), or nil.")
  (-justifications   [tms]       "Every live graph justification.")
  (-ensure-node      [tms datum depth] "Create the node if absent; lower its depth.  The
    one graph mutation that relabels nothing: a node with no premise mark and no
    justification is OUT either way.")
  (-add-premise      [tms datum strength] "Mark `datum` a premise at `strength`, and
    relabel its region.  Writes `:attribute` as well as `:graph` — `strength` is the
    premise strength `-premise-strength` answers.")
  (-suspend-premise  [tms datum] "Drop `datum`'s premise mark and relabel — no sweep.")
  (-add-justification [tms just] "Record `just` and relabel what it moves.  `just` carries
    its own strength, so this writes `:attribute` too.")
  (-retract          [tms datum] "Drop the premise, relabel, sweep; return the removals.")
  (-sweep            [tms seeds] "Sweep the consequence closure of `seeds`.")
  (-relabel          [tms]       "Whole-graph relabel — no engine path calls it; see
    `vaelii.impl.jtms/relabel`.  The one method whose cost is the graph rather than a
    region, which is why nothing on the engine path may acquire the habit.")

  ;; ---- :attribute — the per-element strengths the class fixpoint reads --------
  (-premise-strength [tms datum] "Its assumption strength, or nil.  Read once per
    in-region node by the class fixpoint, which is what obligation 4 requires to be a
    memory read on every representation.")
  (-restrength-informant [tms informant strength]
    "Set `strength` as the rule-contribution slot of every justification whose
    informant is `informant`, and relabel the region their consequences span.  Cost is
    that region, plus the scan for the informant's justifications.")

  ;; ---- :blocked — invalid justifications, computed by the caller --------------
  (-blocked          [tms]       "The blocked justification-id set.")
  (-set-blocked      [tms jids]  "Replace the blocked set and relabel what moved.
    Blocking enters through `valid?`, so it moves `:groundable` as well as `:in` and an
    excepted conclusion is swept rather than retained.  The caller evaluates the
    exceptions and hands `jids` in — the network holds no KB and cannot run the query —
    so the cost here is the region seeded by the justifications whose blocked status
    changed, never the cost of deciding which those are.")
  (-update-blocked   [tms f]     "Apply `f` to the blocked set as one atomic step,
    otherwise `-set-blocked`.")

  ;; ---- :defeated — datums forced OUT, decided by the caller -------------------
  (-defeated         [tms]       "The forced-OUT set.")
  (-defeat           [tms datums] "Force `datums` OUT and relabel their region.  A defeat
    enters the fixpoint as a forced-OUT datum, so it moves `:in` and leaves `:groundable`
    standing, which is what lets a defeated datum revive when the defeat is cleared.
    `settle` decides `datums` by a walk over the opposed set that reads no justification
    edge; the cost here is the forward closure of `datums`, never the cost of that walk.")
  (-clear-defeats    [tms]       "Empty the defeated set and relabel the forward closure
    of what was defeated.")

  ;; ---- :superseded — reported belief subtracted after both fixpoints ----------
  (-superseded       [tms]       "The `datum -> reason` supersession map.")
  (-supersede        [tms m]     "Replace the supersession map.  No relabel, and the one
    override mutation that walks no region: supersession subtracts *reported* belief
    after both fixpoints, so no label moves.  The caller computes `m` from the equality
    closure; the cost is the size of `m`.")

  ;; ---- :output — what a relabel writes ---------------------------------------
  (-believed?        [tms datum] "Is `datum` believed (IN, minus supersession)?  Reads
    `:superseded` as well as `:output`, because `believed = in - superseded` is the
    definition rather than a filter over it.")
  (-believed         [tms]       "Seq of the believed datums, or nil when none.")
  (-any-belief?      [tms]       "Is any datum believed (IN, minus supersession)?  Like
    `-any-node?`, terminates at the first believed datum rather than draining `-believed`.")
  (-defeat-class     [tms datum] "Defeat-class of an IN datum, nil when OUT.  Reads
    `:graph`-resident IN-ness too: `:classes` holds only the datums above the lattice's
    bottom, so being IN is what separates OUT from IN at the default class.")
  (-snapshot         [tms]
    "The whole network as one canonical persistent map — `:nodes :justs :in
    :groundable :defeated :blocked :superseded :classes`.  The only method that spans
    every role, and the *comparison* shape the differential oracle checks; it is the
    shape `RefTms` happens to store, and a dense implementation materializes it, so it
    is a debugging and testing surface, never something an engine path calls.")

  ;; ---- :window — the published flip window ------------------------------------
  (-touched          [tms]       "Datums whose region was relabelled since the reset.")
  (-touched-in       [tms]       "Of those, the ones already believed when first relabelled.")
  (-touched-new      [tms]       "Datums whose node this window created.")
  (-reset-touched    [tms]       "Clear the touched sets."))

(def roles
  "Which role each `Tms` method is in, as `{role #{method-name}}` — the protocol
  docstring's *The seven roles* written as data, so a test holds it rather than review.

  It is a partition of what a method **touches**, and the protocol docstring says why it
  cannot be a partition of what a network may be implemented without: every mutation
  relabels, so every role's mutators write `:output`'s state.  A method that reads across
  roles says so in its own docstring — `-believed?` and `-defeat-class` are the two, and
  each names the reason.

  `jtms_protocol_test` fails on a method in no role, a method in two, and a name here
  that the protocol does not define."
  '{:graph      #{-node? -datums -any-node? -depth -premise? -supports -dependents
                  -justification -justifications -ensure-node -add-premise
                  -suspend-premise -add-justification -retract -sweep -relabel}
    :attribute  #{-premise-strength -restrength-informant}
    :blocked    #{-blocked -set-blocked -update-blocked}
    :defeated   #{-defeated -defeat -clear-defeats}
    :superseded #{-superseded -supersede}
    :output     #{-believed? -believed -any-belief? -defeat-class -snapshot}
    :window     #{-touched -touched-in -touched-new -reset-touched}})
