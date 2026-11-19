;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.jtms-protocol
  "A **held namespace** (`vaelii.impl.types.prover` states what that means): the `Tms`
  protocol alone, no implementation, in its own file apart from `vaelii.impl.jtms` and
  `vaelii.impl.dense-jtms`. Its forty-odd methods make the generated protocol map large
  enough that re-evaluating the form, as cloverage does to instrument a namespace,
  overflows the JVM's 64 KB per-method limit; isolated here, the protocol is loaded and not
  instrumented while `vaelii.impl.jtms` still is (scripts/coverage.sh). It requires no vaelii
  namespace, so the development browser's reloader never re-evaluates it and an edit takes a
  restart.")

(defprotocol Tms
  "What a truth-maintenance network must answer, independent of how it stores the graph.
  `RefTms` (`vaelii.impl.jtms`) and `vaelii.impl.dense-jtms` implement it, selected by
  `open-kb`'s `:tms`. Both run the same least-fixpoint relabel over the same affected region;
  they differ in where a node's premise flag, depth and adjacency live. The obligations an
  implementation owes, each with its enforcing test, are in docs/nmtms.md, What a second
  network owes.

  The network computes one function:

      label(graph, attributes, blocked) -> (in, classes)
      believed                           = in - superseded - held

  `graph` is the nodes and justifications. `attributes` are the per-element strengths the
  class fixpoint reads and the four forced sets the caller decides from stored content
  (docs/nmtms.md, \"The forced-monotonic set\"): `:mono`, `:out`, `:void` and `:held`.
  `blocked` and `superseded` are caller-computed sets replaced whole every settle, because
  the network holds no KB. `blocked` enters inside `valid?` and moves `in`; `superseded` is
  subtracted at the read and moves nothing. A reader's verdict and a visibility `except` are
  applied per reading context by `vaelii.impl.resolution`, not on this protocol.

  `roles` assigns every method one of seven roles (`:graph` `:attribute` `:blocked`
  `:superseded` `:output` `:touched` `:hold`), and `jtms_protocol_test` fails on a method in
  none or in two. Every method is named with a leading `-`; the plain names (`in?`,
  `add-premise`, …) are the public functions in `vaelii.impl.jtms`, which dispatch here."
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
  (-support-count    [tms datum] "How many justifications conclude `datum`, read without
    building the id set `-supports` answers.")
  (-dependent-count  [tms datum] "How many justifications use `datum` as an antecedent, read
    without building the id set `-dependents` answers.")
  (-justification    [tms jid]   "The graph justification (`graph-just` — no bindings), or nil.")
  (-justifications   [tms]       "Every live graph justification.")
  (-ensure-node      [tms datum depth] "Create the node if absent; lower its depth and the
    depths below it (`jtms/lowered-depths`).  The one graph mutation that relabels
    nothing: a node with no premise mark and no justification is OUT either way.")
  (-add-premise      [tms datum strength] "Mark `datum` a premise at `strength`, and
    relabel its region.  Writes `:attribute` as well as `:graph` — `strength` is the
    premise strength `-premise-strength` answers.")
  (-suspend-premise  [tms datum] "Drop `datum`'s premise mark and relabel — no sweep.")
  (-add-justification [tms just] "Record `just` and relabel what it moves.  `just` carries
    its own strength, so this writes `:attribute` too.")
  (-retract          [tms datum] "Drop the premise, relabel, sweep; return the removals.")
  (-sweep            [tms seeds] "Sweep the consequence closure of `seeds`.")
  (-drop-justification [tms jid] "Remove the one justification `jid`, relabel what it
    supported, and sweep what that leaves OUT; return the removals.")
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
  (-forced?          [tms kind x] "Is `x` a member of forced set `kind`?  A set lookup,
    read on the relabel path.")
  (-forced-members   [tms kind] "Every member of forced set `kind`, as a set.  Read by a
    diagnostic that enumerates the set (`vaelii.core/violations`); no relabel path calls it.")
  (-set-forced       [tms kind xs on?] "Add each of `xs` to forced set `kind` (`on?`
    true) or take it out, and relabel the region of the members that moved: the datums
    themselves for `:mono` and `:out`, the consequences for `:void`, and none for `:held`,
    whose IN members `-touched` and `-touched-in` record as a relabel would.  A member need not
    have a node or a justification yet, so a caller writes it before the element it
    governs and the element never holds a label the set rules out.")

  ;; ---- :blocked — invalid justifications, computed by the caller --------------
  (-blocked          [tms]       "The blocked justification-id set.")
  (-set-blocked      [tms jids]  "Replace the blocked set and relabel what moved.
    Blocking enters through `valid?`, so an excepted conclusion goes OUT and is swept
    rather than retained.  An id with no justification is not kept.  The caller
    evaluates the exceptions and hands `jids` in — the network holds no KB and cannot run
    the query — so the cost here is the region seeded by the justifications whose blocked
    status changed, never the cost of deciding which those are.")

  ;; ---- :superseded — reported belief subtracted after the fixpoint -------------
  (-superseded       [tms]       "The `datum -> reason` supersession map.")
  (-supersede        [tms m]     "Replace the supersession map.  No relabel, and the one
    override mutation that walks no region: supersession subtracts *reported* belief
    after the fixpoint, so no label moves.  The caller computes `m` from the equality
    closure.  A map `m` is installed as it is, in O(1); any other collection of entries
    costs its size.")

  ;; ---- :output — what a relabel writes ---------------------------------------
  (-believed?        [tms datum] "Is `datum` believed (IN, minus supersession and the
    `:held` forced set)?  Reads `:superseded` and `:attribute` as well as `:output`,
    because `believed = in - superseded - held` is the definition rather than a filter
    over it.  An empty `:held` set costs one emptiness check.")
  (-believed         [tms]       "Seq of the believed datums, or nil when none.")
  (-any-belief?      [tms]       "Is any datum believed (IN, minus supersession and `:held`)?  Like
    `-any-node?`, terminates at the first believed datum rather than draining `-believed`.")
  (-defeat-class     [tms datum] "Defeat-class of an IN datum, nil when OUT.  Reads
    `:graph`-resident IN-ness too: `:classes` holds only the datums above the lattice's
    bottom, so being IN is what separates OUT from IN at the default class.")
  (-snapshot         [tms]
    "The whole network as one canonical persistent map — `:nodes :justs :in :blocked
    :superseded :classes`.  The only method that spans
    every role, and the *comparison* shape the differential oracle checks; it is the
    shape `RefTms` happens to store, and a dense implementation materializes it, so it
    is a debugging and testing surface, never something an engine path calls.")

  ;; ---- :touched — the published flip set --------------------------------------
  (-touched          [tms]       "Datums whose region was relabelled since the reset.")
  (-touched-in       [tms]       "Of those, the ones already believed when first relabelled.")
  (-touched-new      [tms]       "Datums whose node was created since the reset.")
  (-touched-out      [tms]       "Datums a forced-set change (`-set-forced`) took from IN
    to OUT since the reset.")
  (-touched-down     [tms]       "Datums a relabel since the reset took from IN to OUT, or
    from `:monotonic` to `:default`.")
  (-touched-up       [tms]       "Datums a relabel since the reset took from `:default` to
    `:monotonic` while IN.")
  (-reset-touched    [tms]       "Clear the touched sets, and outdate every mark.")
  (-touch-mark       [tms]       "A mark of this point in the touched sets, which
    `-touched-since` reads: every datum they record after this call is in it.")
  (-touched-since    [tms mark]  "The datums the touched sets recorded after `mark`, a datum
    relabelled again since included; the whole `-touched` set for a mark taken before the
    last `-reset-touched`, or nil.")

  ;; ---- :hold — the labels a settle keeps for the other threads ----------------
  (-hold             [tms h]     "Open hold `h` (`vaelii.impl.observe/new-hold`) on this
    network, and answer true, or answer false when a hold is open on it already.  From this
    call until `-release`, every relabel records the labels it moves as they were before
    the first move, and a read on a thread other than `h`'s owner answers from those while
    `vaelii.impl.observe/reads-held?` is true of `h`.")
  (-release          [tms h]     "Close hold `h` on this network, when it is the one open.")
  (-held             [tms]       "The hold open on this network, or nil."))

(def roles
  "Which role each `Tms` method is in, as `{role #{method-name}}`: the protocol docstring's
  seven roles as data. A partition of what a method touches, not of what an implementation
  may omit, since every mutation relabels. `-believed?` and `-defeat-class` read across
  roles and say so in their own docstrings. `jtms_protocol_test` fails on a method in no
  role, a method in two, and a name here that the protocol does not define."
  '{:graph      #{-node? -datums -any-node? -depth -premise? -supports -dependents
                  -support-count -dependent-count
                  -justification -justifications -ensure-node -add-premise
                  -suspend-premise -add-justification -retract -sweep -drop-justification
                  -relabel}
    :attribute  #{-premise-strength -restrength-informant -forced? -forced-members -set-forced}
    :blocked    #{-blocked -set-blocked}
    :superseded #{-superseded -supersede}
    :output     #{-believed? -believed -any-belief? -defeat-class -snapshot}
    :touched    #{-touched -touched-in -touched-new -touched-out -touched-down -touched-up -reset-touched
                  -touch-mark -touched-since}
    :hold       #{-hold -release -held}})
