;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.wff
  "Well-formedness checks for the special predicates: genl / genlContext (the type and
  context hierarchies), disjoint / disjointMetatype, and argIsa (argument types).
  Each returns a seq of problem strings; `assert` throws if any are present.
  Ordinary sentences are checked for argument *types* by checks/constraint-checks.

  The per-functor check fns are defined here; **which functor gets which check is
  not** — that dispatch is one arm of the special-predicate table in
  `vaelii.impl.special`, so the functor enumeration lives in exactly one place and
  a predicate added to the table without a `:wff` arm is visibly missing rather
  than silently unchecked.  `special/wff-problems` is the walk.

  Plus one check that is about a *rule set* rather than a sentence:
  `negation-cycle` finds the cycle through negation that an `exceptWhen` exception
  closes.  Two things can close one — a rule arriving, and a `genl` edge arriving
  underneath rules already stored — and `checks` runs the search on both paths (see
  the section at the bottom, and docs/exceptions.md)."
  (:require [clojure.string :as str]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.rewrite :as rewrite]
            [vaelii.impl.taxonomy :as tax]))

;; The cycle and overlap checks below read the **global** closure deliberately.  A
;; cycle is a property of the whole edge set: a check narrowed to some context's
;; visible edges would admit an edge that is cyclic globally, and a `genl` cycle is
;; something the taxonomy is entitled to assume it does not have.  The overlap check
;; is the same story one step out: `disjoint` of genl-related types is contradictory
;; wherever the edge path exists, not merely where it is visible.
;;
;; **`genlContext` is the exception, and deliberately.**  A cycle between types says
;; two types are coextensive — a claim about terms, which is what the equality
;; partition is for, and which would make a `disjoint` pair disjoint from itself.  A
;; cycle between *contexts* says only that each sees the other, which is a claim
;; `genlMt` makes routinely (OpenCyc states 49 of them, one of them BaseKB's own
;; component) and which reachability answers perfectly well: the taxonomy keeps its
;; potential over the condensation, so a cycle costs a component rather than
;; soundness.  Merging the contexts instead would be the stronger claim — a context
;; is where a sentex is *stored*, not only what it can see — and would throw away
;; which context an assertion was made in.  See docs/contexts.md.

(defn genl-problems [tax [_ sub super :as s]]
  (cond-> []
    (not= 3 (count s))     (conj "genl takes two arguments")
    (nm/individual? sub)   (conj (str sub " is an individual; genl relates types"))
    (nm/individual? super) (conj (str super " is an individual; genl relates types"))
    (= sub super)          (conj (str sub " genl itself"))
    (and (not= sub super) (tax/genl? tax super sub))
    (conj (str "genl " sub " " super " creates a cycle (" super
               " is already a subtype of " sub ")"))))

(defn genlContext-problems [_tax [_ sub super :as s]]
  (cond-> []
    (not= 3 (count s))        (conj "genlContext takes two arguments")
    (not (nm/context? sub))   (conj (str sub " is not a context (must end in Context)"))
    (not (nm/context? super)) (conj (str super " is not a context (must end in Context)"))
    ;; a self-edge is refused because it claims nothing: the closure is reflexive, so
    ;; the edge was already true before it arrived.  A longer cycle *is* a claim
    ;; (mutual visibility) and is admitted — see the note above.
    (= sub super)             (conj (str sub " genlContext itself"))))

(defn disjoint-problems [tax [_ a b :as s]]
  (cond-> []
    (not= 3 (count s))  (conj "disjoint takes two arguments")
    (nm/individual? a)  (conj (str a " is an individual; disjoint relates types"))
    (nm/individual? b)  (conj (str b " is an individual; disjoint relates types"))
    (= a b)             (conj (str a " disjoint with itself"))
    (and (not= a b) (or (tax/genl? tax a b) (tax/genl? tax b a)))
    (conj (str a " and " b " are genl-related, so they overlap and can't be disjoint"))))

(defn disjointMetatype-problems [_ [_ m :as s]]
  (cond-> []
    (not= 2 (count s)) (conj "disjointMetatype takes one argument")
    (nm/individual? m) (conj (str m " is an individual; disjointMetatype marks a metatype"))))

(defn arg-constraint-problems
  "`argIsa` and `argGenl` — the two argument constraints — are structurally identical:
  a predicate, a positive-integer position, and a type.  They differ only in what
  they *demand* of the argument sitting there, which is `checks`' business, not this
  one's, so one check serves both and reads the functor out of the sentence for its
  messages.  Stating it twice would let the two drift.

  **The constrained relation is not held to a spelling.**  A *function* has argument
  positions exactly as a predicate does — `(argIsa Milli 1 unit_of_measure_no_prefix)`
  says what the argument of a NAT `(Milli Meter)` must be, which is the same kind of
  claim `resultIsa` makes about its result — and a function is CapitalCamelCase, which
  is also how an individual is spelled.  So no spelling test can separate the relation
  this check wants to admit from the term it would want to refuse, and refusing on the
  capital costs the whole vocabulary of function argument types.  The position and the
  *type* argument are still checked, because those are decidable from the sentence.
  A constraint on a term that never heads a sentence is inert, which is the cheaper
  side of the open-world trade this project takes everywhere else.

  A relation may also be **denoted rather than named** — `(argIsa (TypeCapableFn
  skillCapableOf) 1 intelligent_agent)` constrains the relation that NAT denotes — so a
  non-atomic term is a first argument too.  What is left to refuse is a first argument
  that is no kind of term at all: a number, a string, a keyword."
  [_ [f pred n type :as s]]
  (cond-> []
    (not= 4 (count s))    (conj (str f " takes three arguments"))
    (not (or (symbol? pred) (sequential? pred)))
    (conj (str f " constrains a relation, which is named by a symbol or denoted by a"
               " non-atomic term; " (pr-str pred) " is neither"))
    (not (and (integer? n) (pos? n))) (conj (str f " position must be a positive integer"))
    (nm/individual? type) (conj (str type " is an individual; " f " expects a type"))))

(defn inter-arg-constraint-problems
  "`interArgIsa` — the conditional argument constraint: a predicate, a trigger position
  and type, and a target position and type.  `(interArgIsa eats 1 carnivore 2 meat)`.

  The same latitude on the constrained relation `arg-constraint-problems` argues for, and
  for the same reasons: a function has argument positions too, and a relation may be
  denoted by a non-atomic term rather than named.  Both positions and both types are
  checked, since those are decidable from the sentence.

  **The two positions may be the same.**  `(interArgIsa P 1 dog 1 mammal)` says a first
  argument that is a dog is also a mammal — the awkward spelling of a `genl` edge, but a
  true claim the check will enforce, so there is nothing here to refuse.  What the
  positions may not be is absent or non-positive."
  [_ [f pred n type m utype :as s]]
  (cond-> []
    (not= 6 (count s))    (conj (str f " takes five arguments"))
    (not (or (symbol? pred) (sequential? pred)))
    (conj (str f " constrains a relation, which is named by a symbol or denoted by a"
               " non-atomic term; " (pr-str pred) " is neither"))
    (not (and (integer? n) (pos? n)))
    (conj (str f " trigger position must be a positive integer"))
    (not (and (integer? m) (pos? m)))
    (conj (str f " target position must be a positive integer"))
    (nm/individual? type)  (conj (str type " is an individual; " f " expects a type"))
    (nm/individual? utype) (conj (str utype " is an individual; " f " expects a type"))))

(defn arg-preserving-problems
  "`argPreserving` / `argPreservingInverse` — a predicate, a positive-integer
  position, and the relation the argument is preserved along.  Structurally the arg
  constraints' shape, plus the one restriction that is the whole point of the
  declaration: **the relation must be transitive.**

  `vaelii.impl.inherit` walks the named relation to a fixpoint, so a declaration over
  a relation nobody said composes gets transitivity manufactured for it — two hops of
  `begat` licensing a claim that only one hop was ever evidence for.  An `argIsa` on
  argument 3 cannot express that: argIsa is open-world, so it bites only for a
  relation that happens to carry some *other* type and waves through the one that
  carries none, which is the common authoring order (name the relation, type it
  later).  So it is refused here, where the other special predicates' structural
  rules live, and refused identically either way.

  The fix for a refusal is to declare `(transitive R)` first — or to name one of the
  two hierarchies the engine closes itself (`inherit/virtual-relations`).

  The **inheriting** relation is held to what `arg-constraint-problems` holds its own
  first argument to, and for the same reasons: a function is spelled like an
  individual, a relation may be denoted by a NAT rather than named, and a declaration
  about a term that never heads a sentence is inert.  Refusing the CapitalCamelCase
  spelling while admitting the NAT — which is what a `nm/individual?` test does, since
  a compound is not an individual — refuses the conventional spelling and waves the
  exotic one through.  The **preserved-along** relation is stricter, and stays a
  symbol: `fact-reach` walks it by building `(R x ?v)`, which a non-atomic term does
  not make a sentence of, and `usable-relation?` has no transitivity to read off one."
  [tax [f pred n rel :as s]]
  (cond-> []
    (not= 4 (count s))    (conj (str f " takes three arguments"))
    (not (or (symbol? pred) (sequential? pred)))
    (conj (str f " is about a relation, which is named by a symbol or denoted by a"
               " non-atomic term; " (pr-str pred) " is neither"))
    (not (and (integer? n) (pos? n))) (conj (str f " position must be a positive integer"))
    (not (symbol? rel))   (conj (str f " preserves an argument along a relation named by"
                                     " a symbol; " (pr-str rel) " is not one"))
    ;; unscoped on purpose: the structural check asks whether the relation is
    ;; *declared* transitive anywhere, so a declaration whose transitivity lives in a
    ;; context this writer cannot see is still admitted.  What that writer may do with
    ;; it is decided at read time, where `inherit/positions` re-asks from the asking
    ;; context and drops a licence it cannot see.
    (and (symbol? rel) (not (inherit/usable-relation? tax rel nil)))
    (conj (str rel " is not transitive, and " f " walks the relation it names to a"
               " fixpoint — declare (transitive " rel ") before the preservation, or"
               " name one of " (str/join " / " (sort inherit/virtual-relations))))))

(defn prop-problems [_ [f pred :as s]]
  (cond-> []
    (not= 2 (count s))    (conj (str f " takes one argument"))
    (nm/individual? pred) (conj (str pred " is an individual; " f " marks a predicate"))))

;; ---- equality: rewriteOf / sameAs / equals / different -------------------
;; See docs/equality.md.  Three assertable relations feed one closure and one
;; unassertable one reads it.

(defn- rewrite-reaches?
  "Is `to` reachable from `from` along the active `[preferred dispreferred]` claims?
  Adding `(rewriteOf P D)` closes a cycle exactly when `P` is already reachable from
  `D`, which is the multi-edge case a pairwise `(rewriteOf D P)` test would miss."
  [prefs from to]
  (let [out (reduce (fn [m [p d]] (update m p (fnil conj #{}) d)) {} prefs)]
    (loop [seen #{}, stack [from]]
      (when-let [n (peek stack)]
        (cond
          (= n to)     true
          (seen n)     (recur seen (pop stack))
          :else        (recur (conj seen n) (into (pop stack) (get out n #{}))))))))

(defn- rewrite-role
  "The syntactic role of a `rewriteOf` argument, for the same-role check.  A merge
  across incompatible roles is a likely import bug, so it is refused:

    :individual   CapitalCamelCase (Muffet, Tom)
    :predicate    interior uppercase ⇒ camelCase (bornIn, parentOf)
    :type         underscore ⇒ snake_case (physical_object)
    :either       a bare lowercase word (dog, canine) — a type *or* a predicate,
                  ambiguous by syntax alone, so compatible with both
    :opaque       a **namespaced** symbol — an identity the engine minted rather than
                  a name anybody wrote, so it has no spelling to read a role off

  `:either` accepts either non-individual partner; the guard that bites is
  individual-with-non-individual (merging `Muffet` into `dog`) and clearly-camelCase
  predicate with clearly-snake_case type (`parentOf` into `physical_object`).  The
  predicate/type split reads off `naming`: a camelCase predicate is not a valid
  snake_case type (the interior uppercase), and vice versa; a bare lowercase word
  satisfies both, so it is `:either`.

  `:opaque` clashes with nothing, and has to: the naming invariants are conventions
  over names a person chose, and a reified NAT constant (docs/nat.md) is minted.  What
  it denotes is settled by the result types materialized on it, so merging one into the
  real term its function's corresponding predicate names is the intended move, not the
  import bug this check exists to catch."
  [x]
  (cond
    (namespace x)                                   :opaque
    (nm/individual? x)                              :individual
    (and (nm/predicate? x) (not (nm/type-symbol? x))) :predicate
    (and (nm/type-symbol? x) (not (nm/predicate? x))) :type
    :else                                          :either))

(defn- roles-clash?
  "Do two `rewriteOf` roles name incompatible kinds — one an individual and the other
  not, or one a predicate and the other a type?  `:either` clashes with neither
  non-individual role, and `:opaque` with none at all."
  [ra rb]
  (and (not= :opaque ra) (not= :opaque rb)
       (or (not= (= :individual ra) (= :individual rb))
           (= #{:predicate :type} (hash-set ra rb)))))

(defn function-decl-problems
  "`reifiableFunction` / `unreifiableFunction` declare a NAT function's kind.  Their
  one argument is a *function name* — a `FruitFn`-shaped constant, which reads as an
  individual by the naming invariants, so `prop-problems` (which refuses an
  individual) is the wrong check.  All that matters here is the arity and that the
  name is a symbol."
  [_ [f fname :as s]]
  (cond-> []
    (not= 2 (count s))    (conj (str f " takes one argument"))
    (not (symbol? fname)) (conj (str f " expects a function name (a symbol)"))))

(defn correspondence-problems
  "`(functionCorrespondingPredicate F P N)` says the function `F` and the predicate `P`
  state the same relationship, `N` naming the argument of `P` that carries `F`'s value.

  `F` is a function name — a `MotherFn`-shaped constant, an individual by the naming
  invariants — so the individual refusal falls on `P` alone.  `N` is optional and
  1-based; omitted, the value takes `P`'s last argument, which is the shape nearly
  every correspondence has.  Whether `N` is in range is not knowable here: it is
  checked against the *application*'s arity, which no declaration states."
  [_ [f fname pred pos :as s]]
  (cond-> []
    (not (<= 3 (count s) 4))
    (conj (str f " takes a function, a predicate, and optionally an argument position"))
    (not (symbol? fname)) (conj (str f " expects a function name (a symbol)"))
    (not (symbol? pred))  (conj (str f " expects a predicate name (a symbol)"))
    (nm/individual? pred) (conj (str pred " is an individual; " f " names the predicate "
                                     fname " corresponds to"))
    (and (= 4 (count s)) (not (and (integer? pos) (pos? pos))))
    (conj (str f "'s argument position must be a positive integer"))))

(defn equality-problems
  "`rewriteOf` / `sameAs` / `equals` relate **symbols**: the closure is a partition
  over terms, so a compound argument is refused — with two carve-outs, one for each
  kind of compound equality that *does* reduce to machinery that exists.

  * `(rewriteOf T E)` with a **compound** `E` is not term equality at all — it is a
    NAT reify-to-term declaration (docs/nat.md), whose second argument is a quoted NAT
    expression, not a term to merge.  Waved through (only the target `T` need be a
    symbol) and skipped by the equality integrate arm.

  * `(equals L R)` with a **variable-bearing** compound side is a **schematic
    equational rule** — an oriented rewrite `fatherOf∘fatherOf → grandfatherOf`, not a
    merge (docs/equality.md, symbolic equational reasoning).  Its sides are compounds
    by design, so the compound refusal is waived; instead it must be **orientable**
    into a terminating rewrite (`rewrite/orient`), or it is refused here before
    anything is stored.  A ground `(equals (F a) (F b))` is *not* schematic — it
    reifies to symbols first (docs/nat.md) — and a compound that reifies to no symbol
    (a structural NAT measure) still hits the refusal below.

  `rewriteOf` carries two further restrictions.  It is directional, so a self-edge
  (the degenerate cycle, and what a sloppy import pipeline actually emits) and a
  longer cycle both leave the class with no head and are refused like a `genl`
  cycle.  And **both sides must be the same role** — predicate-with-predicate,
  type-with-type, individual-with-individual (`roles-clash?`): rewriting a term of
  one kind into another is meaningless (merging `Muffet` into `dog`) and a likely
  import bug.  Unlike round one, a predicate or a type *is* now a legal `rewriteOf`
  target — the merge moves its trie keys, functor root, rule-index postings and
  `genl` closure with it (docs/equality.md).  `sameAs` / `equals` stay
  individuals-only (OWL); `rewriteOf` is the spelling relation, so it is the one
  that carries vocabulary alignment across predicates and types.  `(sameAs A A)` is
  fine — OWL makes `sameAs` reflexive."
  [tax [f a b :as s]]
  (cond
    (and (= f 'rewriteOf) (sequential? b))
    (cond-> []
      (not= 3 (count s))   (conj "rewriteOf takes two arguments")
      (not (symbol? a))    (conj (str (pr-str a) " must be a term (rewriteOf-to-NAT target)")))

    (rewrite/schematic-equation? s)
    (cond-> []
      (nil? (rewrite/orient a b))
      (conj (str "cannot orient " (pr-str s) " into a terminating rewrite:"
                 " it is permutative (no term order can orient it), or a side carries"
                 " a variable the other lacks")))

    :else
    (cond-> []
      (not= 3 (count s))  (conj (str f " takes two arguments"))
      (sequential? a)     (conj (str (pr-str a) " is a compound; " f " relates symbols"))
      (sequential? b)     (conj (str (pr-str b) " is a compound; " f " relates symbols"))
      (and (= f 'rewriteOf) (= a b))
      (conj (str a " rewriteOf itself"))
      (and (= f 'rewriteOf) (symbol? a) (symbol? b)
           (roles-clash? (rewrite-role a) (rewrite-role b)))
      (conj (str "rewriteOf " a " " b " crosses roles (" (name (rewrite-role a)) " vs "
                 (name (rewrite-role b)) "); it merges same-role terms — predicate with"
                 " predicate, type with type, individual with individual"))
      (and (= f 'rewriteOf) (not= a b) (rewrite-reaches? (tax/equality-prefs tax) b a))
      (conj (str "rewriteOf " a " " b " creates a cycle (" a
                 " is already rewritten away from " b ")")))))

(defn different-problems
  "`different` is **not assertible**.  It is negation as failure over the equality
  closure, answered by a prover and never stored: an assertible one would be OWL's
  `differentFrom`, a positive commitment that a later `sameAs` would contradict, and
  docs/equality.md deliberately does not build it.  Stored as a premise it would also
  be silently ignored, since the prover is authoritative and never reads facts."
  [_ [_ & args]]
  [(str "different is not assertible: it is answered from the equality closure"
        " (a positive commitment that two terms differ would be OWL's differentFrom,"
        " which vaelii does not build) — ask it instead: (ask? kb '(different "
        (str/join " " args) "))")])

(defn naf-problems
  "`unknown`, `thereExists` and the five **aggregates** are **not assertible**.  They
  are query operators — closed-world negation, existential closure, and a reduction
  over a query's solutions — answered by a prover and never stored (docs/naf.md,
  docs/aggregate.md).  `(unknown S)` states no fact: it is a *test* on what the KB
  derives, so stored as a premise it would be a fact with a made-up predicate that
  nothing consults.  `(agg/count 3 ?v S)` states no fact for the sharper reason
  that it states a *stale* one: a count is a function of what is believed now, so
  storing one would put a computed value under truth maintenance with no way to
  invalidate it (docs/aggregate.md, \"Query-only\").  Belongs in a rule antecedent or
  a query goal, not an assertion."
  [_ [f & _args]]
  [(str f " is not assertible: it is a query operator answered by a prover, not a fact"
        " to store — use it in a rule antecedent or ask it, e.g. (ask? kb '(" f " ...))")])

(defn inverse-problems [_ [_ p q :as s]]
  (cond-> []
    (not= 3 (count s)) (conj "inverse takes two arguments")
    (nm/individual? p) (conj (str p " is an individual; inverse relates predicates"))
    (nm/individual? q) (conj (str q " is an individual; inverse relates predicates"))))

;; (Per-functor well-formedness dispatch lives in the `:wff` column of the table in
;; `vaelii.impl.special`, read back through `special/wff-problems` — one enumeration
;; of the special functors, rather than a separate `case` here that a newly added
;; functor could silently miss, leaving it well-formed by omission.)

;; ---- stratification: no cycle through negation ---------------------------
;;
;; `exceptWhen` is negation as failure: asserting a fact can *withdraw* a
;; conclusion.  If one rule's exception depends on what another rule concludes and
;; that rule's exception depends on what the first concludes, the program has a
;; cycle through negation.  Such a program admits zero or several stable models,
;; and which one you land in depends on the order knowledge arrived — which breaks
;; the order-independence invariant docs/nmtms.md makes non-negotiable.  Level 6
;; (no rule backchaining) bounds an exception's *query*, not this: an exception
;; reads forward-derived stored facts, so a cycle across two rules is still
;; constructible.  So the cycle is refused at assert time, here, beside the genl
;; cycle check.
;;
;; Both kinds of outgoing edge fan out over the genl **spec** closure, so a taxonomy
;; edge is as capable of closing a cycle as a rule is — an exception on `flightless`
;; is reached by a stored `(penguin Opus)` the moment `(genl penguin flightless)`
;; holds.  `negation-cycle` is therefore run from two places in `core`: from the
;; rule being asserted, and — when a genl / genlContext edge arrives — from each
;; stored rule carrying an exception, against a taxonomy with the edge added.  The
;; search itself does not care which; it is told a start node and a taxonomy.
;;
;; The dependency graph has two kinds of node and two kinds of edge:
;;
;;   rule R --depends-on--> P     P appears in R's antecedents        (positive)
;;   rule R --excepts-on--> P     R's exception mentions P            (negative)
;;   P --concluded-by--> rule R   R concludes P                       (positive)
;;
;; A cycle crossing **at least one** negative edge is rejected.  A purely positive
;; cycle is ordinary recursion, which the engine supports and bounds by depth, and
;; is deliberately left alone.

(defn- rule-edges
  "The edges out of a rule node, as `[edge predicate]` pairs.

  Both sides fan out over the genl **spec** closure, because predicate dependence
  is not literal: an antecedent `(animal ?x)` is satisfied by a stored
  `(dog Muffet)`, and an exception on `flightless` by a stored `(penguin Opus)` when
  `(genl penguin flightless)`.  This is the fan-out matching does and the one
  `special/recheck-on-predicate` keys the exception trigger on, read in the same
  direction; a cycle that exists only through a subtype has to be caught.
  Expanding the *consuming* side downwards is equivalent to expanding the
  producing side upwards, so the consequent is looked up literally.

  Over-approximation is the safe side here: rejecting a stratified program is
  annoying, accepting an order-dependent one is a correctness hole.  The spec
  closure is the **global** one for the same reason — a context-narrowed fan would
  under-approximate the graph and admit an unstratified rule set."
  [tax {:keys [antecedent-preds exception-preds]}]
  (concat (for [p antecedent-preds, s (tax/specs tax p)] [:depends-on s])
          (for [p exception-preds,  s (tax/specs tax p)] [:excepts-on s])))

(defn negation-cycle
  "Search the rule dependency graph for a cycle through negation created by adding
  rule node `rule`, and describe it — a vector of strings naming the nodes and
  edges around the cycle — or nil if there is none.

  A rule node is `{:id :label :antecedent-preds :exception-preds}`; `concluders`
  maps a predicate to the rule nodes concluding it, and must include `rule` itself
  under its own consequent, since a rule being asserted is not stored yet and a
  self-referential exception (a rule excepting on what it concludes) is exactly a
  one-rule cycle.

  Only cycles through `rule` are looked for.  Every rule assert and every genl edge
  assert runs this check, so the stored graph is already free of them and whatever
  is being added can only close a cycle that passes through it.  For a *rule* that
  start node is the rule itself; for a *taxonomy edge*, which passes through no
  single rule, the caller starts the walk at each rule carrying an exception —
  complete, because every cycle through negation crosses a negative edge and
  negative edges leave excepted rules only.

  The search state is `[rule negative?]` rather than the rule alone: a node reached
  with and without a negative edge behind it are different states, since only the
  negative one closes a bad cycle — that is what keeps positive recursion (which
  reaches the start with `negative?` false, and stops there) accepted.  Rules are
  few, so a plain DFS with no cleverness is right."
  [tax concluders rule]
  (let [start (:id rule)
        step  (fn [[node negative? path]]
                (for [[edge pred] (rule-edges tax node)
                      next-rule   (concluders pred)]
                  [next-rule
                   (or negative? (= :excepts-on edge))
                   (conj path (str (name edge) " " pred) (:label next-rule))]))]
    (loop [frontier [[rule false [(:label rule)]]]
           seen     #{[start false]}]
      (when-let [state (peek frontier)]
        (let [nexts (step state)]
          (if-let [hit (first (filter (fn [[r neg? _]] (and neg? (= start (:id r)))) nexts))]
            (nth hit 2)
            (let [fresh (remove (fn [[r neg? _]] (seen [(:id r) neg?])) nexts)]
              (recur (into (pop frontier) fresh)
                     (into seen (map (fn [[r neg? _]] [(:id r) neg?])) fresh)))))))))

(defn cycle-description
  "Render a `negation-cycle` path as one line, for an error message."
  [cycle]
  (str/join " -> " cycle))
