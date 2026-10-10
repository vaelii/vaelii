;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.wff
  "Well-formedness checks for the special predicates: genl / genlCx (the type and
  context hierarchies), disjoint / disjoint_metatype, and arg (argument types).
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

;; The cycle check below reads the **global** closure deliberately.  A cycle is a
;; property of the whole edge set: a check narrowed to some context's visible edges
;; would admit an edge that is cyclic globally, and a `genl` cycle is something the
;; taxonomy is entitled to assume it does not have.
;;
;; No check here reads a `genl` edge to refuse a `disjoint` or a cover.  A declaration
;; over two `genl`-related types, or a cover naming a part disjoint from its whole, is
;; stored like any other declaration, and the clash it forms with the edge is `settle`'s
;; to report (docs/nmtms.md, "What a refusal may rest on").
;;
;; **`genl` and `genlCx` cycles are both refused, and read the global closure the
;; same way.**  A `genl` cycle claims two types are coextensive — a claim about
;; terms the equality partition owns, and one that would make a `disjoint` pair
;; disjoint from itself.  A `genlCx` cycle claims two contexts see each other, which
;; is well defined — the taxonomy holds one over its condensation, so a cycle costs a
;; component rather than soundness — and is refused anyway, so the context hierarchy
;; is a partial order like the type hierarchy.  `recovery/recover` still replays a
;; stored cycle an older or foreign writer left, past this check, and the taxonomy
;; condenses it.  See docs/contexts.md.

(defn genl-problems [tax [_ sub super :as s] _context]
  (cond-> []
    (not= 3 (count s))     (conj "genl takes two arguments")
    (nm/individual? sub)   (conj (str sub " is an individual; genl relates types"))
    (nm/individual? super) (conj (str super " is an individual; genl relates types"))
    (= sub super)          (conj (str sub " genl itself"))
    (and (not= sub super) (tax/genl?-global tax super sub))
    (conj (str "genl " sub " " super " creates a cycle (" super
               " is already a subtype of " sub ")"))))

(defn genlCx-problems [tax [_ sub super :as s] _context]
  (cond-> []
    (not= 3 (count s))        (conj "genlCx takes two arguments")
    (not (nm/context? sub))   (conj (str sub " is not a context (must start with Cx)"))
    (not (nm/context? super)) (conj (str super " is not a context (must start with Cx)"))
    ;; A **query context** spells like a context and is not one: it names a way of
    ;; reading, is resolved at the read entry point and never reaches the engine
    ;; (`nm/query-contexts`).  An edge naming one would be the only way to give it a
    ;; place in the lattice, which is exactly what must not exist — `CxNothing` sees
    ;; nothing *because* nothing wires it, and `CxEverything` / `CxInference` would
    ;; start inheriting facts they are supposed to read past rather than from.
    (nm/query-context? sub)   (conj (str sub " is a query context, not a place in the "
                                         "hierarchy — nothing may genlCx it"))
    (nm/query-context? super) (conj (str super " is a query context, not a place in the "
                                         "hierarchy — nothing may genlCx it"))
    ;; a self-edge is refused because it claims nothing: the closure is reflexive, so
    ;; the edge was already true before it arrived.  A longer cycle is refused too, so
    ;; the context hierarchy is a partial order — the note above gives the reasoning.
    (= sub super)             (conj (str sub " genlCx itself"))
    (and (not= sub super) (tax/genlCx?-global tax super sub))
    (conj (str "genlCx " sub " " super " creates a cycle (" super
               " already sees " sub ")"))))

(defn disjoint-problems [_ [_ a b :as s] _context]
  (cond-> []
    (not= 3 (count s))  (conj "disjoint takes two arguments")
    (nm/individual? a)  (conj (str a " is an individual; disjoint relates types"))
    (nm/individual? b)  (conj (str b " is an individual; disjoint relates types"))
    (= a b)             (conj (str a " disjoint with itself"))))

(defn covering-problems
  "`covering` and `partition` — a whole followed by two or more distinct parts.

  What is checked is what the declaration *cannot* mean.  A missing `(genl part whole)`
  edge is not among it: the declaration states that edge rather than requiring one, so
  demanding it here would refuse every cover written before its parts and make the answer
  a function of assertion order.  What is refused is a shape no edge could be installed
  for — a part that is the whole, and a part the closure already places above the whole,
  where the edge would close a cycle `genl-problems` refuses in as many words.  A part
  disjoint from the whole is stored, and the clash is reported (the header note).

  The cycle read is global, as `genl-problems`' is (E17_ROSTER): the edge the cover
  installs closes a cycle in the whole edge set whichever context holds the edge above
  it, so a part a sibling context places above the whole is refused here as the bare
  `genl` would be."
  [tax [f whole & parts :as s] _context]
  (cond-> []
    ;; four elements: the functor, the whole, and two parts.  One part covering a whole
    ;; says only that the two have the same instances, which `genl` in both directions
    ;; already says.
    (< (count s) 4)
    (conj (str f " takes a whole and at least two parts"))

    (nm/individual? whole)
    (conj (str whole " is an individual; " f " relates types"))

    (some nm/individual? parts)
    (conj (str (first (filter nm/individual? parts)) " is an individual; " f
               " relates types"))

    (not= (count parts) (count (distinct parts)))
    (conj (str f " names a part twice; each part covers a different piece of " whole))

    (some #(= % whole) parts)
    (conj (str whole " is named as a part of itself"))

    (some #(and (not= % whole) (tax/genl?-global tax whole %)) parts)
    (conj (str (first (filter #(and (not= % whole) (tax/genl?-global tax whole %)) parts))
               " is already a supertype of " whole ", so it cannot be a part of it"))))

(defn disjoint-metatype-problems [_ [_ m :as s] _context]
  (cond-> []
    (not= 2 (count s)) (conj "disjoint_metatype takes one argument")
    (nm/individual? m) (conj (str m " is an individual; disjoint_metatype marks a metatype"))))

(defn sibling-disjoint-problems [_ [_ c :as s] _context]
  (cond-> []
    (not= 2 (count s)) (conj "sibling_disjoint takes one argument")
    (nm/individual? c) (conj (str c " is an individual; sibling_disjoint marks a collection"))))

(defn type-pair-problems
  "`(orthogonal a b)` and `(siblingDisjointException a b)` — two arguments, neither an
  individual.  One type named twice is not refused here: a type subsumes itself, so the
  declaration contradicts the taxonomy, and `decide.related` reports that clash as it
  reports one over two genl-related types."
  [_ [f a b :as s] _context]
  (cond-> []
    (not= 3 (count s)) (conj (str f " takes two arguments"))
    (nm/individual? a) (conj (str a " is an individual; " f " relates types"))
    (nm/individual? b) (conj (str b " is an individual; " f " relates types"))))

(defn arg-constraint-problems
  "`arg` and `genlArg` — the two argument constraints — are structurally identical:
  a predicate, a positive-integer position, and a type.  They differ only in what
  they *demand* of the argument sitting there, which is `checks`' business, not this
  one's, so one check serves both and reads the functor out of the sentence for its
  messages.  Stating it twice would let the two drift.

  **The constrained relation is not held to a spelling.**  A *function* has argument
  positions exactly as a predicate does — `(arg Milli 1 unit_of_measure_no_prefix)`
  says what the argument of a NAT `(Milli Meter)` must be, which is the same kind of
  claim `result` makes about its result — and a function is CapitalCamelCase, which
  is also how an individual is spelled.  So no spelling test can separate the relation
  this check wants to admit from the term it would want to refuse, and refusing on the
  capital costs the whole vocabulary of function argument types.  The position and the
  *type* argument are still checked, because those are decidable from the sentence.
  A constraint on a term that never heads a sentence is inert, which is the cheaper
  side of the open-world trade this project takes everywhere else.

  A relation may also be **denoted rather than named** — `(arg (TypeCapableFn
  skillCapableOf) 1 intelligent_agent)` constrains the relation that NAT denotes — so a
  non-atomic term is a first argument too.  What is left to refuse is a first argument
  that is no kind of term at all: a number, a string, a keyword."
  [_ [f pred n type :as s] _context]
  (cond-> []
    (not= 4 (count s))    (conj (str f " takes three arguments"))
    (not (or (symbol? pred) (sequential? pred)))
    (conj (str f " constrains a relation, which is named by a symbol or denoted by a"
               " non-atomic term; " (pr-str pred) " is neither"))
    (not (and (integer? n) (pos? n))) (conj (str f " position must be a positive integer"))
    (nm/individual? type) (conj (str type " is an individual; " f " expects a type"))))

(defn inter-arg-constraint-problems
  "`interArg` — the conditional argument constraint: a predicate, a trigger position
  and type, and a target position and type.  `(interArg eats 1 carnivore 2 meat)`.

  The same latitude on the constrained relation `arg-constraint-problems` argues for, and
  for the same reasons: a function has argument positions too, and a relation may be
  denoted by a non-atomic term rather than named.  Both positions and both types are
  checked, since those are decidable from the sentence.

  **The two positions may be the same.**  `(interArg P 1 dog 1 mammal)` says a first
  argument that is a dog is also a mammal — the awkward spelling of a `genl` edge, but a
  true claim the check will enforce, so there is nothing here to refuse.  What the
  positions may not be is absent or non-positive."
  [_ [f pred n type m utype :as s] _context]
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

(defn covering-constraint-problems
  "The covering argument constraints — `args` / `argsGenl` name a relation and a type,
  `argAndRest` / `argAndRestGenl` a relation, a positive-integer start position, and a
  type.  The same latitude on the constrained relation `arg-constraint-problems` argues
  for, and the same position and type checks, differing only in whether a start position
  is present.  `args` is `argAndRest` at start 1, so one check reads both arities and
  takes the type from whichever position holds it.

  The homogeneity constraints `interArgs` / `interArgAndRest` have the same two shapes —
  a relation and a type, or a relation, a start and a type — and are read here too."
  [_ [f pred a b :as s] _context]
  (let [tail? (contains? '#{argAndRest argAndRestGenl interArgAndRest} f)
        type  (if tail? b a)
        start a]
    (cond-> []
      (not= (if tail? 4 3) (count s))
      (conj (str f " takes " (if tail? "three" "two") " arguments"))
      (not (or (symbol? pred) (sequential? pred)))
      (conj (str f " constrains a relation, which is named by a symbol or denoted by a"
                 " non-atomic term; " (pr-str pred) " is neither"))
      (and tail? (not (and (integer? start) (pos? start))))
      (conj (str f " start position must be a positive integer"))
      (nm/individual? type) (conj (str type " is an individual; " f " expects a type")))))

(defn arg-preserving-problems
  "`transitiveInArg` / `transitiveInArgInverse` — a predicate, a positive-integer
  position, and the relation the argument is preserved along.  Structurally the arg
  constraints' shape, plus the one restriction that is the whole point of the
  declaration: **the relation must be transitive.**

  `vaelii.impl.inherit` walks the named relation to a fixpoint, so a declaration over
  a relation nobody said composes gets transitivity manufactured for it — two hops of
  `begat` licensing a claim that only one hop was ever evidence for.  An `arg` on
  argument 3 cannot express that: arg is open-world, so it bites only for a
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
  [tax [f pred n rel :as s] _context]
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

(defn- position-mark-problems
  "The problems of a `(Mark P n)` declaration naming a predicate and one argument
  position, the refusal saying the mark marks a `noun`."
  [noun [f pred n :as s]]
  (cond-> []
    (not= 3 (count s))    (conj (str f " takes two arguments"))
    (nm/individual? pred) (conj (str pred " is an individual; " f " marks a " noun))
    (not (and (integer? n) (pos? n)))
    (conj (str f " position must be a positive integer"))))

(defn functional-in-arg-problems
  "`functionalInArg` — a predicate and a positive-integer position, and nothing else.

  `arg-preserving-problems` above is the near neighbour and the difference is the third
  argument it has and this does not: `transitiveInArg` names a relation the argument is
  preserved *along*, and has to refuse a non-transitive one because `inherit` would walk
  it to a fixpoint and manufacture transitivity for it. `functionalInArg` licenses
  nothing and walks nothing — it refuses tuples — so there is no relation to name and no
  such restriction to impose. The two share a name shape and sit on opposite sides of
  the prover/checker divide; `props-over`'s docstring draws the same line.

  The position is held to a **positive** integer for the reason
  `arg-preserving-problems` holds its own: argument positions are one-based throughout,
  so `(functionalInArg P 0)` names no slot. That an `n` exceeding the predicate's
  declared arity is not refused here is deliberate and matches `arity`'s own
  open-worldness — the declaration may legitimately arrive before the arity does, and a
  position past the end simply never matches a tuple.

  The predicate is held to what `prop-problems` holds its subject to rather than to
  `arg-preserving-problems`' looser symbol-or-compound test: this mark is read off a
  sentence's functor, and a functor is a symbol."
  [_ s _context]
  (position-mark-problems "predicate" s))

(defn commutative-in-arg-and-rest-problems
  "`commutativeInArgAndRest` — a predicate and a positive-integer position, and nothing
  else.  `functional-in-arg-problems` above is the shape, and the position is held to the
  same positive integer for the same reason: argument positions are one-based throughout,
  so position 0 names no slot.

  **A position past the predicate's declared arity is not refused**, exactly as
  `functionalInArg`'s is not.  The declaration may legitimately arrive before the arity
  does, so refusing it against a visible arity would make the KB depend on which of the
  two was written first — and a tail starting past the end simply forms no component, so
  a literal at that arity is left alone (`sentex/commuting-components`).  The refusal
  says the mark marks a relation, since a commuting mark may name a function."
  [_ s _context]
  (position-mark-problems "relation" s))

(defn commutative-in-args-problems
  "`commutativeInArgs` — a predicate and at least two distinct positive-integer
  positions.

  **Two positions, not one.**  A component of one position licences no permutation, so a
  one-position declaration would be stored, believed and inert.  That is also why the
  arity is checked here and `commutativeInArgAndRest`'s is not: a tail is open-ended and
  may reach two positions at a higher arity, where a named set is everything it will
  ever name.

  **Distinct positions**, for the same reason read the other way: `(commutativeInArgs P 1
  1)` names one slot twice and so names one position, which is the case above wearing a
  longer spelling.

  A position past the declared arity is not refused — `commutative-in-arg-and-rest-problems`
  gives the argument."
  [_ [f pred & positions :as s] _context]
  (let [ps (vec positions)]
    (cond-> []
      (< (count s) 4)       (conj (str f " takes a relation and at least two positions"))
      (nm/individual? pred) (conj (str pred " is an individual; " f " marks a relation"))
      (not-every? #(and (integer? %) (pos? %)) ps)
      (conj (str f " positions must be positive integers"))
      (and (every? integer? ps) (not= (count ps) (count (distinct ps))))
      (conj (str f " names a position twice; the positions must be distinct")))))

(defn prop-problems [_ [f pred :as s] _context]
  (cond-> []
    (not= 2 (count s))    (conj (str f " takes one argument"))
    (nm/individual? pred) (conj (str pred " is an individual; " f " marks a predicate"))))

(defn closed-extent-for-arg-problems
  "`(closedExtentForArg P n v)` — a predicate, a positive-integer position, and the value
  that position holds in the goals whose extent the grant closes.  The value is any term."
  [_ [f pred n :as s] _context]
  (cond-> []
    (not= 4 (count s))    (conj (str f " takes three arguments"))
    (nm/individual? pred) (conj (str pred " is an individual; " f " marks a predicate"))
    (not (and (integer? n) (pos? n)))
    (conj (str f " position must be a positive integer"))))

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
  "`reifiable_function` / `unreifiable_function` declare a NAT function's kind.  Their
  one argument is a *function name* — a `FruitFn`-shaped constant, which is indistinguishable from an
  individual by the naming invariants, so `prop-problems` (which refuses an
  individual) is the wrong check.  All that matters here is the arity and that the
  name is a symbol."
  [_ [f fname :as s] _context]
  (cond-> []
    (not= 2 (count s))    (conj (str f " takes one argument"))
    (not (symbol? fname)) (conj (str f " expects a function name (a symbol)"))))

(defn context-arg-subrelation-problems
  "`(contextArgSubrelation F pos R)` declares the structural genlCx ordering for a
  context-denoting function `F` (docs/context-nat.md): two `F`-contexts identical except
  at argument `pos` are ordered by the sub-relation `R` on that argument — the more
  specific one (its arg `pos` `R`-below the other's) `genlCx` the more general.

  `F` is a function name (a `Cx*Fn`-shaped constant, an individual by the naming
  invariants), `pos` a 1-based positive integer over `F`'s arguments, and `R` a predicate
  name.  Whether `pos` is in `F`'s arity is not knowable here — no declaration states an
  application's arity — so it is left to the producer, which simply finds no sibling pair
  to order when `pos` is out of range."
  [_ [f fname pos rel :as s] _context]
  (cond-> []
    (not= 4 (count s))    (conj (str f " takes a function, an argument position, and a sub-relation"))
    (not (symbol? fname)) (conj (str f " expects a function name (a symbol)"))
    (not (and (integer? pos) (pos? pos)))
    (conj (str f "'s argument position must be a positive integer"))
    (not (symbol? rel))   (conj (str f " expects a sub-relation name (a symbol)"))
    (and (symbol? rel) (nm/individual? rel))
    (conj (str rel " is an individual; " f " names the sub-relation ordering " fname "'s contexts"))))

(defn correspondence-problems
  "`(functionCorrespondingPredicate F P N)` says the function `F` and the predicate `P`
  state the same relationship, `N` naming the argument of `P` that carries `F`'s value.

  `F` is a function name — a `MotherFn`-shaped constant, an individual by the naming
  invariants — so the individual refusal falls on `P` alone.  `N` is optional and
  1-based; omitted, the value takes `P`'s last argument, which is the shape nearly
  every correspondence has.  Whether `N` is in range is not knowable here: it is
  checked against the *application*'s arity, which no declaration states."
  [_ [f fname pred pos :as s] _context]
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
    equational rule** — an oriented rewrite `fatherOf∘fatherOf → grandfather_of`, not a
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
  import bug.  A predicate or a type *is* a legal `rewriteOf`
  target — the merge moves its trie keys, predicate extent, rule-index postings and
  `genl` closure with it (docs/equality.md).  `sameAs` / `equals` stay
  individuals-only (OWL); `rewriteOf` is the spelling relation, so it is the one
  that carries vocabulary alignment across predicates and types.  `(sameAs A A)` is
  fine — OWL makes `sameAs` reflexive."
  [tax [f a b :as s] _context]
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
  [_ [_ & args] _context]
  [(str "different is not assertible: it is answered from the equality closure"
        " (a positive commitment that two terms differ would be OWL's differentFrom,"
        " which vaelii does not build) — ask it instead: (ask? kb '(different "
        (str/join " " args) "))")])

(defn brave-cautious-problems
  "`bravely` and `cautiously` are **not assertible**.  Each is a *read* on the current
  dilemmas — `(cautiously S)` is S in every optimal labeling, `(bravely S)` in some —
  answered by the brave/cautious prover (`add-reasoner kb :brave-cautious`) and never
  stored.  Stored as a premise it would be a computed value with no way to keep it current,
  the same reason the aggregates and `unknown` are refused; and the prover is authoritative
  and never reads such a fact.  Ask it instead."
  [_ [f & args] _context]
  [(str f " is not assertible: it reads the current dilemmas (in every optimal labeling"
        " for cautiously, in some for bravely) and is answered by the :brave-cautious"
        " reasoner, not stored — ask it, e.g. (ask? kb '(" f " " (str/join " " args) "))")])

(defn naf-problems
  "`unknown`, `thereExists`, `forall` and the five **aggregates** are **not assertible**:
  they are query operators, answered by a prover and never stored.  A stored `(unknown
  S)` would be a fact nothing consults, since the prover answers it; a stored count
  would be stale (docs/aggregate.md, \"Not assertible, and nothing is stored\")."
  [_ [f & _args] _context]
  [(str f " is not assertible: it is a query operator answered by a prover, not a fact"
        " to store — use it in a rule antecedent or ask it, e.g. (ask? kb '(" f " ...))")])

(defn inverse-problems [_ [_ p q :as s] _context]
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
;; holds.  So `checks` searches on two paths: `negation-cycle` from the rule being
;; asserted, and `genl-negation-cycle` from the rules reading a predicate at or above a
;; `genl` edge's supertype, against a taxonomy with the edge added.
;;
;; The dependency graph has two kinds of node and two kinds of edge:
;;
;;   rule R --depends-on--> P     P appears in R's antecedents        (positive)
;;   rule R --excepts-on--> P     R's exception mentions P            (negative)
;;   P --concluded-by--> rule R   R concludes a spec of P             (positive)
;;
;; A cycle crossing **at least one** negative edge is rejected.  A purely positive
;; cycle is ordinary recursion, which the engine supports and bounds by depth, and
;; is deliberately left alone.
;;
;; Both walks run against the edges, from a rule to the rules reading a predicate at or
;; above its consequent: a consequent's upward closure is small where a read predicate's
;; spec closure is not, since a type's ancestors are bounded by the hierarchy's depth and
;; its descendants are most of a broad ontology.  A cycle reversed is a cycle, so the
;; walk finds the cycles a forward walk would.  The closure is the **global** one: a
;; context-narrowed closure would under-approximate the graph and admit an unstratified
;; rule set.

(defn- concluded-key
  "What the walk keys a rule node's consequent by: `::any` for a rule whose consequent
  functor is a variable, which concludes every predicate, else its consequent predicate
  (nil for a rule that concludes nothing)."
  [node]
  (if (:concludes-any? node) ::any (:consequent-pred node)))

(defn- edge-kind
  "The edge from `reader` to a rule concluding something at or below `pred`, which
  `reader` reads: `:excepts-on` when `pred` is among its negative predicates, else
  `:depends-on`."
  [reader pred]
  (if (some #(= pred %) (:exception-preds reader)) :excepts-on :depends-on))

(defn- negation-walk
  "Breadth-first over the dependency graph's edges **reversed**, from `starts`
  (`[node negative?]` pairs, in content order), and the chain to the first state
  `closes?` (node, negative?) accepts, or nil.

  A step from a node concluding `c` goes to each rule reading a predicate in
  `genls-global(c)` (`readers`, which answers a predicate's readers in content order and,
  called with no argument, every rule): an edge `reader -> node` exists exactly when the
  reader reads a predicate whose spec closure holds `c`.  A node concluding any predicate
  steps to every rule.  So a step reads the consequent's upward closure and the rule
  index under each predicate in it, and no spec closure.

  The search state is the consequent and the `negative?` flag, not the rule: two rules
  concluding one predicate have the same edges in.  A state is pushed once, and a
  predicate's readers are expanded once per flag, so a walk costs the rules it reaches and
  the upward closures of their consequents.  `closes?` is asked of every successor, before
  the state is deduplicated.

  The chain is `[start [edge pred node] …]`: each step is the graph edge from its node to
  the one before it, which reads `pred`."
  [tax readers starts closes?]
  (let [seen-c (java.util.HashSet.)
        seen-g (java.util.HashSet.)
        push   (fn [q [node negative? :as state]]
                 (if (.add seen-c [(concluded-key node) negative?]) (conj q state) q))
        steps  (fn [node negative?]
                 (let [c (concluded-key node)]
                   (cond
                     (= ::any c)
                     (when (.add seen-g [::any negative?])
                       (for [r (readers)
                             :let [negs (seq (:exception-preds r))
                                   pred (first (nm/sort-by-content-key
                                                identity (or negs (:antecedent-preds r))))]
                             :when pred]
                         [(if negs :excepts-on :depends-on) pred r]))
                     (some? c)
                     (for [g (nm/sort-by-content-key identity (tax/genls-global tax c))
                           :when (.add seen-g [g negative?])
                           r (readers g)]
                       [(edge-kind r g) c r]))))]
    (or (some (fn [[node negative?]] (when (closes? node negative?) [node])) starts)
        (loop [q (reduce push clojure.lang.PersistentQueue/EMPTY
                         (map (fn [[node negative?]] [node negative? [node]]) starts))]
          (when-let [[node negative? chain] (peek q)]
            (let [out (reduce (fn [q [edge pred r]]
                                (let [neg?  (or negative? (= :excepts-on edge))
                                      chain (conj chain [edge pred r])]
                                  (if (closes? r neg?)
                                    (reduced {:closed chain})
                                    (push q [r neg? chain]))))
                              (pop q)
                              (steps node negative?))]
              (if (map? out) (:closed out) (recur out))))))))

(defn- forward-path
  "A walk's chain written in the graph's direction: the last node's label, then each
  edge as `\"<edge> <pred>\"` and the node it reaches, ending at the start's label."
  [[start & steps]]
  (reduce (fn [path [edge pred node]] (into [(:label node) (str (name edge) " " pred)] path))
          [(:label start)]
          steps))

(defn negation-cycle
  "Search the rule dependency graph for a cycle through negation created by adding
  rule node `rule`, and describe it — a vector of strings naming the nodes and
  edges around the cycle — or nil if there is none.

  A rule node is `{:id :label :antecedent-preds :exception-preds :consequent-pred
  :concludes-any?}`; `readers` maps a predicate to the rule nodes reading it, and must
  include `rule` itself under each predicate it reads, since a rule being asserted is not
  stored yet and a self-referential exception (a rule excepting on what it concludes) is
  exactly a one-rule cycle.

  Only cycles through `rule` are looked for.  Every rule assert and every genl edge
  assert runs a check, so whatever is being added can only close a cycle that passes
  through it.  The walk runs from `rule` against the edges and closes on reaching it
  again with a negative edge on the way (`negation-walk`).

  Which cycle is returned, when several pass through `rule`, is decided by content:
  the walk takes each upward closure in content order, and `readers` must answer each
  predicate's rules in content order (`checks/stratification-readers` does)."
  [tax readers rule]
  (some-> (negation-walk tax readers [[rule false]]
                         (fn [node negative?] (and negative? (= (:id rule) (:id node)))))
          forward-path))

(defn genl-negation-cycle
  "The cycle through negation the edge `(genl sub super)` closes, described as
  `negation-cycle` describes one, or nil.  `tax` holds the edge already; `readers` is the
  stored graph's (`checks/stratification-readers`).

  The edge adds the graph edges from each rule reading a predicate at or above `super`
  to each rule concluding a spec of `sub`, so a cycle the edge closes uses one of them.
  The walk starts at the rules reading a predicate in `genls-global(super)`, in content
  order, and goes against the graph's edges (`negation-walk`).  It closes at a rule
  concluding a spec of `sub` when a negative edge is on the path or the edge from the
  start is negative.  It reads only the rules those starts reach, and finds only cycles
  through the new edge, so a cycle already stored refuses no edge that does not reach it.

  A `genlCx` edge needs no walk: the graph's edges read the `genl` closure alone."
  [tax readers sub super]
  (let [above  (tax/genls-global tax super)
        ;; each reader once; stored rules' contents are distinct, so the order is content's
        starts (->> (into {} (for [g above, r (readers g)] [(:id r) r]))
                    vals
                    (nm/sort-by-content-key :content)
                    (mapv (fn [r] [r (boolean (some above (:exception-preds r)))])))
        below? (fn [node]
                 (or (:concludes-any? node)
                     (some-> (:consequent-pred node) (->> (tax/genls-global tax)) (contains? sub))))]
    (when-let [chain (negation-walk tax readers starts
                                    (fn [node negative?] (and negative? (below? node))))]
      (let [[start] chain
            closing (if (= 1 (count chain)) start (peek (peek chain)))
            edge    (if (some above (:exception-preds start)) :excepts-on :depends-on)]
        (conj (forward-path chain)
              (str (name edge) " " (if (:concludes-any? closing) sub (:consequent-pred closing)))
              (:label closing))))))

(defn cycle-description
  "Render a `negation-cycle` path as one line, for an error message."
  [cycle]
  (str/join " -> " cycle))
