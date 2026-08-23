;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.checks
  "The definitional checks — arg argument types, disjointness, functionality —
  plus ground-ness and the stratification glue over the rule index.

  Second layer of the engine stack (kb <- checks <- special <- integrate <- chain
  <- settle):
  every check reads the KB (taxonomy, index, believed matches) and returns a value
  or throws — nothing here writes.  Both mutation paths consume these: `assert`
  (vaelii.core) throws the value, the derivation path (vaelii.impl.chain) records
  it in the violations ledger."
  (:require [taoensso.nippy :as nippy]
            [vaelii.impl.config :as config]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rewrite :as rewrite]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.wff :as wff]))

;; ---- invariants: naming + argument type constraints ---------------------

;; The definitional checks below are **value-first**: each returns the first
;; violation as a map `{:type ... :message ...}` (or nil), like the wff arms and
;; `rules/range-problems`.  `constraint-checks` throws by wrapping the value on the
;; assert path; `constraint-violation` records it on the derivation path.  The old
;; shape — throw, then catch-your-own-throw against a whitelist of `:type`s — meant
;; a fourth check added without updating the whitelist would rethrow from inside
;; the chaining fixpoint, the exact abort `violations` exists to forbid.

(defn- checkable-term?
  "Is `x` a term the definitional checks can say anything about — any name the KB
  can hold a type membership for?

  Every non-variable symbol qualifies, whatever role its spelling reads as.  A
  predicate is as much a thing as `Muffet` is: the meta-ontology types predicates
  (`unaryPredicate`, `instanceRelationPredicate`, …), separates those types with
  `disjointMetatype`, and constrains predicate-valued argument positions with
  `arg` — so restricting the checks to CapitalCamelCase individuals would leave
  the whole meta-level declared and unenforced.  Numbers, strings and compounds are
  excluded because a type membership cannot be asserted of one (a NAT reifies to its
  constant first, so a reified term is checked under that constant)."
  [x]
  (and (symbol? x) (not (sx/variable? x))))

(def ^:private syntactic-roots
  "The syntactic types a literal is classified into — the roots of the kind lattice
  `quotedArg` types against.  A `quotedArg` whose declared type is neither one of these
  nor below one is out of the feature's domain (an imported constraint typing an argument
  as some domain collection), and the check reads it open-world rather than convicting."
  '#{string number integer symbol})

(defn- literal-type
  "The syntactic type of an argument taken as a **term** — its EDN kind, mapped to the
  type `quotedArg` constrains against: a string is `string`, an integer `integer` (a
  `number` below), any other number `number`, a non-variable symbol `symbol` (a name,
  however its role spells it).  `nil` for a kind quotedArg does not type — a compound, a
  keyword, a boolean, a variable — which the check reads open-world, exactly as
  `args-problem` exempts an argument outside the hierarchy."
  [x]
  (cond
    (string? x)                              'string
    (integer? x)                             'integer
    (number? x)                              'number
    (and (symbol? x) (not (sx/variable? x))) 'symbol
    :else                                    nil))

(defn- syntactic-type?
  "Is `t` a type `quotedArg` can judge a literal against — a syntactic root or a subtype
  of one?  A declared type outside this lattice leaves the constraint open-world."
  [tax t context]
  (or (contains? syntactic-roots t)
      (some #(tax/genl? tax t % context) syntactic-roots)))

(def ^:private declaration-queries
  "Per declaration kind, the sentence `declaration-reader` queries: the functor, then the
  argument tail that follows the predicate being asked about.  A table rather than a cond
  chain, because the kinds differ in *arity* as well as in functor — `interArg` names
  two positions and two types — and a chain would put that difference in the caller."
  '{arg      (arg ?n ?type)
    genlArg     (genlArg ?n ?type)
    quotedArg   (quotedArg ?n ?type)
    interArg (interArg ?n ?type ?m ?utype)})

(defn- declaration-reader
  "A `kind -> [[handle bindings sentex] …]` reader for the argument constraints binding
  one predicate's tuples, memoized for the life of one caller.

  `args-problem`, `genls-problem` and the entailments all ask the same two questions —
  what does `arg` say about this predicate's positions, and what does `genlArg` —
  and `assert` names that read the dominant per-fact cost of a store.  Asking it once
  is what lets the entailment ride along on a walk the check was making anyway instead
  of doubling it.  Realized rather than lazy: a predicate carries a handful of
  declarations, and every caller but the first-violation `for` wants all of them.

  **The read is the union over the predicate's `genl` closure**
  (`res/constraining-predicates`), not the bare predicate: a super-predicate's
  declaration binds the sub-predicate's tuples, since a `genl` edge between predicates
  says the sub's tuples *are* the super's.  One site feeds all four consumers, so the
  refusal, both `genls`-level checks and the minting move together.  The union is
  realized for the reason the single read was: `in-content-order` sorts before the
  first-violation walk starts, so there is no early exit for laziness to serve, and the
  sort is what keeps the refusal keyed on what the KB says rather than on which
  super-predicate the closure happened to enumerate first."
  [kb pred context]
  (let [cache (volatile! {})]
    (fn [kind]
      (if-some [ds (get @cache kind)]
        ds
        (let [[f & tail] (declaration-queries kind)
              ds         (when (symbol? pred)
                           (into []
                                 (mapcat #(res/matches-visible kb (list* f % tail) context))
                                 (res/constraining-predicates kb kind pred context)))]
          (vswap! cache assoc kind ds)
          ds)))))

(defn- declared-of
  "The predicate a declaration match is *about* — its first argument, which is `pred`
  itself for a declaration written on the predicate under test and a super-predicate of
  it for one that descends.  Named in a refusal message so an author told a `fatherOf`
  claim is ill-typed can find the `parentOf` declaration that says so."
  [match]
  (second (:sentence (nth match 2))))

(defn- via-clause
  "The refusal's `, declared of P` clause, or the empty string when the declaration is
  the sentence's own predicate's."
  [via pred]
  (if (= via pred) "" (str ", declared of " via)))

(defn arity-binding-clause
  "How a message says what length binds a predicate: **is declared with 2 arguments** for
  one carrying its own declaration, **takes 2 arguments through parentOf** for one whose
  length descends from a super-predicate.

  Public and spelled once, because a binding is described in more than one place and a
  reader carries the vocabulary from one description to the next.  Both of this
  namespace's doors word it — a wrong-length sentence (`arity-problem`) and a declaration
  naming a position the length denies (`arg-position-problem`) — and
  `settle/report-arity-reach!` words the same binding for the facts one arriving late
  convicts.  \"is declared with\" is false of a predicate that declared nothing and took
  its length off a super, so the split is a claim about the KB rather than a phrasing: a
  reader told it goes looking for a declaration nobody wrote, and one binding wearing two
  descriptions reads as two problems.  `door_and_report_test` is the roster that holds
  every reader's message to this clause."
  [pred via n]
  (str (if (= via pred) "is declared with " "takes ")
       n " argument" (when (not= 1 n) "s")
       (when-not (= via pred) (str " through " via))))

(defn- arg-at
  "The argument sitting at one-based `position` of the argument vector `as`, or nil when
  the position is not one the sentence has.  The bounds test the argument constraints all
  need before they can say anything about a position a declaration names."
  [as position]
  (when (and (integer? position) (<= 1 position (count as)))
    (nth as (dec position))))

(defn- in-content-order
  "Declaration matches sorted by the stored declaration's own sentence — the order
  every first-violation walk reads them in.

  `res/matches-visible` promises the answer *set*: `res/*hierarchical-retrieval*` says
  nothing about order, so a `(first (for …))` over the raw matches would let the
  retrieval strategy pick *which* declaration a refusal names when several convict.
  Sorting on content keys the choice on what the KB says rather than on enumeration —
  the rule `handle-naming` states for the handle a clash is reported as.  Existence is
  untouched: every declaration is still read, and a sentence no declaration convicts
  still has no violation.

  The `pr-str` key is built once per match and compared as a string (`nm/sort-by-content-key`
  with `compare`) — the same lexicographic order, off the per-comparison rebuild — and a
  run of one, the common case for a `(first (for …))` consumer, sorts nothing."
  [ds]
  (nm/sort-by-content-key #(pr-str (:sentence (nth % 2))) compare ds))

(defn- args-problem
  "First (arg pred n type) violation for a sentence, or nil.  Uses genl
  transitivity; only constraints and type memberships visible from `context`
  count.  Open-world: an untyped term can't violate anything.

  **Genl transitivity in two places, not one.**  The constraint *type* is reached
  through the closure, and so is the constrained *predicate*: `decls` reads every
  declaration on `pred` and on the super-predicates `context` can see
  (`res/constraining-predicates`), because a `genl` edge between predicates says the
  sub-predicate's tuples are the super's, and a tuple set only narrows going down.  So
  `(arg parentOf 1 person)` refuses `(fatherOf TheRock1 Mary)` as surely as it
  refuses the same claim spelled `parentOf` — which it has to, since the stored
  sub-predicate fact answers every super-predicate query through the matcher's fan.

  `types` is the shared per-assert membership reader (`kb/membership-reader`), `decls`
  the shared declaration reader.  The two questions asked of each constrained
  argument — is it in the hierarchy at all, and does it reach the constraint type —
  are one retrieval and two set lookups, and a second constraint on the same position
  adds no retrieval at all."
  [_kb sentence _context types decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))]
    (when (symbol? pred)
      (first
       (for [m     (in-content-order (decls 'arg))
             :let  [b   (nth m 1)
                    n   (get b '?n)
                    t   (get b '?type)
                    arg (arg-at as n)]
             :when (and arg (checkable-term? arg)
                        (let [ms (types arg)]
                          (and (kb/isa-among? (:closures ms) 'thing)
                               (not (kb/isa-among? (:closures ms) t)))))]
         {:type :arg-type :sentence sentence :arg arg :expected t :position n
          :message (str "arg constraint: " arg " must be a " t
                        " (arg " n " of " pred (via-clause (declared-of m) pred) ")")})))))

(defn- inter-args-problem
  "First `(interArg pred n T m U)` violation for a sentence, or nil.

  The **conditional** argument constraint: if argument `n` is a `T`, argument `m` must be
  a `U`.  `(interArg eats 1 carnivore 2 meat)` says a carnivore eats meat — a claim
  `arg` cannot make, since `(arg eats 2 meat)` would demand it of every eater.

  Open-world **twice, in opposite directions**, and that is the whole of the reading:

  * The trigger side must be *positively established*.  Silence about argument `n`'s type
    is not evidence that it is a `T`, so an unknown trigger leaves the constraint dormant
    rather than firing it — this is the antecedent of a conditional, and NAF there is a
    reason not to convict.
  * The target side is convicted by *absence*, exactly as `args-problem` is: argument `m`
    must be in the hierarchy at all (or the edges placing it may simply not have arrived)
    and must not reach `U`.  NAF here is a reason to convict.

  One declaration, two readings of the same silence, and getting either backwards inverts
  the constraint: demand the trigger's absence and every untyped argument fires it; excuse
  the target's absence and it never convicts anybody.

  Both sides are context-scoped by construction — `decls` reads only the declarations
  visible from `context` and `types` only the memberships — so a context is convicted
  on evidence it can see, which is the judgement `genls-problem` spells out at length.
  It descends the predicate hierarchy for `args-problem`'s reason and by riding the
  same reader: a conditional constraint on `parentOf` is a claim about every tuple of
  every predicate beneath it.

  **Behind an O(1) gate, unlike its two unconditional neighbours.**  `args-problem` and
  `genls-problem` run their declaration read unconditionally because `arg` is what a
  typed ontology is mostly made of, so the read pays for itself.  Nothing declares
  `interArg` yet, and this check runs on *every* assert — the read `assert` names its
  dominant per-fact cost — so a third retrieval that finds nothing is a tax on every write
  in every KB.  One `count-with-functor` says whether any such declaration is stored at
  all; zero means no scoped read can find one, so there is nothing to look for."
  [kb sentence _context types decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))]
    (when (and (symbol? pred)
               (pos? (p/count-with-functor (:index kb) 'interArg)))
      (first
       (for [d       (in-content-order (decls 'interArg))
             :let  [b       (nth d 1)
                    n       (get b '?n)
                    t       (get b '?type)
                    m       (get b '?m)
                    u       (get b '?utype)
                    trigger (arg-at as n)
                    target  (arg-at as m)]
             :when (and trigger target
                        (checkable-term? trigger) (checkable-term? target)
                        (symbol? t) (symbol? u)
                        ;; the antecedent, established rather than merely unrefuted
                        (kb/isa-among? (:closures (types trigger)) t)
                        (let [tm (types target)]
                          (and (kb/isa-among? (:closures tm) 'thing)
                               (not (kb/isa-among? (:closures tm) u)))))]
         {:type :inter-arg-type :sentence sentence :arg target :expected u :position m
          :trigger trigger :trigger-type t :trigger-position n
          :message (str "arg constraint: " target " must be a " u " (arg " m " of " pred
                        (via-clause (declared-of d) pred)
                        ", because arg " n " is a " t ")")})))))

(defn- genls-problem
  "First `(genlArg pred n type)` violation for a sentence, or nil.

  `genlArg` is `arg` one level up: it constrains the argument to be a **subtype**
  of the named type rather than an instance of it, which is what a type-level relation
  wants — `(genlArg partType 1 physical_object)` says the first argument names a kind
  of physical object, where `(arg partOf 1 physical_object)` says it names one.

  Which constraints apply is context-scoped exactly as `arg` is, and so is the
  subtype test itself: absence of a *visible* path to the constraint type is what
  convicts, the NAF reading judged from the writer's own vantage.  Which constraints
  apply also descends the predicate hierarchy exactly as `arg`'s do, by riding the
  same reader.

  Open-world has a floor here that `arg` does not have.  An argument outside the
  hierarchy is normally exempt, since the edges placing it may not have arrived yet —
  but an **individual** can never acquire them (`wff/genl-problems` refuses `genl` of
  one), so a type-level position holding one is convicted rather than excused.  The
  test is \"outside the hierarchy *and* individual\", not \"individual\", because a
  reified NAT reads as an individual by spelling and is minted with real `genl` edges from
  its `resultGenl` declarations — one that reaches `thing` is judged like any type.

  **A deliberate global/scoped split inside one `cond`.**  The first floor asks what
  the argument *is* (could it ever be a type?) and stays **global**: a reified NAT's
  minting edges land in `CxUniverse`, which the upper band sits above and
  cannot see, so a scoped floor would convict an imported reified NAT used from
  `CxMeasure` as \"an individual, so never a subtype\" — false.  The second
  floor is the **scoped** open-world excuse: an argument with no *visible* path
  into the hierarchy may simply have its edges out of sight, and a NAF check that
  convicted on invisible evidence would convict harder the less a context sees.
  Only an argument with visible evidence that reaches the wrong place is convicted."
  [kb sentence context decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (:taxonomy kb)]
    (when (symbol? pred)
      (first
       (for [d     (in-content-order (decls 'genlArg))
             :let  [b   (nth d 1)
                    n   (get b '?n)
                    t   (get b '?type)
                    arg (arg-at as n)
                    why (when (and arg (checkable-term? arg) (symbol? t))
                          (cond
                            (not (tax/genl? tax arg 'thing))          ; global: the individual floor
                            (when (nm/individual? arg)
                              (str arg " is an individual, so it can never be a subtype of " t))

                            (not (tax/genl? tax arg 'thing context))  ; scoped: no visible evidence
                            nil                                       ; — open world excuses

                            (not (tax/genl? tax arg t context))       ; scoped: the writer's vantage
                            (str arg " must be a subtype of " t)))]
             :when why]
         {:type :arg-genl :sentence sentence :arg arg :expected t :position n
          :message (str "arg constraint: " why " (arg " n " of " pred
                        (via-clause (declared-of d) pred) ")")})))))

(defn- args-quoted-problem
  "First `(quotedArg pred n type)` violation for a sentence, or nil.

  The **mention** twin of `args-problem`: where that types what an argument *denotes*,
  this types the argument *as a term* — its EDN kind (`literal-type`), checked through
  genl against the declared syntactic type.  `(quotedArg nameOfGuy 1 string)` refuses
  `(nameOfGuy 5)` because `5` is a `number`, not a `string`, and admits `(nameOfGuy
  \"Bob\")`.  Closed about a decidable literal, open-world about a kind it does not type
  (a compound, a keyword) — those are exempt, the same floor `args-problem` gives an
  argument outside the hierarchy.

  Behind the same O(1) gate as `inter-args-problem`, and for the same reason: nothing
  declares `quotedArg` in a bare KB, and this runs on every assert, so a
  `count-with-functor` says whether any is stored before a scoped read looks."
  [kb sentence context _types decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (:taxonomy kb)]
    (when (and (symbol? pred)
               (pos? (p/count-with-functor (:index kb) 'quotedArg)))
      (first
       (for [d     (in-content-order (decls 'quotedArg))
             :let  [b   (nth d 1)
                    n   (get b '?n)
                    t   (get b '?type)
                    arg (arg-at as n)
                    lit (literal-type arg)]
             :when (and (some? arg) lit (symbol? t)
                        (not= lit t)
                        (syntactic-type? tax t context)
                        (not (tax/genl? tax lit t context)))]
         {:type :quoted-arg-type :sentence sentence :arg arg :expected t :position n
          :message (str "quoted-arg constraint: " arg " must be a " t " as a term — it is a "
                        lit " (arg " n " of " pred (via-clause (declared-of d) pred) ")")})))))

;; ---- the argument constraints, checked against each other ----------------

(def ^:private arg-constraint-kinds
  "The two **unconditional** argument constraints, each mapped to the other: the value is
  the counterpart a declaration is checked against, and membership is what
  `declaration-problem` reads to recognize one.

  `interArg` is not here and has its own arm.  It is written at a different arity and
  names two positions, so it fits neither the pairing nor the `(= 3 (nm/arity …))` test —
  forcing it in would put that difference inside every reader of this map."
  '{arg genlArg, genlArg arg})

(def predicate-type-arities
  "What each predicate-type membership says the arity is.  The `arity` sentexes and
  these memberships derive each other through the CxCore rules, so a declared
  predicate normally has both — but a `{:chain? false}` assert or a KB loaded without
  the rules has only what was written, so both spellings are read.

  Public because `settle`'s retroactive arity report triggers on an arriving *arity
  declaration*, and these memberships are the second way to write one — a roster read
  twice is a roster that drifts."
  '{unaryPredicate 1 binaryPredicate 2 ternaryPredicate 3})

(defn- tabled-arity
  "The arity the `(arity P n)` **table** gives `pred` from `context`, or nil.

  Read from the **taxonomy cache** (`tax/declared-arity`), which `(arity P n)`
  maintains the way `(transitive P)` maintains its prop: this runs on every assertion,
  and answering it from the index meant a retrieval and a filtered walk of every sentex
  holding `pred` as its first argument — 16 candidates per assertion on an OpenCyc
  load, 13.3M over it, nearly all finding nothing.  A declaration is not something to
  re-derive per write.  One map read, which is why every arity question asks this one
  first and the membership spelling second."
  [kb pred context]
  (let [n (tax/declared-arity (:taxonomy kb) pred context)]
    (when (and (integer? n) (pos? n)) n)))

(defn- membered-arity
  "The arity `pred`'s own predicate-type membership gives it, or nil — the second
  spelling, read off the predicate's types (`types`, the shared per-assert reader), so it
  costs the retrieval `arg` already needs for its arguments rather than one of its
  own.  A retrieval where `tabled-arity` is a map read, which is the whole of why the two
  are separate functions rather than one `or`: a caller asking about several predicates
  wants the cheap half of the question asked of all of them first."
  [types pred]
  (let [cs (:closures (types pred))]
    (first (for [[t n] predicate-type-arities
                 :when (kb/isa-among? cs t)]
             n))))

(defn- variable-arity?
  "Is `pred` declared `variableArity`, from the vantage `types` reads with?

  The escape the whole arity family turns on, spelled once so every arm reads it the same
  way: off the predicate's own memberships, so a mark reached through a `genl` edge
  between collections releases exactly as a directly asserted one does."
  [types pred]
  (kb/isa-among? (:closures (types pred)) 'variableArity))

(defn- own-arity
  "The arity `pred` **itself** is declared with, visible from `context`, or nil when the
  KB has never said.  Both spellings, the table first because it is a map read."
  [kb pred context types]
  (or (tabled-arity kb pred context)
      (membered-arity types pred)))

(defn- inherited-arity
  "The arity `pred`'s **super-predicates** bind it to, as `[n via]`, or nil.

  A `genl` edge between predicates says the sub's tuples *are* the super's, and a tuple
  has an arity: a ternary `fatherOf` fact is a ternary `parentOf` tuple, which
  `(binaryPredicate parentOf)` says does not exist.  So a sub-predicate the KB has said
  nothing about is held to what the predicates above it declare — the cheapest and least
  contestable member of the descension family, since it convicts on the shape of the
  tuple rather than on anything the arguments happen to be.

  **Read only when `pred` declares nothing itself**, and that restriction is the whole of
  the difference between this and preserving arity down the hierarchy as an *answerable*
  fact.  The arity table is untouched, so `(arity child ?n)` still answers the one value
  somebody wrote and `(functional arity)` still has a single value to be functional
  about.

  The case this declines to read cannot disagree with it: a specialization carrying a
  signature of its own is held to the same length as the predicates above it
  (`edge-arity-problem` and `declaration-arity-problem` refuse the pair that disagrees),
  so \"where `pred` declares nothing\" is a restriction on where the *reading* happens
  and not a hole a conflicting declaration escapes through.

  **Unanimity or nothing**, which is the stance `tax/declared-arity` already takes toward
  two contradictory declarations of one predicate: supers that disagree leave the
  question genuinely unsettled, and convicting on whichever was enumerated first would be
  arbitrary.  A `variableArity` super releases the inheritance entirely, for the reason
  it exempts a predicate that carries it — a relation declared to read a chain of any
  length binds nothing beneath it to one length.

  The release is asked of **every** super, not only of the ones that declared the arity
  being inherited.  A super marked `variableArity` and given no length of its own says
  the hierarchy under it reads a chain, which is exactly the claim that should release a
  sibling's binary declaration; reading the mark only off the supers that contributed a
  number let such a super sit in the hierarchy saying nothing, and refused the chain it
  exists to license.  It costs no retrieval to ask it of all of them: the membership
  read is per super and memoized per assert, and the arity spelling below already pays
  it for every super the table does not name.

  `via` is the content-first super that declares the binding arity, so a refusal can name
  the declaration it convicts against.  Free for a predicate with no super-predicates:
  one closure read, already memoized by the argument-constraint reader beside it.

  **Both spellings, like `own-arity`** — the `(arity P n)` table first, since it is a map
  read where the predicate-type membership is a retrieval, and the membership after it
  for a super the table does not name.  A KB loaded with CxCore's rules has both for
  every declared predicate, because the rules derive each from the other; a KB loaded
  without them, or one written with `{:chain? false}`, has only what somebody typed, and
  a descension that saw one spelling and not the other would bind or release by which
  one that was.

  **Cost is one membership read per super-predicate**, and that is a real per-assert
  price on a deep hierarchy rather than a constant: the `variableArity` release has to
  be asked of every super whatever the table said, so the table saves the *arity* read
  and not the membership one.  The read is memoized per assert, so it is one retrieval
  per distinct super and not one per question asked of it.  Making it flat in the depth
  would mean holding the memberships somewhere the taxonomy can answer from — the trade
  `(arity P n)` itself takes one screen up — and it is not a filter that can be bolted
  on here, because a `variableArity` reached through a `genl` edge between collections
  releases exactly as a directly asserted one does, so a roster of the direct spelling
  would not be the superset such a gate needs.  `assert-cost-test`'s `deep-membership`
  workload and `perf`'s `membership-under-depth` pin the shape so it cannot worsen
  unnoticed."
  [kb pred context types]
  (let [tax    (:taxonomy kb)
        supers (sort (disj (tax/genls tax pred context) pred))
        pairs  (into [] (keep (fn [p] (when-let [n (own-arity kb p context types)] [p n])))
                     supers)]
    (when (and (seq pairs)
               (= 1 (count (into #{} (map second) pairs)))
               (not-any? #(variable-arity? types %) supers))
      (let [[p n] (nth pairs 0)] [n p]))))

(defn- declared-arity
  "The arity binding `pred` in `context`, as `[n via]`, or nil when nothing does — its
  own declaration where it has one (`via` is `pred`), else the one its super-predicates
  agree on (`inherited-arity`)."
  [kb pred context types]
  (if-let [n (own-arity kb pred context types)]
    [n pred]
    (inherited-arity kb pred context types)))

(defn- handle-namings
  "The handles of the matches that literally *say* `target`, in content order, else a
  content-ordered choice among the matches that merely entail it.

  `res/matches-visible` is **type-aware**, so a literal comes back alongside everything
  the taxonomy proves implies it: ask for `(animal CI2)` and you also get `(dog CI2)`
  where `dog` is under `animal`.  Every one of them is a true answer to *is this
  believed*, which is all an existence check wants — but a caller naming the handle is
  choosing the sentex a violation is **reported as**, and `ffirst` hands that choice to
  whatever order the retrieval strategy happened to produce.

  Order is not part of that contract, and should not be: `res/*hierarchical-retrieval*`
  promises the answer *set*, and a caller reading whole answers cannot observe more.
  Taking the first match would make it observable — a flag documented as a pure cost
  decision would decide which pair `contradictions` reports and, through arbitration,
  what the KB believes (`clash_oracle_test` under `VAELII_HIER=0`).

  So **both** arms are content-ordered, exact matches first because the direct statement
  is the one the caller asked about.  The order key is the sentence *and its context*:
  `res/matches-visible` fans over the whole `genlCx` cone, so one sentence stated in
  two visible contexts comes back as two exact matches, and a key on the sentence alone
  ties them — leaving the pick to enumeration order in precisely the arm that exists to
  take it away.  Never the handle, which is allocation order: two KBs given one op stream
  must name the same side.

  **Every exact match, not one**, because they are not one sentex.  A term stated to hold
  the same type in a general context and again in one that sees it is two stored
  claims of different provenance and possibly different strength, and each forms its own
  pair with whatever contradicts it — naming only the content-first of them leaves the
  other coexisting with content that denies it.  The entailing arm stays singular: those
  matches are *different* sentences reaching the target through the hierarchy, and each
  already convicts under the type it actually states."
  [matches target]
  (let [sen   (fn [m] (:sentence (nth m 2)))
        order (fn [m] (pr-str [(sen m) (:context (nth m 2))]))]
    (if-let [exact (seq (filter #(= target (sen %)) matches))]
      (map first (sort-by order exact))
      (take 1 (map first (sort-by order matches))))))

(defn- handle-naming
  "The one handle a *refusal* names — the first of `handle-namings`, which is the
  content-first exact match where one is stored.  A refusal needs one reason, and the
  arity arm convicts against a declaration rather than against a pair, so there is
  nothing plural for it to say."
  [matches target]
  (first (handle-namings matches target)))

(defn- arity-declaration-handle
  "The handle of the believed declaration saying `via` has arity `declared`, visible
  from `context` — the sentex a wrong-arity sentence convicts *against*.

  Two spellings declare it and `own-arity` reads both, so both are looked for: the
  `(arity P n)` sentex, and failing that the predicate-type membership `(binaryPredicate
  P)` that says the same thing.  `via` is the predicate the binding arity was read off,
  which is the sentence's own for a locally declared one and a super-predicate for an
  inherited one — so a refusal through the hierarchy names the declaration that convicted
  rather than looking for one the sentence's predicate never had.  Asked only once a
  clash has been found, so an admissible assert never pays for the retrieval."
  [kb via declared context]
  ;; `handle-naming` for the same reason it exists: both reads are type-aware, so a
  ;; subtype of the declaration's own predicate comes back beside it.  The preference
  ;; between the two *spellings* is this `or`, and stays content-ordered by construction.
  (or (let [target (list 'arity via declared)]
        (handle-naming (res/matches-visible kb target context) target))
      (first (for [[t n] predicate-type-arities
                   :when (= n declared)
                   :let  [target (list t via)
                          h (handle-naming (res/matches-visible kb target context) target)]
                   :when h]
               h))))

(defn- arity-problem
  "A sentence used at an arity its predicate is not declared with, or nil.

  The **top literal only**, exactly like `args-problem`: a rule reaches here as its
  `implies` form, whose own arity is 2 and is checked as such, and its antecedents are
  not.  That is the existing line between what `assert` checks and what a rule is
  trusted to contain, and arity does not move it.

  Open-world in the same shape as `arg`: a predicate the KB has never declared can
  be used at any arity, since the declaration may simply not have arrived.  A
  `variableArity` predicate is exempt outright — `lessThan` is declared binary *and*
  reads a chain of any length, and the declaration is what says so.

  The binding arity **descends the predicate hierarchy** where the predicate declares
  none of its own (`inherited-arity`): a `fatherOf` tuple is a `parentOf` tuple, so its
  length is held to what `parentOf` was declared with.

  `:opposing-handle` names the declaration that convicted, so a refusal can say *which*
  one and the retroactive report can point at it.  It does **not** make this arbitrable
  — `arbitrable-kinds` is what decides that, and the comment above it says why arity is
  not on the list even though it names a second sentex.

  `:via` names the predicate the length was read off — `pred` itself for one carrying its
  own declaration, a super-predicate for one that inherits — and the message is worded off
  it, because \"`fatherOf` is declared with 2 arguments\" is false of a predicate nobody
  declared and sends an author looking for a declaration that does not exist.  So an
  inherited length **takes … through** and a declared one **is declared with**, which is
  `arity-binding-clause`'s one spelling of the split — and the key is on the map so a
  reader building its own message reads the same binding, which `settle`'s retroactive
  report and `arg-position-problem` beside it both do."
  [kb sentence context types]
  (let [pred (nm/functor sentence)]
    (when (symbol? pred)
      ;; the arity question is answered from the taxonomy cache and the predicate's
      ;; own type memberships (`declared-arity`) — no declaration query is made here
      (when-let [[declared via] (declared-arity kb pred context types)]
        (let [actual (nm/arity sentence)]
          (when (and (not= actual declared)
                     (not (variable-arity? types pred)))
            {:type :arity :sentence sentence :predicate pred
             :expected declared :actual actual :via via
             :opposing-handle (arity-declaration-handle kb via declared context)
             :message (str pred " " (arity-binding-clause pred via declared)
                           " but has " actual)}))))))

;; ---- arity across a genl edge -------------------------------------------
;;
;; `arity-problem` above holds a *sentence* to its predicate's declared length.  The two
;; arms below hold the **vocabulary** to itself: a `genl` edge between predicates asserts
;; that the sub's tuples *are* the super's, and tuples of different lengths are not the
;; same tuples, so two declared arities across one edge is a pair the KB may not hold.
;;
;; **A specialization does not carry its own signature.**  A signature on the sub that
;; disagrees with the super is not a narrowing, it is a contradiction: `(genl fatherOf
;; parentOf)` beside `(binaryPredicate parentOf)` and `(ternaryPredicate fatherOf)` admits
;; a ternary `fatherOf` fact that answers a `(parentOf ?a ?b ?c)` query the door refuses.
;; Refusing the pair is also what keeps the arity *table* single-valued, which `(functional
;; arity)` needs: a conflicting declaration never lands, so no predicate has two lengths to
;; answer with and no two genl-related predicates disagree about one either.
;;
;; **The arriving sentence is what is refused**, in both directions — the edge when it
;; arrives onto two declared predicates, the declaration when it arrives onto a predicate
;; a visible edge already relates to a differently declared one.  So the KB never enters
;; the inconsistent state, and which sentence is refused is the ordinary first-writer-wins
;; every door refusal already has.
;;
;; **Through the closures on both sides**, because a predicate declaring nothing itself is
;; not a predicate binding nothing: it takes its supers' length (`inherited-arity`), and an
;; edge arriving onto it puts the specs below it into the same tuple set (`descended-arity`).
;; Reading each end's own declaration alone leaves an undeclared predicate between two
;; declared ones as a gap both arms fall through — the case `an-undeclared-predicate-between-
;; two-declared-ones-is-still-a-pair` pins.  Predicates that disagree with *each other* on
;; one side are not a pair: neither is above the other, the end binds neither, and
;; `supers-that-disagree-about-arity-bind-nothing` is the case that says so.

(defn- arity-descension-message
  "The refusal both arms carry: both predicates, both arities, and the edge that makes
  them one claim.  Sub first whichever sentence arrived, so the message is a fact about
  the pair rather than about the arrival order."
  [sub sub-arity super super-arity]
  (str "arity does not descend: " sub-arity " argument" (when (not= 1 sub-arity) "s")
       " declared of " sub ", " super-arity " declared of " super
       ", and (genl " sub " " super ") says every " sub " tuple is a " super
       " tuple — tuples of different lengths are not the same tuples"
       " (give the two one arity, or declare one variableArity)"))

(defn- descended-arity
  "The arity `pred`'s **sub-predicates** declare, as `[n via]`, or nil — the spec-side
  twin of `inherited-arity`, and read for the reason that one is read: a length binding
  one end of an arriving edge does not have to be declared *at* that end.

  Where `inherited-arity` looks up because a sub's tuples are its supers' tuples, this
  looks down because the same edge makes a spec's tuples the super's: `(genl grandOf
  fatherOf)` with `(ternaryPredicate grandOf)` says `fatherOf` has ternary tuples under
  it, so an arriving `(genl fatherOf parentOf)` onto a binary `parentOf` is the same
  incoherent pair seen from below.

  **Unanimity or nothing**, `inherited-arity`'s stance and for its reason.  Two specs
  that disagree with *each other* under an undeclared `pred` are not themselves a pair —
  neither is above the other and `pred` binds neither — so a disagreement here leaves the
  question unsettled rather than convicting on whichever the closure yielded first.

  **Read only when the other end already binds a length**, which is what keeps it off the
  ordinary load: the spec closure of a collection is the whole taxonomy beneath it, and
  an edge between two collections has no arity on either side to make it worth walking."
  [kb pred context types]
  (let [tax   (:taxonomy kb)
        specs (sort (disj (tax/specs tax pred context) pred))
        pairs (into [] (keep (fn [p]
                               (when-not (variable-arity? types p)
                                 (when-let [n (own-arity kb p context types)] [p n]))))
                    specs)]
    (when (and (seq pairs) (= 1 (count (into #{} (map second) pairs))))
      (let [[p n] (nth pairs 0)] [n p]))))

(defn- reached-arity
  "The arity `pred`'s visible relatives bind it to, as `[n via]`, or nil — above it first
  (`inherited-arity`, the commoner and the cheaper, since a predicate has fewer supers
  than a collection has specs), then below it (`descended-arity`).

  What `edge-arity-problem` asks of the end that declares no length of its own, once the
  *other* end has declared one."
  [kb pred context types]
  (or (inherited-arity kb pred context types)
      (descended-arity kb pred context types)))

(defn- arity-descension-violation
  "The violation map for a `sub` / `super` pair declared at `sub-arity` and `super-arity`,
  reported against the sentence that arrived.

  `:opposing-handle` names the *other* side's declaration — the one the KB already holds —
  for `arity-problem`'s reason, and with `arity-problem`'s consequence: `:arity` is not in
  `arbitrable-kinds`, so this is a refusal and not a nogood.  The sentex it names is a
  vocabulary entry the conviction is read through, and the comment above `arbitrable-kinds`
  says why that may not be defeated."
  [kb sentence sub sub-arity super super-arity opposing opposing-arity context]
  {:type :arity :sentence sentence :predicate sub
   :sub sub :sub-arity sub-arity :super super :super-arity super-arity
   :opposing-handle (arity-declaration-handle kb opposing opposing-arity context)
   :message (arity-descension-message sub sub-arity super super-arity)})

(defn- edge-arity-problem
  "An arriving `(genl sub super)` whose two predicates are declared with different
  arities, or nil.

  **The sub's own declaration is read first and the super's only if it found one**, which
  is both the cheap order and the complete one: a clash needs a declaration on each side,
  and an undeclared sub is the case the descension exists to serve.  So an edge between
  two collections — the bulk of what a load asserts — stops on the sub and never reads the
  super.  It stops at a cost rather than at none: `own-arity` falls through to the
  membership spelling wherever the `(arity P n)` table has no entry, and an undeclared
  collection is exactly the term the table does not name, so the ordinary edge pays the
  table read *and* the sub's memberships retrieval — cold here, since this arm runs ahead
  of the argument checks and a `genl` sentence gives them no `arg` position to read the
  same term through.  Both spellings are read on each side (`own-arity`), because a KB loaded
  without CxCore's derivation rules has only what somebody typed and a rule that saw one
  spelling and not the other would refuse by which one that was.

  `variableArity` on **either** side releases, for the reason it exempts the predicate
  carrying it: a relation declared to read a chain of any length makes no claim about the
  length of the tuples above or below it, so there is nothing to contradict.

  **What binds an end is not only what is declared at it.**  An *undeclared* predicate
  between two declared ones hides the pair from a reader of the two endpoints' own
  declarations: `(genl fatherOf parentOf)` onto a binary `parentOf` and `(genl grandOf
  fatherOf)` from a ternary `grandOf` each stop on the side `fatherOf` says nothing about,
  and the KB is left answering `(parentOf ?a ?b ?c)` with a tuple the door refuses — the
  state the comment above says this arm exists to prevent, reachable in 14 of the 24 orders
  those four sentences arrive in.  So the end that declares nothing is read through the
  closures instead, `inherited-arity` for a length above it and `descended-arity` for one
  below (`reached-arity`).

  **One end has to declare its own length for the other to be walked**, and that gate is
  the whole of what keeps this affordable.  A `genl` edge is the commonest vocabulary
  write there is, most of them run between collections, and neither end of those declares
  an arity — so the walk is skipped before it starts and the ordinary edge pays exactly
  what it always did, two `own-arity` reads.  `taxonomy-depth` is the shape that makes the
  gate necessary rather than merely thrifty: edges arriving down one chain give each new
  edge a super whose `genl` closure is every edge already asserted, so walking it per edge
  is quadratic in the chain, and the cell pins that edge at a flat cost 2000 deep.

  What the gate gives up is a pair whose two lengths are *both* only inherited — an
  undeclared sub under a declared super, an undeclared super over a declared one, and an
  edge between those two.  Each of the three edges involved refuses when it is the one
  that arrives onto the others, so the pair is caught in most orders and escapes in the
  ones where the edge between the two undeclared ends arrives last.  Closing that costs
  the quadratic walk above on every edge in the KB, which is not a trade this arm can make
  for a shape two declarations away from anything a hierarchy states."
  [kb sentence context types]
  (when (and (= 'genl (nm/functor sentence)) (= 2 (nm/arity sentence)))
    (let [[sub super] (nm/args sentence)]
      (when (and (checkable-term? sub) (checkable-term? super) (not= sub super)
                 (not (variable-arity? types sub))
                 (not (variable-arity? types super)))
        (let [n (own-arity kb sub context types)
              m (own-arity kb super context types)
              ;; the walk runs on one end only, and only against a length the other end
              ;; declares of itself — both undeclared is the ordinary edge, and it stops here
              a (or (when n [n sub])   (when m (reached-arity kb sub context types)))
              b (or (when m [m super]) (when n (reached-arity kb super context types)))]
          (when (and a b (not= (first a) (first b)))
            (let [[an via-sub]   a
                  [bm via-super] b]
              (arity-descension-violation kb sentence via-sub an via-super bm
                                          via-super bm context))))))))

(defn membership-arity
  "The arity a one-place membership functor `f` declares of its argument, or nil — one of
  the three spellings itself, or a collection the taxonomy makes a `genl` of one.

  Public for the reason `predicate-type-arities` is, and in its place: `settle`'s
  retroactive arity report triggers on an arriving declaration and has to recognise the
  same ones this door does.  Reading the raw map there and the closure here is the drift
  its own docstring warns about, so the closure read is the shared one.

  **Read through the closure because the readers read through one.**  `membered-arity`
  answers off `(:closures (types pred))`, so `(genl myBinPred binaryPredicate)` beside
  `(myBinPred fatherOf)` makes `fatherOf` binary to everything that *reads* a declaration.
  Matching the three literal functors here made the *writer* of one blind to exactly that
  spelling: the disagreeing edge lands, and the reader then convicts facts under it.  A
  roster read twice is a roster that drifts, and these are its two reads.

  The literal is asked first and answers all but the unusual case; only a one-place
  sentence whose functor is not already one of the three pays the cached `genls` behind
  it.  Content-ordered, so a functor made a `genl` of two of them — itself incoherent —
  picks the same one every run."
  [kb f context]
  (or (predicate-type-arities f)
      (let [supers (tax/genls (:taxonomy kb) f context)]
        (first (for [[t n] (sort-by key predicate-type-arities)
                     :when (contains? supers t)]
                 n)))))

(defn- arity-declared-by
  "The `[pred n]` an arriving sentence declares an arity of, or nil — both spellings,
  `(arity P n)` and the `unaryPredicate` / `binaryPredicate` / `ternaryPredicate`
  membership that says the same thing.  The gate on the arm below: nothing else can
  put a predicate in disagreement with one a `genl` edge already relates it to."
  [kb sentence context]
  (let [f  (nm/functor sentence)
        as (vec (nm/args sentence))]
    (cond
      (and (= 'arity f) (= 2 (count as)) (checkable-term? (first as))
           (integer? (second as)) (pos? (second as)))
      [(first as) (second as)]

      (and (= 1 (count as)) (checkable-term? (first as)))
      (when-let [n (membership-arity kb f context)]
        [(first as) n]))))

(defn- declaration-arity-problem
  "An arriving arity declaration that disagrees with one already declared of a predicate
  a visible `genl` edge relates it to, or nil — the other arrival order of
  `edge-arity-problem`, and the same refusal.

  **Both directions of the edge**, since a declaration can arrive onto either end: the
  super closure says what this predicate's tuples already are, the spec closure what
  already claims to be its tuples, and a mismatch either way is the same incoherent pair.
  The two closures are cached, and a predicate outside the `genl` hierarchy — which is
  most of them — has an empty related set and stops there.

  **Scoped like every other descension**, to the edges and declarations `context` can see:
  a writer is refused on evidence its own vantage holds, which is the judgement
  `genls-problem` spells out at length.

  Content-ordered, so which of several disagreeing relatives a refusal names is a function
  of the vocabulary rather than of the order the closure came back in."
  [kb sentence context types]
  (when-let [[pred n] (arity-declared-by kb sentence context)]
    (let [tax     (:taxonomy kb)
          supers  (tax/genls tax pred context)
          related (sort (disj (into supers (tax/specs tax pred context)) pred))]
      (when (and (seq related) (not (variable-arity? types pred)))
        (first
         (for [q     related
               :let  [m (own-arity kb q context types)]
               :when (and m (not= m n) (not (variable-arity? types q)))
               :let  [[sub sn super sm] (if (contains? supers q)
                                          [pred n q m]
                                          [q m pred n])]]
           (arity-descension-violation kb sentence sub sn super sm
                                       q m context)))))))

(defn- arg-position-problem
  "A declaration constraining a position `pred` does not have — `(arg parentOf 5
  animal)` where `parentOf` is declared binary.  The constraint would never fire, so it
  reads as enforced while enforcing nothing.

  Shared by every declaration kind, because `interArg` names **two** positions and both
  are the same mistake.  Open-world: a predicate whose arity the KB has never stated is
  unconstrained — and the arity read is `declared-arity`'s, so a predicate that inherits
  its length from a super-predicate has the position it lacks refused on the same
  grounds.

  **`variableArity` releases it**, as it releases every other arm of the family.  Such a
  predicate reads a tuple of any length from its declared arity upward, so a position past
  that length is one its tuples really do reach and a constraint on it fires — `arg-at`
  bounds-checks per sentence, so the declaration is silent on the short tuples and
  enforced on the long ones.  Refusing it while the same KB admits the very facts it would
  type is the one reading no arrival order makes coherent.

  The release is read off **`pred`'s own memberships and nothing else**, which is
  `variable-arity?`'s definition and is the complete question here.  An inherited length
  reaches this arm only through `inherited-arity`, which already declines to bind when any
  super carries the mark — so a `via` that is not `pred` is a predicate the release was
  asked of and refused, and asking it again would answer a settled question twice.  Asking
  it of `via` *instead* is the reading that loses the case: the mark sits on the sub, which
  is exactly where `inherited-arity` never looks.

  `:via` and the wording that follows it for `arity-problem`'s reason.  **Both routes reach
  here** — a predicate held to a number it declared, and one held to a super's — so
  `arity-binding-clause` says which: `parentOf` *is declared with* 2 arguments, `fatherOf`
  *takes* 2 arguments *through* `parentOf`.  Wording the second as a declaration would be
  false of a predicate nobody declared, and would send an author looking for one that does
  not exist."
  [kb f pred n context types]
  (when (and (integer? n) (pos? n))
    (when-let [[declared via] (declared-arity kb pred context types)]
      (when (and (> n declared) (not (variable-arity? types pred)))
        {:type :arg-position :predicate pred
         :position n :arity declared :via via
         :message (str f " constrains argument " n " of " pred ", which "
                       (arity-binding-clause pred via declared))}))))

(defn- declaration-problem
  "A problem with an `arg` / `genlArg` / `interArg` **declaration** itself, rather
  than with a sentence it constrains — two ways one can contradict what the KB already
  says about the predicate it is about:

  * a position the predicate does not have (`arg-position-problem`).  `interArg` names
    two, and each is checked.
  * a constraint disagreeing with the predicate's own `relationKind` — `genlArg` on
    an `instanceRelationPredicate`, or `arg` on a `typeRelationPredicate`.
    `interArg` reads its types as memberships, so it takes `arg`'s side of that.

  **Both constraints on one position is not a problem**, and this is the case worth
  naming because the opposite reads plausible: one asks the argument to be an instance
  of a type, the other to be a subtype of a type, and a *type* is routinely both.
  `(arg P 2 collection)` with `(genlArg P 2 animal)` says the slot holds a kind of
  animal, and `dog` satisfies it — an instance of `collection`, a subtype of `animal`.
  The two checks are independent and each is open-world on its own, so declaring both
  narrows the slot rather than emptying it.

  Open-world throughout: each arm needs a declaration to contradict, so a predicate
  the KB has said nothing about is unconstrained."
  [kb sentence context types]
  (let [[f pred n _ m] sentence]
    (cond
      (and (= 'interArg f) (= 5 (nm/arity sentence)) (symbol? pred))
      (some-> (or (arg-position-problem kb f pred n context types)
                  (arg-position-problem kb f pred m context types)
                  (when (seq (res/matches-visible kb (list 'typeRelationPredicate pred) context))
                    {:type :arg-constraint-kind :predicate pred
                     :message (str pred " is declared typeRelationPredicate, so its"
                                   " arguments are constrained with genlArg, not " f)}))
              (assoc :sentence sentence))

      (and (contains? arg-constraint-kinds f) (= 3 (nm/arity sentence))
           (symbol? pred) (integer? n) (pos? n))
      (let [other (arg-constraint-kinds f)]
        (or (some-> (arg-position-problem kb f pred n context types)
                    (assoc :sentence sentence))
            (let [clash (if (= f 'arg) 'typeRelationPredicate 'instanceRelationPredicate)]
              (when (seq (res/matches-visible kb (list clash pred) context))
                {:type :arg-constraint-kind :sentence sentence :predicate pred
                 :message (str pred " is declared " clash ", so its arguments are"
                               " constrained with " other ", not " f)})))))))

;; ---- the three violations that name an opposing sentex -------------------
;;
;; Disjointness, functionality and asymmetry are not like the argument constraints.
;; Each convicts by pointing at **another believed sentex** that the incoming one
;; cannot coexist with — a pair, which is exactly what a nogood is, and exactly what
;; `settle` already arbitrates for `S` against `(not S)`.  So each carries the
;; opposing handle and that handle's defeat class, and the layers above decide from
;; the class alone whether this is a *refusal* (contradicting the fixed background) or
;; a *nogood* (contradicting a defeasible claim).  See docs/nmtms.md.
;;
;; **Two families do not join them, for two different reasons.**
;;
;; The argument constraints cannot form a pair at all.  `(parentOf Fred Mary)` violating
;; `(arg parentOf 1 animal)` is convicted by the *absence* of a path from Fred's types
;; to `animal` — an open-world negation-as-failure judgement, not a stored sentex to weigh
;; against — so there is no second member to make a pair of, and nothing for a defeat
;; class to compare.  Those stay refusals.
;;
;; `arity` **does** name a second sentex — the `(arity P n)` declaration, or the
;; predicate-type membership saying the same thing — and is still not arbitrable, which is
;; the case worth naming because the pair looks so much like the three above it.  The
;; sentex it names is the *vocabulary entry the conviction is read through*: `declared-arity`
;; answers from the taxonomy's arity table, which follows belief, so a nogood that defeated
;; the declaration would destroy its own premise.  Measured, on `(pRelOf A B C)` known-true
;; against a `:default` `(arity pRelOf 2)`: the declaration is defeated in the settle that
;; admits the pair, revived by the next settle's `clear-defeats!` while the table it was
;; uninstalled from is still empty, and with the table empty the clash is not re-derived —
;; so it is never reported again, and while the declaration was out a *fourth*-arity fact
;; of the same predicate was admitted too.  One wrong fact would disable a declaration for
;; every other use of the predicate, and belief would depend on how many settles had run.
;;
;; The other two members of the family defeat a *fact* and leave the vocabulary standing,
;; which is why they are stable.  So arity keeps the door refusal, and the retroactive half
;; is a **report** (`settle/report-arity-reach!`) rather than a decision: it names the facts
;; a declaration arriving late convicts, and moves no belief.  Do not promote it to a
;; nogood without first making the vocabulary read independent of the belief the nogood
;; moves.

(def arbitrable-kinds
  "The definitional violations that name **other believed sentexes** rather than a
  malformed sentence, so `settle` can arbitrate them like any other contradiction."
  #{:disjoint :functional :asymmetric :anti-transitive})

(defn opposing-handles
  "The believed sentexes a violation is *against*, as a vector of handles — empty when
  it names none.

  Two spellings, one reading.  The pairwise kinds name a single opposing sentex in
  `:opposing-handle` and always did; `:anti-transitive` convicts a two-step chain and the
  direct step **together**, so it names both other members in `:opposing-handles` (the
  nogood is a triple, not a pair — docs/nmtms.md).  Every consumer that weighs a
  violation against what it opposes reads this rather than either key, so a kind naming
  two is weighed exactly as one naming one is, and the published `:opposing-handle` on
  the three older kinds is left where callers already read it."
  [v]
  (cond
    (seq (:opposing-handles v)) (filterv integer? (:opposing-handles v))
    (integer? (:opposing-handle v)) [(:opposing-handle v)]
    :else []))

(defn- opposing-class
  "The **weakest** defeat class among the sentexes a violation is against, or nil when it
  names none.  Read from the TMS rather than from the record's `:strength`, because a
  derived opposing claim is a premise of nothing and carries its class only on the node.

  Weakest, because the one question asked of it is whether the newcomer could ever be
  believed beside what it opposes (`against-known-true?`): a chain with one defeasible
  step is a chain the arbitration can break, so a refusal there would refuse content the
  KB can perfectly well hold.  Over a single opposing sentex — every kind but
  `:anti-transitive` — this is that sentex's class and nothing has changed."
  [kb v]
  (let [hs (opposing-handles v)]
    (when (seq hs)
      (reduce strength/min (map #(jtms/defeat-class (:tms kb) %) hs)))))

(defn- with-opposing-class
  "Stamp a violation with its opposing sentexes' defeat class, so every consumer reads
  the same answer rather than each fetching it again."
  [kb v]
  (if (and v (seq (opposing-handles v))) (assoc v :opposing-class (opposing-class kb v)) v))

(defn arbitrable?
  "Can `settle` arbitrate this violation instead of the caller refusing it — does it
  name opposing believed sentexes to form a nogood with?"
  [v]
  (boolean (and v (contains? arbitrable-kinds (:type v))
                (seq (opposing-handles v)))))

(defn- against-known-true?
  "Is the opposing side known-true — the fixed background a solve reasons *from*?
  Then admitting the newcomer would store something the KB can never believe, and a
  refusal is the honest answer.  A violation naming no opposing sentex answers true:
  what cannot be arbitrated must be refused."
  [v]
  (or (not (arbitrable? v))
      (strength/known-true? (:opposing-class v))))

(def ^:dynamic *arbitrate-constraints?*
  "Does the **assert** path hand a disjointness or functionality clash to `settle` as
  a nogood instead of throwing?

  **Off by default**, which leaves `assert` refusing exactly what it refuses today: a
  disjoint or functional clash at any strength.  On, the three checks read one rule —
  refuse only against `:monotonic` content, arbitrate against a `:default` claim — and
  `(dog Rex)` beside `(cat Rex)` becomes a represented dilemma rather than a throw.

  The derivation path does not consult this and never did: a rule firing has no caller
  to refuse, so an arbitrable violation there is always placed and arbitrated (which is
  what gives the loser a `why-not`).  This var is only about whether a *writer* is told
  no, and that is a policy question rather than an engine one.

  `binding` it is the ordinary way in; `VAELII_ARBITRATE_CONSTRAINTS=1` sets the root
  value, which is what lets the whole suite be run under it.  A KB that names a
  `:constraints` policy of its own overrides both — `kb/constraint-policies` names them
  and `arbitrating?` is the one read of either."
  ;; A var root, so it is read at namespace load and refuses there — `config`'s own
  ;; docstring says why that is the right door for a `def` and the wrong one for a value
  ;; a worker reads.
  (config/arbitrate-constraints?))

(defn arbitrating?
  "Does `kb` arbitrate a definitional clash against defeasible content rather than
  refusing it at the door — and let a declaration reach back over stored content?

  The KB's own `:constraints` policy decides when it has one (`kb/constraint-policies`
  names them); a KB that named none reads the process default, so
  `VAELII_ARBITRATE_CONSTRAINTS=1` still moves a whole suite and a `binding` still moves
  one call."
  [kb]
  (case (:constraints kb)
    :arbitrate true
    :refuse    false
    *arbitrate-constraints?*))

(defn refuses-assert?
  "Does this violation refuse the sentence on the **assert** path?

  `:asymmetric` reads the class either way — that is the line it draws, and the one the
  other two are generalized to.  `:anti-transitive` reads it the same way, over the
  *weakest* step of the chain it convicts (`opposing-class`), so a chain the arbitration
  could break is arbitrated and one it could not is refused.  `:disjoint` and
  `:functional` refuse unconditionally until `kb`'s constraint policy (`arbitrating?`)
  opts into the same rule.  Everything else is a malformed sentence or an open-world
  judgement and refuses outright."
  [kb v]
  (when v
    (case (:type v)
      (:asymmetric
       :anti-transitive)      (against-known-true? v)
      (:disjoint :functional) (or (not (arbitrating? kb)) (against-known-true? v))
      true)))

(defn- membership-handles-led
  "`membership-handles`' small side: lead from `x`'s own argument-1 postings (a handful)
  and test each up via `genls` (t ∈ genls(t'') ⟺ t'' ∈ specs(t), see `kb/memberships`),
  rather than `matches-visible` walking `specs(t)` *down* — unbounded for a broad t (with
  t = `thing`, every type in the KB), and the closure walk that dominates a cold rebuild's
  clash pass.  The candidate set, the filters (believed, context-visible, `except`-hidden,
  retired) and `handle-namings` are exactly what `matches-visible` would feed here — it is
  `matches-hierarchical` over `(t x)` then `without-excepted`/`without-retired`, and the
  pred-hierarchy filter `t'' ∈ specs(t)` is the same set as `t ∈ genls(t'')` — so the
  answer set is identical, retrieved from the small side.  Split out so `res/*lead-side*`
  can force the `matches-visible` reference the two oracles compare it against."
  [kb t x context]
  (let [recs   (:records kb)
        tms    (:tms kb)
        tax    (:taxonomy kb)
        target (list t x)
        up     (when-not (sx/variable? context) (tax/context-up tax context))
        vis?   (if up #(contains? up %) (constantly true))
        matches (->> (p/sentexes-with-arg (:index kb) 1 x)
                     (keep (fn [h]
                             (when-let [s (p/get-sentex recs h)]
                               (when (and (jtms/in? tms (:id s)) (vis? (:context s)))
                                 (let [sen (:sentence s)]
                                   (when (and (= 1 (nm/arity sen))
                                              (= x (first (nm/args sen)))
                                              (not (sx/exceptWhen-meta? sen)))
                                     (let [t'' (nm/functor sen)]
                                       (when (or (= t'' t)
                                                 (contains? (tax/genls tax t'' context) t))
                                         [(:id s) nil s]))))))))
                     (res/without-excepted kb context)
                     (res/without-retired kb context))]
    (handle-namings matches target)))

(defn- membership-handles
  "The handles of the believed `(t x)` sentexes visible from `context` — the sentexes a
  disjointness clash is *with*.  Asked only once a clash has been found, so an
  admissible assert never pays for it.

  **The sentex saying `(t x)`, not merely one that entails it.**  `matches-visible` is
  type-aware, so asking it for `(animal CI2)` returns the direct membership *and* every
  subtype membership that implies it — `(dog CI2)` where `dog` is under `animal`.  Both
  are true answers to \"is CI2 an animal\", and either would do if this were an
  existence check; but the handle picked becomes the side a clash is *reported as*, so
  taking `ffirst` let the report read `contradicts (dog CI2) (plant CI2)` or
  `contradicts (animal CI2) (plant CI2)` depending on which the retrieval strategy
  happened to enumerate first.  `res/*hierarchical-retrieval*` promises the answer set
  and says nothing about order — correctly, since order is not a thing a caller reading
  whole answers can observe — so that made a documented cost decision change what the
  KB reported, and through arbitration what it believed.  `clash_oracle_test` catches it
  under `VAELII_HIER=0`.

  So: every exact membership when one is stored, and a content-ordered choice among the
  entailing ones when none is — a purely inherited membership has no direct sentex to
  name.  `handle-namings` is that rule, and says the rest, including why the exact arm
  is plural: one sentence stated in two contexts a reader sees is two sentexes, and each
  forms its own pair.

  Two ways to reach the same set, gated by `res/*lead-side*`: `:scoped` runs the
  `matches-visible` reference (specs(t) walked down), anything else leads from the term's
  own postings (`membership-handles-led`)."
  [kb t x context]
  (if (= :scoped res/*lead-side*)
    (handle-namings (res/matches-visible kb (list t x) context) (list t x))
    (membership-handles-led kb t x context)))

(defn- disjoint-problems
  "A type membership (T X) where X already holds a type the taxonomy proves
  disjoint from T, as a violation map, or nil.  **Fully scoped to the asserting
  context**: the memberships read, the disjoint declaration, and the genl edges
  the disjointness closes under must all be visible from `context` — a
  context is only ever refused on grounds it can see.

  X is any term, not only an individual, so a `disjointMetatype` over predicate
  types separates the predicates it is declared of — one predicate cannot be both
  an `instanceRelationPredicate` and a `typeRelationPredicate`.

  `:opposing-handle` is the conflicting membership's own handle: the clash is between
  two sentexes, and naming the second is what lets `settle` weigh them.

  **Every** clash, not the first — `disjoint-problem` takes the first for the refusal
  path, where one reason to refuse is as good as another.  A *pair* is not a reason
  though, it is a fact about two sentexes, and a term holding three mutually disjoint
  types forms three pairs.  Stopping at the first would make which of them `settle`
  reports depend on the order the argument root hands the memberships back, which is
  handle order, which is arrival order.

  A pair per opposing **sentex**, not per opposing type, for the same reason one level
  down: the same membership stated in a general context and in one that sees it is
  two claims, of possibly different strength, and a reader below both is contradicted by
  each.  `functional-problems` counts its clashes that way already."
  [kb sentence context types]
  (when (= 1 (nm/arity sentence))
    (let [t (nm/functor sentence)
          x (first (nm/args sentence))]
      (when (checkable-term? x)
        (let [ts (:types (types x))]
          (when (seq ts)
            ;; one question, asked of each type the term holds: `t` and the asserting
            ;; context are fixed across the loop, and they are what most of the answer
            ;; is a function of
            (let [disjoint? (tax/disjointness-test (:taxonomy kb) t context)]
              (for [t' ts
                    :when (disjoint? t')
                    h    (membership-handles kb t' x context)]
                {:type :disjoint :sentence sentence :types [t t']
                 :opposing-handle h
                 :message (str "disjointness violated: " x " cannot be both "
                               t " and " t')}))))))))

(defn- disjoint-problem
  "The first disjointness clash, for the refusal paths."
  [kb sentence context types]
  (first (disjoint-problems kb sentence context types)))

(defn mergeable-values?
  "Could a functional clash between `x` and `y` be *resolved* by concluding they name
  one thing?  Only when both are plain symbols: the equality closure is a partition
  over symbols (`wff` refuses a compound, and a number or a string is not even an
  indexable term), so `(equals 1980 1990)` is not a sentence the KB can hold.

  This is the line between a clash that is knowledge and a clash that is an error.
  Two spellings of a person may denote one woman; 1980 and 1990 are two numbers and
  no merge can make them one, so a numeric functional clash stays the hard rejection
  it has always been."
  [x y]
  (and (symbol? x) (symbol? y) (not (sx/variable? x)) (not (sx/variable? y))))

(defn- first-per-slot
  "`[handle value via]` triples with the content-first `via` kept per `[handle value]`.

  Several marked predicates in one chain each probe their own slot, and a super's probe
  fans down over its specs — so one stored filler comes back under every mark above it.
  That is one clash, not three: the pair is `[this sentence, that filler]` whichever
  declaration convicts it.  Lazy, because `functional-problem` takes the first and an
  eager dedup would walk a whole functional extent to answer whether one exists."
  [triples]
  (letfn [(step [xs seen]
            (lazy-seq
             (when-let [s (seq xs)]
               (let [t (first s), k [(nth t 0) (nth t 1)]]
                 (if (contains? seen k)
                   (step (rest s) seen)
                   (cons t (step (rest s) (conj seen k))))))))]
    (step triples #{})))

(defn functional-clashes
  "The believed `[handle value via]` triples that already fill a functional slot for the
  same first argument with something other than `b` — the clash a `(functional P)`
  declaration turns into either a rejection or an equality.

  `via` is the predicate carrying the mark this clash is against, which is the
  sentence's own where it carries one and a **super-predicate** where the mark descends
  (`tax/props-over`).  Two `fatherOf` mothers for one child are two `parentOf` values,
  so `(functional parentOf)` convicts them; reading the mark off the exact functor made
  that bypassable through the sub-predicate door while the *slot probe* already fanned
  down the hierarchy, so which spelling arrived second decided whether the clash
  existed.

  The slot is probed **at the marked predicate**: `(parentOf a ?v)` finds a filler
  written either way through the matcher's fan, where `(fatherOf a ?v)` would miss one
  written at the general spelling.  Empty when nothing above the sentence's predicate is
  marked — one map read on a KB that declares nothing functional, which is every bulk
  load."
  [kb sentence context]
  (let [pred (nm/functor sentence)]
    (when (= 2 (nm/arity sentence))
      (let [[a b] (nm/args sentence)]
        (first-per-slot
         (for [q       (sort (tax/props-over (:taxonomy kb) :functional pred context))
               [h bnd] (res/matches-visible kb (list q a '?fv) context)
               :let    [v (get bnd '?fv)]
               :when   (and v (not= v b))]
           [h v q]))))))

(defn- functional-problems
  "A (P a b) where P is functional and `a` already has a value for P that no
  equality could reconcile with `b` (visible from `context`), as a violation map,
  or nil.

  A clash between two **symbols** is not an error: `(functional motherOf)` plus
  two spellings of Tom's mother is exactly where co-reference shows up, and the KB
  *derives* `(equals V1 V2)` from it (see `special/derive-functional-equalities`)
  instead of refusing the second fact.  Everything else — two numbers, two strings, a
  compound — is still the hard contradiction it was, because no merge can make two
  numbers one thing.  See docs/equality.md.

  Every clash, not the first, for the reason `disjoint-problems` gives: a slot filled
  with three irreconcilable values forms three pairs, and which of them is reported may
  not depend on the order the extent came back in.

  The message names the predicate the mark is on, which is the sentence's own unless the
  declaration descended — the slot that is already filled is that predicate's."
  [kb sentence context]
  (let [b (second (nm/args sentence))]
    (for [[h v via] (functional-clashes kb sentence context)
          ;; violation iff no merge could reconcile them: a clash between two symbols is
          ;; not a violation but a co-reference the KB *derives* an equality from (see
          ;; `special/derive-functional-equalities`), everything else is the hard
          ;; contradiction it always was.  A "no merge already has" guard was here as
          ;; `(not (tax/same-class? tax v b))`, but the partition is over symbols, so
          ;; `same-class?` can only hold of two symbols — and `mergeable-values?` has
          ;; already excluded that whole case, so the conjunct only ever ran where it was
          ;; false and could not change the answer.  Deleted rather than left as an
          ;; unscoped read to be widened into: the derivation twin keeps the guard, where
          ;; it is live and scoped (`special/derive-functional-equalities`), and if this
          ;; door ever admits a symbol clash it wants that same context-scoped read, not
          ;; the global one this was.
          :when (not (mergeable-values? v b))]
      {:type :functional :sentence sentence :existing v :new b :opposing-handle h
       :pred via
       :message (str "functional violation: " via " of "
                     (first (nm/args sentence)) " is already " v ", not " b)})))

(defn- functional-problem
  "The first functional clash, for the refusal paths."
  [kb sentence context]
  (first (functional-problems kb sentence context)))

(defn- asymmetry-problems
  "Every `(asymmetric P)` violation a sentence commits in `context`.

  `(asymmetric largerThan)` says `(P a b)` and `(P b a)` cannot both hold, so a claim
  whose **converse** is known-true is a contradiction rather than an addition.  The
  converse counts whether it was stated directly or reached by argument-position
  preservation — `(largerThan dog cat)` reaches `(largerThan cat maine_coon)` and every
  other pair below it, and a strict claim is exactly as binding there as where it was
  written (`vaelii.impl.inherit`).

  Only a **`:monotonic`** opposing claim refuses.  That is the whole strict/typical
  distinction, and it is read off the claim rather than the vocabulary: known-true
  content is the fixed background, so contradicting it is an error, while a `:default`
  generality is something a more specific statement is *entitled* to override — there
  the inheritance is undercut and never fires, so no clash reaches here at all.

  A **`:default`** opposing claim is still reported, and that is what makes a relation
  declared not to hold both ways stop holding both ways in silence: the violation is
  not a refusal (`refuses-assert?` reads the class), it is the pair `settle` arbitrates
  — at equal class, a represented dilemma in `(contradictions kb)`.

  The **strongest** surviving opposing claim is reported first, ties broken on the
  context name and then on the sentence, for the reason `inherit/strongest-per-tuple`
  gives: taking the first found would key an admission decision on handle iteration
  order, and handles are allocated in assertion order.  The sentence is what settles a
  tie the context name cannot — argument preservation reaches the converse from a
  sub-predicate, so two claims of equal class in one context are ordinary, and a key
  that stops at the context leaves that pair to iteration order.

  **One violation per opposing sentex**, in that order, for the reason
  `disjoint-problems` gives: the converse stated in a general context and again in
  one that sees it is two claims, and each is its own pair with the sentence here.  The
  refusal path takes the first and is therefore deciding against the strongest, which is
  the claim it always decided against; the discovery weighs all of them.  Deduped on the
  handle, since preservation can reach one stored claim by several routes.

  That is why the converse is read **twice**.  `inherit/surviving` answers what is
  *inherited* — one claim per tuple, the strongest — which is the right answer to whether
  the converse is licensed, and drops the duplicates on purpose
  (`inherit/strongest-per-tuple`).  The duplicates are exactly what a pair needs, so the
  sentexes literally stating the converse are read beside it and merged on the handle.
  Nothing is resurrected by that: a claim at the goal's own tuple is the most specific
  there is, so `undercut?` never displaced one.

  **The mark is read up the predicate hierarchy** (`tax/props-over`) where the converse
  probe already fanned *down* it, and the asymmetry between those two directions is what
  the descension closes.  `(asymmetric parentOf)` with `(genl fatherOf parentOf)`
  convicted `(parentOf b a)` against a stored `(fatherOf a b)` — `matches-visible` fans
  the converse over `parentOf`'s specs — and admitted the same pair written the other way
  round, because `fatherOf` carries no mark of its own.  Which spelling arrived second
  decided whether the pair existed.

  The converse is probed **at the marked predicate**, not at the sentence's own: it is
  `(parentOf b a)` that `(asymmetric parentOf)` forbids beside `(parentOf a b)`, and
  probing `(fatherOf b a)` would miss a converse stated at the general spelling while
  probing the general one finds both through the fan.  Several supers may carry the mark;
  each contributes its own converse, and the results merge on the handle exactly as the
  two reads of one converse do.

  **A sentence is not its own opposing claim.**  For a self tuple `(P a a)` the converse
  *is* the sentence, so once one is stored it answers its own probe: asserting `(P a a)`
  a second time convicts it against the copy the first assert left, and content the KB
  already believes refuses rather than deduping to the handle it already has.  Asymmetry
  does not hand you irreflexivity here — `CxCore.txt` says a self tuple is admitted, and
  `docs/taxonomy.md` and `docs/inherit.md` say it twice more — so admitting it once and
  refusing it forever after is neither reading.

  **Sentence and context both**, which is what makes it self-identity rather than a rule
  about self tuples: `(P a a)` in one context and `(P a a)` in another are two claims and
  a real pair — each is the other's converse across the context boundary, and
  `a-self-tuple-in-two-contexts-orders-on-the-context` is the case that reads them.  What
  is excluded is the sentence meeting *itself*, which is a comparison on the canonical
  sentence since the checks run before this one has a handle.  For `a` ≠ `b` the converse
  canonicalizes to a different sentence anyway, and a predicate for which it did not
  would be symmetric rather than asymmetric.

  **The context that decides self is the sentence's own — `home` — and not the asker.**
  The two are the same at the door and differ wherever `settle` asks a stored sentex's
  question from a *vantage* that sees more than its own context (`clash-vantages`): there,
  keying self on the asker excluded the twin **stored in the vantage** as though the
  candidate were it.  `(P a a)` written in a general context and again in one that sees it
  is a real pair, and it was reported or not according to which of the two was written
  last — the specific one arriving second convicts from its own context and is found,
  the general one arriving second is asked from the specific vantage and threw its partner
  away.  Order-dependence in what the KB believes, which `clash_oracle_test`'s streams
  measure and `docs/nmtms.md` forbids.

  Ground binary sentences only; an open or n-ary one has no converse to speak of."
  ([kb sentence context] (asymmetry-problems kb sentence context context))
  ([kb sentence context home]
   (let [pred (nm/functor sentence)
         args (vec (nm/args sentence))]
     (when (and (symbol? pred) (= 2 (count args))
                (every? sx/ground-term? args))
       (let [marked   (sort (tax/props-over (:taxonomy kb) :asymmetric pred context))
             ;; read once the mark is there to convict against, so an unmarked predicate
             ;; pays no canonicalization for it
             self     (when (seq marked) (:sentence (res/kb-sentex kb sentence context)))
             claims   (for [q marked
                            :let [converse (list q (second args) (first args))
                                  ;; compared against the *canonical* spelling: the matcher
                                  ;; probes through `kb-sentex`, so a comparison
                                  ;; predicate's converse is stored folded (`greaterThan B
                                  ;; A` as `lessThan A B`) and the raw form would match no
                                  ;; record — leaving `stated` empty and the duplicate
                                  ;; opposing sentexes this second read exists to supply
                                  ;; unsupplied
                                  stored-c (:sentence (res/kb-sentex kb converse context))
                                  stated   (for [m   (res/matches-visible kb converse context)
                                                 :let [sxr (nth m 2) h (first m)]
                                                 :when (= stored-c (:sentence sxr))]
                                             {:polarity :for :handle h
                                              :sentence (:sentence sxr)
                                              :context (:context sxr)
                                              :class (or (jtms/defeat-class (:tms kb) h)
                                                         :default)})]
                            o (concat (filter #(= :for (:polarity %))
                                              (inherit/surviving kb converse context))
                                      stated)
                            :when (not (and (= self (:sentence o))
                                            (= home (:context o))))]
                        (assoc o ::mark q ::converse converse))
             opposing (->> claims
                           ;; one `pr-str` + two `str` in the key — built once per claim,
                           ;; not per comparison; the `[rank …]` tuple orders under `compare`
                           (nm/sort-by-content-key (juxt #(- (strength/rank-of (:class %)))
                                                         #(str (:context %))
                                                         #(pr-str (:sentence %))
                                                         #(str (::mark %)))
                                                   compare)
                           (reduce (fn [acc o]
                                     (if (some #(= (:handle %) (:handle o)) acc)
                                       acc
                                       (conj acc o)))
                                   []))]
         (for [o opposing
               :let [q (::mark o) converse (::converse o)]]
           {:type :asymmetric :sentence sentence :pred q
            :opposing (:sentence o) :opposing-handle (:handle o)
            :message (str "asymmetric: " q " cannot hold both ways, and "
                          (pr-str (:sentence o))
                          (if (= :monotonic (:class o)) " is known true" " is believed")
                          (when (not= (:sentence o) converse)
                            (str " (which reaches " (pr-str converse)
                                 " by argument preservation)")))}))))))

(defn- asymmetry-problem
  "The strongest `(asymmetric P)` violation, for the refusal paths."
  [kb sentence context]
  (first (asymmetry-problems kb sentence context)))

(defn- chain-steps
  "The believed steps matching `pattern` from `context`, as `[handle sentex binding]`
  triples — `binding` being what `var` bound.

  One `matches-visible` probe, so the predicate's **spec closure** is fanned exactly as
  it is everywhere else a mark descends: a probe at `parentOf` reads a `fatherOf` step,
  and a step written at the general spelling is read by a probe at it.  Belief-filtered
  by the matcher, so a defeated step is no step."
  [kb pattern context var]
  (for [[h b sx] (res/matches-visible kb pattern context)]
    [h sx (get b var)]))

(defn- lead-from-source?
  "For the closing role, is `(q a ?m)` the smaller end to enumerate than `(q ?m b)`?

  Both ends enumerate the **same** set of midpoints — `{m : (q a m) ∧ (q m b)}` — so this
  decides only which side is walked and which is probed per candidate, never the answer.
  The two argument roots are read for their cardinality alone (`could-clash?` reads the
  same counts the same over-approximating way: they span every predicate and either
  polarity, so they bound the walk rather than describing it).  A non-symbol has no root
  and cannot be led from."
  [kb a b]
  (let [idx  (:index kb)
        wide Long/MAX_VALUE
        out  (if (symbol? a) (p/count-with-arg idx 1 a) wide)
        in   (if (symbol? b) (p/count-with-arg idx 2 b) wide)]
    (<= out in)))

(defn- chain-triples
  "The forbidden triples `{(q a c), (q a m), (q m c)}` the tuple `(q a b)` is a member of,
  as `[first-step second-step closing]` in **role** order, each element a stored sentex or
  `::self` for the tuple being checked.

  Three roles, and all three are asked, because the settle's discovery walks the sentexes
  a settle *moved* and forms the nogood from whichever member it holds: a triple only two
  of whose members could convict it would be found or missed according to which one
  arrived last (`clash_oracle_test`, \"conviction has to be symmetric\").  The tuple is

  * the **closing** step, over each midpoint `m` with `(q a m)` and `(q m b)` believed;
  * the **first** step, over each `c` with `(q b c)` and the closing `(q a c)` believed;
  * the **second** step, over each `z` with `(q z a)` and the closing `(q z b)` believed.

  The closing role leads from whichever argument root is smaller (`lead-from-source?`)
  and probes the far leg bound; the other two roles have one bound end each and no choice
  to make.  A step reachable **only** by argument preservation is not enumerated — see
  the docstring of `antitransitivity-problems`."
  [kb q a b context]
  (concat
   (if (lead-from-source? kb a b)
     (for [[_ _ m :as s1] (chain-steps kb (list q a '?m) context '?m)
           s2             (chain-steps kb (list q m b) context nil)]
       [s1 s2 ::self])
     (for [[_ _ m :as s2] (chain-steps kb (list q '?m b) context '?m)
           s1             (chain-steps kb (list q a m) context nil)]
       [s1 s2 ::self]))
   (for [[_ _ c :as s2] (chain-steps kb (list q b '?c) context '?c)
         cl             (chain-steps kb (list q a c) context nil)]
     [::self s2 cl])
   (for [[_ _ z :as s1] (chain-steps kb (list q '?z a) context '?z)
         cl             (chain-steps kb (list q z b) context nil)]
     [s1 ::self cl])))

(defn- antitransitivity-problems
  "Every `(antiTransitive P)` violation a sentence commits in `context`.

  `(antiTransitive parentOf)` says a two-step chain forbids the direct step: believing
  `(P a m)` and `(P m c)` makes `(P a c)` contradictory, the dual of `transitive` and the
  reason no predicate is declared both (`(disjoint transitive antiTransitive)`).  So the
  conviction names **two** other believed sentexes rather than one, and the violation
  carries `:opposing-handles` where the pairwise kinds carry `:opposing-handle` —
  `settle` weighs the three together as one nogood (docs/nmtms.md).

  Only a chain every step of which is **`:monotonic`** refuses, which is
  `asymmetry-problems`' rule read over a set rather than over a single claim: the
  opposing class stamped on the violation is the *weakest* of the two steps
  (`opposing-class`), so `refuses-assert?` refuses exactly when the newcomer could never
  be believed beside them and arbitrates otherwise.  At equal class the triple is a
  represented dilemma in `(contradictions kb)` — three claims, none of which the engine
  will pick between, which is what `decide-nogood` does with any tie.

  **The mark is read up the predicate hierarchy** (`tax/props-over`) and the steps are
  probed **at the marked predicate**, exactly as `asymmetry-problems` reads its converse:
  `(antiTransitive parentOf)` with `(genl fatherOf parentOf)` convicts a `fatherOf` chain,
  and a chain written half at each spelling is one chain.  Empty when nothing at or above
  the sentence's predicate is marked — one map read on a KB that declares none, which is
  every bulk load.

  **A sentence is not its own step**, on the rule `asymmetry-problems` states: a stored
  copy of the very claim being checked (same canonical sentence, same `home` context) is
  excluded, so re-asserting a fact does not convict it against itself.  `home` is the
  sentence's own context and not the asker's, for the reason that docstring records at
  length: a twin stored in the *vantage* a stored sentex is asked from is a partner and
  not a self.  What that leaves
  is real and is kept: a triple that collapses to two distinct sentexes — `(P a b)` beside
  `(P b b)` — is a two-member nogood weighed like any pair, and a self tuple `(P a a)`,
  whose whole triple is itself, names no other sentex at all and so convicts nothing.
  `antiTransitive` does not hand you `irreflexive` any more than `asymmetric` does
  (docs/taxonomy.md); a KB that wants the self tuple refused declares the mark that
  refuses it.

  **A step reached only by argument preservation is not enumerated.**
  `asymmetry-problems` reads `inherit/surviving` beside the stored converse; here that
  would make conviction one-sided — preservation reads a goal's arguments upwards, so the
  specific claim asks about the general one and never the reverse (docs/nmtms.md, \"Where
  conviction is one-sided\") — and a triple only one of whose members convicts is a triple
  the incremental discovery finds or misses by arrival order.  A stated absence, not an
  oversight: the spec fan above is what the mark's descension needs, and it is symmetric.

  **Every** violation, not the first, for the reason `disjoint-problems` gives: a hub term
  chains several ways, and which triple is reported may not depend on the order the
  postings came back in.  Deduped on the pair of opposing handles, so one triple reached
  under two marks above the predicate, or from two roles, is one violation — the
  content-first mark kept, as `first-per-slot` keeps its `via`.  Ordered weakest-opposing
  first, so the refusal path (which takes the first) decides against the chain that most
  nearly refuses, and then by content, so nothing rests on iteration order.

  Ground binary sentences only; an open or n-ary one is no step of a chain."
  ([kb sentence context] (antitransitivity-problems kb sentence context context))
  ([kb sentence context home]
   (let [pred (nm/functor sentence)
         args (vec (nm/args sentence))]
     (when (and (symbol? pred) (= 2 (count args))
                (every? sx/ground-term? args))
       (let [tms    (:tms kb)
             [a b]  args
             marked (sort (tax/props-over (:taxonomy kb) :anti-transitive pred context))
             ;; read once the mark is there to convict against, so an unmarked predicate
             ;; pays no canonicalization for it
             self   (when (seq marked) (:sentence (res/kb-sentex kb sentence context)))
             self?  (fn [s] (and (= self (:sentence s)) (= home (:context s))))
             ;; the triple as sentences, in role order, with the checked sentence in its
             ;; own place — what the message reads and what orders one violation against
             ;; another
             said   (fn [s] (if (= ::self s) self (:sentence (second s))))
             found  (for [q     marked
                          steps (chain-triples kb q a b context)
                          :let  [others (remove #(or (= ::self %) (self? (second %))) steps)]
                          ;; every member is this very claim (a self tuple's whole
                          ;; triple), so there is no second sentex to weigh
                          :when (seq others)
                          :let  [hs    (mapv first others)
                                 chain (mapv said steps)]]
                      {:type :anti-transitive :sentence sentence :pred q
                       :chain chain
                       :opposing-handles hs
                       :weakest (reduce strength/min (map #(jtms/defeat-class tms %) hs))
                       :message (str "antiTransitive: " q " chains " (pr-str (first chain))
                                     " and " (pr-str (second chain))
                                     ", so the direct step " (pr-str (nth chain 2))
                                     " cannot hold too")})]
         (->> found
              (nm/sort-by-content-key
               (juxt #(- (strength/rank-of (:weakest %)))
                     #(pr-str (:chain %))
                     #(str (:pred %)))
               compare)
              (reduce (fn [[acc seen] v]
                        (let [k (set (:opposing-handles v))]
                          (if (contains? seen k) [acc seen] [(conj acc v) (conj seen k)])))
                      [[] #{}])
              first
              (mapv #(dissoc % :weakest))))))))

(defn- antitransitivity-problem
  "The violation whose chain most nearly refuses, for the refusal paths."
  [kb sentence context]
  (first (antitransitivity-problems kb sentence context)))

(defn- irreflexivity-problems
  "Every `(irreflexive P)` violation a self tuple `(P a a)` commits in `context`.

  `(irreflexive largerThan)` says `(P a a)` cannot hold, so a self tuple is contradictory
  the moment it is written — unlike `asymmetric`, which admits it (`asymmetry-problems`
  spells out why).  A lone tuple names no second sentex to weigh against, so this is a
  **refusal** at the door and never an arbitrable nogood: `refuses-assert?` reads no
  class here, and the derivation path drops a self tuple a rule concluded.

  The mark is read up the predicate hierarchy (`tax/props-over`), like the two clashes
  above it: `(irreflexive parentOf)` refuses `(fatherOf a a)` too, the sub's tuples being
  the super's.  Ground binary self tuples only — `a` must equal `b`, or there is no self
  tuple to refuse, and a predicate whose two arguments differ has an ordinary tuple that
  irreflexivity says nothing about.

  No `:opposing-handle`: there is no pair.  A declaration arriving after a self tuple was
  stored is the `arity` case rather than the `asymmetric` one — the tuple stands and the
  late mark reports rather than defeats, since promoting a lone-tuple conviction to a
  nogood would make belief depend on how many settles had run (docs/nmtms.md)."
  [kb sentence context]
  (let [pred (nm/functor sentence)
        args (vec (nm/args sentence))]
    (when (and (symbol? pred) (= 2 (count args))
               (= (first args) (second args))
               (every? sx/ground-term? args))
      (for [q (sort (tax/props-over (:taxonomy kb) :irreflexive pred context))]
        {:type :irreflexive :sentence sentence :pred q
         :message (str "irreflexive: " q " cannot hold of a thing and itself, but "
                       (pr-str sentence) " does")}))))

(defn- irreflexivity-problem
  "The first `(irreflexive P)` violation, for the refusal paths."
  [kb sentence context]
  (first (irreflexivity-problems kb sentence context)))

(defn antisymmetric-converses
  "The believed `[handle via]` pairs whose sentence is the converse of `(P a b)` under an
  `(antiSymmetric P)` mark — the facts `(P b a)` that, with the sentence, force
  `(equals a b)`.  Deduped on the converse's handle; `via` is the marked predicate the
  conviction reads through (the sentence's own where it carries the mark, a
  super-predicate where the mark descends), which the equality derivation names in its
  justification.

  The converse is probed **at the marked predicate** and its mark read **up** the
  hierarchy, exactly as `asymmetry-problems` and `functional-clashes` do and for the same
  reason: `(antiSymmetric parentOf)` with `(genl fatherOf parentOf)` must convict a
  `fatherOf` pair whichever spelling arrives last, so reading the mark off the exact
  functor would leave the pair found or missed by arrival order.

  `matches-visible` over the ground converse is the whole probe: it fans **down** to the
  sub-predicate spellings (so `(atOrAbove Alice Bob)` finds a stored `(atOrAboveStrict
  Alice Bob)`) and folds a comparison predicate's converse internally, so no exact-sentence
  filter is wanted here — one would drop exactly the descended pair the up-read exists to
  catch.  Ground binary sentences only."
  [kb sentence context]
  (let [pred (nm/functor sentence)
        args (vec (nm/args sentence))]
    (when (and (symbol? pred) (= 2 (count args))
               (every? sx/ground-term? args))
      (let [[a b]   args
            triples (for [q (sort (tax/props-over (:taxonomy kb) :anti-symmetric pred context))
                          m (res/matches-visible kb (list q b a) context)]
                      [(first m) nil q])]
        (map (fn [[h _ via]] [h via]) (first-per-slot triples))))))

(defn- antisymmetry-problems
  "The `(antiSymmetric P)` violations a sentence commits in `context` that cannot be
  **merged** away — a believed converse whose two arguments no equality could reconcile
  (two numbers, a compound, a self tuple's trivial case aside).

  The mergeable case is not here: two symbols denoting one thing is a co-reference the KB
  *derives* `(equals a b)` from and merges (`special/derive-antisymmetric-equalities`),
  exactly as `functional-problems` leaves a symbol clash to `derive-functional-equalities`.
  What is left is the hard contradiction — `(P 1 2)` beside `(P 2 1)` under an
  antisymmetric `P` forces `1 = 2`, which no merge can make true — and, like a numeric
  functional clash, it **refuses** at the door: this carries no arbitrable class, so
  `refuses-assert?` reads its default and says no.  A self tuple's arguments are equal, so
  it is admitted rather than refused."
  [kb sentence context]
  (let [args (vec (nm/args sentence))]
    (when (= 2 (count args))
      (let [[a b] args]
        (when (and (not= a b) (not (mergeable-values? a b)))
          (for [[_ via] (antisymmetric-converses kb sentence context)]
            {:type :anti-symmetric :sentence sentence :pred via
             :message (str "antisymmetric: " via " with " (pr-str sentence)
                           " and its converse forces " (pr-str (list 'equals a b))
                           ", which no merge can make hold")}))))))

(defn- antisymmetry-problem
  "The first non-mergeable `(antiSymmetric P)` violation, for the refusal paths."
  [kb sentence context]
  (first (antisymmetry-problems kb sentence context)))

(defn- checked-sentence
  "The body the definitional checks see: the double-negation-eliminated positive body,
  so a `(not (not (dog Muffet)))` is still arg/disjoint/functional-checked and a genuine
  negation is not."
  [sentence]
  (or (sx/positive-body sentence) sentence))

(defn- constraint-problem
  "The first definitional violation for `chk` in `context`, as a value, or nil
  when the sentence is admissible.  The checks are stated once, here, and every
  path reads them: `constraint-checks` (assert) throws the value,
  `constraint-violation` (derivation) records it.

  `types` is the shared membership reader (`kb/membership-reader`).  The arms that ask
  what types a term holds ask about the same few terms — the sentence's arguments and
  its predicate — and between them ask several times each: the arity arm reads the
  predicate's memberships for three spellings and again for `variableArity`, `arg`
  reads an argument's twice per constraint, and for a unary sentence the disjointness
  arm wants the very memberships `arg` just read.

  The answer is stamped with the opposing sentex's defeat class where it names one, so
  the two callers decide refusal-versus-nogood from the value alone rather than each
  reaching back into the TMS for the same reading."
  [kb chk context types decls]
  (with-opposing-class
    kb
    (or (arity-problem kb chk context types)
        (edge-arity-problem kb chk context types)
        (declaration-arity-problem kb chk context types)
        (args-problem kb chk context types decls)
        (inter-args-problem kb chk context types decls)
        (genls-problem kb chk context decls)
        (args-quoted-problem kb chk context types decls)
        (declaration-problem kb chk context types)
        (disjoint-problem kb chk context types)
        (asymmetry-problem kb chk context)
        (functional-problem kb chk context)
        (irreflexivity-problem kb chk context)
        (antisymmetry-problem kb chk context)
        (antitransitivity-problem kb chk context))))

;; ---- what the argument constraints *entail* ------------------------------
;; `args-problem` and `genls-problem` read `arg` / `genlArg` as constraints to test,
;; and their open-world floor is the same in both: an argument with no visible place in
;; the genl hierarchy cannot violate anything, so it passes and nothing is learned.  But
;; the declaration says what the argument *is*, and a KB told twice over that Fred fills
;; an `animal` slot still cannot answer `(animal Fred)` with a record.
;;
;; So the declarations are read a second way — as entailments.  The pairing is what is
;; entailed: **one entailment per (sentence, applicable declaration) pair**, drawn
;; whenever the declaration speaks for the context and names a type the hierarchy holds.
;;
;; **Nothing narrows that on grounds of redundancy**, and the reason is the invariant
;; rather than taste.  Every candidate narrowing — "the argument already has a type
;; reaching this one", "the type is already stored" — asks about *derived state*, which
;; is a function of what has arrived so far.  Withhold on those grounds and
;; `(dog Fred)` arriving before the declaration suppresses a materialization that the
;; same three sentences in the other order produce; withhold the *justification* on
;; those grounds and a second fact entailing the same type contributes no support, so
;; retracting the first sweeps a type the second still licenses, and which of the two
;; holds it up depends on which arrived first.  Both are belief varying with arrival
;; order, which is the one thing it may not do (docs/nmtms.md).
;;
;; So every applicable pair draws its entailment and `find-or-create-sentex` /
;; `has-justification?` do the deduplication at the point where it is a property of
;; content: one sentex per sentence, one justification per pair, whatever the order.
;; That a subsuming membership would also have reached the type is not a reason to
;; withhold a justified record — being a record is the whole of what this adds.
;;
;; Nothing here writes: the entailment is a **value**, and the sentex that would
;; justify it does not exist yet — the checks run before anything is stored, so a
;; refusal leaves nothing behind.  `special/deduce-arg-types` materializes it in the
;; post-store slot, beside the decontextualization lift, where there is a handle to
;; hang `[source-handle declaration-handle]` on.

(def ^:dynamic *assertive-arg-types?*
  "Do the argument constraints *entail* as well as constrain?

  **Off by default.**  A KB that derives types it cannot retract cleanly is worse than
  one that derives none, and entailing changes what a KB *contains* rather than only
  what it answers — so it is opt-in, and off leaves the constraint reading alone
  (docs/argtypes.md).

  `binding` it is the ordinary way in.  `VAELII_ASSERTIVE_ARG_TYPES=1` sets the root
  value instead, which is what lets the whole suite be run under it — the parity gate
  that says the entailment is additive rather than a different engine."
  (config/assertive-arg-types?))

(def ^:private universal-context
  "The one context every other sees.  A declaration stated there speaks for every
  context, so it entails locally wherever it is visible; `special/universal-context` is
  the same symbol, named there for the lift."
  'CxUniverse)

(defn- mintable-type?
  "Is `t` a type a membership can be minted in — a name the genl hierarchy actually
  holds?

  A **global** read, like `genls-problem`'s individual floor and for the same reason:
  this asks what the name *is*, not what a context can see of it, and an entailment
  drawn in a context that cannot see `thing` would be an entailment about nothing.
  A name the hierarchy does not hold is not a type we invent a membership in — which
  is where a structural constraint (an argument that must be a number, a string) lands
  without needing a list of exemptions to keep in step."
  [tax t]
  (and (symbol? t) (not (sx/variable? t)) (tax/genl? tax t 'thing)))

(defn- declares-locally?
  "Does the declaration stored at `dh` speak **for** `context`, rather than merely
  reaching it?

  A declaration is *inherited* by every descendant of the context it was written in,
  and there it constrains: an ancestor schema enforces its argument types in every
  context below it.  It does not *entail* there — an upper-band schema would
  otherwise spray derived `(T x)` memberships across every context that inherits it,
  claims no author of that context made.  So only a declaration written in the
  context being checked, or in `CxUniverse` (which speaks for every context by
  construction), draws the entailment.

  One record fetch, asked last of the conditions so it is paid only for a declaration
  that would otherwise mint."
  [kb dh context]
  (let [dc (:context (p/get-sentex (:records kb) dh))]
    (or (= dc context) (= dc universal-context))))

(defn edge-support
  "The handles of the `genl` edge supporters a declaration written of `via` travels down
  to reach `pred` — empty when `via` **is** `pred`, a declaration that rests on no edge.

  Anything **derived** through a super-predicate's declaration rests on three things
  rather than two: the fact, the declaration, and the subsumption that makes the fact
  one of the declaration's tuples.  Naming only the first two would leave the derivation
  standing after the edge was retracted — a derived record supported by content that no
  longer entails it, which is the exact failure justifying a derivation at all is meant
  to prevent.  Both descending derivations read it: the argument-type entailment below,
  and the equality a descended `(functional P)` mints
  (`special/derive-functional-equalities`).

  One supporter per edge on a shortest **visible** path (`tax/reach-support`), which is
  the witness rule everything else depending on a reachability takes: a justification is
  a conjunction of supports, not a proof that no other route exists, so when the named
  route goes what rested on it goes and is re-derived from whatever survives."
  [kb pred via context]
  (if (= pred via)
    []
    (mapv first (tax/reach-support (:taxonomy kb) :genl pred via context))))

(defn- arg-entailments
  "The entailments one argument-constraint kind draws over `sentence`'s arguments in
  `context` — a seq of `{:assert <sentence> :because [decl-handle edge-handle …]
  :position n :kind arg|genlArg}`.

  `eligible?` is the kind's reading of \"this argument is the sort of term the
  entailment can be about\", and it is a property of the **term** alone, never of what
  the KB has learned about it so far — which is what keeps the answer a function of
  content.  It doubles as the early-out: no eligible argument means no declaration can
  say anything, and the declaration query is never run.

  `:because` leads with the declaration and carries the `genl` edges it descended
  through, so the entailment holds only while the subsumption that licensed it does."
  [kb sentence context decls kind eligible? mint]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (:taxonomy kb)]
    (when (and (symbol? pred) (some eligible? as))
      (for [d     (decls kind)
            :let  [dh  (nth d 0)
                   b   (nth d 1)
                   n   (get b '?n)
                   t   (get b '?type)
                   arg (arg-at as n)]
            :when (and arg (eligible? arg)
                       (mintable-type? tax t)
                       (declares-locally? kb dh context))]
        {:assert  (mint arg t)
         :because (into [dh] (edge-support kb pred (declared-of d) context))
         :position n :kind kind}))))

(defn- inter-arg-entailments
  "The entailments `interArg` draws over `sentence`'s arguments in `context`.

  Exactly as strong as `arg`'s, and drawn under the same condition the check convicts
  on: the trigger argument must *already* be established as a `T`, so the entailment is
  what the declaration says once its antecedent holds.  A dormant constraint entails
  nothing, which is the same asymmetry `inter-args-problem` reads.

  `types` is therefore needed here where `arg-entailments` needs none — the unconditional
  kinds ask nothing about what the KB has learned, and this one has to.  Behind the same
  O(1) gate `inter-args-problem` is, and for the same reason."
  [kb sentence context types decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (:taxonomy kb)]
    (when (and (symbol? pred) (some checkable-term? as)
               (pos? (p/count-with-functor (:index kb) 'interArg)))
      (for [d     (decls 'interArg)
            :let  [dh      (nth d 0)
                   b       (nth d 1)
                   n       (get b '?n)
                   t       (get b '?type)
                   m       (get b '?m)
                   u       (get b '?utype)
                   trigger (arg-at as n)
                   target  (arg-at as m)]
            :when (and trigger target
                       (checkable-term? trigger) (checkable-term? target)
                       (symbol? t)
                       (kb/isa-among? (:closures (types trigger)) t)
                       (mintable-type? tax u)
                       (declares-locally? kb dh context))]
        {:assert  (list u target)
         :because (into [dh] (edge-support kb pred (declared-of d) context))
         :position m :kind 'interArg}))))

(defn constraint-entailments
  "What `sentence`'s visible argument declarations entail about its arguments in
  `context` — a vec of `{:assert <sentence> :because [decl-handle edge-handle …]
  :position n :kind arg|genlArg|interArg}`, empty when they entail nothing.

  `(arg parentOf 1 animal)` over `(parentOf Fred Mary)` entails `(animal Fred)`;
  `(genlArg partType 1 physical_object)` over `(partType wheel_kind axle_kind)` entails
  `(genl wheel_kind physical_object)`; `(interArg eats 1 carnivore 2 meat)` over
  `(eats Rex Chunk)` entails `(meat Chunk)` — but only once `Rex` is known to be a
  carnivore, which is the condition the declaration is *about*.  An **individual** in an
  `genlArg` position is convicted by `genls-problem` rather than given an edge, so it is
  ineligible here — said at the point it matters rather than relying on the check having
  run first.

  One entry per applicable declaration, with no narrowing for redundancy: see the
  commentary above for why every candidate narrowing would make belief depend on
  arrival order.  Deduplication is the materializer's, where it is keyed on content.

  **Reads only.**  The caller decides whether to store, and the caller is
  `special/deduce-arg-types`, which mints each one as a derived sentex justified by
  `[the triggering fact, the declaration]` — so retracting either takes the type back."
  ([kb sentence context]
   (constraint-entailments kb sentence context
                           (kb/membership-reader kb context)
                           (declaration-reader kb (nm/functor sentence) context)))
  ([kb sentence context types decls]
   (when *assertive-arg-types?*
     (vec (concat (arg-entailments kb sentence context decls 'arg
                                   checkable-term?
                                   (fn [arg t] (list t arg)))
                  (arg-entailments kb sentence context decls 'genlArg
                                   #(and (checkable-term? %) (not (nm/individual? %)))
                                   (fn [arg t] (list 'genl arg t)))
                  (inter-arg-entailments kb sentence context types decls))))))

(defn constraint-checks
  "Throw the first definitional violation as typed ex-info — the assert path.

  Not every violation refuses.  One that names an opposing *believed* sentex is a
  nogood, and whether the writer is told no is `refuses-assert?`'s question: against
  known-true content, yes (admitting it would store what the KB can never believe);
  against a defeasible claim, the sentence is admitted and `settle` arbitrates the pair
  it forms.  An admitted clash is **not** reported here — settle discovers it from the
  relabelled region, which is what makes the discovery route-agnostic and the answer
  the same in every arrival order.

  Returns the **entailments** the argument constraints draw over an admissible
  sentence (`constraint-entailments`), for the caller to materialize once the sentex
  it would be justified by exists.  Empty unless `*assertive-arg-types?*`."
  [kb sentence context]
  (let [chk   (checked-sentence sentence)
        types (kb/membership-reader kb context)
        decls (declaration-reader kb (nm/functor chk) context)
        p     (constraint-problem kb chk context types decls)]
    (if (refuses-assert? kb p)
      (throw (ex-info (:message p) (dissoc p :message)))
      (constraint-entailments kb chk context types decls))))

(defn constraint-admission
  "The derivation path's `constraint-checks`: one pass over the definitional checks,
  answering both halves as values — `{:violation v}` when `sentence` is inadmissible
  in `context`, else `{:entailments [...]}`.

  Forward chaining must not throw — a rule firing mid-fixpoint that aborted the run
  would leave belief half-computed, and the project's stance is that contradictions
  are soft.  So the derivation path asks the question instead of being stopped by
  the answer.  No try/catch: the checks bottom out as values, so there is no thrown
  answer to fish back out (and no whitelist of `:type`s for a new check to miss).

  An **arbitrable** violation is not a violation here at all.  A firing has no caller
  to refuse, so the two answers available are dropping the conclusion — no sentex, no
  justification, and `why-not` reduced to `:not-stored` — or placing it and letting
  `settle` weigh the pair like any other contradiction.  Placing it is what gives the
  loser a reason, so this reports only what genuinely cannot be represented: a
  malformed sentence, or an argument constraint, whose conviction rests on the
  *absence* of a fact rather than on a second one to weigh against."
  [kb sentence context]
  (let [chk   (checked-sentence sentence)
        types (kb/membership-reader kb context)
        decls (declaration-reader kb (nm/functor chk) context)
        p     (constraint-problem kb chk context types decls)]
    (if (and p (not (arbitrable? p)))
      {:violation {:violation (:type p) :detail (dissoc p :type :sentence)}}
      {:entailments (constraint-entailments kb chk context types decls)})))

(defn constraint-violation
  "The definitional checks as a value alone: nil when `sentence` is admissible in
  `context`, else `{:violation :arity|:arg-type|:arg-genl|:arg-position
  |:arg-constraint-kind|:disjoint|:asymmetric|:functional|:irreflexive|:anti-symmetric
  :detail {...}}`.

  **Every** violation, arbitrable ones included — which is what separates this from
  `constraint-admission`.  The callers are the paths that *mint* content nobody asked
  for and that has somewhere else to be: the decontextualization lift's copy, the
  equality migration's twin, and the gate on what `abduce` may assume.  None of those
  is a rule firing with a conclusion to stand behind — a lift can decline to copy, a
  merge can decline to restate, an abducer can decline to hypothesize — so where a
  firing arbitrates, they refuse, and the refusal is reported rather than thrown."
  [kb sentence context]
  (let [chk   (checked-sentence sentence)
        types (kb/membership-reader kb context)
        decls (declaration-reader kb (nm/functor chk) context)]
    (when-let [p (constraint-problem kb chk context types decls)]
      {:violation (:type p) :detail (dissoc p :type :sentence)})))

(defn arity-violation
  "The arity violation `sentence` commits in `context`, or nil — that one arm, asked of
  content **already stored**.

  The retroactive report's probe (`settle/report-arity-reach!`).  A declaration arriving
  after the facts it convicts was never seen by the check that runs on the way in, so
  the facts are re-asked here — the same `arity-problem` the door reads, so the two
  cannot drift about what a wrong arity is.

  Nothing else in the arm's family is asked: the sentence is stored, so whatever the
  other checks would say about it was said when it was written, and only the *arity*
  declaration is what just arrived.

  **No `:opposing-class`**, unlike every problem `constraint-problem` hands back.  A class
  is what a caller weighs two sides with, and this caller weighs nothing — stamping one
  would advertise an arbitration that deliberately does not happen.

  The four-argument form takes the membership reader rather than building one.  A reader
  memoizes per context for the life of one caller, and the sweep asks this of every fact
  of a whole spec subtree — so building one per fact throws the memo away once per
  question and pays the retrieval every time.  The caller holds one reader per context it
  meets instead."
  ([kb sentence context]
   (arity-violation kb sentence context (kb/membership-reader kb context)))
  ([kb sentence context types]
   (arity-problem kb (checked-sentence sentence) context types)))

(defn arg-position-violation
  "The `:arg-position` violation the **stored declaration** `sentence` commits in
  `context`, or nil — a constraint on a position its predicate does not have.

  `arity-violation`'s twin, one level up: that one asks whether a stored *fact* is the
  wrong length, this one whether a stored *declaration* names a position the length
  leaves it without.  Both re-ask a door check of content already admitted, and both go
  through the arm the door itself reads so the two cannot drift.

  The reader is `vaelii.impl.quality`, not `settle`.  A declaration stranded by an arity
  that arrived later is **inert** — it constrains nothing, refuses nothing and mints
  nothing — so unlike a wrong-length fact there is no admitted content to name and no
  *newly* to report: it reads the same an hour later, which makes it a census question
  rather than a settle one.  `docs/taxonomy.md` records that split.

  Only the position arm.  `declaration-problem` also convicts a declaration disagreeing
  with its predicate's `relationKind`, and an arity arriving is not what makes that true,
  so asking it here would report a second finding under the first one's trigger.

  Both of `interArg`'s positions are asked, as at the door, and the first that
  convicts is the answer.

  Through `checked-sentence`, like the twin and like the door: a doubly negated
  declaration is a declaration and is read as one, and a genuinely negative sentence keeps
  its `not`, which matches neither arm below.  A caller reading the record store hands in
  a sentence the constructor already stripped to its positive body, so the pass costs it
  nothing — the reason to spell it is that the arm is stated once and both entrances to it
  must be the same entrance."
  ([kb sentence context]
   (arg-position-violation kb sentence context (kb/membership-reader kb context)))
  ([kb sentence context types]
   (let [chk            (checked-sentence sentence)
         [f pred n _ m] chk]
     (when (symbol? pred)
       (cond
         (and (= 'interArg f) (= 5 (nm/arity chk)))
         (some-> (or (arg-position-problem kb f pred n context types)
                     (arg-position-problem kb f pred m context types))
                 (assoc :sentence chk))

         (and (contains? arg-constraint-kinds f) (= 3 (nm/arity chk)))
         (some-> (arg-position-problem kb f pred n context types)
                 (assoc :sentence chk)))))))

(defn arbitrable-violations
  "**Every** definitional clash `sentence` forms against believed content visible from
  `context` — the nogood half of the checks, read by `settle`'s discovery.  Empty when
  the sentence is admissible outright.

  Asked of a sentence that is itself **stored and believed**, which is what the
  discovery walks: the clashes it reports are with the *other* members of each pair,
  since a sentence never opposes itself (a term's own type is not disjoint from itself,
  its own value is not a second value, and its own converse is a different tuple).

  Plural, and that is the point.  `constraint-problem` stops at the first violation
  because a refusal needs only one reason.  A pair is not a reason — it is a fact about
  two sentexes — and a term holding three mutually disjoint types forms three of them,
  so stopping at the first would report a set of pairs that depended on the order the
  argument root handed the memberships back.  That order is handle order, which is
  arrival order, which is the one thing belief may not depend on.

  Only the four arbitrable arms run.  The argument constraints cannot name a second
  sentex, and on this path the sentence is already stored — so whatever they would say
  about it was said when it was written.

  `:anti-transitive` names **two** other sentexes rather than one, and is read here the
  same way: `opposing-handles` is what the discovery forms its nogood from, so a triple
  arrives as one entry with three members and a pair as one with two.

  **`context` is the asker and `home` is where the sentence lives**, and the two arms that
  tell a partner from the sentence *itself* read `home` (`asymmetry-problems` records
  what keying that on the asker cost).  The three-argument form is the door's, where a
  sentence is asked about from the context it is being written into and the two are one;
  a caller asking a **stored** sentex's question from a vantage owes the four-argument
  form and its own `(:context s)`."
  ([kb sentence context] (arbitrable-violations kb sentence context context))
  ([kb sentence context home]
   (let [chk   (checked-sentence sentence)
         types (kb/membership-reader kb context)]
     (->> (concat (disjoint-problems kb chk context types)
                  (functional-problems kb chk context)
                  (asymmetry-problems kb chk context home)
                  (antitransitivity-problems kb chk context home))
          (map #(with-opposing-class kb %))
          (filter arbitrable?)))))

(defn check-ground
  "Reject a non-rule sentence that still contains pattern variables.

  A fact asserts something; `(mortal ?x)` asserts nothing — it is an open sentence.
  Stored as a premise it is worse than useless: `unify` matches it against any goal,
  so it silently behaves as a universally quantified fact that nothing ever licensed.
  Universal claims are written as rules, where `check-range-restricted` governs the
  variables.

  Rule-ness is read off the **canonicalized record**, not off the raw input: an
  `implies`, a `set/*Rule` wrapper, and a nested combination of the two all
  canonicalize into `:antecedent`, and pattern-matching the input would have to
  re-derive that (and would miss a spelling).

  A **schematic equation** `(equals (fatherOf (fatherOf ?x)) (grandfatherOf ?x))` is
  the deliberate exception: its variables belong to a term-rewriting schema, not to an
  open fact, so it is stored as an oriented rewrite rule rather than refused
  (docs/equality.md, symbolic equational reasoning).  It is not matched as a fact
  under `unify` — its functor is `equals`, read by the equality machinery, not by the
  fact prover for arbitrary goals."
  [kb sentence context]
  (let [s (res/kb-sentex kb sentence context)]
    (when (and (nil? (:antecedent s)) (not (sx/ground? s))
               (not (rewrite/schematic-equation? sentence))
               ;; a `defn*` collection definition carries the member variable `?x` in
               ;; its condition argument, the way a schematic equation carries its schema
               ;; variables — it is stored to retract and belief-follow, and it expands
               ;; into the rules where those variables belong (docs/defns.md)
               (not (sx/defn-sentence? sentence)))
      (throw (ex-info (str "not ground: " (pr-str sentence)
                           " contains a variable — a fact must be ground"
                           " (write a universal claim as a rule)")
                      {:type :not-ground :sentence sentence :context context})))))

;; ---- storable values ----------------------------------------------------
;; A sentence's leaves must survive the durable log.  Symbols and keywords (the
;; vocabulary), strings/numbers/chars (the literals), and booleans/nil — everything a
;; sentence is built from — always do, and are cleared without a freeze so the assert
;; hot path pays one type-check per leaf and no serialization.  Anything else (a
;; function, an atom/ref, an open stream, a Serializable object off nippy's thaw
;; allowlist) is put through the freeze/thaw pair the on-disk backends run, and refused
;; if either throws — so a value stores in every backend or none, rather than in memory
;; and then throwing at write time on the first disk backend.

(defn- storable-scalar?
  "A leaf nippy always round-trips, recognised without a freeze.  Ordered by how often
  a sentence's leaves are each — the vocabulary (symbols, keywords) and literals
  (strings, numbers) first, the rarer nil/boolean/char last."
  [v]
  (or (symbol? v) (keyword? v) (string? v) (number? v)
      (nil? v) (boolean? v) (char? v)))

(def ^:private ^java.util.concurrent.ConcurrentHashMap storable-class-cache
  "Storability memoized by class.  Every value that reaches the freeze probe is a leaf
  that is neither a scalar nor a collection, and for those it is a property of the
  *class* — a `Date` always freezes and thaws, a function never does, and nippy's own
  thaw allowlist is class-keyed — so the probe runs once per class, not once per value.
  A bulk load of dated or id-stamped facts then pays one freeze/thaw for the type, not
  one per fact.  Bounded by the distinct non-scalar leaf classes a process ever asserts,
  which is a handful."
  (java.util.concurrent.ConcurrentHashMap.))

(defn- nippy-storable?
  "Does a value of `v`'s class survive a nippy freeze *and* thaw without throwing — the
  pair the durable log runs on write and read?  Not a `=` round-trip (a byte array and
  other identity-compared values store fine yet would fail it) and not freeze alone (a
  Serializable value off the thaw allowlist freezes and then throws on read); both must
  succeed.  Memoized by class (see `storable-class-cache`): the first value of a class
  runs the probe, the rest read the boolean it cached."
  [v]
  (let [c      (class v)
        cached (.get storable-class-cache c)]
    (cond
      (identical? Boolean/TRUE cached)  true
      (identical? Boolean/FALSE cached) false
      :else (let [ok (try (nippy/thaw (nippy/freeze v)) true
                          (catch Throwable _ false))]
              (.put storable-class-cache c (if ok Boolean/TRUE Boolean/FALSE))
              ok))))

(defn- first-unstorable
  "The first leaf value anywhere in `x` the durable log cannot store, or nil.
  Collections are descended (a map by its keys then its vals); a scalar is cleared
  without a freeze."
  [x]
  (cond
    (storable-scalar? x) nil
    (map? x)             (or (some first-unstorable (keys x))
                             (some first-unstorable (vals x)))
    (coll? x)            (some first-unstorable x)
    :else                (when-not (nippy-storable? x) x)))

(defn check-encodable
  "Reject a sentence carrying a value no durable backend can store.  A function, an
  atom/ref, an open stream — anything nippy cannot freeze and thaw — stores in the
  in-memory backend and then throws at write time on the first on-disk backend, so the
  same assert would succeed or fail by backend.  Refusing it here makes the backends
  agree: a stored sentence's values round-trip."
  [sentence]
  (when-let [v (first-unstorable sentence)]
    (throw (ex-info (str "value cannot be stored: " (pr-str v) " of type "
                         (.getName (class v)) " does not round-trip through the durable"
                         " log (nippy) — a sentence's values must be serializable")
                    {:type :not-encodable :sentence sentence :value v}))))

;; ---- stratification -----------------------------------------------------
;; The rule-set half of well-formedness: a rule whose `exceptWhen` exception closes
;; a cycle through negation is refused, the way a `genl` cycle is.  The graph itself
;; and the search live in `vaelii.impl.wff`; what lives here is reaching the stored
;; rules, which is the rule index's job — `rules-by-consequent` answers "what could
;; conclude P?" whatever a rule's direction, so no scan is needed.
;;
;; **Two things can close a cycle**, because both kinds of edge fan out over the genl
;; **spec** closure: a *rule* arriving, and a *taxonomy edge* arriving underneath
;; rules that are already stored.  An exception on `flightless` is reached by a
;; stored `(penguin Opus)` the moment `(genl penguin flightless)` holds, whichever of
;; the two arrived last.  So the walk runs on both paths:
;;
;;   `check-stratified`        a rule is being asserted   -> throw
;;   `check-edge-stratified`   an edge is being asserted  -> throw
;;   `edge-stratification-violation`   an edge is being *derived* -> report
;;
;; Only *additions* can close a cycle: `specs` grows monotonically with the edge set,
;; so removing an edge only removes graph edges and a retraction needs no check.

(defn- negative-predicates
  "The predicates a rule depends on **negatively**.

  Three things put a predicate here.  An `exceptWhen` exception and an `(unknown S)`
  antecedent, both negation as failure over what the KB derives — the exception at
  rule granularity, the `unknown` per-literal — so asserting a fact can *withdraw* a
  conclusion, and a cycle through either is order-dependent (docs/exceptions.md,
  docs/naf.md).  Both arrive here already collected as `neg-query-preds`.  And a
  `different` antecedent, which is negation as failure over the **equality closure**:
  it holds exactly while nothing has merged its arguments, so asserting an equality
  *withdraws* it, and a rule that concludes an equality from a `different` antecedent
  is a cycle through negation whose settled state would depend on arrival order
  (docs/equality.md, \"Interactions — Stratification\").

  The negative edge from a `different` antecedent runs to the three relations that
  assert a merge, not to `different` itself — nothing ever concludes `different`, so
  an edge keyed on it would reach no rule and find no cycle."
  [antecedent-preds neg-query-preds]
  (concat neg-query-preds
          (when (some #(= 'different %) antecedent-preds) kb/equality-predicates)))

(defn- exception-predicates
  "The predicates the exceptWhen exceptions of stored rule `handle` mention — the
  negative-edge keys the stratification graph reads, gathered from the rule's
  belief-following exceptWhen meta-sentexes (`provers/rule-exceptions`).

  Read through the query frames (`rules/watched-predicates`), because a cycle runs
  through what the exception *reads*: an exception that is itself an `(unknown S)` is a
  negative dependency on `S`'s predicate, and keyed on `unknown` — which nothing
  concludes — the graph would find no cycle to refuse."
  [kb handle]
  (mapcat rules/watched-predicates (provers/rule-exceptions kb handle)))

(defn- rule-graph-node
  "The stratification graph's view of a stored rule: what it depends on, positively
  (its antecedent predicates) and negatively (the predicates its exceptWhen exceptions
  and its `unknown` antecedents mention, plus the equality relations when it reads
  `different`).  The exceptWhen predicates come from the rule's meta-sentexes, so kb is
  needed.

  The antecedents are read as **dependency** predicates, not as index keys: an edge is
  followed by looking the predicate up among the concluders, and a conclusion is filed
  by `consequent-predicate` — which spells a negation `not` where the index key spells
  it `[:not pred]` (`rules/dependency-predicates`)."
  [kb handle rule-sentex]
  (let [antes (rules/dependency-predicates (:sentence rule-sentex))]
    {:id               handle
     :label            (str "rule#" handle)
     :antecedent-preds antes
     :exception-preds  (negative-predicates
                        antes (concat (exception-predicates kb handle)
                                      (rules/recheck-predicates rule-sentex)))}))

(defn- stored-rule-node
  "The graph node for a stored rule handle — nil if the handle names something that
  is not a rule, which the rule index should never hand back but which a stale
  posting could."
  [kb handle]
  (when-let [rsx (p/get-sentex (:records kb) handle)]
    (when (rules/rule? rsx) (rule-graph-node kb handle rsx))))

(defn- stratification-concluders
  "Predicate -> the rule nodes concluding it, read off the rule index.

  The one-arity is the graph exactly as **stored**, which is what an edge change is
  checked against.  The two-arity adds `pending`, the rule (or exception) being added,
  under its own consequent by hand: it is not reflected in the graph yet, and without
  it a rule whose exception mentions what it concludes — a one-rule cycle — would look
  stratified.  A pending rule whose consequent functor is a **variable** could conclude
  *any* predicate, so it is added under every `pred` the walk asks about — the same
  reason `direct-concluders` folds the catch-all into the stored side."
  ([kb]
   (fn [pred]
     ;; `direct-concluders` folds in the variable-consequent catch-all: a rule concluding
     ;; `(?p …)` could conclude `pred`, so a negation cycle through it must not be missed.
     (keep #(stored-rule-node kb %) (rules/direct-concluders (:index kb) pred))))
  ([kb pending]
   (let [stored      (stratification-concluders kb)
         var-conseq? (sx/variable? (:consequent-pred pending))]
     (fn [pred]
       (cond-> (remove #(= (:id %) (:id pending)) (stored pred))
         (or var-conseq? (= pred (:consequent-pred pending))) (conj pending))))))

(defn check-stratified
  "Throw unless adding this rule leaves the rule set stratified — see
  docs/exceptions.md.  Runs before anything is stored, so a refused rule leaves no
  partial state behind.

  Fast path: with no exception on the rule being added and none on any stored rule,
  the graph has no negative edge at all and no cycle through negation is possible,
  so the walk is skipped entirely.  That is every rule in an ontology that uses no
  exceptions, which is most of them."
  [kb sentence inner context]
  (let [[_ _ exception] (sx/peel-rule-wrapper sentence)
        ;; dependency spelling, not the index key: `rule-graph-node` says why
        antes             (rules/dependency-predicates inner)
        ;; negatives: the exception's predicates, the `unknown` antecedents' *and* the
        ;; **aggregate** bodies'.  All three read what the KB believes rather than a
        ;; fact the firing names, so a cycle through any of them is unstratified — a
        ;; rule whose count is over a relation the rule itself concludes has no settled
        ;; answer, and which one it lands on would depend on arrival order.
        negatives         (negative-predicates antes (concat (keep nm/functor exception)
                                                             (rules/naf-predicates-of inner)
                                                             (rules/aggregate-predicates-of inner)))]
    ;; The fast path skips the walk when the graph has no negative edge at all — now
    ;; a `different` antecedent counts as one, so a rule that reads the equality
    ;; closure is walked even though it carries no `exceptWhen`.
    (when (or (seq negatives) (seq (p/exception-rules (:index kb))))
      (let [pending {:id               ::pending
                     :label            "the rule being asserted"
                     :antecedent-preds antes
                     :exception-preds  negatives
                     :consequent-pred  (rules/consequent-predicate inner)}]
        (when-let [cycle (wff/negation-cycle (:taxonomy kb)
                                             (stratification-concluders kb pending)
                                             pending)]
          (throw (ex-info (str "not stratified: the rule set would have a cycle through "
                               "negation: " (wff/cycle-description cycle))
                          {:type :not-stratified :sentence inner :context context
                           :cycle cycle})))))))

(defn check-no-imperative
  "Refuse a `do/` imperative anywhere inside a rule — antecedent, consequent, or
  `exceptWhen` query.

  A rule is evaluated inside the forward-chaining fixpoint, and an imperative there
  would run a number of times that depends on firing order while mutating the KB the
  fixpoint is still computing over.  Order independence and locality are the two
  invariants the TMS is built on (docs/nmtms.md); a side effect inside the fixpoint
  breaks both at once.  So a `do/` form is legal only at the top level of an `assert`,
  where the caller decided when it happens (docs/labeling.md).

  Walks the whole form rather than the three slots, so a nesting cannot smuggle one
  past — the check is about a fixpoint reaching it, not about where it was written."
  [sentence]
  (when-let [bad (sx/some-form sx/do-form? sentence)]
    (throw (ex-info (str "a do/ imperative cannot appear in a rule: " (pr-str bad))
                    {:type :not-assertible :form bad :sentence sentence}))))

;; ---- the argument constraints a rule's variables carry -------------------
;;
;; `args-problem` holds a **ground** argument to what its position declares.  Every
;; argument of a rule is a variable, so that arm passes over all of them vacuously and
;; the rule is stored — and then each fact the rule concludes is convicted one at a
;; time, by a complaint naming the conclusion and never the rule that wrote it.
;;
;; A variable is one term standing in several positions at once, though, so the
;; positions can be held to **each other** before anything fires.  A variable an
;; antecedent binds through `(arg comment 2 character_string)` and a consequent places
;; into `(genl ?x ?string)` has to be a run of text and a type at the same time, and
;; text and a type are declared disjoint: no term is both, so every firing of that rule
;; would conclude something the door refuses.  The rule is the mistake, and this is
;; where it is said.
;;
;; **A type-level position asks for a type, which is a `unaryPredicate`.**  That is the
;; second reading this arm needs and the KB already holds it twice over: every type is
;; asserted a `unaryPredicate` when the schema loads, and `declaration-problem` refuses
;; an `arg` declaration on a `typeRelationPredicate` precisely because *its* arguments
;; name kinds.  So a position is type-level when a `genlArg` names it **or** when its
;; predicate is a `typeRelationPredicate` — which is how `genl`'s second argument is
;; constrained at all.  That position carries no declaration of its own, deliberately
;; (see CxCore), and the relation kind is what says what it holds.
;;
;; **Instance constraint against instance constraint, and nothing else.**  `(disjoint T
;; U)` says the two types share no instance, which is exactly what two such constraints
;; on one variable ask of it — the reading `args-problem` gives a ground term, asked of
;; a term that is not there yet.  Two *subtype* constraints are left alone: a type below
;; two disjoint types is empty rather than impossible, and nothing else in the KB
;; refuses an empty type.
;;
;; **Positive literals only.**  A negated antecedent says the variable does not fill
;; that position, so a constraint carried there is one no binding ever has to satisfy;
;; reading it would refuse `(implies (and (dog ?x) (not (plant ?x))) …)` for saying
;; exactly what its author meant.  An existential is skipped for the reason its
;; variables are local: what it binds inside is not the variable the rest shares.

(def ^:private collection-type
  "The type a **type-level** argument position asks its filler to be an instance of.
  Every type in the KB is asserted a `unaryPredicate` as the schema loads, so this is
  what `genlArg`'s \"a subtype of T\" and `typeRelationPredicate`'s \"relates kinds\"
  both amount to as a membership — and a membership is what `disjoint` separates."
  'unaryPredicate)

(defn- binding-literals
  "The literals of rule `inner` that **bind** its variables: every positive antecedent,
  plus the consequent — with an `(ist Ctx S)` consequent replaced by the `S` it places,
  since that is the sentence the conclusion is stored as and so the one whose argument
  positions the conclusion has to satisfy."
  [inner]
  (let [c (rules/consequent inner)
        c (if (and (sequential? c) (= sx/ist-functor (first c)) (= 3 (count c)))
            (nth c 2)
            c)]
    (conj (into []
                (remove #(or (sx/negation? %) (sx/unknown? %) (sx/there-exists? %)))
                (rules/antecedents inner))
          c)))

(defn- literal-variable-constraints
  "The memberships one literal demands of the variables sitting in its arguments, as
  `[[variable {:type T :position n :pred P :via V :level :arg|:genlArg|:kind}] …]`.

  Two sources, and they are the two readings a position can carry.  An `(arg P n T)`
  declaration types the filler directly.  A **type-level** position — one a `genlArg`
  names, or any position of a `typeRelationPredicate` — types it as a
  `unaryPredicate`, since what stands there is a kind.  `:level` is kept so the refusal
  can say which reading it read, and `:via` so a constraint that descended from a
  super-predicate names the predicate it was written of, exactly as `args-problem` does.

  Walked in `in-content-order`, so which declaration a refusal names is decided by what
  the KB says rather than by how the retrieval happened to enumerate."
  [kb lit context]
  (let [pred (nm/functor lit)
        as   (vec (nm/args lit))]
    (when (and (sequential? lit) (symbol? pred) (some sx/variable? as))
      (let [decls    (declaration-reader kb pred context)
            type-rel (seq (res/matches-visible kb (list 'typeRelationPredicate pred) context))
            of-kind  (fn [kind mk]
                       (for [m     (in-content-order (decls kind))
                             :let  [b (nth m 1)
                                    n (get b '?n)
                                    a (arg-at as n)]
                             :when (and (sx/variable? a) (symbol? (get b '?type)))]
                         [a (mk m b n)]))]
        (concat
         (of-kind 'arg
                  (fn [m b n] {:type (get b '?type) :position n :pred pred
                               :via (declared-of m) :level :arg}))
         (of-kind 'genlArg
                  (fn [m _ n] {:type collection-type :position n :pred pred
                               :via (declared-of m) :level :genlArg}))
         (when type-rel
           (for [[i a] (map-indexed vector as)
                 :when (sx/variable? a)]
             [a {:type collection-type :position (inc i) :pred pred
                 :via pred :level :kind}])))))))

(defn- variable-constraints
  "`variable -> [{…} …]` over `literals`, in literal order — the whole of what a rule's
  own text says its variables have to be."
  [kb literals context]
  (reduce (fn [acc lit]
            (reduce (fn [acc [v c]] (update acc v (fnil conj []) c))
                    acc
                    (literal-variable-constraints kb lit context)))
          {} literals))

(defn- variable-constraint-clause
  "How a refusal names one constraint it found — **a character_string (arg 2 of
  comment)**, or **a type (arg 2 of genl, a typeRelationPredicate)** for a position
  whose demand comes from the relation kind rather than from a declaration.  Carries
  `via-clause` for a constraint that descended from a super-predicate, exactly as
  `args-problem`'s message does."
  [{:keys [type position pred via level]}]
  (str (case level
         :arg     (str "a " type)
         :genlArg "a type"
         :kind    "a type")
       " (arg " position " of " pred
       (case level
         :genlArg (str ", constrained with genlArg" (via-clause via pred))
         :kind    ", a typeRelationPredicate"
         (via-clause via pred))
       ")"))

(defn- variable-clash-problem
  "The first pair of constraints on one of rule `inner`'s variables that no term
  satisfies at once, or nil.

  Only two **instance** demands can convict: `disjoint` says two types share no
  instance, and a membership is what each of these constraints asks for — the
  `unaryPredicate` a type-level position asks for included.  Variables are taken in
  name order and each one's constraints in literal-then-content order, so a rule
  several of whose variables clash is refused for the same one every time."
  [kb inner context]
  (let [taxo   (:taxonomy kb)
        by-var (variable-constraints kb (binding-literals inner) context)]
    (first
     ;; `str` rather than `pr-str`: a rule variable is a symbol, so the key is a scalar
     ;; that no ambient `*print-length*` can collapse to a shared prefix
     (for [v     (sort-by str (keys by-var))
           :let  [cs (get by-var v)]
           :when (< 1 (count cs))
           [i a] (map-indexed vector cs)
           b     (drop (inc i) cs)
           :when (and (not= (:type a) (:type b))
                      (tax/disjoint? taxo (:type a) (:type b) context))]
       {:type :arg-variable :sentence inner :variable v
        :expected [(:type a) (:type b)]
        :message (str "arg constraint: " v " must be " (variable-constraint-clause a)
                      " and " (variable-constraint-clause b)
                      ", and the two types are disjoint")}))))

(defn- check-variable-constraints!
  "Throw when a variable of rule `inner` carries two argument constraints no term can
  satisfy together.  The value form is `variable-clash-problem`; this is the door's.

  Private, unlike the cross-namespace rule checks beside it in `check-rule!`: every
  door that stores a rule reaches this through that list, so there is no second caller
  for a public name to serve."
  [kb inner context]
  (when-let [p (variable-clash-problem kb inner context)]
    (throw (ex-info (:message p) (dissoc p :message)))))

;; ---- generators: the refusals a rule concluding a rule owes ---------------
;; A generator is a rule and passes everything a rule passes.  What follows is what it
;; owes *as* a generator, and every one of them is asked of each nesting level, since a
;; stamped rule may stamp one in turn and each level reaches the store as a rule in its
;; own right (docs/generators.md).

(defn- stored-generators
  "Every stored generator, as `[handle sentex]` pairs.

  One index lookup, and the cell it reads is the one that looks like a junk posting:
  `rules/consequent-predicate` reads the functor of what a rule concludes, and what a
  generator concludes is a rule — so every generator in the KB is filed under `implies`
  and nothing else is, at any nesting depth.  Nothing backward-chains through it (a
  generator is forward-only, and no goal's functor is `implies`), which leaves it doing
  exactly this one job."
  [kb]
  (into []
        (comp (keep (fn [h] (when-let [s (p/get-sentex (:records kb) h)] [h s])))
              (filter (fn [[_ s]] (rules/generator-sentex? s))))
        (p/rules-by-consequent (:index kb) sx/rule-functor)))

(defn- stamped-predicate
  "The predicate a generator eventually concludes — the **innermost** rule's, through
  however many levels of stamping stand between.  The levels in between conclude rules,
  and `implies` is a key nothing reads as a fact; what reaches the fact store is the
  innermost conclusion, so that is the predicate a cycle can run through."
  [sentence]
  (rules/consequent-predicate (rules/innermost-rule sentence)))

(defn- generator-reads
  "The predicates whose arrival makes this generator **stamp** — the antecedents of
  every level but the innermost.  The innermost rule's antecedents are excluded on
  purpose: they trigger the rule that was stamped, which concludes a fact, and a fact is
  not what makes the rule set grow."
  [sentence]
  (into #{} (mapcat #(keep nm/functor (:antecedents %)))
        (butlast (rules/nesting sentence))))

(defn generator-cycle
  "A description of the cycle adding this generator would put in the rule set, or nil.

  The graph is generators only, and one hop: an edge runs from a generator to any
  generator that reads — in an antecedent it stamps from — the predicate its stamped
  rule concludes.  A cycle there is a rule set that mints rules that mint rules, and
  unlike ordinary recursion nothing bounds it: each round adds *rules* rather than
  facts, and the next round's rules are the ones the last round wrote.

  Refused outright rather than depth-capped.  A cap would make the KB's contents a
  function of how long the chainer happened to run, and \"how many rules does this KB
  have\" would stop having an answer — the same call stratification makes for a cycle
  through negation (docs/exceptions.md).  It is also why *nesting* is not a cap worth
  having: a nested generator stamps one level further before it stops, and what makes a
  rule set unbounded is the cycle, not the depth.

  **Both directions, because either can be the new edge**: the arriving generator may
  stamp what a stored one reads, or read what a stored one stamps, and a self-loop is
  the case where it does both to itself.  Checking only one direction would let the
  cycle in whenever the two generators were asserted in the other order — which is the
  order dependence every check here exists to keep out."
  [kb inner context]
  (when (rules/generated-rule (rules/consequent inner))
    (let [stamps (stamped-predicate inner)
          reads  (generator-reads inner)
          gens   (stored-generators kb)
          where  (or (when (and stamps (reads stamps)) "itself")
                     (some (fn [[h s]]
                             (when (and stamps (contains? (generator-reads (:sentence s))
                                                          stamps))
                               (str "the generator at handle " h)))
                           gens)
                     (some (fn [[h s]]
                             (when-let [p (stamped-predicate (:sentence s))]
                               (when (reads p)
                                 (str "the generator at handle " h ", which stamps "
                                      p))))
                           gens))]
      (when where
        (str "the rule it generates concludes " stamps
             ", and that predicate is read by " where
             (when context (str " (asserting into " context ")")))))))

(defn check-generator!
  "The three refusals that are a **generator**'s alone — a rule whose consequent is a
  rule (docs/generators.md).  Everything else it must satisfy it satisfies as a rule,
  through the list below.

  **Forward-only.** A generator's conclusion is a rule, and there is no backward goal
  whose answer is one — `concluding-rule-handles` reads a goal's predicate, and a
  generator's consequent predicate is `implies`, which names nothing a query asks for.
  A `set/backwardRule` generator would therefore be stored claiming a capability it
  cannot exercise, which is the accepted-and-inert state the indexability refusal
  exists to keep out of the KB.  `:inert` stays legal: it claims nothing.  Asked of
  **every** generator level, since a `set/backwardRule` around a middle level would be
  minted as a backward generator and refused one firing later, in the ledger rather
  than at the sentence.

  **No `exceptWhen` on a stamped rule.** An exception is not a rule field — it is a
  separate meta-sentex keyed by the rule's handle, split off and stored by the assert
  path (`assert-exceptWhen-meta!`), which a firing does not run.  So a stamped
  `exceptWhen` would reach the store as nothing at all: the mint would be a rule whose
  guard had silently evaporated, firing on exactly the bindings its author wrote it not
  to.  A guard that is dropped in silence is worse than one refused, so it is refused.
  An `exceptWhen` on the **outermost** rule is a different and legal thing — it says
  when not to stamp — and the message points there.

  **No generator cycle.** A stamped rule whose conclusion feeds some generator's
  antecedent is a rule set that mints rules that mint rules, with no fixpoint anybody
  has bounded.  Refused outright rather than capped, the same call stratification makes
  for a cycle through negation: the alternative is a KB whose size depends on how long
  the chainer was allowed to run.

  Read by both storage doors through `check-rule!`, so a generator a *firing* stamps
  owes exactly what one an author wrote owes — which is the whole of what makes nesting
  safe: the middle level is checked twice, once as a pattern and once as the rule it
  became."
  [kb sentence context]
  (let [inner  (rules/inner-rule sentence)
        levels (rules/nesting sentence)
        ;; `peel-rule-wrapper` reports the wrapper it found, and a bare rule has none —
        ;; the record's default is what nil means here, as it does at the constructor.
        ;; A level's own wrapper rides the consequent of the level above it, which is
        ;; where a stamped rule's direction is written.
        dirs   (cons (or (first (sx/peel-rule-wrapper sentence)) :both)
                     (map #(or (first (sx/peel-rule-wrapper (:consequent %))) :both)
                          levels))]
    (doseq [[i level dir] (map vector (range) levels dirs)
            :when         (:generated level)]
      (when (seq (nth (sx/peel-rule-wrapper (:consequent level)) 2))
        (throw (ex-info (str "the rule a generator generates cannot carry an exceptWhen:"
                             " an exception is stored as a meta-sentex against the rule's"
                             " handle, and a firing has no way to split one off, so it"
                             " would be dropped in silence.  Put the condition in the"
                             " generated rule's antecedents as an (unknown …), or put the"
                             " exceptWhen on the outermost rule to say when not to"
                             " generate")
                        {:type :not-well-formed :sentence sentence :context context
                         :nesting-level (inc i)})))
      (when-not (contains? #{:forward :both :inert} dir)
        (throw (ex-info (str "a rule generator is forward-only: its conclusion is a rule,"
                             " and no backward goal asks for one.  Drop the"
                             " set/backwardRule wrapper — the wrapper on the innermost"
                             " rule is what sets that rule's direction")
                        {:type :not-indexable :direction dir :sentence sentence
                         :nesting-level (inc i)}))))
    (when-let [cyc (generator-cycle kb inner context)]
      (throw (ex-info (str "a rule generator cannot generate a rule that feeds a"
                           " generator: " cyc)
                      {:type :not-stratified :sentence sentence :context context
                       :cycle cyc})))))

(defn check-rule!
  "Every pre-storage check a rule must pass, as a step that writes nothing.

  **Two doors store a rule** and this is the list both read.  `core/assert` stores one
  an author wrote; a generator firing stores one the KB derived
  (docs/generators.md).  What a rule has to *be* does not depend on which door it came
  through, so a copy per door is the drift this exists to prevent — a check added at
  the assert door that the mint never learned would let the fixpoint store what the
  API refuses.

  Factored out of the assert path so `assert` can also run it over **all** the
  conjuncts of a polycanonicalized rule before storing *any* of them.
  `(implies A (and C1 C2))` is split into one rule per conjunct and then `mapv`d,
  and a `mapv` is not a transaction: with the checks inline, a refusal on C2 left
  C1 already stored, indexed, and chained from, while the caller saw a throw and
  reasonably concluded nothing had been asserted.

  One arm here has no counterpart on the fact path at all —
  `check-variable-constraints!`, which holds a rule's shared variables to the argument
  constraints of every position they stand in.  A ground argument is checked by
  `constraint-checks` on the way in; a variable is checked here or nowhere, since the
  term it will hold does not exist yet.

  A **generator** owes three more (`check-generator!`), and they run last so the
  sharper complaint comes first: a rule that is unbound *and* backward-only is refused
  for the unbound variable, which is the one its author can act on."
  [kb sentence context]
  (let [inner       (rules/inner-rule sentence)
        [direction] (sx/peel-rule-wrapper sentence)]
    ;; on the sentence **as written**, not on `inner`: `inner-rule` peels the
    ;; `exceptWhen` wrapper and takes the exception query with it, so guarding the
    ;; inner rule let an imperative through in the one rule slot that is re-evaluated
    ;; most often
    (check-no-imperative sentence)
    (rules/check-range-restricted (rules/antecedents inner) (rules/consequent inner))
    ;; The NAF-literal checks — closure, quantifier locality, the reduction slot, a
    ;; quantified or empty conjunction.  The sentex constructor runs these too, and runs
    ;; them last, which is what covered both *storage* doors and left the **dry-run** door
    ;; blind: `core/check` predicts an assert without constructing a sentex, so a rule
    ;; whose `unknown` was open, whose binder escaped, or whose conjunction no evaluator
    ;; can answer checked clean and then threw.  Here it is answered before anything is
    ;; built, which is where a prediction can see it.
    (sx/check-naf-closed (rules/antecedents inner) (rules/consequent inner) nil)
    ;; A rule the index cannot key on, refused before it is stored — except when it is
    ;; `:inert`, which runs in neither engine and so promises nothing the index has to
    ;; answer for.  `CxCore`'s `(implies (?pred . ?args) (ist CxUniverse (?pred
    ;; . ?args)))` is that case: the decontextualized-predicate lift is implemented in
    ;; code, and the rule states it for a reader.
    (when-not (= :inert direction)
      (rules/check-indexable-functors inner))
    (nm/check! (:naming kb) inner context)
    ;; the argument constraints the rule's own variables carry, checked against each
    ;; other — the arm above this file's `binding-literals` explains.  Here rather than
    ;; on the fact path because a variable is not an argument any ground check can see,
    ;; and after naming because it reads declarations off the functors naming just
    ;; passed.
    (check-variable-constraints! kb inner context)
    ;; the rule-set check, before anything is stored: an `exceptWhen` is negation as
    ;; failure, and a cycle through it would make the settled state depend on
    ;; arrival order (docs/exceptions.md)
    (check-stratified kb sentence inner context)
    (when (rules/generator? sentence)
      (check-generator! kb sentence context))))

(defn rule-violation
  "`check-rule!` as a **value** in the shape the derivation path files — a
  `{:violation :detail}` map, or nil when the rule stands.

  The mint's form of the same list, and the reason it is a value is the reason every
  check on that path is: a firing runs inside the fixpoint, an exception escaping it
  would leave belief half-computed, and which rule happened to fire first would decide
  what the KB ends up believing.  So a mint that cannot stand is dropped and recorded
  (`violations/report`), never thrown.

  Read through the throwing form rather than restating it, so the two cannot drift —
  the same trick `core/check` plays to predict `assert`."
  [kb sentence context]
  (try (check-rule! kb sentence context) nil
       (catch clojure.lang.ExceptionInfo e
         ;; `:sentence` and `:context` are dropped because the caller re-attaches its
         ;; own — the mint's, which is the rule that was actually refused — and a
         ;; stale copy under the same key would shadow it.  They come off in a step of
         ;; their own, and the type keyword last: both refusal-vocabulary scans read
         ;; the token *following* a type keyword as a refusal type, so listing them in
         ;; one `dissoc` files whichever argument happened to sit there as caller-visible
         ;; vocabulary (`type_contract_test`, `web_propose_test`).
         (let [d      (ex-data e)
               detail (dissoc d :sentence :context)]
           {:violation (get d :type :not-well-formed)
            :detail    (assoc (dissoc detail :type) :message (.getMessage e))}))))

(defn check-exceptWhen-stratified
  "Throw unless adding an exceptWhen exception mentioning `new-exc-preds` to the stored
  rule `rule-handle` leaves the rule set stratified.

  The exception is a new negative edge from the rule to those predicates, so it can
  close a cycle through negation exactly as a whole rule can (`check-stratified`).  The
  pending node is the rule's stored graph node augmented with the new negative edges;
  `stratification-concluders` swaps it in for the stored rule so the walk sees the edge.
  Runs before the meta-sentex is stored, so a refused exception leaves nothing behind."
  [kb rule-handle new-exc-preds context]
  (when-let [rsx (p/get-sentex (:records kb) rule-handle)]
    (let [base    (rule-graph-node kb rule-handle rsx)
          pending (assoc base
                         :label           (str "rule#" rule-handle " (with the new exception)")
                         :exception-preds (concat (:exception-preds base)
                                                  (negative-predicates (:antecedent-preds base)
                                                                       new-exc-preds))
                         :consequent-pred (rules/consequent-predicate (:sentence rsx)))]
      (when (seq (:exception-preds pending))
        (when-let [cycle (wff/negation-cycle (:taxonomy kb)
                                             (stratification-concluders kb pending)
                                             pending)]
          (throw (ex-info (str "not stratified: the exception would give the rule set a "
                               "cycle through negation: " (wff/cycle-description cycle))
                          {:type :not-stratified :rule rule-handle :context context
                           :exception-preds (vec new-exc-preds) :cycle cycle})))))))

(defn- edge-negation-cycle
  "The cycle through negation that adding this `genl` / `genlCx` sentence would
  create among the **stored** rules, or nil.  Nil for anything that is not one of
  those two edges.

  Every cycle through negation contains at least one negative edge, and negative
  edges leave excepted rules only — so starting the walk at each excepted rule is
  complete, and `exception-rules` is exactly that roster in one lookup.  That is the
  same set (and the same reason) as `recheck-every-exception`'s: an edge change has
  no rule and no fact to narrow by, so it re-walks the excepted rules wholesale.
  They are few, and edge changes are rare.

  **Fast path:** no stored rule carries an exception, so the graph has no negative
  edge and no walk can find one.  That is every rule in the bundled starter, so an
  ordinary `genl` assert pays one set read and stops.

  The edge is added to a **detached copy** of the taxonomy rather than to the real
  one: the check runs before anything is written, and a refused edge must leave the
  cached closures untouched as well as the store."
  [kb sentence]
  (let [f (nm/functor sentence)]
    (when (or (= f 'genl) (= f 'genlCx))
      (let [excepted (p/exception-rules (:index kb))]
        (when (seq excepted)
          (let [[_ a b]    sentence
                probe      (tax/detached-copy (:taxonomy kb))
                _          (if (= f 'genl)
                             (tax/add-genl probe a b ::probe)
                             (tax/add-genlCx probe a b ::probe))
                concluders (stratification-concluders kb)]
            (some #(some->> (stored-rule-node kb %)
                            (wff/negation-cycle probe concluders))
                  excepted)))))))

(defn check-edge-stratified
  "Throw unless adding this taxonomy edge leaves the stored rule set stratified.

  The `genl` assert is the operation at fault, so refusing the *edge* is the
  consistent answer: it is what `wff` already does to an edge that would make the
  taxonomy cyclic, and it keeps the invariant that stored state is always stratified
  — which is what lets `check-stratified` look only for cycles through the rule being
  added.  Runs before the sentex is created and before the taxonomy is touched."
  [kb sentence context]
  (when-let [cycle (edge-negation-cycle kb sentence)]
    (throw (ex-info (str "not stratified: " (pr-str sentence)
                         " would give the rule set a cycle through negation: "
                         (wff/cycle-description cycle))
                    {:type :not-stratified :sentence sentence :context context
                     :cycle cycle}))))

;; (`wff-violation` — structural well-formedness as a value, for derived content —
;; lives in `vaelii.impl.special` now: the per-functor wff dispatch is a column of
;; the special-predicate table, which sits a layer above this namespace.)

(defn edge-stratification-violation
  "The same check as a **value**, for a `genl` / `genlCx` edge a rule *derived*
  rather than one a caller asserted: nil when the edge is admissible, else a
  violation map in the shape `constraint-violation` returns.

  A derived edge reaches the taxonomy through `integrate-transitive`, so a rule
  concluding `(genl a b)` can close a cycle with no caller asserting anything.
  Throwing there is the wrong shape — chaining is a fixpoint and must not abort
  halfway through one — so this joins the definitional constraints on the derivation
  path: the conclusion is dropped and reported in `(core/violations kb)`.  Dropping
  it is what keeps the invariant intact, since an unstratified edge that was merely
  *reported* would still be in the taxonomy."
  [kb sentence]
  (when-let [cycle (edge-negation-cycle kb sentence)]
    {:violation :not-stratified
     :detail    {:cycle   cycle
                 :message (str "not stratified: deriving " (pr-str sentence)
                               " would give the rule set a cycle through negation: "
                               (wff/cycle-description cycle))}}))

;; Negation is *not* a hard check.  `(not S)` and `S` co-existing is a soft,
;; prioritized contradiction resolved at settle time (`vaelii.impl.settle`):
;; the weaker-class belief is defeated, a default/default tie is a represented
;; dilemma, and an irreducible `:monotonic` clash is reported, never thrown.
