;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.predicates
  "What is *said* about each term of the engine's own grammar, in one place — the
  declaration half of the twenty-odd functor-keyed rosters scattered across nine
  namespaces, none of which can see each other.

  **The problem this is the bottom half of.**  Adding an engine-interpreted predicate
  means finding every place that keys on a functor name and writing an entry there.
  `special/entries` is the one that got it right: a single ordered table walked by four
  consumers, refused at load if an entry is half-written.  Every other roster —
  `settle`'s eight, `taxonomy`'s three, `checks`' four, `provers`' four, `sentex`'s
  three, `kb/equality-predicates`, `inherit/declarations`, `vocabulary/roster` — is a
  *projection* of the same fact, written where it was needed.  The record of what that
  costs is #45 (one trio spelled out in two places that had to agree), #52 and #54 (one
  spelling wired into one lane of a family and not the other, twice, in different lanes,
  from the same omission).

  **Why data and arms are split, and this half is the data.**  The arms need functions
  from four different layers — `taxonomy`, `wff`, `checks`, `settle` — so a namespace
  holding both could only ever sit at the *top* of the stack, where `taxonomy` and `wff`
  cannot read it.  This namespace therefore requires nothing but `clojure.*` and sits
  below `naming` and `sentex`, at the bottom.  It holds what a term *says*; each layer
  above attaches what is *done* about it.  Where a field seems to want a function it
  holds a **keyword naming** one, resolved by the layer that owns the function.

  **Fields.**  Each entry is `term -> spec`:

    :shape    how the term is written as a sentence, or nil for one that is never a
              sentence functor (a collection: `string`, `thing`, `binary_predicate`).
              `{:args [kind …]}`, optionally `:optional [kind …]` for a trailing
              argument that may be omitted and `:variadic kind` for an open tail.
              Argument kinds are `argument-kinds` below; arity is `(count :args)`.
    :storage  `[kind target]` — which of a small closed set of storage shapes the
              declaration is cached under, and which table it lands in.  `[:none]` for
              a term nothing caches.  `storage-kinds` below.
    :checked  does `special/entries` give the functor a structural well-formedness arm.
    :facets   a set from the **closed** vocabulary `facets` below — the lanes the term
              takes part in.  An open set of keywords would be a roster again, with the
              same drift and none of the checking.
    :family   the family whose spellings must move together, or nil.  `functional` and
              `functionalInArg` are one family written two ways; the four argument
              constraints are another.  `mark-families` below.
    :sweeps   what a declaration arriving *after* the content it constrains puts back
              in question — `sweep-kinds` below — or absent for a term whose retroactive
              half is not `settle`'s clash-exposure pass.  The `:reach` facet says that a
              term sweeps; this says *what*, for the one lane whose reaches have names.
    :stops-short  facet -> prose: an implication of `facet-contract` this term does not
              satisfy, and the reason.  Checked against the set that is actually owed, in
              both directions, so the record can neither be missing nor go stale once the
              term gains the facet.  A recorded exception, not a suppression: the rule
              still holds over everything that does not carry one.
    :opposing-read  prose, on every `:arbitrable` term and on the one that deliberately
              is not: what the conviction's opposing side is **read through**, and
              whether that read survives the nogood defeating either member.  Not
              decidable from the declaration — `arity` names a second sentex exactly as
              the four arbitrable marks do — so it is a stated claim rather than an
              inferred one, which is what `checks.clj`'s comment above `arbitrable-kinds`
              says today in a place no validator could read.
    :notes    prose, only where the term does something this vocabulary has no facet
              for.  A note is a **finding**, not a description: each one is a lane the
              facet vocabulary does not reach yet.
    :enforced prose naming the code path that reads the term — what a KB author is told
              by `core/interpreted` when they ask whether a declaration does anything.
              Carried by the terms CxCore comments and by no others, which is why an
              entry without it is not a defect: the seven grammar terms CxCore does not
              comment are outside the question rather than unanswered.
    :inert    prose recording that nothing reads the term **and that this is a
              decision**.  Written by the `inert` constructor, which sets the facet with
              it, so the class is never a second opinion about the facets.

  **What is deliberately not here** is the arms themselves — and, one step further out,
  which *prover* answers a term's goals.  There is no `:answered-by`: `applicable?` is
  per-prover logic over a goal's shape rather than a per-predicate fact, `add-prover`
  registers provers with no entry here at all, and `provers/sole-prover` already asks the
  coordination question a binding would be reaching for.  The argument in full is
  `provers`' header, under \"Why a prover is not a predicate's property\"; the fact about
  the *declaration* that does belong is the `:answers` facet below.

  **What reads this.**  `special/entries` joins the declarations to `special`'s arms;
  `taxonomy`'s three rosters (`closure-relations`, `arg-declaration-props`,
  `functional-family-marks`), `settle`'s clash-declaration and trigger rosters,
  `spec/::prop-kind` and `vocabulary/roster` are field reads.

  **Two validators, two layers.**  `check-families` runs *here*, at this namespace's
  load, over what one entry can say about another.  `check-facets` runs at `settle`'s,
  because two of its rules read an arm that lives four layers up and a bottom namespace
  cannot see whether an arm exists — it takes those facts as arguments rather than
  requiring the layer that holds them.
  The rosters that have not moved yet are reconstructed from here by `predicates_test`
  and asserted equal to the live one, which is the only defensible proof that the population
  is right before a consumer switches over.  A roster that *has* moved is proved
  differently: its value becomes a literal in the test, since a reconstruction of a
  derived var proves the wiring and nothing about what it holds.

  **Order is content.**  `entries` is a vector, not a map, because `special/entries` is
  ordered and `rebuild-taxonomy` replays it top to bottom with a rebuild arm allowed to
  read what an earlier one wrote.  The table's functors come first, in the table's own
  order; the rest of CxCore's grammar follows.")

;; ---- the closed vocabularies ---------------------------------------------

(def argument-kinds
  "What an argument position denotes, as the `wff` arms already hold it.  Closed: a
  kind here is one an arm can be *generated* from, so a position no kind fits is a
  position whose check has to stay hand-written.

  The distinction that matters most is `:predicate` against `:relation`.  A mark read
  off a sentence's functor (`prop-problems`, `functional-in-arg-problems`) holds its
  subject to a symbol that is not an individual — a functor is a symbol.  An argument
  *constraint* (`arg-constraint-problems`, `arg-preserving-problems`) is looser on
  purpose: a function has argument positions exactly as a predicate does, a function is
  CapitalCamelCase and so is indistinguishable from an individual, and a relation may be denoted by a NAT
  rather than named.  Collapsing the two refuses the conventional spelling and waves the
  exotic one through."
  #{:predicate                ; a symbol that is not an individual — refused by nm/individual?
    :relation                 ; a symbol *or* a non-atomic term: a predicate, a function, or a NAT
    :relation-name            ; a symbol, and one the taxonomy holds transitive
    :type                     ; a symbol that is not an individual — a collection
    :context                  ; a Cx-spelled symbol that is not a query context
    :function                 ; a symbol naming a NAT function (a FruitFn-shaped constant)
    :position                 ; a positive integer, one-based
    :integer                  ; any integer
    :term                     ; anything — a constant, a literal, or a NAT
    :sentence})               ; a nested sentence

(def storage-kinds
  "The shapes a declaration is cached under.  Each names what the add / drop / rebuild
  triple looks like, which is the whole of why the set is small: three arms that differ
  only in the table they call are three arms one shape can write.

  `:mark` is **not** `:prop`, and the difference is not cosmetic: `:prop` means the
  `tax/props` roster, whose keys `spec/::prop-kind` pins, while `disjoint_metatype` and
  `sibling_disjoint` are one-term marks into tables of their own.  Calling them `:prop`
  would put two keywords in that spec that no `has-prop?` ever answers."
  #{:prop                     ; tax/props, keyed by the ::prop-kind keyword — (F P)
    :mark                     ; a one-term mark into a table of its own — (F T)
    :edge                     ; a cached transitive closure — (F sub super)
    :keyed-pair               ; a table keyed on the argument pair — (F a b)
    :pred-position            ; a table keyed on [predicate position] — (F P n)
    :none})                   ; nothing is cached; the declaration is read back per use

(def facets
  "The lanes a term takes part in.  **Closed**, and closed on purpose: growing it is one
  commit that adds the keyword here and the implication that governs it to the facet
  validator at the same time, so a facet can never mean whatever its first user assumed.

  Six of the ten are reconstructible from a live data structure and are pinned that way
  by `predicates_test`.  Four — `:answers`, `:retriggers`, `:convicts` and `:inert` —
  are *claims*: no roster in the tree states them, which is exactly why they are the
  ones that go wrong quietly."
  #{:cached                   ; special/entries gives it the integrate/disintegrate/rebuild triple
    :derived                  ; …and that triple runs on the derivation path too (:derived?)
    :migrates                 ; asserting it merges terms — kb/equality-predicates
    :arbitrable               ; its violation names other believed sentexes, so settle arbitrates it
    :reach                    ; arriving after the facts, it sweeps what it now convicts
    :query-only               ; never stored: the wff arm is the refusal, a prover is the answer
    :answers                  ; a prover answers goals of this functor
    :retriggers               ; its arms post exception re-checks
    :convicts                 ; a definitional check reads it and can convict stored content
    :inert})                  ; nothing reads it, and that is a decision — not an omission

(def facet-contract
  "What carrying a facet commits the declaration to — the closed vocabulary's own
  contract, and what `check-facets` walks.  Keyed by facet, and the keys are `facets`
  **exactly**: the validator refuses the pair if they diverge, so growing the vocabulary
  is the one commit the `facets` docstring promises rather than a keyword whose meaning
  its first user decides.

    :implies  the facets carrying this one entails.  Each is a bug the repo has paid
              for, stated as an implication rather than as a review item: `:convicts`
              without `:reach` convicts at the entry point and misses everything stored before
              it, permanently, in the declaration-last arrival order (#54);
              `:arbitrable` without `:convicts` arbitrates a violation nothing raises;
              `:derived` and `:migrates` without `:cached` name a derivation path for a
              triple that does not exist; `:query-only` without `:answers` is a term
              refused at the entry point and answered by nothing at all; `:retriggers` without
              `:answers` posts a re-check for a goal no prover takes.
    :lane?    is this a lane a mark **family** has to agree about.  The enforcement
              lanes are: a family joined to one of them in one spelling and not another
              fails silently in the arrival order that spelling was the only way into,
              which is #52 and #54, one omission and two lanes.  So is `:answers`, for
              the same reason seen from the query side — `provers/meta-constraint-shape`
              is one table over the argument-constraint family, and a spelling missing
              from it is answered from stored facts alone where its siblings are answered
              up the `genl` closure.  `:retriggers` is not: a re-check posting is one line
              inside one arm, aimed at what that arm's own conclusion changes.
              `:query-only` and `:inert` are classifications of the whole term, which a
              family read by anything at all cannot differ about.

  An implication a term does not satisfy is not automatically a refusal: it is a
  refusal *unless the entry records the exception*, in `:stops-short`.  Five entries carry
  one today, over six facets: three terms convict with no reach, and three answer goals
  about a predicate and post no re-check of their own.  Each reason is about the engine rather than about the
  declaration, and the point of the field is that the reason is written where a validator
  can hold it to being exactly the set that is owed."
  {:cached     {:implies #{}                :lane? true}
   :derived    {:implies #{:cached}         :lane? true}
   :migrates   {:implies #{:cached}         :lane? true}
   :arbitrable {:implies #{:convicts}       :lane? true}
   :reach      {:implies #{}                :lane? true}
   :convicts   {:implies #{:reach}          :lane? true}
   :query-only {:implies #{:answers}        :lane? false}
   :answers    {:implies #{}                :lane? true}
   :retriggers {:implies #{:answers}        :lane? false}
   :inert      {:implies #{}                :lane? false}})

(def sweep-kinds
  "What a declaration arriving **after** the content it constrains puts back in question
  — the reach `settle`'s clash-exposure pass runs for it, and so the structure of the split
  `settle/clash-declaration-kinds` is written as.

  A declaration is not its own candidate the way a fact is.  `(disjoint dog cat)` arriving
  after both memberships has to reach them, or whether the pair is reported depends on
  which was written first.  The kind says where that reach goes: over the **terms** the
  declaration separates, or over the **facts beneath the predicate** a descending mark now
  stands over, or both.

  **A term is a clash declaration by carrying one of these**, so enrolling one and leaving
  `declaration-reach` with no arm for it is not a state that roster can be in.  Absent is
  the answer for a term whose retroactive half is a different mechanism: `arity`'s is a
  *report* that moves no belief, the argument constraints' is `special/entail-existing`,
  which mints rather than convicting, and `siblingDisjointException`'s runs in the removal
  direction.

  **Carrying a sweep is not being in `settle/definitional-marks`**, and reading one roster
  as though it were the other is what #54 filed.  That roster pairs a functor with the
  taxonomy prop key it stores under, which `functionalInArg` has none of — it stores
  `[pred n]` pairs — so the generalized mark is correctly absent from it, and must still
  carry `:predicate-marked` here and a shape for the lane that recognizes it at its own
  arity.  Derive a reach from the pairing table and the generalized mark silently loses
  the one arrival order — declaration-last over an unmergeable pair — that `functional`
  itself handles."
  #{:type-separating         ; the memberships of the terms the declaration separates
    :predicate-marked        ; the facts beneath the predicate a descending mark stands over
    :both})                  ; genl alone: the sub gains ancestors *and* a mark descends

(def mark-families
  "The families whose spellings must move together.  A family lives in more than one
  lane and has twice been joined to only one (#52, #54), so the family is named once and
  each spelling carries it.  `tax/functional-family-marks` and
  `tax/arg-declaration-props` are this field read back.

  **`:functional`** is acted on by the *merge* lane (`special`'s `equate-*` entry points, where
  two fillers of a functional slot are equated) and by the *clash exposure* lane
  (`settle`'s declaration reach and trigger rosters, where two unmergeable fillers are
  reported).  Both lanes have to recognize the same spellings, and neither fails loudly
  when it does not — the merge simply does not happen, or the clash simply is not
  reported, in the one arrival order that route was the only way into.  Enrolling
  `functionalInArg` by name in each place is what left #52 (the declaration-last merge
  entry point held an exact-functor test) and #54 (the declaration arrived and swept nothing)
  open at the same time, in different lanes, from the same omission.  So a third
  spelling is added *here* and the lanes follow.

  **`:argument-constraint`** is the four declarations that constrain a predicate's
  argument positions.  They are read as one — the descension asks per super-predicate
  whether it declares *anything*, `special/entail-existing` sweeps three of the four,
  `checks` pairs two of them against each other — and each is written at its own arity,
  which is why the family is the thing a reader names and the shape is not.

  A family is **not** a storage roster.  `functional` stores under the `:functional`
  prop where `functionalInArg` stores `[pred n]` pairs; the two have no common storage
  to be rostered by, only a common family and a common argument 1.  Keep `:family` and
  `:storage` separate or #52 comes back with a new number."
  #{:functional :argument-constraint})

;; ---- entry constructors --------------------------------------------------
;;
;; Written rather than spelled out, for the reason `special/prop-entry` is: an entry a
;; couple of parameters *construct* has no way for its fields to disagree with each
;; other, and the twenty-two predicate marks `prop` builds differ in exactly one keyword.

(defn- prop
  "A one-place predicate mark — `(F P)` — cached as taxonomy prop `kind`.

  `:derived` unless told otherwise, so a mark that arrives by *derivation* installs
  like an asserted one: a rule concluding `(symmetric P)`, and — the case that actually
  happens on every KB — the CxUniverse copy a `decontextualized_predicate` lift makes of
  one.  The copy carries its own context, which is what a scoped `has-prop?` reads, so
  without the facet the mark is recorded only under the context the declaration was
  stated in while the *sentex* is visible everywhere.  The rebuild arm replays every
  stored sentex of the functor either way, so the live KB and the recovered one
  disagreed about the same store — a restart changed the answer.

  Every mark but `decontextualized_predicate` carries it; that one's reason for
  withholding it is on its own entry."
  [kind & {:keys [facets arg derived? checked? notes sweeps]
           :or   {facets #{} arg :predicate derived? true checked? true}}]
  (cond-> {:shape   {:args [arg]}
           :storage [:prop kind]
           :checked checked?
           :facets  (cond-> (conj facets :cached) derived? (conj :derived))
           :family  nil}
    sweeps (assoc :sweeps sweeps)
    notes  (assoc :notes notes)))

(defn- mark
  "A one-term mark into a table of its own — `(F T)` — cached, but not a `tax/props`
  entry and so not a `spec/::prop-kind` keyword."
  [target & {:keys [facets arg notes sweeps] :or {facets #{} arg :type}}]
  (cond-> {:shape   {:args [arg]}
           :storage [:mark target]
           :checked true
           :facets  (conj facets :cached :derived)
           :family  nil}
    sweeps (assoc :sweeps sweeps)
    notes  (assoc :notes notes)))

(defn- pair
  "A two-argument declaration cached in a table keyed on the pair — `(F a b)`."
  [target arg-kind & {:keys [facets derived? notes sweeps]
                      :or   {facets #{} derived? true}}]
  (cond-> {:shape   {:args [arg-kind arg-kind]}
           :storage [:keyed-pair target]
           :checked true
           :facets  (cond-> (conj facets :cached) derived? (conj :derived))
           :family  nil}
    sweeps (assoc :sweeps sweeps)
    notes  (assoc :notes notes)))

(defn- wff-only
  "A declaration `special/entries` gives a well-formedness arm and nothing else — read
  back through the index per use rather than cached."
  [args & {:keys [facets optional notes] :or {facets #{}}}]
  (cond-> {:shape   (cond-> {:args args} optional (assoc :optional optional))
           :storage [:none]
           :checked true
           :facets  facets
           :family  nil}
    notes (assoc :notes notes)))

(defn- operator
  "A query operator: refused at the entry point — the wff arm *is* the refusal — and answered
  by a prover.  `docs/naf.md`, `docs/aggregate.md`."
  [shape & {:keys [notes]}]
  (cond-> {:shape   shape
           :storage [:none]
           :checked true
           :facets  #{:query-only :answers}
           :family  nil}
    notes (assoc :notes notes)))

(defn- collection
  "A CxCore term that is never a sentence functor — a type, read by name by some check.
  It has no shape: a membership's shape is not per-term data."
  [& {:keys [facets notes] :or {facets #{}}}]
  (cond-> {:shape nil :storage [:none] :checked false :facets facets :family nil}
    notes (assoc :notes notes)))

(defn- structural
  "A term the *canonicalizer* reads, not the table: it becomes a slot of the record and
  is never stored under its own functor."
  [shape notes]
  {:shape shape :storage [:none] :checked false :facets #{} :family nil :notes notes})

;; ---- the vocabulary answer -----------------------------------------------

(defn- enforced
  "`spec` plus `where` — the prose naming the code path that reads the term, which is
  what `vocabulary/roster` answers with and what `core/interpreted` hands a KB author.

  **Prose, and not generated prose.**  No facet set can produce
  \"taxonomy/add-genl — the cached closure every membership, match and placement reads\",
  and a sentence assembled from `#{:cached :convicts}` would be worse than none: the
  audit exists so an author can be told *where* the enforcement is, which is the half of
  the answer that stays a judgement.  What is no longer a judgement is the **class** —
  `roster` reads that off `:facets`, so a term the engine demonstrably reads cannot be
  called inert by writing different prose beside it.

  Nil-tolerant, because the question is only asked about terms CxCore comments: the
  seven grammar terms it does not comment (`equals`, `sameAs`, `functionalInArg` and the
  four query operators) pass through unchanged, and `vocabulary/audit` is what notices a
  term the *ontology* names and this file answers for with nothing."
  [spec where]
  (cond-> spec where (assoc :enforced where)))

(defn- inert
  "`spec` plus `why` — the record that nothing reads the term **and that this is a
  decision rather than an omission**, which is why it sets the `:inert` facet with the
  prose rather than leaving the two to be written separately.

  One constructor for both halves is what makes the contradiction unwritable: an entry
  cannot claim a lane and be classified inert, because claiming a lane means carrying a
  facet and this replaces the facet set outright."
  [spec why]
  (assoc spec :facets #{:inert} :inert why))

;; ---- the entries ---------------------------------------------------------

(def entries
  "`[term spec]` pairs, ordered.  `special/entries`' fifty functors first, in the table's
  own order — that order is replayed by `rebuild-taxonomy` and so is content — then the
  rest of the grammar `vocabulary/roster` covers.

  Read `entry` / `by-facet` / `by-family` / `by-storage` below rather than this vector;
  they are what the rosters above become."
  (vec
   (concat
    ;; ---- the two cached closures ----------------------------------------
    ;;
    ;; :derived on both edges below and on the four separations after them, for one
    ;; argument in two halves.  A conclusion a rule reached must
    ;; constrain the moment it is believed — a derived `(genl a b)` that never reached
    ;; the closure is stored and believed while the taxonomy has not learned the edge,
    ;; and a rule-concluded separation would separate nothing.  And every rebuild arm
    ;; replays every stored sentex of its functor, so without the facet a *restart* is
    ;; what first activates the declaration: the live KB and the recovered one then
    ;; disagree about one store.  Each records the context the declaration was stated
    ;; in besides, which is what a scoped read (`has-prop?`, `disjoint?`) answers from.
    [['genl (enforced (assoc (pair :genl :type
                                   :facets #{:reach :convicts :answers :retriggers}
                                   :sweeps :both)
                             :storage [:edge :genl])
                      "taxonomy/add-genl — the cached closure every membership, match and placement reads")]
     ['genlCx (enforced (assoc (pair :genlCx :context
                                     :facets #{:reach :convicts :answers :retriggers}
                                     :sweeps :type-separating)
                               :storage [:edge :genlCx])
                        "taxonomy/add-genlCx — the visibility closure a context read walks")]

     ;; ---- the separations ------------------------------------------------
     ['disjoint (enforced (assoc (pair :disjoint :type :facets #{:reach :convicts :arbitrable}
                                       :sweeps :type-separating)
                                 :opposing-read
                                 (str "the nogood pairs the two memberships, and the (disjoint A B)"
                                      " declaration the conviction is read through is not a member of"
                                      " it — so whichever membership is defeated, the disjointness"
                                      " table the next pass reads is the one that convicted."))
                          "taxonomy/add-disjoint, read by checks/disjoint-problems and arbitrated by settle")]
     ['disjoint_metatype
      (enforced (mark :disjoint-metatype :facets #{:reach :convicts}
                      :sweeps :type-separating
                      :notes (str "the members already asserted are recorded by the integrate arm"
                                  " as stored rather than believed — a belief-filtered sweep here"
                                  " would leave a defeated membership out of the cache keys"
                                  " permanently. No facet covers a retroactive record of"
                                  " supporters."))
                "taxonomy/mark-disjoint-metatype — the clique consulted, never stored")]
     ['sibling_disjoint (enforced (mark :sibling-disjoint :facets #{:reach :convicts}
                                        :sweeps :type-separating)
                                  (str "taxonomy/mark-sibling-disjoint — the specialization clique keyed off"
                                       " the genl closure, consulted like disjoint_metatype and arbitrated by"
                                       " settle"))]
     ['siblingDisjointException
      (enforced (assoc (pair :sib-exception :type)
                       :notes (str "its *retract* is the one move the generic belief reconcile does"
                                   " not cover — an exception present ab initio kept its pair out"
                                   " of the clash set entirely — so the disintegrate arm posts to"
                                   " :sib-exc-dirty and settle re-arms. That is a reach in the"
                                   " removal direction, which :reach (an arriving declaration)"
                                   " does not name."))
                (str "taxonomy/add-sib-exception — exempts one pair the sibling clique or a"
                     " disjoint_metatype would separate; read globally in disjointness-test,"
                     " and a retract re-arms through settle's :sib-exc-dirty sweep"))]

     ;; ---- the definitional marks -----------------------------------------
     ['transitive  (enforced (prop :transitive :facets #{:answers})
                             (str "taxonomy prop :transitive — the generic closure prover; also a"
                                  " binary_predicate type. (transitive genl) is stored but inert"
                                  " (closure-relations), so genl stays queryable without routing to the"
                                  " generic prover"))]
     ['symmetric   (enforced (prop :symmetric :facets #{:answers})
                             (str "taxonomy prop :symmetric — canonical argument order, so both spellings"
                                  " are one sentex; also a binary_predicate type"))]
     ['asymmetric  (enforced (assoc (prop :asymmetric :facets #{:reach :convicts :arbitrable
                                                                :answers}
                                          :sweeps :predicate-marked)
                                    :opposing-read
                                    (str "the nogood pairs the tuple with its converse; the"
                                         " (asymmetric P) mark is not a member of it, so defeating"
                                         " either direction leaves the mark standing and the"
                                         " conviction re-derivable."))
                             "checks/asymmetry-problem — a nogood against the converse; also a binary_predicate type")]
     ['reflexive   (enforced (prop :reflexive :facets #{:answers})
                             "taxonomy prop :reflexive — the reflexive prover; also a binary_predicate type")]
     ['functional  (enforced (assoc (prop :functional :facets #{:reach :convicts :arbitrable}
                                          :sweeps :predicate-marked)
                                    :family :functional
                                    :opposing-read
                                    (str "the nogood pairs the two fillers of the slot; the"
                                         " (functional P) mark is not a member of it, so defeating"
                                         " either filler leaves the mark standing.")
                                    :notes (str "acted on by two lanes that must recognize the"
                                                " same spellings and neither of which fails"
                                                " loudly: the *merge* entry point, where two fillers of"
                                                " a functional slot are equated, and the *clash"
                                                " exposure* pass, where two unmergeable fillers"
                                                " are reported. Deriving an equality is not"
                                                " :migrates — that facet is for a relation whose"
                                                " own assertion is the merge."))
                             (str "checks/functional-problems, and special/derive-functional-equalities"
                                  " on two symbols; also a binary_predicate type"))]
     ['irreflexive (enforced (prop :irreflexive
                                   :notes (str "convicts a *self* tuple (P a a), which names no other"
                                               " believed sentex — so it is neither :arbitrable nor"
                                               " swept: there is nothing for a late declaration to"
                                               " weigh the fact against. An entry point refusal with no"
                                               " retroactive half."))
                             (str "checks/irreflexivity-problem — a self tuple (P a a) is refused at the"
                                  " entry point; also a binary_predicate type"))]
     ['anti_symmetric (enforced (prop :anti-symmetric
                                      :notes (str "derives (equals a b) from a believed converse"
                                                  " rather than convicting either — so it merges"
                                                  " where the other pairwise marks separate, and"
                                                  " no facet names deriving."))
                                (str "checks/antisymmetry-problems, and"
                                     " special/derive-antisymmetric-equalities merging two symbols a believed"
                                     " converse forces equal; also a binary_predicate type"))]
     ['anti_transitive (enforced (assoc
                                  (prop :anti-transitive :facets #{:reach :convicts :arbitrable}
                                        :sweeps :predicate-marked
                                        :notes (str "the one nogood whose members are three rather"
                                                    " than two: it convicts the two-step chain and"
                                                    " the direct step together."))
                                  :opposing-read
                                  (str "the nogood is the triple — the two-step chain and the direct"
                                       " step — and the (anti_transitive P) mark is none of the three,"
                                       " so whichever step is defeated the mark still reads."))
                                 (str "taxonomy prop :anti-transitive — checks/antitransitivity-problems"
                                      " convicts the two-step chain and the direct step together, as the one"
                                      " nogood whose members are three rather than two (settle/decide-nogood"
                                      " reads the whole set); plus its disjointness with transitive — no"
                                      " predicate is both — and a binary_predicate type"))]

     ;; ---- the arity and the generalized functional mark ------------------
     ;;
     ;; :derived on both, for the prop marks' reason rather than for a rule's: a
     ;; `decontextualized_predicate` lift makes a CxUniverse copy carrying its own
     ;; context, and the scoped read wants that context recorded.
     ['arity (enforced {:shape   {:args [:relation :integer]}
                        :storage [:pred-position :arity]
                        :checked false
                        :facets  #{:cached :derived :reach :convicts}
                        :family  nil
                        :opposing-read
                        (str "the negative answer, and the reason this term names a second sentex"
                             " exactly as the four arbitrable marks do and is still not one of"
                             " them: the sentex it names is the vocabulary entry the conviction is"
                             " READ THROUGH — declared-arity answers from the taxonomy's arity"
                             " table, which follows belief — so a nogood defeating the declaration"
                             " would destroy its own premise. Measured: the declaration is defeated"
                             " in the settle that admits the pair, revived by the next settle's"
                             " clear-defeats! while the table it was uninstalled from is still"
                             " empty, and with the table empty the clash is never re-derived. The"
                             " comment above checks/arbitrable-kinds is the long form.")
                        :notes   (str "convicts and reaches, but is deliberately NOT :arbitrable:"
                                      " the arity table follows belief, so a nogood that defeated"
                                      " the declaration would destroy its own premise. Its"
                                      " retroactive half is settle/report-arity-reach! — a report"
                                      " that moves no belief — and :reach does not distinguish a"
                                      " sweep that decides from one that only names.")}
                       (str "checks/arity-problem at the entry point, settle/report-arity-reach! over"
                            " content stored before it"))]
     ['functionalInArg {:shape   {:args [:predicate :position]}
                        :storage [:pred-position :functional-in-arg]
                        :checked true
                        :facets  #{:cached :derived :reach :convicts :arbitrable}
                        :family  :functional
                        :sweeps  :predicate-marked
                        :opposing-read
                        (str "the same as functional's, read at the declared position: the nogood"
                             " pairs the two fillers of [P n] and the (functionalInArg P n) mark is"
                             " not a member of it.")
                        :notes   (str "read UP the predicate hierarchy and refuses tuples,"
                                      " where transitiveInArg — the same name shape — is"
                                      " read for the goal's own predicate and licenses"
                                      " them. The two sit on opposite sides of the"
                                      " prover/checker divide.")}]
     ['inverse (enforced (assoc (pair :inverse :predicate) :facets #{:cached :derived :answers})
                         "taxonomy/add-inverse — the prover that hands the swapped goal back")]

     ;; ---- placement, lifting and the policy grants -----------------------
     ['decontextualized_predicate
      (enforced (prop :decontextualized :derived? false
                      :notes (str "NOT :derived?, alone among the marks: its integrate arm runs an"
                                  " O(extent) retroactive lift whose copies are chaining seeds, and"
                                  " the derivation path discards an arm's return value. A reach in"
                                  " the *lift* direction, which :reach does not name."))
                "special — the CxUniverse lift, retroactive over the extent")]
     ['forced_decontextualized_predicate (enforced (prop :forced-decontextualized)
                                                   "special — storage straight into CxUniverse")]
     ['target_following_predicate
      (enforced (prop :target-following
                      :notes (str "makes a (P … (sentexHandle H) …) meta-sentex not outlive H."
                                  " A teardown cascade, which no facet names."))
                (str "taxonomy prop :target-following — the mark"
                     " core/retract-following-metas! reads to tear down a meta-sentex when"
                     " the sentex it names by handle is retracted"))]
     ['abducible_predicate  (enforced (prop :abducible)
                                      "taxonomy prop :abducible — the gate on what abduce may hypothesize")]
     ['closed_extent_predicate
      (enforced (prop :closed-extent :facets #{:answers :retriggers}
                      :notes (str "its arms re-index the rules the grant newly governs, from both"
                                  " arrival orders — a rule asserted before the grant carries no"
                                  " posting for P, so nothing on P would ever bring its firings"
                                  " back."))
                (str "taxonomy prop :closed-extent — ClosedExtentProver answers (not (P …))"
                     " from the absence of a positive, and a closed negative rule antecedent"
                     " under the grant is negation as failure"))]
     ['modal_predicate (enforced (prop :modal)
                                 (str "taxonomy prop :modal — the gate BeliefProjectionProver reads to decide"
                                      " which predicates project their sentence into the agent's context"))]

     ;; ---- the NAT function kinds -----------------------------------------
     ['reifiable_function       (enforced (prop :reifiable   :arg :function)
                                          "taxonomy prop :reifiable — the gate that turns the nat reify pass on")]
     ['unreifiable_function     (enforced (prop :unreifiable :arg :function)
                                          "taxonomy prop :unreifiable — kept structural for a prover to compute")]
     ['quoting_function         (enforced (prop :quoting     :arg :function)
                                          (str "taxonomy prop :quoting — its arguments are a mention, held opaque to"
                                               " identity congruence (res/representative-term spelling mode)"))]
     ['context_denoting_function (enforced (prop :context-denoting :arg :function)
                                           (str "taxonomy prop :context-denoting — a Cx*Fn whose applications reify to"
                                                " a cx/ context constant (docs/context-nat.md)"))]
     ['contextArgSubrelation   (enforced (wff-only [:function :position :predicate])
                                         (str "context-nat producer — sibling F-contexts differing at one arg are"
                                              " ordered by the sub-relation on that arg, materializing genlCx"))]
     ['functionCorrespondingPredicate
      (enforced (wff-only [:function :predicate] :optional [:position]
                          :facets #{:answers})
                (str "nat — reifies an application to the value the predicate already names,"
                     " and projects a minted constant back onto it"))]]

    ;; ---- the equality relations ------------------------------------------
    ;; Sorted, so the table is a function of the set rather than of set iteration
    ;; order — the same sort `special/entries` applies to `kb/equality-predicates`.
    ;; Only `rewriteOf` carries vocabulary prose, because CxCore comments only it: the
    ;; other two are grammar the audit is not asked about, which is a fact about the
    ;; ontology rather than about what the engine does with them.
    (map (fn [f]
           [f (enforced
               (assoc (pair :equality :term :derived? false
                            :facets #{:migrates :answers :retriggers})
                      :notes (str "not :derived?, unlike every other cached declaration:"
                                  " the equality arms are reached by name from the"
                                  " derivation path instead. Two compound shapes are not"
                                  " a symbol merge and each arm dispatches on them — a"
                                  " NAT reify-to-term declaration, and a schematic"
                                  " equational rule."))
               (get '{rewriteOf "nat for a compound right side, the equality partition for a symbol"}
                    f))])
         '[equals rewriteOf sameAs])

    ;; ---- the argument constraints ----------------------------------------
    [['arg       (enforced (assoc (prop :declares-arg-isa :arg :relation
                                        :facets #{:reach :convicts :answers :retriggers})
                                  :shape  {:args [:relation :position :type]}
                                  :family :argument-constraint
                                  :notes (str "open-world, so its reach back over stored tuples"
                                              " *mints* the type rather than convicting the fact:"
                                              " special/entail-existing, a third sweep mechanism"
                                              " beside settle's clash reach and its arity report,"
                                              " and the only one gated on a dynamic var"
                                              " (checks/*assertive-arg-types?*)."))
                           "checks/args-problem — refuses on the way in, and entails under *assertive-arg-types?*")]
     ['genlArg   (enforced (assoc (prop :declares-arg-genl :arg :relation
                                        :facets #{:reach :convicts :answers})
                                  :shape  {:args [:relation :position :type]}
                                  :family :argument-constraint
                                  :stops-short
                                  {:retriggers
                                   (str "both inferences it licenses arrive through an ordinary"
                                        " fact trigger: the meta-level one under this functor,"
                                        " a goal of this shape and the declaration answering it"
                                        " sharing it, and the object-level one under"
                                        " the minted membership's own. special/declaration-"
                                        "subjects excludes it for that reason, and arg carries"
                                        " :retriggers for a different one — its arms post the"
                                        " arg-type re-check.")}
                                  :notes "the same one level up; entail-existing covers it too.")
                           "checks/genls-problem — the same, one level up")]
     ['arg1      (inert {:shape {:args [:relation :type]} :storage [:none] :checked false
                         :family nil :facets #{}
                         :notes (str "the binary projection of (arg ?p 1 ?t), bridged to it"
                                     " by CxCore rules in both directions and held to arg's"
                                     " own declaration arms at the projected position"
                                     " (checks/declaration-problem), so both spellings of"
                                     " one declaration refuse identically. The projection"
                                     " relates STORED declarations only — a reading arg"
                                     " generalizes up genl or inherits from a"
                                     " super-predicate has no argN twin; ask arg for those."
                                     " Exists so a positional constraint can be the subject"
                                     " of a binary declaration such as"
                                     " (predAllSpecified arg1 predicate).")}
                        (str "binary projection of arg position 1; enforcement shared with"
                             " arg at the entry point, inference through the bridge rules"))]
     ['arg2      (inert {:shape {:args [:relation :type]} :storage [:none] :checked false
                         :family nil :facets #{}
                         :notes (str "the binary projection of (arg ?p 2 ?t) — see arg1."
                                     " Deliberately shipped ahead of any consumer, for"
                                     " symmetry with the KE packet that commissioned the"
                                     " family; unused-for-now is the stated decision, the"
                                     " way serve's open-routes states its.")}
                        "binary projection of arg position 2 — see arg1")]
     ['arg3      (inert {:shape {:args [:relation :type]} :storage [:none] :checked false
                         :family nil :facets #{}
                         :notes (str "the binary projection of (arg ?p 3 ?t) — see arg1"
                                     " and arg2's unused-for-now note.")}
                        "binary projection of arg position 3 — see arg1")]
     ['quotedArg (enforced (assoc (prop :declares-quoted-arg :arg :relation
                                        :facets #{:convicts :answers})
                                  :shape  {:args [:relation :position :type]}
                                  :family :argument-constraint
                                  :stops-short
                                  {:reach
                                   (str "the family's reach is special/entail-existing, which MINTS"
                                        " what a late declaration now says about stored tuples, and"
                                        " a quotedArg says nothing that can be minted: the kind of"
                                        " a written term is computed from the term, so there is no"
                                        " membership to draw. Checked and never entailed, which is"
                                        " docs/argtypes.md's own scope line and not an omission."
                                        " A conviction reach — naming the stored tuples a late"
                                        " quotedArg refuses — would be an arity-shaped report and"
                                        " is a different mechanism from this facet's.")
                                   :retriggers
                                   (str "the goal and the declaration share a functor, so an"
                                        " arriving (quotedArg P n T) posts its own re-check through"
                                        " recheck-on-predicate; the genl edge that imports a"
                                        " super's declaration is the other ingredient, and genl"
                                        " carries :retriggers itself.")}
                                  :notes (str "the mention twin: the family member read for a"
                                              " *mentioned* argument rather than a used one."))
                           (str "checks/args-quoted-problem — the mention twin: types the argument as a"
                                " term by its literal kind; answered up the genl closure by"
                                " provers/MetaConstraintProver, as its three siblings are"))]
     ['interArg  (enforced (assoc (prop :declares-inter-arg-isa :arg :relation
                                        :facets #{:reach :convicts :answers})
                                  :shape  {:args [:relation :position :type :position :type]}
                                  :family :argument-constraint
                                  :stops-short
                                  {:retriggers
                                   (str "genlArg's reason, at the conditional form: each"
                                        " inference it licenses is a stored sentex, and reaches"
                                        " an exception through that sentex's own fact trigger.")}
                                  :notes (str "entail-existing reaches two of its three arrival"
                                              " orders; the third — the trigger's type arriving"
                                              " after both the fact and the declaration — is the"
                                              " family's documented open-world non-reach. The only"
                                              " constraint whose trigger position is contravariant:"
                                              " a stored supertype answers a subtype query there,"
                                              " where every other type position reads up genl."))
                           "checks/inter-args-problem — the conditional form, same two paths")]

     ;; ---- the argument-preserving declarations ---------------------------
     ['transitiveInArg        (enforced (wff-only [:relation :position :relation-name]
                                                  :facets #{:answers})
                                        "inherit — the argument reach along a declared transitive relation")]
     ['transitiveInArgInverse (enforced (wff-only [:relation :position :relation-name]
                                                  :facets #{:answers}
                                                  :notes "the same declaration, read backwards.")
                                        "inherit — the same, read backwards")]

     ;; ---- the definitional collection relations --------------------------
     ['defnNecessary  (enforced (wff-only [:type :sentence] :facets #{:answers}
                                          :notes (str "expanded into a forward rule at assert"
                                                      " (member => condition) and evaluated at"
                                                      " query time as well."))
                                (str "special/materialize-defn-rules — expands to the forward rule (implies"
                                     " (Coll ?x) C), member => condition; also evaluated at query time by"
                                     " provers/DefnNecessaryNegationProver"))]
     ['defnSufficient (enforced (wff-only [:type :sentence] :facets #{:answers}
                                          :notes "the same, the other direction.")
                                (str "special/materialize-defn-rules — expands to the forward rule (implies"
                                     " C (Coll ?x)), condition => member; also evaluated at query time by"
                                     " provers/DefnSufficientProver"))]
     ['defnIff        (enforced (wff-only [:type :sentence] :facets #{:answers}
                                          :notes "both directions at once.")
                                (str "special/materialize-defn-rules — both directions, the necessary rule"
                                     " and the sufficient one"))]

     ;; ---- the query operators --------------------------------------------
     ['different   (operator {:args [] :variadic :term}
                             :notes (str "answered from the equality closure. Being"
                                         " deferred is all it shares with the"
                                         " comparisons: it is not transitive, so it"
                                         " merges no chains."))]
     ['unknown     (operator {:args [:sentence]})]
     ['thereExists (operator {:args [:sentence]})]
     ['forall      (operator {:args [:term :sentence]}
                             :notes "sugar for a nested unknown, desugared at the rule entry point.")]]

    (map (fn [f] [f (enforced (operator {:args [:term :term :sentence]})
                              "the aggregate prover")])
         '[agg/count agg/sum agg/min agg/max agg/avg])

    ;; ======================================================================
    ;; Everything below heads no entry in `special/entries`. It is the rest of
    ;; CxCore's grammar — the terms `vocabulary/roster` answers for and the
    ;; table does not.
    ;; ======================================================================

    ;; ---- the syntactic and denotation type roots -------------------------
    (map (fn [[t where]]
           [t (enforced (collection
                         :notes (str "read by name by checks/syntactic-roots — the kind"
                                     " quotedArg judges a value against."))
                        where)])
         '[[string "checks/syntactic-roots — the kind quotedArg judges a value against, matched by name"]
           [number "checks/syntactic-roots — the same, with integer below it"]
           [keyword "checks/syntactic-roots — the same"]
           [boolean "checks/syntactic-roots — the same"]
           [character "checks/syntactic-roots — the same; a one-letter string is not one"]
           [symbol "checks/syntactic-roots — the same; mention-only, so nothing places it in the domain lattice"]])
    [['integer (enforced (collection :facets #{:answers}
                                     :notes (str "both a syntactic root and the one *evaluable*"
                                                 " kind check: (integer 5) holds because 5 is one,"
                                                 " which is what lets the four sign-refined"
                                                 " collections be defined by defn conditions"
                                                 " resolved at query time."))
                         "checks/syntactic-roots — the same")]]
    (map (fn [[t where]]
           [t (enforced (collection
                         :notes (str "read by name by checks/value-kinds — a"
                                     " value of this sign satisfies an arg declaration"
                                     " naming it."))
                        where)])
         '[[positive_integer "checks/value-kinds — a positive integer value satisfies an arg declaration naming it"]
           [negative_integer "checks/value-kinds — a negative integer value satisfies an arg declaration naming it"]
           [non_negative_integer "checks/value-kinds — zero and positive integer values satisfy an arg declaration naming it"]
           [non_positive_integer "checks/value-kinds — zero and negative integer values satisfy an arg declaration naming it"]])

    ;; ---- the expression kinds --------------------------------------------
    ;; The shape lattice above the value kinds: what a sentence is BUILT OUT OF,
    ;; named as collections so a declaration can one day type an argument by the
    ;; shape of the expression written there.  Nothing reads them.  A compound
    ;; argument has no knowable kind — `checks/value-kind` answers nil for one by
    ;; design (docs/argtypes.md) — and no reader classifies a compound by its
    ;; shape, so `(quotedArg P n relation_application)` stores and convicts
    ;; nothing, and so does the `arg` form.  The vocabulary is one vocabulary and
    ;; the classifier that would give it enforcement does not exist.
    ;;
    ;; `atomic_formula` and `non_atomic_term` are declared disjoint under
    ;; `relation_application` and deliberately NOT declared covering: the KB has no
    ;; vocabulary for stating that a pair of specs exhausts their parent, so a
    ;; covering claim could only be made in prose and nothing would enforce it.
    (map (fn [[t why]] [t (inert (collection :notes why) why)])
         '[[relation_application "documentary: a relation applied to arguments, the shape atomic_formula and non_atomic_term share. No reader classifies a compound by its shape."]
           [denotational_term "documentary: the logic sense of term — an expression that denotes. Named so a declaration can say an argument is one; nothing reads it."]
           [atomic_formula "documentary: a predicate applied to terms. Nothing reads it."]
           [atomic_sentence "documentary: a closed atomic_formula — what a stored LiteralSentex holds. Nothing reads it."]
           [literal "documentary: an atomic_formula or its negation, which is what the LiteralSentex record holds. The record is machinery; this is the collection, and nothing reads it."]
           [formula "documentary: an atomic_formula, an operator applied to formulas, or a quantifier binding variables in one. Nothing reads it."]
           [sentence "documentary: a closed formula, which checks/check-ground is what actually enforces on the way in. The collection itself is read by nothing."]
           [non_atomic_term "documentary: a function applied to terms — the NAT of docs/nat.md, named as a collection. Reification reads the declaration on the function, never this."]])

    ;; ---- the hierarchy roots and the meta-level targets -------------------
    [['thing     (enforced (collection :notes "the hierarchy root the open-world floors test against by name.")
                           "checks — the hierarchy root the open-world floors test against by name")]
     ['predicate (enforced (collection :notes "the arg target CxCore constrains its own meta-level with.")
                           "generic: the arg target CxCore constrains its own meta-level with")]
     ['function  (enforced (collection :notes "the arg target the function-valued positions name.")
                           (str "generic: the arg target the function-valued positions of result,"
                                " genlResult and functionCorrespondingPredicate name"))]

     ;; ---- the predicate types --------------------------------------------
     ['unary_predicate   (enforced (collection :facets #{:convicts :reach}
                                               :notes (str "the membership spelling of an arity —"
                                                           " checks/predicate-type-arities — plus"
                                                           " disjointness with the other two, so a"
                                                           " predicate is at most one of the three."
                                                           " Reaches through settle's arity report,"
                                                           " not through the clash rosters."))
                                   (str "checks/predicate-type-arities — the membership spelling of an arity;"
                                        " plus its disjointness with the other two classes, so a predicate is at"
                                        " most one of the three"))]
     ['binary_predicate  (enforced (collection :facets #{:convicts :reach} :notes "the same, at two.")
                                   (str "checks/predicate-type-arities — the membership spelling of an arity;"
                                        " plus its disjointness with the other two classes, so a predicate is at"
                                        " most one of the three"))]
     ['ternary_predicate (enforced (collection :facets #{:convicts :reach} :notes "the same, at three.")
                                   (str "checks/predicate-type-arities — the membership spelling of an arity;"
                                        " plus its disjointness with the other two classes, so a predicate is at"
                                        " most one of the three"))]
     ['variable_arity    (enforced (collection
                                    :notes (str "the one *exemption* from the arity check — it"
                                                " un-convicts, which is why it carries no facet at"
                                                " all: every lane in this vocabulary names something"
                                                " a term causes, and none names something it"
                                                " prevents."))
                                   "checks/arity-problem — the one exemption from the arity check")]
     ['relation_kind     (enforced (collection :notes "a disjoint_metatype, so its two members separate each other.")
                                   "generic: a disjoint_metatype, so its two members separate each other")]
     ['instance_relation_predicate
      (enforced (assoc (collection :facets #{:convicts})
                       :stops-short
                       {:reach
                        (str "checks/declaration-problem refuses a genlArg on one at the entry point, and"
                             " nothing sweeps for a genlArg already stored when the membership"
                             " arrives. Unlike every other :convicts term what it convicts is a"
                             " *declaration* rather than a fact, so whether the two arrival orders"
                             " actually disagree is an open question, and what settles it is"
                             " running them.")})
                "checks/declaration-problem — an genlArg on one is refused")]
     ['type_relation_predicate
      (enforced (assoc (collection :facets #{:convicts})
                       :stops-short
                       {:reach "the same, refusing an arg instead, and open the same way."})
                "checks/declaration-problem — an arg on one is refused")]
     ['equivalence_relation
      (enforced (collection :notes (str "three CxCore rules derive (symmetric P), (transitive P)"
                                        " and (reflexive P) from it, each enforced in turn — so it"
                                        " is enforced by generic forward chaining and by nothing"
                                        " keyed on its name."))
                (str "generic forward chaining: the three CxCore rules derive (symmetric P),"
                     " (transitive P) and (reflexive P), each enforced in turn; also a"
                     " binary_predicate type"))]
     ['injection
      (enforced (collection :notes (str "three CxCore rules derive (functional P),"
                                        " (functionalInArg P 1) and, off the arg-declared"
                                        " domain and range, (predAllSpecified P D R) — the"
                                        " first two enforced in turn, the third audited on"
                                        " demand, and nothing keyed on its name."))
                (str "generic forward chaining: the three CxCore rules derive (functional P),"
                     " (functionalInArg P 1) and (predAllSpecified P D R); also a"
                     " binary_predicate type"))]
     ['surjection
      (enforced (collection :notes (str "three CxCore rules derive (functional P) and, off"
                                        " the arg-declared domain and range,"
                                        " (predAllSpecified P D R) and (predSpecifiedAll P D R)"
                                        " — the first enforced, the other two audited on"
                                        " demand, and nothing keyed on its name."))
                (str "generic forward chaining: the three CxCore rules derive (functional P),"
                     " (predAllSpecified P D R) and (predSpecifiedAll P D R); also a"
                     " binary_predicate type"))]
     ['bijection
      (enforced (collection :notes (str "two CxCore rules derive (injection P) and"
                                        " (surjection P) from it, and each of those derives"
                                        " its own marks in turn — so it is enforced by generic"
                                        " forward chaining and by nothing keyed on its name,"
                                        " like equivalence_relation."))
                (str "generic forward chaining: the two CxCore rules derive (injection P)"
                     " and (surjection P), whose own rules land the enforced and audited"
                     " marks; also a binary_predicate type"))]

     ;; ---- the connectives and rule wrappers -------------------------------
     ['implies (enforced (structural {:args [:sentence :sentence]}
                                     "canonicalized into the antecedent/consequent slots of a RuleSentex.")
                         "sentex canonicalization — becomes the antecedent/consequent slots of a RuleSentex")]
     ['and     (enforced (structural {:args [] :variadic :sentence}
                                     "the antecedent conjunction; never stored alone.")
                         "sentex canonicalization — the antecedent conjunction, never stored alone")]
     ['or      (enforced (structural {:args [] :variadic :sentence}
                                     (str "polycanonicalized — one rule per alternative, never"
                                          " stored; rules/disjunction-problems refuses every"
                                          " position it could not be expanded out of."))
                         (str "rules/expand-antecedent — polycanonicalization, one rule per"
                              " alternative; never stored, and rules/disjunction-problems refuses"
                              " every position it could not be expanded out of"))]
     ['not     (enforced (structural {:args [:sentence]}
                                     "canonicalized into the polarity slot, and the negation nogoods.")
                         "sentex canonicalization — the polarity slot, and the negation nogoods")]]
    (map (fn [[w where]]
           [w (enforced (structural {:args [:sentence]} "sets the rule's direction or strength.")
                        where)])
         '[[set/forwardRule  "sentex/peel-rule-wrapper — sets the rule's direction"]
           [set/backwardRule "sentex/peel-rule-wrapper — sets the rule's direction"]
           [set/defaultRule  "sentex/peel-rule-wrapper — sets the conferred strength"]
           [set/inertRule    "sentex/peel-rule-wrapper — stored, indexed for neither direction"]])

    ;; ---- the evaluable comparisons ---------------------------------------
    [['lessThan    (enforced {:shape   {:args [] :variadic :term}
                              :storage [:none] :checked false :family nil
                              :facets  #{:answers}
                              :notes   (str "variable arity: (lessThan 1 2 3) is indistinguishable from the chain."
                                            " Computed by a prover, and merged out of a rule body"
                                            " by the chain collapse — but assertible, unlike the"
                                            " query operators, so not :query-only.")}
                             "the comparison prover, plus the chain collapse in a rule body")]
     ['greaterThan (enforced {:shape   {:args [] :variadic :term}
                              :storage [:none] :checked false :family nil
                              :facets  #{:answers}
                              :notes   "canonicalizes to lessThan reversed when stored."}
                             "the comparison prover — canonicalizes to lessThan reversed")]
     ['evaluate    (enforced {:shape   {:args [:term :term]}
                              :storage [:none] :checked false :family nil
                              :facets  #{:answers}
                              :notes   "a whitelist over the arithmetic operators."}
                             "the evaluable prover — a whitelist over the arithmetic operators")]

     ;; ---- the reified-term vocabulary -------------------------------------
     ['termOfUnit (enforced {:shape {:args [:term :term]} :storage [:none] :checked false
                             :family nil :facets #{}
                             :notes "the constant-to-expression half of the reified-term map."}
                            "nat — the constant-to-expression half of the reified-term map")]
     ['result (enforced {:shape {:args [:function :type]} :storage [:none] :checked false
                         :family nil :facets #{}
                         :notes "materialized as a membership on each minted constant."}
                        "nat — materialized as a membership on each minted constant")]
     ['genlResult (enforced {:shape {:args [:function :type]} :storage [:none] :checked false
                             :family nil :facets #{}
                             :notes "materialized as a genl edge on each minted constant."}
                            "nat — materialized as a genl edge on each minted constant")]

     ;; ---- placement and projection -----------------------------------------
     ['ist (enforced {:shape {:args [:context :sentence]} :storage [:none] :checked false
                      :family nil :facets #{}
                      :notes "never stored: it names where the sentence goes, at the assert entry point."}
                     "assert and rule placement — never stored, it names where the sentence goes")]
     ['believes (enforced {:shape {:args [:term :sentence]} :storage [:none] :checked false
                           :family nil :facets #{:answers}
                           :notes (str "a plain binary predicate, assertible and stored like any"
                                       " relation — the projector augments the fact prover rather"
                                       " than replacing it. What makes it modal is the"
                                       " modal_predicate grant, not its name.")}
                          (str "BeliefProjectionProver — (believes a p) is answered by proving p in"
                               " a's CxAgent<a> context; also a plain binary_predicate, assertible and"
                               " stored like any relation, so the projector augments the fact prover"
                               " rather than replacing it"))]

     ;; ---- documentation ---------------------------------------------------
     ['comment (enforced {:shape {:args [:term :term]} :storage [:none] :checked false
                          :family nil :facets #{}
                          :notes (str "ordinary sentexes, queried like any fact — and the"
                                      " population of vocabulary/audit is read off them.")}
                         (str "gloss, core-context/comment-of, and the browser's term pages —"
                              " ordinary sentexes, queried like any fact"))]

     ;; ---- declared and read by nothing, on purpose -------------------------
     ['contradicts (inert (collection
                           :notes (str "a report form the engine *writes*. Nothing"
                                       " reads it as input, and asserting one would"
                                       " put a stale claim under truth maintenance."))
                          (str "a report form the engine *writes*: conflicts and contradictions"
                               " compose it per settle. Nothing reads it as input, and asserting one"
                               " would put a stale claim under truth maintenance."))]
     ['typeToInstancePred
      (inert (collection
              :notes (str "a link, not a rule. Moving a claim between the type and"
                          " instance levels needs a quantifier nothing here"
                          " supplies, so the pairing is recorded for a reader and"
                          " inferred from by nobody."))
             (str "a link, not a rule. Moving a claim between the type and instance"
                  " levels needs a quantifier reading nothing here fixes, so the pairing"
                  " is recorded for a reader and inferred from by nobody."))]

     ;; ---- curation vocabulary: documentation, read like comment ------------
     ;;
     ;; `comment`'s neighbours: prose a curator writes for a reader, stored and retracted
     ;; like any fact and read for inference by nothing.  Inert is the decision rather than
     ;; the omission — the grammar documents itself in its own representation, and a
     ;; cross-reference earns a stored sentex whether or not a check ever keys on it.
     ['termsRelated
      (inert {:shape {:args [] :variadic :term} :storage [:none] :checked false
              :family nil :facets #{}
              :notes (str "documentation the engine stores and never reads: a grouping for"
                          " a reader, drawing no inference, as comment's prose draws none.")}
             (str "a curation grouping of related vocabulary terms (variable arity), for a"
                  " reader. Nothing infers from it — the grouping is documentation, as"
                  " comment's prose is."))]
     ['seeAlso
      (inert {:shape {:args [:term :term]} :storage [:none] :checked false
              :family nil :facets #{}
              :notes (str "documentation the engine stores and never reads, and directional"
                          " on purpose: reading it symmetrically would be an inference, which"
                          " is the one thing this term does not do.")}
             (str "a documentation 'see also' cross-reference between two terms; read like"
                  " comment and by nobody for inference. Directional — (seeAlso a b)"
                  " does not imply (seeAlso b a); the reverse is a separate assertion."))]

     ;; The three worked-example annotations name their example sentex by handle.  Each is
     ;; a `target_following_predicate` in CxCore, so retracting the example tears the
     ;; annotation down with it — that mark's enforcement, reached through a declaration
     ;; rather than through an arm keyed on these functors, which is why they stay inert
     ;; while participating in a teardown.
     ['positiveExample
      (inert {:shape {:args [:term :term]} :storage [:none] :checked false
              :family nil :facets #{}
              :notes (str "belief-following through target_following_predicate, and an"
                          " integrity obligation — the named sentex is provable — held"
                          " by curation_test rather than by any engine path.")}
             (str "a curation meta-sentex naming, by handle, a sentex that is a true example"
                  " of a term's usage. Nothing reads the annotation for inference; its"
                  " integrity (the named sentex is provable) is held by curation_test."
                  " Belief-following via the target_following_predicate mark, so it does not"
                  " outlive the example it names."))]
     ['negativeExample
      (inert {:shape {:args [:term :term]} :storage [:none] :checked false
              :family nil :facets #{}
              :notes (str "the same teardown and the mirror obligation: the named sentex is"
                          " provable as its negation, which curation_test holds.")}
             (str "the same, for a sentex whose negation is provable — a false example of"
                  " a term's usage. Read by no check; its integrity is a test's, and it"
                  " cascades with its target like positiveExample."))]
     ['borderlineExample
      (inert {:shape {:args [:term :term]} :storage [:none] :checked false
              :family nil :facets #{}
              :notes (str "the same teardown, and no obligation at all: truth-agnostic by"
                          " design, so no regression reads its target.")}
             (str "the same pointing shape, truth-agnostic: it names a sentex neither"
                  " asserted true nor false, so it carries no provability obligation and no"
                  " regression reads its target. Documentation only."))]

     ;; ---- the predAll / predExists / predSpecified matrix ------------------
     ;;
     ;; Quantifier-family declarations (docs/predall.md).  The
     ;; *Instance* and *Exists* relations are each declared beside a CxCore **rule
     ;; generator** — a rule whose consequent is a rule — so their enforcement is generic
     ;; forward chaining, keyed on nothing; like `equivalence_relation`, no arm reads the
     ;; functor.  The *Specified* pair is an on-demand integrity audit reached through
     ;; `vaelii.core/specified-violations`.
     ['predAllInstance
      (enforced {:shape {:args [:predicate :type :term]} :storage [:none] :checked false
                 :family nil :facets #{}
                 :notes (str "enforced by the generic chain, not by name: the CxCore"
                             " generator beside the declaration stamps the concrete rule"
                             " when the holes ground.")}
                (str "generic rule generator (docs/generators.md): the CxCore generator"
                     " beside it stamps (implies (?indep ?x) (?pred ?x ?fixed)) — chain"
                     " inference concludes the fixed filler for every member"))]
     ['predInstanceAll
      (enforced {:shape {:args [:predicate :term :type]} :storage [:none] :checked false
                 :family nil :facets #{}
                 :notes "the argument-swapped twin of predAllInstance, same generic chain."}
                (str "generic rule generator: the CxCore generator stamps (implies (?dep ?y)"
                     " (?pred ?fixed ?y)), the argument-swapped twin"))]
     ['predAllExists
      (inert {:shape {:args [:predicate :type :type]} :storage [:none] :checked false
              :family nil :facets #{}
              :notes (str "the whole Exists class is inferentially inert by ruling —"
                          " a stored record plus a sanctioned per-cell placeholder"
                          " functor for authors, nothing derived.")}
             (str "an inert record: every ?indep member bears ?pred to some ?dep member,"
                  " stated and stored, inferred from by nothing. (PredAllExistsFn ?pred"
                  " ?indep ?dep) is the sanctioned placeholder an author may use for the"
                  " unnamed filler."))]
     ['predExistsAll
      (inert {:shape {:args [:predicate :type :type]} :storage [:none] :checked false
              :family nil :facets #{}
              :notes "the argument-swapped twin of predAllExists, inert like the class."}
             (str "an inert record, the argument-swapped twin: some ?dep member bears"
                  " ?pred to every ?indep member. (PredExistsAllFn ?pred ?dep ?indep) is"
                  " its sanctioned placeholder."))]
     ['predExistsInstance
      (inert {:shape {:args [:predicate :type :term]} :storage [:none] :checked false
              :family nil :facets #{}
              :notes (str "a pure existential — no universal to range over — expressible"
                          " precisely because the class stamps nothing.")}
             (str "an inert record: some ?indep member bears ?pred to the fixed filler."
                  " (PredExistsInstanceFn ?pred ?indep ?fixed) is its sanctioned"
                  " placeholder."))]
     ['predInstanceExists
      (inert {:shape {:args [:predicate :term :type]} :storage [:none] :checked false
              :family nil :facets #{}
              :notes "the argument-swapped twin of predExistsInstance."}
             (str "an inert record: the fixed subject bears ?pred to some ?dep member."
                  " (PredInstanceExistsFn ?pred ?fixed ?dep) is its sanctioned"
                  " placeholder."))]
     ['predAllSpecified
      (enforced {:shape {:args [:predicate :type]} :storage [:none] :checked false
                 :family nil :facets #{}
                 :notes (str "an on-demand audit, not a stored constraint: nothing fires on"
                             " assert, and the read is a function a caller invokes. Binary —"
                             " the required filler type is derived from ?pred's own slot-2"
                             " argument contract (arg → membership, genlArg → subtype),"
                             " never restated; no visible slot typing is a"
                             " declaration-contract gap the audit reports explicitly.")}
                (str "vaelii.core/specified-violations — the on-demand integrity"
                     " audit reads the declaration and returns the instances of ?indep with"
                     " no determinate filler; stamps no rule"))]
     ['predSpecifiedAll
      (enforced {:shape {:args [:predicate :type]} :storage [:none] :checked false
                 :family nil :facets #{}
                 :notes (str "the argument-swapped twin, auditing ?pred's first position;"
                             " binary, filler type derived from ?pred's slot-1 contract.")}
                (str "vaelii.core/specified-violations with :first — audits ?pred's"
                     " first position, the argument-swapped twin"))]
     ['PredAllExistsFn
      (enforced (collection :notes (str "a function constant, never a sentence functor; its"
                                        " unreifiable_function mark keeps a ground"
                                        " application a structural NAT. The engine never"
                                        " asserts it — uses are the author's."))
                (str "the predAllExists placeholder function; unreifiable_function keeps its"
                     " application a structural NAT — per-cell and full-arg, an ontological"
                     " marker rather than a skolem witness, and determinate for the"
                     " predAllSpecified audit when an author uses it"))]
     ['PredExistsAllFn
      (enforced (collection :notes "the predExistsAll twin of PredAllExistsFn.")
                (str "the predExistsAll placeholder function; unreifiable_function,"
                     " per-cell and full-arg, distinct from the other Exists cells'"
                     " placeholders"))]
     ['PredExistsInstanceFn
      (enforced (collection :notes "the predExistsInstance twin of PredAllExistsFn.")
                (str "the predExistsInstance placeholder function; unreifiable_function,"
                     " per-cell and full-arg, distinct from the other Exists cells'"
                     " placeholders"))]
     ['PredInstanceExistsFn
      (enforced (collection :notes "the predInstanceExists twin of PredAllExistsFn.")
                (str "the predInstanceExists placeholder function; unreifiable_function,"
                     " per-cell and full-arg, distinct from the other Exists cells'"
                     " placeholders"))]
     ['indeterminate_term
      (enforced (collection :notes (str "an extensible determinacy category: skolem is the"
                                        " built-in first member, a future kind joins by"
                                        " genl."))
                (str "one implementation behind both the predAllSpecified audit and the"
                     " different prover's identity exemption — a filler that is a member"
                     " is not determinate and is exempt from the unique-name assumption"))]])))

(defn- check-families
  "Refuse at load a declaration whose family or whose sweep is half-written, which is the
  whole reason a family is named at all.

  Two rules, and both are #54 stated as a load failure rather than as a review item.
  Every spelling of one family carries the **same** `:sweeps`: a family joined to the
  clash-exposure sweep in one spelling and not another convicts in one arrival order and
  not the other, in whichever lane the spelling was left out of, and neither lane says so.
  And a term that sweeps carries a `:shape`, because the lane that recognizes a
  declaration has to recognize it at the arity it is written in — the second half of #54,
  where the mark was enrolled for the reach and not for the trigger.

  Narrow on purpose.  The general implications between facets — `:sweeps` needing the
  `:reach` facet, a value being one of `sweep-kinds` — are the facet validator's, which is
  a commit of its own; this is the pair the repo has already paid for twice.  Returns
  `entries` unchanged so it can wrap a def, as `special/check-entries` does — and refuses
  under that validator's `:type`, `:bad-table-entry` discriminated by `:mismatch`, for the
  reason it gives itself two shapes under one word: whichever way the table is bad, the
  caller catching it is the namespace load, and there is nothing a keyword of its own
  would let that caller do."
  [entries]
  (doseq [[fam specs] (group-by (comp :family second) entries)
          :when       fam
          :let        [kinds (set (map (comp :sweeps second) specs))]]
    (when (< 1 (count kinds))
      (throw (ex-info (str "mark family " fam " does not agree about what its spellings"
                           " sweep: "
                           (pr-str (into (sorted-map) (map (fn [[t sp]] [t (:sweeps sp)])) specs))
                           " — a spelling left out of the sweep convicts in one arrival"
                           " order and not the other, which is #54")
                      {:type :bad-table-entry :mismatch :family
                       :family fam :sweeps kinds}))))
  (doseq [[term spec] entries
          :when       (:sweeps spec)]
    (when-not (:shape spec)
      (throw (ex-info (str term " sweeps " (:sweeps spec) " and declares no shape — the"
                           " lane that recognizes a declaration recognizes it at the arity"
                           " it is written in, and there is none to read")
                      {:type :bad-table-entry :mismatch :sweeps :functor term}))))
  entries)

(def ^:private lane-facets
  "The facets `facet-contract` marks as lanes a mark family moves through together."
  (into #{} (comp (filter (comp :lane? val)) (map key)) facet-contract))

(defn- family-lanes
  "Family -> the lane facets *some* spelling of it carries — what every other spelling
  is then held to, or has to record stopping short of."
  [entries]
  (reduce (fn [m [_ spec]]
            (if-let [fam (:family spec)]
              (update m fam (fnil into #{}) (filter lane-facets (:facets spec)))
              m))
          {} entries))

(defn- recheck-subject?
  "Does this entry answer goals **about a predicate** — the form a declaration has when
  it moves what a level-6 query says about a predicate other than itself?

  Argument 1, and only argument 1, exactly as `special/declaration-subjects` reads it: the
  subject of a declaration is written first throughout, and `inverse` names two only
  because either one's goals are answered from the other's facts.  A query operator answers
  goals of its own functor and moves nothing about a predicate, so it is not this."
  [spec]
  (and (contains? (:facets spec) :answers)
       (contains? #{:predicate :relation} (first (:args (:shape spec))))))

(defn- owed-facets
  "Facet -> `[rule reason]` for every facet this entry is committed to and does not carry
  — the three rules whose remedy is the same: carry it, or record stopping short of it."
  [term spec lanes recheck-subjects]
  (let [fs (:facets spec)]
    (cond-> (into {}
                  (for [f  (sort fs)
                        i  (sort (:implies (get facet-contract f)))
                        :when (not (contains? fs i))]
                    [i [:implication (str "the :" (name f) " facet implies it")]]))
      (:family spec)
      (into (for [l (sort (get lanes (:family spec))) :when (not (contains? fs l))]
              [l [:family-lane (str "another spelling of the " (:family spec)
                                    " family carries it, and a family joined to a lane in"
                                    " one spelling and not another fails silently in the"
                                    " other")]]))

      (and (recheck-subject? spec)
           (not (contains? fs :retriggers))
           (not (contains? recheck-subjects term)))
      (assoc :retriggers
             [:recheck (str "it answers goals about the predicate at argument 1, and posts"
                            " to the exception re-check queue neither through its own arms"
                            " nor through special/declaration-subjects — so the firings that"
                            " predate it keep a conclusion the firings after it drop")]))))

(defn check-facets
  "Refuse at load a declaration whose facets do not add up — the **cross-layer** half of
  `check-families`, and the one that turns wiring a new predicate into both lanes of a
  family from a review item into a build failure.

`above` carries what the layers above this one enumerate, because this namespace is the
  bottom one: a namespace holding both the declarations and the arms could only sit at the
  *top* of the stack, where `taxonomy` and `wff` could not read it.  So the facts that live
  above arrive as arguments, and the validator is **called** from `settle`'s namespace
  load, which is the first place every facet's arm is visible.  `check-families` stays at
  this namespace's load, where what it checks is one entry against another and nothing
  above is needed.

  * `:recheck-subjects` — the functors that post exception re-checks through the shared
    path (`special/declaration-subjects`) rather than from an arm of their own.
  * `:family-rosters` — `family -> {roster-name functors}`, the rosters that read a mark
    family **as a family**.  Each must enumerate exactly that family.

  Eight rules, eleven `:mismatch` values:

  * `facet-contract` and `facets` enumerate different keywords.  A facet with no row is
    one whose meaning its first user decided.
  * a field value outside its closed vocabulary — a facet, a storage kind, a family, a
    sweep kind, an argument kind.
  * `:cached` and a `:none` storage, or a storage and no `:cached`.  The two say the same
    thing and cannot disagree.
  * a `:sweeps` without the `:reach` facet.  What a declaration puts back in question is
    the reach; a kind without the facet says the sweep runs and nothing sweeps.
  * an `:arbitrable` term with no `:opposing-read` prose.  The third conjunct of
    arbitrability — that the read the conviction is made through does not depend on the
    belief the nogood moves — is not decidable from data, so the honest encoding is a
    required claim.  `arity` carries the same field with the negative answer, which is
    why it names a second sentex and is still not arbitrable.
  * an `:inert` term carrying another facet or a storage.  The `inert` constructor makes
    that unwritable; this is what says the constructor is still the only way in.
  * a roster that reads a family as a family and enumerates something else.  This is the
    `:enumeration` rule of `special/check-declarations` at the family level, and it is the
    one rule here with **no** `:stops-short` escape: where a facet is a claim that an
    entry can answer for in prose, a roster is a set sitting in another namespace, and two
    enumerations of one fact do not get to disagree.  `quotedArg` is why it exists — the
    entry point read it up `res/constraining-predicates` with its three siblings while
    `provers/meta-constraint-shape` had no row for it, so one declaration meant one thing
    to `assert` and another to `ask`.  The lane rule below caught that and offered a
    record; a record is the wrong answer to two rosters disagreeing.
  * a facet the entry is **committed to** and does not carry, by one of three rules —
    `:implication` (`facet-contract`), `:family-lane` (a sibling spelling carries it) or
    `:recheck` (it answers goals about a predicate and posts no re-check) — unless the
    entry records the exception in `:stops-short`.  The record is held to being *exactly*
    the owed set, in both directions, so it can neither be missing nor go stale.

  **What no rule can refuse** is a spelling dropped from its family outright: membership
  is a stated fact, as `:inert` is, and every rule above is about spellings that *are*
  enrolled agreeing with each other.  `predicates_test` pins `tax/functional-family-marks`
  as a literal for exactly that move.

  Rule 1 of the registry — `:cached` implies the whole integrate / disintegrate / rebuild
  triple — is **not** here.  It is `special/check-entries`, at the arm layer, where the
  arms are visible and a `special` load proves it on its own; duplicating it here would
  move the arm check to the top of the stack for nothing.

  O(declarations), no KB, no I/O, no reflection: `check-entries` is the budget.  Returns
  `entries` unchanged so it can wrap a def."
  [entries {:keys [recheck-subjects family-rosters]}]
  (let [refuse (fn [mismatch msg data]
                 (throw (ex-info msg (merge {:type :bad-table-entry :mismatch mismatch}
                                            data))))]
    (when-not (= (set (keys facet-contract)) facets)
      (refuse :contract
              (str "facet-contract and facets enumerate different keywords: "
                   (pr-str (vec (sort (remove facets (keys facet-contract)))))
                   " has a row and is no facet, "
                   (pr-str (vec (sort (remove (set (keys facet-contract)) facets))))
                   " is a facet with no row — a facet with no row is one whose meaning its"
                   " first user decided")
              {:contract (set (keys facet-contract)) :facets facets}))
    (doseq [[fam rosters] (sort-by key family-rosters)
            :let              [spellings (into #{} (comp (filter #(= fam (:family (second %))))
                                                         (map first))
                                               entries)]
            [roster functors] (sort-by key rosters)
            :when             (not= spellings functors)]
      (refuse :family-roster
              (str roster " reads the " fam " family as a family and enumerates "
                   (pr-str (vec (sort functors))) " where the declarations say "
                   (pr-str (vec (sort spellings)))
                   " — a spelling one of them holds and the other does not is one fact"
                   " written twice, and the half that is missing fails silently in"
                   " whichever lane that roster is")
              {:family fam :roster roster :roster-holds functors :declared spellings}))
    (let [lanes (family-lanes entries)]
      (doseq [[term spec] entries
              :let        [fs (:facets spec)
                           [skind] (:storage spec)
                           {:keys [args optional variadic]} (:shape spec)]]
        (doseq [[field bad] [[:facets (vec (sort (remove facets fs)))]
                             [:storage (vec (remove storage-kinds [skind]))]
                             [:family (vec (remove mark-families (keep identity [(:family spec)])))]
                             [:sweeps (vec (remove sweep-kinds (keep identity [(:sweeps spec)])))]
                             [:shape (vec (sort (remove argument-kinds
                                                        (concat args optional
                                                                (when variadic [variadic])))))]]
                :when       (seq bad)]
          (refuse :vocabulary
                  (str term "'s :" (name field) " holds " (pr-str bad)
                       ", which the closed vocabulary does not name — an open field is a"
                       " roster again, with the same drift and none of the checking")
                  {:functor term :field field :outside bad}))

        (when (not= (contains? fs :cached) (not= :none skind))
          (refuse :storage
                  (str term " is declared " (if (contains? fs :cached) "" "un") "cached and"
                       " names " (if (= :none skind) "no storage" (str "the storage " (pr-str (:storage spec))))
                       " — the facet and the storage kind say the same thing and cannot"
                       " disagree")
                  {:functor term :facets fs :storage (:storage spec)}))

        (when (and (:sweeps spec) (not (contains? fs :reach)))
          (refuse :sweep-reach
                  (str term " sweeps " (:sweeps spec) " and does not carry :reach — the"
                       " kind says where the reach goes and the facet says there is one,"
                       " so a kind without the facet claims a sweep that reaches nothing")
                  {:functor term :sweeps (:sweeps spec)}))

        (when (and (contains? fs :arbitrable) (not (:opposing-read spec)))
          (refuse :arbitrable
                  (str term " is arbitrable and does not say what its conviction's opposing"
                       " side is read through — a nogood whose read follows the belief it"
                       " moves destroys its own premise, which is not decidable from this"
                       " table and so has to be claimed on the entry")
                  {:functor term}))

        (when (contains? fs :inert)
          (when-not (and (= #{:inert} fs) (= :none skind) (:inert spec))
            (refuse :inert
                    (str term " is classified inert and carries " (pr-str (vec (sort fs)))
                         " with storage " (pr-str (:storage spec))
                         " — inert means nothing reads it, so it is written by the `inert`"
                         " constructor, which sets the facet with the prose and leaves no"
                         " room for a second opinion")
                    {:functor term :facets fs :storage (:storage spec)})))

        (let [owed     (owed-facets term spec lanes recheck-subjects)
              recorded (:stops-short spec)]
          (doseq [[f [rule reason]] (sort-by key owed)
                  :when             (not (contains? recorded f))]
            (refuse rule
                    (str term " owes the :" (name f) " facet — " reason
                         " — and neither carries it nor records stopping short of it in"
                         " :stops-short")
                    {:functor term :facet f}))
          (doseq [[f why] (sort-by key recorded)]
            (when-not (contains? owed f)
              (refuse :stops-short
                      (str term " records stopping short of :" (name f) " and is owed no"
                           " such facet" (if (contains? fs f)
                                           " — it carries it"
                                           " — no rule asks for it")
                           ", so the record has gone stale and says nothing")
                      {:functor term :facet f}))
            (when-not (and (string? why) (seq why))
              (refuse :stops-short
                      (str term "'s :stops-short entry for :" (name f) " carries no reason,"
                           " and an exception with no reason is a suppression")
                      {:functor term :facet f})))))))
  entries)

(def table
  "`entries` as the lookup map every reader below dispatches through — and where
  `check-families` runs, so a half-wired family fails at namespace load rather than in the
  one lane it was left out of."
  (into {} (check-families entries)))

;; ---- the readers ---------------------------------------------------------

(defn entry
  "The spec for `term`, or nil for one this grammar does not cover.

  Nil is **not** \"nothing reads it\": the population is CxCore's own vocabulary, so an
  ordinary domain predicate is simply not a term this question is asked about."
  [term]
  (get table term))

(defn shape-of
  "`term`'s sentence shape, or nil for a term never written as a sentence functor."
  [term]
  (:shape (entry term)))

(defn mark-shape
  "`:mark` for a one-place mark `(F P)`, `:mark-in-arg` for the two-place `(F P n)` — a
  term's written shape read as the distinction every lane that recognizes a mark at its
  own arity dispatches on.

  Derived from the declared argument list rather than stated, so a spelling cannot be
  recognized at an arity its own arguments contradict.  The marked predicate is argument 1
  of either, which is what lets a reader that only wants the predicate ignore the shape."
  [term]
  (if (= 1 (count (:args (shape-of term)))) :mark :mark-in-arg))

(defn by-facet
  "Every term carrying `facet`, as a set — what the lane rosters become."
  [facet]
  (into #{} (comp (filter #(contains? (:facets (second %)) facet)) (map first)) entries))

(defn sweeps
  "`term -> sweep kind` over every term that sweeps at all, in `entries` order — what
  `settle/clash-declaration-kinds` groups by kind and `clash-declaration-kind` reads
  back flat."
  []
  (into {} (keep (fn [[t spec]] (when-let [k (:sweeps spec)] [t k]))) entries))

(defn by-sweep
  "Every term whose arrival sweeps `kind`, as a set."
  [kind]
  (into #{} (comp (filter #(= kind (:sweeps (second %)))) (map first)) entries))

(defn family
  "Every spelling in family `fam`, as a set — the family read as the thing it is, which
  is what a reader that acts on all of them wants.  `by-family` adds the written shape,
  which only the functional family distinguishes."
  [fam]
  (into #{} (comp (filter #(= fam (:family (second %)))) (map first)) entries))

(defn by-family
  "Every spelling of the **functional** mark family `fam`, mapped to its written shape —
  `:mark` for the one-place `(F P)`, `:mark-in-arg` for the two-place `(F P n)`.

  The shape is *derived* from the argument list rather than stated, so a spelling cannot
  be enrolled in the family under a shape its own arguments contradict.  The marked
  predicate is argument 1 of either, which is what lets a reader that only wants the
  predicate ignore the shape entirely — and what a family whose spellings are written at
  three arities and five (`:argument-constraint`) has no use for, `family` being the
  reader for that one."
  [fam]
  (into {} (map (juxt identity mark-shape)) (family fam)))

(defn by-storage
  "Every term whose storage kind is `kind`, mapped to the table it lands in."
  [kind]
  (into {}
        (comp (filter #(= kind (first (:storage (second %)))))
              (map (fn [[term spec]] [term (second (:storage spec))])))
        entries))

(defn prop-marks
  "The `[term prop-keyword]` pairs of every term carrying `facet` and stored as a
  `tax/props` mark, in `entries` order — a facet read and a storage read at once, because
  the two spellings of a mark are what a caller comparing a *sentence's* functor against a
  *stored* key needs together.

  Case conversion is not an alternative to the pairing and never was: `anti_transitive`
  stores under `:anti-transitive`.  The declaration states the keyword; this reads it
  back."
  [facet]
  (into []
        (comp (filter (fn [[_ spec]] (and (contains? (:facets spec) facet)
                                          (= :prop (first (:storage spec))))))
              (map (fn [[term spec]] [term (second (:storage spec))])))
        entries))

(defn prop-kind
  "The `tax/props` keyword `term`'s mark maintains, or nil for a term that maintains
  none.  `special/prop-entry` reads its arms' kind through this rather than taking it
  as a parameter, which is what makes the set below a fact about the declarations."
  [term]
  (let [[kind target] (:storage (entry term))]
    (when (= :prop kind) target)))

(defn prop-kinds
  "The `tax/props` keywords the grammar declares, as a set — what `spec/::prop-kind`
  enumerates, read off the declarations that maintain them."
  []
  (into #{} (vals (by-storage :prop))))

(def cached
  "Every term `special/entries` gives the integrate / disintegrate / rebuild triple."
  (by-facet :cached))

(def derived
  "Every cached term whose triple runs on the derivation path as well."
  (by-facet :derived))

(def query-only
  "Every term refused at the assert entry point and answered by a prover instead."
  (by-facet :query-only))

(def checked
  "Every term `special/entries` gives a structural well-formedness arm."
  (into #{} (comp (filter (comp :checked second)) (map first)) entries))

(def in-special-table
  "The terms `special/entries` holds an entry for at all — the ones that are cached, or
  structurally checked, or both.  `check-entries` refuses anything else, so this is a
  definition and not an observation."
  (into checked cached))
