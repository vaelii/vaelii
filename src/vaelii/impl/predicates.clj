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
              entry without it is not a defect: the grammar terms CxCore does not
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
  `functional-family-marks`), `settle`'s trigger rosters, `spec/::prop-kind` and
  `vocabulary/roster` are field reads.

  **The validator runs a layer up.**  `check-facets` runs at `settle`'s load, because two
  of its rules read an arm that lives four layers up and a bottom namespace cannot see
  whether an arm exists — it takes those facts as arguments rather than requiring the
  layer that holds them.
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
  CapitalCamelCase and so is indistinguishable from an individual by spelling, and a relation may be denoted by a NAT
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
    :pred-commuting           ; a table keyed on [predicate group] — (F P n) / (F P p …)
    :roster                   ; a table keyed on [whole parts] — (F whole part part …)
    :none})                   ; nothing is cached; the declaration is read back per use

(def facet-contract
  "What carrying a facet commits the declaration to — the closed vocabulary's own
  contract, and what `check-facets` walks.  Keyed by facet, and **its keys are the
  vocabulary**: `facets` below reads them, so a row is what makes a facet exist and
  there is no second list to hold in step with this one.  Growing the vocabulary is
  therefore one edit that cannot leave the implication unwritten — a keyword with no
  row is not a facet whose meaning its first user decides, it is not a facet.

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
  {:cached     {:implies #{}                :lane? true}    ; special/entries gives it the integrate/disintegrate/rebuild triple
   :derived    {:implies #{:cached}         :lane? true}    ; …and that triple runs on the derivation path too (:derived?)
   :migrates   {:implies #{:cached}         :lane? true}    ; asserting it merges terms — kb/equality-predicates
   :arbitrable {:implies #{:convicts}       :lane? true}    ; its violation names other believed sentexes, so settle arbitrates it
   :reach      {:implies #{}                :lane? true}    ; arriving after the facts, it convicts what is stored
   :convicts   {:implies #{:reach}          :lane? true}    ; a definitional check reads it and can convict stored content
   :query-only {:implies #{:answers}        :lane? false}   ; never stored: the wff arm is the refusal, a prover is the answer
   :answers    {:implies #{}                :lane? true}    ; a prover answers goals of this functor
   :retriggers {:implies #{:answers}        :lane? false}   ; its arms post exception re-checks
   :inert      {:implies #{}                :lane? false}}) ; nothing reads it, and that is a decision — not an omission

(def facets
  "The lanes a term takes part in — `facet-contract`'s keys, and **closed** because that
  is where they come from: a facet exists exactly when a row states what carrying it
  commits the declaration to.

  Six of the ten are reconstructible from a live data structure and are pinned that way
  by `predicates_test`.  Four — `:answers`, `:retriggers`, `:convicts` and `:inert` —
  are *claims*: no roster in the tree states them, which is exactly why they are the
  ones that go wrong quietly."
  (set (keys facet-contract)))

(def mark-families
  "The families whose spellings must move together.  A family lives in more than one
  lane and has twice been joined to only one (#52, #54), so the family is named once and
  each spelling carries it.  `tax/functional-family-marks` and
  `tax/arg-declaration-props` are this field read back.

  **`:functional`** is acted on by the *merge* lane (`special`'s `equate-*` entry points, where
  two fillers of a functional slot are equated) and by the *candidate* lane
  (`decide`'s candidate index and `special/offer-marked-existing`, where two unmergeable
  fillers form a nogood the settle places).  Both lanes have to recognize the same spellings, and neither fails loudly
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
;; other, and the twenty-seven predicate marks `prop` builds differ in exactly one keyword.

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
  [kind & {:keys [facets arg derived? checked? notes]
           :or   {facets #{} arg :predicate derived? true checked? true}}]
  (cond-> {:shape   {:args [arg]}
           :storage [:prop kind]
           :checked checked?
           :facets  (cond-> (conj facets :cached) derived? (conj :derived))
           :family  nil}
    notes  (assoc :notes notes)))

(defn- mark
  "A one-term mark into a table of its own — `(F T)` — cached, but not a `tax/props`
  entry and so not a `spec/::prop-kind` keyword."
  [target & {:keys [facets arg notes] :or {facets #{} arg :type}}]
  (cond-> {:shape   {:args [arg]}
           :storage [:mark target]
           :checked true
           :facets  (conj facets :cached :derived)
           :family  nil}
    notes  (assoc :notes notes)))

(defn- pair
  "A two-argument declaration cached in a table keyed on the pair — `(F a b)`."
  [target arg-kind & {:keys [facets derived? notes]
                      :or   {facets #{} derived? true}}]
  (cond-> {:shape   {:args [arg-kind arg-kind]}
           :storage [:keyed-pair target]
           :checked true
           :facets  (cond-> (conj facets :cached) derived? (conj :derived))
           :family  nil}
    notes  (assoc :notes notes)))

(defn- roster
  "A whole-and-parts declaration — `(F whole part part …)` — cached in a table keyed on
  the whole and its sorted part roster together (`tax/cover-key`).

  Variable-arity, and the arity is content: two parts and three parts are two claims
  about one whole, so the roster is part of the key rather than something accumulated
  under the whole."
  [target & {:keys [facets notes opposing-read] :or {facets #{}}}]
  (cond-> {:shape   {:args [:type] :variadic :type}
           :storage [:roster target]
           :checked true
           :facets  (conj facets :cached :derived)
           :family  nil}
    opposing-read (assoc :opposing-read opposing-read)
    notes         (assoc :notes notes)))

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
  grammar terms it does not comment (the query operators other than `different`) pass
  through unchanged, and `vocabulary/audit` is what notices a
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

(def ^:private arity-note
  "The clause every exact-arity class's note ends with — nine classes say one thing, and
  a sentence written nine times is a sentence that drifts in eight of them."
  (str " — tax/exact-arity-classes — plus the disjointness that separates the"
       " relation-wide three, which the kind specializations inherit through their genl"
       " edges. Read as storage by the arity nogoods the settle places."))

;; ---- the entries ---------------------------------------------------------

(def entries
  "`[term spec]` pairs, ordered.  `special/entries`' fifty-nine functors first, in the table's
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
                                   :facets #{:reach :convicts :answers :retriggers})
                             :storage [:edge :genl])
                      "taxonomy/add-genl — the cached closure every membership, match and placement reads")]
     ['genlCx (enforced (assoc (pair :genlCx :context
                                     :facets #{:reach :convicts :answers :retriggers})
                               :storage [:edge :genlCx])
                        "taxonomy/add-genlCx — the visibility closure a context read walks")]

     ;; ---- the separations ------------------------------------------------
     ['disjoint (enforced (assoc (pair :disjoint :type :facets #{:reach :convicts :arbitrable})
                                 :opposing-read
                                 (str "the nogood pairs the two memberships, and the (disjoint A B)"
                                      " declaration the conviction is read through is not a member of"
                                      " it — so whichever membership is defeated, the disjointness"
                                      " table the next pass reads is the one that convicted."))
                          "taxonomy/add-disjoint, read by chain/place-memberships! and checks/disjoint-problems")]
     ['disjoint_metatype
      (enforced (mark :disjoint-metatype :facets #{:reach :convicts}
                      :notes (str "the members already asserted are recorded by the integrate arm"
                                  " as stored rather than believed — a belief-filtered sweep here"
                                  " would leave a defeated membership out of the cache keys"
                                  " permanently. No facet covers a retroactive record of"
                                  " supporters."))
                "taxonomy/mark-disjoint-metatype — the clique consulted, never stored")]
     ['sibling_disjoint (enforced (mark :sibling-disjoint :facets #{:reach :convicts})
                                  (str "taxonomy/mark-sibling-disjoint — the specialization clique keyed off"
                                       " the genl closure, consulted like disjoint_metatype"))]
     ['orthogonal
      (enforced (wff-only [:type :type]
                          :notes (str "convicted rather than convicting: the related-types family"
                                      " reads the stored declaration, or a stored"
                                      " siblingDisjointException through the predicate genl edge,"
                                      " back as a one-member nogood of itself whenever a genl"
                                      " edge or a separation a reader sees contradicts it."))
                (str "decide/related — a one-member nogood of the declaration over a pair a"
                     " reader reads genl-related or separated; and core/subsumption-statuses —"
                     " a stated pair reads :orthogonal with no shared instance"))]
     ['siblingDisjointException
      (enforced (assoc (pair :sib-exception :type)
                       :notes (str "its retract moves the separations a reader reads, which the"
                                   " membership candidates read again (membership/sync-memberships);"
                                   " that is a reach in the removal direction, which :reach (an"
                                   " arriving declaration) does not name. A genl of orthogonal,"
                                   " so the related-types family reads it as the orthogonal it"
                                   " entails."))
                (str "taxonomy/add-sib-exception — exempts one pair from the separation marks"
                     " (sibling_disjoint, disjoint_metatype, a partition or separating roster),"
                     " read at the reader in disjointness-test"))]

     ;; ---- exhaustion: the parts that cover a whole ------------------------
     ;;
     ;; :derived, like the separations above and for the same argument — a rule may
     ;; conclude a cover, and a `decontextualized_predicate` lift copies one into
     ;; CxUniverse, and neither may wait for a restart to reach the taxonomy.
     ;; `separating` and `partition` separate their parts from each other, and every one
     ;; of them installs a `genl` edge per part.
     ['covering
      (enforced (roster :cover :facets #{:reach :convicts :arbitrable}
                        :opposing-read
                        (str "the nogood holds the whole's membership and the negations,"
                             " and the declaration the conviction is read through is not a"
                             " member of it — disjoint's rule, for disjoint's reason: a"
                             " nogood defeating the cover would read a taxonomy without it"
                             " on the next pass, find no violation, and revive it.")
                        :notes (str "the coverage half is answered by provers/CoveringProver"
                                    " and convicts through settle's cover violation; the"
                                    " genl edge per part is installed by the integrate arm,"
                                    " against the covering sentex's own handle."))
                (str "taxonomy/add-cover — the part roster consulted, never stored as a"
                     " sentex per part, plus one taxonomy/add-genl per part"))]
     ['separating
      (enforced (roster :cover :facets #{:reach :convicts}
                        :notes (str "the separation half alone: the roster reaches"
                                    " disjointness-test and no coverage inference, so no"
                                    " nogood of its own and no :arbitrable facet. The genl"
                                    " edge per part is installed as covering's is."))
                (str "taxonomy/add-cover — the part roster read by disjointness-test, which"
                     " separates the parts the way it separates a disjoint metatype's"
                     " members, plus one taxonomy/add-genl per part"))]
     ['partition
      (enforced (roster :cover :facets #{:reach :convicts :arbitrable}
                        :opposing-read
                        (str "the nogood holds the whole's membership and the negations,"
                             " and the declaration the conviction is read through is not a"
                             " member of it — disjoint's rule, for disjoint's reason: a"
                             " nogood defeating the cover would read a taxonomy without it"
                             " on the next pass, find no violation, and revive it.")
                        :notes (str "covering's storage exactly, with the separating flag"
                                    " set: one key and one table, so the coverage half"
                                    " needs no second reader and no genl edge between the"
                                    " two spellings."))
                (str "taxonomy/add-cover — the same roster, read additionally by"
                     " disjointness-test, which separates the parts the way it separates"
                     " a disjoint metatype's members"))]

     ;; ---- the definitional marks -----------------------------------------
     ['transitive  (enforced (prop :transitive :facets #{:answers})
                             (str "taxonomy prop :transitive — the generic closure prover; also a"
                                  " binary_predicate type. (transitive genl) is stored but inert"
                                  " (closure-relations), so genl stays queryable without routing to the"
                                  " generic prover"))]
     ['symmetric   (enforced (prop :symmetric :facets #{:answers})
                             (str "taxonomy prop :symmetric — canonical argument order, so both spellings"
                                  " are one sentex; also a binary_predicate type"))]
     ['commutative (enforced (prop :commutative :facets #{:reach :answers}
                                   :notes (str "the all-arguments spelling, and a queryable"
                                               " classification. Its arm installs the"
                                               " commuting group [:rest 1] beside the prop,"
                                               " so the canonicalizer reads one table for"
                                               " all three spellings and no rule derives"
                                               " (commutativeInArgAndRest P 1) from it."
                                               " Its reach is that group's."))
                             (str "taxonomy prop :commutative, and the commuting group [:rest 1] its"
                                  " arm installs alongside; also a binary_predicate-free"
                                  " relation mark, since it holds at any arity"))]
     ['asymmetric  (enforced (assoc (prop :asymmetric :facets #{:reach :convicts :arbitrable
                                                                :answers})
                                    :opposing-read
                                    (str "the nogood pairs the tuple with its converse; the"
                                         " (asymmetric P) mark is not a member of it, so defeating"
                                         " either direction leaves the mark standing and the"
                                         " conviction re-derivable."))
                             "checks/asymmetry-problem — a nogood against the converse; also a binary_predicate type")]
     ['reflexive   (enforced (prop :reflexive :facets #{:answers})
                             "taxonomy prop :reflexive — the reflexive prover; also a binary_predicate type")]
     ['functional  (enforced (assoc (prop :functional :facets #{:reach :convicts :arbitrable})
                                    :family :functional
                                    :opposing-read
                                    (str "the nogood pairs the two fillers of the slot; the"
                                         " (functional P) mark is not a member of it, so defeating"
                                         " either filler leaves the mark standing.")
                                    :notes (str "acted on by two lanes that must recognize the"
                                                " same spellings and neither of which fails"
                                                " loudly: the *merge* entry point, where two fillers of"
                                                " a functional slot are equated, and the"
                                                " *candidate* offer, where two unmergeable"
                                                " fillers form a nogood the settle places. Deriving"
                                                " an equality is not"
                                                " :migrates — that facet is for a relation whose"
                                                " own assertion is the merge."))
                             (str "checks/functional-problems, and special/derive-functional-equalities"
                                  " on two symbols; also a binary_predicate type"))]
     ['irreflexive (enforced (prop :irreflexive :facets #{:reach :convicts}
                                   :notes (str "convicts a *self* tuple (P a a), a one-member nogood"
                                               " no settle weighs, so it is not :arbitrable:"
                                               " the settle places it"
                                               " from the candidate index, whichever of the mark"
                                               " and the tuple arrived first."))
                             (str "chain/place-tuples! — a stored self tuple under the mark is placed"
                                  " as a nogood; also a binary_predicate type"))]
     ['anti_symmetric (enforced (prop :anti-symmetric :facets #{:reach :convicts}
                                      :notes (str "derives (equals a b) from a believed converse of"
                                                  " two symbols rather than convicting either — so it"
                                                  " merges where the other pairwise marks separate,"
                                                  " and no facet names deriving. A converse no merge"
                                                  " can reconcile is a nogood the settle places,"
                                                  " irreflexive's reading, and not :arbitrable."))
                                (str "special/derive-antisymmetric-equalities merging two symbols a"
                                     " believed converse forces equal, and chain/place-tuples! placing a"
                                     " converse no merge reconciles; also a"
                                     " binary_predicate type"))]
     ['anti_transitive (enforced (assoc
                                  (prop :anti-transitive :facets #{:reach :convicts :arbitrable}
                                        :notes (str "the one nogood whose members are three rather"
                                                    " than two: it convicts the two-step chain and"
                                                    " the direct step together."))
                                  :opposing-read
                                  (str "the nogood is the triple — the two-step chain and the direct"
                                       " step — and the (anti_transitive P) mark is none of the three,"
                                       " so whichever step is defeated the mark still reads."))
                                 (str "taxonomy prop :anti-transitive — checks/antitransitivity-problems"
                                      " convicts the two-step chain and the direct step together, as the one"
                                      " nogood whose members are three rather than two (decide/verdict"
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
                        :notes   (str "binds a relation's length, read as storage beside the"
                                      " exact-arity classes: a tuple breaking it is a one-member"
                                      " nogood the settle places, and two related predicates"
                                      " whose bindings differ are a nogood of the bindings.  Not"
                                      " :arbitrable: no settle weighs it.")}
                       (str "chain/place-arities! — a stored tuple whose length breaks the binding"
                            " is placed as a nogood"))]
     ['arityMin
      (enforced {:shape {:args [:relation :integer]} :storage [:none] :checked false
                 :family nil :facets #{:reach :convicts}
                 :notes (str "floors a variable_arity relation: a shorter tuple is a one-member"
                             " nogood the settle places. Ordinary CxCore rules"
                             " also derive the at_least_*_relation classifications.")}
                "chain/place-arities! floors a variable-arity tuple at the minimum")]
     ['relationTypeByArity
      (enforced {:shape {:args [:type :integer]} :storage [:none] :checked false
                 :family nil :facets #{}
                 :notes "the relation-wide mappings are the premises of one CxCore generator that stamps, per mapping fact, the rule deriving a relation's exact arity from its type."}
                "one CxCore generator stamps the per-type exact-arity rules")]
     ['predicateTypeByArity
      (enforced {:shape {:args [:type :integer]} :storage [:none] :checked false
                 :family nil :facets #{}
                 :notes (str "a genl specialization of relationTypeByArity; a fact of"
                             " its own is a relationTypeByArity fact by ordinary CxCore"
                             " inference, and CxCore ships none — the shipped predicate"
                             " types reach the relation-wide mapping by genl instead.")}
                "genl specialization of relationTypeByArity")]
     ['functionTypeByArity
      (enforced {:shape {:args [:type :integer]} :storage [:none] :checked false
                 :family nil :facets #{}
                 :notes (str "a genl specialization of relationTypeByArity; a fact of"
                             " its own is a relationTypeByArity fact by ordinary CxCore"
                             " inference, and CxCore ships none — the shipped function"
                             " types reach the relation-wide mapping by genl instead.")}
                "genl specialization of relationTypeByArity")]
     ['admitsArgnum
      (enforced {:shape {:args [:relation :position]} :storage [:none] :checked false
                 :family nil :facets #{:answers}
                 :stops-short
                 {:retriggers
                  (str "answered fresh at query time by provers/AdmitsArgnumProver from the"
                       " relation's declared arity and variable-arity mark; it stores no"
                       " declaration and licenses no forward inference, so a query"
                       " re-evaluates against current belief and no firing predates it to"
                       " re-check.")}
                 :notes
                 (str "the position query: (admitsArgnum R n) holds when positive position n"
                      " exists in a well-formed application of R. Answered through"
                      " provers/admits-position?, the one decision checks/arg-position-problem"
                      " refuses against, so the query and the refusal cannot disagree.")}
                "provers/AdmitsArgnumProver — the position query over a relation's arity")]
     ['functionalInArg (enforced
                        {:shape   {:args [:predicate :position]}
                         :storage [:pred-position :functional-in-arg]
                         :checked true
                         :facets  #{:cached :derived :reach :convicts :arbitrable}
                         :family  :functional
                         :opposing-read
                         (str "the same as functional's, read at the declared position: the nogood"
                              " pairs the two fillers of [P n] and the (functionalInArg P n) mark is"
                              " not a member of it.")
                         :notes   (str "read UP the predicate hierarchy and refuses tuples,"
                                       " where transitiveInArg — the same name shape — is"
                                       " read for the goal's own predicate and licenses"
                                       " them. The two sit on opposite sides of the"
                                       " prover/checker divide.")}
                        (str "checks/functional-problems at the declared position, and"
                             " special/derive-functional-equalities on two symbols"))]
     ;; ---- the commutativity marks ----------------------------------------
     ;;
     ;; `symmetric` above commutes the two arguments of a binary predicate.  These two
     ;; state the same licence at any arity — a tail from a position, or a named set of
     ;; positions — and share the `:commuting` table, since the two written shapes reduce
     ;; to one runtime group descriptor (`sentex/commuting-components`).  `commutative`
     ;; is the third spelling and sits with the definitional marks above: it is a
     ;; one-place mark, and its arm installs the group `[:rest 1]` in this table beside
     ;; the `:commutative` prop it also maintains.
     ['commutativeInArgAndRest
      (enforced {:shape   {:args [:relation :position]}
                 :storage [:pred-commuting :commuting]
                 :checked true
                 :facets  #{:cached :derived :reach :answers}
                 :family  nil
                 :notes   (str "the canonical runtime spelling of commutativity: the assert entry point sorts the arguments inside the component it names, so every permitted permutation of a ground fact is one sentex and one handle. A canonicalization mark, not a conviction — it refuses nothing and licenses nothing, so it carries no sweep and reaches no clash roster.")}
                (str "sentex/sort-commuting-args at the assert entry point, and"
                     " integrate/commute-existing for the facts already stored"))]
     ['commutativeInArgs
      (enforced {:shape   {:args [:relation] :variadic :position}
                 :storage [:pred-commuting :commuting]
                 :checked true
                 :facets  #{:cached :derived :reach :answers}
                 :family  nil
                 :notes   (str "the named-set spelling of the same licence: exactly the"
                               " positions written interchange and every unnamed position"
                               " stays where it was. Two declarations that share a position"
                               " are one component rather than two permutations applied in"
                               " sequence — sentex/commuting-components says why.")}
                (str "sentex/sort-commuting-args at the assert entry point, and"
                     " integrate/commute-existing for the facts already stored"))]
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
     ['forced_monotonic_predicate (enforced (prop :forced-monotonic)
                                            (str "decide/verdict, which never takes a literal of the"
                                                 " predicate OUT, and the labeller's forced sets — a"
                                                 " denial held OUT and a firing concluding one from a"
                                                 " non-roster ground held void"))]
     ['forced_monotonic_between_predicates
      (enforced (prop :forced-between-predicates)
                (str "checks/forced-monotonic? — a literal of the predicate whose arguments are all"
                     " spelled as predicates is on the forced-monotonic roster"))]
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
               (get '{rewriteOf "nat for a compound right side, the equality partition for a symbol"
                      sameAs    "the equality partition — a merge of the two classes, answered from the closure by provers/EqualityProver"
                      equals    "the equality partition — a merge of the two classes, answered from the closure by provers/EqualityProver"}
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
     ['arg1      (enforced {:shape {:args [:relation :type]} :storage [:none] :checked false
                            :family nil :facets #{:convicts :reach}
                            :notes (str "the projection relates STORED declarations only — a"
                                        " reading arg generalizes up genl or inherits from a"
                                        " super-predicate has no arg1/arg2/arg3 twin; ask arg for those."
                                        " :family stays nil for arity's reason rather than for"
                                        " want of a family: mark-families rosters the lanes"
                                        " that must recognize one spelling set, and two"
                                        " spellings a rule cycle keeps believed under one check"
                                        " are not that. Exists so a positional constraint can"
                                        " be the subject of a binary declaration such as"
                                        " (predAllSpecified arg1 predicate).")}
                           (str "checks/declaration-problem — arg's own declaration arms at the"
                                " projected position, so both spellings of one declaration"
                                " refuse identically; the bridge rules derive each other, as"
                                " arity and the predicate-type memberships do"))]
     ['arg2      (enforced {:shape {:args [:relation :type]} :storage [:none] :checked false
                            :family nil :facets #{:convicts :reach}
                            :notes "the binary projection of (arg ?p 2 ?t) — see arg1."}
                           (str "checks/declaration-problem — the same at position 2; see"
                                " arg1"))]
     ['arg3      (enforced {:shape {:args [:relation :type]} :storage [:none] :checked false
                            :family nil :facets #{:convicts :reach}
                            :notes "the binary projection of (arg ?p 3 ?t) — see arg1."}
                           (str "checks/declaration-problem — the same at position 3; see"
                                " arg1"))]
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
                                  :notes (str "entail-existing reaches the facts stored before"
                                              " the declaration, and special/triggered-mints the"
                                              " trigger's type arriving after both, in the settle."
                                              " The only"
                                              " constraint whose trigger position is contravariant:"
                                              " a stored supertype answers a subtype query there,"
                                              " where every other type position reads up genl."))
                           "checks/inter-args-problem — the conditional form, same two paths")]

     ;; ---- the homogeneity constraints: interArg over a whole suffix ------
     ;; `interArgs` / `interArgAndRest` demand of every argument in a suffix a type one
     ;; argument there is known to hold.  Convict-and-answer only, like the covering
     ;; forms: each stops short of `:reach` because the family's reach mints and a
     ;; homogeneity constraint mints nothing, and short of `:retriggers` because it posts
     ;; no exception re-check.
     ['interArgs (enforced (assoc (prop :declares-inter-args-isa :arg :relation
                                        :facets #{:convicts :answers})
                                  :shape  {:args [:relation :type]}
                                  :family :argument-constraint
                                  :stops-short
                                  {:reach
                                   (str "the family's reach is special/entail-existing, which"
                                        " MINTS what a late declaration says about stored"
                                        " tuples, and a homogeneity constraint mints nothing:"
                                        " it convicts a mixed application, it does not draw a"
                                        " membership.  A conviction reach over the stored"
                                        " tuples a late interArgs rejects is a different"
                                        " mechanism from this facet's — the stop-short args"
                                        " records.")
                                   :retriggers
                                   (str "it answers goals about the predicate at argument 1 but"
                                        " licenses no inference that is a stored sentex reaching"
                                        " an exception, so it is absent from"
                                        " special/declaration-subjects and posts no re-check —"
                                        " the reason args records.")}
                                  :notes (str "the every-position form of interArgAndRest, and"
                                              " interArgAndRest at start 1: CxCore's two"
                                              " forward rules derive each spelling from the"
                                              " other, and the check reads both as one"
                                              " declaration.  Its type is trigger and target"
                                              " at once, so MetaConstraintProver answers it"
                                              " down the predicate hierarchy and at the"
                                              " stated type only."))
                           "checks/inter-args-homogeneity-problem — every position, one type")]
     ['interArgAndRest (enforced (assoc (prop :declares-inter-arg-and-rest-isa :arg :relation
                                              :facets #{:convicts :answers})
                                        :shape  {:args [:relation :position :type]}
                                        :family :argument-constraint
                                        :stops-short
                                        {:reach "the same as interArgs — see interArgs."
                                         :retriggers "the same as interArgs — see interArgs."}
                                        :notes (str "the suffix form: position and every later"
                                                    " one, the prefix below the start"
                                                    " unconstrained.  interArgs is"
                                                    " interArgAndRest at 1."))
                                 "checks/inter-args-homogeneity-problem — position n onward, one type")]

     ;; ---- the covering constraints: a whole tail typed at once ------------
     ;; `args` / `argsGenl` type every accepted position, `argAndRest` / `argAndRestGenl`
     ;; every position from a start onward — the generalizations of `arg` / `genlArg`
     ;; for a variable-arity tail.  Convict-and-answer only, like `quotedArg`: each stops
     ;; short of `:reach` because the family's reach mints and a covering constraint mints
     ;; nothing, and short of `:retriggers` because it posts no exception re-check.
     ['args (enforced (assoc (prop :declares-args-isa :arg :relation
                                   :facets #{:convicts :answers})
                             :shape  {:args [:relation :type]}
                             :family :argument-constraint
                             :stops-short
                             {:reach
                              (str "the family's reach is special/entail-existing, which"
                                   " MINTS what a late declaration now says about stored"
                                   " tuples, and a covering constraint mints nothing: it"
                                   " convicts a tail value, it does not draw a membership."
                                   " A conviction reach — refusing the stored tuples a late"
                                   " args now rejects — is an arity-shaped report and a"
                                   " different mechanism from this facet's, the same"
                                   " stop-short arityMin records.")
                              :retriggers
                              (str "it answers goals about the predicate at argument 1 but"
                                   " licenses no inference that is a stored sentex reaching"
                                   " an exception, so it is absent from"
                                   " special/declaration-subjects and posts no re-check —"
                                   " quotedArg's reason at the covering arity.")}
                             :notes (str "the every-position instance twin of arg: one"
                                         " declaration types the whole admitted tail, read"
                                         " through the shared declaration reader so a"
                                         " super-predicate's covering constraint binds a"
                                         " sub-predicate's tuples."))
                      "checks/covering-args-problem — every accepted position typed as an instance")]
     ['argsGenl (enforced (assoc (prop :declares-args-genl :arg :relation
                                       :facets #{:convicts :answers})
                                 :shape  {:args [:relation :type]}
                                 :family :argument-constraint
                                 :stops-short
                                 {:reach "the same one level up — see args."
                                  :retriggers "the same one level up — see args."}
                                 :notes "the every-position subtype twin of genlArg — see args.")
                          "checks/covering-genls-problem — every accepted position typed as a subtype")]
     ['argAndRest (enforced (assoc (prop :declares-arg-and-rest-isa :arg :relation
                                         :facets #{:convicts :answers})
                                   :shape  {:args [:relation :position :type]}
                                   :family :argument-constraint
                                   :stops-short
                                   {:reach "the same as args, a tail from a start — see args."
                                    :retriggers "the same as args — see args."}
                                   :notes (str "the tail-from-a-start instance form: position"
                                               " and every later one, the prefix below the"
                                               " start excluded.  args is argAndRest at 1."))
                            "checks/covering-args-problem — position n onward typed as an instance")]
     ['argAndRestGenl (enforced (assoc (prop :declares-arg-and-rest-genl :arg :relation
                                             :facets #{:convicts :answers})
                                       :shape  {:args [:relation :position :type]}
                                       :family :argument-constraint
                                       :stops-short
                                       {:reach "the same as argAndRest — see args."
                                        :retriggers "the same as argAndRest — see args."}
                                       :notes "the tail-from-a-start subtype form — see argAndRest.")
                                "checks/covering-genls-problem — position n onward typed as a subtype")]

     ;; ---- the argument-preserving declarations ---------------------------
     ['transitiveInArgInverse (enforced (wff-only [:relation :position :relation-name]
                                                  :facets #{:answers}
                                                  :notes "the reach against the relation's arrow.")
                                        "inherit — the argument reach against a declared transitive relation's arrow")]
     ['transitiveInArg        (enforced (wff-only [:relation :position :relation-name]
                                                  :facets #{:answers}
                                                  :notes "the same declaration, along the relation's arrow.")
                                        "inherit — the argument reach along a declared transitive relation's arrow")]

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

     ;; ---- a definitional collection relation over kinds -------------------
     ['intersection
      (enforced {:shape {:args [] :variadic :type} :storage [:none] :checked false
                 :family nil :facets #{}
                 :notes (str "a definitional collection relation: its facts drive CxCore"
                             " rules that make the combined kind genl each type it"
                             " intersects and conclude membership from the conjuncts.")}
                (str "ordinary CxCore rule inference — (intersection ?combined . ?types)"
                     " drives the intersection -> genl rules and a membership generator"
                     " (binary and ternary; general arity pends list-membership vocabulary)"))]

     ;; ---- the query operators --------------------------------------------
     ['different   (enforced (operator {:args [] :variadic :term}
                                       :notes (str "answered from the equality closure. Being"
                                                   " deferred is all it shares with the"
                                                   " comparisons: it is not transitive, so it"
                                                   " merges no chains."))
                             (str "provers/DifferentProver — a ground goal of two or more terms,"
                                  " answered from the equality closure under the unique-name"
                                  " assumption"))]
     ['unknown     (operator {:args [:sentence]})]
     ['thereExists (operator {:args [:sentence]})]
     ['forall      (operator {:args [:term :sentence]}
                             :notes "sugar for a nested unknown, desugared at the rule entry point.")]
     ['bravely     (operator {:args [:sentence]}
                             :notes (str "a read of the current dilemmas — S in some optimal"
                                         " labeling; answered by the :brave-cautious prover."))]
     ['cautiously  (operator {:args [:sentence]}
                             :notes (str "a read of the current dilemmas — S in every optimal"
                                         " labeling; answered by the :brave-cautious prover."))]]

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
         '[[expression "documentary: the root of the expression kinds and of the value kinds, below nowhere_never. CxCore holds it so CxCore and every spindle member read those kinds below thing; nothing reads it by name."]
           [unrepresented_term "documentary: the expression kind the value kinds sit under, disjoint from relation, formula, relation_application and context. The disjointness is read as any disjointness is; nothing reads the collection by name."]
           [relation_application "documentary: a relation applied to arguments, the shape atomic_formula and non_atomic_term share. No reader classifies a compound by its shape."]
           [denotational_term "documentary: the logic sense of term — an expression that denotes. Named so a declaration can say an argument is one; nothing reads it."]
           [atomic_formula "documentary: a predicate applied to terms. Nothing reads it."]
           [atomic_sentence "documentary: a closed atomic_formula — what a stored LiteralSentex holds. Nothing reads it."]
           [literal "documentary: an atomic_formula or its negation, which is what the LiteralSentex record holds. The record is machinery; this is the collection, and nothing reads it."]
           [formula "documentary: an atomic_formula, an operator applied to formulas, or a quantifier binding variables in one. Nothing reads it."]
           [sentence "documentary: a closed formula, which checks/check-ground is what actually enforces on the way in. The collection itself is read by nothing."]
           [non_atomic_term "documentary: a function applied to terms — the NAT of docs/nat.md, named as a collection. Reification reads the declaration on the function, never this."]])

    ;; ---- the upper-ontology skeleton -------------------------------------
    ;; The collections CxCore holds so that a spindle member can place its own types
    ;; under the root, or declare a position over a type a second member declares one
    ;; over.  A spindle's members see the head and not each other, so a skeleton
    ;; term defined in one member is invisible to the member extending it — which left
    ;; `animal` unable to reach `thing` from CxOrganism, where it is defined.
    ;;
    ;; They are here because CxCore comments them and `vocabulary/audit` answers for every
    ;; term CxCore comments, not because the engine reads any of them.  It reads none: no
    ;; check names one, and the kinds hanging off them are the members'.  `inert` is the
    ;; class, and the note is what a KB author asking `interpreted` is told.
    (map (fn [[t why]] [t (inert (collection :notes why) why)])
         '[[intangible "ontology, not grammar: something with no mass, the complement of tangible. CxCore holds it so every spindle member can extend it; no engine check names it."]
           [spatial "ontology, not grammar: something with a location in some space, physical or mathematical. CxCore holds it so every spindle member can extend it; no engine check names it."]
           [spatiotemporal "ontology, not grammar: something with a location in space and time. CxCore holds it so every spindle member can extend it; no engine check names it."]
           [tangible "ontology, not grammar: something with mass, and so with a location. CxCore holds it so every spindle member can extend it; no engine check names it."]
           [organism "ontology, not grammar: something alive in its own right. CxCore holds it so CxOrganism's kinds reach the root from CxOrganism; no engine check names it."]
           [biological "ontology, not grammar: a tangible that is an organism or part of one. CxCore holds it so organism reaches tangible through it from CxOrganism and body_part from CxAbstract; no engine check names it."]
           [measure "ontology, not grammar: what a QuantityFn or QuantityIntervalFn application denotes. CxCore holds it so CxMeasure and CxTime can both declare a position over it; no engine check names it."]])

    ;; ---- the space/time complements, nowhere_never, and the metatype ladder ----
    ;; CxCore comments these too, beside their genl edges, so `vocabulary/audit` answers
    ;; for them and they are classified inert like the skeleton above: ontology the engine
    ;; reads by no name.  `temporal` is `spatial`'s
    ;; time twin; `aspatial` / `atemporal` are the not-in-any-space / not-in-time collections
    ;; `nowhere_never` sits under; `uninterrupted` / `intermittent` partition `temporal` by
    ;; whether a thing has a gap in time; the ladder is the metatype-order theory that `typeGenl` reads,
    ;; and `typeGenl` is itself inert.
    (map (fn [[t why]] [t (inert (collection :notes why) why)])
         '[[temporal "ontology, not grammar: something that exists in time. CxCore holds it so CxTime and CxAbstract can extend it; no engine check names it."]
           [aspatial "ontology, not grammar: not located in any space, the complement of spatial. CxCore holds it so every spindle member can place a kind under it; no engine check names it."]
           [atemporal "ontology, not grammar: not located in time, the complement of temporal. CxCore holds it so nowhere_never can sit under it; no engine check names it."]
           [uninterrupted "ontology, not grammar: something temporal present at every moment between its start and its end, one side of the partition of temporal. CxCore holds it so every spindle member can place a kind under it; no engine check names it."]
           [intermittent "ontology, not grammar: something temporal with a gap between its start and its end, the other side of the partition of temporal. CxCore holds it so every spindle member can place a kind under it; no engine check names it."]
           [nowhere_never "ontology, not grammar: in no space and at no time, below aspatial and atemporal and the parent of expression; no engine check names it."]
           [type "ontology, not grammar: a first-order type, on the metatype-order ladder. No engine check names it — typeGenl, which reads the ladder, is inert."]
           [metatype "ontology, not grammar: a second-order type, on the metatype-order ladder. No engine check names it."]
           [meta_metatype "ontology, not grammar: a third-order type, on the metatype-order ladder. No engine check names it."]
           [at_least_metatype "ontology, not grammar: a type of order two or higher, on the metatype-order ladder. No engine check names it."]
           [fixed_order_type "ontology, not grammar: a type whose members are all of one order, on the metatype-order ladder. No engine check names it."]
           [variable_order_type "ontology, not grammar: a type holding members of any order, on the metatype-order ladder. No engine check names it."]
           [type_type_by_order "ontology, not grammar: the disjoint_metatype partitioning fixed_order_type by order. No engine check names it."]])

    ;; ---- the two halves of unary_predicate ---------------------------------
    ;; `empty` and `nonempty` partition `unary_predicate`.  The disjointness audit reads
    ;; both by name to decide whether a shared subtype witnesses an overlap.
    [['empty    (enforced (collection :notes "a unary predicate with no instance in the context the claim is stated in.")
                          "core/subsumption-reading — a shared subtype for which a facts-only read answers (empty c) is no overlap witness")]
     ['nonempty (enforced (collection :notes "a unary predicate with at least one instance in the context the claim is stated in.")
                          "core/subsumption-reading — a shared subtype for which a facts-only read answers (nonempty c) is the :shared-spec witness")]]

    ;; ---- the hierarchy roots and the meta-level targets -------------------
    [['thing     (enforced (collection :notes "the hierarchy root the open-world floors test against by name.")
                           "checks — the hierarchy root the open-world floors test against by name")]
     ['relation  (enforced (collection :notes "the common arg target for predicates and functions.")
                           (str "generic: the whole that function and truth_valued_relation partition,"
                                " and the arg target for relation-wide arity vocabulary"))]
     ['predicate (enforced (collection :notes "the arg target CxCore constrains its own meta-level with.")
                           "generic: the predicate specialization of relation")]
     ['function  (enforced (collection :notes "the arg target the function-valued positions name.")
                           (str "generic: the function specialization of relation and the arg"
                                " target the function-valued positions of result, genlResult"
                                " and functionCorrespondingPredicate name"))]
     ;; The other half of relation, and the three levels below it.  CxCore comments them
     ;; and `vocabulary/audit` answers for every term CxCore comments; no engine check names
     ;; any of the four.  The connectives are read by their own names (the `implies`, `and`,
     ;; `or` and `not` entries above), never through `logical_connective`.
     ['truth_valued_relation (inert (collection :notes "ontology, not grammar: a relation whose applications are true or false, the complement of function within relation. No engine check names it.")
                                    "ontology, not grammar: a relation whose applications are true or false, the complement of function within relation. No engine check names it.")]
     ['logical_constant      (inert (collection :notes "ontology, not grammar: a quantifier or a logical connective, the relations whose meaning the logic fixes. No engine check names it.")
                                    "ontology, not grammar: a quantifier or a logical connective, the relations whose meaning the logic fixes. No engine check names it.")]
     ['logical_connective    (inert (collection :notes "ontology, not grammar: a relation that builds a formula from formulas — and, or, not, implies. The connectives are read by their own names, never through this type.")
                                    "ontology, not grammar: a relation that builds a formula from formulas — and, or, not, implies. The connectives are read by their own names, never through this type.")]
     ['quantifier            (inert (collection :notes "ontology, not grammar: a relation that binds variables in a formula. No shipped term is one; the engine reads forall and thereExists by name.")
                                    "ontology, not grammar: a relation that binds variables in a formula. No shipped term is one; the engine reads forall and thereExists by name.")]

     ['unary   (enforced (collection :facets #{:convicts :reach}
                                     :notes (str "the relation-wide exact-one-argument type, and"
                                                 " the membership spelling of an arity"
                                                 arity-note))
                         "tax/exact-arity-classes — the relation-wide membership spelling of an arity")]
     ['binary  (enforced (collection :facets #{:convicts :reach}
                                     :notes (str "the same, at two" arity-note))
                         "tax/exact-arity-classes — the relation-wide membership spelling of an arity")]
     ['ternary (enforced (collection :facets #{:convicts :reach}
                                     :notes (str "the same, at three" arity-note))
                         "tax/exact-arity-classes — the relation-wide membership spelling of an arity")]

     ;; ---- the predicate types --------------------------------------------
     ['unary_predicate   (enforced (collection :facets #{:convicts :reach}
                                               :notes (str "a predicate's membership spelling of an"
                                                           " arity" arity-note))
                                   (str "tax/exact-arity-classes — a predicate's membership spelling of"
                                        " an arity"))]
     ['binary_predicate  (enforced (collection :facets #{:convicts :reach}
                                               :notes (str "the same, at two" arity-note))
                                   (str "tax/exact-arity-classes — a predicate's membership spelling of"
                                        " an arity"))]
     ['ternary_predicate (enforced (collection :facets #{:convicts :reach}
                                               :notes (str "the same, at three" arity-note))
                                   (str "tax/exact-arity-classes — a predicate's membership spelling of"
                                        " an arity"))]
     ['unary_function
      (enforced (collection :facets #{:convicts :reach}
                            :notes (str "the function specialization of unary, and a"
                                        " function's spelling of an arity" arity-note))
                "tax/exact-arity-classes — a function's membership spelling of an arity")]
     ['binary_function
      (enforced (collection :facets #{:convicts :reach}
                            :notes (str "the same, at two" arity-note))
                "tax/exact-arity-classes — a function's membership spelling of an arity")]
     ['ternary_function
      (enforced (collection :facets #{:convicts :reach}
                            :notes (str "the same, at three" arity-note))
                "tax/exact-arity-classes — a function's membership spelling of an arity")]
     ['fixed_arity       (enforced (collection
                                    :notes (str "classifies one exact argument policy; exact"
                                                " arity declarations and the unary/binary/ternary"
                                                " families specialize it."))
                                   "generic taxonomy classification and ordinary CxCore arity rule")]
     ['fixed_arity_predicate
      (enforced (collection :notes "the predicate specialization of fixed_arity.")
                "generic taxonomy classification under fixed_arity and predicate")]
     ['fixed_arity_function
      (enforced (collection :notes "the function specialization of fixed_arity.")
                "generic taxonomy classification under fixed_arity and function")]
     ['variable_arity    (enforced (collection
                                    :notes (str "the one *exemption* from the arity nogoods — it"
                                                " un-convicts, which is why it carries no facet at"
                                                " all: every lane in this vocabulary names something"
                                                " a term causes, and none names something it"
                                                " prevents."))
                                   "chain/place-arities! — the one exemption from the arity nogoods")]
     ['variable_arity_predicate
      (enforced (collection
                 :notes (str "the predicate specialization of variable_arity; the arity"
                             " nogoods read it as a variable_arity membership."))
                "chain/place-arities! — the variable_arity exemption, spelled for a predicate")]
     ['variable_arity_function
      (enforced (collection
                 :notes (str "the function specialization of variable_arity; it shares the"
                             " relation-wide taxonomy. No function WFF reader consumes it."))
                "generic taxonomy classification under variable_arity and function")]
     ['at_least_binary_relation
      (enforced (collection :notes "derived by a CxCore rule from arityMin greater than one.")
                "ordinary CxCore rule inference from arityMin")]
     ['at_least_ternary_relation
      (enforced (collection :notes "derived by a CxCore rule from arityMin greater than two.")
                "ordinary CxCore rule inference from arityMin")]
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
                                        " domain, (predAllSpecified P D) — the"
                                        " first two enforced in turn, the third audited on"
                                        " demand, and nothing keyed on its name."))
                (str "generic forward chaining: the three CxCore rules derive (functional P),"
                     " (functionalInArg P 1) and (predAllSpecified P D); also a"
                     " binary_predicate type"))]
     ['surjection
      (enforced (collection :notes (str "three CxCore rules derive (functional P) and, off"
                                        " the arg-declared domain and range,"
                                        " (predAllSpecified P D) and (predSpecifiedAll P R)"
                                        " — the first enforced, the other two audited on"
                                        " demand, and nothing keyed on its name."))
                (str "generic forward chaining: the three CxCore rules derive (functional P),"
                     " (predAllSpecified P D) and (predSpecifiedAll P R); also a"
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
           [set/inertRule    "sentex/peel-rule-wrapper — stored, indexed for neither direction"]
           [set/forwardOnlyRule "sentex/peel-rule-wrapper — sets the rule's direction"]
           [set/solveRule    "sentex/peel-rule-wrapper — adds :solve to the rule's engines"]
           [set/assumptionRule "sentex/peel-rule-wrapper — sets the rule's effect to :choose"]
           [set/hardConstraint "sentex/peel-rule-wrapper — sets the rule's effect to :forbid"]
           [set/softConstraint "sentex/peel-rule-wrapper — sets the rule's effect to :penalize"]
           [set/monotonic    "sentex/strength-wrapper — peeled at the entry point into :monotonic strength"]])

    ;; ---- the evaluable comparisons ---------------------------------------
    [['lessThan    (enforced {:shape   {:args [] :variadic :term}
                              :storage [:none] :checked false :family nil
                              :facets  #{:answers}
                              :notes   (str "variable arity: (lessThan 1 2 3) states the chain."
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
     ['matchesPattern (enforced {:shape   {:args [:term :term]}
                                 :storage [:none] :checked false :family nil
                                 :facets  #{:answers}
                                 :notes   (str "the string-shape check: (matchesPattern s pattern) holds when the"
                                               " whole of s matches the regex pattern, both ground strings."
                                               " Computed by the evaluable prover through a step-limited matcher.")}
                                "the evaluable prover — a step-limited whole-string regex match")]

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
                     "assert placement and read goals — never stored, it names where the sentence goes")]
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

     ;; ---- engine-derived meta-sentexes ---------------------------------------
     ['defeat (enforced {:shape {:args [:term]} :storage [:none] :checked false
                         :family nil :facets #{}
                         :notes (str "derived by the engine only: checks/check-no-defeat refuses it"
                                     " in every asserted literal.")}
                        (str "reads/as-stored-naming — the trie read by the handle each defeat"
                             " removes from belief"))]

     ['contradicts (enforced {:shape {:args [:term] :variadic :term} :storage [:none] :checked false
                              :family nil :facets #{}
                              :notes (str "derived by the engine for a placed nogood, one argument per"
                                          " member by handle; the reports compose the same functor"
                                          " over the member sentences.")}
                             (str "chain/place-nogood! — stored at the maximal common descendants of"
                                  " a nogood's members and grounds, justified by them"))]

     ;; ---- declared and read by nothing, on purpose -------------------------
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
     ['genlInverse
      (inert {:shape {:args [:term :term]} :storage [:none] :checked false
              :family nil :facets #{}
              :notes (str "inverse-genl between binary predicates — (genlInverse ?spec ?genl-inv)"
                          " means (?spec ?x ?y) entails (?genl-inv ?y ?x). Not yet engine-enforced;"
                          " aspirational ontology predicate from Lacuna proposals.")}
             (str "aspirational: records that one binary predicate specialises the"
                  " argument-reversed reading of another. No inference path."))]
     ['typeGenl
      (inert {:shape {:args [:term :term]} :storage [:none] :checked false
              :family nil :facets #{}
              :notes (str "higher-order genl: (typeGenl ?classifier ?genl) means every instance"
                          " of ?classifier genls to ?genl. Not yet engine-enforced; intended to"
                          " derive (genl ?x ?genl) from (?classifier ?x) once rule support lands.")}
             (str "aspirational: a higher-order genl constraint whose rule-based derivation"
                  " depends on engine support for higher-order patterns. No inference path."))]
     ['partitionedByType
      (inert {:shape {:args [] :variadic :term} :storage [:none] :checked false
              :family nil :facets #{}
              :notes (str "(partitionedByType ?whole ?classifier . ?cells) records that the"
                          " ?cells exhaustively and disjointly partition ?whole, each a"
                          " ?classifier instance. Inert: the disjointness rides a"
                          " disjoint_metatype and the memberships are stated beside it, so this"
                          " draws no inference and expands to nothing.")}
             (str "a partition declaration (variable arity) documenting that the cell types"
                  " exhaustively and disjointly cover the whole. Nothing infers from it — the"
                  " disjoint_metatype and the explicit memberships carry the separation."))]
     ['argN
      (inert {:shape {:args [:term :integer :sentence]} :storage [:none] :checked false
              :family nil :facets #{}
              :notes (str "a position inside a written formula, 0 the relation or operator."
                          " Nothing derives it, and its (quotedArg argN 3 formula) checks"
                          " nothing, since no reader classifies a compound by its shape.")}
             (str "a statement that a term is argument n of a written formula, position 0"
                  " being the relation or operator. Nothing derives or reads it, and no reader"
                  " classifies a compound by its shape yet."))]
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

     ;; A reviewer's record that a rule-macro suggestion was read and declined.  It names
     ;; the suggestion by content rather than the rule by handle, so a text export keeps it.
     ['declined_rule_macro
      (enforced {:shape {:args [:term]} :storage [:none] :checked false
                 :family nil :facets #{}
                 :notes (str "an ordinary fact over a quoted declaration, read by one pass of"
                             " the integrity sweep and by no inference.")}
                (str "integrity/rule-macro-findings — a rule-macro suggestion the rule's"
                     " context declines is not reported"))]

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
  "Refuse at load a declaration whose facets do not add up — the check that turns wiring a
  new predicate into both lanes of a family from a review item into a build failure.

`above` carries what the layers above this one enumerate, because this namespace is the
  bottom one: a namespace holding both the declarations and the arms could only sit at the
  *top* of the stack, where `taxonomy` and `wff` could not read it.  So the facts that live
  above arrive as arguments, and the validator is **called** from `settle`'s namespace
  load, which is the first place every facet's arm is visible.

  * `:recheck-subjects` — the functors that post exception re-checks through the shared
    path (`special/declaration-subjects`) rather than from an arm of their own.
  * `:family-rosters` — `family -> {roster-name functors}`, the rosters that read a mark
    family **as a family**.  Each must enumerate exactly that family.

  Six rules, nine `:mismatch` values:

  * a field value outside its closed vocabulary — a facet, a storage kind, a family, an
    argument kind.
  * `:cached` and a `:none` storage, or a storage and no `:cached`.  The two say the same
    thing and cannot disagree.
  * an `:arbitrable` term with no `:opposing-read` prose.  The third conjunct of
    arbitrability — that the read the conviction is made through does not depend on the
    belief the nogood moves — is not decidable from data, so the encoding is a
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
  "`entries` as the lookup map every reader below dispatches through."
  (into {} entries))

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
