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
  (:require [clojure.string :as str]
            [taoensso.nippy :as nippy]
            [vaelii.impl.budget :as budget]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.config :as config]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.argument :as argument :refer [*assertive-arg-types?*]]
            [vaelii.impl.decide.arity :as arity :refer [mintable-type?]]
            [vaelii.impl.decide.tuple :as tuple]
            [vaelii.impl.disk.durability :as dur]
            [vaelii.impl.except :as exc]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.io.thaw :as safe]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.predicates :as pr]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rewrite :as rewrite]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.wff :as wff]))

;; ---- invariants: naming + argument type declarations --------------------

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
  (`unary_predicate`, `instance_relation_predicate`, …), separates those types with
  `disjoint_metatype`, and constrains predicate-valued argument positions with
  `arg` — so restricting the checks to CapitalCamelCase individuals would leave
  the whole meta-level declared and unenforced.  Numbers, strings and compounds are
  excluded because a type membership cannot be asserted of one (a NAT reifies to its
  constant first, so a reified term is checked under that constant)."
  [x]
  (and (symbol? x) (not (sx/variable? x))))

(def ^:private syntactic-roots
  "The syntactic types a value is classified into — the roots of the kind lattice
  `quotedArg` types against.  A `quotedArg` whose declared type is neither one of these
  nor below one is out of the feature's domain (an imported constraint typing an argument
  as some domain collection), and the check reads it open-world rather than convicting.

  One per leaf kind a sentence can carry, and complete on purpose: a kind with no root
  here is one both argument checks have to wave through, which is a hole rather than a
  policy.  A compound is the exception `value-kind` states."
  '#{string number integer symbol keyword boolean character})

(defn- value-kind
  "The syntactic type of an argument taken as a **term** — its EDN kind, mapped to the
  type the argument checks compare it against: a string is `string`, an integer `integer`
  (a `number` below), any other number `number`, a keyword `keyword`, a boolean
  `boolean`, a character `character`, a non-variable symbol `symbol` (a name, however its
  role spells it).

  `nil` for the two things that are not a leaf with a knowable kind — a **variable**,
  which is not a term yet, and a **compound**, whose kind is not the question: what
  `(QuantityFn 5 Meter)` denotes is its function's business, so no syntactic answer would
  be the right one and both checks read it open-world.

  The syntactic half is the whole of what this declines to answer, and the semantic half
  is answered beside it: `result` / `genlResult` say what an application denotes, and
  `convicting-result-type` reads them.  A **reifiable** application reaches neither — it
  is minted before the checks run and arrives as the constant its result types were
  materialized on, checked like any symbol — so a compound seen here is one that is never
  minted, and its function's declaration is the only thing the KB can know about it.

  A literal value's kind is `provers/literal-value-kind`'s, the table `EvaluableProver`
  answers a value-kind membership from, so the argument checks and the prover read one
  classification.  A symbol is the one kind added here."
  [x]
  (or (provers/literal-value-kind x)
      (when (and (symbol? x) (not (sx/variable? x))) 'symbol)))

(defn- value-kinds
  "The most specific built-in types known from a value.

  Most values have only their EDN kind. Integers additionally carry the sign-refined
  types declared in core.txt. Zero belongs to both non-negative and non-positive; returning
  a set rather than forcing one artificial leaf keeps both argument constraints exact.

  **Read by both argument readings, which is why it is not named for either.**  `arg`
  types what an argument denotes and `quotedArg` the term written there, and for a
  *value* those coincide — a value denotes itself, which is the whole reason the EDN
  kinds sit in the `genl` lattice at all (core.txt, and `vocabulary.clj`'s note on the
  value kinds).  A sign is as decidable from `5` written in a position as from what
  `5` denotes, so a reading that admitted `integer` and refused `positive_integer` would
  not be more conservative, only wrong in one direction: `args-quoted-problem` read
  `value-kind` alone and so convicted **every** integer of failing
  `(quotedArg P n positive_integer)`, the declared type being *below* the kind rather
  than above it (#55).  One reader, both entry points."
  [x]
  (if (integer? x)
    (cond
      (pos? x) '#{positive_integer non_negative_integer}
      (neg? x) '#{negative_integer non_positive_integer}
      :else    '#{non_negative_integer non_positive_integer})
    (if-some [t (value-kind x)] #{t} #{})))

(def ^:dynamic *pass-reads*
  "A volatile map bound by a pass that decides many convictions (`refresh-argument-holds!`,
  `held-argument-entries`), holding what the pass reads once: each predicate's
  declarations per context (`literal-reader`), the declaring super-predicates' memos
  (`declaration-reader`), the reads no value enters (`value-outside?`), the reads
  `clash-possible?` makes over every context, and the candidate tests and reads every
  declaration shares (`held-demand-test`, `declaration-candidates`).  The pass
  gathers every candidate before it writes a hold.  Nil reads them afresh and asks no
  `clash-possible?`."
  nil)

(defn- pass-read
  "The value `*pass-reads*` holds at `k`, computed by `f` on a miss, or `(f)` when no pass
  is bound."
  [k f]
  (if-let [m *pass-reads*]
    (let [v (get @m k ::miss)]
      (if (= ::miss v) (let [v (f)] (vswap! m assoc k v) v) v))
    (f)))

(defn- value-outside?
  "Is the value or symbol `arg`, of kinds `ks` (`value-kinds`), provably outside the type
  `t` as seen from `context`?  False when a kind is at or below `t`.  Otherwise the
  `:monotonic` definitions decide a literal value first (`provers/value-definition`): a
  sufficient condition true on it admits it, and a necessary condition false on it
  convicts it.  With neither, true when `t` lies below no syntactic root the value's kind
  is under, or when the taxonomy separates `t` from one of the kinds.  A `t` below the value's own root and separated from none of its
  kinds refines the kind (`(genl ip_address string)`, a subtype of `integer`), so the
  value may be a `t` and nothing convicts it.  Under a pass (`*pass-reads*`), each read
  no value enters is held per kind, type and context."
  [kb tax arg ks t context]
  (let [k (value-kind arg)]
    (and (not (pass-read [::kinds-at ks t context] #(boolean (some (fn [kt] (tax/genl? tax kt t context)) ks))))
         (case (provers/value-definition kb arg t context
                                         #(pass-read [::value-frame t context]
                                                     (fn [] (provers/value-definition-frame kb t context))))
           :member  false
           :outside true
           (pass-read [::kinds-outside k ks t context]
                      #(or (not-any? (fn [r] (and (tax/genl? tax k r context) (tax/genl? tax t r context)))
                                     syntactic-roots)
                           (boolean (some (tax/disjointness-test tax t context) ks))))))))

(defn- syntactic-type?
  "Is `t` a type `quotedArg` can judge a value against — a syntactic root or a subtype
  of one, or a kind of `expression` (reflection.txt), which every value kind and
  `symbol` sit below?  `(quotedArg except 1 sentex_handle_term)` so refuses `(except
  212)`, an integer being no `sentex_handle_term`, and `denotational_term` admits a
  symbol or a value.  A declared type outside this lattice leaves the constraint
  open-world."
  [tax t context]
  (or (contains? syntactic-roots t)
      (some #(tax/genl? tax t % context) syntactic-roots)
      (tax/genl? tax t 'expression context)))

(def ^:private declaration-queries
  "Per declaration kind, the sentence `declaration-reader` queries: the functor, then the
  argument tail that follows the predicate being asked about.  A table rather than a cond
  chain, because the kinds differ in *arity* as well as in functor — `interArg` names
  two positions and two types — and a chain would put that difference in the caller."
  '{arg      (arg ?n ?type)
    genlArg     (genlArg ?n ?type)
    quotedArg   (quotedArg ?n ?type)
    interArg (interArg ?n ?type ?m ?utype)
    argArg   (argArg ?n ?m)
    interArgEqual (interArgEqual ?n ?value ?m ?type)
    argsGenl        (argsGenl ?type)
    argAndRest      (argAndRest ?start ?type)
    argAndRestGenl  (argAndRestGenl ?start ?type)
    quotedArgAndRest (quotedArgAndRest ?start ?type)
    interArgs       (interArgs ?type)
    interArgAndRest (interArgAndRest ?start ?type)})

(def ^:private sugar-spellings
  "The argument-constraint spellings the entry point never queries, each with the
  declaration its core.txt forward rule stores in its place: `(args P T)` stores
  `(argAndRest P 1 T)`, and every instance-level read here is of `arg` and `argAndRest`.
  The stored twin carries its own handle, justified by the sugar, so a refusal or an
  entailment names the twin and retracting the sugar takes both with it.  A KB that does
  not load core.txt has no such rule, and its sugar types nothing at the entry point."
  '{args argAndRest})

(def constraint-declaration-functors
  "The argument constraints this namespace answers for at the entry point, as a set —
  `declaration-queries`' keys, which it queries, and the `sugar-spellings` it reads
  through the declaration their forward rules store.

  Public because it is one of the tables that reads the `:argument-constraint` family
  **as a family**, and `predicates/check-facets` holds those to enumerating exactly it.
  A spelling in the family and not here is one the entry point cannot query for and so never
  convicts; a spelling here and not in the family is one nothing declares."
  (into (set (keys declaration-queries)) (keys sugar-spellings)))

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
  super-predicate the closure happened to enumerate first.

  **Two arities.**  `(decls kind)` is the read above.  `(decls ::stored? functor)` is the
  O(1) presence check the conditional arms stand behind — is any `functor` sentex stored
  at all (`kind-stored?`) — memoized in `counts`, which a reader for a *nested*
  application shares with the reader of the sentence it sits in (`(decls ::counts nil)`),
  so one check pays each presence check once however many applications it reads."
  ([kb pred context] (declaration-reader kb pred context (volatile! {})))
  ([kb pred context counts]
   (let [cache (volatile! {})]
     (fn
       ([kind]
        (if-some [ds (get @cache kind)]
          ds
          (let [[f & tail] (declaration-queries kind)
                ds         (cond
                             (not (symbol? pred)) nil
                             ;; written of a function, a `resultArg` binds the
                             ;; `natFormula` facts naming its applications
                             ;; (`result-arg-rows`)
                             (= 'resultArg kind)
                             (when (and (= 'natFormula pred)
                                        (pos? (reads/stored-count-with-functor (:index kb) 'resultArg)))
                               (into [] (res/matches-visible kb '(resultArg ?f ?n) context)))
                             :else
                             (into []
                                   (mapcat #(res/matches-visible kb (list* f % tail) context))
                                   (res/constraining-predicates
                                    kb kind pred context
                                    (when *pass-reads* (pass-read ::declaring-memos #(volatile! {}))))))]
            (vswap! cache assoc kind ds)
            ds)))
       ([op functor]
        (case op
          ::counts  counts
          ::stored? (if-some [b (get @counts functor)]
                      b
                      (let [b (pos? (reads/stored-count-with-functor (:index kb) functor))]
                        (vswap! counts assoc functor b)
                        b))))))))

(defn- kind-stored?
  "Is any `functor` sentex stored — the O(1) presence check, asked through `decls` so a
  check pays it once (`declaration-reader`)."
  [decls functor]
  (decls ::stored? functor))

(defn- arg-at
  "The argument sitting at one-based `position` of the argument vector `as`, or nil when
  the position is not one the sentence has.  The bounds test the argument constraints all
  need before they can say anything about a position a declaration names."
  [as position]
  (when (and (integer? position) (<= 1 position (count as)))
    (nth as (dec position))))

(defn- arg-arg-rows
  "The `(argArg pred n m)` declarations `decls` reads, as `arg` rows over the argument
  vector `as` of one sentence: `[handle {?n n ?type t ?m m} sentex]`, `t` being the
  sentence's argument `m`.  The shape `(decls 'arg)` yields, so the conviction, the
  entailment and the late sweep read an `argArg` exactly as the `arg` it amounts to for
  that sentence, and its support is the `argArg` declaration.  A position the sentence
  lacks, or a non-symbol there, names no type and yields no row.  Read like `arg`, with no
  functor-count check: `(decls 'argArg)` reads only the predicates the taxonomy marks as
  declaring one (`res/constraining-predicates`), which costs no index read on a predicate
  no `argArg` names."
  [decls as]
  (for [[h b sx] (decls 'argArg)
        :let  [m (get b '?m)
               t (arg-at as m)]
        :when (and (symbol? t) (not (sx/variable? t)))]
    [h {'?n (get b '?n) '?type t '?m m} sx]))

(defn- inter-arg-equal-rows
  "The `(interArgEqual pred n v m U)` declarations `decls` reads, as `arg` rows over the
  argument vector `as` of one sentence: `[handle {?n m ?type U ?trigger n ?value v}
  sentex]` for each declaration whose argument `n` is `v`, compared by `=`.  The shape
  `(decls 'arg)` yields, so the conviction, the entailment and the late sweep read the
  declaration as the `arg` it amounts to for that sentence, and its support is the
  `interArgEqual` declaration.  A sentence whose argument `n` is another term, or that has
  no argument `n`, yields no row.  `(decls 'interArgEqual)` reads only the predicates the
  taxonomy marks as declaring one, as `(decls 'arg)` does.  See docs/argtypes.md."
  [decls as]
  (for [[h b sx] (decls 'interArgEqual)
        :let  [n (get b '?n)
               v (get b '?value)]
        :when (= v (arg-at as n))]
    [h {'?n (get b '?m) '?type (get b '?type) '?trigger n '?value v} sx]))

(defn- result-arg-rows
  "The `(resultArg F n)` declarations `decls` reads, as `arg` rows over the `natFormula`
  fact `sentence`, `(natFormula K E)` with `E` an application of `F`: `[handle {?n 1
  ?type t} sentex]`, `t` being `E`'s argument `n`, so the rows type the constant `K` as an
  `arg` at position 1 types it.  A position `E` lacks, or a non-symbol there, names no
  type and yields no row."
  [decls sentence]
  (let [e (nth sentence 2 nil)]
    (when (and (= 'natFormula (nm/functor sentence)) (sequential? e) (symbol? (first e)))
      (let [as (vec (rest e))]
        (for [[h b sx] (decls 'resultArg)
              :when (= (first e) (get b '?f))
              :let  [t (arg-at as (get b '?n))]
              :when (and (symbol? t) (not (sx/variable? t)))]
          [h {'?n 1 '?type t} sx])))))

(defn- arg-rows
  "Every `arg` row binding one sentence with argument vector `as`: the `arg`
  declarations, then the `argArg` ones read over `as` (`arg-arg-rows`), then the
  `interArgEqual` ones it triggers (`inter-arg-equal-rows`)."
  [decls as]
  (-> (vec (decls 'arg))
      (into (arg-arg-rows decls as))
      (into (inter-arg-equal-rows decls as))))

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

  Public and spelled once: `arg-position-problem` words a declaration naming a position
  the length denies with it, and a caller describing a binding reads the same clause.
  \"is declared with\" is false of a predicate that declared nothing and took its length
  off a super, so the split is a claim about the KB rather than a phrasing."
  [pred via n]
  (str (if (= via pred) "is declared with " "takes ")
       n " argument" (when (not= 1 n) "s")
       (when-not (= via pred) (str " through " via))))

(defn- in-content-order
  "Declaration matches sorted by the stored declaration's own sentence — the order
  every first-violation walk reads them in.

  `res/matches-visible` promises the answer *set*: `res/*hierarchical-retrieval*` says
  nothing about order, so a `(first (for …))` over the raw matches would let the
  retrieval strategy pick *which* declaration a refusal names when several convict.
  Sorting on content keys the choice on what the KB says rather than on enumeration —
  the rule `handle-namings` states for the handle a clash is reported as.  Existence is
  untouched: every declaration is still read, and a sentence no declaration convicts
  still has no violation.

  The key is built once per match and compared as a string (`nm/sort-by-content-key`
  with `compare`) — the same lexicographic order, off the per-comparison rebuild — and a
  run of one, the common case for a `(first (for …))` consumer, sorts nothing.  Printed
  through `nm/print-key`, so no ambient `*print-length*` collapses two declarations to
  one prefix: these sentences are *short*, which exposes them rather than protecting them
  — at `*print-length*` 3, `(arg parentOf 1 person)` and `(arg parentOf 1 animal)` print
  the same."
  [ds]
  (nm/sort-by-content-key #(nm/print-key (:sentence (nth % 2))) compare ds))

;; ---- what both readings of an argument declaration need ------------------
;; The two conditions an entailment is drawn under, beside the toggle
;; (`argument/*assertive-arg-types?*`, below `provers`, which reads it).  They sit above
;; the constraint arms rather than beside the entailment arms below because
;; `args-problem` reads them too: under the toggle its symbol arm yields to the
;; entailment, and what it yields to is exactly these conditions.

(def ^:dynamic *refuse-clashes?*
  "Does the write entry point refuse an arbitrable clash as well?  False by default, where
  `refuses-assert?` decides.  `vaelii.core/try-assert` binds it true, and
  `constraint-checks` then refuses every violation the sentence or one of its
  argument-type mints forms (docs/api.md, \"Refusing a clash\")."
  false)

(defn- convicts-symbols?
  "Are a symbol argument's memberships read against its declared type?  Under the
  constraint-only reading, and under `*refuse-clashes?*`.  Under the entailing reading
  `assert` stores the sentence whatever the symbol holds and the settle weighs the
  derived membership, so the read is skipped there."
  []
  (or (not *assertive-arg-types?*) *refuse-clashes?*))

(def ^:dynamic *entry-mints?*
  "Is the sentence being checked one the entry point will reify before storing it?

  True while `vaelii.core/check` reads a fact the way `assert` would store it, and while
  the forward chainer asks whether a conclusion naming an application with no constant
  yet is admissible before it mints one (`chain/reify-conclusion`).  `assert` mints
  every ground application of a reifiable function to a constant before its checks run,
  so an argument that is such an application is read there as that constant; neither
  of the two callers has minted it yet, and under this binding the argument arm reads
  the application as the constant would be read (`minted-application-clash`).  False
  everywhere else, where every reifiable application has already been replaced by its
  constant."
  false)

(defn visibility-support
  "The `genlCx` edge supporters along one visible path from `context` to the context the
  sentex stored at `dh` is written in, or empty when it is written in `context`.  A
  derivation drawn in `context` from a declaration or a fact it inherits rests on that path
  as it rests on the `genl` edges `edge-support` names, so retracting an edge on the path
  takes the derivation back and a surviving route draws it again
  (`special/rederive-descended`)."
  [kb dh context]
  (let [dc (:context (p/get-sentex (:records kb) dh))]
    (if (or (nil? dc) (= dc context))
      []
      (mapv first (tax/reach-support (reasoning/taxonomy kb) :genlCx context dc context)))))

(defn- trigger-supports
  "One support per believed membership `(T' x)` that makes `x` a `t` from `context`: the
  membership's handle, the `genl` edges from `T'` to `t` (`tax/reach-support`), and the
  `genlCx` edges `context` sees the membership through (`visibility-support`).  In content
  order; empty when no membership reaches `t`.  A derivation an `interArg` or a
  homogeneity declaration draws from a trigger names one of these, so retracting the
  membership or an edge on its route takes the derivation back."
  [kb x t context]
  (let [tax (reasoning/taxonomy kb)]
    (into []
          (keep (fn [m]
                  (let [t' (nm/functor (:sentence m))]
                    (when (tax/genl? tax t' t context)
                      (into [(:id m)]
                            (concat (mapv first (tax/reach-support tax :genl t' t context))
                                    (visibility-support kb (:id m) context)))))))
          (sort-by (juxt #(nm/name-key (nm/functor (:sentence %))) #(nm/name-key (:context %)))
                   (res/type-memberships kb x context)))))

(defn- separated-type
  "The content-least type the symbol `x` believes, visible from `context`, that the
  taxonomy separates from `t`, or nil.  The test is `tax/separation-test`, the one
  `disjoint-problems` asks of a membership, so an argument conflict is the clash the
  membership `(t x)` would form.  A type the taxonomy does not separate from `t` leaves
  `x` possibly a `t`, so an argument whose types miss `t` and are not separated from it
  convicts nothing."
  [tax types x t context]
  (when-let [dj? (and (symbol? t) (tax/separation-test tax t context))]
    (nm/min-by-content-key identity (filterv dj? (:types (types x))))))

(defn- outside-declared-type?
  "Does `arg` fail the `(arg P n t)` demand, as seen from `context`?  The separated type
  for a symbol, true for a value provably outside `t` (`value-outside?`), else nil.

  Two readings, because the KB knows two different amounts about the two kinds of term.

  A **symbol** is typed by what somebody asserted, so the reading is open-world: it
  violates the demand only when it believes a type the taxonomy separates from `t`
  (`separated-type`).  A **value** is typed by what it *is* — `value-kind` reads its EDN kind, and
  those kinds sit in the `genl` lattice (core.txt) exactly so this comparison can be made.
  No assertion is involved and none is possible, so there is nothing to be open-world
  about: a string is a `string` and a `string` is not a `dog`, and saying so is the
  difference between a declaration that constrains a position and one that constrains
  the half of it somebody happened to spell with a name.  A `t` that refines the value's
  kind (`(genl ip_address string)`) is the exception: the kind does not decide membership
  of `t`, so the value is convicted only where `t` is separated from one of its kinds.

  The openness moves rather than disappearing, and it moves to the **declared type**: a
  `t` outside the hierarchy is one the lattice cannot place the kind against, which is
  the imported-constraint case `args-quoted-problem` exempts for the same reason.

  A **compound** is neither of the two readings and is not answered here.  It holds no
  membership and its kind is not the question; what it denotes is its function's business,
  and `convicting-result-type` beside this is the arm that reads the function.  What it
  is *given* is a separate question, `nested-input-problem`'s."
  [kb tax types arg t context]
  (if (checkable-term? arg)
    (when (convicts-symbols?) (separated-type tax types arg t context))
    (let [ks (value-kinds arg)]
      (when (seq ks)
        (and (symbol? t)
             (tax/genl? tax t 'thing context)
             (value-outside? kb tax arg ks t context))))))

(defn- application-term?
  "Is `x` a function **application** — a compound whose head is a name?

  The one argument shape neither `checkable-term?` nor `value-kind` answers for: a type
  membership cannot be asserted of it, and its EDN kind is not the question its declared
  position asks.  A **vector** fails the head test rather than being excluded by name — a
  vector in a sentence is a list of forms (an `exceptWhen`'s conjuncts, a `thereExists`'s
  binders), so its first element is a form and not a function."
  [x]
  (and (sequential? x)
       (symbol? (first x))
       (not (sx/variable? (first x)))))

(defn- convicting-result-type
  "The declared result type that convicts the application `x` of failing a demand for
  type `t`, seen from `context`, or nil.  `declared` is the reader for the demand's
  reading — `nat/result-types` for `arg`'s instance demand, `nat/genl-result-types`
  for `genlArg`'s subtype one — and the two are never crossed: `arg` asks what the
  application *is*, `genlArg` what it is a *kind of*, and one declaration answers each.

  **A result declaration is a claim about the function, not about the application.**
  `(result QuantityFn measure)` says every `(QuantityFn m u)` denotes a measure; no
  application is typed on its own, and nothing here computes a per-application type —
  there is nothing to compute, a structural application holding no membership and being
  able to hold none.  A **reified** application does not arrive here at all: it is minted
  before the checks run, and its constant carries these very declarations materialized as
  `(T K)` / `(genl K T)`, which the symbol arm reads.  So this is the reading for the
  applications that are never minted, and it and the mint say the same thing about the
  same function.

  **Open-world, one level out from the symbol reading.**  A head that declares no result
  exempts every application of it, exactly as an unclassified symbol exempts itself.  Only
  a head with a declared result the taxonomy separates from `t`, and none reaching `t`,
  convicts — `separated-type`'s test, with the head's declarations standing where a
  term's memberships stand.

  Content-least where a head declares several, so which of them a refusal names is keyed
  on what the KB says rather than on the order a retrieval enumerated them.

  **A quoting predicate's argument is a mention and is left alone.** `(natFormula K
  (FruitFn AppleTree))` and a compound-argument `(rewriteOf T E)` carry the NAT
  expression as a verbatim payload rather than as a term used in that position
  (`res/nat-quoting-predicates`, docs/nat.md), so typing it by what the function yields
  would type a quotation by its referent.  It is also the one place a mint would pay for
  this: `mint-nat!` writes a `natFormula` per constant, and that write is where a KB
  declaring result types would otherwise buy a scoped retrieval it can never be convicted
  by.  A quoting function's argument (`sx/quoting-functors`) is the same mention one level
  in, reached when `nested-input-problem` reads the quoting function's own declarations.

  Behind `nat/any-result-declarations?` — two O(1) functor counts, reached only for a
  compound sitting at a position some declaration constrains, so a KB that has written no
  result declaration pays nothing for this and one that has pays two integer reads."
  [kb declared pred x t context]
  (when (and (symbol? t) (application-term? x)
             (not (contains? res/nat-quoting-predicates pred))
             (nat/any-result-declarations? kb))
    (let [tax (reasoning/taxonomy kb)
          rs  (vec (declared kb x context))]
      (when (and (not (sx/quoting-functor? pred))
                 (not-any? #(tax/genl? tax % t context) rs))
        (nm/min-by-content-key identity (filterv (tax/disjointness-test tax t context) rs))))))

(defn- entailment-covers?
  "Does the entailing reading answer for the argument `arg` of an argument constraint?

  Under `*assertive-arg-types?*` an argument constraint derives the membership it names
  over a symbol argument (`constraint-entailments`), from a declaration written in the
  asking context or inherited by it.  A symbol believing a type separated from the
  declared one is then a clash between that derived membership and the held one, so its
  conviction is marked `:weighed?`: `assert` stores the sentence and the settle weighs the
  derived membership (docs/argtypes.md), and `try-assert` refuses it (`refuses-assert?`).

  Only the symbol arm is weighed.  A **value** carries its type in its syntax and an
  **application** is typed by its function's `result`; no membership can be derived of
  either, so for both the constraint reading is the only one there is."
  [arg]
  (and *assertive-arg-types?* (checkable-term? arg)))

(defn- minted-application-clash
  "How `assert` reads the argument `x`, a ground application of a reifiable function,
  where the `arg` declaration `d` demands `t` of it: nil when the reading below does not
  apply, `::admitted` when `assert` admits the argument, or the result type the demand
  clashes with.  Asked only under `*entry-mints?*`, the binding `check` reads a sentence
  under.

  `assert` mints such an application before the checks run, and the constant it mints
  holds the function's result types as memberships.  Under `*assertive-arg-types?*`, and
  where the declared type is one the hierarchy holds, the symbol arm then yields: the entailment mints `(t K)` and refuses it
  only where it clashes with a membership the constant holds (`entailment-check`).
  `check` does not mint, so it reads the application here, with the result types standing
  where the constant's memberships would: a result type that reaches `t` admits the
  argument, one the taxonomy separates from `t` is the clash, and any other admits it,
  since the entailment would mint `t` there.  The consequences of minting `(t K)` past that
  one membership are not read.  A quoting predicate's or quoting function's argument is a
  mention, which `convicting-result-type` leaves alone for the same reason, so nil."
  [kb tax pred x t context]
  (when (and *entry-mints?*
             *assertive-arg-types?*
             (not (contains? res/nat-quoting-predicates pred))
             (not (sx/quoting-functor? pred))
             (nat-read/reifiable-ground-nat? kb x)
             (mintable-type? kb t))
    (let [rs (vec (nat/result-types kb x))]
      (if (some #(tax/genl? tax % t context) rs)
        ::admitted
        (let [dj? (tax/disjointness-test tax t context)]
          (or (nm/min-by-content-key identity (filterv dj? rs))
              ::admitted))))))

(defn- arg-type-violation
  "The `:arg-type` violation of `arg` at position `n` under a demand for `t`, its message
  ending in `clause`.  `out` is `outside-declared-type?`'s answer: a separated type names
  the held type in `:disjoint-with`, and under the entailing reading marks the conviction
  `:weighed?` (`entailment-covers?`)."
  [sentence arg t n out clause]
  (cond-> {:type :arg-type :sentence sentence :arg arg :expected t :position n
           ;; `pr-str`, so a convicted string reads as one — it prints the same as `str`
           ;; for every term that could already be convicted here
           :message (str "arg constraint: " (pr-str arg) " must be a " t
                         (when (symbol? out) (str " — " arg " is a " out ", disjoint from " t))
                         clause)}
    (symbol? out)             (assoc :disjoint-with out)
    (and (symbol? out) (entailment-covers? arg)) (assoc :weighed? true)))

(defn- first-refusing
  "The first violation of `vs` that is not `:weighed?`, else the first one: a weighed
  conviction that `assert` stores does not hide a later one that it refuses."
  [vs]
  (or (first (remove :weighed? vs)) (first vs)))

(defn- args-problem
  "First (arg pred n type) violation for a sentence, or nil, a `:weighed?` one only when
  no other convicts (`first-refusing`).  Uses genl transitivity; only constraints and
  type memberships visible from `context` count.  A **symbol** is convicted only by a
  type it believes that the taxonomy separates from the declared one.  A **value**
  carries its type in its syntax and is checked against it — `outside-declared-type?`
  has that argument.

  **Genl transitivity in two places, not one.**  The constraint *type* is reached
  through the closure, and so is the constrained *predicate*: `decls` reads every
  declaration on `pred` and on the super-predicates `context` can see
  (`res/constraining-predicates`), because a `genl` edge between predicates says the
  sub-predicate's tuples are the super's, and a tuple set only narrows going down.  So
  `(arg parentOf 1 person)` refuses `(fatherOf TheRock1 Mary)` as surely as it
  refuses the same claim spelled `parentOf` — which it has to, since the stored
  sub-predicate fact answers every super-predicate query through the matcher's fan.

  **An application is typed by its function's `result`**, which is the one thing the
  KB can know about a term no membership can be asserted of: `(result QuantityFn
  measure)` refuses `(needs_dog (QuantityFn 5 Meter))` under `(arg needs_dog 1 dog)` and
  admits it under `(arg needsMeasure 1 measure)`.  `convicting-result-type` has that
  argument, the open-world floor included.  The application's own inputs are not read
  here: they answer to its function's declarations, and `application-input-problem` runs
  this arm again one level in, with the function where `pred` stands.

  **Under `*assertive-arg-types?*` the symbol arm is weighed** (`entailment-covers?`):
  the declaration mints the type, and the conviction is the clash that mint forms with
  the separated membership, which `assert` stores and the settle weighs.  `entailment-check`
  walks the rest of the cascade before anything is stored.  Under `*entry-mints?*`, the binding `check`
  reads under, a ground application of a reifiable function is read the way `assert`
  reads the constant it mints (`minted-application-clash`), so a clash with its result
  type is `:disjoint` in `check` as it is in `assert`.

  `types` is the shared per-assert membership reader (`kb/membership-reader`), `decls`
  the shared declaration reader.  The two questions asked of each constrained
  argument — is it in the hierarchy at all, and does it reach the constraint type —
  are one retrieval and two set lookups, and a second constraint on the same position
  adds no retrieval at all."
  [kb sentence context types decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (reasoning/taxonomy kb)]
    (when (symbol? pred)
      (first-refusing
       (for [m     (in-content-order (arg-rows decls as))
             :let  [b     (nth m 1)
                    n     (get b '?n)
                    t     (get b '?type)
                    arg   (arg-at as n)
                    ;; a reifiable application, read as the constant `assert` mints
                    clash (when arg (minted-application-clash kb tax pred arg t context))
                    ;; the application arm — nil for every argument that is not one
                    r     (when-not clash
                            (convicting-result-type kb nat/result-types pred arg t context))
                    out   (when (and arg (not clash) (not r))
                            (outside-declared-type? kb tax types arg t context))]
             :when (and arg (not= ::admitted clash) (or clash r out))]
         (if clash
           (let [minted (list t arg)]
             {:type :disjoint :sentence minted :types [t clash] :entailed-from sentence
              :message (str "arg constraint: " (pr-str sentence) " entails " (pr-str minted)
                            ", which cannot be admitted — disjointness violated: "
                            (pr-str arg) " cannot be both " t " and " clash)})
           (arg-type-violation sentence arg t n out
                               (str (when r (str " — " (first arg) " results in a " r))
                                    " (arg " n " of " pred
                                    (when-let [tp (get b '?m)] (str ", the type its arg " tp " names"))
                                    (when-let [tp (get b '?trigger)]
                                      (str ", because arg " tp " is " (pr-str (get b '?value))))
                                    (via-clause (declared-of m) pred) ")"))))))))

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
  * The target side is convicted exactly as `args-problem` convicts a symbol: argument
    `m` must believe a type the taxonomy separates from `U` (`separated-type`).

  Both sides are context-scoped by construction — `decls` reads only the declarations
  visible from `context` and `types` only the memberships — so a context is convicted
  on evidence it can see, which is the judgement `genls-problem` spells out at length.
  It descends the predicate hierarchy for `args-problem`'s reason and by riding the
  same reader: a conditional constraint on `parentOf` is a claim about every tuple of
  every predicate beneath it.

  **Behind an O(1) presence check, unlike its two unconditional neighbours.**  `args-problem` and
  `genls-problem` run their declaration read unconditionally because `arg` is what a
  typed ontology is mostly made of, so the read pays for itself.  Nothing declares
  `interArg` yet, and this check runs on *every* assert — the read `assert` names its
  dominant per-fact cost — so a third retrieval that finds nothing is a tax on every write
  in every KB.  One `count-with-functor` says whether any such declaration is stored at
  all; zero means no scoped read can find one, so there is nothing to look for.

  Under `*assertive-arg-types?*` the declaration derives the target's type once the
  trigger holds (`inter-arg-entailments`), and the conviction is `:weighed?` as
  `args-problem`'s symbol arm is (`entailment-covers?`)."
  [kb sentence context types decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (reasoning/taxonomy kb)]
    (when (and (symbol? pred)
               (convicts-symbols?)
               (kind-stored? decls 'interArg))
      (first
       (for [d       (in-content-order (decls 'interArg))
             :let  [b       (nth d 1)
                    n       (get b '?n)
                    t       (get b '?type)
                    m       (get b '?m)
                    u       (get b '?utype)
                    trigger (arg-at as n)
                    target  (arg-at as m)
                    sep     (when (and trigger target
                                       (checkable-term? trigger) (checkable-term? target)
                                       (symbol? t) (symbol? u)
                                       ;; the antecedent, established rather than merely unrefuted
                                       (kb/isa-among? (types trigger) t))
                              (separated-type tax types target u context))]
             :when sep]
         (cond-> {:type :inter-arg-type :sentence sentence :arg target :expected u :position m
                  :trigger trigger :trigger-type t :trigger-position n :disjoint-with sep
                  :message (str "arg constraint: " target " must be a " u " — " target " is a "
                                sep ", disjoint from " u " (arg " m " of " pred
                                (via-clause (declared-of d) pred)
                                ", because arg " n " is a " t ")")}
           *assertive-arg-types?* (assoc :weighed? true)))))))

(defn- separated-subtype
  "The reason a type `arg` the taxonomy separates from `t` fails a demand for a subtype of
  `t`, as `{:separated reason}` so `genl-violation` can weigh it."
  [arg t]
  {:separated (str arg " must be a subtype of " t " — " arg " is disjoint from " t)})

(defn- genl-violation
  "The `:arg-genl` violation of `arg` at position `n` under a demand for a subtype of `t`.
  `why` is the reason, a string or `separated-subtype`'s map; a separated one is
  `:weighed?` under the entailing reading, as `args-problem`'s symbol arm is
  (`entailment-covers?`)."
  [sentence arg t n why clause]
  (cond-> {:type :arg-genl :sentence sentence :arg arg :expected t :position n
           :message (str "arg constraint: " (if (map? why) (:separated why) why) clause)}
    (and (map? why) *assertive-arg-types?*) (assoc :weighed? true)))

(defn- genls-problem
  "First `(genlArg pred n type)` violation for a sentence, or nil.

  `genlArg` is `arg` one level up: it constrains the argument to be a **subtype**
  of the named type rather than an instance of it, which is what a type-level relation
  wants — `(genlArg partType 1 tangible)` says the first argument names a kind
  of physical object, where `(arg tangiblePartOf 1 tangible)` says it names one.

  Which constraints apply is context-scoped exactly as `arg` is, and so is the
  subtype test itself, judged from the writer's own vantage.  Which constraints apply
  also descends the predicate hierarchy exactly as `arg`'s do, by riding the same
  reader.

  **An application is typed by its function's `genlResult`**, never by its `result`:
  this position wants a kind, and `genlResult` is the declaration saying an application
  names one where `result` says it *is* one.  `convicting-result-type` has that
  argument, and keeps the two readings apart.

  Open-world has a floor here that `arg` does not have.  An argument outside the
  hierarchy is normally exempt, since the edges placing it may not have arrived yet —
  but an **individual** can never acquire them (`wff/genl-problems` refuses `genl` of
  one), so a type-level position holding one is convicted rather than excused.  The
  test is \"outside the hierarchy *and* individual\", not \"individual\", because a
  reified NAT is indistinguishable from an individual by spelling and is minted with real `genl` edges from
  its `genlResult` declarations — one that reaches `thing` is judged like any type.

  **A deliberate global/scoped split inside one `cond`.**  The first floor asks what
  the argument *is* (could it ever be a type?) and stays **global**: a reified NAT's
  minting edges land in `CxUniverse`, which a context wired outside the shipped topology
  cannot see, so a scoped floor would convict an imported reified NAT used from such a
  context as \"an individual, so never a subtype\" — false.  The second
  floor is the **scoped** open-world excuse: an argument with no *visible* path
  into the hierarchy may have its edges out of sight.  Past both floors, only a type the taxonomy separates from the declared one is
  convicted (`tax/disjointness-test`, scoped).  Under `*assertive-arg-types?*` the
  declaration derives the `genl` edge (`constraint-entailments`) and that conviction is
  `:weighed?` (`genl-violation`)."
  [kb sentence context decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (reasoning/taxonomy kb)]
    (when (symbol? pred)
      (first-refusing
       (for [d     (in-content-order (decls 'genlArg))
             :let  [b   (nth d 1)
                    n   (get b '?n)
                    t   (get b '?type)
                    arg (arg-at as n)
                    ;; the application arm — nil for every argument that is not one
                    r   (convicting-result-type kb nat/genl-result-types pred arg t context)
                    why (if r
                          (str (pr-str arg) " must be a subtype of " t " — "
                               (first arg) " results in a subtype of " r)
                          (when (and arg (checkable-term? arg) (symbol? t))
                            (cond
                              (not (tax/genl?-global tax arg 'thing))          ; global: the individual floor
                              (when (nm/individual? arg)
                                (str arg " is an individual, so it can never be a subtype of " t))

                              (not (tax/genl? tax arg 'thing context))  ; scoped: no visible evidence
                              nil                                       ; — open world excuses

                              ;; scoped: the writer's vantage
                              (and (convicts-symbols?) ((tax/disjointness-test tax t context) arg))
                              (separated-subtype arg t))))]
             :when why]
         (genl-violation sentence arg t n why
                         (str " (arg " n " of " pred (via-clause (declared-of d) pred) ")")))))))

;; ---- the covering argument constraints -----------------------------------
;; `arg` and `genlArg` type one numbered position.  `argsGenl` types EVERY accepted
;; position, and `argAndRest` / `argAndRestGenl` every position from a start onward
;; (`args` is the instance every-position spelling, read as the `(argAndRest P 1 T)` its
;; forward rule stores — `sugar-spellings`) — the tail of a variable-arity relation, where naming a largest finite `arg`
;; would make an unbounded relation look finite and leaving the later positions undeclared
;; would drop the contract silently.  Each covering form generalizes its singular twin and
;; reuses its per-argument conviction: `argAndRest` asks the instance question `arg`
;; asks, `argsGenl` and `argAndRestGenl` the subtype question `genlArg` asks.
;;
;; **The walk is over the positions the sentence actually has, not a re-counted tail.**
;; every position the sentence has is walked, including one past a length its relation
;; is bound to: such a tuple is stored and held inert in the `:out` forced set
;; (`vaelii.impl.decide.arity`).  The covering declarations are read
;; through the same `decls` reader the singular forms use, so a super-predicate's covering
;; declaration binds a sub-predicate's tuples for `args-problem`'s reason.

(defn- covering-declared?
  "Is any covering declaration of one of the `:props` `kinds` marked in the taxonomy?
  A `:props` map lookup per kind, not a predicate-extent read — so a KB with no covering
  declaration adds nothing to the firing read budget, where a per-functor
  `stored-count-with-functor` presence check would cost one predicate-extent read per
  assert for a feature the KB does not use.  Over-approximates like
  `inter-args-problem`'s index presence check:
  the mark is global, so a covering constraint on any predicate runs the scoped check for
  every assert, and the scoped `decls` read decides whose tuples it actually binds."
  [kb kinds]
  (let [tax (reasoning/taxonomy kb)]
    (boolean (some #(seq (tax/props tax %)) kinds))))

(defn- covering-triples
  "The covering declarations of the every-position kind `ek` (nil for none — the instance
  level has no every-position kind it queries, `sugar-spellings`) and the tail kind `rk`,
  read through the shared `decls` reader and merged into `[start type kind match]`
  entries in content order — start 1 for `ek`, the declared start for `rk`.  A tail
  declaration whose start is not a positive integer is dropped here rather than convicting
  from an ill-formed position; its own `(arg <rk> 2 positive_integer)` refuses it at the
  entry point, so a stored one is a torn record, not a live constraint.  Sorting keys the
  refusal on what the KB says, exactly as `in-content-order` does for the singular forms."
  [decls ek rk]
  (nm/sort-by-content-key
   #(nm/print-key (:sentence (nth (nth % 3) 2))) compare
   (concat (when ek (for [m (decls ek)] [1 (get (nth m 1) '?type) ek m]))
           (for [m     (decls rk)
                 :let  [b (nth m 1) s (get b '?start)]
                 :when (and (integer? s) (pos? s))]
             [s (get b '?type) rk m]))))

(defn- suffix-positions
  "The one-based positions from `start` to the last argument of the argument vector `as`
  — the walk every tail constraint makes, the covering forms and the homogeneity forms
  alike.  Bounded by the arguments the sentence has."
  [as start]
  (range start (inc (count as))))

(defn- covering-clause
  "How a covering refusal names the position it convicts: `argsGenl, position N` for the
  every-position form, `argAndRest from M, position N` for a tail form — an `args`
  declaration's refusal among them, naming the twin its forward rule stores."
  [kind start pos]
  (if (= 'argsGenl kind)
    (str kind ", position " pos)
    (str kind " from " start ", position " pos)))

(defn- covering-args-problem
  "First `(argAndRest R n T)` violation for a sentence, or nil.  Types every position
  from `n` onward as an **instance** of `T`,
  reusing `args-problem`'s per-argument conviction — `convicting-result-type` for an
  application, `outside-declared-type?` for a symbol or value, and weighing the symbol arm
  under the toggle.  Conjunctive with a singular `(arg R n T)`:
  both are read, neither overrides.  An `(args R T)` is read as the `(argAndRest R 1 T)`
  its forward rule stores (`sugar-spellings`), and the refusal names that twin.

  Behind the O(1) presence check `inter-args-problem` is, and for the same reason:
  nothing declares a covering constraint yet and this runs on every assert."
  [kb sentence context types decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (reasoning/taxonomy kb)]
    (when (and (symbol? pred)
               (covering-declared? kb [:declares-arg-and-rest-isa]))
      (first-refusing
       (for [[start t kind decl] (covering-triples decls nil 'argAndRest)
             pos   (suffix-positions as start)
             :let  [arg (arg-at as pos)
                    r   (convicting-result-type kb nat/result-types pred arg t context)
                    out (when (and arg (not r)) (outside-declared-type? kb tax types arg t context))]
             :when (and arg (or r out))]
         (arg-type-violation sentence arg t pos out
                             (str (when r (str " — " (first arg) " results in a " r))
                                  " (" (covering-clause kind start pos) " of " pred
                                  (via-clause (declared-of decl) pred) ")")))))))

(defn- covering-genls-problem
  "First `(argsGenl R T)` / `(argAndRestGenl R n T)` violation for a sentence, or nil.
  The subtype twin of `covering-args-problem`: every admitted position (or every one from
  `n` onward) must name a **subtype** of `T`, reusing `genls-problem`'s per-argument
  reading — `genlResult` for an application, and the global individual floor, the scoped
  open-world excuse and the scoped separation test for a symbol.  Conjunctive with a singular
  `(genlArg R n T)`.

  **The individual floor is a global read (`tax/genl?-global`), for `genls-problem`'s
  reason (E17_ALLOW).**  The floor asks whether the argument could ever be a type at all;
  a reified NAT's minting `genl` edges land in `CxUniverse`, which a context wired outside
  the shipped topology cannot see, so a scoped floor would convict an imported reified
  NAT used from such a context as \"an individual, so never a subtype\" — false.  The
  separation test stays scoped, the writer's own vantage, and is weighed under the
  entailing reading, as `genls-problem`'s is."
  [kb sentence context decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (reasoning/taxonomy kb)]
    (when (and (symbol? pred)
               (covering-declared? kb [:declares-args-genl :declares-arg-and-rest-genl]))
      (first-refusing
       (for [[start t kind decl] (covering-triples decls 'argsGenl 'argAndRestGenl)
             pos   (suffix-positions as start)
             :let  [arg (arg-at as pos)
                    r   (convicting-result-type kb nat/genl-result-types pred arg t context)
                    why (if r
                          (str (pr-str arg) " must be a subtype of " t " — "
                               (first arg) " results in a subtype of " r)
                          (when (and arg (checkable-term? arg) (symbol? t))
                            (cond
                              (not (tax/genl?-global tax arg 'thing))
                              (when (nm/individual? arg)
                                (str arg " is an individual, so it can never be a subtype of " t))

                              (not (tax/genl? tax arg 'thing context)) nil

                              (and (convicts-symbols?) ((tax/disjointness-test tax t context) arg))
                              (separated-subtype arg t))))]
             :when why]
         (genl-violation sentence arg t pos why
                         (str " (" (covering-clause kind start pos)
                              " of " pred (via-clause (declared-of decl) pred) ")")))))))

;; ---- the homogeneity constraints -----------------------------------------
;; `interArg` demands a type at one position once another position holds a type.
;; `interArgs` / `interArgAndRest` demand ONE type of a whole suffix — every position, or
;; every position from a start onward — once any argument in that suffix holds it.  The
;; type is the trigger and the target at once, and the reading of each side is
;; `inter-args-problem`'s: the trigger must be positively established, the target is
;; convicted by a separated type.  The walk is over the positions the sentence has, for the reason
;; the covering constraints give above.

(defn- homogeneity-declarations
  "The `interArgs` / `interArgAndRest` declarations binding a sentence's tuples, as
  `[start type via]` entries in content order — start 1 for `interArgs`, the declared
  start for `interArgAndRest` — with `via` the predicate the declaration is written of.

  **One entry per constraint, whichever spelling states it.**  core.txt's two forward rules
  derive `(interArgAndRest R 1 T)` from `(interArgs R T)` and `(interArgs R T)` from
  `(interArgAndRest R 1 T)`, so a KB that states either spelling holds both, and a KB
  without those rules holds the one it was told.  The entries are deduplicated on
  `[start type via]` and sorted on a key that spells each of them as `interArgAndRest`, so
  a sentence draws the same refusal whichever spelling arrived, and a stated declaration
  with its derived twin convicts once.  A start that is not a positive integer is dropped,
  as `covering-triples` drops one: `(arg interArgAndRest 2 positive_integer)` refuses it at
  the entry point, so a stored one is a torn record rather than a live constraint."
  [decls]
  (->> (concat (for [m (decls 'interArgs)]
                 [1 (get (nth m 1) '?type) (declared-of m)])
               (for [m     (decls 'interArgAndRest)
                     :let  [b (nth m 1) s (get b '?start)]
                     :when (and (integer? s) (pos? s))]
                 [s (get b '?type) (declared-of m)]))
       distinct
       (nm/sort-by-content-key (fn [[s t via]] (nm/print-key (list 'interArgAndRest via s t)))
                               compare)))

(defn- homogeneity-clause
  "How a homogeneity refusal names the declaration: `interArgs` for start 1, which is
  what both spellings state there, and `interArgAndRest from N` for a later start."
  [start]
  (if (= 1 start) "interArgs" (str "interArgAndRest from " start)))

(defn- inter-args-homogeneity-problem
  "First `(interArgs R T)` / `(interArgAndRest R n T)` violation for a sentence, or nil.

  Per declaration, one pass over the suffix: the first position whose argument is
  positively established as a `T` is the trigger, and the first position whose argument
  believes a type the taxonomy separates from `T` is the target.  A suffix with no trigger is
  unconstrained, so an application whose arguments all lie outside `T` passes, and so
  does one whose other arguments are unknown.  Positions below the start are never read.
  Positions are sentence content, so the first trigger and the first target are chosen
  by content and never by a handle.

  Both sides read `inter-args-problem`'s way, and each for its reason.  A **symbol**
  argument is typed by its memberships (`types`, the shared per-assert reader, so a
  position read as a trigger and as a target costs one retrieval).  A value or a compound
  is neither a trigger nor a target, which is the reading `inter-args-problem` gives
  both of its positions.

  Under `*assertive-arg-types?*` the declaration derives `T` of every other suffix
  argument once a trigger holds (`homogeneity-entailments`), and the conviction is
  `:weighed?` (`entailment-covers?`).  This runs behind the taxonomy `:props` presence
  check `covering-declared?` is, so a KB that declares no homogeneity constraint pays two
  map lookups per assert and no index read."
  [kb sentence context types decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (reasoning/taxonomy kb)]
    (when (and (symbol? pred)
               (convicts-symbols?)
               (covering-declared? kb [:declares-inter-args-isa
                                       :declares-inter-arg-and-rest-isa]))
      (let [holds? (fn [t p] (let [x (arg-at as p)]
                               (and (checkable-term? x)
                                    (kb/isa-among? (types x) t))))
            fails  (fn [t p] (let [x (arg-at as p)]
                               (when (checkable-term? x)
                                 (separated-type tax types x t context))))]
        (first
         (for [[start t via] (homogeneity-declarations decls)
               :when (symbol? t)
               :let  [suffix (suffix-positions as start)
                      n      (first (filter #(holds? t %) suffix))]
               :when n
               :let  [m (first (filter #(fails t %) suffix))]
               :when m
               :let  [target (arg-at as m)
                      sep    (fails t m)]]
           (cond-> {:type :inter-arg-type :sentence sentence :arg target :expected t :position m
                    :trigger (arg-at as n) :trigger-type t :trigger-position n :disjoint-with sep
                    :message (str "arg constraint: " target " must be a " t " — " target " is a "
                                  sep ", disjoint from " t " ("
                                  (homogeneity-clause start) ", position " m " of " pred
                                  (via-clause via pred)
                                  ", because position " n " is a " t ")")}
             *assertive-arg-types?* (assoc :weighed? true))))))))

(defn- compound-kind-against
  "The expression kind of the compound `arg` (`provers/shape-kinds`) that the taxonomy
  separates from `t` as seen from `context`, or nil.  Only a separation convicts: the
  spelling leaves `(R a)` at `non_atomic_expression`, which reaches neither
  `non_atomic_term` nor `formula`, so a kind failing to reach `t` is no conviction."
  [tax arg t context]
  (when (and (sequential? arg) (symbol? t) (not (sx/variable? t)))
    (let [sep? (tax/disjointness-test tax t context)]
      (first (filter sep? (sort-by nm/name-key (provers/shape-kinds arg)))))))

(defn- quoted-outside?
  "Does the argument `arg`, taken as a term, fail the `(quotedArg P n t)` demand, as seen
  from `context`: a value or a symbol provably outside `t` (`value-outside?`), a
  syntactic type (`syntactic-type?`), or a compound one of whose expression kinds the
  taxonomy separates from `t` (`compound-kind-against`)?"
  [kb tax arg t context]
  (let [ks (value-kinds arg)]
    (boolean (and (some? arg) (symbol? t)
                  (if (value-kind arg)
                    (and (not (contains? ks t))
                         (syntactic-type? tax t context)
                         (value-outside? kb tax arg ks t context))
                    (compound-kind-against tax arg t context))))))

(defn- quoted-declarations
  "The `quotedArg` and `quotedArgAndRest` declarations `decls` reads, merged into
  `[start tail? type match]` entries in content order, as `covering-triples` merges the
  covering forms: a `quotedArg` types its one position, a `quotedArgAndRest` its start
  and every later one.  A tail declaration whose start is not a positive integer is
  dropped, its own `(arg quotedArgAndRest 2 positive_integer)` refusing it at the entry
  point."
  [decls]
  (nm/sort-by-content-key
   #(nm/print-key (:sentence (nth (nth % 3) 2))) compare
   (concat (for [m (decls 'quotedArg)]
             [(get (nth m 1) '?n) false (get (nth m 1) '?type) m])
           (for [m     (decls 'quotedArgAndRest)
                 :let  [b (nth m 1) s (get b '?start)]
                 :when (and (integer? s) (pos? s))]
             [s true (get b '?type) m]))))

(defn- quoted-declared?
  "Is any `quotedArg` or `quotedArgAndRest` declaration stored — the presence check the
  mention arms stand behind.  `quotedArg` by the O(1) count `kind-stored?` reads, and
  `quotedArgAndRest` by its `:declares-quoted-arg-and-rest` mark (`covering-declared?`), a
  `:props` lookup the declaration's own arms keep as it arrives and leaves: a second
  count read here would cost every assert of every KB one predicate-extent read for a
  form the KB does not use.  Global, as both presence checks are; the scoped `decls`
  read decides whose tuples a declaration binds and whether the context sees it."
  [kb decls]
  (or (kind-stored? decls 'quotedArg)
      (covering-declared? kb [:declares-quoted-arg-and-rest])))

(defn- args-quoted-problem
  "First `(quotedArg pred n type)` or `(quotedArgAndRest pred n type)` violation for a
  sentence, or nil.  The tail form reads every position from `n` to the last, as
  `argAndRest` does for `arg`.

  The **mention** twin of `args-problem`: where that types what an argument *denotes*,
  this types the argument *as a term* — what is decidable from the value itself
  (`value-kinds`), checked through genl against the declared syntactic type.
  `(quotedArg name_of_guy 1 string)` refuses
  `(name_of_guy 5)` because `5` is a `number`, not a `string`, and admits `(name_of_guy
  \"Bob\")`.  Closed about a decidable value — every leaf kind has a name
  (`syntactic-roots`), a keyword and a character included.  A **compound** is judged by
  the expression kinds its spelling decides (`compound-kind-against`), and convicted only
  where one is separated from the declared type.

  **`value-kinds`, not `value-kind`, and the difference is the sign-refined
  integers.**  `syntactic-type?` admits any type below a syntactic root, so
  `positive_integer` — a part of core.txt's partitions of `integer` — is inside this
  check's domain and always was.  Judged by EDN kind alone the comparison ran the wrong
  way round, asking whether `integer` is below `positive_integer`, and refused every
  integer written in such a position (#55).  The shared reader answers the
  question the declaration actually asks, and the mention and denotation readings agree
  about a value for the reason they always have: a value denotes itself.

  Behind the same O(1) presence check as `inter-args-problem`, and for the same reason: nothing
  declares `quotedArg` in a bare KB, and this runs on every assert, so a
  `count-with-functor` says whether any is stored before a scoped read looks."
  [kb sentence context _types decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        tax  (reasoning/taxonomy kb)]
    (when (and (symbol? pred)
               (quoted-declared? kb decls))
      (first
       (for [[start tail? t d] (quoted-declarations decls)
             n     (if tail? (suffix-positions as start) [start])
             :let  [arg (arg-at as n)
                    lit (value-kind arg)
                    ks  (if lit (value-kinds arg) (provers/shape-kinds arg))]
             :when (quoted-outside? kb tax arg t context)]
         {:type :quoted-arg-type :sentence sentence :arg arg :expected t :position n
          ;; the value types when the refinement is what failed, the bare EDN kind
          ;; otherwise: "it is a integer" says nothing useful about -5 refused a
          ;; positive_integer, where the kind alone is the whole answer for "Bob"
          ;; refused a number
          :message (str "quoted-arg constraint: " arg " must be a " t " as a term — it is a "
                        (if (= ks #{lit}) (str lit) (str/join " / " (sort ks)))
                        (when-not lit
                          (str ", and " (compound-kind-against tax arg t context)
                               " is disjoint from " t))
                        " (" (when tail? (str "quotedArgAndRest from " start ", "))
                        "arg " n " of " pred (via-clause (declared-of d) pred) ")")})))))

;; ---- the inputs of a function application ---------------------------------
;; The arms above read the declarations of the sentence's own relation, and an
;; application sitting in one of its positions is typed there by its function's
;; `result` — what the application *denotes*.  That says nothing about what is written
;; *inside* it: `(arg InputGapFn 1 integer)` constrains the input of every application
;; of `InputGapFn`, and `(observes (InputGapFn "x"))` violates it whatever the result
;; reading concludes.  So the argument arms run a second time, one level in, with the
;; function standing where the predicate stood.  Both readings run; neither replaces
;; the other.

(defn- mentioned-position
  "A test of the positions of the relation `decls` reads that a visible `quotedArg` or
  `quotedArgAndRest` declaration types — the positions holding a **mention** of the term
  written there rather than a use of it.  Through `decls` with no count check of its own:
  the reader memoizes the kind, so `args-quoted-problem`'s read of it over the same
  relation is the one read."
  [decls]
  (let [at   (into #{} (map #(get (nth % 1) '?n)) (decls 'quotedArg))
        from (some->> (decls 'quotedArgAndRest)
                      (keep #(let [s (get (nth % 1) '?start)] (when (and (integer? s) (pos? s)) s)))
                      seq (apply min))]
    (fn [n] (or (contains? at n) (and from (>= n from))))))

(defn quoted-positions
  "A test of the positions of `pred` a `quotedArg` or `quotedArgAndRest` declaration
  visible from `context` types (`mentioned-position`), behind `quoted-declared?`: false
  of every position where neither is stored."
  [kb pred context]
  (let [decls (declaration-reader kb pred context)]
    (if (and (symbol? pred) (not (sx/variable? pred))
             (quoted-declared? kb decls))
      (mentioned-position decls)
      (constantly false))))

(defn- formula-head?
  "Does the compound `x`, written in an argument position, have a head the KB knows as a
  predicate — is it a `predication`, the other half of `non_atomic_expression`
  (core.txt), rather than a function applied to terms?  A formula written as an argument is
  a sentence about its predicate's tuples, which that predicate's declarations do not
  type from here.  A head the KB has not classified is read as a function: its
  declarations are what it has, and a head with none convicts nothing.

  A membership read, so `nested-input-problem` asks it only of an application something
  inside convicted: the common application convicts nothing, and asking first would put
  a read on every assert that carries a compound (`assert_cost_test`'s compound
  workload)."
  [types x]
  (kb/isa-among? (types (first x)) 'predicate))

(defn- nested-input-problem
  "The first violation of a function's own argument declarations by an input written
  inside one of `sentence`'s used arguments, at any depth, or nil.  The violation is the
  arm's own, so its `:sentence` is the innermost application whose input failed.

  **No derivation.**  A declaration arriving derives over the facts already stored, which
  it finds by predicate, and no index finds the applications of a function inside stored
  facts, so a membership derived from a nested input would be drawn in one arrival order
  and not the other.  The arms read here therefore derive nothing.  Under the entailing
  reading a nested symbol's conviction is `:weighed?` as at the top level
  (`entailment-covers?`), so `assert` stores the sentence and `try-assert` refuses it.  A
  value and an application are convicted as at the top level, and a function that
  declares nothing convicts nothing.

  **Terms, not formulas.**  A connective's argument, and a compound whose head is a known
  predicate, is a formula (`formula-head?`), and nothing found inside one convicts.

  **Mentions are not descended into.**  A position a `quotedArg` declaration types holds
  the term written there, not a use of it, so an application in it is syntax and its
  function's declarations about what its inputs denote do not reach it; the same holds
  for the argument of a quoting predicate (`res/nat-quoting-predicates`) and of a
  quoting function (`sx/quoting-functors`).  A quoting function's own declarations are
  still read over its
  application — only what it quotes is left alone.

  One declaration reader per application, built on reaching it, so a sentence with no
  compound argument reads nothing: `application-term?` over its arguments is the whole
  cost."
  [kb sentence context types decls]
  (let [pred (nm/functor sentence)
        as   (nm/args sentence)]
    (when (and (symbol? pred)
               (not (contains? provers/formula-heads pred))
               (some application-term? as)
               (not (contains? res/nat-quoting-predicates pred))
               (not (sx/quoting-functor? pred)))
      (let [mentioned? (mentioned-position decls)]
        (first-refusing
         (for [[n x] (map-indexed (fn [i a] [(inc i) a]) as)
               :when (and (application-term? x)
                          (not (contains? provers/formula-heads (first x)))
                          (not (mentioned? n)))
               :let  [ds (declaration-reader kb (first x) context (decls ::counts nil))
                      p  (first-refusing
                          (keep #(%)
                                [#(args-problem kb x context types ds)
                                 #(inter-args-problem kb x context types ds)
                                 #(inter-args-homogeneity-problem kb x context types ds)
                                 #(genls-problem kb x context ds)
                                 #(covering-args-problem kb x context types ds)
                                 #(covering-genls-problem kb x context ds)
                                 #(args-quoted-problem kb x context types ds)
                                 #(nested-input-problem kb x context types ds)]))]
               :when (and p (not (formula-head? types x)))]
           p))))))

(defn- application-input-problem
  "First violation of a function's argument declarations inside `sentence`'s arguments,
  or nil — `nested-input-problem` reported against the sentence being checked.

  The arm's `:type`, `:arg`, `:expected` and `:position` are kept, so a caller reads a
  nested `:arg-type` exactly as it reads a top-level one and `conviction-watch` watches
  the convicted input.  `:position` is the position in the application's function, and
  `:application` names that application; the message says where it sits."
  [kb sentence context types decls]
  (when-let [p (nested-input-problem kb sentence context types decls)]
    (assoc p
           :sentence sentence
           :application (:sentence p)
           :message (str (:message p) ", inside " (pr-str (:sentence p))))))

;; ---- the argument constraints, checked against each other ----------------

(def ^:private arg-constraint-kinds
  "The two **unconditional** argument constraints, the ones `declaration-problem` reads
  as `(kind P n T)`.

  `interArg` is not here and has its own arm.  It is written at a different arity and
  names two positions, so it fits neither the `(= 3 (nm/arity …))` test — forcing it in
  would put that difference inside every reader of this set."
  '#{arg genlArg})

(defn- variable-arity?
  "Is `pred` declared `variable_arity`, from the vantage `types` reads with?

  The escape the whole arity family turns on, spelled once so every arm reads it the same
  way: off the predicate's own memberships, so a mark reached through a `genl` edge
  between collections releases exactly as a directly asserted one does."
  [types pred]
  (kb/isa-among? (types pred) 'variable_arity))

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
  `res/matches-visible` fans over the whole `genlCx` ancestor set, so one sentence stated in
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
  already convicts under the type it actually states.

  With `all?`, every match is named, the exact ones first, for a caller whose
  entailing matches convict under no type of their own (`negation-handles`)."
  ([matches target] (handle-namings matches target false))
  ([matches target all?]
   (let [sen   (fn [m] (:sentence (nth m 2)))
         ;; `nm/print-key`, and built once per match rather than once per comparison: the
         ;; second arm names ONE handle out of a `res/matches-visible` answer *set*, so a
         ;; key an ambient `*print-length*` collapsed would decide the refusal on
         ;; enumeration order — which is the handle order this key exists to keep out
         order (fn [m] (nm/print-key [(sen m) (:context (nth m 2))]))
         named (fn [ms] (map first (nm/sort-by-content-key order compare ms)))
         exact (seq (filter #(= target (sen %)) matches))]
     (cond
       all?   (concat (named exact) (named (remove #(= target (sen %)) matches)))
       exact  (named exact)
       :else  (take 1 (named matches))))))

(defn- clash-members
  "The stored sentexes of `handles` as `{:handle :sentence :context}`, in content order:
  the members a declaration clash names in `:clashes-with`."
  [kb handles]
  (->> handles
       (keep #(when-let [s (p/get-sentex (:records kb) %)]
                {:handle % :sentence (sx/sentence-of s) :context (:context s)}))
       (nm/sort-by-content-key #(nm/print-key [(:sentence %) (:context %)]) compare)
       vec))

(defn- arg-position-problem
  "A declaration constraining a position `pred` does not have — `(arg parentOf 5
  animal)` where `parentOf` is declared binary — or nil.  The length is
  `arity/relation-length`'s, own or inherited, and a predicate with no bound length is
  unconstrained.  A `variable_arity` mark on `pred`'s own memberships
  (`variable-arity?`) releases every position: its tuples reach any length from its
  declared one upward.  `:via` names the predicate the length was read off, and
  `:clashes-with` the bindings stating it.  `assert` stores such a declaration and the
  length strands it; `try-assert` refuses it (docs/taxonomy.md, \"A declaration the arity
  strands\")."
  [kb f pred n types]
  (when (and (integer? n) (pos? n))
    (when-let [{declared :exact via :via grounds :grounds} (arity/relation-length kb pred true)]
      ;; the position the predicate does not have is the one the shared decision reads as
      ;; certainly-not-admitted — the same function `provers/AdmitsArgnumProver` answers, so
      ;; a position this arm convicts is one `(admitsArgnum pred n)` does not prove
      (when (false? (provers/admits-position? (variable-arity? types pred) declared n))
        {:type :arg-position :predicate pred
         :position n :arity declared :via via
         :clashes-with (clash-members kb grounds)
         :message (str f " constrains argument " n " of " pred ", which "
                       (arity-binding-clause pred via declared))}))))

(defn- declared-positions
  "The positions the declaration `chk` names on its predicate, or nil when `chk` is not
  one: one for `arg` and `genlArg`, two for `interArg`, `interArgEqual` and `argArg`,
  and the projected one for `arg1` through `arg5`."
  [chk]
  (let [[f pred n _ m] chk
        k (nm/arity chk)]
    (when (symbol? pred)
      (cond
        (and (sx/arg-projections f) (= 2 k))              [(sx/arg-projections f)]
        (and (= 'interArg f) (= 5 k))                     [n m]
        (and (= 'interArgEqual f) (= 5 k))                [n (nth chk 4)]
        (and (= 'argArg f) (= 3 k))                       [n (nth chk 3)]
        (and (contains? arg-constraint-kinds f) (= 3 k)) [n]))))

(defn- position-problem
  "The first `arg-position-problem` among the positions the declaration `chk` names
  (`declared-positions`), carrying `chk` as `:sentence`, or nil."
  [kb chk types]
  (let [[f pred] chk]
    (some-> (some #(arg-position-problem kb f pred % types) (declared-positions chk))
            (assoc :sentence chk))))

(defn- declaration-problem
  "A problem an `arg` / `genlArg` / `interArg` / `interArgEqual` / `argArg` declaration,
  or an `arg1`…`arg5` projection, forms with what the KB says about its predicate, or nil:

  * a position the predicate does not have (`position-problem`);
  * a `genlArg` on an `instance_relation_predicate` (`:arg-constraint-kind`), whose
    arguments are individuals and never subtypes, naming the memberships in
    `:clashes-with`.

  Both read stored content, so `assert` stores the declaration and `try-assert` refuses
  it (`declaration-kinds`).  `arg` on a `type_relation_predicate` is not a problem, and
  neither is `arg` beside `genlArg` on one position (docs/taxonomy.md, \"The declarations
  are checked against each other\")."
  [kb sentence context types]
  (or (position-problem kb sentence types)
      (let [[f pred n] sentence]
        (when (and (= 'genlArg f) (= 3 (nm/arity sentence)) (symbol? pred) (integer? n) (pos? n))
          (when-let [ms (seq (res/matches-visible kb (list 'instance_relation_predicate pred) context))]
            {:type :arg-constraint-kind :sentence sentence :predicate pred
             :clashes-with (clash-members kb (map first ms))
             :message (str pred " is declared instance_relation_predicate, so its arguments are"
                           " constrained with arg, not genlArg")})))))

;; ---- the three violations that name an opposing sentex -------------------
;;
;; Disjointness, functionality and asymmetry are not like the argument constraints.
;; Each convicts by pointing at **another believed sentex** that the incoming one
;; cannot coexist with — a pair, which is exactly what a nogood is, and exactly what
;; `settle` already arbitrates for `S` against `(not S)`.  So each carries the
;; opposing handle, the entry point stores the sentence, and `settle` decides the nogood
;; from its members' classes.  See docs/nmtms.md.
;;
;; The argument constraints do not join them: `(parentOf Fred Mary)` violating `(arg
;; parentOf 1 animal)` is convicted by the *absence* of a path from Fred's types to
;; `animal`, an open-world negation-as-failure judgement with no second member to weigh,
;; so those stay refusals.  `arity` is not checked here: a tuple whose length breaks its
;; predicate's binding is a nogood the settle places (`vaelii.impl.decide`).

(def arbitrable-kinds
  "The definitional violations that name **other believed sentexes** rather than a
  malformed sentence, so `settle` can arbitrate them like any other contradiction."
  #{:disjoint :functional :asymmetric :anti-transitive :cover})

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

(defn arbitrable?
  "Can `settle` arbitrate this violation instead of the caller refusing it — does it
  name opposing believed sentexes to form a nogood with?"
  [v]
  (boolean (and v (contains? arbitrable-kinds (:type v))
                (seq (opposing-handles v)))))

(def ^:private declaration-kinds
  "The violations `declaration-problem` convicts a declaration of by reading stored
  content.  `assert` stores the declaration in every arrival order, and `try-assert`
  refuses it."
  #{:arg-position :arg-constraint-kind})

(defn refuses-assert?
  "Does violation `v` refuse its sentence at the write entry point?  True unless `v` is
  arbitrable (`arbitrable?`), `:weighed?` or one of `declaration-kinds`.  A clash naming
  the other believed members of its nogood is stored, and `settle` decides it and reports
  it when every member is `:monotonic`.  An argument conviction the entailing reading
  draws a membership for is stored, and the settle weighs that membership
  (`entailment-covers?`).  A declaration a stored length strands is stored and constrains
  nothing.  A malformed sentence, any other argument conviction and a clash naming no
  stored member refuse (docs/nmtms.md, \"What a refusal may rest on\").  A fact's own
  argument conviction does not refuse at `assert`: `constraint-checks` stores the fact and
  holds it inert (`fact-refuses?`)."
  [v]
  (boolean (and v (not (arbitrable? v)) (not (:weighed? v))
                (not (contains? declaration-kinds (:type v))))))

(defn- entry-refuses?
  "Does violation `v` refuse its sentence at the write entry point under
  `*refuse-clashes?*`?"
  [v]
  (if *refuse-clashes?* (some? v) (refuses-assert? v)))

(def ^:private argument-conviction-kinds
  "The violations that convict an argument of its declared type: under `*refuse-clashes?*`
  each is a definitional clash (`refusal`), and under `assert` the fact is stored and held
  inert unless the entailing reading weighs it (`held-inert?`)."
  #{:arg-type :arg-genl :inter-arg-type :quoted-arg-type})

(defn- held-inert?
  "Is `v` an argument conviction `assert` stores and holds inert: one of
  `argument-conviction-kinds` that the entailing reading does not weigh?"
  [v]
  (boolean (and v (contains? argument-conviction-kinds (:type v)) (not (:weighed? v)))))

(defn- fact-refuses?
  "Does violation `v` refuse a fact at `assert`: `entry-refuses?`, less the argument
  convictions `assert` holds inert (`held-inert?`).  Under `*refuse-clashes?*` every
  violation refuses."
  [v]
  (and (entry-refuses? v) (or *refuse-clashes?* (not (held-inert? v)))))

(defn- membership-handles-led
  "`membership-handles`' small side: lead from `x`'s own argument-1 postings (a handful)
  and test each up via `genl?` (t'' ⊑ t ⟺ t'' ∈ specs(t), see `kb/memberships`),
  rather than `matches-visible` walking `specs(t)` *down* — unbounded for a broad t (with
  t = `thing`, every type in the KB), and the closure walk that dominates a cold rebuild's
  clash pass.  The candidate set, the filters (believed, context-visible, `except`-hidden,
  retired) and `handle-namings` are exactly what `matches-visible` would feed here — it is
  `matches-hierarchical` over `(t x)` then `without-excepted`/`without-retired`, and the
  pred-hierarchy filter `t'' ∈ specs(t)` is the same set as `t'' ⊑ t` — so the
  answer set is identical, retrieved from the small side.  Split out so `res/*lead-side*`
  can force the `matches-visible` reference the two oracles compare it against.

  **The exact postings first.**  `handle-namings` names the matches saying `(t x)` itself
  whenever one survives the filters, and the entailing ones only when none does, so a
  surviving exact match settles the answer and no other posting is walked up.  The
  filters drop matches one at a time, so the exact ones that survive them alone are the
  ones that survive them among the rest.  `disjoint-problems` asks this of the types a
  term is asserted to hold, where an exact posting is the rule, so the exact ones are
  read first by their own trie path under every context, and the term's postings, every
  fact holding it at argument 1, only when none survives."
  [kb t x context]
  (let [recs   (:records kb)
        tms    (reasoning/tms kb)
        tax    (reasoning/taxonomy kb)
        target (list t x)
        up     (when-not (sx/variable? context) (tax/context-up tax context))
        vis?   (if up #(contains? up %) (constantly true))
        cand   (fn [h]
                 (when-let [s (p/get-sentex recs h)]
                   (when (and (jtms/in? tms (:id s)) (vis? (:context s)))
                     (let [sen (:sentence s)]
                       (when (and (= 1 (nm/arity sen))
                                  (= x (first (nm/args sen)))
                                  (not (sx/exceptWhen-meta? sen)))
                         s)))))
        kept   #(->> % (exc/without-excepted kb context) (res/without-retired kb context))
        said   (keep #(when (= target (:sentence %)) [(:id %) nil %]))
        ;; the exact memberships by their own path, then by the postings when none
        ;; survives, which is when the postings are read anyway
        by-path (when (and (symbol? x) (not (sx/variable? x)))
                  (kept (sequence (comp (distinct) (keep cand) said)
                                  (reads/as-stored-at-path (:index kb)
                                                           (sx/path (sx/sentex target '?c))))))
        cands  (delay (into [] (keep cand) (reads/as-stored-with-arg-global (:index kb) 1 x)))
        exact  (if (seq by-path) by-path (kept (sequence said @cands)))]
    (handle-namings
     (if (seq exact)
       exact
       (kept (keep (fn [s]
                     (let [t'' (nm/functor (:sentence s))]
                       ;; a walk, not the closure: every type `x` holds is tested, and a
                       ;; closure read builds the supertype closure of each
                       (when (or (= t'' t) (tax/genl? tax t'' t context))
                         [(:id s) nil s])))
                   @cands)))
     target)))

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

  Two ways to reach the same set, chosen by `res/*lead-side*`: `:scoped` runs the
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

  X is any term, not only an individual, so a `disjoint_metatype` over predicate
  types separates the predicates it is declared of — one predicate cannot be both
  an `instance_relation_predicate` and a `type_relation_predicate`.

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
      ;; one question, asked of each type the term holds: `t` and the asserting context
      ;; are fixed across the loop, and they are what most of the answer is a function
      ;; of.  A `t` no declaration reaches reads none of the term's types.
      (when-let [disjoint? (and (checkable-term? x)
                                (tax/separation-test (reasoning/taxonomy kb) t context))]
        (for [t' (:types (types x))
              :when (disjoint? t')
              h    (membership-handles kb t' x context)]
          {:type :disjoint :sentence sentence :types [t t']
           :opposing-handle h
           :message (str "disjointness violated: " x " cannot be both "
                         t " and " t')})))))

(defn- negation-handles
  "The handles of the believed sentexes visible from `context` that entail `(not (t x))`,
  each a denial of `t` or of a supertype of it, in content order (`handle-namings`).
  `membership-handles` names one entailing match, and `negation-handles` names every one:
  a denial of a supertype rules out the part `t` and convicts under no part of its own,
  so each such denial is a member of its own `covering` nogood, and
  `membership/term-nogoods` forms one nogood per choice of denials."
  [kb t x context]
  (let [target (list 'not (list t x))]
    (handle-namings (res/matches-visible kb target context) target true)))

(defn- separation-denial-handles
  "The handles of the believed memberships `(s x)` visible from `context` whose type a
  separation keeps apart from `t` under the soundness rule (`res/separation-denials`),
  each once, in content order: the sentexes a derived `(not (t x))` rests on, and so the
  members a refuted cover names for the part `t`."
  [kb t x context]
  (into [] (comp (map :membership) (distinct)) (res/separation-denials kb t x context)))

(defn- cover-problem
  "The first refuted cover, as a violation map, when `keep?` accepts it, else nil: a cover
  every one of whose parts is denied of a term the whole holds.

  `(covering W A B)` says that an instance of `W` is an `A` or a `B`. With `(W X)`
  believed and `(not (A X))` and `(not (B X))` believed beside it, the declaration itself
  is refuted — a contradiction among believed sentexes, which is a nogood rather than a
  malformed sentence, so `settle` weighs the membership and the negations and defeats
  the weakest, exactly as it weighs the two memberships of a disjointness clash.

  Asked of the membership `(W X)` or of a negation `(not (A X))`: either one can
  complete the refutation.  `settle` re-asks it of the membership (`reads-clash?`) for a
  nogood a reader found from the term (`membership/term-nogoods`).

  `:opposing-handles` names every other member of the nogood, for the reason
  `:anti-transitive` names both steps of its chain: the contradiction is not a pair, and
  arbitration that could see only one side of it would defeat the one sentex it could
  name whatever the rest were worth.  A part denied through a separation names the
  membership the separation denies it through (`separation-denial-handles`), the same
  witnesses `provers/DisjointnessNegationProver` answers from.  The declaration is not a
  member (the comment on the map says why).

  **Whether `keep?` takes a cover is read before any part is proved.**  The handles a
  cover's violation names are stored reads, and do not depend on how each part is
  denied, so which covers `keep?` would take is known first.  Those are proved in order,
  and the others only when a kept one is refuted, and then only those before it: the
  first refuted cover is the answer whether it is kept or not.  A refusal path keeps
  only a cover naming no opposing handle (`refuses-assert?`), and a cover with a part the
  membership itself puts `x` in, or a part a stored negation or a separation denies,
  always names one, so such a path asks the provers nothing unless some cover could
  refuse.

  Scoped to the asserting context throughout, as `disjoint-problems` is: the declaration,
  the membership and each negation must be visible from `context`, since a context is
  refused only on grounds it can see."
  [kb sentence context keep?]
  (let [tax  (reasoning/taxonomy kb)
        neg? (sx/negation? sentence)
        lit  (if neg? (second sentence) sentence)]
    (when (and (sequential? lit) (= 1 (nm/arity lit)) (symbol? (nm/functor lit)))
      (let [;; `part` is the part this sentence rules out, or nil when the sentence is
            ;; the whole's own membership.  The two shapes are the two arrival orders an
            ;; entry point sees: the last negation completing a refutation, and the
            ;; membership arriving under negations already stored.
            part (when neg? (nm/functor lit))
            x    (first (nm/args lit))
            ;; A part the membership `(t x)` puts `x` in (`t` or a supertype of it) is
            ;; denied only by a stored negation.  A closed extent's negation as failure
            ;; is withdrawn when a member arrives, and the membership under assertion is
            ;; that member, so reading the denial before it is stored would make the
            ;; arrival order decide.
            stored-only? (fn [p] (and (nil? part)
                                      (or (= p (nm/functor lit))
                                          (tax/genl? tax (nm/functor lit) p context))))
            refuted? (fn [[whole parts]]
                       (budget/check-unit!)
                       (and (or (nil? part)
                                (provers/conjunction-derivable? kb [(list whole x)] {} context))
                            ;; every part *but this one*: on the refusal path the sentence
                            ;; under assertion is not stored yet and holds by assumption,
                            ;; and on the settle path it is stored and would answer here
                            ;; anyway.  The parts denied only by a stored negation first:
                            ;; each is a posting read, and the first one undenied ends the
                            ;; test before a part asks the provers
                            (every? (fn [p]
                                      (budget/check-unit!)
                                      (or (= p part)
                                          (if (stored-only? p)
                                            (seq (negation-handles kb p x context))
                                            (provers/conjunction-derivable?
                                             kb [(list 'not (list p x))] {} context))))
                                    (sort-by (complement stored-only?) parts))))
            violation (fn [[whole parts]]
                        {:type :cover :sentence sentence :types (vec (cons whole parts))
                         ;; The membership, the other negations and the memberships a
                         ;; separation denies a part through (`separation-denial-handles`),
                         ;; and **not** the declaration the conviction is read through —
                         ;; `disjoint`'s rule, for `disjoint`'s reason: a nogood holding
                         ;; the declaration would, on defeating it, read a taxonomy without
                         ;; the cover on the next pass, find no violation, revive the
                         ;; declaration and oscillate.  The evidence is what a refuted
                         ;; cover convicts; the cover is the standing claim it is convicted
                         ;; against.  A separation and the `genl` edges it climbs are
                         ;; grounds in the same way.  Naming the denying membership is what
                         ;; makes a cover refuted through a derived denial arbitrable: the
                         ;; violation names the stored sentexes it is against, so the write
                         ;; is stored and placed rather than refused (docs/nmtms.md, "What
                         ;; a refusal may rest on").
                         :opposing-handles
                         (into (if part (vec (membership-handles kb whole x context)) [])
                               (comp (remove #(= % part))
                                     (mapcat #(if (stored-only? %)
                                                (negation-handles kb % x context)
                                                (concat (negation-handles kb % x context)
                                                        (separation-denial-handles kb % x context))))
                                     (distinct))
                               parts)
                         :message (str "coverage violated: " x " is a " whole
                                       ", which every part of the declared cover "
                                       (str/join ", " parts) " is now denied of")})]
        (when (checkable-term? x)
          ;; one read of the term's memberships for every part a separation is asked to
          ;; deny (`res/*membership-memo*`): nothing is written while the covers are read
          (binding [res/*membership-memo* (or res/*membership-memo* (volatile! {}))]
            (let [decls (if neg?
                          (mapv (fn [[whole parts _]] [whole parts])
                                (tax/covers-naming-visible tax part context))
                          (vec (tax/covers-over tax (nm/functor lit) context)))
                  ;; does `keep?` take a refuted cover naming an opposing handle, and one
                  ;; naming none: what it reads of a cover's violation
                  opposed?   (keep? {:type :cover :opposing-handles [0]})
                  unopposed? (keep? {:type :cover :opposing-handles []})
                  ;; Could `[whole parts]` be refuted naming no opposing handle?  Not
                  ;; with a part only a stored negation denies, nor with a part a stored
                  ;; negation or a separation denies, nor with the whole's membership
                  ;; stored beside a negation: each of those is a handle the violation
                  ;; names.  So of the covers this passes, a refuted one names none, and
                  ;; of the rest a refuted one names some.  Taxonomy and posting reads, no
                  ;; prover.
                  bare? (fn [[whole parts]]
                          (and (not (and part (seq (membership-handles kb whole x context))))
                               (every? (fn [p]
                                         (or (= p part)
                                             (and (not (stored-only? p))
                                                  (empty? (negation-handles kb p x context))
                                                  (empty? (separation-denial-handles kb p x context)))))
                                       parts)))
                  kept? (memoize
                         (cond (and opposed? unopposed?) (constantly true)
                               unopposed?                bare?
                               ;; a `keep?` reading more than the handles
                               :else                     #(boolean (keep? (violation %)))))
                  is    (range (count decls))]
              ;; the first refuted cover is the answer, kept or not: the first refuted
              ;; one `keep?` takes, unless a cover before it it does not take is refuted
              (when-let [j (first (filter #(and (kept? (decls %)) (refuted? (decls %))) is))]
                (when-not (some #(and (not (kept? (decls %))) (refuted? (decls %))) (range j))
                  (violation (decls j)))))))))))

(defn- disjoint-problem
  "The first disjointness clash, for the refusal paths."
  [kb sentence context types]
  (first (disjoint-problems kb sentence context types)))

(defn mergeable-values?
  "Could a functional clash between `x` and `y` be resolved by merging them?  Only when
  both are non-variable symbols, since the equality partition holds symbols; any other
  clash is a nogood the settle decides (docs/equality.md, \"`functional` infers equality
  instead of throwing\")."
  [x y]
  (and (symbol? x) (symbol? y) (not (sx/variable? x)) (not (sx/variable? y))))

(defn- first-per-slot
  "`[handle value via …]` rows with the content-first `via` kept per key, `[handle value]`
  by default.  A super's probe fans down over its specs, so one stored filler comes back
  under every mark above it, and that is one clash.  Lazy, so `functional-problem` reads
  only the first.  `functional-clashes` widens the key to `[handle value position]`,
  since two positions of one sentex are two slots."
  ([triples] (first-per-slot triples (fn [t] [(nth t 0) (nth t 1)])))
  ([triples key-fn] (nm/distinct-by key-fn triples)))

(defn functional-clashes
  "The believed `[handle value via n]` rows that fill a functional slot of `sentence` with
  a value other than its own argument `n` (docs/equality.md, \"`functional` infers
  equality instead of throwing\").  `via` is the marked predicate, the sentence's own or a
  super-predicate the mark descends from (`tax/props-over`), and the slot is probed at
  `via`, so a filler written at either spelling is found.  `(functional P)` constrains
  position 2 of an arity-2 sentence and `(functionalInArg P n)` position `n`; both are
  read and their clashes unioned and deduped (`first-per-slot`).  Empty, on one map read,
  when nothing above the predicate is marked."
  [kb sentence context]
  (let [pred (nm/functor sentence)
        tax  (reasoning/taxonomy kb)
        args (vec (nm/args sentence))
        k    (count args)
        ;; `(q a1 … ?fv … ak)` — the sentence's own arguments with position `n` opened
        ;; up.  At arity 2 with n=2 this is `(q a ?fv)`, the probe the arity-2 path built
        ;; by hand, so the generalization reproduces it rather than replacing it.
        probe (fn [q n] (apply list q (assoc args (dec n) '?fv)))
        ;; `[via position]` pairs constraining this sentence.  The arity-2 mark speaks
        ;; only for arity-2 sentences, exactly as before.  `functionalInArg` speaks
        ;; wherever the declared position is a position this sentence actually has — a
        ;; declaration past the end matches no tuple, which is `arity`'s open-worldness
        ;; and the reason `wff` does not refuse it either.
        marks (into (if (= 2 k)
                      (into #{} (map (fn [q] [q 2]))
                            (tax/props-over tax :functional pred context))
                      #{})
                    (filter (fn [[_ n]] (<= n k)))
                    (tax/functional-in-arg-over tax pred context))]
    (when (seq marks)
      (first-per-slot
       (for [[q n]  (sort marks)
             :let   [b (nth args (dec n))]
             [h bnd] (res/matches-visible kb (probe q n) context)
             :let    [v (get bnd '?fv)]
             :when   (and v (not= v b))]
         [h v q n])
       (fn [t] [(nth t 0) (nth t 1) (nth t 3)])))))

(defn functional-filler
  "The incoming filler a clash row is about: argument `n` of `sentence`."
  [sentence [_ _ _ n]]
  (nth (vec (nm/args sentence)) (dec n)))

(defn functional-declaration-supporters
  "The handles of every declaration constraining `via` at position `n`: the
  `(functional via)` sentexes when `n` is 2 and the `(functionalInArg via n)` sentexes,
  unioned, so a merge survives retracting either spelling."
  [tax via n]
  (into (if (= 2 n) (tax/prop-supporters tax :functional via) #{})
        (tax/functional-in-arg-supporters tax via n)))

(defn- functional-problems
  "The irreconcilable functional clashes of `(P a b)` visible from `context`, as violation
  maps, every one of them, so which pair is reported does not depend on extent order.  A
  symbol clash is left out: it merges or forms a nogood by the members' classes
  (`special/derive-functional-equalities`, `vaelii.impl.decide`).  The message names the
  marked predicate, and the position when it is not 2."
  [kb sentence context]
  (for [[h v via n :as clash] (functional-clashes kb sentence context)
        :let [b (functional-filler sentence clash)]
        :when (not (mergeable-values? v b))]
    {:type :functional :sentence sentence :existing v :new b :opposing-handle h
     :pred via :position n
     :message (if (= 2 n)
                (str "functional violation: " via " of "
                     (first (nm/args sentence)) " is already " v ", not " b)
                (str "functional violation: argument " n " of " via " under "
                     (pr-str (vec (keep-indexed (fn [i a] (when (not= i (dec n)) a))
                                                (nm/args sentence))))
                     " is already " v ", not " b))}))

(defn- functional-problem
  "The first functional clash, for the refusal paths."
  [kb sentence context]
  (first (functional-problems kb sentence context)))

(defn- inherited-opposing
  "`c`, a `:for` claim `inherit/surviving` read for `converse`, as an opposing claim.  A
  claim stated at another tuple reaches `converse` by preservation, and carries the
  reading's handles as `::via` and as `:class` the weakest defeat class of the claim and
  those handles, the reading `discovery/preserving-nogoods` weighs.  With no reading, `c`
  carries no `::via`, and the violation names the claim's own handle alone."
  [kb converse c context]
  (if-let [via (when (not= (:tuple c) (vec (nm/args converse)))
                 (some-> (inherit/claim-reading kb converse c context) vec))]
    (assoc c ::via via
           :class (reduce strength/min (:class c)
                          (map #(or (jtms/defeat-class (reasoning/tms kb) %) :default)
                               via)))
    c))

(defn- asymmetry-problems
  "Every `(asymmetric P)` violation a sentence commits in `context`.

  `(asymmetric largerThan)` says `(P a b)` and `(P b a)` cannot both hold, so a claim
  whose **converse** is known-true is a contradiction rather than an addition.  The
  converse counts whether it was stated directly or reached by argument-position
  preservation — `(largerThan dog cat)` reaches `(largerThan cat maine_coon)` and every
  other pair below it, and a strict claim is exactly as binding there as where it was
  written (`vaelii.impl.inherit`).

  A `:default` generality is something a more specific statement is entitled to
  override: there the inheritance is undercut and never fires, so no clash reaches here.
  A claim reached by preservation opposes at the weakest class of the claim and its
  reading, and names the reading's handles (`inherited-opposing`, docs/inherit.md).

  The violation is the pair `settle` arbitrates: the weaker member loses, a tie at
  `:default` is a dilemma in `(contradictions kb)`, and a tie at `:monotonic` is a hard
  clash in `(conflicts kb)`.

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
  discovery weighs all of them, deduped on the handle, since preservation can reach one
  stored claim by several routes.

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
  does not hand you irreflexivity here — `core.txt` says a self tuple is admitted, and
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
  The two are the same at the entry point and differ wherever `settle` asks a stored sentex's
  question from a *vantage* that sees more than its own context (`reads-clash?`).  Key
  self on the asker instead and the twin **stored in the vantage** is thrown away as
  though the candidate were it: `(P a a)` written in a general context and again in one
  that sees it is a real pair, and whether it is reported turns on which of the two is
  written last — the specific one arriving second convicts from its own context and finds
  its partner, the general one arriving second is asked from the specific vantage and
  discards it.  That is order-dependence in what the KB believes, which
  `clash_oracle_test`'s streams measure and `docs/nmtms.md` forbids.

  Ground binary sentences only; an open or n-ary one has no converse to speak of."
  ([kb sentence context] (asymmetry-problems kb sentence context context))
  ([kb sentence context home]
   (let [pred (nm/functor sentence)
         args (vec (nm/args sentence))]
     (when (and (symbol? pred) (= 2 (count args))
                (every? sx/ground-term? args)
                ;; no predicate carries the mark on nearly every KB: one `:props` set read
                ;; then, and none of what follows is built
                (seq (tax/props (reasoning/taxonomy kb) :asymmetric)))
       (let [marked   (sort (tax/props-over (reasoning/taxonomy kb) :asymmetric pred context))
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
                                              :class (or (jtms/defeat-class (reasoning/tms kb) h)
                                                         :default)})]
                            o (concat (keep #(when (= :for (:polarity %))
                                               (inherited-opposing kb converse % context))
                                            (inherit/surviving kb converse context))
                                      stated)
                            :when (not (and (= self (:sentence o))
                                            (= home (:context o))))]
                        (assoc o ::mark q ::converse converse))
             opposing (->> claims
                           ;; one `nm/print-key` + two `str` in the key — built once per
                           ;; claim, not per comparison; the `[rank …]` tuple orders under
                           ;; `compare`.  Printed through `print-key` because `claims` is
                           ;; a `for` over `res/matches-visible`, an answer *set*, and
                           ;; `asymmetry-problem` takes the first: an elided sentence would
                           ;; decide a refusal on which claim the retrieval yielded first
                           (nm/sort-by-content-key (juxt #(- (strength/rank-of (:class %)))
                                                         #(str (:context %))
                                                         #(nm/print-key (:sentence %))
                                                         #(str (::mark %)))
                                                   compare)
                           (reduce (fn [acc o]
                                     (if (some #(= (:handle %) (:handle o)) acc)
                                       acc
                                       (conj acc o)))
                                   []))]
         (for [o opposing
               :let [q (::mark o) converse (::converse o)]]
           (cond-> {:type :asymmetric :sentence sentence :pred q
                    :opposing (:sentence o) :opposing-handle (:handle o)
                    :message (str "asymmetric: " q " cannot hold both ways, and "
                                  (pr-str (:sentence o))
                                  (if (= :monotonic (:class o)) " is known true" " is believed")
                                  (when (not= (:sentence o) converse)
                                    (str " (which reaches " (pr-str converse)
                                         " by argument preservation)")))}
             (::via o) (assoc :opposing-handles (into [(:handle o)] (::via o))
                              :via (::via o)))))))))

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
  The two argument roots are read for their cardinality alone: they span every predicate
  and either polarity, so they bound the walk rather than describing it.  A non-symbol
  has no root and cannot be led from."
  [kb a b]
  (let [idx  (:index kb)
        wide Long/MAX_VALUE
        out  (if (symbol? a) (reads/stored-count-with-arg-global idx 1 a) wide)
        in   (if (symbol? b) (reads/stored-count-with-arg-global idx 2 b) wide)]
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
  "Every `(anti_transitive P)` violation a sentence commits in `context`.

  `(anti_transitive parentOf)` says a two-step chain forbids the direct step: believing
  `(P a m)` and `(P m c)` makes `(P a c)` contradictory, the dual of `transitive` and the
  reason no predicate is declared both (`(disjoint transitive anti_transitive)`).  So the
  conviction names **two** other believed sentexes rather than one, and the violation
  carries `:opposing-handles` where the pairwise kinds carry `:opposing-handle` —
  `settle` weighs the three together as one nogood (docs/nmtms.md).

  The triple is decided as any nogood is: at equal `:default` class it is a dilemma in
  `(contradictions kb)`, three claims none of which the engine picks between, and at
  equal `:monotonic` class a hard clash in `(conflicts kb)`.

  **The mark is read up the predicate hierarchy** (`tax/props-over`) and the steps are
  probed **at the marked predicate**, exactly as `asymmetry-problems` reads its converse:
  `(anti_transitive parentOf)` with `(genl fatherOf parentOf)` convicts a `fatherOf` chain,
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
  `anti_transitive` does not hand you `irreflexive` any more than `asymmetric` does
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
                (every? sx/ground-term? args)
                ;; no predicate carries the mark on nearly every KB: one `:props` set read
                ;; then, and none of what follows is built
                (seq (tax/props (reasoning/taxonomy kb) :anti-transitive)))
       (let [tms    (reasoning/tms kb)
             [a b]  args
             marked (sort (tax/props-over (reasoning/taxonomy kb) :anti-transitive pred context))
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
                       :message (str "anti_transitive: " q " chains " (pr-str (first chain))
                                     " and " (pr-str (second chain))
                                     ", so the direct step " (pr-str (nth chain 2))
                                     " cannot hold too")})]
         (->> found
              ;; `:chain` is three whole sentences — the longest printed value keyed on
              ;; anywhere here, and the first an ambient `*print-length*` truncates — so
              ;; it is printed through `nm/print-key`.  `antitransitivity-problem` takes
              ;; the first of these, and `found` is a `for` over `res/matches-visible`
              (nm/sort-by-content-key
               (juxt #(- (strength/rank-of (:weakest %)))
                     #(nm/print-key (:chain %))
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

(defn antisymmetric-converses
  "The believed `[handle via]` pairs whose sentence is the converse of `(P a b)` under an
  `(anti_symmetric P)` mark — the facts `(P b a)` that, with the sentence, force
  `(equals a b)`.  Deduped on the converse's handle; `via` is the marked predicate the
  conviction reads through (the sentence's own where it carries the mark, a
  super-predicate where the mark descends), which the equality derivation names in its
  justification.

  The converse is probed **at the marked predicate** and its mark read **up** the
  hierarchy, exactly as `asymmetry-problems` and `functional-clashes` do and for the same
  reason: `(anti_symmetric parentOf)` with `(genl fatherOf parentOf)` must convict a
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
            triples (for [q (sort (tax/props-over (reasoning/taxonomy kb) :anti-symmetric pred context))
                          m (res/matches-visible kb (list q b a) context)]
                      [(first m) nil q])]
        (map (fn [[h _ via]] [h via]) (first-per-slot triples))))))

(defn- matches-pattern-problem
  "A `matchesPattern` literal whose pattern argument is a ground string the regex engine
  cannot compile, or nil.  `EvaluableProver` reads the pattern as a value at query time, so
  an author who mistypes it would otherwise get a goal that silently never matches; this
  reports the compile failure at the assert entry point instead.  Only a ground string
  pattern is judged — a variable pattern is open, like every other undecided argument, and a
  non-string pattern is the `quotedArg` arm's refusal, not this one."
  [sentence]
  (when (= 'matchesPattern (nm/functor sentence))
    (let [pattern (second (nm/args sentence))]
      (when (string? pattern)
        (try (java.util.regex.Pattern/compile pattern) nil
             (catch java.util.regex.PatternSyntaxException e
               {:type :bad-pattern :sentence sentence :pattern pattern
                :message (str "matchesPattern was given a pattern that does not compile: "
                              (.getMessage e))}))))))

(defn- checked-sentence
  "The body the definitional checks see: the double-negation-eliminated positive body,
  so a `(not (not (dog Muffet)))` is still arg/disjoint/functional-checked and a genuine
  negation is not.  A literal whose functor is `symmetric` or declares a commuting group
  is read in the argument order `res/kb-sentex` stores it in, so each argument meets the
  declarations at the position it is stored at, whichever spelling was written.

  The marks are read unscoped: the fold decides the stored key, which every reader
  shares."
  [kb sentence]
  (let [body (or (sx/positive-body sentence) sentence)
        f    (when (sequential? body) (first body))
        tax  (when (symbol? f) (reasoning/taxonomy kb))]
    (if (and tax (or (tax/has-prop? tax :symmetric f) (seq (tax/commuting-groups tax f))))
      (:sentence (res/kb-sentex kb body 'default))
      body)))

(defn- argument-problem
  "The first argument conviction of `chk` in `context` that `keep?` accepts, or nil: the
  arms of the declarations that type an argument (`arg`, `interArg`, the homogeneity
  forms, `genlArg` and the covering forms), in `constraint-problem`'s order."
  [kb chk context types decls keep?]
  (some (fn [arm] (let [p (arm)] (when (and p (keep? p)) p)))
        [#(args-problem kb chk context types decls)
         #(inter-args-problem kb chk context types decls)
         #(inter-args-homogeneity-problem kb chk context types decls)
         #(genls-problem kb chk context decls)
         #(covering-args-problem kb chk context types decls)
         #(covering-genls-problem kb chk context decls)]))

(defn- constraint-problem
  "The first definitional violation for `chk` in `context` that `keep?` accepts, as a
  value, or nil.  The checks are stated once, here, and every path reads them:
  `constraint-checks` (assert) throws the first that `refuses-assert?`,
  `constraint-admission` (derivation) drops a firing for it, and `constraint-violation`
  reports the first of any kind (`some?`).  The arms run in order and stop at the first
  accepted, so an arbitrable clash an early arm finds does not hide a refusal a later arm
  finds.

  `types` is the shared membership reader (`kb/membership-reader`).  The arms that ask
  what types a term holds ask about the same few terms — the sentence's arguments and
  its predicate — and between them ask several times each: `arg` reads an argument's
  twice per constraint, and for a unary sentence the disjointness arm wants the very
  memberships `arg` just read."
  [kb chk context types decls keep?]
  ;; each arm names itself to a pass watching a unit's budget (`budget/unit-phase!`)
  (some (fn [[phase arm]]
          (budget/unit-phase! phase)
          (budget/check-unit!)
          (let [p (arm)] (when (and p (keep? p)) p)))
        [[:pattern     #(matches-pattern-problem chk)]
         [:argument    #(argument-problem kb chk context types decls keep?)]
         [:quoted      #(args-quoted-problem kb chk context types decls)]
         [:application #(application-input-problem kb chk context types decls)]
         [:declaration #(declaration-problem kb chk context types)]
         [:disjoint    #(disjoint-problem kb chk context types)]
         [:cover       #(cover-problem kb chk context keep?)]
         [:asymmetry   #(asymmetry-problem kb chk context)]
         [:functional  #(functional-problem kb chk context)]
         [:antitransitivity #(antitransitivity-problem kb chk context)]]))

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
    (mapv first (tax/reach-support (reasoning/taxonomy kb) :genl pred via context))))

(defn- entailment-support
  "What a derivation through the declaration match `d` rests on besides the sentence it
  is drawn over: the declaration, the `genl` edges it descends through to `pred`
  (`edge-support`), and the `genlCx` edges through which `context` sees it
  (`visibility-support`)."
  [kb pred d context]
  (into [(nth d 0)]
        (concat (edge-support kb pred (declared-of d) context)
                (visibility-support kb (nth d 0) context))))

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
  through and the `genlCx` edges it is seen through (`entailment-support`), so the
  entailment holds only while the subsumption and the sighting that licensed it do.  A
  declaration the context inherits derives as one written there does."
  [kb sentence context decls kind eligible? mint]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))]
    (when (and (symbol? pred) (some eligible? as))
      (for [d     (decls kind)
            :let  [b   (nth d 1)
                   n   (get b '?n)
                   t   (get b '?type)
                   arg (arg-at as n)]
            :when (and arg (eligible? arg)
                       (mintable-type? kb t)
                       ;; A `genlArg` mints `(genl arg t)`, which is not-well-formed when
                       ;; `arg` is `t`.  A reflexive `genl` edge is never well-formed for
                       ;; any `t`, and `arg`/`t` are literal terms, so this is a structural
                       ;; exclusion like `mintable-type?` above rather than a redundancy
                       ;; narrowing.
                       (not (and (= kind 'genlArg) (= arg t))))]
        {:assert  (mint arg t)
         :because (entailment-support kb pred d context)
         :position n :kind kind}))))

(defn- result-arg-entailments
  "The memberships the `(resultArg F n)` declarations visible from `context` draw over the
  `natFormula` fact `sentence` (`result-arg-rows`): `(t K)` for the constant `K`, resting
  on the declaration and the `genlCx` edges `context` sees it through."
  [kb sentence context decls]
  (let [k (second sentence)]
    (when (checkable-term? k)
      (for [[h b] (result-arg-rows decls sentence)
            :let  [t (get b '?type)]
            :when (mintable-type? kb t)]
        {:assert  (list t k)
         :because (into [h] (visibility-support kb h context))
         :position 1 :kind 'resultArg}))))

(defn- inter-arg-entailments
  "The entailments `interArg` draws over `sentence`'s arguments in `context`.

  Exactly as strong as `arg`'s, and drawn under the same condition the check convicts
  on: the trigger argument must be established as a `T`, so the entailment is what the
  declaration says once its antecedent holds.  A dormant constraint entails nothing,
  which is the same asymmetry `inter-args-problem` reads.  One entailment per membership
  establishing the trigger, each naming it under `:trigger` and in `:because`
  (`trigger-supports`); `special/triggered-mints` draws them when the membership
  arrives after the fact.

  Behind the same O(1) presence check `inter-args-problem` is, and for the same reason."
  [kb sentence context types decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))]
    (when (and (symbol? pred) (some checkable-term? as)
               (pos? (reads/stored-count-with-functor (:index kb) 'interArg)))
      (for [d     (decls 'interArg)
            :let  [b       (nth d 1)
                   n       (get b '?n)
                   t       (get b '?type)
                   m       (get b '?m)
                   u       (get b '?utype)
                   trigger (arg-at as n)
                   target  (arg-at as m)]
            :when (and trigger target
                       (checkable-term? trigger) (checkable-term? target)
                       (symbol? t)
                       (kb/isa-among? (types trigger) t)
                       (mintable-type? kb u))
            :let  [because (entailment-support kb pred d context)]
            sup   (trigger-supports kb trigger t context)]
        {:assert  (list u target)
         :because (into because sup)
         :trigger (first sup)
         :position m :kind 'interArg}))))

(defn- covering-entailments
  "The entailments the covering declarations draw over `sentence`'s arguments in
  `context`: `(argAndRest R n T)` derives `(T x)` of every symbol argument from its
  start onward — an `(args R T)` through the `(argAndRest R 1 T)` its forward rule
  stores, which is the support the derivation names — and `(argsGenl R T)` and
  `(argAndRestGenl R n T)` derive `(genl x T)`, as `arg` and `genlArg` derive them of one
  position.  An individual is not given an edge and `(genl T T)` is not drawn, for `arg-entailments`'
  reasons.  This runs behind the `:props` presence check `covering-args-problem` stands
  behind."
  [kb sentence context decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))
        draw (fn [ek rk props eligible? mint]
               (when (covering-declared? kb props)
                 (for [[start t kind d] (covering-triples decls ek rk)
                       :when (mintable-type? kb t)
                       pos   (suffix-positions as start)
                       :let  [x (arg-at as pos)]
                       :when (and (checkable-term? x) (eligible? x t))]
                   {:assert (mint x t) :because (entailment-support kb pred d context)
                    :position pos :kind kind})))]
    (when (and (symbol? pred) (some checkable-term? as))
      (concat (draw nil 'argAndRest [:declares-arg-and-rest-isa]
                    (fn [_ _] true) (fn [x t] (list t x)))
              (draw 'argsGenl 'argAndRestGenl [:declares-args-genl :declares-arg-and-rest-genl]
                    (fn [x t] (and (not (nm/individual? x)) (not= x t)))
                    (fn [x t] (list 'genl x t)))))))

(defn- homogeneity-entailments
  "The entailments `(interArgs R T)` and `(interArgAndRest R n T)` draw over `sentence`'s
  arguments in `context`: every suffix argument established as a `T` is a trigger, and
  derives `T` of every other symbol argument in the suffix, once per membership
  establishing it (`trigger-supports`, named under `:trigger`).  A suffix with no trigger
  draws nothing, which is `inter-arg-entailments`' reading of the trigger.  Each
  spelling's declaration supports its own derivation, so a stated declaration and its
  core.txt-derived twin both justify the one record."
  [kb sentence context types decls]
  (let [pred (nm/functor sentence)
        as   (vec (nm/args sentence))]
    (when (and (symbol? pred) (some checkable-term? as)
               (covering-declared? kb [:declares-inter-args-isa
                                       :declares-inter-arg-and-rest-isa]))
      (for [kind  '[interArgs interArgAndRest]
            d     (decls kind)
            :let  [b     (nth d 1)
                   start (if (= kind 'interArgs) 1 (get b '?start))
                   t     (get b '?type)]
            :when (and (integer? start) (pos? start) (mintable-type? kb t))
            :let  [suffix  (suffix-positions as start)
                   because (delay (entailment-support kb pred d context))]
            n     suffix
            :let  [tx (arg-at as n)]
            :when (and (checkable-term? tx) (kb/isa-among? (types tx) t))
            sup   (trigger-supports kb tx t context)
            pos   suffix
            :let  [x (arg-at as pos)]
            :when (and (checkable-term? x) (not= x tx))]
        {:assert (list t x) :because (into @because sup) :trigger (first sup)
         :position pos :kind kind}))))

(defn- stored-spelling
  "`sentence` as the store keeps it in `context`: a `(symmetric P)` literal's arguments
  sorted, a commuting component arranged (`res/kb-sentex`), anything else as written.

  The entailments a fact meets its declarations with read their positions off this on
  every path, so the assert and derivation paths, which reach them before the sentex
  exists, draw the justifications a later declaration or a reload draws.  An unmarked
  predicate pays two taxonomy reads and no canonicalization.

  The marks are read unscoped: the fold decides the stored key, which every reader
  shares."
  [kb sentence context]
  (let [tax (reasoning/taxonomy kb)
        f   (nm/functor sentence)]
    (if (and (symbol? f)
             (or (tax/has-prop? tax :symmetric f) (seq (tax/commuting-groups tax f))))
      (:sentence (res/kb-sentex kb sentence context))
      sentence)))

(defn constraint-entailments
  "What `sentence`'s visible argument declarations entail about its arguments in
  `context` — a vec of `{:assert <sentence> :because [decl-handle edge-handle …]
  :position n :kind <the declaring functor>}`, empty when they entail nothing.  Every
  entailing kind is read: `arg`, `argArg`, `genlArg`, `interArg`, the covering forms,
  the homogeneity forms and, over a `natFormula` fact, `resultArg`, from a declaration
  written in `context` or inherited by it.

  `(arg parentOf 1 animal)` over `(parentOf Fred Mary)` entails `(animal Fred)`, and
  `(argArg holdsOf 1 2)` over `(holdsOf Rex dog)` entails `(dog Rex)`;
  `(genlArg partType 1 tangible)` over `(partType wheel_kind axle_kind)` entails
  `(genl wheel_kind tangible)`; `(interArg eats 1 carnivore 2 meat)` over
  `(eats Rex Chunk)` entails `(meat Chunk)` — but only once `Rex` is known to be a
  carnivore, which is the condition the declaration is *about*.  An **individual** in an
  `genlArg` position is convicted by `genls-problem` rather than given an edge, so it is
  ineligible here — said at the point it matters rather than relying on the check having
  run first.

  One entry per applicable declaration, with no narrowing for redundancy: see the
  commentary above for why every candidate narrowing would make belief depend on
  arrival order.  Deduplication is the materializer's, where it is keyed on content.

  Drawn over the spelling the store keeps (`stored-spelling`), not the one written: a
  `(symmetric P)` fact names each argument at both positions, and which declaration a
  mint rests on must not turn on how the fact was spelled.

  **Reads only.**  The caller decides whether to store, and the caller is
  `special/deduce-arg-types`, which mints each one as a derived sentex justified by the
  triggering fact and `:because` — so retracting any of them takes the type back."
  ([kb sentence context]
   (constraint-entailments kb sentence context
                           (kb/membership-reader kb context)
                           (declaration-reader kb (nm/functor sentence) context)))
  ([kb sentence context types decls]
   (when *assertive-arg-types?*
     (let [sentence (stored-spelling kb sentence context)]
       (vec (concat (arg-entailments kb sentence context decls 'arg
                                     checkable-term?
                                     (fn [arg t] (list t arg)))
                    ;; `argArg` is `arg` with the type read off this sentence, so its
                    ;; rows go through `arg`'s arm under their own kind
                    (arg-entailments kb sentence context
                                     (let [as (vec (nm/args sentence))]
                                       (fn ([k] (if (= k 'argArg) (vec (arg-arg-rows decls as)) []))
                                         ([op functor] (decls op functor))))
                                     'argArg checkable-term?
                                     (fn [arg t] (list t arg)))
                    ;; `interArgEqual` is `arg` on the sentences its value triggers
                    (arg-entailments kb sentence context
                                     (let [as (vec (nm/args sentence))]
                                       (fn ([k] (if (= k 'interArgEqual) (vec (inter-arg-equal-rows decls as)) []))
                                         ([op functor] (decls op functor))))
                                     'interArgEqual checkable-term?
                                     (fn [arg t] (list t arg)))
                    (result-arg-entailments kb sentence context decls)
                    (arg-entailments kb sentence context decls 'genlArg
                                     #(and (checkable-term? %) (not (nm/individual? %)))
                                     (fn [arg t] (list 'genl arg t)))
                    (inter-arg-entailments kb sentence context types decls)
                    (covering-entailments kb sentence context decls)
                    (homogeneity-entailments kb sentence context types decls)))))))

(defn declaration-entailments
  "`constraint-entailments` narrowed to the declaration stored at `dh`: the entries whose
  `:because` leads with `dh`, drawn from that declaration's match alone.  Every arm draws
  one entry per match, so the other declarations on the predicate are not read, and their
  types are not asked `mintable-type?` once per fact of a sweep over `dh`'s extent.

  With `src`, the handle of the fact stored in a context `context` sees, each `:because`
  also names the `genlCx` edges `context` sees the fact through (`visibility-support`):
  the entailments placed below the fact's own context (`special/pair-placements`)."
  ([kb sentence context dh] (declaration-entailments kb sentence context dh nil))
  ([kb sentence context dh src]
   (let [kind  (nm/functor (:sentence (p/get-sentex (:records kb) dh)))
         decls (declaration-reader kb (nm/functor sentence) context)
         ents  (constraint-entailments kb sentence context (kb/membership-reader kb context)
                                       (fn
                                         ([k] (if (= k kind) (filterv #(= dh (nth % 0)) (decls k)) []))
                                         ([op functor] (decls op functor))))
         seen  (when (and src (seq ents)) (visibility-support kb src context))]
     (if (seq seen)
       (mapv (fn [e] (update e :because #(into % (remove (set %)) seen))) ents)
       ents))))

(def ^:dynamic *prune-subsumed-mints?*
  "Does a minted type give way to a more specific one the KB believes?  With this on,
  `(animal Fred)` minted off `(parentOf Fred Mary)` is withheld while `(dog Fred)` is
  believed and comes back when it goes, which takes about a tenth of the records out of a
  shipped load and changes no answer.  On by default (docs/argtypes.md).

  `binding` it is the ordinary way in, and `VAELII_PRUNE_SUBSUMED_MINTS=0` sets the root
  value off — the parity run that says pruning removes records rather than answers."
  (config/prune-subsumed-mints?))

(defn- subsuming-membership
  "The handle of a believed `(T2 x)` that makes a minted `(t x)` in `context`
  redundant, or nil — `T2` a **strict** subtype of `t` through the edges `context`
  sees, stated where `context` can read it.

  The candidate predicates come from the unary predicate set (`as-stored-unary-predicates`,
  one read), so a term claimed under three types costs three subsumption tests rather
  than a walk of `t`'s whole spec subtree, which on a shipped taxonomy is thousands of
  types with no fact between them.  A predicate holding the term in a fact of another
  arity is not a candidate.

  Belief at `context`, not storage: a `(dog Fred)` `context` takes OUT licenses nothing,
  so the mint it would have made redundant stands.  The visibility test is `sees?` in the direction a read
  takes — a membership stated below `context` is invisible there and subsumes nothing.
  Only a handle `ok?` accepts is answered."
  [kb t x context ok?]
  (let [tax (reasoning/taxonomy kb)]
    (first
     (for [p    (reads/as-stored-unary-predicates (:index kb) x)
           :when (and (symbol? p) (not= p t) (tax/genl? tax p t context))
           h    (reads/as-stored-with-args (:index kb) p {1 x})
           :let [sx (p/get-sentex (:records kb) h)]
           :when (and sx (= (list p x) (:sentence sx))
                      (tax/sees? tax context (:context sx))
                      (res/believed-at? kb h context)
                      (ok? h))]
       h))))

(defn- subsuming-edge
  "The handle of a believed `(genl x S)` that makes a minted `(genl x t)` in `context`
  redundant, or nil — `S` a strict subtype of `t` reaching it through the edges
  `context` sees, so `x` reaches `t` over a route of two edges or more.

  Reachability is what a redundant edge does not change: removing every edge of a
  directed acyclic graph that has another route leaves the same closure, which is why
  dropping them all at once is stable rather than a cascade that eats the route it was
  reading.  The taxonomy refuses a `genl` cycle (`edge-stratification-violation`), so the
  acyclicity the argument rests on is the store's invariant rather than an assumption.

  An edge out of `x` that a `covering`, `separating` or `partition` declaration installs
  (`tax/installed-edges`) is a route like a stated one, so the declaration's handle answers
  too, read off the edge's supporters (`tax/genl-edge-supporters`).  Without it a type
  whose only parent edge comes from a declaration keeps every minted edge to an ancestor, and
  each new justification of that record moves a `genl` edge out of the type.  Only a
  handle `ok?` accepts is answered."
  [kb x t context ok?]
  (let [tax (reasoning/taxonomy kb)
        fits? (fn [h sx] (and (tax/sees? tax context (:context sx))
                              (res/believed-at? kb h context)
                              (ok? h)))]
    (or
     (first
      (for [h    (reads/as-stored-with-args (:index kb) 'genl {1 x})
            :let [sx (p/get-sentex (:records kb) h)
                  s  (when sx (nth (:sentence sx) 2 nil))]
            :when (and sx (= 3 (count (:sentence sx))) (symbol? s)
                       (not= s t) (tax/genl? tax s t context)
                       (fits? h sx))]
        h))
     (first
      (for [s    (sort-by nm/name-key (tax/direct-genls tax x context))
            :when (and (symbol? s) (not= s t) (tax/genl? tax s t context))
            h    (sort (tax/genl-edge-supporters tax x s context))
            :let [sx (p/get-sentex (:records kb) h)]
            :when (and sx (not= 'genl (nm/functor (:sentence sx))) (fits? h sx))]
        h)))))

(defn subsumed-mint
  "The handle of the believed record that already says, more specifically, what the
  minted `sentence` says in `context` — or nil when nothing does.

  The two shapes an argument declaration mints: a membership `(t x)`, subsumed by a
  membership in a subtype of `t`; and a `genl` edge, subsumed by a route of two edges or
  more.  Nil for anything else and nil with the toggle off, so a caller asks without
  testing either first.

  **A read of belief, which is what makes it order-independent.**  Withholding the mint
  while the specific membership is believed and drawing it again when that membership
  leaves is a function of the current state, so the arrival order of the fact, the
  declaration and the specific type cannot decide which records the KB ends up holding —
  the property `every-arrival-order-reaches-the-same-belief` asserts.  What the KB *answers*
  is untouched either way: subsumption reaches `t` from the specific type with or without
  a record in between (docs/argtypes.md).

  With `ok?`, the first subsuming record whose handle `ok?` accepts: a stored mint asks for
  one that does not rest on it (`special/withdrawable-mint`)."
  ([kb sentence context] (subsumed-mint kb sentence context (constantly true)))
  ([kb sentence context ok?]
   (when *prune-subsumed-mints?*
     (cond
       (and (= 1 (nm/arity sentence)) (symbol? (nm/functor sentence))
            (symbol? (first (nm/args sentence))))
       (subsuming-membership kb (nm/functor sentence) (first (nm/args sentence)) context ok?)

       (and (= 'genl (nm/functor sentence)) (= 3 (count sentence))
            (symbol? (nth sentence 1)) (symbol? (nth sentence 2)))
       (subsuming-edge kb (nth sentence 1) (nth sentence 2) context ok?)))))

(defn subsumer-reads
  "The handles whose records `subsumed-mint` can fetch when asked about the minted
  `sentence` in `context`: for `(t x)`, the stored `(p x)` of each unary predicate `p`
  holding `x` other than `t`; for `(genl x t)`, every stored `genl` edge out of `x` and
  the supporters of each edge out of `x` that `context` sees.  A superset, read off the
  index and the taxonomy with no subtype, visibility or belief test, for a caller hinting
  a record store (`special/subsumed-mint-blocks`).  Empty where `subsumed-mint` answers
  nil without a read."
  [kb sentence context]
  (let [idx (:index kb)]
    (when *prune-subsumed-mints?*
      (cond
        (and (= 1 (nm/arity sentence)) (symbol? (nm/functor sentence))
             (symbol? (first (nm/args sentence))))
        (let [t (nm/functor sentence) x (first (nm/args sentence))]
          (for [p (reads/as-stored-unary-predicates idx x)
                :when (and (symbol? p) (not= p t))
                h (reads/as-stored-with-args idx p {1 x})]
            h))

        (and (= 'genl (nm/functor sentence)) (= 3 (count sentence))
             (symbol? (nth sentence 1)) (symbol? (nth sentence 2)))
        (let [tax (reasoning/taxonomy kb)
              x   (nth sentence 1)]
          (concat (reads/as-stored-with-args idx 'genl {1 x})
                  (for [s (tax/direct-genls tax x context)
                        :when (symbol? s)
                        h (tax/genl-edge-supporters tax x s context)]
                    h)))))))

(defn- entailment-cascade
  "Every sentence the argument declarations would mint over `sentence` in `context`, and
  over those mints in turn — `{:mints [sentence …] :readers {functor reader}}`.

  This is the closure `special/entail-arg-type` walks as it materializes, computed here
  before anything is stored.  A mint draws its own entailments and must — the retroactive
  direction cascades whether or not the forward one does — so a check that looked only one
  level down would pass a sentence whose *second* consequence the KB cannot hold.

  **Terminates on `seen`.**  A mint is a `(t x)` or a `(genl x t)` over names the KB
  already holds, so the sentences reachable are a subset of a finite product and each is
  expanded once.  That is `entail-arg-type`'s termination argument, made over sentences
  here rather than over stored records.

  One declaration reader per **functor**, kept and handed back: the walk asks the same
  functor's declarations again for every mint that shares one, and the admissibility pass
  below asks a third time.  A reader memoizes for the life of one caller, so building one
  per sentence would throw the memo away at each step and pay `res/constraining-predicates`
  again for it.

  A membership the cascade itself would add is **not** threaded into `types`: the reader
  answers what is stored, which is what the materializer will read too for every mint but
  the ones this same cascade produces.  A clash between two mints of one cascade is
  found by `settle` once the materializer has placed both.

  Seeded with the caller's own reader and its **already-computed** first level, so the
  common case — a sentence whose declarations mint nothing further — walks an empty
  frontier and costs no retrieval at all.  Building a second reader for the triggering
  functor here read its declarations twice per assert, which `assert_cost_test` counts."
  [kb sentence context types decls seed]
  (let [level (into [] (comp (map :assert) (distinct)) seed)]
    (loop [frontier level
           readers  {(nm/functor sentence) decls}
           seen     (conj (set level) sentence)
           mints    level]
      (if-let [s (first frontier)]
        (let [f'    (nm/functor s)
              rs    (if (contains? readers f')
                      readers
                      (assoc readers f' (declaration-reader kb f' context)))
              es    (constraint-entailments kb s context types (get rs f'))
              fresh (into [] (comp (map :assert) (remove seen) (distinct)) es)]
          (recur (into (vec (rest frontier)) fresh)
                 rs
                 (into seen fresh)
                 (into mints fresh)))
        {:mints mints :readers readers}))))

(defn- write-clash
  "The first disjointness clash between two memberships of one write — `sentence` and
  the `mints` its cascade draws — as a violation naming the other member in
  `:clashes-with`, or nil.  Neither member is stored when the entry point asks, so no
  stored-content reader finds the pair; `try-assert` asks this (`*refuse-clashes?*`)."
  [kb sentence context mints]
  (let [tax (reasoning/taxonomy kb)
        ms  (filterv #(and (= 1 (nm/arity %)) (symbol? (nm/functor %))
                           (not= 'not (nm/functor %)))
                     (cons sentence mints))]
    (first
     (for [a ms
           :let [disjoint? (tax/separation-test tax (nm/functor a) context)]
           :when disjoint?
           b ms
           :when (and (not= a b) (= (nm/args a) (nm/args b)) (disjoint? (nm/functor b)))]
       {:type :disjoint :sentence b :types [(nm/functor b) (nm/functor a)]
        :entailed-from sentence
        :clashes-with [{:sentence a :context context}]
        :message (str "arg constraint: " (nm/print-key sentence) " entails "
                      (nm/print-key b) ", disjoint from " (nm/print-key a))}))))

(defn- entailment-check
  "The entailment reading's half of the entry point check:
  `{:entailments [{:assert …} …] :refusal v}` — what `sentence`'s argument declarations
  draw over it, and the first consequence of those declarations the KB could not admit.
  Nil with the toggle off, which is `constraint-entailments`' answer there.

  **The refusal sits on the consequence.**  With the entailment on, `args-problem`'s
  symbol arm yields (`entailment-covers?`), so a wrongly-typed symbol argument is not a
  violation: the declaration says what the argument is.  A *consequence* still can be one
  — a minted membership clashing with a disjoint one —
  so the entry point refuses `sentence` exactly when it would refuse what `sentence`
  entails.  The constraint reading's rule, moved one step along the derivation.

  **Asked before the store.**  `special/entail-arg-type` asks the same question of each
  mint as it materializes, and it runs after the triggering sentex exists — so a mint
  whose violation names no opposing sentex is *dropped* and recorded, and the KB is left
  believing a fact whose declared consequence it rejects.  Asked here, the refusal reaches
  the writer and nothing is stored.  A clash with a believed membership, or between two
  mints of one cascade, refuses nothing: the materializer places each mint and `settle`
  decides the nogood the mints form.

  The violation handed back is the **mint's own**, with the sentence that entailed it in
  `:entailed-from`: what could not be held is what a reader is told, rather than a second
  wording of the argument constraint.

  Naming, well-formedness and edge stratification are **not** asked, only the definitional
  checks: those three live above this namespace, where `special/inadmissible` asks all
  four as one question, and a mint they convict is dropped and reported by the
  materializer.

  One walk of the declarations serves both halves.  The first level is what the caller
  materializes and is also the cascade's seed, so asking `constraint-entailments` again
  for the answer already in hand would read the triggering functor's declarations twice
  per assert — a cost `assert_cost_test` counts."
  [kb sentence context types decls]
  (when *assertive-arg-types?*
    (let [seed (constraint-entailments kb sentence context types decls)]
      ;; The common assert draws no entailment (its functor carries no visible
      ;; declaration).  An empty seed makes the cascade's frontier empty, so `mints` is
      ;; exactly the seed and the refusal `keep` over it is nil — computing the cascade
      ;; and the `keep` at all is the same `{:entailments [] :refusal nil}` reached
      ;; without reading anything.
      (if (empty? seed)
        {:entailments seed :refusal nil}
        (let [{:keys [mints readers]} (entailment-cascade kb sentence context types decls seed)]
          {:entailments seed
           :refusal
           (or (first
                (keep (fn [m]
                        ;; a mint a stored, more specific membership withholds is never
                        ;; stored, and that membership was admitted under every
                        ;; declaration over `m`'s type (`special/entail-arg-type`)
                        (when-let [p (and (not (subsumed-mint kb m context))
                                          (constraint-problem kb m context types
                                                              (get readers (nm/functor m))
                                                              entry-refuses?))]
                          (assoc p :entailed-from sentence
                                 :message (str "arg constraint: " (nm/print-key sentence)
                                               " entails " (nm/print-key m)
                                               ", which cannot be admitted — " (:message p)))))
                      mints))
               (when *refuse-clashes?* (write-clash kb sentence context mints)))})))))

(defn- refusal
  "The ex-info `constraint-checks` throws for violation `v` found in `context`: `v` under
  its own `:type`, or, for a clash that only `*refuse-clashes?*` refuses and for an
  argument conviction under it, `:definitional-clash` with the clash kind in
  `:violation`, each other member in `:clashes-with`, as `{:handle :sentence :context}`
  when it is stored and without `:handle` when it is part of the write (`write-clash`),
  and the kind's own keys in `:detail`.  An argument conviction's members are the
  memberships of its `:disjoint-with` type."
  [kb context v]
  (if (or (arbitrable? v) (contains? v :clashes-with)
          (and *refuse-clashes?* (contains? argument-conviction-kinds (:type v))))
    (ex-info (str "definitional clash: " (:message v))
             {:type          :definitional-clash
              :violation     (:type v)
              :sentence      (:sentence v)
              :entailed-from (:entailed-from v)
              :clashes-with  (into (vec (:clashes-with v))
                                   (map (fn [h]
                                          (let [s (p/get-sentex (:records kb) h)]
                                            {:handle h :sentence (sx/sentence-of s)
                                             :context (:context s)})))
                                   (concat (opposing-handles v)
                                           (when-let [t' (:disjoint-with v)]
                                             (membership-handles kb t' (:arg v)
                                                                 (or (:placed-in v) context)))))
              :detail        (dissoc v :weighed? :message :sentence :entailed-from :clashes-with
                                     :opposing-handle :opposing-handles :type)})
    (ex-info (:message v) (dissoc v :message :weighed?))))

;; ---- the argument constraints a rule's variables carry -------------------
;;
;; `args-problem` holds a **ground** argument to what its position declares.  Every
;; argument of a rule is a variable, so that arm passes over all of them vacuously and
;; the rule is stored — and then each fact the rule concludes is convicted one at a
;; time, by a complaint naming the conclusion and never the rule that wrote it.
;;
;; A variable is one term standing in several positions at once, though, so the
;; positions can be held to **each other** before anything fires.  A variable an
;; antecedent binds through `(arg comment 2 string)` and a consequent places
;; into `(genl ?x ?string)` has to be a run of text and a type at the same time, and
;; text and a type are declared disjoint: no term is both, so every firing of that rule
;; would conclude something the argument checks convict.  `assert` stores such a rule and
;; the argument family holds it in the `:out` forced set (`argument-conviction`), in
;; every arrival order of the rule and its declarations, and `try-assert` refuses it
;; (docs/argtypes.md, "A rule whose variable no term can fill is held inert").
;;
;; **A type-level position asks for a type, which is a `unary_predicate`.**  That is the
;; second reading this arm needs and the KB already holds it: every type is asserted a
;; `unary_predicate` when the schema loads.  So a position a `genlArg` names asks for a
;; `unary_predicate`.  A position of a `type_relation_predicate` asks for what the
;; predicate's `argAndRest` declarations name, `predicate` from core.txt's `(args ?relation
;; predicate)`, because `genl` relates predicates of any arity: `(genl performedBy doneBy)`
;; puts one binary predicate under another.  A position no `argAndRest` covers carries no
;; relation-kind constraint, so a KB that does not load core.txt types none.  That reading
;; is how `genl`'s arguments are constrained at all; they carry no position declaration of
;; their own, deliberately (see core.txt).
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
;;
;; **`arg`, `genlArg`, and `quotedArg` at a kind whose expressions denote themselves.**
;; A `quotedArg` demand at `string` or `number`, or below one, asks for a literal of that
;; kind, and a literal is an instance of its kind, so the demand convicts against an
;; instance demand its kind is separated from (`self-denoting-kinds`).  The arm convicts
;; no other pair:
;;
;;   - `quotedArg` at any other kind, against `arg` or a type-level position.  A
;;     `symbol` expression denotes the term the `arg` side types, and a compound's
;;     expression kind says nothing of its denotation, so both ends accept a binding.
;;   - `quotedArg` × `quotedArg`.  The arm reads no pair of two quoted demands, and a
;;     rule whose two quoted demands no literal meets is stored and believed.
;;   - `interArg`.  Its trigger is a *demand*, not a fact.  `(arg P i T)` does not make
;;     argument `i` a `T` — an unclassified term satisfies it vacuously — so no rule's
;;     own bindings entail the trigger, and a conditional constraint that never provably
;;     fires can convict nothing.
;;   - `arg` × `genlArg` beyond the `unary_predicate` mapping below.  A term may be an
;;     instance of one type and a subtype of another at once; the meta-ontology depends
;;     on it, every type being an instance of `unary_predicate`.
;;
;; Each of those has a witness in `rule_variable_arg_test`, so an extension has to turn
;; one red before it can land.  docs/taxonomy.md carries the same list for a reader.

(def ^:private collection-type
  "The type a **type-level** argument position asks its filler to be an instance of.
  Every type in the KB is asserted a `unary_predicate` as the schema loads, so this is
  what `genlArg`'s \"a subtype of T\" amounts to as a membership, and a membership is
  what `disjoint` separates."
  'unary_predicate)

(defn- binding-literals
  "The literals of rule `inner` that **bind** its variables: every positive antecedent,
  plus the consequent."
  [inner]
  (conj (into []
              (remove #(or (sx/negation? %) (sx/unknown? %) (sx/there-exists? %)))
              (rules/antecedents inner))
        (rules/consequent inner)))

(def ^:private self-denoting-kinds
  "The value kinds whose literals denote themselves.  A `quotedArg` demand at one of these,
  or at a type below one, asks for a literal that is an instance of the demanded type, so
  the rule arm reads it as an instance demand (`literal-variable-constraints`)."
  '[string number])

(defn- self-denoting?
  "Is the type `t` one of `self-denoting-kinds` or below one, as seen from `context`?"
  [tax t context]
  (boolean (some #(or (= t %) (tax/genl? tax t % context)) self-denoting-kinds)))

(defn- literal-reader
  "`[decls type-rel?]` for the functor `pred` read from `context`: its
  `declaration-reader`, and whether `pred` is a `type_relation_predicate` there."
  [kb pred context]
  (pass-read [pred context]
             #(vector (declaration-reader kb pred context)
                      (boolean (seq (res/matches-visible kb (list 'type_relation_predicate pred) context))))))

(defn- pending-constraints
  "The constraints an argument declaration not yet stored places on the variables `as`
  of a literal on `pred`, read from `context`.  `dm` is the declaration's demand
  (`declaration-demand`); it binds the literal when its predicate is `pred` or above it.
  A conditional demand, `interArg`'s or `interArgEqual`'s, places none."
  [tax dm pred as context]
  (when (and dm (nil? (:trigger-pos dm))
             (or (= pred (:pred dm)) (tax/genl? tax pred (:pred dm) context)))
    (let [n (:pos dm)
          a (arg-at as n)
          c {:position n :pred pred :via (:pred dm)}]
      (when (sx/variable? a)
        (case (:kind dm)
          :arg-type        [[a (assoc c :type (:type dm) :level :arg)]]
          :arg-genl        [[a (assoc c :type collection-type :level :genlArg)]]
          :quoted-arg-type (when (self-denoting? tax (:type dm) context)
                             [[a (assoc c :type (:type dm) :level :quoted)]])
          nil)))))

(defn- literal-variable-constraints
  "The memberships one literal demands of the variables sitting in its arguments, as
  `[[variable {:type T :position n :pred P :via V :level :arg|:genlArg|:kind|:quoted}] …]`.

  Four sources.  An `(arg P n T)` declaration types the filler directly.  A
  **type-level** position, one a `genlArg` names, types it as a `unary_predicate`, since
  what stands there is a kind.  Any position of a `type_relation_predicate` is typed by
  each `argAndRest` declaration covering it, `predicate` from core.txt's `(args ?relation
  predicate)`; a position none covers carries no relation-kind constraint.  A
  `(quotedArg P n T)` at a type `self-denoting?` accepts types it as a `T` literal, which
  is an instance of `T`.  `pending`, when given, is the demand of a declaration not yet
  stored, read as stored (`pending-constraints`).  `:level` is kept so the message can
  say which reading it read, and `:via` so a constraint that descended
  from a super-predicate names the predicate it was written of, exactly as `args-problem`
  does.

  Walked in `in-content-order`, so which declaration a conviction names is decided by what
  the KB says rather than by how the retrieval happened to enumerate.

  A literal whose **functor is itself a variable** contributes nothing.  `?pred` names no
  predicate, so `declaration-reader` reads it as a match pattern and every `(arg P n T)`
  in the KB comes back — `(arg typeToInstancePred 2 instance_relation_predicate)` beside
  `(arg instantNotEqual 2 time_point)` — and the conjunction of two unrelated predicates' position 2
  is a demand no term meets.  A variable functor is refused `:not-indexable` where it
  stands as a top-level antecedent (`rules.clj`) and is filled by a generator's hole
  otherwise, so the declarations that bind it are the generated rule's, read when the
  functor is ground."
  [kb lit context pending]
  (let [pred (nm/functor lit)
        as   (vec (nm/args lit))]
    (when (and (sequential? lit) (symbol? pred) (not (sx/variable? pred))
               (some sx/variable? as))
      (let [tax             (reasoning/taxonomy kb)
            [decls type-rel] (literal-reader kb pred context)
            of-kind         (fn [kind mk]
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
         (filter (fn [[_ c]] (self-denoting? tax (:type c) context))
                 (of-kind 'quotedArg
                          (fn [m b n] {:type (get b '?type) :position n :pred pred
                                       :via (declared-of m) :level :quoted})))
         (when type-rel
           (let [tails (for [m     (in-content-order (decls 'argAndRest))
                             :let  [b (nth m 1) s (get b '?start) t (get b '?type)]
                             :when (and (integer? s) (pos? s) (symbol? t) (not (sx/variable? t)))]
                         [s t (declared-of m)])]
             (for [[i a] (map-indexed vector as)
                   :when (sx/variable? a)
                   :let  [n (inc i)]
                   [s t via] tails
                   :when (<= s n)]
               [a {:type t :position n :pred pred :via via :level :kind}])))
         (pending-constraints tax pending pred as context))))))

(defn- variable-constraints
  "`variable -> [{…} …]` over `literals`, in literal order — the whole of what a rule's
  own text, its declarations and the `pending` demand say its variables have to be."
  [kb literals context pending]
  (reduce (fn [acc lit]
            (reduce (fn [acc [v c]] (update acc v (fnil conj []) c))
                    acc
                    (literal-variable-constraints kb lit context pending)))
          {} literals))

(defn- variable-constraint-clause
  "How a conviction names one constraint it found — **a string (arg 2 of
  comment)**, **a predicate (arg 2 of genl, a type_relation_predicate)** for a position
  whose demand comes from the relation kind rather than from a position declaration, or **a
  string literal (arg 1 of p, constrained with quotedArg)**.  Carries `via-clause` for a
  constraint that descended from a super-predicate, exactly as `args-problem`'s message
  does."
  [{:keys [type position pred via level]}]
  (str (case level
         :arg     (str "a " type)
         :genlArg "a type"
         :kind    (str "a " type)
         :quoted  (str "a " type " literal"))
       " (arg " position " of " pred
       (case level
         :genlArg (str ", constrained with genlArg" (via-clause via pred))
         :quoted  (str ", constrained with quotedArg" (via-clause via pred))
         :kind    ", a type_relation_predicate"
         (via-clause via pred))
       ")"))

(defn- variable-clash-problem
  "The first pair of constraints on one of rule `inner`'s variables that no term
  satisfies at once, read from `context`, or nil.  `pending` is an optional declaration
  demand read as stored (`pending-constraints`).

  Only two **instance** demands can convict: `disjoint` says two types share no
  instance, and a membership is what each of these constraints asks for — the
  `unary_predicate` a type-level position asks for included.  A pair of two quoted
  demands is not read.  Variables are taken in name order and each one's constraints in
  literal-then-content order, so a rule several of whose variables clash is convicted for
  the same one every time."
  ([kb inner context] (variable-clash-problem kb inner context nil))
  ([kb inner context pending]
   (let [taxo   (reasoning/taxonomy kb)
         by-var (variable-constraints kb (binding-literals inner) context pending)]
     (first
      ;; `name-key`, not `str`: a rule variable is a symbol, and saying so is what keeps
      ;; the key out of the class an ambient `*print-length*` can collapse
      (for [v     (sort-by nm/name-key (keys by-var))
            :let  [cs (get by-var v)]
            :when (< 1 (count cs))
            [i a] (map-indexed vector cs)
            b     (drop (inc i) cs)
            :when (and (not= (:type a) (:type b))
                       (not (= :quoted (:level a) (:level b)))
                       (pass-read [::disjoint (:type a) (:type b) context]
                                  #(tax/disjoint? taxo (:type a) (:type b) context)))]
        {:type :arg-variable :sentence inner :variable v
         :expected [(:type a) (:type b)]
         :message (str "arg constraint: " v " must be " (variable-constraint-clause a)
                       " and " (variable-constraint-clause b)
                       ", and the two types are disjoint")})))))

(defn- check-variable-constraints!
  "Under `*refuse-clashes?*`, throw `:definitional-clash` with `:violation :arg-variable`
  when a variable of rule `inner` carries two argument constraints no term can satisfy
  together (`variable-clash-problem`).  Otherwise nothing: `assert` stores the rule and
  holds it inert (`argument-conviction`)."
  [kb inner context]
  (when *refuse-clashes?*
    (when-let [p (variable-clash-problem kb inner context)]
      (throw (refusal kb context (assoc p :clashes-with []))))))

(defn- rules-on
  "The handles of the stored rules with an antecedent or a consequent on one of the
  predicates `preds`, read over every context: the rules a declaration on one of `preds`
  can constrain the variables of (`variable-clash-problem`).  The read covers every
  context because the handles are a candidate superset, each decided again from its own
  context (`rule-conviction`)."
  [kb preds]
  (let [idx (:index kb)]
    (for [p preds
          h (concat (reads/as-stored-rules-by-antecedent-global idx p)
                    (reads/as-stored-rules-by-consequent-global idx p))]
      h)))

(defn- declared-positions-global
  "`[{position #{type …}} kind-types]` for the functor `pred`, read as stored over every
  context: the type each `arg`, `genlArg` or `quotedArg` declaration on `pred` or a
  predicate above it places on a position, as `literal-variable-constraints` reads it,
  and, when a membership states `pred` a `type_relation_predicate` or a type below it,
  the set of every `argAndRest` type on `pred` or above it, which bounds what that
  reading places on any position (nil otherwise).
  A superset of what `literal-reader` reads from any one context.  The declaring
  predicates above `pred` are read off one memo per kind for the pass
  (`tax/genls-global-among`), so a pass costs the `genl` edges above its functors once
  rather than a closure per functor."
  [kb tax pred]
  (let [idx    (:index kb)
        hint   (pass-read ::prefetcher #(cap/prefetcher (:records kb)))
        by-pos (for [kind  '[arg genlArg quotedArg]
                     :let  [declaring (tax/props tax (tax/arg-declaration-props kind))]
                     sup   (when (seq declaring)
                             (tax/genls-global-among tax pred declaring
                                                     (pass-read [::declaring kind declaring] #(volatile! {}))))
                     f     (tax/specs-global tax kind)
                     h     (cap/hinting hint cap/recovery-hint-chunk
                                        (reads/as-stored-with-args idx f {1 sup}))
                     :let  [s (:sentence (p/get-sentex (:records kb) h))
                            [_ _ n t] s]
                     :when (and (seq? s) (= 4 (count s)) (symbol? t) (not (sx/variable? t)))
                     ty    (case kind
                             arg       [t]
                             genlArg   [collection-type]
                             quotedArg (when (some #(or (= t %) (tax/genl?-global tax t %)) self-denoting-kinds)
                                         [t]))]
                 [n ty])
        type-rel? (boolean (some #(seq (reads/as-stored-with-args idx % {1 pred}))
                                 (tax/specs-global tax 'type_relation_predicate)))]
    [(reduce (fn [m [n t]] (update m n (fnil conj #{}) t)) {} by-pos)
     (when type-rel?
       (into #{}
             (let [declaring (tax/props tax (tax/arg-declaration-props 'argAndRest))]
               (for [sup (when (seq declaring)
                           (tax/genls-global-among tax pred declaring
                                                   (pass-read [::declaring 'argAndRest declaring] #(volatile! {}))))
                     f   (tax/specs-global tax 'argAndRest)
                     h   (reads/as-stored-with-args idx f {1 sup})
                     :let [[_ _ _ t :as s] (:sentence (p/get-sentex (:records kb) h))]
                     :when (and (seq? s) (= 4 (count s)) (symbol? t) (not (sx/variable? t)))]
                 t))))]))

(defn- clash-possible?
  "Can a reader at some context read a clash between two constraints on one of rule
  `inner`'s variables (`variable-clash-problem`)?  The constraints are read over every
  context as stored (`declared-positions-global`), and a pair is tested unscoped with no
  `siblingDisjointException` (`tax/separation-test`), so false means no context
  convicts the rule.  Each read, a type's test among them, is held in `*pass-reads*`."
  [kb inner]
  (let [tax    (reasoning/taxonomy kb)
        by-var (reduce
                (fn [acc lit]
                  (let [pred (nm/functor lit)
                        as   (nm/args lit)]
                    (if (and (sequential? lit) (symbol? pred) (not (sx/variable? pred))
                             (some sx/variable? as))
                      (let [[by-pos kind-types] (pass-read [::declared pred] #(declared-positions-global kb tax pred))]
                        (reduce (fn [acc [i a]]
                                  (if (sx/variable? a)
                                    (update acc a (fnil into #{})
                                            (into (set (get by-pos (inc i))) kind-types))
                                    acc))
                                acc (map-indexed vector as)))
                      acc)))
                {} (binding-literals inner))]
    (boolean
     (some (fn [ts]
             (let [ts (vec ts)]
               (some (fn [i]
                       (when-let [test (pass-read [::separation (ts i)]
                                                  #(tax/separation-test tax (ts i) nil (constantly false)))]
                         (some #(pass-read [::separated (ts i) %] (fn [] (test %)))
                               (subvec ts (inc i)))))
                     (range (count ts)))))
           (vals by-var)))))

(defn- rule-conviction
  "`variable-clash-problem` of the stored rule `sx`, read from its own context, with the
  variable in the rule's author spelling where its varmap names one, or nil.  Under a
  pass (`*pass-reads*`), a rule `clash-possible?` clears is not read from its context."
  [kb sx]
  (let [inner (rules/inner-rule (sx/sentence-of sx))]
    (when-let [p (when (or (nil? *pass-reads*) (clash-possible? kb inner))
                   (variable-clash-problem kb inner (:context sx)))]
      (update p :variable #(get (:varmap sx) % %)))))

;; ---- a declaration against the tuples it constrains ------------------------

(def ^:private named-tuple-count
  "How many convicted tuples `declaration-conflict` names."
  10)

(defn- declaration-demand
  "What the argument declaration `chk` demands of its predicate's tuples, or nil:
  `{:kind :pred :pos :type}`, the kind being the violation a tuple breaking it is
  convicted of, with `:trigger-pos` and `:trigger-type` for an `interArg` and
  `:trigger-pos` and `:trigger-value` for an `interArgEqual`, which demands what `arg`
  does of the tuples its value triggers.  `arg1`, `arg2` and `arg3` read as `arg` at
  their position."
  [chk]
  (let [[f pred a b c d] chk
        n (nm/arity chk)
        m (case f
            arg              (when (= 3 n) {:kind :arg-type :pos a :type b})
            (arg1 arg2 arg3) (when (= 2 n) {:kind :arg-type :pos ('{arg1 1 arg2 2 arg3 3} f) :type a})
            genlArg          (when (= 3 n) {:kind :arg-genl :pos a :type b})
            quotedArg        (when (= 3 n) {:kind :quoted-arg-type :pos a :type b})
            interArg         (when (= 5 n) {:kind :inter-arg-type :pos c :type d
                                            :trigger-pos a :trigger-type b})
            interArgEqual    (when (and (= 5 n) (pos-int? a))
                               {:kind :arg-type :pos c :type d :trigger-pos a :trigger-value b})
            nil)]
    (when (and m (symbol? pred) (not (sx/variable? pred)) (pos-int? (:pos m))
               (symbol? (:type m)) (not (sx/variable? (:type m))))
      (assoc m :pred pred))))

(defn- breaks-demand?
  "Does the argument `x`, read from `context`, break the demand `dm` at its position?  The
  fact direction's per-argument test: a separated type for `arg` and an `interArg`
  target (`outside-declared-type?`, which also convicts a value for `arg`), a type the
  taxonomy separates from the declared one or an individual outside the hierarchy for
  `genlArg` (`genls-problem`'s individual floor), and a kind outside the declared
  syntactic type for `quotedArg` (`quoted-outside?`).  The individual floor is a global
  read (`tax/genl?-global`) for `genls-problem`'s reason (E17_ALLOW)."
  [kb {:keys [kind type]} tax types x context]
  (case kind
    :arg-type       (outside-declared-type? kb tax types x type context)
    :inter-arg-type (and (checkable-term? x) (separated-type tax types x type context))
    :arg-genl       (and (checkable-term? x)
                         (if (tax/genl? tax x 'thing context)
                           ((tax/disjointness-test tax type context) x)
                           (and (nm/individual? x) (not (tax/genl?-global tax x 'thing)))))
    :quoted-arg-type (quoted-outside? kb tax x type context)))

(defn- declaration-conflict
  "The definitional clash the argument declaration `chk` written in `context` forms with
  the believed tuples it constrains, as a violation of the declaration's kind naming up
  to ten tuples in `:clashes-with` and the count in `:count`, or nil.  `try-assert` asks
  this (`*refuse-clashes?*`); `assert` stores the declaration.

  The tuples are those of the declared predicate and of each predicate below it through
  `genl`, stated in a context `context` sees or one that sees `context`.  The predicates
  below are read over every context (`tax/specs-global`), since a `genl` edge stated below
  `context` relates them there, and each tuple's predicate is tested from the tuple's
  vantage.  The test is the
  fact direction's (`breaks-demand?`), asked once per distinct atomic argument at the
  position and context: the trie children at the position, read in every context because
  the trie keys the context last (`reads/as-stored-atoms-at-global`), then each
  argument's contexts narrowed to those two sets.  Only a convicted argument's tuples are
  read.  A value at the position has no argument root, so the tuples holding one are read
  off the functor in those contexts and each is tested.  A tuple in a context
  `context` sees is read from `context`, and one below it from its own context.  An
  `interArg` tuple is convicted only where its trigger argument believes the trigger
  type, and an `interArgEqual` tuple only where its trigger argument is the value."
  [kb chk context]
  (when-let [{:keys [pred pos type trigger-pos trigger-type trigger-value] :as dm} (declaration-demand chk)]
    (let [tax     (reasoning/taxonomy kb)
          idx     (:index kb)
          recs    (:records kb)
          tms     (reasoning/tms kb)
          up      (set (tax/context-up tax context))
          seen    (into up (tax/context-down tax context))
          memo    (volatile! {})
          readers (fn [v] (or (get @memo v)
                              (let [r (kb/membership-reader kb v)] (vswap! memo assoc v r) r)))
          vantage (fn [c] (if (contains? up c) context c))
          tuple?  (fn [s types]
                    (and s (nil? (:antecedent s)) (not (sx/negative? s)) (jtms/in? tms (:id s))
                         (or (nil? trigger-pos)
                             (let [tr (arg-at (vec (nm/args (:sentence s))) trigger-pos)]
                               (if trigger-type
                                 (and tr (checkable-term? tr)
                                      (kb/isa-among? (types tr) trigger-type))
                                 (= trigger-value tr))))))
          ;; every predicate below `pred` in some context, each tuple's predicate tested
          ;; from its vantage: a `genl` edge stated below `context` puts a predicate
          ;; under `pred` there
          specs   (nm/sort-by-content-key nm/name-key compare (tax/specs-global tax pred))
          under?  (fn [p v] (or (= p pred) (tax/genl? tax p pred v)))
          atoms   (for [p     specs
                        x     (nm/sort-by-content-key nm/print-key compare
                                                      (filter sx/indexable-term?
                                                              (reads/as-stored-atoms-at-global idx p pos)))
                        c     (nm/sort-by-content-key nm/name-key compare
                                                      (reads/as-stored-contexts-with-arg-in idx p pos x seen))
                        :let  [v     (vantage c)
                               types (readers v)]
                        :when (and (under? p v) (breaks-demand? kb dm tax types x v))
                        h     (reads/as-stored-with-args-in idx p {pos x} #{c})
                        :let  [s (p/get-sentex recs h)]
                        :when (tuple? s types)]
                    s)
          ;; a value has no argument root, so its tuples are read off the functor
          values  (for [p     specs
                        :let  [vs (into #{} (remove sx/indexable-term?)
                                        (reads/as-stored-atoms-at-global idx p pos))]
                        :when (seq vs)
                        h     (reads/as-stored-with-functor-in idx p seen)
                        :let  [s (p/get-sentex recs h)
                               x (some-> s :sentence nm/args vec (arg-at pos))]
                        :when (contains? vs x)
                        :let  [v     (vantage (:context s))
                               types (readers v)]
                        :when (and (under? p v) (breaks-demand? kb dm tax types x v) (tuple? s types))]
                    s)
          broken  (concat atoms values)
          n       (count broken)]
      (when (pos? n)
        (let [named (take named-tuple-count
                          (nm/sort-by-content-key #(nm/print-key [(:sentence %) (:context %)])
                                                  compare broken))]
          {:type (:kind dm) :sentence chk :position pos :expected type :count n
           :clashes-with (mapv (fn [s] {:handle (:id s) :sentence (:sentence s) :context (:context s)})
                               named)
           :message (str "arg constraint: " (nm/print-key chk) " is broken by " n
                         " stored tuple" (when (< 1 n) "s") " at argument " pos ", among them "
                         (nm/print-key (:sentence (first named))))})))))

(defn- rule-declaration-conflict
  "The first stored, believed rule that the argument declaration `chk` written in `context`
  would convict, read with `chk`'s demand as stored (`variable-clash-problem`), as an
  `:arg-variable` violation naming the rule in `:clashes-with`, or nil.  `try-assert` asks
  this (`*refuse-clashes?*`).  The rules read are those on the declared predicate and the
  predicates below it (`rules-on`), stated in `context` or a context below it, in content
  order, each read from its own context.  The predicates below are read over every
  context (`tax/specs-global`), since a `genl` edge stated below `context` relates them
  there, and each rule's predicate is tested from the rule's own context."
  [kb chk context]
  (when-let [{pred :pred :as dm} (declaration-demand chk)]
    (let [tax  (reasoning/taxonomy kb)
          recs (:records kb)
          down (set (tax/context-down tax context))]
      (first
       (for [rsx   (->> (for [p    (tax/specs-global tax pred)
                              rsx  (keep #(p/get-sentex recs %) (rules-on kb [p]))
                              :let [c (:context rsx)]
                              :when (and (contains? down c)
                                         (or (= p pred) (tax/genl? tax p pred c)))]
                          rsx)
                        distinct
                        (filter #(res/rule-believed? kb (:id %)))
                        (nm/sort-by-content-key (juxt sx/sentence-of :context)))
             :let  [v (variable-clash-problem kb (rules/inner-rule (sx/sentence-of rsx)) (:context rsx) dm)]
             :when v]
         (assoc v :sentence chk
                :clashes-with [{:handle (:id rsx) :sentence (sx/sentence-of rsx) :context (:context rsx)}]
                :message (str "arg constraint: " (nm/print-key chk) " convicts the stored rule "
                              (nm/print-key (sx/sentence-of rsx)) " — " (:message v))))))))

(def ^:private argument-declaring-kinds
  "The declaration kinds `argument-problem` reads, as `declaration-queries` keys."
  '[arg genlArg interArg interArgEqual args argsGenl argAndRest argAndRestGenl interArgs
    interArgAndRest])

(defn- below-declaration-conflict
  "The first argument conviction of `chk` read from a context below `context` that holds
  a declaration binding `chk`'s tuples, as a violation carrying that context in
  `:placed-in`, or nil.  `try-assert` asks this (`*refuse-clashes?*`): a declaration
  `context` does not see places its derived membership in the context below that sees
  both (docs/argtypes.md, \"Where a mint is placed\"), and the conviction there is the
  clash that membership forms.  Only the declarations `context` does not see are read
  there.  The declarations are read off each kind's argument root
  at the predicate and the predicates above it, narrowed to the contexts below
  `context`, so a context with no descendant reads nothing.  The predicates above are
  read over every context (`tax/genls-global`), since a `genl` edge stated below
  `context` puts the predicate under a declared one there; `argument-problem` reads each
  context's own edges."
  [kb chk context]
  (let [tax  (reasoning/taxonomy kb)
        pred (nm/functor chk)
        down (disj (set (tax/context-down tax context)) context)
        up   (set (tax/context-up tax context))]
    (when (and (symbol? pred) (seq down))
      (let [idx  (:index kb)
            recs (:records kb)
            cs   (into (sorted-set-by #(compare (nm/name-key %1) (nm/name-key %2)))
                       (for [k argument-declaring-kinds
                             ;; every predicate above `pred` in some context: a `genl`
                             ;; edge stated below `context` puts `pred` under a declared one
                             ;; there, and `argument-problem` reads each context's own
                             p (cons pred (tax/genls-global tax pred))
                             h (reads/as-stored-with-args-in idx k {1 p} down)
                             :let [dsx (p/get-sentex recs h)]
                             :when dsx]
                         (:context dsx)))]
        (some (fn [c]
                (let [decls (declaration-reader kb pred c)
                      below (fn
                              ([k] (filterv #(not (contains? up (:context (nth % 2)))) (decls k)))
                              ([op functor] (decls op functor)))]
                  (some-> (argument-problem kb chk c (kb/membership-reader kb c) below some?)
                          (assoc :placed-in c))))
              cs)))))

(defn- complement-conflict
  "The `:complement` violation for the ground literal `sentence` written in `context`: a
  believed match of its complement (`(not S)` for a positive `S`, `S` for a denial) that
  `res/matches-visible` answers from `context`, whose handle `res/holding-class` reads
  `:monotonic` and whose path to the complement crosses only `genl` and `genlInverse`
  edges the reader holds at `:monotonic` (`res/contrapositive-predicates`).  Each such
  match is named in `:clashes-with`, in content order; nil when there is none.

  A positive forced-monotonic literal (`decide/forced-literal?`) is never refused here:
  it wins the negation nogood against its denial at either class (docs/nmtms.md, \"The
  forced-monotonic set\").  `try-assert` asks this (`*refuse-clashes?*`); `assert` stores
  the rebuttal and `settle` weighs it."
  [kb sentence context]
  (let [tax  (reasoning/taxonomy kb)
        s    (:sentence (res/kb-sentex kb sentence context))
        neg? (sx/negation? s)
        body (if neg? (second s) s)
        f    (when (sequential? body) (nm/functor body))]
    (when (and (symbol? f) (not= sx/not-functor f)
               (or neg? (not (decide/forced-literal? tax s))))
      (let [cmp   (if neg? body (list sx/not-functor body))
            args  (vec (nm/args body))
            class (res/holding-class kb)
            ;; a match on `q` entails the complement through `q ⊑ f` (a positive
            ;; complement) or `f ⊑ q` (a denial), straight or with arguments 1 and 2
            ;; exchanged.  Either orientation holds when `context` believes `q` or `f`
            ;; symmetric.
            held? (fn [x]
                    (let [mb       (sx/underlying-body (:sentence x))
                          q        (nm/functor mb)
                          margs    (vec (nm/args mb))
                          swapped? (and (= 2 (count args)) (not= margs args) (= margs (rseq args)))
                          sym?     (or (tax/has-prop? tax :symmetric q context)
                                       (tax/has-prop? tax :symmetric f context))
                          [sub super] (if neg? [q f] [f q])
                          [straight swapped] (res/contrapositive-predicates kb sub context)]
                      (or (and (= q f) (or sym? (not swapped?)))
                          (contains? (if swapped? swapped straight) super)
                          (and sym? (contains? (if swapped? straight swapped) super)))))
            hits  (->> (res/matches-visible kb cmp context)
                       (keep (fn [[h _ x]]
                               (when (and (= :monotonic (class h)) (held? x))
                                 {:handle h :sentence (sx/sentence-of x) :context (:context x)})))
                       (distinct)
                       (nm/sort-by-content-key #(nm/print-key [(:sentence %) (:context %)]) compare))]
        (when (seq hits)
          {:type :complement :sentence s
           :clashes-with hits
           :message (str "complement: " (nm/print-key s) " clashes with "
                         (nm/print-key (:sentence (first hits))) ", believed :monotonic")})))))

(defn- length-conflict
  "The `:arity` violation for the positive tuple `chk` (`arity/fact-shape`) whose length
  breaks its functor's (`arity/broken-binding`), naming the bindings that state the length
  in `:opposing-handles`, or nil.  `assert` stores such a tuple in the `:out` forced set."
  [kb chk _context _strength]
  (when (sequential? chk)
    (when-let [[q n] (arity/fact-shape {:sentence (seq chk)})]
      (when-let [{:keys [length via route grounds] floor :min} (arity/broken-binding kb q n)]
        (cond-> {:type :arity :sentence chk :arguments n :via via :route route
                 :clashes-with [] :opposing-handles grounds
                 :message (str "arity: " (nm/print-key chk) " has " n " arguments, and " q
                               (if length (str " takes " length) (str " takes at least " floor))
                               (when (not= q via) (str ", bound through " via)))}
          length (assoc :length length)
          floor  (assoc :min floor))))))

(defn- mark-handles
  "The handles of the IN `(F q)` marks stating taxonomy prop `kind` of `q` that `context`
  sees, in content order of their contexts."
  [kb kind q context]
  (let [tax (reasoning/taxonomy kb)
        tms (reasoning/tms kb)]
    (->> (tax/prop-supporter-contexts tax kind q)
         (filter (fn [[h c]] (and (jtms/in? tms h) (or (nil? c) (tax/sees? tax context c)))))
         (nm/sort-by-content-key #(str (val %)) compare)
         (mapv key))))

(defn- self-tuple-conflict
  "The `:irreflexive` violation for the ground self tuple `chk` (`tuple/self-tuple?`) of a
  predicate at or below an `irreflexive` mark `context` sees (`tuple/convicting`), naming
  the mark in `:opposing-handles`, or nil.  `assert` stores the tuple and the settle places
  it as a one-member nogood."
  [kb chk context _strength]
  (let [tax (reasoning/taxonomy kb)]
    (when (and (seq (tax/props tax :irreflexive)) (sequential? chk)
               (tuple/self-tuple? {:sentence (seq chk)}))
      (when-let [q (first (tuple/convicting tax :irreflexive [(nm/functor chk)] context))]
        {:type :irreflexive :sentence chk :pred q
         :clashes-with [] :opposing-handles (mark-handles kb :irreflexive q context)
         :message (str "irreflexive: " (nm/print-key chk) " relates a term to itself, and "
                       q " is irreflexive")}))))

(defn- converse-conflict
  "The `:anti-symmetric` violation for the ground binary tuple `chk` (`tuple/binary-tuple`)
  of two distinct arguments whose believed converses under an `anti_symmetric` mark
  `context` sees (`antisymmetric-converses`) do not merge the two (`tuple/merges?`, the
  write `:monotonic` at `strength` or as a forced-monotonic literal), naming each such
  converse in `:opposing-handles` in content order, or nil.  `assert` stores the tuple and
  the settle places the pair."
  [kb chk context strength]
  (let [tax (reasoning/taxonomy kb)]
    (when (and (seq (tax/props tax :anti-symmetric)) (sequential? chk))
      (when-let [[a b] (tuple/binary-tuple {:sentence (seq chk)})]
        (when (not= a b)
          (let [tms   (reasoning/tms kb)
                recs  (:records kb)
                mono? (or (= :monotonic strength) (decide/forced-literal? tax chk))
                hits  (->> (antisymmetric-converses kb chk context)
                           (remove (fn [[h]] (tuple/merges? a b mono? (tuple/monotonic-member? tms h))))
                           (nm/sort-by-content-key
                            (fn [[h via]] (let [x (p/get-sentex recs h)]
                                            (nm/print-key [(:sentence x) (:context x) via])))
                            compare))]
            (when-let [[h via] (first hits)]
              {:type :anti-symmetric :sentence chk :pred via
               :clashes-with [] :opposing-handles (mapv first hits)
               :message (str "anti_symmetric: " (nm/print-key chk) " and "
                             (nm/print-key (:sentence (p/get-sentex recs h)))
                             " relate two distinct terms both ways, and " via
                             " is anti_symmetric")})))))))

(def fact-clash-checks
  "The checks `try-assert` asks of a fact a declaration constrains, as `[violation check]`
  in the order asked, each `(check kb sentence context strength)` answering a violation or
  nil.  A grammar entry's `:clash-checks` `:fact` names one by its violation
  (`predicates/clash-checks`)."
  [[:arity length-conflict]
   [:irreflexive self-tuple-conflict]
   [:anti-symmetric converse-conflict]])

(def ^:private positional-declaration-functors
  "The declarations `declared-positions` reads positions off, less the projections
  `arg1`…`arg5`, each stored beside its `arg` twin."
  '[arg genlArg interArg interArgEqual argArg])

(defn- stranding-conflict
  "The `:arg-position` violation for a write that binds a relation's length so that
  stored, believed declarations on it name a position past that length
  (`arity/write-lengths`), each convicted under the length the write gives and not under
  the stored one, as `arg-position-problem` reads a declaration.  It names up to ten in
  `:clashes-with` and their number in `:count`, or nil.  A relation's length is read the
  same at every context, so a declaration in any context counts, and the declaring
  predicates are read off the KB-wide `tax/props` sets, each declaration then read for
  belief."
  [kb chk mono?]
  (let [tax     (reasoning/taxonomy kb)
        idx     (:index kb)
        recs    (:records kb)
        tms     (reasoning/tms kb)
        memo    (volatile! {})
        readers (fn [c] (or (get @memo c)
                            (let [r (kb/membership-reader kb c)] (vswap! memo assoc c r) r)))
        props   (mapv #(tax/props tax (tax/arg-declaration-props %)) positional-declaration-functors)
        stranded
        (for [[f b] (arity/write-lengths kb chk mono? (fn [f] (some #(contains? % f) props)))
              :when (:exact b)
              k     positional-declaration-functors
              h     (reads/as-stored-with-args idx k {1 f})
              :let  [sx (p/get-sentex recs h)]
              :when (and sx (nil? (:antecedent sx)) (not (sx/negative? sx)) (jtms/in? tms h))
              :let  [d     (:sentence sx)
                     types (readers (:context sx))]
              :when (and (some #(false? (provers/admits-position? (variable-arity? types f) (:exact b) %))
                               (declared-positions d))
                         (nil? (position-problem kb d types)))]
          {:handle h :sentence d :context (:context sx)})
        n (count stranded)]
    (when (pos? n)
      (let [named (take named-tuple-count
                        (nm/sort-by-content-key #(nm/print-key [(:sentence %) (:context %)])
                                                compare stranded))]
        {:type :arg-position :sentence chk :count n :clashes-with (vec named)
         :message (str "arg constraint: " (nm/print-key chk) " binds a length that strands " n
                       " stored declaration" (when (< 1 n) "s") ", among them "
                       (nm/print-key (:sentence (first named))))}))))

(defn- relation-kind-conflict
  "The `:arg-constraint-kind` violation for a write `chk` in `context` that completes a
  pair of a `genlArg` declaration on a predicate `P` and a membership `(T P)` with `T` at
  or below `instance_relation_predicate`, or nil.  The write is the membership, the
  declaration, or a `genl` edge `(genl A B)` with `B` at or below
  `instance_relation_predicate` and `T` at or below `A`.  The other members are stored
  and believed, each stated in a context `context` sees or one that sees `context`.  It
  names up to ten of the memberships for a declaration, else of the declarations, in
  `:clashes-with`, and their number in `:count`.  `try-assert` asks this
  (`*refuse-clashes?*`); `assert` stores the write.  See docs/taxonomy.md."
  [kb chk context]
  (let [tax     (reasoning/taxonomy kb)
        irp     'instance_relation_predicate
        sym?    #(and (symbol? %) (not (sx/variable? %)))
        [f a b] (when (sequential? chk) chk)
        k       (when (sequential? chk) (nm/arity chk))
        ;; declarers and the types below irp are KB-wide supersets; `stored` keeps the
        ;; candidates that are positive literals the JTMS labels in
        declarers (tax/props tax (tax/arg-declaration-props 'genlArg))
        write   (cond
                  (and (= 1 k) (sym? f) (sym? a) (contains? declarers a))   :membership
                  (and (= 'genlArg f) (= 3 k) (sym? a) (pos-int? b))       :declaration
                  (and (= 'genl f) (= 2 k) (sym? a) (sym? b) (seq declarers)
                       (or (= irp b) (contains? (set (tax/specs-global tax irp)) b))) :edge)]
    (when write
      (let [recs    (:records kb)
            idx     (:index kb)
            tms     (reasoning/tms kb)
            seen    (into (set (tax/context-up tax context)) (tax/context-down tax context))
            stored  (fn [hs keep?]
                      (for [h hs
                            :let [sx (p/get-sentex recs h)]
                            :when (and sx (nil? (:antecedent sx)) (not (sx/negative? sx))
                                       (keep? (:sentence sx)) (jtms/in? tms h))]
                        {:handle h :sentence (:sentence sx) :context (:context sx)}))
            decls   (fn [q] (stored (reads/as-stored-with-args-in idx 'genlArg {1 q} seen)
                                    (fn [[_ _ n]] (pos-int? n))))
            members (fn [q] (stored (reads/as-stored-with-args-in idx nil {1 q} seen)
                                    #(and (= 1 (nm/arity %)) (sym? (nm/functor %)))))
            under?  (if (= :edge write)
                      (fn [t v] (and (or (= a t) (tax/genl? tax t a v))
                                     (or (= irp b) (tax/genl? tax b irp v))))
                      (fn [t v] (or (= irp t) (tax/genl? tax t irp v))))
            ;; each pair as [membership declaration], nil standing for the write
            pairs   (case write
                      :membership  (for [d (decls a)] [nil d])
                      :declaration (for [m (members a)] [m nil])
                      :edge        (for [q declarers
                                         m (members q)
                                         d (decls q)]
                                     [m d]))
            hits    (for [[m d] pairs
                          :let  [t (if m (nm/functor (:sentence m)) f)
                                 v (tax/seeing-member tax (into #{context} (keep :context) [m d]))]
                          :when (and v (under? t v))]
                      (if (= :declaration write) m d))
            hs      (distinct hits)
            n       (count hs)]
        (when (pos? n)
          (let [named (take named-tuple-count
                            (nm/sort-by-content-key #(nm/print-key [(:sentence %) (:context %)])
                                                    compare hs))
                q     (if (= :edge write) (second (:sentence (first named))) a)]
            {:type :arg-constraint-kind :sentence chk :predicate q :count n
             :clashes-with (vec named)
             :message (str (nm/print-key chk) " makes " q " an instance_relation_predicate"
                           " constrained by genlArg, against " n " stored "
                           (if (= :declaration write) "membership" "genlArg declaration")
                           (when (< 1 n) "s") ", among them "
                           (nm/print-key (:sentence (first named))))}))))))

(defn- length-declaration-conflict
  "The violation for a write that moves a relation's length (`arity/write-lengths`, the
  write `:monotonic` at `strength` or as a forced-monotonic literal): a length binding, a
  `genl` edge, or a `:monotonic` metatype membership or edge.  `:arity` where stored
  tuples, each believed as its own context reads it (`exc/believed-own?`), break the
  length (`arity/write-breaks`), naming each shape in `:shapes` with its believed count,
  the tuples in `:count` and the relations in `:relations`; for an `except` of a stored
  length binding, `:arity` naming the binding in `:opposing-handles`; else
  `:arg-position` where it strands stored declarations (`stranding-conflict`).  Else nil.
  `assert` stores the write: the settle holds the tuples inert, an except of a binding
  leaves the length bound, and a stranded declaration constrains nothing."
  [kb chk _context strength]
  (if-let [h (kb/except-target chk)]
    (when (arity/binding-handle? kb h)
      {:type :arity :sentence chk :excepted h :clashes-with [] :opposing-handles [h]
       :message (str "arity: " (nm/print-key chk) " hides the length binding "
                     (nm/print-key (:sentence (p/get-sentex (:records kb) h)))
                     ", and a relation's length stays bound at every context")})
    (when (sequential? chk)
      (let [mono?  (or (= :monotonic strength) (decide/forced-literal? (reasoning/taxonomy kb) chk))
            tms    (reasoning/tms kb)
            hid    (exc/own-hidden-fn kb)
            shapes (arity/write-breaks kb (seq chk) mono?
                                       #(and (jtms/in? tms %) (not (and hid (hid %)))))]
        (if (seq shapes)
          (let [n    (transduce (map :count) + shapes)
                rels (count (into #{} (map :relation) shapes))
                {:keys [relation arguments]} (first shapes)]
            {:type :arity :sentence chk :count n :relations rels :shapes shapes :clashes-with []
             :message (str "arity: " (nm/print-key chk) " breaks the length of " n " stored tuple"
                           (when (< 1 n) "s") " of " rels " relation" (when (< 1 rels) "s")
                           ", among them " relation " at " arguments " arguments")})
          (stranding-conflict kb (seq chk) mono?))))))

(defn- self-tuple-declaration-conflict
  "The `:irreflexive` violation for the mark `(irreflexive P)` written in `context` over
  the believed self tuples (`reads/as-stored-self-tuples`) of `P` and of each predicate
  below it as seen from the tuple's vantage, stated in a context `context` sees or one
  that sees `context`.  The predicates below are read over every context
  (`tax/specs-global`), since a `genl` edge stated below `context` relates them there.  It names up to ten of them in `:clashes-with` and their number in `:count`.
  Else nil.  `assert` stores the mark, and the settle places each tuple as a one-member
  nogood."
  [kb chk context _strength]
  (when (and (sequential? chk) (= 'irreflexive (first chk)) (= 2 (count chk))
             (symbol? (second chk)) (not (sx/variable? (second chk))))
    (let [q    (second chk)
          tax  (reasoning/taxonomy kb)
          tms  (reasoning/tms kb)
          idx  (:index kb)
          up   (set (tax/context-up tax context))
          seen (into up (tax/context-down tax context))
          recs (:records kb)
          ;; a tuple's predicate is tested below `q` from its vantage, as
          ;; `declaration-conflict` tests it
          hs   (into #{} (comp (mapcat #(reads/as-stored-self-tuples idx % seen))
                               (filter #(jtms/in? tms %))
                               (filter #(let [sx (p/get-sentex recs %)
                                              f  (nm/functor (:sentence sx))
                                              v  (if (contains? up (:context sx)) context (:context sx))]
                                          (or (= f q) (tax/genl? tax f q v)))))
                     (tax/specs-global tax q))]
      (when (seq hs)
        (let [named (->> hs
                         (keep #(p/get-sentex (:records kb) %))
                         (nm/sort-by-content-key #(nm/print-key [(:sentence %) (:context %)]) compare)
                         (take named-tuple-count))]
          {:type :irreflexive :sentence chk :pred q :count (count hs)
           :clashes-with (mapv (fn [s] {:handle (:id s) :sentence (:sentence s) :context (:context s)})
                               named)
           :message (str "irreflexive: " (nm/print-key chk) " convicts " (count hs)
                         " stored self tuple" (when (< 1 (count hs)) "s") ", among them "
                         (nm/print-key (:sentence (first named))))})))))

(def declaration-clash-checks
  "The checks `try-assert` asks of a declaration that constrains stored facts, as
  `[violation check]` in the order asked, each `(check kb sentence context strength)`
  answering a violation or nil.  A grammar entry's `:clash-checks` `:declaration` names
  one by its violation (`predicates/clash-checks`)."
  [[:arity length-declaration-conflict]
   [:irreflexive self-tuple-declaration-conflict]])

(defn constraint-checks
  "Throw the first definitional violation that `refuses-assert?`, as typed ex-info — the
  assert path.  Under `*refuse-clashes?*`, the first violation of any kind (`refusal`),
  `fact-clash-checks` and `declaration-clash-checks` asked first, with `strength` the
  write's (`:default` when not given).

  A violation naming the other believed members of its nogood does not refuse: the
  sentence is stored and `settle` decides the nogood, whatever the members' classes.  An
  admitted clash is **not** reported here — settle discovers it from the relabelled
  region, which is what makes the discovery route-agnostic and the answer the same in
  every arrival order.  An argument conviction `assert` holds inert (`held-inert?`) does
  not refuse either: it is returned under `:conviction`, and the caller holds the stored
  fact in the `:out` forced set (`argument-conviction`).

  Returns `{:entailments [...] :conviction v}`: the **entailments** the argument
  constraints draw over an admissible sentence (`constraint-entailments`), for the caller
  to materialize once the sentex it would be justified by exists, empty unless
  `*assertive-arg-types?*`, and the held conviction or nil.

  **Two questions, not one, once the entailment is on.**  The sentence has to be
  admissible and so does everything it entails (`entailment-check`) — the argument
  declarations are read as definitions there, so admitting `(parentOf Rex Mary)` is
  admitting `(animal Rex)`, and a KB that cannot hold the second may not be left holding
  the first.  Asked second, and only when the sentence itself passed: a sentence already
  refused needs no second reason, and the cascade is the more expensive read of the two."
  ([kb sentence context] (constraint-checks kb sentence context :default))
  ([kb sentence context strength]
   (let [chk   (checked-sentence kb sentence)
         types (kb/membership-reader kb context)
         decls (declaration-reader kb (nm/functor chk) context)
         p     (or (when *refuse-clashes?*
                     (some (fn [[_ check]] (check kb chk context strength))
                           (concat fact-clash-checks declaration-clash-checks)))
                   (constraint-problem kb chk context types decls entry-refuses?)
                   (when *refuse-clashes?*
                     (or (below-declaration-conflict kb chk context)
                         (declaration-conflict kb chk context)
                         (relation-kind-conflict kb chk context)
                         (rule-declaration-conflict kb chk context)
                         (complement-conflict kb sentence context))))
         ;; an argument conviction `assert` holds inert, and a later arm's refusal behind it
         held  (when (and (not *refuse-clashes?*) (held-inert? p)) p)
         p     (if held (constraint-problem kb chk context types decls fact-refuses?) p)]
     (if p
       (throw (refusal kb context p))
       (let [ec (entailment-check kb chk context types decls)]
         (if-let [p (:refusal ec)]
           (throw (refusal kb context p))
           {:entailments (:entailments ec) :conviction held}))))))

(defn check-length-binding
  "Throw when the length binding `sentence` states (`sx/arity-binding`) disagrees with
  what the sentence alone shows.  For an engine grammar term, a binding that does not
  admit every length its shape admits (`arity/admits-shape?`) is `:length-against-shape`,
  carrying `:relation` and `:shape`, whatever `policy`.  For any other relation, a
  binding against its spelling is `nm/check-binding!`'s, under the `:naming` policy
  `policy`."
  [policy sentence context]
  (when-let [[q kind v] (sx/arity-binding sentence)]
    (if-let [shape (arity/shape-length q)]
      (when-not (arity/admits-shape? q kind v)
        (throw (ex-info (str (pr-str sentence) " binds " q " to " v
                             (case kind
                               :exact (if (= 1 v) " argument" " arguments")
                               :min   " arguments or more")
                             ", but " q " is engine vocabulary whose shape takes "
                             (if (:exact shape)
                               (:exact shape)
                               (str (:min shape) " or more")))
                        {:type :length-against-shape :sentence sentence :context context
                         :relation q :shape (select-keys shape [:exact :min])})))
      (nm/check-binding! policy sentence context))))

(defn check-application-inputs
  "Throw the first violation of a function's argument declarations inside `sentence` in
  `context` — `application-input-problem`, asked of a fact **before** the reify pass.

  `assert` mints every ground reifiable application into its constant before
  `constraint-checks` runs, and the constant carries the function's result types, not
  what the application was given: the inputs are gone by the time the arm that reads
  them could look.  So the assert path asks this first, over the sentence as written,
  from the writer's vantage — the same reading `constraint-checks` gives an unreifiable
  application after the pass, and the one `check` gives both, since `check` does not
  mint.  Asked before the mint, a refused sentence leaves no constant behind.

  Nil for a sentence with no compound argument, before any reader is built."
  [kb sentence context]
  ;; the raw sentence's arguments first: a fact with no compound argument has none under
  ;; any `not` either, and asking this before `checked-sentence` keeps the common fact
  ;; off the canonicalization that reads through its negations
  (when (and (sequential? sentence) (some application-term? (rest sentence)))
    (let [chk (checked-sentence kb sentence)]
      (when (and (symbol? (nm/functor chk)) (some application-term? (nm/args chk)))
        (let [p (application-input-problem kb chk context
                                           (kb/membership-reader kb context)
                                           (declaration-reader kb (nm/functor chk) context))]
          (when (entry-refuses? p)
            (throw (refusal kb context p))))))))

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
  *absence* of a fact rather than on a second one to weigh against.

  An argument conviction `assert` holds inert (`held-inert?`) is not a violation here
  either, unless it convicts a function application's input, which
  `check-application-inputs` refuses at `assert`.  The answer then carries it under
  `:conviction`, as a `{:violation :detail}` map beside the entailments, and the caller
  stores the conclusion and holds it (`hold-argument-conviction!`)."
  [kb sentence context]
  (let [chk   (checked-sentence kb sentence)
        types (kb/membership-reader kb context)
        decls (declaration-reader kb (nm/functor chk) context)
        held? #(and (held-inert? %) (not (:application %)))
        p     (constraint-problem kb chk context types decls refuses-assert?)
        held  (when (held? p) p)
        p     (if held
                (constraint-problem kb chk context types decls #(and (refuses-assert? %) (not (held? %))))
                p)]
    (if p
      {:violation {:violation (:type p) :detail (dissoc p :type :sentence)}}
      (cond-> {:entailments (constraint-entailments kb chk context types decls)}
        held (assoc :conviction {:violation (:type held) :detail (dissoc held :type :sentence)})))))

(defn derivation-violation
  "`constraint-admission`'s violation half alone: nil when `sentence` is admissible in
  `context` or its only violation is arbitrable, else the `{:violation :detail}` map.
  The argument-type mint reads this, so a mint clashing with a believed membership is
  placed and weighed at settle as a rule's conclusion is (docs/argtypes.md)."
  [kb sentence context]
  (let [chk (checked-sentence kb sentence)]
    (when-let [p (constraint-problem kb chk context (kb/membership-reader kb context)
                                     (declaration-reader kb (nm/functor chk) context)
                                     refuses-assert?)]
      {:violation (:type p) :detail (dissoc p :type :sentence)})))

(defn conviction-watch
  "The term whose memberships can lift the argument conviction `v` (a `{:violation
  :detail}` map), as the `{:term}` field a waiting entry carries: the convicted argument,
  whose separating membership leaving, or whose membership arriving under `quotedArg`'s
  kind lattice, can lift the conviction.

  Read off the conviction the entry is decided under, every time it is decided.  A
  re-ask that is still convicted can be convicted on a different argument — an
  application with two targets outside the type names the first, and once that one is
  lifted it names the second — and an entry left watching the first would never be
  re-asked when the second is lifted, so the lifting order would decide whether the
  firing is ever placed."
  [v]
  {:term (get-in v [:detail :arg])})

(defn constraint-violation
  "The definitional checks as a value alone: nil when `sentence` is admissible in
  `context`, else `{:violation :arg-type|:arg-genl|:arg-position
  |:arg-constraint-kind|:disjoint|:asymmetric|:functional|:anti-transitive
  :detail {...}}`.

  **Every** violation, arbitrable ones included — which is what separates this from
  `constraint-admission`.  The callers are the checks on content that is never stored
  when it fails: `special/inadmissible`'s default arity, read by what `abduce` may assume
  and by a context-valued function's computed `genlCx` edge.  Content the engine stores
  on its own behalf (a lift's copy, a merge's twin, an argument-type mint) asks
  `derivation-violation` instead, so its arbitrable clash is stored and decided at each
  reader."
  [kb sentence context]
  (let [chk   (checked-sentence kb sentence)
        types (kb/membership-reader kb context)
        decls (declaration-reader kb (nm/functor chk) context)]
    (when-let [p (constraint-problem kb chk context types decls some?)]
      {:violation (:type p) :detail (dissoc p :type :sentence)})))

(defn arg-position-violation
  "The `:arg-position` violation the **stored declaration** `sentence` commits in
  `context`, or nil — a constraint on a position its predicate does not have
  (`position-problem`, through `checked-sentence` as at the entry point).  The reader is
  `vaelii.impl.integrity`'s `stranded-declarations`: a stranded declaration constrains
  nothing and mints nothing, so it is a sweep question rather than a settle one
  (docs/taxonomy.md)."
  ([kb sentence context]
   (arg-position-violation kb sentence context (kb/membership-reader kb context)))
  ([kb sentence _context types]
   (position-problem kb (checked-sentence kb sentence) types)))

(defn check-sentex-ground
  "`check-ground` over `s`, the sentex already built from `sentence` in `context`: throw
  `:not-ground` when `s` is not a rule and has a free variable, unless `sentence` is a
  schematic equation or a `defn*` definition.  A variable inside a `(Quote …)` or bound
  by a quantifier is not free (`sx/closed?`)."
  [s sentence context]
  (when (and (nil? (:antecedent s)) (not (sx/closed? s))
             (not (rewrite/schematic-equation? sentence))
             ;; a `defn*` collection definition carries the member variable `?x` in
             ;; its condition argument, the way a schematic equation carries its schema
             ;; variables — it is stored to retract and belief-follow, and it expands
             ;; into the rules where those variables belong (docs/defns.md)
             (not (sx/defn-sentence? sentence)))
    (throw (ex-info (str "not ground: " (pr-str sentence)
                         " contains a variable — a fact must be ground"
                         " (write a universal claim as a rule)")
                    {:type :not-ground :sentence sentence :context context}))))

(defn check-ground
  "Reject a non-rule sentence that still contains pattern variables.

  A fact asserts something; `(mortal ?x)` asserts nothing — it is an open formula, not
  a sentence.
  Stored as a premise it is worse than useless: `unify` matches it against any goal,
  so it silently behaves as a universally quantified fact that nothing ever licensed.
  Universal claims are written as rules, where `check-range-restricted` governs the
  variables.

  Rule-ness is read off the **canonicalized record**, not off the raw input: an
  `implies`, a `set/*Rule` wrapper, and a nested combination of the two all
  canonicalize into `:antecedent`, and pattern-matching the input would have to
  re-derive that (and would miss a spelling).

  A **schematic equation** `(equals (fatherOf (fatherOf ?x)) (grandfather_of ?x))` is
  the deliberate exception: its variables belong to a term-rewriting schema, not to an
  open fact, so it is stored as an oriented rewrite rule rather than refused
  (docs/equality.md, symbolic equational reasoning).  It is not matched as a fact
  under `unify` — its functor is `equals`, read by the equality machinery, not by the
  fact prover for arbitrary goals.

  `check-sentex-ground` is the same check over a sentex already built, which is what a
  dump import holds."
  [kb sentence context]
  (check-sentex-ground (res/kb-sentex kb sentence context) sentence context))

(defn check-except-target
  "Refuse a visibility `(except (sentexHandle H))` when no sentex is stored under H
  (`:unknown-handle`).  Handles are allocated in assertion order, so every except this
  admits names a handle below its own, and the except graph `assert` builds is acyclic.
  A target retracted after its except leaves the except naming nothing, and a handle is
  never reissued (docs/contexts.md, except)."
  [kb sentence]
  (when-let [h (kb/except-target sentence)]
    (when (nil? (p/get-sentex (:records kb) h))
      (throw (ex-info (str "except names handle " h ", and no sentex is stored under it")
                      {:type :unknown-handle :handle h :sentence sentence})))))

;; ---- the forced-monotonic set ------------------------------------------

(def uncleared-forcing
  "The forced-monotonic declarations whose retraction is refused, each with the semantics the
  declared predicate has no unforced reading of: `[declaration-functor predicate]` ->
  missing semantics (docs/nmtms.md, \"The forced-monotonic set\")."
  (into {['forced_monotonic_between_predicates 'genl] :unforced-predicate-genl
         ['forced_monotonic_predicate 'genlCx]        :unforced-context-edge
         ['forced_monotonic_predicate 'except]        :unforced-except
         ['forced_monotonic_predicate 'exceptWhen]    :unforced-exception}
        (for [[missing preds]
              {:unforced-relation-mark
               '[irreflexive anti_symmetric asymmetric functional functionalInArg
                 anti_transitive]
               :unforced-definitional-declaration
               '[disjoint covering partition sibling_disjoint orthogonal siblingDisjointException]
               :unforced-arity-binding
               '[arity unary binary ternary quaternary quinary unary_predicate
                 binary_predicate ternary_predicate quaternary_predicate quinary_predicate
                 unary_function binary_function ternary_function quaternary_function
                 quinary_function variable_arity variable_arity_predicate variable_arity_function arityMin]
               :unforced-equality '[rewriteOf sameAs equals]}
              p preds]
          [['forced_monotonic_predicate p] missing])))

(def ^:private declaration-kind
  "The taxonomy property each forced-monotonic declaration functor maintains."
  '{forced_monotonic_predicate          :forced-monotonic
    forced_monotonic_between_predicates :forced-between-predicates})

(defn forced-monotonic?
  "Is `literal` in the forced-monotonic set (`decide/forced-literal?`, docs/nmtms.md,
  \"The forced-monotonic set\"): over every reader, or under the forced-monotonic reading
  `on?`."
  ([kb literal] (decide/forced-literal? (reasoning/taxonomy kb) literal))
  ([kb literal on?] (decide/forced-literal? (reasoning/taxonomy kb) literal on?)))

(defn unforced-antecedents
  "The predicates of the stored rule `rule-sentex`'s antecedents that are not
  `forced-monotonic?` literals (over every reader, or under the forced-monotonic reading `on?`),
  `unknown` antecedents aside, distinct and in antecedent order: the predicates a
  `(forced_monotonic_predicate P)` declaration would make forced-monotonic for the rule's
  firings to conclude a forced-monotonic literal."
  ([kb rule-sentex] (unforced-antecedents kb rule-sentex (partial decide/forced-monotonic? (reasoning/taxonomy kb))))
  ([kb rule-sentex on?]
   (into [] (comp (remove sx/unknown?) (remove #(forced-monotonic? kb % on?)) (map nm/functor)
                  (distinct))
         (:antecedent rule-sentex))))

(defn forced-rule?
  "Is the stored rule `rule-sentex` one whose firings conclude a forced-monotonic literal as an
  ordinary belief: not `set/defaultRule`, no `unknown` antecedent, and no
  `unforced-antecedents`.  Its `exceptWhen` exceptions are meta-sentexes, which
  `forced-conclusion-violation` reads at the firing."
  [kb rule-sentex]
  (let [antes (:antecedent rule-sentex)]
    (boolean (and (seq antes) (not (:defeasible rule-sentex)) (not-any? sx/unknown? antes)
                  (empty? (unforced-antecedents kb rule-sentex))))))

(defn forced-conclusion-violation
  "The `:forced-conclusion` violation of a firing of the rule stored at `rule-handle` that
  concludes the ground sentence `conseq`, or nil when the firing is admitted.  A firing
  concluding a denial of a `forced-monotonic?` literal is convicted, and so is one
  concluding a forced-monotonic literal unless its rule is a `forced-rule?` with no believed
  `exceptWhen`.  A convicted firing is stored and held void (the `:void` forced set), and
  the violation names the rule's `unforced-antecedents` (docs/nmtms.md, \"The
  forced-monotonic set\").  The 3-arity reads the conclusion forced-monotonic over every
  reader: the entry `forced-conclusion-entries` reads for a firing void at some reader.
  The 4-arity reads the conclusion under the forced-monotonic reading `on?` (`network-void?`)."
  ([kb rule-handle conseq]
   (forced-conclusion-violation kb rule-handle conseq (partial decide/forced-monotonic? (reasoning/taxonomy kb))))
  ([kb rule-handle conseq on?]
   (let [neg? (sx/negation? conseq)
         body (if neg? (second conseq) conseq)]
     (when (forced-monotonic? kb body on?)
       (let [rsx (p/get-sentex (:records kb) rule-handle)]
         (when (or neg? (nil? rsx) (not (forced-rule? kb rsx))
                   (seq (provers/rule-exception-entries kb rule-handle)))
           (let [off (if rsx (unforced-antecedents kb rsx) [])]
             {:violation :forced-conclusion
              :detail    {:not-forced-monotonic off
                          :message    (str (pr-str conseq) " is not concluded: " (nm/functor body)
                                           " is forced-monotonic, and a rule concludes a"
                                           " forced-monotonic literal only from forced-monotonic"
                                           " antecedents, with no unknown, exceptWhen or"
                                           " set/defaultRule"
                                           (when (seq off)
                                             (str "; the antecedents that are not forced-monotonic are "
                                                  (str/join ", " off))))}})))))))

(defn network-void?
  "Is a firing of the rule at `rule-handle` concluding `conseq` held void in the network
  (the `:void` forced set): convicted with the conclusion read on the baseline set
  (`decide/global-reading`) and the antecedents on the union over every reader.  A
  conclusion forced-monotonic only by a declaration stated outside CxUniverse is valid in the
  network, and the read walk voids the firing at a reader that sees the declaration
  (`exc/forced-void`)."
  [kb rule-handle conseq]
  (some? (forced-conclusion-violation kb rule-handle conseq
                                      (decide/global-reading (reasoning/taxonomy kb)))))

(defn forced-premise?
  "Does a premise mark on the stored sentex `sx` confer `:monotonic` in the labeller (the
  `:mono` forced set): `sx` is a `genlCx` edge, which caps no firing's class
  (docs/reference.md, decisions 1 and 9).  Every other forced-monotonic literal keeps the
  strength it was written at and is never a loser (`decide/verdict`)."
  [sx]
  (and (not (rules/rule? sx)) (= 'genlCx (nm/functor (:sentence sx)))))

(defn forced-out?
  "Is the stored sentex `sx` held in the `:out` forced set: a fact or a rule the argument
  family holds (`argument/held?`, `argument-conviction`), or a tuple whose length breaks
  its functor's (`arity/inert-tuple?`, docs/taxonomy.md, \"Arity\")?"
  [kb sx]
  (boolean (or (argument/held? kb (:id sx))
               (and (not (rules/rule? sx)) (arity/inert-tuple? kb sx)))))

(defn force-sentex!
  "Write the `:mono`, `:out` and `:held` memberships of the stored sentex `sx` into the
  network: `:held` for a rule holding an open application its own context respells
  nowhere (`nat/held-application?`, docs/nat.md).  The assert path calls it before the
  premise mark, so a forced-out fact is never IN, even for one relabel.  A membership
  already right writes nothing."
  [kb sx]
  (let [tms (reasoning/tms kb)
        h   (:id sx)
        put (fn [kind on?]
              (when (not= on? (jtms/forced? tms kind h))
                (jtms/set-forced tms kind [h] on?)))]
    (put :mono (forced-premise? sx))
    (put :out (forced-out? kb sx))
    (when (rules/rule? sx)
      (put :held (nat/held-application? kb sx)))))

(defn- rule-sentex
  "The stored rule at `h`, or nil when `h` names no stored rule."
  [kb h]
  (when (integer? h)
    (let [sx (p/get-sentex (:records kb) h)]
      (when (rules/rule? sx) sx))))

(defn- concluded-literal
  "The literal the rule consequent `c` concludes, its `not` wrappers peeled."
  [c]
  (if (= 'not (nm/functor c)) (recur (second c)) c))

(defn- declared-firings
  "The ids of the firings of every stored rule that can conclude a predicate a declaration
  makes forced-monotonic (`decide/declared`), or its denial, whose conclusion a reader that
  sees an IN declaration of its predicate sees (`tax/contexts-seen-with-global`).  The
  rules are those filed under the predicate's consequent key or the variable-consequent
  key, and the rules under `not` whose concluded literal has that functor or a variable
  one.  Read off the rule index and the unscoped `genlCx` closure in every context, since
  `vaelii.core/violations` is a whole-KB report, so the cost is those rules' firings and
  not the predicates' fact extent."
  [kb]
  (let [tax   (reasoning/taxonomy kb)
        tms   (reasoning/tms kb)
        decls (reduce-kv (fn [m [_ pred] hcs]
                           (update m pred (fnil into #{})
                                   (keep (fn [[h c]] (when (jtms/in? tms h) c))) hcs))
                         {} (decide/declared tax))]
    (when (seq decls)
      (let [idx     (:index kb)
            recs    (:records kb)
            by-key  #(reads/as-stored-rules-by-consequent-global idx %)
            negated (filter #(let [f (some->> (rule-sentex kb %) :consequent
                                              concluded-literal nm/functor)]
                               (or (sx/variable? f) (contains? decls f)))
                            (by-key 'not))
            rules   (-> #{}
                        (into (mapcat by-key) (keys decls))
                        (into (by-key p/var-consequent-key))
                        (into negated))
            ;; `[jid pred context]` of each firing concluding a declared predicate
            firings (into [] (mapcat (fn [rh]
                                       (keep #(let [j (jtms/justification tms %)
                                                    c (when (= rh (:informant j))
                                                        (p/get-sentex recs (:consequence j)))
                                                    f (some-> c sx/sentence-of concluded-literal nm/functor)]
                                                (when (contains? decls f) [% f (:context c)]))
                                             (jtms/dependents tms rh))))
                          rules)
            seen    (into {} (map (fn [[f fs]]
                                    (let [xs (into #{} (map peek) fs)]
                                      [f (into #{} (mapcat #(tax/contexts-seen-with-global tax % xs))
                                               (decls f))])))
                          (group-by second firings))]
        (into [] (keep (fn [[jid f x]] (when (contains? (seen f) x) jid))) firings)))))

(defn forced-conclusion-entries
  "The `:forced-conclusion` violations of the stored firings `forced-conclusion-violation`
  convicts over every reader, read off the stored state: the firings the network holds
  void (the `:void` forced set), and the `declared-firings`, which a reader that sees the
  declaration reads void.  Each entry is the violation with `:sentence` the conclusion's
  stored spelling, `:context` its context and `:rule` the rule's handle, and carries no
  `:run`.  Equal entries are one; the order is content order of the conclusion, its
  context and the rule's sentence, never a handle's."
  [kb]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (->> (into (set (jtms/forced-members tms :void)) (declared-firings kb))
         (into #{} (keep (fn [jid]
                           (let [j  (jtms/justification tms jid)
                                 rh (:informant j)
                                 c  (some->> (:consequence j) (p/get-sentex recs))]
                             (when (and c (integer? rh))
                               (let [s (sx/sentence-of c)]
                                 (some-> (forced-conclusion-violation kb rh s)
                                         (assoc :sentence s :context (:context c) :rule rh))))))))
         (nm/sort-by-content-key (fn [e] [(:sentence e) (:context e)
                                          (some-> (p/get-sentex recs (:rule e)) sx/sentence-of)]))
         vec)))

(defn- forcing-moves
  "Add to `acc` the forced memberships that move for the stored sentex `sx` and for the
  firings that conclude it or that its rule informs, as `{[kind on?] [id …]}`."
  [kb acc sx]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)
        h    (:id sx)
        put  (fn [acc kind id on?]
               (let [on? (boolean on?)]
                 (if (= on? (jtms/forced? tms kind id))
                   acc
                   (update acc [kind on?] (fnil conj []) id))))
        void (fn [acc jid rh conclusion]
               (put acc :void jid (and (forced-conclusion-violation kb rh (:sentence conclusion))
                                       (network-void? kb rh (:sentence conclusion)))))
        acc  (put acc :mono h (forced-premise? sx))]
    (if (rules/rule? sx)
      ;; a firing is read only when its conclusion can be forced-monotonic now, or when it
      ;; is held void now and the forced-monotonic set may have released it
      (let [c       (:consequent sx)
            body    (if (sx/negation? c) (second c) c)
            reach?  (let [f   (nm/functor body)
                          tax (reasoning/taxonomy kb)]
                      (or (sx/variable? f)
                          (and (symbol? f)
                               (or (decide/forced-monotonic? tax :forced-monotonic f)
                                   (decide/forced-monotonic? tax :forced-between-predicates f)))))]
        (reduce (fn [acc jid]
                  (let [j (jtms/justification tms jid)]
                    (if (and (= h (:informant j)) (or reach? (jtms/forced? tms :void jid)))
                      (if-let [conclusion (p/get-sentex recs (:consequence j))]
                        (void acc jid h conclusion)
                        acc)
                      acc)))
                acc (sort (jtms/dependents tms h))))
      (reduce (fn [acc jid]
                (let [rh (:informant (jtms/justification tms jid))]
                  (if (rule-sentex kb rh) (void acc jid rh sx) acc)))
              (put acc :out h (forced-out? kb sx))
              (sort (jtms/supports tms h))))))

(defn force-sentexes!
  "Rewrite the network's forced memberships for the stored sentexes `sxs` and the
  firings each concludes or informs, from the forced-monotonic set as it stands.  It logs nothing: the
  chainer logs a convicted firing once, as its justification is added.  The relabel each
  set change runs is the whole recompute: nothing stored is written or deleted.  Answers
  whether any membership moved."
  [kb sxs]
  (let [tms   (reasoning/tms kb)
        moves (reduce #(forcing-moves kb %1 %2) {} sxs)]
    (doseq [[[kind on?] ids] moves]
      (jtms/set-forced tms kind ids on?))
    (boolean (seq moves))))

(defn force-reach!
  "Rewrite the forced memberships over what `pred` reaches after it joins or leaves the
  forced-monotonic set (docs/nmtms.md, \"The forced-monotonic set\"), and answer the
  handles of the rules in that reach, which a firing swept while it was held void is
  restored from by a re-join.  `global?` names a move of the baseline set (`decide/global?`): the reach is
  every stored sentex mentioning `pred` (its literals, their denials, the rules reading
  or concluding it) and their firings.  A declaration elsewhere moves no denial's `:out`
  membership, so its reach is the rules reading or concluding `pred`, the rules with a
  variable consequent among them, and their firings: flat in `pred`'s facts.  Both read
  every context, since the forced sets are network state, the union over every reader."
  ([kb pred] (force-reach! kb pred true))
  ([kb pred global?]
   (let [idx (:index kb)
         sxs (if global?
               (into [] (kb/find-sentexes kb pred))
               (into [] (comp (distinct) (keep #(p/get-sentex (:records kb) %)))
                     (concat (reads/as-stored-rules-by-antecedent-global idx pred)
                             (res/concluding-rule-handles kb pred))))]
     (force-sentexes! kb sxs)
     (into [] (comp (filter rules/rule?) (map :id)) sxs))))

(defn force-stored!
  "Write every forced membership the stored content takes under the forced-monotonic set:
  `recover`'s pass, run once the taxonomy replay has rebuilt the forced-monotonic
  properties.  A stored denial of a forced-monotonic literal with no premise mark and no
  support is the record an
  older store kept inert, and it takes the `:default` premise mark it was written with
  (docs/nmtms.md, \"The forced-monotonic set\").  A stored rule `nat/held-application?`
  holds is forced `:held` again (docs/nat.md, \"The corresponding predicate\")."
  [kb]
  (let [tax  (reasoning/taxonomy kb)
        tms  (reasoning/tms kb)
        preds (sort (into #{} (mapcat #(decide/forced-predicates tax %)) decide/forced-kinds))
        by-h (with-open [r (progress/start ::force-read "recover: read the forced predicates' sentexes"
                                           nil)]
               ;; `kb/find-sentexes` of each atom, the records hinted a chunk ahead
               (into {} (comp (keep #(p/get-sentex (:records kb) %)) (map (juxt :id identity)))
                     (cap/hinting (cap/prefetcher (:records kb)) cap/recovery-hint-chunk
                                  (progress/each r (distinct (mapcat #(reads/as-stored-with-term (:index kb) %)
                                                                     preds))))))
        sxs  (vals by-h)]
    (with-open [r (progress/start ::force-stored "recover: write the forced memberships"
                                  (count by-h))]
      (force-sentexes! kb (progress/each r sxs)))
    (run! #(force-sentex! kb %) (nat/held-application-rules kb))
    (doseq [{h :id s :sentence} sxs
            :when (and (sx/negation? s) (forced-monotonic? kb (second s))
                       (not (jtms/premise? tms h))
                       (empty? (jtms/supports tms h)))]
      (p/mark-premise (:records kb) h :default)
      (jtms/add-premise tms h :default))))

;; ---- an argument that fails its declared type is held inert ---------------------
;;
;; `assert` stores a fact whose argument an argument declaration convicts and holds it in
;; the `:out` forced set (docs/argtypes.md, "An argument that fails its declared type is
;; held inert").  The verdict is `argument-conviction` of the stored fact, decided at its
;; write (`constraint-checks`' `:conviction`) and again at the settle for every fact a
;; queued write can move (`refresh-argument-holds!`).

(defn argument-conviction
  "The argument conviction `assert` holds the stored sentex `sx` inert under, as a
  violation value, or nil.  For a fact, the first violation of `argument-problem`'s arms
  and then `args-quoted-problem` that `held-inert?` accepts, read from `sx`'s own context
  as `constraint-checks` reads a written fact.  For a rule, `rule-conviction`.  Nil for a
  denial."
  [kb sx]
  (if (some? (:antecedent sx))
    (rule-conviction kb sx)
    (when (and sx (not (sx/negative? sx)))
      (binding [*refuse-clashes?* false]
        (let [context (:context sx)
              chk     (checked-sentence kb (:sentence sx))
              pred    (nm/functor chk)]
          (when (symbol? pred)
            (let [types (kb/membership-reader kb context)
                  decls (declaration-reader kb pred context)]
              (or (argument-problem kb chk context types decls held-inert?)
                  (let [q (args-quoted-problem kb chk context types decls)]
                    (when (held-inert? q) q))))))))))

(defn hold-argument-conviction!
  "Record the fact at `h`, of functor `f`, as held for an argument conviction, before its
  forced memberships are written (`force-sentex!`): the assert path's half of the verdict
  `constraint-checks` answered under `:conviction`."
  [kb h f]
  (argument/set-held! kb h f true))

(defn hold-rule-conviction!
  "Record the new rule `sx` as held when `rule-conviction` convicts it, and write its
  `:out` membership: the rule entry points' half of the verdict, run before the rule is
  premised or justified, so a convicted rule is never IN."
  [kb sx]
  (when (rule-conviction kb sx)
    (argument/set-held! kb (:id sx) nil true)
    (jtms/set-forced (reasoning/tms kb) :out [(:id sx)] true)))

(defn held-conviction
  "The argument conviction the stored sentex `sx` is held inert under
  (`argument-conviction`), or nil when the argument family does not hold it."
  [kb sx]
  (when (and sx (argument/held? kb (:id sx)))
    (argument-conviction kb sx)))

(defn held-argument-entries
  "The violations of the stored sentexes the argument family holds, read off the stored
  state: `:inert-argument` for a fact and `:inert-rule` for a rule, `:sentence` the
  stored spelling, `:context` its context and `:detail` its conviction
  (`held-conviction`).  The order is content order of the sentence and context, never a
  handle's.  The records are hinted a chunk ahead, and the convictions share one
  `*pass-reads*`, as `refresh-argument-holds!` decides them."
  [kb]
  (let [recs (:records kb)]
    (binding [*pass-reads*         (volatile! {})
              exc/*reader-states* (or exc/*reader-states* (volatile! nil))]
      (->> (cap/hinting (cap/prefetcher recs) cap/recovery-hint-chunk (sort (keys (argument/held kb))))
           (into [] (keep (fn [h]
                            (let [sx (p/get-sentex recs h)]
                              (when-let [v (held-conviction kb sx)]
                                (if (rules/rule? sx)
                                  {:violation :inert-rule :sentence (sx/sentence-of sx)
                                   :context (:context sx) :detail v}
                                  {:violation :inert-argument :sentence (sx/sentence-of sx)
                                   :context (:context sx) :detail v}))))))
           (nm/sort-by-content-key (juxt :sentence :context))
           vec))))

(defn- constrained-functor
  "`(fn [f])`: does some stored argument declaration name `f` or a predicate above it
  (`tax/arg-declaration-props`, over the unscoped closure)?  Memoized per functor.  The
  answer filters candidates over every reader, and each candidate is decided again from
  its own context (`argument-conviction`)."
  [tax]
  (let [prop-sets (into [] (comp (map #(tax/props tax %)) (filter seq)) (vals tax/arg-declaration-props))
        memo      (volatile! {})]
    (fn [f]
      (if-some [b (get @memo f)]
        b
        (let [b (boolean (and (symbol? f) (seq prop-sets)
                              (let [up (tax/genls-global tax f)]
                                (some (fn [r] (or (contains? r f) (some r up))) prop-sets))))]
          (vswap! memo assoc f b)
          b)))))

(defn- declared-functor
  "`(fn [f])`: does some stored argument declaration name `f` itself, in any context?  A
  candidate filter, as `constrained-functor` is."
  [tax]
  (let [prop-sets (into [] (comp (map #(tax/props tax %)) (filter seq)) (vals tax/arg-declaration-props))]
    (fn [f] (boolean (some #(contains? % f) prop-sets)))))

(defn- constrained-functors
  "Every predicate `constrained-functor` accepts: each predicate a stored argument
  declaration names, and every predicate below one, over the unscoped closure.  Sorted
  by print key."
  [tax]
  (->> (vals tax/arg-declaration-props)
       (mapcat #(tax/props tax %))
       (mapcat #(tax/specs-global tax %))
       (filter symbol?)
       distinct
       (sort-by nm/print-key)))

(def ^:private compound-kinds
  "Every expression kind `provers/shape-kinds` can give a compound."
  '[non_atomic_expression ill_formed_expression open_expression closed_expression
    open_formula sentence])

(defn- covering-demands
  "The per-argument demands a covering declaration `chk` makes of its predicate's tuples,
  each with `:from`, the first position it types, in place of `:pos`: `args` and
  `argAndRest` as `arg`, `argsGenl` and `argAndRestGenl` as `genlArg`, and `interArgs`
  and `interArgAndRest` as an `interArg` target at every position from the start.  Nil
  for any other declaration."
  [chk]
  (let [[f pred a b] chk
        n (nm/arity chk)
        m (case f
            args            (when (= 2 n) {:kind :arg-type :from 1 :type a})
            argsGenl        (when (= 2 n) {:kind :arg-genl :from 1 :type a})
            interArgs       (when (= 2 n) {:kind :inter-arg-type :from 1 :type a})
            argAndRest      (when (= 3 n) {:kind :arg-type :from a :type b})
            argAndRestGenl  (when (= 3 n) {:kind :arg-genl :from a :type b})
            interArgAndRest (when (= 3 n) {:kind :inter-arg-type :from a :type b})
            nil)]
    (when (and m (symbol? pred) (not (sx/variable? pred)) (pos-int? (:from m))
               (symbol? (:type m)) (not (sx/variable? (:type m))))
      (assoc m :pred pred))))

(defn- held-demand-test
  "`{:atom? (fn [x]) :test (fn [types x context]) :values-convict? (fn [types-of xs
  contexts])}` for the demand `dm`, with `:atoms-convict?` beside them for `quotedArg`,
  answering only
  for a conviction `assert` holds rather than weighs (`held-inert?`): under the entailing
  reading a separated symbol under `arg`, `interArg` or a separated type under `genlArg`
  is weighed, so only a value, a `genlArg` individual and a `quotedArg` term can be
  held.  `:atom?` says whether an indexed atom can be held at all, before any context is
  read.  A test that reads only the term's kinds and the context is memoized for the pass
  (`*pass-reads*`), under the demand's kind and type, so a declared type's closure is
  walked once per kind and context rather than once per atom or per declaration; a
  separation test is built once per type and context.  Where a `:monotonic` definition can
  decide a literal value under the declared type (`provers/value-definition-reaches?`), a
  value's test is memoized per value instead.  `:values-convict?` and `:atoms-convict?`
  answer whether the test convicts some term of `xs` from some context of `contexts`,
  testing one term per memo key.  The individual floor is a global read for
  `genls-problem`'s reason (E17_ALLOW)."
  [kb {:keys [kind type] :as dm} tax]
  (let [constraint? (not *assertive-arg-types?*)
        memo        (pass-read [::held-tests kind type] #(volatile! {}))
        cached      (fn [k f] (let [v (get @memo k ::none)]
                                (if (identical? v ::none)
                                  (let [v (boolean (f))] (vswap! memo assoc k v) v)
                                  v)))
        reach?      (let [m (pass-read [::value-reach type] #(volatile! {}))]
                      (fn [c]
                        (let [d (get @m c ::none)]
                          (if (identical? d ::none)
                            (let [d (provers/value-definition-reaches? kb type c)] (vswap! m assoc c d) d)
                            d))))
        ;; the memo key of a value's test: its kinds, or the value itself where a
        ;; definition can decide it
        value-key   (fn [x c]
                      (if (and (reach? c) (provers/literal-value-kind x)) [::value x c] [(value-kinds x) c]))
        ;; whether a test convicts some term of `xs` from some context of `cs`: one term
        ;; per memo key (`by` of the term, and the context), every term from a context a
        ;; definition reaches
        grouped     (fn [test by]
                      (fn [types-of xs cs]
                        (let [reps (delay (vals (into {} (map (juxt by identity)) xs)))]
                          (boolean (some (fn [c] (some #(test (types-of c) % c) (if (reach? c) xs @reps)))
                                         cs)))))
        ;; the same question asked of every term from every context
        each        (fn [test]
                      (fn [types-of xs cs]
                        (boolean (some (fn [c] (some #(test (types-of c) % c) xs)) cs))))
        sep-in      (let [m (pass-read [::disjointness type] #(volatile! {}))]
                      (fn [c] (or (get @m c)
                                  (let [f (tax/disjointness-test tax type c)] (vswap! m assoc c f) f))))
        ;; `separated-type`'s test, true of a symbol believing a type separated from `type`
        separated?  (fn [types x c] (boolean (some (sep-in c) (:types (types x)))))
        ;; the individual floor: a symbol with no `genl` edge in any context is outside the
        ;; hierarchy, and only one with an edge pays the walk
        floor?      (fn [x] (cached [::floor x]
                                    #(or (empty? (tax/direct-genls-global tax x))
                                         (not (tax/genl?-global tax x 'thing)))))]
    (case kind
      :arg-type
      (let [test (fn [types x c]
                   (if (checkable-term? x)
                     (and constraint? (separated? types x c))
                     (cached (value-key x c) #(outside-declared-type? kb tax types x type c))))]
        {:atom?           (fn [_] constraint?)
         :test            test
         :values-convict? (grouped test value-kinds)})
      :inter-arg-type
      (let [test (fn [types x c]
                   (and constraint? (checkable-term? x) (separated? types x c)))]
        {:atom?           (fn [_] constraint?)
         :test            test
         :values-convict? (each test)})
      :arg-genl
      (let [test (fn [_ x c]
                   (and (checkable-term? x)
                        (or (and constraint? ((sep-in c) x))
                            (and (nm/individual? x) (floor? x)))))]
        {:atom?           (fn [x] (or constraint? (nm/individual? x)))
         :test            test
         :values-convict? (each test)})
      :quoted-arg-type
      (let [test     (fn [_ x c]
                       (cached (if (value-kind x) (into [(value-kind x)] (value-key x c)) [nil (provers/shape-kinds x) c])
                               #(breaks-demand? kb dm tax nil x c)))
            convict? (grouped test (juxt value-kind value-kinds))]
        {:atom?           (fn [_] true)
         :test            test
         :values-convict? convict?
         :atoms-convict?  convict?}))))

(defn- declaration-candidates
  "The handles of the stored facts the argument declaration `d` (a stored sentex) can
  hold inert among the tuples of the predicates `preds`, stated in a context that sees
  `d`'s.  For a declaration with per-argument demands (`declaration-demand`,
  `covering-demands`), the distinct atoms at each position it types are tested
  (`held-demand-test`) and only a convicted atom's tuples are read.  A value at the
  position has no argument root, so its tuples are read off the functor and each is
  tested from its fact's context; the read runs only when some value there convicts from
  a context stating the predicate.  A compound at the position is read for a `quotedArg`
  demand alone, off the functor, when a compound is stored there
  (`reads/as-stored-tokens-at-global`) and the declared type is separated from some
  compound kind (`compound-kinds`) as seen from `d`'s context, and is tested from its
  fact's context.  A position a covering form types runs to the longest tuple
  stored (`reads/as-stored-shape-lengths`).  For any other declaration every stored tuple
  of `preds` there is a candidate.  The atoms are read over every context, a superset
  `argument-conviction` decides again from each fact's own context.  A predicate with no
  stored fact (`reads/stored-count-with-functor`) is dropped before any test is built."
  [kb d preds]
  (let [tax   (reasoning/taxonomy kb)
        idx   (:index kb)
        preds (filterv #(pos? (long (reads/stored-count-with-functor idx %))) preds)
        seen  (pass-read [::context-down (:context d)] #(set (tax/context-down-global tax (:context d))))
        chk   (:sentence d)]
    (when (seq preds)
      (if-let [dm (or (declaration-demand chk) (covering-demands chk))]
        (let [memo    (pass-read ::membership-readers #(volatile! {}))
              readers (fn [c] (or (get @memo c)
                                  (let [r (kb/membership-reader kb c)] (vswap! memo assoc c r) r)))
              recs    (:records kb)
              {atom? :atom? test :test :keys [values-convict? atoms-convict?]} (held-demand-test kb dm tax)
              compounds? (and (= :quoted-arg-type (:kind dm))
                              (pass-read [::compound-separated (:type dm)]
                                         ;; read unscoped: a context below `d`'s can separate
                                         ;; the type from a compound kind
                                         #(boolean (some (tax/disjointness-test tax (:type dm) nil (constantly false))
                                                         compound-kinds))))]
          (for [p     preds
                pos   (if-let [n (:pos dm)]
                        [n]
                        (range (:from dm) (inc (reduce max 0 (reads/as-stored-shape-lengths idx p)))))
                :let  [ts (pass-read [::tokens-at p pos] #(reads/as-stored-tokens-at-global idx p pos))
                       xs (pass-read [::atoms-at p pos] #(into #{} (remove sx/subterm-mark?) ts))
                       ;; a value has no argument root, so its tuples are read off the
                       ;; functor and tested from each fact's context: a context below
                       ;; `d`'s can convict a value `d`'s context does not
                       vs (into #{} (remove sx/indexable-term?) xs)
                       ;; an atom's contexts and the functor are read only when a test
                       ;; convicts some term there from a context stating `p`, and the
                       ;; compounds only when one stands at `pos`
                       cs  (delay (first (reads/as-stored-contexts-with-functor idx p seen)))
                       as  (filterv #(and (sx/indexable-term? %) (atom? %)) xs)
                       as? (or (nil? atoms-convict?) (and (seq as) (atoms-convict? readers as @cs)))
                       vs? (and (seq vs) (values-convict? readers vs @cs))
                       cs? (and compounds? (boolean (some sx/subterm-mark? ts)))]
                h     (concat
                       (for [x     (when as? as)
                             c     (reads/as-stored-contexts-with-arg-in idx p pos x seen)
                             :when (test (readers c) x c)
                             h     (reads/as-stored-with-args-in idx p {pos x} #{c})]
                         h)
                       (when (or vs? cs?)
                         (filter (fn [h]
                                   (let [sx (p/get-sentex recs h)
                                         a  (some-> sx :sentence nm/args vec (arg-at pos))]
                                     (or (and vs? (contains? vs a)
                                              (test (readers (:context sx)) a (:context sx)))
                                         (and cs? (sequential? a)
                                              (test nil a (:context sx))))))
                                 (reads/as-stored-with-functor-in idx p seen))))]
            h))
        (for [p preds h (reads/as-stored-with-functor-in idx p seen)] h)))))

(defn- declarations-of
  "The stored argument declarations naming `p` at argument 1, in the contexts `ctxs` or in
  every context when `ctxs` is nil."
  [kb p ctxs]
  (let [idx  (:index kb)
        recs (:records kb)]
    (into [] (comp (mapcat #(if ctxs
                              (reads/as-stored-with-args-in idx % {1 p} ctxs)
                              (reads/as-stored-with-args idx % {1 p})))
                   (keep #(p/get-sentex recs %))
                   (filter #(nil? (:antecedent %))))
          (sort argument/declaration-functors))))

(def ^:private spec-walk-limit
  "The most specializations of a moved type the refresh walks before reading every stored
  declaration instead (`lattice-candidates`)."
  512)

(defn- value-kind-moved?
  "Does the moved type `e` stand at or above a kind a value or a compound carries, so a
  `genl` edge or a separation at `e` can move what a value argument is (`value-kinds`) or
  which kind of a compound is separated (`compound-kind-against`)?  Read over every
  context's edges, since the answer widens a candidate set."
  [tax e]
  (boolean (some #(tax/genl?-global tax % e)
                 (concat syntactic-roots compound-kinds
                         '[positive_integer negative_integer
                           non_negative_integer non_positive_integer]))))

(defn- all-declarations
  "Every stored argument declaration, as sentexes."
  [kb]
  (let [idx  (:index kb)
        recs (:records kb)]
    (with-open [r (progress/start ::all-declarations "settle: read the argument declarations" nil)]
      (into [] (comp (keep #(p/get-sentex recs %))
                     (filter #(and (nil? (:antecedent %)) (not (sx/negative? %)))))
            (progress/each r (mapcat #(reads/as-stored-with-functor idx %)
                                     (sort argument/declaration-functors)))))))

(defn- declared-types
  "The types the stored argument declaration `d` names: each symbol argument after its
  predicate."
  [d]
  (into #{} (filter #(and (symbol? %) (not (sx/variable? %)))) (drop 2 (:sentence d))))

(defn- declarations-naming
  "The stored argument declarations naming one of the types `ts` as a declared type, at
  argument 2, 3 or 5, read over every context."
  [kb ts]
  (let [idx (:index kb)]
    (into [] (comp (mapcat (fn [t] (mapcat #(reads/as-stored-with-arg-global idx % t) [2 3 5])))
                   (distinct)
                   (keep #(p/get-sentex (:records kb) %))
                   (filter #(contains? argument/declaration-functors (nm/functor (:sentence %)))))
          (sort-by nm/print-key ts))))

(defn- members-below
  "The symbols a stored membership in the type `t` or a type below it names, read over
  every context, sorted by print key.  The read covers every context because the symbols
  name candidate rules, each decided again from its own context (`rule-conviction`)."
  [kb tax t]
  (let [idx  (:index kb)
        recs (:records kb)]
    (->> (cons t (tax/specs-global tax t))
         (mapcat #(reads/as-stored-with-functor idx %))
         (keep #(let [s (:sentence (p/get-sentex recs %))]
                  (when (and (seq? s) (= 2 (count s)) (symbol? (second s))) (second s))))
         distinct
         (sort-by nm/print-key))))

(defn- type-level-rules
  "The handles of the rules whose variables a type-level position can constrain: the
  rules on a predicate a `genlArg` declaration names or below one, and on a
  `type_relation_predicate` (`literal-variable-constraints`).  The read covers every
  context because the handles are a candidate superset, each decided again from its own
  context (`rule-conviction`)."
  [kb tax]
  (rules-on kb (concat (mapcat #(tax/specs-global tax %) (tax/props tax (get tax/arg-declaration-props 'genlArg)))
                       (members-below kb tax 'type_relation_predicate))))

(defn- declarations-below
  "The stored argument declarations naming a type at or below one of the types `ends`,
  read in one pass over every stored declaration.  The ends above each declared type are
  read off one memo (`tax/genls-global-among`), so the types above many declared types
  are walked once for all of them and for every end.  Read over every context's edges: a
  superset `argument-conviction` decides again from each sentex's own context."
  [kb tax ends]
  (let [among (set ends)
        memo  (volatile! {})
        decls (all-declarations kb)]
    (with-open [r (progress/start ::declarations-below
                                  "settle: find the declarations below the moved types with many specializations"
                                  (count decls))]
      (into [] (filter (fn [d] (some #(seq (tax/genls-global-among tax % among memo)) (declared-types d))))
            (progress/each r decls)))))

(defn- end-candidates
  "The handles a `genl` edge or a separation moved at the type or predicate `e`, whose
  specializations are `below` (nil when more than `spec-walk-limit`), can move the
  verdict of, apart from the tuples under the declarations naming a type at or below `e`
  (`lattice-candidates`): the tuples at or below `e` under a declaration on a predicate at
  or above it, held (`(held-under preds)`) or not, with the rules on those predicates
  (`rules-on`); the rules on the members of `e` when `e` is at or below
  `type_relation_predicate`; and, with `symbols?`, every stored fact naming a term a type
  at or below `e` holds.  Read over every context's edges and tuples, as
  `lattice-candidates` reads."
  [kb tax e below symbols? constrained? held-under]
  (let [idx   (:index kb)
        preds (when (constrained? e) (vec (sort-by nm/print-key (tax/specs-global tax e))))]
    (concat
     (when preds
       (concat
        (held-under preds)
        (rules-on kb preds)
        (mapcat #(declaration-candidates kb % preds)
                (mapcat #(declarations-of kb % nil) (filter (declared-functor tax) (tax/genls-global tax e))))))
     (when (or (= 'type_relation_predicate e) (tax/genl?-global tax e 'type_relation_predicate))
       (rules-on kb (members-below kb tax e)))
     (when symbols?
       (for [t     (sort-by nm/print-key below)
             m     (reads/as-stored-with-functor idx t)
             :let  [s (:sentence (p/get-sentex (:records kb) m))]
             :when (and (seq? s) (= 2 (count s)) (symbol? (second s)))
             h     (reads/as-stored-with-term idx (second s))]
         h)))))

(defn- lattice-candidates
  "The handles the `genl` edges or separations moved at the types or predicates `ends`
  can move the verdict of, as a set, or `::whole` when every declaration is owed a read:
  an end sits at or above a value kind, or, with `symbols?`, has more specializations
  than `spec-walk-limit`.  The handles are each end's `end-candidates`; the tuples under
  each declaration naming a type at or below an end, held or not (`held` is
  `argument/held`), with the rules on its predicates, each declaration read once however
  many ends it is below; and the rules `type-level-rules` names when an end is at or
  above `unary_predicate`.  The declarations below an end with more specializations than
  `spec-walk-limit` are read in one pass (`declarations-below`), the others off the index
  (`declarations-naming`).  Read over every context's edges and tuples: a superset
  `argument-conviction` decides again from each sentex's own context.  Each loop reports
  progress lines, and a shutdown can stop the write before each end and each declaration
  (`dur/check-abort!`)."
  [kb ends symbols? constrained? held]
  (let [tax   (reasoning/taxonomy kb)
        ends  (vec (sort-by nm/print-key ends))
        below (into {} (map (juxt identity #(tax/specs-global-within tax % spec-walk-limit))) ends)
        many  (filterv (comp nil? below) ends)]
    (if (or (some #(value-kind-moved? tax %) ends) (and symbols? (seq many)))
      ::whole
      (let [by    (delay (reduce-kv (fn [m h f] (cond-> m f (update f (fnil conj []) h))) {} held))
            held-under (fn [ps] (mapcat #(get @by %) ps))
            decls (into (sorted-map)
                        (map (juxt :id identity))
                        (concat (when (seq many) (declarations-below kb tax many))
                                (declarations-naming kb (into #{} (mapcat below) ends))))
            hs    (with-open [r (progress/start ::lattice-ends "settle: read what the moved genl ends reach"
                                                (count ends))]
                    (into #{} (mapcat #(do (dur/check-abort!) (end-candidates kb tax % (below %) symbols? constrained? held-under)))
                          (progress/each r ends)))
            hs    (with-open [r (progress/start ::lattice-declarations
                                                "settle: read the tuples under the declarations below the moved genl ends"
                                                (count decls))]
                    (into hs (mapcat #(let [_  (dur/check-abort!)
                                            ps (sort-by nm/print-key (tax/specs-global tax (second (:sentence %))))]
                                        (concat (held-under ps) (rules-on kb ps) (declaration-candidates kb % ps))))
                          (progress/each r (vals decls))))]
        (cond-> hs
          (some #(or (= collection-type %) (tax/genl?-global tax collection-type %)) ends)
          (into (type-level-rules kb tax)))))))

(def ^:dynamic *whole-move-sweeps?*
  "True reads every `genlCx` move whole, as before the moves were split by what each
  reader gains (`tax/context-move`'s `:gains`): the settle's merge and argument-type
  sweeps (`special/move-groups`), its mint withdrawal, and the argument holds
  (`gained-ends-candidates`) over every reader under a moved edge.  The reference
  `genlcx_move_gain_test` holds the split against."
  false)

(def gain-side-blockers
  "The functors whose sentex, stated in a context a `genlCx` move gives a reader, changes
  what the content the reader already saw means to it: a cached relation (a mark, a
  declaration, a `genl` edge, an equality), a function's result declaration
  (`nat/result-types`, which types every application of the function), an `except`, a
  `defeat` and a definition (`sx/defn-predicates`).  A gain stating none of them shows
  the reader facts alone, and a sweep may read what those facts meet in place of what
  the reader saw (`plain-gain?`)."
  (-> (set pr/cached)
      (into '[result genlResult resultArg])
      (conj sx/except-functor sx/defeat-functor)
      (into sx/defn-predicates)))

(defn plain-gain?
  "May a sweep of a group of readers a `genlCx` move gives the contexts `gain`
  (`tax/context-move`'s `:gains`) read what the facts of `gain` meet in place of what the
  readers saw?  When `gain` states none of the `gain-side-blockers`, and no context the
  readers see, `seen`, states an `except`: then every pair, meeting or verdict the move
  changes for such a reader holds a fact stored in `gain` and visible to the reader.  An
  `except` the readers see can hide a fact of `gain` from them, which a sweep from
  `gain`'s side would read past."
  [kb gain seen]
  (let [idx (:index kb)
        states? (fn [fs cs] (some #(seq (reads/as-stored-with-functor-in idx % cs)) fs))]
    (not (or (states? gain-side-blockers gain)
             (states? [sx/except-functor] seen)))))

(def ^:private gain-term-posting-limit
  "The most postings a term named in a `genlCx` move's gain may hold for the argument holds
  to read the term's postings (`gained-ends-candidates`); past it the group's readers'
  constrained tuples are read instead."
  4096)

(defn- gained-ends-candidates
  "The stored facts and rules whose argument hold the `genlCx` edges `edges` entering the
  active set can move, their lower ends having only gained edges since the hold was last
  read (`tax/shrinks-since`, `tax/grows-since`), or nil when the moves are read whole:
  while an `except` reaches a `genlCx` supporter, or past `tax/move-gain-readers`.

  Each edge is read as a move beside every other (`tax/context-move`'s `:gains`, with
  `edges` as `off`, since a context two of them reach is gained through neither alone).  A verdict is read from the sentex's own context,
  so it moves only at a reader the move gives a context.  Per group of such readers: when
  the gain states facts alone (`plain-gain?`), the sentexes stored in a reader's context
  that name a term a membership stored there types, since a verdict reads what the
  arguments are (`kb/memberships`) and, with the declarations, `genl` edges and result
  declarations out of the gain, a fact of the gain types no term but by membership, each
  term read off its postings while they hold no more than `gain-term-posting-limit`; else
  the tuples of `functors` and the rules stored in the readers' contexts."
  [kb tax edges functors]
  (let [idx  (:index kb)
        recs (:records kb)
        ex   (exc/genlCx-except-contexts
              kb {:supports? #(= 'genlCx (nm/functor (some-> (p/get-sentex recs %) sx/body)))
                  :count     (reads/stored-count-with-functor idx 'genlCx)
                  :handles   #(reads/as-stored-with-functor idx 'genlCx)})]
    (when (and (empty? ex) (not *whole-move-sweeps?*))
      (let [edges   (vec (sort-by #(mapv nm/print-key %) edges))
            usable? (fn [a b] (not (reads/stored-opposed? idx (list 'genlCx a b))))
            groups  (reduce (fn [acc [l p]]
                              (if (nil? acc)
                                acc
                                (when-let [gs @(:gains (tax/context-move tax l p ex usable? edges))]
                                  (into acc gs))))
                            [] edges)]
        (when groups
          (for [{:keys [gain readers seen]} (distinct groups)
                :let [rs    (sort-by nm/print-key readers)
                      terms (when (plain-gain? kb gain seen)
                              (into (sorted-set-by #(compare (nm/print-key %1) (nm/print-key %2)))
                                    (comp (mapcat #(reads/as-stored-in-context idx %))
                                          (keep #(p/get-sentex recs %))
                                          (filter #(and (nil? (:antecedent %))
                                                        (= 1 (nm/arity (:sentence %)))))
                                          (mapcat #(rest (:sentence %)))
                                          (mapcat #(tree-seq sequential? seq %))
                                          (filter symbol?)
                                          (remove sx/variable?))
                                    (sort-by nm/print-key gain)))
                      wide? (or (nil? terms)
                                (some #(> (bounded-count (inc gain-term-posting-limit)
                                                         (reads/as-stored-with-term idx %))
                                          gain-term-posting-limit)
                                      terms))]
                h (if wide?
                    (concat (for [f functors
                                  h (reads/as-stored-with-functor-in idx f (set rs))]
                              h)
                            (reads/as-stored-rules-in idx :rule (set rs)))
                    (let [in? (set rs)]
                      (for [t terms
                            h (reads/as-stored-with-term idx t)
                            :when (some-> (p/get-sentex recs h) :context in?)]
                        h)))]
            h))))))

(defn- definition-candidates
  "The handles a definition of the type `t` stored, removed or relabelled can move the
  verdict of (`provers/value-definition`): under each declaration naming a type at or
  below `t`, which inherits `t`'s necessary condition, or at or above `t`, which holds
  the values `t`'s sufficient condition admits, the held facts of the declared predicates
  and the tuples the declaration convicts.  A type at or above every syntactic root is
  skipped, since every value kind is at or below it.  `held` is `argument/held`.  Read
  over every context."
  [kb t held]
  (let [tax   (reasoning/taxonomy kb)
        types (remove (fn [u] (every? #(tax/genl?-global tax % u) syntactic-roots))
                      (into (set (tax/specs-global tax t)) (tax/genls-global tax t)))]
    (for [d     (declarations-naming kb types)
          :let  [preds (sort-by nm/print-key (tax/specs-global tax (second (:sentence d))))
                 under (set preds)]
          h     (concat (keep (fn [[h f]] (when (contains? under f) h)) held)
                        (declaration-candidates kb d preds))]
      h)))

(defn- redecide-holds!
  "Decide `argument-conviction` again for each stored sentex among the handles `hs`, and
  write the moved holds and `:out` memberships (`forced-out?` for a fact no longer held).
  Answers the handles taken out of `:out`, in handle order."
  [kb hs]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)
        out  (volatile! {true [] false []})
        ;; `hs` is lazy, and realizing it reads the candidates
        hs   (with-open [r (progress/start ::hold-candidates "settle: gather the argument hold candidates"
                                           nil)]
               (sort (distinct (progress/each r hs))))]
    (with-open [r (progress/start ::redecide-holds "settle: decide the argument holds again"
                                  (count hs))]
      (doseq [h (cap/hinting (cap/prefetcher recs) cap/recovery-hint-chunk hs)]
        (let [sx  (p/get-sentex recs h)
              on? (some? (argument-conviction kb sx))]
          (when (not= on? (argument/held? kb h))
            (argument/set-held! kb h (some-> sx :sentence nm/functor) on?))
          (when sx
            (let [out? (forced-out? kb sx)]
              (when (not= out? (jtms/forced? tms :out h))
                (vswap! out update out? conj h)))))
        (progress/tick! r)))
    (doseq [[on? ids] @out :when (seq ids)]
      (jtms/set-forced tms :out ids on?))
    (get @out false)))

(defn refresh-argument-holds!
  "Decide the argument holds again for every stored fact and rule a queued write can move
  (`argument/take!`), with `read-under` the taxonomy generations a conviction is read under
  (`special/conviction-generations`): the tuples a declaration stored, removed or
  relabelled constrains, the held ones it constrained, and the rules on the predicates it
  constrains (`rules-on`); the rules on a predicate whose `type_relation_predicate`
  membership moved; under the constraint-only reading, the stored facts naming a term
  whose membership moved; and, when those generations moved, the facts and rules, held or
  not, a moved `genl` edge or separation reaches (`lattice-candidates`), and the tuples
  of the constrained predicates (`constrained-functors`) and the rules stated at or below
  a context whose `genlCx` edges moved; and the tuples a definition stored, removed or
  relabelled can move (`definition-candidates`).  A recover, a rebuilt relation, or a
  move at a value kind reads every declaration whole, with the rules on every
  constrained predicate and `type-level-rules`.  The candidates are read over every
  context, and each is decided from its own (`argument-conviction`).  The queue is taken
  once the lattice candidates are read, so a shutdown that stops the write there
  (`lattice-candidates`) leaves it in place.  Answers the handles taken out of `:out`
  (`redecide-holds!`), or nil when nothing was queued."
  [kb read-under]
  (let [tax (reasoning/taxonomy kb)]
    (when (argument/moved? tax @(reasoning/nogood-candidates kb) read-under)
      ;; one memo for the pass's reads, the candidates' and the decisions' (`pass-read`)
      (binding [*pass-reads*         (volatile! {})
                exc/*reader-states* (or exc/*reader-states* (volatile! nil))]
        (let [{:keys [decls terms kinds defns from owed?]} (argument/queued kb read-under)
              idx          (:index kb)
              symbols?     (not *assertive-arg-types?*)
              constrained? (constrained-functor tax)
              held         (argument/held kb)
              ;; a KB whose taxonomy holds no declaration reads no declaration extent
              whole-scan   (fn [] (concat (keys held)
                                          (when (argument/declares-any? tax)
                                            (concat
                                             (mapcat #(declaration-candidates
                                                       kb % (sort-by nm/print-key (tax/specs-global tax (second (:sentence %)))))
                                                     (all-declarations kb))
                                             (rules-on kb (constrained-functors tax))
                                             (type-level-rules kb tax)))))
              whole?       (or owed? (nil? from) (not= (first from) (first read-under)))
              lattice      (when (and (not whole?) (not= from read-under))
                             (let [[_ g gc sep] from
                                   [_ g' gc' sep'] read-under
                                   ends (cond-> #{}
                                          (not= g g')            (into (tax/moves-since tax :genl g))
                                          (not (identical? sep sep')) (into (tax/separation-moves sep sep')))
                                   cxs  (when (not= gc gc') (tax/moves-since tax :genlCx gc))
                                   hs   (lattice-candidates kb ends symbols? constrained? held)]
                               (if (= ::whole hs)
                                 ::whole
                                 (concat hs
                                         ;; the constrained tuples alone: a context's other
                                         ;; facts are dropped by the filter below
                                         (when (seq cxs)
                                           ;; an end that only gained edges is read by what
                                           ;; its readers gain, the others whole
                                           (let [shrunk (tax/shrinks-since tax :genlCx gc)
                                                 grows  (tax/grows-since tax :genlCx gc)
                                                 edges  (into [] (filter (fn [[a b]] (and (contains? cxs a)
                                                                                          (not (contains? shrunk a))
                                                                                          (contains? (tax/context-parents-global tax a) b))))
                                                              grows)
                                                 gained (when (and grows (seq edges))
                                                          (gained-ends-candidates kb tax edges (constrained-functors tax)))
                                                 ;; an end no grown edge names moved some other way
                                                 shrunk (into shrunk (remove (into #{} (map first) edges)) cxs)
                                                 wide   (if (some? gained) (filterv shrunk cxs) cxs)
                                                 below  (into #{} (mapcat #(tax/context-down-global tax %)) wide)]
                                             (concat
                                              gained
                                              (for [f (constrained-functors tax)
                                                    h (reads/as-stored-with-functor-in idx f below)]
                                                h)
                                              (reads/as-stored-rules-in idx :rule below))))))))
              ;; taken past the lattice read, where a shutdown can stop the write with the
              ;; queue in place
              _            (argument/take! kb read-under)
              hs           (if (or whole? (= ::whole lattice))
                             (whole-scan)
                             (concat
                              lattice
                              (for [[p dc] (sort-by #(nm/print-key (vec %)) decls)
                                    :let   [preds (sort-by nm/print-key (tax/specs-global tax p))
                                            under (set preds)]
                                    h      (concat (keep (fn [[h f]] (when (contains? under f) h)) held)
                                                   (rules-on kb preds)
                                                   (mapcat #(declaration-candidates kb % preds)
                                                           (declarations-of kb p #{dc})))]
                                h)
                              (rules-on kb (sort-by nm/print-key kinds))
                              (mapcat #(definition-candidates kb % held) (sort-by nm/print-key defns))
                              (when symbols?
                                (mapcat #(reads/as-stored-with-term idx %) (sort-by nm/print-key terms)))))]
          (redecide-holds! kb (filter (fn [h] (let [sx (p/get-sentex (:records kb) h)]
                                                (or (argument/held? kb h)
                                                    (rules/rule? sx)
                                                    (and sx (constrained? (nm/functor (:sentence sx)))))))
                                      hs)))))))

(defn forcing-retraction-problem
  "The `:uncleared-forcing` refusal of retracting the sentex at `handle`, as a value, or
  nil: the handle states a forced-monotonic declaration whose predicate has no established unforced
  semantics (`uncleared-forcing`).  The test reads the declaration properties' supporters,
  which are what the sentence alone puts there, and fetches no record.  `where` names the
  entry point."
  [kb handle where]
  (let [tax (reasoning/taxonomy kb)]
    (some (fn [[[functor pred :as decl] missing]]
            (let [kind (declaration-kind functor)]
              (when (contains? (tax/prop-supporter-contexts tax kind pred) handle)
                {:type :uncleared-forcing :handle handle :predicate pred :missing missing
                 :operation where
                 :message (str (pr-str (apply list decl)) " is not retracted: " pred
                               " has no unforced semantics yet (" (name missing)
                               "), so its declaration stays")})))
          uncleared-forcing)))

;; ---- storable values ----------------------------------------------------
;; A sentence's leaves must survive the durable log.  Symbols and keywords (the
;; vocabulary), strings/numbers/chars (the values), and booleans/nil — everything a
;; sentence is built from — always do, and are cleared without a freeze so the assert
;; hot path pays one type-check per leaf and no serialization.  Anything else (a
;; function, an atom/ref, an open stream, a Serializable object off nippy's thaw
;; allowlist) is put through the freeze/thaw pair the on-disk backends run, and refused
;; if either throws — so a value stores in every backend or none, rather than in memory
;; and then throwing at write time on the first disk backend.

(defn- storable-scalar?
  "A leaf nippy always round-trips, recognised without a freeze.  Ordered by how often
  a sentence's leaves are each — the vocabulary (symbols, keywords) and values
  (strings, numbers) first, the rarer nil/boolean/char last."
  [v]
  (or (symbol? v) (keyword? v) (string? v) (number? v)
      (nil? v) (boolean? v) (char? v)))

(defonce ^{:private true
           :tag java.util.concurrent.ConcurrentHashMap
           :doc "Storability memoized by class.  Every value that reaches the freeze probe is a leaf
  that is neither a scalar nor a collection, and for those it is a property of the
  *class* — a `Date` always freezes and thaws, a function never does, and nippy's own
  thaw allowlist is class-keyed — so the probe runs once per class, not once per value.
  A bulk load of dated facts or facts carrying an id then pays one freeze/thaw for the type, not
  one per fact.  Bounded by the distinct non-scalar leaf classes a process ever asserts,
  which is a handful."}
  storable-class-cache
  (java.util.concurrent.ConcurrentHashMap.))

(defn- nippy-storable?
  "Does a value of `v`'s class survive a nippy freeze *and* thaw without throwing — the
  pair the durable log runs on write and read?  Not a `=` round-trip (a byte array and
  other identity-compared values store fine yet would fail it) and not freeze alone (a
  Serializable value off the thaw allowlist freezes and then throws on read); both must
  succeed.  Memoized by class (see `storable-class-cache`): the first value of a class
  runs the probe, the rest read the boolean it cached.

  **The thaw is the one the durable readers run** (`vaelii.impl.io.thaw`), not a bare
  nippy one, so the public entry point and the file readers hold one opinion about what a leaf
  may be.  A class only Java serialization round-trips is refused here rather than
  stored and then refused on the way back off disk — which is the same asymmetry, one
  restart later, that this check exists to close.

  Only an `Exception` is a verdict.  An `Error` — an `OutOfMemoryError` mid-freeze — says
  nothing about the class, so it propagates uncached rather than refusing every later
  value of that class in every KB until the process exits."
  [v]
  (let [c      (class v)
        cached (.get storable-class-cache c)]
    (cond
      (identical? Boolean/TRUE cached)  true
      (identical? Boolean/FALSE cached) false
      :else (let [ok (try (safe/thaw (nippy/freeze v)) true
                          (catch Exception _ false))]
              (.put storable-class-cache c (if ok Boolean/TRUE Boolean/FALSE))
              ok))))

(defn- first-unstorable
  "The first value anywhere in `x` a stored sentence may not carry, as
  `[kind value]` — or nil.  Sequentials are descended; a scalar is cleared without a
  freeze.  Two kinds, and they are two different refusals wearing one `:type`:

  - **`:uncanonical`** — a **map or set** (a record is a map, so it lands here too).
    `sentex/canon` normalizes a sentence's sequentials to `PersistentList` and interns
    its symbols, and it has nothing to do to an unordered collection: two `=` sentences
    differing only in an argument map's implementation or insertion order freeze to
    *different* nippy bytes, which is the hazard `canon` exists to remove
    (docs/canonicalization.md).  `nm/form-rank` has no rank for one either, so
    `compare-form` — every content-keyed tie-break in the engine — has no total order
    over such a sentence, and a tie-break with no order is arrival order.
  - **`:unserializable`** — a leaf whose class does not survive a nippy freeze *and*
    thaw (`nippy-storable?`).

  The uncanonical test comes first because it is the more specific complaint: a map
  full of atoms is refused for being a map, which is the fact that does not go away
  when the atoms do."
  [x]
  (cond
    (storable-scalar? x)   nil
    (or (map? x) (set? x)) [:uncanonical x]
    (sequential? x)        (some first-unstorable x)
    :else                  (when-not (nippy-storable? x) [:unserializable x])))

(defn check-encodable
  "Reject a sentence carrying a value a stored sentence may not carry.

  **Unserializable**: a function, an atom/ref, an open stream — anything nippy cannot
  freeze and thaw — stores in the in-memory backend and then throws at write time on the
  first on-disk backend, so the same assert would succeed or fail by backend.  Refusing
  it here makes the backends agree: a stored sentence's values round-trip.

  **Uncanonical**: a map or a set has no canonical form, so a sentence carrying one has
  neither stable durable bytes nor a content order to tie-break on (`first-unstorable`).
  Refused rather than canonicalized, because there is no ordering of an unordered
  collection that is the *sentence's* — the fix is to write what the KB can order, a
  sequential or a reified term.

  Both throw `:not-encodable`, carrying the offending value under `:value`."
  [sentence]
  (when-let [[kind v] (first-unstorable sentence)]
    (throw (ex-info (if (= :uncanonical kind)
                      (str "value cannot be stored: " (pr-str v) " — a sentence's content"
                           " is EDN scalars and sequentials, and a map or set has no"
                           " canonical form, so it has neither stable durable bytes nor a"
                           " content order to tie-break on (write a sequential — a vector"
                           " of pairs — or reify the structure as a term)")
                      (str "value cannot be stored: " (pr-str v) " of type "
                           (.getName (class v)) " does not round-trip through the durable"
                           " log (nippy) — a sentence's values must be serializable"))
                    {:type :not-encodable :sentence sentence :value v}))))

(defn quantity-shape-problem
  "The `:not-well-formed` problem a non-finite measure magnitude is refused with, or
  nil.  `##Inf` and `##NaN` are `number?`s, and a stored `(QuantityIntervalFn 0 ##Inf
  Second)` makes every duration and metric goal in its context throw a
  NumberFormatException out of the magnitude arithmetic, with no `:type`.  A variable
  magnitude stays legal, since a rule antecedent binds it.  `assert`, `check` and an
  import read it."
  [sentence]
  (when (sequential? sentence)
    (let [bad (fn [x] (and (number? x) (not (Double/isFinite (double x)))))
          q?  #{'QuantityFn 'QuantityIntervalFn}]
      (when-some [t (sx/some-form (fn [form]
                                    (and (sequential? form) (seq form)
                                         (q? (first form)) (some bad (rest form))))
                                  sentence)]
        {:type :not-well-formed :sentence sentence
         :message (str "not well-formed: a measure magnitude must be finite, got "
                       (pr-str t))}))))

;; ---- stratification -----------------------------------------------------
;; The rule-set half of well-formedness: a rule whose `exceptWhen` exception closes
;; a cycle through negation is refused, the way a `genl` cycle is.  The graph itself
;; and the search live in `vaelii.impl.wff`; what lives here is reaching the stored
;; rules, which is the rule index's job — `reads/as-stored-rules-by-consequent-in`
;; answers "what could conclude P?" whatever a rule's direction, so no scan is needed.
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

(def ^:private different-negatives
  "The predicates a `different` antecedent depends on negatively: the relations a fact on
  which withdraws it (`negative-predicates`)."
  (into #{'indeterminate_term 'genl} kb/equality-predicates))

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

  The negative edge from a `different` antecedent runs to every relation that can
  *withdraw* it.  Three assert a merge.  The rest make a term an `indeterminate_term`,
  whose members are exempt from the unique-name assumption, so asserting one withdraws a
  `different` the same way an equality does (docs/predall.md, docs/equality.md).

  Two names carry the indeterminacy half.  `indeterminate_term` is the category itself,
  and a subkind of it needs no name here: `wff/negation-walk` steps from a rule concluding
  a `(vague_kind ?x)` declared under the category to the readers of every predicate in its
  `genls-global` closure, so the category's own edge reaches it.  `genl` is the second,
  and it is the over-approximation this check prefers: a rule concluding `genl` mints a
  subkind the taxonomy does not hold yet, which no fan over the current closure can see.
  It costs a refusal where a rule set reads `different` and concludes any `genl` whatever,
  since the consequent's second argument is a variable at check time.  No shipped rule
  reads `different`, so no KB the ontology builds pays for it.  A skolem's membership is
  structural and no rule concludes one, so it needs no edge.

  All of them run to the concluding relation rather than to `different` itself — nothing
  ever concludes `different`, so an edge keyed on it would reach no rule and find no
  cycle.

  Refusing the cycle is half the answer and `rules/rechecked?` is the other.  A rule that
  merely *reads* `different` closes no cycle and is stored, and the fact that withdraws its
  guard can arrive at any time — so such a rule is registered in the re-check index and its
  firing is re-decided when one does (docs/predall.md)."
  [antecedent-preds neg-query-preds]
  (concat neg-query-preds
          (when (some #(= 'different %) antecedent-preds)
            (nm/sort-by-content-key identity different-negatives))))

(defn- closure-only-predicates
  "The predicates of `negative-predicates` a rule reads only through a `different`
  antecedent: `different-negatives` less its antecedent predicates and `neg-query-preds`.
  `different` reads the stored merges, the stored `indeterminate_term` memberships and
  the stored `genl` edges, so only a rule whose conclusions are stored withdraws it, and
  `wff/negation-walk` takes no edge into such a predicate from a backward-only rule."
  [antecedent-preds neg-query-preds]
  (when (some #(= 'different %) antecedent-preds)
    (reduce disj different-negatives (concat antecedent-preds neg-query-preds))))

(defn- backward-only?
  "Does only the backward chainer run this rule sentex, so that no conclusion of it is
  stored?"
  [sentex]
  (= #{:backward} (:engines sentex)))

(defn- negative-edge-rules
  "Handles of every **stored** rule a negative edge leaves — the presence check on walking at all:
  with none, the stored graph has no negative edge and no cycle through negation.

  Two indexes, because the re-check index is written when a rule is **indexed**.  Its
  `:rules` holds a rule carrying an `exceptWhen`, an `(unknown S)` antecedent, an
  aggregate, a closed-extent negative or a `different` antecedent — `rules/rechecked?`
  is the check, and a `different` one is registered there like the rest, since its firing
  is re-decided when a merge or an indeterminacy withdraws the guard.  A rule stored by a
  build that did not register it is still on the antecedent index, in one lookup under
  `different`, which is the key `rules/antecedent-key` files it under.  The antecedent
  index keeps the refusal right over an index written before the registration existed and
  not yet rebuilt by `reindex`.

  Read `different` out and the presence check under-approximates the graph — a KB whose only
  negative edge is one rule's `different` would skip the walk, and a cycle through it
  would be stored.  Belief is unread on both halves, over-approximating for the reason
  `stratification-readers` does.

  The antecedent lookup sits behind a membership test on the antecedent keys some stored
  rule reads (`reads/stored-rule-key?`).  So a KB no rule of which mentions `different` —
  every KB the shipped ontology builds — reads no rule posting for this half."
  [kb]
  (let [index (:index kb)]
    (cond-> (set (reads/watched-rules index))
      (reads/stored-rule-key? index 'different)
      (into (reads/as-stored-rules-by-antecedent-global index 'different)))))

(defn- rule-graph-node
  "A stored rule as a node of the stratification graph: what it depends on, positively
  (its antecedent predicates) and negatively (the predicates its exceptWhen exceptions
  and its `unknown` antecedents mention, the predicate of a `(not (P …))` a closed-extent
  grant reads as NAF, as an antecedent or inside either kind of query, plus the equality
  relations when it reads `different`).  The exceptWhen predicates come from the rule's
  believed meta-sentexes, `exceptions` (`provers/rule-exceptions`), read through the query frames
  (`rules/watched-predicates`): a cycle runs through what an exception *reads*, and an
  exception that is itself an `(unknown S)` is a negative dependency on `S`'s predicate.

  The antecedents are read as **dependency** predicates, not as index keys: an edge
  joins a reader to a rule whose consequent is filed under a spec of what it reads, and
  a conclusion is filed by `consequent-predicate` — which spells a negation `not` where
  the index key spells it `[:not pred]` (`rules/dependency-predicates`).  The consequent
  is `:concludes-any?` for a rule concluding `(?p …)` that chains, which could conclude
  any predicate (`rules/consequent-index-pred`)."
  ([kb handle rule-sentex]
   (rule-graph-node kb handle rule-sentex (provers/rule-exceptions kb handle)))
  ([kb handle rule-sentex exceptions]
   (let [antes   (rules/dependency-predicates (sx/sentence-of rule-sentex))
         ;; an `:inert` rule with a variable consequent keeps the canonical variable, and
         ;; concludes nothing
         conseq  (rules/consequent-index-pred rule-sentex)
         tx      (reasoning/taxonomy kb)
         ;; `recheck-predicates` less its `different` half, which `negative-predicates`
         ;; adds back and `closure-only-predicates` keeps apart
         negs    (concat (mapcat rules/watched-predicates exceptions)
                         (rules/naf-predicates rule-sentex)
                         (rules/aggregate-predicates rule-sentex)
                         (rules/closed-extent-recheck-predicates-of
                          tx (sx/sentence-of rule-sentex))
                         (rules/closed-extent-query-predicates
                          tx (mapcat identity exceptions)))]
     {:id               handle
      :label            (str "rule#" handle)
      :content          [(sx/sentence-of rule-sentex) (:context rule-sentex)]
      :consequent-pred  (when (symbol? conseq) (when-not (sx/variable? conseq) conseq))
      :concludes-any?   (= p/var-consequent-key conseq)
      :antecedent-preds antes
      :exception-preds  (negative-predicates antes negs)
      :closure-only     (closure-only-predicates antes negs)
      :backward-only?   (backward-only? rule-sentex)})))

(defn- reads-predicate?
  [node g]
  (or (some #(= g %) (:antecedent-preds node))
      (some #(= g %) (:exception-preds node))))

(defn- stored-rule-node
  "The graph node for a stored rule handle — nil if the handle names something that is
  not a rule, which the rule index should never hand back but which a stale posting
  could.  Puts each exceptWhen meta-sentex naming the rule into `believed`, a map, with
  whether it is believed."
  [kb handle ^java.util.Map believed]
  (when-let [rsx (p/get-sentex (:records kb) handle)]
    (when (rules/rule? rsx)
      (let [tms   (reasoning/tms kb)
            metas (provers/stored-exception-metas kb handle)]
        (doseq [m metas] (.put believed (:id m) (jtms/in? tms (:id m))))
        (rule-graph-node kb handle rsx
                         (into [] (comp (filter #(jtms/in? tms (:id %)))
                                        (map #(sx/exception-query-conjuncts (:sentence %))))
                               metas))))))

(defn- stored-stratification-graph
  "The stored rules' half of `stratification-readers`: `{:readers f :starts s …}`, where
  `f` maps a predicate to the stored rule nodes reading it in content order, and with no
  argument answers every stored rule node, and `s` maps an upward closure to the starts of
  a `genl` edge's walk (`wff/negation-starts`).  Each is memoized: the node per rule
  handle, the readers per predicate, the starts per closure.  The rest of the map is what
  `stratification-graph-current?` compares: the index and taxonomy it read, the two
  closed-extent mark sets, and `:believed`, each exceptWhen meta-sentex a node read with
  whether it was believed.  It reads every context and the marks unscoped: the graph is a
  property of every rule the KB stores (`stratification-readers`)."
  [kb]
  (let [index    (:index kb)
        tx       (reasoning/taxonomy kb)
        believed (java.util.HashMap.)
        nodes    (java.util.HashMap.)
        node     (fn [h]
                   (if (.containsKey nodes h)
                     (.get nodes h)
                     (let [n (stored-rule-node kb h believed)] (.put nodes h n) n)))
        ;; content order, since `wff/negation-walk` returns the first cycle it closes, and a
        ;; set of handles iterates in an order the handles decide
        ordered  (fn [handles keep?]
                   (nm/sort-by-content-key :content (filter keep? (keep node (set handles)))))
        by-pred  (java.util.HashMap.)
        every    (delay (ordered (concat (reads/as-stored-rules-in-global index :rule)
                                         (reads/watched-rules index))
                                 some?))
        readers  (fn
                   ([] @every)
                   ([g]
                    (if (.containsKey by-pred g)
                      (.get by-pred g)
                      (let [ante-keys (if (= sx/not-functor g)
                                        (cons g (filter vector? (reads/as-stored-rule-keys index)))
                                        [g])
                            found     (ordered (concat (mapcat #(reads/as-stored-rules-by-antecedent-global index %)
                                                               ante-keys)
                                                       (reads/watched-rules-on index g)
                                                       (when (contains? different-negatives g)
                                                         (reads/as-stored-rules-by-antecedent-global index 'different))
                                                       (when (and (symbol? g) (rules/closed-extent-declared? tx g))
                                                         (reads/as-stored-rules-by-antecedent-global index [:not g])))
                                               #(reads-predicate? % g))]
                        (.put by-pred g found)
                        found))))
        starts   (java.util.HashMap.)]
    {:index      index
     :taxonomy   tx
     :closed     (tax/props tx :closed-extent)
     :closed-arg (tax/props tx :closed-extent-arg)
     :believed   believed
     :readers    readers
     :starts     (fn [above]
                   (or (.get starts above)
                       (let [s (wff/negation-starts readers above)] (.put starts above s) s)))}))

(defn- stratification-graph-current?
  "Does the stored graph `g` still answer for `kb`?  A rule or a re-check posting written
  since, or a rule's engines moving, empties the memo it sits in
  (`rules/*stratification-memo*`); what else a node or a reader read is compared here:
  the index and the taxonomy, the closed-extent mark sets by identity, unscoped as the
  graph reads them, and the belief of each exceptWhen meta-sentex a node read."
  [kb g]
  (let [tx  (reasoning/taxonomy kb)
        tms (reasoning/tms kb)]
    (and (identical? (:index kb) (:index g))
         (identical? tx (:taxonomy g))
         (identical? (tax/props tx :closed-extent) (:closed g))
         (identical? (tax/props tx :closed-extent-arg) (:closed-arg g))
         (every? (fn [[h in?]] (= in? (jtms/in? tms h))) (:believed g)))))

(defn- stratification-graph
  "The stored graph `stratification-readers` reads: the one `rules/*stratification-memo*`
  holds while it is current, else a new one, held there when a pass bound it."
  [kb]
  (let [memo rules/*stratification-memo*
        g    (some-> memo deref)]
    (if (and g (stratification-graph-current? kb g))
      g
      (let [g (stored-stratification-graph kb)]
        (when memo (vreset! memo g))
        g))))

(defn- stratification-readers
  "Predicate -> the rule nodes reading it, positively or negatively, in content order;
  with no argument, every rule node.  `wff/negation-walk` steps from a rule to the readers
  of each predicate at or above its consequent.

  A reader is found through the rule index: the antecedent postings under the predicate
  (every `[:not f]` key for `not`, the dependency spelling of a negated antecedent), the
  re-check postings under it, and the antecedent postings under `different` or `[:not P]`
  where the predicate is one a `different` antecedent or a closed extent makes negative.
  Each candidate's node is read, and kept when its predicates hold the one asked.  Belief
  is unread: refusing a stratified rule set is annoying, accepting an order-dependent one
  is a correctness hole.

  The two-arity adds `pending`, the rule (or exception) being added, after the stored
  readers of each predicate it reads, in place of any stored node with its id: without it
  a rule whose exception mentions what it concludes — a one-rule cycle — would look
  stratified.

  The stored nodes and readers are memoized (`stratification-graph`) for one check, or,
  where an `assert` or a `settle` binds `rules/*stratification-memo*`, for each of its
  checks until a rule, a re-check posting, a closed-extent mark or an exception's belief
  moves (docs/exceptions.md, \"The search\").

  The `closed_extent` mark is read unscoped: the stratification graph is a property of
  every rule the KB stores (`wff/negation-walk`)."
  ([kb] (stratification-readers kb nil))
  ([kb pending]
   (let [readers (:readers (stratification-graph kb))]
     (if-not pending
       readers
       (let [pid  (:id pending)
             with (fn [nodes keep?]
                    (cond-> (filterv #(not= pid (:id %)) nodes)
                      (keep? pending) (conj pending)))]
         (fn
           ([] (with (readers) some?))
           ([g] (with (readers g) #(reads-predicate? % g)))))))))

(defn check-stratified
  "Throw unless adding this rule leaves the rule set stratified — see
  docs/exceptions.md.  Runs before anything is stored, so a refused rule leaves no
  partial state behind.

  Fast path: with no negative edge on the rule being added and none on any stored rule
  (`negative-edge-rules`), the graph has no negative edge at all and no cycle through
  negation is possible, so the walk is skipped entirely.  That is every rule in an
  ontology that uses no negative dependency — no exception, no `unknown`, no aggregate,
  no closed-extent negative and no `different` — which is most of them."
  [kb sentence inner context]
  (let [[_ _ exception] (sx/peel-rule-wrapper sentence)
        ;; dependency spelling, not the index key: `rule-graph-node` says why
        antes             (rules/dependency-predicates inner)
        ;; negatives: the exception's predicates, the `unknown` antecedents', the
        ;; **aggregate** bodies' *and* the predicate of a `(not (P …))` a closed extent
        ;; reads as NAF, as an antecedent or inside either kind of query.  All four read
        ;; what the KB believes rather than a fact the firing names, so a cycle through any
        ;; of them is unstratified — a rule whose count is over a relation the rule itself
        ;; concludes has no settled answer, and which one it lands on would depend on
        ;; arrival order.
        tx                (reasoning/taxonomy kb)
        neg-queries       (concat (rules/watched-predicates exception)
                                  (rules/naf-predicates-of inner)
                                  (rules/aggregate-predicates-of inner)
                                  (rules/closed-extent-recheck-predicates-of tx inner)
                                  (rules/closed-extent-query-predicates tx exception))
        negatives         (negative-predicates antes neg-queries)]
    ;; The fast path skips the walk when the graph has no negative edge at all — and a
    ;; `different` antecedent counts as one on both sides, so a rule that reads the
    ;; equality closure is walked, and a *stored* one keeps the walk alive for a rule
    ;; arriving above it that carries no negative edge of its own.
    (when (or (seq negatives) (seq (negative-edge-rules kb)))
      (let [conseq  (rules/consequent-predicate inner)
            pending {:id               ::pending
                     :label            "the rule being asserted"
                     :antecedent-preds antes
                     :exception-preds  negatives
                     :closure-only     (closure-only-predicates antes neg-queries)
                     :backward-only?   (backward-only? (sx/sentex sentence context))
                     :consequent-pred  (when-not (sx/variable? conseq) conseq)
                     :concludes-any?   (sx/variable? conseq)}]
        (when-let [cycle (wff/negation-cycle (reasoning/taxonomy kb)
                                             (stratification-readers kb pending)
                                             pending)]
          (throw (ex-info (str "not stratified: " (pr-str inner) " would close a cycle"
                               " through negation: " (wff/cycle-description cycle)
                               " — a rule set is stratified when no predicate reaches"
                               " itself through a negative edge, so break the cycle at"
                               " one of the rules named, or conclude into a predicate"
                               " off that path")
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
    (throw (ex-info (str "a do/ imperative cannot appear in a rule: " (pr-str bad)
                         " — a rule is evaluated inside the forward-chaining fixpoint,"
                         " where an imperative runs a number of times that depends on"
                         " firing order.  Assert it on its own, at the top level of an"
                         " assert, where the caller decides when it runs")
                    {:type :not-assertible :form bad :sentence sentence}))))

(defn check-no-defeat
  "Refuse a `defeat` literal anywhere `nm/literals` descends: a fact, a `not`, a rule's
  antecedents and consequent, an `exceptWhen` query.  Throws `:derived-only`.

  The engine derives every `(defeat (sentexHandle H))` (docs/nmtms.md): a placed nogood
  stores one for its unique weakest member.  A defeat written as a premise would remove a
  handle from belief whatever its class, and a rule reading one would fire on a read-time
  verdict.  The check reads the sentence alone, so it refuses the same sentence in every
  KB and every arrival order.  Matching and asking `(defeat ?h)` are reads and pass no
  check."
  [sentence]
  (when-let [[_ lit] (first (filter #(= sx/defeat-functor (nm/functor (second %)))
                                    (nm/literals sentence)))]
    (throw (ex-info (str "defeat is derived by the engine and cannot be asserted: "
                         (pr-str lit) " in " (pr-str sentence)
                         " — a placed nogood stores the defeat of its weakest member")
                    {:type :derived-only :form lit :sentence sentence}))))

;; ---- generators: the refusals a rule concluding a rule owes ---------------
;; A generator is a rule and passes everything a rule passes.  What follows is what it
;; owes *as* a generator, and every one of them is asked of each nesting level, since a
;; generated rule may generate one in turn and each level reaches the store as a rule in its
;; own right (docs/generators.md).

(defn- stored-generators
  "Every stored generator, as `[handle sentex]` pairs.

  One index lookup, and the cell it reads is the one that looks like a junk posting:
  `rules/consequent-predicate` reads the functor of what a rule concludes, and what a
  generator concludes is a rule — so every generator in the KB is filed under `implies`
  and nothing else is, at any nesting depth.  Nothing backward-chains through it (a
  generator is forward-only, and no goal's functor is `implies`), which leaves it doing
  exactly this one job.

  **Content-ordered**, because `generator-cycle` names one of these in a refusal
  message — verbatim, by handle.  The index cell is a *set*, so where three generators
  each close the cycle, an unordered walk would blame whichever the set yielded first,
  which is the arrival order that whole check exists to keep out.  One list per KB, and
  a KB's generators are a handful of rules.

  **As stored, and a defeated generator is listed** — the entry point is the as-stored one on
  purpose.  What reads this is `generator-cycle`, a stratification refusal, and a cycle is
  a property of what the KB has *written*: a generator whose support is withdrawn is
  retained and revivable, so filtering it out would accept a program today and refuse it
  after a retraction somewhere else revives the rule that closes the loop.  A refusal that
  moves with belief is a refusal nobody can act on."
  [kb]
  (nm/sort-by-content-key
   (fn [[_ s]] [(sx/sentence-of s) (:context s)])
   (into []
         (comp (keep (fn [h] (when-let [s (p/get-sentex (:records kb) h)] [h s])))
               (filter (fn [[_ s]] (rules/generator-sentex? s))))
         (reads/as-stored-rules-by-consequent-global (:index kb) sx/rule-functor))))

(defn- generated-conclusion-predicate
  "The predicate a generator eventually concludes — the **innermost** rule's, through
  however many levels of generation stand between.  The levels in between conclude rules,
  and nothing reads a sentence under the `implies` key as a fact; what reaches the fact
  store is the innermost conclusion, so that is the predicate a cycle can run through."
  [sentence]
  (rules/consequent-predicate (rules/innermost-rule sentence)))

(defn- generator-reads
  "The predicates whose arrival makes this generator **generate** — the antecedents of
  every level but the innermost.  The innermost rule's antecedents are excluded on
  purpose: they trigger the rule that was generated, which concludes a fact, and a fact is
  not what makes the rule set grow."
  [sentence]
  (into #{} (mapcat #(keep nm/functor (:antecedents %)))
        (butlast (rules/nesting sentence))))

(defn generator-cycle
  "A description of the cycle adding this generator would put in the rule set, or nil.

  The graph is generators only, and one hop: an edge runs from a generator to any
  generator that reads — in an antecedent it generates from — the predicate its generated
  rule concludes.  A cycle there is a rule set that mints rules that mint rules, and
  unlike ordinary recursion nothing bounds it: each round adds *rules* rather than
  facts, and the next round's rules are the ones the last round wrote.

  Refused outright rather than depth-capped.  A cap would make the KB's contents a
  function of how long the chainer happened to run, and \"how many rules does this KB
  have\" would stop having an answer — the same call stratification makes for a cycle
  through negation (docs/exceptions.md).  It is also why *nesting* is not a cap worth
  having: a nested generator generates one level further before it stops, and what makes a
  rule set unbounded is the cycle, not the depth.

  **Both directions, because either can be the new edge**: the arriving generator may
  generate what a stored one reads, or read what a stored one generates, and a self-loop is
  the case where it does both to itself.  Checking only one direction would let the
  cycle in whenever the two generators were asserted in the other order — which is the
  order dependence every check here exists to keep out."
  [kb inner context]
  (when (rules/generated-rule (rules/consequent inner))
    (let [concl  (generated-conclusion-predicate inner)
          reads  (generator-reads inner)
          gens   (stored-generators kb)
          where  (or (when (and concl (reads concl)) "itself")
                     (some (fn [[h s]]
                             (when (and concl (contains? (generator-reads (sx/sentence-of s))
                                                         concl))
                               (str "the generator at handle " h)))
                           gens)
                     (some (fn [[h s]]
                             (when-let [p (generated-conclusion-predicate (sx/sentence-of s))]
                               (when (reads p)
                                 (str "the generator at handle " h
                                      ", which generates a rule concluding " p))))
                           gens))]
      (when where
        (str "the rule it generates concludes " concl
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

  **No `exceptWhen` on a generated rule.** An exception is not a rule field — it is a
  separate meta-sentex keyed by the rule's handle, split off and stored by the assert
  path (`assert-exceptWhen-meta!`), which a firing does not run.  So a generated
  `exceptWhen` would reach the store as nothing at all: the mint would be a rule whose
  guard had silently evaporated, firing on exactly the bindings its author wrote it not
  to.  A guard that is dropped in silence is worse than one refused, so it is refused.
  An `exceptWhen` on the **outermost** rule is a different and legal thing — it says
  when the generator does not fire — and the message points there.

  **No generator cycle.** A generated rule whose conclusion feeds some generator's
  antecedent is a rule set that mints rules that mint rules, with no fixpoint anybody
  has bounded.  Refused outright rather than capped, the same call stratification makes
  for a cycle through negation: the alternative is a KB whose size depends on how long
  the chainer was allowed to run.

  Read by both storage entry points through `check-rule!`, so a generator a *firing* generates
  owes exactly what one an author wrote owes — which is the whole of what makes nesting
  safe: the middle level is checked twice, once as a pattern and once as the rule it
  became."
  [kb sentence context]
  (let [inner  (rules/inner-rule sentence)
        levels (rules/nesting sentence)
        ;; `peel-rule-wrapper` reports the wrapper it found, and a bare rule has none —
        ;; the record's default is what nil means here, as it does at the constructor.
        ;; Every sentence this runs on is a generator, and a bare generator defaults to
        ;; :forward at the constructor (a backward generator is meaningless), so nil is
        ;; :forward here.  A level's own wrapper rides the consequent of the level above
        ;; it, which is where a generated rule's direction is written.
        dirs   (cons (or (first (sx/peel-rule-wrapper sentence)) :forward)
                     (map #(or (first (sx/peel-rule-wrapper (:consequent %))) :forward)
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
      (when-not (contains? #{:forward :both :inert :forward-only} dir)
        (throw (ex-info (str "a rule generator is forward-only: its conclusion is a rule,"
                             " and no backward goal asks for one.  Drop the"
                             " set/backwardRule wrapper — the wrapper on the innermost"
                             " rule is what sets that rule's direction")
                        {:type :not-indexable :direction dir :sentence sentence
                         :nesting-level (inc i)}))))
    (when-let [cyc (generator-cycle kb inner context)]
      (throw (ex-info (str "a rule generator cannot generate a rule that feeds a"
                           " generator: " cyc
                           " — each round of that loop generates the rules the next round"
                           " reads, so nothing bounds the rule set.  Assert one of those"
                           " rules directly instead of generating it")
                      {:type :not-stratified :sentence sentence :context context
                       :cycle cyc})))))

(defn check-rule-shape
  "The refusals of `check-rule!` that read nothing from the KB, in its order: a `do/`
  imperative anywhere in the rule, an `or` no expansion removes, a consequent variable no
  antecedent binds, an open NAF literal, and a variable antecedent functor on a rule that
  is not `:inert` (an inert rule runs in neither engine, so the index owes it nothing).
  `check-rule!` runs this first, and a dump import runs it over each rule frame, which
  may not read the KB: a declaration or rule the frame depends on may arrive later in
  the stream (docs/naming.md)."
  [sentence]
  (let [inner       (rules/inner-rule sentence)
        [direction] (sx/peel-rule-wrapper sentence)]
    ;; on the sentence **as written**, not on `inner`: `inner-rule` peels the
    ;; `exceptWhen` wrapper and takes the exception query with it, so guarding the
    ;; inner rule let an imperative through in the one rule slot that is re-evaluated
    ;; most often
    (check-no-imperative sentence)
    (check-no-defeat sentence)
    ;; An `or` the polycanonicalization can expand away is gone by the time `assert` or
    ;; the mint reaches here, since both store the *expansion*.  What is left is the rule
    ;; that could not be expanded: one over `rules/max-alternatives`, or one whose `or`
    ;; sits where nothing expands it.  The assert entry point refuses it at the shape
    ;; guard, before the split; the mint and the import have only this list.
    (rules/check-disjunction! sentence)
    (rules/check-range-restricted (rules/antecedents inner) (rules/consequent inner))
    ;; The NAF-literal checks — closure, quantifier locality, the reduction slot, a
    ;; quantified or empty conjunction.  The sentex constructor runs these too; here
    ;; they run before anything is built, so `core/check`, which constructs no sentex,
    ;; predicts them.
    (sx/check-naf-closed (rules/antecedents inner) (rules/consequent inner) nil)
    (when-not (= :inert direction)
      (rules/check-indexable-functors inner))))

(defn check-rule!
  "Every pre-storage check a rule must pass, as a step that writes nothing.

  **Two entry points store a rule** and this is the list both read.  `core/assert` stores one
  an author wrote; a generator firing stores one the KB derived
  (docs/generators.md).  What a rule has to *be* does not depend on which entry point it came
  through, so a copy per entry point is the drift this exists to prevent — a check added at
  the assert entry point that the mint never learned would let the fixpoint store what the
  API refuses.

  Factored out of the assert path so `assert` can also run it over **all** the
  conjuncts of a polycanonicalized rule before storing *any* of them.
  `(implies A (and C1 C2))` is split into one rule per conjunct and then `mapv`d,
  and a `mapv` is not a transaction: with the checks inline, a refusal on C2 leaves
  C1 already stored, indexed, and chained from, while the caller sees a throw and
  reasonably concludes nothing was asserted.

  One arm here refuses only under `*refuse-clashes?*` (`try-assert`):
  `check-variable-constraints!`, which holds a rule's shared variables to the argument
  constraints of every position they stand in.  `assert` stores a rule that arm convicts
  and holds it inert (`hold-rule-conviction!`).

  A **generator** owes three more (`check-generator!`), and they run last so the
  sharper complaint comes first: a rule that is unbound *and* backward-only is refused
  for the unbound variable, which is the one its author can act on."
  [kb sentence context]
  (let [inner (rules/inner-rule sentence)]
    (check-rule-shape sentence)
    (nm/check! (:naming kb) inner context)
    ;; the argument constraints the rule's own variables carry, checked against each
    ;; other, refused under `try-assert` alone; `assert` stores the rule and holds it
    ;; inert.  After naming because it reads declarations off the functors naming just
    ;; passed.
    (check-variable-constraints! kb inner context)
    ;; the rule-set check, before anything is stored: an `exceptWhen` is negation as
    ;; failure, and a cycle through it would make the settled state depend on
    ;; arrival order (docs/exceptions.md)
    (check-stratified kb sentence inner context)
    (when (rules/generator? sentence)
      (check-generator! kb sentence context))))

(defn rule-violation
  "`check-rule!` as a **value** in the form the derivation path files — a
  `{:violation :detail}` map, or nil when the rule stands.

  The mint's form of the same list, and the reason it is a value is the reason every
  check on that path is: a firing runs inside the fixpoint, an exception escaping it
  would leave belief half-computed, and which rule happened to fire first would decide
  what the KB ends up believing.  So a mint that cannot stand is dropped and recorded
  (`violations/report`), never thrown.

  Read through the throwing form rather than restating it, so the two cannot drift —
  the same trick `core/check` plays to predict `assert`."
  [kb sentence context]
  ;; a mint the `:arg-variable` arm convicts is stored and held inert, also when a
  ;; `try-assert`'s write fires it
  (try (binding [*refuse-clashes?* false] (check-rule! kb sentence context)) nil
       (catch clojure.lang.ExceptionInfo e
         ;; `:sentence` and `:context` are dropped because the caller re-attaches its
         ;; own — the mint's, which is the rule that was actually refused — and a
         ;; stale copy under the same key would shadow it.  They come off in a step of
         ;; their own, and the type keyword last: the refusal-vocabulary scan reads
         ;; the token *following* a type keyword as a refusal type, so listing them in
         ;; one `dissoc` files whichever argument happened to sit there as caller-visible
         ;; vocabulary (`type_contract_test`).
         (let [d      (ex-data e)
               detail (dissoc d :sentence :context)]
           {:violation (get d :type :not-well-formed)
            :detail    (assoc (dissoc detail :type) :message (.getMessage e))}))))

(defn check-exceptWhen-stratified
  "Throw unless adding the exceptWhen exception with conjuncts `exc` to the stored rule
  `rule-handle` leaves the rule set stratified.

  The exception is a new negative edge from the rule to the predicates it reads
  (`rules/watched-predicates`, and the predicate of a `(not (P …))` a closed extent reads
  as NAF, `rules/closed-extent-query-predicates`), so it can close a cycle through
  negation exactly as a whole rule can (`check-stratified`).  The pending node is the
  rule's stored graph node augmented with the new negative edges;
  `stratification-readers` swaps it in for the stored rule so the walk sees the edge.
  Runs before the meta-sentex is stored, so a refused exception leaves nothing behind."
  [kb rule-handle exc context]
  (when-let [rsx (p/get-sentex (:records kb) rule-handle)]
    (let [new-exc-preds (distinct (concat (rules/watched-predicates exc)
                                          (rules/closed-extent-query-predicates
                                           (reasoning/taxonomy kb) exc)))
          base          (rule-graph-node kb rule-handle rsx)
          pending       (assoc base
                               :label           (str "rule#" rule-handle " (with the new exception)")
                               :exception-preds (concat (:exception-preds base)
                                                        (negative-predicates (:antecedent-preds base)
                                                                             new-exc-preds))
                               :closure-only    (reduce disj (:closure-only base) new-exc-preds))]
      (when (seq (:exception-preds pending))
        (when-let [cycle (wff/negation-cycle (reasoning/taxonomy kb)
                                             (stratification-readers kb pending)
                                             pending)]
          (throw (ex-info (str "not stratified: the exception on rule#" rule-handle
                               " reads " (pr-str (vec new-exc-preds)) " and would close a"
                               " cycle through negation: " (wff/cycle-description cycle)
                               " — a rule set is stratified when no predicate reaches"
                               " itself through a negative edge, so guard the rule with"
                               " an antecedent instead, or write the exception over a"
                               " predicate off that path")
                          {:type :not-stratified :rule rule-handle :context context
                           :exception-preds (vec new-exc-preds) :cycle cycle})))))))

(def ^:private closed-extent-grant-arities
  "The functors that grant a closed extent on their first argument's predicate, each with
  the length of its sentence: the whole-predicate grant, the per-argument grant, and the
  per-argument grant's binary spellings, which CxUniverse's forward rules turn into the
  ternary.  The binary spellings are checked here as well, because a derived ternary
  reaches no assert-time check."
  '{closed_extent_predicate 2
    closedExtentForArg      4
    closedExtentForArg1     3
    closedExtentForArg2     3
    closedExtentForArg3     3
    closedExtentForArg4     3
    closedExtentForArg5     3})

(defn check-closed-extent-stratified
  "Throw `:not-stratified` unless declaring `(closed_extent_predicate P)`,
  `(closedExtentForArg P n v)` or a binary spelling of the second leaves the rule set
  stratified; nil for any other sentence.  The walk starts at each stored rule the grant
  governs (`provers/closed-extent-rules`: a closed `(not (P …))` antecedent, or one inside
  an `unknown` antecedent, an aggregate body or an `exceptWhen` query), in content
  order, so two rules that each close a cycle give one refusal.  It runs before anything
  is written (docs/naf.md, \"Stratification, from both arrival orders\")."
  [kb sentence context]
  (when (and (sequential? sentence)
             (= (get closed-extent-grant-arities (nm/functor sentence)) (count sentence)))
    (let [pred (second sentence)]
      (when-let [[node cycle]
                 (->> (provers/closed-extent-rules kb pred)
                      (keep (fn [rh] (some->> (p/get-sentex (:records kb) rh) (vector rh))))
                      (nm/sort-by-content-key (fn [[_ rsx]] [(sx/sentence-of rsx) (:context rsx)]))
                      (keep (fn [[rh rsx]]
                              (let [base    (rule-graph-node kb rh rsx)
                                    pending (assoc base
                                                   :label (str "rule#" rh
                                                               " (under the closed extent)")
                                                   :exception-preds
                                                   (concat (:exception-preds base)
                                                           (negative-predicates
                                                            (:antecedent-preds base) [pred]))
                                                   :closure-only
                                                   (disj (:closure-only base) pred))]
                                (when-let [c (wff/negation-cycle
                                              (reasoning/taxonomy kb)
                                              (stratification-readers kb pending)
                                              pending)]
                                  [pending c]))))
                      first)]
        (throw (ex-info (str "not stratified: " (pr-str sentence)
                             " would close a cycle through negation: "
                             (wff/cycle-description cycle)
                             " — the grant reads every closed (not …) antecedent on that"
                             " path as negation as failure, so leave the predicate open,"
                             " or break the cycle at one of the rules named")
                        {:type :not-stratified :sentence sentence :context context
                         :rule (:id node) :cycle cycle}))))))

(defn- edge-negation-cycle
  "The cycle through negation that adding this `genl` sentence would create among the
  **stored** rules, or nil.  Nil for anything else: a `genlCx` edge moves no edge of the
  graph, which reads the `genl` closure alone.

  `wff/genl-negation-cycle` walks once, from the rules the edge's added graph edges point
  to.  Three tests skip the walk, in this order: the edge's upper end is already in the
  unscoped closure of its lower end; no stored rule carries a negative edge
  (`negative-edge-rules`); no stored rule concludes `(?p …)`, `a` or a spec of `a`, read
  off the consequent index in that order, the specs from `a`'s unscoped spec closure
  while it holds at most the stored rule count.  Each test's reason is
  docs/exceptions.md, \"A taxonomy edge closes a cycle too\".

  The edge is added to a **detached copy** of the taxonomy rather than to the real
  one: the check runs before anything is written, and a refused edge must leave the
  cached closures untouched as well as the store."
  [kb sentence]
  (when (= 'genl (nm/functor sentence))
    (let [[_ a b]    sentence
          tax        (reasoning/taxonomy kb)
          index      (:index kb)
          concludes? #(seq (reads/as-stored-rules-by-consequent-global index %))
          below?     (fn []
                       (or (concludes? p/var-consequent-key)
                           (concludes? a)
                           (if-some [specs (tax/specs-global-within
                                            tax a (reads/stored-rule-count-global index))]
                             (boolean (some concludes? (disj specs a)))
                             true)))]
      (when-not (or (tax/genl?-global tax a b) (empty? (negative-edge-rules kb)) (not (below?)))
        (let [probe (tax/detached-copy tax)
              graph (stratification-graph kb)]
          (tax/add-genl probe a b ::probe)
          (wff/genl-negation-cycle probe (:readers graph) (:starts graph) a b))))))

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
                         " would close a cycle through negation: "
                         (wff/cycle-description cycle)
                         " — the edge fans each rule's negative dependencies over the"
                         " specs below it, so break the cycle at one of the rules named,"
                         " or place the edge under a type off that path")
                    {:type :not-stratified :sentence sentence :context context
                     :cycle cycle}))))

;; (`wff-violation` — structural well-formedness as a value, for derived content —
;; lives in `vaelii.impl.special` now: the per-functor wff dispatch is a column of
;; the special-predicate table, which sits a layer above this namespace.)

(defn edge-stratification-violation
  "The same check as a **value**, for a `genl` edge a rule *derived*
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

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(caches/register-derived
 {:id :K8 :label "Storable classes" :kind :cache :keyed-by :value :reads [] :retired-by {}
  :holds-content? false
  :computed :read :imaged? false :var #'storable-class-cache
  :value (fn [_] storable-class-cache)
  :note "class to whether a value of it can be stored; content-keyed, bounded by the classes seen"})
