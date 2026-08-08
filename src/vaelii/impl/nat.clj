;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.nat
  "Non-atomic terms (NATs) via reification — Strategy A.

  A NAT is a function-application term `(F arg…)` that denotes an entity —
  `(FruitFn AppleTree)`, `(CapitalOf France)`.  A function splits by declaration
  into two kinds:

    (reifiableFunction F)    object-denoting.  A ground `(F a…)` is a **reified NAT**: it
                             reifies to an opaque `nat/`-namespaced constant `K`
                             *before* it reaches the index, so the reified NAT autoindexes
                             exactly like a hand-minted symbol — no trie-key change,
                             no term-index change.
    (unreifiableFunction F)  evaluated/interpreted.  The NAT is a **structural NAT** and stays
                             *structural* — `(QuantityFn 5 Meter)` keeps its magnitude
                             and unit readable for a downstream prover; it is never
                             minted.

  The constant↔expression map is itself an ordinary stored fact, `(termOfUnit K E)`
  in UniverseContext, so the inverted term index makes `E`'s constituents (and `K`)
  discoverable natively — no KV side tables.  `K` stays STABLE across renames: a
  rename rewrites the expression inside the one `termOfUnit` sentex in place, and
  nested NATs referencing `K` need no cascade.

  This namespace holds the detectors, the index-backed lookups, display expansion,
  and the reify — **both** modes: the read-mode (dedup, never mint) and the
  write-mode (mint a fresh constant, materialize its result types, merge rename
  collisions).  The write-mode stores its `termOfUnit` and result-type facts through the
  full assert path, reached by `vaelii.impl.wiring` — which is where the reason that is
  not an ordinary require is written down.  So all NAT reification lives here.

  What sits above this and *calls* the reify rather than reimplementing it:
  `vaelii.impl.skolem` mints the witness an existential rule head fires to, and
  `vaelii.core` drops an orphaned reified NAT when its last use is retracted (it rides the
  `retract!` sweep).

  Reads the store, the taxonomy and belief directly (nat <- kb); reaches assertion only
  through the seam above."
  (:require [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.wiring :as wiring]))

(def nat-namespace
  "Reserved namespace for reified-NAT constants.  The cheap detector the
  display and mutation layers key on — a symbol is a reified NAT iff its namespace
  is exactly this."
  "nat")

(def universal-context
  "Where every NAT bookkeeping fact lives — `(reifiableFunction F)`, `(termOfUnit K
  E)`, `(resultIsa F T)`, and a minted reified NAT's materialized types — so it is visible
  from every context, matching the other universal vocabulary."
  'UniverseContext)

(def no-match
  "The reserved `nat/` constant a read-mode reify resolves an unknown (never-minted)
  NAT to.  It can never be a real minted constant, so a query carrying it matches
  nothing — an unknown-NAT query returns empty without minting.  Never written,
  never displayed."
  'nat/no-match)

(def nat-quoting-predicates
  "Predicates whose NAT-bearing argument is a *quoted* expression and must NOT be
  reified or type-checked as a term: the arg holds the literal NAT being mapped
  (`termOfUnit`) or reified-to-a-real-term (`rewriteOf`)."
  '#{termOfUnit rewriteOf})

(defn reified-nat-symbol?
  "True iff `term` is a reified-NAT constant — a symbol in the `nat/`
  namespace."
  [term]
  (and (symbol? term) (= nat-namespace (namespace term))))

(defn fresh-constant
  "Allocate a fresh, opaque `nat/`-namespaced reified NAT constant.  Only ever appears in
  argument position, so `naming/problems` (which checks functors, not arguments)
  never sees it as a functor and needs no exemption."
  []
  (symbol nat-namespace (name (gensym "g"))))

;; ---- the reifiable gate --------------------------------------------------
;; A function's kind is predicate metadata, cached in the taxonomy like
;; transitive/symmetric/functional: `(reifiableFunction F)` marks the `:reifiable`
;; prop, `(unreifiableFunction F)` the `:unreifiable` one (both belief-following,
;; via `vaelii.impl.special`'s prop-entry).  So the per-sentence gate is a free
;; in-memory set read — no index probe, no mtime cache to keep coherent.

(defn any-reifiable-functions?
  "Cheap gate: does the KB declare any reifiableFunction?  False ⇒ no sentence can
  contain a reifiable NAT, so the reify pass and the rename/remove NAT steps
  short-circuit to a no-op.  An in-memory taxonomy-prop read."
  [kb]
  (boolean (seq (tax/props (:taxonomy kb) :reifiable))))

(defn reifiable-function?
  "True iff `(reifiableFunction head)` is believed.  Read straight off the taxonomy
  metadata, so it is context-independent — deliberately, since reification decides
  *term identity*, which cannot vary by reader — and belief-following: a defeated or
  retracted declaration stops the function reifying."
  [kb head]
  (and (symbol? head)
       (not (reified-nat-symbol? head))
       (tax/has-prop? (:taxonomy kb) :reifiable head)))

(defn- ground-form?
  "True iff `form` contains no pattern variables anywhere (any nesting)."
  [form]
  (not-any? sx/variable? (tree-seq sequential? seq form)))

(defn reifiable-ground-nat?
  "True iff `form` is a ground `(F …)` whose head F is a reifiableFunction — a NAT we
  may reify.  Ground because an open NAT (`(F ?x)`) would need an enumerating prover to
  mint anything, so it is left alone."
  [kb form]
  (and (seq? form)
       (seq form)
       (reifiable-function? kb (first form))
       (ground-form? form)))

;; ---- index-backed lookups ------------------------------------------------
;; `E → K` (dedup) and `K → E` (reverse) are both `(termOfUnit …)` queries — the
;; functor/argument roots answer them, so no new IndexStore method is needed.  Reads
;; are belief-filtered by `kb/sentexes-matching`, so a superseded spelling (a renamed reified NAT's old
;; expression) does not answer.

(defn nat-expression
  "The NAT expression a reified constant denotes, or nil."
  [kb nat-sym]
  (when (reified-nat-symbol? nat-sym)
    (some-> (first (kb/sentexes-matching kb (list 'termOfUnit nat-sym '?e) universal-context))
            :sentence
            (nth 2))))

(defn dedup-constant
  "The existing reified constant for the ground NAT expression `E`, or nil — the
  `E → K` half of the 1:1 map, so re-reifying an expression finds the constant
  already minted for it rather than minting a second."
  [kb E]
  (some-> (first (kb/sentexes-matching kb (list 'termOfUnit '?k E) universal-context))
          :sentence
          second))

(defn rewrite-target
  "The real term `T` a `(rewriteOf T E)` declaration says the NAT expression `E`
  reifies to instead of a fresh constant, or nil.  A quoting-predicate declaration:
  `E` is the literal NAT payload, `T` an existing atomic term."
  [kb E]
  (some-> (first (kb/sentexes-matching kb (list 'rewriteOf '?t E) universal-context))
          :sentence
          second))

(defn- result-targets
  "The distinct arg2s of believed `(<pred> head ?t)` facts — the result types of the
  reifiable function `head` under `pred`."
  [kb pred head]
  (->> (kb/sentexes-matching kb (list pred head '?t) '?ctx)
       (keep #(nth (:sentence %) 2))
       distinct))

(defn result-isa-types
  "Types `T` with `(resultIsa head T)` — materialized as `(T K)` on a freshly minted
  reified NAT whose function is `head` (its output is an *instance* of T)."
  [kb head] (result-targets kb 'resultIsa head))

(defn result-genl-types
  "Types `T` with `(resultGenl head T)` — materialized as `(genl K T)` on a freshly
  minted reified NAT whose function is `head` (its output is a *subtype* of T)."
  [kb head] (result-targets kb 'resultGenl head))

;; ---- the corresponding predicate -----------------------------------------
;; `(functionCorrespondingPredicate F P N)` states that a function and a predicate say
;; the same thing: `F` maps `a₁ … a_M` to `V` exactly when `(P a₁ … a_{N-1} V a_N …
;; a_M)` holds.  `N` is 1-based over `P`'s arguments, and omitting it puts the value
;; **last** — `(functionCorrespondingPredicate MotherFn motherOf)` makes `(MotherFn
;; Muffet)` the `?v` of `(motherOf Muffet ?v)`, which is the shape nearly every
;; correspondence has.
;;
;; It is read in **both** directions, and that is the whole of its point: an ontology
;; that reifies a function and its predicate separately otherwise says one thing twice
;; and can reason with only whichever half it was told.
;;
;;   value → term   a believed `(motherOf Muffet Mary)` reifies `(MotherFn Muffet)` to
;;                  `Mary`, so the expression names the object the KB already has a
;;                  name for instead of minting a second one beside it.
;;   term → value   a constant minted because no value was known yet is *projected*
;;                  back onto the predicate — `(motherOf Muffet K)` — so the placeholder
;;                  answers that predicate's questions rather than being a term
;;                  nothing says anything about.
;;
;; The two meet when the value arrives after the mint, and that is the case order
;; independence turns on: the projected fact and the new one are two values for one
;; application, so `reconcile-correspondence!` equates them and the migration folds the
;; constant away.  Declaring the correspondence *last* is reconciled the same way.
;;
;; A correspondence bites only on a `reifiableFunction`: an undeclared function's
;; application is left a raw compound the reify pass never visits.

(def correspondence-predicate
  "The declaration relating a NAT function to the predicate stating the same thing."
  'functionCorrespondingPredicate)

(defn any-corresponding-predicates?
  "Cheap gate: does the KB declare any `functionCorrespondingPredicate`?  An O(1)
  functor count, so a KB that declares none pays one integer read per assert and
  nothing else."
  [kb]
  (pos? (p/count-with-functor (:index kb) correspondence-predicate)))

(defn- believed-correspondences
  "Believed correspondence declarations as `[function predicate position-or-nil]`
  triples, kept where `match?` holds of the triple.

  Read from the **functor root alone** and filtered in memory rather than narrowed on
  an argument root: the declarations number one per reified function and so are few,
  where the position-2 argument roots hold every fact ever asserted about `P` — and this is
  asked once per assert, which is the last place to make a cost a function of the
  corpus.  Belief is filtered here rather than through `kb/sentexes-matching`: the
  declaration has two legal arities, and a pattern query would need one probe per arity
  to see both."
  [kb match?]
  (when (any-corresponding-predicates? kb)
    (->> (p/sentexes-with-args (:index kb) correspondence-predicate {})
         (keep #(p/get-sentex (:records kb) %))
         (filter #(jtms/in? (:tms kb) (:id %)))
         (map :sentence)
         (filter #(<= 3 (count %) 4))
         (map (fn [[_ f pr n]] [f pr (when (integer? n) n)]))
         distinct
         (filter match?))))

(defn correspondence-of
  "The `[predicate position]` declared for function `f` applied to `m` arguments, or
  nil.  `position` defaults to `m + 1`, the value last.

  Nil when the KB believes **more than one** declaration for `f`, deliberately: two are
  two different claims about what `(f a…)` denotes, and picking between them by handle
  would make term identity depend on the order they were asserted in."
  [kb f m]
  (let [ds (believed-correspondences kb #(= f (first %)))]
    (when (= 1 (count ds))
      (let [[_ pr n] (first ds)
            pos      (or n (inc m))]
        (when (and (symbol? pr) (<= 1 pos (inc m)))
          [pr pos])))))

(defn- insert-at
  "`args` with `v` spliced in at 1-based `position`."
  [args position v]
  (let [i (dec position)]
    (concat (take i args) [v] (drop i args))))

(defn corresponding-literal
  "The sentence the correspondence makes equivalent to `E = v` — the predicate applied
  to `E`'s arguments with `v` at the declared position — or nil when `E`'s function has
  no single correspondence."
  [kb E v]
  (let [args (rest E)]
    (when-let [[pr pos] (correspondence-of kb (first E) (count args))]
      (apply list pr (insert-at args pos v)))))

(defn correspondence-value
  "The term a believed corresponding fact already names as the value of the ground NAT
  expression `E`, or nil.  Exactly one value, or none: several believed values mean the
  KB does not agree on what `E` denotes, and reifying to one of them would be a guess
  the reader could not see."
  [kb E]
  (when-let [goal (corresponding-literal kb E '?v)]
    (let [pos (some (fn [[i x]] (when (= '?v x) i)) (map-indexed vector goal))
          vs  (->> (kb/sentexes-matching kb goal '?ctx)
                   (map #(nth (:sentence %) pos))
                   (remove sequential?)
                   distinct)]
      (when (= 1 (count vs)) (first vs)))))

(defn- minted-applications
  "The `[expression constant]` pairs already minted for function `f` — its
  `termOfUnit` entries, reached through the **inverted term index** (which descends
  into a ground compound, so the expression's head is one of its posted terms) rather
  than by reading the whole map."
  [kb f]
  (->> (kb/find-sentexes kb f)
       (filter #(and (= universal-context (:context %))
                     (= 'termOfUnit (nm/functor (:sentence %)))
                     (jtms/in? (:tms kb) (:id %))))
       (keep (fn [{[_ k E] :sentence}]
               (when (and (seq? E) (= f (first E))) [E k])))
       distinct))

;; ---- display / export ----------------------------------------------------

(defn- contains-reified-nat?
  "True iff `form` contains a reified NAT constant anywhere."
  [form]
  (boolean (some reified-nat-symbol? (tree-seq seq? seq form))))

(defn expand-expression
  "Recursively replace every reified NAT constant in `form` with the functional
  expression it denotes — human-readable printing / export
  (`(color (FruitFn AppleTree) Red)`, never a raw `nat/` symbol).  Returns `form`
  UNCHANGED (same identity) when it holds no reified NAT, so content holding no reified NAT is
  untouched; only reified NAT-bearing forms are rebuilt."
  [kb form]
  (cond
    (reified-nat-symbol? form) (if-let [e (nat-expression kb form)]
                                 (expand-expression kb e)
                                 form)
    (and (seq? form) (contains-reified-nat? form))
    (apply list (map #(expand-expression kb %) form))
    :else form))

;; ---- the reify walk (parameterized over the leaf action) -----------------
;; The sentence/literal walk is shared by the write path (mint) and the read path
;; (dedup) — only the leaf, what to do with a reifiable ground NAT, differs.  The
;; walk descends into nested non-NAT literals (rule bodies, conjuncts) but leaves
;; the head predicate and any quoting-predicate argument opaque.

(defn reify-in
  "Reify every reifiable ground NAT subterm of literal/sentence `s`, calling
  `nat-fn` (a `(fn [kb form])`) at each one — it returns the NAT's constant, having
  reified any nested NAT args itself.  Quoting-predicate arguments
  (`termOfUnit` / `rewriteOf`) are left opaque, as is every head predicate.

  **A vector is descended element by element, and every element of it.**  A vector in a
  sentence is a *list of forms* rather than a literal — an `exceptWhen`'s conjuncts, a
  `thereExists`'s binders — so it has no head predicate to hold opaque and no element to
  skip.  Stopping at one would leave an exception's query spelled with the compound
  while the fact it is about is stored under the constant, and an exception that cannot
  be answered does not hold: the rule would fire, unguarded and silently."
  [kb s nat-fn]
  (cond
    (reifiable-ground-nat? kb s) (nat-fn kb s)
    (vector? s) (mapv #(reify-in kb % nat-fn) s)
    (and (seq? s) (seq s))
    (if (contains? nat-quoting-predicates (first s))
      s
      (apply list (first s) (map #(reify-in kb % nat-fn) (rest s))))
    :else s))

(defn- reify-nat-for-read
  "Read-mode leaf: reify nested NAT args, then resolve the whole expression to its
  EXISTING term (a `rewriteOf` target, the value its corresponding predicate names,
  else a minted `termOfUnit` constant) — or the `no-match` sentinel when it was never
  minted.  Never mints."
  [kb form]
  (let [E (apply list (first form)
                 (map #(if (reifiable-ground-nat? kb %) (reify-nat-for-read kb %) %)
                      (rest form)))]
    (or (rewrite-target kb E) (correspondence-value kb E) (dedup-constant kb E) no-match)))

(defn maybe-reify-for-read
  "Reify every reifiable ground NAT subterm of a QUERY `sentence` to its existing
  constant (dedup, never mint) so the query matches the stored atomic form.  A
  never-minted NAT resolves to `no-match`, so an unknown-NAT query matches nothing.
  Cheap no-op when the KB declares no `reifiableFunction`."
  [kb sentence]
  (if (any-reifiable-functions? kb)
    (reify-in kb sentence reify-nat-for-read)
    sentence))

;; ---- rename / remove detection -------------------------------------------
;; The maintenance that keeps the 1:1 constant↔expression invariant.  These find the
;; sentexes to act on; the acting (assert an equality to merge, retract to remove)
;; is in `vaelii.core`, which owns those operations.

(defn- group-collisions
  "`[survivor [dup …]]` per expression that more than one constant names, survivor
  lexicographically smallest so the choice is content-keyed."
  [termOfUnit-sentences]
  (->> termOfUnit-sentences
       (group-by #(nth % 2))                          ; group by expression E
       (keep (fn [[_ sents]]
               (let [ks (sort (distinct (map second sents)))]
                 (when (next ks) [(first ks) (rest ks)]))))))

(defn colliding-constant-groups
  "Believed reified constants that share one expression — `[survivor [dup …]]` per
  collision.  A rename can collapse two NATs onto one expression; restoring the 1:1
  invariant means merging each group's `dup`s into its `survivor`.

  Reads the whole map, so this is the answer *about the KB*; the maintenance after a
  rename asks the narrower question `collisions-touching` instead."
  [kb]
  (group-collisions (map :sentence (kb/sentexes-matching kb '(termOfUnit ?k ?e) universal-context))))

(defn- collisions-touching
  "The collisions a merge of `terms` can have created.  A migration twin restates its
  expression under the class **representative**, so every constant in such a collision
  has a `termOfUnit` sentex naming one of those terms — which the inverted term index
  answers directly, in the size of the class rather than the size of the map.

  Complete for what a merge produces: the twin names the representative, and so does
  the constant it collided with (they hold the same expression), so one term-index
  read per merged term reaches both sides of every pair."
  [kb terms]
  (let [rep #(tax/representative (:taxonomy kb) %)]
    (->> (into #{} (mapcat #(kb/find-sentexes kb %))
               (into #{} (mapcat (fn [t] [t (rep t)])) terms))
         (filter (fn [sx] (and (= universal-context (:context sx))
                               (= 'termOfUnit (nm/functor (:sentence sx)))
                               (jtms/in? (:tms kb) (:id sx)))))
         (map :sentence)
         group-collisions)))

(defn- nat-bookkeeping-of?
  "Is `sx` one of constant `k`'s own bookkeeping sentexes — its `termOfUnit` map, a
  materialized result type (`(T k)` / `(genl k T)`), or the correspondence
  `projection` minted alongside it — as opposed to a real use `(p k …)` that keeps it
  alive?

  The projection counts for the same reason a result type does: it states what `k`
  *is*, not something anybody claimed about it, so a constant whose only remaining
  sentex is its own projection is as orphaned as one with no sentex at all."
  [k projection sx]
  (let [s (:sentence sx)
        f (nm/functor s)
        a (vec (nm/args s))]
    (or (and (= f 'termOfUnit) (= k (first a)))
        (and (= 1 (count a))   (= k (first a)))        ; (T k)
        (and (= f 'genl)       (= k (first a)))        ; (genl k T)
        (and (some? projection) (= s projection)))))

(defn orphaned-constants
  "Reified constants no live use references any more: every believed sentex naming
  `k` is one of `k`'s own bookkeeping sentexes.  Removing the fact that used a reified NAT
  leaves it an orphan — its `termOfUnit` and materialized types would dangle a raw
  `nat/` symbol — so those are collected and removed."
  [kb]
  (->> (kb/sentexes-matching kb '(termOfUnit ?k ?e) universal-context)
       (map (fn [{[_ k E] :sentence}] [k E]))
       distinct
       (filter (fn [[k E]]
                 (let [projection (corresponding-literal kb E k)]
                   (every? #(nat-bookkeeping-of? k projection %)
                           (filter #(jtms/in? (:tms kb) (:id %)) (kb/find-sentexes kb k))))))
       (map first)
       distinct))

(defn bookkeeping-handles
  "The believed bookkeeping sentex handles of constant `k` — its `termOfUnit` and
  materialized result-type premises, plus its correspondence projection — the ones to
  retract when `k` is orphaned."
  [kb k]
  (let [E          (nat-expression kb k)
        projection (when E (corresponding-literal kb E k))]
    (->> (kb/find-sentexes kb k)
         (filter #(jtms/in? (:tms kb) (:id %)))
         (filter #(nat-bookkeeping-of? k projection %))
         (map :id)
         distinct)))

;; ---- write-mode reify: mint + result-type materialization ----------------
;; A ground reifiable NAT is replaced by its opaque constant *before* WFF and the
;; constraint checks, so the compound never reaches the index and the minted constant
;; carries the materialized result types those checks read (docs/nat.md).  Stores
;; through `wiring/assert-sentence`, so a KB with no reifiableFunction pays nothing (the
;; callers gate on `any-reifiable-functions?`).

;; Forward reference, not a cycle in this file: `reify-or-mint-nat` calls `mint-nat!`,
;; and the re-entry back into it leaves the namespace through `wiring/assert-sentence`
;; rather than being a direct call here.  Kept because moving `mint-nat!` above this
;; point would separate it from the minting helpers it belongs with; every var it needs
;; is already defined above, so reordering *would* work if that ever stops being true.
(declare mint-nat!)

(defn reify-or-mint-nat
  "Reify a ground NAT `form` to the term it denotes: reify any nested NAT args first,
  then return the existing term for the expression — a `rewriteOf` target, the value
  its corresponding predicate already names, else a prior `termOfUnit` mint — or mint a
  fresh constant.

  A **real term outranks a placeholder**, which is why the correspondence is consulted
  before the dedup probe: a constant minted while the value was unknown is folded onto
  that value as soon as it arrives (`reconcile-correspondence!`), so by the time both
  exist the two answers agree — and until the merge lands, resolving to the name a
  reader wrote beats resolving to an opaque one."
  ([kb form] (reify-or-mint-nat kb form true))
  ([kb form chain?]
   (let [E (apply list (first form)
                  (map #(if (reifiable-ground-nat? kb %) (reify-or-mint-nat kb % chain?) %)
                       (rest form)))]
     (or (rewrite-target kb E) (correspondence-value kb E)
         (dedup-constant kb E) (mint-nat! kb E chain?)))))

(defn mint-nat!
  "Mint a fresh reified constant for the ground NAT expression `E`: allocate an opaque
  `nat/` constant `K`, assert `(termOfUnit K E)` in UniverseContext, materialize the
  function's result types (`(T K)` per `resultIsa`, `(genl K T)` per `resultGenl`),
  and return `K`.  The bookkeeping is `:monotonic` — a reified NAT's identity and result
  types are structural, not defeasible defaults.  `assert` stores synchronously, so a
  second occurrence of `E` in the same sentence dedups against this.

  All three assertions are the *same* bookkeeping, so all three take the chaining the
  caller asked for.  Minting is a step inside somebody else's assert, and a bulk load
  that turned chaining off did so for the whole load: on OpenCyc the two unqualified
  ones ran 46,346 chain fixpoints nobody wanted, most of whose conclusions were then
  dropped for having no placement context."
  ([kb E] (mint-nat! kb E true))
  ([kb E chain?]
   (let [k    (fresh-constant)
         head (first E)
         univ universal-context
         opts {:strength :monotonic :chain? chain?}]
     (wiring/assert-sentence kb (list 'termOfUnit k E) univ (assoc opts :chain? false))
     (doseq [t (result-isa-types kb head)]
       (wiring/assert-sentence kb (list t k) univ opts))
     (doseq [t (result-genl-types kb head)]
       (wiring/assert-sentence kb (list 'genl k t) univ opts))
     ;; the correspondence read the other way: the constant *is* the value the
     ;; corresponding predicate relates these arguments to, so project it back onto
     ;; that predicate.  Last, after the result types — the projected literal is
     ;; argIsa-checked like any fact, and `k`'s types are what it is checked against.
     (when-let [lit (corresponding-literal kb E k)]
       (wiring/assert-sentence kb lit univ opts))
     k)))

(defn maybe-reify-nats
  "Replace every ground reifiable NAT subterm of `sentence` with its reified constant,
  minting as needed.  A cheap no-op when the KB declares no `reifiableFunction`."
  ([kb sentence] (maybe-reify-nats kb sentence true))
  ([kb sentence chain?]
   (if (any-reifiable-functions? kb)
     (reify-in kb sentence #(reify-or-mint-nat %1 %2 chain?))
     sentence)))

(defn merge-colliding-nats!
  "Restore the 1:1 constant↔expression invariant the just-asserted equality
  `sentence` may have broken: when two reified constants have collapsed onto one
  expression, merge each group's extras into its lexicographically-smallest survivor
  by asserting an equality, which migrates the extras' uses onto the survivor.  The
  equality re-enters this check, but a merge removes a colliding constant, so it
  converges — the second pass finds no collision.

  Scoped to the class `sentence` merged (`collisions-touching`): the collisions a
  merge can create all name its representative, so there is nothing to learn from the
  constants it did not touch — and rereading the whole map on every equality would
  make a bulk load quadratic in the NATs it has minted.

  So this repairs what a merge **caused**, and nothing else.  A collision that arrived
  another way — a `:bulk?` load skips the dedup probe, and an import restores whatever
  the dump held — is not swept up by the next unrelated equality the way a whole-map
  rescan would have swept it.  `colliding-constant-groups` is the whole-KB question,
  for a caller that wants to ask it."
  [kb sentence]
  (doseq [[survivor dups] (collisions-touching kb (filter symbol? (rest sentence)))
          dup dups]
    (wiring/assert-sentence kb (list 'equals survivor dup) universal-context {:strength :monotonic})))

;; ---- correspondence maintenance ------------------------------------------
;; The two directions above are consistent only while a constant and the value its
;; corresponding predicate names cannot both stand for one application.  These keep
;; that true whichever of the three — the application, the fact, the declaration —
;; arrives last.

(defn- retire-placeholder!
  "Merge the minted constant `k` into the value `v` its corresponding predicate names —
  the move that makes the arrival order of an application and its value stop mattering.

  `rewriteOf` rather than `equals`, because the two sides are not interchangeable: `v`
  is a name somebody wrote and `k` is an opaque stand-in for not knowing it, so the
  class has a term that should win the election rather than whichever one sorts first.
  Every use of `k` migrates onto `v`, its `termOfUnit` map included, so the expression
  goes on resolving — to the real term now."
  [kb v k]
  (wiring/assert-sentence kb (list 'rewriteOf v k) universal-context {:strength :monotonic}))

(defn- merge-corresponding-nat!
  "Equate the constant minted for an application with the value a just-asserted
  corresponding fact gives it.  `(motherOf Muffet Mary)` arriving after `(MotherFn Muffet)`
  minted `K` leaves the KB holding two values for one application; the declaration says
  they are one object, so the equality says so too and the migration folds `K`'s uses
  onto `Mary`."
  [kb sentence]
  (let [args (vec (rest sentence))
        m    (dec (count args))]
    (doseq [[f _ n] (believed-correspondences kb #(= (first sentence) (second %)))
            :let    [pos (or n (inc m))]
            :when   (and (<= 0 m) (<= 1 pos (inc m)) (reifiable-function? kb f))
            :let    [v (nth args (dec pos))
                     E (apply list f (concat (subvec args 0 (dec pos)) (subvec args pos)))
                     k (dedup-constant kb E)]
            :when   (and k (not= k v))]
      (retire-placeholder! kb v k))))

(defn- reconcile-declared-correspondence!
  "Bring the constants already minted for function `f` into line with a correspondence
  that arrived *after* them.  Each application either has a believed value — the two
  name one object, so equate them — or has none, and the constant is projected onto the
  predicate the way a fresh mint would have projected it.

  Idempotent: once projected, the constant *is* the believed value, so a second run
  would equate it with itself and does nothing."
  [kb f]
  (doseq [[E k] (minted-applications kb f)]
    (if-let [v (correspondence-value kb E)]
      (when-not (= v k) (retire-placeholder! kb v k))
      (when-let [lit (corresponding-literal kb E k)]
        (wiring/assert-sentence kb lit universal-context {:strength :monotonic})))))

(defn reconcile-correspondence!
  "The correspondence maintenance a just-asserted `sentence` calls for: a declaration
  reconciles the applications minted before it, and a fact on a corresponding predicate
  reconciles the one application it names a value for.  A no-op — one integer read —
  on a KB that declares no correspondence."
  [kb sentence]
  (when (and (any-corresponding-predicates? kb) (seq sentence))
    (if (= correspondence-predicate (first sentence))
      (when (symbol? (second sentence))
        (reconcile-declared-correspondence! kb (second sentence)))
      (merge-corresponding-nat! kb sentence))))
