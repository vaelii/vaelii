;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.nat
  "Non-atomic terms (NATs) via reification — Strategy A.

  A NAT is a function-application term `(F arg…)` that denotes an entity —
  `(FruitFn AppleTree)`, `(CapitalOf France)`.  A function splits by declaration
  into two kinds:

    (reifiable_function F)    object-denoting.  A ground `(F a…)` is a **reified NAT**: it
                             reifies to an opaque `nat/`-namespaced constant `K`
                             *before* it reaches the index, so the reified NAT autoindexes
                             exactly like a hand-minted symbol — no trie-key change,
                             no term-index change.
    (unreifiable_function F)  evaluated/interpreted.  The NAT is a **structural NAT** and stays
                             *structural* — `(QuantityFn 5 Meter)` keeps its magnitude
                             and unit readable for a downstream prover; it is never
                             minted.

  The constant↔expression map is itself an ordinary stored fact, `(termOfUnit K E)`
  in CxUniverse, so the inverted term index makes `E`'s constituents (and `K`)
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
  `vaelii.impl.nat-maintenance` sequences the post-assert reconciliation and drops an
  orphaned reified NAT when its last use is retracted (it rides the `retract!` sweep).

  Reads the store, the taxonomy and belief directly (nat <- kb); reaches assertion only
  through the fns above."
  (:require [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.wiring :as wiring]))

(def nat-namespace
  "Reserved namespace for **object**-denoting reified-NAT constants — a
  `(reifiable_function F)` application `(F a…)` mints one.  The cheap detector the
  display and mutation layers key on."
  "nat")

(def context-namespace
  "Reserved namespace for **context**-denoting reified-NAT constants — a
  `(context_denoting_function F)` application `(F a…)` mints one (docs/context-nat.md).
  A `Cx*Fn` reifies to a `cx/` constant that classifies as a *context* (so it can be a
  sentex's context slot and a `genlCx` node), while its structural argument stays
  readable in the `termOfUnit` map.  Distinct from `nat/` because role-reading is
  spelling-only (docs/naming.md): the namespace, not a belief, carries the context role."
  "cx")

(def reified-namespaces
  "The two reserved namespaces a reified constant lives in — object (`nat/`) and
  context (`cx/`).  Everything that asks 'is this an opaque reified constant' — display,
  the `K → E` lookup, the orphan sweep — keys on membership here, since both kinds carry
  a `termOfUnit` map and reify the same way; only the mint namespace and the role differ."
  #{"nat" "cx"})

(def universal-context
  "Where every NAT bookkeeping fact lives — `(reifiable_function F)`, `(termOfUnit K
  E)`, `(result F T)`, and a minted reified NAT's materialized types — so it is visible
  from every context, matching the other universal vocabulary."
  'CxUniverse)

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
  "True iff `term` is a reified constant — a symbol in one of the two reserved
  reified namespaces, object (`nat/`) or context (`cx/`).  Despite the object-case name it
  recognizes both kinds: every caller wants 'is this an opaque
  reified constant', which both are — they share the `termOfUnit` map, the
  display expansion, and the orphan sweep."
  [term]
  (and (symbol? term) (contains? reified-namespaces (namespace term))))

(defn reified-context-symbol?
  "True iff `term` is a reified **context** constant — a symbol in the `cx/`
  namespace.  The discriminant that lets a reified constant classify as a context
  (`naming/context?`) while an object `nat/` constant classifies as a term, and what the
  orphan sweep reads to ask the *context* liveness question of one: a context is kept
  alive by what is stored **in** it as much as by what names it (`orphan?`)."
  [term]
  (and (symbol? term) (= context-namespace (namespace term))))

(defn reified-object-symbol?
  "True iff `term` is a reified **object** constant — a symbol in the `nat/` namespace.
  The other half of the pair: an object constant denotes a *thing* sentences talk about,
  so nothing can be stored in it and naming is the whole of its liveness."
  [term]
  (and (symbol? term) (= nat-namespace (namespace term))))

(def nat-scheme-tag
  "The one-letter scheme prefix on every content-named reified constant, `nat/a…`.  A
  **letter** because a symbol whose name starts with a digit is not a readable token
  (`nat/9x…` reads back as an invalid token), so a numeric-leading hash could not
  round-trip through a dump.  The letter is also the **version**: `a` is this scheme —
  SHA-256 truncated to 96 bits, base62 — and a later hash or encoding change is `b`, old
  constants keeping the names they were minted with (the whole reason a name carries its
  scheme).  One letter covers both jobs, so there is nothing to separate and no separator.
  Not `g`, the prefix `fresh-constant`'s gensym still uses, so the tag also tells a
  content-named constant from a legacy `nat/g…` one.

  Base62, not base64url, because a reified constant only ever stands in **argument**
  position, where it is held to the same spelling rules as any name
  (`naming/argument-problem`) — and base64url's two extra characters, `-` and `_`, are
  precisely the two those rules forbid (`-` would also make the name read as a `sense`).
  Base62 drops just those two, so `nat/a…` is `[A-Za-z0-9]` and matches the camelCase rule
  (`naming/predicate?`) — the same rule the old `nat/g…` gensym matched, and why that one
  passed.  The name is 18 characters: the one-letter tag and a 17-digit base62 payload."
  "a")

(def ^:private base62-alphabet
  "The 62 name-safe digits in ASCII order (`0-9A-Za-z`), so a base62 name sorts the same
  as the bytes behind it — the order `dedup-constant` / `group-collisions` elect a
  survivor by."
  "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz")

(defn- base62
  "Byte array `b` as an unsigned big-endian integer, base62-encoded (`base62-alphabet`)
  and left-padded with `0` to `width` digits, so the name is fixed-length."
  [^bytes b width]
  (let [sixty-two (BigInteger/valueOf 62)]
    (loop [n (BigInteger. 1 b), acc ()]
      (if (pos? (.signum n))
        (recur (.divide n sixty-two)
               (cons (.charAt ^String base62-alphabet (.intValue (.mod n sixty-two))) acc))
        (let [s (apply str acc)]
          (str (apply str (repeat (max 0 (- width (count s))) \0)) s))))))

(defn- content-name
  "The deterministic constant name expression `E` reifies to: `nat-scheme-tag` followed
  by the first 96 bits of `SHA-256(E)` in base62, left-padded to 17 digits (62^17 > 2^96
  ≥ 62^16, so 17 is the width that covers the range).  A function of `E`'s printed content
  alone, so the same expression mints the same constant in any process and after any
  retract/rebuild, and a fact stated about the constant goes on referring to it — which is
  how the skolem digest (`skolem/rule-digest`) keys its witnesses, and for the same
  order-independence reason; the difference is only that a NAT hashes its own
  already-reified expression rather than a rule.  Print limits are bound off exactly as
  that digest binds them, so a REPL's ambient `*print-length*`/`*print-level*` cannot
  elide `E` out of its own identity and collapse two expressions onto one name."
  [E]
  (let [s   (binding [*print-length* nil *print-level* nil *print-meta* false]
              (pr-str E))
        d   (.digest (java.security.MessageDigest/getInstance "SHA-256")
                     (.getBytes ^String s "UTF-8"))
        b96 ^bytes (java.util.Arrays/copyOf ^bytes d 12)]
    (str nat-scheme-tag (base62 b96 17))))

(defn constant-for
  "The opaque reified constant expression `E` reifies to, in reserved namespace `ns`
  (`nat` for an object NAT, `cx` for a context NAT).  Deterministic in `E`'s content
  (`content-name`), so re-reifying `E` — in this process, in another, or in a KB rebuilt
  in another order — yields the *same* constant.  A hash collision (two expressions, one
  name) can only degrade into the ordinary two-expressions-one-constant case the merge
  repair already reconciles by content (`authoritative-expression`), never into a wrong
  answer.  A `nat/` name matches the camelCase argument convention (`nat-scheme-tag`
  explains the base62 choice) and a `cx/` name is exempt as a context spelling
  (`naming/context?`), so neither needs an exemption in `naming/argument-problem`, where a
  reified constant is checked — only ever as an argument, never as a functor."
  [ns E]
  (symbol ns (content-name E)))

(defn fresh-constant
  "Allocate a fresh, opaque reified constant with a process-unique gensym name in the
  given reserved namespace — `nat` (default) or `cx`.  For a throwaway constant not tied
  to an expression; the mint path names by content instead (`constant-for`), so this is
  not on it.  The `g…` name is camelCase, matching the argument convention the mint's
  base62 name matches too (`constant-for`), so it needs no naming exemption either."
  ([] (fresh-constant nat-namespace))
  ([ns] (symbol ns (name (gensym "g")))))

;; ---- the reifiable gate --------------------------------------------------
;; A function's kind is predicate metadata, cached in the taxonomy like
;; transitive/symmetric/functional: `(reifiable_function F)` marks the `:reifiable`
;; prop, `(unreifiable_function F)` the `:unreifiable` one (both belief-following,
;; via `vaelii.impl.special`'s prop-entry).  So the per-sentence gate is a free
;; in-memory set read — no index probe, no mtime cache to keep coherent.

(defn any-reifiable-functions?
  "Cheap gate: does the KB declare any function that reifies — a `reifiable_function`
  (object, mints `nat/`) or a `context_denoting_function` (context, mints `cx/`)?  False ⇒
  no sentence can contain a reifiable NAT, so the reify pass and the rename/remove NAT
  steps short-circuit to a no-op.  Two in-memory taxonomy-prop reads."
  [kb]
  (let [tx (reasoning/taxonomy kb)]
    (boolean (or (seq (tax/props tx :reifiable))
                 (seq (tax/props tx :context-denoting))))))

(defn any-context-denoting-functions?
  "Cheap gate: does the KB declare any `context_denoting_function`?  A free in-memory
  taxonomy-prop read — the context half of `any-reifiable-functions?`.  False ⇒ the KB has
  no `cx/` context to order, so the structural-genlCx producer's revival re-run is a no-op
  without even paying the `any-context-subrelations?` functor-count index read."
  [kb]
  (boolean (seq (tax/props (reasoning/taxonomy kb) :context-denoting))))

(defn context-denoting-function?
  "True iff `(context_denoting_function head)` is believed — head reifies to a `cx/`
  context constant rather than a `nat/` object constant (docs/context-nat.md).  Read off
  the taxonomy metadata like `reifiable-function?`, so it is context-independent and
  belief-following."
  [kb head]
  (and (symbol? head)
       (not (reified-nat-symbol? head))
       (tax/has-prop? (reasoning/taxonomy kb) :context-denoting head)))

(defn reifiable-function?
  "True iff `head` reifies its ground applications — either `(reifiable_function head)`
  (object → `nat/`) or `(context_denoting_function head)` (context → `cx/`).  Read straight
  off the taxonomy metadata, so it is context-independent — deliberately, since reification
  decides *term identity*, which cannot vary by reader — and belief-following: a defeated
  or retracted declaration stops the function reifying."
  [kb head]
  (and (symbol? head)
       (not (reified-nat-symbol? head))
       (or (tax/has-prop? (reasoning/taxonomy kb) :reifiable head)
           (tax/has-prop? (reasoning/taxonomy kb) :context-denoting head))))

(defn- ground-form?
  "True iff `form` contains no pattern variables anywhere (any nesting)."
  [form]
  (not-any? sx/variable? (tree-seq sequential? seq form)))

(defn reifiable-ground-nat?
  "True iff `form` is a ground `(F …)` whose head F is an **object** reifiable_function — a
  NAT the sentence/argument reify walk may mint to a `nat/` constant.  Ground because an
  open NAT (`(F ?x)`) would need an enumerating prover to mint anything, so it is left
  alone.  `sequential?`, not `seq?`: reification runs before `canon`, so a vector-spelled
  `[F …]` is the same NAT as `(F …)` — gating on the list spelling alone would store the
  raw compound where the other spelling stores the constant, two handles for one canonical
  sentence.

  A **context-denoting** `Cx*Fn` application is excluded, even though it too reifies
  (`reifiable-function?` is true of it): it reifies to a `cx/` *context* constant, and only
  in the **context slot** (`maybe-reify-context`), never as a sentence argument.  Minting it
  on the sentence walk would make one `cx/` constant both a context and an untyped object
  relatum — `(happenedDuring E (CxTimeFn CxMonad (DatetimeFn \"2000\")))`'s arg 2 aliasing
  the very context `(likes …)` is stored in — so in a sentence it stays a structural
  compound, exactly as an `unreifiable_function` NAT does (docs/context-nat.md)."
  [kb form]
  (and (sequential? form)
       (seq form)
       (reifiable-function? kb (first form))
       (not (context-denoting-function? kb (first form)))
       (ground-form? form)))

;; ---- index-backed lookups ------------------------------------------------
;; `E → K` (dedup) and `K → E` (reverse) are both `(termOfUnit …)` queries — the
;; functor/argument roots answer them, so no new IndexStore method is needed.  Reads
;; are belief-filtered by `kb/sentexes-matching`, so a superseded spelling (a renamed reified NAT's old
;; expression) does not answer.

(defn authoritative-expression
  "The one expression a reified constant denotes, chosen from `exprs` — the **content-least**
  of them.

  Normally there is nothing to choose: the map is 1:1 and `exprs` holds one member.  A
  collision the repair has yet to reach holds several, and every reader of the map has to
  make the same choice out of them or they disagree about one constant — `orphan?` deciding
  a constant orphaned against one expression while `bookkeeping-handles` computes what to
  retract from another is a sweep that retracts the wrong records.  Content, never arrival,
  for the reason `dedup-constant` elects the surviving constant the same way: which of two
  spellings the retrieval yielded first is not an answer about the KB."
  [exprs]
  (nm/min-by-content-key identity exprs))

(defn nat-expression
  "The NAT expression a reified constant denotes, or nil — the authoritative one where an
  unrepaired collision maps it to more than one (`authoritative-expression`)."
  [kb nat-sym]
  (when (reified-nat-symbol? nat-sym)
    (authoritative-expression
     (keep #(nth (:sentence %) 2 nil)
           (kb/sentexes-matching kb (list 'termOfUnit nat-sym '?e) universal-context)))))

(defn dedup-constant
  "The existing reified constant for the ground NAT expression `E`, or nil — the
  `E → K` half of the 1:1 map, so re-reifying an expression finds the constant
  already minted for it rather than minting a second.  More than one constant can
  name `E` (a `:bulk?` load skips this probe, and an import restores whatever the
  dump held), and the answer is then the lexicographically smallest — the survivor
  `group-collisions` elects — so a read resolves to the constant the merge repair
  keeps rather than to whichever the retrieval yielded first."
  [kb E]
  (->> (kb/sentexes-matching kb (list 'termOfUnit '?k E) universal-context)
       (map #(second (:sentence %)))
       sort
       first))

(defn rewrite-target
  "The real term `T` a `(rewriteOf T E)` declaration says the NAT expression `E`
  reifies to instead of a fresh constant, or nil.  A quoting-predicate declaration:
  `E` is the literal NAT payload, `T` an existing atomic term.

  Nil when the believed declarations name **more than one target**, exactly as
  `correspondence-of` answers its twin question: picking between them by whichever
  the retrieval yielded first would store `(likes Tom Mary)` or `(likes Tom Maria)`
  according to the order two `rewriteOf`s arrived — divergent *stored* state, which
  every later read then inherits.  Two targets are a disagreement for the clash
  machinery, not a tie for this read to break; two declarations of **one** target
  (the engine's own reconcile writes those) are one answer."
  [kb E]
  (let [ts (into #{} (comp (map #(second (:sentence %))) (take 2))
                 (kb/sentexes-matching kb (list 'rewriteOf '?t E) universal-context))]
    (when (= 1 (count ts))
      (first ts))))

(defn- result-targets
  "The distinct arg2s of believed `(<pred> head ?t)` facts — the result types the function
  `head` is declared with under `pred`.

  **Two vantages, and the caller picks by which question it is asking.**  The mint asks
  globally: it materializes what it reads into `CxUniverse`, which every context sees, so
  a declaration written where the minting assert cannot see it still types the constant
  for every later reader — the context-independence `reifiable-function?` takes, and for
  its reason, what a term denotes not being a thing a reader may vary.  A **check** asks
  from `context`: it convicts on an absence, and the whole definitional family judges from
  the asking context's vantage, so a declaration that context cannot see may not refuse
  it.

  The scoped arity reads through `res/matches-visible` rather than a literal match at one
  context.  A result declaration lives in `CxUniverse` and is asked about from wherever
  the sentence is being written, so the read walks the `genlCx` ancestor set exactly as every
  other declaration read does."
  ([kb pred head]
   (->> (kb/sentexes-matching kb (list pred head '?t) '?ctx)
        (keep #(nth (:sentence %) 2))
        distinct))
  ([kb pred head context]
   (->> (res/matches-visible kb (list pred head '?t) context)
        (keep #(get (nth % 1) '?t))
        distinct)))

(defn result-types
  "Types `T` with `(result head T)` — what an application of `head` is an *instance*
  of.  Materialized as `(T K)` on a freshly minted reified NAT whose function is `head`,
  and read at check time for an application that is never minted (docs/argtypes.md).
  Globally, or (with `context`) through only the declarations visible from it."
  ([kb head] (result-targets kb 'result head))
  ([kb head context] (result-targets kb 'result head context)))

(defn genl-result-types
  "Types `T` with `(genlResult head T)` — what an application of `head` is a *subtype*
  of.  Materialized as `(genl K T)` on a freshly minted reified NAT whose function is
  `head`, and read at check time for an application that is never minted.  Globally, or
  (with `context`) through only the declarations visible from it."
  ([kb head] (result-targets kb 'genlResult head))
  ([kb head context] (result-targets kb 'genlResult head context)))

(defn any-result-declarations?
  "Cheap gate: does the KB declare any `result` or `genlResult`?  False ⇒ no mint has
  materialized a result type and no application can be typed by one, so both the orphan
  sweep's question about them and the argument checks' are answered without a probe.  Two
  O(1) functor counts, the same shape as `any-corresponding-predicates?`."
  [kb]
  (let [ix (:index kb)]
    (or (pos? (reads/stored-count-with-functor ix 'result))
        (pos? (reads/stored-count-with-functor ix 'genlResult)))))

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
;; A correspondence bites only on a `reifiable_function`: an undeclared function's
;; application is left a raw compound the reify pass never visits.

(def correspondence-predicate
  "The declaration relating a NAT function to the predicate stating the same thing."
  'functionCorrespondingPredicate)

(defn any-corresponding-predicates?
  "Cheap gate: does the KB declare any `functionCorrespondingPredicate`?  An O(1)
  functor count, so a KB that declares none pays one integer read per assert and
  nothing else."
  [kb]
  (pos? (reads/stored-count-with-functor (:index kb) correspondence-predicate)))

(defn- believed-correspondences
  "Believed correspondence declarations as `[function predicate position-or-nil]`
  triples, kept where `match?` holds of the triple.

  Read from the **functor root alone** and filtered in memory rather than narrowed on
  an argument root: the declarations number one per reified function and so are few,
  where the position-2 argument roots hold every fact ever asserted about `P` — and this is
  asked once per assert, which is the last place to make a cost a function of the
  corpus.  Belief is filtered at the **entry point** rather than through `kb/sentexes-matching`:
  the declaration has two legal arities, and a pattern query would need one probe per
  arity to see both."
  [kb match?]
  (when (any-corresponding-predicates? kb)
    (->> (reads/believed-with-args kb correspondence-predicate {})
         (keep #(p/get-sentex (:records kb) %))
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
                     (jtms/in? (reasoning/tms kb) (:id %))))
       (keep (fn [{[_ k E] :sentence}]
               (when (and (seq? E) (= f (first E))) [E k])))
       distinct))

;; ---- display / export ----------------------------------------------------

(defn- contains-reified-nat?
  "True iff `form` contains a reified NAT constant anywhere.  `sequential?` so the
  walk descends a rule's antecedent vector, the one vector `canon` keeps."
  [form]
  (boolean (some reified-nat-symbol? (tree-seq sequential? seq form))))

(defn expand-expression
  "Recursively replace every reified NAT constant in `form` with the functional
  expression it denotes — human-readable printing / export
  (`(color (FruitFn AppleTree) Red)`, never a raw `nat/` symbol).  Returns `form`
  UNCHANGED (same identity) when it holds no reified NAT, so content holding no reified NAT is
  untouched; only reified NAT-bearing forms are rebuilt.  A vector rebuilds as a
  vector — an antecedent list stays the shape its record stores."
  [kb form]
  (cond
    (reified-nat-symbol? form) (if-let [e (nat-expression kb form)]
                                 (expand-expression kb e)
                                 form)
    (and (seq? form) (contains-reified-nat? form))
    (apply list (map #(expand-expression kb %) form))
    (and (vector? form) (contains-reified-nat? form))
    (mapv #(expand-expression kb %) form)
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
  minted.  Never mints.

  A **`quoting_function`'s argument is a mention**, held opaque here exactly as the write
  leaf `reify-or-mint-nat` holds it: `(Quote (FruitFn Apple))` was minted against the
  literal payload, so a query must resolve against that literal too — reifying the inner
  NAT here would probe for `(Quote <constant>)`, which was never stored, and the fact
  would read back as no-match."
  [kb form]
  (let [E (if (tax/quoting-function? (reasoning/taxonomy kb) (first form))
            (apply list form)
            (apply list (first form)
                   (map #(if (reifiable-ground-nat? kb %) (reify-nat-for-read kb %) %)
                        (rest form))))]
    (or (rewrite-target kb E) (correspondence-value kb E) (dedup-constant kb E) no-match)))

(defn maybe-reify-for-read
  "Reify every reifiable ground NAT subterm of a QUERY `sentence` to its existing
  constant (dedup, never mint) so the query matches the stored atomic form.  A
  never-minted NAT resolves to `no-match`, so an unknown-NAT query matches nothing.
  Cheap no-op when the KB declares no `reifiable_function`."
  [kb sentence]
  (if (any-reifiable-functions? kb)
    (reify-in kb sentence reify-nat-for-read)
    sentence))

(defn- has-no-match?
  "Does the read-mode reify of a sentence carry the `no-match` sentinel anywhere — i.e.
  did some reifiable NAT in it have no stored constant?  Walks lists and vectors only, so
  a string or other scalar argument is never descended into."
  [form]
  (or (= form no-match)
      (and (or (seq? form) (vector? form))
           (boolean (some has-no-match? form)))))

(defn resolve-for-read
  "The read-mode reify of `sentence` (`maybe-reify-for-read`: dedup, never mint) when
  every reifiable NAT in it already has a stored constant, else nil — the sentence names
  a NAT that was never minted, so it has no stored atomic form.

  A read entry point hands the reified sentence with its `no-match` sentinels straight to
  the lookup, which then matches nothing; a write path that must not mint (`core/assert-
  inert`) refuses on nil instead, and an un-stored canonicalizer (`core/canonical-sentex`)
  keeps the compound.  Cheap no-op returning the sentence unchanged when the KB declares
  no `reifiable_function`."
  [kb sentence]
  (let [r (maybe-reify-for-read kb sentence)]
    (when-not (has-no-match? r) r)))

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
  (let [rep #(tax/representative (reasoning/taxonomy kb) %)]
    (->> (into #{} (mapcat #(kb/find-sentexes kb %))
               (into #{} (mapcat (fn [t] [t (rep t)])) terms))
         (filter (fn [sx] (and (= universal-context (:context sx))
                               (= 'termOfUnit (nm/functor (:sentence sx)))
                               (jtms/in? (reasoning/tms kb) (:id sx)))))
         (map :sentence)
         group-collisions)))

(defn- minted-for
  "The sentences `mint-nat!` writes **about** the constant `k` it minted for expression
  `E`: the materialized result types — `(T k)` per believed `(result F T)` and
  `(genl k T)` per `(genlResult F T)`, `F` being `E`'s function — and the correspondence
  projection.  All of them land in `universal-context`, which is where the mint puts
  them.

  This is what the orphan sweep discriminates by, and the question it asks is
  **authorship**, not shape: the engine wrote these, so it re-reads the declarations the
  mint read to find out which sentences those were.  Reading shape instead makes a
  user's own unary claim about a reified NAT — `(prime K)`, `(genl K SomeType)` — look
  like a materialized type, and the sweep then retracts the claim along with the
  constant.

  Empty for a **context** constant, mirroring the mint: `mint-nat!` writes a `cx/`
  constant's `termOfUnit` and nothing else, result types and the correspondence being
  object-denoting concerns a place is not (docs/context-nat.md).  Re-derived rather than
  assumed, so a `Cx*Fn` that does carry a `result` declaration does not make a reader's
  own `(T cx/g1)` look like a sentence the mint wrote."
  [kb k E]
  (if (reified-context-symbol? k)
    #{}
    (into (if-let [lit (corresponding-literal kb E k)] #{lit} #{})
          (when (any-result-declarations? kb)
            (let [head (first E)]
              (concat (map #(list % k) (result-types kb head))
                      (map #(list 'genl k %) (genl-result-types kb head))))))))

(defn- computed-genlCx-edge?
  "Is `sx` a `genlCx` edge the **structural producer** materialized — the engine's own
  wiring of a `cx/` context into the lattice (docs/context-nat.md) — rather than an edge
  somebody asserted or a rule concluded?

  Authorship again, and the justification is where it is recorded: the producer deduces
  its edges under the `contextArgSubrelation` informant and nothing else uses that
  informant, so an edge that is not a premise and whose every support carries it was
  written by the producer.  A premise is the caller's edge however the producer also
  derives it, and a support under any other informant is a rule's conclusion — either is
  content, and content naming a context keeps it alive.

  This is what makes the computed containment *not* a liveness source: a month context
  `genlCx`-ing its year is derived from the two `termOfUnit` maps, so counting it as a
  use would make every context the producer ever ordered immortal, each holding the
  other up.  Belief is not read — the question is who wrote the edge, and a defeated
  declaration leaves a stored edge the producer still owns."
  [kb sx]
  (let [s (:sentence sx)]
    (and (= 'genlCx (nm/functor s))
         (= universal-context (:context sx))
         (let [tms (reasoning/tms kb)
               h   (:id sx)
               js  (jtms/supports tms h)]
           (and (not (jtms/premise? tms h))
                (seq js)
                (every? #(= 'contextArgSubrelation (:informant (jtms/justification tms %)))
                        js))))))

(defn- nat-bookkeeping-of?
  "Is `sx` one of constant `k`'s own bookkeeping sentexes — its `termOfUnit` map, or one
  of the sentences `minted-for` says the mint wrote about it — as opposed to a real use
  `(p k …)` that keeps it alive?

  A minted sentence counts because it states what `k` *is*, not something anybody
  claimed about it, so a constant whose only remaining sentexes are its map, its result
  types and its own projection is as orphaned as one with no sentex at all.  Anything
  else naming `k` is somebody's assertion whatever its arity: `(prime K)` is a claim
  about `K` exactly as `(noted Author K)` is.

  `minted` is a **delay**, and the map clause is what makes that pay: the constant a
  teardown collects has its `termOfUnit` and nothing else left, so the common answer is
  reached without asking the declarations what the mint wrote."
  [k minted sx]
  (let [s (:sentence sx)]
    (or (and (= 'termOfUnit (nm/functor s)) (= k (first (nm/args s))))
        (and (= universal-context (:context sx)) (contains? @minted s)))))

(defn- mapped-expressions
  "The expressions `k`'s own `termOfUnit` sentexes map it to, read off `sentexes` — the
  term-index answer for `k`, which holds its map beside its uses.  Normally one; a
  collision the 1:1 invariant has yet to be restored on has several."
  [k sentexes]
  (keep (fn [sx]
          (let [s (:sentence sx)]
            (when (and (= universal-context (:context sx))
                       (= 'termOfUnit (nm/functor s))
                       (= k (second s)))
              (nth s 2 nil))))
        sentexes))

(defn orphan?
  "Is the reified constant `k` orphaned — is every **stored** sentex naming it one of
  `k`'s own bookkeeping sentexes?  False when nothing maps it: a constant with no
  believed `termOfUnit` names no expression, so there is no map left to dangle.

  For a **context** constant the same question reaches one thing more, because a context
  is somewhere sentexes are as well as something sentences name: it is orphaned when its
  context slot holds nothing, no stored sentence names it, and no stored `genlCx` edge
  does either — bar the edges the structural producer computed from its own `termOfUnit`
  (`computed-genlCx-edge?`), which are the engine's wiring rather than anybody's claim.
  Its only bookkeeping is that map (`minted-for`).

  Uses count by storage, not belief: a stored-but-OUT use revives when the defeat
  above it lifts, and an inert use (a labeling's choice head) has no TMS node at all
  — collecting the map from under either would leave it dangling a raw `nat/`
  symbol, and re-reifying the expression would then mint a second constant beside
  the first, a collision no merge repair caused.  Only the map read
  (`mapped-expressions`) follows belief, so a superseded spelling still answers
  nothing.

  **One term-index read answers the whole question.**  `k`'s uses, its map and its
  materialized types are all sentexes naming `k`, so the inverted term index
  (docs/indexing.md) hands back the lot in the size of `k`'s own footprint, and nothing
  here is a function of how many other constants the KB has minted.  The index posts a
  sentex's **context** beside its content terms (`kv/sentex-terms`), so a `cx/` context's
  extent is in that same answer and no second question has to be asked to be correct.

  **A context is asked the cheap half first.**  A context NAT is a *place*, so what is
  stored in it keeps it alive as surely as what names it — and a live one is the common
  case and the expensive one, since its extent is exactly what the term-index answer
  would materialize.  `count-in-context` settles it in one O(1) read on every backend
  (docs/indexing.md, the secondary roots), so a context holding a million facts costs a
  count rather than a million record fetches, and only an **empty** one goes on to the
  term read.  Stored, not believed, for the reason the uses are.

  Asked of the **authoritative** expression alone, not of any expression that would
  answer yes: an unrepaired collision maps `k` to several, and `bookkeeping-handles`
  computes the retraction set from exactly one of them (`nat-expression`), so deciding
  orphanhood against a different one would retract `E₂`'s bookkeeping on `E₁`'s verdict."
  [kb k]
  (let [ctx? (reified-context-symbol? k)]
    (if (and ctx? (pos? (long (reads/stored-count-in-context (:index kb) k))))
      false
      (let [all  (kb/find-sentexes kb k)
            live (filterv #(jtms/in? (reasoning/tms kb) (:id %)) all)]
        (boolean
         (when-let [E (authoritative-expression (mapped-expressions k live))]
           (let [minted (delay (minted-for kb k E))]
             (every? #(or (nat-bookkeeping-of? k minted %)
                          (and ctx? (computed-genlCx-edge? kb %)))
                     all))))))))

(defn orphaned-constants
  "Every reified constant in the KB that no live use references any more.  Removing the
  fact that used a reified NAT leaves it an orphan — its `termOfUnit` and materialized
  types would dangle a raw `nat/` symbol — so those are collected and removed.

  Reads the whole map, so this is the answer *about the KB*, and its cost is the KB's
  whole `termOfUnit` population; the maintenance after a teardown asks the narrower
  `orphaned-among` instead.

  Both kinds: an object constant nothing names, and a context constant nothing is stored
  in, names or wires (`orphan?`)."
  [kb]
  (->> (kb/sentexes-matching kb '(termOfUnit ?k ?e) universal-context)
       (map (fn [{[_ k _] :sentence}] k))
       distinct
       (filter reified-nat-symbol?)
       (filterv #(orphan? kb %))))

(defn- orphaned-among
  "The orphans among `candidates` — `orphaned-constants`' question asked of named
  constants rather than of every constant in the KB.

  This is the question a teardown has: a constant becomes an orphan only when something
  that referenced it goes, so the constants the departing sentexes named
  (`constants-named-by`) are the whole of what can have become one, and a KB's other NATs
  cannot answer differently for having been counted.  Cost is the candidate set's, not
  the map's.

  A candidate that is neither reserved namespace is dropped rather than probed — a
  removed sentence names ordinary terms too, and none of them has a map to orphan."
  [kb candidates]
  (into [] (comp (filter reified-nat-symbol?) (distinct) (filter #(orphan? kb %))) candidates))

(defn reified-nats-in
  "Every reified-NAT constant `form` names, at any nesting.

  Descends a vector as well as a list, since a vector in a sentence is a *list of forms*
  — an `exceptWhen`'s conjuncts, a `thereExists`'s binders — and a constant standing in
  one is as much a reference as a constant in a literal."
  [form]
  (into #{} (filter reified-nat-symbol?) (tree-seq sequential? seq form)))

(defn- constants-named-by
  "Every reified-NAT constant the `sentexes` reference — the candidate set a region-scoped
  orphan sweep asks `orphaned-among` about, given what a teardown removed.

  Two places a removed sentex can reference one, because a `cx/` constant can be either
  end of a reference: the **sentence**, at any nesting, and the sentex's own **context**,
  which is where the last fact leaving a reified context is the removal that orphans it.
  Reading the sentence alone would find a context only through an edge or a mention and
  never through its extent, so emptying a context would leave it standing until something
  unrelated named it."
  [sentexes]
  (into #{} (mapcat (fn [sx]
                      (cond-> (reified-nats-in (sx/sentence-of sx))
                        (reified-context-symbol? (:context sx)) (conj (:context sx)))))
        sentexes))

(defn orphans-named-by
  "The orphans among the constants the removed `sentexes` named — the region-scoped
  question a teardown's sweep asks each round, which is `constants-named-by` fed straight
  to `orphaned-among`.

  One entry point because the two halves are one question: a constant becomes an orphan
  only when something referencing it goes, so the candidate set *is* what the departing
  sentexes named, and asking the second half of anything else would be asking about a
  constant no removal touched.  The whole-KB reading is `orphaned-constants`."
  [kb sentexes]
  (orphaned-among kb (constants-named-by sentexes)))

(defn bookkeeping-handles
  "The bookkeeping sentex handles of constant `k` — its `termOfUnit` and materialized
  result-type premises, plus its correspondence projection — the ones to retract when
  `k` is orphaned.  Not belief-filtered: once `k` is orphaned everything it owns
  goes, and a bookkeeping sentex sitting OUT would otherwise stay stored, a map for
  a constant the sweep has already collected.

  A **context** constant's is its `termOfUnit` alone, and the structural `genlCx` edges
  the producer computed off it are deliberately not listed: they are *derived*, so
  retracting the map withdraws their one premise and the dependency-directed sweep
  deletes them (docs/nmtms.md).  Which is also what puts the far end of each edge in the
  next round's candidate set, so a chain of ordered contexts collapses by the rule that
  collapsed the first.

  **Realized before it returns**, because the caller retracts what it hands back and
  `minted` is a read of the very sentexes being retracted: it asks `k`'s `termOfUnit`
  which expression the mint wrote about, so a tail forced after the map's own
  retraction answers `#{}` and the materialized types and the projection stop looking
  like bookkeeping — left stored, naming a constant the sweep has collected.  Whether
  that happens is decided by which sentex the term index hands back first, so a lazy
  answer here is a dangling `nat/` symbol in some retrieval orders and not in others."
  [kb k]
  (let [minted (delay (if-let [E (nat-expression kb k)] (minted-for kb k E) #{}))]
    (into [] (comp (filter #(nat-bookkeeping-of? k minted %))
                   (map :id)
                   (distinct))
          (kb/find-sentexes kb k))))

;; ---- write-mode reify: mint + result-type materialization ----------------
;; A ground reifiable NAT is replaced by its opaque constant *before* WFF and the
;; constraint checks, so the compound never reaches the index and the minted constant
;; carries the materialized result types those checks read (docs/nat.md).  Stores
;; through `wiring/assert-sentence`, so a KB with no reifiable_function pays nothing (the
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
  reader wrote beats resolving to an opaque one.

  A **`quoting_function`'s argument is a mention** — the term named as syntax — so its
  nested NATs are **not** reified: `(Quote (FruitFn Apple))` mints against the literal
  `(FruitFn Apple)`, not against that NAT's own constant, or two quoted syntaxes whose
  payloads' referents merged would collapse to one mention.  The whole quoted expression
  is the identity, held opaque here the same way `res/representative-term` holds it opaque
  to a `sameAs` merge."
  ([kb form] (reify-or-mint-nat kb form true))
  ([kb form chain?]
   (let [E (if (tax/quoting-function? (reasoning/taxonomy kb) (first form))
             (apply list form)
             (apply list (first form)
                    (map #(if (reifiable-ground-nat? kb %) (reify-or-mint-nat kb % chain?) %)
                         (rest form))))]
     (or (rewrite-target kb E) (correspondence-value kb E)
         (dedup-constant kb E) (mint-nat! kb E chain?)))))

(defn mint-nat!
  "Mint a fresh reified constant for the ground NAT expression `E`: allocate an opaque
  constant `K` in `E`'s reify namespace (`cx/` for a context-denoting function, else
  `nat/`), assert `(termOfUnit K E)` in CxUniverse, and — for an **object** NAT only —
  materialize the function's result types (`(T K)` per `result`, `(genl K T)` per
  `genlResult`) and the correspondence projection.  Returns `K`.  The bookkeeping is
  `:monotonic` — a reified NAT's identity and result types are structural, not defeasible
  defaults.  `assert` stores synchronously, so a second occurrence of `E` in the same
  sentence dedups against this.

  A **context** NAT (`cx/`) skips the result-type and correspondence machinery: those are
  object-denoting concerns (a constant that *is an instance of* a type, or *is the value*
  a predicate names), and a context is neither — it is a place, wired into the `genlCx`
  lattice by the structural producer rather than typed (docs/context-nat.md).  Its only
  bookkeeping is the `termOfUnit` map.

  The result types and the correspondence projection take the chaining the caller
  asked for; `(termOfUnit K E)` is asserted with chaining off regardless — the
  identity record is what the dedup probe reads, not content a rule fires on.
  Minting is a step inside somebody else's assert, and a bulk load that turned
  chaining off did so for the whole load: on OpenCyc the two unqualified ones ran
  46,346 chain fixpoints nobody wanted, most of whose conclusions were then dropped
  for having no placement context."
  ([kb E] (mint-nat! kb E true))
  ([kb E chain?]
   (let [head (first E)
         ctx? (context-denoting-function? kb head)
         k    (constant-for (if ctx? context-namespace nat-namespace) E)
         univ universal-context
         opts {:strength :monotonic :chain? chain?}]
     (wiring/assert-sentence kb (list 'termOfUnit k E) univ (assoc opts :chain? false))
     (when-not ctx?
       (doseq [t (result-types kb head)]
         (wiring/assert-sentence kb (list t k) univ opts))
       (doseq [t (genl-result-types kb head)]
         (wiring/assert-sentence kb (list 'genl k t) univ opts))
       ;; the correspondence read the other way: the constant *is* the value the
       ;; corresponding predicate relates these arguments to, so project it back onto
       ;; that predicate.  Last, after the result types — the projected literal is
       ;; arg-checked like any fact, and `k`'s types are what it is checked against.
       (when-let [lit (corresponding-literal kb E k)]
         (wiring/assert-sentence kb lit univ opts)))
     k)))

(defn maybe-reify-nats
  "Replace every ground reifiable NAT subterm of `sentence` with its reified constant,
  minting as needed.  A cheap no-op when the KB declares no `reifiable_function`."
  ([kb sentence] (maybe-reify-nats kb sentence true))
  ([kb sentence chain?]
   (if (any-reifiable-functions? kb)
     (reify-in kb sentence #(reify-or-mint-nat %1 %2 chain?))
     sentence)))

(defn context-denoting-ground-nat?
  "True iff `form` is a ground application whose head is a `context_denoting_function` — a
  context NAT the context slot may reify to a `cx/` constant."
  [kb form]
  (and (sequential? form) (seq form)
       (context-denoting-function? kb (first form))
       (ground-form? form)))

(defn maybe-reify-context
  "Reify a **context slot** `(CxTimeFn …)` to its `cx/` constant — the context-slot twin
  of `maybe-reify-nats`, which reifies a *sentence*.  The context argument is passed to
  `assert` beside the sentence, so it is not on the sentence-reify walk; without this a
  compound context is refused for shape (docs/context-nat.md).  Minting when `mint?` (the
  write path), dedup-only when not (a read goal resolves to an existing context, never
  mints one).  A bare symbol (a `Cx…` name or an already-reified `cx/` constant) and any
  non-context-denoting form pass through unchanged — the latter to be caught by the
  ordinary context-shape / naming checks."
  ([kb context] (maybe-reify-context kb context true))
  ([kb context mint?]
   (if (and (any-reifiable-functions? kb) (context-denoting-ground-nat? kb context))
     (if mint?
       (reify-or-mint-nat kb context false)
       ;; the read leaf, not a third copy of the expression walk: `reify-nat-for-read` is
       ;; `reify-or-mint-nat` minus the mint, so a context slot resolves through the same
       ;; three ranks the write path minted against — a `rewriteOf` target, the value a
       ;; corresponding predicate names, then the dedup probe — and holds a quoting
       ;; function's argument opaque the same way.  Resolving a context by the dedup probe
       ;; alone would read back `no-match` from a slot the write path stored under a
       ;; `rewriteOf` target.
       (reify-nat-for-read kb context))
     context)))

(defn- merge-colliding-nats!
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

(defn- reconcile-correspondence!
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

(defn reconcile-nats!
  "The reified-constant maintenance a just-asserted `sentence` owes, in the order the
  assert path runs it: the collision merge first, then the correspondence.

  An equality assert is a rename, and its migration can collapse two reified constants
  onto one expression — so `merge-colliding-nats!` restores the 1:1
  constant↔expression invariant, and only after an equality, since nothing else can
  break it.  `reconcile-correspondence!` then equates an application with the value its
  corresponding predicate names, whichever of the application, the fact and the
  declaration arrived last.

  Both are no-ops — one integer read each — on a KB that states no equality and declares
  no correspondence.  `vaelii.impl.nat-maintenance/reconcile-assert` is the caller, and it
  holds the `any-reifiable-functions?` gate ahead of this."
  [kb sentence]
  (when (kb/equality-sentence? sentence)
    (merge-colliding-nats! kb sentence))
  (reconcile-correspondence! kb sentence))
