;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.rules
  "A rule *is* a sentex — same structure (sentence + context), different indexing.
  Its sentence is an implication:

    (implies (and <antecedent> ...) <consequent>)     ; single antecedent needs no `and`

  Antecedents and consequent are sentence patterns that may contain variables.
  Rules are indexed by their antecedent/consequent predicates (see the index
  store) so forward chaining finds candidate rules without scanning, and — being
  ordinary sentexes — they get handles, TMS support, and retraction for free.

  Rules must be range-restricted: every consequent variable appears in some
  antecedent, so a fired consequent is ground.  The one exemption is a **head
  existential** — a consequent variable explicitly marked `(exists ?y C)`, which
  forward firing skolemizes to a deterministic constant (docs/skolem.md); range
  restriction permits only the marked variable and still rejects any *accidentally*
  unbound one.  The same closure is required of an `exceptWhen` exception, which is a
  query rather than a conclusion but must be ground for the same reason (checked at the
  assert layer via `sentex/check-exception-closed`)."
  (:require [clojure.string :as str]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]))

;; The rule *form* — its functor, its parts, its builder — has one owner:
;; `vaelii.impl.sentex`, whose constructor both parses and rebuilds it, so its
;; spelling decisions are the stored spelling.  The names below are delegations
;; kept for this namespace's readers; the dependency direction — rules already
;; requires sentex for the wrapper tables, peeling, and exception machinery —
;; decides which namespace owns the form.

(defn rule-sentence?
  "Is `sentence` a rule form `(implies <ante> <conseq>)`?"
  [sentence]
  (sx/implies? sentence))

(defn rule?
  "Is `sentex` a rule — a record with an `:antecedent`?  The field is the discriminant
  everywhere; a rule record holds no sentence to test."
  [sentex]
  (some? (:antecedent sentex)))

(defn antecedents
  "The antecedent patterns of a rule sentence (unwrapping a leading `and`)."
  [sentence]
  (sx/rule-antecedents sentence))

(defn consequent [sentence] (sx/rule-consequent sentence))

(defn rule-sentence
  "Build a rule sentence from antecedent patterns and a consequent pattern.
  One spelling for the whole codebase — see `sentex/rule-sentence`."
  [antecedents consequent]
  (sx/rule-sentence antecedents consequent))

(defn antecedent-key
  "The antecedent-index key an antecedent `literal` files under: its functor, or
  `[:not f]` for a negation whose body has functor `f`.

  Keyed under the bare `not` every negated antecedent of every rule shares one bucket,
  and each arriving negation builds the view of, and tries to match, every one of them;
  keyed by the body's predicate an arriving `(not (p a))` reaches the rules with a
  negated antecedent on `p` — and, through `trigger-keys`' genl walk, those on a genl of
  `p`, which is the direction subsumption runs in under a negation.  A vector, so the key
  can never collide with a predicate, which is always a symbol.  The same spelling on the
  index side (`antecedent-predicates`, every writer) and the trigger side
  (`trigger-keys`)."
  [literal]
  (let [f (nm/functor literal)]
    (if (and (= sx/not-functor f) (= 2 (count literal)))
      (let [g (nm/functor (second literal))]
        (if (symbol? g) [:not g] f))
      f)))

(defn antecedent-keys
  "`antecedent-key` of each of `antes` — a rule record's `:antecedent`, or the antecedents
  `antecedent-predicates` splits off a sentence."
  [antes]
  (keep antecedent-key antes))

(defn antecedent-predicates
  "The antecedent-index keys of a rule `sentence` — each antecedent's `antecedent-key`.
  What `p/index-rule` files a rule under and what the `:rule-antecedents` roster counts;
  a positive literal's key is its predicate, a negated one's is `[:not pred]`."
  [sentence]
  (antecedent-keys (antecedents sentence)))

(defn dependency-predicates
  "The antecedent keys of a rule `sentence` as **`consequent-predicate` keys** — what a
  rule reading those antecedents depends on, spelled the way the thing that could
  satisfy it is filed.

  The two spellings differ on one shape and only one: an `antecedent-key` distinguishes
  negations by their body's predicate (`[:not flies]`, so an arriving `(not (p a))`
  reaches the rules that read a negation on `p` and not every rule that reads any
  negation), while a *conclusion* `(not (flies ?x))` is filed by its functor root, which
  is `not`.  So a reader looking a dependency up among the concluders has to ask for
  `not`; asking for `[:not flies]` reads an empty bucket, and an edge that is silently
  not there is a negation cycle `checks/check-stratified` accepts instead of refusing.

  Coarser than the index key, deliberately: every negated antecedent depends on every
  negated conclusion here.  Over-approximating is the safe direction for the one caller
  — refusing a stratified rule set is annoying, accepting an order-dependent one is a
  correctness hole (`wff/rule-edges`)."
  [sentence]
  (map #(if (vector? %) sx/not-functor %) (antecedent-predicates sentence)))

(defn trigger-keys
  "The antecedent-index keys an arriving fact `sentence` triggers rules through, and the
  trigger side of `antecedent-key`.

  A **positive** fact's predicate and its supertypes: a fact on a spec satisfies an
  antecedent on its genl, which is `match1`'s subsumption.  A **negative** fact is the
  mirror, because a `genl` edge carries the other way through a negation — `(not (p a))`
  entails `(not (q a))` for every *spec* `q` of `p` — so it triggers `[:not q]` for each
  spec of its body's predicate.

  **Enumerated from `roster` rather than from the spec closure**, `roster` being the live
  `:rule-antecedents` map of keys some stored rule reads.  The two sides of the mirror
  are not the same size: the positive fan walks the *up* set, which a hierarchy bounds by
  its depth, while the negative one walks the *down* set, which on a broad ontology is
  most of it — an arriving `(not (thing X))` would cost one index probe per type in the
  KB.  Keeping the negated keys some rule actually reads costs one `genls` membership
  test per such key, and rules reading a negation are few; a KB with none pays a map
  read.  Complete because the roster is bumped from `antecedent-predicates` at the same
  choke point that files the index keys (`special/index-rule-sentex`), so the keys a rule
  is filed under are exactly the keys the roster holds."
  [tax sentence roster]
  (let [k (antecedent-key sentence)]
    (if (vector? k)
      (let [g (second k)]
        (into [] (comp (filter vector?)
                       (filter #(contains? (tax/genls-global tax (second %)) g)))
              (keys roster)))
      (tax/genls-global tax k))))

(defn consequent-key
  "`consequent-predicate` of a rule whose consequent pattern is `c0`, read off the
  consequent itself — which a rule record holds as its `:consequent`."
  [c0]
  (let [c (let [inner (peek (sx/peel-rule-wrapper c0))]
            (if (sx/implies? inner) inner c0))]
    (nm/functor c)))

(defn consequent-predicate
  "The predicate a rule concludes.

  A **generator** concludes a rule, so its key is `implies` — reached by peeling the
  `set/*Rule` wrapper first, because that wrapper belongs to the rule being stamped
  rather than to the generator (docs/generators.md).  Without the peel one generator
  files under `set/defaultRule` and the next under `implies`, by nothing more than how
  its stamped rule happened to be written, and the single cell that answers *which rules
  are generators* would answer for some of them."
  [sentence]
  (consequent-key (consequent sentence)))

;; ---- virtual rule-direction predicates ----------------------------------
;; Wrapping a rule sets its inference direction on assert.  Default (a bare implies) is
;; :backward — forward chaining materializes a conclusion per match, intractable on a
;; large KB, so forward is opt-in (set/forwardRule).  Four directions:
;;   :forward / :both  forward AND backward (set/forwardRule adds forward without taking
;;                     the backward use away) — the forward mode the ontology uses.
;;   :backward         backward only (the default).
;;   :forward-only     forward-chains but is NOT usable in backward proof (set/forwardOnlyRule).
;;                     A tests-only mode — the shipped ontology never uses it.
;;   :inert            neither engine (documentation).
;; The *index* is complete either way — a rule is filed under both its antecedent and its
;; consequent predicates whatever its direction (`special/index-rule-sentex`) — and the
;; direction on the record is what the two chainers read.

(defn forward?  [direction] (contains? #{:forward :both :forward-only} direction))
(defn backward? [direction] (contains? #{:backward :both :forward} direction))

(defn forward-sentex?
  "Does this stored rule sentex forward-chain?  Read off the record, which carries
  the direction its `set/*Rule` wrapper set.  An `assumptionRule` (a choice head) and a
  `hard`/`softConstraint` (a contradiction marker) never chain — their heads are decided
  or forbidden by a solve, not derived — so they are inference-inert in both directions
  regardless of the direction they were written with."
  [sentex] (and (not (:assumption sentex)) (not (:constraint sentex))
                (forward? (:direction sentex))))

(defn backward-sentex?
  "Does this stored rule sentex backward-chain?  An `assumptionRule` / constraint rule
  does not (see `forward-sentex?`)."
  [sentex] (and (not (:assumption sentex)) (not (:constraint sentex))
                (backward? (:direction sentex))))

;; ---- exceptWhen: the rule states its own exception ------------------------
;; `(exceptWhen <query> <rule>)` blocks: for a binding its query holds of, the rule
;; does not conclude.  The exception is *not* part of the rule record — it is a
;; separate belief-following meta-sentex `(exceptWhen <query> (sentexHandle H))`
;; naming the rule by handle (`sentex/exceptWhen-meta`); the engine reads a rule's
;; exceptions through `provers/rule-exceptions`, and their predicates are registered
;; in the re-check index by the meta-sentex's own indexing (`special`).  See
;; docs/exceptions.md.

(defn assumption?
  "Is this stored rule sentex a `set/assumptionRule` — a choice rule whose head a solve
  decides rather than the chainer deriving?  Read straight off the record's
  `:assumption` field, like `:defeasible` (docs/solving.md)."
  [sentex] (boolean (:assumption sentex)))

(defn constraint-of
  "The constraint class of this stored rule sentex — `:hard` / `:soft` from its
  `set/hardConstraint` / `set/softConstraint` wrapper, or nil for an ordinary rule.
  Read straight off the record's `:constraint` field (docs/solving.md)."
  [sentex] (:constraint sentex))

(defn constraint?
  "Is this stored rule sentex a `set/hardConstraint` / `set/softConstraint` — a
  contradiction rule whose conjunctive body a solve grounds into a nogood?"
  [sentex] (boolean (:constraint sentex)))

;; ---- negation as failure: `unknown` antecedents --------------------------
;; An `(unknown S)` antecedent is closed-world negation inline in the rule body, the
;; per-literal cousin of `exceptWhen`: the rule does not conclude for a binding under
;; which `S` is derivable.  Like an exception it is re-evaluated (never stored) and
;; drives the same block / sweep / revive machinery — so the accessors below mirror
;; the exception ones, and `special`/`settle` read both.  (A standalone positive
;; `thereExists` is desugared away in the sentex constructor, so it is an ordinary
;; antecedent here, not a NAF one.)  See docs/naf.md.

(defn naf-antecedents-of
  "The `(unknown S)` antecedent literals of a raw rule *sentence* — for the checks
  that run before a rule is stored as a sentex (stratification)."
  [rule-sentence]
  (filter sx/unknown? (antecedents rule-sentence)))

(defn naf-antecedents
  "The `(unknown S)` antecedent literals of a stored rule — its negation-as-failure
  conditions."
  [sentex]
  (filter sx/unknown? (:antecedent sentex)))

(defn has-naf?
  "Does this rule carry any `unknown` antecedent?"
  [sentex]
  (boolean (seq (naf-antecedents sentex))))

(def different-flip-predicates
  "The predicates a fact can arrive on that flips a `(different …)` antecedent.

  `different` is negation as failure over two things: the equality closure, and the
  `indeterminate_term` category whose members are exempt from the unique-name assumption.
  A merge makes a difference stop holding, and pinning an indeterminate term makes one
  start — so a rule reading `different` owes a re-check on both, in both directions.

  A subkind of the category needs no entry: `special/recheck-on-predicate` fans an
  arriving fact's predicate up its `genls-global` closure, so a `(vague_kind Foggy)`
  declared under the category reaches a rule registered on `indeterminate_term` alone.
  `genl` is here because the edge itself is what makes a kind indeterminate, and a skolem
  is not, because a skolem's membership is minted rather than asserted and no fact ever
  arrives on it.

  The same set `checks/negative-predicates` runs the stratification edge to, because the
  question is the same one: what can withdraw a difference."
  '#{rewriteOf sameAs equals indeterminate_term genl})

(defn different-antecedents
  "The `(different …)` antecedent literals of a stored rule — its unique-name conditions,
  which read the equality closure and the `indeterminate_term` category rather than a fact
  the justification names."
  [sentex]
  (filter #(= 'different (nm/functor %)) (:antecedent sentex)))

(defn has-different?
  "Does this rule carry a `(different …)` antecedent?"
  [sentex]
  (boolean (seq (different-antecedents sentex))))

(defn watched-literals
  "The literals a re-check must actually watch for the query literal `q` — the frames
  peeled off until what is left is something a *fact* can carry.

  A query operator's own functor is not one: no sentex is stored under `unknown`,
  `thereExists` or `agg/count`, so a rule registered in the re-check index under one is
  registered under a predicate nothing ever arrives on, and no fact can ever queue it.
  The condition would then be evaluated correctly and re-evaluated never, which reads as
  a guard that holds whatever happens.

  So each frame yields what it reads: an `unknown` its conjuncts (recursively — a
  conjunction is watched conjunct by conjunct, since it starts holding when the *last*
  of them does), a `thereExists` its body, an aggregate its census body.  An `(and …)`
  is peeled for the same reason and reached the same way: nothing is stored under `and`,
  and a conjunction under a quantifier is a **joined** query (docs/naf.md) whose every
  conjunct can be the one that completes it.  Anything else is a literal a fact can
  carry, and is watched as itself.

  A `not` frame is deliberately **not** peeled: the trigger side keys an arriving
  `(not S)` under `not` too (`special/recheck-on-sentence` reads the sentence's own
  functor), so the two agree — coarsely, one bucket for every negated condition, but
  they agree, and peeling one side alone is what would break it.

  One function for both readers: an `unknown` antecedent's query, and an `exceptWhen`
  conjunct — which may itself be any of these, `exceptWhen`'s query being any closed
  level-6 goal."
  [q]
  (cond
    (sx/unknown? q)      (mapcat watched-literals (sx/naf-query-conjuncts q))
    (sx/there-exists? q) (watched-literals (nth q 2))
    (sx/aggregate? q)    (watched-literals (sx/aggregate-body q))
    (sx/conjunction? q)  (mapcat watched-literals (sx/conjuncts q))
    :else                [q]))

(defn watched-predicates
  "The predicates a re-check keys `queries` under — `watched-literals` of each, then its
  functor.  What `exceptWhen`'s three registration sites and the stratification graph
  read of an exception's conjuncts, and what `naf-predicates` reads of an `unknown`
  antecedent's."
  [queries]
  (keep nm/functor (mapcat watched-literals queries)))

(defn- naf-queries-of
  "The query literals one `(unknown …)` antecedent is evaluated as: its conjuncts
  (`sentex/naf-query-conjuncts`), each unwrapped to what the level-6 query reads.

  **Every** conjunct, because the antecedent is only maintained if all of them are
  watched: a conjunction blocks when all hold, so a fact arriving on any one of their
  predicates can be what makes the whole condition hold, and a rule keyed on the first
  conjunct alone would never be re-checked for the others."
  [unk]
  (mapcat watched-literals (sx/naf-query-conjuncts unk)))

(defn naf-predicates-of
  "The predicates a raw rule *sentence*'s `unknown` antecedents mention — for the
  stratification check on a rule not yet stored (the mirror of the exception's
  negative dependence)."
  [rule-sentence]
  (keep nm/functor (mapcat naf-queries-of (naf-antecedents-of rule-sentence))))

(defn naf-predicates
  "The predicates a rule's `unknown` antecedents mention — the keys the re-check index
  posts the rule under, so a fact arriving or leaving on one re-evaluates the NAF
  condition.  The exception analogue is `exception-predicates`; both feed the same
  `[:exception-index …]` index."
  [sentex]
  (keep nm/functor (mapcat naf-queries-of (naf-antecedents sentex))))

(defn naf-queries
  "The inner query literals of a rule's `unknown` antecedents (each conjunct, unwrapped
  past a `thereExists`), so the settle-time firing filter can shape them against a
  trigger exactly as it shapes an exception's conjuncts — the ground ones narrow, the
  existential ones fall through to 'keep' like any non-flat conjunct."
  [sentex]
  (mapcat naf-queries-of (naf-antecedents sentex)))

;; ---- aggregation: a rule antecedent that counts --------------------------
;; An aggregate antecedent is the other non-monotonic literal a rule body can carry:
;; `(agg/count ?n ?v S)` binds `?n` to a function of what is *believed*, so a
;; fact arriving on `S`'s predicate can withdraw a firing that rested on the old
;; count.  That is `unknown`'s maintenance problem exactly, so it takes `unknown`'s
;; machinery — the same re-check index, the same settle-time re-evaluation, the same
;; negative edge in the stratification graph.  See docs/aggregate.md.

(defn aggregate-antecedents-of
  "The aggregate antecedent literals of a raw rule *sentence* — for the checks that
  run before a rule is stored as a sentex (stratification)."
  [rule-sentence]
  (filter sx/aggregate? (antecedents rule-sentence)))

(defn aggregate-antecedents
  "The aggregate antecedent literals of a stored rule."
  [sentex]
  (filter sx/aggregate? (:antecedent sentex)))

(defn has-aggregate?
  "Does this rule carry any aggregate antecedent?"
  [sentex]
  (boolean (seq (aggregate-antecedents sentex))))

(defn aggregate-queries
  "The body queries of a rule's aggregate antecedents, so the settle-time firing
  filter can shape them against a trigger exactly as it shapes an exception's
  conjuncts.  The **whole** body, conjunctive or not: a conjunction has no readable
  shape and a one-literal body mentions the reduction variable by construction, so
  neither is ground and every one falls through to 'keep' — an aggregate's firings are
  never narrowed away, which is the safe direction.  A reader that needs the conjuncts
  themselves peels them with `watched-literals`, as `special` does to find the negated
  ones."
  [sentex]
  (map sx/aggregate-body (aggregate-antecedents sentex)))

(defn aggregate-predicates-of
  "The predicates a raw rule *sentence*'s aggregate bodies mention — the negative-edge
  keys the stratification graph reads, and the re-check keys the index posts under.

  Read through `watched-literals`, for the reason the `unknown` side is: a **joined**
  census body is watched conjunct by conjunct, since a fact arriving on any one of their
  predicates changes which witnesses the join finds and so what the count is.  Keying on
  the body's own functor would post a conjunctive body under `and`, a predicate nothing
  ever arrives on — a count that is evaluated correctly and re-evaluated never."
  [rule-sentence]
  (watched-predicates (aggregate-antecedents-of rule-sentence)))

(defn aggregate-predicates
  "The predicates a stored rule's aggregate bodies mention."
  [sentex]
  (watched-predicates (aggregate-antecedents sentex)))

;; ---- a closed extent: `(not (P …))` read as negation as failure ----------
;; `(closed_extent_predicate P)` is a context-scoped grant that P's **believed** extent is
;; complete, so nothing being stored about `(P a)` is enough to conclude `(not (P a))`
;; (docs/naf.md).  In a rule body that turns a *closed* negative antecedent into a NAF
;; literal: withheld from the join, decided at derive time, and maintained on the same
;; re-check index `unknown` uses.  The structural half lives here; whether the grant is
;; in force is a taxonomy read the callers pass in.

(defn negative-literal?
  "Is `a` a `(not (P …))` literal with a flat, symbol-headed body — the form a closed
  extent can be read over?"
  [a]
  (and (sequential? a) (= 2 (count a)) (= 'not (first a))
       (let [b (second a)] (and (sequential? b) (symbol? (first b))))))

(defn closed-negative-antecedents
  "The `(not L)` antecedents of `antes` every variable of which another **generator**
  antecedent binds — the negative literals that are a *test* rather than a source of
  bindings.

  Only these can be read as negation as failure.  A negative antecedent whose variable
  nothing else binds is what *produces* that binding, by matching a stored `(not …)`;
  withholding it from the join would leave the rule with nothing to fire on, which is a
  silently inert rule rather than a different reading."
  [antes]
  (let [gens  (remove #(or (sx/unknown? %) (sx/deferred-literal? %) (negative-literal? %))
                      antes)
        bound (into #{} (mapcat sx/free-vars) gens)]
    (filterv #(and (negative-literal? %) (every? bound (sx/free-vars %))) antes)))

(defn closed-extent-antecedents
  "The closed negative antecedents of `antes` whose predicate `tx` declares a closed
  extent — read **unscoped**, because the join has no placement context to scope by, and
  an over-selected literal is one derive time decides correctly anyway: it asks the full
  level-6 question in the conclusion's context, which a context without the grant answers
  exactly as it does today.

  Gated on the KB declaring any closed extent at all, so a KB not using the feature pays
  one set read on the join path and stops."
  [tx antes]
  (if (empty? (tax/props tx :closed-extent))
    []
    (filterv #(tax/has-prop? tx :closed-extent (nm/functor (second %)))
             (closed-negative-antecedents antes))))

(defn closed-extent-predicates-of
  "The predicates a raw rule *sentence*'s closed-extent negative antecedents read — the
  re-check keys the index posts the rule under, and the negative edges the stratification
  graph reads.  The key is the predicate **inside** the `not`: `recheck-on-sentence` posts
  an arriving sentence under its own functor *and* its underlying body's, so this one key
  catches a `(P a)` arriving and a `(not (P a))` arriving alike."
  [tx rule-sentence]
  (keep #(nm/functor (second %)) (closed-extent-antecedents tx (antecedents rule-sentence))))

(defn has-nested-naf?
  "Does this rule carry a NAF query with a **NAF inside it** — a nested `(unknown …)`,
  or an aggregate under the quantifier?

  The distinction is about which direction an arriving fact moves the condition.  A
  plain `(unknown S)` is antitone in what the KB derives: a fact can only make `S`
  derivable, so it can only *block*.  A nested one is not — `(unknown (thereExists ?y
  (and (childOf Bob ?y) (unknown (asleep ?y)))))` is the `forall` desugar, and an
  arriving `(asleep …)` removes the witness and **releases** the block.  So such a rule
  is owed a re-join whatever the blocked set did, exactly as an aggregate is."
  [sentex]
  (boolean (some (fn [unk] (sx/some-form #(or (sx/unknown? %) (sx/aggregate? %))
                                         (second unk)))
                 (naf-antecedents sentex))))

(defn arrival-releasable?
  "Can an arriving fact *release* one of this rule's re-check conditions rather than
  only impose one?  True for an **aggregate** (a census that rose licenses a firing no
  block ever suppressed) and for a **nested** NAF (a fact can remove the witness the
  inner query found).  Both are the same asymmetry: the blocked set is the wrong
  instrument, because there was never a blocked justification to move.

  Read by the settle loop, which owes such a rule a re-join, and by the two taxonomy
  edge triggers, which wave it through their firing-side narrowing for the same reason:
  a firing that never existed leaves no placement and no bindings to test."
  [sentex]
  (or (has-aggregate? sentex) (has-nested-naf? sentex)))

(defn recheck-predicates
  "The predicates whose change must re-check this rule for its **own** re-check
  conditions — the predicates its `unknown` antecedents and its **aggregate** bodies
  mention, plus `different-flip-predicates` where it reads `different`.  A closed-extent
  negative antecedent adds its own
  (`closed-extent-predicates-of`), separately, because whether it is one is a taxonomy
  read rather than a property of the sentence.  (An exceptWhen exception is a separate meta-sentex, registered under its
  rule by the meta-sentex's own indexing; it is not read off the rule.)  The key set
  the `[:exception-index …]` index posts a rule under when it is indexed.

  The three kinds are one key set because they are one problem: each reads what the KB
  believes at firing time rather than a fact the justification names, so each needs a
  fact arriving on those predicates to bring the firing back for re-decision.  A
  `different` antecedent is the case with nothing to name at all — it holds by the
  *absence* of a merge, so no support handle exists for a justification to carry and the
  re-check is the only instrument that can withdraw the firing (docs/predall.md)."
  [sentex]
  (distinct (concat (naf-predicates sentex)
                    (aggregate-predicates sentex)
                    (when (has-different? sentex) different-flip-predicates))))

(defn rechecked?
  "Does this rule carry a re-check condition of its **own** — an `unknown` antecedent, an
  aggregate, or a `different` antecedent?  The gate on registering it in the re-check
  index; an exceptWhen exception is registered by its own meta-sentex and is not read off
  the rule."
  [sentex]
  (or (has-naf? sentex) (has-aggregate? sentex) (has-different? sentex)))

;; ---- what the join cannot do, and the placement can ----------------------
;; An aggregate is evaluated per **placement context**, not in the join, because a
;; census depends on where it is taken and the join does not yet know where the
;; conclusion lands.  So its `?n` is unbound for the whole join — and that reaches
;; further than the aggregate itself: a `(lessThan 2 ?n)` written after it is a
;; *computed* literal, so it has no fact to match and nothing to wait for, and the
;; chainer refuses to run it against an unbound input rather than report a comparison
;; that never ran as one that failed.
;;
;; The answer is that such a literal is not a join literal at all.  It moves to the
;; placement phase with the aggregate that feeds it, where `?n` exists — which is also
;; the context the backward chainers evaluate it in, so the three agree.

(defn post-join-literals
  "The antecedent literals evaluated **after** the join: every aggregate, plus every
  deferred literal reading a variable an aggregate produces — or that one of *those*
  produces in turn, so an `(evaluate ?d (+ ?n 1))` carries a later `(lessThan ?d 9)`
  along with it.

  **In written order**, which is the order they run in, because a computed literal
  reads what is written before it.  That is not a rule aggregates introduce: an
  `evaluate` chain has always had to be written downhill, since canonical order holds a
  deferred literal in the author's position and every chainer runs it there.  Making an
  aggregate an exception — reordering the phase so a comparison could be written above
  its own count — is what a *forward* chainer could do and a backward one could not, so
  it would buy convenience at the price of the two disagreeing about one rule.
  `sentex/check-naf-closed` refuses the uphill writing instead.

  `unknown` is deliberately not here: it binds nothing, so it never needs the ordering,
  and it is already evaluated per placement as `:naf`.

  Asked on **every** join, so the gate is a short-circuiting `some` that allocates
  nothing: no aggregate, no post-join phase, and the overwhelming majority of rules
  have none."
  [antes]
  (if-not (some sx/aggregate? antes)
    []
    (:out (reduce (fn [{:keys [produced out] :as acc} a]
                    (if (or (sx/aggregate? a)
                            (and (sx/deferred-literal? a)
                                 (not (sx/unknown? a))
                                 (some produced (sx/deferred-input-vars a))))
                      {:produced (into produced (sx/deferred-output-vars a))
                       :out      (conj out a)}
                      acc))
                  {:produced #{} :out []}
                  antes))))

(defn post-join-antecedents
  "`post-join-literals` over a stored rule's antecedents."
  [sentex]
  (post-join-literals (vec (:antecedent sentex))))

(def ^:private direction-wrapper
  "The surface `set/*Rule` wrapper each direction rewraps and exports to.  `:backward` is
  the default (a bare implies), so it needs no wrapper; `:both` and `:forward` both mean
  forward + backward and write as `set/forwardRule`; `:forward-only` (forward, never
  backward — a tests-only mode) writes `set/forwardOnlyRule`; `:inert` writes
  `set/inertRule`."
  '{:forward set/forwardRule :both set/forwardRule
    :forward-only set/forwardOnlyRule :inert set/inertRule})

(defn wrap-direction
  "Express `direction` as the corresponding `set/*Rule` wrapper around `sentence`.
  `:backward` needs no wrapper — a bare `(implies …)` is backward by default."
  [sentence direction]
  (if-let [w (direction-wrapper direction)] (list w sentence) sentence))

(defn inner-rule
  "The bare `(implies …)` inside any virtual rule wrappers (`set/*Rule` and
  `exceptWhen`, which may nest in any order — a defeasible forward rule with an
  exception).  The direction / default / assumption wrappers become record fields and
  the exceptWhen becomes a meta-sentex, so the checks and the stored sentence both work
  on this.

  A `forall` antecedent is desugared here too (`sentex/desugar-forall-rule`), so every
  pre-storage check — range restriction, closure, quantifier locality, stratification —
  reads the nested NAF the constructor will store rather than the sugar it was written
  with.  A stored rule holds no `forall`, so this is the identity on one."
  [sentence]
  (let [[_ _ _ _ _ inner] (sx/peel-rule-wrapper sentence)]
    (sx/desugar-forall-rule inner)))

;; ---- cardinality bounds on choice heads ----------------------------------
;; `(asp/atMost k ?v pattern)` bounds how many of the ground choice heads matching
;; `pattern` a solve may set true — counting over the projected variable `?v` and
;; grouping by the pattern's other variables, the way `agg/count` projects a variable.
;; It is not an `(implies …)` rule, so it is normalized (below) into an ordinary
;; hard/soft constraint rule whose consequent MARKER carries the operator and the bound:
;;   (asp/atMost 6 ?c (empireBuild ?c transport))
;;     -> (set/hardConstraint (implies (empireBuild ?c transport) (cardAtMost 6 ?c)))
;; Everything downstream then treats it as the constraint rule it is — the trie key, the
;; codec, and subsumption all distinguish `atMost 6` from `atMost 3` and from a bare twin
;; because k and the operator ride the stored consequent, so none of them need a new arm.
;; Only `solve-context` reads the marker back (`cardinality-of`) and grounds it to ONE
;; solver cardinality atom rather than the `C(n, k+1)` subset nogoods a hand-written
;; encoding needs (docs/solving.md).

(def cardinality-markers
  "The consequent-marker functors a normalized cardinality rule carries."
  '#{cardAtMost cardAtLeast})

(def ^:private cardinality-wrappers
  "The four surface wrappers → `[marker constraint-class]`."
  '{asp/atMost      [cardAtMost  :hard]
    asp/atLeast     [cardAtLeast :hard]
    asp/softAtMost  [cardAtMost  :soft]
    asp/softAtLeast [cardAtLeast :soft]})

(def ^:private cardinality-rewrap
  "The inverse of `cardinality-wrappers`: `[marker constraint-class]` → surface wrapper,
  so `rewrap` restores the authored form on export."
  (into {} (map (fn [[w mc]] [mc w])) cardinality-wrappers))

;; ---- minimize objectives and soft-constraint priorities ------------------
;; `asp/minimize` and a priority-tagged `set/softConstraint` are the answer-set
;; *objective* surface — the weak-constraint counterpart to the hard/soft nogoods.  Like
;; the cardinality bounds they normalize into an internal `set/softConstraint` whose
;; consequent MARKER carries the extra operands (a priority level, and for a minimize the
;; per-head weight variable), so nothing downstream needs a new rule arm: `solve-context`
;; reads the marker back (`soft-cost-of`), and `edge/translate` already keys a minimize's
;; objective level off the nogood's `:priority` and its per-literal weight off `[[v w]]`.
;; A soft with no priority stays level-1 (`:priority 1`), unit weight, as every soft was
;; before.  Distinct priorities become distinct lexicographic minimize levels, so a
;; lower-priority tiebreak breaks ties among the higher objective's optima without the
;; solver churning a plateau of equal-cost models (docs/solving.md).

(def minimize-marker
  "The consequent-marker functor a normalized `asp/minimize` carries:
  `(minimizeCost <priority> <weight-var>)`."
  'minimizeCost)

(def soft-priority-marker
  "The consequent-marker functor a normalized priority-tagged `set/softConstraint`
  carries: `(softPriority <priority> <the authored consequent>)`."
  'softPriority)

(def minimize-wrapper 'asp/minimize)

(def ^:private priority-constraint-wrappers
  "The constraint wrappers a leading-integer priority may tag."
  '#{set/softConstraint set/hardConstraint})

(defn minimize-surface?
  "Is `sentence` a `(asp/minimize priority ?weight body)` surface form?"
  [sentence]
  (boolean (and (sequential? sentence) (seq sentence)
                (= minimize-wrapper (first sentence)))))

(defn soft-priority-surface?
  "Is `sentence` a priority-tagged constraint wrapper — a leading positive integer before
  the rule, `(set/softConstraint P (implies …))`?"
  [sentence]
  (boolean (and (sequential? sentence) (= 3 (count sentence))
                (contains? priority-constraint-wrappers (first sentence))
                (integer? (second sentence)))))

(defn cardinality-surface?
  "Is `sentence` a `(asp/atMost …)` / `(asp/atLeast …)` surface form (or a soft twin)?"
  [sentence]
  (boolean (and (sequential? sentence) (seq sentence)
                (contains? cardinality-wrappers (first sentence)))))

(defn normalize-cardinality
  "Rewrite a `(asp/atMost k ?v pattern)` surface form into the internal constraint rule
  `(set/hardConstraint (implies pattern (cardAtMost k ?v)))` — the soft twins into
  `set/softConstraint`.  The identity on anything else, so `assert` and `check` apply it
  to every sentence.

  Refuses a malformed bound here, at the entry point, before storage: `k` a non-negative
  integer, `?v` a variable the pattern binds, `pattern` a literal.  The range check that
  runs on the rewritten rule then holds `?v` to the pattern for free — the counted
  variable is the consequent marker's only variable, and it comes from the antecedent."
  [sentence]
  (if-not (cardinality-surface? sentence)
    sentence
    (let [[wrapper k v pattern] sentence
          [marker klass]        (cardinality-wrappers wrapper)]
      (when-not (= 4 (count sentence))
        (throw (ex-info (str "a cardinality bound is (" wrapper " k ?counted pattern); got "
                             (pr-str sentence))
                        {:type :not-well-formed :sentence sentence})))
      (when-not (and (integer? k) (not (neg? k)))
        (throw (ex-info (str "a cardinality bound's count must be a non-negative integer; got "
                             (pr-str k) " in " (pr-str sentence))
                        {:type :not-well-formed :sentence sentence :count k})))
      (when-not (sx/variable? v)
        (throw (ex-info (str "a cardinality bound's counted slot must be a variable; got "
                             (pr-str v) " in " (pr-str sentence))
                        {:type :not-well-formed :sentence sentence :counted v})))
      (when-not (and (sequential? pattern)
                     (some #{v} (filter sx/variable? (tree-seq sequential? seq pattern))))
        (throw (ex-info (str "a cardinality bound's counted variable " (pr-str v)
                             " must appear in the pattern " (pr-str pattern))
                        {:type :not-well-formed :sentence sentence :counted v :pattern pattern})))
      (list (get {:hard 'set/hardConstraint :soft 'set/softConstraint} klass)
            (sx/rule-sentence [pattern] (list marker k v))))))

(defn normalize-soft-priority
  "Rewrite a priority-tagged `(set/softConstraint P (implies body C))` into the internal
  `(set/softConstraint (implies body (softPriority P C)))`, moving the priority level onto
  the consequent marker so the split, the checks, and the store see an ordinary soft
  constraint.  The identity on anything else.

  Refuses a malformed form here, before storage: the priority a positive integer, the
  wrapper `set/softConstraint` (a hard constraint is an integrity constraint, never
  minimized, so a priority on it is meaningless), and the body a rule."
  [sentence]
  (if-not (soft-priority-surface? sentence)
    sentence
    (let [[wrapper priority inner] sentence]
      (when-not (= 'set/softConstraint wrapper)
        (throw (ex-info (str "a priority applies only to a minimized soft constraint; "
                             (pr-str wrapper) " is a hard integrity constraint with no "
                             "objective level: " (pr-str sentence))
                        {:type :not-well-formed :sentence sentence})))
      (when-not (pos-int? priority)
        (throw (ex-info (str "a soft constraint's priority must be a positive integer; got "
                             (pr-str priority) " in " (pr-str sentence))
                        {:type :not-well-formed :sentence sentence :priority priority})))
      (when-not (and (sx/implies? inner) (= 3 (count inner)))
        (throw (ex-info (str "a priority-tagged soft constraint wraps a rule; got "
                             (pr-str inner) " in " (pr-str sentence))
                        {:type :not-well-formed :sentence sentence})))
      (list 'set/softConstraint
            (list 'implies (second inner)
                  (list soft-priority-marker priority (nth inner 2)))))))

(defn normalize-minimize
  "Rewrite `(asp/minimize priority ?weight body)` into the internal soft constraint
  `(set/softConstraint (implies body (minimizeCost priority ?weight)))` — a soft whose
  choice-head body is penalized by the data weight `?weight` at `priority`, so the
  objective at that level sums `?weight` over every chosen head.  `body` names a choice
  head and binds `?weight` off a background fact — the weak-constraint idiom
  `#minimize{ W@P, head : head-facts, weight-fact }`.  The identity on anything else.

  Refuses a malformed form: the priority a positive integer, `?weight` a variable the body
  binds, `body` a literal or conjunction."
  [sentence]
  (if-not (minimize-surface? sentence)
    sentence
    (let [[_ priority w body] sentence]
      (when-not (= 4 (count sentence))
        (throw (ex-info (str "a minimize is (asp/minimize priority ?weight body); got "
                             (pr-str sentence))
                        {:type :not-well-formed :sentence sentence})))
      (when-not (pos-int? priority)
        (throw (ex-info (str "a minimize's priority must be a positive integer; got "
                             (pr-str priority) " in " (pr-str sentence))
                        {:type :not-well-formed :sentence sentence :priority priority})))
      (when-not (sx/variable? w)
        (throw (ex-info (str "a minimize's weight slot must be a variable; got " (pr-str w)
                             " in " (pr-str sentence))
                        {:type :not-well-formed :sentence sentence :weight w})))
      (when-not (and (sequential? body)
                     (some #{w} (filter sx/variable? (tree-seq sequential? seq body))))
        (throw (ex-info (str "a minimize's weight variable " (pr-str w) " must appear in "
                             "the body " (pr-str body))
                        {:type :not-well-formed :sentence sentence :weight w :body body})))
      (list 'set/softConstraint
            (list 'implies body (list minimize-marker priority w))))))

(def internal-markers
  "The consequent-marker functors the answer-set surfaces normalize into.  No authored
  sentence spells one: `refuse-internal-marker` refuses a constraint rule that does."
  (conj cardinality-markers minimize-marker soft-priority-marker))

(def ^:private internal-marker-surface
  "The surface form to write in place of each internal marker, for the refusal message."
  '{cardAtMost   "(asp/atMost k ?counted pattern) or (asp/softAtMost …)"
    cardAtLeast  "(asp/atLeast k ?counted pattern) or (asp/softAtLeast …)"
    minimizeCost "(asp/minimize priority ?weight body)"
    softPriority "(set/softConstraint priority (implies body marker))"})

(defn- authored-constraint-consequents
  "The consequent literals of the rule a constraint wrapper holds, as written: through any
  direction, default or assumption wrapper around the constraint wrapper and past a leading
  priority inside it, one per conjunct of a conjunctive consequent.  Empty for every other
  sentence."
  [sentence]
  (let [peel? (fn [s] (and (sequential? s) (= 2 (count s))
                           (let [h (first s)]
                             (or (contains? sx/rule-direction-wrappers h)
                                 (= sx/default-rule-wrapper h)
                                 (= sx/assumption-rule-wrapper h)))))
        s     (loop [s sentence] (if (peel? s) (recur (second s)) s))]
    (if-not (and (sequential? s) (seq s) (contains? sx/constraint-rule-wrappers (first s)))
      []
      (let [inner (last s)
            c     (when (and (sx/implies? inner) (= 3 (count inner))) (nth inner 2))]
        (if (and (sequential? c) (= 'and (first c))) (rest c) (some-> c vector))))))

(defn refuse-internal-marker
  "Throw `:not-well-formed` when a constraint rule's authored consequent is one of the
  `internal-markers`; return `sentence` unchanged otherwise.  A hand-written marker skips
  the operand checks its surface form runs, and the solve reads each operand as a count or
  an objective level, so a symbol operand such as `(cardAtMost ?a ?c)` would reach
  arithmetic and throw a bare `ClassCastException` out of `do/label`."
  [sentence]
  (if-let [m (some #(when (and (sequential? %) (contains? internal-markers (first %))) %)
                   (authored-constraint-consequents sentence))]
    (throw (ex-info (str (pr-str (first m)) " is the internal marker a solve surface "
                         "normalizes into, not an authored consequent; write "
                         (internal-marker-surface (first m)) " instead: " (pr-str sentence))
                    {:type :not-well-formed :sentence sentence :marker (first m)}))
    sentence))

(defn normalize-solve-surface
  "Rewrite the answer-set surface forms — cardinality bounds, priority-tagged soft
  constraints, and minimize objectives — into their internal constraint-rule forms, so
  the split, the checks, and the store all see ordinary constraint rules.  Each rewrite is
  the identity off its own surface, and the three surfaces are disjoint, so the order does
  not matter; the identity on every other sentence.  A constraint rule that spells an
  internal marker itself is refused first (`refuse-internal-marker`)."
  [sentence]
  (-> sentence refuse-internal-marker
      normalize-cardinality normalize-soft-priority normalize-minimize))

(defn cardinality-of
  "The cardinality bound a stored constraint rule expresses — `{:op :at-most|:at-least
  :k int :counted ?v}` — read off the consequent marker `(cardAtMost k ?v)` /
  `(cardAtLeast k ?v)`, or nil for an ordinary constraint rule."
  [sentex]
  (let [c (:consequent sentex)]
    (when (and (sequential? c) (contains? cardinality-markers (first c)))
      {:op      (if (= 'cardAtMost (first c)) :at-most :at-least)
       :k       (second c)
       :counted (nth c 2)})))

(defn soft-cost-of
  "Read the objective level and per-head weight a **ground** soft-constraint marker
  carries, for `solve-context` to put on the nogood — the counterpart to `cardinality-of`
  for the minimize/priority surface:

    `(minimizeCost p w)` → `{:priority p :weight w :marker marker}` — a minimize term over
                           the chosen head, weighted `w` at level `p`;
    `(softPriority p m)` → `{:priority p :marker m}` — the authored soft `m`, at level `p`,
                           unit weight;
    anything else        → `{:priority 1 :marker marker}` — an ordinary soft, level 1.

  `:marker` is the value to name the nogood by (the authored one, unwrapped)."
  [marker]
  (cond
    (and (sequential? marker) (= minimize-marker (first marker)))
    {:priority (nth marker 1) :weight (nth marker 2) :marker marker}
    (and (sequential? marker) (= soft-priority-marker (first marker)))
    {:priority (nth marker 1) :marker (nth marker 2)}
    :else
    {:priority 1 :marker marker}))

;; ---- polycanonicalization: split a conjunctive consequent ----------------

(defn- conjunctive? [c] (and (sequential? c) (= 'and (first c))))

(defn rewrap
  "Put the direction / default / assumption / constraint wrappers a rule was written
  with back around `sentence` — the inverse of `sx/peel-rule-wrapper`, since the
  wrappers ride the record, not the stored sentence.  Four callers: a polycanonicalized
  conjunct keeps the mode of the rule it came from, `split-exceptWhen` restores the
  qualified rule's other wrappers after stripping the exception, an equality merge's
  migrated rule twin keeps the mode of the rule it restates (`special/migrate-sentex`),
  and an imported rule record is rebuilt around the modes its frame carries
  (`io.import`).  An
  exceptWhen is not among them — it is split off before this runs and stored as a
  meta-sentex against each conjunct's handle (`split-exceptWhen`).

  A **cardinality** constraint rule restores its authored surface instead of the
  internal `set/hardConstraint (implies …)` form: its consequent is a `cardAtMost` /
  `cardAtLeast` marker, so `(asp/atMost k ?v pattern)` comes back rather than the rule it
  was normalized to (`normalize-cardinality`)."
  [sentence direction defeasible assumption constraint]
  (let [conseq (when (sx/implies? sentence) (consequent sentence))
        cf     (when (sequential? conseq) (first conseq))]
    (cond
      ;; a minimize restores its authored `(asp/minimize p ?w body)` — the whole
      ;; antecedent form is the body, conjunctive or not
      (and constraint (= minimize-marker cf))
      (let [[_ p w] conseq]
        (list minimize-wrapper p w (second sentence)))
      ;; a priority-tagged soft restores `(set/softConstraint p (implies body C))`
      (and constraint (= soft-priority-marker cf))
      (let [[_ p m] conseq]
        (list 'set/softConstraint p (list 'implies (second sentence) m)))
      ;; a cardinality bound restores its authored surface (`normalize-cardinality`)
      (and constraint (contains? cardinality-markers cf))
      (let [[marker k v] conseq]
        (list (cardinality-rewrap [marker constraint]) k v (first (antecedents sentence))))
      :else
      (cond-> sentence
        defeasible      (->> (list sx/default-rule-wrapper))
        assumption      (->> (list sx/assumption-rule-wrapper))
        constraint      (->> (list (get {:hard 'set/hardConstraint :soft 'set/softConstraint}
                                        constraint)))
        direction       (wrap-direction direction)))))

(defn expand-consequent
  "Polycanonicalize a rule that concludes a conjunction into one rule per conjunct,
  preserving any virtual wrapper (default / forward / backward / inert / assumptionRule).
  A rule `(implies A (and C1 C2))` becomes `[(implies A C1) (implies A C2)]`; anything
  else (a non-rule, or a rule with a single consequent) returns `[sentence]` unchanged.

  Runs on a rule whose exceptWhen has already been split off (`split-exceptWhen`), so
  the exception is re-attached once per conjunct by the caller, against each conjunct's
  own handle."
  [sentence]
  (let [[dir def? _exc assum con inner] (sx/peel-rule-wrapper sentence)]
    (if (and (rule-sentence? inner)
             (conjunctive? (consequent inner)) (seq (rest (consequent inner))))
      (let [as (antecedents inner)]
        (mapv #(rewrap (rule-sentence as %) dir def? assum con) (rest (consequent inner))))
      [sentence])))

;; ---- polycanonicalization: distribute a disjunctive antecedent ----------
;; The antecedent twin of the conjunctive-consequent split above, and the same trick:
;; `or` never reaches the record.  `(implies (or A B) C)` is stored as the two rules
;; `(implies A C)` and `(implies B C)`, each an ordinary rule sentex with its own
;; handle, its own justifications and its own retraction — so nothing downstream of the
;; assert entry point has to know the connective exists.  The two splits compose: a rule that
;; disjoins its antecedent *and* conjoins its consequent stores the **product**
;; (`expand-rule`).  See docs/canonicalization.md.

(def max-alternatives
  "How many alternatives one rule may expand to.  A disjunctive antecedent is *stored*
  expanded, so the width is paid in handles, index entries and TMS nodes rather than at
  query time — and a nest of `or`s multiplies, so the cost of a typo is exponential in a
  sentence that still reads like one line.  Sixteen is the width past which a rule is
  better written as a type: assert a `genl` and one rule on the supertype, which is one
  handle however many members it covers."
  16)

(defn- distributes-or?
  "Does this antecedent form carry an `or` in a position the DNF distributes over —
  itself, or inside an `and` / `or` it nests in?  An `or` in an *argument* slot is a
  term, not a connective frame, and is left where it stands."
  [form]
  (cond
    (sx/disjunction? form) true
    (conjunctive? form)    (boolean (some distributes-or? (rest form)))
    :else                  false))

(defn- alternative-count
  "How many DNF alternatives one antecedent form yields — a sum over an `or`'s
  disjuncts, a product over a distributing `and`'s conjuncts, one for a literal.
  Arithmetic rather than a count of the expansion, so a rule far over the cap is
  refused without ever being materialized: `+'` and `*'` promote, so a nest deep enough
  to overflow a long still reports its own width."
  [form]
  (cond
    (sx/disjunction? form) (reduce +' 0 (map alternative-count (sx/disjuncts form)))
    (and (conjunctive? form) (distributes-or? form))
    (reduce *' 1 (map alternative-count (rest form)))
    :else 1))

(defn- antecedent-alternative-count
  "The number of rules a whole antecedent list expands to — the product of its members'."
  [antes]
  (reduce *' 1 (map alternative-count antes)))

(defn antecedent-alternatives
  "The DNF alternatives of an antecedent list, as `{:antecedents [...] :choices [...]}`
  in written order — `:antecedents` being that alternative's literals and `:choices` the
  disjuncts it took, which is what a refusal names when one alternative is the bad one.

  A disjunct that is itself compound contributes its *own* choices rather than being
  named whole, so the innermost disjunct is what a message points at: in
  `(or (and A (or B C)) D)` an alternative's choice is `B`, `C` or `D`, never the `and`."
  [antes]
  (letfn [(combine [xs ys]
            (for [x xs, y ys]
              {:antecedents (into (:antecedents x) (:antecedents y))
               :choices     (into (:choices x) (:choices y))}))
          (dnf [form]
            (cond
              (sx/disjunction? form)
              (for [d (sx/disjuncts form), alt (dnf d)]
                (if (seq (:choices alt)) alt (assoc alt :choices [d])))

              (and (conjunctive? form) (distributes-or? form))
              (reduce combine [{:antecedents [] :choices []}] (map dnf (rest form)))

              :else [{:antecedents [form] :choices []}]))]
    (reduce combine [{:antecedents [] :choices []}] (map dnf antes))))

(defn expand-antecedent
  "Polycanonicalize a rule whose antecedent disjoins into one rule per DNF alternative,
  preserving any virtual wrapper.  `(implies (or A B) C)` becomes
  `[(implies A C) (implies B C)]` and `(implies (and (or A B) D) C)` distributes to
  `[(implies (and A D) C) (implies (and B D) C)]`; anything else — a non-rule, a rule
  with no `or`, an `or` in an argument slot — returns `[sentence]` unchanged.

  **Only the level written here.**  A generator's stamped rule keeps its `or` until the
  mint substitutes the holes, and `chain/mint-rule` expands what it is about to store —
  so the alternatives a generator stamps are the alternatives of the rule it stamped,
  and each is checked and indexed in its own right.

  Returns `[sentence]` unexpanded for a rule the cap refuses or an empty `(or)`, which
  is what keeps the refusal loud rather than large: `disjunction-problems` reports both
  from the unexpanded form, and materializing 2^n rules to find out how many there were
  is the cost the cap exists to not pay."
  [sentence]
  (let [[dir def? _exc assum con inner] (sx/peel-rule-wrapper sentence)]
    (if (and (rule-sentence? inner) (some distributes-or? (antecedents inner)))
      (let [antes (antecedents inner)
            n     (antecedent-alternative-count antes)]
        (if (or (zero? n) (> n max-alternatives))
          [sentence]
          (mapv #(rewrap (rule-sentence (:antecedents %) (consequent inner))
                         dir def? assum con)
                (antecedent-alternatives antes))))
      [sentence])))

(defn expand-rule
  "Both polycanonicalizations of a rule, composed: one rule per DNF alternative of the
  antecedent, and within each, one per conjunct of the consequent.  A rule that does
  neither returns `[sentence]`, so every caller can treat the result uniformly.

  The **product**, and in that order — alternatives outermost, conjuncts within — which
  is the order `assert` stores them and therefore the order an `exceptWhen` is
  re-attached along.  `(implies (or A B) (and C1 C2))` stores four rules."
  [sentence]
  (into [] (mapcat expand-consequent) (expand-antecedent sentence)))

(defn split-exceptWhen
  "Split an `(exceptWhen <query> <rule>)` assertion into `[exception inner]`.

  `exception` is the flattened conjunction of every exceptWhen wrapper (a vector of
  literals in the author's variable names, block-if-all-hold), and `inner` is what the
  exceptWhen qualifies: the wrapped rule with its exceptWhen(s) stripped but its
  direction / default / assumption wrappers intact, or the `(sentexHandle H)` a
  bare-handle exceptWhen named.  `[nil sentence]` when there is no exceptWhen.

  This is the layer at which an exceptWhen becomes a separate meta-sentex: the assert
  layer stores `inner` as the rule (or resolves the handle) and the exception as
  `(exceptWhen <aligned-query> (sentexHandle H))` against it."
  [sentence]
  (let [[dir def? exc assum con inner] (sx/peel-rule-wrapper sentence)]
    (if (seq exc)
      [(vec exc) (if (sx/sentex-handle? inner) inner (rewrap inner dir def? assum con))]
      [nil sentence])))

(defn- deep-vars
  "Every variable anywhere in a form (descends into nested subterms, so a variable
  inside a compound argument or a stamped rule is covered)."
  [form]
  (filter sx/variable? (tree-seq sequential? seq form)))

;; ---- generators: a rule whose consequent is a rule -----------------------
;; `(implies <antes> (implies <inner-antes> <inner-conseq>))` — a **generator**, whose
;; firing stamps the inner rule out with its holes filled.  The scoping rule is
;; computed, not annotated: the inner rule's variables that its enclosing antecedents
;; also mention are **holes**, bound by the join and ground at mint; the rest are the
;; stamped rule's own, and belong to it.
;;
;; The nesting is not capped.  A stamped rule may itself be a generator, and then the
;; mint stamps in turn — each level's firing grounds that level's holes and stores the
;; level below it.  One reading decides every level, because the scoping rule composes:
;; a variable belongs to the **outermost** level whose antecedents mention it, which is
;; the level whose firing makes it ground.  See docs/generators.md.

(defn generated-rule
  "The bare rule form a generator's `consequent` stamps out — the `(implies …)` inside
  whatever `set/*Rule` wrapper the author put on it — or nil when the consequent
  concludes a fact, which is every ordinary rule.

  The wrapper is peeled here and *kept* by the caller that mints: it sets the
  **stamped** rule's direction, which is the only place a direction can be written for
  a rule nobody types out."
  [consequent]
  (let [inner (peek (sx/peel-rule-wrapper consequent))]
    (when (sx/implies? inner) inner)))

(defn generator?
  "Is this rule *sentence* a generator — does it conclude a rule?"
  [sentence]
  (some? (generated-rule (consequent (inner-rule sentence)))))

(defn generator-sentex?
  "Is this stored rule sentex a generator?  Read off the record's `:consequent`, which
  is where the canonicalized rule kept it."
  [sentex]
  (boolean (some-> (:consequent sentex) generated-rule)))

(defn holes
  "The variables a generator's stamped rule takes from the firing — those its
  enclosing `antecedents` also mention, as a set.

  Computed rather than declared, which is the whole reason a generator needs no
  vocabulary of its own: sharing a variable name with the antecedents *is* how an
  author says \"fill this in\", and the remaining variables are the stamped rule's own
  by the same token.  Two spellings cannot disagree, because there is only one.

  One level's question.  Under nesting each level asks it of the level below, and
  `nesting` carries the answers down as `:bound`."
  [antecedents generated]
  (let [ante-vars (into #{} (mapcat deep-vars antecedents))]
    (into #{} (filter ante-vars) (deep-vars generated))))

(defn nesting
  "A rule sentence peeled into its **levels**, outermost first — one map per `implies`:

      {:antecedents …  ; that level's antecedent patterns
       :consequent  …  ; what it concludes, wrapper and all
       :generated   …  ; the bare rule it stamps, nil at the innermost level
       :bound       …} ; the variables an *enclosing* level's antecedents bind

  An ordinary rule is one level with no `:generated`; a generator is two; a generator
  that stamps a generator is three, and so on with no cap.

  `:bound` is the whole of the scoping rule, accumulated on the way down: by the time a
  level's rule is stored, every enclosing level has fired and substituted its own holes,
  so those variables are **ground** there — which is what lets one stand in functor
  position, and what counts as bound when the innermost rule's range restriction is
  checked.  A variable an enclosing level does *not* bind belongs to the level it is
  written at or further in.

  One peel rather than a recursion per question: the holes, the variable functors and
  the range restriction are all read off these levels, so they cannot disagree about
  which level owns a variable.

  An ordinary rule stops after one level, so a rule that stamps nothing pays one peel
  and one map for being read this way."
  [sentence]
  (loop [r (inner-rule sentence) bound #{} acc []]
    (let [as    (antecedents r)
          c     (consequent r)
          g     (generated-rule c)
          level {:antecedents as :consequent c :generated g :bound bound}]
      (if g
        (recur g (into bound (mapcat deep-vars) as) (conj acc level))
        (conj acc level)))))

(defn innermost-rule
  "The rule at the bottom of a generator's nesting — the one whose consequent is a
  **conclusion** rather than another rule, and so the only level of a generator that
  ever concludes a fact.  `inner-rule` for a rule that stamps nothing."
  [sentence]
  (let [{:keys [antecedents consequent]} (peek (nesting sentence))]
    (rule-sentence antecedents consequent)))

(defn- ordinary-range-problems
  "`range-problems` for a rule that concludes a *fact* — every rule but a generator.
  `bound` is what counts as bound beside the antecedents' own variables: empty for a
  written rule, and a generator's holes for the rule it stamps out."
  [antecedents consequent bound]
  (let [exists?   (sx/head-exists? consequent)
        evars     (if exists? (sx/head-exists-vars consequent) #{})
        cbody     (if exists? (sx/head-exists-body consequent) consequent)
        cvars     (deep-vars cbody)
        ante-vars (into (set bound) (mapcat deep-vars) antecedents)]
    (cond-> []
      (and (sequential? cbody) (= 'and (first cbody))
           (empty? (rest cbody)))
      (conj "rule consequent is an empty conjunction")

      ;; `_` is an anonymous wildcard: two occurrences are two *different* variables
      ;; (canonicalization numbers each one separately), so it can never carry a
      ;; binding from an antecedent to the consequent — matching one against another
      ;; would store a non-ground junk fact.
      (some #(= '_ %) cvars)
      (conj "rule consequent uses the anonymous wildcard _, which binds nothing")

      :always
      (into (for [v (distinct cvars)
                  :when (and (not= '_ v) (not (ante-vars v)) (not (evars v)))]
              (str "rule is not range-restricted: consequent variable " v
                   " is unbound by the antecedents"))))))

(defn range-problems
  "Why `antecedents => consequent` is not range-restricted, as a seq of problem
  strings — empty when the rule is fine.  The value form, like the wff arms:
  a caller that refuses wraps it in a throw, and a fixpoint that must not abort
  can record it instead.

  A head existential `(exists ?y C)` exempts **only** its marked variable(s): the
  check runs over the inner `C`, and every consequent variable that is neither
  antecedent-bound nor existentially marked is still a problem — so an accidental
  typo is caught while a deliberate `∃` is allowed (docs/skolem.md).

  A **generator** is checked at its innermost level, and the two claims are about
  *different* rules.  Every generator level's own range restriction is vacuous — its
  consequent is a rule rather than a conclusion, and what it stamps has free variables on
  purpose — so what is checked is the **innermost** rule's, with every enclosing level's
  holes counted as bound because substitution makes them ground before anything is
  stored.  Checking it here rather than at firing is what makes the refusal reach the
  author: a generator that can only ever stamp junk is refused where it is written, not
  once per binding at the far end of a fixpoint.

  Each generator level owes one claim of its own: it must fill a hole **no enclosing
  level has already filled**.  A level whose every shared variable is already ground
  stamps the same rule at every firing, which is a rule its author could have written —
  and under nesting that is a mistake the outer fill *creates*, so saying it here is
  what keeps the refusal at the sentence instead of once per mint in the ledger."
  [antecedents consequent]
  (let [levels (nesting (rule-sentence antecedents consequent))
        inner  (peek levels)]
    (-> (into []
              (comp (map-indexed vector)
                    (keep (fn [[i {:keys [antecedents generated bound]}]]
                            (when (every? bound (holes antecedents generated))
                              (if (pos? i)
                                (str "rule generator at nesting level " (inc i)
                                     " shares no variable with the rule it generates"
                                     " that a level further out has not already filled,"
                                     " so every firing stamps the same rule: share a"
                                     " variable the levels above it do not")
                                (str "rule generator shares no variable with the rule it"
                                     " generates, so every firing stamps the same rule:"
                                     " share the variable that is meant to vary, or"
                                     " write the rule itself"))))))
              (butlast levels))
        (into (ordinary-range-problems (:antecedents inner) (:consequent inner)
                                       (:bound inner))))))

(defn check-range-restricted
  "Throw `:type :not-range-restricted` unless every consequent variable is bound by
  some antecedent (and the consequent is a well-formed conclusion).

  Uses `ex-info`, not `clojure.core/assert`: an elidable check under `*assert*` false
  would store the junk rule *silently* — the exact failure `check-ground` exists to
  prevent — and an `AssertionError` carries no `:type` for callers to discriminate
  on."
  [antecedents consequent]
  (when-let [problems (seq (range-problems antecedents consequent))]
    (throw (ex-info (first problems)
                    {:type        :not-range-restricted
                     :problems    (vec problems)
                     :antecedents (vec antecedents)
                     :consequent  consequent}))))

;; ---- what a disjunction may not do --------------------------------------
;; `or` earns its place by *disappearing* (`expand-antecedent`), so the refusals below
;; are the positions from which it cannot: a place where nothing would expand it, or a
;; width at which expanding it is the wrong storage.  Every one is a pure read of the
;; sentence, which is why they are reported at the shape entry point — before the KB is read
;; at all, by both storage entry points and by `core/check` alike.

(defn- some-disjunction
  "The first `or` anywhere in `form`, or nil."
  [form]
  (sx/some-form sx/disjunction? form))

(defn- malformed
  "The `:not-well-formed` problem an `or` in a position nothing expands carries.  The
  keyword is a literal at this one site rather than an argument: the refusal vocabulary
  is scanned from the sources (`type_contract_test`), and a `:type` behind a parameter is
  one that scan can name but not resolve."
  [sentence extra message]
  (merge {:type :not-well-formed :sentence sentence :message message} extra))

(defn- query-body-problem
  "The refusal an `or` inside a closed-query body carries.  `unknown`, `thereExists` and
  the aggregates are answered as **one** closed query each (docs/naf.md,
  docs/aggregate.md): the evaluator runs the body's conjuncts and reads whether they
  held, and nothing there unions two runs — so an `or` under one of them is a query the
  answer is not computed from, which is the one way a guard can silently pass
  everything.  Not expanded either, because the body is not the rule: splitting the rule
  on it would make `(unknown (or A B))` mean \"A is underivable **or** B is\", which is
  the De Morgan opposite of what it reads as."
  [sentence frame rewrite]
  (malformed
   sentence {:frame frame}
   (str "or cannot stand inside the body of " frame ": it is answered as one closed"
        " query and nothing there unions two runs, so the disjunction would decide the"
        " rule without being evaluated — " rewrite)))

(defn- antecedent-disjunction-problems
  "The refusals one antecedent literal's `or`s carry, walking the frames a disjunction
  may legally nest in — `and` and `or` themselves — and naming the ones it may not."
  [sentence lit]
  (cond
    (sx/disjunction? lit)
    (if (empty? (sx/disjuncts lit))
      [(malformed
        sentence {:literal lit}
        (str "or takes at least one alternative, and (or) offers none: a rule with an"
             " empty disjunct list expands to no rules at all, which is not the rule"
             " that was written.  Drop the antecedent, or name the alternatives"))]
      (vec (mapcat #(antecedent-disjunction-problems sentence %) (sx/disjuncts lit))))

    (conjunctive? lit)
    (vec (mapcat #(antecedent-disjunction-problems sentence %) (rest lit)))

    (sx/negation? lit)
    (if (some-disjunction (second lit))
      [(malformed
        sentence {:literal lit}
        (str "or cannot stand under not: (not (or A B)) is \"neither A nor B\", which is"
             " a conjunction of negations rather than a choice, and expanding the rule on"
             " it would store the opposite claim.  Write the two negations as separate"
             " antecedents"))]
      [])

    (sx/unknown? lit)
    (if (some-disjunction (second lit))
      [(query-body-problem sentence "unknown"
                           (str "(unknown (or A B)) is \"neither A nor B is derivable\","
                                " so write (unknown A) and (unknown B) as two"
                                " antecedents"))]
      [])

    (sx/there-exists? lit)
    (if (some-disjunction (nth lit 2))
      [(query-body-problem sentence "thereExists"
                           (str "there is no rewrite that keeps one witness: write one"
                                " rule per alternative, each with its own thereExists"))]
      [])

    (sx/aggregate? lit)
    (if (some-disjunction (sx/aggregate-body lit))
      [(query-body-problem sentence (name (first lit))
                           (str "a count over a union is not the sum of two counts —"
                                " a witness satisfying both alternatives would be"
                                " counted twice — so name the extent with a rule and"
                                " aggregate over that"))]
      [])

    :else []))

(defn- consequent-disjunction-problem
  "The refusal an `or` in a rule's conclusion carries.  A disjunctive *head* is not
  something forward chaining can place: it says one of two things holds without saying
  which, and belief is a label on a sentex rather than on a set of them.  What the
  engine does have is the choice itself — `set/assumptionRule` offers the head to a
  solve, and the solver picks a model (docs/solving.md).  So the head is written as one
  assumptionRule per alternative, with a constraint saying what may not be chosen
  together."
  [sentence conseq]
  (malformed
   sentence {:consequent conseq}
   (str "or cannot stand in a rule's conclusion: a disjunctive head asserts that one of"
        " the alternatives holds without saying which, and forward chaining places a"
        " sentex rather than a choice.  Offer the alternatives to a solve instead —"
        " one (set/assumptionRule (implies <body> <alternative>)) each, with a"
        " set/hardConstraint ruling out the combinations that cannot stand — and read"
        " the answer with solve (docs/solving.md)")))

(defn- exception-disjunction-problem
  "The refusal an `or` inside an `exceptWhen` query carries.  The exception is *already*
  disjunctive across assertions: each `exceptWhen` meta-sentex is an independent
  \"unless\" clause and a firing is blocked if **any** of them holds
  (`provers/rule-exceptions`), while the conjuncts within one all must hold.  So a
  disjunctive exception is two exceptions, and writing it that way keeps each one
  separately assertable, retractable and believable — which one `or` inside a single
  query would not be."
  [sentence q]
  (malformed
   sentence {:exception q}
   (str "or cannot stand inside an exceptWhen query: the conjuncts of one exception all"
        " have to hold.  Assert one exceptWhen per alternative against the same rule —"
        " (exceptWhen <alternative> (sentexHandle H)) — since a firing is blocked if any"
        " of a rule's exceptions holds, which is the disjunction, one clause at a time")))

(defn- width-problem
  "The refusal a rule too wide to expand carries, naming the count."
  [sentence n]
  {:type :disjunction-too-wide :sentence sentence
   :alternatives n :cap max-alternatives
   :message
   (str "a disjunctive antecedent is stored as one rule per alternative, and this one"
        " expands to " n ", over the cap of " max-alternatives ".  The width is paid in"
        " handles, index entries and TMS nodes rather than at query time, and nested"
        " disjuncts multiply.  Name the alternatives as a type instead — a genl edge per"
        " member and one rule on the supertype — or split the rule by hand")})

(defn- alternative-range-problems
  "Range restriction, asked **per alternative**, naming the disjuncts that alternative
  took.

  This is the check a disjunctive rule cannot inherit from the ordinary one, because the
  ordinary one reads the disjunction whole: `(implies (or (dog ?p) (cat ?q)) (fed ?p))`
  has `?p` somewhere in its antecedents, so the flat read passes — and then one of the
  two rules it expands to concludes about a variable nothing binds.  Refusing the
  **whole** rule rather than the bad half is what keeps the expansion invisible: a rule
  the author wrote is stored entirely or not at all, exactly as a conjunctive consequent
  is."
  [sentence level]
  (let [{:keys [antecedents consequent bound]} level]
    (vec (for [alt (antecedent-alternatives antecedents)
               p   (ordinary-range-problems (:antecedents alt) consequent bound)]
           {:type :not-range-restricted :sentence sentence
            :problems [p] :antecedents (:antecedents alt) :consequent consequent
            :disjuncts (:choices alt)
            :message
            (str p ", in the alternative that takes "
                 (str/join " and " (map pr-str (:choices alt)))
                 " — every alternative a disjunctive antecedent expands to is a rule in"
                 " its own right, and each has to bind the consequent on its own")}))))

(defn disjunction-problems
  "Why a sentence's `or`s cannot be polycanonicalized away, as problem maps — empty when
  they can, and empty in one read for the overwhelming majority of sentences, which
  carry no `or` at all.

  Four families, reported in that order so the sharpest complaint comes first: an `or`
  in a position nothing expands (a conclusion, a closed-query body, an exception, a
  standalone sentence), an empty `(or)`, a rule wider than `max-alternatives`, and an
  alternative the consequent is not range-restricted over.

  A **generator** is read level by level: every level's antecedents may disjoin, since
  the mint expands what it stores, and only the innermost level's consequent is a
  conclusion.  The innermost range check counts an enclosing level's variables as bound
  whether or not the alternative taken there binds them — the mint's own
  `checks/rule-violation` answers for the rule that is actually stamped."
  [sentence]
  (if-not (some-disjunction sentence)
    []
    (let [[_ _ exc _ _ inner] (sx/peel-rule-wrapper sentence)]
      (if-not (rule-sentence? inner)
        (if (sx/disjunction? inner)
          [(malformed
            sentence {}
            (str "a disjunction is not one assertable sentence: nothing decides which"
                 " alternative holds, and belief is a label on a sentex rather than on a"
                 " set of them.  As a rule antecedent an or expands to one rule per"
                 " alternative; as a conclusion, offer the alternatives to a solve with"
                 " set/assumptionRule (docs/solving.md)"))]
          [])
        (let [levels     (nesting inner)
              innermost  (peek levels)
              structural (-> (vec (for [level levels
                                        lit   (:antecedents level)
                                        p     (antecedent-disjunction-problems sentence lit)]
                                    p))
                             (into (when (some-disjunction (:consequent innermost))
                                     [(consequent-disjunction-problem
                                       sentence (:consequent innermost))]))
                             (into (for [q exc :when (some-disjunction q)]
                                     (exception-disjunction-problem sentence q))))]
          (if (seq structural)
            structural
            (let [wide (vec (for [level levels
                                  :let  [n (antecedent-alternative-count (:antecedents level))]
                                  :when (> n max-alternatives)]
                              (width-problem sentence n)))]
              (cond
                (seq wide) wide
                (some distributes-or? (:antecedents innermost))
                (alternative-range-problems sentence innermost)
                :else []))))))))

(defn check-disjunction!
  "Throw the first `disjunction-problems` refusal, or return nil.  The throwing form both
  storage entry points read: `core/check-sentence-shape!` runs it before anything is stored, and
  `checks/check-rule!` runs it again over what is about to be stored — which is where a
  rule the cap refused, and so never expanded, is caught on the mint path."
  [sentence]
  (when-let [p (first (disjunction-problems sentence))]
    (throw (ex-info (:message p) (dissoc p :message)))))

;; ---- the functor a rule is indexed by ------------------------------------

(defn variable-functor-literals
  "The `[role literal]` pairs of a rule whose functor is a **variable** — `(?p ?x ?y)`,
  or the dotted rest `(?pred . ?args)`.  Read through `naming/applied-literals` one
  level at a time, so the frames descended into are the ones the naming check descends:
  a negated antecedent, a head existential, an aggregate's body.

  Inside a generator's stamped rule the question is asked of **non-holes only**, and
  that is the carve the whole feature rests on.  The index's claim is on what gets
  stored as a rule; a stamped rule is a pattern, and what gets stored is the mint —
  checked in its own right, by this function, when it is minted.  A variable an
  **enclosing** level binds is therefore fine in functor position, because that level's
  firing makes it concrete before anything is keyed on it, and that is what lets one
  generator range over a family of predicates while every rule the index ever sees has a
  concrete functor.

  **Enclosing, not same-level**, and the distinction is the whole of what nesting buys.
  `(implies (and (?tpred ?type ?cap) (?type ?instance)) …)` stamped by a generator that
  binds `?tpred` fills the first functor and not the second: `?type` is bound by a
  literal of the rule *being stored*, so the mint is a rule the index cannot key, and
  refusing it is refusing exactly what would otherwise be stored inert.  Written a level
  further in — `(implies (?tpred ?type ?cap) (implies (?type ?instance) …))` — `?type` is
  a hole of the middle level, ground before its rule is stored, and both functors are
  concrete by the time anything is indexed.

  A stamped variable functor no enclosing level binds is refused as loudly as any other,
  and it has to be: nothing will ever bind it, so every mint it produces is the
  accepted-and-inert rule this check exists to keep out — and refusing it here names
  the generator, where refusing it at the mint would name a rule the author never
  wrote."
  [sentence]
  (letfn [(level-literals [i {:keys [antecedents consequent generated]}]
            ;; only the innermost level's consequent is a conclusion; every other one is
            ;; the level below, read there as that level's own literals
            (let [arole (if (pos? i) :generated-antecedent :antecedent)
                  crole (if (pos? i) :generated-consequent :consequent)]
              (cond-> (into [] (mapcat #(nm/applied-literals arole %)) antecedents)
                (nil? generated) (into (nm/applied-literals crole consequent)))))
          (level-problems [i level]
            (filter (fn [[_ lit]]
                      (let [f (nm/functor lit)]
                        (and (sx/variable? f) (not ((:bound level) f)))))
                    (level-literals i level)))]
    (vec (mapcat level-problems (range) (nesting sentence)))))

(defn check-indexable-functors
  "Throw `:type :not-indexable` when an **antecedent** literal of the rule `sentence`
  puts a variable in functor position.  A variable functor in the **consequent** is
  allowed and indexed (see `consequent-index-pred`), so this refuses only the half the
  engine cannot key.

  **The split, and why it falls where it does.**  The rule index is keyed by predicate,
  and a variable names none.  For a *consequent* that adds no work the range check does
  not already buy: every consequent variable is antecedent-bound
  (`check-range-restricted`), so a rule concluding `(?p ?y ?x)` fires forward through its
  *concrete* antecedent with `?p` already ground, and the `var-consequent-key` catch-all
  cell makes it reachable by a backward goal.  For an *antecedent* it is the widest
  trigger the engine can have: `(?p ?x ?y)` names no predicate to key on, so
  `chain/fire-rules-for` cannot find the rule from an arriving fact, and it would fire
  only when a concrete-predicate antecedent beside it arrives — `(transitive foo)` before
  the facts derives nothing, and after them joins over whatever happens to be stored at
  that instant.  Two arrival orders, two answers, from a rule the engine reported as
  accepted.  That half stays refused.

  The workaround the message names is the instantiated rule: one rule per predicate the
  metarule was meant to range over, each with a functor the index can read — written by
  hand, or by the **generator** that stamps them, which is what a variable antecedent
  functor usually wants to be (docs/generators.md).  So the message names the level to
  move it to when the rule is one a generator stamps: a functor a level *further out*
  binds is ground before its rule is stored, and only the ones nothing binds are left.

  An `:inert` rule is exempt at the caller (`checks/check-rule!`): it runs in neither
  engine by construction, so it claims nothing the index has to honour."
  [sentence]
  (when-let [bad (seq (filter (comp #{:antecedent :generated-antecedent} first)
                              (variable-functor-literals sentence)))]
    (let [[role lit] (first bad)
          stamped?   (= :generated-antecedent role)]
      (throw (ex-info (str "a rule's antecedent predicate cannot be a variable: "
                           (pr-str lit)
                           (when stamped? " in the generated rule's antecedent")
                           " — the rule index is keyed by predicate, so a variable"
                           " functor there names none for an arriving fact to trigger,"
                           " and the rule would fire over whatever is stored when a"
                           " concrete antecedent beside it arrives.  "
                           (if stamped?
                             (str "Nothing an enclosing generator binds fills it: move"
                                  " the literal that binds it out one level, so the"
                                  " functor is ground before the rule is stamped.")
                             (str "Assert the instantiated rules, one per predicate it"
                                  " ranges over, or stamp them from a generator whose"
                                  " antecedent binds the predicate.")))
                      {:type :not-indexable :role role :literal lit
                       :literals (mapv second bad) :sentence sentence})))))

(defn consequent-index-pred
  "The key the consequent slot of `p/index-rule` files `rule-sentex` under: its
  `consequent-predicate`, or `p/var-consequent-key` when that predicate is a variable —
  a rule with concrete antecedents concluding `(?p …)`, which `check-indexable-functors`
  allows.  Such a rule is filed under the one shared catch-all bucket rather than the
  canonical `?var0` no goal can spell, and `resolution/concluding-rule-handles` unions
  that bucket into every concrete-goal answer so a backward goal can reach it.

  **An `:inert` rule is the exception**: it chains in neither engine, so it concludes nothing and must not surface as a concluder for
  every goal.  It keeps the canonical variable — a dead key nothing reads — and only a
  rule that can actually conclude reaches `:var-pred`.

  One spelling for all three writers — `special/index-rule-sentex`, its unindex twin, and
  `reindex/index-rule-entry` — so a rebuilt index files the key a live one does."
  [rule-sentex]
  (let [c (consequent-key (:consequent rule-sentex))]
    (if (and (sx/variable? c) (not= :inert (:direction rule-sentex)))
      p/var-consequent-key
      c)))

(defn direct-concluders
  "Rule handles whose consequent predicate is exactly `pred`, unioned with the
  variable-consequent catch-all (`p/var-consequent-key`): a rule concluding `(?p …)` could
  conclude `pred` once `?p` binds, so any reader answering \"which stored rules conclude
  `pred`\" must include it or it disagrees with the backward chainer.  This is the
  **stored-graph** read — no spec fan, unlike `resolution/concluding-rule-handles` — shared
  by the stratification-cycle check and the blocked-firing explanation."
  [index pred]
  (into (set (reads/as-stored-rules-by-consequent index p/var-consequent-key))
        (reads/as-stored-rules-by-consequent index pred)))
