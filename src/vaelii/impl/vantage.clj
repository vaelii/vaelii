;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.vantage
  "`CxInference` — which readers can answer a goal, and the two ways of working that out.

  A **variable** context reads \"in some context\", and it reads it **joint**, exactly as
  `CxInference` does: an answer survives only if some one reader's `genlCx` ancestor set covers
  the whole derivation, so two facts no single context sees are never joined
  (docs/contexts.md).  The reader that covered it is the answer's **witness** — handed
  back as `?ctx` for `CxInference`, unified into the variable for a variable context.

  Two implementations, because they are worth comparing and must not disagree:

  - **`:fan`** (the reference) enumerates the readers and asks each one the ordinary
    scoped question.  Sound by construction — every answer is one a real vantage really
    gives — and it inherits `except`, retired-spelling and closure scoping for free,
    since each reader runs the same path a named context runs.
  - **`:post-hoc`** asks once, unscoped, carrying what each answer *rested on*, and places
    the result with `tax/maximal-common-descendant-contexts` — the backward twin of what a
    forward firing does (`vaelii.impl.chain`).  One pass instead of |readers|.

  Post-hoc is the one that can be wrong, because an unscoped pass sees a KB with three
  filters off and has to put them back by reasoning about the *placement* instead of the
  read.  Remove any of the three below and `vantage_differential_test` goes red:

  - **the subsumption edges.**  Retrieval is type-aware, so a matched fact is not the only
    ingredient of its own match — a reader that sees the fact but not the `genl` edge it
    was matched over does not have the answer (`subsumption-support`).
  - **the exceptions.**  `matches-visible` at `'?ctx` runs where the hidden set is empty by
    construction, so an answer can be placed in the very context that `except`s one of its
    facts (`placements`).
  - **the retired spellings.**  Supersession is per reader, so a placement below an equality
    merge sees both a fact and its twin and retires one spelling an unscoped pass keeps
    (`retires-an-ingredient?`).

  And what it cannot do is **declared rather than guessed**: a computed answer — a closure
  walk, an evaluable, an inferred argument type — names no context to place by, so
  `placeable?` asks the registry whether the stored-fact prover is the only one that
  applies, and `answers` hands anything else back to the fan and says so.  A narrowing that
  does not announce itself is indistinguishable from a covered case.

  The two must return the same answers, witnesses included.  `query_context_test` pins the
  cases one at a time; `vantage_differential_test` compares them over generated lattices,
  and each of the five things above turns it red when removed."
  (:require [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(def witness-key
  "Where a `CxInference` answer reports the reader that witnessed it: the keyword
  `:context`, **beside** the bindings rather than among them.

  A binding is what a *variable* the caller wrote gets bound to, and `CxInference` is a
  constant — the caller named no variable, so there is nothing to bind and inventing one
  would be this namespace answering a question nobody asked.  Assoc'ing `?ctx` instead
  is indistinguishable from a binding and is not one: no `?ctx` appears in the call.  A keyword cannot
  collide with a binding either, since those are keyed by the `?`-symbols the goal
  spells.

  Pass a **variable** context instead and the witness really is a binding — it unifies into
  that variable, under whatever name the caller chose."
  :context)

(def ^:dynamic *strategy*
  "Which implementation answers a `CxInference` read: `:fan` (the reference) or
  `:post-hoc`.

  A pure cost decision that **must not change the answer set**, in the shape
  `res/*hierarchical-retrieval*` already establishes for retrieval — so it is a var to
  rebind in a benchmark or a differential test, not an option on the read entry points.  Outside
  post-hoc's declared domain the fan answers whatever this says.

  **`:post-hoc` by default, because it is bounded rather than because it is faster.**  On
  its own it is the riskier of the two: it wins by many multiples where the join stays
  inside contexts that see each other, and loses by several where it does not.  `bail`
  removes the tail — a run that outgrows its budget is abandoned and the fan answers — so
  what is left is a strategy that wins 1.5x to 17x in its regime and costs at most about
  1.5x outside it, the extra being the bounded probe.  On a store large enough that every
  join outgrows the budget, this *is* the fan, reached after a probe of `lattice contexts
  × 20` rows."
  :post-hoc)

;; ---- the readers --------------------------------------------------------

(defn- candidate-contexts
  "The contexts holding a fact any literal of `goals` could match, unscoped.

  The seed the lattice cannot supply: a context wired by **no** `genlCx` edge is not a node
  of the closure, so `tax/contexts` does not list it, while a fact asserted into it is
  perfectly real and that context is its own (only) reader.

  **This is O(the match set), and that is a known cost.** About a microsecond per match, so
  a broad literal over a very large store spends real time here before answering anything,
  on every read that does not name a context. Dropping it and letting the lattice define
  the vantages is O(1) and *wrong*: the suite asserts into unwired contexts in a dozen
  namespaces and expects an unscoped read to find those facts, which is the honest signal
  that an island is a place people put knowledge. The cheap version of this wants a census
  of fact-holding contexts maintained where sentexes are written; the index keeps a
  per-context root already and exposes no way to enumerate it."
  [kb goals]
  (into #{}
        (comp (mapcat (fn [g] (res/matches-visible kb g '?ctx)))
              (map first)
              (keep (fn [h] (:context (p/get-sentex (:records kb) h)))))
        goals))

(defn readers
  "Every context that could be the vantage a `CxInference` answer is witnessed by: the
  `genlCx` lattice, plus any context outside it holding a fact the goal could match.

  The closure runs only when the seed adds something. `meet-closure` is O(pairs), each pair
  a `maximal-common-descendant-contexts`, and over the lattice's own nodes it cannot add a
  member: a common descendant is drawn from the `context-down` closures, so it is a node
  already. Running it anyway cost more than a whole post-hoc read on a 24-context KB, to
  return the set it was handed."
  [kb goals]
  (let [t     (reasoning/taxonomy kb)
        nodes (set (tax/contexts t))
        extra (into #{} (remove nodes) (candidate-contexts kb goals))]
    (if (empty? extra)
      nodes
      (tax/meet-closure t (into nodes extra)))))

;; ---- (a) the fan --------------------------------------------------------

(defn- attach-witness
  "How an answer reports the reader that witnessed it, as `bindings -> context -> answer`
  (or nil to drop the answer).

  Two callers wrote the context two ways and mean two different things by it:

  - a **variable** — `?ctx`, `?home`, whatever the caller spelled — names somewhere to put
    the answer, so the witness *unifies* into it.  Already bound to a different context by
    the goal itself, the answer is dropped rather than overwritten: that is what unifying
    means, and overwriting is what has the plain wildcard join report a context chosen by
    whichever literal the plan happened to order last.
  - **`CxInference`**, a constant, names no variable at all, so there is nothing to bind
    and the witness goes beside the bindings under `witness-key`.

  A `:proof?` answer is not a binding map but `{:bindings … :proof …}`, and the distinction
  above decides where the witness lands in it: a **binding** goes inside `:bindings`, where
  a caller reading that key will find it, and `witness-key` stays beside them — it is a
  side channel by construction, and a third top-level key is what it is for.  Assoc'ed at
  the top either way, a variable witness is invisible to `(:bindings answer)` and its unify
  check reads a key that is never there, so an already-bound `?ctx` would go unhonoured
  under `:proof?` alone."
  [witness]
  (if (sx/variable? witness)
    (fn [b w]
      (let [inner (get b :bindings b)]
        (when (= w (get inner witness w))
          (if (identical? inner b)
            (assoc b witness w)
            (assoc b :bindings (assoc inner witness w))))))
    (fn [b w] (assoc b witness-key w))))

(defn- witnessed
  "`binding -> #{contexts that answered it}`, collapsed to one row per binding per
  **maximal** witness.

  The readers below one that answered add no claim: a more specific context sees a superset
  of the same knowledge, so it answers whatever its ancestor did and for the same reasons.
  Reporting every one of them would make the answer count a fact about how finely the KB
  happens to be divided rather than about the question, so the witness is the most general
  reader — `tax/maximal-contexts`, the same notion of *most general* a forward firing places
  its conclusion by.

  **Shared by both strategies, and that is the point.** Maximality is a property of a
  *binding* — of every context that answers it, however many derivations got there — not of
  one derivation. Maximize per derivation instead and post-hoc reports one binding twice,
  at a reader and at a reader below it, wherever an equality merge migrated a twin into
  both. Computing the witness in one place is what stops the two strategies from disagreeing
  about a rule neither of them is really free to choose.

  **This is where a read stops being lazy**, and it cannot be otherwise: which witness is
  maximal is not knowable until every reader has been asked.

  Grouped by the whole answer, which under `:proof?` means **per derivation** rather than
  per binding: two proofs of one binding keep a witness each.  That is the reading `:proof?`
  asks for — a proof is a claim about one derivation, and the context that witnessed *it* is
  the honest answer — but it is a different grouping from the bare-bindings case above, and
  worth knowing before comparing the two."
  [kb witness by-binding]
  (let [t      (reasoning/taxonomy kb)
        attach (attach-witness witness)]
    (vec (mapcat (fn [[b ws]]
                   (keep (fn [w] (attach b w)) (sort (tax/maximal-contexts t ws))))
                 by-binding))))

(defn fan
  "Ask every reader the ordinary scoped question, and keep what a reader really answered.

  `run-at` is the read itself, as a function of the context to run it in — the function that
  keeps this namespace out of `vaelii.core`'s way, and that lets one implementation serve
  `query`, `prove`, `ask` and `sentexes-matching` alike."
  [kb goals witness run-at]
  (let [rs (readers kb goals)]
    (if (empty? rs)
      ;; **No vantage exists, so there is none to require.**  The reader set is empty only
      ;; when the KB has no contexts *and* no stored fact the goal could match — a context
      ;; holding one is its own reader, and the seed finds it.  What is left is an answer
      ;; that rests on nothing at all: an evaluable, `different`, arithmetic.  Such an
      ;; answer is unconditional, true from every vantage including the ones this KB has yet
      ;; to acquire, so requiring a reader for it would drop it for want of a witness rather
      ;; than for want of support.  Answered unscoped and with no witness, there being no
      ;; context to name.
      (vec (run-at '?ctx))
      (witnessed kb witness
                 (reduce (fn [acc reader]
                           (reduce (fn [m b] (update m b (fnil conj #{}) reader))
                                   acc (run-at reader)))
                         {} rs)))))

(defn fan-distinct
  "The fan for a read that answers with **records** rather than bindings —
  `sentexes-matching`, whose maps already carry the `:context` a binding needs a witness
  for.

  So there is no witness to attach and nothing to place: a single sentence has no
  derivation to hold together, and the joint reading only bites where a join does.  What
  the fan still contributes is the per-reader filtering a wildcard skips — a sentex
  `except`ed from every context that can see it is hidden here and visible at `'?ctx`,
  which is the difference between asking the KB and asking a vantage."
  [kb goals run-at]
  (let [rs (readers kb goals)]
    (if (empty? rs)
      ;; the lattice is empty, so there is no vantage to require — see `fan`
      (vec (distinct (run-at '?ctx)))
      ;; **Lazy over the readers**, since `sentexes-matching` promises a seq that fetches
      ;; what it is asked for.  There is no witness to maximize here, so unlike `fan` there
      ;; is nothing that has to see every reader before it can answer at all: `distinct` is
      ;; a stateful transducer and `sequence` drives it one reader at a time, so a `take` of
      ;; five stops at the reader that supplied the fifth.  The `readers` seed is still paid
      ;; up front — which contexts can answer is not knowable lazily — so the first element
      ;; costs a scan of the goal's match set and the rest cost what they return.
      (sequence (comp (mapcat run-at) (distinct)) rs))))

;; ---- (b) post-hoc placement ---------------------------------------------

(def ^:dynamic *rows-per-reader*
  "How many join rows post-hoc may build per reader before it gives up and lets the fan
  answer.

  The two strategies do not dominate each other and **which wins is a fact about the data,
  not about the lattice**, so there is nothing cheap to predict from.  Post-hoc reads once
  and places afterwards, which is far cheaper when the join stays inside contexts that see
  each other.  When it does not — a wide flat lattice whose siblings hold facts about the
  same individuals, which is an ordinary way to model per-source or per-period knowledge —
  every cross-sibling pair matches on the join key and dies at placement, so post-hoc does
  O(readers²) work for O(readers) answers while the fan does O(readers).  Fitting a
  predictor to the lattice's shape got it right five times in fourteen.

  **What the measurements do say is that post-hoc's edge is on *small* joins.**  It loses
  on large ones two different ways — a wide flat lattice discards most of what it builds,
  and a deep one discards nothing but still loses, because a quadratic join costs less
  partitioned across readers than done whole.  Only the first is visible as waste, so the
  meter counts rows built rather than rows discarded: size is the signal both failures
  share.

  So it is measured rather than predicted: the join counts what it builds, and a run that
  passes `lattice contexts × this` has demonstrated the blowup and is abandoned.  Wasted
  work is bounded by the budget, the fan then answers, and **no answer can change** — this
  is a cost decision in the shape `res/*hierarchical-retrieval*` already establishes.  20
  puts the bail well above what an ordinary join builds and well below the quadratic case.

  The **lattice** rather than `readers`, because `readers` costs O(the goal's match set),
  and paying that to pick a row count would put the scan back on the one path that never
  needs it.  A KB whose contexts are all islands has no lattice nodes at all, hence the
  floor of one: the budget is a row count for a cost decision, not a claim about the
  reader set."
  20)

(def ^:private abandoned
  "What the join hands back when it passes its budget.  A sentinel rather than an exception:
  the caller is one `identical?` away and an exception would be control flow wearing a
  costume."
  ::abandoned)

(defn- fact-only?
  "Is this one literal answered by the stored-fact prover and nothing else?

  Asked of a literal rather than of the goal, because **the answer changes under
  substitution**: `applicable?` gates on groundness for most provers — `ArgTypeProver` on
  whether the argument is an individual, the meta-constraint and quantity provers on the
  same kind of test — so `(zt_t ?a)` is fact-only as written and `(zt_t ZX)` is not, once a
  join has bound `?a`.  A gate asked once of the goal as written therefore admits a
  conjunction whose second literal reaches a prover post-hoc never consults, and post-hoc
  answers with less than the fan.  So the join re-asks it of what it actually matches."
  [kb reg g]
  (and (sequential? g)
       (not (sx/deferred-literal? g))
       (let [ps (provers/applicable-provers kb reg g '?ctx)]
         (and (seq ps) (every? provers/fact-prover? ps)))))

(defn placeable?
  "Is `goals` inside post-hoc's domain — is every literal one that **only the stored-fact
  prover** answers?

  Post-hoc places an answer by the contexts of what it rested on, so it can only answer
  where everything it rests on *has* a context.  A stored match does: it names a sentex,
  and the `genl` edges it subsumed through name supporters.  A computed answer does not — a
  closure walk two hops long, an evaluable, an inferred argument type — and there is no
  honest context to place it by.  Guessing one would place an answer where the edges it
  rests on are not visible, which is the failure this whole namespace exists to avoid.

  Asked of the **registry** rather than of the literal's shape, because the shape does not
  say: `(gp0 ?a ?b)` and `(genl aa_t ?x)` are the same shape and only the second walks a
  closure.  `provers/applicable-provers` is what the dispatch itself asks, so the domain
  cannot drift from what actually runs.  A `deferred` literal is excluded by the same test
  — its prover is not the fact prover — and cheaply, since `applicable?` is designed to be
  the cheap question.

  This is the gate at the **entry point**, and it is not the whole of it: `applicable?` gates on
  groundness, so a literal can leave the domain once a join binds it.  `fact-only?` is
  re-asked of each substituted literal for that reason, and the join abandons where the
  answer changes."
  [kb goals]
  (let [reg (provers/registry kb)]
    (every? #(fact-only? kb reg %) goals)))

(defn- subsumption-support
  "The `[handle ctx]` supporters of the `genl` path that lets a fact spelled
  `stored-functor` answer a literal asking `goal-functor` — empty when the two are the same
  functor, which is nearly every match.

  **A matched fact is not the only ingredient of its own match.** Retrieval is type-aware:
  `(hound_t ?x)` is answered by a stored `(pup_t Rex)` over `(genl pup_t hound_t)`, and a
  reader that sees the fact but not that edge does not have the answer. Recording the
  fact's context alone would place the answer wherever the fact is visible, which is how
  post-hoc reports an answer from `CxA` that no reader of the KB actually has.

  This is `chain/subsumption-support` asked backwards, and deliberately the same call:
  a forward firing feeds these supporters' contexts to the placement beside the rule's and
  the facts', and a backward one has to reach the same verdict or the two chainers
  disagree about one KB. The vantage is **nil** — global — for the reason it is there: the
  edges are an *ingredient* of the answer, so their contexts are an input to deciding where
  it can be read rather than a test on a decision already made."
  [tax goal-functor stored-functor]
  (when (and (symbol? goal-functor) (symbol? stored-functor)
             (not= goal-functor stored-functor)
             ;; the global closure is the gate, exactly as it is forward: a functor pair
             ;; the closure does not relate was matched by something else (a variable
             ;; functor, say) and has no path to witness
             (contains? (tax/genls-global tax stored-functor) goal-functor))
    (tax/reach-support tax :genl stored-functor goal-functor nil)))

(defn- join-carrying-contexts
  "The conjunctive join, carrying the context of every ingredient it used.

  The same left-to-right reduce `inference/solve-inline` runs — each literal substituted
  with the bindings taken so far, matched, and merged — with one addition: what the match
  **rested on** joins an accumulating set, so what arrives at the end is `[bindings
  contexts]` rather than bindings alone. Two things go in: the matched sentex's own
  context, and the contexts of the `genl` edges the match subsumed through. Matching runs
  at `'?ctx`, which is what makes this one pass instead of |readers|, and what makes the
  placement afterwards required rather than a formality."
  [kb goals budget]
  (let [tax   (reasoning/taxonomy kb)
        reg   (provers/registry kb)
        built (volatile! 0)
        ;; **The first literal is not metered.**  The budget guards the *multiplication* —
        ;; a partial solution carried into the next literal and matched against everything
        ;; there — and the first stage does no multiplying: its rows are the answer set's
        ;; own floor, every one of them productive.  Metered, a single-literal read of
        ;; eight thousand facts abandoned a pass it was winning and fanned over eighteen
        ;; readers instead, which is the one shape post-hoc cannot lose.
        stage (volatile! 0)]
    (reduce
     (fn [sols literal]
       (vswap! stage inc)
       (let [metered? (> @stage 1)
             out
             (reduce
              (fn [acc [b hs ctxs]]
                (let [g  (res/substitute literal b)
                      gf (nm/functor g)]
                  ;; **The domain gate, re-asked of the substituted literal.**  `placeable?`
                  ;; saw this literal with its variables in, and binding them can bring a
                  ;; prover into scope that a pass of `matches-visible` alone never consults
                  ;; — a missing answer being as wrong as a wrong one.  Stage one needs no
                  ;; re-ask: nothing is bound yet, so the literal is what the gate passed.
                  (if (and metered? (not (fact-only? kb reg g)))
                    (reduced abandoned)
                    (reduce
                     (fn [acc m]
                       (if (and metered? (> @built budget))
                         ;; **Abandoned mid-stage, and that is the point.**  Checking between
                         ;; literals bounds the placement pass and not the row building, which is
                         ;; the cost — the blowup is in the rows.  Doubly `reduced` so the inner
                         ;; reduce stops and hands the outer one a `Reduced` to stop on too.
                         (reduced (reduced abandoned))
                         (let [h (nth m 0)]
                           (when metered? (vswap! built inc))
                           (if-let [sx (p/get-sentex (:records kb) h)]
                             (let [sup   (subsumption-support tax gf (nm/functor (:sentence sx)))
                                   ctxs' (into (conj ctxs (:context sx)) (keep second) sup)]
                               ;; **Prune here, not at the end.**  A partial solution whose
                               ;; ingredients already have no common descendant can never acquire
                               ;; one — a later literal only adds contexts, and a common descendant
                               ;; must see them all — so carrying it forward multiplies a row that
                               ;; is already dead against every match of every remaining literal.
                               (if (or (= ctxs' ctxs) (tax/common-descendant? tax ctxs'))
                                 (conj acc [(merge b (nth m 1))
                                            (into (conj hs h) (map first) sup)
                                            ctxs'])
                                 acc))
                             acc))))
                     acc
                     (res/matches-visible kb g '?ctx)))))
              []
              sols)]
         ;; **Three reduces, so the sentinel needs three hops.**  Goals, then the partial
         ;; solutions, then that literal's matches: a doubly-`reduced` value stops the inner
         ;; two and arrives here as the bare sentinel, which the goals-reduce would carry on
         ;; and hand back as `sols` — reducing over a keyword.  Stopping here is the third.
         (if (identical? abandoned out) (reduced abandoned) out)))
     [[res/no-bindings #{} #{}]]
     goals)))

(defn- retires-an-ingredient?
  "Would the reader `w` have **retired** the spelling one of `supporters` is stored under?

  The third thing an unscoped pass cannot see for itself, after the subsumption edges and
  the exceptions. Supersession is per *reader*, not per datum: a fact stated above an
  equality merge is believed where it lives — its own context was told nothing — while a
  context below the merge sees both it and the twin migration placed there, and reports one
  fact twice under two names it knows denote one thing. `matches-visible` at `'?ctx` filters
  none of that, so post-hoc has to ask it of the placement instead of the read.

  Gated on the KB having merged anything at all, exactly as `res/without-retired` gates
  itself: every KB until somebody states an equality pays one deref for the whole query."
  [kb merged? supporters w]
  (let [visible (delay (res/visible-supporter-fn kb w))
        recs    (:records kb)]
    (some (fn [h]
            (when-let [sx (p/get-sentex recs h)]
              (res/retired-for? kb visible merged? (sx/sentence-of sx))))
          supporters)))

(defn- placements
  "Where an answer resting on `supporters` (in `ctxs`) could be read from.

  The plain case is the placement rule itself: the maximal contexts that see every
  ingredient. The other case is what an unscoped pass cannot see for itself — a **visibility
  exception**. `matches-visible` at `'?ctx` runs where the hidden set is empty by
  construction, so post-hoc matches a sentex that is `except`ed from the very context it is
  about to place the answer in, and reports an answer no reader has.

  So a targeted supporter forces the same descent `chain/exception-aware-placements` makes
  forward: enumerate the contexts that structurally see every ingredient, keep the ones that
  see every *exact* supporter, and maximize those. `excepted-anywhere?` is the coarse gate,
  so an ordinary answer — which is nearly every answer — takes no ancestor set walk at all and
  reaches the one-line path above."
  [kb supporters ctxs]
  (let [tax     (reasoning/taxonomy kb)
        merged? (tax/merged-term-pred tax)
        base    (if (some #(res/excepted-anywhere? kb %) supporters)
                  (tax/maximal-contexts
                   tax (filterv (fn [c] (every? #(res/supporter-visible? kb % c) supporters))
                                (tax/common-descendants tax ctxs)))
                  (tax/maximal-common-descendant-contexts tax ctxs))]
    (cond->> base
      merged? (remove #(retires-an-ingredient? kb merged? supporters %)))))

(defn post-hoc
  "Answer unscoped, then keep only what some reader could have seen whole.

  The placement is `tax/maximal-common-descendant-contexts` of the contexts the answer's
  own facts came from — empty when they have no common view, which is exactly the case
  the unscoped default answers and should not.

  **Bindings are projected onto the goal's own variables first**, and that is not cosmetic.
  Matching runs at `'?ctx`, and `match-one` unifies the *context slot* too, so every raw
  binding carries a `?ctx` naming the context its match came from. Left in, two derivations
  of one binding — a fact and the twin an equality merge migrated below it — are two
  different keys, they never group, and each keeps a witness the other would have collapsed.
  `query` projects for its own reasons and the fan inherits it; post-hoc has to do it
  deliberately."
  [kb goals witness budget prepared-at]
  (let [vars (or (sx/symbols-where sx/variable? goals) #{})
        ;; memoized: the candidates repeat across rows, and preparing a goal is not free
        ;; **A goal some merge rewrote is not post-hoc's to answer.**  Preparation is per
        ;; reader: a context above a `sameAs` never rewrites the caller's spelling, so it
        ;; asks a *different question* and gets different answers — `(gp1 GI1 ?y)` binding
        ;; `?y` to `GI1` where the global partition's `(gp1 GI0 ?y)` binds it to `GI0`.  One
        ;; unscoped pass asks one question, so it cannot produce the other reader's answers
        ;; at all, and no amount of placement repairs a row that was never built.  The fan
        ;; re-prepares per reader and is right by construction.
        ;;
        ;; `CxNothing` is the probe: it sees no equality, so preparing there yields the
        ;; question as written, and a global preparation that differs means some merge
        ;; touched it.  One extra preparation per query, on merged KBs only.
        rewritten? (and prepared-at (not= goals (prepared-at 'CxNothing)))
        rows (if rewritten? abandoned (join-carrying-contexts kb goals budget))]
    (if (identical? abandoned rows)
      abandoned
      (witnessed kb witness (reduce (fn [acc [b hs ctxs]]
                                      (let [b (select-keys b vars)]
                                        (reduce (fn [m w] (update m b (fnil conj #{}) w))
                                                acc (placements kb hs ctxs))))
                                    {} rows)))))

;; ---- the entry point -----------------------------------------------------------

(defn- nothing-to-witness?
  "Is every literal of `goals` **computed** rather than matched — `different`, `evaluate`,
  `unknown` — so that no literal names a context and there is no witness to pick?

  This is where the joint reading has to stop, and `unknown` is why.  Fanning over readers
  is **existential** over them, and negation as failure is not monotone: a fact stored,
  believed and plainly visible is nonetheless *unknown* to any context that cannot see it,
  and on a KB with more than one context there is nearly always such a context.  So
  `(unknown X)` fanned would be satisfied by the most ignorant reader in the KB and answer
  true of everything — the reading inverted, not narrowed.

  A **mixed** goal is fine and needs no rule: the monotone literals constrain which readers
  can answer at all, and the `unknown` is then evaluated at those readers and nowhere else,
  so `[(p ?x) (unknown (q ?x))]` reads “a reader that sees p and does not know q” — which
  is what it should.  The pathology is only a goal with *no* monotone literal to pick a
  witness with, and such a goal is asked of the KB rather than from a vantage.  Answered
  unscoped, with no witness, there being nothing that could bear one.

  `evaluate` and `different` are here for the same structural reason rather than the
  epistemic one: they are computed, so they name no context, so they cannot witness."
  [goals]
  (every? #(and (sequential? %) (sx/deferred-literal? %)) goals))

(defn answers
  "`goals` answered as `CxInference` reads them: one binding map per answer per maximal
  witness, the witness bound to `?ctx`.

  `run-at` answers the goal from one named context, and is what the fan calls per reader.
  `:expands-rules?` says a rule may be expanded under this read, which puts it outside
  post-hoc's domain whatever the literals look like — an antecedent fact is not one of
  `goals`, so its context never reaches the placement.

  Returns `{:answers [...] :strategy :fan|:post-hoc}`; the strategy is reported rather
  than assumed because it may not be the one `*strategy*` asked for."
  [kb goals run-at {:keys [expands-rules? witness prepared-at]}]
  (let [witness (or witness 'CxInference)]
    (cond
      (nothing-to-witness? goals)
      {:answers (vec (run-at '?ctx)) :strategy :unscoped}

      (and (= :post-hoc *strategy*) (not expands-rules?) (placeable? kb goals))
      ;; post-hoc first, and the fan if it proves to be in the blowup regime.  A cost
      ;; decision only: the fan answers whatever post-hoc abandoned, and the two agree by
      ;; construction and by `vantage_differential_test`.
      ;; The budget is sized off the **lattice** rather than `readers`, and that is not an
      ;; approximation worth apologising for: it is a row count for a cost decision, and
      ;; `readers` costs O(the goal's match set) because it also hunts for contexts outside
      ;; the lattice.  Paying that to pick a number would put the scan back on the default
      ;; path — the one case that never needs it, since post-hoc places from the ingredients
      ;; it matched and enumerates no readers at all.  A run that bails reaches the fan,
      ;; which pays for the real set then.
      (let [budget (* (max 1 (count (tax/contexts (reasoning/taxonomy kb)))) *rows-per-reader*)
            rows   (post-hoc kb goals witness budget prepared-at)]
        (if (identical? abandoned rows)
          {:answers (fan kb goals witness run-at) :strategy :fan :abandoned-post-hoc true}
          {:answers rows :strategy :post-hoc}))

      :else
      {:answers (fan kb goals witness run-at) :strategy :fan})))
