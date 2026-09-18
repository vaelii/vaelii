;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.reads
  "The named entry points onto the index — a read **as stored**, or a read **as believed**.

  The fourth invariant is that a stored sentex is not a believed one (README.md, \"The
  model in one page\").  Every `IndexStore` posting is storage: it holds a defeated
  default, a conclusion whose support was withdrawn and a spelling an equality retired,
  because all three are revivable and the index is not where belief lives.  So a caller
  reading a posting has a question to answer, and until it is asked in the name of the
  read nothing distinguishes the caller that answered it from the one that forgot.

  This namespace is where it is asked.  Every raw `vaelii.impl.protocols` index read
  outside a short roster of implementers goes through an entry point here, and the entry point's own
  name says which answer it gives — `lein lint`'s **E16** is what keeps that true, and
  its roster is the one place the exceptions are written down.

  ## The two entry points, and why they take different arguments

  - **`as-stored-…` takes the index store.**  An as-stored read *is* an index
    operation, so the entry point's arglist is the protocol method's and nothing else is in
    scope.  A caller reaching one is saying it wants storage: a candidate set it filters
    itself, a roster that must over-approximate, a diagnostic that reports what is
    written.  Each entry point below says what a stored-but-disbelieved answer is *for*.
  - **`believed-…` takes the KB.**  Belief lives in the JTMS, so a believed read is a
    question about the KB and not about the index — which is exactly the distinction the
    arglists carry.  The filter is `jtms/in?`, which already drops a **superseded**
    spelling along with a defeated one (`vaelii.impl.jtms`'s `-in?`), so a believed entry point
    means what `kb/sentexes-matching` means for the handles it yields.

  An entry point is a **wrapper and never a rewrite**: one call to the protocol method it names,
  the same laziness, the same count-aware path.  It adds no index operation, which is
  what keeps `assert_cost_test` reading the same numbers on either side of one.

  ## Where there is only one entry point, and why

  - **The cardinalities** (`stored-count-…`) count a posting set's members.  Belief is
    not in the index, so there is no O(1) believed count and this namespace does not
    pretend otherwise — a believed count is `(count (believed-… …))` and is O(n).  The
    public readers state the same thing (`vaelii.core/count-with-functor`).
  - **The vocabulary** (`stored-terms`, `stored-term-count`) is the roster of names the
    term index is keyed by.  A name enters with the first sentex mentioning it and leaves
    with the last, so it answers *what this KB talks about* — a question defeat does not
    change.
  - **The watched-rule roster** (`watched-rule?`, `watched-rules`, `watched-rules-on`)
    answers \"which rules might need re-checking\", never \"does the exception hold\", and
    stores no truth value at all (`protocols/IndexStore`).  Filtering it by belief would
    narrow a re-check queue, and a missed re-check is a wrong belief where an extra one
    is a query nobody needed.

  ## Two belief questions this namespace does not answer

  - **A rule's** belief is `resolution/rule-believed?` and not `jtms/in?`: a sentex the
    TMS holds no node for is *available* rather than disbelieved, which is an arm a plain
    membership test does not have.  So `as-stored-rules-by-antecedent` and its consequent
    twin have no believed sibling here, and a chainer asks `res/rule-believed?` of each
    handle it means to fire.
  - **`resolution/*belief-blind*`** is not read here.  It is a named opt-out scoped to
    the retrieval entry point that resolves `CxEverything`, and no caller of these entry points is on
    that path — an entry point that consulted it would extend the opt-out to reads nobody granted
    it to."
  (:require [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- extents: the trie and the secondary roots ---------------------------

(defn as-stored-in-context
  "Handles stored in `context` — its whole extent, rules included, belief unread.

  A stored-but-disbelieved answer is what a caller wants here when it is about the
  *contents* of a context rather than about what holds in it: a teardown that must remove
  every record it finds, an ancestor set sweep that fetches each record and decides on the record,
  a level-1 diagnostic reporting what the root holds."
  [index context]
  (p/sentexes-in-context index context))

(defn as-stored-with-functor
  "Handles of fact sentexes whose functor is `pred`, any arity, either polarity — belief
  unread.

  The candidate-set read: a caller narrowing by predicate almost always fetches each
  record and decides on its polarity, its context and its belief together, and doing so
  one handle at a time is cheaper than two passes over the same set.  A caller whose
  filter is belief alone takes `believed-with-functor` instead."
  [index pred]
  (p/sentexes-with-functor index pred))

(defn as-stored-with-arg
  "Handles of fact sentexes holding `term` at 1-based argument `pos` — belief unread.

  The argument root is scoped by predicate, so this is the narrow read a pattern pinning
  an argument after a variable wants.  Same shape as `as-stored-with-functor`: a
  candidate set whose consumer decides per record."
  [index pos term]
  (p/sentexes-with-arg index pos term))

(defn as-stored-with-args
  "Handles with functor `pred` AND each `[pos term]` of `pos-terms` — one intersection of
  the functor root and the named argument roots, belief unread.  `pred` may be nil, for a
  variable-functor pattern."
  [index pred pos-terms]
  (p/sentexes-with-args index pred pos-terms))

(defn as-stored-with-term
  "Handles the inverted term index keys by `term` — belief unread.

  Exact for a symbol; for a compound outside the indexed depth bounds it holds only the
  sentexes that nest it deep enough, so `kb/find-sentexes` is the exact read for one.  The
  postings are a candidate set in both cases: a term appears in a sentence the reader then
  has to look at."
  [index term]
  (p/sentexes-with-term index term))

(defn as-stored-at-path
  "Handles whose trie path matches `pattern` — one walk, no records fetched, nothing
  interpreted.  A variable token in the path is a wildcard that fans over every child.

  The rawest read the index has, and the only caller that wants it is one reporting the
  index itself: level 0 of `vaelii.impl.levels` addresses the trie directly and interprets
  neither belief nor polarity, which is what makes it the floor the other levels are
  measured against."
  [index pattern]
  (p/lookup index pattern))

(defn believed-with-functor
  "Handles of fact sentexes with functor `pred` that the KB **believes** — the extent
  above, filtered by `jtms/in?`.

  Lazy, as the posting read is: the filter is applied as the seq is walked, so a consumer
  taking a prefix pays a TMS probe per handle it takes and not per handle in the root.  A
  superseded spelling drops out with a defeated one, since that is what `in?` answers."
  [kb pred]
  (let [tms (reasoning/tms kb)]
    (filter #(jtms/in? tms %) (p/sentexes-with-functor (:index kb) pred))))

(defn believed-with-args
  "Handles with functor `pred` AND each `[pos term]` of `pos-terms` that the KB
  **believes** — `as-stored-with-args` filtered by `jtms/in?`, lazily.

  The narrowing read's believed entry point: a caller that knows several of a sentence's terms
  and wants only what holds asks here rather than intersecting and then filtering by
  hand."
  [kb pred pos-terms]
  (let [tms (reasoning/tms kb)]
    (filter #(jtms/in? tms %) (p/sentexes-with-args (:index kb) pred pos-terms))))

;; ---- cardinalities: a posting set's size, and never its members -----------

(defn stored-count-in-context
  "How many sentexes are **stored** in `context` — one set-size read, O(1), nothing
  fetched and no belief consulted.  A defeated default still occupies its context."
  [index context]
  (p/count-in-context index context))

(defn stored-count-with-functor
  "How many fact sentexes are **stored** with functor `pred` — one set-size read, O(1).

  The gate in front of nearly every definitional check in the engine: a KB that declares
  none of a feature's predicates pays one integer read and stops, which is what keeps an
  unused feature off the assert path."
  [index pred]
  (p/count-with-functor index pred))

(defn stored-count-with-arg
  "How many fact sentexes **store** `term` at argument position `pos` — one O(1) set-size
  read per predicate declaring an argument at that slot, since the argument roots are
  scoped by predicate."
  [index pos term]
  (p/count-with-arg index pos term))

(defn stored-count-at
  "How many sentexes are **stored** under trie prefix `prefix` — the count-aware trie's
  own tally, no walk.  `[]` is the whole KB."
  [index prefix]
  (p/count-at index prefix))

(defn stored-count-children
  "How many child tokens sit under interior prefix `prefix` — the trie's distinct-value
  count at a position, answered without building the child set.

  What the planner's cost model divides by, so it must not scale with the KB:
  `(count (stored-children …))` would, and this does not."
  [index prefix]
  (p/count-children index prefix))

;; ---- the vocabulary roster -----------------------------------------------

(defn stored-terms
  "Every symbol term the index is keyed by — the KB's vocabulary, unordered.

  A name is in this roster while some **stored** sentex mentions it, so it answers what
  the KB talks about rather than what it currently holds: defeating the one fact about a
  term does not unname the term."
  [index]
  (p/terms index))

(defn stored-term-count
  "How many distinct symbol terms the index is keyed by — the roster's own count, no
  walk over it."
  [index]
  (p/term-count index))

;; ---- the rule indexes ----------------------------------------------------

(defn as-stored-rules-by-antecedent
  "Handles of rules with an antecedent on `pred` — every rule, whatever its direction,
  belief unread.

  Belief for a **rule** is `resolution/rule-believed?` and not `jtms/in?`, which is why
  there is no believed entry point beside this one: a rule the TMS holds no node for is available
  rather than disbelieved, and a chainer asks that question of each handle it means to
  fire."
  [index pred]
  (p/rules-by-antecedent index pred))

(defn as-stored-rules-by-consequent
  "Handles of rules concluding `pred` — every rule, whatever its direction, belief unread.

  `resolution/rule-believed?` is the belief question, as for the antecedent entry point above.  A
  rule whose consequent functor is a variable files under `protocols/var-consequent-key`
  rather than under a canonical `?var0`, so a concrete goal's answer is this bucket
  unioned with that catch-all (`resolution/concluding-rule-handles`)."
  [index pred]
  (p/rules-by-consequent index pred))

;; ---- the watched-rule (exception re-check) roster -------------------------

(defn watched-rule?
  "Is `handle` in the exception/watched-rule roster — O(1) membership, the firing-path
  gate.

  The roster stores no truth value, so there is no second entry point: it answers which rules
  carry an `exceptWhen` at all, never whether one holds.  Whether the exception *fires* is
  `provers/exceptions-block?`, and whether the rule itself is believed is
  `resolution/rule-believed?`."
  [index handle]
  (p/exception-rule? index handle))

(defn watched-rules
  "Handles of every rule carrying a re-check condition — an exception, an `(unknown S)`
  antecedent, an aggregate, a closed-extent negative or a `different` antecedent
  (`rules/rechecked?`).

  Read to **queue re-checks**, which is why belief is not filtered: over-queueing costs a
  query at the next settle and under-queueing leaves a conclusion standing on evidence
  that has moved.  A trigger is conservative in the direction the answer is."
  [index]
  (p/exception-rules index))

(defn watched-rules-on
  "Handles of rules whose re-check condition mentions `pred` — the predicate-scoped slice
  of `watched-rules`, and unfiltered for its reason."
  [index pred]
  (p/rules-with-exception-on index pred))
