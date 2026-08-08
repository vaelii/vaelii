;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.levels
  "The lookup-to-query stack: eight levels of escalating interpretive machinery over
  the same goal, from a raw index read to full backward chaining.

  Every layer the engine already has is a *point on a ladder* — the trie knows
  nothing but paths, `raw-match` adds unification, `matches-visible` adds context
  inheritance, the prover engine adds closures and rules.  Naming those points and
  giving them one call shape makes the cost of an answer legible: you can ask what
  the cheapest machinery that answers a goal is (`escalate`), or watch an answer
  appear as machinery is switched on (`explain`).

    0 :raw      handles at an index location — no sentence semantics at all
    1 :extent   one literal context, narrowed by functor; no unification
    2 :local    + unification and the symmetric mirror, one literal context
    3 :visible  + context inheritance (the genlContext up-closure)
    4 :typed    + predicate inheritance (the genl spec walk)
    5 :closed   + transitive closure for transitive predicates
    6 :solved   the whole prover registry — no member of it expands a rule
    7 :proved   + rule expansion (the recursive chainer, registry as its leaf)

  Each level adds **exactly one** mechanism to the one below it, so a result that
  appears at level n and not at n-1 is attributable to that mechanism alone.

  **Monotonicity, and the two joints where it is not free.**  Levels 3-5 are wider
  calls to the same matcher, and level 5 is literally `level 4 ∪ the closure`, so an
  answer reachable at one of them is reachable at the next.  Two joints are not like
  that, and naming them is half of what naming the levels is for:

    1 -> 2 **narrows**.  Level 1 is candidate retrieval and never looks at the goal's
    arguments; level 2 unifies.  So for any goal that pins an argument level 2 is a
    *subset* of level 1 — which is one of the two reasons `escalate` floors at 2.

    3 -> 4 can **drop** an answer.  Level 4 is `res/matches-visible`, which reads the
    `except` visibility filter that `res/raw-match` does not, so a sentex a believed
    `(except (sentexHandle H))` hides from the view context is matched at levels 2 and
    3 and gone from level 4 up.  Level 4 is right and the engine agrees — `ask` denies
    that goal too.  What it costs is `escalate`, which will name level 2 as the
    machinery sufficient for a goal the engine does not answer.  No floor fixes that:
    whether a level over-reports is a property of the KB, not of the level.

  Level 6 delegates to the real engine (`provers/solve-goal-with`) and therefore
  inherits its behaviour, including the short-circuit where a prover claiming
  completeness 100 runs *alone*: for a `genl` goal, level 6 returns the taxonomy
  closure rather than the union of closure and stored facts, which is why level 6
  answers may carry no handle where level 4's did.

  What does **not** bend is the content.  Completeness 100 claims a superset of what
  every other applicable prover would answer for that goal (`provers`, the contract at
  the head of the file), and a prover bearing on a channel it cannot read reports below
  100 for the goal so the union runs.  So from level 4 up an answer climbing the stack
  can lose its handle and never its existence.

  **Laziness.** Every level returns a lazy seq, and each is lazy as deep as the
  layer under it allows, so taking one result is strictly cheaper than taking all.
  Where that is impossible it is inherent, not an oversight, and is noted at the
  site: reading a stored set is one operation whether you take one member or all of
  them, and a transitive closure has no partial answer.  The property that does
  hold everywhere is that per-result work — a record fetch, an expensive prover, a
  rule expansion — is paid per result consumed."
  (:require [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]))

(def level-table
  "The stack as data: what each level is called and the one mechanism it adds."
  [{:level 0 :name :raw     :below nil       :adds "raw handles at an index location"}
   {:level 1 :name :extent  :below :raw      :adds "one literal context, narrowed by functor"}
   {:level 2 :name :local   :below :extent   :adds "unification + the symmetric mirror"}
   {:level 3 :name :visible :below :local    :adds "context inheritance via genlContext"}
   {:level 4 :name :typed   :below :visible  :adds "predicate inheritance via the genl spec walk"}
   {:level 5 :name :closed  :below :typed    :adds "transitive closure for transitive predicates"}
   {:level 6 :name :solved  :below :closed   :adds "the whole prover registry"}
   {:level 7 :name :proved  :below :solved   :adds "rule expansion (backward chaining)"}])

(def max-level (-> level-table count dec))

(def query-floor
  "The first level that answers a *goal* rather than a question about storage, and
  so `escalate`'s default floor.

  Levels 0 and 1 are retrieval, not matching: level 1 ignores the goal's arguments
  entirely (that is what level 2 adds), and level 0 ignores belief — a defeated
  sentex still has a handle in the trie.  Either will happily report a hit for a
  goal it cannot actually verify: `(genl dog thing)` gets an answer at level 1 from
  some *other* stored genl fact in the same context.  Escalating from 0 would
  therefore name the wrong mechanism.  Pass an explicit floor of 0 to include them.

  A floor is the coarse half of that guard and the only half a constant can supply.
  Levels 2 and 3 match against the store without the `except` visibility filter (see
  the ns docstring), so a goal whose only stored answer is excepted is reported here at
  level 2 while `ask` denies it.  That depends on the KB rather than on the level, so
  no floor rules it out — read `explain`, where the drop at level 4 is visible."
  2)

(defn- level-name [n] (:name (nth level-table n)))

;; ---- result maps --------------------------------------------------------
;; One shape across all eight levels; a field a level cannot supply is nil.  Levels
;; 0-4 answer from a stored sentex, so they carry its :handle; levels 5-7 answer
;; through provers that return bindings only, so :sentence is the goal under those
;; bindings and :handle is nil — the answer is derived, not stored.

(defn- stored-result
  "A result backed by a stored sentex.  `stored` is the record `match-one` already
  fetched to unify against, so this costs no extra round trip."
  [level h bindings stored]
  {:level    level
   :handle   h
   :sentence (:sentence stored)
   :context  (:context stored)
   :bindings bindings})

(defn- derived-result
  "A result computed by a prover: bindings, and the goal seen through them."
  [level goal context bindings]
  (let [b (res/resolve-bindings bindings)]
    {:level    level
     :handle   nil
     :sentence (res/substitute goal b)
     :context  context
     :bindings b}))

(defn- distinct-by
  "Lazy `distinct` on a key function, keeping the first of each key.  Used to fold a
  derived answer into the stored one it duplicates: level 5 unions level 4's results
  (which carry handles) with closure results (which do not), and the stored one comes
  first, so the surviving result is the one with provenance."
  [f coll]
  (letfn [(step [xs seen]
            (lazy-seq
             (when-let [s (seq xs)]
               (let [x (first s), k (f x)]
                 (if (contains? seen k)
                   (step (rest s) seen)
                   (cons x (step (rest s) (conj seen k))))))))]
    (step coll #{})))

(defn- answer-key [r] [(:sentence r) (:context r) (:bindings r)])

(defn- answered-goal
  "The goal seen through a result's bindings — what makes two results the *same
  answer* when the two were reached different ways.  Neither stored field says it: a
  stored result carries the sentence it was stored **as** (a subtype instance, in
  general) and the context it was stored **in**, while a derived one carries the goal
  under its bindings and the context it was *asked* in.  A closure that re-derives a
  fact it also read from an ancestor context therefore agrees with the stored result
  on neither field, and keying the fold on either would call one answer two."
  [goal r]
  (res/substitute goal (res/resolve-bindings (:bindings r))))

;; ---- the levels ---------------------------------------------------------

(defn- goal-path
  "The index path for a goal.  A vector *is* a path already (level 0 addresses the
  index directly); a sentence is turned into one through `kb-sentex`, so symmetric
  arguments key the way they were stored."
  [kb goal context]
  (if (vector? goal) goal (sx/path (res/kb-sentex kb goal context))))

(defn- level-0
  "Raw handles at an index location.  No records are fetched and nothing is
  interpreted — not belief, not polarity, not the goal's arguments beyond what the
  path already encodes.  `p/lookup` is one trie walk regardless of how much of the
  result you consume."
  [kb goal context]
  (map (fn [h] {:level 0 :handle h :sentence nil :context nil :bindings nil})
       (p/lookup (:index kb) (goal-path kb goal context))))

(defn- root-refs
  "The secondary roots that constrain a level-1 lookup, each with its O(1)
  cardinality: the context root when the context is concrete, the functor root when
  the goal has one."
  [kb goal context]
  (let [idx  (:index kb)
        pred (when (sequential? goal) (nm/functor goal))]
    (cond-> []
      (and (some? context) (not (sx/variable? context)))
      (conj {:count (p/count-in-context idx context)
             :fetch #(p/sentexes-in-context idx context)})
      (symbol? pred)
      (conj {:count (p/count-with-functor idx pred)
             :fetch #(p/sentexes-with-functor idx pred)}))))

(defn- level-1
  "One literal context, no inheritance, no rules: the context's extent, narrowed to
  the goal's functor.  Arguments are *not* matched — this is candidate retrieval, and
  unification is what level 2 adds.

  Both constraints are secondary roots whose cardinality is their own set size, so we
  drive from whichever is smaller and stream-filter it against the other.  The
  filtering set costs one set read however much is consumed (inherent — a set read has
  no partial form), but the per-result work, a record fetch, is paid per result."
  [kb goal context]
  (let [[drive other] (sort-by :count (root-refs kb goal context))]
    (if (nil? drive)
      ()
      (let [keep? (if other (let [s (set ((:fetch other)))] #(contains? s %)) (constantly true))]
        (->> ((:fetch drive))
             (filter keep?)
             (keep (fn [h]
                     (when-let [s (p/get-sentex (:records kb) h)]
                       (stored-result 1 h nil s)))))))))

(defn- level-2
  "Exact-sentence match in a single literal context: unification against the stored
  sentence, belief-filtered, with the symmetric mirror probed.  No inheritance of any
  kind — the context is a literal trie token and a type predicate is not fanned out."
  [kb goal context]
  (map (fn [[h b s]] (stored-result 2 h b s)) (res/raw-match kb goal context)))

(defn- level-3
  "Level 2 plus **context inheritance**: the goal is matched in every context the
  view context sees, i.e. its genlContext up-closure.  Still no subtype fan-out, so
  this isolates what genlContext alone contributes.  A variable context already means
  'any context', so there is nothing to add.

  Reading up the cone is also what *creates* a retired spelling, which is why the
  reader-scoped filter belongs to this level rather than the one above.  A fact stated
  above an equality merge is believed where it lives — its own context was told nothing
  — while a context below the merge sees both it and the twin migration placed there,
  so an unfiltered fan-out hands back one fact twice, under two names the reader knows
  denote one thing (`res/without-retired`, docs/equality.md).  That is an artifact of
  the fan-out, not something the fan-out found."
  [kb goal context]
  (map (fn [[h b s]] (stored-result 3 h b s))
       (if (sx/variable? context)
         (res/raw-match kb goal context)
         (res/without-retired kb context
                              (res/lazy-mapcat #(res/raw-match kb goal %)
                                               (tax/context-up (:taxonomy kb) context))))))

(defn- level-4
  "Level 3 plus **predicate inheritance**: a unary type predicate is matched over its
  genl subtype closure, so `(animal ?x)` is satisfied by a stored `(dog Muffet)`.  This
  is exactly `res/matches-visible` — the layer the whole engine matches through."
  [kb goal context]
  (map (fn [[h b s]] (stored-result 4 h b s)) (res/matches-visible kb goal context)))

(defn- level-5
  "Level 4 plus **transitive closure**: the cached genl/genlContext closures and any
  predicate declared `(transitive P)`.  A closure has no partial answer — computing
  one link computes the fixpoint — so the closure half forces itself, but level 4's
  stored matches stream first and answer alone if they suffice.

  A closure is built from the very edges level 4 reads, so it re-derives most of what
  it read: a derived answer a stored result already carries is dropped, and the stored
  one — the one with a handle — survives.  The fold is **one-way**.  Two stored matches
  for one answer are two facts and both stay, because this level is level 4 *plus* a
  mechanism and must never be level 4 minus a duplicate."
  [kb goal context]
  (let [tp     (filter provers/transitive-prover? (provers/registry kb))
        ;; level 4's results are re-tagged to 5: `:level` is the level of the
        ;; *lookup*, not a claim about where the answer was first reachable —
        ;; `explain` is what answers that question.
        stored (map #(assoc % :level 5) (level-4 kb goal context))]
    (if (empty? tp)
      stored
      ;; Behind a `delay`, so a closure with nothing to say never builds the set — and
      ;; read off `:sentence` on the derived side, which `derived-result` has already
      ;; computed as exactly this key (`substitute` over an idempotently-resolved
      ;; binding map).  Only the stored side pays, and only once a derived answer has
      ;; arrived to be checked against it.
      (let [already (delay (into #{} (map #(answered-goal goal %)) stored))]
        (lazy-cat stored
                  (->> (provers/solve-goal-with kb tp goal context)
                       (map #(derived-result 5 goal context %))
                       (remove #(contains? @already (:sentence %)))
                       (distinct-by answer-key)))))))

(defn- engine-goal
  "The goal as the engine's own dispatch sees it: a ground reifiable NAT reified to the
  constant it denotes, and a term an equality merge retired rewritten to its class
  representative.  `core/ask` prepares its goal exactly this way and the backward
  chainers do too, so a level claiming to *be* that dispatch has to ask the same
  question — otherwise a goal spelled with a retired name, or one holding a NAT, is
  answered by `ask` and missed here, and the stack reports that *no* level reaches
  something the engine reaches at the first ask.

  It belongs to level 6 rather than lower down because it is a question about truth
  rather than about storage: levels 2-5 match the goal as written, which is what makes
  them a legible account of what the index and the two hierarchies hold."
  [kb goal context]
  (kb/rewrite-goal kb (nat/maybe-reify-for-read kb goal) context))

(defn- solved
  "Level 6: the real engine over a prover list, so dispatch, cost estimates and the
  complete-prover short-circuit are the ones `ask` uses."
  [level kb provers goal context]
  (distinct-by answer-key
               (map #(derived-result level goal context %)
                    (provers/solve-goal-with kb provers goal context))))

(defn- level-6
  "The whole prover registry: closures, disjointness, the predicate-metadata
  reasoners, evaluables, argIsa type inference and the fact prover — everything that
  answers from what is stored or cached, nothing that derives through rules.  No
  member of the registry expands a rule, so this is `ask`'s own dispatch and level 6
  answers whatever `ask` answers — the goal prepared the way `ask` prepares it
  (`engine-goal`) included."
  [kb goal context]
  (solved 6 kb (provers/registry kb) (engine-goal kb goal context) context))

(defn- level-7
  "Level 6 plus **rule expansion**: the recursive chainer with the registry as its
  leaf, so a rule's antecedent is answerable by any prover and the rules themselves
  are what this level adds over the one below.

  The unbounded engine on purpose.  A level is a question about *machinery* — what
  does backchaining reach that the registry alone does not — and answering it under a
  depth bound would answer a question about the bound instead.  `core/query` is where
  a bounded rule search lives, because there a caller has one to name.

  Unbounded is not the same as eager, and this level must be **lazy** like the seven
  below it: `escalate` climbs until something answers and reads one result to decide, and
  the browser pages a level at a time — so a level that realized its whole answer set
  before returning would make the most expensive level the one that costs the most to
  merely ask.  `res/prove-seq` drives the same search a solution at a time."
  [kb goal context]
  (let [goal     (engine-goal kb goal context)
        rules-fn (fn [g] (provers/candidate-rules kb g context))
        leaf     (fn [kb g context] (provers/solve-goal kb g context))]
    (distinct-by answer-key
                 (map #(derived-result 7 goal context %)
                      (res/prove-seq kb rules-fn [goal] context
                                     {:leaf-solver  leaf
                                      :est-override (provers/registry-est-override
                                                     kb context)})))))

(def ^:private level-fns
  [level-0 level-1 level-2 level-3 level-4 level-5 level-6 level-7])

;; ---- the stack ----------------------------------------------------------

(defn lookup
  "Answer `goal` in `context` using exactly the machinery of `level` (0-7).  A lazy
  seq of uniform result maps: {:level :handle :sentence :context :bindings}."
  [kb level goal context]
  (when-not (and (integer? level) (<= 0 level max-level))
    (throw (ex-info (str "level must be 0-" max-level) {:type :bad-level :level level})))
  ((nth level-fns level) kb goal context))

(defn escalate
  "Climb the stack from `floor` (default `query-floor`, 2) and stop at the first
  level that answers `goal`, returning {:level :name :results :tried}.  `:results`
  is the lazy seq from that level, so the climb costs one result per level tried,
  not a full answer per level.  Nothing answers → :level nil with every level tried.

  The default floor skips the two retrieval levels, which can report a hit for a
  goal they cannot verify — see `query-floor`.  Pass 0 to include them."
  ([kb goal context] (escalate kb goal context query-floor))
  ([kb goal context floor]
   ;; the same 0-7 vocabulary `lookup` refuses outside of: a floor above the top
   ;; would make `tried` empty and answer {:level nil} — a plausible "nothing
   ;; answered" for what is an off-by-one in the caller's arithmetic
   (when-not (and (integer? floor) (<= 0 floor max-level))
     (throw (ex-info (str "floor must be 0-" max-level) {:type :bad-level :floor floor})))
   (let [tried (range floor (inc max-level))
         ;; `some`, not `(first (keep ...))`: `(range 2 8)` is a **chunked** seq, and
         ;; `keep`'s chunked path runs its function over the whole chunk before
         ;; yielding anything — so a goal answered at level 2 still probed levels 3-7,
         ;; backward chaining included.  The reported `:tried` said `[2]` while six
         ;; levels had run, which is the expensive half of the claim silently false.
         ;; `some` walks with `recur` and stops at the first hit.
         hit   (some (fn [n]
                       (let [rs (lookup kb n goal context)]
                         (when (seq rs) [n rs])))
                     tried)]
     (if hit
       (let [[n rs] hit]
         {:level n :name (level-name n) :results rs :tried (vec (range floor (inc n)))})
       {:level nil :name nil :results () :tried (vec tried)}))))

(defn explain
  "Run every level over `goal` and report what each yields: a seq of {:level :name
  :count}.  A diagnostic — it counts, so it realizes every level fully.  The first
  level whose count jumps is the mechanism the answer depends on."
  [kb goal context]
  (for [{:keys [level name]} level-table]
    {:level level :name name :count (count (lookup kb level goal context))}))
