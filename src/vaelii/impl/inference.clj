;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.inference
  "A **backward** chainer whose state is a set of nodes ordered by cost — not
  `vaelii.impl.chain`'s *forward* agenda, which is a queue of newly believed data
  waiting to be matched against rules.  This one runs from a query towards the facts,
  and what its agenda holds is unfinished proofs.

  The other backward chainer is path-structured, walking an explicit goal stack
  (`res/prove-from`).  Here
  the unit is a **node** — a whole conjunction plus everything accumulated to reach it —
  and expanding one is a single rewrite:

      node:   [ L₁ … Lᵢ … Lₙ ]                        σ
      rule:   A₁…Aₖ ⟹ C,  with  b = unify(Lᵢ, C)
      child:  [ b(L₁) … b(Aᵢ…) … b(Lₙ) ]              σ ∪ b

  The rule's antecedents under the head unifier are the **residual** — what is left to
  prove if this rule is the one that fires — spliced in where `Lᵢ` was.  Applied
  repeatedly, that transformation is the whole search: every node is the query rewritten
  through some sequence of rules, and a node whose conjunction solves against facts
  alone is a completed proof.

  Two things follow from the state being a value rather than a call stack.  A stop
  between two expansions leaves an **agenda**, not a continuation closure, so a bounded
  run is `budget/collect` over the result stream and nothing else.  And the tree is an
  artifact that outlives the search, which is where dead ends and \"why did this cost so
  much\" answers come from.

  A third follows from the frontier being a priority queue: **which** node pops next is a
  policy rather than a structure, and it lives in `vaelii.impl.tactics` — one additive
  estimate whose signs the caller picks.  Every tactician returns the same answer set;
  what differs is when.

  **What it is good at, measured.**  The residual stays *symbolic* — `(anc ?y ?z)` is
  not re-asked once per binding of `?y`, it is rewritten once — so the node count is a
  function of the rule graph and the depth bound, not of the data.  Over a kinship DAG
  the same seven nodes answer 16 leaves and 64 of them, and an open query runs 2-6x
  faster than the DFS because each node's conjunction is one planned join rather than a
  tuple-at-a-time walk.  A **bound** query is the other way round (2-4x slower): the
  rewrite ignores what the caller already knows and computes the relation, then filters.
  A conjunctive query is 2-3x slower still, because a k-literal conjunction has more
  ways to be rewritten than a single goal does.

  **What it cannot do.**  Termination here is the depth bound, and nothing else.  The
  DFS is data-driven — it substitutes as it goes, so a chain of length n terminates
  after n steps whatever bound it was given — while a symbolic residual grows a conjunct
  per rewrite and would grow forever.  So `*max-depth*` is a real ceiling: a derivation
  deeper than it is not found, and the depth a query needs is a property of the *data*.
  Answer-set parity with `prove` therefore holds up to the bound and not past it, which
  is why the selector defaults to `:dfs` (`core/*query-engine*`).  Iterative deepening
  is what would close that, and it is not built.

  See docs/inference.md."
  (:require [clojure.set :as set]
            [clojure.walk :as walk]
            [vaelii.impl.budget :as budget]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.tactics :as tactics]))

(def ^:dynamic *max-depth*
  "How many rule expansions any one literal may be rewritten through, and **nil by default**.
  It is the termination condition: a residual grows a conjunct per rewrite and the claimed-key
  set cannot stop it.  The bound is per literal, each conjunct carrying its own remaining
  budget decremented only when it is rewritten, so the literal expanded first cannot spend the
  whole allowance (`res/prove-from` carries one depth per frame).

  There is no default because the depth a query needs is a property of the KB's derivation
  chains, and a wrong default loses answers.  The caller says, or the search refuses to start."
  nil)

(defn- required-depth
  "The depth bound for this run, or a refusal naming the choice that was not made."
  [max-depth]
  (or max-depth *max-depth*
      (throw (ex-info (str "the node engine needs a depth bound: pass :max-depth, or bind "
                           "inference/*max-depth*.  There is no default because the depth a "
                           "query needs is a property of the data, not of the engine.")
                      {:type :no-depth-bound}))))

;; ---- the node ------------------------------------------------------------
;; {:literals   [{:sentence S :depth d} …]  the conjunction still to prove, written in
;;                                          this node's OWN namespace: ?var0 ?var1 …
;;  :from       the leftmost literal this node may rewrite (see `children`)
;;  :answer-terms {the asker's var -> a term here}  the whole chain of rewrites, folded
;;  :guards     [{:test <closure over a rule's own names> :rule <carrying rule's handle>
;;                :terms {rule-var -> term here}}]
;;  :derived    [S …]  goals a rewrite above answered, written here — only the ones
;;                     belief could already have defeated (`res/defeated-index`), so it
;;                     is empty for every node of a KB with no defeat on those predicates
;;  :nvars      how many variables this node names, so a rule can be numbered past them
;;  :supports   the handles of the rules expanded above
;;  :tree-depth rewrites taken
;;  :id :parent-id}
;;
;; **Every node is a canonicalized conjunction** (`sentex/canonical-conjunction`).  Two
;; conjunctions that differ only in what their variables are called are one question, so
;; numbering them the same way is what lets the claimed-key set recognize a node the
;; search already built — identity is structural, rather than a renaming heuristic laid
;; over an accumulating namespace.  It is also what makes the *rule* problem go away: a
;; stored rule is spelled `?var0 ?var1 …` and so is a node, so a rule is numbered
;; **past** the node's variables before it is unified, and the two namespaces are
;; disjoint by construction rather than by decorating names apart after the fact.
;;
;; The price of a namespace per node is that nothing crosses between two of them for
;; free, and `push-term` is the toll.  Each rewrite pushes every term the node is still
;; accountable for — what the asker asked about, and what each pending guard was written
;; over — through the head unifier and into the child's numbering.  Renaming is
;; `sx/rename-vars`, one pass, because these maps are permutations: canonicalizing a
;; conjunction that already uses canonical names, crossed over, yields `{?var0 ?var1,
;; ?var1 ?var0}`, and chasing that does not terminate.
;;
;; They are maps to **terms** and not to variables, which is the part that is easy to get
;; wrong and costs an answer when you do.  A rewrite can *ground* what it renames: the
;; goal `(flies Robin)` against the head `(flies ?var0)` leaves a child with no variable
;; in it at all, and a variable-only map would drop `?x = Robin` at exactly the rewrite
;; that established it.

(defn- push-term
  "A term written in the namespace of the node being rewritten, moved into the child's:
  substituted through the head unifier, then renamed into the child's canonical
  numbering.

  This is the one operation the whole bookkeeping is made of, and it is a **term** map
  rather than a variable map for a reason a variable map cannot survive.  A rewrite does
  not only rename what a node knows — it can *ground* it.  Unifying `(flies ?var0)`
  against a rule head `(flies ?var0)` for the goal `(flies Robin)` leaves the rule's
  variable equal to `Robin`, and a child conjunction with no variable in it at all.  A
  map that carried only surviving variables would drop what the asker asked about at
  exactly the rewrite that answered it."
  [t b vm-inv]
  (sx/rename-vars (res/substitute t b) vm-inv))

(defn- push-terms [m b vm-inv]
  (persistent!
   (reduce-kv (fn [acc k t] (assoc! acc k (push-term t b vm-inv))) (transient {}) m)))

(defn- resolve-terms
  "`{name -> term}` with each term resolved against a solution — how a node's answer, or
  a guard's argument, is read out of a solution in the node's own namespace."
  [m sol]
  (persistent!
   (reduce-kv (fn [acc k t] (assoc! acc k (res/substitute t sol))) (transient {}) m)))

(defn node-key
  "The key a node is claimed under: its literals, the depths they carry, the map back to the
  asker's variables (`:answer-terms`), the set of pending guard identities, `:derived` and the
  rewrite start.  The literals are already canonical, so alpha-variant conjunctions are one key.

  `:answer-terms` keeps apart two paths that ask the same question for different answers.  A
  guard's identity is its rule and its term map, never a count, since two distinct guarded
  rules rewriting one goal to one residual would otherwise read as one node and drop every
  answer only the second exception admits.  `:derived` keeps apart paths that answered
  different goals, one of which may have used a goal belief defeated; it is empty for a KB
  with no defeat on the predicates in play."
  [{:keys [literals answer-terms guards derived from] :as _node}]
  [(mapv :sentence literals)
   (mapv :depth literals)
   answer-terms
   (into #{} (map (fn [g] [(:rule g) (:terms g)])) guards)
   derived
   from])

;; ---- the frontier order --------------------------------------------------

(def ^:dynamic *estimate*
  "`(fn [kb strategy node] -> long)`, the number the frontier is ordered by.

  `tactics/estimate` unless a caller substitutes one — the extension point a whole ordering policy
  reaches through, which is why the frontier is a priority queue rather than a stack.
  Whatever is bound here must be an **ordering** and not a filter: the search visits the
  same nodes in every order, so a number that changed the answer set would be a number
  that dropped one."
  tactics/estimate)

(def ^:dynamic *strategy*
  "The strategy a session runs under when its caller names none — nil for
  `tactics/defaults`.  A tactician keyword or a strategy map (`tactics/strategy`)."
  nil)

;; ---- the priority queue --------------------------------------------------
;; Entries are `[estimate content id]` in a sorted set, so the order is total and
;; deterministic.  The id, not the node — a node is a value in the registry, and the
;; queue holds only what it needs to choose.
;;
;; **A cost tie breaks on content**, which is the whole reason the entry carries a third
;; thing.  An estimate is a coarse number and ties constantly, and the tie decides which
;; node a `:node-budget` run expands before it stops — so breaking it on the id would key
;; a bounded search's answer set on the order the nodes happened to be minted, which is
;; the order the rules were asserted in.  `frontier-key` is what the node *is* — the
;; residual conjunction, and the position the next rewrite resumes from — and the id
;; stays behind it so the comparator is total: two entries that compared equal would be
;; one entry in a sorted set, and the second node would be dropped rather than searched.

(defn frontier-key
  "What the frontier orders a cost tie by: the node's residual conjunction and the literal
  index a rewrite resumes from.  Read from the node's own content, so two searches over
  the same knowledge fill the frontier the same way whatever order it arrived in."
  [node]
  [(mapv :sentence (:literals node)) (long (:from node))])

(def ^:private frontier-order
  "Estimate first, then content (`nm/compare-form` — structural, so no key is printed),
  then id.  A `Comparator` for the frontier's sorted set."
  (fn [[^long e1 c1 ^long i1] [^long e2 c2 ^long i2]]
    (let [c (Long/compare e1 e2)]
      (if (zero? c)
        (let [c (long (nm/compare-form c1 c2))]
          (if (zero? c) (Long/compare i1 i2) c))
        c))))

(defn empty-queue [] (sorted-set-by frontier-order))

(defn queue-push [q ^long est content ^long id] (conj q [est content id]))

(defn queue-pop
  "`[entry queue']`, or **nil** when the queue is empty."
  [q]
  (when-let [e (first q)] [e (disj q e)]))

;; ---- the session ---------------------------------------------------------

(defn session
  "A search over `goals` (a vector of sentences) in `context`, ready to be stepped.

  Everything the search knows is in here and nothing is captured in a closure: the
  frontier, the node registry, the results, the claimed keys, the counters.  A caller
  may hold it, read it between steps, and hand it back."
  ([kb goals context] (session kb goals context {}))
  ([kb goals context {:keys [max-depth] :as opts}]
   (let [depth (long (required-depth max-depth))
         strat (tactics/strategy (get opts :strategy *strategy*))
         ;; the root is the asker's question canonicalized, and `vm` is the only record
         ;; of what they called its variables — every answer the search finds comes back
         ;; through here
         [canon vm] (sx/canonical-conjunction (vec goals))
         root  {:literals     (mapv (fn [g] {:sentence g :depth depth}) canon)
                :from         0
                ;; the asker's variables, each pointing at the canonical variable that
                ;; now stands for it — the direction every rewrite pushes forward
                :answer-terms (set/map-invert vm)
                :nvars        (count vm)
                :guards       []
                ;; nothing has been rewritten yet, so no answer of this node is a rule
                ;; expansion's and belief has nothing to have decided against
                :derived      []
                :supports   #{}
                :tree-depth 0
                :context    context
                :id         0
                :parent-id  nil}
         sess  {:kb          kb
                :context     context
                :max-depth   depth
                :strategy    strat
                :leaf-solver (:leaf-solver opts)
                ;; the cost model the leaf is planned by, and only ever supplied with
                ;; one — the index model is right for a stored-facts leaf (`solve-inline`)
                :est-override (:est-override opts)
                :proof?      (boolean (:proof? opts))
                ;; What belief has already defeated, read once for the whole search: a
                ;; query writes nothing, so the derived defeated set cannot move
                ;; underneath it.  nil — the common case — is the presence check that keeps every
                ;; node's `:derived` empty and this check out of the search entirely.
                :defeated    (res/defeated-index kb)
                :queue      (atom (queue-push (empty-queue) (*estimate* kb strat root)
                                              (frontier-key root) 0))
                :nodes      (atom {0 root})
                :claimed    (atom #{(node-key root)})
                :seen       (atom #{})
                :counter    (atom 0)
                ;; Set to true when the depth bound stopped a rewrite the search would
                ;; otherwise have taken (`depth-truncated?`).  Allocated only under
                ;; `:track-truncation?`, so `step!`'s candidate-rule probe is off the plain
                ;; query path — `core/query-status` asks for it, `core/query` never does.
                :truncated  (when (:track-truncation? opts) (atom false))
                ;; The transitive predicates whose closure a leaf did not enumerate for a
                ;; both-open goal (`provers/*unenumerated*`), bound around each expansion's
                ;; solve in `step!`, so every driver of this session reads one set and a
                ;; resume keeps adding to it.
                :unenumerated (provers/unenumerated-collector)
                :stats      (atom {:expanded 0 :dropped 0 :solutions 0})}]
     sess)))

(defn- claim!
  "Take `k` for this session, or report that it was already taken.  `swap-vals!` is a
  compare-and-set, so the test and the take are one step — which is what lets a later
  driver run expansions concurrently without this becoming a rewrite."
  [sess k]
  (let [[old new] (swap-vals! (:claimed sess) conj k)]
    (not (identical? old new))))

;; ---- (a) solving a node's conjunction, at depth 0 ------------------------

(defn- solve-inline
  "Every substitution that proves the node's conjunction against facts alone; rule expansion
  is for the children.

  Conjuncts run in `plan/order`, the plan the DFS uses, and not in the frontier's order, so the
  join is strategy-independent.  A deferred literal (`different` / `evaluate` / `unknown`) is
  computed through the registry, as in the other chainers, and never rewritten in `children`.
  No substitution map is threaded in: the node's literals already carry every unifier taken.

  `leaf-solver` answers a literal the search will not rewrite: nil is the stored facts, and the
  registry makes every prover answer a leaf.  `est-override` is the cost model that leaf is
  planned by (the index would price a `genl` conjunct answered from the cached closure as the
  cheapest literal); the DFS chainer takes the same pair (`res/prove-from`)."
  [kb literals context leaf-solver est-override]
  (let [planned (plan/order kb literals context {:est-override est-override})]
    (reduce (fn [sols literal]
              (mapcat (fn [b]
                        (let [g (res/substitute literal b)]
                          (cond
                            (sx/deferred-literal? g)
                            (map #(merge b %) (res/solve-deferred kb g context))
                            leaf-solver
                            (map #(merge b %) (leaf-solver kb g context))
                            :else
                            (map (fn [m] (merge b (nth m 1)))
                                 (res/matches-visible kb g context)))))
                      sols))
            [res/no-bindings]
            planned)))

;; ---- (b) the residual children -------------------------------------------

(defn- ask-guard
  "Is this guard satisfied by `sol`?

  A guard is an `exceptWhen` closure written over its own rule's variable names, plus the
  terms those names now stand for here.  The solution is **augmented** with them rather
  than replaced, so a guard that also reads a name both namespaces happen to share still
  finds it.  Resolving through the solution matters: the term may be a variable this node
  only just bound."
  [{:keys [test terms]} sol]
  (test (merge sol (resolve-terms terms sol))))

(defn- collapse-repeats
  "`literals` with each repeated sentence kept once, and the index a repeat folded onto.
  Conjunction is idempotent, and a residual carrying a repeat has a `node-key` the claimed-key
  set cannot recognize, so a cyclic rule graph would add a conjunct per turn of the cycle.  A
  kept literal takes the largest depth of the copies folded onto it, since a deeper copy admits
  every rewrite a shallower one does.

  Returns `[kept fold slots]`.  `fold` is the smallest index in `kept` that a later copy folded
  onto, and `slots` the index in `kept` each of `literals` landed on; both are nil when no
  sentence repeated."
  [literals]
  (if (< (count literals) 2)
    [literals nil nil]
    (let [acc (reduce (fn [{:keys [out idx fold] :as acc} l]
                        (if-let [j (get idx (:sentence l))]
                          (assoc acc
                                 :out  (update-in out [j :depth] max (long (:depth l)))
                                 :fold (if fold (min (long fold) (long j)) (long j)))
                          (assoc acc
                                 :out (conj out l)
                                 :idx (assoc idx (:sentence l) (count out)))))
                      {:out [] :idx {} :fold nil}
                      literals)]
      [(:out acc) (:fold acc)
       (when (:fold acc) (mapv #(get (:idx acc) (:sentence %)) literals))])))

(defn- restates-goal?
  "Does the rewrite's residual ask the goal it replaced again, or something stronger, so that
  the parent reaches every answer of the child through a sibling?  True when a residual
  literal would answer `g`, the goal under the head unifier, as a rule consequent does
  (`res/subsuming-unify` binding nothing) and lands at a depth no larger than `goal-depth`, the
  goal's depth in the parent; the collapse raised no carried literal's depth; and the child's
  `rewrite-from` reopens nothing left of the parent's `from`.  A carried literal equal to the
  goal does not count, since two copies of one goal would drop both rewrites.

  `spliced` is the conjunction before the collapse, `slots` the collapse's map from each spliced
  position to its place in `kept` (nil when nothing folded), and positions `i` up to `i + arity`
  are the residual's."
  [kb context g goal-depth from rewrite-from spliced kept slots i arity]
  (let [i     (long i)
        end   (+ i (long arity))
        depth (fn [^long p] (long (:depth (if slots (nth kept (nth slots p)) (nth spliced p)))))]
    (boolean
     (and (>= (long rewrite-from) (long from))
          (or (nil? slots)
              (every? (fn [^long p] (= (long (:depth (nth spliced p))) (depth p)))
                      (concat (range i) (range end (count spliced)))))
          (some (fn [^long p]
                  (and (<= (depth p) (long goal-depth))
                       (= res/no-bindings
                          (res/subsuming-unify kb g (:sentence (nth spliced p))
                                               res/no-bindings context))))
                (range i end))))))

(defn- children
  "The nodes reachable from this one by rewriting one literal through one rule.

  Rewriting goes left to right and never backwards (`:from`), so the frontier does not carry
  every interleaving of a conjunction's rewrites: 49 nodes instead of 241 on a two-literal
  ancestor query.  The rule is numbered past this node's variables
  (`sx/canonical-conjunction` with a start of `:nvars`) before unifying, since stored rules and
  nodes are both spelled `?var0 ?var1 …`.  The child is canonicalized in turn, so every term
  the node is still accountable for is pushed into the new numbering: the asker's answers and
  each pending guard's numbering (`shift-back`).  The spliced conjunction goes through
  `collapse-repeats`.  A child whose residual asks the goal it rewrote again is not built
  (`restates-goal?`)."
  [kb node context defeated]
  (let [{:keys [literals guards supports tree-depth from nvars answer-terms derived]} node]
    (for [i     (range (long from) (count literals))
          :let  [{:keys [sentence depth]} (nth literals i)]
          :when (and (>= (long depth) 1) (not (sx/deferred-literal? sentence)))
          rule  (provers/candidate-rules kb sentence context)
          :let  [{:keys [antecedents consequent guard handle]} rule
                 [shifted shift-back] (sx/canonical-conjunction
                                       (into [consequent] antecedents) nvars)
                 b (res/subsuming-unify kb sentence (first shifted) res/no-bindings context)]
          :when b
          :let  [carry (fn [l] (update l :sentence #(res/substitute % b)))
                 resid (mapv (fn [a] {:sentence (res/substitute a b)
                                      :depth    (dec (long depth))})
                             (rest shifted))
                 spliced (-> (mapv carry (take i literals))
                             (into resid)
                             (into (map carry) (drop (inc i) literals)))
                 [mixed fold slots] (collapse-repeats spliced)
                 ;; The child resumes rewriting at `i`, the first residual literal, except
                 ;; where a copy folded onto a literal left of that position.  The literal
                 ;; a copy folded onto carries a larger depth than the parent gave it, and
                 ;; a rewrite start to the right of that literal would never spend the
                 ;; difference.  A fold left of `i` also shortens the prefix, which moves
                 ;; the first residual literal one position left per fold; `fold` is at or
                 ;; below both indices, so one `min` covers the two.
                 rewrite-from (if fold (min (long i) (long fold)) (long i))]
          :when (not (restates-goal? kb context (res/substitute sentence b) depth from
                                     rewrite-from spliced mixed slots i (count resid)))
          :let  [[canon vm] (sx/canonical-conjunction (mapv :sentence mixed))
                 vm-inv (set/map-invert vm)]]
      {:literals     (mapv (fn [l s] (assoc l :sentence s)) mixed canon)
       :from         rewrite-from
       :answer-terms (push-terms answer-terms b vm-inv)
       :nvars        (count vm)
       ;; The goal this rewrite is answering, carried into the child's namespace so the
       ;; node that completes the argument can ask belief about the answer — the node
       ;; engine's version of `res/prove`'s defeat marker, arrived at the same way the
       ;; guards were: this is the last frame that still knows what was rewritten.
       ;; Recorded only for a goal belief could have defeated, so a KB with no
       ;; contradiction on that predicate carries an empty vector and no cost.
       :derived      (cond-> (mapv #(push-term % b vm-inv) derived)
                       (res/defeatable-goal? defeated sentence)
                       (conj (push-term sentence b vm-inv)))
       :guards       (cond-> (mapv (fn [g] (update g :terms push-terms b vm-inv)) guards)
                       guard (conj {:test  guard
                                    ;; the carrying rule — the guard's identity in
                                    ;; `node-key`, since the closure itself has none
                                    :rule  handle
                                    ;; the rule's own names, each pointing at the term it
                                    ;; stands for once the head has been unified
                                    :terms (push-terms (set/map-invert shift-back)
                                                       b vm-inv)}))
       :supports     (cond-> supports handle (conj handle))
       ;; the one rewrite that produced this child, in the *parent's* namespace — which
       ;; is the namespace the parent's own literals are written in, so a walk up
       ;; `:parent-id` replays the derivation without re-deriving anything.  One small
       ;; map per node against a node registry that already holds every node: the proof
       ;; is a read of the search's state rather than a second structure beside it.
       ;; `:push` is the same pair every other term here travels through — two map
       ;; references, no new allocation, and what lets a proof replay put every level of
       ;; the tree in one namespace instead of one per node.  `:slots` is the
       ;; collapse's map from each spliced position to the literal it landed on, nil
       ;; when nothing folded; `:arity` stays, since a nil `:slots` does not give it
       :rewrite      {:rule handle :at i :arity (count resid) :slots slots :goal sentence
                      :push [b vm-inv]}
       :tree-depth   (inc (long tree-depth))
       :context      context})))

;; ---- reading the proof back out ------------------------------------------

(defn- node-chain
  "`node` and every node above it, **root first** — one walk up `:parent-id`."
  [nodes node]
  (loop [n node, acc ()]
    (if-let [p (get nodes (:parent-id n))]
      (recur p (conj acc n))
      (vec (cons n acc)))))

(defn- rule-display
  "The rule sentex's sentence with the author's variable names back, for a proof to read
  the way it was written.  nil when the handle names nothing (a retracted rule)."
  [kb handle]
  (when-let [sx (and handle (p/get-sentex (:records kb) handle))]
    (sx/authored-sentence sx)))

(defn proof-tree
  "Why this node's conjunction follows: the derivation the search took, read back out of the
  state.  A vector, one tree per conjunct of the query:

      {:goal S :via :rule :rule <handle> :sentence <the rule, as written>
       :because [ <the same map, per antecedent> ]}
      {:goal S :via :leaf}                     a literal the search never rewrote

  `:because` reads as `core/why` does, but this reads a search about something merely derived
  and `why` reads the JTMS about something the KB holds.

  The proof is a replay of `:parent-id`: each node records the one rewrite that produced it
  (the rule, the literal index it replaced, how many antecedents it spliced in), so the replay
  starts with the root's conjuncts as leaves and turns one leaf per rewrite into a rule node.
  A literal stands for every leaf the collapse folded onto it, and the rewrite's `:slots` says
  where each spliced literal landed.  A leaf is a literal handed to the leaf solver, which
  reports bindings only, so no prover is recorded.  Sentences carry the node's canonical
  variables."
  [kb {:keys [nodes]} node]
  (let [ns    @nodes
        chain (node-chain ns node)
        ;; `forest` is the proof so far, one tree per conjunct; `paths` holds, per literal
        ;; of the *current* node, the leaves in it that literal stands for, so a rewrite
        ;; knows what to grow
        forest (mapv (fn [l] {:goal (:sentence l) :via :leaf})
                     (:literals (first chain)))
        paths  (mapv (fn [i] [[i]]) (range (count forest)))]
    (loop [forest forest, paths paths, cs (rest chain)]
      (if-let [c (first cs)]
        (let [{:keys [rule at arity slots goal push]} (:rewrite c)
              [b vm-inv] push
              at    (long at)
              arity (long arity)
              here  (nth paths at)
              lits  (:literals c)
              ;; each leaf being rewritten becomes a rule node — still in the *parent's*
              ;; namespace, like everything else in the forest
              node  (cond-> {:goal goal :via :rule :rule rule :because []}
                      rule (assoc :sentence (rule-display kb rule)))
              grown (reduce #(assoc-in %1 %2 node) forest here)
              ;; …then the whole forest moves into the child's, so one `?var0` means one
              ;; thing across the finished tree rather than one thing per level
              moved (walk/postwalk (fn [x]
                                     (if (and (map? x) (contains? x :goal))
                                       (update x :goal push-term b vm-inv)
                                       x))
                                   grown)
              landed (fn [j] (if slots (nth slots j) j))
              kids  (mapv (fn [k] {:goal (:sentence (nth lits (landed (+ at k)))) :via :leaf})
                          (range arity))
              ;; one entry per spliced position, then merged onto the literal each landed on
              spliced (-> (subvec paths 0 at)
                          (into (map (fn [k] (mapv #(into % [:because k]) here)))
                                (range arity))
                          (into (subvec paths (inc at))))]
          (recur (reduce #(assoc-in %1 (conj %2 :because) kids) moved here)
                 (if slots
                   (reduce-kv (fn [acc j ps] (update acc (nth slots j) into ps))
                              (vec (repeat (count lits) []))
                              spliced)
                   spliced)
                 (rest cs)))
        forest))))

;; ---- stepping ------------------------------------------------------------

(defn- rewritable?
  "Would any candidate rule's consequent unify with `sentence` in `context` — the unify
  half of `children`'s rewrite test, without building the residual.  `nvars` is the node's
  variable count, and the rule's consequent is shifted clear of the node's own `?varN`
  names by it before unifying, exactly as `children` shifts the whole rule: the two share
  the `?varN` namespace, so a plain unify would collide them and miss a rewrite a freshened
  one takes.  A truncation check asks only *whether* a rewrite was available, never carries
  one out, so the shifted consequent alone is enough."
  [kb sentence context nvars]
  (boolean (some (fn [rule]
                   (let [[shifted _] (sx/canonical-conjunction [(:consequent rule)] nvars)]
                     (res/subsuming-unify kb sentence (first shifted)
                                          res/no-bindings context)))
                 (provers/candidate-rules kb sentence context))))

(defn- depth-truncated?
  "Did the depth bound stop a rewrite this node would otherwise have taken?  True when a
  live literal — one `children` still considers, at index ≥ `:from` — is at depth 0, is
  not a deferred literal, and has a candidate rule that unifies.  That is the exact case
  `children`'s `(>= depth 1)` filter drops: a rewrite site the search reached and the
  bound refused.  Read only under `:track-truncation?`, so the candidate-rule probe never
  runs on the plain query path."
  [kb {:keys [literals from nvars]} context]
  (boolean
   (some (fn [{:keys [sentence depth]}]
           (and (< (long depth) 1)
                (not (sx/deferred-literal? sentence))
                (rewritable? kb sentence context nvars)))
         (subvec literals (long from)))))

(defn- node-solutions
  "The solutions `node`'s conjunction has against the leaf, past its guards and belief's
  defeats and in the asker's variables — realized, and with nothing recorded, so a
  `step!` stopped inside it leaves the session as it found it."
  [kb node context leaf-solver est-override defeated]
  (->> (solve-inline kb (mapv :sentence (:literals node)) context leaf-solver est-override)
       (filter (fn [s] (every? #(ask-guard % s) (:guards node))))
       (map res/resolve-bindings)
       ;; A rewrite above answered a goal; belief may already have decided
       ;; against that answer, and the proving levels agree with belief
       ;; (`res/defeated-answer?`).  Asked here rather than at the rewrite
       ;; for the guards' reason — this is the moment the argument is
       ;; complete — and skipped outright for a node with nothing recorded,
       ;; which is every node of a KB with no defeat in play.
       (remove (fn [s]
                 (and (seq (:derived node))
                      (some #(res/defeated-answer?
                               kb defeated (res/substitute % s) context)
                            (:derived node)))))
       ;; the node solves in its own namespace; `:answer-terms` says what
       ;; each of the asker's variables now stands for here, so reading the
       ;; answer out is resolving those terms and nothing more.  A rule's own
       ;; scratch variables are named by nothing in that map, which is the
       ;; whole of why they never reach an answer
       (map #(resolve-terms (:answer-terms node) %))
       vec))

(defn step!
  "Expand the cheapest node: solve its conjunction inline, claim and enqueue its children, and
  return the solutions it completed, a vector, empty when it completed none.  **nil** when the
  frontier is empty, the only exhaustion signal.

  Solutions are run past the node's guards, projected onto the query's variables and deduped
  against everything already returned.  A guard is asked here because the argument is
  complete here.  Whether the node produced anything is what the tactician's child bias reads
  (`tactics/child-bias`).  Under `:first-result?` a productive node builds no children.

  `dl` is the `System/nanoTime` instant a leaf's walk stops at (`budget/interruptible`; the
  1-arity has none).  A node the deadline stops inside goes back on the frontier as it was and
  the answer is `::budget/interrupted`.  A thread interrupted before the step throws
  `InterruptedException` and expands nothing."
  ([sess] (step! sess nil))
  ([{:keys [kb context queue nodes counter stats seen strategy leaf-solver est-override
            proof? defeated truncated unenumerated]
     :as sess}
    dl]
   ;; An interrupted thread stops here, between two expansions, with the session intact:
   ;; nothing else in the search reads the flag, and a cancelled future would otherwise
   ;; run its search to the depth bound.  `Thread/interrupted` clears the flag, as a
   ;; thrown `InterruptedException` does.
   (when (Thread/interrupted)
     (throw (InterruptedException. "the node engine's search was interrupted")))
   (let [q0 @queue]
     (when-let [[[_ _ id] q'] (queue-pop q0)]
       (reset! queue q')
       ;; One node expansion is one search step, so it is the scope the transitive-closure
       ;; memo and the held resident values belong to: the inline join below solves a literal
       ;; once per binding of its join variable, which is exactly the repetition the memo
       ;; collapses.  `sols` is reduced to a vector inside, so nothing lazy escapes.
       (observe/with-search-scope
         (let [node  (get @nodes id)
               ;; The depth bound's one silent failure mode, made observable: a rewrite
               ;; site this node reached and the bound refused (`depth-truncated?`).  Off
               ;; entirely unless the session asked for it, and skipped once a prior node
               ;; already found one — a report needs the bit set, not every place it was set.
               _     (when (and truncated (not @truncated) (depth-truncated? kb node context))
                       (reset! truncated true))
               found (budget/interruptible
                      dl #(binding [provers/*unenumerated* unenumerated]
                            (node-solutions kb node context leaf-solver est-override defeated)))]
           (if (identical? ::budget/interrupted found)
             (do (reset! queue q0) found)
             (let [;; Dedup keys on the **bindings**, with or without a proof: two
                   ;; derivations of one answer are one answer, and the proof returned is
                   ;; the first one found.  A caller wanting every derivation wants the
                   ;; search tree, not this seq.
                   sols (reduce (fn [acc s]
                                  (let [[old new] (swap-vals! seen conj s)]
                                    (if (identical? old new)
                                      acc
                                      (conj acc (if proof?
                                                  {:bindings s
                                                   :proof    (proof-tree kb sess node)}
                                                  s)))))
                                [] found)
                   paid (boolean (seq sols))
                   bias (tactics/child-bias strategy paid)]
               (when-not (and (:first-result? strategy) paid)
                 (doseq [kid (children kb node context defeated)]
                   (if (claim! sess (node-key kid))
                     (let [kid-id (swap! counter inc)
                           kid    (assoc kid :id kid-id :parent-id id)]
                       (swap! nodes assoc kid-id kid)
                       (swap! queue queue-push (+ (long (*estimate* kb strategy kid)) (long bias))
                              (frontier-key kid) kid-id))
                     (swap! stats update :dropped inc))))
               (swap! stats (fn [s] (-> s (update :expanded inc)
                                        (update :solutions + (count sols)))))
               sols))))))))

(defn search-seq
  "The session's solutions, lazily — one node expanded per pull, so a consumer that
  stops reading stops the search.  A node that completes nothing costs the consumer
  nothing but does advance the search: one pull runs `step!` until a node yields, so a
  wide unproductive stretch is inside one element.  A **deadline** therefore cannot be
  held between elements of this seq; `search-within` is the bounded drive."
  [sess]
  (lazy-seq
   (loop []
     (let [r (step! sess)]
       (cond
         (nil? r) nil
         (seq r)  (concat r (search-seq sess))
         :else    (recur))))))

(defn search-within
  "Drive `sess` under `budget` (`:max-ms` and `:max-results`) and return the partial-result
  contract `budget/collect` returns (`:results` / `:status` / `:count` / `:elapsed-ms` /
  `:resume`), the shape `core/prove-within` promises.

  The bounds are checked before every node expansion, so the deadline stops the drive within
  one expansion; `budget/collect` over `search-seq` would check only after a node yielded.  The
  session is the continuation: `:resume` drives it further under a fresh budget.  Solutions
  completed past a `:max-results` cap ride the continuation as `pending`.  The order of checks
  is `collect`'s: cap, deadline, then work.  The deadline also reaches a leaf's walk (`step!`'s
  `dl`); a node stopped there returns to the frontier and the continuation expands it with no
  deadline, so a resume loop under a fixed budget terminates."
  ([sess budget] (search-within sess budget [] false))
  ([sess budget pending unbounded-first?]
   (budget/check-budget! budget)
   (let [max-results (:max-results budget)
         dl          (budget/deadline budget)
         start       (System/nanoTime)]
     (loop [pending (vec pending), acc (transient []), unbounded? unbounded-first?]
       (cond
         (and max-results (>= (count acc) (long max-results)))
         (budget/from-batch (persistent! acc) :capped start
                            (fn [b] (search-within sess b pending unbounded?)))

         (and dl (>= (System/nanoTime) (long dl)))
         (budget/from-batch (persistent! acc) :timeout start
                            (fn [b] (search-within sess b pending unbounded?)))

         (seq pending)
         (recur (subvec pending 1) (conj! acc (nth pending 0)) unbounded?)

         :else
         (let [r (step! sess (when-not unbounded? dl))]
           (cond
             (nil? r)
             (budget/from-batch (persistent! acc) :complete start nil)

             (identical? ::budget/interrupted r)
             (budget/from-batch (persistent! acc) :timeout start
                                (fn [b] (search-within sess b [] true)))

             :else
             (recur (vec r) acc false))))))))

(defn- run-one
  "One search, under one strategy — the whole engine, and what every mode below drives.
  `:max-results` stops the search once that many solutions are in hand.  `:max-ms` drives
  it through `search-within`, and reaching the clock throws an ex-info carrying
  `::timeout`, which ends a portfolio race as any racer's throw does."
  [kb goals context opts]
  (let [sess (session kb goals context opts)]
    (if (:max-ms opts)
      (let [{:keys [results status elapsed-ms]}
            (search-within sess (select-keys opts [:max-ms :max-results]))]
        (when (= :timeout status)
          (throw (ex-info "the node engine's search reached its clock"
                          {::timeout true :elapsed-ms elapsed-ms})))
        results)
      (let [xs (search-seq sess)]
        (vec (if-let [n (:max-results opts)] (take n xs) xs))))))

(def default-racers
  "The tacticians a portfolio races when the caller names none: the shipped ordering, a
  dive, and level order.  Three orderings that disagree about everything, which is the
  only property a racer set needs."
  [:cost :depth-first :breadth-first])

(defn- answer-bindings
  "A `step!` solution's bindings, whether it came bare or wrapped beside a proof.  A
  binding map's keys are the query's variables, so `:bindings` names a slot only the
  wrapped shape has."
  [s]
  (if (and (map? s) (contains? s :bindings)) (:bindings s) s))

(defn portfolio-solutions
  "Race several tacticians over `goals` and return the union of their answers.

  Each racer is a complete search, so the union equals any single racer's answer set and the
  portfolio buys latency under a bound.  Incomplete strategies are refused, since
  `:first-result?` would enlarge the union.  A query writes nothing, so each racer touches
  its own session's atoms, and the shared literal cache is an atom whose worst case is
  duplicated work; no writing search (abduction) is reachable from here.  Each racer reads
  the belief the caller reads.  The union is deduped on the bindings, as `step!` is, since
  two racers that reach one answer differ only in the `:proof`."
  ([kb goals context] (portfolio-solutions kb goals context {}))
  ([kb goals context opts]
   (let [base   (tactics/strategy (get opts :strategy *strategy*))
         racers (get opts :racers default-racers)
         live?  (or observe/*live* (observe/hold-owner?))]
     (when-not (tactics/complete? base)
       (throw (ex-info (str "a portfolio races complete searches only — the strategy in"
                            " force sets :first-result? "
                            (pr-str (:first-result? base))
                            ", which stops the search rather than steering it.  Drop"
                            " :first-result? to race it, or run it on its own")
                       {:type :incomplete-racer :strategy base})))
     (let [states (mapv (fn [_] [(atom :new) (promise)]) racers)
           runs   (mapv (fn [t [state done]]
                          ;; `tactics/with-tactician`, not `assoc`: a normalized strategy
                          ;; carries all three signs, and `strategy` lets an explicit sign
                          ;; win over the tactician's — so re-pointing one by `assoc` would
                          ;; race three copies of the base ordering under three names
                          (future
                            (when (compare-and-set! state :new :running)
                              (try
                                (binding [observe/*handle-cache*            nil
                                          kb/*chain-authoritative-functors* nil
                                          observe/*write-record*            nil
                                          observe/*live*                    live?]
                                  (run-one kb goals context
                                           (assoc opts :strategy
                                                  (tactics/with-tactician base t))))
                                (finally (deliver done true))))))
                        racers states)]
       ;; a racer that throws ends the race, and the rest are cancelled, since nothing would
       ;; consume their answers.  A caller reading live belief also waits for each started
       ;; racer to stop, so none reads that belief after the caller writes again
       (try
         (first (reduce (fn [[acc seen] s]
                          (let [k (answer-bindings s)]
                            (if (contains? seen k)
                              [acc seen]
                              [(conj acc s) (conj seen k)])))
                        [[] #{}]
                        (mapcat deref runs)))
         (catch Throwable t
           (run! future-cancel runs)
           (when live?
             (doseq [[state done] states]
               (when-not (compare-and-set! state :new :skipped) @done)))
           (throw t)))))))

(defn solutions
  "Every solution of `goals` in `context`, as `prove` returns them — a vector of binding
  maps over the query's variables, deduped.

  `opts` carries `:max-depth`, the `:strategy` (`tactics/strategy`), `:portfolio?` to
  race the default racers instead of running one ordering, and `:auto?` to let
  `tactics/auto-strategy` pick from the structure of the query.  An explicit `:strategy`
  answers `:auto?`, so naming one turns the probe off.  `:max-results` caps the answer
  at that many, and every racer's run too, for an existence question
  (`core/query?`, `core/provable?`), which reads only whether the vector is empty.

  Neither `:portfolio?` nor an `:auto?` that picks one is an **anytime** mode: a race is
  driven to completion before it can be unioned, so it has no partial answer to give.
  `core/prove-within` drives `search-seq` directly and is unaffected."
  ([kb goals context] (solutions kb goals context {}))
  ([kb goals context opts]
   (let [pick (when (and (:auto? opts) (not (:strategy opts)))
                (tactics/auto-strategy kb goals context (required-depth (:max-depth opts))))
         opts (cond-> opts (and pick (not= :portfolio pick)) (assoc :strategy pick))]
     (cond->> (if (or (:portfolio? opts) (= :portfolio pick))
                (portfolio-solutions kb goals context opts)
                (run-one kb goals context opts))
       (:max-results opts) (into [] (take (:max-results opts)))))))

(defn tree-stats
  "The search tree as data once (or while) it is running: how many nodes were built and
  expanded, how many arrivals the claimed-key set dropped, how many solutions were
  completed, and how deep the rewriting went."
  [{:keys [nodes claimed stats queue]}]
  (let [ns (vals @nodes)]
    (merge @stats
           {:nodes     (count ns)
            :claimed   (count @claimed)
            :frontier  (count @queue)
            :max-depth (reduce max 0 (map :tree-depth ns))})))

(defn unenumerated
  "`sess`'s collector as `provers/unenumerated-report`'s two keys: `:unenumerated`, the
  transitive predicates whose closure a both-open goal in the search did not enumerate,
  and `:unenumerated-in-guards`, those of them recorded inside an `unknown` or
  `exceptWhen` evaluation, where the missed pair can admit an answer (docs/inference.md)."
  [sess]
  (provers/unenumerated-report (:unenumerated sess)))

(defn search-report
  "One node-engine search over `goals`, driven to completion and reported:

      {:answers                 <vector of binding maps, `solutions`' own>
       :truncated?              <bool>   the depth bound stopped a rewrite the search would
                                         otherwise have taken; `false` with an empty
                                         `:unenumerated` means every answer within the bound
       :timeout?                <bool>   `opts`' `:max-ms` passed before the frontier emptied
       :time-to-first-answer-ms <double|nil>   nil when there are no answers
       :total-time-ms           <double>
       :stats                   <tree-stats>
       :unenumerated            <vector>  the transitive predicates a goal asked with both
                                          arguments open (`provers/*unenumerated*`)
       :unenumerated-in-guards  <vector>  the subset recorded inside an `unknown` or
                                          `exceptWhen` evaluation (`unenumerated`)}

  `:truncated?` is conservative: `true` means a branch was stopped at the bound, and a shallower
  branch may have answered it.  It drives `solutions`' single-strategy run (`:auto?` picks
  one ordering, never a race) with `:track-truncation?` on."
  [kb goals context opts]
  (let [pick (when (and (:auto? opts) (not (:strategy opts)))
               (tactics/auto-strategy kb goals context (required-depth (:max-depth opts))))
        opts (cond-> (assoc opts :track-truncation? true)
               (and pick (not= :portfolio pick)) (assoc :strategy pick))
        sess (session kb goals context opts)
        dl   (budget/deadline opts)
        start (System/nanoTime)
        done (fn [acc first-ns timeout?]
               (merge {:answers                 (persistent! acc)
                       :truncated?              (boolean (some-> (:truncated sess) deref))
                       :timeout?                timeout?
                       :time-to-first-answer-ms (when first-ns (/ (double first-ns) 1e6))
                       :total-time-ms           (/ (double (- (System/nanoTime) start)) 1e6)
                       :stats                   (tree-stats sess)}
                      (unenumerated sess)))]
    (loop [acc (transient []), first-ns nil]
      (let [r (if (and dl (>= (long (budget/now)) (long dl))) ::budget/interrupted (step! sess dl))]
        (cond
          (nil? r)                              (done acc first-ns false)
          (identical? ::budget/interrupted r)   (done acc first-ns true)
          (empty? r)                            (recur acc first-ns)
          :else (recur (reduce conj! acc r) (or first-ns (- (System/nanoTime) start))))))))

;; ---- the search as data, for a debugger ----------------------------------

(def default-node-budget
  "How many node expansions `search-tree` drives before it stops and reports the tree
  **bounded**.  This bounds the *work*, and it is separate from any cap the caller later
  puts on the *render*: a depth bound alone does not stop a wide frontier — a converging
  rule graph builds one well inside its depth — so an enormous KB could otherwise turn one
  debug read into an unbounded search.  A run that hits this has not lost answers the way
  a depth bound does; it has only stopped drawing the tree past the budget."
  2000)

(defn- node-data
  "One finished node as serializable data: its id and parent, how deep in the tree it sits,
  the itemized estimate that ordered it (`tactics/estimate-breakdown`), the one rewrite
  that produced it (nil for the root — the literal it replaced, the rule handle, and the
  rule as written), the answers that came off it, and how many guards it carries.  Read
  out of the node the search already built — no second structure beside it."
  [kb strat results node]
  (let [{:keys [id parent-id tree-depth rewrite guards]} node]
    (cond-> {:id         id
             :parent-id  parent-id
             :tree-depth tree-depth
             :estimate   (tactics/estimate-breakdown kb strat node)
             :results    (mapv answer-bindings (get results id))
             :guards     (count guards)}
      rewrite (assoc :rewrite {:goal     (:goal rewrite)
                               :rule     (:rule rewrite)
                               :sentence (rule-display kb (:rule rewrite))}))))

(defn- finish-tree
  [kb sess strat goals answers results status]
  (merge
   {:goals    (vec goals)
    :context  (:context sess)
    :strategy (:tactician strat)
    :status   status
    :bounded? (not= :complete status)
    :answers  answers
    :nodes    (mapv #(node-data kb strat results %) (sort-by :id (vals @(:nodes sess))))
    :stats    (tree-stats sess)}
   (unenumerated sess)))

(defn search-tree
  "Run a bounded backward search for `goals` in `context` and return the tree the run built,
  every node the frontier reached, as plain data a client can render without holding the
  session.  The read behind the inference debugger.

  The work is bounded by `:max-depth` (required), a node-expansion budget (`:node-budget`,
  `default-node-budget`) and a wall-clock `:max-ms` that reports `:timeout`.  Pass the same
  `:leaf-solver` / `:est-override` as `query`.

  Returns `{:goals :context :strategy :status :bounded? :answers :nodes :stats :unenumerated
  :unenumerated-in-guards}`.  `:status` is `:complete`, `:bounded` (the node budget) or
  `:timeout`.  `:answers` are `query`'s under `:proof? true`, each tagged with the `:node` it
  came off.  `:nodes` is every node as `node-data`, in allocation order.  Read-only
  (`portfolio-solutions`)."
  ([kb goals context] (search-tree kb goals context {}))
  ([kb goals context {:keys [node-budget max-ms] :as opts}]
   (let [sess     (session kb (vec goals) context (assoc opts :proof? true))
         strat    (:strategy sess)
         queue    (:queue sess)
         budget   (long (or node-budget default-node-budget))
         deadline (when max-ms (+ (System/currentTimeMillis) (long max-ms)))]
     (loop [answers [], results {}, expanded 0]
       (let [entry (first @queue)]
         (cond
           (nil? entry)
           (finish-tree kb sess strat goals answers results :complete)

           (>= expanded budget)
           (finish-tree kb sess strat goals answers results :bounded)

           (and deadline (>= (System/currentTimeMillis) (long deadline)))
           (finish-tree kb sess strat goals answers results :timeout)

           :else
           ;; a frontier entry is `[estimate content id]`, and the tree is keyed by node
           (let [nid  (long (nth entry 2))
                 sols (step! sess)]
             (if (nil? sols)
               (finish-tree kb sess strat goals answers results :complete)
               (recur (into answers (map #(assoc % :node nid)) sols)
                      (cond-> results (seq sols) (assoc nid sols))
                      (inc expanded))))))))))

(def default-compare-tacticians
  "The tacticians `compare-tacticians` runs when the caller names no subset: the shipped
  default and three orderings that disagree with it and each other.  Enough spread to show
  the answer set is the *same* across genuinely different searches — the property the page
  asserts rather than assumes."
  [:ground-first :cost :depth-first :breadth-first])

(defn- compare-row
  [t sess answers status ms]
  (let [u (unenumerated sess)]
    (merge (tree-stats sess)
           u
           {:tactician t
            :status    (if (and (= :complete status) (seq (:unenumerated u))) :incomplete status)
            :ms        ms
            :answers   (into #{} (map answer-bindings) answers)})))

(defn compare-tacticians
  "Run `goals` in `context` under each of several tacticians, each to completion (bounded),
  and return one row per tactician: its search (`tree-stats`), its wall-clock `:ms`, its
  `:status` and its `:answers` set.  Every tactician reorders the frontier of a complete search,
  so the answer sets must be identical, and a differing row is a bug the completeness sweep says
  cannot happen.  `:first-result?` is a strategy flag and no row carries it.

  Bounded as `search-tree` is: `:node-budget` per run, and an optional `:max-ms`, one
  deadline for the whole call, so a row it reaches reports `:timeout` and the rows after
  it run no node.  A tactician named twice runs once.  Pass `query`'s `:leaf-solver` /
  `:est-override`."
  ([kb goals context] (compare-tacticians kb goals context {}))
  ([kb goals context {:keys [tacticians node-budget] :as opts}]
   (let [ts       (distinct (or (seq tacticians) default-compare-tacticians))
         budget   (long (or node-budget default-node-budget))
         deadline (budget/deadline opts)]
     (mapv
      (fn [t]
        (let [sess     (session kb (vec goals) context (assoc opts :strategy t :proof? false))
              queue    (:queue sess)
              t0       (System/currentTimeMillis)
              elapsed  (fn [] (- (System/currentTimeMillis) t0))]
          (loop [answers [], expanded 0]
            (let [entry (first @queue)]
              (cond
                (nil? entry)
                (compare-row t sess answers :complete (elapsed))

                (>= expanded budget)
                (compare-row t sess answers :bounded (elapsed))

                (and deadline (>= (long (budget/now)) (long deadline)))
                (compare-row t sess answers :timeout (elapsed))

                :else
                (let [sols (step! sess)]
                  (if (nil? sols)
                    (compare-row t sess answers :complete (elapsed))
                    (recur (into answers sols) (inc expanded)))))))))
      ts))))
