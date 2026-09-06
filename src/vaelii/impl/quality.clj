;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.quality
  "Readings about the **knowledge**, where the rest of the instrumentation reads the
  engine — `readings` below is the roster, and what each one asks is: which rules never fire, how skewed the predicate extents are, how deep the rule
  graph's chains reach, how much of the taxonomy is connected to anything, which argument
  declarations name a position their predicate does not have, which rules another rule
  already covers, and which rule pairs would contradict each other if both fired.

  `settle-stats` and `chain-stats` answer *how the engine ran*.  These answer *whether the
  knowledge is any good*, which is the question the author of a large KB has and the one
  nothing else here asks.  None of it is a gate: a threshold on somebody's ontology is not
  a build failure, and `lein perf` gates the engine while this reports on the content.

  **Every reading comes off state that already exists, and nothing new is indexed.**  A
  `rule -> firings` index would be a second copy of the JTMS adjacency to keep in step,
  which is the failure class the taxonomy's single `:support` map exists to avoid.  So the
  cost is
  `O(terms + rules + firings + ancestor pairs + declarations × super-predicates
  + candidate rule pairs)` and never
  `O(sentexes)` — the **vocabulary and the rule set**, which on a KB of a million facts
  about a hundred individuals is a hundred-odd names and a few hundred rules.  **Ancestor
  pairs and not edges**, which is the term
  worth spelling out: `taxonomy-coverage` reads each type's whole `genl` up-closure to find
  the root, so a chain of V types costs Θ(V²) where it has V−1 edges.  Vocabulary-sized on
  any ontology anybody writes, which is the claim that matters, and not an edge count:

  - **One walk over the term roster**, and one is the number: the functor names come off it
    by filter, and the type-shaped names come off *those* rather than off the roster a
    second time.  Measured at 8x the terms for 8x the cost, so the walk is the term the
    formula above leads with.
  - **Three O(1) index reads per functor name** — the stored extent off the count-aware
    trie, and the rule postings *both* ways.  That is everything the extent and chain
    readings need, and it is where the rule handles come from, so nothing on this pass
    reaches the record store at all — the record reads are the listed rules' and the two
    rule-hygiene readings' below.
  - **The firing census reads each rule's own `:consequences` adjacency**, the candidate
    set `jtms/restrength-informant*` uses, and never scans the justification map.  At
    11.5M justifications that difference is the report existing or not.
  - **The chain depth condenses strongly-connected components first.**  A KB's rule graph
    is cyclic in the ordinary case — `(genl ?a ?b) & (genl ?b ?c) => (genl ?a ?c)` alone
    makes it so — so memoizing a *path* re-explores the reachable subgraph along every one
    of them.  Memoize the component.
  - **The declaration census enumerates the declarations** and asks each what binds its own
    predicate's length, rather than asking every predicate what declares it.  That is a map
    read where the predicate carries a length of its own and one arity read per
    super-predicate where it inherits one, which is the `× super-predicates` above and the
    one term of the formula that is not flat.  It is also the second reader of the record
    store, for the declarations themselves — vocabulary, and therefore few.
  - **The two rule-hygiene readings are the third**, and the one that reads a record per
    *rule*: a rule's antecedents, its consequent and its four availability slots live on
    the record and nowhere else, so `+ rules + candidate pairs` is what they add.  A pair
    is a candidate only where the consequent index says one rule could conclude what the
    other does, and the two properties they read are gated on the KB declaring any
    (`marked-groups`), so a KB whose rules conclude different things pays the grouping and
    stops.

  Every count is of what is **stored**.  A believed extent is O(n) per predicate
  (`vaelii.core/count-with-functor` says why), which would turn an O(predicates) report
  into an O(sentexes) one — and stored-vs-believed is exactly the distinction an author
  wants to see rather than have chosen for them.  Two readings consult belief anyway: the
  firing census, because \"fired and every conclusion defeated\" is a category and not a
  rounding error, and the declaration census, because a disbelieved declaration constrains
  nothing for a reason that has nothing to do with the position it names.  The two
  rule-hygiene readings are as-stored about the *rules* and belief-following about the
  *declarations* they read, which `rules read against each other` below argues."
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]))

(def default-limit
  "How many rules and how many heavy predicates the report lists before it says it
  truncated.  A cap rather than the whole set because the *counts* are the headline and a
  30,000-entry list is not one; `:limit` raises it."
  25)

(def ^:private progress-every
  "How many predicates or rules a phase covers between `:on-progress` calls.  Low enough
  that a cancel lands promptly on a corpus-sized vocabulary, high enough that the callback
  is not the cost of the pass."
  4096)

;; ---- the vocabulary pass -------------------------------------------------
;; One walk, and the three readings that come off it.  A rule is enumerated from the rule
;; index rather than by scanning the records: `index-rule-sentex` posts every rule under
;; all of its antecedent predicates and its consequent predicate, whatever its direction,
;; so probing both ways over the functor names finds every rule the index can key.

(defn- functor-name?
  "Could `t` be the functor of a literal?  Every predicate and every type name is
  lowercase-initial (`docs/naming.md`), and nothing else may head a literal, so this is
  the filter that keeps the pass to a few reads per *predicate* instead of per term."
  [t]
  (and (symbol? t) (or (nm/predicate? t) (nm/type-symbol? t))))

(defn- vocabulary-pass
  "The stored extent per predicate, plus `rule -> antecedent predicates` and
  `rule -> consequent predicate`, in one walk over the vocabulary's functor names.

  `:type-names` rides along: every type-shaped name is lowercase-initial and so is already
  in this filter's answer, which is what keeps the taxonomy reading from walking the term
  roster a second time — the roster is the report's one superlinear term and it is walked
  once.

  **Every read here is an as-stored one, and both halves need to be.**  The extent is a
  cardinality, which the index answers and belief cannot narrow without a walk per
  predicate — the skew reading is about how the *knowledge* is shaped, not about what
  survived the last settle.  The rule postings are as-stored for a sharper reason: what
  `firing-census` sorts them into is *never fired* and *fired with every conclusion
  defeated*, so a believed entry point would drop from the census exactly the rules the report
  exists to name, and the two counts beside them would come back zero on the KB with the
  most to answer for."
  [kb progress!]
  (let [idx   (:index kb)
        preds (into [] (filter functor-name?) (reads/stored-terms idx))
        total (count preds)]
    ;; before the loop, so a phase with nothing in it still reports itself — a caller
    ;; watching the phases is watching for where a long report is, and \"skipped because
    ;; empty\" and \"not reached\" must not read the same
    (progress! {:phase :extents :done 0 :total total})
    (loop [i 0, extents (transient {}), ante (transient {}), conseq (transient {})]
      (if (= i total)
        {:predicates total
         :type-names (into #{} (filter nm/type-symbol?) preds)
         :extents    (persistent! extents)
         :ante       (persistent! ante)
         :conseq     (persistent! conseq)}
        (let [pred (nth preds i)
              n    (reads/stored-count-with-functor idx pred)]
          (when (and (pos? i) (zero? (mod i progress-every)))
            (progress! {:phase :extents :done i :total total}))
          (recur (inc i)
                 (if (pos? n) (assoc! extents pred n) extents)
                 (reduce (fn [m h] (assoc! m h (conj (get m h #{}) pred)))
                         ante (reads/as-stored-rules-by-antecedent idx pred))
                 (reduce (fn [m h] (assoc! m h pred))
                         conseq (reads/as-stored-rules-by-consequent idx pred))))))))

;; ---- which rules never fire ----------------------------------------------

(defn- rule-line
  "A listed rule as something an author can read: its handle, the sentence as *written*
  (a rule is stored canonically numbered, which reads as gibberish), and its context."
  [kb h]
  (when-let [sx (p/get-sentex (:records kb) h)]
    {:handle   h
     :sentence (if-let [vm (:varmap sx)]
                 (sx/originalize (:sentence sx) vm)
                 (:sentence sx))
     :context  (:context sx)}))

(defn- signature
  "A rule's **content** key: its consequent predicate and its antecedent predicates
  sorted, both read off the vocabulary pass and neither of them a record read.

  What the listed sets are ranked on, because a handle is assertion order and ranking on
  one would make the capped list a function of the order the author happened to write the
  rules in — the same knowledge loaded differently would list different rules under the
  same counts.  Two rules can share a signature (the pass knows their predicates, not
  their shape), and `rule-line-order` breaks exactly those ties."
  [pass h]
  [(str (get-in pass [:conseq h]))
   (str/join "," (sort (map str (get-in pass [:ante h] #{}))))])

(defn- rule-line-order
  "`handles` in content order, as rendered lines, capped at `limit`.

  The signature ranks them for free.  Where several rules share one — the tie the
  vocabulary pass cannot see through — the sentences themselves decide, and **only those
  are fetched**: a group of one is already ordered, so the record store is still read for
  the listed rules plus whichever share a signature with them, never for every rule in the
  set."
  [kb pass handles limit]
  (->> handles
       (group-by #(signature pass %))
       (sort-by key)
       (mapcat (fn [[_ hs]]
                 (if (next hs)
                   ;; the context joins the key: one implication stated in two contexts
                   ;; shares sentence and signature, and the residual tie fell to the
                   ;; handle set's iteration order — ahead of the `take limit` cap.
                   ;; `print-key`, not a bare `pr-str`: an ambient `*print-length*`
                   ;; elides two long sentences to one prefix and the tie falls back to
                   ;; handle order (naming.clj says why).  Decorated, so the record
                   ;; store is read once per rule and not once per comparison.
                   (nm/sort-by-content-key
                    (fn [h] (let [rl (rule-line kb h)]
                              [(nm/print-key (:sentence rl)) (nm/name-key (:context rl))]))
                    compare
                    hs)
                   hs)))
       (take limit)
       (into [] (keep #(rule-line kb %)))))

(defn- firing-census
  "Sort every rule handle into one of three categories by reading its node's dependents:
  never fired, fired with every conclusion defeated, or live.

  The listed handles are capped at `limit` and taken in **content order**
  (`rule-line-order`), never in handle order: a handle is assertion order, so ranking on
  one would make the listed subset a function of the order the rules were written in while
  the counts beside it are not — two loads of the same knowledge reporting the same totals
  over different examples."
  [kb pass handles limit progress!]
  (let [tms   (:tms kb)
        hs    (vec handles)
        total (count hs)]
    (progress! {:phase :rules :done 0 :total total})
    (loop [i 0, never [], defeated [], fired 0, firings 0]
      (if (= i total)
        (let [listed (fn [hs] (rule-line-order kb pass hs limit))]
          {:total              total
           :never              (listed never)
           :never-count        (count never)
           :all-defeated       (listed defeated)
           :all-defeated-count (count defeated)
           :fired              fired
           :firings            firings
           :truncated?         (boolean (or (> (count never) limit)
                                            (> (count defeated) limit)))})
        (let [h    (nth hs i)
              js   (into [] (comp (keep #(jtms/justification tms %))
                                  (filter #(= h (:informant %))))
                         (jtms/dependents tms h))
              live (count (filter #(jtms/in? tms (:consequence %)) js))]
          (when (and (pos? i) (zero? (mod i progress-every)))
            (progress! {:phase :rules :done i :total total}))
          (recur (inc i)
                 (if (empty? js) (conj never h) never)
                 (if (and (seq js) (zero? live)) (conj defeated h) defeated)
                 (if (pos? live) (inc fired) fired)
                 (+ firings (count js))))))))

;; ---- how skewed the extents are ------------------------------------------

(defn- gini
  "The Gini coefficient over the extent sizes: 0.0 when every predicate holds the same
  number, rising towards 1 as one holds everything (exactly `(n-1)/n` at that limit, so a
  small vocabulary cannot reach 1).  The single number that goes in a baseline; the
  buckets are what an author reads."
  [counts]
  (let [xs (vec (sort counts))
        n  (count xs)
        s  (reduce + 0 xs)]
    (if (or (zero? n) (zero? s))
      0.0
      (double (/ (- (* 2 (reduce + 0 (map-indexed (fn [i x] (* (inc i) x)) xs)))
                    (* (inc n) s))
                 (* n s))))))

(defn- extent-skew
  "Buckets by order of magnitude, a Gini, and the heaviest predicates.  Ties among the
  heaviest break on the **name**, so the list is the same however the KB was loaded."
  [pass limit]
  (let [extents (:extents pass)
        xs      (vec (vals extents))]
    {:predicates  (:predicates pass)
     :with-extent (count xs)
     :stored      (reduce + 0 xs)
     :gini        (gini xs)
     :buckets     (frequencies (map #(long (Math/floor (Math/log10 (double %)))) xs))
     :heaviest    (into [] (comp (map (fn [[pred n]] [pred n])) (take limit))
                        (sort-by (juxt (comp - val) (comp nm/print-key key)) extents))}))

;; ---- how deep the chains reach -------------------------------------------

(defn- rule-graph
  "consequent functor -> the antecedent functors of every rule concluding it."
  [{:keys [ante conseq]}]
  (reduce-kv (fn [g h c] (update g c (fnil into #{}) (get ante h #{})))
             {} conseq))

(defn- sccs
  "Tarjan's strongly-connected components, iterative — the recursive spelling overflows
  the stack on a graph a rule set is entitled to have.  Returns a vector of node sets."
  [g]
  (let [nodes (into #{} (concat (keys g) (mapcat val g)))]
    (loop [stack (vec nodes), idx {}, low {}, on #{}, s [], out [], counter 0, work []]
      (cond
        (seq work)
        (let [[v state] (peek work)]
          (case state
            :enter
            (if (contains? idx v)
              (recur stack idx low on s out counter (pop work))
              (recur stack (assoc idx v counter) (assoc low v counter) (conj on v)
                     (conj s v) out (inc counter)
                     (into (conj (pop work) [v :exit])
                           (map (fn [w] [w :enter])) (get g v #{}))))
            :exit
            (let [lo  (reduce (fn [a w] (if (contains? on w)
                                          (min a (get low w (get idx w)))
                                          a))
                              (get low v) (get g v #{}))
                  low (assoc low v lo)]
              (if (= lo (get idx v))
                (let [[component s'] (split-with #(not= % v) (reverse s))
                      component      (conj (vec component) v)]
                  (recur stack idx low (reduce disj on component)
                         (vec (reverse (rest s'))) (conj out (set component)) counter (pop work)))
                (recur stack idx low on s out counter (pop work))))))
        (seq stack)
        (recur (pop stack) idx low on s out counter [[(peek stack) :enter]])
        :else out))))

(defn- component-depths
  "Longest path to a leaf, per condensed component, on an **explicit** stack: the
  recursive spelling stack-overflows just past a thousand-deep chain, which a rule graph
  is entitled to have.  The condensation is a DAG, so this terminates on a cyclic input —
  which is the ordinary input."
  [cg ids]
  (loop [todo (vec ids), depths {}]
    (if-let [c (peek todo)]
      (if (contains? depths c)
        (recur (pop todo) depths)
        (let [ss     (get cg c)
              undone (into [] (remove #(contains? depths %)) ss)]
          (if (seq undone)
            (recur (into todo undone) depths)
            (recur (pop todo)
                   (assoc depths c (if (seq ss) (inc (reduce max 0 (map depths ss))) 0))))))
      depths)))

(defn- chain-depth
  "Depth per rule — the depth of the component its consequent functor lands in — as a
  histogram plus the fraction of rules in a chain at least that deep, which is the reading
  a single number loses: most rules can sit at depth 1 while one outlier reaches 7."
  [pass progress!]
  (progress! {:phase :chains :done 0 :total (count (:conseq pass))})
  (let [g      (rule-graph pass)
        comps  (sccs g)
        k      (count comps)
        ;; the condensation is keyed by a component **id**, not by the component itself:
        ;; two node sets compare equal in O(nodes), and the `remove` below runs one such
        ;; comparison per edge — which is how an O(V+E) pass turns into O(V*E) and reads as
        ;; a second, quieter version of the memoize-the-path mistake (measured: 1,146ms to
        ;; 36ms on a 4,000-functor cycle)
        of     (into {} (for [i (range k), node (nth comps i)] [node i]))
        cg     (reduce (fn [m i]
                         (assoc m i (into #{} (comp (mapcat #(get g % #{}))
                                                    (keep of)
                                                    (remove #(= % i)))
                                          (nth comps i))))
                       {} (range k))
        depths (component-depths cg (range k))
        ;; per rule, not per component: a component's depth is shared by every rule
        ;; concluding into it, and it is rules the author is asking about
        rules  (into [] (keep #(get depths (get of %))) (vals (:conseq pass)))
        n      (count rules)
        hist   (frequencies rules)
        deepest (reduce max 0 (keys hist))]
    {:functors   (count of)
     :components k
     ;; a self-loop is a cycle of one node, and `genl` transitivity is exactly that — so
     ;; counting only multi-node components would report the commonest cycle as acyclic
     :cyclic     (count (filter (fn [c] (or (> (count c) 1)
                                            (some #(contains? (get g % #{}) %) c)))
                                comps))
     :largest    (reduce max 0 (map count comps))
     :rules      n
     :depths     hist
     :at-least   (into (sorted-map)
                       (for [d (range 1 (inc deepest))]
                         [d (if (zero? n)
                              0.0
                              (double (/ (count (filter #(>= % d) rules)) n)))]))}))

;; ---- how much of the taxonomy is connected -------------------------------

(defn- taxonomy-coverage
  "Two numbers, not one: how many type names carry a `genl` edge at all, and how many
  reach the root.  A type with an edge into a disconnected island is counted by the first
  and not the second, and **the gap between them is the finding**.

  The root is *found*, not assumed — `thing` is this engine's and a converted corpus
  brings its own — so whatever type the most others reach is the one reported against, and
  the reading means the same on a corpus that never heard of `thing`.

  The denominator is every type-shaped name in the vocabulary, which by `docs/naming.md`
  includes a bare lowercase word (`likes` is a legal predicate *and* a legal type name).
  A unique declared arity other than one excludes a known non-unary predicate; unknown
  or conflicting arities remain candidates rather than hiding disconnected type islands.
  That is why the gap is the finding rather than either fraction on its own.

  Reachability is **reflexive**, as `genls` is: the root reaches itself, so `:rooted`
  counts it and `:islands` is exactly the edged types outside the root's ancestor set."
  [kb pass progress!]
  (let [taxo  (:taxonomy kb)
        ;; Memoized: the reach walk below asks this once per node AND once per ancestor
        ;; of every node, which on the 124k-type conversion above is a few million calls
        ;; over a name set two orders of magnitude smaller.  Each call reads the
        ;; taxonomy atom and allocates, and the answer cannot move inside one reading.
        type-candidate? (memoize
                         (fn [name]
                           (let [arity (tax/declared-arity taxo name)]
                             (or (nil? arity) (= 1 arity)))))
        nodes (into #{} (filter type-candidate?) (tax/types taxo))
        named (into #{} (filter type-candidate?) (:type-names pass))]
    (progress! {:phase :taxonomy :done 0 :total (count nodes)})
    (let [reach (frequencies (mapcat #(filter type-candidate? (tax/genls-global taxo %)) nodes))
          [root rooted] (first (sort-by (juxt (comp - val) (comp nm/print-key key)) reach))]
      {:names   (count (into named nodes))
       :edged   (count nodes)
       :root    root
       :rooted  (or rooted 0)
       :islands (max 0 (- (count nodes) (or rooted 0)))})))

;; ---- declarations that constrain nothing ---------------------------------
;;
;; `(arg parentOf 3 person)` is admitted while `parentOf` has no declared length —
;; open-world, and the highest position a declaration names is a lower bound on the arity
;; rather than a claim about it.  Then a length arrives, by any of the three routes
;; `checks/declared-arity` reads, and the declaration is left constraining a position the
;; predicate provably does not have.  It is not refused: refusing it would make the
;; *binding's* arrival order decide what the KB holds.  It simply stops meaning anything,
;; while the entry point refuses the identical sentence one line later.
;;
;; A `variable_arity` predicate is the case where the length is not the last word, and the
;; entry point's arm releases it: such a predicate reads a tuple of any length from its declared
;; arity upward, so a position past that length is one its tuples really do reach.  Nothing
;; of its is listed here, however high the position, because nothing of its is stranded.
;;
;; **Here rather than in the settle ledger**, and the asymmetry with `arity` is the whole
;; argument.  A wrong-length *fact* is content an `assert` admitted because it could not
;; have known, so `settle/report-arity-reach!` says *newly* — only the settle knows that.
;; A stranded declaration is inert: it constrains nothing, refuses nothing and mints
;; nothing, and it reads the same an hour later as at the moment it went stale.  There is
;; no newly to report, so paying per write buys nothing a census does not give for free —
;; and a per-declaration ledger entry would compete for the 1,000 slots `violations` keeps
;; and log a `:warn` line each.  Measured: this walk is 0.008 ms at 32 declarations and
;; 0.103 ms at 512, against 3.3 ms for the per-predicate probes a settle-side sweep over a
;; 512-predicate subtree would have made.

(def ^:private declaration-functors
  "The argument constraints, in the order this walks them.  A vector rather than the
  roster in `checks`, because this is a walk order and that is a membership test."
  '[arg genlArg interArg])

(defn- stranded-declarations
  "Which argument constraints name a position their predicate does not have.

  **Enumerated, not probed per predicate.**  Declarations are vocabulary and vocabulary is
  small — the whole bundled ontology has 298 — so reading all of them and asking each
  about its own predicate is cheaper than asking each predicate what declares it, and it
  does not grow with the spec subtree underneath.  What it does grow with is the hierarchy
  *above*: `checks/declared-arity` is a map read for a predicate carrying a length of its
  own and a walk of the supers for one that inherits its length, so the reading is
  `O(declarations × super-predicates)` — the term the namespace's bound carries for it.

  Belief-filtered, unlike the extent counts beside it: a stored, disbelieved declaration
  constrains nothing for a reason that has nothing to do with its position, and listing it
  here would name the wrong defect.

  `:message` is the one `checks` wrote when it convicted, **carried rather than
  re-derived**: a caller reading this map and a caller reading `check`'s answer are told
  the same thing in the same words, and there is no second wording to drift from it.

  One membership reader per context met, for the reason `settle`'s sweep holds one — a
  reader memoizes for the life of one caller, so building one per declaration pays the
  retrieval every time and throws the memo away unread."
  [kb limit progress!]
  (let [reader (let [cache (volatile! {})]
                 (fn [ctx]
                   (or (get @cache ctx)
                       (let [r (kb/membership-reader kb ctx)]
                         (vswap! cache assoc ctx r)
                         r))))
        stored (into []
                     (comp (mapcat #(reads/as-stored-with-functor (:index kb) %))
                           (distinct)
                           (keep #(p/get-sentex (:records kb) %))
                           (filter #(= :positive (:polarity %)))
                           (filter #(jtms/in? (:tms kb) (:id %))))
                     declaration-functors)]
    (progress! {:phase :declarations :done 0 :total (count stored)})
    (let [found   (into []
                        (keep (fn [sx]
                                (let [ctx (:context sx)]
                                  (when-let [v (checks/arg-position-violation
                                                kb (:sentence sx) ctx (reader ctx))]
                                    {:handle    (:id sx)
                                     :sentence  (:sentence sx)
                                     :context   ctx
                                     :predicate (:predicate v)
                                     :position  (:position v)
                                     :arity     (:arity v)
                                     :via       (:via v)
                                     :message   (:message v)}))))
                        stored)
          ;; content order, so the listed set is a function of the vocabulary rather than
          ;; of the handle order the index walked
          ordered (nm/sort-by-content-key
                   (juxt (comp nm/print-key :sentence) (comp nm/print-key :context))
                   compare found)]
      {:total          (count stored)
       :stranded       (vec (take limit ordered))
       :stranded-count (count found)
       :truncated?     (> (count found) limit)})))

;; ---- rules read against each other ---------------------------------------
;;
;; The five readings above ask about a rule's relation to the **KB** — whether it fired,
;; how deep its chain runs.  The two below ask about a rule's relation to **another
;; rule**, which is the one question in the census that needs the rules themselves and
;; not their index postings: one record read per rule, and a unification per candidate
;; pair.  So these two add `O(rules + candidate pairs)` to the report and no term that
;; grows with what the KB stores.
;;
;; Read **as stored**, like the firing census and for its reason: a rule the KB currently
;; disbelieves is still a rule somebody wrote, and a redundancy in the text does not stop
;; being one while its support is defeated.  The declarations these readings consult —
;; `genl`, `disjoint`, `functional`, `asymmetric`, `genlCx` — do follow belief, because a
;; separation nobody believes separates nothing.
;;
;; A rule whose consequent functor is a **variable** is outside both: it concludes
;; whatever binds, so it would cover every rule in the KB and clash with every other,
;; which is a page of findings about one rule.

(defn- form-variables
  "Every variable anywhere in `form`, as a set."
  [form]
  (into #{} (filter sx/variable?) (tree-seq sequential? seq form)))

(defn- rule-variables
  "Every variable across a rule's patterns, **sorted by name** — so the renamings below
  are a function of the rule's content rather than of a set's iteration order, and two
  loads of the same KB report the same substitution."
  [forms]
  (sort (reduce into #{} (map form-variables forms))))

(defn- freezing
  "`[freeze unfreeze]` over a rule's variables: each replaced by a namespaced symbol no
  sentence can spell, and the map back.

  Subsumption is a **one-way match** — a substitution over the covering rule's variables
  alone — and `unify` binds in either direction.  Freezing the covered rule's variables
  into constants is what makes the two-way unifier run one way, without a second matcher
  to keep in step with the first."
  [forms]
  (let [m (into {}
                (map-indexed (fn [i v] [v (symbol "vaelii.impl.quality" (str "frozen" i))]))
                (rule-variables forms))]
    [m (into {} (map (fn [[v f]] [f v])) m)]))

(defn- restore
  "`form` with every term `m` names replaced.  `sentex/rename-vars` is the same walk for
  *variables* and answers nothing here: what a freeze put in the form is a constant, which
  is the whole point of freezing it, so unfreezing needs a walk that does not test for a
  `?`."
  [form m]
  (cond
    (contains? m form) (get m form)
    (vector? form)     (mapv #(restore % m) form)
    (sequential? form) (apply list (map #(restore % m) form))
    :else              form))

(defn- renaming
  "A rule's variables renamed apart from any other rule's.  Every stored rule is numbered
  `?var0 …` (docs/canonicalization.md), so unifying two of them untouched would join
  variables that share a name and nothing else."
  [forms]
  (into {}
        (map-indexed (fn [i v] [v (symbol (str "?other" i))]))
        (rule-variables forms)))

(defn- rule-view
  "One rule as these two readings read it: the decomposition off the record, the
  consequent split into polarity and body, and the sentence as its author wrote it."
  [sx]
  (let [conseq (:consequent sx)
        neg?   (sx/negation? conseq)
        body   (if neg? (second conseq) conseq)
        sent   (if-let [vm (:varmap sx)] (sx/originalize (:sentence sx) vm) (:sentence sx))]
    {:handle     (:id sx)
     :context    (:context sx)
     :varmap     (:varmap sx)
     :sentence   sent
     :sort-key   [(nm/print-key sent) (nm/print-key (:context sx))]
     :antecedent (vec (:antecedent sx))
     :consequent conseq
     :body       body
     :polarity   (if neg? :negative :positive)
     :functor    (nm/functor body)
     :arity      (nm/arity body)
     :direction  (:direction sx)
     :defeasible (boolean (:defeasible sx))
     :assumption (boolean (:assumption sx))
     :constraint (:constraint sx)}))

(defn- rule-views
  "Every rule the census enumerated, as a `rule-view` — the one record read per rule these
  readings pay, and the phase both of them are announced under.

  A negated implication and a variable-functor consequent are dropped here: the first
  concludes nothing to cover or clash with, and the second concludes anything."
  [kb handles progress!]
  (let [hs    (vec handles)
        total (count hs)]
    (progress! {:phase :subsumption :done 0 :total total})
    (loop [i 0, out (transient [])]
      (if (= i total)
        (persistent! out)
        (let [sx (p/get-sentex (:records kb) (nth hs i))
              v  (when (and sx (some? (:antecedent sx)) (= :positive (:polarity sx)))
                   (rule-view sx))]
          (when (and (pos? i) (zero? (mod i progress-every)))
            (progress! {:phase :subsumption :done i :total total}))
          (recur (inc i)
                 (if (and v (symbol? (:functor v)) (not (sx/variable? (:functor v))))
                   (conj! out v)
                   out)))))))

(defn- by-consequent
  "`[polarity functor] -> views` — the pruning index both readings pair over, and the
  reason neither is a cross product over the rule set."
  [views]
  (group-by (juxt :polarity :functor) views))

(defn- rule-exception-conjuncts
  "The `exceptWhen` conjunctions in force for a rule, or nil.  Gated on the watched-rule
  roster, so an ordinary rule — every rule, on nearly every KB — pays one O(1) membership
  read and no term lookup."
  [kb handle]
  (when (reads/watched-rule? (:index kb) handle)
    (seq (provers/rule-exceptions kb handle))))

;; ---- reading six: rules another rule already covers -----------------------

(def ^:private direction-covers
  "Which directions a rule of each direction can stand in for.  `:both` is the only one
  that covers a direction other than its own, and `:inert` covers nothing but `:inert`: a
  rule that chains in neither engine cannot stand in for one that does."
  {:both #{:both :forward :backward} :forward #{:forward} :backward #{:backward}
   :inert #{:inert}})

(defn- available-at-least?
  "Is `r1` at least as **available** as `r2` — could every firing of `r2` have been one of
  `r1`?  Four slots decide it, and each is a way one rule reaches where the other does
  not:

  - **direction**, since a `:forward` rule answers no backward goal;
  - **defeasibility**, since a default cannot stand in for a strict rule — its conclusion
    is defeated exactly where the strict one's stands;
  - **`assumption`** and **`constraint`**, since neither chains at all: each is a *choice*
    or a *nogood* for a solve (docs/solving.md) and part of the rule's identity.

  What it does not read is the rule sentex's own **strength**, which says how the rule is
  defeated rather than where it runs."
  [r1 r2]
  (and (contains? (get direction-covers (:direction r1) #{}) (:direction r2))
       (or (not (:defeasible r1)) (:defeasible r2))
       (= (:assumption r1) (:assumption r2))
       (= (:constraint r1) (:constraint r2))))

(defn- antecedents-covered
  "A binding extending `bindings` under which **every** literal of `generals` matches some
  literal of `specifics`, or nil.

  Backtracking, because which specific literal a general one takes decides what the next
  one can take — and an antecedent list is three or four literals, so the search is a
  handful of unifications rather than a cost.  `subsuming-unify` is the match, so a
  general literal on `P` is met by a specific one on a spec of `P` (docs/inference.md,
  predicate subsumption in matching)."
  [kb generals specifics bindings context]
  (if (empty? generals)
    bindings
    (some (fn [s]
            (when-let [b (res/subsuming-unify kb (first generals) s bindings context)]
              (antecedents-covered kb (rest generals) specifics b context)))
          specifics)))

(defn- readable-substitution
  "σ as an author reads it: the covering rule's own variable names bound to the covered
  rule's terms in *its* names.  Both sides are stored numbered, so the raw map is
  `{?var0 ?var1}` twice over and says nothing about either rule."
  [sigma r1 r2 unfreeze]
  (let [vm1 (or (:varmap r1) {})
        vm2 (or (:varmap r2) {})]
    (into (sorted-map)
          (map (fn [[v t]]
                 [(get vm1 v v)
                  (sx/rename-vars (restore (res/substitute t sigma) unfreeze) vm2)]))
          sigma)))

(defn- exceptions-covered?
  "Does `r2` carry every `exceptWhen` `r1` does?  An exception the covering rule carries
  and the covered one lacks is a case `r1` declines to conclude and `r2` concludes, so
  `r1` does not cover it.

  Compared as conjunct **sets** after σ, since an exception is stored in its own rule's
  canonical variable names and the two rules do not share them."
  [kb r1 r2 sigma unfreeze]
  (let [e1 (rule-exception-conjuncts kb (:handle r1))]
    (or (nil? e1)
        (let [e2 (into #{} (map set) (rule-exception-conjuncts kb (:handle r2)))]
          (every? (fn [c]
                    (contains? e2 (into #{}
                                        (map #(restore (res/substitute % sigma) unfreeze))
                                        c)))
                  e1)))))

(defn- subsumption
  "Does `r1` subsume `r2` — is there one substitution σ over `r1`'s variables with
  `ante(r1)σ ⊆ ante(r2)` and `conseq(r1)σ = conseq(r2)`?  σ as `readable-substitution`
  writes it, or nil.

  **Predicate-genl aware in both halves, and in opposite directions.**  An antecedent of
  `r1` on `P` is covered by an antecedent of `r2` on a *spec* of `P`, because whatever
  satisfies the spec satisfies `P` — `match1`'s fan, asked of a pattern instead of a
  fact.  A consequent of `r1` on a *spec* of `r2`'s covers it, because concluding the
  subtype answers every goal the supertype would; a consequent on a **super** does not
  cover, which is the half a reader expects to be symmetric and is not.  Both are
  `subsuming-unify`, which is where the direction lives.

  Asked from `r2`'s context, and `r1` must be visible there: a rule covered by one it
  cannot see is not covered.

  **`(count ante(r1)) > (count ante(r2))` is pruned**, and it is the one case the reading
  under-reports: σ may collapse two of `r1`'s antecedents onto one of `r2`'s, so a rule
  with more antecedents can still subsume.  A missing hit is the safe direction for a
  report that names redundancies."
  [kb r1 r2]
  (let [context (:context r2)]
    (when (and (not= (:handle r1) (:handle r2))
               (<= (count (:antecedent r1)) (count (:antecedent r2)))
               (available-at-least? r1 r2)
               (tax/sees? (:taxonomy kb) context (:context r1)))
      (let [[freeze unfreeze] (freezing (cons (:consequent r2) (:antecedent r2)))
            c2    (sx/rename-vars (:consequent r2) freeze)
            a2    (mapv #(sx/rename-vars % freeze) (:antecedent r2))
            b     (res/subsuming-unify kb c2 (:consequent r1) res/no-bindings context)
            sigma (when b (antecedents-covered kb (:antecedent r1) a2 b context))]
        (when (and sigma (exceptions-covered? kb r1 r2 sigma unfreeze))
          (readable-substitution sigma r1 r2 unfreeze))))))

(defn- covering-candidates
  "The rules that could cover `r2`: those concluding a **spec** of its consequent
  predicate, or — under a negation, where a `genl` edge carries the other way — a genl of
  it.  Scoped by `r2`'s context, which is the vantage the subsumption is claimed from, so
  an edge invisible there cannot make one rule cover another."
  [kb index r2]
  (let [tax   (:taxonomy kb)
        reach (if (= :negative (:polarity r2))
                (tax/genls tax (:functor r2) (:context r2))
                (tax/specs tax (:functor r2) (:context r2)))]
    (into [] (mapcat #(get index [(:polarity r2) %])) reach)))

(defn- subsumed-rules
  "Which stored rules another stored rule already covers.

  An exact duplicate cannot be here: two rules identical up to variable names, antecedent
  order or a symmetric argument order are **one handle** (docs/canonicalization.md).  So
  every hit is either a redundancy or a deliberate specialization — a rule written for the
  narrow case beside the general one — and **the reading cannot tell them apart**, because
  the difference is in what the author meant rather than in what the KB holds.  It names
  the pair and the substitution and leaves the judgement.

  Content-ordered on both loops, so the capped list is a function of the rules and not of
  the order they were written in."
  [kb views limit progress!]
  (let [index   (by-consequent views)
        ordered (nm/sort-by-content-key :sort-key compare views)
        total   (count ordered)
        found   (loop [i 0, out (transient [])]
                  (if (= i total)
                    (persistent! out)
                    (let [r2   (nth ordered i)
                          hits (into []
                                     (keep (fn [r1]
                                             (when-let [s (subsumption kb r1 r2)]
                                               {:subsumed     (:handle r2)
                                                :by           (:handle r1)
                                                :substitution s
                                                :context      (:context r2)
                                                :sentence     (:sentence r2)
                                                :by-sentence  (:sentence r1)})))
                                     (nm/sort-by-content-key
                                      :sort-key compare (covering-candidates kb index r2)))]
                      (when (and (pos? i) (zero? (mod i progress-every)))
                        (progress! {:phase :subsumption :done i :total total}))
                      (recur (inc i) (reduce conj! out hits)))))]
    {:total          total
     :subsumed       (vec (take limit found))
     :subsumed-count (count found)
     :truncated?     (> (count found) limit)}))

;; ---- reading seven: contradictions in waiting -----------------------------

(defn- renamed
  "`view` with its patterns renamed apart, for a pairing that unifies two rules rather
  than matching one against the other."
  [v]
  (let [m (renaming (cons (:consequent v) (:antecedent v)))]
    (assoc v
           :consequent (sx/rename-vars (:consequent v) m)
           :body       (sx/rename-vars (:body v) m)
           :antecedent (mapv #(sx/rename-vars % m) (:antecedent v))
           :rename     m)))

(defn- pair-context
  "The context a nogood between two rules could form in — a **common descendant** of the
  two, since a clash is a clash where both halves are visible (docs/nmtms.md, \"Which
  contexts can contradict each other\").  Asking only whether one sees the other would
  exempt every sibling pair.  nil when no context sees both, which is the pair that is not
  a finding: neither rule's conclusion is anywhere near the other's.  The least of the
  maxima by content, so the reported context does not depend on a set's iteration order."
  [kb a b]
  (nm/min-by-content-key
   nm/print-key compare
   ;; `into #{}` and not the set literal: two rules in one context is the ordinary case,
   ;; and `#{x x}` is a duplicate-key throw rather than a one-element set
   (tax/maximal-common-descendant-contexts
    (:taxonomy kb) (into #{} [(:context a) (:context b)]))))

(defn- functional-marks-by-position
  "`{1 #{pred …} 2 #{pred …}}` — the predicates carrying a functional-family mark on each
  position of a **binary** tuple, at or above `f`.

  `(functional P)` joins position 2, being `(functionalInArg P 2)` written the arity-2
  way.  A mark at position 3 or beyond appears in neither: it constrains a slot a binary
  literal does not have, and pairing two conclusions on a constraint neither is subject
  to would be a report about nothing.

  Split by position because the pairwise test is not symmetric in the two: the mark names
  the constrained slot, so position 2 unifies argument 1 and compares argument 2, and
  position 1 does the mirror.  One read of the table serves both."
  [tax f context]
  (let [inarg (tax/functional-in-arg-over tax f context)
        at    (fn [n] (into #{} (comp (filter #(= n (second %))) (map first)) inarg))]
    {1 (at 1)
     2 (into (at 2) (tax/props-over tax :functional f context))}))

(defn- marks-over
  "The predicates a `kind` mark reaches at or above `f`, as one set — **the one place the
  clash detector spells a mark's reach**, read by all three of the sites that need it.

  For `:asymmetric` that is `tax/props-over` and nothing more.  For `:functional` it is
  both spellings and **both positions a binary tuple has**, which is
  `functional-marks-by-position` unioned.

  A mark names the *constrained* slot and the rest of the tuple is its determinant, so on
  a binary conclusion position 2 is the familiar reading — subject in argument 1, value in
  argument 2 — and position 1 is its mirror, the subject in argument 2.  Only position 3
  and up are genuinely out of reach here, constraining a slot these literals do not have.

  Unioned rather than kept apart because this answers *candidate* questions: which pairs
  are formed and which groups a view joins.  An over-approximated candidate merely fails
  `consequent-clash` and yields nothing, where a missing one is never asked at all.  The
  pairwise test is the caller that has to know which position it is looking at, and it
  reads the split map directly.

  **Three callers, which is why this is a function and not three expressions.**  The
  reach is asked at the candidate gate (`marked-groups`, does the KB declare any and which
  group does a view join), at the lookup (`clash-partners`, which groups does this rule's
  functor reach) and at the pairwise test (`consequent-clash`, do these two share one).
  #56 was found and half-fixed twice before that was noticed: widening the pairwise test
  alone left the gate answering nil, and widening the gate too left the lookup finding no
  group.  A mark family reaches a pass through every one of its reads or through none."
  [tax kind f context]
  (if (= :functional kind)
    (let [by-pos (functional-marks-by-position tax f context)]
      (into (get by-pos 1) (get by-pos 2)))
    (tax/props-over tax kind f context)))

(defn- marks-declared?
  "Does the KB declare any `kind` mark at all — the O(1) gate `marked-groups` opens on,
  reading the same two rosters `marks-over` reads.

  The `:functional` arm is `tax/functional-family-declared?` rather than the `or` written
  out here, because that question — does the taxonomy hold a functional mark of *either*
  spelling — is asked by every entry point of the family (`special`'s three `equate-*` lanes as
  well as this pass), and spelling it per caller is what #52, #54 and #56 each were: one
  reader of a two-spelling family that had only learned one.  A third spelling joins the
  roster there and reaches all of them."
  [tax kind]
  (if (= :functional kind)
    (tax/functional-family-declared? tax)
    (boolean (seq (tax/props tax kind)))))

(defn- consequent-clash
  "How `a`'s consequent and `b`'s would clash if both rules fired — `[kind σ]`, or nil.
  `b`'s variables are renamed apart from `a`'s, so σ is over both.

  Four kinds, asked in a fixed order so a pair that answers to two — a predicate declared
  both `functional` and `asymmetric` — lands under one of them rather than under whichever
  a map iterated to first:

  - **`:negation`** — one concludes `S` and the other `(not T)` where `S` entails `T`.
    The genl fan runs one way here: `(dog X)` contradicts `(not (animal X))` and
    `(animal X)` does not contradict `(not (dog X))`.
  - **`:disjoint`** — two unary type conclusions about one term whose types a `disjoint`,
    `sibling_disjoint` or `disjoint_metatype` declaration separates.
  - **`:functional`** — two conclusions filling one functional slot for one subject with
    values that are not the same term.  The mark is read **up** the predicate hierarchy,
    so two `fatherOf` conclusions clash against `(functional parentOf)`, and it is read
    in **both** spellings: `(functionalInArg parentOf 2)` says the same thing about the
    same slot, so a detector reading only `:props` was blind to a KB that spells it that
    way (#56).  Read per **position**: the mark names the constrained slot, so a
    position-2 mark unifies the subjects and compares the values and a position-1 mark
    mirrors that, and only position 3 and up is out of reach — a slot these two literals
    do not have.
  - **`:asymmetric`** — one tuple concluded both ways round, under a predicate declared
    `asymmetric` anywhere above either.  A self tuple `(P a a)` is not one: the ontology
    admits it, so a σ identifying the two arguments is no clash."
  [kb a b context]
  (let [tax (:taxonomy kb)
        fa  (:functor a)
        fb  (:functor b)]
    (cond
      (not= (:polarity a) (:polarity b))
      (let [[pos neg] (if (= :positive (:polarity a)) [a b] [b a])]
        (when-let [s (res/subsuming-unify kb (:body neg) (:consequent pos)
                                          res/no-bindings context)]
          [:negation s]))

      (= :negative (:polarity a)) nil    ; two negations agree about everything

      :else
      (or
       (when (and (= 1 (:arity a)) (= 1 (:arity b)) (not= fa fb)
                  (tax/disjoint? tax fa fb context))
         (when-let [s (res/unify (second (:body a)) (second (:body b)))]
           [:disjoint s]))
       (when (and (= 2 (:arity a)) (= 2 (:arity b)))
         ;; Per position, because the mark names the CONSTRAINED slot and the rest of the
         ;; tuple is its determinant: a position-2 mark unifies the subjects and compares
         ;; the values, and a position-1 mark is that read in the mirror.  Reading
         ;; position 2 alone left `(functionalInArg P 1)` enforced by
         ;; `checks/functional-clashes` and invisible to this pass.
         (let [pa (functional-marks-by-position tax fa context)
               pb (functional-marks-by-position tax fb context)
               [s1 v1] (nm/args (:body a))
               [s2 v2] (nm/args (:body b))
               clash (fn [det-a det-b val-a val-b]
                       (when-let [s (res/unify det-a det-b)]
                         (when (not= (res/substitute val-a s) (res/substitute val-b s))
                           [:functional s])))]
           (or (when (seq (set/intersection (get pa 2) (get pb 2)))
                 (clash s1 s2 v1 v2))
               (when (seq (set/intersection (get pa 1) (get pb 1)))
                 (clash v1 v2 s1 s2)))))
       (when (and (= 2 (:arity a)) (= 2 (:arity b))
                  (seq (set/intersection (marks-over tax :asymmetric fa context)
                                         (marks-over tax :asymmetric fb context))))
         (let [[x1 y1] (nm/args (:body a))
               [x2 y2] (nm/args (:body b))]
           (when-let [s (res/unify (list x1 y1) (list y2 x2))]
             (when (not= (res/substitute x1 s) (res/substitute y1 s))
               [:asymmetric s]))))))))

(defn- separated-antecedents?
  "Do two of these literals claim one term is of two types a declaration separates?  The
  one thing the joint-satisfiability test reads a declaration for, and it reads the same
  one the consequent side does."
  [kb lits context]
  (let [tax     (:taxonomy kb)
        by-term (reduce (fn [m l]
                          (let [f (nm/functor l)]
                            (if (and (= 1 (nm/arity l)) (symbol? f) (not (sx/variable? f)))
                              (update m (second l) (fnil conj #{}) f)
                              m)))
                        {} lits)]
    (boolean (some (fn [[_ ts]]
                     (let [ts (vec ts)]
                       (some (fn [[x y]] (tax/disjoint? tax x y context))
                             (for [i (range (count ts)), j (range (inc i) (count ts))]
                               [(nth ts i) (nth ts j)]))))
                   by-term))))

(defn- literal-arity-claim
  "The arity `lit` binds its first argument to, or nil — the two spellings `checks`
  reads, asked of a *literal* rather than of the store.

  `(arity ?p n)` says it outright.  A unary `(T ?p)` says it whenever `T` reaches one of
  the exact-arity classes up `genl`, which is what makes `(symmetric ?p)` a claim of arity
  2: `symmetric` is a kind of `binary_predicate`.  The roster is
  `checks/exact-arity-classes`, read here rather than copied, since a roster read twice
  is a roster that drifts, and read in key order so a term reaching two that disagree —
  itself incoherent — reports the same one every run."
  [tax lit context]
  (let [f (nm/functor lit)]
    (when (and (symbol? f) (not (sx/variable? f)))
      (cond
        (and (= 'arity f) (= 2 (nm/arity lit)))
        (let [n (last (nm/args lit))] (when (integer? n) n))

        (= 1 (nm/arity lit))
        (let [supers (tax/genls tax f context)]
          (some (fn [[t n]] (when (contains? supers t) n))
                (sort-by key checks/exact-arity-classes)))))))

(defn- arity-conflicted?
  "Do two of these literals bind one term to two arities?  A predicate takes one number of
  arguments — `(functional arity)` says so of the table, and the relation-wide classes are
  pairwise `disjoint`, which their kind specializations inherit (docs/taxonomy.md) — so no
  term satisfies both, whichever of the two spellings each literal used.  `(arity ?p 1)` beside `(arity ?p 2)`, and `(arity ?p 1)`
  beside `(equivalence_relation ?p)`, are the same finding read two ways.

  A declaration read, not an inference: nothing is derived and no fact is consulted, the
  same standing `separated-antecedents?` has beside it."
  [kb lits context]
  (let [tax     (:taxonomy kb)
        by-term (reduce (fn [m l]
                          (if-let [n (literal-arity-claim tax l context)]
                            (update m (second l) (fnil conj #{}) n)
                            m))
                        {} lits)]
    (boolean (some (fn [[_ ns]] (> (count ns) 1)) by-term))))

(defn- jointly-satisfiable?
  "Could both antecedent sets hold at once — **shallowly**?

  Three things rule it out and nothing else does: a literal appearing under σ together
  with its own negation, one term claimed to be of two separated types, and one term bound
  to two arities.  **No inference is run and no fact is consulted** — each of the three is
  a declaration read.  This is what the rules say about each other, and a pair it admits
  is a clash that *could* form rather than one that will — which is the whole reading,
  since a clash that had already formed would be in `(contradictions kb)` instead."
  [kb a b sigma context]
  (let [lits (into (mapv #(res/substitute % sigma) (:antecedent a))
                   (map #(res/substitute % sigma))
                   (:antecedent b))
        pos  (into #{} (remove sx/negation?) lits)
        neg  (into #{} (comp (filter sx/negation?) (map second)) lits)]
    (and (empty? (set/intersection pos neg))
         (not (separated-antecedents? kb pos context))
         (not (arity-conflicted? kb pos context)))))

(defn- rule-functors
  "Every predicate a rule names — its consequent's and its antecedents', a negation
  unwrapped."
  [v]
  (into #{(:functor v)}
        (keep (fn [l] (let [f (nm/functor (if (sx/negation? l) (second l) l))]
                        (when (symbol? f) f))))
        (:antecedent v)))

(defn- exception-names-other?
  "Does `a`'s `exceptWhen` name a predicate `b` is about?  That is the form a stated
  exception has — \"birds fly, unless penguins\" beside \"penguins do not fly\" — and it is
  why such a pair is reported as `:excepted` rather than hidden: a reader wants to see
  which clashes are already handled, not to be told there are none."
  [kb a b]
  (when-let [cs (rule-exception-conjuncts kb (:handle a))]
    (let [fs (rule-functors b)]
      (boolean (some (fn [c]
                       (some #(contains? fs (nm/functor (if (sx/negation? %) (second %) %))) c))
                     cs)))))

(defn- readable-unifier
  "σ in the two rules' own variable names, the **second** rule's carrying a trailing `'`.

  Both authors are free to write `?x`, and a map holding two of them says nothing; primed,
  `{?x' ?x}` reads as what it is — the second rule's `?x` is the first's."
  [sigma a b]
  (let [back (into (or (:varmap a) {})
                   (map (fn [[v r]]
                          [r (symbol (str (name (get (:varmap b) v v)) "'"))]))
                   (:rename b))]
    (into (sorted-map)
          (map (fn [[v t]]
                 [(get back v v) (sx/rename-vars (res/substitute t sigma) back)]))
          sigma)))

(defn- marked-groups
  "`marked predicate -> the binary-conclusion views under it`, for one property.  nil when
  the KB declares none, which is the gate that keeps the pairing off a KB with nothing to
  say — one map read.

  **`:functional` reads both spellings, here as well as in `consequent-clash`** (#56).
  This is the gate that decides which pairs are ever *formed*, so widening only the
  pairwise test left it answering nil for a KB whose sole mark is `(functionalInArg P 2)`
  — no candidate pair, and nothing for the widened test to run on.  The reach is
  `marks-over`, which is where the two spellings and the position-2 filter are
  stated once; `:asymmetric` has one spelling and keeps the plain read."
  [tax kind views]
  (when (marks-declared? tax kind)
    (reduce (fn [m v]
              (reduce (fn [m q] (update m q (fnil conj []) v)) m
                      (marks-over tax kind (:functor v) nil)))
            {}
            (filter #(and (= :positive (:polarity %)) (= 2 (:arity %))) views))))

(defn- clash-index
  "What `clash-partners` looks a rule's candidates up in — the consequent index, the
  distinct unary conclusion functors (only where the KB declares some separation at all),
  and the marked groups for the two predicate properties."
  [kb views]
  (let [tax (:taxonomy kb)
        pos (filterv #(= :positive (:polarity %)) views)]
    {:by-key   (by-consequent views)
     :unary-fs (when (or (seq (tax/disjoint-pairs tax))
                         (seq (tax/disjoint-metatypes tax))
                         (seq (tax/sibling-disjoints tax)))
                 (into #{} (comp (filter #(= 1 (:arity %))) (map :functor)) pos))
     :marked   {:functional (marked-groups tax :functional pos)
                :asymmetric (marked-groups tax :asymmetric pos)}}))

(defn- clash-partners
  "The rules worth asking `consequent-clash` about beside `a`.

  The **negation fan is global** and the pair is decided scoped, which is the form a
  candidate read has everywhere in the engine: the vantage a clash is asked from is a
  common descendant of the two rules' contexts and belongs to neither of them, so fanning
  from either would drop a pair the context that can see both would find.  An
  over-approximated candidate merely fails `consequent-clash` and yields nothing."
  [kb {:keys [by-key unary-fs marked]} a]
  (let [tax  (:taxonomy kb)
        f    (:functor a)
        pos? (= :positive (:polarity a))]
    (distinct
     (concat
      (if pos?
        (mapcat #(get by-key [:negative %]) (tax/genls-global tax f))
        (mapcat #(get by-key [:positive %]) (tax/specs-global tax f)))
      (when (and pos? unary-fs (= 1 (:arity a)))
        (for [g unary-fs
              :when (and (not= g f) (tax/disjoint? tax f g nil))
              b (get by-key [:positive g])]
          b))
      (when (and pos? (= 2 (:arity a)))
        (for [kind  [:functional :asymmetric]
              :let  [groups (get marked kind)]
              :when groups
              q     (marks-over tax kind f nil)
              b     (get groups q)]
          b))))))

(defn- clash-entry
  "The finding for one candidate pair, or nil."
  [kb a b0]
  (when-let [ctx (pair-context kb a b0)]
    (let [b (renamed b0)]
      (when-let [[kind s] (consequent-clash kb a b ctx)]
        (when (jointly-satisfiable? kb a b s ctx)
          {:rules     [(:handle a) (:handle b0)]
           :kind      kind
           :unifier   (readable-unifier s a b)
           :context   ctx
           :sentences [(:sentence a) (:sentence b0)]
           :excepted  (boolean (or (exception-names-other? kb a b0)
                                   (exception-names-other? kb b0 a)))})))))

(defn- rule-clashes
  "Rule pairs whose consequents would clash if both fired and whose antecedents could
  shallowly hold at once.

  **Static analysis of the rules**, which is what makes it a different question from
  `(contradictions kb)`: nothing here is derived, nothing believed and nothing asked of the
  KB's facts.  A pair is a clash the rules *admit*, and whether it ever forms depends on
  content nobody has asserted yet.

  A pair is taken once, in content order, and a rule is never paired with itself — the
  reading is about two rules disagreeing."
  [kb views limit progress!]
  (let [index   (clash-index kb views)
        ordered (nm/sort-by-content-key :sort-key compare views)
        total   (count ordered)]
    (progress! {:phase :clashes :done 0 :total total})
    (let [found (loop [i 0, out (transient [])]
                  (if (= i total)
                    (persistent! out)
                    (let [a    (nth ordered i)
                          hits (into []
                                     (keep (fn [b] (clash-entry kb a b)))
                                     (nm/sort-by-content-key
                                      :sort-key compare
                                      (filter #(neg? (compare (:sort-key a) (:sort-key %)))
                                              (clash-partners kb index a))))]
                      (when (and (pos? i) (zero? (mod i progress-every)))
                        (progress! {:phase :clashes :done i :total total}))
                      (recur (inc i) (reduce conj! out hits)))))]
      {:total      total
       :pairs      (vec (take limit found))
       :pair-count (count found)
       :truncated? (> (count found) limit)})))

;; ---- the report ----------------------------------------------------------

;; ---- the readings, as a roster -------------------------------------------

(def ^:private readings
  "One row per reading, in the order the report prints them — the data half, holding what
  a reading is *called* and never what renders it.  The arms are `render-arms`, below the
  helpers they need, and `check-readings!` joins the two at load.

    :key    what `census` answers under, and what `report` reads.
    :title  the `##` heading, so a section cannot be headed one thing here and another
            where it is written.
    :shape  the sub-key whose presence says a map really is a census answer, or absent for
            a reading the shape test does not ask about.  A reading gains a `:shape` only
            when a census map without it is no longer a census map, which is a decision
            about stored reports rather than about the reading — see `check-report-shape!`.

  Everything downstream is read off this: `census` is refused a key with no row
  (`reading-map`), `report` walks it, and the shape test is the `:shape` column.  Written
  out, the three would be the same seven names in three places, and the failure that
  leaves is the quiet one — a reading `census` answers and `report` has no section for
  renders as *absence*, which reads exactly like a KB with nothing to report."
  [{:key :rules        :title "Rules that never fire"                        :shape :total}
   {:key :extents      :title "Predicate extent skew"                        :shape :predicates}
   {:key :chains       :title "Chain depth over the rule graph"              :shape :rules}
   {:key :taxonomy     :title "Taxonomy coverage"                            :shape :names}
   {:key :declarations :title "Argument constraints that constrain nothing"}
   {:key :subsumption  :title "Rules another rule already covers"}
   {:key :clashes      :title "Contradictions in waiting"}])

(def ^:private reading-keys (into #{} (map :key) readings))

(defn- reading-map
  "The census answer, held to the roster: a reading with no row is refused here rather
  than dropped by `report`, and a row `census` does not answer is refused rather than
  rendering as a section that is simply never there.

  `opts/check!`'s argument at the other end of the same namespace — a key nothing reads is
  not a key — and the reason it runs here rather than at load is that `census` builds its
  map in a `let` whose *order* is part of what it answers (the phases an `:on-progress`
  caller sees), so the map literal is written out and cannot be folded from the roster."
  [m]
  (let [given (set (keys m))]
    (when-not (= reading-keys given)
      (throw (ex-info (str "kb-quality answered " (pr-str (vec (sort given)))
                           " and the readings are " (pr-str (vec (sort reading-keys)))
                           " — a reading with no row renders as an absent section, which"
                           " is indistinguishable from a KB with nothing to report.")
                      {:type :bad-table-entry :mismatch :reading
                       :answered (vec (sort given)) :declared (vec (sort reading-keys))}))))
  m)

(defn census
  "The readings as one map, keyed by `readings`' `:key` and held to that roster on the way
  out (`reading-map`).  `vaelii.core/kb-quality` is the entry point and documents the options."
  [kb {:keys [limit on-progress]}]
  ;; sequenced in a `let` rather than left to a map literal's argument order: the phases a
  ;; caller watching `:on-progress` sees are part of what this answers, and an evaluation
  ;; order is not something to read off the structure of a literal
  (let [limit     (or limit default-limit)
        progress! (or on-progress (fn [_] nil))
        pass      (vocabulary-pass kb progress!)
        handles   (into (set (keys (:ante pass))) (keys (:conseq pass)))
        rules     (firing-census kb pass handles limit progress!)
        extents   (extent-skew pass limit)
        chains    (chain-depth pass progress!)
        taxonomy  (taxonomy-coverage kb pass progress!)
        decls     (stranded-declarations kb limit progress!)
        ;; one record read per rule, shared by the two readings that need the rules
        ;; themselves rather than their postings
        views     (rule-views kb handles progress!)
        subsumed  (subsumed-rules kb views limit progress!)
        clashes   (rule-clashes kb views limit progress!)]
    (reading-map
     {:rules rules :extents extents :chains chains :taxonomy taxonomy
      :declarations decls :subsumption subsumed :clashes clashes})))

;; ---- the same map, as prose ----------------------------------------------
;; A separate function over the report rather than a second traversal of the KB, so
;; nothing can print a figure the data does not hold.

(defn- pct [n total] (if (pos? total) (format "%.1f%%" (* 100.0 (/ (double n) total))) "—"))

(defn- commas [n] (format "%,d" (long n)))

(defn- rule-lines [heading rules]
  (when (seq rules)
    (str "\n" heading "\n\n"
         (str/join "\n" (for [{:keys [handle sentence context]} rules]
                          (str "- `" handle "` `" (pr-str sentence) "` in `" context "`")))
         "\n")))

;; Each arm renders its reading's **body** and nothing else: the `##` heading is
;; `readings`' `:title`, written once by `report`, so a section cannot be headed one thing
;; in the roster and another where it is emitted.  Every body ends in exactly one newline,
;; which is what puts a blank line before the next heading and what makes the sections
;; composable in any subset.

(defn- render-rules [r]
  (str (commas (:total r)) " rules — **" (commas (:never-count r)) " never fired** ("
       (pct (:never-count r) (:total r)) "), " (commas (:all-defeated-count r))
       " fired with every conclusion defeated, " (commas (:fired r))
       " live; " (commas (:firings r)) " recorded firings in all.\n\n"
       "A firing is a **currently supported** one: a rule whose conclusions have since been\n"
       "retracted has no live justification and is counted as never fired.\n"
       (rule-lines "### Never fired" (:never r))
       (rule-lines "### Fired, every conclusion defeated" (:all-defeated r))
       (when (:truncated? r)
         "\nThe lists are capped; the counts above are not.\n")))

(defn- render-extents [e]
  (str (commas (:predicates e)) " predicates, " (commas (:with-extent e))
       " with an extent, " (commas (:stored e)) " stored facts, Gini "
       (format "%.4f" (:gini e)) ".\n\n"
       "| extent | predicates |\n|---|---|\n"
       (str/join "\n" (for [[k n] (sort (:buckets e))]
                        (str "| 10^" k " | " (commas n) " |")))
       "\n\n### The heaviest\n\n"
       (str/join "\n" (for [[pred n] (:heaviest e)]
                        (str "- `" pred "` — " (commas n))))
       "\n"))

(defn- render-chains [c]
  (str (commas (:functors c)) " functors in " (commas (:components c))
       " components (" (commas (:cyclic c)) " cyclic, largest " (commas (:largest c))
       "), over " (commas (:rules c)) " rules.\n\n"
       "| depth | rules | at least |\n|---|---|---|\n"
       (str/join "\n" (for [[d n] (sort (:depths c))]
                        (str "| " d " | " (commas n) " | "
                             (if-let [f (get (:at-least c) d)]
                               (format "%.1f%%" (* 100.0 f))
                               "100.0%")
                             " |")))
       "\n"))

(defn- render-taxonomy [t]
  (str (commas (:names t)) " type names — " (commas (:edged t))
       " carry a `genl` edge (" (pct (:edged t) (:names t)) ")"
       (if-let [root (:root t)]
         (str ", " (commas (:rooted t)) " reach `" root "` ("
              (pct (:rooted t) (:names t)) ").\n\n"
              "Edged but not reaching the root: " (commas (:islands t))
              " — the types sitting in disconnected islands, and the gap between the two\n"
              "fractions above is the finding rather than either one of them.\n")
         ;; no edge anywhere means no root to report against, which is a different statement
         ;; from a root nothing reaches — and an empty code span is neither
         ".\n\nNo `genl` edge anywhere, so there is no root to measure reach against.\n")))

(defn- render-declarations [d]
  (str (commas (:total d)) " argument declaration"
       (when (not= 1 (:total d)) "s") " — **"
       (commas (:stranded-count d))
       (if (= 1 (:stranded-count d))
         " names a position its predicate does not have"
         " name a position their predicate does not have")
       "** (" (pct (:stranded-count d) (:total d)) ").\n\n"
       "Such a declaration is admitted while the predicate has no declared length and\n"
       "goes inert when one arrives, so it reads as enforced while enforcing nothing.\n"
       "It is a finding rather than an error: nothing is wrong with the KB's belief,\n"
       "and the fix is to correct the position, to declare the arity the author meant,\n"
       "or to mark the predicate `variable_arity` where its tuples really do reach that\n"
       "far.\n"
       (when (seq (:stranded d))
         (str "\n"
              (str/join "\n"
                        (for [{:keys [sentence context message]} (:stranded d)]
                          (str "- `" (pr-str sentence) "` in `" context "`"
                               (when message (str " — " message)))))
              "\n"))
       (when (:truncated? d)
         "\nThe list is capped; the count above is not.\n")))

(defn- render-subsumption [s]
  (str (commas (:total s)) " rules — **"
       (commas (:subsumed-count s))
       (if (= 1 (:subsumed-count s))
         " is covered by another"
         " are covered by another")
       "** (" (pct (:subsumed-count s) (:total s)) ").\n\n"
       "A covering rule fires wherever the covered one does and concludes at least as\n"
       "much, so the covered rule adds nothing the KB would not have had.  An exact\n"
       "duplicate cannot appear here — two rules alike up to variable names or\n"
       "antecedent order are one handle — so each of these is either a redundancy or a\n"
       "deliberate specialization, and which one it is lives in what the author meant\n"
       "rather than in what the KB holds.\n"
       (when (seq (:subsumed s))
         (str "\n"
              (str/join "\n"
                        (for [{:keys [subsumed by substitution context sentence
                                      by-sentence]} (:subsumed s)]
                          (str "- `" subsumed "` `" (pr-str sentence) "` in `" context
                               "` — covered by `" by "` `" (pr-str by-sentence)
                               "` under `" (pr-str substitution) "`")))
              "\n"))
       (when (:truncated? s)
         "\nThe list is capped; the count above is not.\n")))

(defn- render-clashes [c]
  (str (commas (:total c)) " rules — **" (commas (:pair-count c))
       (if (= 1 (:pair-count c)) " pair" " pairs")
       " would clash if both fired**.\n\n"
       "One substitution makes the two conclusions incompatible and nothing in the two\n"
       "antecedent sets shallowly rules out both holding.  No inference is run and no\n"
       "fact is consulted: this is what the rules say about each other, not what the KB\n"
       "believes.  A pair marked **excepted** is the intended shape — one of the two\n"
       "carries an `exceptWhen` naming the other's case, so the clash is already stated\n"
       "as an exception rather than left to arbitration.\n"
       (when (seq (:pairs c))
         (str "\n"
              (str/join "\n"
                        (for [{hs :rules :keys [kind context sentences excepted]}
                              (:pairs c)]
                          (str "- " (name kind) " in `" context "`: `" (first hs)
                               "` `" (pr-str (first sentences)) "` against `"
                               (second hs) "` `" (pr-str (second sentences)) "`"
                               (when excepted " — excepted"))))
              "\n"))
       (when (:truncated? c)
         "\nThe list is capped; the count above is not.\n")))

(def ^:private render-arms
  "The arms half of `readings`: reading key -> `(fn [sub-map] body)`."
  {:rules        render-rules
   :extents      render-extents
   :chains       render-chains
   :taxonomy     render-taxonomy
   :declarations render-declarations
   :subsumption  render-subsumption
   :clashes      render-clashes})

(defn- check-readings!
  "Refuse at load a roster and a set of arms that do not agree.

  A reading with a row and no arm would print a heading over nothing; an arm with no row
  would never be reached, since `report` walks the roster.  Neither is visible from a test
  that renders a KB, because both are about a reading the suite does not have — which is
  every reading on the day it is added.

  **Takes both halves**, rather than reading the two vars beside it, so a test can drive
  it over halves that disagree.  A validator called only by its own namespace's load has
  run every branch it will ever run against a table that passes, and nothing then says it
  would refuse: a `remove` written the wrong way round reads exactly like a roster with
  nothing wrong.  Returns the roster, as `predicates/check-families` does.

  Refuses under `:bad-table-entry` discriminated by `:mismatch`, as
  `predicates/check-families`, `config/check-switches!` and `kb/check-backends!` do."
  [readings render-arms]
  (let [keys-of (into #{} (map :key) readings)]
    (doseq [k (sort (remove render-arms keys-of))]
      (throw (ex-info (str "reading " k " is on `readings` and has no arm in `render-arms`"
                           " — `report` would write its heading over an empty section.")
                      {:type :bad-table-entry :mismatch :unarmed-reading :reading k})))
    (doseq [k (sort (remove keys-of (keys render-arms)))]
      (throw (ex-info (str "`render-arms` renders " k ", which is on no row of `readings`"
                           " — `report` walks the roster, so the arm is never reached and"
                           " the reading has no title, no place in the order and no say in"
                           " the shape test.")
                      {:type :bad-table-entry :mismatch :unrostered-arm :reading k})))
    (doseq [{:keys [key title]} readings]
      (when (str/blank? title)
        (throw (ex-info (str "reading " key " has no title, and `report` writes the title as"
                             " the section's heading — a blank one is a `##` over nothing.")
                        {:type :bad-table-entry :mismatch :blank-title :reading key}))))
    (let [dupes (into #{} (comp (filter (fn [[_ v]] (< 1 (count v)))) (map key))
                      (group-by :title readings))]
      (when (seq dupes)
        (throw (ex-info (str "two readings share a heading: " (pr-str (vec (sort dupes)))
                             " — a reader cannot tell which section they are looking at, and"
                             " a search for the heading finds the wrong one.")
                        {:type :bad-table-entry :mismatch :duplicate-title :titles dupes}))))
    (when-not (= (count readings) (count keys-of))
      (throw (ex-info (str "`readings` names a key twice — " (pr-str (mapv :key readings))
                           " — and the second row would be rendered under the first's"
                           " title, or not at all.")
                      {:type :bad-table-entry :mismatch :duplicate-reading
                       :keys (mapv :key readings)}))))
  readings)

(check-readings! readings render-arms)

(defn- check-report-shape!
  "Refuse a map that is not a census answer, naming the readings whose presence says it is.

  A page of zeros and dashes is what a caller who passed the wrong map would otherwise be
  handed, and it is indistinguishable from a report of an empty KB.

  The test asks only for the readings carrying a `:shape`, and the three without one are
  the point rather than an oversight: **a census answer from before a reading existed is
  still a census answer**, and refusing to render one would turn a stored report into an
  unreadable one.  So a new reading is added without a `:shape`, and gains one only if
  there comes a day when a map lacking it is no longer a report."
  [quality]
  (let [shaped (filterv :shape readings)]
    (when-not (and (map? quality)
                   (every? (fn [{:keys [key shape]}] (get-in quality [key shape])) shaped))
      (throw (ex-info (str "not a kb-quality report — want the map `kb-quality` answers,"
                           " with " (str/join " / " (map (comp str :key) shaped)) "; got "
                           (if (map? quality)
                             (pr-str (vec (sort (keys quality))))
                             (pr-str (type quality))))
                      {:type :not-a-report
                       :keys (when (map? quality) (vec (sort (keys quality))))})))))

(defn report
  "The `census` map as Markdown — the readings in `readings`' order, each under its own
  `:title`, the counts first and the lists after.  A map that is not a census answer is
  refused (`:not-a-report`); which readings decide that is `check-report-shape!`.

  A section is written when its key is there and omitted when it is not, so a stored
  answer from before a reading existed still renders.  The roster is what makes the
  omission a *decision*: a key `census` answers reaches this walk or is refused at
  `census` (`reading-map`), and a row with nothing to render it fails the build
  (`check-readings!`).  Neither was true when the sections were written out — a reading
  with no section rendered as absence, which reads exactly like a KB with nothing to
  report.

  A listed declaration's reason line is the `:message` the census carries rather than a
  second derivation of it, which would be the same sentence written twice, free to drift
  on either side."
  [quality]
  (check-report-shape! quality)
  (apply str "# KB quality\n"
         (for [{:keys [key title]} readings
               :let                [m (get quality key)]
               :when               m]
           (str "\n## " title "\n\n" ((render-arms key) m)))))
