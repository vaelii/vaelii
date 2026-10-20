;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.quality
  "Readings about the **knowledge**, where the rest of the instrumentation reads the
  engine — `readings` below is the table, and what each one asks is: which rules never fire, how skewed the predicate extents are, how deep the rule
  graph's chains reach, how much of the taxonomy is connected to anything, which argument
  declarations name a position their predicate does not have, which rules another rule
  already covers, and which rule pairs would contradict each other if both fired.

  `settle-stats` and `chain-stats` answer *how the engine ran*.  These answer *whether the
  knowledge is any good*, which is the question the author of a large KB has and the one
  nothing else here asks.  None of it is a required check: a threshold on somebody's ontology
  is not a build failure, and `lein perf` checks the engine while this reports on the
  content.

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

  - **One walk over the term-name set**, and one is the number: the functor names come off it
    by filter, and the type-shaped names come off *those* rather than off the term-name set a
    second time.  Measured at 8x the terms for 8x the cost, so the walk is the term the
    formula above leads with.
  - **Three O(1) index reads per functor name** — the stored extent off the count-aware
    trie, and the rule postings *both* ways.  That is everything the extent and chain
    readings need, and it is where the rule handles come from, so nothing on this pass
    reaches the record store at all — the record reads are the listed rules' and the two
    rule-hygiene readings' below.
  - **The firing census reads each rule's own `:consequences` adjacency**, the candidate
    set `jtms/restrength-informant*` uses, and never scans the justification map.  On a
    store of millions of justifications that difference is the report existing or not.
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
    other does, and the two properties they read run only when the KB declares any
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
            [vaelii.impl.except :as exc]
            [vaelii.impl.integrity :as integrity]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

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
  in this filter's answer, which is what keeps the taxonomy reading from walking the term-name
  set a second time — the set is the report's one superlinear term and it is walked
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
        preds (into [] (filter functor-name?) (reads/stored-terms-global idx))
        total (count preds)]
    ;; before the loop, so a phase with nothing in it still reports itself — a caller
    ;; watching the phases is watching for where a long report is, and \"skipped because
    ;; empty\" and \"not reached\" must not read the same
    (progress! {:phase :extents :done 0 :total total})
    (with-open [r (progress/start ::extents "quality: read the predicate extents" total)]
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
            (progress/tick! r)
            (recur (inc i)
                   (if (pos? n) (assoc! extents pred n) extents)
                   (reduce (fn [m h] (assoc! m h (conj (get m h #{}) pred)))
                           ante (reads/as-stored-rules-by-antecedent-global idx pred))
                   (reduce (fn [m h] (assoc! m h pred))
                           conseq (reads/as-stored-rules-by-consequent-global idx pred)))))))))

;; ---- which rules never fire ----------------------------------------------

(defn- rule-line
  "A listed rule as something an author can read: its handle, the sentence as *written*
  (a rule is stored canonically numbered, which reads as gibberish), and its context."
  [kb h]
  (when-let [sx (p/get-sentex (:records kb) h)]
    {:handle   h
     :sentence (sx/authored-sentence sx)
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
  (let [tms   (reasoning/tms kb)
        hs    (vec handles)
        total (count hs)]
    (progress! {:phase :rules :done 0 :total total})
    (with-open [r (progress/start ::rules "quality: census the rule firings" total)]
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
                ;; a conclusion as its own context believes it
                live (count (filter #(exc/believed-own? kb (:consequence %)) js))]
            (when (and (pos? i) (zero? (mod i progress-every)))
              (progress! {:phase :rules :done i :total total}))
            (progress/tick! r)
            (recur (inc i)
                   (if (empty? js) (conj never h) never)
                   (if (and (seq js) (zero? live)) (conj defeated h) defeated)
                   (if (pos? live) (inc fired) fired)
                   (+ firings (count js)))))))))

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
  A `kb/relation?` name is excluded; a name with no stored arity remains a candidate
  rather than hiding disconnected type islands.
  That is why the gap is the finding rather than either fraction on its own.

  Reachability is **reflexive**, as `genls` is: the root reaches itself, so `:rooted`
  counts it and `:islands` is exactly the edged types outside the root's ancestor set.

  The closures are unscoped: the report counts the whole taxonomy and has no reader."
  [kb pass progress!]
  (let [taxo  (reasoning/taxonomy kb)
        ;; Memoized: the reach walk below asks this once per node AND once per ancestor
        ;; of every node, which on the 124k-type conversion above is a few million calls
        ;; over a name set two orders of magnitude smaller.  Each call reads the
        ;; taxonomy atom and allocates, and the answer cannot move inside one reading.
        type-candidate? (memoize #(not (kb/relation? kb % nil)))
        nodes (into #{} (filter type-candidate?) (tax/types taxo))
        named (into #{} (filter type-candidate?) (:type-names pass))]
    (progress! {:phase :taxonomy :done 0 :total (count nodes)})
    (let [reach (with-open [r (progress/start ::taxonomy "quality: walk the type ancestor sets"
                                              (count nodes))]
                  (frequencies (mapcat #(filter type-candidate? (tax/genls-global taxo %))
                                       (progress/each r nodes))))
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
;; rather than a claim about it.  Then a length arrives, by any of the routes
;; `arity/relation-length` reads, and the declaration is left constraining a position the
;; predicate provably does not have.  It is not refused: refusing it would make the
;; *binding's* arrival order decide what the KB holds.  It simply stops meaning anything,
;; while the entry point refuses the identical sentence one line later.
;;
;; A `variable_arity` predicate is the case where the length is not the last word, and the
;; entry point's arm releases it: such a predicate reads a tuple of any length from its declared
;; arity upward, so a position past that length is one its tuples really do reach.  Nothing
;; of its is listed here, however high the position, because nothing of its is stranded.
;;
;; **Here rather than in the settle ledger.**  A wrong-length *fact* is a claim each reader
;; believes or withdraws (`vaelii.impl.decide`).  A stranded declaration is inert: it constrains nothing, refuses nothing and mints
;; nothing, and it reads the same an hour later as at the moment it went stale.  There is
;; no newly to report, so paying per write buys nothing a census does not give for free —
;; and a per-declaration ledger entry would compete for the 1,000 slots `violations` keeps
;; and log a `:warn` line each.  Measured: this walk is 0.008 ms at 32 declarations and
;; 0.103 ms at 512, against 3.3 ms for the per-predicate probes a settle-side sweep over a
;; 512-predicate subtree would have made.

(def ^:private declaration-functors
  "The argument constraints, in the order this walks them.  A vector rather than the
  set in `checks`, because this is a walk order and that is a membership test."
  '[arg genlArg interArg interArgEqual])

(defn- thing-typed
  "The type a declaration's `sentence` mints in is `thing`: the last argument of `arg` and
  `genlArg`, the fifth of `interArg` and `interArgEqual`."
  [sentence]
  (= 'thing (if (contains? '#{interArg interArgEqual} (nm/functor sentence))
              (nth sentence 5 nil)
              (last sentence))))

(defn- stranded-declarations
  "Which argument constraints name a position their predicate does not have, and which
  type a position `thing` (`:typed-thing`, each with `:facts`, its predicate's stored
  extent).  A declaration typing `thing` mints nothing (`arity/mintable-type?`), so the
  remedy is a narrower type in the declaration.

  **Enumerated, not probed per predicate.**  Declarations are vocabulary and vocabulary is
  small — the whole bundled ontology has 298 — so reading all of them and asking each
  about its own predicate is cheaper than asking each predicate what declares it, and it
  does not grow with the spec subtree underneath.  What it does grow with is the hierarchy
  *above*: `arity/relation-length` is a binding read for a predicate carrying a length of
  its own and a walk of the supers for one that inherits its length, so the reading is
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
                           (filter #(not (sx/negative? %)))
                           (filter #(exc/believed-own? kb (:id %))))
                     declaration-functors)]
    (progress! {:phase :declarations :done 0 :total (count stored)})
    (let [found   (with-open [r (progress/start ::declarations
                                                "quality: check the argument declarations"
                                                (count stored))]
                    (into []
                          (keep (fn [sx]
                                  (progress/tick! r)
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
                          stored))
          ;; content order, so the listed set is a function of the vocabulary rather than
          ;; of the handle order the index walked
          order   #(nm/sort-by-content-key
                    (juxt (comp nm/print-key :sentence) (comp nm/print-key :context))
                    compare %)
          ordered (order found)
          things  (order (for [sx stored :when (thing-typed (:sentence sx))]
                           {:handle   (:id sx)
                            :sentence (:sentence sx)
                            :context  (:context sx)
                            :facts    (reads/stored-count-with-functor
                                       (:index kb) (second (:sentence sx)))}))]
      {:total             (count stored)
       :stranded          (vec (take limit ordered))
       :stranded-count    (count found)
       :truncated?        (> (count found) limit)
       :typed-thing       (vec (take limit things))
       :typed-thing-count (count things)})))

;; ---- rules read against each other ---------------------------------------
;;
;; The five readings above ask about a rule's relation to the **KB** — whether it fired,
;; how deep its chain runs.  The two below ask about a rule's relation to **another
;; rule**, which is the one question in the census that needs the rules themselves and
;; not their index postings: one record read per rule, and a unification per candidate
;; not their index postings: one record read per rule (`integrity/rule-rows`, read once
;; for both), and a unification per candidate pair.  So these two add
;; `O(rules + candidate pairs)` to the report and no term that grows with what the KB
;; stores.  The clash pairing is `vaelii.impl.integrity`'s, whose comment says how it reads;
;; subsumption below reads the same way: the rules as stored, a rule the KB currently
;; disbelieves still being a rule somebody wrote, and the declarations it consults
;; following belief.

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
                (integrity/rule-variables forms))]
    [m (set/map-invert m)]))

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

;; ---- reading six: rules another rule already covers -----------------------

(defn- engines-cover?
  "Can a rule run by `e1` stand in for one run by `e2`?  When it runs in every engine `e2`
  does: forward + backward covers every chaining set, forward-only covers only itself, and
  backward covers only backward.  An inert rule (`#{}`) is covered by an inert rule
  alone, since a rule that chains in neither engine is documentation, and a rule that
  does chain is not a restatement of it."
  [e1 e2]
  (if (empty? e2) (empty? e1) (every? (set e1) e2)))

(defn- available-at-least?
  "Is `r1` at least as **available** as `r2` — could every firing of `r2` have been one of
  `r1`?  Three slots decide it, and each is a way one rule reaches where the other does
  not:

  - **engines**, since a backward rule forward-chains nothing and an inert rule chains in
    neither engine (`engines-cover?`);
  - **defeasibility**, since a default cannot stand in for a strict rule — its conclusion
    is defeated exactly where the strict one's stands;
  - **effect**, since a choice or constraint rule does not chain at all: each is a
    *choice* or a *nogood* for a solve (docs/solving.md) and part of the rule's identity.

  What it does not read is the rule sentex's own **strength**, which says how the rule is
  defeated rather than where it runs."
  [r1 r2]
  (and (engines-cover? (:engines r1) (:engines r2))
       (or (not (:defeasible r1)) (:defeasible r2))
       (= (:effect r1) (:effect r2))))

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
  (let [e1 (integrity/rule-exception-conjuncts kb (:handle r1))]
    (or (nil? e1)
        (let [e2 (into #{} (map set) (integrity/rule-exception-conjuncts kb (:handle r2)))]
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
               (tax/sees? (reasoning/taxonomy kb) context (:context r1)))
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
  (let [tax   (reasoning/taxonomy kb)
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
  [kb rows limit progress!]
  (let [index   (integrity/by-consequent rows)
        ordered (nm/sort-by-content-key :sort-key compare rows)
        total   (count ordered)
        found   (with-open [r (progress/start ::subsumption "quality: find the subsumed rules" total)]
                  (loop [i 0, out (transient [])]
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
                        (progress/tick! r)
                        (recur (inc i) (reduce conj! out hits))))))]
    {:total          total
     :subsumed       (vec (take limit found))
     :subsumed-count (count found)
     :truncated?     (> (count found) limit)}))

;; ---- reading seven: contradictions in waiting -----------------------------

(defn- rule-clashes
  "Rule pairs whose consequents would clash if both fired: `integrity/clash-pairs` over
  every rule the census enumerated, counted and capped — the pairing kb-integrity's
  `:rule-clash` and `:rule-clash-review` categories split by who acts on a pair."
  [kb rows limit progress!]
  (let [found (with-open [r (progress/start ::clashes "quality: find the rule clashes"
                                            (count rows))]
                (let [pairs (vec (integrity/clash-pairs
                                  kb rows
                                  (fn [m]
                                    (progress/tick-to! r (:done m))
                                    (progress! (assoc m :phase :clashes)))))]
                  (progress/tick-to! r (count rows))
                  pairs))]
    {:total      (count rows)
     :pairs      (vec (take limit found))
     :pair-count (count found)
     :truncated? (> (count found) limit)}))

;; ---- the report ----------------------------------------------------------

;; ---- the readings, as a table --------------------------------------------

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
  "The census answer, held to the table: a reading with no row is refused here rather
  than dropped by `report`, and a row `census` does not answer is refused rather than
  rendering as a section that is simply never there.

  `opts/check!`'s argument at the other end of the same namespace — a key nothing reads is
  not a key — and the reason it runs here rather than at load is that `census` builds its
  map in a `let` whose *order* is part of what it answers (the phases an `:on-progress`
  caller sees), so the map literal is written out and cannot be folded from the table."
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
  "The readings as one map, keyed by `readings`' `:key` and held to that table on the way
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
        rows      (integrity/rule-rows kb handles #(progress! (assoc % :phase :subsumption)))
        subsumed  (subsumed-rules kb rows limit progress!)
        clashes   (rule-clashes kb rows limit progress!)]
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
;; in the table and another where it is emitted.  Every body ends in exactly one newline,
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
         "\nThe list is capped; the count above is not.\n")
       (when (pos? (:typed-thing-count d 0))
         (str "\n**" (commas (:typed-thing-count d))
              (if (= 1 (:typed-thing-count d)) " declaration types" " declarations type")
              " a position `thing`**, which mints nothing; a narrower type in the\n"
              "declaration types the facts listed beside it.\n\n"
              (str/join "\n"
                        (for [{:keys [sentence context facts]} (:typed-thing d)]
                          (str "- `" (pr-str sentence) "` in `" context "` — "
                               (commas facts) " stored fact" (when (not= 1 facts) "s"))))
              "\n"))))

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
  "Refuse at load a readings table and a set of arms that do not agree.

  A reading with a row and no arm would print a heading over nothing; an arm with no row
  would never be reached, since `report` walks the table.  Neither is visible from a test
  that renders a KB, because both are about a reading the suite does not have — which is
  every reading on the day it is added.

  **Takes both halves**, rather than reading the two vars beside it, so a test can drive
  it over halves that disagree.  A validator called only by its own namespace's load has
  run every branch it will ever run against a table that passes, and nothing then says it
  would refuse: a `remove` written the wrong way round reads exactly like a table with
  nothing wrong.  Returns the table, as `predicates/check-facets` does.

  Refuses under `:bad-table-entry` discriminated by `:mismatch`, as
  `predicates/check-facets`, `config/check-switches!` and `kb/check-backends!` do."
  [readings render-arms]
  (let [keys-of (into #{} (map :key) readings)]
    (doseq [k (sort (remove render-arms keys-of))]
      (throw (ex-info (str "reading " k " is on `readings` and has no arm in `render-arms`"
                           " — `report` would write its heading over an empty section.")
                      {:type :bad-table-entry :mismatch :unarmed-reading :reading k})))
    (doseq [k (sort (remove keys-of (keys render-arms)))]
      (throw (ex-info (str "`render-arms` renders " k ", which is on no row of `readings`"
                           " — `report` walks the table, so the arm is never reached and"
                           " the reading has no title, no place in the order and no say in"
                           " the shape test.")
                      {:type :bad-table-entry :mismatch :unlisted-arm :reading k})))
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
  answer from before a reading existed still renders.  The table is what makes the
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
