;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.host.io.generate
  "Synthesize a knowledge base of a chosen **shape**.

  The two other kinds of KB are given: a shipped ontology (`vaelii.host.starter`) is
  fixed content, and an imported corpus (`vaelii.impl.io.import`, or a translated one)
  is whatever the source says.  Neither lets you ask *what happens at ten times the
  rules*, and that is the question a scale or behaviour measurement is made of.  So this
  namespace generates a KB from a handful of numbers — how many types, individuals,
  predicates, facts and rules, how the rules split forward/backward, how many of them are
  defeasible — and each number is a knob the browser renders as a slider (`knobs`).

  Two properties make a generated KB usable as a measurement rather than as noise:

  * **Deterministic.**  Each of `plan`'s three draw streams owns a `java.util.Random`
    seeded from the plan seed and its own constant (`stream-seeds`), so the same
    parameters give the same KB whichever order a reader realizes the streams in — a
    shape can be reproduced from the numbers alone, and a run compared against a rerun.
  * **Stratified.**  Predicates are split into layers: facts populate layer 0, and a rule
    concluding a layer-k predicate draws its antecedents only from layers below k.  The
    rule set is therefore acyclic, so forward chaining cascades base → derived →
    further-derived and terminates, instead of the runaway recursion a rule set wired at
    random produces.  Individuals and predicates are Zipf-sampled, so the corpus has hot
    terms and a long tail like a real one rather than a uniform smear.

  `plan` is pure — the whole KB as data, nothing asserted.  `load-into` asserts it,
  reporting progress through an optional `:on-progress` callback (which may throw to
  cancel the load, the flag `vaelii.browser.catalog` cancels on)."
  (:require [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.host.starter :as starter]
            [vaelii.impl.rules :as rules]))

;; ---- the knobs -----------------------------------------------------------

(def knobs
  "The generator's numeric parameters as data — one entry per slider the browser draws.
  `:scale :log` marks a knob whose slider moves over orders of magnitude (the counts
  that reach into the millions); the rest are linear.  Keeping this a value rather than
  a form in the page means the UI and the generator cannot disagree about the range of
  a parameter or its default."
  [{:key :types       :label "Types"        :min 0 :max 100000 :step 1    :default 200 :scale :log
    :help "unary type predicates, wired into a genl tree under thing"}
   {:key :branching   :label "Branching"    :min 2 :max 16     :step 1    :default 4
    :help "children per node in that type tree — low is deep, high is flat"}
   {:key :individuals :label "Individuals"  :min 0 :max 5000000 :step 1   :default 2000 :scale :log
    :help "named things, each given one type membership"}
   {:key :predicates  :label "Predicates"   :min 2 :max 20000  :step 1    :default 40 :scale :log
    :help "binary relation predicates, split into the rule layers"}
   {:key :facts       :label "Facts"        :min 0 :max 20000000 :step 1  :default 5000 :scale :log
    :help "ground relation facts over the base band of predicates"}
   {:key :rules       :label "Rules"        :min 0 :max 500000 :step 1    :default 200 :scale :log
    :help "chain-join rules, antecedents drawn from the layers below their consequent"}
   {:key :forward     :label "Forward mix"  :min 0 :max 100    :step 1    :default 50 :unit "%"
    :help "share of rules that forward-chain; the rest are backward-only"}
   {:key :defeasible  :label "Defeasible"   :min 0 :max 100    :step 1    :default 10 :unit "%"
    :help "share of rules asserted as defaults (set/defaultRule)"}
   {:key :antecedents :label "Antecedents"  :min 1 :max 8      :step 1    :default 3
    :help "the peak of the per-rule antecedent count (a distribution around it)"}
   {:key :layers      :label "Rule layers"  :min 2 :max 8      :step 1    :default 3
    :help "how deep a derivation can cascade — the predicate stratification"}
   {:key :contexts    :label "Contexts"     :min 1 :max 512    :step 1    :default 1
    :help "contexts the facts are spread over — a chain, each seeing the one above"}])

(def defaults
  "Every parameter with its default: the numeric knobs plus the four that are not
  sliders — the seed, whether to forward-chain at the end and what bounds that run,
  and which shipped vocabulary the generated content sits on top of."
  (assoc (into {} (map (juxt :key :default)) knobs)
         :seed 1
         :chain? false
         ;; the engine's own backstop, surfaced because chaining is by far the longest
         ;; phase of a chained load: a dense join is superlinear in the justifications it
         ;; has already recorded, so what makes such a load come back is this number and
         ;; the depth bound below it.  A single datum's fan-out is atomic, so a run
         ;; overshoots the cap by whatever the last one derived
         :max-derivations 100000
         :base :core))                                   ; :core (the vocabulary head) | :starter

(def ^:private context-root 'CxGenerated)

;; ---- deterministic sampling ---------------------------------------------

(defn- zipf-cdf
  "Cumulative Zipf weights over ranks 1..n at exponent `s` — the array a uniform draw
  binary-searches into, so rank 0 is the hottest term and the tail is long."
  ^doubles [^long n ^double s]
  (let [w (double-array (max 1 n))]
    (loop [i 0, acc 0.0]
      (if (< i (alength w))
        (let [acc' (+ acc (/ 1.0 (Math/pow (inc i) s)))]
          (aset w i acc')
          (recur (inc i) acc'))
        w))))

(defn- zipf
  "One draw from `cdf`."
  ^long [^doubles cdf ^java.util.Random rng]
  (let [total (aget cdf (dec (alength cdf)))
        idx   (java.util.Arrays/binarySearch cdf (* total (.nextDouble rng)))]
    (if (neg? idx) (min (dec (alength cdf)) (- (- idx) 1)) idx)))

;; ---- the vocabulary ------------------------------------------------------
;; Every generated name carries its role in its spelling, exactly as the naming
;; invariants require (vaelii.impl.naming): a type is snake_case, an individual
;; CapitalCamelCase, a predicate camelCase, a context starts with Cx.

(defn- type-name    [i] (symbol (str "gen_type_" i)))
(defn- ind-name     [i] (symbol (str "GenInd" i)))
(defn- pred-name    [i] (symbol (str "genRel" i)))
(defn- context-name [i] (symbol (str "CxGenBand" i)))

(defn- genl-edges
  "The type tree: type *i*'s parent is type `(quot (dec i) branching)`, so a parent's
  index is always below its child's and asserting in index order is asserting **most
  general first** — the order a taxonomy wants, since each edge invalidates the cached
  closure the next one reads.  Type 0 roots the tree under `thing`."
  [n branching]
  (when (pos? n)
    (cons (list 'genl (type-name 0) 'thing)
          (for [i (range 1 n)]
            (list 'genl (type-name i) (type-name (quot (dec i) branching)))))))

(defn- bands
  "The predicate names split into `layers` bands: band 0 is the base (what facts are
  stated over), band k is what a layer-k rule concludes.  A band past the vocabulary
  is dropped rather than emitted empty — two predicates under eight layers is two
  bands, and a rule can only conclude into a band that names a predicate (an empty
  band would put `(nth [] …)` inside the lazy rule draw, mid-load)."
  [preds layers]
  (let [base (max 1 (quot preds (max 2 layers)))
        rest (max 1 (quot (- preds base) (max 1 (dec layers))))]
    (into [(mapv pred-name (range base))]
          (for [k     (range 1 layers)
                :let  [b (mapv pred-name (range (min preds (+ base (* (dec k) rest)))
                                                (min preds (+ base (* k rest)))))]
                :when (seq b)]
            b))))

(defn- antecedent-counts
  "A distribution of antecedent counts peaking at `peak` — the form a real rule corpus
  has (a few one-antecedent rules, a mode at three or four, a thin tail)."
  [peak]
  (vec (mapcat (fn [[k w]] (repeat w (max 1 k)))
               [[(dec peak) 20] [peak 40] [(inc peak) 24] [(+ 2 peak) 12] [(+ 3 peak) 4]])))

;; ---- the plan ------------------------------------------------------------

(def ^:private stream-seeds
  "One seed offset per **independently drawn stream** of the plan.

  The three lazy seqs a plan hands back — `:memberships`, `:facts`, `:rules` — are
  realized by whoever holds the plan, in whatever order that caller wants: `load-into`
  takes memberships, then rules, then facts, and a test reading the map takes them in
  another.  Sharing one `Random` across the three would make each stream's *values* a
  function of when the others were realized, so the same parameters would describe
  different KBs depending on the order they were asked for — which is exactly the
  property `plan` promises it does not have.  A stream per generator closes that: each
  draws from its own `Random`, seeded off the plan's seed, so the interleaving cannot be
  observed.  (Within one stream the order is the seq's own and is fixed.)

  The offsets are the SplitMix64 mixing constants, written as the signed longs they are
  (a positive hex literal that wide is indistinguishable from a `BigInt`): distinct, odd and
  high-entropy, so two streams of one plan and one stream of two adjacent seeds do not
  alias."
  {:memberships -7046029254386353131        ; 0x9E3779B97F4A7C15
   :facts       -4658895280553007687        ; 0xBF58476D1CE4E5B9
   :rules       -7723592293110705685})      ; 0x94D049BB133111EB

(defn- stream-rng
  "The `Random` for one of `plan`'s draw streams — see `stream-seeds`."
  ^java.util.Random [seed stream]
  (java.util.Random. (bit-xor (long seed) (long (stream-seeds stream)))))

(defn plan
  "The whole synthetic KB as data — pure, and a function of `params` alone (the seed
  included), so the same numbers describe the same KB every time, **whatever order its
  streams are realized in** (`stream-seeds`).

  Returns `{:params :context-edges :genls :memberships :facts :rules :units}`, where
  `:units` is the total number of assertions `load-into` will make (what a progress bar
  divides by).  The fact and membership seqs are lazy and generated in chunks, so a
  ten-million-fact plan is a description rather than a heap full of lists."
  [params]
  (let [{:keys [types branching individuals predicates facts rules forward defeasible
                antecedents layers contexts seed]}
        (merge defaults params)
        mrng   (stream-rng seed :memberships)
        frng   (stream-rng seed :facts)
        rrng   (stream-rng seed :rules)
        ctxs   (if (< contexts 2)
                 [context-root]
                 (mapv context-name (range contexts)))
        bs     (bands (max 2 predicates) (max 2 layers))
        base   (first bs)
        icdf   (zipf-cdf (max 1 individuals) 1.0)
        tcdf   (zipf-cdf (max 1 types) 1.0)
        bcdf   (zipf-cdf (count base) 1.1)
        adist  (antecedent-counts antecedents)
        ;; the fact contexts form a **chain** under the schema context, not a fan of
        ;; siblings: two incomparable contexts have no common descendant, so a rule
        ;; joining a fact from each would complete with nowhere to put its conclusion
        ;; (`:no-placement`).  Down a chain every pair is comparable and the conclusion
        ;; lands in the deeper of the two.
        ;;
        ;; Bound rather than written inline in the map below, because `:units` is the
        ;; count of assertions `load-into` makes and this is one of the phases it counts:
        ;; the head edge under `CxCore` is an assertion the context *list* does not name,
        ;; so a unit total derived from that list runs one short of the bar it drives.
        cedges (cons (list 'genlCx context-root 'CxCore)
                     ;; each band sees the one above it — `(genlCx Sub Super)`,
                     ;; so the *second* element of a consecutive pair is the child
                     (map (fn [[super sub]] (list 'genlCx sub super))
                          (partition 2 1 (cons context-root
                                               (remove #{context-root} ctxs)))))
        ;; a type membership names a *specific* type: the tree is filled breadth-first,
        ;; so the deep (specific) types are the high indices — draw Zipf from the top
        ;; end so an individual is usually a leaf kind and only rarely a bare root one
        a-type #(type-name (- (max 1 types) 1 (zipf tcdf mrng)))     ; memberships only
        an-ind #(ind-name (zipf icdf frng))                          ; facts only
        ;; per target layer: the band it concludes into, and every band below it
        per-k  (into {} (for [k (range 1 (count bs))]
                          (let [cb (nth bs k)
                                lo (vec (mapcat #(nth bs %) (range k)))]
                            [k {:cb cb :ccdf (zipf-cdf (max 1 (count cb)) 1.3)
                                :lo lo :lcdf (zipf-cdf (max 1 (count lo)) 1.1)}])))]
    {:params       (merge defaults params)
     :context-edges cedges
     :genls        (genl-edges types branching)
     ;; every individual gets one type membership, in a context chosen round-robin so
     ;; the bands are evenly populated whatever the individual distribution does
     :memberships  (map (fn [i] [(list (a-type) (ind-name i)) (nth ctxs (mod i (count ctxs)))])
                        (range individuals))
     :facts        (map (fn [i] [(list (nth base (zipf bcdf frng)) (an-ind) (an-ind))
                                 (nth ctxs (mod i (count ctxs)))])
                        (range facts))
     ;; **Direction and defeasibility are two draws, not two thresholds on one index.**
     ;; Read off `(< i n)` they would be perfectly correlated: at any settings where
     ;; `defeasible` ≤ `forward`, every defeasible rule would also be a forward one, and
     ;; no settings at all would produce a defeasible *backward* rule — a shape the corpus
     ;; could not exercise however the knobs were turned.  Two percentage draws from the
     ;; rule stream's own `Random` keep them independent, at the price that each mix is a
     ;; share rather than an exact count.  Both are drawn in the `let` rather than in the
     ;; map below, so the order they consume the stream in is the source order here and
     ;; not a map literal's evaluation order.
     :rules        (map (fn [_]
                          (let [a    (nth adist (.nextInt rrng (count adist)))
                                k    (inc (.nextInt rrng (max 1 (dec (count bs)))))
                                {:keys [cb ccdf lo lcdf]} (per-k k)
                                vars (mapv #(symbol (str "?v" %)) (range (inc a)))
                                antes (mapv (fn [j] (list (nth lo (zipf lcdf rrng))
                                                          (nth vars j) (nth vars (inc j))))
                                            (range a))
                                conseq (list (nth cb (zipf ccdf rrng))
                                             (first vars) (peek vars))
                                fwd?  (< (.nextInt rrng 100) (long forward))
                                def?  (< (.nextInt rrng 100) (long defeasible))]
                            {:antecedents antes
                             :consequent  conseq
                             :direction   (if fwd? :forward :backward)
                             :defeasible? def?
                             :layer       k}))
                        (range rules))
     :units        (+ (count cedges) (max 0 types) individuals facts rules)}))

;; ---- loading it ----------------------------------------------------------

(def ^:private chunk-size
  "How many facts are asserted between progress reports.  Small enough that a bar moves
  and a cancel lands promptly, large enough that the report is not the cost."
  20000)

(defn- rule-sentence
  "The rule as a sentence, with its direction and defeasibility written the way an author
  writes them — a `set/*Rule` wrapper and a `set/defaultRule` around the implication.
  Both canonicalize into record fields, so this is only how they are *spelled*."
  [{:keys [antecedents consequent direction defeasible?]}]
  (cond-> (rules/wrap-direction (rules/rule-sentence antecedents consequent) direction)
    defeasible? (->> (list 'set/defaultRule))))

(defn load-into
  "Generate a KB from `params` and assert it into `kb`.  Returns a summary map.

  `:on-progress` is called with `{:phase :done :total :note}` at every phase boundary and
  every `chunk-size` assertions; it may **throw** to abort the load, which is how a
  caller cancels one (nothing is undone — the KB simply holds what had landed).  The
  chaining phase reports through the same callback (`chain`'s own `:on-progress`), so it
  moves and cancels like the assert phases; what it counts is conclusions rather than
  planned units, so it carries no total.

  The load is one `with-deferred-settle` per phase (belief reconciled once, not per
  fact), facts go through the bulk path (`v/bulk-assert-facts!` — they are well-formed by
  construction and deduped here, which are exactly that path's two preconditions), and
  forward chaining is left until the end: a rule that fires per arriving fact would do
  the same work N times over a growing KB and reach the same fixpoint."
  ([kb params] (load-into kb params {}))
  ([kb params {:keys [on-progress] :or {on-progress (fn [_])}}]
   (let [p       (merge defaults params)
         {:keys [context-edges genls memberships facts rules units]} (plan p)
         done    (volatile! 0)
         report  (fn [phase note]
                   (on-progress {:phase phase :done @done :total units :note note}))
         bump    (fn [phase n note] (vswap! done + n) (report phase note))
         ;; chaining counts something else entirely — conclusions, not units of planned
         ;; work — and a fixpoint has no total (the agenda grows as it derives), so the
         ;; total is cleared rather than left reading as the assert phases' one.  What
         ;; there is to show is how much has been concluded and how much agenda is left.
         chain-report (fn [{:keys [derived pending]}]
                        (on-progress {:phase :chaining :done (or derived 0) :total nil
                                      :note (if pending
                                              (format "derived · %,d on the agenda" (long pending))
                                              "forward chaining to a fixpoint")}))
         ;; The two fact phases are deduped here so the bulk path's "pairwise distinct"
         ;; precondition holds; a HashSet of the entries costs a fraction of what the
         ;; sentexes themselves will.
         ;;
         ;; Keyed on the **whole `[sentence context]` entry**, because that is the
         ;; precondition `bulk-assert-facts!` states: no two the same sentence *in the
         ;; same context*.  A sentence is a distinct sentex in each context that holds
         ;; it, so keying on the sentence alone would drop every repeat past the first
         ;; and make `:contexts` a knob that spreads the facts without adding any.
         seen    (java.util.HashSet.)
         fresh   (fn [batch] (into [] (filter #(.add seen %)) batch))
         load!   (fn [phase batches]
                   (doseq [batch batches]
                     (let [b (fresh batch)]
                       (doseq [[ctx group] (group-by second b)]
                         (v/bulk-assert-facts! kb (map first group) ctx))
                       (bump phase (count batch) nil))))]
     (report :vocabulary "loading the shipped vocabulary")
     (case (:base p)
       :starter (starter/load-into kb)
       (core-context/load-into kb))
     (report :contexts "wiring the contexts")
     (v/assert-many kb context-edges context-root {:chain? false})
     (bump :contexts (count context-edges) nil)
     (report :types "the type hierarchy, most general first")
     (doseq [batch (partition-all chunk-size genls)]
       (v/assert-many kb batch context-root {:chain? false})
       (bump :types (count batch) nil))
     (report :individuals "type memberships")
     (load! :individuals (partition-all chunk-size memberships))
     (report :rules "rules")
     (doseq [batch (partition-all 1000 rules)]
       (v/with-deferred-settle kb
         (doseq [r batch]
           (v/assert kb (rule-sentence r) context-root {:chain? false})))
       (bump :rules (count batch) nil))
     (report :facts "ground facts")
     (load! :facts (partition-all chunk-size facts))
     (let [chained (when (:chain? p)
                     (chain-report {})
                     ;; **Bounded by the layer count.**  A derivation over this rule set
                     ;; cannot legitimately cascade deeper than there are layers — every
                     ;; rule concludes strictly above what it reads.  Anything deeper is
                     ;; a join fanning out over itself, so the bound turns a corpus whose
                     ;; shape happens to be dense into a truncated run (reported as
                     ;; `:truncated?`) rather than a chain that does not come back.
                     (v/forward-chain kb {:max-depth (or (:max-depth p) (inc (:layers p)))
                                          :max-derivations (:max-derivations p)
                                          :on-progress chain-report}))]
       (report :done nil)
       {:params  p
        :units   units
        ;; the stored count, counted as storage: summing per-context reads the
        ;; *believed* genlCx closure, which undercounts a context no believed
        ;; edge reaches
        :stored  (v/sentex-count kb)
        :derived (:derived chained 0)
        :truncated? (boolean (:truncated? chained))}))))
