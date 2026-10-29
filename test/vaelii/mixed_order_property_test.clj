;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.mixed-order-property-test
  "Order independence over a **mixed** KB, on every storage backend.

  The per-subsystem shuffle tests each hold one mechanism still and permute the rest:
  `aggregate_test` the aggregates, `equality_test` the partition, `inherit_forward_test`
  the genl seeding, `constraint_nogood_test` the nogoods, `canonical_vars_test` the
  variable canonicalization, `asp_edge_test` the solver. `property_test` generates
  scenarios rather than writing them, but from one pool in one context.

  A mixed KB is where the mechanisms meet, and the meeting is the part no per-subsystem
  shuffle sees. So the pool here spans them at once: ground facts in three contexts
  joined by `genlCx` edges, a four-link `genl` chain, a defeasible rule and a monotonic
  one, a rule with a negated antecedent, a rule carrying its own `exceptWhen`, a `sameAs`
  edge above one of the context edges and two `equals` edges — one beside the fact it
  displaces, one on the type a rule fires on — and two chains that end where they began.
  A drawn subset routinely puts a taxonomy edge, an equality merge, an exception and a
  retraction into one KB, and the question is whether the arrival order of those decides
  anything.

  **The declarations that reach back are in the pool too**, because each is a mark whose
  arrival order is the whole question and none of them was drawn here before:

  - a rule guarded by `(different ?a ?b)`, which is negation as failure over the equality
    closure and over the `indeterminate_term` category and so names no handle a
    justification can carry — its two arguments are a pair one of the pool's own `equals`
    edges merges, and the category reaches it twice more, by a direct membership and by a
    kind declared under it;
  - `(functionalInArg keeperOf 1)` over a `(genl ownerOf keeperOf)` edge, so the mark, the
    edge and two facts are four ingredients of one merge and every arrival order runs a
    different retroactive arm;
  - `(symmetric walksWith)` over a pair **both** of whose spellings a rule concluded,
    which is the fold that has no bare premise to take;
  - `(predSpecifiedAll keeperOf dog)` over an `(arg keeperOf 1 person)` slot contract, an
    integrity audit that stores nothing and reads the believed extents, the elected
    spelling and the category at once.

  **What is compared, and why it is content.** Three readings, all handle-free:

  - the believed sentences **per assertion context**, and per **view** context up the
    `genlCx` ancestor set (which is where the exception force and the visibility condition land);
  - the belief label of each believed sentex — `defeat-class`, plus the contradiction
    and conflict tallies, so a flipped class or a double-counted dilemma surfaces;
  - the `genl` / `genlCx` closures at every probe type and context, plus the equality
    partition they are cached beside, the `different` answer over five probe pairs, and
    the integrity audit's violation set.

  `different` is read directly as well as through the conclusion it guards, and the reason
  is what makes it need the re-check index at all: it holds by the *absence* of a merge,
  so a firing it withdrew leaves nothing in the sentence sets to say why.

  Which sentexes are **stored** is deliberately absent, for `property_test`'s reason: a
  conclusion drawn and then defeated leaves a record an ordering that defeated its
  antecedent first never wrote, and both orderings read the same belief off different
  record sets. A stored sentex is not a believed one.

  **Every backend, one JVM.** `scripts/test-backends.sh` runs the whole suite on each of
  the eight, which is the thorough regression test and a thing somebody has to remember; this
  opens all eight itself, so an order-dependence that only appears under the durable
  index fails in an ordinary `lein test`. The KBs are private — their own spaces, and a
  private temp directory per durable arm — so they share a store with nothing.

  **Two runs of one property, and the difference is the seed.** The `:default` sweep
  fixes it and draws small scenarios, so a red is reproducible from the failure alone.
  The `^:slow` run takes three fixed seeds and draws the whole pool. Both assert one
  `is` per backend (per seed, in the slow one) whatever they find, so the assertion
  count is a property of the file rather than of the box."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [clojure.walk :as walk]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

;; ---- the vocabulary the pool is written in --------------------------------

(def ^:private cx-base  'CxMixBase)
(def ^:private cx-home  'CxMixHome)
(def ^:private cx-field 'CxMixField)

;; The contexts a reading is taken from: the three the pool writes in, plus the one the
;; `genlCx` edges are asserted in — an edge is forced global (docs/contexts.md), so where
;; it is stored may not decide what the closure says.
(def ^:private view-contexts [cx-base cx-home cx-field 'CxUniverse])

(def ^:private probe-types '[terrier dog mammal animal thing])
(def ^:private probe-terms '[Rex Nell Tom Thomas Bud Sparrow Ann Anna Kip Kipper])

(def ^:private probe-pairs
  "The term pairs the unique-name assumption is read over. Three are pairs an equality
  edge in the pool merges, one is a pair nothing merges, and one crosses the two sides of
  the world — so the reading holds a `different` that is true throughout, ones a merge
  turns false, and ones the `indeterminate_term` category turns false without any merge."
  '[[Kip Kipper] [Ann Anna] [Tom Thomas] [Rex Nell] [Kip Ann]])

(defn- default-rule [antes conseq]
  (list 'set/defaultRule (list 'set/forwardRule (list 'implies (cons 'and antes) conseq))))

;; Each entry is a **chain**: `[label op]` pairs that must run in the order written.
;; Most chains are one op long and constrain nothing; the two at the end hold a
;; retraction to the assertion whose handle it names, which a flat permutation cannot
;; say. Labelled so a shrunk counterexample prints the operations.
;;
;; Every chain is well-formed on its own and any sub-multiset runs in any linear
;; extension without throwing — so a failing property is an order-dependence and not a
;; bad input. A chain drawn twice re-asserts a sentence that canonicalizes to the handle
;; it already has, and the second retraction then names nothing, which `retract!` takes.
(def ^:private chain-pool
  [;; the two contexts, hung under the base
   [[:home-sees-base
     #(v/assert % (list 'genlCx cx-home cx-base) 'CxUniverse {:strength :monotonic})]]
   [[:field-sees-base
     #(v/assert % (list 'genlCx cx-field cx-base) 'CxUniverse {:strength :monotonic})]]
   ;; the genl chain, one link per chain so a subset can break it anywhere
   [[:terrier-is-a-dog
     #(v/assert % '(genl terrier dog) cx-base {:strength :monotonic})]]
   [[:dogs-are-mammals
     #(v/assert % '(genl dog mammal) cx-base {:strength :monotonic})]]
   [[:mammals-are-animals
     #(v/assert % '(genl mammal animal) cx-base {:strength :monotonic})]]
   ;; ground facts, spread over the two child contexts
   [[:rex-is-a-terrier
     #(v/assert % '(terrier Rex) cx-home {:strength :monotonic})]]
   [[:nell-is-a-dog
     #(v/assert % '(dog Nell) cx-field)]]
   [[:tom-is-a-mammal
     #(v/assert % '(mammal Tom) cx-field {:strength :monotonic})]]
   [[:bud-is-a-dog
     #(v/assert % '(dog Bud) cx-home)]]
   ;; the rules: a default, a monotonic one over its conclusion, one that triggers on a
   ;; negated antecedent, and one that states its own exception
   [[:dogs-bark
     #(v/assert % (default-rule '[(dog ?x)] '(barks ?x)) cx-base)]]
   [[:barking-is-audible
     #(v/assert-rule % '[(barks ?x)] '(audible ?x) cx-base {:direction :forward :strength :monotonic})]]
   [[:a-silent-dog-is-quiet
     #(v/assert-rule % '[(dog ?x) (not (barks ?x))] '(quiet ?x) cx-base {:direction :forward})]]
   [[:mammals-have-fur-unless-shorn
     #(v/assert % (list 'exceptWhen '(shorn ?x)
                        (default-rule '[(mammal ?x)] '(has_fur ?x)))
                cx-base)]]
   [[:rex-is-shorn
     #(v/assert % '(shorn Rex) cx-home {:strength :monotonic})]]
   ;; The equality edges, each over an individual a stored fact mentions — so a merge has
   ;; records to displace and a representative to elect, and the closure behind
   ;; `representative` / `equiv-class` is recomputed on an edge that can arrive anywhere
   ;; in the sequence.
   ;;
   ;; **The three positions a merge can sit in are all in the pool**, because each is a
   ;; different question about when migration runs and all three are settled by content
   ;; rather than by arrival:
   ;;
   ;; - `kip-equals-kipper` sits in the context holding the fact it displaces, which is
   ;;   the merge arriving beside its own records;
   ;; - `ann-is-anna` sits **above** a `genlCx` edge, so `cx-field` cannot see it until
   ;;   `field-sees-base` is drawn and arrives — and when that edge arrives last it is
   ;;   the edge, not the merge and not the fact, that owes the restatement;
   ;; - `tom-is-thomas` reaches a **rule**: `mammal` is what the excepted default fires
   ;;   on, so the merge retires the spelling the rule's own trigger arrives under, and
   ;;   the conclusion must be drawn once at the elected name whichever of the three
   ;;   came last.
   [[:ann-owns-nell
     #(v/assert % '(ownerOf Anna Nell) cx-field {:strength :monotonic})]]
   [[:ann-is-anna
     #(v/assert % '(sameAs Ann Anna) cx-base {:strength :monotonic})]]
   [[:kip-owns-rex
     #(v/assert % '(ownerOf Kip Rex) cx-home {:strength :monotonic})]]
   [[:kip-equals-kipper
     #(v/assert % '(equals Kip Kipper) cx-home {:strength :monotonic})]]
   [[:tom-is-thomas
     #(v/assert % '(equals Tom Thomas) cx-base {:strength :monotonic})]]
   ;; ---- the chains that end where they began ----
   ;; A fact learned and forgotten. While it stands it feeds the default rule and
   ;; whatever the default feeds, so the retraction has a cascade to sweep.
   [[:sparrow-is-a-dog
     #(v/assert % '(dog Sparrow) cx-field)]
    [:forget-the-sparrow
     #(v/retract! % (v/handle-of % '(dog Sparrow) cx-field))]]
   ;; A doubt raised and withdrawn. This one defeats rather than adds, and it is also
   ;; what makes `a-silent-dog-is-quiet` fire: while it stands Nell is quiet rather than
   ;; barking, and lifting it has to take the quiet back.
   [[:doubt-nells-barking
     #(v/assert % '(not (barks Nell)) cx-field {:strength :monotonic})]
    [:withdraw-the-doubt
     #(v/retract! % (v/handle-of % '(not (barks Nell)) cx-field))]]

   ;; ---- the unique-name guard, and the three things that suspend it ----
   ;; A `(different ?a ?b)` antecedent is negation as failure over TWO inputs: the
   ;; equality closure, and the `indeterminate_term` category whose members are exempt
   ;; from the unique-name assumption. It holds by the *absence* of a merge, so it names
   ;; no handle a justification can carry and no `SupportingProver` support can reach it —
   ;; the re-check index is the only instrument that can withdraw or restore the firing,
   ;; and this pool is where it meets everything else.
   ;;
   ;; The guard's two arguments are **Kip and Kipper**, which `kip-equals-kipper` above
   ;; already merges, so one flip source is a chain the pool had before this one. The
   ;; other two are the category itself and a kind declared under it, which reaches the
   ;; guard through the genls fan rather than by name.
   [[:kipper-owns-rex-too
     #(v/assert % '(ownerOf Kipper Rex) cx-home {:strength :monotonic})]]
   [[:two-owners-are-shared-custody
     #(v/assert % (default-rule '[(ownerOf ?a ?d) (ownerOf ?b ?d) (different ?a ?b)]
                                '(shared_custody ?d))
                cx-base)]]
   [[:kipper-is-indeterminate
     #(v/assert % '(indeterminate_term Kipper) 'CxUniverse {:strength :monotonic})]]
   [[:an-uncertain-thing-is-indeterminate
     #(v/assert % '(genl uncertain_thing indeterminate_term) cx-base {:strength :monotonic})]]
   [[:kip-is-uncertain
     #(v/assert % '(uncertain_thing Kip) cx-home {:strength :monotonic})]]

   ;; ---- a functional mark on a super-predicate, and the edge that carries it down ----
   ;; `(functionalInArg keeperOf 1)` says the other argument determines argument 1, and it
   ;; is read up the predicate hierarchy, so the mark, the `(genl ownerOf keeperOf)` edge
   ;; and the two `ownerOf` facts are four ingredients of one merge. Each arrival order
   ;; runs a different arm — the facts last meet an ingested mark, the mark last runs
   ;; `special/equate-existing`, the edge last runs `special/equate-under-edge`, whose
   ;; mark check read the arity-2 spelling alone until 0.14.0. Both fillers are symbols, so the
   ;; pair merges rather than being refused, and the merge is a second route to the class
   ;; `kip-equals-kipper` elects.
   [[:one-keeper-per-animal
     #(v/assert % '(functionalInArg keeperOf 1) 'CxUniverse {:strength :monotonic})]]
   [[:owning-is-keeping
     #(v/assert % '(genl ownerOf keeperOf) cx-base {:strength :monotonic})]]

   ;; ---- a symmetric mark over a pair two rules concluded ----
   ;; The mark's effect is canonicalization: the entry point sorts a symmetric literal's
   ;; arguments, so a mark arriving after the facts migrates the records. Here BOTH
   ;; spellings of the proposition are a rule's conclusion off the same `ownerOf` fact, so
   ;; neither row can leave by having its premise dropped and the fold runs through
   ;; `integrate/fold-supports!` instead. The arguments are also what the pool's two
   ;; equality edges merge, so the fold and the migration meet.
   [[:an-owner-walks-the-dog
     #(v/assert-rule % '[(ownerOf ?o ?d)] '(walksWith ?o ?d) cx-base {:direction :forward})]]
   [[:the-dog-walks-the-owner
     #(v/assert-rule % '[(ownerOf ?o ?d)] '(walksWith ?d ?o) cx-base {:direction :forward})]]
   [[:walking-is-mutual
     #(v/assert % '(symmetric walksWith) 'CxUniverse {:strength :monotonic})]]

   ;; ---- the integrity audit, which reads belief and stores nothing ----
   ;; `(predSpecifiedAll keeperOf dog)` requires every dog to have a determinate keeper,
   ;; and `(arg keeperOf 1 person)` is where the required filler type is stated — the
   ;; declaration restates no type of its own, so the slot contract is a fourth input the
   ;; audit reads and a fourth chain the pool permutes. The audit is a read, so its own
   ;; order independence is structural; what makes it worth drawing is *what* it reads —
   ;; the believed extents, the equality partition that decides which name a filler
   ;; carries, the slot contract that decides which fillers count, and the
   ;; `indeterminate_term` category that decides whether the filler counts at all. Each
   ;; declaration audits every reader seeing the requirement and a defining home.
   ;; The ancestor's requirement reaches the child-local populations. Bud has no keeper in this
   ;; pool, so the home reading remains nonempty rather than silently vacuous.
   [[:a-keeper-is-a-person
     #(v/assert % '(arg keeperOf 1 person) cx-base {:strength :monotonic})]]
   [[:every-dog-has-a-person
     #(v/assert % '(predSpecifiedAll keeperOf dog) cx-base {:strength :monotonic})]]
   [[:every-home-dog-has-a-person
     #(v/assert % '(predSpecifiedAll keeperOf dog) cx-home {:strength :monotonic})]]
   [[:every-field-dog-has-a-person
     #(v/assert % '(predSpecifiedAll keeperOf dog) cx-field {:strength :monotonic})]]
   [[:ann-is-a-person
     #(v/assert % '(person Ann) cx-base {:strength :monotonic})]
    [:kip-is-a-person
     #(v/assert % '(person Kip) cx-base {:strength :monotonic})]]])

(defn- op-of    [[ci si]] (second (nth (nth chain-pool ci) si)))
(defn- label-of [[ci si]] (first  (nth (nth chain-pool ci) si)))

(defn- chain-index
  "The pool index of the chain whose first step carries `label`.  The witness below names
  the chains it wants by what they do rather than by where they sit, so a chain inserted
  above one of them does not silently re-point it at another."
  [label]
  (or (first (keep-indexed (fn [i c] (when (= label (ffirst c)) i)) chain-pool))
      (throw (ex-info "no chain carries that label" {:label label}))))

;; ---- the reading ----------------------------------------------------------

(defn- name-by-content
  "`form` with every `(sentexHandle N)` term replaced by the **sentence** stored at N.

  A meta-sentex predicates about another sentex by naming its handle, and `exceptWhen`
  is stored that way (docs/exceptions.md): the rule keeps its own handle and the
  exception becomes `(exceptWhen <query> (sentexHandle H))` beside it. So the stored
  sentence carries an allocation order *inside its own content*, and two orderings that
  attach the same exception to the same rule spell it `(sentexHandle 1)` and
  `(sentexHandle 2)`. Neither belief nor the attachment differs; only the number does.
  What the claim is about is the referent's content, which is what this substitutes.
  Bounded, so a meta naming a meta terminates whatever the store holds."
  ([kb form] (name-by-content kb form 4))
  ([kb form depth]
   (if (neg? ^long depth)
     form
     (walk/postwalk
      (fn [x]
        (if-let [id (and (v/sentex-handle? x) (v/handle-id x))]
          (if-let [sx (v/sentex kb id)]
            (list 'sentexHandle (name-by-content kb (v/sentence-of sx) (dec (long depth))))
            x)
          x))
      form))))

(defn- believed-rows
  "`{:handle :sentence :context}` for every believed sentex — the handle is carried for
  the label reads below and never compared."
  [kb]
  (into []
        (keep (fn [h]
                (when (v/in? kb h)
                  (when-let [sx (v/sentex kb h)]
                    {:handle   (long h)
                     :sentence (name-by-content kb (v/sentence-of sx))
                     :context  (:context sx)}))))
        (tu/sentex-ids kb)))

(defn- reading
  "A whole-KB reading, compared as one value across orderings. Content and belief only."
  [kb]
  (let [rows (believed-rows kb)]
    {;; the believed sentences, grouped by the context they were asserted in
     :believed-by-context
     (reduce (fn [m r] (update m (:context r) (fnil conj #{}) (:sentence r))) {} rows)
     ;; and grouped by the context a reader stands in: up the genlCx ancestor set, after the
     ;; exception cascade that context can see
     :visible-from
     (into {} (for [c view-contexts]
                [c (into #{} (comp (filter #(and (v/sees? kb c (:context %))
                                                 (v/believed? kb (:handle %) c)))
                                   (map :sentence))
                         rows)]))
     ;; the belief label of each, keyed by content
     :defeat-classes
     (into {} (map (fn [r] [[(:context r) (:sentence r)] (v/defeat-class kb (:handle r))])) rows)
     :contradictions (count (v/contradictions kb))
     :conflicts      (count (v/conflicts kb))
     ;; the cached closures, per context because a closure is scoped
     :genls   (into {} (for [c view-contexts t probe-types] [[c t] (v/genls kb t c)]))
     :specs   (into {} (for [c view-contexts t probe-types] [[c t] (v/specs kb t c)]))
     :isa     (into {} (for [c view-contexts x probe-terms t probe-types]
                         [[c x t] (v/isa? kb x t c)]))
     :context-up   (into {} (for [c view-contexts] [c (v/context-up kb c)]))
     :context-down (into {} (for [c view-contexts] [c (v/context-down kb c)]))
     ;; the equality partition, cached and recomputed the same way the closures are
     :equiv-class    (into {} (for [c view-contexts x probe-terms] [[c x] (v/equiv-class kb x c)]))
     :representative (into {} (for [c view-contexts x probe-terms] [[c x] (v/representative kb x c)]))
     ;; the unique-name assumption, which a merge suspends in one direction and an
     ;; `indeterminate_term` membership in the other. Read here as well as through the
     ;; conclusion it guards, because the guard names no handle and a firing it withdrew
     ;; leaves nothing in the sentence sets above to say why
     :different (into {} (for [c view-contexts [x y] probe-pairs]
                           [[c x y] (v/ask? kb (list 'different x y) c)]))
     ;; the integrity audit, which reads the believed extents, the partition and the
     ;; category at once and stores nothing
     :specified (into {} (for [c view-contexts] [c (v/all-specified-violations kb c)]))}))

(defn- run-order
  "Apply one ordering to a fresh KB over `opts`' stores and read it.

  A **new KB value** per ordering rather than one KB cleared between them: `clear!`
  empties the stores and says so, but the JTMS and the taxonomy live in memory and it
  leaves them where they are (`core/clear!`, and it is what `tu/fresh` re-opens for).
  Two KBs over one durable directory share the store, so a durable arm re-opens rather
  than remounting."
  [opts order]
  (let [kb (doto (v/open-kb (assoc opts :recover? false)) (tu/clear-kb!))]
    (doseq [step order] ((op-of step) kb))
    (reading kb)))

(defn- disagreement
  "nil when every ordering reads the same, else the first key they differ at with the
  distinct values under it — a whole-map mismatch over fourteen keys names none of them."
  [opts orders]
  (let [readings (mapv #(run-order opts %) orders)
        head     (first readings)]
    (some (fn [k]
            (let [vs (into #{} (map #(get % k)) readings)]
              (when (< 1 (count vs)) {:key k :values vs})))
          (sort-by str (keys head)))))

;; ---- the backends ---------------------------------------------------------

;; A private temp directory per durable arm rather than one derived from a space
;; number: a derived directory is a fixed global path, so a previous run that was killed
;; rather than closed leaves its single-writer lock behind and every later run fails on
;; it.
(defn- disk-dir []
  (str (java.nio.file.Files/createTempDirectory
        "vaelii-mixorder-" (into-array java.nio.file.attribute.FileAttribute []))))

(defn- backends
  "The eight `scripts/lib/suite-configs.sh` names, as opts. Namespaced spaces, so a KB
  here shares a store with nothing — not another test's, and not its own siblings'."
  []
  [{:backend :memory          :space [::mix :memory]}
   {:backend :memory-dense    :space [::mix :dense]}
   {:backend :memory-columnar :space [::mix :columnar]}
   {:backend :disk-memory     :dir (disk-dir)}
   {:backend :disk-dense      :dir (disk-dir)}
   {:backend :disk-columnar   :dir (disk-dir)}
   {:backend :disk-log        :dir (disk-dir)}
   ;; the fork decorator over an EMPTY base (docs/overlay.md): every merge rule
   ;; degenerates, so the orderings must agree exactly as they do on the plain store
   {:backend :overlay
    :base    {:backend :memory :space [::mix :overlay-base]}
    :overlay {:backend :memory :space [::mix :overlay-top]}}])

(defn- on-backend
  "Call `(f opts)`, and leave nothing behind — a durable arm holds a single-writer lock
  and file handles for the JVM's life unless it is closed."
  [opts f]
  (try (f opts)
       (finally
         (doto (v/open-kb (assoc opts :recover? false)) (tu/clear-kb!))
         (when-let [dir (:dir opts)]
           ((requiring-resolve 'vaelii.impl.disk.backend/close-dir!) dir)
           ;; best-effort: the durability daemon may still hold a handle, in which case
           ;; a few KB survive in the OS temp directory — which is what it is for
           (doseq [f (reverse (file-seq (java.io.File. ^String dir)))]
             (.delete ^java.io.File f))))))

;; ---- the generator --------------------------------------------------------

(defn- gen-linearization
  "One random linear extension of `chains`: at each step take the head of a chain that
  still has steps left, so every chain keeps its own order while the chains interleave
  freely. Written out rather than taken from a test.check combinator, so it stays fixed
  across versions of the library."
  [chains]
  (let [chains (into [] (remove empty?) chains)]
    (if (empty? chains)
      (gen/return [])
      (gen/let [i    (gen/choose 0 (dec (count chains)))
                tail (gen-linearization (update chains i rest))]
        (into [(first (nth chains i))] tail)))))

(defn- steps-of
  "The drawn chain indices as chains of `[chain-index step-index]` steps — data, so a
  shrunk counterexample prints as something a reader can map back to labels."
  [picks]
  (mapv (fn [ci] (into [] (map-indexed (fn [si _] [ci si])) (nth chain-pool ci))) picks))

(defn- gen-scenario
  "A sub-multiset of the pool, `lo` to `hi` chains, and `n` independent orderings of it.
  Independent orderings rather than the written order against a reordering: with chains
  the written order is one linear extension among many and has no claim to be the
  reference, and drawing them all makes the property symmetric in what it compares."
  [lo hi n]
  (gen/let [picks  (gen/vector (gen/choose 0 (dec (count chain-pool))) lo hi)
            orders (apply gen/tuple (repeat n (gen-linearization (steps-of picks))))]
    (vec orders)))

(defn- labels-of [orders] (mapv #(mapv label-of %) orders))

(defn- check-seed
  "Run the property against one backend at one seed and report it as one `is`, whatever
  it finds — so the assertion count is a property of the file and not of what it found."
  [opts scenario num-tests seed]
  (let [res      (tc/quick-check num-tests
                                 (prop/for-all [orders scenario]
                                               (nil? (disagreement opts orders)))
                                 :seed seed)
        smallest (some-> res :shrunk :smallest first)]
    (is (:pass? res)
        (str (name (:backend opts)) " reads two orderings of one KB differently"
             " (seed " seed ")"
             (when smallest
               (str "\n  orderings: " (pr-str (labels-of smallest))
                    "\n  " (pr-str (disagreement opts smallest))))))))

;; ---- the properties -------------------------------------------------------

;; Small scenarios and a fixed seed: the draws are the same on every machine and every
;; run, so a red reproduces from the failure alone.
(def ^:private default-seed 20260825)

(deftest a-mixed-kb-reads-the-same-in-any-order
  ;; Parity between orderings that all did nothing is worthless, so assert the pool's shape
  ;; first: run every chain in the order written and check the KB it builds is the
  ;; interaction-dense one the docstring claims.
  (testing "the pool is not vacuous"
    (on-backend {:backend :memory :space [::mix :witness]}
                (fn [opts]
                  (let [r (run-order opts (into [] cat (steps-of (range (count chain-pool)))))]
                    (is (contains? (get-in r [:visible-from cx-home]) '(barks Bud))
                        "the default rule fired, over a type it reaches by the genl chain")
                    (is (contains? (get-in r [:visible-from cx-home]) '(audible Bud))
                        "and the monotonic rule fired on its conclusion")
                    (is (contains? (get-in r [:visible-from cx-home]) '(has_fur Bud))
                        "the excepted rule concluded where its exception does not hold")
                    (is (not (contains? (get-in r [:visible-from cx-home]) '(has_fur Rex)))
                        "and was blocked where it does")
                    (is (= '#{terrier dog mammal animal} (get-in r [:genls [cx-home 'terrier]]))
                        "the genl chain closed")
                    (is (= #{cx-base cx-home} (get-in r [:context-up cx-home]))
                        "and the genlCx edge did")
                    (is (contains? (get-in r [:visible-from cx-field]) '(barks Nell))
                        "a sibling context's own conclusion is visible from it")
                    (is (not (contains? (get-in r [:visible-from cx-home]) '(barks Nell)))
                        "and not from the other side of the ancestor set")
                    (is (= (get-in r [:representative [cx-field 'Ann]])
                           (get-in r [:representative [cx-field 'Anna]]))
                        "the sameAs edge merged")
                    (is (contains? (get-in r [:believed-by-context cx-field])
                                   (list 'ownerOf (get-in r [:representative [cx-field 'Ann]]) 'Nell))
                        "and the fact it displaced, a context edge below it, is restated")
                    (is (contains? (get-in r [:visible-from cx-field]) '(has_fur Thomas))
                        "the merge on the rule's own type concludes at the elected spelling")
                    (is (not (contains? (get-in r [:visible-from cx-field]) '(has_fur Tom)))
                        "and nowhere else")
                    (is (not (contains? (get-in r [:believed-by-context cx-field]) '(dog Sparrow)))
                        "and the chains that end where they began left nothing behind")
                    ;; the symmetric mark folded the pair both rules concluded: one row
                    ;; for one proposition, spelled the way the entry point spells it
                    (is (contains? (get-in r [:believed-by-context cx-home]) '(walksWith Kip Rex))
                        "the two rules' conclusions are one row at the sorted spelling")
                    (is (not (contains? (get-in r [:believed-by-context cx-home])
                                        '(walksWith Rex Kip)))
                        "and the mirror is not a second row beside it")
                    ;; the functionalInArg mark reached the sub-predicate's facts through
                    ;; the genl edge, and the merge it derived elects the same class the
                    ;; stated `equals` edge does
                    (is (= 'Kip (get-in r [:representative [cx-home 'Kipper]]))
                        "the two names for one keeper are one thing")
                    (is (not (contains? (get-in r [:believed-by-context cx-home])
                                        '(ownerOf Kipper Rex)))
                        "so the retired spelling is not believed beside the elected one")
                    ;; ...which makes the guard false, and the firing it licensed goes
                    (is (false? (get-in r [:different [cx-home 'Kip 'Kipper]]))
                        "a merge suspends the unique-name assumption for the pair")
                    (is (not (contains? (get-in r [:believed-by-context cx-home])
                                        '(shared_custody Rex)))
                        "and one owner under two names is not two owners")
                    ;; the kind declared under `indeterminate_term` suspends it for a term
                    ;; no merge touched, and only where the membership is visible
                    (is (false? (get-in r [:different [cx-home 'Kip 'Ann]]))
                        "an indeterminate term is not provably different from anything")
                    (is (true? (get-in r [:different [cx-base 'Kip 'Ann]]))
                        "and the exemption stops where the membership stops being visible")
                    ;; the audit reads all three: the extents, the elected spelling and
                    ;; the category
                    (is (= {'[predSpecifiedAll keeperOf dog]
                            {:status :audited :violations '#{Rex Bud}}}
                           (get-in r [:specified cx-base]))
                        "the ancestor requirement is checked in both child readers")
                    (is (= {'[predSpecifiedAll keeperOf dog]
                            {:status :audited :violations '#{Rex Bud}}}
                           (get-in r [:specified cx-home]))
                        "Bud has no keeper at all, and Rex's is an indeterminate term")
                    (is (= {'[predSpecifiedAll keeperOf dog]
                            {:status :audited :violations '#{Rex Bud}}}
                           (get-in r [:specified cx-field]))
                        "the shared ancestor requirement retains the failing home reader")))))
  (testing "and the guard the pool suspends can be seen holding"
    ;; Every reading above is of a guard something has made false, which on its own would
    ;; leave a rule that never fires indistinguishable from one that always does. This
    ;; draws the same rule over the same two owners with neither the merge nor the
    ;; indeterminacy in the KB, so the positive side of `different` is on the record too.
    (on-backend {:backend :memory :space [::mix :witness-una]}
                (fn [opts]
                  (let [r (run-order opts
                                     (into [] cat
                                           (steps-of (mapv chain-index
                                                           [:home-sees-base :terrier-is-a-dog
                                                            :rex-is-a-terrier :kip-owns-rex
                                                            :kipper-owns-rex-too
                                                            :two-owners-are-shared-custody]))))]
                    (is (true? (get-in r [:different [cx-home 'Kip 'Kipper]]))
                        "nothing has merged the two names or declared either indeterminate")
                    (is (contains? (get-in r [:believed-by-context cx-home])
                                   '(shared_custody Rex))
                        "so they are two owners and the guarded rule fires")))))
  (let [scenario (gen-scenario 3 8 3)]
    (doseq [opts (backends)]
      (testing (str "backend " (name (:backend opts)))
        (on-backend opts #(check-seed % scenario 4 default-seed))))))

;; The search half: three seeds and the whole pool, so a shape the fixed seed never draws
;; has somewhere to be found. The seeds are written down rather than taken from the
;; clock — a counterexample nobody can re-run is a counterexample nobody fixes.
(def ^:private slow-seeds [20260825 314159265 987654321])

(deftest ^:slow a-large-mixed-kb-reads-the-same-in-any-order
  (let [scenario (gen-scenario 6 (count chain-pool) 3)]
    (doseq [opts (backends)]
      (testing (str "backend " (name (:backend opts)))
        ;; one `is` per seed, and the durable arm's directory torn down once at the end
        ;; rather than per seed
        (on-backend opts
                    (fn [o] (doseq [seed slow-seeds]
                              (check-seed o scenario 12 seed))))))))
