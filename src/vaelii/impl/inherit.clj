;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.inherit
  "**Argument-position preservation** — when a claim about one term licenses the same
  claim about another.

  `(largerThan dog cat)` says something about two *kinds*.  Whether it also says
  something about a golden retriever and a maine coon is not decidable from the
  sentence: it depends on whether the relation distributes over the kinds' members.
  Some relations do (`disjoint` — subtypes of disjoint types are disjoint) and some
  emphatically do not (a chihuahua is a dog, a maine coon is a cat, and the maine coon
  is bigger).  So it is **declared**, per predicate, per argument position:

      (transitiveInArg        P n R)   ; a stored (P … w …) licenses (P … a …) when (R a w)
      (transitiveInArgInverse P n R)   ; …licenses it when (R w a)

  `R` is any **transitive** relation — `genl` and `genlCx` through their cached
  closures, or a predicate declared `(transitive R)` walked over stored facts.  A
  declaration over anything else is refused at assert
  (`wff/arg-preserving-problems`): the reach is walked to a fixpoint, so a relation
  that was never said to compose would have transitivity *manufactured* for it, and
  `(arg transitiveInArg 3 transitive)` cannot say so — arg is
  open-world, and an untyped relation cannot violate it.  Naming the relation is what
  keeps this from being a `genl` special case: an argument can equally be preserved
  along `partOf`, `connectedTo`, or anything else transitive.  The inverse form exists
  so the *other* direction never requires declaring an inverse predicate that has no
  other purpose.

  Several declarations may name one argument position; their reaches **union**, since
  each independently licenses the claim.

  ## Preservation stays on one side of the type/instance line

  `genl` relates **types**, so `(largerThan dog cat)` preserved along `genl` reaches
  `golden_retriever` and `maine_coon` and stops there.  It says nothing about Rex and
  Whiskers, and that is not a gap here to fill: `relation_kind` is a `disjoint_metatype`
  over `type_relation_predicate` and `instance_relation_predicate`, so one predicate
  symbol relates kinds *or* instances and never both.  A `largerThan` that inherited
  across the line would be a predicate of both kinds at once, which the KB's own
  meta-ontology refuses.

  Preservation moves an argument along a relation, leaving the predicate and the level
  it lives at alone.  Crossing the line is a *different* claim — it links two
  predicates and has a quantifier reading to pin down (every member? some member?) —
  and the vocabulary for it is `(typeToInstancePred TypePred InstancePred)`, which
  records the pairing for a reader and is inferred from by nothing.

  ## Specificity, and why it is not the deleted axis

  The interesting case is a claim that inherits *and* a more specific claim that
  disagrees.  `(typicallyLargerThan dog cat)` reaches `[chihuahua maine_coon]`;
  `(typicallyLargerThan maine_coon chihuahua)` is stated directly.  The stated one
  wins, and the general one simply **does not fire for that pair** — undercutting, not
  defeat.  Nothing is derived, so there is nothing to arbitrate.

  That matters, because `docs/nmtms.md` deleted genl-based specificity as an
  arbitration axis on the grounds that it was inference *about* the knowledge rather
  than *from* it: it scored a type by the size of its up-closure, a numeric proxy that
  tied silently whenever the exception was not keyed on a narrower type.  Nothing here
  reconstructs an ordering.  Two claims are compared along the **very relation the
  inheritance travels down** — `[maine_coon chihuahua]` is below `[cat dog]` because
  `(genl maine_coon cat)` and `(genl chihuahua dog)` are edges the KB holds.  Claims
  that are genuinely incomparable are not ranked at all; they come back `:ambiguous`,
  which is the same answer the engine gives every other unresolvable clash.

  ## Strict versus typical, for free

  A `:monotonic` claim is **never** undercut.  Strength already propagates from a
  justification's antecedents, so `(largerThan dog cat)` asserted `{:strength
  :monotonic}` inherits as known-true and a contrary specific claim is a
  contradiction, while `(typicallyLargerThan dog cat)` at the default `:default`
  inherits defeasibly and yields to the specific claim.  One declaration, both
  behaviours, and the difference is stated where it belongs: on the claim, not on the
  vocabulary.

  Where the contradiction goes depends on how the contrary claim is spelled.  A converse
  under an `(asymmetric P)` is `checks/asymmetry-problem`'s, and known-true content
  refuses it at the entry point.  A plain `(not (P a b))` needs no mark and is not refused: it is
  admitted and paired with the inherited claim by `settle/preserving-nogoods`, whose
  members are the general claim and everything the reading rests on, so `decide-nogood`
  weighs the set and the weakest member decides (`clashing-claim` below,
  `docs/inherit.md` for the readings).

  Ground goals only.  An open argument is left to the fact and rule provers, in the
  shape `different` and the NAF operators already use — enumerating it would mean
  walking the inverse reach of every stored witness, which is a different and much
  larger question than the one a closed goal asks."
  (:require [vaelii.impl.jtms :as jtms]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.strength :as st]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(def declarations
  "The two declaration functors, mapped to whether they read `R` backwards."
  '{transitiveInArg false, transitiveInArgInverse true})

;; ---- one question, one set of closure reads ------------------------------

(def ^:dynamic *memo*
  "A per-question cache for the two reads every layer here repeats — an atom of
  `{[:positions pred context] -> …, [:reach rel inverse? x context] -> set}`, or nil
  for no memoization.

  Answering one ground goal asks for a predicate's declared positions from
  `applicable?`, `verdict`, `surviving` and `claims`, and for a term's reach once per
  preserved position and then again per *pair* of claims inside `undercut?`.  Neither
  answer can change while the question is being answered — a query never mutates
  belief — so the memo is created fresh per top-level question and needs no
  invalidation protocol at all.  `with-memo` reuses an outer one when a caller has
  already opened it, which is the discipline `observe/*reach-memo*` follows for the
  transitive closure."
  nil)

(defmacro with-memo
  "Answer `body` under a memo, reusing the enclosing one when there is one.

  **`body` must be eager**, the precondition `observe/with-search-scope` carries for the
  same reason: a lazy seq handed back from here realizes after the binding frame has
  popped, so every `positions` and `reach` its elements ask for is walked again from
  scratch. Nothing reports that — the answers are identical — so each seq-returning
  layer below realizes before it returns."
  [& body]
  `(binding [*memo* (or *memo* (atom {}))] ~@body))

(defn- memoized [k f]
  (if-let [m *memo*]
    (if (contains? @m k)
      (get @m k)
      (let [v (f)] (swap! m assoc k v) v))
    (f)))

(def virtual-relations
  "The relations `witness-terms` walks from a cached closure of the engine's own
  rather than from stored `(R a b)` facts — the type hierarchy and the context
  hierarchy.  Both are transitive by construction, so a `(transitive R)` declaration
  on them is inert (it never routes them to the generic prover); every other relation
  must carry one, which is what `wff/arg-preserving-problems` reads this set to decide.
  The same set the taxonomy names `closure-relations`."
  tax/closure-relations)

;; ---- the declared positions ---------------------------------------------
;; Read as ordinary stored sentexes through `matches-visible`, exactly as `arg` and
;; `genlArg` are — so they are context-scoped and belief-following with no cache of
;; their own, and a retracted declaration stops applying the moment it stops being
;; believed.

(defn usable-relation?
  "May a declaration's `R` be walked?  Either the engine owns its closure, or the KB
  says it composes.  Read at *use* and not only at assert, so retracting
  `(transitive R)` stops the inheritance it licensed the way retracting anything else
  here does — the declaration is stored, but a relation nobody currently says is
  transitive is one whose reach we have no right to close.  Read from `context`, like
  the declaration itself: a transitivity claim some invisible context makes is not
  a licence this one holds."
  [tax rel context]
  (boolean (or (contains? virtual-relations rel)
               (tax/has-prop? tax :transitive rel context))))

(def ^:private declaration-functors
  "`declarations`' keys, held rather than re-`keys`-ed: `declared-anywhere?` runs on
  every `applicable?` of a preservation-aware prover."
  (vec (keys declarations)))

(defn declared-about?
  "Could any stored declaration name `pred`?  The declaration functors' roots
  intersected with the argument root at position 1, where a declaration's predicate
  sits — one set intersection per functor, against a root that is empty for nearly
  every KB and tiny for the rest.

  This is a **gate, not an answer**: it is neither belief-filtered nor context-scoped,
  so a true says only that the real read is worth making.  A false is exact, because a
  declaration naming `pred` would be in that intersection whatever anyone believes
  about it.  That is also what makes it the right question for a *conservative* caller
  that wants no answer at all, only \"could preservation be in play here\":
  `settle/cross-argument-predicate?` reads it to decide whether an exception conjunct's
  arguments may be compared with a trigger's, where an under-selection is a missed
  withdrawal.

  It earns its place on the query path rather than the assert path.  `positions` is
  read by `TransitiveInArgProver.applicable?` and by `provers/shadowing-channels`, so it
  runs for **every goal's functor in the KB**, and each real read is two
  `matches-visible` calls.  Ungated, one declaration anywhere made a `genl` goal cost
  2.8x what it costs in a KB with none — a tax every query pays for a feature almost
  none of them use.

  Two stages, because the two questions have different prices and different answers.
  The **cardinality** read is O(1) and false for nearly every KB there is, so it comes
  first and nothing else runs; the **intersection** is a real (if small) index read
  and only a KB that declares something ever pays it."
  [kb pred]
  (let [idx (:index kb)]
    (boolean
     (some (fn [f]
             (and (pos? (reads/stored-count-with-functor idx f))
                  (seq (reads/as-stored-with-args idx f {1 pred}))))
           declaration-functors))))

(defn positions
  "`[{:n :rel :inverse? :handle :in} …]` — the preserved argument positions declared for
  `pred`, visible from `context`, whose relation is one this may actually walk.  Empty
  (the overwhelmingly common case) means the predicate inherits nothing and every
  consumer here is a no-op.

  Several declarations may name one position; they are not collapsed here, because
  their reaches **union** (`reach`) rather than compete.

  Each carries the `:handle` of the declaration it was read off, which is what
  `support-for` names when a firing rests on the move it licenses: the declaration is
  as much a reason for an inherited claim as the claim itself, and retracting it has to
  withdraw whatever was concluded.

  **`:in` is the context the declaration was asserted in**, and it is here because
  `move-support` names *one* declaration out of the several that may license a move:
  `[rel, inverse?, n]` fixes the declaration's whole sentence, so two visible statements
  of it differ only in where they were said, and without `:in` the choice would fall to
  `matches-visible`' answer set — handle order, which is arrival order.  It costs one
  record fetch per declaration, paid inside the memo rather than per firing, over a list
  that is empty for nearly every predicate.

  Realized rather than lazy, and memoized on `[pred context]`: four layers of one
  question ask for this, and each computation is two `matches-visible` calls.

  Behind a root-intersection gate on any declaration naming `pred` at all, so a
  predicate nobody declared about — which is every predicate but a handful, in every
  KB — pays one intersection against an empty root rather than two index lookups.  The
  same shape of gate `special.clj` puts in front of the exception re-check triggers,
  for the same reason."
  [kb pred context]
  (when (and (symbol? pred) (declared-about? kb pred))
    (memoized [:positions pred context]
              #(vec (for [[f inverse?] declarations
                          [h b] (res/matches-visible kb (list f pred '?n '?rel) context)
                          :let  [n (get b '?n) rel (get b '?rel)]
                          :when (and (integer? n) (pos? n) (symbol? rel)
                                     (usable-relation? (reasoning/taxonomy kb) rel context))]
                      {:n n :rel rel :inverse? inverse? :handle h
                       :in (:context (p/get-sentex (:records kb) h))})))))

(defn declarations-exist?
  "Does this KB declare any preservation at all?  One set-cardinality read per
  declaration functor, false for nearly every KB there is, and the gate in front of
  every read the forward path makes: `moved-predicates` runs per datum of a chaining
  run, where a KB that declares nothing must pay O(1) and stop.

  Neither belief-filtered nor context-scoped, for `declared`'s reason — a false is
  exact whatever anyone believes, since a declaration would be in the root."
  [kb]
  (let [idx (:index kb)]
    (boolean (some #(pos? (reads/stored-count-with-functor idx %)) declaration-functors))))

(defn declared
  "Every declaration's `[P R]` pair — the predicate that inherits, and the relation it
  inherits along — read off the functor roots rather than through `matches-visible`.

  Deliberately **not** context-scoped and not belief-filtered, because the callers are
  `vaelii.impl.special`'s exception re-check triggers, and a trigger must be
  conservative in the direction the answer is: a declaration this edge cannot see
  still qualifies a rule in some context that can, and a missed trigger leaves a
  conclusion blocked (or unblocked) on evidence that has since moved.  Over-queueing
  costs a level-6 query at the next settle; under-queueing is a wrong belief.

  Costs one set-cardinality read per functor on a KB that declares none, which is
  nearly all of them, and the callers are additionally gated on some rule carrying an
  `exceptWhen` at all — so the record fetches here are paid only by a KB using both
  features."
  [kb]
  (let [recs (:records kb) idx (:index kb)]
    (into #{}
          (comp (filter #(pos? (reads/stored-count-with-functor idx %)))
                (mapcat #(reads/as-stored-with-functor idx %))
                (keep #(p/get-sentex recs %))
                (keep (fn [sxr]
                        (let [[_ pred _ rel] (:sentence sxr)]
                          (when (and (symbol? pred) (symbol? rel)) [pred rel])))))
          (keys declarations))))

;; ---- the reach of one argument ------------------------------------------

(defn- fact-reach
  "Reflexive-transitive reach of `x` over a declared-transitive `rel`, read from the
  believed facts.  The virtual relations never come here — their closures are the
  engine's own, which is the whole reason they are `virtual-relations`."
  [kb rel inverse? x context]
  (let [step (fn [n]
               (into #{} (keep #(get (second %) '?rv))
                     (res/matches-visible
                      kb (if inverse? (list rel '?rv n) (list rel n '?rv)) context)))]
    (loop [seen #{x}, frontier [x]]
      (if-let [n (peek frontier)]
        (let [fresh (remove seen (step n))]
          (recur (into seen fresh) (into (pop frontier) fresh)))
        seen))))

(defn witness-terms
  "The terms a claim's argument may be **stated of** for it to reach `x` at this
  position: `{w : (rel x w)}` for `transitiveInArg`, `{w : (rel w x)}` for the inverse
  form.  Reflexive, so `x` itself is always among them and a directly-stated claim is
  found by the same walk as an inherited one.

  One declaration's reach.  Callers want a *position's*, which is the union over the
  declarations made at it — `reach`.

  The `genl` walk is **scoped to `context`**, exactly as `fact-reach` is: a claim
  travels along the edges the asking context can see and no others, or a context
  would inherit `(largerThan dog cat)` down to a subtype some invisible theory
  declared.  `genlCx` stays global — the context closure is (docs/taxonomy.md,
  the stated exception), and a preservation along it is a claim about the topology,
  which is universal.

  Memoized on `[rel inverse? x context]` for the life of one question.  The virtual
  relations read a cached closure and would survive without it; a **fact-relation** is
  the one that must not be re-walked, since each walk costs a `matches-visible` per
  node and `undercut?` asks for the same term's reach once per pair of claims."
  [kb {:keys [rel inverse?]} x context]
  (memoized [:reach rel inverse? x context]
            (fn []
              (let [tx (reasoning/taxonomy kb)]
                (case rel
                  genl        (if inverse? (tax/specs tx x context) (tax/genls tx x context))
                  genlCx (if inverse? (tax/context-down tx x) (tax/context-up tx x)) ; global on purpose
                  (fact-reach kb rel inverse? x context))))))

(defn- reach
  "The terms one argument may be stated of, over **every** declaration at its
  position: a union, because each independently licenses the claim.  A position
  preserved along both `genl` and a declared-transitive `partOf` reaches what either
  reaches, and `below?` compares along the same union."
  [kb poss x context]
  (if (= 1 (count poss))
    (witness-terms kb (first poss) x context)   ; the common case: no set to rebuild
    (into #{} (mapcat #(witness-terms kb % x context)) poss)))

;; ---- the claims bearing on a goal ---------------------------------------

(defn- by-position
  "The declarations grouped by the argument position they preserve, dropping any
  position the goal does not have — a declaration naming argument 3 of a binary
  predicate is ill-advised but stored, and reading past the tuple's end is not the
  way to report it."
  [positions arity]
  (into {} (filter (fn [[n _]] (<= n arity))) (group-by :n positions)))

(defn- slots
  "What a claim's argument may be, per argument position of the goal: `{:reach terms}`
  at a preserved position, `{:pinned term}` where the goal's own argument stands.

  The **product** of the reaches is the set of tuples a claim could be stated at, and
  it is what the two retrieval paths below are two ways of intersecting with what is
  actually stored."
  [kb positions args context]
  (let [by-n (by-position positions (count args))]
    (mapv (fn [i]
            (if-let [poss (by-n (inc i))]
              {:reach (reach kb poss (nth args i) context)}
              {:pinned (nth args i)}))
          (range (count args)))))

(defn- product-tuples
  "Every argument tuple a claim could be stated at — the product of the reaches,
  pinned elsewhere."
  [slots]
  (reduce (fn [tuples s]
            (let [terms (or (:reach s) #{(:pinned s)})]
              (for [t tuples, w terms] (conj t w))))
          [[]]
          slots))

(def ^:private product-ceiling
  "Past this the product's size stops being counted and is simply *large*.  The number
  is only ever compared against a stored extent, and no extent reaches it."
  1e12)

(defn- product-size
  "How many tuples the product holds — the count the extent is weighed against."
  ^double [slots]
  (reduce (fn [^double n s]
            (if (>= n product-ceiling)
              n
              (* n (double (if-let [r (:reach s)] (count r) 1)))))
          1.0 slots))

(defn- extent-size
  "How many stored sentexes one open probe would walk: the predicate's functor root,
  narrowed by whichever pinned argument position is most selective.

  Read through `order`, because that is where the pinned term will actually **sit** in
  the probe.  The converse an asymmetric predicate is denied by swaps the tuple
  indices, so a term pinned at tuple index 0 is looked up at sentence position 2 — and
  counting it at position 1 estimates a probe nobody is about to make.  For the
  forward order the two coincide, which is why this reads the same as counting by
  tuple index everywhere else.

  Both roots span either polarity, so this covers the negated probe as well as the
  positive one.  It is an under-count where a **sub-predicate** contributes through
  the genl fan — which makes it a cost estimate rather than a count, and the direction
  is the safe one: an under-count only ever prefers the path whose cost is linear in
  what was written."
  ^double [kb pred slots order]
  (let [idx (:index kb)]
    (double
     (reduce (fn [n j]
               (let [s (nth slots (nth order j))]
                 (if-some [t (:pinned s)] (min n (reads/stored-count-with-arg idx (inc j) t)) n)))
             (reads/stored-count-with-functor idx pred)
             (range (count order))))))

;; ---- the two ways to find them ------------------------------------------
;; A claim bearing on the goal is a stored sentence whose argument tuple lies in the
;; product.  There are two ways to intersect a product with a store, and which is
;; cheaper is a property of the KB rather than of the feature: **enumerate the
;; product** and probe each tuple (cost: the product), or **read the extent** of the
;; predicate with a variable at every preserved position and keep the tuples that land
;; in the product (cost: what was written about that predicate).  Both go through
;; `matches-visible`, so subsumption, the symmetric mirror, context visibility and
;; belief are the same set either way — the choice is retrieval, never semantics.

(defn- probe-var [j] (symbol (str "?w" j)))

(defn- probe-sentence
  "The sentence to look up.  `order` maps each argument position of the *sentence* to
  the tuple index it fills: the identity for a claim read forwards, `[1 0]` for the
  converse an asymmetric predicate is denied by.  `terms` supplies a term for a tuple
  index, or nil to leave a variable there."
  [pred slots order terms]
  (cons pred (map-indexed (fn [j ti]
                            (let [s (nth slots ti)]
                              (if (:reach s) (or (terms ti) (probe-var j)) (:pinned s))))
                          order)))

(defn- in-product?
  "Is `tuple` one of the tuples a claim bearing on the goal could be stated at?  Asked
  of every position, pinned ones included: the symmetric mirror can hand back a match
  whose arguments sit in the other order, and a pinned position is only pinned in the
  pattern."
  [slots tuple]
  (and (= (count tuple) (count slots))
       (every? (fn [i]
                 (let [s (nth slots i) t (nth tuple i)]
                   (if-let [r (:reach s)] (contains? r t) (= t (:pinned s)))))
               (range (count slots)))))

(defn- bound-tuple
  "The tuple a match is a statement about, read back through `order` — the bindings at
  the preserved positions, the goal's own terms at the pinned ones.  nil when a
  preserved position came back unbound, which no match of this pattern can do."
  [bindings slots order]
  (reduce (fn [t j]
            (let [ti (nth order j) s (nth slots ti)]
              (if (:reach s)
                (if-some [v (get bindings (probe-var j))] (assoc t ti v) (reduced nil))
                (assoc t ti (:pinned s)))))
          (vec (repeat (count slots) nil))
          (range (count order))))

(defn- believed-matches
  "`[tuple handle sentex]` for every believed sentex matching `sentence` that states
  something about a tuple in the product.  `known` is the tuple when the caller
  already has it — a ground probe binds nothing to read one back from."
  [kb sentence slots order context known]
  (for [[h b] (res/matches-visible kb sentence context)
        :let  [tuple (or known (bound-tuple b slots order))]
        :when (and tuple (in-product? slots tuple))
        :let  [sxr (p/get-sentex (:records kb) h)]
        :when (and sxr (jtms/in? (reasoning/tms kb) h))]
    [tuple h sxr]))

(def ^:dynamic *retrieval*
  "Which of the two paths finds the claims: `:auto` weighs the extent against the
  product per goal, `:extent` and `:product` force one.  The forcing values exist so a
  test can hold the two against each other on the same KB — they answer the identical
  claim set by construction (both filter `matches-visible` by the same
  `in-product?`), and `inherit_oracle_test` is the claim that they do."
  :auto)

(defn- found-claims
  "Every believed statement bearing on the goal at `order` and `negated?`, by whichever
  of the two retrieval paths is cheaper for this KB."
  [kb pred slots order negated? context]
  (let [wrap (fn [s] (if negated? (list 'not s) s))]
    (if (case *retrieval*
          :extent  true
          :product false
          (<= (extent-size kb pred slots order) (product-size slots)))
      (believed-matches kb (wrap (probe-sentence pred slots order (constantly nil)))
                        slots order context nil)
      (mapcat (fn [tuple]
                (believed-matches kb (wrap (probe-sentence pred slots order tuple))
                                  slots order context tuple))
              (product-tuples slots)))))

(defn- strongest-per-tuple
  "One claim per tuple — the **strongest** believed statement of it, with its
  defeat-class.

  Strongest, and not merely the first found, because one tuple can be stated in
  several visible contexts at different strengths.  `:class` decides both whether a
  claim can be undercut and whether `checks/asymmetry-problem` refuses, so taking the
  first would key an *admission* decision on handle iteration order — and handles are
  allocated in assertion order, which is the one thing belief may never depend on.
  The maximum over the class lattice is a function of the content alone, and the ties
  it leaves are broken on the context **name**, then the sentence's printed form, for
  the same reason: one tuple can carry two sentences in one context at one class (the
  matcher is type-aware, so a goal fans over sub-predicates), and a tie left to the
  retrieval order would survive differently under the retrieval sweeps."
  [kb polarity found]
  (->> found
       (map (fn [[tuple h sxr]]
              {:polarity polarity :handle h :sentence (:sentence sxr)
               :context (:context sxr) :tuple tuple
               :class (or (jtms/defeat-class (reasoning/tms kb) h) :default)}))
       (group-by :tuple)
       (map (fn [[_ cs]]
              ;; the strongest claim on a tuple: key built once per claim (min in one
              ;; pass), not per comparison of a full sort thrown away but for its first.
              ;; The sentence prints through `nm/print-key`, since `cs` is a bucket of a
              ;; `res/matches-visible` answer *set* and the winner's `:class` is what
              ;; `verdict` and `checks/asymmetry-problem` read — an ambient
              ;; `*print-length*` collapsing the key would decide an admission on the
              ;; order the retrieval happened to answer in
              (nm/min-by-content-key (juxt #(- (st/rank-of (:class %)))
                                           #(nm/name-key (:context %))
                                           #(nm/print-key (:sentence %)))
                                     compare
                                     cs)))))

(defn claims
  "Every believed claim bearing on the ground goal `(P a1 … an)`, each tagged with the
  argument tuple it is stated at and whether it argues `:for` or `:against`.

  Against comes from two places: an explicit `(not (P …))` at a tuple in range, and —
  when `P` is declared `asymmetric` — the converse `(P … y … x …)`, since a relation
  that cannot hold both ways is denied by its own mirror.  The converse is only read
  for a **binary** goal, which is the only arity for which `asymmetric` means
  anything.

  **Every probe is made, and one tuple can yield several claims.**  A tuple where both
  `P` and `(not P)` are believed is a contradiction the KB already reports through
  `(contradictions kb)`; taking whichever probe answered first would have this read it
  as a clean `:for` and hand `verdict` a decision that the engine, looking at the same
  two sentexes, refuses to make.  Collecting both sends it to `verdict` as the
  `:ambiguous` it is.  The price is two probes per tuple rather than short-circuiting on
  the positive (three for an asymmetric predicate) — the two `:against` sources are
  kept separately rather than folded, since they can be believed at different
  strengths and `undercut?` reads that per claim.

  The converse probe is skipped at a **self tuple** `[a a]`, where it would read the
  very sentex the positive probe just read and file it as opposition.  That is one
  fact disputing itself, not two claims disagreeing, and it is the one shape where
  collecting both polarities would manufacture the dilemma rather than report it.
  (`(P a a)` under an `asymmetric P` *is* wrong — asymmetry implies irreflexivity —
  but it is wrong in a way `contradictions` does not report either, so answering
  `:ambiguous` here would be this function inventing a verdict on its own.)"
  [kb goal context]
  (with-memo
    (let [pred  (nm/functor goal)
          args  (vec (nm/args goal))
          poss  (positions kb pred context)
          asym? (tax/has-prop? (reasoning/taxonomy kb) :asymmetric pred context)
          ;; With no preserved position the product is the goal's own arguments alone,
          ;; so this still answers "what is believed about exactly this tuple" — which
          ;; is what the asymmetry check needs of a predicate that inherits nothing.
          sl    (slots kb poss args context)
          fwd   (vec (range (count args)))
          probe (fn [order negated? polarity]
                  (strongest-per-tuple
                   kb polarity (found-claims kb pred sl order negated? context)))]
      ;; realized here, inside the memo (`with-memo`): the probes read the store and
      ;; `strongest-per-tuple` groups lazily, so a seq handed back unrealized does all
      ;; of that with the memo gone
      (vec
       (concat
        (probe fwd false :for)
        (probe fwd true  :against)
        ;; The converse is read with the tuple indices swapped, so a stored `(P x y)`
        ;; is filed against the tuple `[y x]` it denies.
        (when (and asym? (= 2 (count args)))
          (remove #(= (first (:tuple %)) (second (:tuple %)))
                  (probe [1 0] false :against))))))))

;; ---- specificity ---------------------------------------------------------

(defn- below?
  "Is tuple `t1` at or below `t2` — for every preserved position, is `t2`'s term one
  of the terms `t1`'s can be stated of?  The order is read off the same relations the
  inheritance travels, never off a score."
  [kb positions t1 t2 context]
  (every? (fn [[n poss]]
            (contains? (reach kb poss (nth t1 (dec n)) context) (nth t2 (dec n))))
          (by-position positions (count t1))))

(defn- undercut?
  "Is `c` displaced by a strictly more specific claim?  Only a `:default` claim can
  be: a `:monotonic` one is known-true, so a contrary specific claim is a
  contradiction to report rather than a refinement to defer to."
  [kb positions c others context]
  (and (= :default (:class c))
       (boolean (some (fn [o] (and (not= (:tuple o) (:tuple c))
                                   (below? kb positions (:tuple o) (:tuple c) context)))
                      others))))

(defn surviving
  "The believed claims bearing on `goal` that a strictly more specific one has not
  displaced, each carrying its `:polarity` and `:class`.  The raw material both
  consumers read: the prover turns it into a verdict, and `checks/asymmetry-problem`
  asks the narrower question of whether any survivor is **known-true**."
  [kb goal context]
  (with-memo
    (let [poss (positions kb (nm/functor goal) context)
          cs   (claims kb goal context)]
      ;; realized inside the memo, and this is the layer where it matters most:
      ;; `undercut?` compares every claim against every other and each comparison walks
      ;; a `reach` per preserved position, so a seq escaping the binding pays that
      ;; product uncached.  Both callers outside this namespace drain it
      ;; (`checks/asymmetry-problems`, `provers`), so nothing is realized that a lazy
      ;; answer would have skipped.
      (into [] (remove #(undercut? kb poss % cs context)) cs))))

(defn verdict
  "What the preserved claims say about the ground goal:

    `:for`       — some claim reaches it and nothing surviving disagrees
    `:against`   — the surviving claims deny it
    `:ambiguous` — surviving claims disagree at incomparable specificity, which is a
                   dilemma and is deliberately not decided here
    `nil`        — nothing bears on it, or the predicate declares no preserved position

  Claims displaced by a strictly more specific one drop out first; that is where a
  general default yields to a specific statement without either being defeated."
  [kb goal context]
  ;; Gated on a declared position: without one there is no inheritance to perform, and
  ;; answering from the goal's own tuple would just be `FactProver` wearing a hat.
  (with-memo
    (when (seq (positions kb (nm/functor goal) context))
      (let [polarity (into #{} (map :polarity) (surviving kb goal context))]
        (cond
          (= polarity #{:for})     :for
          (= polarity #{:against}) :against
          (seq polarity)           :ambiguous)))))

(defn ground-goal?
  "A closed positive literal this can speak about.

  A negated goal is left alone: `(not (P a b))` asks whether the claim is *refuted*,
  and an inheritance that only ever licenses claims has nothing to say about that —
  `:against` here means \"not licensed\", the open-world reading, not \"licensed to be
  false\"."
  [goal]
  (and (sequential? goal) (seq goal)
       (symbol? (nm/functor goal))
       (not= 'not (nm/functor goal))
       (seq (nm/args goal))
       (every? sx/ground-term? (nm/args goal))))

;; ---- what an inherited claim rests on ------------------------------------
;;
;; An inherited claim is not stored, so it has no handle for a justification to name.
;; What it does have is the sentexes it was **read from**: the claim actually stated,
;; the declaration licensing the move, and the relation edges the reach travelled —
;; every one of them an ordinary sentex with a handle and a context.  Naming them is
;; what gives an inherited antecedent the contract a matched one has: retraction
;; reaches whatever was concluded from it, `why` explains it, and placement can see
;; where its reasons live.  `docs/inherit.md` and `docs/qcn.md` (the same shape, for a
;; relation a constraint network entails).
;;
;; It is *a* witness rather than every witness, the simplification the qualitative
;; support makes for the same reason: a claim reachable two ways carries one
;; justification, and the second route is re-derived after a retraction rather than
;; recorded in advance.

(defn- one-supporter
  "One handle for a believed `sentence` visible from `context`, chosen on the
  supporting sentex's **context name and printed sentence** — never on its handle,
  which is allocated in assertion order.  Which supporter a firing names decides
  where its conclusion can be placed, so picking the first the index yielded would
  make placement depend on the order the KB was built in.  The sentence is the
  second key because the matches are a fan, not one sentence: a sub-predicate's
  sentex answers a query on its `genl`, so two matches can share a context while
  spelling different claims."
  [kb sentence context]
  (->> (res/matches-visible kb sentence context)
       (keep (fn [[h _]]
               (when-let [sxr (p/get-sentex (:records kb) h)]
                 (when (jtms/in? (reasoning/tms kb) h)
                   [[(str (:context sxr))
                     (binding [*print-length* nil *print-level* nil]
                       (pr-str (:sentence sxr)))]
                    h]))))
       (sort-by first)
       first
       second))

(defn- licensed-terms
  "The terms a claim stated at `w` reaches at this position — `witness-terms` read the
  other way round, which is the same walk with the declaration's direction flipped.
  `witness-terms` asks what a *goal* may be stated of; the forward join asks what a
  *claim* licenses, and `(rel a w)` is one relation read from either end."
  [kb {:keys [rel inverse?]} w context]
  (witness-terms kb {:rel rel :inverse? (not inverse?)} w context))

(defn- fact-path
  "The handles of the stored facts along one path from `a` to `w` over the
  declared-transitive `rel`, or nil when `context` sees none; empty when `a` is `w`.

  What `taxonomy/reach-support` is for the two virtual relations, over the very
  adjacency `fact-reach` walks — so a path is found for exactly the pairs the reach
  answers and the two cannot disagree about what a context reaches.  Breadth-first, so
  the witness is a shortest path; neighbours are expanded in term order and a tie
  between two facts stating one step is broken on the **context name and then on what
  the fact says**, so the witness is a function of the content rather than of the order
  the facts arrived in.  The sentence is in the key because the matcher is type-aware
  and a goal fans over sub-predicates: two believed sentexes routinely state one step
  from one context, and the handle chosen here becomes an antecedent of the recorded
  justification — the same completeness `one-supporter` keys on just above."
  [kb rel inverse? a w context]
  (if (= a w)
    []
    (let [step (fn [n]
                 (->> (res/matches-visible
                       kb (if inverse? (list rel '?rv n) (list rel n '?rv)) context)
                      (keep (fn [[h b]]
                              (let [v (get b '?rv)]
                                (when (and v (not= v n))
                                  (when-let [sxr (p/get-sentex (:records kb) h)]
                                    [v h (str (:context sxr))
                                     (nm/print-key (:sentence sxr))])))))
                      (nm/sort-by-content-key
                       (juxt #(nm/print-key (nth % 0)) #(nth % 2) #(nth % 3)) compare)
                      (partition-by first)
                      (map first)))]
      (loop [q (conj clojure.lang.PersistentQueue/EMPTY a), parent {a nil}]
        (when-let [n (peek q)]
          (if (= n w)
            (loop [x n, acc []]
              (if (= x a)
                acc
                (let [[p h] (get parent x)] (recur p (conj acc h)))))
            (let [fresh (remove #(contains? parent (first %)) (step n))]
              (recur (into (pop q) (map first) fresh)
                     (reduce (fn [m [v h]] (assoc m v [n h])) parent fresh)))))))))

(defn- move-support
  "The handles licensing the step from the claim's term `w` to the goal's `a` at one
  preserved position: the declaration that permits the move, the relation edges the
  reach travelled, and — for a fact-relation — the `(transitive R)` the reach is
  closed under, which `usable-relation?` reads at *use* and so may be withdrawn with
  nothing else moving.  nil when no declaration at this position reaches from one to
  the other through edges `context` can see.

  **Empty when the position did not move**, and that is the whole of the reflexive
  case: a claim stated at the goal's own term rests on no edge and needs no licence, so
  it contributes nothing and the justification stays the one the ordinary matcher
  already records.

  One declaration is named, not all of them — the union of their reaches is what
  licenses the claim, and any member of it that reaches is a complete reason.  **Which
  one is a content choice**: `poss` is materialized from a `res/matches-visible` answer
  set, and `[rel, inverse?]` alone fixes the declaration's sentence — the position is
  constant across `poss`, which arrives already grouped by it — so the asserting context
  is what separates two visible statements of one declaration.  The chosen handle is
  prepended to the support list and lands in a justification, so retracting one of two
  equivalent declarations must not withdraw a conclusion by coin-toss."
  [kb poss a w context]
  (if (= a w)
    []
    (first
     (keep (fn [{:keys [rel inverse? handle]}]
             (let [[sub super] (if inverse? [w a] [a w])]
               (when-let [es (if (contains? virtual-relations rel)
                               (some->> (tax/reach-support (reasoning/taxonomy kb) (keyword rel) sub super
                                                           (when (= 'genl rel) context))
                                        (mapv first))
                               (when-let [p (fact-path kb rel inverse? a w context)]
                                 (if-let [t (one-supporter kb (list 'transitive rel) context)]
                                   (conj (vec p) t)
                                   (vec p))))]
                 (into [handle] es))))
           (nm/sort-by-content-key
            (juxt #(str (:rel %)) #(str (:inverse? %)) #(str (:in %))) compare poss)))))

(defn- claim-support
  "What the reading of claim `c` at the goal's arguments `args` rests on, beyond the
  claim itself: the declaration permitting each move, the relation edges the reach
  travelled, and — for a mirrored reading — the `(symmetric …)` that licensed the
  mirror.  nil when no declaration reaches from the claim's tuple to `args` through
  edges `context` can see; empty when the claim is stated at the goal's own tuple and
  nothing had to move.

  The claim's **own** handle is deliberately absent: one caller names it separately
  (`support-for`'s `:claim`) and the other makes it a member of a nogood in its own
  right (`clashing-claim`), and folding it in here would have each of them strip it
  back out.

  `by-n` is `by-position`'s grouping of the declared positions, hoisted by the caller
  because both of them already hold it."
  [kb by-n args c context]
  (when-let [hs (reduce (fn [acc i]
                          (if-let [ps (by-n (inc i))]
                            (if-let [s (move-support kb ps (nth args i)
                                                     (nth (:tuple c) i) context)]
                              (into acc s)
                              (reduced nil))
                            acc))
                        []
                        (range (count args)))]
    ;; A claim whose stored orientation is not the tuple it was read at came through the
    ;; symmetric mirror, and that reading rests on a `(symmetric …)` declaration exactly
    ;; as a fact-relation reach rests on `(transitive R)`: name it, so retracting the
    ;; symmetry withdraws what only the mirror licensed.  The matcher mirrors each fanned
    ;; literal on *its own* declaration, so the one named is the stored sentence's
    ;; functor's — the goal predicate's only when they coincide.
    (let [hs (if (and (= 2 (count args))
                      (not= (vec (nm/args (:sentence c))) (:tuple c)))
               (if-let [sh (one-supporter
                            kb (list 'symmetric (nm/functor (:sentence c))) context)]
                 (conj hs sh)
                 hs)
               hs)]
      (into [] (distinct) hs))))

(defn support-for
  "What licenses the ground goal `(P a1 … an)` by preservation — `{:claim handle
  :handles [handle …]}`, the claim it was read off and every sentex the reading rests
  on — or nil.

  `verdict` answers *whether*; this answers *from what*, which is what a justification
  needs.  The semantics are `verdict`'s exactly: the surviving claims must agree, so a
  goal the KB also denies, or one two claims disagree about at incomparable
  specificity, licenses nothing here either.

  **A goal the KB states directly licenses nothing**, and that is deliberate.
  `witness-terms` is reflexive, so a stored `(P a b)` is among the claims bearing on
  `(P a b)` — it is the diagonal, it rests on no edge, and the ordinary matcher already
  finds it with a justification of its own.  Answering it here too would hand the same
  conclusion a second justification resting on nothing the first did not already name.

  One claim is named where several survive, chosen on defeat class first and then on
  content — the tuple, the context and the sentence, all spellings rather than
  handles (one tuple can carry two sentences at one class and context, the matcher
  being type-aware, and the chosen handle lands in a recorded justification)."
  [kb goal context]
  (with-memo
    (let [pred (nm/functor goal)
          args (vec (nm/args goal))
          poss (positions kb pred context)]
      (when (seq poss)
        (let [sv (surviving kb goal context)]
          (when (and (seq sv)
                     (= #{:for} (into #{} (map :polarity) sv))
                     (not-any? #(= (:tuple %) args) sv))
            (let [by-n (by-position poss (count args))]
              (first
               (keep (fn [c]
                       (when-let [hs (claim-support kb by-n args c context)]
                         {:claim (:handle c)
                          :handles (into [] (distinct) (cons (:handle c) hs))}))
                     ;; the key mixes a `str` tuple and a printed sentence — built once
                     ;; per survivor now, not per comparison; the `[rank …]` tuple orders
                     ;; under `compare`.  Through `nm/print-key`, because the survivor
                     ;; chosen here has its `:handle` written into a recorded
                     ;; justification and `sv` is drawn from a `res/matches-visible`
                     ;; answer *set*
                     (nm/sort-by-content-key (juxt #(- (st/rank-of (:class %)))
                                                   #(nm/print-key (:tuple %))
                                                   #(nm/name-key (:context %))
                                                   #(nm/print-key (:sentence %)))
                                             compare
                                             sv))))))))))

(defn clashing-claim
  "The **known-true** claim that reaches `sentence`'s own tuple by preservation and
  denies it — `{:sentence :context :claim handle :handles [handle …] :class}` — or nil.

  `sentence` is a stored fact of a preserved predicate, in either polarity; the claim
  looked for is the opposite one.  A stored `(not (P a b))` is denied by a `(P w b)`
  above it, and a stored `(P a b)` by a `(not (P w b))` above it, since `claims` reads
  both polarities out of the reach.

  **Known-true, because that is the whole of what `undercut?` leaves standing.**  A
  `:default` general claim yields to a nearer contrary one: it is undercut, never fires
  for that tuple, and there is nothing for anybody to report (docs/inherit.md).  A
  `:monotonic` one is not undercut — its docstring calls a contrary specific claim \"a
  contradiction to report rather than a refinement to defer to\" — so it survives beside
  the stored claim, `verdict` answers `:ambiguous`, and the pair is exactly what has no
  handle to be reported by.  This is what gives it one.

  **The claim's own tuple is excluded**, and that is what keeps this to the inherited
  case: a claim stated at the very tuple `sentence` is about is an ordinary `P` beside
  an ordinary `(not P)`, both stored, which `settle/negation-nogoods` already pairs off
  the `:opposed` set.  Reporting it here as well would report one pair twice.

  `:handles` is the reading's support and not the claim — the declaration that permits
  each move, the relation edges the reach travelled, the `(transitive R)` a fact-relation
  reach is closed under, and the `(symmetric …)` behind a mirrored reading.  Every one of
  them is a sentex that has to hold for the inherited claim to be read at all, which is
  what lets a caller pair `sentence` with the whole reading rather than with a claim
  whose relevance rests on sentexes nobody named.

  One claim is named where several reach, chosen on content — the tuple, then the
  asserting context, then what the claim says, all spellings rather than handles, since
  the chosen handle lands in a reported nogood.  Asked from the vantage of `context`,
  which callers pass as the stored sentence's own: a claim in a context that cannot see
  the general one is not denied by it."
  [kb sentence context]
  (with-memo
    (let [neg? (and (sequential? sentence) (= 'not (nm/functor sentence))
                    (= 2 (count sentence)))
          body (if neg? (second sentence) sentence)]
      (when (ground-goal? body)
        (let [pred (nm/functor body)
              args (vec (nm/args body))
              poss (positions kb pred context)]
          (when (seq poss)
            (let [want (if neg? :for :against)
                  by-n (by-position poss (count args))
                  sv   (->> (surviving kb body context)
                            (filter #(and (= want (:polarity %))
                                          (st/known-true? (:class %))
                                          (not= (:tuple %) args))))]
              (first
               (keep (fn [c]
                       (when-let [hs (claim-support kb by-n args c context)]
                         {:sentence (if neg? body (list 'not body))
                          :context  context
                          :claim    (:handle c)
                          :handles  hs
                          :class    (:class c)}))
                     (nm/sort-by-content-key (juxt #(nm/print-key (:tuple %))
                                                   #(nm/name-key (:context %))
                                                   #(nm/print-key (:sentence %)))
                                             compare
                                             sv))))))))))

;; ---- enumerating what a claim licenses -----------------------------------
;; A backward goal is closed and asks one question.  A **forward** antecedent is a
;; pattern, so the question runs the other way: which tuples does a stored claim
;; license, and which of them does this literal admit?  That is the walk `docs/inherit.md`
;; declines to make for an open *goal* — it is the larger question — and the forward
;; join is exactly the caller for whom it is the right one, because a conclusion has to
;; be drawn per tuple whether or not anybody asked.

(defn- goal-bindings
  "The bindings making the literal's argument list `args` the tuple `t`, or nil where
  they cannot: a ground argument must be the tuple's term, and a variable written twice
  must take one value."
  [args t]
  (reduce (fn [b i]
            (let [a (nth args i) v (nth t i)]
              (if (and (symbol? a) (sx/variable? a))
                (if-let [prev (get b a)]
                  (if (= prev v) b (reduced nil))
                  (assoc b a v))
                (if (= a v) b (reduced nil)))))
          {}
          (range (count args))))

(defn- stated-claims
  "`[tuple handle]` for every believed claim of `pred` this literal could inherit from
  — the predicate's extent, with the literal's own ground arguments pinned at the
  positions that preserve nothing, since there the claim's term *is* the conclusion's.

  A preserved position is left open even where the literal pins it: the claim licensing
  that term is stated *above* it, and narrowing to the term itself would find only the
  diagonal.

  A **symmetric** predicate's claim is a statement of both orientations, and an open
  probe surfaces only the stored one — the mirror shares its handle, so the matcher's
  mirrored probe of an open pattern adds no second row.  Ground probes bake the
  orientation into the pattern (which is how the backward entry point reads the mirror), so
  the swap has to happen here: a tuple whose stored sentence's own functor is declared
  symmetric — the fan surfaces sub-predicates, and the matcher mirrors each fanned
  literal on *its* declaration — is also read backwards, kept where the pattern's
  pinned positions still agree."
  [kb pred args poss context]
  (let [by-n (by-position poss (count args))
        pat  (mapv (fn [i]
                     (let [a (nth args i)]
                       (if (or (by-n (inc i)) (and (symbol? a) (sx/variable? a)))
                         (probe-var i)
                         a)))
                   (range (count args)))
        base (for [[h b] (res/matches-visible kb (cons pred pat) context)
                   :when (jtms/in? (reasoning/tms kb) h)
                   :let  [t (mapv (fn [i]
                                    (let [p (nth pat i)]
                                      (if (= p (probe-var i)) (get b p) p)))
                                  (range (count args)))]
                   :when (every? some? t)]
               [t h])]
    (if-not (= 2 (count args))
      base
      (let [tx   (reasoning/taxonomy kb)
            syms (into #{} (filter #(tax/has-prop? tx :symmetric %))
                       (res/sub-predicates kb pred nil))]
        (if (empty? syms)
          base
          (concat base
                  (for [[t h] base
                        :let  [sxr (p/get-sentex (:records kb) h)
                               f   (some-> sxr :sentence nm/functor)]
                        :when (and f (contains? syms f))
                        :let  [rt [(nth t 1) (nth t 0)]]
                        :when (and (not= rt t)
                                   (every? #(let [pp (nth pat %)]
                                              (or (= pp (probe-var %)) (= pp (nth rt %))))
                                           (range 2)))]
                    [rt h])))))))

(defn- licensed-product
  "Every tuple a claim stated at `w` licenses that the literal's arguments admit — the
  product of the licensed terms at the preserved positions, the claim's own term
  elsewhere, and a ground argument of the literal pinned wherever it has one."
  [kb by-n args w context]
  (reduce (fn [tuples i]
            (let [terms (if-let [ps (by-n (inc i))]
                          (let [r (if (= 1 (count ps))
                                    (licensed-terms kb (first ps) (nth w i) context)
                                    (into #{} (mapcat #(licensed-terms kb % (nth w i) context)) ps))
                                a (nth args i)]
                            (if (and (symbol? a) (sx/variable? a))
                              r
                              (when (contains? r a) #{a})))
                          #{(nth w i)})]
              (for [tp tuples, x terms] (conj tp x))))
          [[]]
          (range (count args))))

(defn solve-with-support
  "Solve the antecedent literal `literal` by **preservation**: a seq of `{:bindings
  :claim :handles}`, one per inherited claim it matches, each carrying the claim it was
  read off and the handles the reading rests on.

  A closed literal asks `support-for` once.  An open one enumerates: every believed
  claim of the predicate, the tuples it licenses, and then the same `support-for` per
  tuple — so the tuples are *found* by the reach and *admitted* by the full semantics,
  and an antecedent can no more join on an undercut or disputed claim than `ask` can
  answer one.

  The diagonal is dropped (`support-for`), so a claim stated at the tuple it is asked
  about stays the ordinary matcher's to find.  Nothing here replaces that matcher; the
  caller unions the two."
  [kb literal context]
  (with-memo
    (when (and (sequential? literal) (seq literal) (symbol? (nm/functor literal))
               (not= 'not (nm/functor literal)) (seq (nm/args literal)))
      (let [pred (nm/functor literal)
            args (vec (nm/args literal))
            poss (positions kb pred context)]
        (when (seq poss)
          (if (every? sx/ground-term? args)
            (when-let [s (support-for kb literal context)]
              [(assoc s :bindings {})])
            (let [by-n (by-position poss (count args))]
              ;; realized inside the memo: `licensed-product` walks a `reach` per
              ;; preserved position per claim and `support-for` opens a memo of its own
              ;; per tuple, so an escaping seq shares nothing between the tuples of one
              ;; literal.  The join drains this per state (`chain/solve-preserving`),
              ;; so the whole product is what it consumes either way.
              (into [] (distinct)
                    (for [[w _] (stated-claims kb pred args poss context)
                          t     (licensed-product kb by-n args w context)
                          :when (not= t w)
                          :let  [b (goal-bindings args t)]
                          :when b
                          :let  [s (support-for kb (cons pred t) context)]
                          :when s]
                      (assoc s :bindings b))))))))))

;; ---- which rules an arriving sentence moves ------------------------------

(defn moved-predicates
  "The preserved predicates whose licensed claims `sen` may have moved.

  Four channels, and none of them is the predicate-keyed trigger a forward rule is
  ordinarily fired from:

  * a **claim** on `P` (or on a sub-predicate of it) licenses a tuple nobody stated,
    and undercuts one somebody did;
  * a fact on the **relation** `R` — a `genl` / `genlCx` edge included — moves
    every reach walked along it, with neither of its terms appearing anywhere near `P`;
  * the **declaration** itself, which names `P` at argument 1;
  * `(transitive R)`, the licence `usable-relation?` reads at use, which names no `P`
    at all; `(asymmetric P)`, which is what gives a converse the standing to deny
    an inherited claim; and `(symmetric P)`, which makes the mirror of every stored
    claim a claim — arriving late it licenses tuples nobody re-joined for.

  The reads are **global** and not belief-filtered, exactly as `declared`'s are and for
  the same reason: over-selecting costs a join that derives what is already there,
  under-selecting is a conclusion that depends on when a sentence arrived.  Behind
  `declarations-exist?`, so a KB that declares nothing pays two cardinality reads.

  **The three-argument form takes the `[P R]` pairs**, for a caller holding them already
  and asking this per member of a settle's region: both reads behind the gate — the
  cardinalities and `declared`'s own record fetches — are per call, and a caller that
  knows the KB declares something (`kb`'s `:preserving` roster says so with no index
  read at all) would pay them once per handle for an answer that cannot move inside one
  settle."
  ([kb sen]
   (when (and (sequential? sen) (seq sen) (declarations-exist? kb))
     (moved-predicates kb sen (declared kb))))
  ([kb sen decls]
   (let [body  (or (sx/underlying-body sen) sen)
         f     (nm/functor body)
         arg1  (nth body 1 nil)]
     (when (symbol? f)
       (cond
         (contains? declarations f) (when (symbol? arg1) #{arg1})
         (= 'transitive f)          (into #{} (comp (filter #(= arg1 (second %))) (map first)) decls)
         (= 'asymmetric f)          (when (some #(= arg1 (first %)) decls) #{arg1})
         ;; the mirror is applied per fanned literal on its own declaration, so a
         ;; symmetry on a sub-predicate moves every preserved super it feeds
         (= 'symmetric f)           (when (symbol? arg1)
                                      (let [ups (tax/genls-global (reasoning/taxonomy kb) arg1)]
                                        (into #{} (comp (filter #(ups (first %))) (map first)) decls)))
         :else (let [preds (tax/genls-global (reasoning/taxonomy kb) f)]
                 (into #{}
                       (comp (filter (fn [[p r]] (or (preds p) (preds r)))) (map first))
                       decls)))))))

(defn rejoin-rules
  "The forward rules to re-join in full because `sen` moved what a preserved predicate
  licenses — every rule carrying an antecedent on one — or nil.

  Keyed on the antecedent index rather than on the arriving sentence's predicate,
  because the two are unrelated: `(genl chihuahua dog)` licenses a `largerThan`
  antecedent and no walk from `genl` reaches `largerThan`.  That is the same shape the
  qualitative re-join has, for the same reason, and `special/recheck-preserving-along`
  reads the same declarations to close the exception side of the identical channel."
  [kb sen]
  (when-let [ps (seq (moved-predicates kb sen))]
    (let [idx (:index kb)
          rs  (into #{} (mapcat #(reads/as-stored-rules-by-antecedent idx %)) ps)]
      (when (seq rs) rs))))
