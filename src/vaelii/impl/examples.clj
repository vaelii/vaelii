;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.examples
  "Worked examples of the reasoning the shipped ontology actually does — the data, and
  the one function that runs one.

  **Nothing here is a story about the engine.**  Each example names the sentexes it
  rests on, and those are looked up in the live KB before anything is claimed: an
  example whose `rests-on` sentences are not stored is reported *unavailable* rather
  than answered, so switching to another corpus greys the examples out instead of
  silently showing a verdict computed from vocabulary that is not there.  The verdict
  itself is an ordinary `ask` / `escalate` / `check`, and the proof is `why`.

  Two kinds, and the split is about what the KB ships rather than about presentation:

    **read-only** — no premises.  The shipped schema is types, taxonomy, metadata and
    rules, so everything asked *of kinds* is answerable with no write at all, and the
    page computes it on render.  This is where the taxonomy, `argPreserving`,
    disjointness and the predicate meta-ontology live.

    **sandboxed** — premises naming individuals.  The starter ships no cast (the
    fables and their casts live in the test-world), so an example about defaults,
    joins or refusals has to bring its own, and it writes them into the reader's own
    sandbox context.  Nothing shipped can see in, and the sandbox reset takes the
    whole thing away.

  `:expect` is what the ontology is supposed to answer, and `examples_test` asserts
  every one of them — so the page cannot drift away from the KB it describes."
  (:require [vaelii.impl.access :as v]))

;; ---- the table ----------------------------------------------------------

(def examples
  "Every worked example, in the order the page shows them.  `:rests-on` is
  `[sentence context]` pairs — real stored sentexes, linked on the page and looked up
  to decide availability.  `:premises` are sentences written into the sandbox, types
  first so the `argIsa` checks bind."
  [;; ---- taxonomy: what a closure answers that no sentex says ----------
   {:id "genl-chain" :group "Taxonomy"
    :title "A chain nobody stored"
    :shows "Two stored edges, one question they never state. Transitivity is a cached
            closure rather than a rule, so the answer costs a set lookup and no chaining
            at all — and no (genl penguin animal) sentex is ever materialized."
    :rests-on [['(genl penguin bird) 'CxOrganism]
               ['(genl bird animal) 'CxOrganism]]
    :goal '(genl penguin animal) :context 'CxWell :expect :yes}

   {:id "disjoint-metatype" :group "Taxonomy"
    :title "Ten separations from one declaration"
    :shows "Nobody wrote that a penguin is not a dog. One disjointMetatype separates the
            five vertebrate classes pairwise, and genl carries each separation down to
            every subtype. The pairs are consulted, never stored: retract the metatype
            and all ten go at once."
    :rests-on [['(disjointMetatype vertebrateClass) 'CxOrganism]
               ['(vertebrateClass bird) 'CxOrganism]
               ['(vertebrateClass mammal) 'CxOrganism]]
    :goal '(disjoint penguin dog) :context 'CxWell :expect :yes}

   {:id "arg-preserving" :group "Taxonomy"
    :title "A claim about kinds, reaching kinds it never mentions"
    :shows "(largerThan mammal insect) is a claim about two kinds. Because largerThan is
            declared argPreserving along genl on both positions, it answers about every
            pair of subkinds beneath it — here dogs and ants, about whose sizes the KB
            holds nothing whatever."
    :rests-on [['(largerThan mammal insect) 'CxSize]
               ['(argPreserving largerThan 1 genl) 'CxAbstract]
               ['(argPreserving largerThan 2 genl) 'CxAbstract]]
    :goal '(largerThan dog ant) :context 'CxWell :expect :yes}

   {:id "arg-preserving-stops" :group "Taxonomy"
    :title "…and does not reach the other way"
    :shows "The same declaration, the converse question. Preservation moves an argument
            down the hierarchy; it does not make the relation symmetric, and largerThan
            is declared asymmetric besides. A KB that answered this would be inventing."
    :rests-on [['(largerThan mammal insect) 'CxSize]
               ['(asymmetric largerThan) 'CxAbstract]]
    :goal '(largerThan ant dog) :context 'CxWell :expect :no}

   ;; ---- the vocabulary reasoning about itself -------------------------
   {:id "metadata-to-type" :group "Predicates about predicates"
    :title "Declaring a property concludes a type"
    :shows "(symmetric friendOf) is metadata the engine reads. It is also an ordinary
            antecedent: a CxCore rule concludes the predicate-type membership from
            it, into CxUniverse by an ist consequent. So the type hierarchy over
            predicates is derived, not maintained."
    :rests-on [['(symmetric friendOf) 'CxSociety]
               ['(implies (and (symmetric ?p)) (symmetricPredicate ?p)) 'CxCore]]
    :goal '(symmetricPredicate friendOf) :context 'CxWell :expect :yes}

   {:id "arity-cycle" :group "Predicates about predicates"
    :title "Two rules that derive each other"
    :shows "The arity and the predicate-type membership each conclude the other, so
            asserting either keeps the whole cycle believed. Positive recursion is
            ordinary — it is a cycle through negation that the stratification check
            refuses."
    :rests-on [['(binaryPredicate largerThan) 'CxAbstract]
               ['(implies (and (binaryPredicate ?p)) (arity ?p 2)) 'CxCore]]
    :goal '(arity largerThan 2) :context 'CxWell :expect :yes}

   {:id "type-level" :group "Predicates about predicates"
    :title "A relation between kinds, marked as one"
    :shows "largerThan relates kinds and parentOf relates individuals, and the KB says
            which is which. relationKind is a disjointMetatype over the two, so a
            predicate is at most one of them — asking whether largerThan relates
            individuals is answered no, not merely left unanswered."
    :rests-on [['(typeRelationPredicate largerThan) 'CxAbstract]
               ['(disjointMetatype relationKind) 'CxCore]]
    :goal '(instanceRelationPredicate largerThan) :context 'CxWell :expect :no}

   {:id "part-type" :group "Predicates about predicates"
    :title "Preserved on one position and not the other"
    :shows "Nobody wrote that penguins have wings. partType is declared argPreserving
            along genl on its first position only, and that asymmetry is the claim: a
            kind of bird has whatever parts birds have, while birds having wings says
            nothing about which kinds of wing. Compare largerThan, which is declared on
            both — each position is a separate decision about the relation."
    :rests-on [['(partType bird wing) 'CxAnatomy]
               ['(argPreserving partType 1 genl) 'CxAbstract]
               ['(genl penguin bird) 'CxOrganism]]
    :goal '(partType penguin wing) :context 'CxWell :expect :yes}

   ;; ---- defaults and their exceptions ---------------------------------
   {:id "default-alive" :group "Defaults and exceptions"
    :title "Alive until told otherwise"
    :shows "Nobody said Rex was alive. A default rule concludes it of every living
            thing, and nothing about being a dog mentions living things — the rule's
            antecedent is matched by fanning it out over the subtype closure. The
            conclusion is defeasible, which the next card is about."
    :rests-on [['(exceptWhen (dead ?x)
                             (set/defaultRule (implies (and (living_thing ?x)) (alive ?x))))
                'CxBiology]]
    :premises '[(dog RexEx)]
    :goal '(alive RexEx) :expect :yes}

   {:id "default-dead" :group "Defaults and exceptions"
    :title "…and the death is a claim, not an absence"
    :shows "Assert the death and the alive rule stops firing — its own exceptWhen
            blocks it, so there is no conclusion to defeat and nothing to arbitrate. A
            separate rule concludes the negation, so the KB ends up holding that Max is
            not alive rather than merely failing to conclude that he is. Those are
            different claims, and only the first supports an argument."
    :rests-on [['(implies (and (dead ?x)) (not (alive ?x))) 'CxBiology]]
    ;; a different dog from the card above, deliberately: the reader's sandbox holds
    ;; every example at once, so killing that one would turn the card above into a
    ;; verdict the example above does not expect
    :premises '[(dog MaxEx) (dead MaxEx)]
    :goal '(not (alive MaxEx)) :expect :yes}

   {:id "exception-by-class" :group "Defaults and exceptions"
    :title "An exception that names a whole class"
    :shows "Animals breathe air by default, except fish. The exception names a class
            rather than one awkward species, and matching fans an antecedent out over
            the subtype closure — so it reaches every kind of fish the ontology will
            ever hold, with no upkeep."
    :rests-on [['(exceptWhen (fish ?x)
                             (set/defaultRule (implies (and (animal ?x)) (breathesAir ?x))))
                'CxBiology]]
    :premises '[(fish NemoEx)]
    :goal '(breathesAir NemoEx) :expect :no}

   {:id "cold-blooded" :group "Defaults and exceptions"
    :title "A property read off the class"
    :shows "Nothing is stored about Shelly's blood. Warm-bloodedness follows from the
            vertebrate class, the five classes are pairwise disjoint, so exactly one of
            the five rules fires and the KB cannot hold both halves."
    :rests-on [['(implies (and (reptile ?x)) (not (warmBlooded ?x))) 'CxBiology]]
    :premises '[(tortoise ShellyEx)]
    :goal '(not (warmBlooded ShellyEx)) :expect :yes}

   ;; ---- joins ---------------------------------------------------------
   {:id "grandparent" :group "Rules that join"
    :title "Two facts meeting at a variable"
    :shows "Neither parentOf fact says anything about grandparents. The rule joins them
            on the shared middle variable, and the planner orders the antecedents by
            estimated fan-out before running them."
    :rests-on [['(implies (and (parentOf ?x ?y) (parentOf ?y ?z)) (grandparentOf ?x ?z))
                'CxKinship]]
    :premises '[(human AdaEx) (human BenEx) (human CalEx)
                (parentOf AdaEx BenEx) (parentOf BenEx CalEx)]
    :goal '(grandparentOf AdaEx CalEx) :expect :yes}

   {:id "part-location" :group "Rules that join"
    :title "A part is wherever its whole is"
    :shows "Location was stated of the car and parthood of the wheel; the conclusion is
            about neither on its own. Retract either premise and it goes — the
            justification names both, so the sweep is dependency-directed."
    :rests-on [['(implies (and (partOf ?part ?whole) (locatedIn ?whole ?place))
                          (locatedIn ?part ?place))
                'CxMereology]]
    :premises '[(vehicle CarEx) (artifact WheelEx) (building GarageEx)
                (partOf WheelEx CarEx) (locatedIn CarEx GarageEx)]
    :goal '(locatedIn WheelEx GarageEx) :expect :yes}

   {:id "owns-parts" :group "Rules that join"
    :title "Owning a whole is owning its parts"
    :shows "The same join shape on a social relation rather than a spatial one. One
            rule, and every part of everything anyone owns follows."
    :rests-on [['(implies (and (owns ?p ?whole) (partOf ?part ?whole)) (owns ?p ?part))
                'CxMereology]]
    :premises '[(person AdaEx) (vehicle CarEx) (artifact WheelEx)
                (owns AdaEx CarEx) (partOf WheelEx CarEx)]
    :goal '(owns AdaEx WheelEx) :expect :yes}

   {:id "symmetry-then-rule" :group "Rules that join"
    :title "Both chainers, one rule, one stored fact"
    :shows "The forward pass concluded acquaintance in the direction the friendship was
            canonically stored. This asks the other direction, so no stored sentex
            matches and the backward chainer runs the same rule over the same symmetric
            fact, probing both argument orders. knows is deliberately not symmetric:
            declaring it so would have the KB assert the converse of every acquaintance
            it ever learned."
    :rests-on [['(symmetric friendOf) 'CxSociety]
               ['(implies (and (friendOf ?x ?y)) (knows ?x ?y)) 'CxSocial]]
    :premises '[(person AdaEx) (person BenEx) (friendOf AdaEx BenEx)]
    :goal '(knows BenEx AdaEx) :expect :yes}

   {:id "evaluable-older" :group "Rules that join"
    :title "A rule that computes rather than looks up"
    :shows "olderThan is a backward rule whose third antecedent is evaluable: lessThan
            is computed from ground numbers, never stored and never forward-chained.
            The planner pins it after the two antecedents that bind its arguments."
    :rests-on [['(set/backwardRule
                  (implies (and (birthYearOf ?x ?bx) (birthYearOf ?y ?by) (lessThan ?bx ?by))
                           (olderThan ?x ?y)))
                'CxKinship]]
    :premises '[(human AdaEx) (human BenEx)
                (birthYearOf AdaEx 1970) (birthYearOf BenEx 1980)]
    :goal '(olderThan AdaEx BenEx) :expect :yes}

   ;; ---- what the KB will not accept -----------------------------------
   {:id "disjoint-refusal" :group "What it refuses"
    :title "A membership the taxonomy forbids"
    :shows "Rex is a dog, dog and cat are disjoint, so the KB refuses to be told he is
            also a cat. Not a warning and not a contradiction to arbitrate later —
            check reports it and nothing is stored."
    :rests-on [['(disjoint dog cat) 'CxOrganism]]
    :premises '[(dog RexEx)]
    :kind :refusal
    :refuse '(cat RexEx)}

   {:id "argisa-refusal" :group "What it refuses"
    :title "An argument the predicate's own type constraint forbids"
    :shows "eats wants food in its second position, and a garage is a building. The
            constraint is open-world — an argument whose type is unknown cannot violate
            it — so this is refused for what the KB knows the garage to be, not for
            what it has not been told."
    :rests-on [['(argIsa eats 2 food) 'CxLife]
               ['(genl building artifact) 'CxAbstract]]
    :premises '[(dog RexEx) (building GarageEx)]
    :kind :refusal
    :refuse '(eats RexEx GarageEx)}

   {:id "not-ground-refusal" :group "What it refuses"
    :title "A universal written as a fact"
    :shows "(mortal ?x) looks like a claim that everything is mortal. Stored as a
            premise it would unify with any goal at all — a universal nobody licensed —
            so facts must be ground and universals are written as rules, where
            range-restriction governs the variables."
    :rests-on [['(set/defaultRule (implies (and (living_thing ?x)) (mortal ?x)))
                'CxBiology]]
    :kind :refusal
    :refuse '(mortal ?x)}])

(def groups
  "The example groups, in page order."
  (distinct (map :group examples)))

(defn by-id [id] (first (filter #(= id (:id %)) examples)))

;; ---- running one --------------------------------------------------------

(defn available?
  "Is every sentex this example rests on actually stored?  One `handle-of` per
  dependency — indexed, and find-*without*-create, so asking costs nothing and writes
  nothing.  A KB that does not hold them cannot be asked the example's question."
  [kb {:keys [rests-on]}]
  (every? (fn [[sentence context]] (v/handle-of kb sentence context)) rests-on))

(defn established?
  "Are this example's premises already written into `context`?  One `handle-of` per
  premise, so a page asking of every example pays a handful of indexed lookups and
  writes nothing.  An example with no premises is never established — it needs nothing."
  [kb {:keys [premises]} context]
  (boolean (and context (seq premises)
                (every? #(v/handle-of kb % context) premises))))

(defn dependencies
  "The `[sentence context handle]` triples the example rests on, so a page can link
  each to the record it names and show which are missing."
  [kb {:keys [rests-on]}]
  (for [[sentence context] rests-on]
    [sentence context (v/handle-of kb sentence context)]))

(defn- goal-verdict
  "Ask the goal, and say by what machinery.  `escalate` climbs the lookup-to-query
  stack and stops at the first level that answers, so the level *is* the mechanism:
  level 3 means context inheritance reached it, 5 means a closure, 7 means the rule
  chainers had to run.  A goal nothing answers comes back with a nil level, which is
  the honest report and not an error."
  [kb {:keys [goal expect]} context]
  (let [{:keys [level name results]} (v/escalate kb goal context)
        answered? (some? level)
        ;; the handle off the level that answered, not a fresh `handle-of` in the asking
        ;; context: an answer inherited from a supercontext, or one the closures derived
        ;; and never materialized, has no record *there* — the first carries a handle
        ;; from where it is really stored and the second honestly carries none
        handle    (when answered? (:handle (first results)))]
    {:answered? answered?
     :level level :level-name name
     :handle handle
     :why (when handle (v/why kb handle))
     :as-intended? (= answered? (= :yes expect))}))

(defn- refusal-verdict
  "What `check` says about the sentence this example expects to be refused.  A read —
  it answers what `assert` would do and stores nothing — so the example can show a
  refusal without the KB ever having held the thing refused."
  [kb {:keys [refuse]} context]
  (let [problems (v/check kb refuse context)]
    {:refused? (boolean (seq problems))
     :problems problems
     :as-intended? (boolean (seq problems))}))

(defn run
  "Run one example against `kb` and answer what it did.  `context` is where the
  question is asked: the reader's sandbox for an example with premises, and any context
  seeing the whole ontology for one without.

  Writes nothing.  Establishing an example's premises is `establish!`, which the page
  does on an explicit click — so rendering the gallery is a read however many examples
  it holds."
  [kb {:keys [kind] :as example} context]
  (merge {:id (:id example) :available? (available? kb example)}
         (when (available? kb example)
           (if (= :refusal kind)
             (refusal-verdict kb example context)
             (goal-verdict kb example context)))))

(defn establish!
  "Write an example's premises into `context` — one `edit`, so the whole batch settles
  once.  Idempotent: a premise already stored is found rather than duplicated, so
  re-running an example is not re-asserting it.

  Returns the handles the batch added."
  [kb {:keys [premises]} context]
  (when (seq premises)
    (:added (v/edit! kb {:add (mapv (fn [s] [s context]) premises)}))))
