;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.constraint-nogood-test
  "Definitional violations as **nogoods** rather than as a throw and a drop.

  Disjointness, functionality and asymmetry each convict by naming a second believed
  sentex.  That is a nogood in exactly the sense `S` against `(not S)` is one, and the
  engine already has a theory of those: defeat the weaker, represent an equal
  defeasible pair as a dilemma, report an equal known-true pair.  These tests pin the
  three places that theory now reaches, and the one place it deliberately does not.

  What is *not* softened, and is tested here as much as what is:

  * A **malformed** sentence still throws — `wff` is about the sentence, not about a
    pair, and there is nothing to weigh it against.
  * A violation **against known-true content** still refuses on the assert path,
    because admitting it and then defeating it stores something the KB will never
    believe.
  * An **argument constraint** (`argIsa` / `argGenl` / `interArgIsa`) is convicted by the
    *absence* of a path from the argument's types to the constraint type — an
    open-world judgement with no opposing sentex — so it stays a refusal and, on the
    derivation path, a drop.
  * **`arity`** stays a refusal for a different reason, and `constraint-vocabulary-test`
    is where that is pinned: it *does* name an opposing sentex, and that sentex is the
    vocabulary entry the conviction is read through, so a nogood over the pair would
    defeat its own premise."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- fwd [antes conseq]
  (list 'set/forwardRule (vr/rule-sentence antes conseq)))

(defn- permutations [coll]
  (if (<= (count coll) 1)
    (list (seq coll))
    (for [i (range (count coll))
          p (permutations (concat (take i coll) (drop (inc i) coll)))]
      (cons (nth coll i) p))))

;;; ── asymmetry: a relation declared not to hold both ways ──────────────

(tu/deftest-kb an-asymmetric-pair-at-default-is-a-represented-dilemma
  ;; The measured gap: `(asymmetric P)` refused only against known-true content, so at
  ;; the default strength a relation declared not to hold both ways held both ways and
  ;; nothing said so.  Every other :default/:default clash in this engine is a
  ;; represented dilemma; this one was silence.
  (tu/with-terms [typLarger dog_t cat_t]
    (v/assert kb (list 'asymmetric typLarger) 'UniverseContext)
    (v/assert kb (list typLarger dog_t cat_t) 'UniverseContext)
    (testing "the converse is still admitted — neither claim outranks the other"
      (is (v/assert kb (list typLarger cat_t dog_t) 'UniverseContext)))
    (testing "but the KB no longer holds it in silence"
      (let [cs (v/contradictions kb)]
        (is (= 1 (count cs)) "the pair is reported exactly once")
        (is (= #{(v/handle-of kb (list typLarger dog_t cat_t) 'UniverseContext)
                 (v/handle-of kb (list typLarger cat_t dog_t) 'UniverseContext)}
               (:nogood (first cs))))
        (is (= 2 (count (:sides (first cs))))
            "both sides' justifications, which is what an application ranks with")))
    (testing "and both stay believed — a dilemma is represented, not decided"
      (is (v/ask? kb (list typLarger dog_t cat_t) 'UniverseContext))
      (is (v/ask? kb (list typLarger cat_t dog_t) 'UniverseContext)))))

(tu/deftest-kb an-asymmetric-pair-against-known-true-content-is-still-refused
  ;; the line the other two checks are generalized to: it was always read off `:class`
  (tu/with-terms [typLarger dog_t cat_t]
    (v/assert kb (list 'asymmetric typLarger) 'UniverseContext)
    (v/assert kb (list typLarger dog_t cat_t) 'UniverseContext {:strength :monotonic})
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list typLarger cat_t dog_t) 'UniverseContext)))
    (testing "and nothing was stored by the refusal"
      (is (nil? (v/handle-of kb (list typLarger cat_t dog_t) 'UniverseContext))))))

;;; ── the assert path keeps its guardrail unless asked otherwise ────────

(tu/deftest-kb a-disjoint-clash-on-the-assert-path-still-refuses-by-default
  (tu/with-terms [dog_t cat_t Muffet]
    (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
    (v/assert kb (list dog_t Muffet) 'UniverseContext)
    (is (thrown? clojure.lang.ExceptionInfo (v/assert kb (list cat_t Muffet) 'UniverseContext)))
    (is (nil? (v/handle-of kb (list cat_t Muffet) 'UniverseContext))
        "a refusal stores nothing")
    (is (empty? (v/contradictions kb)))))

(tu/deftest-kb the-assert-path-arbitrates-when-asked-to
  ;; `*arbitrate-constraints?*` is the policy seam: whether a *writer* is told no is a
  ;; question about the application, not about the engine.  On, all three checks read
  ;; the one rule — refuse only against known-true content.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb (tu/fresh)]
      (tu/with-terms [dog_t cat_t Muffet]
        (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
        (v/assert kb (list dog_t Muffet) 'UniverseContext)
        (testing "the clashing membership is admitted rather than refused"
          (is (v/assert kb (list cat_t Muffet) 'UniverseContext)))
        (testing "and the pair is a represented dilemma, both believed"
          (is (seq (v/sentexes-matching kb (list dog_t Muffet) 'UniverseContext)))
          (is (seq (v/sentexes-matching kb (list cat_t Muffet) 'UniverseContext)))
          (is (= 1 (count (v/contradictions kb)))))))))

(tu/deftest-kb arbitration-never-admits-a-clash-with-known-true-content
  ;; the one thing the var does not buy: admitting what the KB can never believe
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb (tu/fresh)]
      (tu/with-terms [dog_t cat_t Muffet]
        (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
        (v/assert kb (list dog_t Muffet) 'UniverseContext {:strength :monotonic})
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list cat_t Muffet) 'UniverseContext)))
        (is (nil? (v/handle-of kb (list cat_t Muffet) 'UniverseContext)))))))

;;; ── what stays a refusal ──────────────────────────────────────────────

(tu/deftest-kb a-malformed-sentence-still-throws-however-the-policy-is-set
  ;; `wff` is about the sentence.  There is no second believed sentex to weigh it
  ;; against, so there is nothing for `settle` to arbitrate and softening it would
  ;; simply store nonsense.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb (tu/fresh)]
      (tu/with-terms [dog_t Muffet]
        (testing "a genl cycle"
          (is (thrown? clojure.lang.ExceptionInfo
                       (v/assert kb (list 'genl dog_t dog_t) 'UniverseContext))))
        (testing "a genl of an individual"
          (is (thrown? clojure.lang.ExceptionInfo
                       (v/assert kb (list 'genl Muffet dog_t) 'UniverseContext))))
        (testing "a non-ground fact"
          (is (thrown? clojure.lang.ExceptionInfo
                       (v/assert kb (list dog_t '?x) 'UniverseContext))))))))

(tu/deftest-kb an-argument-constraint-is-not-a-nogood
  ;; It convicts by the *absence* of a path from the argument's types to the constraint
  ;; type — negation as failure, not a stored sentex — so there is no pair to make and
  ;; it stays a refusal at the door and a drop at the firing.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb (tu/fresh)]
      (tu/with-terms [person_t rock_t parentOf Boulder Muffet]
        (v/assert kb (list 'genl person_t 'thing) 'UniverseContext)
        (v/assert kb (list 'genl rock_t 'thing) 'UniverseContext)
        (v/assert kb (list 'argIsa parentOf 1 person_t) 'UniverseContext)
        (v/assert kb (list rock_t Boulder) 'UniverseContext)
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list parentOf Boulder Muffet) 'UniverseContext))
            "refused at the door even with arbitration on")
        (is (empty? (v/contradictions kb)))))))

;;; ── the loser has a reason ────────────────────────────────────────────

(tu/deftest-kb an-arbitrated-loser-is-stored-and-has-a-why-not
  ;; the point of arbitrating rather than dropping: a dropped conclusion leaves no
  ;; record, so `why-not` can only say `:not-stored`
  (tu/with-terms [dog_t fish_t Rex]
    (v/assert kb (list 'disjoint dog_t fish_t) 'UniverseContext)
    (v/assert kb (list dog_t Rex) 'UniverseContext {:strength :monotonic})
    (v/assert kb (list 'set/defaultRule (vr/rule-sentence [(list dog_t '?x)] (list fish_t '?x)))
              'UniverseContext)
    (let [h (v/handle-of kb (list fish_t Rex) 'UniverseContext)]
      (is (integer? h) "the conclusion is placed, not discarded")
      (is (not (v/in? kb h)))
      (is (= :defeated (:reason (v/why-not kb h)))))))

;;; ── what the report says ──────────────────────────────────────────────

(tu/deftest-kb a-definitional-dilemma-names-the-constraint-it-violated
  ;; a rebuttal and a definitional clash are both dilemmas and both stay believed, so
  ;; without `:kind` they read alike — and they are not alike
  (tu/with-terms [dog_t cat_t Muffet]
    (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
    (v/assert kb (list dog_t Muffet) 'UniverseContext)
    (v/assert kb (fwd [(list dog_t '?x)] (list cat_t '?x)) 'UniverseContext)
    (testing "a definitional clash names its constraint"
      (is (= [:disjoint] (mapv :kind (v/contradictions kb)))))
    (testing "and ranks above a rebuttal"
      (is (every? #(<= 3 (:priority %)) (v/contradictions kb))))))

(tu/deftest-kb a-rebuttal-dilemma-has-no-constraint-to-name
  (tu/with-terms [flies Opus]
    (v/assert kb (list flies Opus) 'UniverseContext)
    (v/assert kb (list 'not (list flies Opus)) 'UniverseContext)
    (testing "a rebuttal names none"
      (is (= [nil] (mapv :kind (v/contradictions kb)))))
    (testing "and ranks below a definitional clash"
      (is (every? #(<= (:priority %) 2) (v/contradictions kb))))))

(tu/deftest-kb a-clash-is-reported-never-stored
  ;; `(contradicts X Y)` is a report form, not a sentex — asserting one would make it a
  ;; premise needing truth maintenance of its own, and it would go stale the moment
  ;; either side moved.  CoreContext says so of the predicate; this holds the engine to
  ;; it, since the report *reads* like a sentence and the mistake would be invisible.
  (tu/with-terms [dog_t cat_t Muffet]
    (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
    (v/assert kb (list dog_t Muffet) 'UniverseContext)
    (let [before (v/sentex-count kb)]
      (v/assert kb (fwd [(list dog_t '?x)] (list cat_t '?x)) 'UniverseContext)
      (let [reported (:sentence (first (v/contradictions kb)))]
        (is (= 'contradicts (first reported)) "the report reads as a sentence")
        (is (zero? (count (v/sentexes-with-functor kb 'contradicts)))
            "and is stored nowhere")
        (is (nil? (v/handle-of kb reported 'UniverseContext)))
        (is (empty? (v/sentexes-matching kb (list 'contradicts '?a '?b) '?ctx)))
        (is (= (+ 2 before) (v/sentex-count kb))
            "the rule and its conclusion, and nothing for the clash")))))

(def ^:private report-keys
  "Every key a standing clash is reported with, whichever reading found it."
  #{:nogood :priority :sentence :handles :kind :sides})

(tu/deftest-kb an-irreducible-conflict-reports-the-full-shape
  ;; `conflicts` reports the same full shape `contradictions` does.  Handing back the
  ;; raw nogood here instead would give the *harder* case — where the engine has
  ;; declined hardest and the application has the most to do — the least to do it with.
  (tu/with-terms [dog_t fish_t Rex]
    (v/assert kb (list 'disjoint dog_t fish_t) 'UniverseContext)
    (v/assert kb (list dog_t Rex) 'UniverseContext {:strength :monotonic})
    (v/assert-rule kb [(list dog_t '?x)] (list fish_t '?x) 'UniverseContext)
    (let [c (first (v/conflicts kb))]
      (is (some? c) "an irreducible known-true clash")
      (is (= report-keys (into #{} (keys c))))
      (is (= :disjoint (:kind c)))
      (is (= 2 (count (:sides c))))
      (is (every? #(contains? % :justifications) (:sides c))
          "including what each side rests on — the material an application acts on")
      (is (= [:monotonic :monotonic] (mapv :defeat-class (:sides c)))))))

(tu/deftest-kb a-dilemma-reports-the-same-shape-as-a-conflict
  (tu/with-terms [dog_t cat_t Muffet]
    (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
    (v/assert kb (list dog_t Muffet) 'UniverseContext)
    (v/assert kb (fwd [(list dog_t '?x)] (list cat_t '?x)) 'UniverseContext)
    (is (= report-keys (into #{} (keys (first (v/contradictions kb)))))
        "the two readings differ in why the pair stands, not in what is reported")))

;;; ── the candidate set does not grow without bound ─────────────────────

(tu/deftest-kb a-pair-that-stops-clashing-leaves-the-candidate-set
  ;; `:clashes` is what lets a standing dilemma outlive the settle that found it, so it
  ;; is consulted every settle — which means a pair that has stopped clashing and is
  ;; never forgotten costs an `arbitrable-violations` call per settle, forever.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb (tu/fresh)]
      (tu/with-terms [dog_t cat_t Muffet]
        (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
        (v/assert kb (list dog_t Muffet) 'UniverseContext)
        (v/assert kb (list cat_t Muffet) 'UniverseContext)
        (is (= 1 (count (:pairs @(:clashes kb)))) "the pair is remembered")
        (testing "retracting the separation retires it, and it is forgotten"
          (v/retract! kb (v/handle-of kb (list 'disjoint dog_t cat_t) 'UniverseContext))
          (is (empty? (v/contradictions kb)))
          (is (empty? (:pairs @(:clashes kb)))
              "both members still stored and believed, and they no longer clash"))
        (testing "and re-declaring it finds the pair again through the region"
          (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
          (is (= 1 (count (v/contradictions kb)))))))))

(tu/deftest-kb a-standing-pair-is-not-re-derived-by-an-unrelated-settle
  ;; `:clashes` is consulted every settle and a settle runs after every mutation, so
  ;; re-deriving every standing pair each time makes loading N clashing facts O(N²) —
  ;; the shape docs/nmtms.md records for the defaults phase.  Measured before the memo:
  ;; one assert at 300 standing clashes took 36ms against 8ms at 50.
  ;;
  ;; Pinned by **object identity** rather than by a clock: a carried entry is the very
  ;; map the previous settle produced, which is only true if nothing re-derived it.  A
  ;; timing assertion would be flaky; this cannot be.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb (tu/fresh)]
      (tu/with-terms [dog_t cat_t Muffet Rex]
        (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
        (v/assert kb (list dog_t Muffet) 'UniverseContext)
        (v/assert kb (list cat_t Muffet) 'UniverseContext)
        (let [pair  (first (keys (:nogoods @(:clashes kb))))
              entry (get (:nogoods @(:clashes kb)) pair)]
          (is (some? entry))
          (testing "a settle that moves nothing of the pair's carries it forward"
            (v/assert kb (list dog_t Rex) 'UniverseContext)
            (is (identical? entry (get (:nogoods @(:clashes kb)) pair))
                "re-derived, so the memo is not being used"))
          (testing "and moving the vocabulary does re-derive it"
            ;; the separation itself changing is what the memo may never take on trust
            (v/retract! kb (v/handle-of kb (list 'disjoint dog_t cat_t) 'UniverseContext))
            (is (nil? (get (:nogoods @(:clashes kb)) pair)))
            (is (empty? (v/contradictions kb)))))))))

(tu/deftest-kb a-pair-with-a-defeated-member-is-kept
  ;; the other side of the pruning rule: a check cannot see past a defeat to say whether
  ;; the pair would still clash, so forgetting it would mean a revival went unreported
  (tu/with-terms [dog_t fish_t Rex]
    (v/assert kb (list 'disjoint dog_t fish_t) 'UniverseContext)
    (v/assert kb (list dog_t Rex) 'UniverseContext {:strength :monotonic})
    (v/assert kb (list 'set/defaultRule (vr/rule-sentence [(list dog_t '?x)] (list fish_t '?x)))
              'UniverseContext)
    (let [h (v/handle-of kb (list fish_t Rex) 'UniverseContext)]
      (is (not (v/in? kb h)) "the derived side lost")
      (is (= 1 (count (:pairs @(:clashes kb))))
          "and the pair is retained, so the clash is re-reported if it revives"))))

(tu/deftest-kb a-carried-report-still-names-a-side-s-second-derivation
  ;; The *report* is memoized on the settle's region beside the nogood itself, and one
  ;; part of it does not follow the region.  A **redundant** justification — a second
  ;; derivation of an already-believed conclusion, conferring no stronger a class — is
  ;; exactly the write the JTMS declines to relabel for, so a side's supporting set grows
  ;; while its handle never enters a region.  The justifications behind each side are what
  ;; a caller ranks a dilemma with, so a report carried past that is a report naming fewer
  ;; reasons than the KB holds.  `nmtms_test` pins the same property for a plain rebuttal;
  ;; here the whole chain — `:clashes`, then `:reports` — is the definitional one.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb (tu/fresh)]
      (tu/with-terms [dog_t cat_t Rex markA markB]
        (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
        (v/assert kb (list dog_t Rex) 'UniverseContext)
        (v/assert kb (list 'set/defaultRule (vr/rule-sentence [(list markA '?x)] (list cat_t '?x)))
                  'UniverseContext)
        (v/assert kb (list markA Rex) 'UniverseContext)
        (let [h (v/handle-of kb (list cat_t Rex) 'UniverseContext)]
          (is (= 1 (count (v/contradictions kb))) "a default/default clash is a dilemma")
          (is (v/in? kb h))
          ;; a second rule reaching the same conclusion: belief is unmoved, so no relabel
          (v/assert kb (list 'set/defaultRule (vr/rule-sentence [(list markB '?x)] (list cat_t '?x)))
                    'UniverseContext)
          (v/assert kb (list markB Rex) 'UniverseContext)
          (is (= 2 (count (v/supporting-justifications kb h))))
          (let [side (some (fn [c] (some #(when (= h (:handle %)) %) (:sides c)))
                           (v/contradictions kb))]
            (is (some? side))
            (is (= :disjoint (:kind (first (v/contradictions kb)))))
            (is (= (count (v/supporting-justifications kb h))
                   (count (:justifications side)))
                "the report names both derivations, not the one it named last settle")))))))

(tu/deftest-kb an-equal-known-true-clash-is-a-conflict-not-a-dilemma
  ;; the third branch of `decide-nogood`: neither side can be defeated, so it is
  ;; irreducible and reported by `conflicts` — never thrown from inside the fixpoint
  (tu/with-terms [dog_t fish_t Rex]
    (v/assert kb (list 'disjoint dog_t fish_t) 'UniverseContext)
    (v/assert kb (list dog_t Rex) 'UniverseContext {:strength :monotonic})
    ;; a bare rule confers :monotonic and is capped by its antecedent, so the
    ;; conclusion is known-true too and ties with the membership
    (v/assert-rule kb [(list dog_t '?x)] (list fish_t '?x) 'UniverseContext)
    (let [cs (v/conflicts kb)]
      (is (= 1 (count cs)))
      (is (= :disjoint (:kind (first cs))))
      (is (= #{(v/handle-of kb (list dog_t Rex)  'UniverseContext)
               (v/handle-of kb (list fish_t Rex) 'UniverseContext)}
             (:nogood (first cs)))))
    (is (empty? (v/contradictions kb)) "an irreducible clash is not a dilemma")))

;;; ── recomputed, never accumulated ─────────────────────────────────────

(tu/deftest-kb a-dilemma-goes-when-its-ingredient-does-and-comes-back-with-it
  ;; the discipline belief itself follows: the pair is re-derived from current state
  ;; each settle, so retracting an ingredient retires it and restoring one revives it.
  ;; A ledger entry would do neither — which is the difference between arbitrating a
  ;; clash and filing a report about it.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb (tu/fresh)]
      (tu/with-terms [dog_t cat_t Muffet]
        (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
        (v/assert kb (list dog_t Muffet) 'UniverseContext)
        (v/assert kb (list cat_t Muffet) 'UniverseContext)
        (is (= 1 (count (v/contradictions kb))))
        (testing "retracting one membership retires the pair"
          (v/retract! kb (v/handle-of kb (list cat_t Muffet) 'UniverseContext))
          (is (empty? (v/contradictions kb)))
          (is (seq (v/sentexes-matching kb (list dog_t Muffet) 'UniverseContext))
              "and leaves the survivor alone"))
        (testing "and asserting it again brings the pair back"
          (v/assert kb (list cat_t Muffet) 'UniverseContext)
          (is (= 1 (count (v/contradictions kb)))))
        (testing "retracting the *declaration* retires it too — nothing separates them now"
          (v/retract! kb (v/handle-of kb (list 'disjoint dog_t cat_t) 'UniverseContext))
          (is (empty? (v/contradictions kb))))))))

(tu/deftest-kb an-arbitration-survives-a-rebuild
  ;; A nogood is *state*, not an event: belief depends on it.  The exposure pass beside
  ;; it sits out a rebuild because "newly exposed" is vacuous when everything arrives at
  ;; once — but a rebuild that skipped this would come up with the loser of a decided
  ;; clash believed again, and the KB would answer differently either side of a restart.
  (tu/with-terms [dog_t fish_t Rex]
    (v/assert kb (list 'disjoint dog_t fish_t) 'UniverseContext)
    (v/assert kb (list dog_t Rex) 'UniverseContext {:strength :monotonic})
    (v/assert kb (list 'set/defaultRule (vr/rule-sentence [(list dog_t '?x)] (list fish_t '?x)))
              'UniverseContext)
    (let [h (v/handle-of kb (list fish_t Rex) 'UniverseContext)]
      (is (not (v/in? kb h)) "defeated before the rebuild")
      (v/recover kb)
      (is (not (v/in? kb h)) "and still defeated after it"))))

(tu/deftest-kb a-dilemma-survives-a-rebuild
  (tu/with-terms [dog_t cat_t Muffet]
    (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
    (v/assert kb (list dog_t Muffet) 'UniverseContext)
    (v/assert kb (fwd [(list dog_t '?x)] (list cat_t '?x)) 'UniverseContext)
    (is (= 1 (count (v/contradictions kb))) "a dilemma before the rebuild")
    (v/recover kb)
    (is (= 1 (count (v/contradictions kb))) "and the same dilemma after it")))

;;; ── a declaration reaching content stored before it ───────────────────

(tu/deftest-kb a-functional-declaration-arriving-last-is-arbitrated
  ;; the `predicate-sentexes` sweep: the two values were admissible when written,
  ;; because nothing said the predicate was functional yet
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb (tu/fresh)]
      (tu/with-terms [birthYearOf Tom]
        (v/assert kb (list birthYearOf Tom 1980) 'UniverseContext)
        (v/assert kb (list birthYearOf Tom 1990) 'UniverseContext)
        (is (empty? (v/contradictions kb)) "nothing says one value only, yet")
        (v/assert kb (list 'functional birthYearOf) 'UniverseContext)
        (is (= [:functional] (mapv :kind (v/contradictions kb))))))))

(tu/deftest-kb a-genl-edge-arriving-last-is-arbitrated
  ;; the `instances-below` sweep: the held types were not themselves separated until an
  ;; edge put one of them under a separated type
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb (tu/fresh)]
      (tu/with-terms [dog_t canine_t cat_t Rex]
        (v/assert kb (list 'genl canine_t 'thing) 'UniverseContext)
        (v/assert kb (list 'genl cat_t 'thing) 'UniverseContext)
        (v/assert kb (list 'genl dog_t 'thing) 'UniverseContext)
        (v/assert kb (list 'disjoint canine_t cat_t) 'UniverseContext)
        (v/assert kb (list dog_t Rex) 'UniverseContext)
        (v/assert kb (list cat_t Rex) 'UniverseContext)
        (is (empty? (v/contradictions kb)) "a dog-cat is odd but nothing separates them")
        (v/assert kb (list 'genl dog_t canine_t) 'UniverseContext)
        (is (= [:disjoint] (mapv :kind (v/contradictions kb))))))))

(tu/deftest-kb a-disjoint-metatype-arriving-last-is-arbitrated
  ;; the `disjointMetatype` sweep: the clique is a property of the code rather than
  ;; stored pairs, so the members have to be reached through `tax/metatype-members`
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb (tu/fresh)]
      (tu/with-terms [animalSpecies dog_t cat_t Muffet]
        (v/assert kb (list 'genl dog_t 'thing) 'UniverseContext)
        (v/assert kb (list 'genl cat_t 'thing) 'UniverseContext)
        (v/assert kb (list animalSpecies dog_t) 'UniverseContext)
        (v/assert kb (list animalSpecies cat_t) 'UniverseContext)
        (v/assert kb (list dog_t Muffet) 'UniverseContext)
        (v/assert kb (list cat_t Muffet) 'UniverseContext)
        (is (empty? (v/contradictions kb)) "the metatype is not disjoint yet")
        (v/assert kb (list 'disjointMetatype animalSpecies) 'UniverseContext)
        (is (= [:disjoint] (mapv :kind (v/contradictions kb))))
        (testing "and dropping the metatype releases the pair, as it releases the clique"
          (v/retract! kb (v/handle-of kb (list 'disjointMetatype animalSpecies) 'UniverseContext))
          (is (empty? (v/contradictions kb))))))))

(tu/deftest-kb a-metatype-member-arriving-last-is-arbitrated
  ;; the `metatype-member-reach` sweep, and the one trigger no functor names: a term
  ;; joining an already-disjoint metatype separates it from every member already there,
  ;; and the sentence saying so is an ordinary unary membership whose functor is
  ;; whatever the metatype happens to be called.  Only the taxonomy knows it declares
  ;; anything at all, so a fixed vocabulary of declaration functors cannot see it — and
  ;; the exposure pass, which reads the taxonomy, would report the pair while nothing
  ;; decided it.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb (tu/fresh)]
      (tu/with-terms [animalSpecies dog_t cat_t Muffet]
        (v/assert kb (list 'genl dog_t 'thing) 'UniverseContext)
        (v/assert kb (list 'genl cat_t 'thing) 'UniverseContext)
        (v/assert kb (list animalSpecies dog_t) 'UniverseContext)
        (v/assert kb (list 'disjointMetatype animalSpecies) 'UniverseContext)
        (v/assert kb (list dog_t Muffet) 'UniverseContext)
        (v/assert kb (list cat_t Muffet) 'UniverseContext)
        (is (empty? (v/contradictions kb))
            "cat_t is not a member yet, so the metatype separates nothing from dog_t")
        (v/assert kb (list animalSpecies cat_t) 'UniverseContext)
        (is (v/disjoint? kb dog_t cat_t) "the clique closed over the arriving member")
        (is (= [:disjoint] (mapv :kind (v/contradictions kb)))
            "the pair the new member separates is exposed but never arbitrated")))))

(tu/deftest-kb a-genlcontext-edge-arriving-last-is-arbitrated
  ;; the `members-in-cone` sweep: neither writer could see the other, so both
  ;; memberships were admissible — until a visibility edge put them in one cone
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb (tu/fresh)]
      (tu/with-terms [AContext BContext t1 t2 Pip]
        (v/assert kb (list 'genl t1 'thing) 'UniverseContext)
        (v/assert kb (list 'genl t2 'thing) 'UniverseContext)
        (v/assert kb (list 'genlContext AContext 'UniverseContext) 'UniverseContext)
        (v/assert kb (list 'genlContext BContext 'UniverseContext) 'UniverseContext)
        (v/assert kb (list 'disjoint t1 t2) 'UniverseContext)
        (v/assert kb (list t1 Pip) AContext)
        (v/assert kb (list t2 Pip) BContext)
        (is (not (v/sees? kb BContext AContext)))
        (is (empty? (v/contradictions kb))
            "each is admissible where it was written — neither context sees the other")
        (v/assert kb (list 'genlContext BContext AContext) 'UniverseContext)
        (is (= [:disjoint] (mapv :kind (v/contradictions kb)))
            "the visibility edge is what makes them a pair")))))

;;; ── the pair only one context can see ─────────────────────────────────

;; A separation, a functional slot and an asymmetric claim are all checked against what
;; the *asking* context can see, which is right — a context is convicted only on
;; grounds it can see.  It leaves a pair whose halves sit either side of a `genlContext`
;; edge answerable from exactly one of the two contexts they are written in, so the
;; question has to be asked from there rather than from whichever half arrived last
;; (`settle/clash-askers`).

(defn- straddle-kb
  "A general context, one that sees it, and the declaration in `UniverseContext` — the
  lattice all three kinds are exercised over."
  [kb gen spec]
  (v/assert kb (list 'genlContext gen 'UniverseContext) 'UniverseContext)
  (v/assert kb (list 'genlContext spec gen) 'UniverseContext))

;; Each written **general-last**, which is the order the general side's own check cannot
;; answer: it sees neither the specific membership nor the specific claim.  One test per
;; kind, since a clash reported once is reported until its ingredients move and a second
;; scenario in the same KB would read the first one's answer.

(tu/deftest-kb a-separation-across-a-visibility-edge-is-arbitrated
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-terms [GenContext SpecContext dog_t cat_t Muffet]
      (straddle-kb kb GenContext SpecContext)
      (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
      (v/assert kb (list cat_t Muffet) SpecContext)
      (v/assert kb (list dog_t Muffet) GenContext)
      (is (= [:disjoint] (mapv :kind (v/contradictions kb)))))))

(tu/deftest-kb a-functional-slot-filled-across-a-visibility-edge-is-arbitrated
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-terms [GenContext SpecContext ageOf Tom]
      (straddle-kb kb GenContext SpecContext)
      (v/assert kb (list 'functional ageOf) 'UniverseContext)
      (v/assert kb (list ageOf Tom 6) SpecContext)
      (v/assert kb (list ageOf Tom 5) GenContext)
      (is (= [:functional] (mapv :kind (v/contradictions kb)))))))

(tu/deftest-kb an-asymmetric-converse-across-a-visibility-edge-is-arbitrated
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-terms [GenContext SpecContext biggerThan Ann Bob]
      (straddle-kb kb GenContext SpecContext)
      (v/assert kb (list 'asymmetric biggerThan) 'UniverseContext)
      (v/assert kb (list biggerThan Bob Ann) SpecContext)
      (v/assert kb (list biggerThan Ann Bob) GenContext)
      (is (= [:asymmetric] (mapv :kind (v/contradictions kb)))))))

(tu/deftest-kb known-true-content-does-not-coexist-with-a-default-that-denies-it
  ;; What the reporting gap costs: the general claim is admitted because its own context
  ;; cannot see the specific one, and without a vantage that can, a `:monotonic` claim
  ;; sits beside a `:default` the KB knows to be wrong.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb (tu/fresh)]
      (tu/with-terms [GenContext SpecContext animal_t plant_t Ox]
        (straddle-kb kb GenContext SpecContext)
        (v/assert kb (list 'disjoint animal_t plant_t) 'UniverseContext)
        (v/assert kb (list plant_t Ox) SpecContext)
        (v/assert kb (list animal_t Ox) GenContext {:strength :monotonic})
        (is (v/ask? kb (list animal_t Ox) GenContext))
        (is (not (v/ask? kb (list plant_t Ox) SpecContext))
            "the default loses to known-true content it could not see when it was written")
        (is (empty? (v/contradictions kb)) "decided, so there is no dilemma left to report")))))

(tu/deftest-kb a-membership-stated-in-two-visible-contexts-forms-two-pairs
  ;; One sentence stated in a general context and again in one that sees it is *two*
  ;; sentexes, of possibly different strength, and a third membership that denies the
  ;; type denies both.  Naming only the content-first of them left the other believed
  ;; beside content that contradicts it.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb (tu/fresh)]
      (tu/with-terms [GenContext SpecContext dog_t cat_t Muffet]
        (straddle-kb kb GenContext SpecContext)
        (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
        (v/assert kb (list dog_t Muffet) GenContext)
        (v/assert kb (list dog_t Muffet) SpecContext)
        (v/assert kb (list cat_t Muffet) SpecContext)
        (is (= 2 (count (v/contradictions kb)))
            "one pair per opposing sentex, not one per opposing type")
        (is (= #{#{(v/handle-of kb (list cat_t Muffet) SpecContext)
                   (v/handle-of kb (list dog_t Muffet) GenContext)}
                 #{(v/handle-of kb (list cat_t Muffet) SpecContext)
                   (v/handle-of kb (list dog_t Muffet) SpecContext)}}
               (into #{} (map :nogood) (v/contradictions kb))))))))

(tu/deftest-kb a-pair-reachable-from-several-viewers-is-one-entry
  ;; Two incomparable siblings, and *two* contexts below both — so the pair has two
  ;; maximal common descendants and the check runs from each.  A nogood is keyed on the
  ;; handle pair and its sentence is content-ordered, so which viewer found it decides
  ;; nothing; an entry per viewer would report one clash twice and make the count a
  ;; property of the context lattice.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-terms [AContext BContext KContext LContext t1 t2 Pip]
      (v/assert kb (list 'genlContext AContext 'UniverseContext) 'UniverseContext)
      (v/assert kb (list 'genlContext BContext 'UniverseContext) 'UniverseContext)
      (doseq [k [KContext LContext]]
        (v/assert kb (list 'genlContext k AContext) 'UniverseContext)
        (v/assert kb (list 'genlContext k BContext) 'UniverseContext))
      (v/assert kb (list 'disjoint t1 t2) 'UniverseContext)
      (v/assert kb (list t1 Pip) AContext)
      (is (not (v/sees? kb BContext AContext)))
      (v/assert kb (list t2 Pip) BContext)
      (let [cs (v/contradictions kb)]
        (is (= 1 (count cs)) "one clash, however many contexts can see it")
        (is (= #{(v/handle-of kb (list t1 Pip) AContext)
                 (v/handle-of kb (list t2 Pip) BContext)}
               (:nogood (first cs))))
        (is (= :disjoint (:kind (first cs))))))))

(tu/deftest-kb a-retraction-that-splits-the-visibility-releases-the-pair
  ;; The other direction, and the one a maintained candidate set can get wrong: `:clashes`
  ;; is keyed on storage and recomputed from belief, so a pair whose *joint view* goes
  ;; away has to stop being reported and stop being remembered — not sit there costing an
  ;; `arbitrable-violations` call per settle for the rest of the KB's life.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb (tu/fresh)]
      (tu/with-terms [GenContext SpecContext dog_t cat_t Muffet]
        (straddle-kb kb GenContext SpecContext)
        (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
        (v/assert kb (list cat_t Muffet) SpecContext)
        (v/assert kb (list dog_t Muffet) GenContext)
        (is (= 1 (count (v/contradictions kb))))
        (is (= 1 (count (:pairs @(:clashes kb)))) "the pair is remembered")
        (testing "the edge leaving takes the joint view with it"
          (v/retract! kb (v/handle-of kb (list 'genlContext SpecContext GenContext)
                                      'UniverseContext))
          (is (not (v/sees? kb SpecContext GenContext)))
          (is (empty? (v/contradictions kb)))
          (is (empty? (:pairs @(:clashes kb)))
              "both members still believed, and no context sees them together")
          (is (v/ask? kb (list dog_t Muffet) GenContext))
          (is (v/ask? kb (list cat_t Muffet) SpecContext)))
        (testing "and the edge returning brings the pair back"
          (v/assert kb (list 'genlContext SpecContext GenContext) 'UniverseContext)
          (is (= 1 (count (v/contradictions kb)))))))))

;;; ── more than two ─────────────────────────────────────────────────────

(deftest ^:slow three-mutually-disjoint-memberships-report-all-three-pairs
  ;; A term holding three mutually disjoint types forms three pairs, and each stored
  ;; membership convicts against the other two.  The definitional checks stop at the
  ;; *first* violation, which is right for a refusal and wrong for discovery: which
  ;; partner each membership picked would come from the order the argument root handed
  ;; the memberships back — handle order, so arrival order.  Written as a permutation
  ;; because a count assertion alone would have passed while the *set* drifted.
  (binding [checks/*arbitrate-constraints?* true]
    (let [ops [#(v/assert % '(disjoint za zb) 'UniverseContext)
               #(v/assert % '(disjoint zb zc) 'UniverseContext)
               #(v/assert % '(disjoint za zc) 'UniverseContext)
               #(v/assert % '(za Pip) 'UniverseContext)
               #(v/assert % '(zb Pip) 'UniverseContext)
               #(v/assert % '(zc Pip) 'UniverseContext)]
          observe (fn [kb]
                    ;; the *set* of clashing sentence pairs, keyed on content — handles
                    ;; differ between orderings, so comparing them would prove nothing
                    {:pairs (into #{}
                                  (map (fn [c]
                                         (into #{} (map :sentence) (:sides c))))
                                  (v/contradictions kb))
                     :believed (count (filter #(seq (v/sentexes-matching kb (list % 'Pip) 'UniverseContext))
                                              '[za zb zc]))})
          os (into #{} (map (fn [ordering]
                              (let [kb (tu/fresh)]
                                (doseq [op ordering] (op kb))
                                (observe kb))))
                   (permutations ops))]
      (is (= 1 (count os))
          (str "three-way clash: " (count os) " distinct outcomes across 720 orderings — "
               (pr-str os)))
      (testing "all three pairs, and all three memberships still believed"
        (is (= 3 (count (:pairs (first os)))))
        (is (= 3 (:believed (first os)))))
      (tu/clear-kb! (tu/test-kb)))))

(tu/deftest-kb a-functional-clash-on-the-assert-path-arbitrates-when-asked-to
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-kb [kb (tu/fresh)]
      (tu/with-terms [birthYearOf Tom]
        (v/assert kb (list 'functional birthYearOf) 'UniverseContext)
        (v/assert kb (list birthYearOf Tom 1980) 'UniverseContext)
        (testing "the second value is admitted rather than refused"
          (is (v/assert kb (list birthYearOf Tom 1990) 'UniverseContext)))
        (is (= [:functional] (mapv :kind (v/contradictions kb))))))))

;;; ── order independence, tested directly ───────────────────────────────

(deftest a-violating-set-settles-the-same-way-in-every-arrival-order
  ;; The whole reason for the change.  Today's assert path blames whichever assert
  ;; arrives last for a property of a *set*: state the separation first and the second
  ;; membership throws, state it last and the memberships are merely reported.  Under
  ;; arbitration every order lands on the same belief and the same dilemma.
  ;;
  ;; Run with the policy on, because that is the configuration in which all three
  ;; routes — the two memberships and the declaration — agree.  24 orderings.
  (binding [checks/*arbitrate-constraints?* true]
    (let [ops [#(v/assert % '(genl zdog thing) 'UniverseContext)
               #(v/assert % '(disjoint zdog zfish) 'UniverseContext)
               #(v/assert % '(zdog Rex) 'UniverseContext)
               #(v/assert % '(zfish Rex) 'UniverseContext)]
          observe (fn [kb]
                    {:dog        (boolean (seq (v/sentexes-matching kb '(zdog Rex) 'UniverseContext)))
                     :fish       (boolean (seq (v/sentexes-matching kb '(zfish Rex) 'UniverseContext)))
                     :dilemmas   (count (v/contradictions kb))
                     :conflicts  (count (v/conflicts kb))})
          os (into #{} (map (fn [ordering]
                              (let [kb (tu/fresh)]
                                (doseq [op ordering] (op kb))
                                (observe kb))))
                   (permutations ops))]
      (is (= 1 (count os))
          (str "disjointness clash: " (count os) " distinct outcomes across 24 orderings — "
               (pr-str os)))
      (testing "and the one outcome represents the clash rather than hiding it"
        (is (= {:dog true :fish true :dilemmas 1 :conflicts 0} (first os))))
      (tu/clear-kb! (tu/test-kb)))))

(deftest a-clash-across-a-visibility-edge-settles-the-same-way-in-every-arrival-order
  ;; The clash only one side can see.  `ZGenContext` is general and `ZSpecContext` sees
  ;; it, so the two memberships are jointly visible from exactly one of the two contexts
  ;; they are written in — and the definitional checks are scoped to the asserting
  ;; context, correctly, because a context is only convicted on grounds it can see.
  ;; Asking the pair's question from the arriving sentex's *own* context therefore
  ;; answers it from the general side, which cannot see the specific membership at all.
  ;;
  ;; Belief is what has to agree, not storage: the general-claim-last order admits the
  ;; default and defeats it, while the specific-claim-last order is refused at the door
  ;; (admitting what the KB can never believe is still what `:arbitrate` will not do).
  ;; That is `belief-agrees-whichever-arrived-first-under-arbitrate`'s split, one
  ;; visibility edge out.  120 orderings.
  (binding [checks/*arbitrate-constraints?* true]
    (let [ops [#(v/assert % '(genlContext ZGenContext UniverseContext) 'UniverseContext)
               #(v/assert % '(genlContext ZSpecContext ZGenContext) 'UniverseContext)
               #(v/assert % '(disjoint zoanimal zoplant) 'UniverseContext)
               #(v/assert % '(zoanimal OX) 'ZGenContext {:strength :monotonic})
               #(v/assert % '(zoplant OX) 'ZSpecContext)]
          observe (fn [kb]
                    {:known-true (v/ask? kb '(zoanimal OX) 'ZGenContext)
                     :default    (v/ask? kb '(zoplant OX) 'ZSpecContext)
                     :dilemmas   (count (v/contradictions kb))
                     :conflicts  (count (v/conflicts kb))})
          os (into #{} (map (fn [ordering]
                              (let [kb (tu/fresh)]
                                (doseq [op ordering]
                                  (try (op kb) (catch clojure.lang.ExceptionInfo _ nil)))
                                (observe kb))))
                   (permutations ops))]
      (is (= 1 (count os))
          (str "clash across a visibility edge: " (count os)
               " distinct outcomes across 120 orderings — " (pr-str os)))
      (testing "and the one outcome defeats the default rather than leaving it beside content that denies it"
        (is (= {:known-true true :default false :dilemmas 0 :conflicts 0} (first os))))
      (tu/clear-kb! (tu/test-kb)))))

(deftest an-asymmetric-violating-set-settles-the-same-way-in-every-arrival-order
  ;; the same invariant for the check that was silent rather than throwing: the
  ;; declaration may arrive before or after either direction of the relation
  (binding [checks/*arbitrate-constraints?* true]
    (let [ops [#(v/assert % '(asymmetric zTypLarger) 'UniverseContext)
               #(v/assert % '(zTypLarger zdog zcat) 'UniverseContext)
               #(v/assert % '(zTypLarger zcat zdog) 'UniverseContext)]
          observe (fn [kb]
                    {:fwd      (v/ask? kb '(zTypLarger zdog zcat) 'UniverseContext)
                     :bwd      (v/ask? kb '(zTypLarger zcat zdog) 'UniverseContext)
                     :dilemmas (count (v/contradictions kb))})
          os (into #{} (map (fn [ordering]
                              (let [kb (tu/fresh)]
                                (doseq [op ordering] (op kb))
                                (observe kb))))
                   (permutations ops))]
      (is (= 1 (count os))
          (str "asymmetric pair: " (count os) " distinct outcomes across 6 orderings — "
               (pr-str os)))
      (is (= {:fwd true :bwd true :dilemmas 1} (first os)))
      (tu/clear-kb! (tu/test-kb)))))

(deftest a-report-orders-its-sides-by-content-not-by-arrival
  ;; `clash-nogoods` orders the pair inside `:sentence` "by their printed form rather
  ;; than by which side was walked", and for a stated reason: a set that told the two
  ;; entries apart would report one clash or two depending on the arrival order.  The
  ;; report the caller actually reads has to follow the same rule, or the answer to
  ;; "which side is `(first (:sides c))`?" is whichever was asserted first — a handle
  ;; keyed on arrival order, reaching the public reading through the back door.
  (binding [checks/*arbitrate-constraints?* true]
    (let [shape (fn [ops]
                  (let [kb (tu/fresh)]
                    (doseq [op ops] (op kb))
                    (mapv (fn [r] [(:sentence r) (mapv :sentence (:sides r)) (:handles r)])
                          (v/contradictions kb))))
          strip (fn [rs] (mapv (fn [[s sides _]] [s sides]) rs))
          dog #(v/assert % '(zdog Rex) 'UniverseContext)
          cat #(v/assert % '(zcat Rex) 'UniverseContext)
          sep #(v/assert % '(disjoint zdog zcat) 'UniverseContext)
          pos #(v/assert % '(zbird Tweety) 'UniverseContext)
          neg #(v/assert % '(not (zbird Tweety)) 'UniverseContext)]
      (testing "a definitional clash"
        (is (= (strip (shape [sep dog cat])) (strip (shape [sep cat dog])))
            "the two sides swap places when the two memberships swap arrival order"))
      (testing "a plain rebuttal"
        (is (= (strip (shape [pos neg])) (strip (shape [neg pos])))))
      (testing "and `:handles` names the sides in the order `:sides` reports them"
        (let [[[_ sides handles]] (shape [sep dog cat])
              [[_ sides' handles']] (shape [sep cat dog])]
          (is (= sides sides'))
          (is (= 2 (count handles) (count handles')))))
      (tu/clear-kb! (tu/test-kb)))))

(deftest a-metatype-clique-settles-the-same-way-in-every-arrival-order
  ;; the same invariant for the trigger the taxonomy owns rather than the vocabulary:
  ;; the separation is a property of *four* sentences — the metatype declaration and the
  ;; two memberships that make the clique, plus the two type memberships that clash —
  ;; and none of them is the one to blame.  120 orderings.
  (binding [checks/*arbitrate-constraints?* true]
    (let [ops [#(v/assert % '(disjointMetatype zSpecies) 'UniverseContext)
               #(v/assert % '(zSpecies zdog) 'UniverseContext)
               #(v/assert % '(zSpecies zcat) 'UniverseContext)
               #(v/assert % '(zdog Rex) 'UniverseContext)
               #(v/assert % '(zcat Rex) 'UniverseContext)]
          observe (fn [kb]
                    {:dog       (boolean (seq (v/sentexes-matching kb '(zdog Rex) 'UniverseContext)))
                     :cat       (boolean (seq (v/sentexes-matching kb '(zcat Rex) 'UniverseContext)))
                     :dilemmas  (count (v/contradictions kb))
                     :conflicts (count (v/conflicts kb))})
          os (into #{} (map (fn [ordering]
                              (let [kb (tu/fresh)]
                                (doseq [op ordering] (op kb))
                                (observe kb))))
                   (permutations ops))]
      (is (= 1 (count os))
          (str "metatype clique: " (count os) " distinct outcomes across 120 orderings — "
               (pr-str os)))
      (is (= {:dog true :cat true :dilemmas 1 :conflicts 0} (first os)))
      (tu/clear-kb! (tu/test-kb)))))

;;; ── the policy as a per-KB option, not only a process default ──────────

;; `checks/*arbitrate-constraints?*` decides the policy for a whole process, and it is
;; set from an environment variable — so an application that wants one KB curating a
;; hand-written ontology beside one ingesting a corpus whose schema arrives last could
;; not have both.  `open-kb`'s `:constraints` is the same policy per KB, and it is a
;; front-door setting for `:naming`'s reason: whether a *writer* is told no is a question
;; about the application.

(defn- arbitrating-kb [] (v/open-kb (assoc tu/scratch-space :constraints :arbitrate)))
(defn- refusing-kb    [] (v/open-kb (assoc tu/scratch-space :constraints :refuse)))

(deftest the-per-kb-policy-decides-in-both-directions
  (testing ":arbitrate admits under a process default that refuses"
    (tu/with-neutral-kb [kb arbitrating-kb]
      (tu/with-terms [dog_t cat_t Muffet]
        (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
        (v/assert kb (list dog_t Muffet) 'UniverseContext)
        (is (v/assert kb (list cat_t Muffet) 'UniverseContext))
        (is (= 1 (count (v/contradictions kb)))))))
  (testing ":refuse refuses under a process default that arbitrates"
    (binding [checks/*arbitrate-constraints?* true]
      (tu/with-neutral-kb [kb refusing-kb]
        (tu/with-terms [dog_t cat_t Muffet]
          (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
          (v/assert kb (list dog_t Muffet) 'UniverseContext)
          (is (thrown? clojure.lang.ExceptionInfo
                       (v/assert kb (list cat_t Muffet) 'UniverseContext)))
          (is (nil? (v/handle-of kb (list cat_t Muffet) 'UniverseContext))))))))

(deftest a-kb-that-names-no-policy-still-reads-the-process-default
  ;; nil is not a third policy — it means the caller said nothing, and the var is what
  ;; answers then.  Without this, setting a default per KB would take the env var and
  ;; every `binding` out of the picture for every KB in the process.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-neutral-kb [kb tu/fresh]
      (tu/with-terms [dog_t cat_t Muffet]
        (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
        (v/assert kb (list dog_t Muffet) 'UniverseContext)
        (is (v/assert kb (list cat_t Muffet) 'UniverseContext)
            "an unstated policy arbitrates when the process default does")))))

(deftest a-declaration-arriving-last-reaches-back-only-under-arbitrate
  ;; The asymmetry this option exists for.  A schema that arrives after the facts it
  ;; convicts is the normal shape of an import, and under `:refuse` the violation is
  ;; *filed* while both memberships stay believed — the forward door refuses an identical
  ;; fact one line later, so whether the KB is consistent depends on arrival order.
  (testing ":refuse files the exposure and decides nothing"
    (tu/with-neutral-kb [kb refusing-kb]
      (tu/with-terms [dog_t cat_t Muffet]
        (v/assert kb (list dog_t Muffet) 'UniverseContext {:strength :monotonic})
        (v/assert kb (list cat_t Muffet) 'UniverseContext)
        (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
        (is (some #{:disjoint} (map :violation (v/violations kb))))
        (is (empty? (v/contradictions kb)))
        (is (v/ask? kb (list cat_t Muffet) 'UniverseContext)
            "the weaker membership is still believed"))))
  (testing ":arbitrate reaches back and defeats the weaker side"
    (tu/with-neutral-kb [kb arbitrating-kb]
      (tu/with-terms [dog_t cat_t Muffet]
        (v/assert kb (list dog_t Muffet) 'UniverseContext {:strength :monotonic})
        (v/assert kb (list cat_t Muffet) 'UniverseContext)
        (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
        (is (v/ask? kb (list dog_t Muffet) 'UniverseContext))
        (is (not (v/ask? kb (list cat_t Muffet) 'UniverseContext))
            "the default loses to known-true content it was stored before")))))

(deftest belief-agrees-whichever-arrived-first-under-arbitrate
  ;; Storage does not: the schema-first order **refuses** the clashing membership at the
  ;; door (admitting what the KB can never believe is what `:arbitrate` still will not
  ;; do), while the facts-first order admits and defeats it.  What has to agree is
  ;; belief, and it does.
  (let [believed (fn [build ops]
                   (tu/with-neutral-kb [kb build]
                     (tu/with-terms [dog_t cat_t Muffet]
                       (doseq [op (ops dog_t cat_t Muffet)]
                         (try (op kb) (catch clojure.lang.ExceptionInfo _ nil)))
                       {:known-true (v/ask? kb (list dog_t Muffet) 'UniverseContext)
                        :default    (v/ask? kb (list cat_t Muffet) 'UniverseContext)})))
        facts-first  (believed arbitrating-kb
                               (fn [d c F] [#(v/assert % (list d F) 'UniverseContext {:strength :monotonic})
                                            #(v/assert % (list c F) 'UniverseContext)
                                            #(v/assert % (list 'disjoint d c) 'UniverseContext)]))
        schema-first (believed arbitrating-kb
                               (fn [d c F] [#(v/assert % (list 'disjoint d c) 'UniverseContext)
                                            #(v/assert % (list d F) 'UniverseContext {:strength :monotonic})
                                            #(v/assert % (list c F) 'UniverseContext)]))]
    (is (= facts-first schema-first))
    (is (= {:known-true true :default false} facts-first))))

(deftest an-unknown-constraints-policy-is-refused
  ;; the same failure `:naming` is held to: a KB that silently took `:refuse` when it was
  ;; told `:arbitrate` refuses content the caller expected to land and be arbitrated
  (let [d (try (v/open-kb (assoc tu/scratch-space :constraints :arbitrat)) nil
               (catch clojure.lang.ExceptionInfo e (ex-data e)))]
    (is (= :unknown-option (:type d)))
    (is (= [:arbitrate :refuse] (:options d)))))

(deftest a-recover-decides-a-standing-clash-under-either-policy
  ;; The policy lives on the KB handle, not in the store, so the same records can be
  ;; reopened under the other one — and a rebuild's region is *every* stored sentex, so
  ;; `clash-nogoods` finds a standing clash from the region alone and decides it whichever
  ;; policy is in force.  Pinned rather than left to be discovered: under `:refuse` a KB
  ;; believes both sides of a clash it was built incrementally into and one side of the
  ;; same clash after a restart, and that asymmetry should not move without a test failing.
  ;; Its own space, keyed by a namespaced vector rather than a number, so it can
  ;; collide with nothing — including a second concurrent run, which `VAELII_TEST_SPACE`
  ;; moves the suite's block for but could not move a hard-coded integer.
  (let [spaces {:space [::restart]}
        build! (fn [kb dog_t cat_t Muffet]
                 (v/assert kb (list dog_t Muffet) 'UniverseContext {:strength :monotonic})
                 (v/assert kb (list cat_t Muffet) 'UniverseContext)
                 (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext))
        believed (fn [kb dog_t cat_t Muffet]
                   [(v/in? kb (v/handle-of kb (list dog_t Muffet) 'UniverseContext))
                    (v/in? kb (v/handle-of kb (list cat_t Muffet) 'UniverseContext))])]
    (tu/with-terms [dog_t cat_t Muffet]
      (let [kb (doto (v/open-kb (assoc spaces :constraints :refuse :recover? false)) (tu/clear-kb!))]
        (try
          (build! kb dog_t cat_t Muffet)
          (is (= [true true] (believed kb dog_t cat_t Muffet))
              ":refuse files the exposure and leaves both sides believed")
          (is (some #{:disjoint} (map :violation (v/violations kb))))
          (testing "recovered under the same policy, the clash is decided"
            (let [re (v/open-kb (assoc spaces :constraints :refuse :recover? :auto))]
              (is (= [true false] (believed re dog_t cat_t Muffet)))))
          (testing "and under :arbitrate, which agrees either side of the restart"
            (let [re (v/open-kb (assoc spaces :constraints :arbitrate :recover? :auto))]
              (is (= [true false] (believed re dog_t cat_t Muffet)))))
          (finally (tu/clear-kb! kb)))))))
