;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.rewriteof-predicate-test
  "`rewriteOf` over **predicates** and **types** — round two of equality
  (docs/equality.md).  A merge `(rewriteOf Canonical Deprecated)` where the two are
  predicates or types (not individuals) retires the deprecated spelling and moves
  its *functor* uses — facts headed by it, the `genl` closure, the predicate
  metadata, and the rules that mention it — onto the representative, riding the same
  belief-following migration machinery that round one built for individuals.

  Each test pins one acceptance from the design prompt.  House rules apply:
  gensym'd temporaries via `tu/with-terms` (a predicate `bornIn` and a type `dog`
  come out camelCase / snake_case respectively, so the merge is between two fresh
  same-role terms), engine vocabulary (`rewriteOf`, `genl`, `transitive`,
  `disjoint`, `implies`) literal, and the neutral fixture asserts the KB restores."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- helpers (mirroring equality_test) -----------------------------------

(defn- believed? [kb sentence context]
  (let [h (v/handle-of kb sentence context)]
    (boolean (and h (v/in? kb h)))))

(defn- stored-not-believed? [kb sentence context]
  (let [h (v/handle-of kb sentence context)]
    (and (some? h) (some? (v/sentex kb h)) (not (v/in? kb h)))))

(defn- ask-values [kb goal context var]
  (set (map #(get % var) (v/ask kb goal context))))

;; ==========================================================================
;; 1. wff: rewriteOf is now legal over predicates and types, same-role only
;; ==========================================================================

(tu/deftest-kb predicate-and-type-rewriteof-is-well-formed
  (tu/with-terms [bornIn birthplaceOf CxName]
    (is (integer? (v/assert kb (list 'rewriteOf bornIn birthplaceOf) CxName))
        "a predicate-with-predicate rewriteOf is accepted"))
  (tu/with-terms [dog canine CxName]
    (is (integer? (v/assert kb (list 'rewriteOf canine dog) CxName))
        "a type-with-type rewriteOf is accepted")))

(tu/deftest-kb crossing-roles-is-refused
  (tu/with-terms [parentOf physical_object Muffet CxName]
    (testing "an individual with a predicate is a likely import bug"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'rewriteOf parentOf Muffet) CxName))))
    (testing "a clearly-camelCase predicate with a clearly-snake_case type"
      ;; built by hand rather than taken from `with-terms`: a predicate temp is bare
      ;; lowercase now, which satisfies both conventions and so clashes with neither —
      ;; this assertion needs a name that is unambiguously a relation
      (let [camelPred (symbol (str (tu/tmp-pred) "Of"))]
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list 'rewriteOf camelPred physical_object) CxName)))))))

;; ==========================================================================
;; 2. Predicate merge over facts (roles 2 — functor position)
;; ==========================================================================
;; Store a fact under the deprecated predicate, merge, and the representative
;; predicate now answers while the deprecated predicate's extent does not.

(tu/deftest-kb predicate-merge-moves-facts-to-the-representative-functor
  (tu/with-terms [bornIn birthplaceOf Ada London CxName]
    (v/assert kb (list birthplaceOf Ada London) CxName)
    (v/assert kb (list 'rewriteOf bornIn birthplaceOf) CxName)
    (testing "the representative-headed fact is believed"
      (is (believed? kb (list bornIn Ada London) CxName)))
    (testing "the deprecated-headed fact is stored but blocked"
      (is (stored-not-believed? kb (list birthplaceOf Ada London) CxName)))
    (testing "an open query under the representative binds"
      (is (= #{London} (ask-values kb (list bornIn Ada '?c) CxName '?c))))
    (testing "a goal under the retired spelling is rewritten and still answers"
      (is (= #{London} (ask-values kb (list birthplaceOf Ada '?c) CxName '?c))))
    (testing "the deprecated predicate's extent has no believed sentex"
      (is (empty? (v/sentexes-with-functor kb birthplaceOf {:believed? true})))
      (is (seq (v/sentexes-with-functor kb bornIn {:believed? true}))))))

;; ==========================================================================
;; 3. Predicate merge over rules (role 4 — the genuine work)
;; ==========================================================================
;; A rule written on the deprecated predicate fires after the merge as though it
;; had been written on the representative; retracting the merge restores it.

(tu/deftest-kb a-rule-on-the-deprecated-predicate-fires-under-the-representative
  (tu/with-terms [bornIn birthplaceOf knownPlace Ada London CxName]
    (v/assert-rule kb [(list birthplaceOf '?x '?c)] (list knownPlace '?c) CxName {:direction :forward})
    (v/assert kb (list birthplaceOf Ada London) CxName)
    (testing "before the merge the rule concludes under the deprecated predicate"
      (is (believed? kb (list knownPlace London) CxName)))
    (let [eq (v/assert kb (list 'rewriteOf bornIn birthplaceOf) CxName)]
      (testing "after the merge the conclusion still holds (rule fired on the twin fact)"
        (is (believed? kb (list knownPlace London) CxName)))
      (testing "the representative-headed rule exists and fires on a *new* fact"
        (tu/with-terms [Bob Paris]
          (v/assert kb (list bornIn Bob Paris) CxName)
          (is (believed? kb (list knownPlace Paris) CxName)
              "a fact asserted under the representative reaches the migrated rule")))
      (testing "retracting the merge restores the original rule and its behaviour"
        (v/retract! kb eq)
        (is (believed? kb (list birthplaceOf Ada London) CxName)
            "the original fact revives")
        (is (believed? kb (list knownPlace London) CxName)
            "the original rule concludes again")))))

(tu/deftest-kb merge-before-rule-and-rule-before-merge-agree
  (letfn [(place [order]
            (tu/with-neutral-kb [kb tu/fresh]
              (tu/with-terms [bornIn birthplaceOf knownPlace Ada London CxName]
                (let [rule! #(v/assert-rule kb [(list birthplaceOf '?x '?c)]
                                            (list knownPlace '?c) CxName {:direction :forward})
                      fact! #(v/assert kb (list birthplaceOf Ada London) CxName)
                      merge! #(v/assert kb (list 'rewriteOf bornIn birthplaceOf) CxName)]
                  (doseq [op order] (op {:rule rule! :fact fact! :merge merge!}))
                  {:known  (believed? kb (list knownPlace London) CxName)
                   :moved  (believed? kb (list bornIn Ada London) CxName)
                   :blocked (stored-not-believed? kb (list birthplaceOf Ada London) CxName)}))))]
    (let [rbm (place [#((% :rule)) #((% :fact)) #((% :merge))])   ; rule, fact, then merge
          mbr (place [#((% :merge)) #((% :rule)) #((% :fact))])]  ; merge first, then rule + fact
      (is (= rbm mbr) "order of rule / fact / merge must not change belief")
      (is (:known rbm))
      (is (:moved rbm))
      (is (:blocked rbm)))))

;; A migrated rule keeps the flavour of the rule it restates — its wrappers ride the
;; record, not the stored sentence, so re-canonicalizing the rewritten bare implies
;; must put them back (`rules/rewrap`).

(tu/deftest-kb rule-migration-preserves-defeasibility
  (tu/with-terms [bornIn birthplaceOf knownPlace Ada London CxName]
    (v/assert kb (list 'set/defaultRule
                       (list 'set/forwardRule (list 'implies (list birthplaceOf '?x '?c) (list knownPlace '?c))))
              CxName)
    (v/assert kb (list birthplaceOf Ada London) CxName)
    (v/assert kb (list 'rewriteOf bornIn birthplaceOf) CxName)
    (let [kh   (v/handle-of kb (list knownPlace London) CxName)
          twin (->> (v/supporting-justifications kb kh) (map :informant) (filter integer?) first)]
      (is (some? twin) "the defeasible rule fired on the migrated fact")
      (is (:defeasible (v/sentex kb twin)) "the twin rule stays defeasible")
      (is (= :default (v/defeat-class kb kh))
          "so its conclusion is held at :default, not hardened to :monotonic"))))

(tu/deftest-kb rule-migration-preserves-backward-only-direction
  (tu/with-terms [bornIn birthplaceOf knownPlace Ada London CxName]
    ;; a backward-only rule never forward-chains — that must survive the merge
    (v/assert kb (list 'set/backwardRule
                       (list 'implies (list birthplaceOf '?x '?c) (list knownPlace '?c)))
              CxName)
    (v/assert kb (list birthplaceOf Ada London) CxName)
    (v/assert kb (list 'rewriteOf bornIn birthplaceOf) CxName)
    (testing "the twin does not forward-chain (direction :backward preserved)"
      (is (not (believed? kb (list knownPlace London) CxName))))
    (testing "but it is still backward-provable under the representative"
      (is (v/query? kb (list knownPlace London) CxName {:max-depth 2})))))

;; A migrated rule keeps its exceptWhen exception — the meta-sentex is re-pointed onto
;; the twin, so the twin fires guarded (docs/equality.md, round two).

(tu/deftest-kb a-migrated-rule-keeps-its-exception
  (tu/with-terms [bornIn birthplaceOf knownPlace secret Ada London Bob Paris CxName]
    ;; birthplaceOf x c  =>  knownPlace c, EXCEPT when (secret x) — exception on a
    ;; *different* predicate than the one that will be merged
    (v/assert kb (list 'exceptWhen (list secret '?x)
                       (list 'set/forwardRule (list 'implies (list birthplaceOf '?x '?c) (list knownPlace '?c))))
              CxName)
    (v/assert kb (list birthplaceOf Ada London) CxName)
    (v/assert kb (list birthplaceOf Bob Paris) CxName)
    (v/assert kb (list secret Bob) CxName)
    (testing "before the merge the exception blocks Bob but not Ada"
      (is (believed? kb (list knownPlace London) CxName))
      (is (not (believed? kb (list knownPlace Paris) CxName))))
    (let [eq (v/assert kb (list 'rewriteOf bornIn birthplaceOf) CxName)]  ; predicate merge
      (testing "after the merge the migrated rule concludes AND still excepts"
        (is (believed? kb (list knownPlace London) CxName) "Ada's conclusion survives")
        (is (not (believed? kb (list knownPlace Paris) CxName))
            "Bob is still excepted — the exception migrated onto the twin rule"))
      (testing "the migrated exception blocks a NEW secret fact fed to the twin"
        (tu/with-terms [Cid Rome]
          (v/assert kb (list bornIn Cid Rome) CxName)
          (is (believed? kb (list knownPlace Rome) CxName) "Cid concludes while not secret")
          (v/assert kb (list secret Cid) CxName)
          (is (not (believed? kb (list knownPlace Rome) CxName))
              "asserting secret blocks the twin rule — its exception re-check index moved")))
      (testing "retracting the merge revives the original rule and its exception"
        (v/retract! kb eq)
        (is (believed? kb (list knownPlace London) CxName))
        (is (not (believed? kb (list knownPlace Paris) CxName))
            "Bob is excepted again under the original rule")))))

;; The mirror of the above with the arrival order flipped: the merge runs FIRST, then the
;; exception arrives.  Migration ran before the exception existed, so it never saw it —
;; the exception lands on the superseded original and the live twin fires *unguarded*
;; unless it is re-pointed onto the twin on arrival (`migrate-meta-onto-twins`,
;; docs/equality.md, the meta-after-merge case).

(tu/deftest-kb an-exception-asserted-after-the-merge-guards-the-live-twin
  (tu/with-terms [bornIn birthplaceOf knownPlace secret Ada London Bob Paris CxName]
    (v/assert kb (list 'implies (list birthplaceOf '?x '?c) (list knownPlace '?c)) CxName {:direction :forward})
    (v/assert kb (list birthplaceOf Ada London) CxName)
    (v/assert kb (list birthplaceOf Bob Paris) CxName)
    (v/assert kb (list secret Bob) CxName)
    (let [eq (v/assert kb (list 'rewriteOf bornIn birthplaceOf) CxName)]  ; merge migrates the rule FIRST
      (testing "the twin concludes for both before any exception exists"
        (is (believed? kb (list knownPlace London) CxName))
        (is (believed? kb (list knownPlace Paris) CxName) "Bob concludes — nothing guards him yet"))
      ;; NOW the exception arrives, naming the rule by its (superseded) wrapper form
      (v/assert kb (list 'exceptWhen (list secret '?x)
                         (list 'set/forwardRule (list 'implies (list birthplaceOf '?x '?c) (list knownPlace '?c))))
                CxName)
      (testing "the late exception re-points onto the twin and guards it"
        (is (believed? kb (list knownPlace London) CxName) "Ada is not secret — still concludes")
        (is (not (believed? kb (list knownPlace Paris) CxName))
            "Bob is now excepted — the exception migrated onto the live twin"))
      (testing "and it still guards a NEW secret fed to the twin's predicate"
        (tu/with-terms [Cid Rome]
          (v/assert kb (list bornIn Cid Rome) CxName)
          (is (believed? kb (list knownPlace Rome) CxName) "Cid concludes while not secret")
          (v/assert kb (list secret Cid) CxName)
          (is (not (believed? kb (list knownPlace Rome) CxName)) "asserting secret blocks the twin")))
      (testing "retracting the merge revives the original rule, still guarded"
        (v/retract! kb eq)
        (is (believed? kb (list knownPlace London) CxName))
        (is (not (believed? kb (list knownPlace Paris) CxName)) "Bob excepted under the original")))))

(tu/deftest-kb a-migrated-multi-antecedent-rule-realigns-its-exception
  ;; When a merge reorders a rule's antecedents, the twin renumbers its canonical
  ;; variables — so the exception query (stored in canonical vars) must be realigned or
  ;; it would key on the wrong argument.  Merging `stepOf` to a name that sorts *before*
  ;; `relOf` moves the second antecedent to the front; the exception is on `relOf`'s
  ;; first arg and must still key there.
  (tu/with-terms [relOf stepOf aStepOf goalOf flagOf A B Mid End CxName]
    (v/assert kb (list 'exceptWhen (list flagOf '?x)
                       (list 'set/forwardRule (list 'implies (list 'and (list relOf '?x '?y) (list stepOf '?y '?z))
                                                    (list goalOf '?x '?z))))
              CxName)
    (v/assert kb (list relOf A Mid) CxName)
    (v/assert kb (list relOf B Mid) CxName)
    (v/assert kb (list stepOf Mid End) CxName)
    (v/assert kb (list flagOf B) CxName)          ; B flagged (first arg), A not
    (testing "before the merge: A concludes, B is excepted"
      (is (believed? kb (list goalOf A End) CxName))
      (is (not (believed? kb (list goalOf B End) CxName))))
    (v/assert kb (list 'rewriteOf aStepOf stepOf) CxName)   ; reorders the antecedents
    (testing "after the merge the exception still keys on the first argument"
      (is (believed? kb (list goalOf A End) CxName) "A still concludes")
      (is (not (believed? kb (list goalOf B End) CxName))
          "B is still excepted — the exception realigned to the twin's canonical vars"))))

(tu/deftest-kb a-migrated-naf-rule-keeps-its-guard
  (tu/with-terms [bornIn birthplaceOf knownPlace disputed Ada London CxName]
    ;; birthplaceOf x c AND (unknown (disputed c)) => knownPlace c
    (v/assert kb (list 'implies
                       (list 'and (list birthplaceOf '?x '?c) (list 'unknown (list disputed '?c)))
                       (list knownPlace '?c))
              CxName {:direction :forward})
    (v/assert kb (list birthplaceOf Ada London) CxName)
    (testing "before the merge the NAF antecedent holds (London not disputed) → concludes"
      (is (believed? kb (list knownPlace London) CxName)))
    (v/assert kb (list 'rewriteOf bornIn birthplaceOf) CxName)
    (testing "the migrated rule still concludes (NAF rewrote with the rule sentence)"
      (is (believed? kb (list knownPlace London) CxName)))
    (testing "and the migrated NAF antecedent still withdraws it when disputed arrives"
      (v/assert kb (list disputed London) CxName)
      (is (not (believed? kb (list knownPlace London) CxName))
          "the twin rule's unknown-guard re-check index moved with it"))))

;; ==========================================================================
;; 4. Type merge — the genl closure moves (roles 3, 2)
;; ==========================================================================

(tu/deftest-kb type-merge-moves-the-genl-closure-and-memberships
  (tu/with-terms [puppy dog canine animal Rex CxName]
    (v/assert kb (list 'genl puppy dog) CxName)
    (v/assert kb (list 'genl dog animal) CxName)
    (v/assert kb (list dog Rex) CxName)
    (v/assert kb (list 'rewriteOf canine dog) CxName)
    (testing "membership and the closure answer under the representative"
      (is (v/isa? kb Rex canine CxName))
      (is (v/isa? kb Rex animal CxName))
      (is (contains? (set (v/genls kb canine)) animal))
      (is (contains? (set (v/specs kb canine)) puppy)))
    (testing "the deprecated type is superseded"
      (is (stored-not-believed? kb (list dog Rex) CxName))
      (is (stored-not-believed? kb (list 'genl dog animal) CxName)))
    (testing "the deprecated type no longer answers isa?"
      (is (not (contains? (set (v/genls kb dog)) animal))
          "dog's own closure is gone once nothing believes its edges")))
  ;; retracting the merge must *revive* the genl closure — the un-supersession branch
  ;; of the settle-finish reconcile.  Fresh terms so this is independent of the block above.
  (tu/with-terms [dog canine animal Rex CxName]
    (v/assert kb (list 'genl dog animal) CxName)
    (v/assert kb (list dog Rex) CxName)
    (let [eq (v/assert kb (list 'rewriteOf canine dog) CxName)]
      (is (v/isa? kb Rex canine CxName))
      (is (not (contains? (set (v/genls kb dog)) animal)) "dog's edge is superseded")
      (v/retract! kb eq)
      (testing "the retired type's closure comes back and the merge is undone"
        (is (contains? (set (v/genls kb dog)) animal) "dog's genl edge revived")
        (is (v/isa? kb Rex animal CxName))
        (is (believed? kb (list dog Rex) CxName) "the original membership revived")
        (is (not (v/isa? kb Rex canine CxName)) "canine is no longer dog")))))

;; ==========================================================================
;; 5. Predicate metadata moves under the representative (role 5)
;; ==========================================================================

(tu/deftest-kb transitive-metadata-survives-a-predicate-merge
  (tu/with-terms [tangiblePartOf containedBy A B C CxName]
    ;; declare containedBy transitive, then retire it in favour of tangiblePartOf
    (v/assert kb (list 'transitive containedBy) CxName)
    (v/assert kb (list containedBy A B) CxName)
    (v/assert kb (list containedBy B C) CxName)
    (v/assert kb (list 'rewriteOf tangiblePartOf containedBy) CxName)
    (testing "the representative predicate is transitive"
      (is (v/has-prop? kb :transitive tangiblePartOf))
      (is (v/ask? kb (list tangiblePartOf A C) CxName)
          "transitivity holds under the representative across the migrated facts"))))

(tu/deftest-kb disjointness-survives-a-type-merge
  (tu/with-terms [dog canine cat CxName]
    (v/assert kb (list 'disjoint dog cat) CxName)
    (v/assert kb (list 'rewriteOf canine dog) CxName)
    (testing "the representative type stays disjoint from the other"
      (is (v/disjoint? kb canine cat))
      (is (stored-not-believed? kb (list 'disjoint dog cat) CxName)))))

;; ==========================================================================
;; 5b. Soundness: a type merged in an exceptWhen QUERY keeps blocking
;; ==========================================================================
;; The flight rule mentions no merged predicate (so it is not migrated), but its
;; exception query does — and the exception meta-sentex migrates its query onto the
;; representative, so the exception keeps holding of the migrated facts.  Losing this
;; would be *unsound*: a penguin renamed would suddenly fly.

(tu/deftest-kb an-exception-query-migrates-and-keeps-blocking
  (tu/with-terms [bird flies penguin antarctic_bird Opus CxName]
    (v/assert kb (list 'exceptWhen (list penguin '?x)
                       (list 'set/defaultRule
                             (list 'set/forwardRule (list 'implies (list bird '?x) (list flies '?x)))))
              CxName)
    (v/assert kb (list bird Opus) CxName)
    (v/assert kb (list penguin Opus) CxName)
    (testing "before the merge the exception blocks — Opus does not fly"
      (is (not (believed? kb (list flies Opus) CxName))))
    (v/assert kb (list 'rewriteOf antarctic_bird penguin) CxName)   ; type merge
    (testing "after the merge the exception still blocks (query migrated to the rep)"
      (is (believed? kb (list antarctic_bird Opus) CxName)
          "the penguin fact moved to the representative")
      (is (not (believed? kb (list flies Opus) CxName))
          "the migrated exception still holds of the migrated fact — Opus stays grounded"))))

;; ==========================================================================
;; 6. No regression — an individual merge still holds rules back
;; ==========================================================================

(tu/deftest-kb an-individual-merge-does-not-migrate-a-rule
  (tu/with-terms [likes friendly Tom Thomas Ann CxName]
    ;; a rule mentioning an individual constant Tom
    (let [rule (v/assert-rule kb [(list likes '?x Tom)] (list friendly '?x) CxName {:direction :forward})]
      (v/assert kb (list 'rewriteOf Tom Thomas) CxName)   ; individuals: Thomas retired
      (testing "the rule itself is left alone (migration would have superseded it)"
        (is (v/in? kb rule) "the original rule stays believed, unmigrated")
        (is (v/premise? kb rule) "and remains a premise, not a derived twin"))
      (testing "reasoning still works via fact migration, on the original rule"
        (v/assert kb (list likes Ann Thomas) CxName)  ; migrates to (likes Ann Tom)
        (let [fh (v/handle-of kb (list friendly Ann) CxName)]
          (is (some? fh))
          (is (v/in? kb fh))
          (let [rules-used (->> (v/supporting-justifications kb fh)
                                (map :informant) (filter integer?) set)]
            (is (contains? rules-used rule)
                "the original rule fired — no migrated twin rule was created")))))))
