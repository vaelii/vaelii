;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.commutative-test
  "The three commutativity marks — `commutative`, `commutativeInArgs` and
  `commutativeInArgAndRest` — which say that named arguments of a relation may be
  permuted without changing the proposition.

  `symmetric` is the case that already existed: a binary predicate whose two arguments
  interchange, sorted into canonical order so the two spellings of a ground fact are one
  sentex.  These state the same licence at any arity, over a tail from a position or over
  a named set of positions, and reduce to one runtime group descriptor the canonicalizer
  reads (`sentex/commuting-components`).

  **Canonicalization is the feature.**  Every row below that asks about a query, a rule,
  a retraction or a recovery is asking the same question one step downstream: did the
  permitted permutations resolve to *one* stored sentex.  So the storage rows come first
  and the rest rest on them.

  Three places the engine can be wrong here, and a row for each:

  - **Variable arity conflated.**  A `:rest` group is closed by the literal's own arity,
    so `(covering W A B)` and `(covering W A B C)` are two claims and no permutation moves
    an argument between them.
  - **Multiplicity lost.**  Sorting a sequence is not deduping one: `(P W a b b)` keeps
    three tail arguments.
  - **One spelling leaning on the other.**  `commutative` and `commutativeInArgAndRest … 1`
    state one licence, and each installs it at its own arm rather than deriving the other.
    Each has to licence the permutation alone, withdraw it alone, and survive `recover`
    alone.  The CxCore bridges between the marks carry the directions that are not a
    backward cycle — two `set/inertRule`s for the equivalence, `set/forwardOnlyRule` for
    the arity bridge to `symmetric` — and a row below pins each one."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (tu/load-core!))))

(def ^:private U 'CxUniverse)

(defn- ex-type
  "The `:type` of the ex-info a thunk throws, or nil.  A refusal that collapses into an
  arity or naming error is exactly the regression a bare `thrown?` stays green through."
  [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(defn- stored
  "The sentence each believed match of `pattern` is stored under, as a set — what the
  store actually holds, rather than what the goal asked for."
  [kb pattern]
  (into #{} (map :sentence) (v/sentexes-matching kb pattern U)))

(defn- handles
  "The handles believed to match `pattern` in CxUniverse, as a set."
  [kb pattern]
  (into #{} (map :id) (v/sentexes-matching kb pattern U)))

;; ---- the pure reduction: declarations to components ----------------------
;;
;; No KB, so a failure here is the descriptor algebra and not the plumbing above it.

(tu/deftest-kb components-close-a-tail-at-the-literals-own-arity
  (is (= [[2 3 4]] (sx/commuting-components #{[:rest 2]} 4)))
  (is (= [[2 3]]   (sx/commuting-components #{[:rest 2]} 3)))
  (testing "a tail reaching one position licences nothing, so no component forms"
    (is (nil? (sx/commuting-components #{[:rest 2]} 2)))
    (is (nil? (sx/commuting-components #{[:rest 3]} 2))))
  (testing "a unary relation marked commutative is identity-only, without a special case"
    (is (nil? (sx/commuting-components #{[:rest 1]} 1)))))

(tu/deftest-kb overlapping-groups-merge-into-one-component
  ;; 1 and 2 interchange, 2 and 3 interchange, so 1 and 3 interchange through 2.  Applying
  ;; the two in sequence would make the stored form depend on which ran first, which is an
  ;; order dependence in the storage key.
  (is (= [[1 2 3]] (sx/commuting-components #{[:args [1 2]] [:args [2 3]]} 3)))
  (testing "disjoint groups stay two components"
    (is (= [[1 2] [3 4]] (sx/commuting-components #{[:args [1 2]] [:args [3 4]]} 4)))))

(tu/deftest-kb the-arrangement-fan-is-pruned-to-what-a-stored-fact-can-hold
  ;; Storage sorts the ground arguments inside a component, so an arrangement holding
  ;; them out of order matches nothing and is not probed.  With `v` variables among `g`
  ;; positions that is `g!/(g-v)!` probes rather than `g!`.
  (let [tail2 (fn [_ _] #{[:rest 2]})
        all   (fn [_ _] #{[:rest 1]})]
    (is (= 1 (count (sx/commuting-arrangements '(covering W A B C) tail2)))
        "a ground tail probes once, however long it is")
    (is (= 3 (count (sx/commuting-arrangements '(covering W A ?x C) tail2)))
        "one variable among three positions: 3!/2! = 3")
    (is (= 6 (count (sx/commuting-arrangements '(covering W ?a ?b C) tail2)))
        "two variables among three: 3!/1! = 6")
    (testing "a repeated variable writes one literal, so it is one probe"
      (is (= 1 (count (sx/commuting-arrangements '(sib ?a ?a) all)))))
    (testing "an unmarked predicate contributes no fan at all"
      (is (= ['(foo a b)] (sx/commuting-arrangements '(foo a b) (constantly nil)))))))

;; ---- storage: every permitted permutation is one sentex -----------------

(tu/deftest-kb every-permutation-of-a-marked-ternary-is-one-handle
  (tu/with-terms [mixes A B C]
    (v/assert kb (list 'commutative mixes) U)
    (let [hs (into #{} (for [args [[A B C] [A C B] [B A C] [B C A] [C A B] [C B A]]]
                         (v/assert kb (apply list mixes args) U)))]
      (is (= 1 (count hs))
          "all six ground permutations canonicalize to one sentex and one handle")
      (is (= 1 (count (handles kb (list mixes '?x '?y '?z))))
          "and the store holds one row, not six"))))

(tu/deftest-kb an-unnamed-position-stays-where-it-was-written
  (tu/with-terms [spans A B D E]
    ;; only the first two positions interchange; the third is fixed
    (v/assert kb (list 'commutativeInArgs spans 1 2) U)
    (let [h1 (v/assert kb (list spans A B D) U)
          h2 (v/assert kb (list spans B A D) U)
          h3 (v/assert kb (list spans A D B) U)]
      (is (= h1 h2) "the two named positions interchange")
      (is (not= h1 h3) "moving an argument out of the component is a different claim")
      (is (= 2 (count (handles kb (list spans '?x '?y '?z))))
          "so the store holds two rows")
      (is (not= h1 (v/assert kb (list spans A B E) U))
          "and the fixed position still distinguishes claims"))))

(tu/deftest-kb a-tail-commutes-and-the-whole-stays-in-position-one
  (tu/with-terms [covering W A B C]
    (v/assert kb (list 'commutativeInArgAndRest covering 2) U)
    (let [h (v/assert kb (list covering W A B C) U)]
      (is (= h (v/assert kb (list covering W C B A) U)) "the parts commute")
      (is (= h (v/assert kb (list covering W B A C) U)) "in any order")
      (is (not= h (v/assert kb (list covering A W B C) U))
          "moving the whole out of position 1 is a different claim"))))

(tu/deftest-kb two-runtime-arities-stay-two-claims
  ;; The sharp edge of variable arity: the component is closed by the *literal's* arity,
  ;; so a permutation can never move an argument between one arity's claim and another's.
  (tu/with-terms [covering W A B C]
    (v/assert kb (list 'commutativeInArgAndRest covering 2) U)
    (let [three (v/assert kb (list covering W A B) U)
          four  (v/assert kb (list covering W A B C) U)]
      (is (not= three four) "three arguments and four are two propositions")
      (is (= three (v/assert kb (list covering W B A) U)))
      (is (= four  (v/assert kb (list covering W C A B) U)))
      (is (= 2 (count (into (handles kb (list covering '?w '?a '?b))
                            (handles kb (list covering '?w '?a '?b '?c)))))))))

(tu/deftest-kb repeated-arguments-keep-their-multiplicity
  (tu/with-terms [covering W A B]
    (v/assert kb (list 'commutativeInArgAndRest covering 2) U)
    (let [h (v/assert kb (list covering W A B B) U)]
      (is (= (list covering W A B B) (:sentence (v/sentex kb h)))
          "commutativity changes order, never content or arity — the repeat is still there")
      (is (= h (v/assert kb (list covering W B A B) U)) "and the repeat permutes like any other")
      (is (not= h (v/assert kb (list covering W A B) U))
          "dropping the repeat is a different claim"))))

;; ---- lookup: a goal in any order finds the one row ----------------------

(tu/deftest-kb a-goal-naming-the-parts-in-any-order-finds-the-stored-row
  (tu/with-terms [covering W A B C]
    (v/assert kb (list 'commutativeInArgAndRest covering 2) U)
    (v/assert kb (list covering W A B C) U)
    (doseq [args [[W A B C] [W C B A] [W B C A]]]
      (is (v/ask? kb (apply list covering args) U)
          (str "ground goal " args " answers off the one stored row")))
    (is (not (v/ask? kb (list covering A W B C) U))
        "but a goal moving the whole out of position 1 does not")
    (testing "and a partly-bound goal binds the variable at every tail position"
      (is (= #{A B C} (into #{} (map '?x) (v/ask kb (list covering W '?x '?y '?z) U)))
          "?x reaches each of the three parts across the arrangements"))))

(tu/deftest-kb a-rule-antecedent-matches-a-permuted-fact-in-either-arrival-order
  ;; The arrival order is the whole point, and each half reaches the fact by a different
  ;; route.  **Fact first**: the rule's initial scan runs the matcher, which fans the
  ;; arrangements.  **Rule first**: the fact arrives as a datum and forward chaining runs
  ;; `res/match1`, a plain unify against the antecedent as written — so without
  ;; `trigger-bindings`' own fan the same two ingredients derive a conclusion or not
  ;; depending on which was written second, which is `symmetric-mirror`'s argument at a
  ;; longer arity.
  (testing "the fact is stored before the rule"
    (tu/with-terms [covering W A B C flagged]
      (v/assert kb (list 'commutativeInArgAndRest covering 2) U)
      (v/assert kb (list covering W A B C) U)
      ;; the antecedent names the parts in an order the stored row does not hold them in
      (v/assert-rule kb [(list covering '?w C A B)] (list flagged '?w)
                     U {:direction :forward})
      (is (v/ask? kb (list flagged W) U)
          "the rule's scan reaches the one stored row through a permitted permutation")))
  (testing "the rule is stored before the fact"
    (tu/with-terms [covering W A B C flagged]
      (v/assert kb (list 'commutativeInArgAndRest covering 2) U)
      (v/assert-rule kb [(list covering '?w C A B)] (list flagged '?w)
                     U {:direction :forward})
      (v/assert kb (list covering W A B C) U)
      (is (v/ask? kb (list flagged W) U)
          "and the trigger reaches it the same way, so belief does not read the order"))))

(tu/deftest-kb two-rules-differing-only-by-a-permutation-are-one-rule
  ;; A rule's antecedent literal canonicalizes exactly as a fact does when it is ground,
  ;; so the two spellings of a permitted permutation are one rule and one handle.  A
  ;; literal holding a variable is a **pattern** and is never reordered — `symmetric`'s
  ;; rule and this one's — so two rules differing by a permutation of a *pattern* stay
  ;; two, which is the normal canonical-variable behaviour and not a gap here.
  (tu/with-terms [covering W A B C flagged]
    (v/assert kb (list 'commutativeInArgAndRest covering 2) U)
    (is (= (v/assert-rule kb [(list covering W A B C)] (list flagged W) U {:direction :forward})
           (v/assert-rule kb [(list covering W C A B)] (list flagged W) U {:direction :forward}))
        "two ground antecedents differing by a permitted permutation are one rule")))

;; ---- the retroactive half: a declaration reaching stored facts ----------

(tu/deftest-kb a-late-declaration-folds-the-facts-already-stored
  ;; The same claim `symmetrize-existing` makes for `symmetric`, and for the blunter
  ;; reason: the entry point sorts, so a declaration arriving second would otherwise leave
  ;; the store holding spellings no later assertion produces — and two rows for one
  ;; proposition where both spellings were written, each retractable without the other.
  (tu/with-terms [covering W A B C]
    (let [h1 (v/assert kb (list covering W A B C) U)
          h2 (v/assert kb (list covering W C B A) U)]
      (is (not= h1 h2) "before the declaration the two orders are two rows")
      (v/assert kb (list 'commutativeInArgAndRest covering 2) U)
      (is (= 1 (count (handles kb (list covering '?w '?a '?b '?c))))
          "the declaration reaches back, and one proposition is one row")
      (is (= #{(list covering W A B C)} (stored kb (list covering '?w '?a '?b '?c)))
          "spelled the way every later assertion spells it"))))

(defn- orders [coll]
  (if (empty? coll)
    [[]]
    (mapcat (fn [x] (map #(vec (cons x %)) (orders (remove #{x} coll)))) coll)))

(tu/deftest-kb a-late-mark-reaches-a-rule-over-facts-already-stored
  ;; A mark moves which tuples an antecedent reaches over facts already stored.  A fact
  ;; out of canonical order is re-spelled and reaches the rules as new content; a fact
  ;; already in canonical order is not, and only the mark's own re-join reaches it
  ;; (`chain/permuting-rejoin-rules`).  Both spellings of the fact against both rule
  ;; targets, so one combination is a canonical fact the rule reads only permuted.
  (doseq [[mark ternary?] [['commutative false] ['commutativeInArgs true]]
          [x y]           [[0 1] [1 0]]
          target          [0 1]]
    (let [results
          (vec (for [order (orders [:rule :fact :mark])]
                 (tu/with-terms [rel A B C flagged]
                   (let [ab    [A B]
                         tail  (when ternary? [C])
                         other (nth ab (- 1 target))]
                     (doseq [step order]
                       (case step
                         :rule (v/assert-rule kb [(apply list rel '?v (nth ab target) tail)]
                                              (list flagged '?v) U {:direction :forward})
                         :fact (v/assert kb (apply list rel (nth ab x) (nth ab y) tail) U)
                         :mark (v/assert kb (if ternary? (list mark rel 1 2) (list mark rel)) U)))
                     [order (v/ask? kb (list flagged other) U)]))))]
      (is (every? second results)
          (str mark " fact " [x y] " target " target ": "
               (pr-str (mapv first (remove second results))))))))

(tu/deftest-kb the-mark-reads-the-exact-functor-and-not-the-subtype
  ;; `kb-sentex` reads the mark off the literal's own functor, so a `genl` edge below a
  ;; commutative predicate does not make the sub-predicate commutative — a row re-spelled
  ;; at the subtype would be one the entry point stores the other way round on the very
  ;; next write.  The same line `constraint_descension_test` holds for `symmetric`.
  (tu/with-terms [covering namedCovering W A B]
    (v/assert kb (list 'commutativeInArgAndRest covering 2) U)
    (v/assert kb (list 'genl namedCovering covering) U)
    (is (not= (v/assert kb (list namedCovering W A B) U)
              (v/assert kb (list namedCovering W B A) U))
        "the sub-predicate permutes nothing of its own")))

;; ---- the bridges ---------------------------------------------------------

(tu/deftest-kb a-symmetric-predicate-is-commutative-and-a-commutative-binary-is-symmetric
  (tu/with-terms [sibOf comm2]
    (v/assert kb (list 'symmetric sibOf) U)
    (is (v/ask? kb (list 'commutative sibOf) U)
        "(genl symmetric commutative) classifies every symmetric predicate")
    (v/assert kb (list 'commutative comm2) U)
    (v/assert kb (list 'arity comm2 2) U)
    (is (v/ask? kb (list 'symmetric comm2) U)
        "and the bridge rule reads the arity back the other way"))
  (testing "commutative at another arity implies neither symmetric nor arity 2"
    (tu/with-terms [comm3]
      (v/assert kb (list 'commutative comm3) U)
      (v/assert kb (list 'arity comm3 3) U)
      (is (not (v/ask? kb (list 'symmetric comm3) U)))
      (is (not (v/ask? kb (list 'arity comm3 2) U))))))

(tu/deftest-kb either-spelling-licences-the-permutation-on-its-own
  ;; The two spellings state one licence and neither derives the other: each arm installs
  ;; the group `[:rest 1]` itself.  So the canonicalizer has to fold a permutation under
  ;; whichever spelling was written, with the other never asserted and never believed.
  (tu/with-terms [mixes tails A B C]
    (v/assert kb (list 'commutative mixes) U)
    (is (= (v/assert kb (list mixes A B C) U)
           (v/assert kb (list mixes C B A) U))
        "the sugar alone folds every permutation onto one handle")
    (v/assert kb (list 'commutativeInArgAndRest tails 1) U)
    (is (= (v/assert kb (list tails A B C) U)
           (v/assert kb (list tails C B A) U))
        "and the tail-at-1 spelling alone folds the same permutations")
    (testing "neither spelling is derived from the other"
      (is (not (v/ask? kb (list 'commutativeInArgAndRest mixes 1) U))
          "the equivalence is inert, so the sugar concludes no tail-at-1")
      (is (not (v/ask? kb (list 'commutative tails) U))
          "and a tail-at-1 concludes no sugar"))))

(tu/deftest-kb no-bridge-between-the-marks-is-walkable-backward
  ;; Three CxCore rules bridge these marks, and each concludes something another of them
  ;; needs.  `set/forwardRule` adds forward chaining *without* taking the backward use
  ;; away (`rules/backward?` accepts `:forward`), so written that way all three answer
  ;; goals — and `provers/candidate-rules` carries no ancestor-goal guard to stop the
  ;; descent.  `(genl commutative relation)` puts `(commutative ?p)` under every open
  ;; `(relation ?x)` query, so the cost reached every caller of the inference engine:
  ;; `vaelii.arity-vocabulary-test` never finished under `VAELII_QUERY_ENGINE=inference`.
  ;;
  ;; The two directions of the equivalence are **inert** — each mark installs its group
  ;; at its own arm, so neither has to derive the other.  The arity bridge is
  ;; **forward-only** — it does derive, and only its backward direction is the cycle.
  ;; Either one written as `set/forwardRule` returns the stall, which is what this pins.
  (doseq [[rule want]
          [['(implies (and (commutative ?p)) (commutativeInArgAndRest ?p 1))      :inert]
           ['(implies (and (commutativeInArgAndRest ?p 1)) (commutative ?p))      :inert]
           ['(implies (and (commutative ?p) (arity ?p 2)) (symmetric ?p)) :forward-only]]]
    (let [h (v/handle-of kb rule 'CxCore)]
      (is (some? h) (str "the bridge is still written down: " (pr-str rule)))
      (is (= want (:direction (v/sentex kb h)))
          (str "a backward-walkable bridge here is the cycle: " (pr-str rule))))))

(tu/deftest-kb retracting-the-sugar-withdraws-its-licence
  ;; The mark installs the group, so withdrawing the mark has to uninstall it: a
  ;; permutation written afterwards is a claim of its own.
  (tu/with-terms [mixes A B C]
    (let [h (v/assert kb (list 'commutative mixes) U)]
      (is (= (v/assert kb (list mixes A B C) U)
             (v/assert kb (list mixes C B A) U))
          "the licence holds while the mark is believed")
      (v/retract! kb h)
      (is (not (v/ask? kb (list 'commutative mixes) U))
          "the mark goes")
      (is (not= (v/assert kb (list mixes A C B) U)
                (v/assert kb (list mixes B C A) U))
          "and the licence goes with it"))))

;; ---- the refusals --------------------------------------------------------

(tu/deftest-kb a-malformed-declaration-is-refused-at-the-entry-point
  (tu/with-terms [p]
    (testing "positions are one-based positive integers"
      (is (= :not-well-formed (ex-type #(v/assert kb (list 'commutativeInArgAndRest p 0) U))))
      (is (= :not-well-formed (ex-type #(v/assert kb (list 'commutativeInArgAndRest p -1) U))))
      (is (= :not-well-formed (ex-type #(v/assert kb (list 'commutativeInArgs p 1 0) U)))))
    (testing "a named set names at least two distinct positions, or it licences nothing"
      (is (= :not-well-formed (ex-type #(v/assert kb (list 'commutativeInArgs p 1) U))))
      (is (= :not-well-formed (ex-type #(v/assert kb (list 'commutativeInArgs p 1 1) U)))))))

(tu/deftest-kb the-written-position-order-does-not-decide-the-entry
  ;; The three arms key on one descriptor however the author wrote the positions, or a
  ;; retraction would miss the entry its assertion installed.
  (tu/with-terms [spans A B D]
    (v/assert kb (list 'commutativeInArgs spans 2 1) U)
    (is (= (v/assert kb (list spans A B D) U)
           (v/assert kb (list spans B A D) U))
        "(commutativeInArgs P 2 1) installs what (commutativeInArgs P 1 2) installs")))

(tu/deftest-kb retracting-the-declaration-stops-the-licence
  (tu/with-terms [covering W A B]
    (let [d (v/assert kb (list 'commutativeInArgAndRest covering 2) U)]
      (is (= (v/assert kb (list covering W A B) U)
             (v/assert kb (list covering W B A) U)))
      (v/retract! kb d)
      (is (not (v/ask? kb (list 'commutativeInArgAndRest covering 2) U))
          "the declaration is gone")
      ;; the *spelling* the migration left is a spelling and not a claim, so the rows
      ;; already stored stay as they are — `commute-existing` says why the write is not
      ;; undone.  What stops is the licence over writes that follow.
      (tu/with-terms [D E]
        (is (not= (v/assert kb (list covering W D E) U)
                  (v/assert kb (list covering W E D) U))
            "and a later pair of orders is two claims again")))))

;; ---- symmetric does not move --------------------------------------------

(tu/deftest-kb symmetric-keeps-its-canonicalization-lookup-and-classification
  (tu/with-terms [sibOf Ann Bob]
    (v/assert kb (list 'symmetric sibOf) U)
    (let [h (v/assert kb (list sibOf Ann Bob) U)]
      (is (= h (v/assert kb (list sibOf Bob Ann) U)) "one sentex for the pair")
      (is (v/ask? kb (list sibOf Ann Bob) U))
      (is (v/ask? kb (list sibOf Bob Ann) U))
      (is (= 2 (count (v/ask kb (list sibOf '?a '?b) U)))
          "an all-variable pattern still binds the one stored fact both ways round"))))

;; ---- recovery -----------------------------------------------------------

(defn- restarted
  "A process restart: a second KB value over the same stores, whose in-memory taxonomy
  and JTMS start empty and are rebuilt from the records alone.  `tu/test-kb` opens with
  `:recover? false`, so the rebuild is this call's and nothing else's."
  []
  (doto (tu/test-kb) (v/recover)))

(tu/deftest-kb a-restart-reads-the-commuting-table-back-off-the-records
  ;; The `:commuting` table is in memory and nowhere stored, so the only durable trace is
  ;; the declaration sentexes and the `:rebuild` arm that replays them.  A restart that
  ;; lost the table would go on answering queries — the records are already spelled
  ;; canonically — and would start storing a second row for the next permutation written.
  (tu/with-terms [covering W A B C]
    (v/assert kb (list 'commutativeInArgAndRest covering 2) U)
    (v/assert kb (list 'commutativeInArgs covering 2 3) U)
    (let [live (v/assert kb (list covering W A B C) U)
          back (restarted)]
      (is (= 1 (count (handles back (list covering '?w '?a '?b '?c))))
          "the recovered store holds the one row the live KB holds")
      (is (v/ask? back (list covering W C A B) U)
          "and answers a permuted goal off it")
      (is (= live (v/assert back (list covering W B C A) U))
          "and a permutation written after the restart still resolves to that row"))))

(tu/deftest-kb a-restart-replays-the-sugars-group-too
  ;; `(commutative P)` installs `[:rest 1]` at its own arm, so its `:rebuild` arm has to
  ;; replay the group as well as the `:commutative` prop.  A rebuild that replayed only
  ;; the prop would answer queries — the records are already spelled canonically — and
  ;; start storing a second row for the next permutation written, which is the failure
  ;; `a-restart-reads-the-commuting-table-back-off-the-records` describes for the other
  ;; two spellings.
  (tu/with-terms [mixes A B C]
    (v/assert kb (list 'commutative mixes) U)
    (let [live (v/assert kb (list mixes A B C) U)
          back (restarted)]
      (is (v/ask? back (list 'commutative mixes) U)
          "the mark comes back")
      (is (= 1 (count (handles back (list mixes '?a '?b '?c))))
          "the recovered store holds the one row the live KB holds")
      (is (= live (v/assert back (list mixes C B A) U))
          "and a permutation written after the restart still resolves to that row"))))

(tu/deftest-kb a-restart-revives-no-withdrawn-licence
  ;; The mark's group is supported by the mark's own handle, so a retraction before the
  ;; restart has to stay retracted: a rebuild replays the stored declaration sentexes,
  ;; and a withdrawn one is not among them.
  (tu/with-terms [mixes A B C]
    (let [h (v/assert kb (list 'commutative mixes) U)]
      (v/retract! kb h)
      (let [back (restarted)]
        (is (not (v/ask? back (list 'commutative mixes) U))
            "the withdrawn mark stays withdrawn")
        ;; two rows for one proposition is the failure, so the probe has to write both
        ;; and then take them back — the fixture holds this namespace net-neutral.
        (let [one (v/assert back (list mixes A B C) U)
              two (v/assert back (list mixes C B A) U)]
          (is (not= one two)
              "and the licence it installed does not come back with the restart")
          (v/retract! back one)
          (v/retract! back two))))))

;; ---- bulk load ----------------------------------------------------------

(tu/deftest-kb a-bulk-load-dedups-a-permutation-the-caller-cannot-see
  ;; The bulk fast path skips the dedup probe, because a distinct corpus never hits an
  ;; existing sentex — except that a *permutation* of a stored row is not distinct, and
  ;; the caller cannot tell: separating `(covering W C A B)` from a stored `(covering W A
  ;; B C)` needs exactly the taxonomy read the fast path is avoiding.  So a commuting
  ;; functor keeps the probe, and the bulk result is what loading one-by-one gives.
  (tu/with-terms [covering W A B C]
    (v/assert kb (list 'commutativeInArgAndRest covering 2) U)
    (binding [v/*bulk-load?* true]
      (v/assert-many kb [(list covering W A B C)
                         (list covering W C A B)
                         (list covering W B C A)]
                     U))
    (is (= 1 (count (handles kb (list covering '?w '?a '?b '?c))))
        "three permutations bulk-loaded are one row")))
