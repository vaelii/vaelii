;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.functional-in-arg-test
  "`(functionalInArg P n)` says the other arguments of `P` determine argument `n`.

  `functional` is the arity-2 special case with `n` fixed at 2: `functional-clashes`
  destructures `(nm/args sentence)` as `[a b]` and probes `(list q a '?fv)`, so arg 1
  determines arg 2 and nothing else can be said.  `namesObject(namespace, path, object)`
  wants `(namespace, path) → object` — a composite determinant — and there is no way to
  spell it.  The generalization is a *determinant set*: every argument position except
  `n`, taken together, fixes the filler at `n`.

  Two degenerate ends bracket it, and both are tested here rather than assumed:

  - `(functionalInArg P 2)` on a binary predicate must behave exactly as `(functional P)`
    does today.  That is the regression half — the generalization is not allowed to move
    arity-2 behaviour.
  - `(functionalInArg P 1)` on a **unary** predicate has an *empty* determinant, which
    reads as \"at most one filler, full stop.\"  Every filler must reconcile with every
    other, so it is the sharpest available probe of the merge/reject rule and it is what
    Pace's matrix uses.

  The merge/reject rule itself is not new and is not ours to invent.  `CxCore.txt:259`:

      two symbols derive (equals V1 V2) and merge, so retracting either fact or the
      declaration un-merges them, while two non-symbols such as 1980 and 1990 are
      refused outright, no merge being able to make two numbers one thing

  and `mergeable-values?` (checks.clj) is the code half.  So the matrix below is one
  question asked five ways: *does the generalized determinant reach the same verdict the
  arity-2 path reaches, in every context that can see both fillers?*

  Context shape throughout, per Pace's specification:

      CxUniverse
        ├── CxLeft   (p ThingOne)
        ├── CxRight  (p ThingTwo)
        ├── CxBottom      sees CxLeft and CxRight
        ├── CxBottomOne   sees CxLeft and CxRight
        └── CxBottomTwo   sees CxLeft and CxRight

  Neither CxLeft nor CxRight sees the other, so each is individually consistent and the
  clash exists only from a context below both.  The two bottoms are not redundant: they
  pin that the verdict is a property of *what a context sees*, not of which context ran
  first or of state left behind by the first descent.

  STATUS.  Written before the implementation existed, deliberately.  vaelii#43 closed
  the cross-context arrival-order gap this matrix was blocked on: rows 1, 2 and 4 are
  unpended and pass, alongside the five that never needed it (the arity-2 regression
  half, the composite-determinant case this mark exists for, and both 212-arity rows).
  Closing it took more than the accessor `functionalInArg` was missing from
  `special/equate-under-context-edge`'s own predicate roster — `derive-functional-
  equalities` (and its antisymmetric twin) now sweep every reader below a fact's own
  context on **every** arrival order, not only the genlCx-edge one, since these rows
  wire their contexts before their facts and so exercise the plain fact-arrival
  trigger; and `settle/could-clash?`, `partner-contexts` and `constraint-facts-in-
  cone` needed their own empty-determinant arm, since none of the three had ever read
  past arity 2 for a `functional`-family mark.  Two of the two-argument rows also had
  their own assertions corrected rather than the engine bent to fit them — row 1
  checked `contradictions` where an unmergeable cross-context clash actually lands in
  `violations` (the same door the arity-2 case already takes), and row 2's \"neither
  side alone concludes anything\" used the unscoped whole-KB `same-class?` where a
  scoped, per-context read was the question actually being asked.

  Row 3 (`an-asserted-difference-ties-the-merge-into-a-represented-dilemma`) settled
  its open question (vaelii#43/#44): the clash it sets up settles as a represented
  dilemma at `:default` strength — belief order-independent, contradiction reported
  once, exactly `nixon-diamond-is-the-same-dilemma-every-time`'s shape — and the row
  now asserts exactly that, because a represented dilemma is what \"the clash is not
  lost\" means, and it is stronger than the storage-checks the old expectations used."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(def ^:private U 'CxUniverse)

(defn- contexts!
  "Mint the five contexts and wire the bottoms to see both sides.

  `(genlCx c g)` puts `g` above `c` — `c` sees `g`.  The bottoms therefore name CxLeft
  and CxRight, not the other way about, and CxLeft/CxRight name only CxUniverse so they
  stay blind to each other."
  [kb {:keys [left right bottoms]}]
  (doseq [c (into [left right] bottoms)]
    (v/assert kb (list 'genlCx c U) U))
  (doseq [b bottoms, side [left right]]
    (v/assert kb (list 'genlCx b side) U)))

(defmacro ^:private check
  "`is`, with the KB kept out of the failure report.

  `clojure.test` prints the asserted form with its arguments *evaluated*, so any bare
  `(is (merged? kb x y))` dumps the entire KB record — records, index, TMS, provers — into
  the report and buries the one bit that matters.  Binding first prints `false`."
  [expr msg]
  `(let [r# ~expr] (is r# (str ~msg "  ⟵ " '~expr))))

(defn- merged?
  "Did the two fillers end up in one equality class?"
  [kb x y]
  (boolean (v/same-class? kb x y)))

(defn- equality-in?
  "Is `(equals x y)` a stored sentex visible from `ctx`?  This is the per-context
  question, and the one Pace's matrix is actually about."
  [kb x y ctx]
  (boolean (v/handle-of kb (list 'equals x y) ctx)))

(defn- clash-contexts
  "The set of contexts named by the sides of every recorded contradiction.

  `contradictions` entries carry `:sides [{:handle :sentence :context …} …]` — the
  context is on each **side**, not on the entry, which is worth stating because reading
  `:context` off the entry yields nil for every entry and a filter that is quietly
  always empty."
  [kb]
  (into #{} (mapcat #(map :context (:sides %))) (v/contradictions kb)))

(defn- any-contradiction?
  "Is there any recorded contradiction at all?"
  [kb]
  (boolean (seq (v/contradictions kb))))

(defn- violation-contexts
  "The set of contexts named `:visible-from` by every recorded `:functional`
  violation — the `violations`-ledger analogue of `clash-contexts`.

  An unmergeable clash a `genlCx` edge completes is **reported, not decided**: nothing
  was ever refused (both facts were already stored and believed before the edge made
  them jointly visible, so there was no write left to turn away) and nothing is
  arbitrated under the default `:refuse` constraint policy, so it never reaches
  `contradictions` — `settle/expose-constraint-clashes!` is the door it takes instead,
  and `docs/equality.md`'s own account of the arity-2 `functional` case takes the
  identical door for the identical reason.  Checking `contradictions` here would be
  the same mistake vaelii#43's own repro made checking it over `violations`."
  [kb]
  (into #{} (mapcat #(get-in % [:detail :visible-from]))
        (filter #(= :functional (:violation %)) (v/violations kb))))

(defn- any-functional-violation?
  "Is there any recorded `:functional` violation at all?"
  [kb]
  (boolean (some #(= :functional (:violation %)) (v/violations kb))))

(defn- ex-type
  "The `:type` of the ex-info a thunk throws, or nil.  A refusal that collapses into an
  arity or naming error is exactly the regression a bare `thrown?` stays green through."
  [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

;; ---- the regression half: arity 2 must not move -------------------------

(tu/deftest-kb functional-in-arg-2-on-a-binary-predicate-is-todays-functional
  ;; The generalization earns nothing if it changes what already works.  Same fixture as
  ;; the existing functional tests, spelled the new way.
  (tu/with-terms [parentOf Tom]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list 'functionalInArg parentOf 2) U)
      (v/assert kb (list parentOf Tom lo) U)
      (v/assert kb (list parentOf Tom hi) U)
      (is (merged? kb lo hi)
          "arg 1 determines arg 2, two symbol fillers, merged — as (functional parentOf)")))
  (testing "and the numeric side still refuses outright"
    (tu/with-terms [birthYearOf Tom]
      (v/assert kb (list 'functionalInArg birthYearOf 2) U)
      (v/assert kb (list birthYearOf Tom 1980) U)
      (is (some? (ex-type #(v/assert kb (list birthYearOf Tom 1990) U)))
          "no merge can make 1980 and 1990 one thing"))))

;; ---- Pace's matrix, rows 1 and 2 ----------------------------------------

;; vaelii#43 closed the gap: `special/equate-under-context-edge` (and the
;; `derive-functional-equalities` sweep it now shares with the plain fact-arrival
;; trigger) derives the merge from CxBottom, and `settle/could-clash?` /
;; `partner-contexts` / `constraint-facts-in-cone` — none of which had ever read the
;; `:functional-in-arg` table, only the arity-2 `:functional` one — now admit the
;; empty-determinant shape too, so `expose-constraint-clashes!` finds the unmergeable
;; pair.  That ledger, `v/violations`, is where an unmergeable cross-context clash
;; lands under the default `:refuse` policy — not `contradictions`, which the arity-2
;; `functional` case does not reach here either (docs/equality.md).  This row now
;; reads `violations`, not the door the original spec checked.
(tu/deftest-kb two-numbers-under-an-empty-determinant-contradict-in-the-context-below
  ;; Row 1.  `(p 1)` in CxLeft and `(p 2)` in CxRight are each fine where they stand;
  ;; CxBottom sees both and no merge can reconcile two numbers, so the clash is a
  ;; contradiction rather than knowledge.
  (tu/with-terms [p CxLeft CxRight CxBottom]
    (contexts! kb {:left CxLeft :right CxRight :bottoms [CxBottom]})
    (v/assert kb (list 'functionalInArg p 1) U)
    (v/assert kb (list p 1) CxLeft)
    (v/assert kb (list p 2) CxRight)
    (testing "the clash is reported, and it belongs to the vantage that sees it"
      (check (any-functional-violation? kb)
             "two numbers, one empty-determinant slot, nothing to merge")
      (check (= #{CxBottom} (violation-contexts kb))
             "CxBottom, not the leaves the fillers were asserted in"))
    (testing "and no equality is derived anywhere, numbers being unmergeable"
      (check (not (equality-in? kb 1 2 CxBottom)) "no (equals 1 2)"))))

(tu/deftest-kb a-clash-no-context-can-see-is-not-a-clash
  ;; Pace's rule, S174, and the converse of the row above — the half that makes it a
  ;; rule rather than a labelling choice:
  ;;
  ;;   "it's silly to compute {CxLeft CxRight} if they're both leaf contexts. Who cares
  ;;    whether there's an implicit contradiction if there's no context that sees that
  ;;    contradiction. that's just wasting compute."
  ;;
  ;; Same two facts as the row above, with **no context below either side**.  Neither
  ;; leaf can see the other, so no vantage exists from which the two fillers are both
  ;; present, and there is nothing to report.  A contradiction here would mean the engine
  ;; is computing clashes eagerly across mutually blind contexts.
  (tu/with-terms [p CxLeft CxRight]
    (doseq [c [CxLeft CxRight]]
      (v/assert kb (list 'genlCx c U) U))
    (v/assert kb (list 'functionalInArg p 1) U)
    (v/assert kb (list p 1) CxLeft)
    (v/assert kb (list p 2) CxRight)
    (check (not (any-contradiction? kb))
           "no context sees both fillers, so the clash does not exist to be had")
    (check (empty? (clash-contexts kb)) "and nothing is stamped with a vantage")))

;; vaelii#43 closed the gap.  The two facts arrive into a topology `contexts!` wires
;; before either one exists, so this is the *fact*-arrives-last shape rather than the
;; *edge*-arrives-last one — which needed `derive-functional-equalities` itself to
;; sweep every reader below a fact's own context (`tax/context-down`), not only
;; `equate-under-context-edge`'s own genlCx-triggered sweep.
(tu/deftest-kb two-symbols-under-an-empty-determinant-merge-in-the-context-below
  ;; Row 2, and the one Pace specified the answer for: the desired behaviour is
  ;; `(equals ThingOne ThingTwo)` in CxBottom.  This is where a functional clash is
  ;; *knowledge* — two names for one thing — rather than an error.
  (tu/with-terms [p ThingOne ThingTwo CxLeft CxRight CxBottom]
    (contexts! kb {:left CxLeft :right CxRight :bottoms [CxBottom]})
    (v/assert kb (list 'functionalInArg p 1) U)
    (v/assert kb (list p ThingOne) CxLeft)
    (v/assert kb (list p ThingTwo) CxRight)
    (testing "neither side alone concludes anything about the pair"
      ;; `merged?` reads the unscoped, whole-KB partition — true the moment ANY context
      ;; derives the equality, CxBottom included, so it cannot be the check for "this
      ;; particular vantage sees nothing" (docs/equality.md: identity is a fact about the
      ;; world once believed anywhere, and it is the *scoped* read — `same-class?` with a
      ;; context — that answers what a given reader is entitled to rely on).
      (is (not (v/same-class? kb ThingOne ThingTwo CxLeft))
          "CxLeft cannot see CxRight's filler")
      (is (not (v/same-class? kb ThingOne ThingTwo CxRight))
          "CxRight cannot see CxLeft's filler"))
    (testing "and the context below both derives the equality"
      (is (some? (v/handle-of kb (list 'equals ThingOne ThingTwo) CxBottom))
          "(equals ThingOne ThingTwo) in CxBottom, which is what was asked for")
      (is (not (any-contradiction? kb))
          "a merge is knowledge, not an error"))))

;; ---- row 3: the explicit different ---------------------------------------

;; DECIDED (vaelii#43 discussion -> #44): the row expects the dilemma.  The
;; cross-context clash exists (`(not (equals ThingOne ThingTwo))` and the functional
;; derivation do meet), and empirically, in both orderings, a `:default` denial does
;; not "deny exactly that" — it ties.  `derive-equality` always labels its own
;; justification `:monotonic`, but a derivation's effective class is the weakest of
;; its antecedents (docs/nmtms.md), and `(p ThingOne)` / `(p ThingTwo)` are asserted
;; `:default` too, so the derived equality caps at `:default` — the same class as the
;; negation.  Two `:default` claims at equal class do not pick a loser in this
;; engine; they are a represented dilemma, exactly `nixon-diamond-is-the-same-
;; dilemma-every-time`'s shape (order_independence_test.clj).
;;
;; Why dilemma-expectation over marking the denial `:monotonic` (the road not
;; taken, from the #43 finding): `:monotonic` defeats the derived equality without
;; unmaking it — its sentex stays stored in CxBottom, so the row's storage-checks
;; would still need replacing with belief-checks *and* the strength change, and the
;; row would then pin an arbitration rather than the thing it exists for.  What the
;; row is for is "the clash is not lost": both sides believed, neither defeated,
;; the pair reported exactly once, in both orders.  A represented dilemma in
;; `contradictions` is that claim — stronger than the old expectations, which only
;; said the negation wins and nothing about how the tie is reported.
(tu/deftest-kb an-asserted-difference-ties-the-merge-into-a-represented-dilemma
  ;; Row 3, and the row most likely to expose a real defect: two resolution paths meet
  ;; here.  The functional constraint wants to derive `(equals ThingOne ThingTwo)`; the
  ;; asserted `(not (equals ThingOne ThingTwo))` commits to distinctness at the same
  ;; `:default` class.  Whichever runs first must not decide the answer, so this is
  ;; asserted in both orders, and the reading must not vary between them.
  ;; NOTE: spelled `(not (equals …))`, not `(different …)`.  `different` is **not
  ;; assertible** — it is negation as failure over the equality closure, answered by a
  ;; prover and never stored (`wff.clj` `different-problems`, `docs/equality.md:83`), and
  ;; an assertible one would be OWL's `differentFrom`, which equality.md:540 declines on
  ;; purpose.  A stored negated equality is the only way to commit to distinctness here.
  (doseq [[label difference-first?] [["difference asserted first" true]
                                     ["difference asserted last" false]]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [p ThingOne ThingTwo CxLeft CxRight CxBottom]
        (contexts! kb {:left CxLeft :right CxRight :bottoms [CxBottom]})
        (v/assert kb (list 'functionalInArg p 1) U)
        (when difference-first?
          (v/assert kb (list 'not (list 'equals ThingOne ThingTwo)) U))
        (v/assert kb (list p ThingOne) CxLeft)
        (v/assert kb (list p ThingTwo) CxRight)
        (when-not difference-first?
          (v/assert kb (list 'not (list 'equals ThingOne ThingTwo)) U))
        (testing label
          (let [pos (v/handle-of kb (list 'equals ThingOne ThingTwo) CxBottom)
                neg (v/handle-of kb (list 'not (list 'equals ThingOne ThingTwo)) U)
                dilemmas (v/contradictions kb)]
            (is (true? (v/in? kb pos))
                "the derived equality remains believed — the merge is not undone")
            (is (merged? kb ThingOne ThingTwo)
                "and the believed equality still joins the two fillers")
            (is (true? (v/in? kb neg))
                "the asserted difference remains believed — neither side wins")
            (is (= [:default :default]
                   [(v/defeat-class kb pos) (v/defeat-class kb neg)])
                "neither side was defeated — the dilemma is represented, not decided")
            (is (= 1 (count dilemmas))
                "the pair is reported exactly once")
            (is (= #{pos neg} (:nogood (first dilemmas)))
                "the reported dilemma is this exact positive/negative pair")
            (is (= 'contradicts (first (:sentence (first dilemmas))))
                "and it is reported as a contradiction"))
          (is (zero? (count (v/conflicts kb)))
              "as a dilemma, not a conflict"))))))

;; ---- row 4: two bottoms, same verdict ------------------------------------

;; vaelii#43 closed the gap, and this row is what pins the fix has no favorite
;; reader: `equate-under-context-edge`'s candidate walk and `derive-functional-
;; equalities`' own `context-down` sweep both reach every reader below a marked
;; predicate's stored facts, not the first one asked.
(tu/deftest-kb both-contexts-below-reach-the-same-verdict
  ;; Row 4.  CxBottomOne and CxBottomTwo see exactly the same two facts and neither sees
  ;; the other.  A verdict that differs between them would mean the answer depends on
  ;; which descent ran first, or on state one left behind — which is the failure mode
  ;; the pair exists to catch, not a property anyone wants.
  (testing "the mergeable pair merges in both"
    (tu/with-terms [p ThingOne ThingTwo CxLeft CxRight CxBottomOne CxBottomTwo]
      (contexts! kb {:left CxLeft :right CxRight
                     :bottoms [CxBottomOne CxBottomTwo]})
      (v/assert kb (list 'functionalInArg p 1) U)
      (v/assert kb (list p ThingOne) CxLeft)
      (v/assert kb (list p ThingTwo) CxRight)
      (doseq [b [CxBottomOne CxBottomTwo]]
        (is (equality-in? kb ThingOne ThingTwo b)
            (str "equality derived in " b)))))
  (testing "and the unmergeable pair contradicts in both"
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [p CxLeft CxRight CxBottomOne CxBottomTwo]
        (contexts! kb {:left CxLeft :right CxRight
                       :bottoms [CxBottomOne CxBottomTwo]})
        (v/assert kb (list 'functionalInArg p 1) U)
        (v/assert kb (list p 1) CxLeft)
        (v/assert kb (list p 2) CxRight)
        ;; `violations`, not `contradictions` — see row 1's comment: an unmergeable
        ;; cross-context clash is reported through the exposure ledger under the
        ;; default `:refuse` policy, the same door the arity-2 `functional` case
        ;; already takes.
        (is (any-functional-violation? kb) "the unmergeable clash is reported")
        (doseq [b [CxBottomOne CxBottomTwo]]
          (is (not (equality-in? kb 1 2 b))
              (str "and no equality is manufactured in " b)))))))

;; ---- the motivating case -------------------------------------------------

(tu/deftest-kb a-composite-determinant-fixes-the-filesystem-constraint
  ;; The reason this exists.  `namesObject(namespace, path, object)` needs
  ;; `(namespace, path) → object`: same namespace and same path, one object.  Arity-2
  ;; `functional` cannot say it, because the determinant is two arguments wide.
  (tu/with-terms [namesObject NsA PathA ObjOne ObjTwo]
    (v/assert kb (list 'functionalInArg namesObject 3) U)
    (v/assert kb (list namesObject NsA PathA ObjOne) U)
    (v/assert kb (list namesObject NsA PathA ObjTwo) U)
    (is (merged? kb ObjOne ObjTwo)
        "one namespace and one path name one object, so the two names merge"))
  (testing "and a different path is a different slot, so nothing merges"
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [namesObject NsA PathA PathB ObjOne ObjTwo]
        (v/assert kb (list 'functionalInArg namesObject 3) U)
        (v/assert kb (list namesObject NsA PathA ObjOne) U)
        (v/assert kb (list namesObject NsA PathB ObjTwo) U)
        (is (not (merged? kb ObjOne ObjTwo))
            "the determinant differs, so these fill two slots and neither constrains the other")))))

;; ---- the wide case: Pace's 212 ------------------------------------------

(def ^:private wide-arity
  "212, at Pace's request.  Nothing in the suite goes above 7 and the metatype names stop
  at three, so this is the first argument count anything here has been asked to carry."
  212)

(defn- wide-sentence
  "`(P a1 … a211 tail)` — the shared 211-position determinant with `tail` at position 212."
  [pred prefix tail]
  (apply list pred (conj (vec prefix) tail)))

(tu/deftest-kb a-212-arity-predicate-is-expressible-and-checked
  ;; Above three there is no metatype to reach for — `checks.clj` is literally
  ;; `'{unaryPredicate 1 binaryPredicate 2 ternaryPredicate 3}` — so the `arity` table is
  ;; the only way to state this, and no ceiling exists anywhere in the wff validation.
  ;; The point is to find an unstated assumption about argument count if one is there,
  ;; not to model anything a KB would really say.
  (tu/with-terms [wideP]
    (let [args (vec (repeatedly wide-arity #(tu/tmp-ind "W")))
          s    (apply list wideP args)]
      (v/assert kb (list 'arity wideP wide-arity) U)
      (v/assert kb s U)
      (check (v/ask? kb s U) "a 212-argument sentence asserts and answers")
      (check (= wide-arity (count (rest s))) "and reads back at its stated width")
      (testing "a sentence of the wrong width is refused against the declared arity"
        (check (some? (ex-type #(v/assert kb (apply list wideP (pop args)) U)))
               "211 arguments where 212 were declared")))))

(tu/deftest-kb functional-in-arg-at-position-212
  ;; The motivating shape at scale.  `namesObject` has a two-position determinant; this
  ;; has a **211**-position one, which is where "every position except n" stops being
  ;; notional and starts being work.  Two sentences agreeing on all 211 and differing at
  ;; the 212th are one slot with two fillers.
  (tu/with-terms [wideP]
    (let [prefix  (vec (repeatedly (dec wide-arity) #(tu/tmp-ind "W")))
          [lo hi] (sort [(tu/tmp-ind "Filler") (tu/tmp-ind "Filler")])]
      (v/assert kb (list 'arity wideP wide-arity) U)
      (v/assert kb (list 'functionalInArg wideP wide-arity) U)
      (v/assert kb (wide-sentence wideP prefix lo) U)
      (v/assert kb (wide-sentence wideP prefix hi) U)
      (check (merged? kb lo hi)
             "211 positions agree, so position 212 is determined and the fillers merge")))
  (testing "and a determinant differing anywhere in those 211 is a different slot"
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [wideP]
        (let [prefix  (vec (repeatedly (dec wide-arity) #(tu/tmp-ind "W")))
              other   (assoc prefix 4 (tu/tmp-ind "Divergent"))
              [lo hi] (sort [(tu/tmp-ind "Filler") (tu/tmp-ind "Filler")])]
          (v/assert kb (list 'arity wideP wide-arity) U)
          (v/assert kb (list 'functionalInArg wideP wide-arity) U)
          (v/assert kb (wide-sentence wideP prefix lo) U)
          (v/assert kb (wide-sentence wideP other  hi) U)
          (check (not (merged? kb lo hi))
                 "one position out of 211 differs, so these fill two slots and neither binds the other"))))))

;; ---- declaration-last: the arrival order the settle sweep exists for ------

;; `equate-existing`'s docstring states order-independence as an invariant, and vaelii#43
;; found it holds for declaration-last and predicate-`genl`-edge-last while failing for
;; context-`genlCx`-edge-last.  Declaration-last is the order `functional` gets RIGHT,
;; and it gets it right through `settle`: `clash-declaration-functors` names the functors
;; whose arrival implicates content already stored, and the dispatch beside it sweeps the
;; marked predicate's subtree.
;;
;; `functionalInArg` was merged (#44) without reaching `settle.clj` at all, so it enforces
;; at assert and is invisible to that sweep — a generalization weaker than the special
;; case it generalizes, on the one axis the special case handles.  These two tests are
;; the receipt for that, and the control is not optional: without it a red pair proves
;; only that the fixture is wrong.

(tu/deftest-kb control-declaring-functional-after-the-facts-convicts
  ;; THE CONTROL.  Read this result first.  If this is red the fixture is broken and the
  ;; test below measures nothing — the S175 lesson about a probe whose own known-good
  ;; case never engaged the machinery it was aimed at.
  (tu/with-terms [parentOf Tom]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list parentOf Tom lo) U)
      (v/assert kb (list parentOf Tom hi) U)
      (v/assert kb (list 'functional parentOf) U)          ; declaration LAST
      (is (merged? kb lo hi)
          "today's functional convicts a pair already stored when the mark arrives"))))

(tu/deftest-kb declaring-functional-in-arg-after-the-facts-convicts
  ;; Same fixture, same arrival order, spelled the generalized way.  Must behave exactly
  ;; as the control does: the regression half of the generalization applies to arrival
  ;; order as much as to verdict.
  (tu/with-terms [parentOf Tom]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list parentOf Tom lo) U)
      (v/assert kb (list parentOf Tom hi) U)
      (v/assert kb (list 'functionalInArg parentOf 2) U)   ; declaration LAST
      (is (merged? kb lo hi)
          "(functionalInArg P 2) must convict retroactively exactly as (functional P) does"))))

(tu/deftest-kb control-declaring-functional-in-arg-before-the-facts-still-convicts
  ;; The already-passing order, restated here so a regression in the fix is visible
  ;; beside the thing it fixes rather than in another test's file.
  (tu/with-terms [parentOf Tom]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list 'functionalInArg parentOf 2) U)   ; declaration FIRST
      (v/assert kb (list parentOf Tom lo) U)
      (v/assert kb (list parentOf Tom hi) U)
      (is (merged? kb lo hi)
          "declaration-first was never broken and must stay unbroken"))))
