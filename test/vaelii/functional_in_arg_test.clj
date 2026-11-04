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
    does.  That is the regression half — the generalization is not allowed to move
    arity-2 behaviour.
  - `(functionalInArg P 1)` on a **unary** predicate has an *empty* determinant, which
    reads as \"at most one filler, full stop.\"  Every filler must reconcile with every
    other, so it is the sharpest available probe of the merge/reject rule and it is what
    the matrix below uses.

  The merge-or-nogood rule itself is not new and is not ours to invent.  CxUniverse's
  comment on `functional`:

      two symbols both known true (monotonic) derive (equals V1 V2) and merge, so
      retracting either fact or the declaration un-merges them. Any other collision is
      a nogood each context reading the pair decides

  and `mergeable-values?` (checks.clj) is the code half.  So the matrix below is one
  question asked five ways: *does the generalized determinant reach the same verdict the
  arity-2 path reaches, in every context that can see both fillers?*

  Context shape throughout:

      CxUniverse
        ├── CxLeft   (p ThingOne)
        ├── CxRight  (p ThingTwo)
        ├── CxBottom      sees CxLeft and CxRight
        ├── CxBottomOne   sees CxLeft and CxRight
        └── CxBottomTwo   sees CxLeft and CxRight

  Neither CxLeft nor CxRight sees the other, so each is individually consistent and the
  clash exists only from a context below both.  The two bottoms are not redundant: they
  assert that the verdict is a property of *what a context sees*, not of which context ran
  first or of state left behind by the first descent.

  The rows split by filler kind, since the two kinds take different lanes.  A pair of
  symbol fillers takes the *merge* lane: `special/equate-existing`, `equate-under-edge`
  and `equate-under-context-edge` when a declaration, a `genl` edge or a `genlCx` edge
  arrives last, and `derive-functional-equalities` when a fact arrives last, reading
  every context below the fact's own.  A pair no merge can reconcile takes the *clash*
  lane: `vaelii.impl.decide.tuple` places the nogood, and when the mark arrives last
  `special/offer-marked-existing` offers the stored tuples to `decide/offer!`.  The
  declaration-last blocks at the end of this file assert both lanes.

  Row 3 (`an-asserted-difference-leaves-two-default-fillers-a-represented-dilemma`)
  asserts a represented dilemma at `:default` strength — belief order-independent,
  contradiction reported once, exactly `nixon-diamond-is-the-same-dilemma-every-time`'s
  shape — because a represented dilemma is what \"the clash is not lost\" means."
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
  question, and the one the matrix is about."
  [kb x y ctx]
  (boolean (v/handle-of kb (list 'equals x y) ctx)))

(defn- clash-contexts
  "The set of contexts named by the sides of every recorded contradiction.

  `contradictions` entries carry `:sides [{:handle :sentence :context …} …]` — the
  context is on each **side**, not on the entry, which matters because reading
  `:context` off the entry yields nil for every entry and a filter that is quietly
  always empty."
  [kb]
  (into #{} (mapcat #(map :context (:sides %))) (v/contradictions kb)))

(defn- any-contradiction?
  "Is there any recorded contradiction at all?"
  [kb]
  (boolean (seq (v/contradictions kb))))

(defn- reading-contexts
  "Which of `ctxs` read a `:functional` dilemma — the reader arity of `contradictions`,
  which keeps an entry only for a context that sees every side and believes every
  member.

  An unmergeable clash a `genlCx` edge completes is **decided, not refused**: both facts
  were already stored and believed before the edge made them jointly visible, so there
  was no write left to turn away, and the vantage that sees them both weighs the pair
  under either constraint policy.  Two numbers cannot be ranked, so the answer is a
  dilemma and both fillers stand."
  [kb ctxs]
  (into #{} (filter #(some (comp #{:functional} :kind) (v/contradictions kb %))) ctxs))

(defn- any-functional-violation?
  "Is there any recorded `:functional` violation at all?"
  [kb]
  (boolean (some #(= :functional (:violation %)) (v/violations kb))))

(defn- any-functional-clash?
  "Is a `:functional` clash on record at all — decided into `contradictions` or
  `conflicts`, or filed as exposed?  A clash some vantage sees whole is decided under
  either constraint policy."
  [kb]
  (boolean (or (any-functional-violation? kb)
               (some #(= :functional (:kind %)) (concat (v/contradictions kb) (v/conflicts kb))))))

;; ---- the regression half: arity 2 must not move -------------------------

(tu/deftest-kb functional-in-arg-2-on-a-binary-predicate-is-todays-functional
  ;; The fixture of the `functional` tests, spelled with `functionalInArg`.
  (tu/with-terms [parentOf Tom]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list 'functionalInArg parentOf 2) U)
      (v/assert kb (list parentOf Tom lo) U {:strength :monotonic})
      (v/assert kb (list parentOf Tom hi) U {:strength :monotonic})
      (is (merged? kb lo hi)
          "arg 1 determines arg 2, two symbol fillers, merged — as (functional parentOf)")))
  (testing "and the numeric side is a clash, not a merge"
    (tu/with-terms [birthYearOf Tom]
      (v/assert kb (list 'functionalInArg birthYearOf 2) U)
      (v/assert kb (list birthYearOf Tom 1980) U)
      (is (tu/stored-in-clash? kb (list birthYearOf Tom 1990) U)
          "no merge can make 1980 and 1990 one thing"))))

;; The third arrival order of the same three ingredients, and the one the arity-2
;; regression above does not reach: the declaration and the facts are both stored, and
;; the `genl` edge that puts the facts under the mark arrives LAST
;; (`special/equate-under-edge`).
;;
;; The entry point's body asks `derive-functional-equalities`, which reads both
;; spellings, and its presence check is `tax/functional-family-declared?`, read by every
;; entry point of the family.  A presence check reading `props :functional` alone would
;; take the "declares nothing functional" exit for a KB whose only mark is
;; `(functionalInArg P n)`, and merge nothing.
;; **Two tests and not one parameterized over the spelling**: the presence check under
;; test is *global* (does the taxonomy hold any functional-family mark at all), so two
;; arms sharing one KB cannot tell the spellings apart.  The control arm's
;; `(functional …)` makes the presence check answer true, and the generalized arm then
;; passes whether or not its own spelling is read.  `:each` gives each `deftest` its own
;; fresh KB, so the isolation has to be at that grain.
(defn- merges-when-the-edge-arrives-last?
  "Assert `decl` on a super-predicate and two fillers on a sub-predicate, then the `genl`
  edge between them LAST.  True iff the fillers ended up merged.  Checks along the way
  that nothing merged *before* the edge, so a true answer is the edge's doing."
  [kb decl]
  (tu/with-terms [parentOf fatherOf Tom]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      ;; the mark on the super-predicate, and the facts on the sub — with no edge
      ;; between them yet, so nothing is under the mark and nothing may merge
      (v/assert kb (decl parentOf) U)
      (v/assert kb (list fatherOf Tom lo) U {:strength :monotonic})
      (v/assert kb (list fatherOf Tom hi) U {:strength :monotonic})
      (check (not (merged? kb lo hi))
             "no edge yet, so the fillers are not under the mark")
      ;; ...and the edge last, which is what puts them there
      (v/assert kb (list 'genl fatherOf parentOf) U)
      (merged? kb lo hi))))

(tu/deftest-kb a-genl-edge-arriving-last-merges-under-functional
  ;; the control: the arity-2 spelling
  (check (merges-when-the-edge-arrives-last? kb #(list 'functional %))
         "(functional P): the edge arriving last reaches the facts already stored"))

(tu/deftest-kb a-genl-edge-arriving-last-merges-under-functional-in-arg
  ;; the regression, in its own KB so the presence check answers false to begin with
  (check (merges-when-the-edge-arrives-last? kb #(list 'functionalInArg % 2))
         "(functionalInArg P 2): the same, or the generalization moved arity-2 behaviour"))

;; ---- the mark's other position on a binary predicate --------------------

;; `(functionalInArg P n)` names the **constrained** slot; the rest of the tuple is its
;; determinant.  On a binary predicate that gives two readings, not one: position 2 is
;; `functional` — argument 1 determines argument 2 — and position 1 is its mirror,
;; argument 2 determining argument 1.  `checks/functional-clashes` convicts both
;; (`nm/args` opened at `n`, never assumed binary), and the clash lane decides a
;; position-1 pair split across two contexts at the reader that sees both halves, as it
;; decides a position-2 pair.
(tu/deftest-kb both-positions-of-a-binary-mark-are-enforced-in-one-context
  (doseq [[n facts label]
          [[2 '[(PTom PMaryA) (PTom PMaryB)] "position 2, determinant in argument 1"]
           [1 '[(PMaryA PTom) (PMaryB PTom)] "position 1, determinant in argument 2"]]]
    (testing label
      (tu/with-terms [pRel]
        (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])
              Tom     (tu/tmp-ind "Tom")
              subst   {'PTom Tom 'PMaryA lo 'PMaryB hi}]
          (v/assert kb (list 'functionalInArg pRel n) U)
          (doseq [f facts] (v/assert kb (cons pRel (map subst f)) U {:strength :monotonic}))
          (check (merged? kb lo hi)
                 (str label ": the determinant is shared, so the fillers are one")))))))

(tu/deftest-kb a-position-1-clash-across-contexts-is-decided-like-a-position-2-one
  ;; Two unmergeable fillers, each fine where it stands, clashing only from below.  The
  ;; position-2 twin of this is `two-numbers-under-an-empty-determinant-contradict…`
  ;; below; this is the same question with the determinant on the other side.
  (tu/with-terms [pRel CxLeft CxRight CxBottom]
    (contexts! kb {:left CxLeft :right CxRight :bottoms [CxBottom]})
    (let [Tom (tu/tmp-ind "Tom")]
      (v/assert kb (list 'functionalInArg pRel 1) U)
      (v/assert kb (list pRel 1 Tom) CxLeft)
      (v/assert kb (list pRel 2 Tom) CxRight)
      (check (any-functional-clash? kb)
             "argument 2 is the determinant and shared, and no merge makes 1 and 2 one")
      (check (= #{CxBottom} (reading-contexts kb [CxLeft CxRight CxBottom]))
             "decided at the vantage that sees both, as a position-2 pair is"))))

;; ---- the matrix, rows 1 and 2 -------------------------------------------

;; Two numbers in two sibling contexts take the clash lane: no merge reconciles them, so
;; the pair is decided at CxBottom, the context that sees both.  Two numbers cannot be
;; ranked, so the vantage below reports a dilemma and both fillers stand: the row reads
;; `contradictions` from that vantage, which is the question the matrix asks.
(tu/deftest-kb two-numbers-under-an-empty-determinant-contradict-in-the-context-below
  ;; Row 1.  `(p 1)` in CxLeft and `(p 2)` in CxRight are each fine where they stand;
  ;; CxBottom sees both and no merge can reconcile two numbers, so the clash is a
  ;; contradiction rather than knowledge.
  (tu/with-terms [p CxLeft CxRight CxBottom]
    (contexts! kb {:left CxLeft :right CxRight :bottoms [CxBottom]})
    (v/assert kb (list 'functionalInArg p 1) U)
    (v/assert kb (list p 1) CxLeft)
    (v/assert kb (list p 2) CxRight)
    (testing "the clash is decided, and it belongs to the vantage that sees it"
      (check (any-functional-clash? kb)
             "two numbers, one empty-determinant slot, nothing to merge")
      (check (= #{CxBottom} (reading-contexts kb [CxLeft CxRight CxBottom]))
             "CxBottom, not the leaves the fillers were asserted in"))
    (testing "and no equality is derived anywhere, numbers being unmergeable"
      (check (not (equality-in? kb 1 2 CxBottom)) "no (equals 1 2)"))))

(tu/deftest-kb a-clash-no-context-can-see-is-not-a-clash
  ;; The converse of the row above, and the half that makes it a rule rather than a
  ;; labelling choice: a clash between two leaf contexts that no context sees together
  ;; is not computed.
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
    (check (empty? (clash-contexts kb)) "and nothing is tagged with a vantage")))

;; The two facts arrive into a topology `contexts!` wires before either one exists, so
;; this is the *fact*-arrives-last shape rather than the *edge*-arrives-last one:
;; `derive-functional-equalities` reaches CxBottom by sweeping every reader below the
;; fact's own context (`tax/context-down`), with no `genlCx` edge arriving.
(tu/deftest-kb two-symbols-under-an-empty-determinant-merge-in-the-context-below
  ;; Row 2: the desired behaviour is
  ;; `(equals ThingOne ThingTwo)` in CxBottom.  This is where a functional clash is
  ;; *knowledge* — two names for one thing — rather than an error.
  (tu/with-terms [p ThingOne ThingTwo CxLeft CxRight CxBottom]
    (contexts! kb {:left CxLeft :right CxRight :bottoms [CxBottom]})
    (v/assert kb (list 'functionalInArg p 1) U)
    (v/assert kb (list p ThingOne) CxLeft {:strength :monotonic})
    (v/assert kb (list p ThingTwo) CxRight {:strength :monotonic})
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

;; The row expects a dilemma.  `(p ThingOne)` and `(p ThingTwo)` are asserted `:default`,
;; and a merge needs every member `:monotonic` (docs/reference.md, decision 6), so no
;; equality is derived: the two fillers are a `functionalInArg` nogood at CxBottom, and
;; two `:default` members tied at the weakest class are a represented dilemma, the shape
;; of `nixon-diamond-is-the-same-dilemma-every-time` (order_independence_test.clj).  The
;; asserted `(not (equals ThingOne ThingTwo))` is a denial of a forced-monotonic literal, and no
;; equality stands beside it, so it is believed.
;; The row asserts that the clash is not lost: both fillers believed, neither
;; defeated, the pair reported exactly once, in both orders.
(tu/deftest-kb an-asserted-difference-leaves-two-default-fillers-a-represented-dilemma
  ;; Row 3.  Two paths meet here: the functional constraint over two `:default` symbol
  ;; fillers, and the asserted `(not (equals ThingOne ThingTwo))`.  Whichever runs first
  ;; must not decide the answer, so this is asserted in both orders, and the reading
  ;; must not vary between them.
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
        (let [one (v/assert kb (list p ThingOne) CxLeft)
              two (v/assert kb (list p ThingTwo) CxRight)]
          (when-not difference-first?
            (v/assert kb (list 'not (list 'equals ThingOne ThingTwo)) U))
          (testing label
            (let [pos (v/handle-of kb (list 'equals ThingOne ThingTwo) CxBottom)
                  neg (v/handle-of kb (list 'not (list 'equals ThingOne ThingTwo)) U)
                  dilemmas (v/contradictions kb)]
              (is (nil? pos)
                  "no equality is derived from two :default fillers")
              (is (not (merged? kb ThingOne ThingTwo))
                  "so the two fillers stay apart")
              (is (true? (v/in? kb neg))
                  "the asserted difference is believed: no equality stands beside it")
              (is (= [:default :default]
                     [(v/defeat-class kb one) (v/defeat-class kb two)])
                  "neither filler was defeated — the dilemma is represented, not decided")
              (is (= 1 (count dilemmas))
                  "the pair is reported exactly once")
              (is (= #{one two} (:nogood (first dilemmas)))
                  "the reported dilemma is this exact pair of fillers")
              (is (= 'contradicts (first (:sentence (first dilemmas))))
                  "and it is reported as a contradiction"))
            (is (zero? (count (v/conflicts kb)))
                "as a dilemma, not a conflict")))))))

;; ---- the pair placed, and a reader that merges its fillers ------------------

(tu/deftest-kb a-functional-pair-is-placed-and-a-reader-merging-its-fillers-reads-no-defeat
  ;;   CxUniverse  (functional p)
  ;;     ├─ CxLeft    (p Tom ThingOne) default
  ;;     ├─ CxRight   (p Tom ThingTwo) monotonic
  ;;     └─ CxBottom  sees both
  ;;          └─ CxMerge  (sameAs ThingOne ThingTwo)
  ;; The pair is placed at CxBottom with the default filler's defeat; CxMerge reads the
  ;; two fillers as one class, so it reads no nogood and believes both.
  (tu/with-terms [p Tom ThingOne ThingTwo CxLeft CxRight CxBottom CxMerge]
    (contexts! kb {:left CxLeft :right CxRight :bottoms [CxBottom]})
    (v/assert kb (list 'genlCx CxMerge CxBottom) U)
    (let [mark (v/assert kb (list 'functional p) U {:strength :monotonic})
          los  (v/assert kb (list p Tom ThingOne) CxLeft)
          win  (v/assert kb (list p Tom ThingTwo) CxRight {:strength :monotonic})
          L    [(list p Tom ThingOne) CxLeft]
          W    [(list p Tom ThingTwo) CxRight]
          at   (fn [ctx] (into #{} (comp (filter #(= ctx (:context %)))
                                         (map #(tu/handle-free kb [(:sentence %) (:context %)])))
                               (concat (v/sentexes-with-functor kb 'contradicts)
                                       (v/sentexes-with-functor kb 'defeat))))]
      (testing "the contradicts and the defeat are stored at CxBottom, the mark a ground"
        (is (= #{[(list 'contradicts L W) CxBottom] [(list 'defeat L) CxBottom]} (at CxBottom)))
        (let [[c] (filter #(= CxBottom (:context %)) (v/sentexes-with-functor kb 'contradicts))]
          (is (every? (set (mapcat :antecedents (v/supporting-justifications kb (:id c))))
                      [los win mark]))))
      (testing "no reader decides the pair"
        (check (false? (v/believed? kb los CxBottom)) "CxBottom does not believe the default filler"))
      (testing "a reader below that merges the fillers reads no defeat"
        (v/assert kb (list 'sameAs ThingOne ThingTwo) CxMerge {:strength :monotonic})
        (check (true? (v/believed? kb los CxMerge)) "CxMerge believes the default filler")
        (check (false? (v/believed? kb los CxBottom)) "and CxBottom still does not")))))

;; ---- row 4: two bottoms, same verdict ------------------------------------

;; This row asserts that the merge lane favours no reader: `equate-under-context-edge`'s
;; candidate walk and `derive-functional-equalities`' own `context-down` sweep both
;; reach every reader below a marked predicate's stored facts, not the first one asked.
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
      (v/assert kb (list p ThingOne) CxLeft {:strength :monotonic})
      (v/assert kb (list p ThingTwo) CxRight {:strength :monotonic})
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
        ;; see row 1's comment: an unmergeable cross-context clash is weighed at the
        ;; vantage under either policy, and two numbers tie, so it lands in
        ;; `contradictions` with both fillers standing.
        (is (any-functional-clash? kb) "the unmergeable clash is decided")
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
    (v/assert kb (list namesObject NsA PathA ObjOne) U {:strength :monotonic})
    (v/assert kb (list namesObject NsA PathA ObjTwo) U {:strength :monotonic})
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

;; ---- the wide case: arity 212 ------------------------------------------

(def ^:private wide-arity
  "212.  Nothing else in the suite goes above 7 and the metatype names stop
  at three, so this is the first argument count anything here has been asked to carry."
  212)

(defn- wide-sentence
  "`(P a1 … a211 tail)` — the shared 211-position determinant with `tail` at position 212."
  [pred prefix tail]
  (apply list pred (conj (vec prefix) tail)))

(tu/deftest-kb a-212-arity-predicate-is-expressible-and-checked
  ;; Above three there is no metatype to reach for — `checks.clj` is literally
  ;; `'{unary_predicate 1 binary_predicate 2 ternary_predicate 3}` — so the `arity` table is
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
      (testing "a sentence of the wrong width is read OUT against the declared arity"
        (check (tu/stored-in-clash? kb (apply list wideP (pop args)) U)
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
      (v/assert kb (wide-sentence wideP prefix lo) U {:strength :monotonic})
      (v/assert kb (wide-sentence wideP prefix hi) U {:strength :monotonic})
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

;; These rows put the declaration LAST, after the facts it convicts.
;; `special/equate-existing` sweeps the marked predicate's spec subtree when a
;; `functional` or `functionalInArg` declaration arrives.  The control is not optional:
;; without it a red pair proves only that the fixture is wrong.

(tu/deftest-kb control-declaring-functional-after-the-facts-convicts
  ;; THE CONTROL.  Read this result first.  If this is red the fixture is broken and the
  ;; test below measures nothing.
  (tu/with-terms [parentOf Tom]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list parentOf Tom lo) U {:strength :monotonic})
      (v/assert kb (list parentOf Tom hi) U {:strength :monotonic})
      (v/assert kb (list 'functional parentOf) U)          ; declaration LAST
      (is (merged? kb lo hi)
          "functional convicts a pair already stored when the mark arrives"))))

(tu/deftest-kb declaring-functional-in-arg-after-the-facts-convicts
  ;; Same fixture, same arrival order, spelled the generalized way.  Must behave exactly
  ;; as the control does: the regression half of the generalization applies to arrival
  ;; order as much as to verdict.
  (tu/with-terms [parentOf Tom]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list parentOf Tom lo) U {:strength :monotonic})
      (v/assert kb (list parentOf Tom hi) U {:strength :monotonic})
      (v/assert kb (list 'functionalInArg parentOf 2) U)   ; declaration LAST
      (is (merged? kb lo hi)
          "(functionalInArg P 2) must convict retroactively exactly as (functional P) does"))))

(tu/deftest-kb control-declaring-functional-in-arg-before-the-facts-still-convicts
  ;; The declaration-first order, beside the declaration-last rows so a regression in
  ;; either order shows in this file.
  (tu/with-terms [parentOf Tom]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list 'functionalInArg parentOf 2) U)   ; declaration FIRST
      (v/assert kb (list parentOf Tom lo) U {:strength :monotonic})
      (v/assert kb (list parentOf Tom hi) U {:strength :monotonic})
      (is (merged? kb lo hi)
          "declaration first convicts as declaration last does"))))

;; ---- declaration-last over an UNMERGEABLE pair ---------------------------

;; The declaration-last rows above test the *merge* lane: two symbol fillers, reconciled
;; by `special/equate-existing`.  The other half of the same arrival order is the pair no
;; merge can reconcile, and it takes the clash lane: `special/offer-marked-existing`
;; offers the stored tuples beneath the marked predicate to `decide/offer!`, for
;; `(functional P)` and `(functionalInArg P n)` alike.  The control is not optional, for
;; the reason the merge rows give.

(tu/deftest-kb control-functional-declared-after-unmergeable-facts-is-reported
  ;; THE CONTROL for the two rows below.  Read this result first.
  (tu/with-terms [birthYearOf Tom]
    (v/assert kb (list birthYearOf Tom 1980) U)
    (v/assert kb (list birthYearOf Tom 1990) U)
    (v/assert kb (list 'functional birthYearOf) U)       ; declaration LAST
    (check (any-functional-clash? kb)
           "functional accounts for a pair already stored when the mark arrives")))

(tu/deftest-kb functional-in-arg-2-declared-after-unmergeable-facts-is-reported
  ;; The regression half of the generalization, applied to the clash lane: at arity 2
  ;; this is `(functional P)` spelled with `functionalInArg` and must behave identically.
  (tu/with-terms [birthYearOf Tom]
    (v/assert kb (list birthYearOf Tom 1980) U)
    (v/assert kb (list birthYearOf Tom 1990) U)
    (v/assert kb (list 'functionalInArg birthYearOf 2) U) ; declaration LAST
    (check (any-functional-clash? kb)
           "(functionalInArg P 2) must account for the pair retroactively exactly as (functional P) does")))

(tu/deftest-kb functional-in-arg-3-declared-after-unmergeable-facts-is-reported
  ;; The shape the mark exists for, in the arrival order the special case handles: a
  ;; composite determinant whose declaration lands after the tuples it convicts.
  (tu/with-terms [namesObject NsA PathA]
    (v/assert kb (list namesObject NsA PathA 1) U)
    (v/assert kb (list namesObject NsA PathA 2) U)
    (v/assert kb (list 'functionalInArg namesObject 3) U) ; declaration LAST
    (check (any-functional-clash? kb)
           "one namespace and one path cannot name two numbers, whenever the mark arrives")))

(tu/deftest-kb a-genl-edge-arriving-last-carries-the-generalized-mark-down
  ;; The third arrival order for the clash lane, and the one that proves the reach is
  ;; read down the hierarchy rather than off the exact functor: the mark and the facts
  ;; are both already stored, and it is the `genl` edge between their predicates that
  ;; puts the pair under it.
  (tu/with-terms [parentOf fatherOf Tom]
    (v/assert kb (list 'functionalInArg parentOf 2) U)
    (v/assert kb (list fatherOf Tom 1980) U)
    (v/assert kb (list fatherOf Tom 1990) U)
    (v/assert kb (list 'genl fatherOf parentOf) U)        ; edge LAST
    (check (any-functional-clash? kb)
           "the mark descends to fatherOf when the edge lands, and the stored pair is decided")))

(tu/deftest-kb a-malformed-generalized-declaration-triggers-no-sweep
  ;; The trigger check reads the position as well as the predicate.  A declaration whose
  ;; second argument is not an integer names no slot, and must not reach the sweep as
  ;; though it did — nor take the assert down on the way.
  (tu/with-terms [parentOf Tom Mary]
    (v/assert kb (list parentOf Tom Mary) U)
    (check (some? (tu/refusal-type #(v/assert kb (list 'functionalInArg parentOf 'Two) U)))
           "a non-integer position is refused outright")
    (check (not (any-functional-violation? kb))
           "and nothing is swept on its behalf")))

(tu/deftest-kb a-middle-position-pair-across-two-contexts-is-decided-at-the-joint-reader
  ;; `(functionalInArg P 2)` on a ternary: the determinant is arguments 1 and 3, a pair
  ;; split across two contexts, and the reader that sees both takes the default OUT.
  (tu/with-terms [scoreOf Team Match CxL CxR CxJ]
    (doseq [[c up] [[CxL U] [CxR U] [CxJ CxL] [CxJ CxR]]]
      (v/assert kb (list 'genlCx c up) U))
    (v/assert kb (list 'functionalInArg scoreOf 2) U)
    (let [low  (v/assert kb (list scoreOf Team 1 Match) CxL)
          high (v/assert kb (list scoreOf Team 2 Match) CxR {:strength :monotonic})]
      (check (v/believed? kb low CxL) "each context believes its own tuple")
      (check (and (not (v/believed? kb low CxJ)) (v/believed? kb high CxJ))
             "and the reader seeing both takes the default OUT"))))
