;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.solve-test
  "The soft-contradiction `Solver` protocol: `Program`, `content-key`, and the shipped
  `local-solver` stub (`vaelii.impl.solve`).

  Two separate things are at stake here.

  **The split between what a solver may decide and what it may not.**  A `Program`
  carries `:assumptions` — contested `:default` nodes — and `:fixed`, the known-true
  background a solve reasons *from*.  A solver that could withdraw the fixed side
  would be deciding the premises rather than the edges (docs/nmtms.md).  `program`
  is where that split is drawn, and `local-solver` is where it must be respected:
  only a contested member is ever defeated.

  **Order independence.**  Handles are allocated in assertion order, so a tie broken
  on handle id would make the Nixon diamond elect whichever side was typed first —
  the engine-wide invariant in docs/nmtms.md, and the reason `content-key` exists.
  The tests below re-run the same claims under swapped handle numbering and demand
  the same *claim* lose both times, and re-run the same nogoods in a different input
  order and demand the identical result.

  Almost everything here is **pure** — hand-built `Program` values, no store, no
  fixture — in the style of `strength_test` and `jtms_blocked_test`.  That is not a
  convenience: `core/decide-nogood` routes no plain default/default rebuttal to any
  solver (a rebuttal is a represented dilemma, see `nmtms_test`), so the
  `:contested` branch of `resolve-contradictions` is currently unreachable and the
  stub cannot be driven end to end at all.  Testing it as a unit is the only way it
  gets covered, and it is the level the contract lives at anyway: `set-solver` takes
  any implementation, and this is the behaviour that implementation is replacing.

  The last section is the one part that needs a KB — that `local-solver` really is
  the solver a fresh KB ships with, and that `set-solver` swaps it."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.solve :as solve]
            [vaelii.impl.types.solve :as solve-types]
            [vaelii.test-util :as tu]))

;; ---- builders ------------------------------------------------------------
;;
;; Sentences are `(a)`, `(b)`, … so the content ordering is legible: `content-key`
;; is `(pr-str [sentence context handle])`, hence "[(a) C 1]" < "[(b) C 2]" on the
;; sentence alone.  Every expectation below is stated in terms of that, never in
;; terms of which handle happens to carry it.

(defn- content
  "Handle → what it asserts, from `handle sentence` pairs, all in one context."
  [& pairs]
  (into {} (map (fn [[h s]] [h {:sentence s :context 'C}])) (partition 2 pairs)))

(defn- ng
  "A nogood map in the shape `core/negation-nogoods` produces."
  [priority & handles]
  {:nogood (set handles) :priority priority :sentence (list 'contradicts handles)})

(defn- decide [program] (solve-types/solve solve/local-solver program))

(defn- claims
  "What `handles` assert, per `content` — so an assertion names the *claim* that
  lost rather than the handle, which is the whole point of the content keying."
  [content handles]
  (into #{} (map #(get-in content [% :sentence])) handles))

;; ---- 1. Program: the split between decidable and fixed -------------------

(deftest program-splits-contested-assumptions-from-fixed-background
  ;; The one structural guarantee the `Solver` protocol rests on.  A member of a nogood
  ;; that is not contested is known-true background: it belongs in `:fixed`, never in
  ;; `:assumptions`, and its content must not be handed over either — `content-key`
  ;; is a tie-break among things that may lose, and nothing fixed may lose.
  (let [c (content 1 '(a) 2 '(b) 9 '(z))
        p (solve/program #{1 2} [(ng 0 1 2) (ng 0 2 9)] c)]
    (testing "only the contested handles are assumptions"
      (is (= #{1 2} (:assumptions p))))
    (testing "the uncontested member of a relevant nogood is fixed background"
      (is (= #{9} (:fixed p))))
    (testing "and the fixed handle's content is withheld — it is not up for decision"
      (is (= #{1 2} (set (keys (:content p)))))
      (is (nil? (get-in p [:content 9]))))
    (testing "both nogoods are relevant: each touches a contested handle"
      (is (= 2 (count (:contradictions p)))))))

(deftest program-drops-a-nogood-with-no-contested-member
  ;; A clash between two known-true datums is *irreducible* — `settle` classifies it
  ;; as hard and reports it through `conflicts`.  Handing it to a solver would be
  ;; asking which premise to give up, so `program` filters it out before it can be
  ;; asked, and its members do not become fixed background either (nothing in the
  ;; program refers to them).
  (let [p (solve/program #{1} [(ng 0 1 2) (ng 5 7 8)] (content 1 '(a) 2 '(b) 7 '(c) 8 '(d)))]
    (is (= [#{1 2}] (mapv :nogood (:contradictions p))))
    (is (= #{2} (:fixed p)) "7 and 8 are not background to anything the solver sees")))

(deftest an-empty-program-decides-nothing
  ;; Nothing contested, nothing to satisfy.  `settle` short-circuits before building
  ;; this, but the protocol has to be total: a solver is a plug-in and may be handed one.
  (let [p (solve/program #{} [] {})]
    (is (= #{} (:assumptions p)))
    (is (= #{} (:fixed p)))
    (is (= [] (:contradictions p)))
    (is (= {} (:content p)))
    (is (= {:defeat #{} :violated []} (decide p)))))

(deftest a-neg-nogood-is-an-at-least-one
  ;; `:neg` members are forbidden to be *absent* together.  With every member still
  ;; believed the requirement holds — nothing to defeat, nothing violated; only a
  ;; nogood whose `:neg` members are all defeated is violated, and defeating more
  ;; cannot restore presence.
  (let [c (content 1 '(a) 2 '(b))]
    (testing "a satisfied at-least-one is skipped, not violated"
      (let [p (solve/program #{1 2}
                             [{:neg #{1 2} :priority 0 :sentence '(atleastone)}]
                             c)]
        (is (= {:defeat #{} :violated []} (decide p)))))
    (testing "a fixed member satisfies it permanently"
      (let [p (solve/program #{1}
                             [{:neg #{1 2} :priority 0 :sentence '(atleastone)}]
                             c)]
        (is (= #{2} (:fixed p)) "handle 2 is background, assumed true")
        (is (= {:defeat #{} :violated []} (decide p)))))
    (testing "a mixed nogood defeats its positive member, never reads :neg as positive"
      ;; forbidden: (a) held while (b) absent — satisfied by defeating (a)... but (b)
      ;; is believed, so the body never holds and nothing needs deciding
      (let [p (solve/program #{1 2}
                             [{:nogood #{1} :neg #{2} :priority 0 :sentence '(implic)}]
                             c)]
        (is (= {:defeat #{} :violated []} (decide p)))))))

;; ---- 2. content-key: the order-independence primitive --------------------

(deftest content-key-orders-on-the-claim-not-on-the-handle
  ;; The bug this exists to prevent, stated directly: the same two claims under
  ;; swapped handle numbering must sort the same way.  Keying on the handle — or
  ;; putting the handle first in the vector — reverses the second comparison.
  (let [p1 (solve/program #{1 2} [] (content 1 '(a) 2 '(b)))
        p2 (solve/program #{1 2} [] (content 1 '(b) 2 '(a)))
        key1 #(solve/content-key p1 %)
        key2 #(solve/content-key p2 %)]
    (testing "in p1 the claim (a) sits on handle 1 and sorts first"
      (is (neg? (compare (key1 1) (key1 2)))))
    (testing "in p2 it sits on handle 2 and still sorts first"
      (is (neg? (compare (key2 2) (key2 1)))))
    (testing "because the claim leads the key and the handle only trails it"
      (is (str/starts-with? (key1 1) "[(a) C "))
      (is (str/starts-with? (key2 2) "[(a) C "))
      (is (not= (key1 1) (key2 2))
          "the two keys do differ — in the trailing handle, which is why it must be last"))))

(deftest content-key-separates-the-same-sentence-in-different-contexts
  ;; A sentex is a sentence *plus* a context, so two contexts asserting the same
  ;; sentence are two different claims and must key differently.  Dropping the
  ;; context from the vector would collapse them and push the choice onto the
  ;; handle fallback — order dependence by the back entry point.
  (let [p (solve/program #{1 2} []
                         {1 {:sentence '(a) :context 'C}
                          2 {:sentence '(a) :context 'D}})]
    (is (not= (solve/content-key p 1) (solve/content-key p 2)))))

(deftest content-key-falls-back-to-the-handle-only-for-identical-content
  ;; The documented last resort.  Two entries with the same sentence and context
  ;; cannot be told apart by content, and a key that collided there would make
  ;; `(last (sort-by content-key ...))` pick unpredictably among equals.  The handle
  ;; is the tiebreak of last resort precisely because it is total.
  (let [p (solve/program #{1 2} [] (content 1 '(a) 2 '(a)))]
    (is (not= (solve/content-key p 1) (solve/content-key p 2)))
    (is (neg? (compare (solve/content-key p 1) (solve/content-key p 2))))))

(deftest content-key-is-total-over-handles-the-program-has-no-content-for
  ;; A fixed member appears in a nogood but carries no content (see
  ;; `program-splits-...` above), and the nogood *ordering* key maps over every
  ;; member.  So `content-key` must answer for a handle it knows nothing about
  ;; rather than blow up mid-solve.
  (let [p (solve/program #{1} [(ng 0 1 9)] (content 1 '(a) 9 '(z)))]
    (is (string? (solve/content-key p 9)))
    (is (not= (solve/content-key p 9) (solve/content-key p 8))
        "distinct unknown handles still get distinct keys")))

;; ---- 3. local-solver: the decision ---------------------------------------

(deftest a-two-way-tie-defeats-exactly-one-side
  (let [c (content 1 '(a) 2 '(b))
        r (decide (solve/program #{1 2} [(ng 0 1 2)] c))]
    (testing "one of the two contested defaults gives way, not both and not neither"
      (is (= 1 (count (:defeat r)))))
    (testing "and it is the greatest content-key — the claim (b)"
      (is (= #{'(b)} (claims c (:defeat r)))))
    (testing "with nothing left unsatisfiable"
      (is (= [] (:violated r))))))

(deftest the-same-claim-loses-under-any-handle-numbering
  ;; The headline invariant.  Same two claims, handles swapped: a handle-keyed
  ;; tie-break elects a different *sentence* the second time, which in a KB means the
  ;; Nixon diamond resolving according to typing order.  Comparing the defeated
  ;; sentence rather than the defeated handle is what makes that visible.
  (let [c1 (content 1 '(a) 2 '(b))
        c2 (content 1 '(b) 2 '(a))
        r1 (decide (solve/program #{1 2} [(ng 0 1 2)] c1))
        r2 (decide (solve/program #{1 2} [(ng 0 1 2)] c2))]
    (is (= 1 (count (:defeat r1))))
    (is (= 1 (count (:defeat r2))))
    (testing "the same claim loses both times"
      (is (= (claims c1 (:defeat r1)) (claims c2 (:defeat r2)))))
    (testing "though a different handle carries it — otherwise the test proves nothing"
      (is (not= (:defeat r1) (:defeat r2))))))

(deftest the-result-does-not-depend-on-the-order-the-nogoods-arrive-in
  ;; `:contradictions` is a vector built by walking the KB, and an earlier choice
  ;; constrains every later one, so walking it as given would make the outcome depend
  ;; on iteration order.  The sort is what removes that; deleting it passes every
  ;; single-nogood test above and fails this one.
  (let [c  (content 1 '(a) 2 '(b) 3 '(c))
        as (decide (solve/program #{1 2 3} [(ng 0 1 2) (ng 0 2 3)] c))
        bs (decide (solve/program #{1 2 3} [(ng 0 2 3) (ng 0 1 2)] c))]
    (is (= as bs))
    (is (seq (:defeat as)) "and it actually decided something")))

;; ---- 4. what may be defeated ---------------------------------------------

(deftest only-a-contested-member-is-ever-defeated
  ;; The fixed side is known-true.  Dropping the `(filter assumptions ...)` would let
  ;; the stub defeat it — `settle/accepted-defeat` clamps the *output* of a third-party
  ;; solver for exactly this reason, but the shipped one must not need clamping.
  ;; Note the fixed member here carries the greater content-key, so a stub that
  ;; ignored `:assumptions` would pick it.
  (let [c (content 1 '(a) 9 '(z))
        p (solve/program #{1} [(ng 0 1 9)] c)
        r (decide p)]
    (is (= #{9} (:fixed p)) "the setup really does put the bigger key on the fixed side")
    (is (= #{1} (:defeat r)))
    (is (= [] (:violated r)))))

(deftest a-nogood-with-no-choosable-member-is-reported-violated
  ;; The `(empty? choosable)` arm.  `program` filters such nogoods out, so this shape
  ;; only arrives from a hand-built Program.  The contract is that a solve never
  ;; *fails*: the unsatisfiable contradiction is returned as data, whole, so a caller
  ;; can report its sentence and priority.
  (let [bad (ng 3 7 8)
        r   (solve-types/solve solve/local-solver
                               (solve-types/->Program #{} #{7 8} [bad] {} []))]
    (is (= #{} (:defeat r)))
    (is (= [bad] (:violated r)) "the whole nogood map comes back, not just its handles")))

(deftest a-violated-nogood-does-not-stop-the-satisfiable-ones
  ;; Violation is per-contradiction, not a failed solve: the loop must keep going and
  ;; still decide everything it can.  An implementation that returned early on the
  ;; first unsatisfiable nogood would lose the defeat.
  (let [c   (content 1 '(a))
        bad (ng 0 7 8)
        r   (solve-types/solve solve/local-solver
                               (solve-types/->Program #{1} #{7 8 9} [(ng 0 1 9) bad] c []))]
    (is (= #{1} (:defeat r)))
    (is (= [bad] (:violated r)))))

;; ---- 5. priority, and the already-satisfied skip -------------------------

(deftest the-highest-priority-nogood-is-decided-first
  ;; Priority is caller-assigned rank (`negation-nogoods` scores it from the members'
  ;; defeat-classes), and an earlier choice constrains later ones — so which nogood
  ;; goes first is observable in how much belief the solve costs.
  ;;
  ;; Both orderings are asserted, because only the pair distinguishes the sort key
  ;; from its negation: dropping the `-` from `(comp - :priority)` swaps these two
  ;; results, and either one alone still looks right.
  (let [c (content 1 '(a) 2 '(b) 3 '(c))]
    (testing "with the {1,2} pair ranked first, giving up (b) settles both"
      (let [r (decide (solve/program #{1 2 3} [(ng 10 1 2) (ng 0 2 3)] c))]
        (is (= #{'(b)} (claims c (:defeat r))))))
    (testing "with the {2,3} pair ranked first, the greedy walk costs a second datum"
      (let [r (decide (solve/program #{1 2 3} [(ng 0 1 2) (ng 10 2 3)] c))]
        (is (= #{'(b) '(c)} (claims c (:defeat r))))))))

(deftest a-nogood-already-satisfied-by-an-earlier-choice-is-skipped
  ;; The `(< (count live) (count nogood))` arm.  Two overlapping pairs where the first
  ;; decision happens to fall on the shared member: the second nogood no longer has
  ;; all its members believed, so it is satisfied and must added no work more.
  (let [c (content 1 '(a) 2 '(b) 3 '(c))
        r (decide (solve/program #{1 2 3} [(ng 0 1 2) (ng 0 2 3)] c))]
    (is (= #{'(b)} (claims c (:defeat r))) "one defeat satisfies both")
    (is (= [] (:violated r)) "a satisfied nogood is not a violated one")))

(deftest a-wider-nogood-is-satisfied-by-one-defeated-member
  ;; The satisfied check is "at least one member is out", NOT `(<= (count live) 1)`
  ;; — the right test for a *pair* and wrong for anything wider: a three-member nogood
  ;; with one member already out still has two live, so a stub reading it that way
  ;; decides the nogood a second time and disbelieves a second datum to satisfy a
  ;; constraint that already holds.  Here the {2,3,4} nogood is satisfied the moment
  ;; (b) is defeated, and defeating (d) as well is the failure this pins.
  ;;
  ;; Latent rather than live — `negation-nogoods` only ever builds P/¬P pairs — but
  ;; `program` is a public fn that accepts any nogood, and over-defeating is the
  ;; failure mode the whole assumptions/fixed split exists to prevent.
  (let [c (content 1 '(a) 2 '(b) 3 '(c) 4 '(d))
        r (decide (solve/program #{1 2 3 4} [(ng 0 1 2) (ng 0 2 3 4)] c))]
    (is (= #{'(b)} (claims c (:defeat r)))
        "defeating (b) satisfies both nogoods; (d) must survive")
    (is (= [] (:violated r)))))

(deftest a-wide-nogood-standing-alone-still-costs-one-defeat
  ;; The complement, so the fix above cannot be mistaken for "wide nogoods are always
  ;; skipped": with nothing yet defeated a three-member nogood is live in full and
  ;; must be decided exactly once.
  (let [c (content 1 '(a) 2 '(b) 3 '(c))
        r (decide (solve/program #{1 2 3} [(ng 0 1 2 3)] c))]
    (is (= #{'(c)} (claims c (:defeat r))))
    (is (= [] (:violated r)))))

(deftest the-stub-is-greedy-and-not-globally-minimal
  ;; Pinning the documented boundary between the stub and the ASP backend
  ;; (docs/nmtms.md: "where the stub walks contradictions one at a time, ASP optimizes
  ;; globally").  Both nogoods share handle 1, so defeating (a) alone would settle
  ;; them; the stub takes the greatest content-key of each in turn and spends two.
  ;; `asp_edge_test/defeat-is-minimal-across-overlapping-nogoods` is the same shape
  ;; against the real solver, and it gets the one-atom cover — that difference is the
  ;; reason the backend exists, so it should be visible from both sides.
  (let [c (content 1 '(a) 2 '(b) 3 '(c))
        r (decide (solve/program #{1 2 3} [(ng 0 1 2) (ng 0 1 3)] c))]
    (is (= #{'(b) '(c)} (claims c (:defeat r))))
    (is (= [] (:violated r)) "suboptimal, but it did satisfy both")))

(deftest a-solve-is-a-pure-function-of-its-program
  ;; Determinism is the contract `last-program` and `asp.label/classify` are written
  ;; against: the recorded Program has to be enough to reconstruct the decision, and
  ;; the *only* thing that carries.  So the comparison is against two other Programs —
  ;; one rebuilt field for field from what a recorder hands back, one carrying the same
  ;; claims written down in another order.  `(= (decide p) (decide p))` on one object
  ;; says only that `decide` is not a random number generator.
  (let [c        (content 1 '(a) 2 '(b) 3 '(c))
        p        (solve/program #{1 2 3} [(ng 1 1 2) (ng 0 2 3)] c)
        recorded (solve-types/map->Program (into {} p))
        other    (solve/program #{3 2 1} [(ng 0 3 2) (ng 1 2 1)]
                                (content 3 '(c) 2 '(b) 1 '(a)))
        r        (decide p)]
    (is (not (identical? p recorded)))
    (is (= p recorded) "a Program is a value, so it reconstructs field for field")
    (is (= r (decide recorded)) "the recorded Program decides what the original did")
    (is (= r (decide other))
        "and so does the same program written down in another order — nothing may key on
         the order the nogoods or the content arrived in")
    (is (= #{'(b)} (claims c (:defeat r))) "the content-sort loser, in every ordering")
    (is (= #{:defeat :violated} (set (keys r))) "and the result shape is closed")))

;; ---- 6. the protocol on a live KB --------------------------------------------

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb the-shipped-default-solver-is-the-local-stub
  ;; `core/open-kb` installs `solve/local-solver`.  Everything above tests that stub
  ;; because it is what a KB actually runs with — if the default drifted to something
  ;; else this file would be testing a solver nobody uses.
  (is (identical? solve/local-solver @(:solver kb))))

(tu/deftest-kb set-solver-installs-the-solver-and-returns-the-kb
  ;; The plug-in contract: `set-solver` mutates the KB's solver atom in place and
  ;; hands the KB back so it can be threaded.  Returning a *new* KB instead would
  ;; typecheck, read fine, and silently leave every caller holding the old solver.
  ;;
  ;; `nmtms_test/an-installed-solver-is-never-asked-to-decide-a-plain-rebuttal` covers
  ;; the other half — that the engine does not currently consult it for a rebuttal.
  (let [asked  (atom [])
        plugin (reify solve-types/Solver
                 (solve [_ program]
                   (swap! asked conj program)
                   {:defeat #{} :violated []}))
        ret    (v/set-solver kb plugin)]
    (is (identical? kb ret) "set-solver is threadable")
    (is (identical? plugin @(:solver kb)))
    (testing "and the installed solver is what a solve dispatches to"
      (let [p (solve/program #{1 2} [(ng 0 1 2)] (content 1 '(a) 2 '(b)))]
        (is (= {:defeat #{} :violated []} (solve-types/solve @(:solver kb) p)))
        (is (= [p] @asked) "the plug-in saw the program, unaltered")))
    (testing "whereas the stub it replaced would have decided that same program"
      (is (= #{2} (:defeat (decide (solve/program #{1 2} [(ng 0 1 2)]
                                                  (content 1 '(a) 2 '(b))))))))))
