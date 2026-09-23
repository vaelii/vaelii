;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.descended-declaration-test
  "What a declaration above a predicate binds below it, on the five channels
  `constraint-descension-test` leaves open.

  That namespace pins the descension where it is *asserted*: an edge written by a
  caller, a mark read off a super, a refusal that names the declaration that convicted.
  Each test here is a place where the same descension has to happen and the ingredient
  arrives by another entry point, or where reading it right is only visible in a count or a key:

  * a declaration's **own** position check reads the arity the predicate *inherits*, so a
    sub-predicate that declares no length of its own has a position refused on its
    super's grounds;
  * the `genl` edge arrives by **derivation** rather than by assertion, and the
    conclusion path owes the same two descents the assert path makes;
  * an `exceptWhen` guard turns on a type only a **super**-predicate's `arg` mints, so
    the re-check trigger has to fan up the hierarchy the way the inference does;
  * one stored filler under **two** stacked marks is one clash, not one per mark;
  * and a clash convicted through the hierarchy names the **marked** predicate, which is
    what a report has to print and what nothing read.

  House rules as everywhere: gensym'd temporaries via `tu/with-terms`, engine vocabulary
  (`genl`, `arg`, `functional`, `asymmetric`, `exceptWhen`, `set/defaultRule`,
  contexts) literal."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- ex-type
  "The `:type` on the ex-info a thunk throws, or nil if it does not throw.  Named rather
  than `(thrown? ExceptionInfo …)`: a descension collapsing into a naming or arity
  refusal is exactly the regression a bare `thrown?` stays green through."
  [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(defn- believed?
  "Is `sentence` a **stored, believed** sentex in `ctx`?  Deliberately not `ask` — a mint
  is about a record existing, which a prover's answer is not.

  Boolean rather than truthy, and `same-class` below likewise: `clojure.test` prints the
  *evaluated arguments* of a failing predicate, so passing the KB straight to `is` dumps
  every record, index entry and TMS node into the failure report."
  [kb sentence ctx]
  (let [h (v/handle-of kb sentence ctx)]
    (boolean (and h (v/in? kb h)))))

(defn- same-class? [kb x y] (boolean (v/same-class? kb x y)))

(defn- edge-deriving-rule
  "A rule that **concludes** a `genl` edge from an ordinary binary fact, so the edge can
  arrive down the derivation path instead of through `assert`."
  [relates]
  (list 'set/forwardRule (vr/rule-sentence [(list relates '?x '?y)] (list 'genl '?x '?y))))

;; ---- a declaration's own position check reads the inherited arity -------
;;
;; `constraint-descension-test`'s `a-declarations-own-checks-read-its-own-predicates-
;; arity` holds the near half: a sub-predicate carrying `(ternary_predicate fatherOf)` may
;; declare its own third position however binary its supers are.  The far half is a
;; sub-predicate carrying **nothing** — where `own-arity` answers nil and
;; `declared-arity` falls through to the hierarchy — and reading `own-arity` there admits
;; a constraint on a position the predicate provably does not have.

(tu/deftest-kb an-inherited-arity-refuses-a-position-the-sub-predicate-never-declared
  (tu/with-terms [parentOf fatherOf]
    (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
    (testing "the position the inherited length does not have is refused"
      (is (= :arg-position
             (ex-type #(v/assert kb (list 'arg fatherOf 3 'thing) 'CxUniverse)))
          "fatherOf declares no length of its own, so a fatherOf tuple is a binary
           parentOf tuple and has no third argument to constrain"))
    (testing "and the message names the length it was held to, and where it came from"
      ;; Both routes reach this arm: a predicate carrying its own declaration is convicted
      ;; against its own number and told so (`arggenl-test`'s
      ;; `a-constraint-on-a-position-the-predicate-lacks-is-refused`), which is why the
      ;; message branches rather than saying one thing.  What this pins is the branch the
      ;; inherited route takes — "declared with 2 arguments" is false of fatherOf, which
      ;; declares nothing, and would send an author looking for a declaration on it that
      ;; does not exist
      (let [m (:message (first (v/check kb (list 'arg fatherOf 3 'thing) 'CxUniverse)))]
        (is (re-find (re-pattern (str "takes 2 arguments through " parentOf)) m))
        (is (not (re-find #"declared with" m)))))
    (testing "a position the inherited length does have is admitted"
      (is (v/assert kb (list 'arg fatherOf 2 'thing) 'CxUniverse)))))

;; ---- the edge arrives by derivation -------------------------------------
;;
;; Every arrival-order case elsewhere **asserts** the edge, so the two descents the
;; conclusion path owes are unreachable from a test that writes one: a rule concluding
;; `(genl ?x ?y)` is the only entry point to them, and nothing drove it.

(tu/deftest-kb a-derived-genl-edge-merges-the-fillers-under-a-mark-above-it
  ;; `equate-under-edge` on the derivation path.  The two fillers and the `functional`
  ;; mark are all in place before the edge exists, so the edge is the last of the three
  ;; ingredients — and it is *concluded*, not written.  Without the call the same three
  ;; sentences merge when a caller writes the edge and do not when a rule derives it.
  (tu/with-terms [parentOf fatherOf relates Tom]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list 'functional parentOf) 'CxUniverse)
      (v/assert kb (list fatherOf Tom lo) 'CxUniverse)
      (v/assert kb (list fatherOf Tom hi) 'CxUniverse)
      (is (false? (same-class? kb lo hi)) "nothing above fatherOf carries the mark yet")
      (v/assert kb (edge-deriving-rule relates) 'CxUniverse)
      (v/assert kb (list relates fatherOf parentOf) 'CxUniverse)
      (is (true? (believed? kb (list 'genl fatherOf parentOf) 'CxUniverse))
          "the edge is a conclusion, not an assertion")
      (is (true? (same-class? kb lo hi))
          "a derived edge brings the stored fillers under the mark above them, exactly as
           an asserted one does"))))

(tu/deftest-kb a-derived-genl-edge-entails-the-argument-types-above-it
  ;; `entail-under-edge` on the same path, and the same three ingredients in the same
  ;; order: the fact and the `arg` declaration first, the edge concluded last.
  (tu/with-terms [person parentOf fatherOf relates Ann Mary]
    (binding [checks/*assertive-arg-types?* true]
      (v/assert kb (list 'genl person 'thing) 'CxUniverse)
      (v/assert kb (list 'arg parentOf 1 person) 'CxUniverse)
      (v/assert kb (list fatherOf Ann Mary) 'CxUniverse)
      (is (false? (believed? kb (list person Ann) 'CxUniverse))
          "nothing connects fatherOf to the declaration yet")
      (v/assert kb (edge-deriving-rule relates) 'CxUniverse)
      (v/assert kb (list relates fatherOf parentOf) 'CxUniverse)
      (is (true? (believed? kb (list 'genl fatherOf parentOf) 'CxUniverse))
          "the edge is a conclusion, not an assertion")
      (is (true? (believed? kb (list person Ann) 'CxUniverse))
          "a derived edge mints what the declaration above says of the stored fact"))))

;; ---- the exception trigger fans up the predicate hierarchy --------------
;;
;; `arg` read as an inference makes a fact evidence of a membership nobody wrote, so a
;; fact can flip an `exceptWhen` with nothing on the excepted type having been asserted.
;; `except-recheck-test` pins that channel where the declaration is on the fact's own
;; functor.  The declaration descends too — a `fatherOf` tuple is a `parentOf` tuple and
;; is typed by `parentOf`'s declarations — so the trigger has to look up the hierarchy or
;; the channel is blind again for exactly the facts the descension opened.

(tu/deftest-kb an-exception-on-a-type-a-super-predicates-arg-mints-is-rechecked
  (tu/with-terms [person parentOf fatherOf mark seen Ann Rex M1 CxStory]
    (v/assert kb (list 'genlCx CxStory 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'arg parentOf 1 person) CxStory)
    (v/assert kb (list 'genl fatherOf parentOf) CxStory)
    (v/assert kb (list 'exceptWhen (list person Ann)
                       (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence [(list mark '?x)]
                                                                                       (list seen '?x)))))
              CxStory)
    (v/assert kb (list mark M1) CxStory)
    (is (seq (v/sentexes-matching kb (list seen M1) '?ctx))
        "it fires while nothing types Ann")
    (v/assert kb (list fatherOf Ann Rex) CxStory)
    (testing "the usage types Ann through the declaration above fatherOf"
      (is (true? (v/ask? kb (list person Ann) CxStory))))
    (is (empty? (v/sentexes-matching kb (list seen M1) '?ctx))
        "so the exception holds and the conclusion is swept — the trigger has to reach a
         declaration written of a predicate the fact never names")))

;; ---- one filler under two marks is one clash ---------------------------

(tu/deftest-kb one-stored-filler-under-two-stacked-marks-is-one-clash
  ;; A super's slot probe fans **down** over its specs, so a marked predicate two levels
  ;; up and one level up each find the same stored `fatherYearOf` fact.  That is one pair
  ;; — this sentence and that filler — whichever declaration convicts it, and reporting it
  ;; per mark would make the count a function of how deep the marked chain happens to run.
  (tu/with-terms [ancestorYearOf parentYearOf fatherYearOf Tom]
    (v/with-deferred-settle kb
      (v/assert kb (list 'functional ancestorYearOf) 'CxUniverse)
      (v/assert kb (list 'functional parentYearOf) 'CxUniverse)
      (v/assert kb (list 'genl fatherYearOf parentYearOf) 'CxUniverse)
      (v/assert kb (list 'genl parentYearOf ancestorYearOf) 'CxUniverse))
    (v/assert kb (list fatherYearOf Tom 1980) 'CxUniverse)
    (let [vs (checks/arbitrable-violations kb (list fatherYearOf Tom 1990) 'CxUniverse)]
      (is (= 1 (count vs))
          (str "two marks above one filler is one clash, not one per mark: "
               (pr-str (mapv (juxt :type :pred :existing) vs))))
      (is (= :functional (:type (first vs))))
      (is (= 1980 (:existing (first vs))))
      ;; `:pred` is what the report prints for "which declaration was broken", and the
      ;; one clash has to name a predicate that carries the mark rather than the
      ;; sentence's own functor — which carries none, and is what a reader falling back
      ;; to `(nm/functor …)` would print
      (is (contains? #{parentYearOf ancestorYearOf} (:pred (first vs)))
          (str "the clash names one of the two marked predicates, got "
               (pr-str (:pred (first vs)))))
      (is (not= fatherYearOf (:pred (first vs)))
          "and not the sentence's own functor, which is unmarked"))
    (testing "and both marks really are above the sentence's predicate"
      (is (= :functional (ex-type #(v/assert kb (list fatherYearOf Tom 1990) 'CxUniverse)))))))

;; ---- a clash names the predicate the mark is on ------------------------
;;
;; `:pred` is what a report prints when it says which declaration was broken, and the
;; only case where it differs from the sentence's own functor is a mark read up the
;; hierarchy.  `settle` falls back to `(nm/functor …)` when a violation carries none, so
;; every reader agreed with the producer for as long as the two could only differ here.

(tu/deftest-kb a-descended-functional-clash-names-the-marked-super
  (tu/with-terms [parentYearOf fatherYearOf Tom]
    (v/assert kb (list 'functional parentYearOf) 'CxUniverse)
    (v/assert kb (list 'genl fatherYearOf parentYearOf) 'CxUniverse)
    (v/assert kb (list fatherYearOf Tom 1980) 'CxUniverse)
    (let [p (first (v/check kb (list fatherYearOf Tom 1990) 'CxUniverse))]
      (is (= :functional (:type p)))
      (is (= parentYearOf (:pred p))
          "the slot that is already filled is the marked predicate's, not the functor's"))))

(tu/deftest-kb a-descended-asymmetric-clash-names-the-marked-super
  (tu/with-terms [zzOver zzWayOver A B]
    (v/assert kb (list 'asymmetric zzOver) 'CxUniverse)
    (v/assert kb (list 'genl zzWayOver zzOver) 'CxUniverse)
    (v/assert kb (list zzWayOver A B) 'CxUniverse {:strength :monotonic})
    (let [p (first (v/check kb (list zzWayOver B A) 'CxUniverse))]
      (is (= :asymmetric (:type p)))
      (is (= zzOver (:pred p))
          "the predicate that cannot hold both ways is the marked one"))))

(tu/deftest-kb a-cross-context-clash-marked-at-two-levels-is-one-nogood
  ;; The consumer side, one level up.  `aaYearOf` and `zzBirthYearOf` both carry the
  ;; mark, so the pair convicts twice — once per mark — and the two convictions are one
  ;; clash.  A nogood keyed on anything but the handle set would weigh it twice and let
  ;; the count depend on how many levels of the hierarchy happened to be marked.
  ;; Which of the two marks a *refusal* names is the `(v/check …)` row above, `:pred`
  ;; being the check's own key.
  (tu/with-terms [CxA CxB CxW aaYearOf zzBirthYearOf Tom]
    (let [one (list zzBirthYearOf Tom 1970)
          two (list zzBirthYearOf Tom 1980)]
      (v/with-deferred-settle kb
        (v/assert kb (list 'functional aaYearOf) 'CxUniverse)
        (v/assert kb (list 'functional zzBirthYearOf) 'CxUniverse)
        (v/assert kb (list 'genl zzBirthYearOf aaYearOf) 'CxUniverse))
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxW CxA) 'CxUniverse)
      (v/assert kb (list 'genlCx CxW CxB) 'CxUniverse)
      ;; neither writer can see the other's filler, so both store
      (v/assert kb one CxA)
      (v/assert kb two CxB)
      (let [cs (v/contradictions kb)]
        (is (= [:functional] (mapv :kind cs)) "one nogood for the pair, not one per mark")
        (is (= #{[one CxA] [two CxB]}
               (into #{} (map (juxt :sentence :context)) (:sides (first cs)))))
        (is (seq (v/contradictions kb CxW)) "and CxW is the vantage that reads it")
        (is (empty? (v/contradictions kb CxA))
            "where CxA, which sees one half, reads no dilemma")))))

(tu/deftest-kb a-cross-context-clash-is-decided-through-a-mark-on-the-super-alone
  ;; The gate the case above had to work around.  `could-clash?` and `partner-contexts`
  ;; decide, per sentex, whether a binary fact can be half of a pair at all — and they
  ;; asked `has-prop?` of the exact functor while every check they gate asks `props-over`.
  ;; So the descension the checks implement was invisible here: a pair the assert entry point
  ;; refuses in one context was never weighed across two, because the pass dropped both
  ;; halves before looking at them.  Nothing marks the sub-predicate now.
  (tu/with-terms [CxA CxB CxW aaYearOf zzBirthYearOf Tom]
    (v/with-deferred-settle kb
      (v/assert kb (list 'functional aaYearOf) 'CxUniverse)
      (v/assert kb (list 'genl zzBirthYearOf aaYearOf) 'CxUniverse))
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxW CxA) 'CxUniverse)
    (v/assert kb (list 'genlCx CxW CxB) 'CxUniverse)
    (v/assert kb (list zzBirthYearOf Tom 1970) CxA)
    (v/assert kb (list zzBirthYearOf Tom 1980) CxB)
    (is (= [:functional] (mapv :kind (v/contradictions kb)))
        "the mark is above the functor, and the pair is still a pair")
    (is (seq (v/contradictions kb CxW)) "weighed at CxW, which sees both halves")
    (is (empty? (v/contradictions kb CxA)))))

(tu/deftest-kb a-cross-context-partner-need-not-share-the-sentences-functor
  ;; The other half of the same gate.  `partner-contexts` narrowed the postings it read
  ;; to the sentence's own functor, which was the right narrowing while a mark could only
  ;; sit on the functor — and drops exactly the pairs descending it exists to catch: under
  ;; `(functional aaMeasureOf)` a `zzHeightOf` reading and a `zzStatureOf` one are two
  ;; values of one slot, spelled differently.
  ;;
  ;; Numeric fillers on purpose: two **symbols** filling one functional slot are the
  ;; co-reference case and the engine merges them into an `equals` rather than convicting
  ;; anything, so a clash count would pin the wrong half.  No merge can make two
  ;; numbers one thing, which is what leaves a clash for the vantage to weigh.
  (tu/with-terms [CxA CxB CxW aaMeasureOf zzHeightOf zzStatureOf Tom]
    (v/with-deferred-settle kb
      (v/assert kb (list 'functional aaMeasureOf) 'CxUniverse)
      (v/assert kb (list 'genl zzHeightOf aaMeasureOf) 'CxUniverse)
      (v/assert kb (list 'genl zzStatureOf aaMeasureOf) 'CxUniverse))
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxW CxA) 'CxUniverse)
    (v/assert kb (list 'genlCx CxW CxB) 'CxUniverse)
    (v/assert kb (list zzHeightOf Tom 170) CxA)
    (v/assert kb (list zzStatureOf Tom 180) CxB)
    (is (= [:functional] (mapv :kind (v/contradictions kb)))
        "two spellings of one aaMeasureOf slot, seen together from CxW")
    (is (seq (v/contradictions kb CxW)))
    (is (empty? (v/contradictions kb CxA)))))
