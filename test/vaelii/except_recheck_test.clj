;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.except-recheck-test
  "The cost of the `exceptWhen` re-check and re-chain, and the channels every trigger
  must still reach (docs/exceptions.md).

  The cost tests count level-6 exception evaluations (`provers/exception-holds?` calls,
  through `with-redefs`) rather than time them, so a quadratic shows in the count at
  sizes a clock cannot separate.  Each test builds its own KB on the **isolated**
  database pair, since it rebuilds in a loop."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.provers :as provers]
            [vaelii.test-util :as tu]))

(def ^:private ctx 'CxRecheckCost)

(defn- counting-evaluations
  "Run `f`, returning the number of level-6 exception evaluations it caused."
  [f]
  (let [n    (atom 0)
        orig provers/exception-holds?]
    (with-redefs [provers/exception-holds?
                  (fn [& args] (swap! n inc) (apply orig args))]
      (f))
    @n))

(defn- excepted-rule!
  "`(probe_x ?x) => (seen_x ?x)`, excepted when `(skip_x ?x)`."
  [kb]
  (v/assert kb '(exceptWhen (skip_x ?x)
                            (set/defaultRule (set/forwardRule (implies (and (probe_x ?x)) (seen_x ?x)))))
            ctx))

(defn- probe! [kb i] (v/assert kb (list 'probe_x (symbol (str "PX" i))) ctx))

;; ---- the re-check is not quadratic in a rule's firing count -------------

(deftest a-trigger-re-checks-only-the-firings-it-could-reach
  ;; `n` firings of one excepted rule, then six triggers on the exception's predicate
  ;; about individuals no firing names, so none can block or release anything.  Visiting
  ;; every firing costs n×6 queries.  The absolute bound keeps the ratio from passing with
  ;; both readings large.
  (doseq [[label rule! firing! trigger]
          [["placed firings" excepted-rule! probe! 'skip_x]
           ;; the exception fact first, so each firing is refused and recorded
           ;; (docs/exceptions.md, \"A refused firing is remembered as bindings\")
           ["refused firings" excepted-rule!
            (fn [kb i] (v/assert kb (list 'skip_x (symbol (str "PX" i))) ctx) (probe! kb i))
            'skip_x]
           ;; narrowed through its query frame, as the index keys it
           ["an (unknown S) exception"
            (fn [kb]
              (v/assert kb '(exceptWhen (unknown (qskip_x ?x))
                                        (set/defaultRule
                                         (set/forwardRule (implies (and (qprobe_x ?x)) (qseen_x ?x)))))
                        ctx))
            (fn [kb i] (v/assert kb (list 'qprobe_x (symbol (str "QX" i))) ctx))
            'qskip_x]]]
    (testing label
      (let [cost (fn [n]
                   (tu/with-cleared-kb [kb tu/isolated-fresh]
                     (rule! kb)
                     (dotimes [i n] (firing! kb i))
                     (counting-evaluations
                      #(dotimes [i 6]
                         (v/assert kb (list trigger (symbol (str "Unrelated" i))) ctx)))))
            few  (cost 8)
            many (cost 32)]
        (is (<= many (+ 4 (* 2 (max 1 few))))
            (str label ": re-check cost grew with the firing count: " few " -> " many
                 " evaluations for the same 6 triggers"))
        (is (< many 32)
            (str label ": 6 triggers that can block nothing cost " many " level-6 queries"))))))

(deftest a-blocked-rule-is-not-re-joined-over-the-whole-fact-extent
  (testing "settling a pass that blocks re-derives what it released, not the rule's
            whole extent"
    ;; A second rule derives the exception for every individual, so every firing is
    ;; blocked and swept and no pass releases anything.
    (let [cost (fn [n]
                 (tu/with-cleared-kb [kb tu/isolated-fresh]
                   (excepted-rule! kb)
                   (v/assert kb '(set/defaultRule (set/forwardRule (implies (and (probe_x ?x)) (skip_x ?x)))) ctx {:direction :forward})
                   (counting-evaluations #(dotimes [i n] (probe! kb i)))))
          small (cost 10)
          big   (cost 40)]
      ;; linear would be 4x, quadratic 16x; 6x separates them with room for the
      ;; constant term
      (is (< big (* 6 (max 1 small)))
          (str "quadrupling the asserts multiplied the exception evaluations by "
               (double (/ big (max 1 small))) " (" small " -> " big ")")))))

;; ---- what the narrowing must still reach --------------------------------

(deftest a-fact-at-a-subtype-of-the-exceptions-predicate-still-blocks
  (testing "an exception on a general type is satisfied by a fact at a subtype"
    ;; The trigger's predicate is below the exception's in the genl closure, so a filter
    ;; comparing the two predicates for equality misses it.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(genl xpenguin xflightless) ctx)
      (v/assert kb '(exceptWhen (xflightless ?x)
                                (set/defaultRule (set/forwardRule (implies (and (xbird ?x)) (xflies ?x)))))
                ctx)
      (v/assert kb '(xbird Opus) ctx)
      (is (seq (v/sentexes-matching kb '(xflies Opus) '?ctx))
          "the rule concludes while nothing excepts it")
      (v/assert kb '(xpenguin Opus) ctx)
      (is (empty? (v/sentexes-matching kb '(xflies Opus) '?ctx))
          "a penguin fact satisfies the flightless exception through the genl closure"))))

(deftest a-genl-edge-change-still-re-checks-every-firing
  (testing "a taxonomy edge carries no triggering fact, so it re-checks everything"
    ;; Nothing arrives on the exception's predicate: the closure moves, so the rule is
    ;; queued with no sentence to narrow on.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(exceptWhen (xflightless ?x)
                                (set/defaultRule (set/forwardRule (implies (and (xbird ?x)) (xflies ?x)))))
                ctx)
      (v/assert kb '(xbird Tweety) ctx)
      (v/assert kb '(xpenguin Tweety) ctx)
      (is (seq (v/sentexes-matching kb '(xflies Tweety) '?ctx))
          "a penguin is not yet flightless: no edge relates the types")
      (v/assert kb '(genl xpenguin xflightless) ctx)
      (is (empty? (v/sentexes-matching kb '(xflies Tweety) '?ctx))
          "the edge makes the exception hold, and the conclusion is swept"))))

(deftest a-genlCx-edge-rechecks-only-the-exceptions-in-its-ancestor-set
  (testing "a genlCx edge outside every excepted rule's placement ancestor set re-checks
            none of them, instead of the whole excepted-rule roster"
    ;; A genlCx edge can flip only an exception evaluated in a context the edge's `sub`
    ;; reaches (`context-down`), so an edge elsewhere re-checks nothing.  Re-checking
    ;; every fired excepted rule would cost one level-6 query per rule.
    (let [cost (fn [n-rules]
                 (tu/with-cleared-kb [kb tu/isolated-fresh]
                   ;; n distinct excepted rules, each fired once in `ctx` (a conclusion each)
                   (dotimes [i n-rules]
                     (let [p (symbol (str "cprobe" i)) s (symbol (str "cseen" i))
                           k (symbol (str "cskip" i))]
                       (v/assert kb (list 'exceptWhen (list k '?x)
                                          (list 'set/defaultRule
                                                (list 'set/forwardRule (list 'implies (list 'and (list p '?x)) (list s '?x)))))
                                 ctx)
                       (v/assert kb (list p (symbol (str "CI" i))) ctx)))
                   ;; a fresh genlCx edge whose ancestor set (context-down of its sub) does
                   ;; not reach `ctx`, so no fired exception is in it
                   (counting-evaluations
                    #(v/assert kb '(genlCx CxFarSub CxFarSuper)
                               'CxUniverse {:strength :monotonic}))))
          few  (cost 5)
          many (cost 20)]
      (is (= 0 few many)
          (str "an out-of-ancestor-set genlCx edge re-checked exceptions instead of "
               "narrowing to its ancestor set: " few " (5 rules) / " many " (20 rules)")))))

(deftest a-released-exception-is-still-re-derived
  (testing "retracting what the exception rested on brings the conclusion back"
    ;; Revival under `exceptWhen` is a re-derivation, not a relabel: the conclusion was
    ;; swept.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (excepted-rule! kb)
      (v/assert kb '(probe_x PX0) ctx)
      (is (seq (v/sentexes-matching kb '(seen_x PX0) '?ctx)) "concluded while unexcepted")
      (let [h (v/assert kb '(skip_x PX0) ctx)]
        (is (empty? (v/sentexes-matching kb '(seen_x PX0) '?ctx)) "blocked and swept")
        (v/retract! kb h)
        (is (seq (v/sentexes-matching kb '(seen_x PX0) '?ctx))
            "the released exception is re-derived by the time retract! returns")))))

;; ---- the choke points: every mutation path posts the re-check -----------
;;
;; Every path that stores or removes a sentex posts to the re-check queue through
;; `integrate/sentex-added` / `sentex-removed!` or `special`'s derivation-path twin.
;; One test per path: a derived arrival, a derived departure through `retract!`'s
;; teardown, and a departure through the exception sweep inside `settle`.

(deftest a-derived-fact-triggers-the-re-check
  (testing "an exception satisfied only by inference still blocks: the derived fact
            is a re-check trigger like an asserted one"
    ;; skip_x never arrives as a premise — a second rule concludes it — so the
    ;; trigger must come from the derivation path's choke point.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (excepted-rule! kb)
      (v/assert kb '(set/forwardRule (implies (and (mark_x ?x)) (skip_x ?x))) ctx)
      (v/assert kb '(probe_x PX0) ctx)
      (is (seq (v/sentexes-matching kb '(seen_x PX0) '?ctx)) "concluded while nothing excepts it")
      (v/assert kb '(mark_x PX0) ctx)          ; skip_x PX0 arrives by derivation only
      (is (seq (v/sentexes-matching kb '(skip_x PX0) '?ctx)) "the exception fact was derived")
      (is (empty? (v/sentexes-matching kb '(seen_x PX0) '?ctx))
          "the derived exception blocked the rule and its conclusion was swept"))))

(deftest a-retraction-triggers-the-re-check
  (testing "a fact leaving through retract!'s teardown is a re-check trigger: the
            swept derived exception releases the rule"
    ;; The exception fact is itself derived, so retracting its premise removes it
    ;; through retract!'s removal loop — the removal choke point.  Without the
    ;; posting there, nothing re-chains the released rule and seen_x never appears.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (excepted-rule! kb)
      (v/assert kb '(set/forwardRule (implies (and (mark_x ?x)) (skip_x ?x))) ctx)
      (let [h (v/assert kb '(mark_x PX0) ctx)] ; skip_x PX0 derived before the firing
        (v/assert kb '(probe_x PX0) ctx)
        (is (empty? (v/sentexes-matching kb '(seen_x PX0) '?ctx)) "blocked while the exception holds")
        (v/retract! kb h)                      ; mark_x goes; skip_x is swept with it
        (is (empty? (v/sentexes-matching kb '(skip_x PX0) '?ctx)) "the derived exception fell away")
        (is (seq (v/sentexes-matching kb '(seen_x PX0) '?ctx))
            "the exception's departure re-chained the rule by the time retract! returned")))))

(deftest a-sweep-triggers-the-re-check
  (testing "a conclusion deleted by the exception sweep is itself a trigger: its
            departure releases the rule it was blocking"
    ;; Two excepted rules in a chain: probe_x ⇒ skip_x (except lift_x) and
    ;; probe_x ⇒ seen_x (except skip_x).  Lifting the first sweeps skip_x *inside
    ;; settle*, and that deletion — the sweep's own teardown, not an assert or a
    ;; retract — must release the second rule within the same fixpoint.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (excepted-rule! kb)
      (v/assert kb '(exceptWhen (lift_x ?x)
                                (set/defaultRule (set/forwardRule (implies (and (probe_x ?x)) (skip_x ?x)))))
                ctx)
      (v/assert kb '(probe_x PX0) ctx)
      (is (seq (v/sentexes-matching kb '(skip_x PX0) '?ctx)) "the exception fact is derived")
      (is (empty? (v/sentexes-matching kb '(seen_x PX0) '?ctx)) "and blocks the seen_x rule")
      (v/assert kb '(lift_x PX0) ctx)
      (is (empty? (v/sentexes-matching kb '(skip_x PX0) '?ctx)) "the lift blocks skip_x, which is swept")
      (is (seq (v/sentexes-matching kb '(seen_x PX0) '?ctx))
          "the swept exception released seen_x inside the same settle"))))

;; ---- the genl edge trigger is narrowed to the closures it moves ----------
;;
;; docs/exceptions.md, "Taxonomy changes are keyed on what the closure moved".

(deftest a-genl-edge-re-checks-only-what-its-closure-touches
  (testing "the touched rule's conclusion is swept; the untouched rule's firings are
            not even re-evaluated"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      ;; touched: excepts on tall_thing, one firing.  untouched: excepts on skip_x,
      ;; twenty firings, which queueing every excepted rule would re-check.
      (v/assert kb '(exceptWhen (tall_thing ?x)
                                (set/defaultRule (set/forwardRule (implies (and (probe_a ?x)) (big_a ?x)))))
                ctx)
      (excepted-rule! kb)
      (dotimes [i 20] (probe! kb i))
      (v/assert kb '(probe_a PA1) ctx)
      (v/assert kb '(giant_thing PA1) ctx)
      (is (seq (v/sentexes-matching kb '(big_a PA1) '?ctx)) "no edge yet: a giant is not yet tall")
      (let [n (counting-evaluations
               #(v/assert kb '(genl giant_thing tall_thing) ctx))]
        (is (empty? (v/sentexes-matching kb '(big_a PA1) '?ctx))
            "the edge reaches the tall_thing exception, so the touched rule is queued
             and its conclusion swept — narrowing must never skip an affected rule")
        (is (= 20 (count (v/sentexes-matching kb '(seen_x ?x) '?ctx)))
            "the untouched rule's conclusions all stand")
        (is (< n 10)
            (str "the edge caused " n " exception evaluations; the untouched rule's "
                 "20 firings must not be among them"))))))

;; ---- and the negated conjunct, which registers under `not` ---------------
;;
;; A negated conjunct is keyed on the edge's subtype closure
;; (`special/recheck-negated-exceptions`), since a contravariant negative match reads the
;; up-closure of the conjunct's own predicate.  Outside the moved closure the edge adds no
;; work; inside it the rule is queued with `:all`.

(defn- negated-exception-cost
  "Level-6 evaluations caused by asserting `(genl <sub> negsuper_t)` on a KB whose one
  excepted rule has fired `firings` times, excepted when `(not (<pred> ?x))` holds."
  [firings sub pred]
  (tu/with-cleared-kb [kb tu/isolated-fresh]
    (v/assert kb (list 'exceptWhen (list 'not (list pred '?x))
                       '(set/defaultRule (set/forwardRule (implies (and (neg_probe ?x)) (neg_seen ?x)))))
              ctx)
    (dotimes [i firings] (v/assert kb (list 'neg_probe (symbol (str "NG" i))) ctx))
    (counting-evaluations
     #(v/assert kb (list 'genl sub 'negsuper_t) ctx {:strength :monotonic}))))

(deftest a-genl-edge-does-not-re-check-a-negation-whose-closure-it-left-alone
  (testing "an edge under a subtype no negated conjunct names re-checks none of that
            rule's firings, however many it made"
    ;; The edge's `sub` is a fresh type; the negated conjunct is about `negskip`, whose
    ;; up-closure the edge did not move.
    (let [few  (negated-exception-cost 8  'negvictim_t 'negskip)
          many (negated-exception-cost 32 'negvictim_t 'negskip)]
      (is (= 0 few many)
          (str "an unrelated genl edge re-evaluated a negated exception's firings: "
               few " (8 firings) / " many " (32 firings)")))))

(deftest a-genl-edge-under-a-negations-own-predicate-still-re-checks-it
  (testing "the wave-through is kept where a contravariant reading could reach: an
            edge whose subtype *is* the negated conjunct's predicate queues the rule"
    ;; `(genl negskip negsuper_t)` moves `genls(negskip)`, the closure a contravariant
    ;; match reads to answer `(not (negskip X))`, so every firing is re-decided.
    (let [n (negated-exception-cost 8 'negskip 'negskip)]
      (is (= 8 n)
          (str "an edge on the negated conjunct's own predicate re-checked " n
               " of 8 firings; the defensive wave-through must keep all of them")))))

(deftest a-negated-exception-still-blocks-and-releases
  (testing "narrowing the edge trigger changes nothing about what a negation excepts"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(exceptWhen (not (negskip ?x))
                                (set/defaultRule (set/forwardRule (implies (and (neg_probe ?x)) (neg_seen ?x)))))
                ctx)
      (v/assert kb '(neg_probe NG0) ctx)
      (is (seq (v/sentexes-matching kb '(neg_seen NG0) '?ctx))
          "nothing denies negskip of NG0, so the exception does not hold")
      (let [h (v/assert kb '(not (negskip NG0)) ctx)]
        (is (empty? (v/sentexes-matching kb '(neg_seen NG0) '?ctx))
            "the stored negation satisfies the exception and the conclusion is swept")
        (v/retract! kb h)
        (is (seq (v/sentexes-matching kb '(neg_seen NG0) '?ctx))
            "and its departure releases the rule")))))

;; ---- the two channels a fact reaches an exception through sideways -------
;;
;; Preservation and `arg` inference move an exception's answer with a fact that agrees
;; with the conjunct on no argument (docs/exceptions.md, "Five channels a declaration or
;; a fact reaches an exception through sideways").  Both directions are pinned.

(deftest a-preserved-argument-position-still-withdraws-the-conclusion
  (testing "a claim stated at the supertypes satisfies an exception written at the subtypes"
    ;; The trigger and the conjunct share no argument, so the argument-agreement filter
    ;; drops the firing unless preservation keeps it.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(transitiveInArgInverse pbigger 1 genl) ctx)
      (v/assert kb '(transitiveInArgInverse pbigger 2 genl) ctx)
      (v/assert kb '(genl ppoodle pdog) ctx)
      (v/assert kb '(genl psiamese pcat) ctx)
      (v/assert kb '(exceptWhen (pbigger ppoodle psiamese)
                                (set/defaultRule (set/forwardRule (implies (and (pmark ?x)) (pseen ?x)))))
                ctx)
      (v/assert kb '(pmark PM1) ctx)
      (is (seq (v/sentexes-matching kb '(pseen PM1) '?ctx))
          "fires while nothing excepts it")
      (v/assert kb '(pbigger pdog pcat) ctx)
      (is (v/ask? kb '(pbigger ppoodle psiamese) ctx)
          "the claim is inherited down to the subtypes")
      (is (empty? (v/sentexes-matching kb '(pseen PM1) '?ctx))
          "so the exception holds and the conclusion is swept"))))

(deftest a-preserved-argument-position-still-releases-the-conclusion
  (testing "and removing the inherited claim brings the conclusion back"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(transitiveInArgInverse pbigger 1 genl) ctx)
      (v/assert kb '(transitiveInArgInverse pbigger 2 genl) ctx)
      (v/assert kb '(genl ppoodle pdog) ctx)
      (v/assert kb '(genl psiamese pcat) ctx)
      (v/assert kb '(exceptWhen (pbigger ppoodle psiamese)
                                (set/defaultRule (set/forwardRule (implies (and (pmark ?x)) (pseen ?x)))))
                ctx)
      (v/assert kb '(pbigger pdog pcat) ctx)
      (v/assert kb '(pmark PM1) ctx)
      (is (empty? (v/sentexes-matching kb '(pseen PM1) '?ctx))
          "the exception holds at firing time, so nothing is concluded")
      (v/retract! kb (v/handle-of kb '(pbigger pdog pcat) ctx))
      (is (not (v/ask? kb '(pbigger ppoodle psiamese) ctx)))
      (is (seq (v/sentexes-matching kb '(pseen PM1) '?ctx))
          "the release is a re-derivation, and it happens"))))

(deftest an-argisa-inferred-type-still-withdraws-the-conclusion
  (testing "a fact on an arg-constrained predicate satisfies an exception on the
            declared type"
    ;; `ArgTypeProver` makes X a mammal from `(motherOf X …)` with nothing on `mammal`
    ;; written and no genl path from `motherOf` to it.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(arg amotherOf 1 amammal) ctx)
      (v/assert kb '(exceptWhen (amammal AMuffet)
                                (set/defaultRule (set/forwardRule (implies (and (amark ?x)) (aseen ?x)))))
                ctx)
      (v/assert kb '(amark AM1) ctx)
      (is (seq (v/sentexes-matching kb '(aseen AM1) '?ctx))
          "fires while nothing excepts it")
      (v/assert kb '(amotherOf AMuffet ARex) ctx)
      (is (v/ask? kb '(amammal AMuffet) ctx)
          "the usage types the individual")
      (is (empty? (v/sentexes-matching kb '(aseen AM1) '?ctx))
          "so the exception holds and the conclusion is swept"))))

(deftest an-argisa-declaration-arriving-after-the-facts-still-withdraws
  (testing "the other arrival order: the facts first, then the declaration that types them"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(exceptWhen (amammal AMuffet)
                                (set/defaultRule (set/forwardRule (implies (and (amark ?x)) (aseen ?x)))))
                ctx)
      (v/assert kb '(amotherOf AMuffet ARex) ctx)
      (v/assert kb '(amark AM1) ctx)
      (is (seq (v/sentexes-matching kb '(aseen AM1) '?ctx))
          "nothing types AMuffet yet")
      (v/assert kb '(arg amotherOf 1 amammal) ctx)
      (is (v/ask? kb '(amammal AMuffet) ctx))
      (is (empty? (v/sentexes-matching kb '(aseen AM1) '?ctx))
          "the declaration reaches the fact that was already stored"))))

(deftest an-argisa-inferred-type-still-releases-the-conclusion
  (testing "and retracting the typing fact releases the exception"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(arg amotherOf 1 amammal) ctx)
      (v/assert kb '(exceptWhen (amammal AMuffet)
                                (set/defaultRule (set/forwardRule (implies (and (amark ?x)) (aseen ?x)))))
                ctx)
      (v/assert kb '(amotherOf AMuffet ARex) ctx)
      (v/assert kb '(amark AM1) ctx)
      (is (empty? (v/sentexes-matching kb '(aseen AM1) '?ctx)))
      (v/retract! kb (v/handle-of kb '(amotherOf AMuffet ARex) ctx))
      (is (not (v/ask? kb '(amammal AMuffet) ctx)))
      (is (seq (v/sentexes-matching kb '(aseen AM1) '?ctx))
          "nothing types AMuffet any more, so the conclusion is re-derived"))))

(deftest a-tail-inferred-type-still-withdraws-the-conclusion
  (testing "a fact typed by an argAndRest declaration satisfies an exception on the
            declared type, in either arrival order"
    ;; Under the constraint reading nothing mints the membership, so only the
    ;; `ArgTypeProver` inference answers it, and only a re-check reaches the firing.
    (doseq [[label decl-first?] [["the declaration first" true] ["the fact first" false]]]
      (tu/without-entailing
       (tu/with-cleared-kb [kb tu/isolated-fresh]
         (let [decl! #(v/assert kb '(argAndRest aherdOf 2 amammal) ctx)]
           (when decl-first? (decl!))
           (v/assert kb '(exceptWhen (amammal ARex)
                                     (set/defaultRule (set/forwardRule (implies (and (amark ?x)) (aseen ?x)))))
                     ctx)
           (v/assert kb '(amark AM1) ctx)
           (is (seq (v/sentexes-matching kb '(aseen AM1) '?ctx))
               (str label ": fires while nothing excepts it"))
           (v/assert kb '(aherdOf AHerd AMuffet ARex) ctx)
           (when-not decl-first? (decl!))
           (is (v/ask? kb '(amammal ARex) ctx)
               (str label ": the usage at a tail position types the individual"))
           (is (empty? (v/sentexes-matching kb '(aseen AM1) '?ctx))
               (str label ": so the exception holds and the conclusion is swept"))))))))

;; ---- the third channel: a declaration, not a fact -----------------------
;;
;; A declaration changes what may be concluded from facts already stored, and none of
;; these is on the predicate the exception is written over.

(deftest a-declaration-arriving-late-still-withdraws-the-conclusion
  ;; Each row: the facts, the declaration, and the goal it makes answerable, which is the
  ;; exception of `(<pfx>mark ?x) => (<pfx>seen ?x)`.
  (doseq [[label goal facts decls]
          [["(symmetric P) answers a stored fact's mirror"
            '(ssibOf SBob SAnn) '[(ssibOf SAnn SBob)] '[(symmetric ssibOf)]]
           ["(transitive P) closes a stored chain"
            '(tpartOf TPiston TCar) '[(tpartOf TPiston TEngine) (tpartOf TEngine TCar)]
            '[(transitive tpartOf)]]
           ["(reflexive P) answers a self-pair nobody wrote"
            '(rlikes RBob RBob) '[(rlikes RAnn RAnn)] '[(reflexive rlikes)]]
           ;; the exception names the predicate with no facts of its own
           ["(inverse P Q) answers a goal on P from Q's facts"
            '(ichildOf IBob IAnn) '[(iparentOf IAnn IBob)] '[(inverse ichildOf iparentOf)]]
           ["(transitiveInArg P n R) opens the inheritance over stored facts"
            '(gbigger gpoodle gsiamese)
            '[(genl gpoodle gdog) (genl gsiamese gcat) (gbigger gdog gcat)]
            '[(transitiveInArgInverse gbigger 1 genl) (transitiveInArgInverse gbigger 2 genl)]]]]
    (testing label
      (tu/with-cleared-kb [kb tu/isolated-fresh]
        (let [pfx  (subs (name (first goal)) 0 1)
              mark (symbol (str pfx "mark"))
              seen (symbol (str pfx "seen"))
              ind  (symbol (str (str/upper-case pfx) "M1"))]
          (doseq [f facts] (v/assert kb f ctx))
          (v/assert kb (list 'exceptWhen goal
                             (list 'set/defaultRule
                                   (list 'set/forwardRule
                                         (list 'implies (list 'and (list mark '?x)) (list seen '?x)))))
                    ctx)
          (v/assert kb (list mark ind) ctx)
          (is (seq (v/sentexes-matching kb (list seen ind) '?ctx))
              (str label ": fires while nothing answers the exception"))
          (doseq [d decls] (v/assert kb d ctx))
          (is (v/ask? kb goal ctx) (str label ": the declaration answers the goal"))
          (is (empty? (v/sentexes-matching kb (list seen ind) '?ctx))
              (str label ": so the exception holds and the conclusion is swept")))))))

(deftest an-asymmetry-declaration-arriving-late-moves-the-exceptions-answer
  (testing "(asymmetric P) gives the converse the standing to undercut"
    ;; The declaration moves the answer the other way: `(nbigger nmc nchi)` undercuts the
    ;; pair the general claim inherits only once the predicate is asymmetric.  The firing
    ;; that predates it was refused at derive time and is re-derived from its recorded
    ;; refusal (docs/exceptions.md).
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(genl nchi ndog) ctx)
      (v/assert kb '(genl nmc ncat) ctx)
      (v/assert kb '(transitiveInArgInverse nbigger 1 genl) ctx)
      (v/assert kb '(transitiveInArgInverse nbigger 2 genl) ctx)
      (v/assert kb '(nbigger ndog ncat) ctx)
      (v/assert kb '(nbigger nmc nchi) ctx)
      (v/assert kb '(exceptWhen (nbigger nchi nmc)
                                (set/defaultRule (set/forwardRule (implies (and (nmark ?x)) (nseen ?x)))))
                ctx)
      (v/assert kb '(nmark NM1) ctx)
      (is (v/ask? kb '(nbigger nchi nmc) ctx)
          "the general claim reaches the pair, and nothing yet disputes it")
      (is (empty? (v/sentexes-matching kb '(nseen NM1) '?ctx))
          "so the firing is refused at derive time")
      (v/assert kb '(asymmetric nbigger) ctx)
      (is (not (v/ask? kb '(nbigger nchi nmc) ctx))
          "the specific converse now undercuts the general claim")
      (is (seq (v/sentexes-matching kb '(nseen NM1) '?ctx))
          "so the refused firing is re-derived from what it recorded")
      (v/assert kb '(nmark NM2) ctx)
      (is (seq (v/sentexes-matching kb '(nseen NM2) '?ctx))
          "and a firing made after the declaration is not blocked"))))

(deftest withdrawing-a-transitivity-releases-the-inheritance-it-licensed
  (testing "(transitive R) is also the licence every (transitiveInArg P n R) reads at use"
    ;; Nothing mentions `wneeds_oil` except the preservation declaration, and retracting
    ;; the relation's transitivity is what stops its reach from closing.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(transitive wpartOf) ctx)
      (v/assert kb '(wpartOf WPiston WEngine) ctx)
      (v/assert kb '(wpartOf WEngine WCar) ctx)
      (v/assert kb '(transitiveInArgInverse wneeds_oil 1 wpartOf) ctx)
      (v/assert kb '(wneeds_oil WCar) ctx)
      (v/assert kb '(exceptWhen (wneeds_oil WPiston)
                                (set/defaultRule (set/forwardRule (implies (and (wmark ?x)) (wseen ?x)))))
                ctx)
      (v/assert kb '(wmark WM1) ctx)
      (is (v/ask? kb '(wneeds_oil WPiston) ctx)
          "two hops of a transitive relation, so the claim reaches the piston")
      (is (empty? (v/sentexes-matching kb '(wseen WM1) '?ctx))
          "the exception holds at firing time, so nothing is concluded")
      (v/retract! kb (v/handle-of kb '(transitive wpartOf) ctx))
      (is (not (v/ask? kb '(wneeds_oil WPiston) ctx))
          "a relation nobody says composes is one whose reach may not be closed")
      (is (seq (v/sentexes-matching kb '(wseen WM1) '?ctx))
          "so the exception is released and the conclusion comes back"))))

(deftest a-declaration-does-not-re-check-a-kb-that-declares-no-exception
  (testing "the declaration channel is gated on some rule carrying an exceptWhen"
    ;; Declarations beside standing firings of an unexcepted rule cost no level-6
    ;; evaluations.
    (let [cost (fn [n]
                 (tu/with-cleared-kb [kb tu/isolated-fresh]
                   (v/assert kb '(set/defaultRule
                                  (set/forwardRule (implies (and (dmark ?x)) (dseen ?x))))
                             ctx {:direction :forward})
                   (dotimes [i 20] (v/assert kb (list 'dmark (symbol (str "DM" i))) ctx))
                   (counting-evaluations
                    #(dotimes [i n]
                       (v/assert kb (list 'symmetric (symbol (str "dpred" i))) ctx)))))]
      (is (= 0 (cost 5) (cost 40))
          "a declaration re-checked exceptions on a KB that has none"))))

;; ---- the channel that moves no fact at all: the equality closure --------
;;
;; A merge retires a spelling and rewrites the question, and nothing on the condition's
;; own predicate moves.  `rewriteOf` rather than `sameAs` throughout: `(rewriteOf Kept
;; Retired)` names the loser, so the counterexample fact is not migrated, and a migration
;; would post an ordinary predicate-keyed trigger that hides the channel under test.

(defn- merge-rule!
  "`(mmark ?x) => (mseen ?x)`, excepted when `(mskip ?x)`."
  [kb]
  (v/assert kb '(exceptWhen (mskip ?x)
                            (set/defaultRule (set/forwardRule (implies (and (mmark ?x)) (mseen ?x)))))
            ctx))

(deftest a-merge-that-makes-an-exception-hold-withdraws-the-conclusion
  (testing "an exception satisfied only under the firing's representative still blocks"
    ;; The merge retires `MOne` for `MTwo`, so the firing's conjunct reads `(mskip MTwo)`,
    ;; which holds.  Nothing on `mskip` moved.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (merge-rule! kb)
      (v/assert kb '(mskip MTwo) ctx)
      (v/assert kb '(mmark MOne) ctx)
      (is (seq (v/sentexes-matching kb '(mseen ?x) ctx))
          "fires while nothing excepts MOne")
      (let [h (v/assert kb '(rewriteOf MTwo MOne) ctx)]
        (is (= '["(mskip MTwo)"]
               (mapv #(pr-str (:sentence %)) (v/sentexes-matching kb '(mskip ?x) ctx)))
            "and the exception's own predicate is untouched by the merge")
        (is (empty? (v/sentexes-matching kb '(mseen ?x) ctx))
            "so the exception holds and the conclusion is swept, under either spelling")
        (testing "and splitting the class again releases it"
          (v/retract! kb h)
          (is (seq (v/sentexes-matching kb '(mseen MOne) ctx))
              "the release is a re-derivation, and it happens"))))))

(deftest the-merge-arriving-first-reaches-the-same-belief
  (testing "the order that never needed a trigger still agrees with the one that does"
    ;; The oracle for the test above: the firing is refused at derive time, and no
    ;; trigger is involved.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(rewriteOf MTwo MOne) ctx)
      (merge-rule! kb)
      (v/assert kb '(mskip MTwo) ctx)
      (v/assert kb '(mmark MOne) ctx)
      (is (empty? (v/sentexes-matching kb '(mseen ?x) ctx))
          "merged first, the rule never concludes")))
  (testing "and the same order without the exception fact concludes, under the representative"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(rewriteOf MTwo MOne) ctx)
      (merge-rule! kb)
      (v/assert kb '(mmark MOne) ctx)
      (is (= '[(mseen MTwo)] (mapv :sentence (v/sentexes-matching kb '(mseen ?x) ctx)))))))

(deftest the-exception-fact-arriving-after-the-merge-reaches-the-same-belief
  (testing "a trigger spelled under the representative reaches a firing bound to the
            retired spelling"
    ;; The firing's stored binding is `MOne` and the trigger is spelled `MTwo`, so the
    ;; narrowing has to compare them under the representative.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (merge-rule! kb)
      (v/assert kb '(mmark MOne) ctx)
      (v/assert kb '(rewriteOf MTwo MOne) ctx)
      (is (= '["(mseen MTwo)"]
             (mapv #(pr-str (:sentence %)) (v/sentexes-matching kb '(mseen ?x) ctx)))
          "fires, and the merge re-spells the conclusion under the representative")
      (v/assert kb '(mskip MTwo) ctx)
      (is (empty? (v/sentexes-matching kb '(mseen ?x) ctx))
          "the exception holds under the firing's settled binding, so it is swept")
      (is (empty? (v/sentexes-matching kb '(mseen ?x) '?c))
          "under either spelling, in any context"))))

;; ---- and every one of the 24 orders, not the three written out above ----
;;
;; A block condition is decided at derive time, from a trigger, and off a refusal record,
;; and a merge can arrive between any of them, so the sweeps run all 24 orderings of four
;; assertions.  They differ in where the retired spelling sits: the firing's binding, the
;; condition's own constant, and inside an `(unknown …)`.

(defn- orderings
  "Every ordering of `coll` — a small local permutation, since the sweeps below are over
  four assertions and the suite carries no combinatorics dependency."
  [coll]
  (if (empty? coll)
    [[]]
    (mapcat (fn [x] (map #(vec (cons x %)) (orderings (remove #{x} coll)))) coll)))

(defn- belief-per-order
  "`{belief [order …]}` over every ordering of `ops` — a map of assertion thunks — with
  `read` taking the belief once each order has been asserted into its own cleared KB."
  [ops read]
  (reduce (fn [acc order]
            (tu/with-cleared-kb [kb tu/isolated-fresh]
              (doseq [k order] ((get ops k) kb))
              (update acc (read kb) (fnil conj []) order)))
          {}
          (orderings (keys ops))))

(defn- one-belief!
  "Assert that every ordering of `ops` reaches `expected`, naming the orders that did
  not when one does not."
  [label ops read expected]
  (let [outcome (belief-per-order ops read)]
    ;; the key set, so a failure prints the beliefs that disagreed rather than 24
    ;; orderings twice over; the message carries the tally and the divergent orders
    (is (= #{expected} (set (keys outcome)))
        (str label ": belief depends on arrival order — "
             (pr-str (into {} (map (fn [[b os]] [b (count os)])) outcome))
             ", the divergent orders being "
             (pr-str (mapcat val (dissoc outcome expected)))))))

(deftest every-arrival-order-of-a-merge-reaches-one-belief
  (testing "the firing's own binding is the retired spelling"
    ;; `(mskip MOne)` is asserted under the retired spelling and canonicalized at the
    ;; entry point, the rule binds `?x` to `MOne`, and the exception has to be asked under the
    ;; representative wherever the merge lands in the order.
    (one-belief! "a bound term"
                 {:rule  #(merge-rule! %)
                  :mark  #(v/assert % '(mmark MOne) ctx)
                  :merge #(v/assert % '(rewriteOf MTwo MOne) ctx)
                  :skip  #(v/assert % '(mskip MOne) ctx)}
                 #(mapv :sentence (v/sentexes-matching % '(mseen ?x) '?c))
                 [])
    ;; the positive control: without the exception fact every order concludes, so the
    ;; empty answer above is the exception's and not a rule that never fires
    (one-belief! "a bound term, unexcepted"
                 {:rule  #(merge-rule! %)
                  :mark  #(v/assert % '(mmark MOne) ctx)
                  :merge #(v/assert % '(rewriteOf MTwo MOne) ctx)}
                 #(mapv :sentence (v/sentexes-matching % '(mseen ?x) '?c))
                 '[(mseen MTwo)]))
  (testing "the exception conjunct's own constant is the retired spelling"
    ;; Nothing the firing binds has merged at all: what moved is a term the *rule* was
    ;; written with, and a rule is held back from an individual-only rewrite migration,
    ;; so the stored condition keeps naming `BOne` for good.
    (one-belief! "a conjunct constant"
                 {:rule  #(v/assert % '(exceptWhen (bskip BOne)
                                                   (set/defaultRule
                                                    (set/forwardRule (implies (and (bmark ?x)) (bseen ?x)))))
                                    ctx)
                  :mark  #(v/assert % '(bmark BM1) ctx)
                  :merge #(v/assert % '(rewriteOf BTwo BOne) ctx)
                  :fact  #(v/assert % '(bskip BTwo) ctx)}
                 #(mapv :sentence (v/sentexes-matching % '(bseen ?x) '?c))
                 [])
    (one-belief! "a conjunct constant, unexcepted"
                 {:rule  #(v/assert % '(exceptWhen (bskip BOne)
                                                   (set/defaultRule
                                                    (set/forwardRule (implies (and (bmark ?x)) (bseen ?x)))))
                                    ctx)
                  :mark  #(v/assert % '(bmark BM1) ctx)
                  :merge #(v/assert % '(rewriteOf BTwo BOne) ctx)}
                 #(mapv :sentence (v/sentexes-matching % '(bseen ?x) '?c))
                 '[(bseen BM1)]))
  (testing "a firing's own binding, in the polarity where the wrong answer is unsound"
    ;; `(unknown (yskip ?x))` asked under the stored binding is answered *absent* about a
    ;; term the KB answers under its representative, so the rule concludes where it must
    ;; not — where a silently-false exception merely fails to guard.
    (one-belief! "a naf inner query"
                 {:rule  #(v/assert % '(set/defaultRule
                                        (set/forwardRule (implies (and (ymark ?x) (unknown (yskip ?x)))
                                                                  (yseen ?x))))
                                    ctx)
                  :mark  #(v/assert % '(ymark YOne) ctx)
                  :merge #(v/assert % '(rewriteOf YTwo YOne) ctx)
                  :fact  #(v/assert % '(yskip YOne) ctx)}
                 #(mapv :sentence (v/sentexes-matching % '(yseen ?x) '?c))
                 [])
    (one-belief! "a naf inner query, with nothing for it to find"
                 {:rule  #(v/assert % '(set/defaultRule
                                        (set/forwardRule (implies (and (ymark ?x) (unknown (yskip ?x)))
                                                                  (yseen ?x))))
                                    ctx)
                  :mark  #(v/assert % '(ymark YOne) ctx)
                  :merge #(v/assert % '(rewriteOf YTwo YOne) ctx)}
                 #(mapv :sentence (v/sentexes-matching % '(yseen ?x) '?c))
                 '[(yseen YTwo)])))

(deftest a-merged-binding-does-not-re-check-every-firing-a-rule-ever-made
  (testing "a trigger that can block nothing costs no level-6 query, merges or not"
    ;; Both sides of the narrowing are read under the representative, so a KB whose every
    ;; firing bound a merged term narrows as one that merged nothing.
    (let [cost (fn [merged?]
                 (tu/with-cleared-kb [kb tu/isolated-fresh]
                   (excepted-rule! kb)
                   (dotimes [i 20]
                     (probe! kb i)
                     (when merged?
                       (v/assert kb (list 'rewriteOf (symbol (str "PY" i))
                                          (symbol (str "PX" i)))
                                 ctx)))
                   [(counting-evaluations
                     #(v/assert kb '(skip_x Unrelated0) ctx))
                    (count (v/sentexes-matching kb '(seen_x ?x) '?c))]))]
      (is (= [0 20] (cost false)) "20 firings, one unrelated trigger, nothing merged")
      (is (= [0 20] (cost true))
          "the same trigger re-checked every firing because each bound a merged term"))))

(deftest a-genlCx-edge-retakes-a-census-with-no-firing-to-key-on
  (testing "an aggregate rule is exempt from the placement-ancestor-set narrowing"
    ;; The genlCx narrowing reads where a rule's firings were placed.  An aggregate's
    ;; rising census licenses a firing that never existed, so there is no placement to
    ;; read, and the rule is queued regardless.
    (let [belief (fn [edge-last?]
                   (tu/with-cleared-kb [kb tu/isolated-fresh]
                     ;; both under the rule's own context, so a firing has somewhere to
                     ;; be placed; the edge under test is the one between them
                     (v/assert kb (list 'genlCx 'CxGSub ctx) ctx
                               {:strength :monotonic})
                     (v/assert kb (list 'genlCx 'CxGUp ctx) ctx
                               {:strength :monotonic})
                     (when-not edge-last?
                       (v/assert kb '(genlCx CxGSub CxGUp) ctx
                                 {:strength :monotonic}))
                     (v/assert kb '(gperson GAnn) 'CxGSub)
                     (v/assert kb '(implies (and (gperson ?x)
                                                 (agg/count ?n ?c (gchildOf ?x ?c))
                                                 (lessThan 2 ?n))
                                            (glarge_family ?x))
                               ctx {:direction :forward})
                     (doseq [c '[GC1 GC2 GC3]]
                       (v/assert kb (list 'gchildOf 'GAnn c) 'CxGUp))
                     (when edge-last?
                       (v/assert kb '(genlCx CxGSub CxGUp) ctx
                                 {:strength :monotonic}))
                     (mapv :sentence (v/sentexes-matching kb '(glarge_family ?x)
                                                          'CxGSub))))]
      (is (= '[(glarge_family GAnn)] (belief false))
          "with the edge in place the census sees three children and the rule fires")
      (is (= (belief false) (belief true))
          "and the edge arriving last reaches the same belief"))))

(deftest an-exception-on-an-undeclared-type-is-not-re-checked-by-every-fact
  (testing "the arg channel is keyed on the declaration, not on every fact there is"
    ;; Facts on a predicate nothing declares an `arg` for cost no exception evaluations,
    ;; however many firings stand.
    (let [cost (fn [n]
                 (tu/with-cleared-kb [kb tu/isolated-fresh]
                   (v/assert kb '(exceptWhen (uskip_thing UOne)
                                             (set/defaultRule
                                              (set/forwardRule (implies (and (umark ?x)) (useen ?x)))))
                             ctx)
                   (dotimes [i 20] (v/assert kb (list 'umark (symbol (str "UM" i))) ctx))
                   (counting-evaluations
                    #(dotimes [i n]
                       (v/assert kb (list 'uplain (symbol (str "UP" i)) 'UVal) ctx)))))]
      (is (= 0 (cost 5) (cost 40))
          "a fact on an unconstrained predicate re-checked exceptions anyway"))))

(deftest an-exception-that-is-itself-a-query-operator-is-watched-by-what-it-reads
  (testing "the re-check key is the predicate the query reads, not the operator's own"
    ;; The initial answer needs no re-check, so the release is what proves the key: the
    ;; fact that makes the inner query derivable turns the `unknown` false.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(exceptWhen (unknown (and (qskip ?x) (rskip ?x)))
                                (set/defaultRule (set/forwardRule (implies (and (qmark ?x)) (qseen ?x)))))
                ctx)
      (v/assert kb '(qmark QOne) ctx)
      (is (empty? (v/sentexes-matching kb '(qseen ?x) ctx))
          "neither conjunct is derivable, so the unknown holds and the exception blocks")
      (v/assert kb '(qskip QOne) ctx)
      (is (empty? (v/sentexes-matching kb '(qseen ?x) ctx))
          "one conjunct short — the inner conjunction still is not derivable")
      (v/assert kb '(rskip QOne) ctx)
      (is (seq (v/sentexes-matching kb '(qseen QOne) ctx))
          "the second conjunct completes it, so the unknown is false and the rule fires")
      (testing "and retracting it blocks again, the release being re-decided each time"
        (v/retract! kb (v/handle-of kb '(rskip QOne) ctx))
        (is (empty? (v/sentexes-matching kb '(qseen ?x) ctx)))))))

(deftest a-cycle-through-an-exception-that-is-a-query-operator-is-refused
  (testing "the negative edge runs to what the exception reads, so the cycle is seen"
    ;; The stratification graph reads the same keys: `(unknown S)` is a negative
    ;; dependency on `S`'s predicate.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(exceptWhen (unknown (cskip ?x))
                                (set/defaultRule (set/forwardRule (implies (and (cmark ?x)) (cseen ?x)))))
                ctx)
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not stratified"
           (v/assert kb '(implies (cseen ?x) (cskip ?x)) ctx {:direction :forward}))))))

