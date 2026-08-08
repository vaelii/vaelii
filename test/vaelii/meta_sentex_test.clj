;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.meta-sentex-test
  "Meta-sentexes: a sentex that names another sentex through a **handle**.

  A handle `(sentexHandle <id>)` is the term form of a stored sentex's integer handle,
  so `exceptWhen` (a rule's exception) and `except` (visibility removal) reference the
  sentex they are about rather than inlining it.  This namespace grows with the feature;
  it starts with the handle term primitives (`vaelii.impl.sentex`)."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- handle term primitives ---------------------------------------------

(deftest a-handle-builds-parses-and-round-trips
  (let [h (sx/sentex-handle 42)]
    (testing "shape"
      (is (= '(sentexHandle 42) h))
      (is (sx/sentex-handle? h))
      (is (= 42 (sx/handle-id h))))
    (testing "a non-handle is rejected, and handle-id is nil for it"
      (is (not (sx/sentex-handle? '(penguin ?x))))
      (is (not (sx/sentex-handle? '(sentexHandle ?x))))   ; the id must be an integer, not a var
      (is (not (sx/sentex-handle? 'sentexHandle)))
      (is (nil? (sx/handle-id '(penguin Opus)))))))

(deftest a-handle-is-ground-and-index-stable
  (let [h (sx/sentex-handle 7)]
    (testing "a handle is ground — it holds no variable"
      (is (not (sx/variable? h)))
      (is (sx/ground-term? h)))
    (testing "canon leaves it a canonical list, byte-stable for keys"
      (is (= h (sx/canon h)))
      (is (= (sx/canon h) (sx/canon (sx/sentex-handle 7)))))))

(deftest the-handle-compound-is-indexed-but-its-id-is-not
  ;; The whole `(sentexHandle 7)` is a ground compound, so it is an indexable term — a
  ;; meta-sentex is findable by the handle it names.  The bare id 7 is a number and is
  ;; dropped, so nothing is findable by a raw id.
  (let [h (sx/sentex-handle 7)]
    (is (sx/indexable-term? h) "the handle compound is an index key")
    (is (not (sx/indexable-term? 7)) "the raw id is not")))

;; ---- exceptWhen: the exception names its rule by handle ------------------

(tu/deftest-kb exceptWhen-can-name-a-rule-by-handle-directly
  ;; The user may write `(exceptWhen Q (sentexHandle H))` against an already-stored rule
  ;; H, and the query is aligned to H's variables just as the inline wrapper's is — the
  ;; same meta-sentex, the same block.
  (let [ctx (tu/tmp-ctx "Bird") bird (tu/tmp-type) penguin (tu/tmp-type)
        flies (tu/tmp-pred) Opus (tu/tmp-ind) Tweety (tu/tmp-ind)]
    (v/assert kb (list 'genlContext ctx 'WellContext) 'UniverseContext {:strength :monotonic})
    (let [rh (v/assert kb (list 'set/defaultRule (list 'implies (list bird '?b) (list flies '?b))) ctx)]
      (v/assert kb (list 'exceptWhen (list penguin '?b) (sx/sentex-handle rh)) ctx)
      (v/assert kb (list bird Opus) ctx)
      (v/assert kb (list penguin Opus) ctx)
      (v/assert kb (list bird Tweety) ctx)
      (testing "the handle-form exception blocks exactly the excepted binding"
        (is (empty? (v/sentexes-matching kb (list flies Opus) ctx)))
        (is (seq (v/sentexes-matching kb (list flies Tweety) ctx))))
      (testing "and reads back as the rule's exception, aligned to its canonical vars"
        (is (= [[(list penguin '?var0)]] (provers/rule-exceptions kb rh)))))))

(tu/deftest-kb two-exceptions-on-one-rule-block-if-either-holds
  ;; Separately-asserted exceptWhens amend the one rule (block-if-any); a bird excepted
  ;; by either is grounded, one excepted by neither flies, and retracting one exception
  ;; leaves the other in force.
  (let [ctx (tu/tmp-ctx "Bird") bird (tu/tmp-type) penguin (tu/tmp-type) ostrich (tu/tmp-type)
        flies (tu/tmp-pred) P (tu/tmp-ind) O (tu/tmp-ind) R (tu/tmp-ind)]
    (v/assert kb (list 'genlContext ctx 'WellContext) 'UniverseContext {:strength :monotonic})
    (v/assert kb (list 'exceptWhen (list penguin '?x)
                       (list 'set/defaultRule (list 'implies (list bird '?x) (list flies '?x)))) ctx)
    (let [rh  (v/handle-of kb (list 'implies (list bird '?var0) (list flies '?var0)) ctx)
          eh2 (v/assert kb (list 'exceptWhen (list ostrich '?y)
                                 (list 'set/defaultRule (list 'implies (list bird '?y) (list flies '?y)))) ctx)]
      (doseq [[b t] [[P penguin] [O ostrich]]]
        (v/assert kb (list bird b) ctx) (v/assert kb (list t b) ctx))
      (v/assert kb (list bird R) ctx)
      (testing "the rule carries both exceptions and blocks either trigger"
        (is (= 2 (count (provers/rule-exceptions kb rh))))
        (is (empty? (v/sentexes-matching kb (list flies P) ctx)))
        (is (empty? (v/sentexes-matching kb (list flies O) ctx)))
        (is (seq (v/sentexes-matching kb (list flies R) ctx))))
      (testing "retracting one exception leaves the other governing"
        (v/retract! kb eh2)
        (is (= 1 (count (provers/rule-exceptions kb rh))))
        (is (empty? (v/sentexes-matching kb (list flies P) ctx)) "penguin still excepted")
        (is (seq (v/sentexes-matching kb (list flies O) ctx)) "ostrich flies again")))))

(tu/deftest-kb a-conjunctive-consequent-aligns-the-exception-per-conjunct
  ;; A conjunctive consequent splits into one rule per conjunct, and a self-join tie
  ;; group in the antecedents can be numbered *differently* by each conjunct (the
  ;; consequent breaks the tie).  The exception must align to each conjunct's own
  ;; numbering, not the whole rule's — otherwise one conjunct checks the wrong argument.
  (let [ctx (tu/tmp-ctx "C") p (tu/tmp-type) q (tu/tmp-pred) r (tu/tmp-pred)
        bad (tu/tmp-type) Foo (tu/tmp-ind) Bar (tu/tmp-ind)]
    (v/assert kb (list 'genlContext ctx 'WellContext) 'UniverseContext {:strength :monotonic})
    ;; (p ?a),(p ?b) tie; consequent (and (q ?a) (r ?b)); exception (bad ?b)
    (v/assert kb (list 'exceptWhen (list bad '?b)
                       (list 'set/defaultRule
                             (list 'implies (list 'and (list p '?a) (list p '?b))
                                   (list 'and (list q '?a) (list r '?b)))))
              ctx)
    (v/assert kb (list p Foo) ctx)
    (v/assert kb (list p Bar) ctx)
    (v/assert kb (list bad Bar) ctx)          ; Bar is bad -> the (bad ?b) exception hits ?b=Bar
    (testing "the not-bad witness is concluded on both projections"
      (is (seq (v/sentexes-matching kb (list q Foo) ctx)) "q(Foo): Foo is a valid ?a")
      (is (seq (v/sentexes-matching kb (list r Foo) ctx)) "r(Foo): Foo is a valid ?b"))
    (testing "the bad witness is blocked on the ?b projection — for whichever conjunct r is"
      (is (empty? (v/sentexes-matching kb (list r Bar) ctx))
          "r(Bar): Bar is the excepted ?b, so no r conclusion about it"))))

(tu/deftest-kb retracting-the-rule-leaves-a-harmless-orphan-exception
  ;; Retracting the *rule* (not the exception) leaves the exceptWhen meta-sentex naming
  ;; a now-dead handle.  It governs nothing — no rule fires — and a later fact on the
  ;; exception's predicate re-checking that dead handle must not error.
  (let [ctx (tu/tmp-ctx "B") bird (tu/tmp-type) penguin (tu/tmp-type)
        flies (tu/tmp-pred) Opus (tu/tmp-ind)]
    (v/assert kb (list 'genlContext ctx 'WellContext) 'UniverseContext {:strength :monotonic})
    (let [rh (v/assert kb (list 'set/defaultRule (list 'implies (list bird '?b) (list flies '?b))) ctx)
          mh (v/assert kb (list 'exceptWhen (list penguin '?b) (sx/sentex-handle rh)) ctx)]
      (v/assert kb (list bird Opus) ctx)
      (is (seq (v/sentexes-matching kb (list flies Opus) ctx)))
      (v/retract! kb rh)
      (is (empty? (v/sentexes-matching kb (list flies Opus) ctx)) "the rule and its conclusion are gone")
      (testing "a fact re-checking the orphaned meta's dead rule handle does not error"
        (v/assert kb (list penguin Opus) ctx)
        (is (nil? (v/handle-of kb (list flies Opus) ctx))))
      (v/retract! kb mh))))

(tu/deftest-kb exceptWhen-survives-recover
  ;; The exception is a stored meta-sentex, so rebuilding belief from the durable stores
  ;; must re-block the same conclusions — `recover` re-checks every exception and settles.
  (let [ctx (tu/tmp-ctx "Bird") bird (tu/tmp-type) penguin (tu/tmp-type)
        flies (tu/tmp-pred) Opus (tu/tmp-ind) Tweety (tu/tmp-ind)]
    (v/assert kb (list 'genlContext ctx 'WellContext) 'UniverseContext {:strength :monotonic})
    (v/assert kb (list 'exceptWhen (list penguin '?b)
                       (list 'set/defaultRule (list 'implies (list bird '?b) (list flies '?b)))) ctx)
    (v/assert kb (list bird Opus) ctx)
    (v/assert kb (list penguin Opus) ctx)
    (v/assert kb (list bird Tweety) ctx)
    (testing "before recover: the penguin is blocked, the plain bird flies"
      (is (empty? (v/sentexes-matching kb (list flies Opus) ctx)))
      (is (seq (v/sentexes-matching kb (list flies Tweety) ctx))))
    (v/recover kb)
    (testing "after recover: the same block and the same conclusion"
      (is (empty? (v/sentexes-matching kb (list flies Opus) ctx)))
      (is (seq (v/sentexes-matching kb (list flies Tweety) ctx))))))

;; ---- except: visibility removal down a context subtree -------------------

(tu/deftest-kb except-hides-a-sentex-from-a-context-and-its-descendants
  ;; (except (sentexHandle H)) asserted in C removes visibility of sentex H from C and
  ;; every context that sees C (its descendants), leaving the more general contexts C
  ;; sees untouched.  It rides the ordinary genlContext up-closure — the except is a
  ;; belief-following fact, visible from exactly where it hides its target.
  (let [gp (tu/tmp-ctx "Gp") pm (tu/tmp-ctx "Pm") cm (tu/tmp-ctx "Cm")
        shiny (tu/tmp-pred) gold (tu/tmp-ind)]
    (v/assert kb (list 'genlContext gp 'WellContext) 'UniverseContext {:strength :monotonic})
    (v/assert kb (list 'genlContext pm gp) 'UniverseContext {:strength :monotonic})   ; pm sees gp
    (v/assert kb (list 'genlContext cm pm) 'UniverseContext {:strength :monotonic})   ; cm sees pm
    (let [h (v/assert kb (list shiny gold) gp {:strength :monotonic})]
      (testing "visible up and down the chain before any except"
        (is (v/ask? kb (list shiny gold) gp))
        (is (v/ask? kb (list shiny gold) cm) "inherited into a descendant"))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle h)) pm {:strength :monotonic})]
        (testing "hidden where excepted and below, untouched above"
          (is (v/ask? kb (list shiny gold) gp) "the ancestor is unaffected")
          (is (not (v/ask? kb (list shiny gold) pm)) "hidden in the excepting context")
          (is (not (v/ask? kb (list shiny gold) cm)) "and in its descendant")
          (is (empty? (v/sentexes-matching kb (list shiny gold) pm)) "exact-context query hides it too")
          (is (seq (v/sentexes-matching kb (list shiny gold) '?ctx)) "an any-context read still finds it above"))
        (testing "retracting the except restores visibility — belief-following"
          (v/retract! kb eh)
          (is (v/ask? kb (list shiny gold) cm)))))))

(tu/deftest-kb except-hides-a-membership-from-the-type-reads-too
  ;; `types-of` and `isa?` are retrieval, not a separate notion of what the KB holds, so
  ;; they apply the same three filters the matcher does — believed, visible, not
  ;; excepted.  The third one matters most to the definitional checks, which are built
  ;; on these two: a hidden membership that still answered `types-of` would let
  ;; disjointness refuse a sentence on a ground its context cannot see.
  (let [ctx (tu/tmp-ctx "Sub") dog (tu/tmp-type "dog") Muffet (tu/tmp-ind "Muffet")]
    (v/assert kb (list 'genlContext ctx 'WellContext) 'UniverseContext {:strength :monotonic})
    (let [h (v/assert kb (list dog Muffet) ctx {:strength :monotonic})]
      (is (= [dog] (vec (v/types-of kb Muffet ctx))))
      (is (v/isa? kb Muffet dog ctx))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle h)) ctx {:strength :monotonic})]
        (testing "hidden from both reads where the except is visible"
          (is (empty? (v/types-of kb Muffet ctx)))
          (is (not (v/isa? kb Muffet dog ctx))))
        (testing "an any-context read still finds it, as with query"
          ;; an except hides its target from the contexts that *see* it, not from the
          ;; general ones above — so a read that stands nowhere in particular is unmoved
          (is (= [dog] (vec (v/types-of kb Muffet)))))
        (testing "and both come back when the except goes — belief-following"
          (v/retract! kb eh)
          (is (= [dog] (vec (v/types-of kb Muffet ctx))))
          (is (v/isa? kb Muffet dog ctx)))))))

(tu/deftest-kb a-defeated-except-does-not-hide
  ;; The filter reads *believed* excepts, so an except defeated by a stronger contrary
  ;; belief stops hiding — visibility follows belief, like every cached relation.
  (let [ctx (tu/tmp-ctx "Sub") shiny (tu/tmp-pred) gold (tu/tmp-ind)]
    (v/assert kb (list 'genlContext ctx 'WellContext) 'UniverseContext {:strength :monotonic})
    (let [h (v/assert kb (list shiny gold) ctx {:strength :monotonic})]
      (v/assert kb (list 'except (sx/sentex-handle h)) ctx {:strength :default})
      (is (not (v/ask? kb (list shiny gold) ctx)) "the default except hides it")
      (v/assert kb (list 'not (list 'except (sx/sentex-handle h))) ctx {:strength :monotonic})
      (testing "the monotonic negation defeats the default except; the target reappears"
        (is (v/ask? kb (list shiny gold) ctx))))))

(tu/deftest-kb defeating-an-except-revives-the-derivation-it-blocked
  ;; A belief flip on an except is a visibility flip.  The store/removal chokepoints
  ;; queue the re-check when one arrives or leaves; the settle queues the same
  ;; re-check when one is defeated or revived — else defeating an except revives
  ;; nothing it hid: backward proving answers yes while the store holds nothing, and
  ;; which belief set the KB ends with depends on the order the except and its
  ;; defeater arrived.
  (let [ctx (tu/tmp-ctx "Sub") qq (tu/tmp-pred) pp (tu/tmp-pred) Aa (tu/tmp-ind)]
    (v/assert kb (list 'genlContext ctx 'WellContext) 'UniverseContext {:strength :monotonic})
    (let [h (v/assert kb (list qq Aa) ctx {:strength :monotonic})]
      (v/assert kb (list 'implies (list qq '?x) (list pp '?x)) ctx)
      (is (seq (v/sentexes-matching kb (list pp Aa) ctx)) "the rule fired")
      (v/assert kb (list 'except (sx/sentex-handle h)) ctx {:strength :default})
      (is (empty? (v/sentexes-matching kb (list pp Aa) ctx)) "the except sweeps the conclusion")
      (v/assert kb (list 'not (list 'except (sx/sentex-handle h))) ctx {:strength :monotonic})
      (testing "defeating the except re-derives what it hid, as retracting it would"
        (is (v/ask? kb (list qq Aa) ctx) "the target is seeable again")
        (is (seq (v/sentexes-matching kb (list pp Aa) ctx))
            "and the conclusion resting on it is back in the store"))
      (testing "the same knowledge in the other order ends in the same belief"
        (tu/with-terms [Bb]
          (let [h2 (v/assert kb (list qq Bb) ctx {:strength :monotonic})]
            (v/assert kb (list 'not (list 'except (sx/sentex-handle h2))) ctx
                      {:strength :monotonic})
            (v/assert kb (list 'except (sx/sentex-handle h2)) ctx {:strength :default})
            (is (seq (v/sentexes-matching kb (list pp Bb) ctx))
                "an except born defeated hides nothing")))))))

;; ---- except: the full derivation block ----------------------------------

(tu/deftest-kb except-blocks-a-derivation-that-rests-on-the-hidden-fact
  ;; `except` removes visibility for derivation as well as reads: a rule firing that
  ;; used the hidden fact as an antecedent and placed its conclusion in the cone rests
  ;; on a fact that context can no longer see, so the conclusion is swept — and revived
  ;; when the except is retracted.  A conclusion the except does not reach (placed above
  ;; its cone) is untouched.
  (let [gp (tu/tmp-ctx "Gp") pm (tu/tmp-ctx "Pm") cm (tu/tmp-ctx "Cm")
        shiny (tu/tmp-pred) sparkles (tu/tmp-pred) gold (tu/tmp-ind)]
    (v/assert kb (list 'genlContext gp 'WellContext) 'UniverseContext {:strength :monotonic})
    (v/assert kb (list 'genlContext pm gp) 'UniverseContext {:strength :monotonic})   ; pm sees gp
    (v/assert kb (list 'genlContext cm pm) 'UniverseContext {:strength :monotonic})   ; cm sees pm
    (let [h (v/assert kb (list shiny gold) gp {:strength :monotonic})]
      ;; a rule in cm derives (sparkles gold) in cm from the shiny fact it inherits from gp
      (v/assert kb (list 'implies (list shiny '?x) (list sparkles '?x)) cm)
      (testing "the derivation stands before any except"
        (is (seq (v/sentexes-matching kb (list sparkles gold) cm))))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle h)) pm {:strength :monotonic})]
        (testing "the except hides the antecedent from the cone, so the conclusion is swept"
          (is (empty? (v/sentexes-matching kb (list sparkles gold) cm))
              "the derivation resting on the now-invisible fact is gone")
          (is (nil? (v/handle-of kb (list sparkles gold) cm))
              "swept, not merely disbelieved — the derivation was deleted"))
        (testing "and the antecedent itself is still there above the except's cone"
          (is (v/ask? kb (list shiny gold) gp)))
        (testing "retracting the except re-derives the conclusion"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list sparkles gold) cm))))))))

(tu/deftest-kb a-genlContext-edge-re-checks-except-blocked-derivations
  ;; An `except` block depends on which contexts see the excepting context, so moving a
  ;; genlContext edge can release it.  `cm` sees the fact's context `gp` **directly** and
  ;; the excepting context `pm` separately; retracting only the `cm->pm` edge leaves the
  ;; fact visible (the rule still fires) but stops the except being seen from `cm`, so the
  ;; blocked derivation revives.
  (let [gp (tu/tmp-ctx "Gp") pm (tu/tmp-ctx "Pm") cm (tu/tmp-ctx "Cm")
        shiny (tu/tmp-pred) sparkles (tu/tmp-pred) gold (tu/tmp-ind)]
    (v/assert kb (list 'genlContext gp 'WellContext) 'UniverseContext {:strength :monotonic})
    (v/assert kb (list 'genlContext pm gp) 'UniverseContext {:strength :monotonic})
    (v/assert kb (list 'genlContext cm gp) 'UniverseContext {:strength :monotonic})   ; cm sees gp directly
    (let [edge (v/assert kb (list 'genlContext cm pm) 'UniverseContext {:strength :monotonic})   ; ...and pm
          h    (v/assert kb (list shiny gold) gp {:strength :monotonic})]
      (v/assert kb (list 'implies (list shiny '?x) (list sparkles '?x)) cm)
      (v/assert kb (list 'except (sx/sentex-handle h)) pm {:strength :monotonic})
      (testing "cm sees pm, so the except hides the antecedent and blocks the derivation"
        (is (empty? (v/sentexes-matching kb (list sparkles gold) cm))))
      (testing "retract cm->pm: cm still sees the fact via gp but no longer the except"
        (v/retract! kb edge)
        (is (seq (v/sentexes-matching kb (list sparkles gold) cm))
            "the derivation revives once its context stops seeing the except")))))

(tu/deftest-kb except-blocks-a-derivation-at-derive-time-too
  ;; When the except is already in force, a rule that fires afterward must not place a
  ;; conclusion resting on the hidden fact in the first place — the derive-time twin of
  ;; the sweep above.
  (let [gp (tu/tmp-ctx "Gp") pm (tu/tmp-ctx "Pm") cm (tu/tmp-ctx "Cm")
        shiny (tu/tmp-pred) sparkles (tu/tmp-pred) gold (tu/tmp-ind)]
    (v/assert kb (list 'genlContext gp 'WellContext) 'UniverseContext {:strength :monotonic})
    (v/assert kb (list 'genlContext pm gp) 'UniverseContext {:strength :monotonic})
    (v/assert kb (list 'genlContext cm pm) 'UniverseContext {:strength :monotonic})
    (let [h (v/assert kb (list shiny gold) gp {:strength :monotonic})]
      (v/assert kb (list 'except (sx/sentex-handle h)) pm {:strength :monotonic})
      ;; the rule arrives *after* the except; its conclusion in cm would rest on the
      ;; hidden fact, so it is never placed there
      (v/assert kb (list 'implies (list shiny '?x) (list sparkles '?x)) cm)
      (testing "no conclusion is placed in the cone"
        (is (empty? (v/sentexes-matching kb (list sparkles gold) cm)))
        (is (nil? (v/handle-of kb (list sparkles gold) cm)))))))
