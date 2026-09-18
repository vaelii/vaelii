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
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
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
    (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [rh (v/assert kb (list 'set/defaultRule (list 'set/forwardRule (list 'implies (list bird '?b) (list flies '?b)))) ctx)]
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
    (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'exceptWhen (list penguin '?x)
                       (list 'set/defaultRule (list 'set/forwardRule (list 'implies (list bird '?x) (list flies '?x))))) ctx)
    (let [rh  (v/handle-of kb (list 'implies (list bird '?var0) (list flies '?var0)) ctx)
          eh2 (v/assert kb (list 'exceptWhen (list ostrich '?y)
                                 (list 'set/defaultRule (list 'set/forwardRule (list 'implies (list bird '?y) (list flies '?y))))) ctx)]
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
    (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse {:strength :monotonic})
    ;; (p ?a),(p ?b) tie; consequent (and (q ?a) (r ?b)); exception (bad ?b)
    (v/assert kb (list 'exceptWhen (list bad '?b)
                       (list 'set/defaultRule
                             (list 'set/forwardRule (list 'implies (list 'and (list p '?a) (list p '?b))
                                                          (list 'and (list q '?a) (list r '?b))))))
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
    (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [rh (v/assert kb (list 'set/defaultRule (list 'set/forwardRule (list 'implies (list bird '?b) (list flies '?b)))) ctx)
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
    (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'exceptWhen (list penguin '?b)
                       (list 'set/defaultRule (list 'set/forwardRule (list 'implies (list bird '?b) (list flies '?b))))) ctx)
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
  ;; sees untouched.  It rides the ordinary genlCx up-closure — the except is a
  ;; belief-following fact, visible from exactly where it hides its target.
  (let [gp (tu/tmp-ctx "Gp") pm (tu/tmp-ctx "Pm") cm (tu/tmp-ctx "Cm")
        shiny (tu/tmp-pred) gold (tu/tmp-ind)]
    (v/assert kb (list 'genlCx gp 'CxWell) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx pm gp) 'CxUniverse {:strength :monotonic})   ; pm sees gp
    (v/assert kb (list 'genlCx cm pm) 'CxUniverse {:strength :monotonic})   ; cm sees pm
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
    (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse {:strength :monotonic})
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
    (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse {:strength :monotonic})
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
    (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [h (v/assert kb (list qq Aa) ctx {:strength :monotonic})]
      (v/assert kb (list 'implies (list qq '?x) (list pp '?x)) ctx {:direction :forward})
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
  ;; used the hidden fact as an antecedent and placed its conclusion in the ancestor set rests
  ;; on a fact that context can no longer see, so the conclusion is swept — and revived
  ;; when the except is retracted.  A conclusion the except does not reach (placed above
  ;; its ancestor set) is untouched.
  (let [gp (tu/tmp-ctx "Gp") pm (tu/tmp-ctx "Pm") cm (tu/tmp-ctx "Cm")
        shiny (tu/tmp-pred) sparkles (tu/tmp-pred) gold (tu/tmp-ind)]
    (v/assert kb (list 'genlCx gp 'CxWell) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx pm gp) 'CxUniverse {:strength :monotonic})   ; pm sees gp
    (v/assert kb (list 'genlCx cm pm) 'CxUniverse {:strength :monotonic})   ; cm sees pm
    (let [h (v/assert kb (list shiny gold) gp {:strength :monotonic})]
      ;; a rule in cm derives (sparkles gold) in cm from the shiny fact it inherits from gp
      (v/assert kb (list 'implies (list shiny '?x) (list sparkles '?x)) cm {:direction :forward})
      (testing "the derivation stands before any except"
        (is (seq (v/sentexes-matching kb (list sparkles gold) cm))))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle h)) pm {:strength :monotonic})]
        (testing "the except hides the antecedent from the ancestor set, so the conclusion is swept"
          (is (empty? (v/sentexes-matching kb (list sparkles gold) cm))
              "the derivation resting on the now-invisible fact is gone")
          (is (nil? (v/handle-of kb (list sparkles gold) cm))
              "swept, not merely disbelieved — the derivation was deleted"))
        (testing "and the antecedent itself is still there above the except's ancestor set"
          (is (v/ask? kb (list shiny gold) gp)))
        (testing "retracting the except re-derives the conclusion"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list sparkles gold) cm))))))))

(tu/deftest-kb a-genlCx-edge-re-checks-except-blocked-derivations
  ;; An `except` block depends on which contexts see the excepting context, so moving a
  ;; genlCx edge can release it.  `cm` sees the fact's context `gp` **directly** and
  ;; the excepting context `pm` separately; retracting only the `cm->pm` edge leaves the
  ;; fact visible (the rule still fires) but stops the except being seen from `cm`, so the
  ;; blocked derivation revives.
  (let [gp (tu/tmp-ctx "Gp") pm (tu/tmp-ctx "Pm") cm (tu/tmp-ctx "Cm")
        shiny (tu/tmp-pred) sparkles (tu/tmp-pred) gold (tu/tmp-ind)]
    (v/assert kb (list 'genlCx gp 'CxWell) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx pm gp) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx cm gp) 'CxUniverse {:strength :monotonic})   ; cm sees gp directly
    (let [edge (v/assert kb (list 'genlCx cm pm) 'CxUniverse {:strength :monotonic})   ; ...and pm
          h    (v/assert kb (list shiny gold) gp {:strength :monotonic})]
      (v/assert kb (list 'implies (list shiny '?x) (list sparkles '?x)) cm {:direction :forward})
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
    (v/assert kb (list 'genlCx gp 'CxWell) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx pm gp) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx cm pm) 'CxUniverse {:strength :monotonic})
    (let [h (v/assert kb (list shiny gold) gp {:strength :monotonic})]
      (v/assert kb (list 'except (sx/sentex-handle h)) pm {:strength :monotonic})
      ;; the rule arrives *after* the except; its conclusion in cm would rest on the
      ;; hidden fact, so it is never placed there
      (v/assert kb (list 'implies (list shiny '?x) (list sparkles '?x)) cm {:direction :forward})
      (testing "no conclusion is placed in the ancestor set"
        (is (empty? (v/sentexes-matching kb (list sparkles gold) cm)))
        (is (nil? (v/handle-of kb (list sparkles gold) cm)))))))

;; ---- except: the roster the read is served from -------------------------
;; `res/excepted-handles` is asked per placement and per candidate justification, so it
;; reads the KB's `:excepted` roster — `{context -> {except-handle -> hidden-handle}}`,
;; maintained at the store and removal choke points — rather than fetching every stored
;; `except` record and re-deriving its target.  A roster that drifts from storage is a
;; wrong *belief* and not a slow one: a fact left visible that should be hidden, or
;; hidden that should not be.  So what these pin is the equality against a full scan,
;; held at every point a sentex can arrive or leave.

(defn- excepted-by-scan
  "The reference read: every stored `except` fetched from the record store, filtered by
  belief and by whether `view-context` sees where it was asserted.  This is what
  `res/excepted-handles` computed before it had a roster to read off, kept here as the
  oracle — the roster is only correct if it answers the same thing."
  [kb view-context]
  (if (sx/variable? view-context)
    #{}
    (let [up (tax/context-up (reasoning/taxonomy kb) view-context)]
      (into #{}
            (comp (map #(p/get-sentex (:records kb) %))
                  (filter some?)
                  (filter #(jtms/in? (reasoning/tms kb) (:id %)))
                  (filter #(contains? up (:context %)))
                  (keep #(sx/handle-id (second (:sentence %)))))
            (p/sentexes-with-functor (:index kb) sx/except-functor)))))

(defn- roster-agrees?
  "Does the roster answer the scan, from every context in play — and does the membership
  read (`res/excepted?`, which the per-placement caller goes through) answer the same
  thing as the set read for every handle either of them could be asked about?  A
  divergence there is a firing blocked or admitted against a hidden set nothing else
  agrees with, which is exactly the drift that makes an incrementally-maintained roster a
  wrong belief rather than a slow one."
  [kb contexts]
  (let [handles (into #{} (mapcat #(excepted-by-scan kb %)) contexts)]
    (every? (fn [c]
              (let [scanned (excepted-by-scan kb c)]
                (and (= scanned (res/excepted-handles kb c))
                     (every? #(= (contains? scanned %) (res/excepted? kb % c)) handles))))
            contexts)))

(tu/deftest-kb the-roster-answers-what-a-full-scan-of-storage-answers
  ;; Every way a roster entry can be created, defeated, revived or removed, with the
  ;; scan checked after each — an arrival, a second except in another context on the
  ;; same target, a defeat, a revival, a retraction, and the target's own removal.
  (let [gp (tu/tmp-ctx "Gp") pm (tu/tmp-ctx "Pm") cm (tu/tmp-ctx "Cm")
        ctxs [gp pm cm 'CxWell 'CxUniverse '?ctx]
        shiny (tu/tmp-pred) gold (tu/tmp-ind) lead (tu/tmp-ind)]
    (v/assert kb (list 'genlCx gp 'CxWell) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx pm gp) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx cm pm) 'CxUniverse {:strength :monotonic})
    (is (roster-agrees? kb ctxs) "an empty roster and an empty scan")
    (let [h  (v/assert kb (list shiny gold) gp {:strength :monotonic})
          h2 (v/assert kb (list shiny lead) gp {:strength :monotonic})]
      (is (roster-agrees? kb ctxs) "storing a fact is not storing an except")
      (let [e1 (v/assert kb (list 'except (sx/sentex-handle h)) pm {:strength :monotonic})]
        (is (roster-agrees? kb ctxs) "one except, one context")
        (is (= #{h} (res/excepted-handles kb cm)) "and it is the target that is hidden")
        (let [e2 (v/assert kb (list 'except (sx/sentex-handle h)) cm {:strength :monotonic})
              ;; :default, so the monotonic negation below can defeat it — a monotonic
              ;; except and a monotonic negation are a contradiction, not a defeat
              e3 (v/assert kb (list 'except (sx/sentex-handle h2)) pm {:strength :default})]
          (is (roster-agrees? kb ctxs) "a second except on one target, and a second in one context")
          (is (= #{h h2} (res/excepted-handles kb cm)))
          (testing "a defeated except is out of the roster's answer, being out of belief"
            (v/assert kb (list 'not (list 'except (sx/sentex-handle h2))) pm
                      {:strength :monotonic})
            (is (roster-agrees? kb ctxs))
            (is (= #{h} (res/excepted-handles kb cm)) "h2 is visible again"))
          (testing "retracting one of two excepts on a target leaves the other hiding it"
            (v/retract! kb e2)
            (is (roster-agrees? kb ctxs))
            (is (= #{h} (res/excepted-handles kb cm)) "e1 still hides h from cm"))
          (v/retract! kb e3)
          (is (roster-agrees? kb ctxs) "and the defeated one's record can go too")
          (testing "retracting the last except empties the roster"
            (v/retract! kb e1)
            (is (roster-agrees? kb ctxs))
            (is (empty? (res/excepted-handles kb cm)))))))))

(tu/deftest-kb the-roster-survives-a-recover
  ;; The roster is derived from storage and no store holds it, so `recover` rebuilds it
  ;; — the same standing `rebuild-opposed!` has, and the one a **fork** rides on, since
  ;; a fork recovers over the merged view rather than inheriting its base's belief.
  (let [gp (tu/tmp-ctx "Gp") pm (tu/tmp-ctx "Pm")
        shiny (tu/tmp-pred) gold (tu/tmp-ind)]
    (v/assert kb (list 'genlCx gp 'CxWell) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx pm gp) 'CxUniverse {:strength :monotonic})
    (let [h (v/assert kb (list shiny gold) gp {:strength :monotonic})]
      (v/assert kb (list 'except (sx/sentex-handle h)) pm {:strength :monotonic})
      (is (= #{h} (res/excepted-handles kb pm)))
      (v/recover kb)
      (testing "the rebuilt roster hides exactly what the pre-recover one did"
        (is (= #{h} (res/excepted-handles kb pm)))
        (is (roster-agrees? kb [gp pm 'CxWell]))
        (is (not (v/ask? kb (list shiny gold) pm)) "and the read still follows it")
        (is (v/ask? kb (list shiny gold) gp))))))

;; ---- except strength converse: monotonic except defeats default not-except -

(tu/deftest-kb a-monotonic-except-defeats-a-default-not-except
  ;; The converse of `a-defeated-except-does-not-hide`: a default (not (except H))
  ;; cannot override a monotonic (except H) — strength wins, so the target stays hidden.
  (let [ctx (tu/tmp-ctx "Conv") shiny (tu/tmp-pred) gold (tu/tmp-ind)]
    (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [h (v/assert kb (list shiny gold) ctx {:strength :monotonic})]
      (v/assert kb (list 'except (sx/sentex-handle h)) ctx {:strength :monotonic})
      (is (not (v/ask? kb (list shiny gold) ctx)) "the monotonic except hides it")
      (v/assert kb (list 'not (list 'except (sx/sentex-handle h))) ctx {:strength :default})
      (testing "the default negation cannot defeat the monotonic except; the target stays hidden"
        (is (not (v/ask? kb (list shiny gold) ctx)))))))

;; ---- meta-exception: excepting an except cascades -------------------------

(tu/deftest-kb meta-exception-cascades-restoring-visibility
  ;; A meta-exception — (except (sentexHandle E)) where E is itself an (except …) —
  ;; cascades: hiding the except suppresses its effect and restores visibility of the
  ;; target the inner except was hiding.
  (let [ctx (tu/tmp-ctx "MetaEx") shiny (tu/tmp-pred) gold (tu/tmp-ind)]
    (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [h (v/assert kb (list shiny gold) ctx {:strength :monotonic})]
      (testing "P is true after assertion"
        (is (v/ask? kb (list shiny gold) ctx)))
      (let [e (v/assert kb (list 'except (sx/sentex-handle h)) ctx {:strength :monotonic})]
        (testing "P is hidden after excepting"
          (is (not (v/ask? kb (list shiny gold) ctx))))
        (let [m (v/assert kb (list 'except (sx/sentex-handle e)) ctx {:strength :monotonic})]
          (testing "excepting the except restores visibility — the cascade"
            (is (v/ask? kb (list shiny gold) ctx)
                "P should be visible again: E hides H, M hides E, so E's effect is suppressed"))
          (testing "the inner except E is hidden"
            (is (not (v/ask? kb (list 'except (sx/sentex-handle h)) ctx))
                "the except itself is hidden by the meta-except"))
          (testing "retracting the meta-except re-hides P"
            (v/retract! kb m)
            (is (not (v/ask? kb (list shiny gold) ctx))
                "E's effect is restored when M goes away")))))))

;; ---- meta-except counter: no leak when the inner except goes first --------

(tu/deftest-kb meta-except-count-drops-when-inner-except-retracted-before-meta
  ;; `:meta-except-count` gates the read-time cascade path (resolution/excepted-handles),
  ;; so it must stay equal to what `rebuild-excepted!` recomputes: the number of stored
  ;; excepts whose target is itself a stored except.  Retracting the inner except E before
  ;; the meta-except M = (except E) strands M — its target no longer resolves — so the
  ;; count must fall the moment E leaves, not over-count for the KB's lifetime.
  (let [ctx (tu/tmp-ctx "MetaCount") shiny (tu/tmp-pred) gold (tu/tmp-ind)]
    (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [h (v/assert kb (list shiny gold) ctx {:strength :monotonic})
          e (v/assert kb (list 'except (sx/sentex-handle h)) ctx {:strength :monotonic})
          m (v/assert kb (list 'except (sx/sentex-handle e)) ctx {:strength :monotonic})]
      (testing "M is a meta-except: its target E is itself an except"
        (is (= 1 @(reasoning/meta-except-count kb))))
      (testing "retracting the inner except E strands M, so the count drops at once"
        (v/retract! kb e)
        (is (= 0 @(reasoning/meta-except-count kb))
            "the count must not leak while M dangles over a deleted E"))
      (testing "retracting the meta-except M leaves the count at zero"
        (v/retract! kb m)
        (is (= 0 @(reasoning/meta-except-count kb))))
      (testing "the incremental count equals a fresh recomputation from storage"
        (kb/rebuild-excepted! kb)
        (is (= 0 @(reasoning/meta-except-count kb)))))))

;; ---- ordering contract: except-target extraction before mutation ----------

(tu/deftest-kb except-target-is-captured-before-storage-deletion
  ;; Structural contract: sentex-removed! must extract the except target handle
  ;; BEFORE the first destructive mutation (disintegrate-sentex!, delete-sentex!).
  ;; This pins the defensive binding introduced in 484b59f — the immutable local
  ;; happens to survive deletion in Clojure, but the contract should not depend on
  ;; that accident.
  (let [ctx  (tu/tmp-ctx "Ord")
        pred (tu/tmp-pred) ind (tu/tmp-ind)
        log  (atom [])
        real-except-target     kb/except-target
        real-disintegrate      special/disintegrate-sentex!]
    (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [h  (v/assert kb (list pred ind) ctx {:strength :monotonic})
          eh (v/assert kb (list 'except (sx/sentex-handle h)) ctx {:strength :monotonic})]
      ;; Verify the except is working before we retract
      (is (not (v/ask? kb (list pred ind) ctx)) "except hides the fact")
      ;; Instrument: record the order of except-target vs disintegrate-sentex!
      (with-redefs [kb/except-target        (fn [sentence]
                                              (swap! log conj :except-target)
                                              (real-except-target sentence))
                    special/disintegrate-sentex! (fn [kb sentex]
                                                   (swap! log conj :disintegrate)
                                                   (real-disintegrate kb sentex))]
        (v/retract! kb eh))
      ;; The fact should be visible again after retracting the except
      (is (v/ask? kb (list pred ind) ctx) "retracting except restores visibility")
      ;; The structural contract: except-target must appear before disintegrate
      (let [events @log
            target-idx      (.indexOf ^java.util.List events :except-target)
            disintegrate-idx (.indexOf ^java.util.List events :disintegrate)]
        (is (>= target-idx 0) "except-target was called during retraction")
        (is (>= disintegrate-idx 0) "disintegrate-sentex! was called during retraction")
        (is (< target-idx disintegrate-idx)
            "except-target must be called before the first destructive mutation")))))

;; ---- a handle-naming meta follows its target through a merge --------------
;; A merge restates the sentex a meta names as a twin under the representative.  The meta
;; must follow, in **both** arrival orders — the meta before the merge (`migrate-into`
;; carries it) and the meta after the merge (`migrate-meta-onto-twins` re-points it onto
;; the live twin) — or the merge silently un-hides an excepted fact / unguards a rule.
;; (docs/equality.md, the meta-after-merge case.)

(tu/deftest-kb except-follows-its-target-through-a-merge
  (let [ctx  (tu/tmp-ctx "Ex")
        near (tu/tmp-pred) home (tu/tmp-ind)
        oldp (tu/tmp-ind) newp (tu/tmp-ind)]     ; oldp deprecated in favour of newp
    (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse {:strength :monotonic})
    (testing "except asserted BEFORE the merge is carried onto the twin"
      (let [h (v/assert kb (list near home oldp) ctx {:strength :monotonic})]
        (v/assert kb (list 'except (sx/sentex-handle h)) ctx {:strength :monotonic})
        (is (not (v/ask? kb (list near home oldp) ctx)) "the original is hidden")
        (v/assert kb (list 'rewriteOf newp oldp) ctx {:strength :monotonic})
        (is (some? (kb/find-sentex-handle kb (list near home newp) ctx))
            "the merge created a twin under the representative")
        (is (not (v/ask? kb (list near home newp) ctx))
            "and the twin is hidden too — the except was carried onto it")))))

(tu/deftest-kb except-asserted-after-a-merge-hides-the-live-twin
  (let [ctx  (tu/tmp-ctx "Ex")
        near (tu/tmp-pred) home (tu/tmp-ind)
        oldp (tu/tmp-ind) newp (tu/tmp-ind)]
    (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [h (v/assert kb (list near home oldp) ctx {:strength :monotonic})]
      (v/assert kb (list 'rewriteOf newp oldp) ctx {:strength :monotonic})  ; migrate FIRST
      (is (v/ask? kb (list near home newp) ctx) "the twin is visible before any except")
      (v/assert kb (list 'except (sx/sentex-handle h)) ctx {:strength :monotonic})  ; except the dead original
      (is (not (v/ask? kb (list near home newp) ctx))
          "excepting the superseded original follows onto the live twin")
      (testing "and the hiding lifts when the except is retracted — belief-following"
        (v/retract! kb (kb/find-sentex-handle kb (list 'except (sx/sentex-handle h)) ctx))
        (is (v/ask? kb (list near home newp) ctx) "the twin is visible again")))))
