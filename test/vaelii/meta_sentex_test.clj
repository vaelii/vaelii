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
            [vaelii.impl.except :as exc]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
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

(tu/deftest-kb sentexes-naming-answers-every-meta-nesting-the-handle-and-no-other
  (tu/with-terms [sourcedFrom Wiki Fido Rex dog CxMeta]
    (let [h      (v/assert kb (list dog Fido) CxMeta)
          other  (v/assert kb (list dog Rex) CxMeta)
          direct (v/assert kb (list sourcedFrom (v/sentex-handle h) Wiki) CxMeta)
          nested (v/assert kb (list sourcedFrom (list sourcedFrom (v/sentex-handle h) Wiki) Wiki) CxMeta)]
      (v/assert kb (list sourcedFrom (v/sentex-handle other) Wiki) CxMeta)
      (is (= #{direct nested} (set (map :id (v/sentexes-naming kb h)))))
      (is (= #{direct nested} (set (map :id (v/sentexes-naming kb h {:believed? true})))))
      (is (empty? (v/sentexes-naming kb direct)))
      (is (empty? (v/sentexes-naming kb nil))))))

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

(tu/deftest-kb two-spellings-of-one-exception-are-one-meta-sentex
  (doseq [spelling [:comparison :symmetric]]
    (tu/with-terms [tpX tp_y tsym Ann Bob Xi]
      (let [[e1 e2] (case spelling
                      :comparison [(list 'greaterThan '?y 3) (list 'lessThan 3 '?y)]
                      :symmetric  [(list tsym Ann Bob) (list tsym Bob Ann)])
            rule (list 'set/forwardRule (list 'implies (list tpX '?x '?y) (list tp_y '?x)))]
        (when (= spelling :symmetric)
          (v/assert kb (list 'symmetric tsym) 'CxUniverse)
          (v/assert kb (list tsym Ann Bob) 'CxUniverse))
        (let [m1 (v/assert kb (list 'exceptWhen e1 rule) 'CxUniverse)
              m2 (v/assert kb (list 'exceptWhen e2 rule) 'CxUniverse)]
          (v/assert kb (list tpX Xi 5) 'CxUniverse)
          (testing (name spelling)
            (is (= m1 m2) "an exception conjunct folds as a stored literal does (docs/canonicalization.md)")
            (is (empty? (v/sentexes-matching kb (list tp_y Xi) 'CxUniverse)) "the exception blocks the rule")
            (v/retract! kb m1)
            (is (seq (v/sentexes-matching kb (list tp_y Xi) 'CxUniverse)) "retracting the one handle releases the rule")))))))

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

;; ---- except: the reads the index serves ------------------------------------
;; `exc/excepted-handles` and `exc/excepted?` read the excepts off the index, by context
;; (the `except` extent) and by target (the trie), rather than fetching every stored
;; `except` record.  A read that drifts from storage is a wrong *belief* and not a slow
;; one: a fact left visible that should be hidden, or hidden that should not be.  So these
;; assert the equality against a full scan, held at every point a sentex can arrive
;; or leave.

(defn- excepted-by-scan
  "The reference read: every stored `except` fetched from the record store, filtered by
  belief and by whether `view-context` sees where it was asserted: the oracle the index
  reads are held to."
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

(defn- except-set-agrees?
  "Does the except set answer the scan, from every context in play — and does the membership
  read (`exc/excepted?`, which the per-placement caller goes through) answer the same
  thing as the set read for every handle either of them could be asked about?  A
  divergence there is a firing blocked or admitted against a hidden set nothing else
  agrees with, which is exactly the drift that makes an incrementally-maintained set a
  wrong belief rather than a slow one."
  [kb contexts]
  (let [handles (into #{} (mapcat #(excepted-by-scan kb %)) contexts)]
    (every? (fn [c]
              (let [scanned (excepted-by-scan kb c)]
                (and (= scanned (exc/excepted-handles kb c))
                     (every? #(= (contains? scanned %) (exc/excepted? kb % c)) handles))))
            contexts)))

(tu/deftest-kb the-except-set-answers-what-a-full-scan-of-storage-answers
  ;; Every way an except-set entry can be created or removed, with the scan checked after each
  ;; — an arrival, a second except in another context on the same target, an inert
  ;; denial, a retraction, and the target's own removal.
  (let [gp (tu/tmp-ctx "Gp") pm (tu/tmp-ctx "Pm") cm (tu/tmp-ctx "Cm")
        ctxs [gp pm cm 'CxWell 'CxUniverse '?ctx]
        shiny (tu/tmp-pred) gold (tu/tmp-ind) lead (tu/tmp-ind)]
    (v/assert kb (list 'genlCx gp 'CxWell) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx pm gp) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx cm pm) 'CxUniverse {:strength :monotonic})
    (is (except-set-agrees? kb ctxs) "an empty except set and an empty scan")
    (let [h  (v/assert kb (list shiny gold) gp {:strength :monotonic})
          h2 (v/assert kb (list shiny lead) gp {:strength :monotonic})]
      (is (except-set-agrees? kb ctxs) "storing a fact is not storing an except")
      (let [e1 (v/assert kb (list 'except (sx/sentex-handle h)) pm {:strength :monotonic})]
        (is (except-set-agrees? kb ctxs) "one except, one context")
        (is (= #{h} (exc/excepted-handles kb cm)) "and it is the target that is hidden")
        (let [e2 (v/assert kb (list 'except (sx/sentex-handle h)) cm {:strength :monotonic})
              e3 (v/assert kb (list 'except (sx/sentex-handle h2)) pm {:strength :default})]
          (is (except-set-agrees? kb ctxs) "a second except on one target, and a second in one context")
          (is (= #{h h2} (exc/excepted-handles kb cm)))
          (testing "a denied except stays in the except set's answer, its denial losing to it"
            (v/assert kb (list 'not (list 'except (sx/sentex-handle h2))) pm
                      {:strength :monotonic})
            (is (except-set-agrees? kb ctxs))
            (is (= #{h h2} (exc/excepted-handles kb cm)) "h2 stays hidden"))
          (testing "retracting one of two excepts on a target leaves the other hiding it"
            (v/retract! kb e2)
            (is (except-set-agrees? kb ctxs))
            (is (= #{h h2} (exc/excepted-handles kb cm)) "e1 still hides h from cm"))
          (v/retract! kb e3)
          (is (except-set-agrees? kb ctxs) "and the retracted one's record goes")
          (is (= #{h} (exc/excepted-handles kb cm)) "h2 is visible again")
          (testing "retracting the last except empties the except set"
            (v/retract! kb e1)
            (is (except-set-agrees? kb ctxs))
            (is (empty? (exc/excepted-handles kb cm)))))))))

(tu/deftest-kb the-except-set-survives-a-recover
  ;; The except set is derived from storage and no store holds it, so `recover` rebuilds it,
  ;; and a **fork** rides on that, since a fork recovers over the merged contents rather than
  ;; inheriting its base's belief.
  (let [gp (tu/tmp-ctx "Gp") pm (tu/tmp-ctx "Pm")
        shiny (tu/tmp-pred) gold (tu/tmp-ind)]
    (v/assert kb (list 'genlCx gp 'CxWell) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx pm gp) 'CxUniverse {:strength :monotonic})
    (let [h (v/assert kb (list shiny gold) gp {:strength :monotonic})]
      (v/assert kb (list 'except (sx/sentex-handle h)) pm {:strength :monotonic})
      (is (= #{h} (exc/excepted-handles kb pm)))
      (v/recover kb)
      (testing "the rebuilt except set hides exactly what the pre-recover one did"
        (is (= #{h} (exc/excepted-handles kb pm)))
        (is (except-set-agrees? kb [gp pm 'CxWell]))
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
          (testing "a third depth toggles again"
            (let [m2 (v/assert kb (list 'except (sx/sentex-handle m)) ctx {:strength :monotonic})]
              (is (not (v/ask? kb (list shiny gold) ctx)) "M2 hides M, so E hides P again")
              (v/retract! kb m2)
              (is (v/ask? kb (list shiny gold) ctx) "without M2, M hides E and P is visible")))
          (testing "retracting the meta-except re-hides P"
            (v/retract! kb m)
            (is (not (v/ask? kb (list shiny gold) ctx))
                "E's effect is restored when M goes away")))))))

;; ---- a meta-except over a retracted except ---------------------------------

(tu/deftest-kb a-meta-except-whose-inner-except-is-retracted-hides-nothing
  ;; Retracting the inner except E before the meta-except M = (except E) strands M: its
  ;; target is no longer stored, so the cascade reads no except of the fact E hid.
  (let [ctx (tu/tmp-ctx "MetaCount") shiny (tu/tmp-pred) gold (tu/tmp-ind)]
    (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [h (v/assert kb (list shiny gold) ctx {:strength :monotonic})
          e (v/assert kb (list 'except (sx/sentex-handle h)) ctx {:strength :monotonic})
          m (v/assert kb (list 'except (sx/sentex-handle e)) ctx {:strength :monotonic})]
      (testing "M hides E, so the fact is visible"
        (is (v/ask? kb (list shiny gold) ctx))
        (is (not (contains? (exc/excepted-handles kb ctx) h))))
      (testing "with E retracted, M names no stored except and the fact stays visible"
        (v/retract! kb e)
        (is (v/ask? kb (list shiny gold) ctx))
        (is (not (contains? (exc/excepted-handles kb ctx) h))))
      (testing "with M retracted too, the fact stays visible"
        (v/retract! kb m)
        (is (v/ask? kb (list shiny gold) ctx))))))

;; ---- an except names a stored handle ---------------------------------------

(tu/deftest-kb an-except-naming-no-stored-handle-is-refused
  ;; Handles are allocated in assertion order, so an except naming a handle not yet
  ;; allocated hides whichever sentex arrives there: here the except itself.
  (let [ctx (tu/tmp-ctx "Fwd") shiny (tu/tmp-pred) gold (tu/tmp-ind)]
    (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [h    (v/assert kb (list shiny gold) ctx {:strength :monotonic})
          gone (v/assert kb (list shiny (tu/tmp-ind)) ctx {:strength :monotonic})]
      (v/retract! kb gone)
      (doseq [[label target] [["the handle the except would receive" (inc gone)]
                              ["a retracted handle" gone]]
              :let [ex (list 'except (sx/sentex-handle target))]]
        (testing label
          (is (= [:unknown-handle] (mapv :type (v/check kb ex ctx))))
          (is (= :unknown-handle
                 (try (v/assert kb ex ctx {:strength :monotonic}) nil
                      (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
          (is (nil? (v/handle-of kb ex ctx)))))
      (testing "an except naming a stored handle is admitted"
        (is (= [] (v/check kb (list 'except (sx/sentex-handle h)) ctx)))))))

;; ---- ordering contract: except-target extraction before mutation ----------

(tu/deftest-kb except-target-is-captured-before-storage-deletion
  ;; Structural contract: sentex-removed! must extract the except target handle
  ;; BEFORE the first destructive mutation (disintegrate-sentex!, delete-sentex!).
  ;; This asserts the defensive binding — the immutable local
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
