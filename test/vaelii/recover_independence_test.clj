;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.recover-independence-test
  "The **restart** axis of the engine's first invariant: one store, read two ways, gives
  one answer.

  `order_independence_test` asks whether the same knowledge in any order yields the same
  beliefs.  This asks the question a running process cannot: whether the KB that
  *derived* its state agrees with the KB that *rebuilt* it.  The two arrive at the
  taxonomy and the JTMS by different routes — the derivation path integrates each sentex
  as it lands, `recover` replays every stored sentex of a functor and then narrows to
  belief (docs/storage.md, \"Persistence & recovery\") — and nothing but a test compares
  them.  A cache the derivation path forgets to write is invisible until a restart writes
  it, and a cache `recover` writes from storage rather than from belief is invisible until
  a restart revives something the live KB had defeated.  Either way one store answers two
  ways, and the operator sees it as \"it worked yesterday\".

  Each test therefore reads the live KB, opens a **second KB value over the same stores**
  — whose taxonomy and JTMS start empty — recovers it, and demands the identical reading.
  Reading a map rather than a boolean, for `order_independence_test`'s reason: a
  restart that loses one of three caches still answers `true` to the one question a
  boolean asks.

  The scenarios are the ones where the two routes are known to have diverged: a member,
  an edge or a visibility `except` a **rule** concluded rather than an assert (nothing
  keys the derivation path on a functor the metatype *is*), and the two condition
  evaluations that are re-asked rather than stored, over a term whose spelling a merge
  retired."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- restarted
  "A process restart: a second KB value over the same stores, whose in-memory taxonomy
  and JTMS start empty and are rebuilt from the records alone.  `tu/test-kb` opens with
  `:recover? false`, so the rebuild is this call's and nothing else's."
  []
  (doto (tu/test-kb) (v/recover)))

(defn- one-reading!
  "Read `observe` off the live KB and off a restart of it, assert the two agree, and
  return the reading."
  [label kb observe]
  (let [live (observe kb)
        back (observe (restarted))]
    (is (= live back)
        (str label ": the restarted KB disagrees with the live one over one store — live "
             (pr-str live) ", recovered " (pr-str back)))
    live))

;; ---- a rule concluded it, and only an assert had ever been integrated ----

(tu/deftest-kb a-rule-derived-metatype-member-reads-the-same-after-a-restart
  ;; A metatype's members are cached in memory and nowhere stored — the only durable
  ;; trace is the `(M T)` sentexes — and the member arm keys on nothing a table can name,
  ;; the functor *being* the metatype.  `recover`'s member pass walks every stored `(M T)`
  ;; whatever put it there, so a derivation path that skipped the arm separated the pair
  ;; only once a restart had replayed it.
  (tu/with-terms [species dog_t cat_t seedOf]
    (v/assert kb (list 'disjoint_metatype species) 'CxUniverse)
    (v/assert kb (list species dog_t) 'CxUniverse)
    ;; `cat_t` joins the metatype by inference alone — nothing states `(species cat_t)`
    (v/assert kb (list 'implies (list seedOf '?x) (list species '?x)) 'CxUniverse {:direction :forward})
    (v/assert kb (list seedOf cat_t) 'CxUniverse)
    (let [observe (fn [k] {:members  (tax/metatype-members (reasoning/taxonomy k) species)
                           :disjoint (v/disjoint? k dog_t cat_t)
                           :stored   (boolean (seq (v/sentexes-matching k (list species cat_t) '?c)))})
          reading (one-reading! "a rule-derived metatype member" kb observe)]
      (is (= {:members #{dog_t cat_t} :disjoint true :stored true} reading)
          "the derived membership separates the pair, and says so on both sides of a restart"))))

(tu/deftest-kb a-rule-derived-except-reads-the-same-after-a-restart
  ;; A visibility `except` is dispatched on the sentence's shape rather than out of the
  ;; special-predicate table, and the roster it writes is kept at the store primitive —
  ;; which `recover` replays and a derivation path can miss.  The rule fires first, so
  ;; there is a standing firing for the except to sweep: a cold KB computes rather than
  ;; recalls, and would hide the difference.
  (tu/with-terms [q p hide Aa Trigger CxSub]
    (v/assert kb (list 'genlCx CxSub 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [h (v/assert kb (list q Aa) CxSub {:strength :monotonic})]
      (v/assert kb (list 'implies (list q '?x) (list p '?x)) CxSub {:direction :forward :strength :monotonic})
      (v/assert kb (list 'implies (list hide '?z) (list 'except (sx/sentex-handle h)))
                CxSub {:direction :forward :strength :monotonic})
      (v/assert kb (list hide Trigger) CxSub {:strength :monotonic})
      (let [observe (fn [k] {:target     (v/ask? k (list q Aa) CxSub)
                             :conclusion (boolean (seq (v/sentexes-matching k (list p Aa) CxSub)))
                             :except     (boolean (seq (v/sentexes-matching
                                                        k (list 'except (sx/sentex-handle h)) '?c)))})
            reading (one-reading! "a rule-derived visibility except" kb observe)]
        (is (= {:target false :conclusion false :except true} reading)
            "the derived except hides its target and sweeps what rested on it, either side
             of a restart")))))

(tu/deftest-kb a-rule-derived-genl-edge-reads-the-same-after-a-restart
  ;; The closure a `genl` edge feeds is derived state twice over — the edge is concluded
  ;; by a rule, and the membership answer is computed from the cached closure.  So a
  ;; restart has to re-read the concluded edge as an edge, not merely as a stored
  ;; sentence nothing consults.
  (tu/with-terms [subOf sub_t mid_t Ind]
    (v/assert kb (list 'implies (list subOf '?a '?b) (list 'genl '?a '?b)) 'CxUniverse {:direction :forward})
    (v/assert kb (list subOf sub_t mid_t) 'CxUniverse)
    (v/assert kb (list sub_t Ind) 'CxUniverse)
    (let [observe (fn [k] {:isa   (v/isa? k Ind mid_t)
                           :genls (contains? (set (v/genls k sub_t)) mid_t)
                           :edge  (boolean (seq (v/sentexes-matching k (list 'genl sub_t mid_t) '?c)))})
          reading (one-reading! "a rule-derived genl edge" kb observe)]
      (is (= {:isa true :genls true :edge true} reading)
          "a concluded edge answers isa? like an asserted one, before and after a restart"))))

;; ---- a condition that is re-asked rather than stored --------------------

(tu/deftest-kb an-equality-merge-under-a-live-rule-reads-the-same-after-a-restart
  ;; The partition behind `rewriteOf` is a cache like the closures, and a rule standing
  ;; over the merged term is what makes losing it visible: the conclusion is stored at the
  ;; representative, and a restart that replayed the fact without the merge would answer
  ;; the retired spelling differently from the live KB that answered it through the class.
  (tu/with-terms [eqSeed eqSeen EPref EDep]
    (v/assert kb (list 'implies (list eqSeed '?x) (list eqSeen '?x)) 'CxUniverse {:direction :forward})
    (v/assert kb (list eqSeed EDep) 'CxUniverse)
    (v/assert kb (list 'rewriteOf EPref EDep) 'CxUniverse {:strength :monotonic})
    (let [observe (fn [k] {:conclusions (set (map :sentence
                                                  (v/sentexes-matching k (list eqSeen '?x) '?c)))
                           :ask-pref    (v/ask? k (list eqSeen EPref) 'CxUniverse)
                           :ask-dep     (v/ask? k (list eqSeen EDep) 'CxUniverse)})
          reading (one-reading! "an equality merge under a live rule" kb observe)]
      (is (= 1 (count (:conclusions reading)))
          "one conclusion — the class is one term, not two")
      (is (= [true true] [(:ask-pref reading) (:ask-dep reading)])
          "and both spellings answer it, the retired one through its representative"))))

(tu/deftest-kb an-except-conjunct-over-a-merged-term-reads-the-same-after-a-restart
  ;; Nothing about an exception is stored, so it is re-evaluated — and after a restart it
  ;; is re-evaluated against a taxonomy nobody watched being built.  The conjunct names a
  ;; term the merge retired, so the block holds only where the partition was replayed and
  ;; the condition is asked under the representative.  The blocked conclusion is an
  ;; **absence**, which is the reading a restart can most easily turn into a presence.
  (tu/with-terms [xmark xseen xskip XBase XOne XTwo]
    (v/assert kb (list 'exceptWhen (list xskip XOne)
                       (list 'set/defaultRule
                             (list 'set/forwardRule (list 'implies (list 'and (list xmark '?x)) (list xseen '?x)))))
              'CxUniverse)
    (v/assert kb (list xmark XBase) 'CxUniverse)
    (v/assert kb (list 'rewriteOf XTwo XOne) 'CxUniverse)
    (v/assert kb (list xskip XTwo) 'CxUniverse)
    (let [observe (fn [k] {:seen (set (map :sentence (v/sentexes-matching k (list xseen '?x) '?c)))
                           :ask  (v/ask? k (list xseen XBase) 'CxUniverse)})
          reading (one-reading! "an exceptWhen conjunct over a merged term" kb observe)]
      (is (= {:seen #{} :ask false} reading)
          "the exception holds under the representative, and a restart does not release it")))
  (testing "and the same claim for the naf spelling of the condition"
    ;; `(unknown S)` is the polarity where the wrong answer draws a conclusion rather than
    ;; failing to withdraw one, so a restart that lost the partition would not merely fail
    ;; to block — it would believe something the live KB does not.
    (tu/with-terms [ymark yseen yskip YBase YOne YTwo]
      (v/assert kb (list 'set/defaultRule
                         (list 'set/forwardRule (list 'implies (list 'and (list ymark '?x) (list 'unknown (list yskip YOne)))
                                                      (list yseen '?x))))
                'CxUniverse)
      (v/assert kb (list ymark YBase) 'CxUniverse)
      (v/assert kb (list 'rewriteOf YTwo YOne) 'CxUniverse)
      (v/assert kb (list yskip YTwo) 'CxUniverse)
      (let [observe (fn [k] {:seen (set (map :sentence (v/sentexes-matching k (list yseen '?x) '?c)))
                             :ask  (v/ask? k (list yseen YBase) 'CxUniverse)})
            reading (one-reading! "a naf condition over a merged term" kb observe)]
        (is (= {:seen #{} :ask false} reading)
            "a term with an answer under its representative is not absent, restarted either")))))

(tu/deftest-kb a-late-symmetric-mark-reads-the-same-after-a-restart
  ;; The durable half of vaelii#61.  A `(symmetric P)` mark arriving after both spellings
  ;; of a pair were stored *migrates the records* — one row is folded into the other and
  ;; the survivor is re-spelled where it lies — which is the one retroactive arm that
  ;; writes rather than derives, and so the one a restart can most directly contradict.
  ;; A migration that moved only the live KB's reading would leave the records still
  ;; spelling the fact two ways, so `recover` rebuilds the pair the live KB has just
  ;; collapsed and the KB answers one thing until it restarts and another afterwards.
  (tu/with-terms [pborders SEsp SFra]
    (v/assert kb (list pborders SEsp SFra) 'CxUniverse)
    (v/assert kb (list pborders SFra SEsp) 'CxUniverse)
    (v/assert kb (list 'symmetric pborders) 'CxUniverse)
    (let [observe (fn [k]
                    {:rows    (set (map :sentence (v/sentexes-matching k (list pborders '?x '?y) '?c)))
                     :handles (count (set [(v/handle-of k (list pborders SEsp SFra) 'CxUniverse)
                                           (v/handle-of k (list pborders SFra SEsp) 'CxUniverse)]))
                     :ask-sf  (v/ask? k (list pborders SEsp SFra) 'CxUniverse)
                     :ask-fs  (v/ask? k (list pborders SFra SEsp) 'CxUniverse)})
          reading (one-reading! "a late symmetric mark" kb observe)]
      (is (= 1 (count (:rows reading))) "one proposition, one record — restarted too")
      (is (= 1 (:handles reading)) "and both spellings resolve to the one handle")
      (is (= [true true] [(:ask-sf reading) (:ask-fs reading)])))))

(tu/deftest-kb a-different-guarded-rule-is-re-checkable-after-a-restart
  ;; A `(different …)` antecedent holds by the *absence* of a merge, so it names no handle
  ;; a justification can carry and the re-check index is the only instrument that can
  ;; withdraw the firing it guards (docs/equality.md).  The posting is written when the
  ;; rule is **indexed** and nothing about blocking is durable, so a restart that rebuilds
  ;; the rule without rebuilding the posting reads exactly as the live KB does — right up
  ;; until a merge arrives, and then keeps a conclusion the live KB would withdraw.
  ;;
  ;; The withdrawing fact therefore lands on the **restarted** KB and not before it, which
  ;; is what the sibling tests here cannot do with `one-reading!`: the two KBs share one
  ;; store, so a merge asserted live is a merge the rebuild replays rather than one it has
  ;; to re-decide.
  (tu/with-terms [dpRel dqRel DAa DBb]
    (v/assert kb (list 'binary_predicate dpRel) 'CxUniverse)
    (v/assert kb (list 'binary_predicate dqRel) 'CxUniverse)
    (v/assert kb (list 'implies (list 'and (list dpRel '?x '?y) (list 'different '?x '?y))
                       (list dqRel '?x '?y))
              'CxUniverse {:direction :forward})
    (v/assert kb (list dpRel DAa DBb) 'CxUniverse)
    (is (v/ask? kb (list dqRel DAa DBb) 'CxUniverse)
        "the guard holds, so the live KB fired")
    (let [back (restarted)]
      (is (v/ask? back (list dqRel DAa DBb) 'CxUniverse)
          "and the rebuild agrees the firing stands")
      (let [merge (v/assert back (list 'sameAs DAa DBb) 'CxUniverse)]
        (is (not (v/ask? back (list 'different DAa DBb) 'CxUniverse))
            "merged, so the two are no longer provably different")
        (is (not (v/ask? back (list dqRel DAa DBb) 'CxUniverse))
            "and the rebuilt KB re-checks the firing the guard licensed, as the live one does")
        (v/retract! back merge)
        (is (v/ask? back (list dqRel DAa DBb) 'CxUniverse)
            "the release direction survives the restart too")))
    ;; the re-derivation above was drawn by the *rebuilt* KB, whose justification the
    ;; fixture's KB value has no node for, so the store is cleared here rather than left
    ;; to a teardown that can only unwind what one TMS recorded
    (tu/clear-kb! (tu/test-kb))))

(tu/deftest-kb a-computed-context-edge-merge-reads-the-same-after-a-restart
  ;; vaelii#56.  The `genlCx` edge here is **computed** — `contextArgSubrelation` makes
  ;; January a spec of its year structurally, and nobody asserts the edge — so the merge
  ;; it licenses is derived by a producer that runs on the assert maintenance path and
  ;; nowhere in `recover`'s replay.  What a restart rebuilds instead is the stored edge
  ;; sentex, its justification, and the twins the merge wrote, and the question is
  ;; whether those three add up to the reading the deriving KB reached: a merge the live
  ;; KB performed off a route the rebuild does not travel is exactly the structure that
  ;; answers one way today and another after a restart.
  (v/assert kb '(context_denoting_function CxCalFn) 'CxUniverse)
  (v/assert kb '(unreifiable_function DatetimeFn) 'CxUniverse)
  (v/assert kb '(contextArgSubrelation CxCalFn 2 subintervalOf) 'CxUniverse)
  (let [year  '(CxCalFn CxMonad (DatetimeFn "2000"))
        month '(CxCalFn CxMonad (DatetimeFn "2000-01"))]
    (v/assert kb '(functionalInArg the_best 1) year)
    (v/assert kb '(the_best LaMulanaTwo) year)
    (v/assert kb '(the_best Silksong) month)
    (let [observe (fn [k]
                    {:from-january (sort (map (comp str '?x) (v/ask k '(the_best ?x) month)))
                     :merged?      (boolean (v/same-class? k 'LaMulanaTwo 'Silksong))
                     :rows         (set (map :sentence
                                             (v/sentexes-matching k '(the_best ?x) '?c)))})
          reading (one-reading! "a computed calendar edge's merge" kb observe)]
      (is (true? (:merged? reading)) "the two fillers are one thing, restarted too")
      (is (= ["LaMulanaTwo"] (:from-january reading))
          "and January reads one filler on both sides of the restart"))))
