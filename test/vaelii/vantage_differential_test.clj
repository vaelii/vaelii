;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.vantage-differential-test
  "**The two `CxInference` strategies must answer alike, or one of them is wrong.**

  `:fan` asks every reader the ordinary scoped question and is sound by construction —
  whatever it returns, a real vantage really said. `:post-hoc` asks once unscoped and
  reconstructs where the answer could be read from, which is faster and is the one that can
  be wrong: it sees a KB with no context filter, no `except` filter and no retired-spelling
  filter, and has to put all three back by reasoning about the *placement* instead of the
  read. Every hand-written case in `query_context_test` is one way it got that wrong.

  Three hand-written cases prove three points. This proves the property, over generated
  lattices: random contexts, random `genlCx` edges between them, facts scattered across
  them, and the three complications that make the two strategies come apart — a `genl`
  edge in one context that lets a fact in another answer a goal, a visibility `except`, and
  an equality merge. Goals are single literals and two-literal joins, since the joint
  reading only bites where a join does.

  Deterministic: one seed, printed with any failure, so a red run reproduces exactly.
  This is `matches_hierarchical_test`'s shape — an oracle and a faster path that must not
  disagree — applied a layer up.

  **A generated world that answers nothing proves nothing**, so the run asserts that the
  goals found real answers overall; a generator that drifted into producing empty KBs
  would otherwise report green forever."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.vantage :as vantage]
            [vaelii.test-util :as tu])
  (:import (java.util Random)))

(def ^:private seed 20260822)
(def ^:private worlds 14)

(defn- rint [^Random r n] (.nextInt r (int n)))

(defn- build-world!
  "A small random world in `kb`: a context lattice, facts scattered over it, and the three
  complications. Returns the goals to ask of it."
  [kb ^Random r]
  (let [nctx  (+ 2 (rint r 3))
        ctxs  (mapv #(symbol (str "CxG" %)) (range nctx))
        preds (mapv #(symbol (str "gp" %)) (range 2))
        types [(symbol "ga_t") (symbol "gb_t")]
        inds  (mapv #(symbol (str "GI" %)) (range 3))]
    ;; every generated context hangs under CxUniverse, then a random extra edge or two
    ;; between them — enough for readers that see several, and for readers that see none
    ;; of each other
    (doseq [c ctxs] (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
    (dotimes [_ (rint r 3)]
      (let [a (rint r nctx) b (rint r nctx)]
        ;; sub -> super, low index above high, so the lattice stays acyclic
        (when (< a b)
          (v/assert kb (list 'genlCx (ctxs b) (ctxs a)) 'CxUniverse))))
    ;; facts
    (dotimes [_ (+ 2 (rint r 4))]
      (v/assert kb (list (preds (rint r 2)) (inds (rint r 3)) (inds (rint r 3)))
                (ctxs (rint r nctx))))
    ;; a type membership plus a genl edge, usually in a different context — the
    ;; subsumption ingredient
    (v/assert kb (list (types 0) (inds (rint r 3))) (ctxs (rint r nctx)))
    (v/assert kb (list 'genl (types 0) (types 1)) (ctxs (rint r nctx)))
    ;; An argument-type declaration, sometimes.  Its point is not the declaration but what
    ;; it does to the *domain gate*: `ArgTypeProver` gates on its argument being an
    ;; individual, so a type literal is fact-only as written and stops being fact-only once
    ;; a join binds it.  Without one of these in the world, no generated goal can leave
    ;; post-hoc's domain halfway through, and the re-ask on the substituted literal is
    ;; never exercised.
    (when (zero? (rint r 2))
      (v/assert kb (list 'arg (preds 0) 1 (types 0)) (ctxs (rint r nctx))))
    ;; an except on one stored fact, sometimes
    (when (zero? (rint r 3))
      (when-let [h (:id (first (v/sort-by-content (juxt :sentence :context)
                                                  (v/sentexes-matching kb (list (preds 0) '?a '?b)
                                                                       '?ctx))))]
        (v/assert kb (list 'except (list 'sentexHandle h)) (ctxs (rint r nctx)))))
    ;; An equality merge, sometimes — and *deliberately shaped*, because the structure that
    ;; makes the two strategies disagree is narrow and a uniform random draw does not find
    ;; it.  Supersession is per reader, so the divergence needs a fact stated ABOVE a merge
    ;; (stated earlier, so it is not rewritten on the way in) and a placement dragged to or
    ;; below the merge by a second ingredient — only then does the reader see both the fact
    ;; and its twin and retire one spelling that an unscoped pass keeps.
    (when (zero? (rint r 3))
      (let [up  (ctxs 0)
            low (ctxs (max 1 (rint r nctx)))]
        (v/assert kb (list 'genlCx low up) 'CxUniverse)
        (v/assert kb (list (preds 1) (inds 1) (inds 1)) up)     ; above the merge, first
        (v/assert kb (list (preds 0) (inds 2) (inds 2)) low)    ; drags placement down
        (v/assert kb (list 'sameAs (inds 0) (inds 1)) low)))
    (into [(list (types 1) '?x)
           (list (preds 0) '?a '?b)
           (list (preds 1) '?a '?b)
           ;; **A goal naming the merged spelling.**  Equality rewrites a goal by the merges
           ;; *its reader* sees, and post-hoc matches one rewritten globally — so a reader
           ;; above the merge is one that could not have asked this question at all.  Every
           ;; other goal here spells a term no `sameAs` touches, which is why the divergence
           ;; hid: the shape needs the merged name in the goal, not only in the store.
           (list (preds 1) (inds 1) '?y)
           (list (preds 0) '?a (inds 0))
           ;; Two goals the stored-fact prover is NOT alone on, so the domain gate is
           ;; exercised rather than assumed: `genl` walks the cached closure (a two-hop
           ;; answer is in no stored sentex), and a ground membership reaches the argument
           ;; -type prover.  Both must come back through the fan.
           (list 'genl (types 0) '?x)
           (list (types 1) (inds 0))]
          [[(list (preds 0) '?a '?b) (list (preds 1) '?b '?c)]
           [(list (preds 0) '?a '?b) (list (types 1) '?a)]
           [(list (types 1) '?x) (list (preds 1) '?x '?y)]
           ;; no shared variable on purpose: the join exists to force a placement that
           ;; sees both ingredients, which is what puts the reader below the merge
           [(list (preds 1) '?a '?b) (list (preds 0) '?c '?d)]
           ;; **Three literals.**  The bail fires at the second stage at the earliest, so
           ;; only a third literal reduces over what the bail handed back — the one shape
           ;; that turned an abandoned join into a thrown exception rather than a fan.
           [(list (preds 0) '?a '?b) (list (preds 1) '?b '?c) (list (types 1) '?a)]
           [(list (types 1) '?x) (list (preds 0) '?x '?y) (list (preds 1) '?y '?z)]])))

(defn- lattices-agree
  "The property over the first `n` worlds `seed` generates."
  [n]
  (let [r (Random. seed)
        answered (atom 0)
        ran      (atom 0)
        skipped  (atom 0)]
    (dotimes [w n]
      (let [kb (tu/isolated-fresh)]
        (tu/load-starter! kb)
        (let [goals (build-world! kb r)]
          (doseq [goal goals
                  ;; **both spellings of the joint reading**, since they attach the witness
                  ;; differently — `CxInference` beside the bindings under `:context`, a
                  ;; variable unified into itself — and the variable is the one every short
                  ;; arity takes, so it is the path most reads go down.
                  ctx  ['CxInference '?home]
                  ;; **Both sides of the bail.**  At 20 a generated world never outgrows its
                  ;; budget, so the abandoned path — and the sentinel's trip back out
                  ;; through three reduces — went untested by construction.  At 1 nearly
                  ;; every join abandons, and the fan has to answer the same thing.
                  rpr  [20 1]]
            (let [fan  (set (binding [vantage/*strategy* :fan
                                      vantage/*rows-per-reader* rpr]
                              (v/query kb goal ctx)))
                  post (set (binding [vantage/*strategy* :post-hoc
                                      vantage/*rows-per-reader* rpr]
                              (v/query kb goal ctx)))]
              (swap! answered + (count fan))
              (swap! (if (vantage/placeable? kb (if (vector? goal) goal [goal])) ran skipped) inc)
              (is (= fan post)
                  (str "world " w " (seed " seed "), goal " (pr-str goal) " at " ctx
                       ", rows-per-reader " rpr
                       "\n  fan only:      " (pr-str (sort-by str (remove post fan)))
                       "\n  post-hoc only: " (pr-str (sort-by str (remove fan post))))))))))
    (testing "the generator produced worlds that actually answer"
      (is (< 20 @answered)
          (str "only " @answered " answers over " n
               " worlds — a generator drifted into empty KBs agrees with itself trivially")))
    (testing "and post-hoc actually ran on most of them"
      ;; The failure this guards is a comparison that proves nothing.  `placeable?` hands
      ;; a goal it cannot place back to the fan, so a domain that quietly narrowed to
      ;; nothing would make every row above compare the fan with itself — green forever,
      ;; and testing no second implementation at all.
      (is (< @skipped @ran)
          (str "post-hoc ran on " @ran " goals and was skipped on " @skipped
               " — the comparison is mostly the fan against itself")))))

(deftest fan-and-post-hoc-agree-over-generated-lattices
  ;; four worlds at :default, 192 answers from them; `…-over-many-generated-lattices`
  ;; runs all of `worlds`
  (lattices-agree 4))

(deftest ^:slow fan-and-post-hoc-agree-over-many-generated-lattices
  (lattices-agree worlds))

(deftest post-hoc-hands-a-rule-expanding-read-back-to-the-fan
  ;; The domain boundary, asserted rather than assumed.  An antecedent fact is not one of
  ;; `goals`, so its context never reaches a placement — post-hoc cannot answer a read that
  ;; expands rules, and `answers` says so rather than answering wrongly.
  (let [kb (tu/isolated-fresh)]
    (tu/load-starter! kb)
    (v/assert kb '(genlCx CxRA CxUniverse) 'CxUniverse)
    (v/assert kb '(gq_t GRex) 'CxRA)
    (v/assert-rule kb ['(gq_t ?x)] '(gr_t ?x) 'CxRA)
    (let [goal '(gr_t ?x)]
      (is (seq (v/query kb goal 'CxRA {:max-depth 2})) "precondition: the rule answers it")
      (binding [vantage/*strategy* :post-hoc]
        (let [{:keys [strategy]} (vantage/answers kb [goal] #(v/query kb goal % {:max-depth 2})
                                                  {:expands-rules? true})]
          (is (= :fan strategy) "asked for post-hoc, handed back the fan, and says so"))))))
