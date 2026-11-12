;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.vantage-differential-test
  "The `:fan` and `:post-hoc` strategies return the same answers and witnesses over
  generated lattices holding the three filters post-hoc restores at the placement: a `genl`
  edge in one context that lets a fact in another answer, an `except`, and an equality
  merge (docs/contexts.md).  Every other world is constraint-only, so a membership the
  argument-type prover infers is stored nowhere and post-hoc places it by its usage and
  declaration.  One seed, printed with any failure.  The run also asserts that
  the goals found answers and that post-hoc ran on most of them, so a generator or a domain
  that narrowed to nothing fails."
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
    ;; subsumption ingredient — and sometimes the same edge stated in a second context,
    ;; which gives a placement two routes
    (v/assert kb (list (types 0) (inds (rint r 3))) (ctxs (rint r nctx)))
    (v/assert kb (list 'genl (types 0) (types 1)) (ctxs (rint r nctx)))
    (when (zero? (rint r 2))
      (v/assert kb (list 'genl (types 0) (types 1)) (ctxs (rint r nctx))))
    ;; an argument-type declaration, sometimes: `ArgTypeProver` applies only to an
    ;; individual, so a type literal reaches it once a join binds it
    (when (zero? (rint r 2))
      (v/assert kb (list 'arg (preds 0) 1 (types 0)) (ctxs (rint r nctx))))
    ;; a context no edge wires, sometimes, holding a usage and a declaration of its own:
    ;; it is a reader only of what it holds
    (when (zero? (rint r 2))
      (v/assert kb (list (preds 1) (inds 2) (inds 0)) 'CxGLone)
      (v/assert kb (list 'arg (preds 1) 1 (types 1)) 'CxGLone))
    ;; an except on one stored fact, sometimes
    (when (zero? (rint r 3))
      (when-let [h (:id (first (v/sort-by-content (juxt :sentence :context)
                                                  (v/sentexes-matching kb (list (preds 0) '?a '?b)
                                                                       '?ctx))))]
        (v/assert kb (list 'except (list 'sentexHandle h)) (ctxs (rint r nctx)))))
    ;; an equality merge, sometimes, shaped because a uniform draw does not find the
    ;; shape: a fact stated above the merge before it, and a second ingredient that drags
    ;; the placement to or below the merge, where the reader sees the fact and its twin
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
           ;; a goal naming the merged spelling, which a reader above the merge asks as
           ;; written
           (list (preds 1) (inds 1) '?y)
           (list (preds 0) '?a (inds 0))
           ;; `genl` walks the cached closure, outside post-hoc's domain, and a ground
           ;; membership reaches the argument-type prover, inside it
           (list 'genl (types 0) '?x)
           (list (types 1) (inds 0))
           (list (types 1) (inds 2))
           (list (types 0) (inds 1))]
          [[(list (preds 0) '?a '?b) (list (preds 1) '?b '?c)]
           [(list (preds 0) '?a '?b) (list (types 1) '?a)]
           [(list (types 1) '?x) (list (preds 1) '?x '?y)]
           ;; no shared variable on purpose: the join exists to force a placement that
           ;; sees both ingredients, which is what puts the reader below the merge
           [(list (preds 1) '?a '?b) (list (preds 0) '?c '?d)]
           ;; three literals: the bail fires at the second stage at the earliest, so only a
           ;; third literal reduces over what it handed back
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
      (tu/with-cleared-kb [kb #(tu/isolated-fresh)]
        (let [in-reading (if (odd? w) #(tu/without-entailing (%)) #(%))]
          (tu/load-starter! kb)
          (in-reading
           (fn []
             (doseq [goal (build-world! kb r)
                     ;; both spellings of the joint reading, which attach the witness differently
                     ctx  ['CxInference '?home]
                     ;; both sides of the bail: at 20 a generated world never outgrows its
                     ;; budget, and at 1 nearly every join abandons
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
                          "\n  post-hoc only: " (pr-str (sort-by str (remove fan post))))))))))))
    (testing "the generator produced worlds that actually answer"
      (is (< 20 @answered)
          (str "only " @answered " answers over " n
               " worlds — a generator drifted into empty KBs agrees with itself trivially")))
    (testing "and post-hoc actually ran on most of them"
      (is (< @skipped @ran)
          (str "post-hoc ran on " @ran " goals and was skipped on " @skipped
               " — the comparison is mostly the fan against itself")))))

(deftest fan-and-post-hoc-agree-over-generated-lattices
  ;; four worlds at :default; `…-over-many-generated-lattices` runs all of `worlds`
  (lattices-agree 4))

(deftest ^:slow fan-and-post-hoc-agree-over-many-generated-lattices
  (lattices-agree worlds))

(deftest post-hoc-places-a-covered-route-where-an-except-hides-the-covering-edge
  ;; `(genl ta tb)` in CxG and again in CxS below it, `(ta Fido)` in CxR below CxS.  The
  ;; CxG edge's route covers the CxS edge's, and CxR excepts the CxG edge, so CxR reads
  ;; `(tb Fido)` through the CxS edge alone.  The control excepts the CxS edge instead.
  (tu/with-cleared-kb [kb #(tu/isolated-fresh)]
    (tu/load-starter! kb)
    (doseq [hide [:general :specific] open? [false true]]
      (tu/with-terms [CxG CxS CxR ta tb Fido]
        (v/assert kb (list 'genlCx CxG 'CxUniverse) 'CxUniverse)
        (v/assert kb (list 'genlCx CxS CxG) 'CxUniverse)
        (v/assert kb (list 'genlCx CxR CxS) 'CxUniverse)
        (let [hg   (v/assert kb (list 'genl ta tb) CxG)
              hs   (v/assert kb (list 'genl ta tb) CxS)
              goal (list tb (if open? '?x Fido))
              run  (fn [s] (binding [vantage/*strategy* s]
                             (vantage/answers kb [goal] #(v/query kb goal %) {})))]
          (v/assert kb (list ta Fido) CxR)
          (v/assert kb (list 'except (list 'sentexHandle (if (= :general hide) hg hs))) CxR)
          (let [fan (run :fan) post (run :post-hoc)]
            (is (= :post-hoc (:strategy post)) (pr-str hide goal))
            (is (= #{CxR}
                   (set (map vantage/witness-key (:answers fan)))
                   (set (map vantage/witness-key (:answers post))))
                (pr-str hide goal))))))))

(deftest post-hoc-hands-a-rule-expanding-read-back-to-the-fan
  (tu/with-cleared-kb [kb #(tu/isolated-fresh)]
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
