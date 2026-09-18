;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.genlcx-sweep-test
  "What a `(genlCx sub super)` edge's merge sweep must still derive, now that it sweeps
  only the readers the edge changed the ancestor set of.

  `equate-under-context-edge-via` hands `context-down(sub)` to both twins' `derive`, so a
  reader outside that set is not visited.  The argument for that is in
  `derive-functional-equalities`' docstring; what a test can hold is the behaviour the
  argument predicts, and the cases here are the ones that separate the narrowing from a
  wrong one:

  - **a reader wired under `sub` before the edge, holding nothing of its own.**  This is
    the case `context-edge-reader-ancestors` names when it rejects `context-up(super)` as
    a candidate set.  Narrowing *candidates* that way loses the merge; narrowing *readers*
    keeps it, because that reader is in `context-down(sub)`.  A change that confuses the
    two fails here.
  - **a reader seeing a half `sub` cannot.**  The case that separates `context-down(sub)`
    from `sub` alone, and the only one here that does: a merge derived at `sub` is stored
    there and inherited by every reader below, so `same-class-in?` reads the same either
    way — unless the reader's own other branch holds a half `sub` never sees, which is
    what this one arranges.
  - **the same, three contexts deep.**  `context-down` is a closure, so a chain below
    `sub` is in it; a narrowing that took `sub`'s direct children would pass the case
    above and fail this one.
  - **a reader that an `except` has cut out of `context-down(sub)`.**  It cannot see the
    branch the edge joins, so it must *not* merge, while its unexcepted sibling in the
    same position must.  This is where a reader set read off the raw closure rather than
    the visibility-filtered one would show.
  - **a forced budget truncation.**  The budget bounds candidates and this bounds
    readers; the two are pinned here to not interact.

  `genlcx_sweep_cost_test` holds the other half — that the count does not grow with
  readers the edge did not reach, which is the property the narrowing exists for."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(defn- merged-at?
  "Does `ctx` see a merge reconciling `a` and `b`?  The scoped read, never the whole-KB
  `same-class?`: which contexts hold the merge is the question every case here asks."
  [kb a b ctx]
  (boolean (res/same-class-in? kb a b ctx)))

(defn- two-branch-kb
  "A KB with a functional mark and two mutually blind branches under CxUniverse, one
  holding each half of a clash — the shape every case below joins with one edge.
  Returns the KB; the caller wires whatever sits under `left` and asserts the edge."
  [kb left right pred a v1 v2]
  (v/assert kb (list 'functional pred) 'CxUniverse)
  (v/assert kb (list 'genlCx left 'CxUniverse) 'CxCore)
  (v/assert kb (list 'genlCx right 'CxUniverse) 'CxCore)
  (v/assert kb (list pred a v1) left)
  (v/assert kb (list pred a v2) right)
  kb)

(deftest a-reader-wired-under-sub-before-the-edge-still-gains-the-merge
  ;; The case `context-edge-reader-ancestors` rejects `context-up(super)` over: the reader
  ;; holds nothing itself, and both halves reach it only once the edge lands.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [parentOf Tom MumA MumB CxLeft CxRight CxSub CxRead]
      (two-branch-kb kb CxLeft CxRight parentOf Tom MumA MumB)
      (v/assert kb (list 'genlCx CxSub CxLeft) 'CxCore)
      (v/assert kb (list 'genlCx CxRead CxSub) 'CxCore)
      (is (not (merged-at? kb MumA MumB CxRead))
          "before the edge no context sees both halves")
      (v/assert kb (list 'genlCx CxSub CxRight) 'CxCore)
      (testing "the edge reaches the reader below sub, not only sub"
        (is (merged-at? kb MumA MumB CxRead))
        (is (merged-at? kb MumA MumB CxSub)))
      (testing "and no context whose ancestor set the edge left alone"
        (is (not (merged-at? kb MumA MumB CxLeft)))
        (is (not (merged-at? kb MumA MumB CxRight)))))))

(deftest a-reader-seeing-a-half-sub-cannot-derives-the-merge-itself
  ;; The case that says the swept set is `context-down(sub)` and not `sub` alone.  Every
  ;; other case here would survive a sweep narrowed to `sub`, because a merge derived
  ;; there is *stored* there and every reader below inherits it — `same-class-in?` cannot
  ;; tell the two apart.  Here it can: CxRead inherits from CxSub and from CxExtra, and
  ;; only CxExtra holds the first half, so the pair is jointly visible at CxRead and at no
  ;; context above it.  A sweep that skipped CxRead would leave nothing to inherit.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [parentOf Tom MumA MumB CxExtra CxRight CxSub CxRead]
      (v/assert kb (list 'functional parentOf) 'CxUniverse)
      (doseq [[lo hi] [[CxExtra 'CxUniverse] [CxRight 'CxUniverse] [CxSub 'CxUniverse]
                       [CxRead CxSub] [CxRead CxExtra]]]
        (v/assert kb (list 'genlCx lo hi) 'CxCore))
      (v/assert kb (list parentOf Tom MumA) CxExtra)
      (v/assert kb (list parentOf Tom MumB) CxRight)
      (is (not (merged-at? kb MumA MumB CxRead)) "no context sees both halves yet")
      (v/assert kb (list 'genlCx CxSub CxRight) 'CxCore)
      (testing "the reader below sub derives it, being the only context that sees the pair"
        (is (merged-at? kb MumA MumB CxRead)))
      (testing "and sub itself does not, never having seen the half in the reader's branch"
        (is (not (merged-at? kb MumA MumB CxSub)))))))

(deftest the-reader-chain-below-sub-is-a-closure-not-a-child-set
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [parentOf Tom MumA MumB CxLeft CxRight CxSub CxR1 CxR2 CxR3]
      (two-branch-kb kb CxLeft CxRight parentOf Tom MumA MumB)
      (v/assert kb (list 'genlCx CxSub CxLeft) 'CxCore)
      (doseq [[lo hi] [[CxR1 CxSub] [CxR2 CxR1] [CxR3 CxR2]]]
        (v/assert kb (list 'genlCx lo hi) 'CxCore))
      (v/assert kb (list 'genlCx CxSub CxRight) 'CxCore)
      (is (every? #(merged-at? kb MumA MumB %) [CxR1 CxR2 CxR3])
          "three deep below sub, all of them in context-down(sub)"))))

(deftest an-excepted-reader-is-outside-the-swept-set-and-does-not-merge
  ;; `context-down` filters by each candidate's own forward walk, so a reader that hides
  ;; its own edge to `sub` drops out — and must, since it cannot see the joined branch.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [parentOf Tom MumA MumB CxLeft CxRight CxSub CxHidden CxPlain]
      (two-branch-kb kb CxLeft CxRight parentOf Tom MumA MumB)
      (v/assert kb (list 'genlCx CxSub CxLeft) 'CxCore {:strength :monotonic})
      (v/assert kb (list 'genlCx CxPlain CxSub) 'CxCore {:strength :monotonic})
      (let [edge (v/assert kb (list 'genlCx CxHidden CxSub) 'CxCore {:strength :monotonic})]
        (is (contains? (set (tax/context-down (reasoning/taxonomy kb) CxSub)) CxHidden)
            "in the swept set before the except")
        (v/assert kb (list 'except (sx/sentex-handle edge)) CxHidden {:strength :monotonic})
        (is (not (contains? (set (tax/context-down (reasoning/taxonomy kb) CxSub)) CxHidden))
            "and out of it after"))
      (v/assert kb (list 'genlCx CxSub CxRight) 'CxCore {:strength :monotonic})
      (testing "the excepted reader cannot see the joined branch, so it holds no merge"
        (is (not (merged-at? kb MumA MumB CxHidden))))
      (testing "its unexcepted sibling in the same position does"
        (is (merged-at? kb MumA MumB CxPlain))))))

(deftest the-candidate-budget-and-the-reader-set-do-not-interact
  ;; The budget cuts a prefix of the FACTS; the reader set cuts the CONTEXTS each
  ;; surviving fact is re-derived at.  A cut budget must still derive one merge per
  ;; candidate it kept, and still file exactly one truncation notice.
  (let [pairs 12
        cut   4]
    (doseq [[budget expected-merges expected-notices]
            [[cut cut 1] [(* 4 pairs) pairs 0]]]
      (tu/with-neutral-kb [kb tu/fresh]
        (tu/with-terms [parentOf CxLeft CxRight CxSub CxRead]
          (binding [tax/*exposure-instance-budget* budget]
            (v/assert kb (list 'functional parentOf) 'CxUniverse)
            (v/assert kb (list 'genlCx CxLeft 'CxUniverse) 'CxCore)
            (v/assert kb (list 'genlCx CxRight 'CxUniverse) 'CxCore)
            (v/assert kb (list 'genlCx CxSub CxLeft) 'CxCore)
            (v/assert kb (list 'genlCx CxRead CxSub) 'CxCore)
            (let [kids (vec (for [_ (range pairs)]
                              [(tu/fresh-term :individual "Kid")
                               (tu/fresh-term :individual "MumA")
                               (tu/fresh-term :individual "MumB")]))]
              (doseq [[k a b] kids]
                (v/assert kb (list parentOf k a) CxLeft)
                (v/assert kb (list parentOf k b) CxRight))
              (v/assert kb (list 'genlCx CxSub CxRight) 'CxCore)
              (testing (str "budget " budget ": merges the candidates it kept")
                (is (= expected-merges
                       (count (filter (fn [[_ a b]] (merged-at? kb a b CxRead)) kids)))))
              (testing (str "budget " budget ": files one notice per cut, and none when uncut")
                (is (= expected-notices
                       (count (filter #(= :context-edge-exposure-truncated (:violation %))
                                      (v/violations kb)))))))))))))
