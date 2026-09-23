;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.laziness-test
  "The retrieval stack's laziness contract: **per-result work is paid per result
  consumed**.

  `vaelii.impl.levels` states it in its ns docstring and `res/lazy-mapcat` exists
  for nothing else — chunked `mapcat` would expand every context and every subtype,
  each its own trie walk, before handing back the first result.  That is a *cost*
  claim, and cost claims rot silently: an eager implementation returns exactly the
  same answers, so every content test in the suite stays green while the engine
  quietly does N times the work.  The proof of that: replacing both `lazy-mapcat`
  calls in `resolution.clj` with `clojure.core/mapcat` passed the whole suite.

  So these tests count side effects rather than results.  Each one instruments the
  expensive call at a probe point (`raw-match` = one trie probe per branch,
  `provers/solve-goal-with` = one closure computation), consumes exactly **one**
  result, and asserts the count is far below what consuming all of them costs.

  The margin matters and is not arbitrary.  An eager `mapcat` is `(apply concat (map
  f coll))`, and `apply` reads four elements off the mapped seq to fill `concat`'s
  arglist — so *four* branches expand before the first result, and more if the source
  is chunked.  Every threshold below is therefore set at 2, which a lazy
  implementation meets and an eager one cannot.

  **The other half of the contract is where laziness must *not* reach**: a seq built
  under a thread binding realizes after that binding has popped, so a layer that hands
  one back loses the scope it was computed in.  `res/blind-seq` says what that costs
  when the binding is a flag; the last section here measures it where the binding is a
  cache (`inherit/with-memo`), which is the structure that stays silent because the answers
  are identical either way."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.levels :as levels]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- measuring ----------------------------------------------------------

(defn- calls
  "Count invocations of `v` while `run` consumes a lazy seq, once with `first` and
  once with `dorun`; returns `[one all]`.  `run` takes the consuming function so the
  *same* expression is built twice — a seq realized once and re-consumed would cache
  its work and measure nothing."
  [v run]
  (let [n (atom 0), orig @v]
    (with-redefs-fn {v (fn [& args] (swap! n inc) (apply orig args))}
      (fn []
        (run first)
        (let [one @n]
          (reset! n 0)
          (run dorun)
          [one @n])))))

;; ---- levels 3 and 4: the genlCx fan-out ----------------------------
;;
;; Catches: an eager walk of the context up-closure at EITHER of its two call sites.
;; They are separate code — level 3 fans out itself (`levels.clj:185`) because it must
;; skip the subtype walk that level 4 adds, and level 4 inherits `res/matches-visible`
;; (`resolution.clj:180`) — so the test runs both, and a mutation of one is not masked by
;; the other still being lazy.
;;
;; The pre-existing coverage (levels_test.clj:252) reaches neither: its fixture puts
;; every fact in ONE context, so the fan-out has a single branch and eager and lazy
;; are indistinguishable.  Here the goal is visible from forty contexts, every one of
;; which would answer it, so a lazy walk stops at the first.

(tu/deftest-kb one-result-expands-one-context-not-the-whole-up-closure
  (tu/with-terms [parentOf Tom CxSub]
    (let [supers (vec (repeatedly 40 #(tu/tmp-ctx "Super")))
          goal   (list parentOf Tom '?k)]
      (doseq [c supers]
        (v/assert kb (list 'genlCx CxSub c) 'CxUniverse {:chain? false})
        (v/assert kb (list parentOf Tom (tu/tmp-ind "Kid")) c {:chain? false}))
      ;; the view context is in its own up-closure, so populate it too — a barren
      ;; branch makes the measurement depend on set iteration order, not on laziness
      (v/assert kb (list parentOf Tom (tu/tmp-ind "Kid")) CxSub {:chain? false})
      ;; a BINARY goal, so `match-pattern` short-circuits to `raw-match` and the only
      ;; fan-out in play is over contexts.  Bind the hierarchical path off: this pins the
      ;; *reference fan-out*'s laziness (level 4's default is the set-algebra path, which
      ;; filters contexts in memory rather than fanning — its own laziness is below).
      (binding [res/*hierarchical-retrieval* false]
        (doseq [level [3 4]]
          (let [[one all] (calls #'res/raw-match
                                 (fn [consume] (consume (v/lookup kb level goal CxSub))))]
            (testing (str "level " level ": the up-closure really is forty-one contexts wide")
              (is (= 41 all)))
            (testing (str "level " level ": one result costs one context probe, not forty-one")
              (is (= 1 one)
                  (str "level " level " expanded " one " contexts to produce one result, out of "
                       all " — an eager mapcat expands at least four")))))))))

;; ---- level 4: the genl subtype fan-out ----------------------------------
;;
;; Catches: `res/match-pattern` (resolution.clj:168) using `clojure.core/mapcat` over
;; the spec closure.  It needs a fixture of its own because `match-pattern` fans out
;; only for a UNARY goal — query a binary one and this branch is never entered.

(tu/deftest-kb one-result-expands-one-subtype-not-the-whole-spec-closure
  (tu/with-terms [animal CxStory]
    (let [goal (list animal '?x)]
      (doseq [_ (range 40)]
        (let [t (tu/tmp-type "dog")]
          (v/assert kb (list 'genl t animal) CxStory {:chain? false})
          (v/assert kb (list t (tu/tmp-ind "Muffet")) CxStory {:chain? false})))
      ;; `animal` is in its own spec closure — populate it, for the reason above
      (v/assert kb (list animal (tu/tmp-ind "Muffet")) CxStory {:chain? false})
      ;; the reference fan-out (level 4's default is the set-algebra path — see below)
      (binding [res/*hierarchical-retrieval* false]
        (let [[one all] (calls #'res/raw-match
                               (fn [consume] (consume (v/lookup kb 4 goal CxStory))))]
          (testing "the spec closure really is forty-one subtypes wide"
            (is (= 41 all)))
          (testing "one result costs one subtype probe, not forty-one"
            (is (= 1 one)
                (str "expanded " one " subtypes to produce one result, out of " all))))))))

;; ---- both axes at once ---------------------------------------------------
;;
;; The two `lazy-mapcat`s nest: `matches-visible` maps over contexts, and each
;; context's `match-pattern` maps over subtypes.  An eager pair is quadratic, so this
;; is the structure that shows what the laziness is actually worth — and it catches a
;; regression in *either* call site, including one that only reintroduces eagerness
;; on the inner axis.

(tu/deftest-kb the-context-and-subtype-fan-outs-do-not-multiply
  (tu/with-terms [animal CxSub]
    (let [goal (list animal '?x)
          typs (vec (repeatedly 12 #(tu/tmp-type "dog")))
          ctxs (vec (repeatedly 12 #(tu/tmp-ctx "Super")))]
      (doseq [c ctxs]
        (v/assert kb (list 'genlCx CxSub c) 'CxUniverse {:chain? false}))
      (doseq [t typs]
        (v/assert kb (list 'genl t animal) CxSub {:chain? false}))
      ;; EVERY cell of the cross product is populated — including the view context
      ;; itself (which is in its own up-closure) and `animal` itself (which is in its
      ;; own spec closure).  Leave either empty and the branch order, which is set
      ;; iteration order over gensyms, decides whether a lazy walk pays for a whole
      ;; barren row: the test then passes or fails by luck rather than by laziness.
      (doseq [c (conj ctxs CxSub), t (conj typs animal)]
        (v/assert kb (list t (tu/tmp-ind "Muffet")) c {:chain? false}))
      ;; the reference fan-out (level 4's default is the set-algebra path — see below)
      (binding [res/*hierarchical-retrieval* false]
        (let [[one all] (calls #'res/raw-match
                               (fn [consume] (consume (v/lookup kb 4 goal CxSub))))]
          (testing "the full cross product is what taking every result costs"
            (is (= 169 all)))
          (testing "taking one result costs one cell of it"
            (is (= 1 one)
                (str "expanded " one " of " all " (context x subtype) branches for one result"))))))))

;; ---- the default set-algebra path walks its posting lazily --------------
;;
;; With `*hierarchical-retrieval*` on (the default), a positive literal is answered by
;; leading with the argument-root posting and filtering the predicate/context
;; hierarchies in memory (`res/matches-hierarchical`) — no fan-out over the two
;; closures at all.  `lead-candidates` hands the posting back by reference and only
;; walks it as results are consumed, so an existence check must not realize the whole
;; posting.  This is the laziness that lets it stay the default for existence checks;
;; the fan-out tests above bind the flag off to pin the reference path instead.

(tu/deftest-kb the-set-algebra-path-walks-its-posting-lazily
  (tu/with-terms [likes Anchor CxStory]
    (let [goal (list likes Anchor '?x)]
      (doseq [_ (range 60)]
        (v/assert kb (list likes Anchor (tu/tmp-ind "Kid")) CxStory {:chain? false}))
      ;; jtms/in? runs once per posting entry the keep visits — the per-candidate call site.
      ;; Pin the flag on: this test is about the set-algebra path (as the fan-out tests
      ;; above pin it off), independent of the global default.
      (binding [res/*hierarchical-retrieval* true]
        (let [[one all] (calls #'jtms/in?
                               (fn [consume] (consume (v/lookup kb 4 goal CxStory))))]
          (testing "the argument-root posting really is sixty facts wide"
            (is (= 60 all)))
          (testing "one result walks the posting only to the first match, not all sixty"
            (is (<= one 2)
                (str "the set-algebra path realized " one " of " all
                     " posting entries for one result"))))))))

;; ---- level 2: the symmetric mirror --------------------------------------
;;
;; Catches: `res/raw-match` (resolution.clj:153) using `concat` instead of `lazy-cat`.
;; The mirrored probe of a symmetric predicate is a second full index lookup, and the
;; `seen` set that dedupes it realizes *every* direct hit to build itself — so an
;; eager mirror charges a consumer answered by the direct probe for both.

(tu/deftest-kb the-symmetric-mirror-probe-is-deferred-until-the-direct-hits-run-out
  (tu/with-terms [siblingOf CxStory]
    (v/assert kb (list 'symmetric siblingOf) CxStory)
    (let [Anchor (tu/tmp-ind "Anchor")
          goal   (list siblingOf Anchor '?x)]
      (doseq [_ (range 40)]
        (v/assert kb (list siblingOf Anchor (tu/tmp-ind "Sib")) CxStory {:chain? false}))
      (let [[one all] (calls #'res/match-one
                             (fn [consume] (consume (v/lookup kb 2 goal CxStory))))]
        (testing "draining the seq does probe both argument orders"
          (is (= 2 all)))
        (testing "one result probes only the direct order"
          (is (= 1 one) "the mirror ran before the direct hits were exhausted"))))))

;; ---- level 5: the transitive closure ------------------------------------
;;
;; Catches: `levels/level-5` (levels.clj:206) using `concat` instead of `lazy-cat`.
;; Its docstring concedes that a closure has no partial answer — computing one link
;; computes the fixpoint — and claims level 4's stored matches "stream first and
;; answer alone if they suffice".  That claim is what makes the concession tolerable,
;; and nothing tested it: level 5 was tested for content only.
;;
;; `provers/solve-goal-with` is the right probe point because it is not itself lazy at the
;; top — it filters for a complete prover and, finding one, calls its `solve`
;; directly.  So *reaching* it is already paying for the closure.

(tu/deftest-kb level-5-does-not-force-the-closure-when-a-stored-match-answers
  (tu/with-terms [ancestorOf Ann Bob Carol CxStory]
    (v/assert kb (list 'transitive ancestorOf) CxStory)
    (v/assert kb (list ancestorOf Ann Bob) CxStory)     ; level 4 answers from this
    (v/assert kb (list ancestorOf Bob Carol) CxStory)   ; only the closure reaches Carol
    (let [goal (list ancestorOf Ann '?x)
          [one all] (calls #'provers/solve-goal-with
                           (fn [consume] (consume (v/lookup kb 5 goal CxStory))))]
      (testing "draining the seq does run the closure"
        (is (= 1 all)))
      (testing "the stored edge answers first, and the closure is never entered"
        (is (zero? one)
            "taking one result forced the transitive prover"))
      (testing "and the closure still contributes when the seq is drained"
        (is (= #{Bob Carol}
               (set (map #(get (:bindings %) '?x) (v/lookup kb 5 goal CxStory)))))))))

;; ---- escalate ------------------------------------------------------------
;;
;; Catches a REAL BUG, now fixed in levels.clj:263.  `escalate` climbed with
;; `(first (keep f (range floor 8)))`, and `(range 2 8)` is a **chunked** seq: `keep`'s
;; chunked path runs `f` over the whole chunk before yielding anything, so a goal
;; answered at level 2 still ran levels 3, 4, 5, 6 AND 7 — backward chaining
;; included.  The returned `:tried` said `[2]` the entire time, so the report was
;; actively misleading about what had been paid.  Nothing caught it because every
;; level returns the same answers whether or not it was consulted.

(tu/deftest-kb escalate-stops-running-levels-at-the-first-one-that-answers
  (tu/with-terms [dog Muffet CxStory]
    (v/assert kb (list dog Muffet) CxStory)
    (let [ran  (atom [])
          orig levels/lookup]
      (with-redefs [levels/lookup (fn [k l g c] (swap! ran conj l) (orig k l g c))]
        (let [r (v/escalate kb (list dog Muffet) CxStory)]
          (testing "the goal is answered at the query floor"
            (is (= 2 (:level r))))
          (testing ":tried is not a summary of the climb — it IS the climb"
            (is (= (:tried r) @ran)
                (str "reported trying " (:tried r) " but ran " @ran))
            (is (= [2] @ran))))))))

(tu/deftest-kb escalate-runs-each-level-once-on-the-way-up
  ;; The other half of the same invariant: a goal only backchaining answers must climb
  ;; every level, exactly once each, and stop at 7 rather than over-running.
  (tu/with-terms [parentOf grandparentOf Tom Bob Ann CxStory]
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                   (list grandparentOf '?x '?z) CxStory {:direction :backward})
    (v/assert kb (list parentOf Tom Bob) CxStory)
    (v/assert kb (list parentOf Bob Ann) CxStory)
    (let [ran  (atom [])
          orig levels/lookup]
      (with-redefs [levels/lookup (fn [k l g c] (swap! ran conj l) (orig k l g c))]
        (let [r (v/escalate kb (list grandparentOf Tom '?who) CxStory)]
          (is (= 7 (:level r)))
          (is (= [2 3 4 5 6 7] @ran))
          (is (= (:tried r) @ran)))))))

;; ---- the results seq escalate hands back --------------------------------
;;
;; `escalate` documents `:results` as "the lazy seq from that level", i.e. the climb
;; costs one result per level tried and the caller pays for the rest only if it wants
;; them.  Seq'ing a level to test it for emptiness must not drain it.

(tu/deftest-kb escalate-returns-a-lazy-results-seq-it-has-not-drained
  (tu/with-terms [parentOf Tom CxStory]
    (let [goal (list parentOf Tom '?k)]
      (doseq [_ (range 40)]
        (v/assert kb (list parentOf Tom (tu/tmp-ind "Kid")) CxStory {:chain? false}))
      (let [n     (atom 0)
            orig  @#'res/match-one]
        (with-redefs-fn {#'res/match-one
                         (fn [k s c] (swap! n inc) (orig k s c))}
          (fn []
            (let [r (v/escalate kb goal CxStory)]
              (testing "finding the level probed the index once, not once per answer"
                (is (= 2 (:level r)))
                (is (= 1 @n)))
              (testing "and the results are all still there when asked for"
                (is (= 40 (count (:results r))))))))))))

;; ---- the budget entry point spends the stream one result at a time --------------
;;
;; `budget/collect` reads `rest` rather than `next` so a cap of n pulls exactly n, and
;; docs/anytime.md says so.  That claim rests on something the fn cannot check: `seq` on
;; a **chunked** source realizes thirty-two elements whatever the cap says, so a single
;; `mapv` or a vector anywhere in the answer stream would make the entry point pay a chunk per
;; ask while still returning the right n.  `provers/project` ends in `distinct` (not
;; chunk-aware) and every layer under it walks its postings a result at a time, which is
;; what makes the claim exact — measured here at the same per-candidate call site.

(tu/deftest-kb a-capped-ask-pays-for-the-cap-and-not-for-a-chunk
  (tu/with-terms [likes Anchor CxStory]
    (doseq [_ (range 60)]
      (v/assert kb (list likes Anchor (tu/tmp-ind "Kid")) CxStory {:chain? false}))
    (let [goal (list likes Anchor '?x)
          runs (fn [b] (let [n (atom 0), orig @#'jtms/in?]
                         (with-redefs-fn {#'jtms/in? (fn [& args] (swap! n inc) (apply orig args))}
                           (fn [] [(v/ask-within kb goal CxStory b) @n]))))
          [capped few] (runs {:max-results 2})
          [whole all]  (runs {})]
      (testing "the cap is honoured, and the extent really is sixty wide"
        (is (= 2 (:count capped)))
        (is (= :capped (:status capped)))
        (is (= 60 (:count whole)))
        (is (< 50 all)))
      (testing "and two answers cost two, not a chunk of thirty-two"
        (is (< few (quot all 4))
            (str "a two-answer cap cost " few " belief reads against " all
                 " for the whole extent — a chunked answer stream pays thirty-two"
                 " whatever the cap says"))))))

;; ---- laziness escaping a binding: the preservation memo -------------------
;;
;; `inherit/with-memo` holds one cache of `positions` and `reach` for the length of one
;; question, and each layer under it builds a seq.  Handed back unrealized, that seq
;; realizes with the binding frame popped: every `reach` is walked from scratch, and
;; `undercut?` asks for one per *pair* of claims.  Nothing else can catch it — the
;; answers are identical, so every content test stays green.
;;
;; The probe point is `res/matches-visible`.  A reach over a **fact-relation** reads it once per
;; node it walks (`inherit/fact-reach`), so a re-walked reach is visible as a read that a
;; memo hit would have skipped.  The measurement is the same drain run twice: once bare,
;; once inside an enclosing `with-memo`.  A layer that realized under its own memo makes
;; the enclosing one worth nothing, so the two counts agree; a layer that handed its seq
;; out makes the enclosing one the only memo there is, and they do not.

(defn- visible-reads
  "How many `res/matches-visible` calls `run` makes."
  [run]
  (let [n (atom 0), orig @#'res/matches-visible]
    (with-redefs-fn {#'res/matches-visible (fn [& args] (swap! n inc) (apply orig args))}
      (fn [] (run) @n))))

(defn- preserved-fan!
  "`rel` transitive with `base` a part of every one of `owners`, `pred` preserved along
  `rel` at position 1, and `pred` stated of every owner.  So a goal about `base` has one
  claim per owner and no two of them are comparable — every claim survives, and
  `undercut?` asks for a reach once per *pair* on the way to saying so."
  [kb rel pred base owners]
  (v/with-deferred-settle kb
    (v/assert kb (list 'transitive rel) 'CxUniverse)
    (v/assert kb (list 'transitiveInArg pred 1 rel) 'CxUniverse)
    (doseq [o owners]
      (v/assert kb (list rel base o) 'CxUniverse)
      (v/assert kb (list pred o) 'CxUniverse))))

(tu/deftest-kb the-surviving-claims-are-realized-inside-the-memo-that-computed-them
  (tu/with-terms [partOf needsWork]
    (let [base   (tu/tmp-ind "Part")
          owners (vec (repeatedly 5 #(tu/tmp-ind "Whole")))
          goal   (list needsWork base)
          drain  #(doall (inherit/surviving kb goal 'CxUniverse))]
      (preserved-fan! kb partOf needsWork base owners)
      (drain)                                   ; warm whatever caches persist between asks
      (let [bare (visible-reads drain)
            held (visible-reads #(inherit/with-memo (drain)))]
        (testing "the fixture really does walk the reach"
          (is (= 5 (count (drain))) "one surviving claim per owner, none comparable")
          (is (pos? held)))
        (testing "an enclosing memo saves nothing, because the answer was realized in its own"
          (is (= bare held)
              (str "draining outside a memo cost " bare " visible reads against " held
                   " inside one — the seq escaped `with-memo` and re-walked the reach")))))))

(tu/deftest-kb the-forward-preservation-solutions-are-realized-inside-their-own-memo
  ;; `solve-with-support`'s open arm is the other escape: `licensed-product` walks a reach
  ;; per claim and `supports-for` opens a memo of its own per tuple, so a seq handed out
  ;; shares nothing between the tuples of one literal.  Same measurement, same claim.
  (tu/with-terms [partOf needsWork]
    (let [base   (tu/tmp-ind "Part")
          owners (vec (repeatedly 5 #(tu/tmp-ind "Whole")))
          lit    (list needsWork '?x)
          drain  #(doall (inherit/solve-with-support kb lit '?ctx))]
      (preserved-fan! kb partOf needsWork base owners)
      (drain)
      (let [bare (visible-reads drain)
            held (visible-reads #(inherit/with-memo (drain)))]
        (testing "the fixture really does enumerate licensed tuples"
          (is (seq (drain)) "the unstated part inherits from every whole it is part of")
          (is (pos? held)))
        (testing "an enclosing memo saves nothing here either"
          (is (= bare held)
              (str "draining outside a memo cost " bare " visible reads against " held
                   " inside one")))))))
