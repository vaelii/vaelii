;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.canon-edge-test
  "Canonicalization at its edges: the places where the canonical form could quietly
  stop being **a function of the rule's content alone**.

  `canon_test` specifies the mechanisms.  This namespace attacks the two ways they
  can fail without looking broken:

    * **arrival order leaking back in.**  Canonical antecedent order is decided by
      searching the orderings of a tie group, and any shortcut in that search — a
      size cutoff, a comparison that stops before the consequent — hands the decision
      back to the order the author happened to write.  Nothing throws; two spellings
      of one rule simply become two rules, and every guarantee resting on dedup (one
      handle, one direction, one set of justifications) is silently off.  Both shortcuts
      were real: see `a-tie-group-past-the-old-cutoff-still-dedups` and
      `a-cross-product-dedups-on-what-its-consequent-says`.
    * **an operational hold-back being treated as a logical one.**  Deferred
      evaluables, a dotted-rest splice, and a partially-ground symmetric literal all
      keep the position the author gave them, on purpose.  Each guard reads like dead
      code, and removing any of them yields *no solutions* rather than an error.

  Claims about the canonical form itself are asserted on the sentex `sx/sentex`
  builds, not through a query: `res/raw-match` probes both argument orders for a
  symmetric predicate, so an end-to-end query would answer correctly even if
  canonicalization had mangled what was stored."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- helpers -------------------------------------------------------------

(defn- chain
  "A join chain of `n` literals over `pred` — (pred ?p0 ?p1) (pred ?p1 ?p2) … — whose
  variables are named from `prefix`.  Every literal is the same predicate at the same
  arity with no ground argument, so `cmp-blind` cannot separate any of them: the tie
  group is the whole chain, and only the variable *sharing* distinguishes an
  ordering."
  [pred n prefix]
  (mapv (fn [i] (list pred (symbol (str prefix i)) (symbol (str prefix (inc i)))))
        (range n)))

(defn- permutations [coll]
  (if (<= (count coll) 1)
    (list (seq coll))
    (for [i (range (count coll))
          p (permutations (concat (take i coll) (drop (inc i) coll)))]
      (cons (nth coll i) p))))

(defn- sentex-count [kb] (count (p/sentex-ids (:records kb))))

;; ---- tie-group search: no cutoff, and the whole rule decides -------------

(tu/deftest-kb a-tie-group-past-the-old-cutoff-still-dedups
  ;; THE BUG: `candidate-orders` enumerated every permutation of every tie group and
  ;; gave up past 720 candidates, returning the `sort cmp-blind` order instead.
  ;; Clojure's sort is *stable*, so past that threshold the canonical form was the
  ;; author's written order — seven tied literals (5040) or four tied triples (1296)
  ;; stopped deduplicating, with nothing to show for it.  Six literals (720) stayed
  ;; correct, which is exactly why the cutoff never surfaced.
  (tu/with-terms [linksTo spans]
    (testing "seven tied literals — 5040 orderings, seven times the old cutoff"
      (let [h1 (v/assert-rule kb (chain linksTo 7 "?p") (list spans '?p0 '?p7) 'CxU)
            n1 (sentex-count kb)
            h2 (v/assert-rule kb (vec (reverse (chain linksTo 7 "?w")))
                              (list spans '?w0 '?w7) 'CxU)]
        (is (= h1 h2) "the same chain written backwards is the same rule")
        (is (= n1 (sentex-count kb)) "and stored nothing new")))
    (testing "and the reversed *join* is still a genuinely different rule"
      (is (not= (v/assert-rule kb (chain linksTo 7 "?p") (list spans '?p0 '?p7) 'CxU)
                (v/assert-rule kb (chain linksTo 7 "?p") (list spans '?p7 '?p0) 'CxU)))))
  (tu/with-terms [aTo bTo cTo dTo spans]
    (testing "four tie groups of three — 1296 candidates, also past the old cutoff"
      (let [gs (mapcat (fn [pd pfx] (chain pd 3 pfx))
                       [aTo bTo cTo dTo] ["?a" "?b" "?c" "?d"])
            h1 (v/assert-rule kb (vec gs) (list spans '?a0 '?d3) 'CxU)
            n1 (sentex-count kb)
            h2 (v/assert-rule kb (vec (reverse gs)) (list spans '?a0 '?d3) 'CxU)]
        (is (= h1 h2))
        (is (= n1 (sentex-count kb)))))))

(deftest every-ordering-of-a-tied-rule-canonicalizes-alike
  ;; The property the tie-group search exists for, checked exhaustively rather than on
  ;; one pair: a five-literal cycle over a single predicate ties completely under
  ;; `cmp-blind`, and all 120 spellings must land on one form.  Picking the winner on
  ;; the antecedents alone produces *five* here — the 120 orderings enumerate fine under
  ;; the cutoff, and the tiebreak is what fails (see the next test).
  (let [lits '[(p ?a ?b) (p ?b ?c) (p ?c ?d) (p ?d ?e) (p ?e ?a)]
        forms (into #{} (map #(sx/sentence-of (sx/sentex (list 'implies (cons 'and %) '(out ?a)) 'CxA)))
                    (permutations lits))]
    (is (= 1 (count forms)) (str "one canonical form, got " (count forms) ": " (pr-str forms)))))

(deftest a-cross-product-dedups-on-what-its-consequent-says
  ;; THE BUG: the winning ordering was chosen by comparing the numbered *antecedents*
  ;; only.  Two orderings of a tie group can render identical antecedents and still
  ;; disagree about which of them the consequent points at, and the loop kept whichever
  ;; it saw first — i.e. the author's order.  A two-literal tie group is enough, so
  ;; this was reachable a thousand times below the cutoff and independent of it.
  ;;
  ;; (p ?a ?b) and (p ?c ?d) share nothing, so both orders give
  ;; [(p ?var0 ?var1) (p ?var2 ?var3)]; only (q ?var0 ?var2) vs (q ?var2 ?var0) differ,
  ;; and they are the same rule up to renaming.
  (let [s1 (sx/sentex '(implies (and (p ?a ?b) (p ?c ?d)) (q ?a ?c)) 'CxA)
        s2 (sx/sentex '(implies (and (p ?c ?d) (p ?a ?b)) (q ?a ?c)) 'CxA)]
    (testing "the antecedents alone cannot separate them"
      (is (= '[(p ?var0 ?var1) (p ?var2 ?var3)] (:antecedent s1) (:antecedent s2))))
    (testing "so the consequent decides, the same way round both times"
      (is (= '(q ?var0 ?var2) (:consequent s1) (:consequent s2)))
      (is (= (sx/path s1) (sx/path s2)))))
  ;; (An exceptWhen exception no longer participates in the rule's canonical tiebreak —
  ;; it is a separate meta-sentex — so it cannot re-introduce arrival-order dependence
  ;; here; its own conjunct-order independence is `canon_test`'s
  ;; `a-vector-exceptions-conjuncts-are-order-insensitive`.)
  (testing "a rule whose antecedents are *wholly* interchangeable still dedups"
    ;; four disconnected copies of one predicate: every ordering renders the same
    ;; antecedents, and only the consequent says which copy matters
    (let [lits '[(p ?a ?b) (p ?c ?d) (p ?e ?f) (p ?g ?h)]
          forms (into #{} (map #(sx/sentence-of (sx/sentex (list 'implies (cons 'and %) '(out ?e)) 'CxA)))
                      (permutations lits))]
      (is (= 1 (count forms))))))

;; ---- the automorphic cross product is bounded, not enumerated -----------
;; k joinless literals of one predicate whose consequent numbers each differently are a
;; genuine automorphism: every ordering renders the identical antecedents, so only the
;; consequent separates them and the exact search would materialise all k! orderings
;; before choosing.  `prune-by-tail` folds the consequent into the search — the group is
;; joinless and tail-isolated, so its ordering changes nothing but its own consequent —
;; keeping only the minimal-so-far survivors each round.  The result is unchanged (still
;; the whole-rule minimum); only the cost is, from k! to O(k²).

(defn- joinless-antes [k]
  (mapv (fn [i] (list 'rel (symbol (str "?a" (* 2 i))) (symbol (str "?a" (inc (* 2 i))))))
        (range k)))

(deftest an-automorphic-cross-product-canonicalizes-without-enumerating
  (testing "all 720 orderings of six joinless literals land on one form"
    (let [antes (joinless-antes 6)
          rule  (fn [a] (list 'implies (cons 'and a) (cons 'q (map second a))))  ; consequent refs each first arg
          forms (into #{} (map #(sx/sentence-of (sx/sentex (rule (vec %)) 'CxA)))
                      (permutations antes))]
      (is (= 1 (count forms)) (str "expected one canonical form, got " (count forms)))
      (testing "and it is the minimal numbering — each antecedent's first var in consequent order"
        (is (= '(q ?var0 ?var2 ?var4 ?var6 ?var8 ?var10)
               (:consequent (sx/sentex (rule antes) 'CxA)))))))
  (testing "twelve literals canonicalize in milliseconds where k! would take hours"
    (let [rule (fn [a] (list 'implies (cons 'and a) (cons 'q (map second a))))
          t0   (System/nanoTime)
          _    (sx/sentex (rule (joinless-antes 12)) 'CxA)
          ms   (/ (- (System/nanoTime) t0) 1e6)]
      (is (< ms 1000) (str "k=12 took " ms " ms — a factorial search would not return")))))

(deftest prune-by-tail-stays-exact-across-consequent-shapes
  ;; The greedy tail projection must agree with the exhaustive search for *every* way a
  ;; consequent can reference an automorphic group — all first args, second args, a
  ;; subset, a repeat, or none — so each shape below is checked to canonicalize alike
  ;; across all 24 orderings of four joinless literals.
  (let [antes (joinless-antes 4)                      ; (rel ?a0 ?a1)(rel ?a2 ?a3)(rel ?a4 ?a5)(rel ?a6 ?a7)
        conseqs ['(q ?a0 ?a2 ?a4 ?a6)                 ; every first arg, in order
                 '(q ?a1 ?a3 ?a5 ?a7)                 ; every second arg
                 '(q ?a6 ?a0)                         ; a subset, out of order
                 '(q ?a2 ?a2 ?a4)                     ; a repeat
                 '(q ?a3 ?a0 ?a5)                     ; mixed first/second
                 '(out Constant)]]                    ; none — wholly interchangeable
    (doseq [conseq conseqs]
      (let [forms (into #{} (map #(sx/sentence-of (sx/sentex (list 'implies (cons 'and %) conseq) 'CxA)))
                        (permutations antes))]
        (is (= 1 (count forms))
            (str "consequent " (pr-str conseq) " gave " (count forms) " forms across orderings"))))))

(deftest an-automorphic-group-beside-a-join-chain-still-dedups
  ;; A joinless group (eligible for prune-by-tail) and a join chain (not) in one rule:
  ;; the two paths must compose.  Every ordering of the whole antecedent set lands on one
  ;; form, checked across a sample of orderings (the full set is 8! and covered by the
  ;; per-part exhaustive tests above).
  (let [xprod (joinless-antes 2)                      ; (rel ?a0 ?a1)(rel ?a2 ?a3)
        chn   (chain 'edge 3 "?p")                    ; (edge ?p0 ?p1)(edge ?p1 ?p2)(edge ?p2 ?p3)
        conseq '(q ?a0 ?p0 ?p3)
        canon (fn [lits] (sx/sentence-of (sx/sentex (list 'implies (cons 'and (vec lits)) conseq) 'CxA)))
        forms (into #{} (map canon)
                    [(into (vec xprod) chn)                                  ; xprod then chain
                     (into (vec chn) xprod)                                  ; chain then xprod
                     (reverse (into (vec xprod) chn))                        ; all reversed
                     (concat [(first chn)] xprod (rest chn))                 ; interleaved
                     (concat (reverse xprod) (reverse chn))])]               ; each part reversed
    (is (= 1 (count forms)) (str "mixed rule gave " (count forms) " forms"))))

(tu/deftest-kb a-three-literal-tie-group-dedups-across-every-author-order
  ;; `tie-groups` accumulates maximal runs, and the search permutes within one.  A
  ;; two-literal self-join (the case `canon_test` covers) exercises neither the run
  ;; accumulation past a pair nor an ordering decided two picks deep.
  (tu/with-terms [linksTo spans]
    (let [lits (chain linksTo 3 "?p")
          conseq (list spans '?p0 '?p3)
          h1 (v/assert-rule kb lits conseq 'CxU)
          n1 (sentex-count kb)
          hs (mapv #(v/assert-rule kb (vec %) conseq 'CxU) (permutations lits))]
      (testing "all six spellings resolve to the one handle"
        (is (= #{h1} (set hs)))
        (is (= n1 (sentex-count kb))))
      (testing "and the stored chain reads in canonical variable order"
        (is (= [(list linksTo '?var0 '?var1)
                (list linksTo '?var1 '?var2)
                (list linksTo '?var2 '?var3)]
               (:antecedent (v/sentex kb h1))))))))

;; ---- deferred (evaluable) literals: the author's order is operational ----

(tu/deftest-kb chained-evaluables-keep-the-authors-order-and-fire
  ;; `defs` is appended verbatim, precisely so one computation can feed the next.
  ;; Sorting or reversing it would look harmless — the rule still stores, still
  ;; matches, still has the right variables — and would yield *no solutions*, because
  ;; the second evaluate would run before the first bound its input.  Only an
  ;; end-to-end firing catches that, so this test does both halves.
  (tu/with-terms [startsAt twoOn A]
    (v/assert kb (list startsAt A 1) 'CxU)
    (let [h (v/assert-rule kb [(list startsAt '?x '?n)
                               (list 'evaluate '?a (list '+ '?n 1))
                               (list 'evaluate '?b (list '+ '?a 1))]   ; ?b needs ?a
                           (list twoOn '?x '?b) 'CxU {:direction :backward})
          ante (:antecedent (v/sentex kb h))]
      (testing "the generator leads, and the two evaluables keep their written order"
        (is (= startsAt (ffirst ante)))
        (is (= '[(evaluate ?var2 (+ ?var1 1)) (evaluate ?var3 (+ ?var2 1))]
               (vec (rest ante)))
            "the second computation reads the variable the first produced"))
      (testing "and the chain actually computes: 1 + 1 + 1"
        (is (= [{'?z 3}] (vec (v/query kb (list twoOn A '?z) 'CxU {:max-depth 2}))))
        (is (v/query? kb (list twoOn A 3) 'CxU {:max-depth 2}))
        (is (not (v/query? kb (list twoOn A 4) 'CxU {:max-depth 2}))))))
  (testing "written before its generator, the pair is still held back in its own order"
    (let [s (sx/sentex '(implies (and (evaluate ?a (+ ?x 1)) (evaluate ?b (+ ?a 1)) (foo ?x))
                                 (bar ?b)) 'CxA)]
      (is (= '[(foo ?var0) (evaluate ?var1 (+ ?var0 1)) (evaluate ?var2 (+ ?var1 1))]
             (:antecedent s))))))

;; ---- dotted rest: a splice, not a positional argument list ---------------

(deftest a-dotted-rest-is-never-folded-or-merged
  ;; `fold-comparison` and `collapse-comparison-chains` both refuse forms containing
  ;; the dot marker.  The guards look like dead code — every ordinary comparison is a
  ;; flat list — but a dotted form's arguments are a *splice*, and treating the tail
  ;; variable as an argument produces a literal that quietly matches nothing.
  (testing "a dotted greaterThan is not reversed onto lessThan"
    (is (= '(greaterThan ?a . ?rest) (sx/sentence-of (sx/sentex '(greaterThan ?a . ?rest) 'CxA))))
    (testing "while the ordinary form still folds"
      (is (= '(lessThan 3 5) (sx/sentence-of (sx/sentex '(greaterThan 5 3) 'CxA))))))
  (testing "two dotted lessThans do not merge into one variable-arity literal"
    ;; the structure that *would* merge: the tail of the first is the head of the second,
    ;; which is exactly the (a<b)+(b<c) test `collapse-comparison-chains` looks for.
    ;; Splicing them yields (lessThan ?a . ?r . ?s) — a literal with two rest markers,
    ;; which nothing can ever match.
    (let [s (sx/sentex '(implies (and (foo ?a ?r ?s) (lessThan ?a . ?r) (lessThan ?r . ?s))
                                 (bar ?a)) 'CxA)
          lts (filterv #(= 'lessThan (first %)) (:antecedent s))]
      (is (= 2 (count lts)) "both survive")
      (is (every? #(= 1 (count (filter #{'.} %))) lts) "each with exactly one dot marker"))
    (testing "while the undotted chain over the same shape still collapses"
      (let [s (sx/sentex '(implies (and (foo ?a ?b ?c) (lessThan ?a ?b) (lessThan ?b ?c))
                                   (bar ?a)) 'CxA)]
        (is (= 1 (count (filterv #(= 'lessThan (first %)) (:antecedent s)))))))))

;; ---- symmetric arguments: only a *ground* literal is reordered -----------

(deftest a-partially-ground-symmetric-literal-keeps-its-argument-order
  ;; `every? ground-term?` is required.  A literal holding a variable is a pattern
  ;; — a query, or an antecedent about to be matched — and variables sort last, so
  ;; sorting one would move its ground argument into slot 1 and stop it matching the
  ;; stored fact.  Asserted on the constructed sentex on purpose: `res/raw-match`
  ;; probes both argument orders for a symmetric predicate, so a query would keep
  ;; answering correctly while the stored antecedent was wrong.
  (let [sym #{'sib}]
    (testing "a pattern is left exactly as written, either way round"
      (is (= '(sib ?x B) (sx/sentence-of (sx/sentex '(sib ?x B) 'CxA {:symmetric? sym}))))
      (is (= '(sib B ?x) (sx/sentence-of (sx/sentex '(sib B ?x) 'CxA {:symmetric? sym})))))
    (testing "a variable nested inside a compound argument counts as non-ground too"
      (is (= '(sib (f ?x) B) (sx/sentence-of (sx/sentex '(sib (f ?x) B) 'CxA {:symmetric? sym})))))
    (testing "while a fully ground literal is sorted, which is what dedups the pair"
      (is (= '(sib Ann Zed) (sx/sentence-of (sx/sentex '(sib Zed Ann) 'CxA {:symmetric? sym}))))
      (is (= '(sib Ann Zed) (sx/sentence-of (sx/sentex '(sib Ann Zed) 'CxA {:symmetric? sym})))))
    (testing "and an undeclared predicate is never touched"
      (is (= '(ord Zed Ann) (sx/sentence-of (sx/sentex '(ord Zed Ann) 'CxA {:symmetric? sym})))))))

;; ---- nested exceptions conjoin ------------------------------------------

(tu/deftest-kb two-nested-exceptions-conjoin
  ;; `peel-rule-wrapper` loops through the wrappers and `into`s each exception onto the
  ;; one below, so two `exceptWhen`s written together are **one** two-conjunct exception
  ;; (block-if-all).  Keeping only the outer (or only the inner) would silently widen
  ;; the rule, which no test of a single wrapper can see.
  (let [bird (tu/tmp-type) penguin (tu/tmp-type) young (tu/tmp-type) flies (tu/tmp-pred)
        rule-form (vr/rule-sentence [(list bird '?b)] (list flies '?b))
        nested (v/assert kb (list 'exceptWhen (list young '?b)
                                  (list 'exceptWhen (list penguin '?b)
                                        (list 'set/defaultRule
                                              (list 'implies (list bird '?b) (list flies '?b)))))
                         'CxU)
        rh (v/handle-of kb rule-form 'CxU)]
    (testing "both exceptions survive as one sorted, deduplicated conjunction"
      (is (= 1 (count (provers/rule-exceptions kb rh))))
      (is (= #{(list penguin '?var0) (list young '?var0)}
             (set (first (provers/rule-exceptions kb rh))))))
    (testing "so nesting and a single two-conjunct wrapper are one meta-sentex"
      (let [single (v/assert kb (list 'exceptWhen [(list penguin '?z) (list young '?z)]
                                      (list 'set/defaultRule
                                            (list 'implies (list bird '?z) (list flies '?z))))
                             'CxU)]
        (is (= nested single))))
    (testing "and the wrappers underneath still reach the rule's own fields"
      (is (true? (:defeasible (v/sentex kb rh))))
      (is (= (list 'implies (list bird '?var0) (list flies '?var0))
             (v/sentence-of (v/sentex kb rh))))))
  (testing "a third nesting conjoins too, and its order is not its identity"
    (let [bird (tu/tmp-type) a1 (tu/tmp-type) b1 (tu/tmp-type) c1 (tu/tmp-type) flies (tu/tmp-pred)
          rule-form (vr/rule-sentence [(list bird '?b)] (list flies '?b))
          a (v/assert kb (list 'exceptWhen (list a1 '?b)
                               (list 'exceptWhen (list b1 '?b)
                                     (list 'exceptWhen (list c1 '?b)
                                           (list 'implies (list bird '?b) (list flies '?b)))))
                      'CxU)
          b (v/assert kb (list 'exceptWhen (list c1 '?x)
                               (list 'exceptWhen (list a1 '?x)
                                     (list 'exceptWhen (list b1 '?x)
                                           (list 'implies (list bird '?x) (list flies '?x)))))
                      'CxU)
          rh (v/handle-of kb rule-form 'CxU)]
      (is (= a b))
      (is (= 3 (count (first (provers/rule-exceptions kb rh))))))))

;; ---- the lexical last resort actually resolves something ----------------

(tu/deftest-kb constants-break-a-tie-lexically
  ;; `cmp-term` / `cmp-blind` end with (compare (str a) (str b)).  It is indistinguishable from a
  ;; defensive default, and reducing it to 0 compiles, passes every structural test,
  ;; and turns two literals differing only in a ground constant into a *tie group* —
  ;; handing their order back to the author and breaking dedup.
  (testing "two literals separated only by a constant symbol are ordered, not tied"
    (let [s (sx/sentex '(implies (and (p Zed) (p Ann)) (q Zed)) 'CxA)]
      (is (= '[(p Ann) (p Zed)] (:antecedent s)) "lexically ascending, not as written")))
  (testing "so the two spellings are one rule"
    (is (= (sx/sentence-of (sx/sentex '(implies (and (p Zed) (p Ann)) (q Zed)) 'CxA))
           (sx/sentence-of (sx/sentex '(implies (and (p Ann) (p Zed)) (q Zed)) 'CxA)))))
  (tu/with-terms [holds noted Zed Ann]
    ;; the consequent takes its own predicate: a literal sharing the consequent's
    ;; predicate is held back as the recursive one, which would decide the order for a
    ;; reason that has nothing to do with the tiebreak under test
    (testing "and they resolve to one handle in the store"
      (let [h1 (v/assert-rule kb [(list holds Zed) (list holds Ann)]
                              (list noted Zed) 'CxU)
            n1 (sentex-count kb)
            h2 (v/assert-rule kb [(list holds Ann) (list holds Zed)]
                              (list noted Zed) 'CxU)]
        (is (= h1 h2))
        (is (= n1 (sentex-count kb)))))))

;; ---- the two comparators agree where they overlap ------------------------
;;
;; `cmp-blind` is `cmp-term` with one arm changed (any two variables tie), and the
;; tie-group machinery is sound only while they agree on everything ELSE — a
;; divergence on ground terms would let the pre-numbering order and the final
;; numbered order disagree about which candidates even form a tie group.  Nothing
;; but a comment tied them together; this pins it.  Privates reached via #' —
;; the invariant is exactly about internals no public fn exposes.

(deftest cmp-blind-agrees-with-cmp-term-on-variable-free-terms
  (let [cmp-blind @#'sx/cmp-blind
        cmp-term  @#'sx/cmp-term
        sign      #(cond (neg? %) -1 (pos? %) 1 :else 0)
        ;; a fixed corpus: every rank class (number, string, constant, compound),
        ;; nesting, arity ties, value ties — no variables
        corpus    ['(p a b) '(p a c) '(p a) '(q a b) '(p (f a) b) '(p (f a b) b)
                   '(p 1 2) '(p 1 "s") 'a 'b "s" "t" 1 2 1.5
                   '(lessThan 1 2 3) '(not (p a)) '(p (g (h a)) b)]]
    (doseq [x corpus, y corpus]
      (is (= (sign (cmp-term x y)) (sign (cmp-blind x y)))
          (str "comparators disagree on " (pr-str x) " vs " (pr-str y))))))
