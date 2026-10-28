;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.quality-test
  "`kb-quality` — the seven readings about the knowledge rather than about the engine.

  Every reading is a claim about a KB whose answer is known by construction, because that
  is the only way a distribution can be checked: a rule that fires twice, one that never
  fires, one whose every conclusion is defeated and one retracted after firing all look the
  same from a firing count alone, and the whole point of the census is that they do not
  land in the same category.

  The one test here that is not about correctness is
  `a-densely-cyclic-rule-graph-condenses-instead-of-re-exploring-it`.  A rule graph is
  cyclic in the ordinary case, and the failure it guards against is not a wrong answer, it
  is a report that never returns."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.quality :as quality]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- default-rule [antes conseq]
  (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence antes conseq))))

(defn- handles [entries] (set (map :handle entries)))

;; ---- which rules never fire ----------------------------------------------

(tu/deftest-kb the-four-firing-outcomes-land-in-three-different-categories
  (tu/with-terms [bird ghost penguin sings has_wings glows flies hasBeak
                  Robin Tweety Waddles]
    (let [fires   (v/assert-rule kb [(list bird '?x)] (list has_wings '?x) 'CxUniverse {:direction :forward})
          never   (v/assert-rule kb [(list ghost '?x)] (list glows '?x) 'CxUniverse {:direction :forward})
          beaten  (v/assert kb (default-rule [(list penguin '?x)] (list flies '?x))
                            'CxUniverse)
          undone  (v/assert-rule kb [(list sings '?x)] (list hasBeak '?x) 'CxUniverse {:direction :forward})
          sang    (v/assert kb (list sings Robin) 'CxUniverse)]
      (v/assert kb (list bird Robin) 'CxUniverse)
      (v/assert kb (list bird Tweety) 'CxUniverse)
      (v/assert kb (list penguin Waddles) 'CxUniverse)
      ;; known-true, so it out-ranks the default conclusion the rule just placed
      (v/assert kb (list 'not (list flies Waddles)) 'CxUniverse {:strength :monotonic})
      (v/retract! kb sang)
      (let [q (:rules (v/kb-quality kb))]
        (testing "a rule with two supported conclusions is live, and both firings count"
          (is (= 1 (:fired q)))
          (is (<= 2 (:firings q)))
          (is (not (contains? (handles (:never q)) fires))))
        (testing "a rule nothing matched never fired"
          (is (contains? (handles (:never q)) never)))
        (testing "a rule whose *support* was retracted also reads as never fired — the
                  census counts currently-supported firings, and firings-ever is a
                  different question nothing here answers"
          (is (contains? (handles (:never q)) undone)))
        (testing "a rule that fired and had every conclusion defeated is its own category,
                  and it is the interesting one: it runs and contributes nothing"
          (is (= #{beaten} (handles (:all-defeated q))))
          (is (= 1 (:all-defeated-count q))))
        (testing ":firings is every recorded firing, the defeated ones included — so it is
                  not the live rules' share of them, and the report must not give the impression that
                  it were"
          (is (= 3 (:firings q))
              "two from the live rule, one from the rule whose conclusion is defeated"))
        (testing "each listed rule reads as its author wrote it, not as it is stored"
          (is (= (list 'implies (list ghost '?x) (list glows '?x))
                 (:sentence (first (filter #(= never (:handle %)) (:never q))))))
          (is (= 'CxUniverse
                 (:context (first (filter #(= never (:handle %)) (:never q)))))))))))

(tu/deftest-kb every-rule-the-index-can-key-is-in-the-census
  ;; the claim the cost argument rests on: rules are enumerated from the rule index, not by
  ;; scanning the record store, and the two must agree on a KB whose rules are all keyable
  (tu/with-terms [a_type b_type c_type pOne pTwo pThree]
    (v/assert-rule kb [(list a_type '?x)] (list pOne '?x) 'CxUniverse {:direction :forward})
    (v/assert-rule kb [(list b_type '?x)] (list pTwo '?x) 'CxUniverse {:direction :forward})
    (v/assert-rule kb [(list a_type '?x) (list b_type '?x)] (list pThree '?x) 'CxUniverse {:direction :forward})
    (v/assert kb (list 'genl c_type a_type) 'CxUniverse)
    (let [recs    (:records kb)
          scanned (into #{} (filter #(some-> (p/get-sentex recs %) vr/rule?))
                        (p/sentex-ids recs))]
      (is (pos? (count scanned)))
      (is (= (count scanned) (:total (:rules (v/kb-quality kb))))))))

;; ---- extent skew ---------------------------------------------------------

(deftest gini-is-zero-when-nothing-is-skewed-and-approaches-one-when-everything-is
  (let [gini #'quality/gini]
    (testing "the degenerate ends"
      (is (= 0.0 (gini [])))
      (is (= 0.0 (gini [0 0 0])) "no extent at all is not skew")
      (is (= 0.0 (gini [5 5 5 5])) "every predicate the same size"))
    (testing "one predicate holding everything is (n-1)/n — 1.0 only in the limit, so a
              small vocabulary cannot reach it and the number must not be read as if it did"
      (is (= 0.75 (gini [0 0 0 10])))
      (is (< 0.99 (gini (conj (vec (repeat 999 0)) 1000)))))
    (testing "hand-computed: sorted [1 2 3 4] gives (2*30 - 5*10) / (4*10)"
      (is (= 0.25 (gini [1 2 3 4]))))))

(tu/deftest-kb the-extents-are-stored-counts-bucketed-by-order-of-magnitude
  (tu/with-terms [manyOf fewOf onceOf Holder]
    (dotimes [i 120] (v/assert kb (list manyOf Holder (symbol (str "QT" i))) 'CxUniverse))
    (dotimes [i 12]  (v/assert kb (list fewOf Holder (symbol (str "QF" i))) 'CxUniverse))
    (v/assert kb (list onceOf Holder Holder) 'CxUniverse)
    (let [e (:extents (v/kb-quality kb))]
      (testing "one bucket per order of magnitude, and the count is what is stored"
        (is (= 1 (get (:buckets e) 2)) "120 sits in 10^2")
        (is (= 1 (get (:buckets e) 1)) "12 in 10^1")
        (is (= 1 (get (:buckets e) 0)) "1 in 10^0")
        (is (= 133 (:stored e))))
      (testing "the heaviest are named, heaviest first"
        (is (= [manyOf 120] (first (:heaviest e))))
        (is (= [fewOf 12] (second (:heaviest e)))))
      (testing "and the skew is a single number beside the buckets"
        (is (< 0.0 (:gini e) 1.0))))))

(tu/deftest-kb a-limit-caps-each-listed-set-and-the-report-says-it-did
  (tu/with-terms [a_type pOne pTwo pThree pFour]
    ;; four *distinct* consequents: four rules identical up to variable names would
    ;; canonicalize to one handle, which is a different property and not this one
    (doseq [pred [pOne pTwo pThree pFour]]
      (v/assert-rule kb [(list a_type '?x)] (list pred '?x) 'CxUniverse {:direction :forward}))
    (let [q (:rules (v/kb-quality kb {:limit 2}))]
      (is (= 4 (:never-count q)) "the count is of the whole set")
      (is (= 2 (count (:never q))) "the list is not")
      (is (true? (:truncated? q)))
      (is (false? (:truncated? (:rules (v/kb-quality kb {:limit 100}))))))))

(tu/deftest-kb the-capped-list-is-chosen-by-content-not-by-the-order-the-rules-arrived
  ;; A handle is assertion order.  Ranking the capped set on one would make the *listed*
  ;; rules a function of the order an author happened to write them in while the counts
  ;; beside them are not — two loads of the same knowledge reporting the same totals over
  ;; different examples, which is the reading a baseline is compared against.
  ;;
  ;; The discriminator: assert the rules in the **reverse** of the order their consequent
  ;; names sort in.  Ranked by handle the listed pair would be the two asserted first (the
  ;; two largest names); ranked by content it is the two smallest, whenever they arrived.
  (tu/with-terms [a_type]
    (let [preds  (mapv #(tu/fresh-term :predicate (str "pFixed" %))
                       ["Alpha" "Beta" "Gamma" "Delta"])
          sorted (vec (sort-by str preds))]
      (doseq [p (reverse sorted)]
        (v/assert-rule kb [(list a_type '?x)] (list p '?x) 'CxUniverse {:direction :forward}))
      (let [q       (:rules (v/kb-quality kb {:limit 2}))
            shown   (into #{} (map #(nth (:sentence %) 2)) (:never q))
            wanted  (into #{} (map #(list % '?x)) (take 2 sorted))]
        (is (= 4 (:never-count q)) "all four are in the count")
        (is (= wanted shown)
            (str "and the two listed are the content-smallest, which are the two asserted "
                 "*last* — a handle ranking would have shown the other pair"))))))

(tu/deftest-kb the-signature-tie-break-survives-an-ambient-print-length
  ;; Two rules sharing one signature (same consequent predicate, same antecedent
  ;; predicate set) are tie-broken on their *printed sentences*.  A bare `pr-str` key
  ;; honours the caller's `*print-length*` — a REPL's, typically — which elides both
  ;; sentences to the same `(implies ...)` prefix, collapses the key, and drops the tie
  ;; back onto handle order, i.e. the order the author happened to write the rules in.
  ;; The guard is `nm/print-key` (naming.clj says why); this asserts that the tie-break
  ;; wears it.
  ;;
  ;; The discriminator: two same-signature rules asserted in reverse content order, a
  ;; limit of one, and `*print-length*` bound the way a REPL would leave it.  Guarded,
  ;; the listed rule is the content-smallest; unguarded, it is whichever came first.
  (tu/with-terms [a_type pShared]
    ;; content-larger sentence first: `(implies (and (a_type ?x)) (pShared ?x ?x))`
    ;; sorts *after* `(implies (and (a_type ?x) (a_type ?y)) (pShared ?x ?y))` — at the
    ;; first divergence the two-antecedent form has a space where this one has `)`.
    (v/assert-rule kb [(list a_type '?x)] (list pShared '?x '?x) 'CxUniverse {:direction :forward})
    (v/assert-rule kb [(list a_type '?x) (list a_type '?y)]
                   (list pShared '?x '?y) 'CxUniverse {:direction :forward})
    (let [q     (binding [*print-length* 1]
                  (:rules (v/kb-quality kb {:limit 1})))
          shown (into #{} (map :sentence) (:never q))]
      (is (= 2 (:never-count q)) "both rules are in the count")
      (is (= #{(list 'implies (list 'and (list a_type '?x) (list a_type '?y))
                     (list pShared '?x '?y))}
             shown)
          (str "and the one listed is the content-smallest, which was asserted *second*"
               " — a collapsed print key would have listed the first-asserted rule")))))

;; ---- chain depth over the rule graph -------------------------------------

(tu/deftest-kb chain-depth-is-per-rule-and-counts-the-transitive-cycle-as-one
  (tu/with-terms [a_type pMid pTop chained]
    ;; a transitive rule is a self-loop in the functor graph, which is the commonest cycle
    ;; there is — `genl`'s own transitivity has this shape
    (v/assert-rule kb [(list chained '?x '?y) (list chained '?y '?z)]
                   (list chained '?x '?z) 'CxUniverse {:direction :forward})
    (v/assert-rule kb [(list a_type '?x)] (list pMid '?x) 'CxUniverse {:direction :forward})
    (v/assert-rule kb [(list pMid '?x)] (list pTop '?x) 'CxUniverse {:direction :forward})
    (let [c (:chains (v/kb-quality kb))]
      (is (= 3 (:rules c)))
      (is (<= 1 (:cyclic c)) "the self-loop is a cycle of one node, not an acyclic node")
      (testing "depth is the longest path to a leaf, per rule"
        (is (= 1 (get (:depths c) 0)) "the transitive rule's own component leads nowhere")
        (is (= 1 (get (:depths c) 1)))
        (is (= 1 (get (:depths c) 2))))
      (testing "and the fraction at or above each depth, which a single number loses"
        (is (< 0.66 (get (:at-least c) 1) 0.67) "two of the three rules")
        (is (< 0.33 (get (:at-least c) 2) 0.34) "one of them")))))

(deftest a-densely-cyclic-rule-graph-condenses-instead-of-re-exploring-it
  ;; The incident this guards against was not a wrong answer: memoizing the *path* rather
  ;; than the node re-explored the whole reachable subgraph along every one of them, which
  ;; on a densely cyclic rule set is exponential and occupied two threads for hours with no
  ;; termination.  So the assertion is a wall clock, and the bound is generous on purpose —
  ;; what it separates is milliseconds from never.
  (let [n      20000
        preds  (mapv #(symbol (str "cyc" %)) (range n))
        conseq (into {} (map (fn [i] [i (nth preds i)])) (range n))
        ante   (into {} (map (fn [i] [i #{(nth preds (mod (dec i) n))
                                          (nth preds (mod (- i 100) n))}]))
                     (range n))
        ;; one rule above the cycle, so a depth is computed *over* the condensation rather
        ;; than merely surviving it
        conseq (assoc conseq n 'cycTop)
        ante   (assoc ante n #{(nth preds 0)})
        t0     (System/nanoTime)
        c      (#'quality/chain-depth {:ante ante :conseq conseq} (fn [_] nil))
        ms     (/ (- (System/nanoTime) t0) 1e6)]
    (is (= 2 (:components c)) "4,000 mutually reachable functors are one component")
    (is (= n (:largest c)))
    (is (= 1 (:cyclic c)))
    (is (= {0 n, 1 1} (:depths c)))
    (is (< ms 10000) (str "the condensation took " (long ms) " ms"))))

;; ---- taxonomy coverage ---------------------------------------------------

(tu/deftest-kb taxonomy-coverage-is-two-numbers-and-the-gap-between-them-is-the-finding
  (tu/with-terms [root_type mid_type leaf_type island_a island_b lonely_type Ownerless]
    (v/assert kb (list 'genl leaf_type mid_type) 'CxUniverse)
    (v/assert kb (list 'genl mid_type root_type) 'CxUniverse)
    ;; two types with an edge between them and no path to the root: covered by the first
    ;; number, not by the second, which is the whole reason there are two
    (v/assert kb (list 'genl island_a island_b) 'CxUniverse)
    ;; a type-shaped name in the vocabulary that no edge mentions at all
    (v/assert kb (list lonely_type Ownerless) 'CxUniverse)
    (let [t (:taxonomy (v/kb-quality kb))]
      (is (= root_type (:root t)) "the root is found, not assumed — nothing here is `thing`")
      (is (= 5 (:edged t)) "the five types some genl edge names")
      (is (= 3 (:rooted t)) "reflexively: leaf, mid, and the root itself")
      (is (= 2 (:islands t)) "the island pair, and nothing else")
      (testing "the denominator is every type-shaped name in the vocabulary — the six here
                plus `genl` itself, because a bare lowercase word is a legal type name as
                well as a legal predicate and this KB declares no arity to tell them
                apart.  Which is exactly why the *gap* above is the finding rather than
                either fraction on its own"
        (is (= 7 (:names t)))))))

(tu/deftest-kb taxonomy-coverage-excludes-known-nonunary-components-not-unknown-types
  (tu/with-terms [root_type mid_type leaf_type island_a island_b parent_relation child_relation]
    (doseq [[sub super] [[leaf_type mid_type] [mid_type root_type]
                         [island_a island_b] [child_relation parent_relation]]]
      (v/assert kb (list 'genl sub super) 'CxUniverse))
    ;; `:strict` refuses a snake_case relation's length binding
    (doseq [relation [parent_relation child_relation]]
      (v/assert (assoc kb :naming :off) (list 'arity relation 2) 'CxUniverse))
    (v/assert kb (list 'arity leaf_type 1) 'CxUniverse)
    (let [t (:taxonomy (v/kb-quality kb))]
      (is (= root_type (:root t)) "a corpus need not use thing as its root")
      (is (= 5 (:edged t)) "declared binary predicates are not unary type nodes")
      (is (= 3 (:rooted t)) "known unary and unknown types both remain")
      (is (= 2 (:islands t)) "untyped disconnected islands are still findings"))))

(tu/deftest-kb taxonomy-coverage-excludes-a-sub-relation-edge-between-variable-arity-relations
  ;; `(genl partition covering)` is an edge between two relations, not two types: neither
  ;; has an exact arity, so the unique-arity exclusion above does not reach them, and
  ;; counting them made a true sub-relation edge read as a two-node island.
  (tu/with-terms [root_type leaf_type covers splits]
    (v/assert kb (list 'genl leaf_type root_type) 'CxUniverse)
    (doseq [relation [covers splits]]
      (v/assert kb (list 'variable_arity relation) 'CxUniverse))
    (v/assert kb (list 'genl splits covers) 'CxUniverse)
    (let [t (:taxonomy (v/kb-quality kb))]
      (is (= root_type (:root t)))
      (is (= 2 (:edged t)) "the two relations are not type nodes")
      (is (= 0 (:islands t)) "so their edge is not an island"))))

;; ---- the options, and the emitter ----------------------------------------

(tu/deftest-kb an-option-nothing-reads-and-a-bound-that-is-not-one-are-refused
  (testing "a misspelt bound reads as no bound at all, which for a cap means uncapped"
    (let [e (try (v/kb-quality kb {:limt 5}) (catch clojure.lang.ExceptionInfo e e))]
      (is (= :unknown-option (:type (ex-data e))))
      (is (str/includes? (.getMessage ^Exception e) ":limt"))))
  (testing "and a known key holding a value it cannot mean"
    (doseq [bad [0 -1 "5" 2.5]]
      (is (= :unknown-option (:type (ex-data (try (v/kb-quality kb {:limit bad})
                                                  (catch clojure.lang.ExceptionInfo e e)))))
          (str "refused: " (pr-str bad))))))

(tu/deftest-kb the-phases-are-reported-in-order-and-a-throw-from-one-stops-the-report
  (let [seen (atom [])]
    (v/kb-quality kb {:on-progress #(swap! seen conj (:phase %))})
    (is (= [:extents :rules :chains :taxonomy :declarations :subsumption :clashes]
           (distinct @seen))))
  (testing "the callback throwing is how a long report is cancelled — the reading is of
            current state, so a half-finished one is discarded rather than repaired"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"enough"
                          (v/kb-quality kb {:on-progress (fn [_] (throw (ex-info "enough" {})))})))))

(deftest the-report-renders-the-map-and-reads-nothing-else
  ;; the emitter takes the map, not the KB, so a figure it prints is one the data holds —
  ;; hand-built here for exactly that reason
  (let [md (v/quality-report
            {:rules    {:total 3 :never [{:handle 7 :sentence '(implies (a ?x) (b ?x))
                                          :context 'CxSome}]
                        :never-count 1 :all-defeated [] :all-defeated-count 0
                        :fired 2 :firings 9 :truncated? false}
             :extents  {:predicates 4 :with-extent 2 :stored 130 :gini 0.5
                        :buckets {0 1, 2 1} :heaviest [['many_of 120] ['fewOf 10]]}
             :chains   {:functors 5 :components 4 :cyclic 1 :largest 2 :rules 3
                        :depths {0 2, 1 1} :at-least {1 0.3333}}
             :taxonomy {:names 6 :edged 5 :root 'root_type :rooted 3 :islands 2}})]
    (is (str/starts-with? md "# KB quality"))
    (is (str/includes? md "3 rules — **1 never fired** (33.3%)"))
    (is (str/includes? md "2 live; 9 recorded firings in all")
        "the firing total is stated as a total, not as the live rules' share of one")
    (is (str/includes? md "(implies (a ?x) (b ?x))"))
    (is (str/includes? md "Gini 0.5000"))
    (is (str/includes? md "| 10^2 | 1 |"))
    (is (str/includes? md "`many_of` — 120"))
    (is (str/includes? md "1 cyclic, largest 2"))
    (is (str/includes? md "reach `root_type`"))
    (is (str/includes? md "Edged but not reaching the root: 2"))
    (is (not (str/includes? md "The lists are capped")) "nothing was capped")))

(tu/deftest-kb a-kb-with-no-genl-edge-anywhere-has-no-root-to-report-against
  ;; the empty end of the taxonomy reading: a root that is nil is *no root*, which is a
  ;; different statement from a root nothing reaches — and an empty code span is neither
  (let [t (:taxonomy (v/kb-quality kb))]
    (is (nil? (:root t)))
    (is (zero? (:edged t)))
    (let [md (v/quality-report (v/kb-quality kb))]
      (is (str/includes? md "No `genl` edge anywhere, so there is no root"))
      (is (not (str/includes? md "reach ``")) "and never an empty name in a code span"))))

(deftest every-reading-gets-its-own-heading-in-table-order
  ;; What the load-time validator cannot see. It holds `readings` to `render-arms` — a row
  ;; with nothing to render it, an arm on no row — but it never renders anything, so it
  ;; cannot tell whether the heading a row declares is the heading the report actually
  ;; writes, or whether one arm's body quietly carries a `##` of its own. That is the
  ;; whole boundary between the table and the page.
  (let [readings @#'quality/readings
        full     {:rules    {:total 1 :never [] :never-count 0 :all-defeated []
                             :all-defeated-count 0 :fired 1 :firings 1 :truncated? false}
                  :extents  {:predicates 1 :with-extent 1 :stored 1 :gini 0.0
                             :buckets {0 1} :heaviest [['p 1]]}
                  :chains   {:functors 1 :components 1 :cyclic 0 :largest 1 :rules 1
                             :depths {0 1} :at-least {}}
                  :taxonomy {:names 1 :edged 1 :root 'root_type :rooted 1 :islands 0}
                  :declarations {:total 1 :stranded-count 0 :truncated? false :stranded []}
                  :subsumption  {:total 1 :subsumed-count 0 :truncated? false :subsumed []}
                  :clashes      {:total 1 :pair-count 0 :truncated? false :pairs []}}
        md       (v/quality-report full)
        headings (map #(subs % 3) (re-seq #"(?m)^## .*$" md))]
    (is (= (map :title readings) headings)
        "every reading writes its own title as a `##`, once, in the table's order — and
         no arm writes a second-level heading of its own")
    (testing "and a reading left out of the map takes its heading with it"
      (let [without (v/quality-report (dissoc full :subsumption))]
        (is (= (remove #{"Rules another rule already covers"} (map :title readings))
               (map #(subs % 3) (re-seq #"(?m)^## .*$" without))))))))

(deftest a-map-that-is-not-a-report-is-refused-rather-than-rendered-as-zeros
  ;; a page of zeros and dashes is a report a caller who passed the wrong map cannot tell
  ;; from a report of an empty KB
  (doseq [bad [{} nil {:rules {}} {:rules {:total 1}}]]
    (let [e (try (v/quality-report bad) (catch clojure.lang.ExceptionInfo e e))]
      (is (= :not-a-report (:type (ex-data e))) (str "refused: " (pr-str bad))))))

;; ---- argument constraints that constrain nothing -------------------------
;;
;; `(arg parentOf 3 person)` is admitted while `parentOf` has no declared length, and
;; goes inert when one arrives.  The entry point refuses the identical sentence a line later, so
;; without this reading an author gets the silence `constraint-vocabulary-test` opens on:
;; a declaration that is enforced and one that enforces nothing look the same.
;;
;; Deliberately *not* in `violations`.  A wrong-length fact is content an assert admitted
;; because it could not have known and the settle reports it as new; a stranded
;; declaration constrains nothing and reads the same an hour later.  See
;; `docs/taxonomy.md`.

(defn- stranded [kb] (:declarations (v/kb-quality kb)))

(tu/deftest-kb a-constraint-past-the-arity-is-listed-and-one-within-it-is-not
  (tu/with-terms [parentOf a_type]
    (v/assert kb (list 'genl a_type 'thing) 'CxUniverse)
    (v/assert kb (list 'arg parentOf 3 a_type) 'CxUniverse)
    (is (zero? (:stranded-count (stranded kb)))
        "nothing binds parentOf yet, so the position is a lower bound and not a mistake")
    (v/assert kb (list 'arg parentOf 1 a_type) 'CxUniverse)
    (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
    (let [d (stranded kb)]
      (is (= 2 (:total d))
          "the two arg declarations — the arity spelling is not an argument constraint")
      (is (= 1 (:stranded-count d)) "only the one naming a position parentOf lacks")
      (let [e (first (:stranded d))]
        (is (= (list 'arg parentOf 3 a_type) (:sentence e)))
        (is (= parentOf (:predicate e)))
        (is (= 3 (:position e)))
        (is (= 2 (:arity e)))
        (is (= parentOf (:via e)) "declared of itself"))
      (is (false? (:truncated? d))))))

(tu/deftest-kb an-inherited-arity-strands-a-declaration-and-the-entry-names-the-super
  ;; the descended half: `fatherOf` declares no length of its own, so the entry has to
  ;; name the predicate the length was read off or an author goes looking for a
  ;; declaration nobody wrote
  (tu/with-terms [parentOf fatherOf a_type]
    (v/assert kb (list 'genl a_type 'thing) 'CxUniverse)
    (v/assert kb (list 'arg fatherOf 3 a_type) 'CxUniverse)
    (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
    (is (zero? (:stranded-count (stranded kb))) "no edge yet, so fatherOf binds nothing")
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
    (let [e (first (:stranded (stranded kb)))]
      (is (= fatherOf (:predicate e)))
      (is (= parentOf (:via e)) "the length came through the super")
      (is (= 2 (:arity e))))))

(tu/deftest-kb a-variableArity-predicate-strands-none-of-its-declarations
  ;; The census reads the entry point's own arm, so the release has to reach it here too.  A
  ;; predicate whose three-argument facts the same KB stores *has* a third argument, and
  ;; listing the declaration that types it puts a falsehood in the report: the rendered
  ;; line carries the refusal's own wording, so it says chainOf is declared with two
  ;; arguments about a predicate whose three-argument fact is admitted a line later.
  (tu/with-terms [chainOf a_type A B C]
    (v/assert kb (list 'genl a_type 'thing) 'CxUniverse)
    (v/assert kb (list 'arg chainOf 3 a_type) 'CxUniverse)
    (v/assert kb (list 'interArg chainOf 1 a_type 5 a_type) 'CxUniverse)
    (v/assert kb (list 'binary_predicate chainOf) 'CxUniverse)
    (is (= 2 (:stranded-count (stranded kb)))
        "binary and nothing else, so both declarations reach past the length")
    (v/assert kb (list 'variable_arity chainOf) 'CxUniverse)
    (let [d (stranded kb)]
      (is (= 2 (:total d)) "both are still there to be read")
      (is (zero? (:stranded-count d))
          "and each of them constrains something: the tuples reaching those positions store")
      (is (empty? (:stranded d))))
    (v/assert kb (list a_type C) 'CxUniverse)
    (is (v/assert kb (list chainOf A B C) 'CxUniverse)
        "the fact the census would otherwise have called impossible")))

(tu/deftest-kb a-variableArity-sub-is-not-stranded-by-the-length-above-it
  ;; The inherited route into the same reading: a sub carrying the mark is bound to no
  ;; length (`arity/relation-length`), so the entry is not stranded.
  (tu/with-terms [chainOf subChainOf a_type]
    (v/assert kb (list 'genl a_type 'thing) 'CxUniverse)
    (v/assert kb (list 'arg subChainOf 3 a_type) 'CxUniverse)
    (v/assert kb (list 'binary_predicate chainOf) 'CxUniverse)
    (v/assert kb (list 'genl subChainOf chainOf) 'CxUniverse)
    (let [e (first (:stranded (stranded kb)))]
      (is (= subChainOf (:predicate e)))
      (is (= chainOf (:via e)) "two arguments, taken through the super"))
    (v/assert kb (list 'variable_arity subChainOf) 'CxUniverse)
    (is (zero? (:stranded-count (stranded kb)))
        "the mark on the sub releases what the super bound it to")))

(tu/deftest-kb both-of-a-conditional-constraints-positions-are-asked
  ;; `interArg` names two, and the target position is the one a single-position check
  ;; would miss
  (tu/with-terms [eats a_type]
    (v/assert kb (list 'genl a_type 'thing) 'CxUniverse)
    (v/assert kb (list 'interArg eats 1 a_type 4 a_type) 'CxUniverse)
    (v/assert kb (list 'binary_predicate eats) 'CxUniverse)
    (is (= 1 (:stranded-count (stranded kb))))
    (is (= 4 (:position (first (:stranded (stranded kb))))))))

(tu/deftest-kb a-denied-declaration-stays-listed-and-a-retracted-one-does-not
  ;; arg is forced-monotonic, so a denial of a stored declaration loses to
  ;; it and the declaration stays in belief and in the census: it is still the
  ;; stranded position its author wrote.  It leaves the census only by retraction.
  (tu/with-terms [parentOf a_type]
    (v/assert kb (list 'genl a_type 'thing) 'CxUniverse)
    (let [h (v/assert kb (list 'arg parentOf 3 a_type) 'CxUniverse {:strength :default})]
      (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
      (is (= 1 (:stranded-count (stranded kb))))
      (v/assert kb (list 'not (list 'arg parentOf 3 a_type)) 'CxUniverse
                {:strength :monotonic})
      (is (= 1 (:stranded-count (stranded kb))) "a denial loses to the declaration it denies")
      (v/retract! kb h)
      (is (zero? (:stranded-count (stranded kb))) "out of the store, out of the census"))))

(tu/deftest-kb the-limit-caps-the-stranded-list-and-not-its-count
  (tu/with-terms [a_type]
    (v/assert kb (list 'genl a_type 'thing) 'CxUniverse)
    (doseq [i (range 5)
            :let [p (tu/tmp-pred (str "wide" i))]]
      (v/assert kb (list 'arg p 3 a_type) 'CxUniverse)
      (v/assert kb (list 'binary_predicate p) 'CxUniverse))
    (let [d (:declarations (v/kb-quality kb {:limit 2}))]
      (is (= 5 (:stranded-count d)))
      (is (= 2 (count (:stranded d))))
      (is (true? (:truncated? d))))))

(deftest the-report-writes-the-declarations-section-and-omits-it-when-absent
  (let [base {:rules    {:total 1 :never [] :never-count 0 :all-defeated []
                         :all-defeated-count 0 :fired 1 :firings 1 :truncated? false}
              :extents  {:predicates 1 :with-extent 1 :stored 1 :gini 0.0
                         :buckets {0 1} :heaviest [['p 1]]}
              :chains   {:functors 1 :components 1 :cyclic 0 :largest 1 :rules 1
                         :depths {0 1} :at-least {}}
              :taxonomy {:names 1 :edged 1 :root 'root_type :rooted 1 :islands 0}}
        md   (v/quality-report
              (assoc base :declarations
                     {:total 4 :stranded-count 1 :truncated? false
                      :stranded [{:handle 9 :sentence '(arg fatherOf 3 person)
                                  :context 'CxUniverse :predicate 'fatherOf
                                  :position 3 :arity 2 :via 'parentOf
                                  :message (str "arg constrains argument 3 of fatherOf,"
                                                " which takes 2 arguments through"
                                                " parentOf")}]}))]
    (is (str/includes? md "4 argument declarations — **1 names a position its predicate"))
    (is (str/includes? md "(arg fatherOf 3 person)"))
    (is (str/includes? md
                       (str "- `(arg fatherOf 3 person)` in `CxUniverse` — arg"
                            " constrains argument 3 of fatherOf, which takes 2 arguments"
                            " through parentOf"))
        "the reason is the message the census carried, printed rather than re-derived —
         and an inherited length reads as one taken through the super rather than as a
         declaration nobody wrote")
    (is (str/includes? md (str "the fix is to correct the position, to declare the arity"
                               " the author meant,\nor to mark the predicate"
                               " `variable_arity` where its tuples really do reach that\n"
                               "far."))
        "all three ways out, the third being the one the entry point itself releases on")
    (testing "a census answer from before this reading existed still renders"
      ;; the shape test does not ask for the key, so an older stored report is readable
      ;; rather than refused
      (let [old (v/quality-report base)]
        (is (str/starts-with? old "# KB quality"))
        (is (not (str/includes? old "constrain nothing")))))))

;; ---- rules another rule already covers -----------------------------------
;;
;; An exact duplicate cannot reach this reading: two rules alike up to variable names,
;; antecedent order or a symmetric argument order are one handle (docs/canonicalization.md).
;; So every hit is a redundancy or a deliberate specialization, and the tests below are
;; about which pairs the reading calls covered — not about telling those two apart, which
;; it does not claim to do.

(defn- wrapped [w antes conseq] (list w (vr/rule-sentence antes conseq)))

(defn- except-rule [exception antes conseq]
  (list 'exceptWhen exception (default-rule antes conseq)))

(defn- covered [kb] (:subsumption (v/kb-quality kb)))

(defn- covered-pairs [kb] (set (map (juxt :by :subsumed) (:subsumed (covered kb)))))

(tu/deftest-kb a-rule-written-for-a-subtype-is-covered-by-the-one-above-it
  ;; The antecedent half of the genl awareness: whatever satisfies `dog_kind` satisfies
  ;; `animal_kind`, so the general rule fires wherever the specific one does and concludes
  ;; the same thing.  Without the edge the two rules are about unrelated types and neither
  ;; covers anything.
  (tu/with-terms [animal_kind dog_kind flies]
    (let [general  (v/assert-rule kb [(list animal_kind '?x)] (list flies '?x) 'CxUniverse {:direction :forward})
          specific (v/assert-rule kb [(list dog_kind '?y)] (list flies '?y) 'CxUniverse {:direction :forward})]
      (is (zero? (:subsumed-count (covered kb)))
          "no genl edge, so the two antecedents are about unrelated types")
      (v/assert kb (list 'genl dog_kind animal_kind) 'CxUniverse)
      (let [q (covered kb)
            e (first (:subsumed q))]
        (is (= 1 (:subsumed-count q)))
        (is (= specific (:subsumed e)))
        (is (= general (:by e)))
        (is (= 'CxUniverse (:context e)))
        (is (= (list 'implies (list dog_kind '?y) (list flies '?y)) (:sentence e))
            "each rule reads as its author wrote it, not as it is stored")
        (is (= '{?x ?y} (:substitution e))
            "σ in the two authors' own names — the covering rule's ?x is the covered
             rule's ?y — and not in the ?var0 numbering both are stored under")
        (is (= 2 (:total q)) "both rules were compared")
        (is (false? (:truncated? q)))))))

(tu/deftest-kb the-consequent-fan-runs-one-way-and-only-one
  ;; The half a reader expects to be symmetric and is not.  A rule concluding the SUBTYPE
  ;; covers one concluding the supertype — `(dog_kind X)` answers every goal
  ;; `(animal_kind ?x)` would — and the reverse covers nothing, because concluding
  ;; `animal_kind` says nothing about dogs.
  (tu/with-terms [animal_kind dog_kind pet]
    (v/assert kb (list 'genl dog_kind animal_kind) 'CxUniverse)
    (let [narrow (v/assert-rule kb [(list pet '?x)] (list dog_kind '?x) 'CxUniverse {:direction :forward})
          broad  (v/assert-rule kb [(list pet '?x)] (list animal_kind '?x) 'CxUniverse {:direction :forward})]
      (is (= #{[narrow broad]} (covered-pairs kb))
          "the subtype conclusion covers the supertype one, and nothing covers it"))))

(tu/deftest-kb a-rule-with-fewer-antecedents-covers-the-one-that-adds-a-condition
  ;; `ante(R1)σ ⊆ ante(R2)` as literal sets: the extra condition narrows when the general
  ;; rule already fires, so the narrow rule concludes nothing new.
  (tu/with-terms [bird_kind healthy flies]
    (let [general (v/assert-rule kb [(list bird_kind '?x)] (list flies '?x) 'CxUniverse {:direction :forward})
          narrow  (v/assert-rule kb [(list bird_kind '?x) (list healthy '?x)]
                                 (list flies '?x) 'CxUniverse {:direction :forward})]
      (is (= #{[general narrow]} (covered-pairs kb))))))

(tu/deftest-kb a-default-does-not-stand-in-for-a-strict-rule
  ;; The availability half.  A defeasible conclusion is defeated exactly where the strict
  ;; one stands, so a default that fires wherever a strict rule does still leaves the
  ;; strict rule doing something.  The control is the same pair with both defeasible.
  (tu/with-terms [bird_kind healthy flies]
    (v/assert kb (default-rule [(list bird_kind '?x)] (list flies '?x)) 'CxUniverse)
    (v/assert-rule kb [(list bird_kind '?x) (list healthy '?x)] (list flies '?x)
                   'CxUniverse {:direction :forward})
    (is (zero? (:subsumed-count (covered kb)))
        "the covering rule is a default and the covered one is not")
    (tu/with-terms [swims]
      (let [general (v/assert kb (default-rule [(list bird_kind '?x)] (list swims '?x))
                              'CxUniverse)
            narrow  (v/assert kb (default-rule [(list bird_kind '?x) (list healthy '?x)]
                                               (list swims '?x))
                              'CxUniverse)]
        (is (contains? (covered-pairs kb) [general narrow])
            "both defeasible, and the general one covers")))))

(tu/deftest-kb a-direction-covers-itself-and-forward-covers-the-others
  ;; A `set/forwardOnlyRule` answers no backward goal, so it cannot stand in for one — the
  ;; covered rule would stop being reachable from the direction it was written for.
  ;; `:forward` / `:both` are forward + backward, so they can.
  (tu/with-terms [bird_kind healthy flies]
    (v/assert kb (wrapped 'set/forwardOnlyRule [(list bird_kind '?x)] (list flies '?x))
              'CxUniverse)
    (v/assert kb (wrapped 'set/backwardRule [(list bird_kind '?x) (list healthy '?x)]
                          (list flies '?x))
              'CxUniverse)
    (is (zero? (:subsumed-count (covered kb)))
        ":forward-only covers :forward-only and nothing else")
    (tu/with-terms [swims]
      (let [both   (v/assert-rule kb [(list bird_kind '?x)] (list swims '?x) 'CxUniverse {:direction :forward})
            narrow (v/assert kb (wrapped 'set/backwardRule
                                         [(list bird_kind '?x) (list healthy '?x)]
                                         (list swims '?x))
                             'CxUniverse)]
        (is (contains? (covered-pairs kb) [both narrow])
            ":forward is forward + backward, and covers a backward rule")))))

(tu/deftest-kb an-exception-the-covering-rule-carries-and-the-covered-one-lacks-is-a-case-it-declines
  ;; `exceptWhen` is not on the record — it is a separate belief-following meta-sentex
  ;; naming the rule — so a rule and its excepted twin look identical to a reading that
  ;; only unifies patterns.  The exception is a binding the covering rule refuses to
  ;; conclude for and the covered one concludes for, which is exactly not covering it.
  (tu/with-terms [bird_kind healthy penguin_kind flies]
    (v/assert kb (except-rule (list penguin_kind '?x) [(list bird_kind '?x)]
                              (list flies '?x))
              'CxUniverse)
    (v/assert kb (default-rule [(list bird_kind '?x) (list healthy '?x)] (list flies '?x))
              'CxUniverse)
    (is (zero? (:subsumed-count (covered kb))))
    (testing "and the same exception on both sides covers again — the covered rule
              declines the same binding"
      ;; the handles here are the *meta-sentexes*' (asserting an `exceptWhen` wrapper
      ;; answers the exception it stored, not the rule it qualifies), so the pair is read
      ;; off the sentences
      (tu/with-terms [swims]
        (v/assert kb (except-rule (list penguin_kind '?x)
                                  [(list bird_kind '?x)] (list swims '?x))
                  'CxUniverse)
        (v/assert kb (except-rule (list penguin_kind '?x)
                                  [(list bird_kind '?x) (list healthy '?x)]
                                  (list swims '?x))
                  'CxUniverse)
        (let [q (covered kb)
              e (first (:subsumed q))]
          (is (= 1 (:subsumed-count q)))
          (is (= (list swims '?x) (last (:sentence e))))
          (is (= (list swims '?x) (last (:by-sentence e))))
          (is (= 'and (first (second (:sentence e))))
              "the covered rule is the one that adds a condition")
          (is (= (list bird_kind '?x) (second (:by-sentence e)))))))))

(tu/deftest-kb a-rule-is-not-covered-by-one-its-context-cannot-see
  ;; Context scoping, asked from the covered rule's own context: a rule covered by one it
  ;; cannot see is not covered, because the firing it was supposed to be spared never
  ;; happens there.
  (tu/with-terms [bird_kind healthy flies CxUp CxDown]
    (let [general (v/assert-rule kb [(list bird_kind '?x)] (list flies '?x) CxUp {:direction :forward})
          narrow  (v/assert-rule kb [(list bird_kind '?x) (list healthy '?x)]
                                 (list flies '?x) CxDown {:direction :forward})]
      (is (zero? (:subsumed-count (covered kb)))
          "two contexts with no edge between them see nothing of each other")
      (v/assert kb (list 'genlCx CxDown CxUp) 'CxUniverse)
      (let [e (first (:subsumed (covered kb)))]
        (is (= [general narrow] [(:by e) (:subsumed e)]))
        (is (= CxDown (:context e))
            "reported in the covered rule's context, which is the vantage it was asked
             from")))))

(tu/deftest-kb the-covered-list-is-capped-and-its-count-is-not
  (tu/with-terms [bird_kind flies]
    (let [general (v/assert-rule kb [(list bird_kind '?x)] (list flies '?x) 'CxUniverse {:direction :forward})]
      (doseq [i (range 4)
              :let [c (tu/fresh-term :predicate (str "quiteHealthy" i))]]
        (v/assert-rule kb [(list bird_kind '?x) (list c '?x)] (list flies '?x) 'CxUniverse {:direction :forward}))
      (let [q (:subsumption (v/kb-quality kb {:limit 2}))]
        (is (= 4 (:subsumed-count q)) "the count is of the whole set")
        (is (= 2 (count (:subsumed q))) "the list is not")
        (is (true? (:truncated? q)))
        (is (every? #(= general (:by %)) (:subsumed q)))))))

;; ---- contradictions in waiting -------------------------------------------
;;
;; Static analysis of the rules: nothing is derived, nothing believed and no fact is
;; consulted.  A pair here is a clash the rules *admit* — whether it ever forms depends on
;; content nobody has asserted — which is what makes it a different question from
;; `(contradictions kb)`.

(defn- clashes [kb] (:clashes (v/kb-quality kb)))

(defn- clash-kinds [kb] (set (map :kind (:pairs (clashes kb)))))

(tu/deftest-kb a-conclusion-and-a-negated-one-that-unify-are-a-clash-in-waiting
  (tu/with-terms [bird_kind penguin_kind flies]
    (let [yes (v/assert-rule kb [(list bird_kind '?x)] (list flies '?x) 'CxUniverse {:direction :forward})
          no  (v/assert-rule kb [(list penguin_kind '?x)] (list 'not (list flies '?x))
                             'CxUniverse {:direction :forward})
          q   (clashes kb)
          e   (first (:pairs q))]
      (is (= 1 (:pair-count q)))
      (is (= :negation (:kind e)))
      (is (= #{yes no} (set (:rules e))))
      (is (= 'CxUniverse (:context e)))
      (is (false? (:excepted e)))
      (is (= 1 (count (:unifier e)))
          "one identification: the two rules are about the same ?x")
      (is (= 2 (:total q)))
      (is (false? (:truncated? q))))))

(tu/deftest-kb the-negation-fan-runs-down-the-hierarchy-and-not-up
  ;; `(dog_kind X)` contradicts `(not (animal_kind X))` because a dog is an animal.
  ;; `(animal_kind X)` contradicts nothing about dogs, so the pair the other way round is
  ;; not a clash and must not be reported as one.
  (tu/with-terms [animal_kind dog_kind pet stray tame feral]
    (v/assert kb (list 'genl dog_kind animal_kind) 'CxUniverse)
    (let [dog      (v/assert-rule kb [(list pet '?x)] (list dog_kind '?x) 'CxUniverse {:direction :forward})
          not-any  (v/assert-rule kb [(list stray '?x)]
                                  (list 'not (list animal_kind '?x)) 'CxUniverse {:direction :forward})
          any      (v/assert-rule kb [(list tame '?x)] (list animal_kind '?x) 'CxUniverse {:direction :forward})
          not-dog  (v/assert-rule kb [(list feral '?x)]
                                  (list 'not (list dog_kind '?x)) 'CxUniverse {:direction :forward})
          pairs    (set (map (comp set :rules) (:pairs (clashes kb))))]
      (is (= #{:negation} (clash-kinds kb)))
      (is (contains? pairs #{dog not-any})
          "concluding the subtype contradicts denying the supertype")
      (is (contains? pairs #{any not-any}) "and each predicate contradicts its own denial")
      (is (contains? pairs #{dog not-dog}))
      (is (not (contains? pairs #{any not-dog}))
          "but concluding the supertype says nothing about the subtype, so denying the
           subtype beside it is no contradiction — which is the fan a symmetric reading
           would have reported")
      (is (= 3 (:pair-count (clashes kb)))))))

(tu/deftest-kb two-conclusions-a-disjointness-separates-are-a-clash-in-waiting
  (tu/with-terms [cat_kind dog_kind barks meows]
    (v/assert kb (list 'genl cat_kind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl dog_kind 'thing) 'CxUniverse)
    (v/assert kb (list 'disjoint cat_kind dog_kind) 'CxUniverse)
    (v/assert-rule kb [(list barks '?x)] (list dog_kind '?x) 'CxUniverse {:direction :forward})
    (v/assert-rule kb [(list meows '?x)] (list cat_kind '?x) 'CxUniverse {:direction :forward})
    (let [e (first (:pairs (clashes kb)))]
      (is (= :disjoint (:kind e)))
      (is (= 'CxUniverse (:context e))))))

(tu/deftest-kb two-values-for-one-functional-slot-are-a-clash-in-waiting
  ;; The mark is read **up** the predicate hierarchy, so two conclusions written at
  ;; sub-predicates clash against the declaration above them — which is the spelling a
  ;; reading that took the mark off the exact functor would miss.
  (tu/with-terms [parentOf fatherOf motherOf begat bore]
    (v/assert kb (list 'functional parentOf) 'CxUniverse)
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
    (v/assert kb (list 'genl motherOf parentOf) 'CxUniverse)
    (v/assert-rule kb [(list begat '?x '?y)] (list fatherOf '?x '?y) 'CxUniverse {:direction :forward})
    (v/assert-rule kb [(list bore '?x '?y)] (list motherOf '?x '?y) 'CxUniverse {:direction :forward})
    (let [e (first (:pairs (clashes kb)))]
      (is (= :functional (:kind e)))
      (is (= 1 (:pair-count (clashes kb)))))))

(tu/deftest-kb the-generalized-functional-mark-is-a-clash-in-waiting-too
  ;; #56, and the same fixture as the row above with the mark spelled the other way.
  ;; `(functionalInArg parentOf 2)` says exactly what `(functional parentOf)` says about
  ;; exactly this slot, so a KB that spells it that way must read as clash-prone rather
  ;; than clash-free — the detector read `:props` alone and answered for one spelling.
  (tu/with-terms [parentOf fatherOf motherOf begat bore]
    (v/assert kb (list 'functionalInArg parentOf 2) 'CxUniverse)
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
    (v/assert kb (list 'genl motherOf parentOf) 'CxUniverse)
    (v/assert-rule kb [(list begat '?x '?y)] (list fatherOf '?x '?y) 'CxUniverse {:direction :forward})
    (v/assert-rule kb [(list bore '?x '?y)] (list motherOf '?x '?y) 'CxUniverse {:direction :forward})
    (let [e (first (:pairs (clashes kb)))]
      (is (= :functional (:kind e)))
      (is (= 1 (:pair-count (clashes kb)))))))

(tu/deftest-kb a-generalized-mark-at-another-position-is-no-arity-2-clash
  ;; The counterpart, which bounds the widening: `(functionalInArg parentOf 3)`
  ;; constrains a slot a binary conclusion does not have, so pairing two binary
  ;; conclusions on it would report a constraint neither is subject to.
  (tu/with-terms [parentOf fatherOf motherOf begat bore]
    (v/assert kb (list 'functionalInArg parentOf 3) 'CxUniverse)
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
    (v/assert kb (list 'genl motherOf parentOf) 'CxUniverse)
    (v/assert-rule kb [(list begat '?x '?y)] (list fatherOf '?x '?y) 'CxUniverse {:direction :forward})
    (v/assert-rule kb [(list bore '?x '?y)] (list motherOf '?x '?y) 'CxUniverse {:direction :forward})
    (is (zero? (:pair-count (clashes kb)))
        "position 3 says nothing about two binary conclusions")))

(tu/deftest-kb the-generalized-mark-at-position-1-is-a-clash-in-waiting-too
  ;; The mirror of the row above, and the half #56 left behind: position **1** is a slot a
  ;; binary conclusion does have, so `(functionalInArg parentOf 1)` — argument 2
  ;; determines argument 1 — constrains these two rules exactly as position 2 does, with
  ;; the subject and the value the other way round.  `checks/functional-clashes` has
  ;; always convicted the pair; the detector read position 2 alone and called the KB
  ;; clash-free.
  ;;
  ;; Same fixture as the two rows above with the determinant moved: the rules agree on
  ;; argument 2 and differ on argument 1, which is the clash this spelling names.
  (tu/with-terms [parentOf fatherOf motherOf begat bore]
    (v/assert kb (list 'functionalInArg parentOf 1) 'CxUniverse)
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
    (v/assert kb (list 'genl motherOf parentOf) 'CxUniverse)
    (v/assert-rule kb [(list begat '?x '?y)] (list fatherOf '?x '?y) 'CxUniverse {:direction :forward})
    (v/assert-rule kb [(list bore '?x '?z)] (list motherOf '?z '?x) 'CxUniverse {:direction :forward})
    (let [e (first (:pairs (clashes kb)))]
      (is (= :functional (:kind e)))
      (is (= 1 (:pair-count (clashes kb)))))))

(tu/deftest-kb one-tuple-concluded-both-ways-round-is-a-clash-in-waiting
  (tu/with-terms [outranks bossOf juniorTo]
    (v/assert kb (list 'asymmetric outranks) 'CxUniverse)
    (v/assert-rule kb [(list bossOf '?x '?y)] (list outranks '?x '?y) 'CxUniverse {:direction :forward})
    (v/assert-rule kb [(list juniorTo '?x '?y)] (list outranks '?y '?x) 'CxUniverse {:direction :forward})
    (let [e (first (:pairs (clashes kb)))]
      (is (= :asymmetric (:kind e)))
      (is (= 1 (:pair-count (clashes kb)))))))

(tu/deftest-kb antecedents-that-cannot-both-hold-are-not-a-clash-in-waiting
  ;; The shallow satisfiability test, all four halves of it: a literal beside its own
  ;; negation, one term claimed to be of two separated types, one term bound to two
  ;; arities, and a literal beside the negation of a predicate it is a spec of.  None runs inference — they are the three things readable off the antecedent
  ;; sets themselves.
  (testing "a literal and its negation"
    (tu/with-terms [bird_kind penguin_kind flies]
      (v/assert-rule kb [(list bird_kind '?x)] (list flies '?x) 'CxUniverse {:direction :forward})
      (v/assert-rule kb [(list penguin_kind '?x) (list 'not (list bird_kind '?x))]
                     (list 'not (list flies '?x)) 'CxUniverse {:direction :forward})
      (is (zero? (:pair-count (clashes kb))))))
  (testing "and two antecedent types a declaration separates"
    (tu/with-terms [cat_kind dog_kind barks]
      (v/assert kb (list 'genl cat_kind 'thing) 'CxUniverse)
      (v/assert kb (list 'genl dog_kind 'thing) 'CxUniverse)
      (v/assert-rule kb [(list dog_kind '?x)] (list barks '?x) 'CxUniverse {:direction :forward})
      (v/assert-rule kb [(list cat_kind '?x)] (list 'not (list barks '?x)) 'CxUniverse {:direction :forward})
      (is (= 1 (:pair-count (clashes kb))) "nothing separates the two antecedents yet")
      (v/assert kb (list 'disjoint cat_kind dog_kind) 'CxUniverse)
      (is (zero? (:pair-count (clashes kb)))
          "no cat is a dog, so the two rules never both fire for one term")))
  (testing "and one term bound to two arities, in either spelling"
    (tu/with-terms [oneish twoish equiv_kind]
      (v/assert kb (list 'genl oneish 'thing) 'CxUniverse)
      (v/assert kb (list 'genl twoish 'thing) 'CxUniverse)
      (v/assert kb (list 'disjoint oneish twoish) 'CxUniverse)
      ;; the arity table's functionality, which core.txt states as (functional arity)
      (v/assert kb '(functionalInArg arity 2) 'CxUniverse)
      (v/assert-rule kb ['(arity ?p 1)] (list oneish '?p) 'CxUniverse {:direction :forward})
      (v/assert-rule kb ['(arity ?p 1)] (list twoish '?p) 'CxUniverse {:direction :forward})
      (is (= 1 (:pair-count (clashes kb)))
          "one arity claim on each side: the conclusions are separated and both can fire")
      (v/assert-rule kb ['(arity ?p 2)] (list twoish '?p) 'CxUniverse {:direction :forward})
      (is (= 1 (:pair-count (clashes kb)))
          "the arity table is functional, so no ?p is both 1 and 2 places")
      (testing "and a class membership says the same thing the other way"
        (v/assert kb (list 'genl equiv_kind 'binary_predicate) 'CxUniverse)
        (v/assert-rule kb [(list equiv_kind '?p)] (list twoish '?p) 'CxUniverse {:direction :forward})
        (is (= 1 (:pair-count (clashes kb)))
            "equiv_kind reaches binary_predicate up genl, so it claims arity 2"))))
  (testing "and a literal beside the negation of a predicate it is a spec of"
    (let [before (:pair-count (clashes kb))]
      (tu/with-terms [coversOf properCoversOf]
        (v/assert kb (list 'genl properCoversOf coversOf) 'CxUniverse)
        (v/assert-rule kb [(list coversOf '?x '?y) (list 'not (list coversOf '?y '?x))]
                       (list properCoversOf '?x '?y) 'CxUniverse {:direction :forward})
        (v/assert-rule kb [(list properCoversOf '?x '?y)] (list 'not (list coversOf '?y '?x))
                       'CxUniverse {:direction :forward})
        (is (= before (:pair-count (clashes kb)))
            "the second rule needs a proper tuple where the first denies its plain one")))))

(tu/deftest-kb an-arity-floor-above-an-exact-arity-is-no-clash-in-waiting
  ;; A floor rule reads `(arity ?p ?n)` or `(arityMin ?p ?n)` with `?n` above a bound.  The
  ;; arity table is functional by the KB's own mark, so beside a claim of exactly n places `?n` is n, and a bound
  ;; of n or more admits no ?p.  An arityMin above the exact arity admits none either.
  (doseq [[floor-functor bound exact reachable?] '[[arity 2 2 false]
                                                   [arity 1 2 true]
                                                   [arityMin 3 2 false]]]
    (tu/with-terms [lowish highish]
      (v/assert kb (list 'genl lowish 'thing) 'CxUniverse)
      (v/assert kb (list 'genl highish 'thing) 'CxUniverse)
      (v/assert kb (list 'disjoint lowish highish) 'CxUniverse)
      ;; the arity table's functionality, which core.txt states as (functional arity)
      (v/assert kb '(functionalInArg arity 2) 'CxUniverse)
      (let [before (:pair-count (clashes kb))]
        (v/assert-rule kb [(list 'arity '?p exact)] (list lowish '?p) 'CxUniverse
                       {:direction :forward})
        (v/assert-rule kb [(list floor-functor '?p '?n) (list 'greaterThan '?n bound)]
                       (list highish '?p) 'CxUniverse {:direction :forward})
        (is (= (if reachable? (inc before) before) (:pair-count (clashes kb)))
            (str "(" floor-functor " ?p ?n) above " bound " beside exactly " exact
                 (if reachable? " can both hold" " admits no ?p")))))))

(tu/deftest-kb a-floor-class-disjoint-from-the-exact-class-is-no-clash-in-waiting
  ;; A floor class such as core.txt's at_least_binary is disjoint from the exact class one
  ;; below it, `(disjoint at_least_binary unary)`.  `(arity ?p 1)` claims ?p is `unary`, the
  ;; relation-wide exact class of that length, so beside `(floorish ?p)` under a stated
  ;; `(disjoint floorish unary)` no ?p meets both.  The disjointness is the KB's: a floor
  ;; nothing separates from `unary` pairs as before, and a length the floor admits stays a
  ;; candidate.
  (let [U       'CxUniverse
        pair-of (fn [kb lo-body hi-body]
                  (tu/with-terms [lowish highish]
                    (v/assert kb (list 'genl lowish 'thing) U)
                    (v/assert kb (list 'genl highish 'thing) U)
                    (v/assert kb (list 'disjoint lowish highish) U)
                    (let [before (:pair-count (clashes kb))]
                      (v/assert-rule kb lo-body (list lowish '?p) U {:direction :forward})
                      (v/assert-rule kb hi-body (list highish '?p) U {:direction :forward})
                      (- (:pair-count (clashes kb)) before))))]
    (tu/with-terms [floorish]
      (v/assert kb (list 'genl floorish 'thing) U)
      (testing "a floor nothing separates from unary leaves the pair a candidate"
        (is (= 1 (pair-of kb ['(arity ?p 1)] [(list floorish '?p)]))))
      (v/assert kb (list 'disjoint floorish 'unary) U)
      (testing "a floor disjoint from unary admits no ?p of exactly one place"
        (is (zero? (pair-of kb ['(arity ?p 1)] [(list floorish '?p)]))))
      (testing "a length the floor admits leaves the pair a candidate"
        (is (= 1 (pair-of kb ['(arity ?p 2)] [(list floorish '?p)])))))))

(tu/deftest-kb a-functional-slot-filled-two-incompatible-ways-is-no-clash-in-waiting
  ;; `(functionalInArg P n)` says one filler at position n for each tuple of the others,
  ;; so two antecedents filling that slot for one tuple with two numbers, or with a number
  ;; and a variable bounded away from it, admit no term between them.  The checker reads
  ;; the mark off the KB, so it is a declaration read like the rest, and a slot nothing
  ;; marks pairs as before.
  (let [U       'CxUniverse
        pair-of (fn [kb lo-body hi-body]
                  (tu/with-terms [lowish highish]
                    (v/assert kb (list 'genl lowish 'thing) U)
                    (v/assert kb (list 'genl highish 'thing) U)
                    (v/assert kb (list 'disjoint lowish highish) U)
                    (let [before (:pair-count (clashes kb))]
                      (v/assert-rule kb lo-body (list lowish '?p) U {:direction :forward})
                      (v/assert-rule kb hi-body (list highish '?p) U {:direction :forward})
                      (- (:pair-count (clashes kb)) before))))]
    (tu/with-terms [sizeOf]
      (v/assert kb (list 'binary_predicate sizeOf) U)
      (testing "unmarked, two numbers in one slot are two facts that can both hold"
        (is (= 1 (pair-of kb [(list sizeOf '?p 1)] [(list sizeOf '?p 2)]))))
      (v/assert kb (list 'functionalInArg sizeOf 2) U)
      (testing "marked, two distinct numbers in the slot admit no ?p"
        (is (zero? (pair-of kb [(list sizeOf '?p 1)] [(list sizeOf '?p 2)]))))
      (testing "nor does a number at or below the other's lower bound"
        (is (zero? (pair-of kb [(list sizeOf '?p 1)]
                            [(list sizeOf '?p '?n) (list 'lessThan 1 '?n)])))
        (is (zero? (pair-of kb [(list sizeOf '?p 1)]
                            [(list sizeOf '?p '?n) (list 'greaterThan '?n 3)]))))
      (testing "nor a number at or above the other's upper bound"
        (is (zero? (pair-of kb [(list sizeOf '?p 2)]
                            [(list sizeOf '?p '?n) (list 'lessThan '?n 2)])))
        (is (zero? (pair-of kb [(list sizeOf '?p 5)]
                            [(list sizeOf '?p '?n) (list 'greaterThan 4 '?n)]))))
      (testing "a number the bound admits overlaps, so the pair is still a clash in waiting"
        (is (= 1 (pair-of kb [(list sizeOf '?p 2)]
                          [(list sizeOf '?p '?n) (list 'lessThan 1 '?n)])))))
    (testing "the arity table is functional by its own declaration, not by its name"
      (is (= 1 (pair-of kb ['(arity ?p 1)] ['(arity ?p 2)]))
          "a KB that does not declare arity functional leaves the two arities a pair")
      (is (= 1 (pair-of kb ['(arity ?p 1)] ['(arity ?p ?n) '(lessThan 1 ?n)])))
      (let [h (v/assert kb '(functionalInArg arity 2) U)]
        (is (zero? (pair-of kb ['(arity ?p 1)] ['(arity ?p 2)])))
        (is (zero? (pair-of kb ['(arity ?p 1)] ['(arity ?p ?n) '(lessThan 1 ?n)])))
        (is (= 1 (pair-of kb ['(arity ?p 2)] ['(arity ?p ?n) '(lessThan 1 ?n)]))
            "arity 2 is above 1, so both rules can fire for one binary ?p")
        (v/retract! kb h)))))

(tu/deftest-kb an-arg-type-disjoint-from-the-other-conclusion-is-not-a-clash-in-waiting
  ;; The fourth half of the satisfiability test, the one `separated-antecedents?` cannot
  ;; read: the type that rules a term out is not a membership the antecedent states but a
  ;; type an `arg` declaration demands.  `(measures ?p ?v)` demands `?p` be a `gauge`
  ;; through `(arg measures 1 gauge)`, and the paired rule concludes `(ledgered ?p)`, which
  ;; places the same term under `record` — disjoint, so no ground term makes both
  ;; antecedents hold and the pair is unreachable (vaelii#95).  The demand is read against
  ;; the paired rule's *conclusion*, since `logged` states nothing about its argument.
  (tu/with-terms [gauge record calibrated ledgered measures logged]
    (v/assert kb (list 'genl gauge 'thing) 'CxUniverse)
    (v/assert kb (list 'genl record 'thing) 'CxUniverse)
    (v/assert kb (list 'genl calibrated gauge) 'CxUniverse)
    (v/assert kb (list 'genl ledgered record) 'CxUniverse)
    (v/assert kb (list 'disjoint gauge record) 'CxUniverse)
    (v/assert-rule kb [(list measures '?p '?v)] (list calibrated '?p) 'CxUniverse {:direction :forward})
    (v/assert-rule kb [(list logged '?p)] (list ledgered '?p) 'CxUniverse {:direction :forward})
    (testing "an unknown antecedent domain leaves the disjoint conclusions a clash in waiting"
      (is (= 1 (:pair-count (clashes kb)))
          "measures declares no argument type yet, so nothing rules the shared term out"))
    (testing "a declared domain the other conclusion does not exclude stays a candidate"
      (v/assert kb (list 'arg measures 1 'thing) 'CxUniverse)
      (is (= 1 (:pair-count (clashes kb)))
          "thing excludes nothing, so the pair is still a candidate (vaelii#95, criterion 2)"))
    (testing "a declared domain disjoint from the other conclusion prunes it"
      (v/assert kb (list 'arg measures 1 gauge) 'CxUniverse)
      (is (zero? (:pair-count (clashes kb)))
          "a gauge is not a record, so measures and logged never both fire for one term"))))

(tu/deftest-kb a-covering-declaration-prunes-as-arg-does
  ;; `args` and `argAndRest` are `arg` over a run of positions, so whatever reads `arg`
  ;; reads them too: `(argAndRest measures 2 gauge)` types position 2 and every later one,
  ;; and `(args measures gauge)` stores `(argAndRest measures 1 gauge)`.  A tail starting past
  ;; the shared term's position says nothing about it.
  (tu/with-terms [gauge record calibrated ledgered measures logged]
    (v/assert kb (list 'genl gauge 'thing) 'CxUniverse)
    (v/assert kb (list 'genl record 'thing) 'CxUniverse)
    (v/assert kb (list 'genl calibrated gauge) 'CxUniverse)
    (v/assert kb (list 'genl ledgered record) 'CxUniverse)
    (v/assert kb (list 'disjoint gauge record) 'CxUniverse)
    (v/assert-rule kb [(list measures '?v '?p)] (list calibrated '?p) 'CxUniverse {:direction :forward})
    (v/assert-rule kb [(list logged '?p)] (list ledgered '?p) 'CxUniverse {:direction :forward})
    (is (= 1 (:pair-count (clashes kb))) "nothing types measures yet")
    (testing "a tail starting past the shared term's position leaves the pair a candidate"
      (let [h (v/assert kb (list 'argAndRest measures 3 gauge) 'CxUniverse)]
        (is (= 1 (:pair-count (clashes kb))))
        (v/retract! kb h)))
    (testing "a tail covering it prunes the pair"
      (let [h (v/assert kb (list 'argAndRest measures 2 gauge) 'CxUniverse)]
        (is (zero? (:pair-count (clashes kb)))
            "a gauge is not a record, read off argAndRest as off arg")
        (v/retract! kb h)))
    (testing "and so does args, through the argAndRest from position 1 core.txt's forward
              rule stores, restated here since this KB loads no core.txt"
      (v/assert-rule kb ['(args ?relation ?type)] '(argAndRest ?relation 1 ?type) 'CxUniverse
                     {:direction :forward})
      (v/assert kb (list 'args measures gauge) 'CxUniverse)
      (is (zero? (:pair-count (clashes kb)))
          "a gauge is not a record, read off args as off arg"))))

(tu/deftest-kb a-genlArg-typed-antecedent-is-not-read-and-so-not-pruned
  ;; The scope boundary of the reading above, asserted as a limitation rather than fixed.
  ;; `arg-type-conflicted?` reads `arg` and not `genlArg`: `(genlArg subGauge 1 gauge)`
  ;; demands the argument be a *subtype* of `gauge` rather than a member of it — a claim
  ;; one stratum up — so it is not compared against a membership conclusion through
  ;; `disjoint?`, which would conflate the two levels.  The pair therefore stays reported,
  ;; and a sound `genlArg` reading would be its own check over two subtype bounds.
  (tu/with-terms [gauge record calibrated ledgered subGauge logged]
    (v/assert kb (list 'genl gauge 'thing) 'CxUniverse)
    (v/assert kb (list 'genl record 'thing) 'CxUniverse)
    (v/assert kb (list 'genl calibrated gauge) 'CxUniverse)
    (v/assert kb (list 'genl ledgered record) 'CxUniverse)
    (v/assert kb (list 'disjoint gauge record) 'CxUniverse)
    (v/assert kb (list 'genlArg subGauge 1 gauge) 'CxUniverse)
    (v/assert-rule kb [(list subGauge '?p '?q)] (list calibrated '?p) 'CxUniverse {:direction :forward})
    (v/assert-rule kb [(list logged '?p)] (list ledgered '?p) 'CxUniverse {:direction :forward})
    (is (= 1 (:pair-count (clashes kb)))
        "the genlArg subtype bound is not read, so the disjoint conclusions stay a candidate")))

(defn- paired? [kb a b] (boolean (some #(= #{a b} (set (:rules %))) (:pairs (clashes kb)))))

(tu/deftest-kb a-genl-antecedent-types-its-first-argument-by-the-arity-of-its-second
  ;; `(genl ?r actsIn)` holds only of a relation of actsIn's length, so `?r` is demanded
  ;; `binary`, which no walker is (#210).  A class of relations that `binary` does not
  ;; exclude stays a candidate, and so does a class of types when the second argument is
  ;; itself a type.  A second argument of no exact length demands nothing.
  (tu/with-terms [actsIn acting_relation idle_relation walker strides lazes
                  mammalish furred_kind bald_kind shaves listsOf relatesTo]
    (v/assert kb (list 'arity actsIn 2) 'CxUniverse)
    (v/assert kb (list 'variable_arity listsOf) 'CxUniverse)
    (v/assert kb (list 'arity mammalish 1) 'CxUniverse)
    (doseq [c '[unary binary]] (v/assert kb (list 'genl c 'relation) 'CxUniverse))
    (doseq [t [acting_relation idle_relation]] (v/assert kb (list 'genl t 'binary) 'CxUniverse))
    (doseq [t [furred_kind bald_kind]] (v/assert kb (list 'genl t 'unary) 'CxUniverse))
    (v/assert kb (list 'disjoint walker 'relation) 'CxUniverse)
    (v/assert kb (list 'disjoint acting_relation idle_relation) 'CxUniverse)
    (v/assert kb (list 'disjoint furred_kind bald_kind) 'CxUniverse)
    (let [rule   #(v/assert-rule kb [%1] %2 'CxUniverse {:direction :forward})
          acting (rule (list 'genl '?r actsIn) (list acting_relation '?r))
          walks  (rule (list strides '?x) (list walker '?x))
          idle   (rule (list lazes '?r) (list idle_relation '?r))
          furred (rule (list 'genl '?t mammalish) (list furred_kind '?t))
          bald   (rule (list shaves '?t) (list bald_kind '?t))
          lists  (rule (list 'genl '?r listsOf) (list acting_relation '?r))
          relates (rule (list 'genl '?r relatesTo) (list acting_relation '?r))]
      (is (not (paired? kb acting walks)) "a binary relation is no walker")
      (is (not (paired? kb furred walks)) "a type is no walker")
      (is (paired? kb acting idle) "binary excludes neither class of relations")
      (is (paired? kb furred bald) "unary excludes neither class of types")
      (is (paired? kb lists walks) "listsOf is variable_arity")
      (is (paired? kb relates walks) "relatesTo binds no length"))))

(tu/deftest-kb an-application-is-typed-by-its-functions-result-and-arg-declarations
  ;; A term two rules unify can be an application, and the application is an instance of
  ;; its function's `result` while its arguments take the function's `arg` types (#169).
  ;; Each declaration is asserted after the pair is seen, so the same two rules over a
  ;; function declaring nothing are the control.
  (testing "a result disjoint from a type the other rule states of the application"
    (tu/with-terms [moment metallic brief alloyed spanned SpanFn]
      (v/assert kb (list 'disjoint moment metallic) 'CxUniverse)
      (v/assert kb (list 'genl brief moment) 'CxUniverse)
      (let [rule  #(v/assert-rule kb [%1] %2 'CxUniverse {:direction :forward})
            metal (rule (list alloyed '?y) (list metallic '?y))
            span  (rule (list spanned '?x) (list brief (list SpanFn '?x)))]
        (is (paired? kb metal span) "SpanFn declares no result")
        (v/assert kb (list 'result SpanFn moment) 'CxUniverse)
        (is (not (paired? kb metal span)) "every application of SpanFn is a moment"))))
  (testing "an arg type disjoint from a type the other rule states of the argument"
    (tu/with-terms [temporal_kind counted_kind lasting counts brief SpanFn]
      (v/assert kb (list 'disjoint temporal_kind counted_kind) 'CxUniverse)
      (v/assert kb (list 'disjoint lasting counted_kind) 'CxUniverse)
      (let [rule  #(v/assert-rule kb [%1] %2 'CxUniverse {:direction :forward})
            tally (rule (list counts '?z) (list counted_kind '?z))
            lasts (rule (list brief (list SpanFn '?w)) (list lasting '?w))]
        (is (paired? kb tally lasts) "SpanFn declares no argument type")
        (v/assert kb (list 'arg SpanFn 1 temporal_kind) 'CxUniverse)
        (is (not (paired? kb tally lasts)) "SpanFn takes a temporal_kind, which nothing counted is"))))
  (testing "an application at a position quotedArg types is a mention and demands nothing"
    (tu/with-terms [temporal_kind counted_kind lasting counts spanned quotes SpanFn]
      (v/assert kb (list 'disjoint temporal_kind counted_kind) 'CxUniverse)
      (v/assert kb (list 'disjoint lasting counted_kind) 'CxUniverse)
      (v/assert kb (list 'arg SpanFn 1 temporal_kind) 'CxUniverse)
      (v/assert kb (list 'quotedArg quotes 2 'thing) 'CxUniverse)
      (let [rule  #(v/assert-rule kb %1 %2 'CxUniverse {:direction :forward})
            tally (rule [(list counts '?z)] (list counted_kind '?z))
            lasts (rule [(list spanned '?w) (list quotes '?w (list SpanFn '?w))] (list lasting '?w))]
        (is (paired? kb tally lasts) "the quoted (SpanFn ?w) is not a use of ?w")))))

(tu/deftest-kb two-rules-no-context-can-see-together-are-not-a-clash-in-waiting
  ;; A nogood needs a context that sees both halves (docs/nmtms.md).  Asking only whether
  ;; one rule's context sees the other's would exempt every sibling pair, so the test is a
  ;; common descendant — and two contexts with none have no clash to form.
  (tu/with-terms [bird_kind penguin_kind flies CxLeft CxRight CxBoth]
    (v/assert-rule kb [(list bird_kind '?x)] (list flies '?x) CxLeft {:direction :forward})
    (v/assert-rule kb [(list penguin_kind '?x)] (list 'not (list flies '?x)) CxRight {:direction :forward})
    (is (zero? (:pair-count (clashes kb))) "two contexts, no common descendant")
    (v/assert kb (list 'genlCx CxBoth CxLeft) 'CxUniverse)
    (v/assert kb (list 'genlCx CxBoth CxRight) 'CxUniverse)
    (let [e (first (:pairs (clashes kb)))]
      (is (= :negation (:kind e)))
      (is (= CxBoth (:context e))
          "reported in the context where the nogood could form, which is neither rule's"))))

(tu/deftest-kb a-clash-a-stated-exception-already-handles-is-marked-and-not-hidden
  ;; "Birds fly, unless penguins" beside "penguins do not fly" is the *intended* shape,
  ;; and a reading that dropped it would tell an author there was nothing to see where
  ;; what there is to see is that the pair is handled.
  (tu/with-terms [bird_kind penguin_kind flies]
    (v/assert kb (except-rule (list penguin_kind '?x) [(list bird_kind '?x)]
                              (list flies '?x))
              'CxUniverse)
    (v/assert-rule kb [(list penguin_kind '?x)] (list 'not (list flies '?x)) 'CxUniverse {:direction :forward})
    (let [e (first (:pairs (clashes kb)))]
      (is (= :negation (:kind e)))
      (is (true? (:excepted e))
          "the exception names the other rule's antecedent, so the clash is stated"))))

(deftest the-report-writes-the-two-rule-hygiene-sections-and-omits-them-when-absent
  (let [base {:rules    {:total 2 :never [] :never-count 0 :all-defeated []
                         :all-defeated-count 0 :fired 2 :firings 2 :truncated? false}
              :extents  {:predicates 1 :with-extent 1 :stored 1 :gini 0.0
                         :buckets {0 1} :heaviest [['p 1]]}
              :chains   {:functors 1 :components 1 :cyclic 0 :largest 1 :rules 2
                         :depths {0 2} :at-least {}}
              :taxonomy {:names 1 :edged 1 :root 'root_type :rooted 1 :islands 0}}
        md   (v/quality-report
              (assoc base
                     :subsumption
                     {:total 2 :subsumed-count 1 :truncated? false
                      :subsumed [{:subsumed 8 :by 7 :substitution '{?x ?y}
                                  :context 'CxUniverse
                                  :sentence '(implies (dog_kind ?y) (flies ?y))
                                  :by-sentence '(implies (animal_kind ?x) (flies ?x))}]}
                     :clashes
                     {:total 2 :pair-count 1 :truncated? false
                      :pairs [{:rules [7 8] :kind :negation :unifier '{?x' ?x}
                               :context 'CxUniverse :excepted true
                               :sentences ['(implies (bird_kind ?x) (flies ?x))
                                           '(implies (penguin_kind ?x)
                                                     (not (flies ?x)))]}]}))]
    (is (str/includes? md "2 rules — **1 is covered by another** (50.0%)"))
    (is (str/includes? md (str "- `8` `(implies (dog_kind ?y) (flies ?y))` in `CxUniverse`"
                               " — covered by `7` `(implies (animal_kind ?x) (flies ?x))`"
                               " under `{?x ?y}`")))
    (is (str/includes? md "2 rules — **1 pair would clash if both fired**"))
    (is (str/includes? md (str "- negation in `CxUniverse`: `7` `(implies (bird_kind ?x)"
                               " (flies ?x))` against `8` `(implies (penguin_kind ?x) (not"
                               " (flies ?x)))` — excepted")))
    (testing "a census answer from before either reading existed still renders"
      (let [old (v/quality-report base)]
        (is (str/starts-with? old "# KB quality"))
        (is (not (str/includes? old "already covers")))
        (is (not (str/includes? old "Contradictions in waiting")))))))

(deftest the-readings-validator-refuses-a-table-and-arms-that-disagree
  ;; `check-readings!` runs at this namespace's load, over one table that agrees with its
  ;; arms — so every branch it has taken is the one that throws nothing, and until
  ;; something drives it over halves that disagree, "it refuses" is a claim about code
  ;; that has never run.  The check it *cannot* see is the one above:
  ;; `every-reading-gets-its-own-heading-in-table-order` renders and reads the headings.
  (let [check   @#'quality/check-readings!
        arms    @#'quality/render-arms
        rows    @#'quality/readings
        refusal (fn [readings render-arms]
                  (try (check readings render-arms) nil
                       (catch clojure.lang.ExceptionInfo e (ex-data e))))]
    (testing "the live halves pass, which is what the namespace load asserts"
      (is (= rows (check rows arms))))
    (testing "a row with nothing to render it, which prints a heading over an empty section"
      (let [data (refusal (conj rows {:key :ghost :title "Ghost"}) arms)]
        (is (= :bad-table-entry (:type data)))
        (is (= :unarmed-reading (:mismatch data)))
        (is (= :ghost (:reading data)))))
    (testing "an arm on no row, which `report`'s walk never reaches"
      (is (= :unlisted-arm
             (:mismatch (refusal rows (assoc arms :ghost (fn [_] "")))))))
    (testing "a blank heading, which is a `##` over nothing"
      (is (= :blank-title
             (:mismatch (refusal (conj (vec (butlast rows))
                                       (assoc (last rows) :title "  "))
                                 arms)))))
    (testing "two rows under one heading, where a reader cannot tell the sections apart"
      (is (= :duplicate-title
             (:mismatch (refusal (conj (vec (butlast rows))
                                       (assoc (last rows) :title (:title (first rows))))
                                 arms)))))
    (testing "one key twice, where the second row renders under the first's title or not at all"
      (is (= :duplicate-reading
             (:mismatch (refusal (conj (vec rows) (assoc (first rows) :title "Twice"))
                                 arms)))))))
