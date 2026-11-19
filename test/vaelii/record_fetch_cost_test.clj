;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.record-fetch-cost-test
  "What an operation costs the **record store**, as counted fetches — the other index,
  and the one `assert_cost_test` cannot see.

  That counted test counts `IndexStore` reads and this one counts `RecordStore` fetches, and the
  two come apart exactly where it hurts.  `kb/find-sentex-handle` asked the trie for a
  sentence's handle with `p/lookup`, whose wildcard token fans over every stored sentex of
  the same *shape*, and then read the record of each to find the one that was actually
  this sentence.  By `:reads` that is **one** index read and unimpeachable; by what it
  cost it was 2,779 µs against 13 µs per call at 800 candidates, because the eight hundred
  records behind those handles were paged one at a time.  On the durable store each of
  those is a positional slot read, a positional frame read and a nippy thaw past the LRU —
  orders above what any index read costs — and nothing counted them.

  `p/leaf-at` is the fix and the budgets below enforce it: a non-ground `handle-of`
  fetches **no** records, because the exact leaf of an α-renamed key holds only sentexes
  that share the sentence's shape and a KB of ground facts stores none there.  A change
  back to a matching read makes that number the size of the extent.

  ## Why a count, and why exact

  `assert_cost_test`'s reasons, unchanged: the quantity is an integer the engine computes,
  so there is no warm-up, no tail mean and no tolerance, and it reads the same on a loaded
  box.  Exact equality rather than a ceiling, so a legitimate improvement **fails this
  test**, and the commit that earns it rewrites the expected number, carrying its own size
  as data.

  ## What it does not catch

  - **What a fetch costs.**  One `get-sentex` counts once whether it hits the disk store's
    LRU or pages a frame, and the two differ by orders.  This counts how many a caller
    asks for, which is the quantity a caller controls.
  - **A store's own internal reads.**  The tally sits on the protocol method, so
    `mark-premise` re-fetching inside the durable store is not counted where the RAM store
    reaching into its state map is not either — a tally that counted both would be a
    reading of which backend is running rather than of what the engine asked for.
  - **A configuration other than the shipped one**, and a backend other than `:memory`.
    Both are fixed below for `assert_cost_test`'s reasons."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.rules :as rules]
            [vaelii.test-util :as tu]))

;; the instrument is process-wide, so a test that threw while collecting would hand the
;; next namespace a running tally
(use-fixtures :each (fn [t] (try (t) (finally (prof/stop)))))

(def ^:private n
  "Operations per workload.  Large enough that a per-operation fetch lands as a
  three-digit difference, small enough that five workloads are a second or two."
  100)

(def ^:private fetch-space
  "The KB every workload runs on: in-RAM, its own space, the reference TMS — fixed for
  `assert_cost_test`'s reasons.  The **backend**, because a budget is a claim about one
  store and the durable one answers a fetch from an LRU whose contents depend on what ran
  before it; the **TMS**, because `VAELII_TEST_TMS=dense` walks a different support graph
  and fetches a different number of justifications."
  (-> tu/plain-memory-space
      (update :space conj ::record-fetch)
      (assoc :tms :reference)))

(defn- fresh [] (doto (v/open-kb fetch-space) (tu/clear-kb!)))

(defn- ind [prefix i] (symbol (str prefix i)))

;; ---- the workloads -------------------------------------------------------
;;
;; Each returns a **thunk**, so everything the workload needs in place is built before the
;; instrument starts and only the operation being priced is counted.

(defn- ground-assert
  "A binary fact of fresh individuals — the floor, and the one a fetch added to the assert
  path is clearest on."
  []
  (let [kb (fresh)]
    (fn [] (dotimes [i n]
             (v/assert kb (list 'rfPlain (ind "RfA" i) (ind "RfB" i)) 'CxPerf {})))))

(defn- ground-handle-of
  "`handle-of` for a **ground** sentence that is stored.  A ground sentence keys the trie
  exactly, so its leaf holds its own handle alone and the first candidate is the answer —
  no record is read to tell it apart from anything."
  []
  (let [kb (fresh)]
    (dotimes [i n] (v/assert kb (list 'rfCand (ind "RfC" i) 'RfVal) 'CxPerf {}))
    (fn [] (dotimes [i n]
             (v/handle-of kb (list 'rfCand (ind "RfC" i) 'RfVal) 'CxPerf)))))

(defn- nonground-handle-of
  "**The workload the regression is priced by.**  `handle-of` for a sentence carrying a
  variable, over a KB holding `n` ground facts of exactly that shape.

  The pattern α-renames to `(rfCand ?0 RfVal)` and no sentex is stored at that key, so the
  exact leaf is empty and the answer is nil with **no record read at all**.  Asked as a
  *match* instead, the variable is a wildcard: the walk returns all `n` ground handles and
  the caller then reads a record apiece to find that none of them is this sentence.  That
  is the structure of the fix, and `n` is what this budget reads if it comes back."
  []
  (let [kb (fresh)]
    (dotimes [i n] (v/assert kb (list 'rfCand (ind "RfC" i) 'RfVal) 'CxPerf {}))
    (fn [] (dotimes [_ n]
             (v/handle-of kb '(rfCand ?x RfVal) 'CxPerf)))))

(defn- retraction
  "The `ground-assert` workload's facts, retracted in the order they arrived."
  []
  (let [kb (fresh)
        hs (mapv (fn [i] (v/assert kb (list 'rfPlain (ind "RfA" i) (ind "RfB" i)) 'CxPerf {}))
                 (range n))]
    (fn [] (doseq [h hs] (v/retract! kb h)))))

(defn- rule-fired
  "A fact arriving through one forward rule, so each assert stores **two** sentexes — the
  datum and the conclusion.  The derived half is where a fetch is easiest to add without
  noticing, since nothing a caller wrote is on that path: the chainer reads the datum's
  record, each candidate rule's record, and each matched fact's record again to place the
  conclusion."
  []
  (let [kb (fresh)]
    (v/assert kb (rules/rule-sentence ['(rfSrc ?x ?y)] '(rfDst ?x ?y))
              'CxPerf {:direction :forward :strength :monotonic})
    (fn [] (dotimes [i n]
             (v/assert kb (list 'rfSrc (ind "RfR" i) (ind "RfS" i)) 'CxPerf {})))))

;; ---- the budgets ---------------------------------------------------------
;;
;; Measured, not designed, at `n` = 100 — what the engine does today, written down so the
;; next change to any of these numbers is visible.  A failure prints the delta per kind.
;;
;; A kind is **absent rather than held at 0**, and that is the stronger claim: a kind a
;; workload never fetches is a key the tally never emits, so one fetch of it fails the
;; budget.  The two `handle-of` budgets are empty maps for exactly that reason, and they
;; are the point of the file.

(def ^:private budgets
  [{:name :ground-assert
    :build ground-assert
    ;; two sentex fetches per assert — the dedup probe and the settle's read of the
    ;; sentex it just stored — plus one provenance read
    :fetches {:sentex 200 :provenance 100}}

   {:name :ground-handle-of
    :build ground-handle-of
    ;; nothing: a ground key's leaf holds its own handle and `stored-at` returns it
    :fetches {}}

   {:name :nonground-handle-of
    :build nonground-handle-of
    ;; nothing, and this is the budget that would read 100 if the exact-leaf read went
    ;; back to a wildcard match
    :fetches {}}

   {:name :retraction
    :build retraction
    ;; one per retraction: the record the teardown is about
    :fetches {:sentex 100}}

   {:name :rule-fired
    :build rule-fired
    ;; six per assert, for two stored sentexes — the datum, the candidate rule, the
    ;; matched facts and the placement's re-reads.  The justification's content sort
    ;; reads the antecedent facts alone, not the rule it drops from the stored vector.
    :fetches {:sentex 600 :provenance 100}}])

;; ---- measuring -----------------------------------------------------------

(defn- measure
  "Run one workload under the instrument and return its fetch tally.  The KB is built
  inside the fixed configuration too: a corpus laid down under one reader and priced
  under another would be a workload nobody runs."
  [build]
  (tu/with-shipped-config
    (let [thunk (build)
          _     (prof/start)
          _     (thunk)
          snap  (prof/stop)]
      (into {} (:fetches snap)))))

(defn- delta-report
  "The kinds whose count moved, as a table — every kind either side names, so one that
  appeared from nowhere reads as `0 -> 100` rather than going missing."
  [expected actual]
  (->> (sort (into (set (keys expected)) (keys actual)))
       (keep (fn [k]
               (let [e (get expected k 0), a (get actual k 0)]
                 (when (not= e a)
                   (format "    %-16s %6d -> %-6d  (%+d)" (name k) e a (- a e))))))
       (str/join "\n")))

(deftest record-fetch-cost-is-what-it-was
  (doseq [{:keys [name build fetches]} budgets]
    (testing (str "the " (clojure.core/name name) " workload")
      (let [got (measure build)]
        (is (= fetches got)
            (format (str "%s: the record-fetch budget moved.\n%s\n"
                         "  If this change is intended, update the expected number — the diff is "
                         "the change's own record-store cost.\n"
                         "  If it is not, an operation started paging records the index "
                         "was already answering for, which no `:reads` budget can see.")
                    (clojure.core/name name) (delta-report fetches got)))))))

(deftest a-nonground-handle-of-reads-the-exact-leaf-and-nothing-else
  ;; The claim above as a *shape* beside the constant: the fetch count must not track the
  ;; extent.  A wildcard match reads one record per stored sentex of the pattern's shape,
  ;; so it grows with the corpus where the exact leaf does not — which is the difference
  ;; between 13 µs and 2,779 µs at 800 candidates, and the reason this file exists.
  (tu/with-shipped-config
    (let [probe (fn [population]
                  (let [kb (fresh)]
                    (dotimes [i population]
                      (v/assert kb (list 'rfWide (ind "RfW" i) 'RfVal) 'CxPerf {}))
                    (prof/start)
                    (dotimes [_ 10] (v/handle-of kb '(rfWide ?x RfVal) 'CxPerf))
                    (let [snap (prof/stop)]
                      {:fetches (reduce + 0 (vals (:fetches snap)))
                       :answer  (v/handle-of kb '(rfWide ?x RfVal) 'CxPerf)})))
          narrow (probe 20)
          wide   (probe 200)]
      (is (nil? (:answer narrow)) "no sentex is stored at the α-renamed key")
      (is (zero? (long (:fetches narrow)))
          "an empty leaf is an empty candidate set, so nothing is paged to sift it")
      (is (= (:fetches narrow) (:fetches wide))
          (str "the fetch count must be flat in the extent of the pattern's shape — a "
               "wildcard read is back (" (:fetches narrow) " -> " (:fetches wide) ")")))))

(deftest a-delta-merge-fetches-records-bounded-by-the-delta-whatever-the-kb-size
  (tu/with-shipped-config
    (let [probe (fn [population]
                  (let [open (fn [tag] (doto (v/open-kb (update fetch-space :space conj tag))
                                         (tu/clear-kb!)))
                        src  (open ::delta-src)
                        dst  (open ::delta-dst)
                        dir  (tu/temp-dir "vaelii-fetch-" "delta" "-")
                        fact #(list 'rfBase (ind "RfD" %) 'RfVal)]
                    (try
                      (tu/rm-rf! dir)
                      (doseq [kb [src dst]] (v/assert kb '(genlCx CxPerfB CxPerf) 'CxUniverse))
                      (dotimes [i population]
                        (v/assert src (fact i) 'CxPerf {})
                        (v/assert dst (fact (- population 1 i)) 'CxPerf {}))
                      (let [f (v/fork src)]
                        (try
                          (dotimes [i 10]
                            (v/assert f (list 'except (v/sentex-handle (v/handle-of f (fact i) 'CxPerf)))
                                      'CxPerfB))
                          (v/export-text! f (.getPath dir) {:delta? true})
                          (finally (v/close! f))))
                      (prof/start)
                      (let [r    (v/load-text! dst (.getPath dir) {:merge? true})
                            snap (prof/stop)]
                        {:fetches (reduce + 0 (vals (:fetches snap))) :refused (:refused r)})
                      (finally (tu/clear-kb! src) (tu/clear-kb! dst) (tu/rm-rf! dir)))))
          small (probe 20)
          large (probe 200)]
      (is (empty? (:refused small)) "every reference resolves")
      (is (= (:fetches small) (:fetches large))
          (str "the merge's fetch count must be flat in the KB's size — a read over every "
               "stored sentex is back (" (:fetches small) " -> " (:fetches large) ")")))))

(deftest a-declaration-pages-no-instance-it-does-not-believe
  ;; A dump imported `{:belief? :stored}` holds its records with the network empty until
  ;; a `recover`, and an install asserts its ontology into that state.  The clash pass
  ;; reads what a `genl` edge puts in question as the *believed* members below it, and it
  ;; paged each member's record before asking belief — every member of the type, since
  ;; none passes and so none spends the instance budget, so an install into a large
  ;; store paged the store.  Asked of the handle first, it pages none.
  (tu/with-shipped-config
    (let [probe (fn [population]
                  (let [dir (str (java.nio.file.Files/createTempDirectory
                                  "rf-stored" (make-array java.nio.file.attribute.FileAttribute 0)))
                        src (fresh)]
                    (dotimes [i population]
                      (v/assert src (list 'rf_dog (ind "RfD" i)) 'CxPerf {:strength :monotonic}))
                    (v/export! src dir {})
                    (let [kb (fresh)]
                      (v/import! kb dir {:belief? :stored})
                      (binding [v/*write-unrecovered?* true]
                        (v/assert kb '(disjoint rf_animal rf_plant) 'CxPerf {:strength :monotonic})
                        (prof/start)
                        (v/assert kb '(genl rf_dog rf_animal) 'CxPerf {:strength :monotonic})
                        (let [snap (prof/stop)]
                          {:fetches  (reduce + 0 (vals (:fetches snap)))
                           :believed (v/query? kb '(rf_dog RfD0) 'CxPerf)})))))
          narrow (probe 20)
          wide   (probe 200)]
      (is (false? (:believed wide)) "the imported members are stored and not believed")
      (is (= (:fetches narrow) (:fetches wide))
          (str "the edge's fetches must be flat in how many unbelieved members sit below "
               "it — a record is paged before its belief is asked again ("
               (:fetches narrow) " -> " (:fetches wide) ")")))))

(deftest a-genl-edge-pages-the-mint-family-not-the-extent-below-it
  ;; A `genl` edge asks whether it made a minted membership redundant, and a member below
  ;; its sub-type can only be asked about a mint it holds.  It paged every membership below
  ;; the sub-type to learn its term and then looked the term up in the mint family — during an
  ;; ontology install into a large store, half of a settle.  The edge's other reads page the
  ;; members too, for reasons of their own, so what is priced is the difference pruning
  ;; makes: with one mint in the family, it must not grow with the members.
  (tu/with-shipped-config
    (let [probe (fn [population prune?]
                  (binding [argument/*assertive-arg-types?* true
                            checks/*prune-subsumed-mints?* prune?]
                    (let [kb (fresh)]
                      (v/assert kb '(genlCx CxPerf CxUniverse) 'CxUniverse)
                      (v/assert kb '(genl rf_owner thing) 'CxPerf {:strength :monotonic})
                      (v/assert kb '(arg rfOwns 1 rf_owner) 'CxPerf {:strength :monotonic})
                      (v/assert kb '(rfOwns RfA RfThing) 'CxPerf {})
                      (dotimes [i population]
                        (v/assert kb (list 'rf_sub (ind "RfM" i)) 'CxPerf {}))
                      (prof/start)
                      (v/assert kb '(genl rf_sub rf_super) 'CxPerf {:strength :monotonic})
                      (let [snap (prof/stop)]
                        {:fetches (reduce + 0 (vals (:fetches snap)))
                         :minted  (some? (v/handle-of kb '(rf_owner RfA) 'CxPerf))}))))
          pruning (fn [population]
                    (- (long (:fetches (probe population true)))
                       (long (:fetches (probe population false)))))]
      (is (:minted (probe 20 true)) "the declaration minted its membership, so the mint family holds one")
      (is (= (pruning 20) (pruning 200))
          (str "what pruning pages on a genl edge must be flat in the members below it that "
               "hold no mint (" (pruning 20) " -> " (pruning 200) ")")))))

(deftest a-genl-edge-pages-the-readers-of-a-lazy-conclusion-once-per-functor
  (tu/with-shipped-config
    (let [k     4
          probe (fn [readers]
                  (let [kb (doto (fresh) (tu/load-core!))]
                    (v/assert kb '(genlCx CxPerf CxUniverse) 'CxUniverse)
                    (dotimes [i readers]
                      (v/assert kb (list 'set/forwardRule
                                         (list 'implies (list 'and '(arity ?r 2) (list (symbol (str "rf_tag" i)) '?r))
                                               (list (symbol (str "rf_tagged" i)) '?r)))
                                'CxPerf))
                    (prof/start)
                    (dotimes [i n]
                      (v/assert kb (list 'genl (ind "rf_kind" i) 'binary_predicate) 'CxPerf {:strength :monotonic}))
                    (long (get-in (prof/stop) [:fetches :sentex] 0))))]
      (is (= (* n k) (- (probe k) (probe 0)))
          (str "the upper ontology's five arity converses conclude `arity`, and an edge into "
               "binary_predicate reaches the `binary` one reads: " k " more readers of `arity` "
               "must add " k " sentex fetches per edge, not " (* 5 k))))))

(deftest a-lazy-reader-s-batch-re-join-reads-each-owing-membership-once
  (tu/with-shipped-config
    (let [probe (fn [tagged members]
                  (let [kb (fresh)]
                    (v/assert kb '(set/lazyForwardRule (implies (rf_cls ?r) (rfArity ?r 2))) 'CxPerf)
                    (v/assert kb '(set/forwardRule (implies (and (rf_tag ?r) (rfArity ?r ?n)) (rf_out ?r)))
                              'CxPerf)
                    (dotimes [i 300] (v/assert kb (list 'rfArity (ind "RfS" i) 3) 'CxPerf))
                    (dotimes [i tagged] (v/assert kb (list 'rf_tag (ind "RfT" i)) 'CxPerf))
                    (prof/start)
                    (v/with-deferred-settle kb
                      (v/assert kb '(rf_cls RfT0) 'CxPerf)
                      (dotimes [i members] (v/assert kb (list 'rf_cls (ind "RfM" i)) 'CxPerf)))
                    [(long (get-in (prof/stop) [:fetches :sentex] 0))
                     (v/query? kb '(rf_out RfT0) 'CxPerf)]))
          per   (fn [tagged]
                  (let [[few fired] (probe tagged 10)
                        [many]      (probe tagged 20)]
                    (is fired "the tagged member's firing proves the lazy literal")
                    (- many few)))
          [a b] [(per 10) (per 100)]]
      (is (= a b)
          (str "the reader joins `(rf_tag ?r)` before the lazy `(rfArity ?r ?n)`, so the "
               "settle proves the lazy literal once per tagged relation from the owing "
               "memberships (`chain/delta-lazy-rows`): ten more memberships must add the same "
               "sentex fetches beside 10 tagged relations as beside 100 (" a " -> " b ")")))))

(deftest a-run-reads-each-reader-of-a-lazy-conclusion-once
  (tu/with-shipped-config
    (let [k     4
          probe (fn [readers members]
                  (let [kb (fresh)]
                    (v/assert kb '(set/lazyForwardRule (implies (rf_cls ?r) (rfArity ?r 2))) 'CxPerf)
                    (dotimes [i readers]
                      (v/assert kb (list 'set/inertRule
                                         (list 'implies (list 'and '(rfArity ?r 2) (list (ind "rf_tag" i) '?r))
                                               (list (ind "rf_tagged" i) '?r)))
                                'CxPerf))
                    (dotimes [i members] (v/assert kb (list 'rf_src (ind "RfM" i)) 'CxPerf))
                    (prof/start)
                    (v/assert kb '(set/forwardRule (implies (rf_src ?x) (rf_cls ?x))) 'CxPerf)
                    (long (get-in (prof/stop) [:fetches :sentex] 0))))
          added (fn [members] (- (probe k members) (probe 0 members)))
          [a b] [(added 10) (added 20)]]
      (is (= a b)
          (str "the rule's arrival concludes one `rf_cls` membership per `rf_src` member in "
               "one run, and each owes the inert readers of `rfArity` a re-join "
               "(`chain/lazy-readers`): " k " readers must add the same sentex fetches to a "
               "run concluding 10 memberships as to one concluding 20 (" a " -> " b ")")))))

(deftest a-type-antecedent-no-declared-type-reaches-pages-no-declaration-per-rule
  (tu/with-shipped-config
    (let [probe (fn [declared? rules]
                  (let [kb (fresh)]
                    (when declared?
                      (v/assert kb '(result RfMakeFn rf_cat) 'CxPerf {:strength :monotonic})
                      (v/assert kb '(resultArg RfKindFn 2) 'CxPerf {:strength :monotonic})
                      (v/assert kb '(rfHolds RfA (RfKindFn RfB rf_cat)) 'CxPerf {}))
                    (dotimes [i rules] (v/assert kb (list (ind "rf_dog" i) (ind "RfD" i)) 'CxPerf {}))
                    (prof/start)
                    (dotimes [i rules]
                      (v/assert kb (rules/rule-sentence [(list (ind "rf_dog" i) '?x)] '(rf_animal ?x))
                                'CxPerf {:direction :forward :strength :monotonic}))
                    [(reduce + 0 (vals (:fetches (prof/stop))))
                     (v/query? kb (list 'rf_animal (ind "RfD" (dec rules))) 'CxPerf)]))
          added (fn [rules]
                  (let [[with fired] (probe true rules)
                        [without]    (probe false rules)]
                    (is fired "the last rule concludes over its member")
                    (- (long with) (long without))))
          few   (added 10)
          many  (added 100)]
      (is (= few many)
          (str "each rule joins `(rf_dogN ?x)` with `?x` open, and the declarations type "
               "applications as `rf_cat` alone, so they must add the same fetches to 10 "
               "rules as to 100 (" few " -> " many ")")))))

(deftest a-backward-goal-pages-no-rule-its-argument-heads-exclude
  (tu/with-shipped-config
    (let [probe (fn [rules]
                  (let [kb (fresh)]
                    (v/assert kb '(rf_src RfStart) 'CxPerf {:strength :monotonic})
                    (v/assert kb (rules/rule-sentence ['(rf_src ?x)] '(rfLinked ?x RfEnd))
                              'CxPerf {:strength :monotonic})
                    (dotimes [i rules]
                      (v/assert kb (rules/rule-sentence [(list 'rf_src (ind "RfK" i))]
                                                        (list 'rfLinked (list 'RfPairFn (ind "RfK" i)) 'RfEnd))
                                'CxPerf {:strength :monotonic}))
                    (prof/start)
                    (let [answer (v/query? kb '(rfLinked RfStart RfEnd) 'CxPerf {:max-depth 2})]
                      [(reduce + 0 (vals (:fetches (prof/stop)))) answer])))
          [few answered] (probe 10)
          [many]         (probe 100)]
      (is answered "the rule concluding `(rfLinked ?x RfEnd)` answers the goal")
      (is (= few many)
          (str "no `(rfLinked (RfPairFn RfKN) RfEnd)` consequent has an argument headed by "
               "`RfStart`, so the goal pages none of them: 100 must cost the fetches 10 do ("
               few " -> " many ")")))))

(deftest a-context-edge-pages-the-marked-facts-not-the-context
  ;; A `genlCx` edge equates what a functional predicate's facts force across the contexts
  ;; it joins, so its candidates are the facts of marked predicates in the widened
  ;; ancestor set.  It paged every fact in those contexts and then asked each for a mark:
  ;; an edge into a large store's context paged every fact of it, once per edge of an
  ;; ontology install.  The edge's other reads page the believed facts for reasons of
  ;; their own, so what is priced is the difference the declaration makes: with one
  ;; marked fact, it must not grow with the unmarked ones.
  (tu/with-shipped-config
    (let [probe (fn [population functional?]
                  (let [kb (fresh)]
                    (v/assert kb '(genlCx CxRfBig CxUniverse) 'CxUniverse)
                    (when functional?
                      (v/assert kb '(functional rfMotherOf) 'CxUniverse {:strength :monotonic}))
                    (v/assert kb '(rfMotherOf RfKid RfMum) 'CxRfBig {})
                    (dotimes [i population]
                      (v/assert kb (list 'rfLikes (ind "RfX" i) 'RfY) 'CxRfBig {}))
                    (prof/start)
                    (v/assert kb '(genlCx CxRfSmall CxRfBig) 'CxUniverse {:strength :monotonic})
                    (let [snap (prof/stop)]
                      (reduce + 0 (vals (:fetches snap))))))
          marking (fn [population] (- (long (probe population true)) (long (probe population false))))]
      (is (= (marking 20) (marking 200))
          (str "what the functional mark pages on a genlCx edge must be flat in the unmarked "
               "facts of the contexts it widens (" (marking 20) " -> " (marking 200) ")")))))

(deftest a-recover-walks-the-types-under-its-edges-once
  ;; A `recover` brings every record IN in one settle, so every `genl` edge asks at once
  ;; which mints it gave a new route, and each asked for the types under its own sub: a
  ;; closure walk and a count read per type, per edge.  Over a subtree many edges leave
  ;; from, that is the subtree once per edge, so a recover grows with edges times subtree
  ;; rather than with the taxonomy.  Each edge moved still costs pruning a read or so of
  ;; its own, so what is priced is what one more edge adds, and it must not grow with the
  ;; subtree under it.  The walk reads index counts, not records, so both are summed.
  (tu/with-shipped-config
    (let [probe (fn [depth edges prune?]
                  (binding [argument/*assertive-arg-types?* true
                            checks/*prune-subsumed-mints?* prune?]
                    (let [dir (str (java.nio.file.Files/createTempDirectory
                                    "rf-recover" (make-array java.nio.file.attribute.FileAttribute 0)))
                          src (fresh)]
                      (v/assert src '(genlCx CxPerf CxUniverse) 'CxUniverse)
                      (v/assert src '(genl rf_owner thing) 'CxPerf {:strength :monotonic})
                      (v/assert src '(arg rfOwns 1 rf_owner) 'CxPerf {:strength :monotonic})
                      (v/assert src '(rfOwns RfA RfThing) 'CxPerf {})
                      (dotimes [i depth]
                        (v/assert src (list 'genl (ind "rf_chain" i) (ind "rf_chain" (inc i)))
                                  'CxPerf {:strength :monotonic}))
                      (dotimes [i edges]
                        (v/assert src (list 'genl (ind "rf_chain" depth) (ind "rf_up" i))
                                  'CxPerf {:strength :monotonic}))
                      (v/export! src dir {})
                      ;; stored, not believed: the recover brings every record IN, as a
                      ;; build's finish stage does
                      (let [kb (fresh)]
                        (v/import! kb dir {:belief? :stored})
                        (prof/start)
                        (v/recover kb)
                        (let [snap (prof/stop)]
                          {:cost   (+ (reduce + 0 (vals (:fetches snap)))
                                      (reduce + 0 (vals (:reads snap))))
                           :minted (some? (v/handle-of kb '(rf_owner RfA) 'CxPerf))})))))
          pruning (fn [depth edges]
                    (- (long (:cost (probe depth edges true)))
                       (long (:cost (probe depth edges false)))))
          per-30  (fn [depth] (- (pruning depth 40) (pruning depth 10)))]
      (is (:minted (probe 5 10 true)) "the declaration minted its membership, so the mint family holds one")
      (is (= (per-30 5) (per-30 20))
          (str "what thirty more edges add to pruning in a recover must not grow with the "
               "subtree under them (" (per-30 5) " -> " (per-30 20) ")")))))

(deftest a-recover-pages-the-defeats-not-the-store
  ;; A `recover`'s settle relabels every stored sentex, and the settle posts the re-check
  ;; each relabelled `defeat` owes its target.  What is priced is the difference one
  ;; stored defeat makes, and it must not grow with the facts beside it.
  (tu/with-shipped-config
    (let [probe (fn [population defeat?]
                  (let [kb (fresh)]
                    (dotimes [i population]
                      (v/assert kb (list 'rfPlain (ind "RfP" i) 'RfQ) 'CxPerf {}))
                    (when defeat?
                      (v/assert kb '(rf_denied RfN) 'CxPerf {})
                      (v/assert kb '(not (rf_denied RfN)) 'CxPerf {:strength :monotonic}))
                    (prof/start)
                    (v/recover kb)
                    (reduce + 0 (vals (:fetches (prof/stop))))))
          defeat (fn [population] (- (long (probe population true)) (long (probe population false))))]
      (is (= (defeat 20) (defeat 200))
          (str "what a stored defeat pages in a recover must be flat in the facts beside it ("
               (defeat 20) " -> " (defeat 200) ")")))))

(deftest a-recover-pages-the-mints-not-the-store
  ;; A `recover`'s settle brings every record IN, and the mint withdrawal asks the stored
  ;; mints the whole question when fewer are stored than the region holds.  What is priced
  ;; is the difference one stored mint makes, and it must not grow with the facts beside it.
  (tu/with-shipped-config
    (binding [argument/*assertive-arg-types?* true
              checks/*prune-subsumed-mints?* true]
      (let [probe (fn [population mint?]
                    (let [kb (fresh)]
                      (dotimes [i population]
                        (v/assert kb (list 'rfPlain (ind "RfP" i) 'RfQ) 'CxPerf {}))
                      (when mint?
                        (v/assert kb '(genl rf_owner thing) 'CxPerf {:strength :monotonic})
                        (v/assert kb '(arg rfOwns 1 rf_owner) 'CxPerf {:strength :monotonic})
                        (v/assert kb '(rfOwns RfA RfThing) 'CxPerf {}))
                      (prof/start)
                      (v/recover kb)
                      (reduce + 0 (vals (:fetches (prof/stop))))))
            mint  (fn [population] (- (long (probe population true)) (long (probe population false))))]
        (is (= (mint 20) (mint 200))
            (str "what a stored mint pages in a recover must be flat in the facts beside it ("
                 (mint 20) " -> " (mint 200) ")"))))))

(deftest a-forced-monotonic-declaration-pages-no-rule-reading-its-predicate
  (tu/with-shipped-config
    (let [probe (fn [rules]
                  (let [kb (fresh)]
                    (v/assert kb '(forced_monotonic_predicate rf_kept) 'CxPerf {:strength :monotonic})
                    (dotimes [i rules]
                      (v/assert kb (rules/rule-sentence ['(rf_kept ?x)] (list (ind "rf_out" i) '?x))
                                'CxPerf {:strength :monotonic}))
                    (prof/start)
                    (let [held (doall (for [i (range 10)
                                            :let [fact (list 'rfPlain (ind "RfA" i) 'RfB)]]
                                        (do (v/assert kb fact 'CxPerf {})
                                            (v/query? kb fact 'CxPerf))))]
                      [(reduce + 0 (vals (:fetches (prof/stop)))) held])))
          [few held] (probe 10)
          [many]     (probe 100)]
      (is (every? true? held) "each write is believed")
      (is (= few many)
          (str "ten writes and queries beside 10 or 100 rules reading a forced-monotonic "
               "predicate must page the same records, since `exc/forced-reads?` reads the "
               "rules' contexts off the index (" few " -> " many ")")))))

(deftest a-write-naming-an-application-pages-no-correspondence-declaration
  (tu/with-shipped-config
    (let [probe (fn [decls]
                  (let [kb (fresh)]
                    (v/assert kb '(reifiable_function RfFruitFn) 'CxPerf {:strength :monotonic})
                    (v/assert kb '(functionCorrespondingPredicate RfFruitFn rfFruitOf 2) 'CxPerf
                              {:strength :monotonic})
                    (dotimes [i decls]
                      (v/assert kb (list 'functionCorrespondingPredicate (ind "RfFn" i) (ind "rfPred" i) 2)
                                'CxPerf {:strength :monotonic}))
                    (v/assert kb '(rfLikes RfAnn (RfFruitFn RfTree)) 'CxPerf {})
                    (prof/start)
                    (dotimes [i 10]
                      (v/assert kb (list 'rfLikes 'RfAnn (list 'RfFruitFn (ind "RfTree" i))) 'CxPerf {}))
                    [(reduce + 0 (vals (:fetches (prof/stop))))
                     (v/query? kb '(rfLikes RfAnn (RfFruitFn RfTree9)) 'CxPerf)]))
          [few held] (probe 10)
          [many]     (probe 100)]
      (is held "the last write is believed")
      (is (= few many)
          (str "ten writes naming an application beside 10 or 100 correspondence "
               "declarations must page the same records, since `res/stored-correspondences` "
               "holds the declarations' records (" few " -> " many ")")))))

(deftest a-named-target-write-pages-no-justification-another-informant-gave
  (tu/with-shipped-config
    (let [probe (fn [rules]
                  (let [kb (fresh)]
                    (doseq [s '[(reifiable_function RfQualFn)
                                (result RfQualFn rf_qualified)
                                (functionCorrespondingPredicate RfQualFn rfQualOf 2)
                                (rewriteOf RfRoot (RfQualFn RfBase))]]
                      (v/assert kb s 'CxUniverse))
                    (dotimes [i rules]
                      (v/assert kb (rules/rule-sentence ['(rfTagged ?x ?t)] (list (ind "rf_out" i) '?t))
                                'CxUniverse {:direction :forward}))
                    (prof/start)
                    (dotimes [i 10] (v/assert kb (list 'rfTagged 'RfRoot (ind "RfTag" i)) 'CxUniverse))
                    [(:justification (:fetches (prof/stop)) 0)
                     (v/ask? kb '(rfQualOf RfBase RfRoot) 'CxUniverse)]))
          [few named] (probe 10)
          [many]      (probe 100)]
      (is (true? named) "the named application's projection holds")
      (is (= few many)
          (str "ten writes naming the target, each the antecedent of 10 or 100 rule firings "
               "that do not name it, must page the same justifications, since "
               "`named-application/sync!` reads the informant off the network (" few " -> "
               many ")")))))

(deftest a-genl-edge-reads-each-rule-reading-genl-once
  (tu/with-shipped-config
    (let [probe (fn [rules]
                  (let [kb (fresh)]
                    (dotimes [i rules]
                      (v/assert kb (rules/rule-sentence [(list 'genl '?p (ind "rf_top" i))] '(rf_kindish ?p))
                                'CxPerf {:direction :forward}))
                    (prof/start)
                    (dotimes [i 10] (v/assert kb (list 'genl (ind "rf_kind" i) 'rf_base) 'CxPerf))
                    (reduce + 0 (vals (:fetches (prof/stop))))))
          few  (probe 10)
          many (probe 100)]
      (is (<= (- many few) (* 10 90))
          (str "ten edges beside 90 more rules reading `genl`, none reaching the edge, must read "
               "each rule's record at most once per edge, since `chain/closure-rejoins` and the "
               "trigger share one read (" few " -> " many ")")))))

(deftest the-instrument-counts-nothing-when-off
  ;; The budgets are only meaningful if the call sites add no work when nobody is collecting.
  (testing "a workload outside `start`/`stop` records no fetch"
    (is (false? (prof/profiling?)))
    ((ground-assert))
    (is (nil? (prof/snapshot)))))
