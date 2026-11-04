;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.relation-properties-test
  "The four relation properties, enforced rather than declared, and
  `negates` beside them:

  * **`irreflexive`** — a self tuple `(P a a)` is a one-member nogood each reader
    decides: a `:default` one is OUT where the mark is read, a `:monotonic` one is a
    hard clash in `conflicts`.
  * **`anti_symmetric`** — a believed converse `(P b a)` of two symbols merges the two
    arguments, deriving `(equals a b)`; a converse of two arguments no merge reconciles
    is a two-member nogood each reader decides.
  * **`anti_transitive`** — the two-step chain and the direct step are convicted
    **together**, as the one nogood whose members are three rather than two
    (docs/nmtms.md).  Its classification and `(disjoint transitive anti_transitive)` are
    enforced beside that.
  * **`equivalence_relation`** — no engine code: three CxUniverse forward rules derive
    `symmetric`, `transitive` and `reflexive`, each enforced in turn.
  * **`negates`** — two tuples of one argument list under the two sides are a nogood, a
    declaration whose sides' lengths no argument list fits is a clash of the
    declaration, and a ground denial is answered from the other side.

  A vocabulary KB on the collapsed single-predicate model (an algebraic property is one
  predicate, not a mark and a twin): each new property is one predicate with `(genl X
  binary_predicate)`, and the lattice sits on the bare marks — so the SHIPPED declarations
  are what is tested, not a hand-built fixture that could drift from the file."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.decide.arity :as arity]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(def U 'CxUniverse)

(defn- believed-at?
  "Is `s`, stored in `ctx`, believed as `reader` reads it?"
  ([kb s ctx] (believed-at? kb s ctx ctx))
  ([kb s ctx reader]
   (boolean (some-> (v/handle-of kb s ctx) (as-> h (v/believed? kb h reader))))))

(defn- clash-kinds
  "`{:conflicts #{[kind sentence]} :contradictions #{[kind sentence]}}` of every report."
  [kb]
  {:conflicts      (into #{} (map (juxt :kind :sentence)) (v/conflicts kb))
   :contradictions (into #{} (map (juxt :kind :sentence)) (v/contradictions kb))})

(defn- readings
  "Run the thunks of `steps` in each order of their keys, and answer the distinct
  `[belief reports]` readings: `read` gives the belief, `clash-kinds` the reports.  One
  reading means every order agrees."
  [kb steps read]
  (into #{}
        (for [order (tu/orders (sort (keys steps)))]
          (let [hs (mapv #((steps %)) order)
                r  [(read) (clash-kinds kb)]]
            (run! #(v/retract! kb %) (rseq hs))
            r))))

;;; ── irreflexive: a self tuple is a one-member nogood ─────────────────────────

(defn- placed
  "The stored `contradicts` and `defeat` sentexes, each as `[sentence context]` with its
  `sentexHandle` arguments resolved."
  [kb]
  (into #{} (for [f '[contradicts defeat]
                  s (v/sentexes-with-functor kb f)]
              (tu/handle-free kb [(:sentence s) (:context s)]))))

(tu/deftest-kb a-self-tuple-under-a-descended-mark-is-placed-and-no-reader-decides-it
  ;;   CxUniverse  (irreflexive before)
  ;;     └─ CxS    (genl beforeStrict before)  (beforeStrict Alice Alice) default
  (tu/with-terms [before beforeStrict Alice CxS]
    (v/assert kb (list 'genlCx CxS U) U)
    (let [mark (v/assert kb (list 'irreflexive before) U)
          edge (v/assert kb (list 'genl beforeStrict before) CxS)
          self (v/assert kb (list beforeStrict Alice Alice) CxS)
          L    [(list beforeStrict Alice Alice) CxS]]
      (testing "the contradicts and the defeat of the self tuple are stored at CxS"
        (is (= #{[(list 'contradicts L) CxS] [(list 'defeat L) CxS]} (placed kb))))
      (testing "the mark and the predicate edge the reading climbed are grounds"
        (let [[c] (v/sentexes-with-functor kb 'contradicts)]
          (is (every? (set (mapcat :antecedents (v/supporting-justifications kb (:id c))))
                      [self mark edge]))))
      (testing "no reader decides the self tuple, and the defeat hides it at CxS"
        (is (false? (v/believed? kb self CxS))))
      (testing "retracting the edge takes the placed sentexes out"
        (v/retract! kb edge)
        (is (empty? (placed kb)))
        (is (true? (v/believed? kb self CxS)))))))

(tu/deftest-kb an-irreflexive-mark-takes-a-default-self-tuple-out-in-either-order
  (tu/with-terms [before Alice Bob]
    (let [self (list before Alice Alice)
          rs   (readings kb {:mark  #(v/assert kb (list 'irreflexive before) U)
                             :tuple #(v/assert kb self U)}
                         #(believed-at? kb self U))]
      (is (= #{[false {:conflicts #{} :contradictions #{}}]} rs)
          "stored in both orders, OUT at the reader that reads the mark, and reported nowhere"))
    (testing "check reports nothing, since nothing is refused"
      (v/assert kb (list 'irreflexive before) U)
      (is (empty? (v/check kb (list before Alice Alice) U))))
    (testing "an ordinary non-self tuple of the same predicate is believed"
      (v/assert kb (list before Alice Bob) U)
      (is (believed-at? kb (list before Alice Bob) U)))))

(tu/deftest-kb a-mark-stated-beside-its-excepted-derivation-convicts-at-the-excepting-reader
  ;;   CxUniverse  (injection ageRel) monotonic; a core.txt rule derives (functional ageRel)
  ;;     └─ CxHid  (ageRel Tom 1) default  (ageRel Tom 2) monotonic  (except (injection ageRel))
  ;; CxHid reads no mark while the derivation alone states it.  The mark stated as well
  ;; convicts the pair there, and the placement reads the network: the default filler its
  ;; own defeat hides at CxHid is no reason to move the placement.
  (tu/with-terms [ageRel Tom CxHid]
    (v/assert kb (list 'genlCx CxHid U) U)
    (let [M   {:strength :monotonic}
          inj (v/assert kb (list 'injection ageRel) U M)
          los (v/assert kb (list ageRel Tom 1) CxHid)]
      (v/assert kb (list ageRel Tom 2) CxHid M)
      (v/assert kb (list 'except (list 'sentexHandle inj)) CxHid M)
      (is (true? (v/believed? kb los CxHid)) "the excepted derivation states no mark at CxHid")
      (v/assert kb (list 'functional ageRel) U M)
      (is (false? (v/believed? kb los CxHid)) "the stated mark convicts the pair at CxHid"))))

(tu/deftest-kb a-monotonic-self-tuple-under-an-irreflexive-mark-is-a-conflict-in-either-order
  (tu/with-terms [before Alice]
    (let [self (list before Alice Alice)
          rs   (readings kb {:mark  #(v/assert kb (list 'irreflexive before) U)
                             :tuple #(v/assert kb self U {:strength :monotonic})}
                         #(believed-at? kb self U))]
      (is (= #{[true {:conflicts #{[:irreflexive (list 'contradicts self)]}
                      :contradictions #{}}]}
             rs)
          "believed, and reported as a hard clash, in both orders"))))

(tu/deftest-kb retracting-the-irreflexive-declaration-restores-the-self-tuple
  (tu/with-terms [before Alice]
    (let [decl (v/assert kb (list 'irreflexive before) U)]
      (v/assert kb (list before Alice Alice) U)
      (is (not (believed-at? kb (list before Alice Alice) U)))
      (v/retract! kb decl)
      (is (believed-at? kb (list before Alice Alice) U)))))

(tu/deftest-kb a-self-tuple-under-a-descended-irreflexive-mark-is-out-in-every-order
  ;; The mark on `near`, the tuple of `nearish` beneath it, and the edge between them:
  ;; any of the three can arrive last.
  (tu/with-terms [near nearish Dora]
    (let [self (list nearish Dora Dora)]
      (is (= #{[false {:conflicts #{} :contradictions #{}}]}
             (readings kb {:mark  #(v/assert kb (list 'irreflexive near) U)
                           :edge  #(v/assert kb (list 'genl nearish near) U)
                           :tuple #(v/assert kb self U)}
                       #(believed-at? kb self U)))))))

(tu/deftest-kb a-conclusion-resting-on-an-irreflexive-loser-is-withdrawn-with-it
  (tu/with-terms [near warm_blooded Dora]
    (v/assert kb (list 'set/forwardRule (list 'implies (list near '?x '?x) (list warm_blooded '?x)))
              U {:strength :monotonic})
    (v/assert kb (list near Dora Dora) U)
    (is (believed-at? kb (list warm_blooded Dora) U))
    (v/assert kb (list 'irreflexive near) U)
    (is (not (believed-at? kb (list near Dora Dora) U)))
    (is (not (believed-at? kb (list warm_blooded Dora) U))
        "the conclusion rests only on the loser")))

;;; ── anti_symmetric: a believed converse merges the two arguments ───────

(defn- merged?
  "Is the antisymmetric-derived `(equals a b)` stored and believed — the merge landed?
  `ask?` on the equality is not the read: a closed goal is rewritten to the
  representative before lookup, so the belief of the derived sentex is read off its
  handle directly, the way `equality_test` reads a migrated twin."
  [kb a b ctx]
  (let [[lo hi] (sort [a b])
        h       (v/handle-of kb (list 'equals lo hi) ctx)]
    (boolean (and h (v/in? kb h)))))

(tu/deftest-kb an-antisymmetric-converse-derives-an-equality
  (tu/with-terms [atOrAbove Alice Bob]
    (v/assert kb (list 'anti_symmetric atOrAbove) U)
    (v/assert kb (list atOrAbove Alice Bob) U {:strength :monotonic})
    (testing "no merge from one direction alone"
      (is (not (merged? kb Alice Bob U))))
    (v/assert kb (list atOrAbove Bob Alice) U {:strength :monotonic})
    (testing "the converse forces the equality"
      (is (merged? kb Alice Bob U)))
    (testing "and it is a derivation, not a premise, justified by both facts and the mark"
      (let [[lo hi] (sort [Alice Bob])
            eqh     (v/handle-of kb (list 'equals lo hi) U)]
        (is (some? eqh))
        (is (v/in? kb eqh))
        (is (false? (v/premise? kb eqh)))))))

(tu/deftest-kb the-antisymmetric-merge-is-the-same-in-both-arrival-orders
  (doseq [order [:fact-then-converse :converse-then-fact]]
    (testing order
      (tu/with-terms [atOrAbove Alice Bob]
        (v/assert kb (list 'anti_symmetric atOrAbove) U)
        (if (= order :fact-then-converse)
          (do (v/assert kb (list atOrAbove Alice Bob) U {:strength :monotonic})
              (v/assert kb (list atOrAbove Bob Alice) U {:strength :monotonic}))
          (do (v/assert kb (list atOrAbove Bob Alice) U {:strength :monotonic})
              (v/assert kb (list atOrAbove Alice Bob) U {:strength :monotonic})))
        (is (merged? kb Alice Bob U))))))

(tu/deftest-kb a-converse-stated-through-a-sub-predicate-merges-and-rests-on-the-edge
  (tu/with-terms [atOrAbove strictlyAbove Alice Bob]
    (v/assert kb (list 'anti_symmetric atOrAbove) U)
    (let [edge (v/assert kb (list 'genl strictlyAbove atOrAbove) U)]
      (v/assert kb (list atOrAbove Alice Bob) U {:strength :monotonic})
      (v/assert kb (list strictlyAbove Bob Alice) U {:strength :monotonic})
      (is (merged? kb Alice Bob U) "the sub-predicate's fact is a converse of the marked one")
      (v/retract! kb edge)
      (is (not (merged? kb Alice Bob U))
          "the merge goes with the genl edge that made the two functors one relation"))))

(tu/deftest-kb an-antisymmetric-declaration-arriving-last-still-merges
  ;; The retroactive direction — `special/antisym-equate-existing` — so the answer does
  ;; not depend on whether the mark or the facts were written first.
  (tu/with-terms [atOrAbove Alice Bob]
    (v/assert kb (list atOrAbove Alice Bob) U {:strength :monotonic})
    (v/assert kb (list atOrAbove Bob Alice) U {:strength :monotonic})
    (is (not (merged? kb Alice Bob U)) "no mark yet, no merge")
    (v/assert kb (list 'anti_symmetric atOrAbove) U)
    (is (merged? kb Alice Bob U) "the declaration reaches the stored pair")))

(tu/deftest-kb retracting-a-supporting-fact-un-merges-the-antisymmetric-equality
  (tu/with-terms [atOrAbove Alice Bob]
    (v/assert kb (list 'anti_symmetric atOrAbove) U)
    (v/assert kb (list atOrAbove Alice Bob) U {:strength :monotonic})
    (let [converse (v/assert kb (list atOrAbove Bob Alice) U {:strength :monotonic})]
      (is (merged? kb Alice Bob U))
      (v/retract! kb converse)
      (testing "one direction gone, the equality goes with it"
        (is (not (merged? kb Alice Bob U)))))))

(tu/deftest-kb retracting-the-antisymmetric-declaration-un-merges
  (tu/with-terms [atOrAbove Alice Bob]
    (let [decl (v/assert kb (list 'anti_symmetric atOrAbove) U)]
      (v/assert kb (list atOrAbove Alice Bob) U {:strength :monotonic})
      (v/assert kb (list atOrAbove Bob Alice) U {:strength :monotonic})
      (is (merged? kb Alice Bob U))
      (v/retract! kb decl)
      (testing "the merge rested on the mark, and un-does when it goes"
        (is (not (merged? kb Alice Bob U)))))))

(tu/deftest-kb a-self-tuple-of-an-antisymmetric-predicate-is-admitted
  ;; Its converse is itself and (equals a a) is trivial, so nothing merges and nothing
  ;; refuses — the CxUniverse comment's promise.
  (tu/with-terms [atOrAbove Alice]
    (v/assert kb (list 'anti_symmetric atOrAbove) U)
    (is (v/assert kb (list atOrAbove Alice Alice) U))
    (is (v/ask? kb (list atOrAbove Alice Alice) U))))

(tu/deftest-kb an-antisymmetric-converse-no-merge-can-reconcile-is-a-nogood-in-every-order
  ;; Two numbers a converse forces equal, which no merge can make one thing: a two-member
  ;; nogood each reader decides from the members' classes.
  (doseq [[label [c12 c21] want] [["the :default member loses" [:default :monotonic]
                                   [[false true] {:conflicts #{} :contradictions #{}}]]
                                  ["two :default members are a dilemma" [:default :default]
                                   [[true true] {:conflicts #{} :contradictions #{:pair}}]]
                                  ["two :monotonic members are a conflict" [:monotonic :monotonic]
                                   [[true true] {:conflicts #{:pair} :contradictions #{}}]]]]
    (testing label
      (tu/with-terms [atOrAbove]
        (let [pair  [:anti-symmetric (list 'contradicts (list atOrAbove 1 2) (list atOrAbove 2 1))]
              [b r] want
              want  [b (update-vals r #(if (seq %) #{pair} #{}))]]
          (is (= #{want}
                 (readings kb {:mark #(v/assert kb (list 'anti_symmetric atOrAbove) U)
                               :a    #(v/assert kb (list atOrAbove 1 2) U {:strength c12})
                               :b    #(v/assert kb (list atOrAbove 2 1) U {:strength c21})}
                           #(vector (believed-at? kb (list atOrAbove 1 2) U)
                                    (believed-at? kb (list atOrAbove 2 1) U))))))))))

(tu/deftest-kb a-converse-pair-is-decided-at-the-joint-reader-and-nowhere-above-it
  ;; One direction in `CxA`, the other in `CxB`, and `CxJ` below both: `CxJ` reads the
  ;; nogood and takes the `:default` member OUT, and `CxA` reads no converse, whatever
  ;; the order the facts and the reader's edges arrive in.  CxUniverse lifts the mark to
  ;; CxUniverse, so every context reads it.
  (tu/with-terms [atOrAbove CxA CxB CxJ]
    (v/assert kb (list 'genlCx CxA U) U)
    (v/assert kb (list 'genlCx CxB U) U)
    (v/assert kb (list 'anti_symmetric atOrAbove) U)
    (is (= #{[[true false true] {:conflicts #{} :contradictions #{}}]}
           (readings kb {:a    #(v/assert kb (list atOrAbove 1 2) CxA)
                         :b    #(v/assert kb (list atOrAbove 2 1) CxB {:strength :monotonic})
                         :to-a #(v/assert kb (list 'genlCx CxJ CxA) U)
                         :to-b #(v/assert kb (list 'genlCx CxJ CxB) U)}
                     #(vector (believed-at? kb (list atOrAbove 1 2) CxA)
                              (believed-at? kb (list atOrAbove 1 2) CxA CxJ)
                              (believed-at? kb (list atOrAbove 2 1) CxB CxJ)))))))

(tu/deftest-kb an-unmergeable-converse-under-a-descended-mark-is-decided-in-every-order
  ;; A converse of two numbers is found under the tuple's own functor
  ;; (`tuple/converse-handles`), so both directions are spelled with the sub-predicate.
  (tu/with-terms [atOrAbove atOrAboveStrict]
    (is (= #{[[false true] {:conflicts #{} :contradictions #{}}]}
           (readings kb {:mark     #(v/assert kb (list 'anti_symmetric atOrAbove) U)
                         :edge     #(v/assert kb (list 'genl atOrAboveStrict atOrAbove) U)
                         :fact     #(v/assert kb (list atOrAboveStrict 1 2) U)
                         :converse #(v/assert kb (list atOrAboveStrict 2 1) U
                                              {:strength :monotonic})}
                     #(vector (believed-at? kb (list atOrAboveStrict 1 2) U)
                              (believed-at? kb (list atOrAboveStrict 2 1) U)))))))

(tu/deftest-kb an-antisymmetric-mark-on-a-super-predicate-merges-a-sub-pair
  ;; The mark descends the predicate hierarchy, exactly as functional's does.
  (tu/with-terms [atOrAbove atOrAboveStrict Alice Bob]
    (v/assert kb (list 'genl atOrAboveStrict atOrAbove) U)
    (v/assert kb (list 'anti_symmetric atOrAbove) U)
    (v/assert kb (list atOrAboveStrict Alice Bob) U {:strength :monotonic})
    (v/assert kb (list atOrAboveStrict Bob Alice) U {:strength :monotonic})
    (is (merged? kb Alice Bob U)
        "two sub-predicate tuples are convicted by the super's mark")))

;; `special/derive-antisymmetric-equalities` justifies the merge once per declaring
;; sentex (`tax/prop-supporters`), read KB-wide rather than from the merge's context —
;; `equality_test/a-merge-rests-on-every-functional-declaration-not-on-one-of-them` asserts
;; the same read for `functional`.  A declaration stated in a sibling context therefore
;; supports a merge in a context that cannot see it, and `VAELII_AUDIT_SUPPORT` reports
;; that justification.

(defn- declaration-contexts
  "The contexts of the `anti_symmetric` declarations the `(equals a b)` merge in `ctx`
  names among its supporters, as a set."
  [kb a b ctx]
  (let [[lo hi] (sort [a b])
        h       (v/handle-of kb (list 'equals lo hi) ctx)]
    (set (for [s (:support (tu/why-root kb h))
               x (:because s)
               :when (= 'anti_symmetric (first (:sentence x)))]
           (:context x)))))

(tu/deftest-kb an-antisymmetric-merge-rests-on-every-declaration-not-on-one-of-them
  ;; Both directions, on fresh terms each time, for the functional test's reason: a merge
  ;; resting on one arbitrary declaration passes whenever the retracted one is not it.
  (tu/with-terms [CxFam CxStory]
    (v/assert kb (list 'genlCx CxFam U) U)
    (v/assert kb (list 'genlCx CxStory U) U)
    (doseq [retire [:first :second]]
      (let [atOrAbove (tu/tmp-pred "atOrAbove")
            alice     (tu/tmp-ind "Alice")
            bob       (tu/tmp-ind "Bob")
            h1        (v/assert kb (list 'anti_symmetric atOrAbove) CxFam)
            h2        (v/assert kb (list 'anti_symmetric atOrAbove) CxStory)]
        (v/assert kb (list atOrAbove alice bob) CxFam {:strength :monotonic})
        (v/assert kb (list atOrAbove bob alice) CxFam {:strength :monotonic})
        (is (merged? kb alice bob CxFam) "the merge is derived while both declarations stand")
        (testing (str "retiring the " (name retire) " declaration leaves the merge")
          (v/retract! kb (if (= retire :first) h1 h2))
          (is (merged? kb alice bob CxFam)))))))

(tu/deftest-kb an-antisymmetric-declaration-in-a-sibling-context-supports-the-merge
  (tu/with-terms [CxFam CxStory]
    (v/assert kb (list 'genlCx CxFam U) U)
    (v/assert kb (list 'genlCx CxStory U) U)
    (let [atOrAbove (tu/tmp-pred "atOrAbove")
          alice     (tu/tmp-ind "Alice")
          bob       (tu/tmp-ind "Bob")
          decl      (v/assert kb (list 'anti_symmetric atOrAbove) CxStory)]
      (v/assert kb (list atOrAbove alice bob) CxFam {:strength :monotonic})
      (v/assert kb (list atOrAbove bob alice) CxFam {:strength :monotonic})
      (testing "the declaration stated in CxStory merges the pair in CxFam"
        (is (not (v/sees? kb CxFam CxStory)))
        (is (merged? kb alice bob CxFam)))
      (testing "the merge names the CxStory declaration, which CxFam does not see"
        (is (contains? (declaration-contexts kb alice bob CxFam) CxStory)))
      (testing "retracting the declaration un-merges"
        (v/retract! kb decl)
        (is (not (merged? kb alice bob CxFam)))))))

(tu/deftest-kb a-merge-mark-in-a-sibling-merges-from-every-context-in-either-order
  ;; `anti_symmetric`, `functional` and `functionalInArg` are decontextualized, so a mark
  ;; stated in CxStory
  ;; is lifted into CxUniverse and read from every context.  A merge is placed where its
  ;; mark is visible, so the copy derives the merge as well as the statement does
  ;; (`special/copy-merges`): the mark stated after the facts merged below CxStory
  ;; alone, where stated before them it merged at CxUniverse.
  (tu/with-terms [CxFam CxStory]
    (v/assert kb (list 'genlCx CxFam U) U)
    (v/assert kb (list 'genlCx CxStory U) U)
    (doseq [mark        ['anti_symmetric 'functional 'functionalInArg]
            decl-first? [true false]]
      (let [rel   (tu/tmp-pred "rel")
            [a b c] (repeatedly 3 #(tu/tmp-ind "Party"))
            [facts x y] (case mark
                          anti_symmetric  [[(list rel a b) (list rel b a)] a b]
                          functional      [[(list rel a b) (list rel a c)] b c]
                          ;; position 1 is the one a shared second argument determines
                          functionalInArg [[(list rel b a) (list rel c a)] b c])
            decl! #(v/assert kb (if (= 'functionalInArg mark) (list mark rel 1) (list mark rel))
                             CxStory)]
        (v/assert kb (list 'arity rel 2) U)
        (when decl-first? (decl!))
        (doseq [f facts] (v/assert kb f U {:strength :monotonic}))
        (when-not decl-first? (decl!))
        (testing (str mark (if decl-first? " stated before" " stated after") " the facts")
          (is (= [true true true]
                 (mapv #(= (v/representative kb x %) (v/representative kb y %))
                       [U CxFam CxStory]))))))))

(tu/deftest-kb a-merge-mark-stated-in-any-context-merges-the-facts-each-context-sees
  ;; A mark is lifted to CxUniverse, which every context sees, so wherever it is stated it
  ;; merges the facts a context sees: facts in CxUniverse merge everywhere, and facts in a
  ;; context no edge names merge there alone.  Each in either order.
  (tu/with-terms [CxFam CxStory CxIsle]
    (doseq [mark                       ['anti_symmetric 'functional 'functionalInArg]
            [mark-cx fact-cx expected] [[CxIsle U [true true true]]
                                        [CxStory CxIsle [false false true]]
                                        [CxIsle CxIsle [false false true]]]
            decl-first?                [true false]]
      (let [rel   (tu/tmp-pred "rel")
            [a b c] (repeatedly 3 #(tu/tmp-ind "Party"))
            [facts x y] (case mark
                          anti_symmetric  [[(list rel a b) (list rel b a)] a b]
                          functional      [[(list rel a b) (list rel a c)] b c]
                          functionalInArg [[(list rel b a) (list rel c a)] b c])
            decl! #(v/assert kb (if (= 'functionalInArg mark) (list mark rel 1) (list mark rel))
                             mark-cx)]
        (v/assert kb (list 'arity rel 2) U)
        (when decl-first? (decl!))
        (doseq [f facts] (v/assert kb f fact-cx {:strength :monotonic}))
        (when-not decl-first? (decl!))
        (testing (str mark " in " mark-cx ", facts in " fact-cx
                      (if decl-first? ", stated before" ", stated after"))
          (is (= expected
                 (mapv #(= (v/representative kb x %) (v/representative kb y %))
                       [U CxFam CxIsle]))))))))

;;; ── anti_transitive: declared, chain conviction deferred ───────────────

(tu/deftest-kb antitransitive-classifies-and-clashes-with-transitive
  ;; The enforced half.  The bare mark carries its classification — (anti_transitive P)
  ;; makes P a binary_predicate — and declaring the same predicate transitive too is a
  ;; direct disjoint membership clash, which the forced-monotonic mark wins.
  (tu/with-terms [flowsInto]
    (v/assert kb (list 'anti_transitive flowsInto) U)
    (testing "the mark classifies it as a binary_predicate"
      (is (v/ask? kb (list 'binary_predicate flowsInto) U)))
    (testing "and declaring it transitive too is stored and loses — no predicate is both"
      (is (tu/stored-in-clash? kb (list 'transitive flowsInto) U))
      (is (v/ask? kb (list 'anti_transitive flowsInto) U)))))

(tu/deftest-kb a-known-true-chain-and-its-known-true-direct-step-are-one-conflict
  ;; The conviction, read the way `asymmetric` reads its converse: a chain no member of
  ;; which can be defeated is stored whole and stands in `conflicts`.
  (tu/with-terms [parentOf Alice Bob Carol]
    (v/assert kb (list 'anti_transitive parentOf) U)
    (v/assert kb (list parentOf Alice Bob) U {:strength :monotonic})
    (v/assert kb (list parentOf Bob Carol) U {:strength :monotonic})
    (testing "the check finds nothing to refuse, and the assert stores the direct step"
      (is (empty? (v/check kb (list parentOf Alice Carol) U {:strength :monotonic})))
      (is (v/assert kb (list parentOf Alice Carol) U {:strength :monotonic})))
    (testing "and the conflict names all three members, not two"
      (is (= [#{(v/handle-of kb (list parentOf Alice Bob) U)
                (v/handle-of kb (list parentOf Bob Carol) U)
                (v/handle-of kb (list parentOf Alice Carol) U)}]
             (mapv :nogood (v/conflicts kb)))))))

(tu/deftest-kb the-chain-is-convicted-from-whichever-member-arrives-last
  ;; Conviction has to be symmetric or the discovery would find the triple by arrival
  ;; order: the closing step convicts the chain, and each step convicts the other step
  ;; beside the closing tuple (`checks/chain-triples`, three roles).
  (tu/with-terms [parentOf Alice Bob Carol]
    (v/assert kb (list 'anti_transitive parentOf) U)
    (v/assert kb (list parentOf Alice Carol) U {:strength :monotonic})
    (v/assert kb (list parentOf Alice Bob) U {:strength :monotonic})
    (testing "the second step closes the same triple, and as the one default member it loses"
      (is (tu/stored-in-clash? kb (list parentOf Bob Carol) U))
      (is (= :defeated (:reason (v/why-not kb (v/handle-of kb (list parentOf Bob Carol) U))))))))

(tu/deftest-kb three-defaults-are-one-dilemma-of-three-members
  ;; The `:default` reading, and the one that says this is a nogood rather than a
  ;; directional rule: no member out-ranks the others, so none is defeated and the whole
  ;; set is reported.  A pairwise engine could not say this at all.
  (tu/with-terms [parentOf Alice Bob Carol]
    (v/assert kb (list 'anti_transitive parentOf) U)
    (v/assert kb (list parentOf Alice Bob) U)
    (v/assert kb (list parentOf Bob Carol) U)
    (testing "the direct step is admitted — nothing here out-ranks anything"
      (is (empty? (v/check kb (list parentOf Alice Carol) U)))
      (is (v/assert kb (list parentOf Alice Carol) U)))
    (let [cs (v/contradictions kb)]
      (testing "and the KB says so, once, over all three"
        (is (= 1 (count cs)))
        (is (= :anti-transitive (:kind (first cs))))
        (is (= 3 (count (:sides (first cs)))))
        (is (= #{(v/handle-of kb (list parentOf Alice Bob) U)
                 (v/handle-of kb (list parentOf Bob Carol) U)
                 (v/handle-of kb (list parentOf Alice Carol) U)}
               (:nogood (first cs)))))
      (testing "all three stay believed — a dilemma is represented, not decided"
        (is (every? #(v/ask? kb % U)
                    [(list parentOf Alice Bob) (list parentOf Bob Carol)
                     (list parentOf Alice Carol)]))))))

(tu/deftest-kb the-one-defeasible-member-of-a-chain-is-the-one-defeated
  ;; The mixed case: a unique weakest member is what a nogood of any width is decided on
  ;; (`decide/verdict`), so the defeasible step loses to the two known-true claims
  ;; and keeps a `why-not` while it does.
  (tu/with-terms [parentOf Alice Bob Carol]
    (v/assert kb (list 'anti_transitive parentOf) U)
    (v/assert kb (list parentOf Alice Bob) U {:strength :monotonic})
    (v/assert kb (list parentOf Bob Carol) U)
    (is (v/assert kb (list parentOf Alice Carol) U {:strength :monotonic}))
    (testing "the default step is the member that goes"
      (is (not (v/ask? kb (list parentOf Bob Carol) U)))
      (is (v/ask? kb (list parentOf Alice Bob) U))
      (is (v/ask? kb (list parentOf Alice Carol) U))
      (is (= :defeated (:reason (v/why-not kb (v/handle-of kb (list parentOf Bob Carol) U))))))
    (testing "and a decided clash is not also a standing dilemma"
      (is (empty? (v/contradictions kb))))))

(tu/deftest-kb the-antitransitive-mark-is-read-up-the-predicate-hierarchy
  ;; The descension every constraint mark takes: the sub's tuples ARE the super's, so a
  ;; chain spelled at a sub-predicate is a chain the super's mark convicts — and which
  ;; spelling arrived last decides nothing.
  (tu/with-terms [parentOf fatherOf Alice Bob Carol]
    (v/assert kb (list 'anti_transitive parentOf) U)
    (v/assert kb (list 'genl fatherOf parentOf) U)
    (v/assert kb (list fatherOf Alice Bob) U {:strength :monotonic})
    (v/assert kb (list fatherOf Bob Carol) U {:strength :monotonic})
    (is (tu/stored-in-clash? kb (list fatherOf Alice Carol) U))
    (is (= :defeated (:reason (v/why-not kb (v/handle-of kb (list fatherOf Alice Carol) U)))))))

(tu/deftest-kb an-antitransitive-self-tuple-is-admitted
  ;; The stated absence: `(P a a)` is its own two-step chain, so the triple collapses onto
  ;; one sentex and there is no second claim to weigh — a lone tuple, which this engine
  ;; refuses at the entry point or not at all (`checks/antitransitivity-problems`).
  ;; `anti_transitive` does not hand you `irreflexive`, exactly as `asymmetric` does not.
  (tu/with-terms [parentOf Alice]
    (v/assert kb (list 'anti_transitive parentOf) U)
    (is (empty? (v/check kb (list parentOf Alice Alice) U)))
    (is (v/assert kb (list parentOf Alice Alice) U))
    (is (v/ask? kb (list parentOf Alice Alice) U))
    (is (empty? (v/contradictions kb)))))

(tu/deftest-kb retracting-the-antitransitive-mark-releases-the-chain
  ;; The clash follows belief in the *declaration* as much as in the facts: the mark is
  ;; the whole of what makes the three a nogood.
  (tu/with-terms [parentOf Alice Bob Carol]
    (let [decl (v/assert kb (list 'anti_transitive parentOf) U)]
      (v/assert kb (list parentOf Alice Bob) U)
      (v/assert kb (list parentOf Bob Carol) U)
      (v/assert kb (list parentOf Alice Carol) U)
      (is (= 1 (count (v/contradictions kb))))
      (v/retract! kb decl)
      (testing "the three are ordinary facts again"
        (is (empty? (v/contradictions kb)))
        (is (every? #(v/ask? kb % U)
                    [(list parentOf Alice Bob) (list parentOf Bob Carol)
                     (list parentOf Alice Carol)]))))))

;;; ── equivalence_relation: three marks, no engine code ──────────────────

(tu/deftest-kb an-equivalence-relation-derives-symmetric-transitive-and-reflexive
  (tu/with-terms [sameAgeAs]
    (v/assert kb (list 'equivalence_relation sameAgeAs) U)
    (testing "the three marks are derived"
      (is (v/ask? kb (list 'symmetric sameAgeAs) U))
      (is (v/ask? kb (list 'transitive sameAgeAs) U))
      (is (v/ask? kb (list 'reflexive sameAgeAs) U)))
    (testing "and each is enforced in turn, behaviourally"
      (tu/with-terms [Alice Bob Carol]
        (v/assert kb (list sameAgeAs Alice Bob) U)
        (is (v/ask? kb (list sameAgeAs Bob Alice) U) "symmetric: both spellings answer")
        (is (v/ask? kb (list sameAgeAs Alice Alice) U) "reflexive: a self tuple answers")
        (v/assert kb (list sameAgeAs Bob Carol) U)
        (is (v/ask? kb (list sameAgeAs Alice Carol) U) "transitive: the chain closes")))))

(tu/deftest-kb retracting-the-equivalence-declaration-drops-the-three-marks
  (tu/with-terms [sameAgeAs]
    (let [decl (v/assert kb (list 'equivalence_relation sameAgeAs) U)]
      (is (v/ask? kb (list 'symmetric sameAgeAs) U))
      (v/retract! kb decl)
      (testing "the derived marks rested on the declaration and go with it"
        (is (not (v/ask? kb (list 'symmetric sameAgeAs) U)))
        (is (not (v/ask? kb (list 'transitive sameAgeAs) U)))
        (is (not (v/ask? kb (list 'reflexive sameAgeAs) U)))))))

;;; ── the property lattice, shipped in CxUniverse ───────────────────────────

(tu/deftest-kb asymmetric-classifies-as-irreflexive-and-antisymmetric
  ;; The shipped genl edges on the bare marks (issue #14's original spelling): every
  ;; asymmetric predicate is classified irreflexive and antisymmetric.  Crucially this is
  ;; a query CLASSIFICATION, not the :irreflexive PROPERTY — a genl-inherited membership
  ;; sets no mark, so an asymmetric predicate still admits its self tuple.
  (tu/with-terms [tallerThan]
    (v/assert kb (list 'asymmetric tallerThan) U)
    (testing "classified as both, via (genl asymmetric irreflexive/anti_symmetric)"
      (is (v/ask? kb (list 'irreflexive tallerThan) U))
      (is (v/ask? kb (list 'anti_symmetric tallerThan) U)))
    (testing "but the classification does not enforce — the self tuple is still admitted"
      (tu/with-terms [Giant]
        (is (v/assert kb (list tallerThan Giant Giant) U))
        (is (v/ask? kb (list tallerThan Giant Giant) U))))))

(tu/deftest-kb symmetric-and-asymmetric-are-disjoint
  ;; `(disjoint symmetric asymmetric)` on the bare marks: a direct membership in the second
  ;; clashes with the first.  `asymmetric` is forced monotonic, so it defeats the
  ;; `:default` `symmetric` mark whichever arrived first.
  (tu/with-terms [nextTo]
    (v/assert kb (list 'symmetric nextTo) U)
    (testing "so declaring the same predicate asymmetric is stored, and the pair is weighed"
      (is (empty? (v/check kb (list 'asymmetric nextTo) U)))
      (is (v/assert kb (list 'asymmetric nextTo) U))
      (is (v/ask? kb (list 'asymmetric nextTo) U))
      (is (not (v/ask? kb (list 'symmetric nextTo) U))))))

(tu/deftest-kb reflexive-and-irreflexive-are-disjoint
  ;; `irreflexive` is forced monotonic, so it defeats the `:default` `reflexive` mark
  (tu/with-terms [sameSizeAs]
    (v/assert kb (list 'reflexive sameSizeAs) U)
    (testing "so declaring the same predicate irreflexive is stored, and the pair is weighed"
      (is (v/assert kb (list 'irreflexive sameSizeAs) U))
      (is (v/ask? kb (list 'irreflexive sameSizeAs) U))
      (is (not (v/ask? kb (list 'reflexive sameSizeAs) U))))))

(tu/deftest-kb an-equivalence-relation-is-classified-as-a-binarypredicate
  (tu/with-terms [sameAgeAs]
    (v/assert kb (list 'equivalence_relation sameAgeAs) U)
    (is (v/ask? kb (list 'binary_predicate sameAgeAs) U))
    (testing "carrying the three marks it stands in for"
      (is (v/ask? kb (list 'symmetric sameAgeAs) U))
      (is (v/ask? kb (list 'transitive sameAgeAs) U))
      (is (v/ask? kb (list 'reflexive sameAgeAs) U)))))

;;; ── negates: two relations hold of no argument list together ─────────────────

(tu/deftest-kb negates-places-one-nogood-over-two-tuples-in-every-arrival-order
  (tu/with-terms [scorns admires Eve Fay]
    (let [a  (list scorns Eve Fay)
          b  (list admires Eve Fay)
          rs (readings kb {:decl #(v/assert kb (list 'negates scorns admires) U)
                           :a    #(v/assert kb a U)
                           :b    #(v/assert kb b U)}
                       #(mapv (fn [s] (v/ask? kb s U)) [a b]))]
      (is (= #{[[true true]
                {:conflicts #{}
                 :contradictions #{[:negates (list 'contradicts b a)]}}]}
             (tu/handle-free kb rs))))))

(tu/deftest-kb negates-reads-the-sub-predicates-of-both-sides-in-every-arrival-order
  (tu/with-terms [scorns admires sneersAt adores Ida Jo]
    (let [rs (readings kb {:decl #(v/assert kb (list 'negates scorns admires) U)
                           :e1   #(v/assert kb (list 'genl sneersAt scorns) U)
                           :e2   #(v/assert kb (list 'genl adores admires) U)
                           :a    #(v/assert kb (list sneersAt Ida Jo) U)
                           :b    #(v/assert kb (list adores Ida Jo) U)}
                       (constantly nil))]
      (is (= 1 (count rs)))
      (is (= #{[:negates (list 'contradicts (list adores Ida Jo) (list sneersAt Ida Jo))]}
             (:contradictions (second (first rs))))))))

(tu/deftest-kb retracting-the-negates-declaration-releases-the-pair
  (tu/with-terms [scorns admires Eve Fay]
    (let [decl (v/assert kb (list 'negates scorns admires) U)]
      (v/assert kb (list scorns Eve Fay) U)
      (v/assert kb (list admires Eve Fay) U)
      (is (= 1 (count (v/contradictions kb))))
      (v/retract! kb decl)
      (is (empty? (v/contradictions kb)))
      (is (empty? (placed kb))))))

(tu/deftest-kb negates-places-a-pair-of-ternary-tuples
  (tu/with-terms [gives withholds Ann Bob Cup Pen]
    (v/assert kb (list 'negates gives withholds) U)
    (v/assert kb (list gives Ann Bob Cup) U {:strength :monotonic})
    (v/assert kb (list withholds Ann Bob Pen) U)
    (testing "tuples of two argument lists are no pair"
      (is (empty? (v/contradictions kb))))
    (testing "a tuple of the other side on the same list loses to the monotonic one"
      (is (tu/stored-in-clash? kb (list withholds Ann Bob Cup) U))
      (is (= :defeated (:reason (v/why-not kb (v/handle-of kb (list withholds Ann Bob Cup) U))))))))

(tu/deftest-kb a-negates-declaration-over-two-lengths-is-placed-not-refused-in-every-order
  (tu/with-terms [twoR threeR]
    (let [decl (list 'negates twoR threeR)]
      (is (empty? (v/check kb decl U)))
      (let [rs (readings kb {:decl  #(v/assert kb decl U)
                             :two   #(v/assert kb (list 'binary_predicate twoR) U)
                             :three #(v/assert kb (list 'ternary_predicate threeR) U)}
                         #(v/ask? kb decl U))]
        (testing "the declaration stays believed, and its clash is a conflict"
          (is (= #{[true [[:negates-arity #{twoR threeR}]] #{}]}
                 (into #{} (map (fn [[b {:keys [conflicts contradictions]}]]
                                  [b (mapv (fn [[k [_ d]]] [k (set (rest d))]) conflicts)
                                   contradictions]))
                       rs))))))))

(tu/deftest-kb a-negates-declaration-over-two-unary-predicates-is-a-clash-of-the-declaration
  (tu/with-terms [alive dead]
    (v/assert kb (list 'unary_predicate alive) U)
    (v/assert kb (list 'unary_predicate dead) U)
    (let [h (v/assert kb (list 'negates alive dead) U)]
      (is (= [[:negates-unary #{h}]] (mapv (juxt :kind :nogood) (v/conflicts kb))))
      (testing "the report names the bindings stating the lengths"
        (is (= #{(list 'unary_predicate alive) (list 'unary_predicate dead)}
               (into #{} (map :sentence) (:grounds (first (v/conflicts kb)))))))
      (v/retract! kb (v/handle-of kb (list 'unary_predicate dead) U))
      (testing "a length leaving releases the clash"
        (is (empty? (v/conflicts kb)))))))

(tu/deftest-kb a-length-a-genl-edge-gives-a-negates-side-is-a-clash-of-the-declaration
  (tu/with-terms [twoR threeR subR]
    (v/assert kb (list 'binary_predicate twoR) U)
    (v/assert kb (list 'ternary_predicate threeR) U)
    (let [decl (v/assert kb (list 'negates twoR subR) U)]
      (is (empty? (v/conflicts kb)))
      (let [edge (v/assert kb (list 'genl subR threeR) U)]
        (is (= [[:negates-arity #{decl}]] (mapv (juxt :kind :nogood) (v/conflicts kb))))
        (v/retract! kb edge)
        (is (empty? (v/conflicts kb)))))))

(tu/deftest-kb a-write-moving-no-side-length-reads-no-negates-declaration
  (tu/with-terms [aR bR cR dog animal]
    (v/assert kb (list 'negates aR bR) U)
    (let [reads (atom 0)
          clash arity/negates-clash]
      (with-redefs [arity/negates-clash (fn [& xs] (swap! reads inc) (apply clash xs))]
        (v/assert kb (list 'genl dog animal) U)
        (v/assert kb (list 'binary_predicate cR) U)
        (let [unrelated @reads]
          (v/assert kb (list 'binary_predicate aR) U)
          (is (= [0 true] [unrelated (pos? @reads)])))))))

(tu/deftest-kb negates-of-one-predicate-places-each-tuple-alone
  (tu/with-terms [nullR Ann Bob Cal]
    (let [rs (readings kb {:decl #(v/assert kb (list 'negates nullR nullR) U)
                           :a    #(v/assert kb (list nullR Ann Bob) U)}
                       #(v/ask? kb (list nullR Ann Bob) U))]
      (is (= #{[false {:conflicts #{} :contradictions #{}}]} rs)))
    (v/assert kb (list 'negates nullR nullR) U)
    (v/assert kb (list nullR Ann Bob) U {:strength :monotonic})
    (testing "a monotonic tuple is a one-member conflict"
      (is (= #{[:negates (list 'contradicts (list nullR Ann Bob))]}
             (tu/handle-free kb (:conflicts (clash-kinds kb))))))
    (testing "and every ground denial holds"
      (is (v/ask? kb (list 'not (list nullR Bob Cal)) U)))))

(tu/deftest-kb the-negates-prover-answers-a-denial-from-the-other-side
  (tu/with-terms [scorns admires sneersAt Gus Hal]
    (v/assert kb (list 'negates scorns admires) U)
    (v/assert kb (list 'genl sneersAt scorns) U)
    (is (not (v/ask? kb (list 'not (list scorns Gus Hal)) U)))
    (let [h (v/assert kb (list admires Gus Hal) U)]
      (testing "a believed tuple of one side answers the denial of the other and its specs"
        (is (v/ask? kb (list 'not (list scorns Gus Hal)) U))
        (is (v/ask? kb (list 'not (list sneersAt Gus Hal)) U))
        (is (not (v/ask? kb (list 'not (list admires Gus Hal)) U))))
      (v/retract! kb h)
      (is (not (v/ask? kb (list 'not (list scorns Gus Hal)) U))))))

(tu/deftest-kb a-denial-of-a-negates-declaration-loses-to-it
  ;; `negates` is forced-monotonic: a stated denial of a declaration loses to it, so the
  ;; pair stays placed.
  (tu/with-terms [scorns admires Eve Fay]
    (let [decl (v/assert kb (list 'negates scorns admires) U)
          den  (v/assert kb (list 'not (list 'negates scorns admires)) U)]
      (v/assert kb (list scorns Eve Fay) U)
      (v/assert kb (list admires Eve Fay) U)
      (is (v/believed? kb decl U))
      (is (not (v/believed? kb den U)))
      (is (= #{:negates} (into #{} (map :kind) (v/contradictions kb)))))))
