;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.reference-test
  "The engine's belief against the belief reference (docs/reference.md), and against
  itself across arrival orders.

  Two kinds of test:

  - **Fixed worlds.** Scenarios run in every arrival order of the writes that can move,
    with the expected belief at named contexts written out.  These need no reference.
  - **Random worlds.** `vaelii.ref.gen/gen-world` over a fixed seed set, each world run in
    every permutation of its writes when it has at most `exhaustive-up-to` of them and in
    a seeded sample of orders otherwise.  The reference judges every write offered
    (decision D8): a write the engine refuses is a divergence of kind
    `:engine-refused-other`, and every belief disagreement of a run that refused nothing is shrunk and
    classified (`gen/divergences`).

  **The known-divergence rule.** A divergence whose `:kind` is a key of
  `known-divergences` is counted and printed, one line per kind; any other kind fails
  the test, with one summary line per divergence and its EDN report under
  `gen/default-report-dir`.  No divergence is dropped without being counted.

  Every KB here is an in-RAM KB on a space of its own, opened by `gen/load-world!` and
  closed with its stores dropped in a `finally`, so no test shares a store with another
  and none uses the `vaelii.test-util` fixtures or their net-neutrality check: a KB that
  is closed and dropped leaves nothing behind to check."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.ref.believe :as believe]
            [vaelii.ref.gen :as gen]
            [vaelii.ref.nogoods :as nogoods]
            [vaelii.test-util :as tu]))

(def known-divergences
  "The divergence kinds the engine shows at HEAD against the decisions of 2026-09-29 (D1–D17),
  each naming the decision it departs from and the engine change it waits on.  A kind
  leaves this map when the change lands."
  {})

(def ^:private judges
  "`gen/check-world`'s judges.  `:reference` is `world -> {C {:believed :out :inherited
  :nogoods}}`."
  {:reference #(believe/believe % nogoods/families)})

(def ^:private U 'CxUniverse)

(defn- w
  "A world write; the strength defaults to `:default`, the engine's own default."
  ([s c] (w s c :default))
  ([s c strength] {:sentence s :context c :strength strength}))

;; ---- fixed worlds ------------------------------------------------------

(defn- expected-failures
  "Run `world` in each of `orders` and return one entry per order, context and sentence
  where the engine's belief differs from `expected` (`{C {S bool}}`), naming the order,
  both answers and what the engine refused in that order.  The first order's KB is also
  closed and recovered, and its recovered belief judged the same way, its entries marked
  `:recovered`.  `asks` (`{C #{S}}`) names the inherited claims read through `ask?`
  (`gen/engine-beliefs`).  A run whose every refusal is of a kind in `known-divergences`
  is left out and its refusals are returned under `:known`; the result is `{:failures
  [...] :known {kind n}}`."
  [world orders expected & [asks]]
  (let [runs  (into [] (map-indexed #(gen/run-order world %2 {} (or asks {}) (zero? %1)))
                    orders)
        runs  (into runs (keep #(when-let [b (:recovered %)]
                                  (assoc % :beliefs b :recovered? true)))
                    runs)
        known (for [r runs rf (:refused r)
                    :let [k (gen/refusal-kind rf)]
                    :when (contains? known-divergences k)]
                k)
        judge (fn [{:keys [order beliefs refused recovered?]}]
                (if (and (seq refused)
                         (every? #(contains? known-divergences (gen/refusal-kind %)) refused))
                  []
                  (for [[c m] expected
                        [s want] m
                        :let [got (contains? (get beliefs c #{}) s)]
                        :when (not= want got)]
                    (cond-> {:order    (mapv :sentence order)
                             :context  c
                             :sentence s
                             :engine   got
                             :expected want
                             :refused  (mapv (juxt (comp :sentence :refused) :type) refused)}
                      recovered? (assoc :recovered true)))))]
    {:failures (into [] (mapcat judge) runs)
     :known    (frequencies known)}))

(defn- failure-text [label failures n]
  (str label ": " (count failures) " wrong reading(s) over " n " orders"
       (apply str (for [f (take 4 failures)] (str "\n  " (pr-str f))))))

(defn- print-known [label known]
  (doseq [[k n] (sort-by key known)]
    (println (str label ": known divergence " (name k) " × " n " ("
                  (:decision (known-divergences k)) ", waits on "
                  (:waits-on (known-divergences k)) ")"))))

(defn- release-lattice
  "The release lattice of `scoped_defeat_test` with the denial above CxB, as
  `[world wiring content]`:

    CxUniverse  (genl chi thing) (genl dog thing) (genl cat thing)
                (disjoint dog cat) monotonic
      ├─ CxA    (genl chi dog) default
      └─ CxD    (not (genl chi dog)) monotonic
    CxB sees CxA and CxD: (chi Kit) default, (cat Kit) monotonic

  CxB reads no separation between chi and cat, so both memberships are believed there."
  [{:keys [chi dog cat Kit CxA CxB CxD]}]
  (let [wiring  [(w (list 'genl chi 'thing) U) (w (list 'genl dog 'thing) U)
                 (w (list 'genl cat 'thing) U)
                 (w (list 'genlCx CxA U) U) (w (list 'genlCx CxB CxA) U)
                 (w (list 'genlCx CxD U) U) (w (list 'genlCx CxB CxD) U)
                 (w (list 'disjoint dog cat) U :monotonic)
                 (w (list 'genl chi dog) CxA)]
        content [(w (list 'not (list 'genl chi dog)) CxD :monotonic)
                 (w (list chi Kit) CxB)
                 (w (list cat Kit) CxB :monotonic)]]
    [{:contexts #{U CxA CxB CxD} :writes (into wiring content)} wiring content]))

(deftest the-release-lattice-believes-both-memberships-at-its-reader-in-every-order
  (tu/with-terms [chi dog cat Kit CxA CxB CxD]
    (let [[world wiring content] (release-lattice {:chi chi :dog dog :cat cat :Kit Kit
                                                   :CxA CxA :CxB CxB :CxD CxD})
          orders (mapv #(into wiring %) (gen/permutations content))
          {fails :failures known :known}
          (expected-failures world orders {CxB {(list chi Kit) true (list cat Kit) true}})]
      (print-known "release lattice" known)
      (is (empty? fails) (failure-text "release lattice" fails (count orders))))))

(deftest a-second-settle-pass-leaves-the-release-lattice-reading-unchanged
  ;; Decision D2: belief does not depend on how many passes a settle runs.  The release
  ;; lattice, then in CxUniverse (pp ?x) & (unknown (blk ?x)) => (rr ?x), (pp Zed), and
  ;; last (blk Zed), whose settle runs a second pass.
  (tu/with-terms [chi dog cat Kit CxA CxB CxD pp blk rr Zed]
    (let [[world wiring content] (release-lattice {:chi chi :dog dog :cat cat :Kit Kit
                                                   :CxA CxA :CxB CxB :CxD CxD})
          two-pass [(w (list 'implies (list 'and (list pp '?x) (list 'unknown (list blk '?x)))
                             (list rr '?x))
                       U)
                    (w (list pp Zed) U)
                    (w (list blk Zed) U)]
          world    (update world :writes into two-pass)
          orders   (mapv #(-> wiring (into %) (into two-pass)) (gen/permutations content))
          {fails :failures known :known}
          (expected-failures world orders {CxB {(list chi Kit) true (list cat Kit) true}})]
      (print-known "two-pass release lattice" known)
      (is (empty? fails) (failure-text "two-pass release lattice" fails (count orders))))))

(defn- classify-failures
  "Split `fails` (from `expected-failures`) into `{:failures [...] :known {kind n}}` by
  `gen/classify` over the reference's result on `world`: a failure whose kind is in
  `known-divergences` is counted under `:known`, merged into `known`, and the rest stay
  failures."
  [world fails known]
  (let [ref (believe/believe world nogoods/families)]
    (reduce (fn [acc d]
              (let [kind (gen/classify world ref (assoc d :reference (:expected d)))]
                (if (contains? known-divergences kind)
                  (update-in acc [:known kind] (fnil inc 0))
                  (update acc :failures conj d))))
            {:failures [] :known known}
            fails)))

(deftest an-irreflexive-mark-takes-a-default-self-tuple-out-in-either-order
  ;; Decision D7: an irreflexive violation is a one-member nogood, so a :default self
  ;; tuple is OUT wherever the mark is visible, whichever arrives first.
  (tu/with-terms [properPartOf Ann CxA]
    (let [mark   (w (list 'irreflexive properPartOf) CxA :monotonic)
          self   (w (list properPartOf Ann Ann) CxA)
          world  {:contexts #{CxA} :writes [mark self]}
          orders (gen/permutations [mark self])
          {fails :failures known :known}
          (expected-failures world orders {CxA {(list properPartOf Ann Ann) false}})
          {fails :failures known :known} (classify-failures world fails known)]
      (print-known "irreflexive self tuple" known)
      (is (empty? fails) (failure-text "irreflexive self tuple" fails (count orders))))))

;; Decisions D1, D7, D10–D13 and D17: a write the forced-monotonic roster rules out is
;; stored and inert, never refused, so the engine stores it in every order and equals the
;; reference, which sets it aside.

(defn- reference-agrees
  "The entries of `expected` (`{C {S bool}}`) the reference's result on `world` answers
  otherwise, as `[C S want]`."
  [world expected]
  (let [ref (believe/believe world nogoods/families)]
    (vec (for [[c m] expected
               [s want] m
               :when (not= want (contains? (set (get-in ref [c :believed])) s))]
           [c s want]))))

(deftest an-irreflexive-loser-leaves-no-disjoint-pair-at-its-reader-in-every-order
  ;; Decisions D7 and D16 before prompt 54: the reader decides the irreflexive nogood and
  ;; the settle decides the disjoint one.  The rule concludes (cat Kit) from the self
  ;; tuple, so a reader that takes the tuple OUT withdraws (cat Kit) with it and reads no
  ;; disjoint pair, and (dog Kit) stays believed there.  CxB sees CxA and holds the mark,
  ;; so the tuple is believed at CxA and OUT at CxB.
  ;;
  ;;   CxUniverse  (genl dog thing) (genl cat thing) (disjoint dog cat) monotonic
  ;;   CxA         (tangiblePartOf Kit Kit) default   (dog Kit) default
  ;;               (tangiblePartOf ?x ?x) => (cat ?x) monotonic
  ;;   CxB sees CxA: (irreflexive tangiblePartOf)
  (tu/with-terms [tangiblePartOf dog cat Kit CxA CxB]
    (let [wiring  [(w (list 'genl dog 'thing) U) (w (list 'genl cat 'thing) U)
                   (w (list 'genlCx CxA U) U) (w (list 'genlCx CxB CxA) U)
                   (w (list 'disjoint dog cat) U :monotonic)]
          content [(w (list 'irreflexive tangiblePartOf) CxB :monotonic)
                   (w (gen/forward (list 'implies (list tangiblePartOf '?x '?x) (list cat '?x))) CxA
                      :monotonic)
                   (w (list tangiblePartOf Kit Kit) CxA)
                   (w (list dog Kit) CxA)]
          world    {:contexts #{U CxA CxB} :writes (into wiring content)}
          expected {CxA {(list tangiblePartOf Kit Kit) true (list cat Kit) true (list dog Kit) true}
                    CxB {(list tangiblePartOf Kit Kit) false (list cat Kit) false (list dog Kit) true}}
          orders   (mapv #(into wiring %) (gen/permutations content))
          {fails :failures known :known} (expected-failures world orders expected)]
      (is (= [] (reference-agrees world expected)))
      (print-known "irreflexive loser beside a disjoint pair" known)
      (is (empty? fails) (failure-text "irreflexive loser beside a disjoint pair" fails
                                       (count orders))))))

(deftest a-denial-of-a-roster-literal-is-inert-in-every-order
  ;;   CxUniverse  (genl dog thing) (genl cat thing)
  ;;   CxA         (disjoint dog cat) default, stored monotonic   (not (disjoint dog cat))
  ;;               (dog Rex) default   (cat Rex) monotonic
  (tu/with-terms [dog cat Rex CxA]
    (let [wiring  [(w (list 'genl dog 'thing) U) (w (list 'genl cat 'thing) U)
                   (w (list 'genlCx CxA U) U)]
          content [(w (list 'disjoint dog cat) CxA)
                   (w (list 'not (list 'disjoint dog cat)) CxA :monotonic)
                   (w (list dog Rex) CxA)
                   (w (list cat Rex) CxA :monotonic)]
          world   {:contexts #{U CxA} :writes (into wiring content)}
          want    {CxA {(list dog Rex) false (list cat Rex) true
                        (list 'not (list 'disjoint dog cat)) false}}
          orders  (mapv #(into wiring %) (gen/permutations content))
          {fails :failures known :known} (expected-failures world orders want)]
      (is (empty? (reference-agrees world want)))
      (print-known "inert denial" known)
      (is (empty? fails) (failure-text "inert denial" fails (count orders))))))

(deftest a-rule-concluding-a-roster-literal-from-a-plain-antecedent-is-inert-in-every-order
  ;;   CxA  (kindPair ?a ?b) => (disjoint ?a ?b)   (kindPair bird fish)
  ;;        (bird Tweety) default   (fish Tweety) default
  (tu/with-terms [kindPair bird fish Tweety CxA]
    (let [wiring  [(w (list 'genl bird 'thing) U) (w (list 'genl fish 'thing) U)
                   (w (list 'genlCx CxA U) U)]
          content [(w (gen/forward (list 'implies (list kindPair '?a '?b) (list 'disjoint '?a '?b))) CxA)
                   (w (list kindPair bird fish) CxA)
                   (w (list bird Tweety) CxA)
                   (w (list fish Tweety) CxA)]
          world   {:contexts #{U CxA} :writes (into wiring content)}
          want    {CxA {(list bird Tweety) true (list fish Tweety) true
                        (list 'disjoint bird fish) false}}
          orders  (mapv #(into wiring %) (gen/permutations content))
          {fails :failures known :known} (expected-failures world orders want)]
      (is (empty? (reference-agrees world want)))
      (print-known "inert rule" known)
      (is (empty? fails) (failure-text "inert rule" fails (count orders))))))

;; A pass whose only work is re-chaining the rules watching a datum that pass's
;; resolution defeated does not end the settle.  Each scenario defeats the datum a guard
;; reads through a nogood whose winner does not share the datum's functor, so no
;; re-check queues the rule's watchers and the release is the pass's only work.

(deftest a-guarded-rule-a-cross-functor-defeat-releases-fires-in-every-order
  ;;   CxWell  (disjoint happy sad) monotonic   (pp Zed)
  ;;           (happy Zed) default               (sad Zed) monotonic
  ;;           the rule, in the unknown form and in the exceptWhen form:
  ;;             (pp ?x) & (unknown (happy ?x)) => (rr ?x)
  ;;             (exceptWhen (happy ?x) (pp ?x) => (rr ?x))
  (doseq [[label rule-of] [["unknown release"
                            (fn [pp happy rr]
                              (list 'implies (list 'and (list pp '?x) (list 'unknown (list happy '?x)))
                                    (list rr '?x)))]
                           ["exceptWhen release"
                            (fn [pp happy rr]
                              (list 'exceptWhen (list happy '?x)
                                    (list 'implies (list pp '?x) (list rr '?x))))]]]
    (tu/with-terms [happy sad pp rr Zed CxWell]
      (let [ws     [(w (list 'disjoint happy sad) CxWell :monotonic)
                    (w (rule-of pp happy rr) CxWell)
                    (w (list pp Zed) CxWell)
                    (w (list happy Zed) CxWell)
                    (w (list sad Zed) CxWell :monotonic)]
            orders (gen/permutations ws)
            {fails :failures known :known}
            (expected-failures {:contexts #{CxWell} :writes ws} orders
                               {CxWell {(list rr Zed) true (list happy Zed) false}})]
        (print-known label known)
        (is (empty? fails) (failure-text label fails (count orders)))))))

(deftest a-defeat-of-a-blocker-s-support-releases-the-guarded-firing-in-every-order
  ;;   CxUniverse  (exceptWhen (penguin ?x) (bird ?x) => (flies ?x))
  ;;               (antarctic ?x) => (penguin ?x)
  ;;               (bird Opus)   (antarctic Opus) default   (not (antarctic Opus)) monotonic
  ;; The denial takes the blocker's support OUT, so the guarded firing is released.
  (tu/with-terms [penguin bird flies antarctic Opus]
    (let [U      'CxUniverse
          ws     [(w (list 'exceptWhen (list penguin '?x)
                           (list 'implies (list bird '?x) (list flies '?x))) U)
                  (w (list 'implies (list antarctic '?x) (list penguin '?x)) U)
                  (w (list bird Opus) U)
                  (w (list antarctic Opus) U)
                  (w (list 'not (list antarctic Opus)) U :monotonic)]
          orders (gen/permutations ws)
          {fails :failures known :known}
          (expected-failures {:contexts #{U} :writes ws} orders
                             {U {(list flies Opus) true (list penguin Opus) false}})]
      (print-known "blocker's support defeated" known)
      (is (empty? fails) (failure-text "blocker's support defeated" fails (count orders))))))

(deftest a-guarded-rule-a-reader-s-verdict-releases-fires-in-every-order
  ;;   CxA  (happy Zed) default          CxD  (not (happy Zed)) monotonic
  ;;   CxB sees CxA and CxD:  (pp ?x) & (unknown (happy ?x)) => (rr ?x),  (pp Zed)
  ;;
  ;; CxB decides the pair and takes (happy Zed) OUT with no relabel, so the verdict has
  ;; to post the rule's re-check itself.
  (tu/with-terms [happy pp rr Zed CxA CxB CxD]
    (let [wiring  [(w (list 'genlCx CxA U) U) (w (list 'genlCx CxD U) U)
                   (w (list 'genlCx CxB CxA) U) (w (list 'genlCx CxB CxD) U)]
          content [(w (list happy Zed) CxA)
                   (w (list 'not (list happy Zed)) CxD :monotonic)
                   (w (list 'set/forwardRule
                            (list 'implies (list 'and (list pp '?x) (list 'unknown (list happy '?x)))
                                  (list rr '?x)))
                      CxB)
                   (w (list pp Zed) CxB)]
          orders  (mapv #(into wiring %) (gen/permutations content))
          {fails :failures known :known}
          (expected-failures {:contexts #{U CxA CxB CxD} :writes (into wiring content)} orders
                             {CxB {(list rr Zed) true (list happy Zed) false}})]
      (print-known "reader's verdict release" known)
      (is (empty? fails) (failure-text "reader's verdict release" fails (count orders))))))

(deftest a-declaration-below-a-pair-stored-in-one-context-decides-it-there-in-every-order
  ;;   CxA  (b Ind) monotonic   (a Ind) default
  ;;   CxB sees CxA:  (disjoint a b)
  ;;
  ;; The pair's members share a context, and only a reader below it sees the separation.
  (tu/with-terms [a b Ind CxA CxB]
    (let [ws     [(w (list 'genlCx CxB CxA) U)
                  (w (list b Ind) CxA :monotonic)
                  (w (list a Ind) CxA)
                  (w (list 'disjoint a b) CxB :monotonic)]
          orders (gen/permutations ws)
          {fails :failures known :known}
          (expected-failures {:contexts #{U CxA CxB} :writes ws} orders
                             {CxA {(list a Ind) true (list b Ind) true}
                              CxB {(list a Ind) false (list b Ind) true}})]
      (print-known "declaration below the pair" known)
      (is (empty? fails) (failure-text "declaration below the pair" fails (count orders))))))

(deftest a-declaration-below-a-dilemma-decides-it-only-where-it-is-seen-in-every-order
  ;;   CxUniverse  (disjoint ta tb) monotonic   (ta Ind) default   (tb Ind) default
  ;;     └─ CxA    (forced_monotonic_predicate ta)
  ;;
  ;; CxA reads `ta` on the roster, so `(tb Ind)` loses there; CxUniverse reads a dilemma.
  (tu/with-terms [ta tb Ind CxA]
    (let [ws     [(w (list 'genlCx CxA U) U)
                  (w (list 'disjoint ta tb) U :monotonic)
                  (w (list ta Ind) U)
                  (w (list tb Ind) U)
                  (w (list 'forced_monotonic_predicate ta) CxA)]
          orders (gen/permutations ws)
          {fails :failures known :known}
          (expected-failures {:contexts #{U CxA} :writes ws} orders
                             {U   {(list ta Ind) true (list tb Ind) true}
                              CxA {(list ta Ind) true (list tb Ind) false}})]
      (print-known "declaration below a dilemma" known)
      (is (empty? fails) (failure-text "declaration below a dilemma" fails (count orders))))))

(deftest a-declaration-below-a-denial-makes-it-inert-only-where-it-is-seen-in-every-order
  ;;   CxUniverse  (not (ta Ind)) monotonic   (ta Ind) default
  ;;     └─ CxA    (forced_monotonic_predicate ta)
  ;;
  ;; CxA reads the denial inert; CxUniverse reads `(ta Ind)` defeated by it.
  (tu/with-terms [ta Ind CxA]
    (let [ws     [(w (list 'genlCx CxA U) U)
                  (w (list 'not (list ta Ind)) U :monotonic)
                  (w (list ta Ind) U)
                  (w (list 'forced_monotonic_predicate ta) CxA)]
          orders (gen/permutations ws)
          {fails :failures known :known}
          (expected-failures {:contexts #{U CxA} :writes ws} orders
                             {U   {(list ta Ind) false (list 'not (list ta Ind)) true}
                              CxA {(list ta Ind) true (list 'not (list ta Ind)) false}})]
      (print-known "declaration below a denial" known)
      (is (empty? fails) (failure-text "declaration below a denial" fails (count orders))))))

(deftest a-vantage-below-a-dilemma-decides-its-stronger-inherited-reading-in-every-order
  ;;   CxUniverse  (transitiveInArgInverse heavierThan 1 genl) (genl hauler animal)
  ;;               (genl vehicle animal) monotonic
  ;;               (genl cart hauler) default   (not (heavierThan cart Bone1)) default
  ;;               K1 (heavierThan hauler Bone1) monotonic, in one world of the two
  ;;   CxLeft sees CxUniverse: (genl cart vehicle) and K2 (heavierThan vehicle Bone1)
  ;;               monotonic
  ;;
  ;; CxUniverse reads K1 over the default edge, a dilemma, and keeps the denial.  CxLeft
  ;; reads K2 over a known-true route, where the denial is the unique weakest member.
  (tu/with-terms [heavierThan cart hauler vehicle animal Bone1 CxLeft]
    (doseq [k1? [false true]]
      (let [den      (list 'not (list heavierThan cart Bone1))
            claim    (list heavierThan cart Bone1)
            wiring   [(w (list 'transitiveInArgInverse heavierThan 1 'genl) U :monotonic)
                      (w (list 'genl hauler animal) U :monotonic)
                      (w (list 'genl vehicle animal) U :monotonic)
                      (w (list 'genl cart hauler) U)
                      (w den U)
                      (w (list 'genl cart vehicle) CxLeft :monotonic)]
            content  (cond-> [(w (list heavierThan vehicle Bone1) CxLeft :monotonic)
                              (w (list 'genlCx CxLeft U) U)]
                       k1? (conj (w (list heavierThan hauler Bone1) U :monotonic)))
            world    {:contexts #{U CxLeft} :writes (into wiring content)}
            expected {U {den true} CxLeft {den false claim true}}
            orders   (mapv #(into wiring %) (gen/permutations content))
            label    (str "stronger reading below a dilemma, K1 " k1?)
            {fails :failures known :known}
            (expected-failures world orders expected {CxLeft #{claim}})]
        (is (= [] (reference-agrees world expected)))
        (print-known label known)
        (is (empty? fails) (failure-text label fails (count orders)))))))

(deftest a-guarded-rule-a-lifted-dilemma-releases-fires-in-every-order
  ;;   CxWell  (pp ?x) & (unknown (happy ?x)) => (rr ?x)
  ;;           (src ?x) => (not (happy ?x)) monotonic
  ;;           (happy Zed) default   (not (happy Zed)) default   (pp Zed)   (src Zed) monotonic
  ;;
  ;; The two defaults are a dilemma until (src Zed) derives the negation at :monotonic,
  ;; which defeats (happy Zed).  The derivation stores no new sentence, so no re-check
  ;; queues the rule's watchers.
  (tu/with-terms [happy pp rr src Zed CxWell]
    (let [wiring  [(w (list 'implies (list 'and (list pp '?x) (list 'unknown (list happy '?x)))
                            (list rr '?x))
                      CxWell)
                   (w (list 'implies (list src '?x) (list 'not (list happy '?x))) CxWell :monotonic)]
          content [(w (list pp Zed) CxWell)
                   (w (list happy Zed) CxWell)
                   (w (list 'not (list happy Zed)) CxWell)
                   (w (list src Zed) CxWell :monotonic)]
          orders  (mapv #(into wiring %) (gen/permutations content))
          {fails :failures known :known}
          (expected-failures {:contexts #{CxWell} :writes (into wiring content)} orders
                             {CxWell {(list rr Zed) true (list happy Zed) false}})]
      (print-known "lifted dilemma release" known)
      (is (empty? fails) (failure-text "lifted dilemma release" fails (count orders))))))

(deftest a-guarded-conclusion-ties-a-default-membership-in-every-order
  ;; Decision D14.
  ;;   CxWell  (disjoint aa bb) monotonic   (pp Zed) monotonic   (bb Zed) default
  ;;           a :monotonic rule, in the unknown form and in the exceptWhen form:
  ;;             (pp ?x) & (unknown (qq ?x)) => (aa ?x)
  ;;             (exceptWhen (qq ?x) (pp ?x) => (aa ?x))
  ;; The conclusion (aa Zed) is :default, so the disjoint nogood is a dilemma.
  (doseq [[label rule-of] [["unknown dilemma"
                            (fn [pp qq aa]
                              (list 'set/forwardRule
                                    (list 'implies (list 'and (list pp '?x) (list 'unknown (list qq '?x)))
                                          (list aa '?x))))]
                           ["exceptWhen dilemma"
                            (fn [pp qq aa]
                              (list 'exceptWhen (list qq '?x)
                                    (list 'set/forwardRule (list 'implies (list pp '?x) (list aa '?x)))))]]]
    (tu/with-terms [aa bb pp qq Zed CxWell]
      (let [ws     [(w (list 'disjoint aa bb) CxWell :monotonic)
                    (w (rule-of pp qq aa) CxWell :monotonic)
                    (w (list pp Zed) CxWell :monotonic)
                    (w (list bb Zed) CxWell)]
            orders (gen/permutations ws)
            {fails :failures known :known}
            (expected-failures {:contexts #{CxWell} :writes ws} orders
                               {CxWell {(list aa Zed) true (list bb Zed) true}})]
        (print-known label known)
        (is (empty? fails) (failure-text label fails (count orders)))))))

(deftest a-guard-is-asked-at-every-reader-below-the-placement-in-every-order
  ;; D4: CxB sees CxA.  CxA: the rule and (pp Zed); CxB: (qq Zed).  CxA believes
  ;; (rr Zed) and CxB does not, with the rule's guard an `unknown` or an `exceptWhen`.
  (doseq [[label rule-of] [["unknown below the placement"
                            (fn [pp qq rr]
                              (list 'set/forwardRule
                                    (list 'implies (list 'and (list pp '?x) (list 'unknown (list qq '?x)))
                                          (list rr '?x))))]
                           ["exceptWhen below the placement"
                            (fn [pp qq rr]
                              (list 'exceptWhen (list qq '?x)
                                    (list 'set/forwardRule (list 'implies (list pp '?x) (list rr '?x)))))]]]
    (tu/with-terms [pp qq rr Zed CxA CxB]
      (let [ws       [(w (list 'genlCx CxA U) U :monotonic)
                      (w (list 'genlCx CxB CxA) U :monotonic)
                      (w (rule-of pp qq rr) CxA)
                      (w (list pp Zed) CxA)
                      (w (list qq Zed) CxB)]
            world    {:contexts #{U CxA CxB} :writes ws}
            expected {CxA {(list rr Zed) true} CxB {(list rr Zed) false (list qq Zed) true}}
            {fails :failures known :known}
            (expected-failures world (gen/permutations ws) expected)]
        (is (= [] (reference-agrees world expected)))
        (print-known label known)
        (is (empty? fails) (failure-text label fails 120))))))

(deftest a-report-names-the-declarations-the-reference-grounds-it-on
  ;; Invariant 3 and the ruling on prompt 42: a report's `:grounds` are the declarations
  ;; of the reference's `:ground`, with the `genl` edge it is read over left out.
  ;;   CxWell  (disjoint aa bb) (disjoint aa cc) (genl cc bb)   (aa Zed) (cc Zed)
  (tu/with-terms [aa bb cc Zed CxWell]
    (let [ws     [(w (list 'genl aa 'thing) CxWell :monotonic)
                  (w (list 'genl bb 'thing) CxWell :monotonic)
                  (w (list 'genl cc bb) CxWell :monotonic)
                  (w (list 'disjoint aa bb) CxWell :monotonic)
                  (w (list 'disjoint aa cc) CxWell :monotonic)
                  (w (list aa Zed) CxWell :monotonic)
                  (w (list cc Zed) CxWell :monotonic)]
          world  {:contexts #{CxWell} :writes ws}
          ref    ((:reference judges) world)
          runs   (mapv #(gen/run-order world % {})
                       [ws (vec (reverse ws))])
          report (fn [run] (first (:reports (:reports run))))]
      (is (= [2 2] (mapv (comp count :grounds report) runs))
          "both separations, in either order")
      (is (every? #(empty? (gen/grounds-disagreements ref %)) runs))
      (is (= 1 (count (gen/grounds-disagreements
                       ref (update-in (first runs) [:reports :reports 0 :grounds]
                                      #(set (rest (sort-by pr-str %)))))))
          "and a report missing one is a disagreement"))))

(deftest a-chain-in-three-contexts-is-decided-where-one-reader-sees-it-whole-in-every-order
  ;; Decisions D3 and D16: an anti_transitive chain whose three steps sit in three contexts
  ;; is decided by the reader that sees all three, and a reader that sees two steps reads
  ;; no clash.
  ;;
  ;;   CxUniverse  (anti_transitive nearP)
  ;;   CxA (nearP Aa Bb) monotonic   CxB (nearP Bb Cc) monotonic   CxC (nearP Aa Cc)
  ;;   CxAB sees CxA CxB   CxBC sees CxB CxC   CxAC sees CxA CxC
  ;;   CxW sees CxAB CxBC CxAC
  (tu/with-terms [nearP Aa Bb Cc CxA CxB CxC CxAB CxBC CxAC CxW]
    (let [wiring  (into [(w (list 'anti_transitive nearP) U :monotonic)]
                        (for [[sub sup] [[CxA U] [CxB U] [CxC U] [CxAB CxA] [CxAB CxB]
                                         [CxBC CxB] [CxBC CxC] [CxAC CxA] [CxAC CxC]
                                         [CxW CxAB] [CxW CxBC] [CxW CxAC]]]
                          (w (list 'genlCx sub sup) U)))
          content [(w (list nearP Aa Bb) CxA :monotonic)
                   (w (list nearP Bb Cc) CxB :monotonic)
                   (w (list nearP Aa Cc) CxC)]
          world    {:contexts #{U CxA CxB CxC CxAB CxBC CxAC CxW} :writes (into wiring content)}
          direct   (list nearP Aa Cc)
          expected {CxAC {direct true} CxBC {direct true} CxAB {(list nearP Aa Bb) true}
                    CxW  {direct false (list nearP Aa Bb) true (list nearP Bb Cc) true}}
          orders   (mapv #(into wiring %) (gen/permutations content))
          {fails :failures known :known} (expected-failures world orders expected)]
      (is (= [] (reference-agrees world expected)))
      (print-known "chain in three contexts" known)
      (is (empty? fails) (failure-text "chain in three contexts" fails (count orders))))))

(deftest a-pair-across-a-context-edge-is-decided-at-the-joint-reader-in-every-order
  ;; Decision D16: a functional collision and an asymmetric converse whose two tuples are
  ;; stated in two contexts are decided by the reader that sees both, whichever of the
  ;; mark, the tuples and the edge that forms the joint view arrives last.
  ;;
  ;;   CxUniverse  (functional ageOf)          or (asymmetric beats)
  ;;   CxL         (ageOf Kit 3)               or (beats Kit Rex)
  ;;   CxR         (ageOf Kit 4) monotonic     or (beats Rex Kit) monotonic
  ;;   CxJ sees CxL and CxR
  (tu/with-terms [ageOf beats Kit Rex CxL CxR CxJ]
    (doseq [[label mark loser winner] [["functional pair" (list 'functional ageOf)
                                        (list ageOf Kit 3) (list ageOf Kit 4)]
                                       ["asymmetric pair" (list 'asymmetric beats)
                                        (list beats Kit Rex) (list beats Rex Kit)]]]
      (let [wiring  [(w (list 'genlCx CxL U) U) (w (list 'genlCx CxR U) U)
                     (w (list 'genlCx CxJ CxL) U)]
            content [(w mark U :monotonic)
                     (w loser CxL)
                     (w winner CxR :monotonic)
                     (w (list 'genlCx CxJ CxR) U)]
            world    {:contexts #{U CxL CxR CxJ} :writes (into wiring content)}
            expected {CxL {loser true} CxR {winner true} CxJ {loser false winner true}}
            orders   (mapv #(into wiring %) (gen/permutations content))
            {fails :failures known :known} (expected-failures world orders expected)]
        (is (= [] (reference-agrees world expected)))
        (print-known label known)
        (is (empty? fails) (failure-text label fails (count orders)))))))

(deftest a-functional-pair-that-is-also-a-chain-is-decided-in-every-order
  ;; Slow-twin seed 189: `(rel C A)` and `(rel C C)` are a functional pair and, read as
  ;; `(rel C C)` then `(rel C A)` for both the second and the direct step, an
  ;; `anti_transitive` chain of the same two members.  The chain's mark is where CxC does
  ;; not read it, so CxC decides the functional pair alone and takes the default OUT.
  (tu/with-terms [rel IndA IndC CxA CxC]
    (let [ws       [(w (list 'anti_transitive rel) CxA :monotonic)
                    (w (list 'functional rel) CxC :monotonic)
                    (w (list rel IndC IndA) CxC :monotonic)
                    (w (list rel IndC IndC) CxC)]
          world    {:contexts #{CxA CxC} :writes ws}
          expected {CxC {(list rel IndC IndA) true (list rel IndC IndC) false}}
          orders   (gen/permutations ws)
          {fails :failures known :known} (expected-failures world orders expected)]
      (is (= [] (reference-agrees world expected)))
      (print-known "functional pair that is also a chain" known)
      (is (empty? fails) (failure-text "functional pair that is also a chain" fails
                                       (count orders))))))

(deftest a-genlcx-edge-that-forms-the-joint-view-below-its-sub-decides-the-pair-in-every-order
  ;; Decision D16: a membership or tuple pair whose ground reaches a common descendant of
  ;; the pair's two contexts only through a `genlCx` edge is decided there, whichever of
  ;; the members, the ground and the edge arrives last.  Three grounds: a `disjoint`
  ;; declaration, a `functional` mark, and a `genl` edge under a separation stated in
  ;; CxUniverse.
  ;;
  ;;   CxUniverse  (genl a thing) (genl b thing) (genl a2 thing)
  ;;     ├─ CxA     the monotonic member
  ;;     ├─ CxB     the default member
  ;;     ├─ CxDecl  the ground
  ;;     └─ CxH     (genlCx CxH CxDecl), permuted with the three writes above
  ;;   CxW sees CxA and CxB; CxZ sees CxW and CxH
  ;;
  ;; CxW reads no ground and believes both; CxZ reads it and takes the default member OUT.
  (tu/with-terms [a b a2 ageOf Pip CxA CxB CxDecl CxH CxW CxZ]
    (doseq [[label strong weak ground extra]
            [["disjoint ground" (list a Pip) (list b Pip) (list 'disjoint a b) []]
             ["functional ground" (list ageOf Pip 1) (list ageOf Pip 2) (list 'functional ageOf) []]
             ["genl-edge ground" (list a Pip) (list b Pip) (list 'genl a a2)
              [(w (list 'disjoint a2 b) U :monotonic)]]]]
      (let [wiring   (-> [(w (list 'genl a 'thing) U) (w (list 'genl b 'thing) U)
                          (w (list 'genl a2 'thing) U)]
                         (into (for [[sub super] [[CxA U] [CxB U] [CxDecl U] [CxH U]
                                                  [CxW CxA] [CxW CxB] [CxZ CxW] [CxZ CxH]]]
                                 (w (list 'genlCx sub super) U)))
                         (into extra))
            content  [(w strong CxA :monotonic)
                      (w weak CxB)
                      (w ground CxDecl :monotonic)
                      (w (list 'genlCx CxH CxDecl) U)]
            world    {:contexts #{U CxA CxB CxDecl CxH CxW CxZ} :writes (into wiring content)}
            expected {CxZ {strong true weak false}
                      CxW {strong true weak true}}
            orders   (mapv #(into wiring %) (gen/permutations content))
            {fails :failures known :known} (expected-failures world orders expected)]
        (is (= [] (reference-agrees world expected)))
        (print-known label known)
        (is (empty? fails) (failure-text label fails (count orders)))))))

(deftest a-cover-refuted-through-a-denial-of-a-part-s-supertype-is-decided-in-every-order
  ;; A denial of a supertype of a part denies the part, so `(not (q X))` with `(genl p1 q)`
  ;; rules out `(p1 X)`, and with `(not (p2 X))` the cover refutes the default `(whole X)`,
  ;; whichever of the cover, the membership and the two denials arrives last.
  ;;
  ;;   CxUniverse  (genl p1 whole) (genl p2 whole) (genl p1 q)
  ;;               (covering whole p1 p2)   (whole X) default
  ;;               (not (q X)) monotonic    (not (p2 X)) monotonic
  (tu/with-terms [whole p1 p2 q X]
    (let [wiring   [(w (list 'genl p1 whole) U :monotonic) (w (list 'genl p2 whole) U :monotonic)
                    (w (list 'genl p1 q) U :monotonic)]
          content  [(w (list 'covering whole p1 p2) U :monotonic)
                    (w (list whole X) U)
                    (w (list 'not (list q X)) U :monotonic)
                    (w (list 'not (list p2 X)) U :monotonic)]
          world    {:contexts #{U} :writes (into wiring content)}
          expected {U {(list whole X) false
                       (list 'not (list q X)) true
                       (list 'not (list p2 X)) true}}
          orders   (mapv #(into wiring %) (gen/permutations content))
          {fails :failures known :known} (expected-failures world orders expected)]
      (is (= [] (reference-agrees world expected)))
      (print-known "cover through a supertype denial" known)
      (is (empty? fails) (failure-text "cover through a supertype denial" fails
                                       (count orders))))))

(deftest a-membership-beside-a-denial-of-a-supertype-is-decided-where-the-edge-is-seen-in-every-order
  ;; No cover is stored: the edge alone convicts the membership beside the denial.
  ;;
  ;;   CxUniverse            (dog Rex) default   (not (animal Rex)) monotonic
  ;;   CxA sees CxUniverse:  (genl dog animal) monotonic
  ;;   CxB sees CxA
  ;;
  ;; CxA and CxB read the edge, so (dog Rex) loses there.  CxUniverse does not, and keeps it.
  (tu/with-terms [dog animal Rex CxA CxB]
    (let [member   (list dog Rex)
          denial   (list 'not (list animal Rex))
          wiring   [(w (list 'genlCx CxA U) U :monotonic) (w (list 'genlCx CxB CxA) U :monotonic)]
          content  [(w (list 'genl dog animal) CxA :monotonic)
                    (w member U)
                    (w denial U :monotonic)]
          world    {:contexts #{U CxA CxB} :writes (into wiring content)}
          expected {U   {member true  denial true}
                    CxA {member false denial true}
                    CxB {member false denial true}}
          orders   (mapv #(into wiring %) (gen/permutations content))
          {fails :failures known :known} (expected-failures world orders expected)]
      (is (= [] (reference-agrees world expected)))
      (print-known "membership beside a supertype denial" known)
      (is (empty? fails) (failure-text "membership beside a supertype denial" fails
                                       (count orders))))))

(deftest a-membership-beside-an-inherited-membership-of-a-separated-type-is-decided-where-the-separation-is-seen-in-every-order
  ;;   CxUniverse            (transitiveInArgInverse down 1 genl) (genl lower upper)
  ;;                         (down upper) monotonic   (plain lower) default
  ;;   CxA sees CxUniverse:  (disjoint down plain) monotonic
  ;;   CxB sees CxA
  ;;
  ;; (down upper) reaches (down lower).  CxA and CxB read the separation, so (plain lower)
  ;; loses there.  CxUniverse does not, and keeps it.
  (tu/with-terms [down plain upper lower CxA CxB]
    (let [member   (list plain lower)
          claim    (list down upper)
          wiring   [(w (list 'genlCx CxA U) U :monotonic) (w (list 'genlCx CxB CxA) U :monotonic)
                    (w (list 'transitiveInArgInverse down 1 'genl) U :monotonic)
                    (w (list 'genl lower upper) U :monotonic)]
          content  [(w claim U :monotonic)
                    (w (list 'disjoint down plain) CxA :monotonic)
                    (w member U)]
          world    {:contexts #{U CxA CxB} :writes (into wiring content)}
          expected {U   {member true  claim true}
                    CxA {member false claim true}
                    CxB {member false claim true}}
          orders   (mapv #(into wiring %) (gen/permutations content))
          {fails :failures known :known} (expected-failures world orders expected)]
      (is (= [] (reference-agrees world expected)))
      (print-known "membership beside a separated inherited one" known)
      (is (empty? fails) (failure-text "membership beside a separated inherited one" fails
                                       (count orders))))))

;; Random reference world 283: the reader withdraws a ground and re-reads each `covering`
;; nogood, once per denial of the whole.
(deftest a-cover-denial-stated-in-two-contexts-convicts-at-a-reader-that-withdraws-a-ground-in-every-order
  ;;   CxA  (covering whole p1 p2)   (genl p2 other)   (p2 Kit)   (not (whole Kit))
  ;;   CxB sees CxA: (not (whole Kit)) monotonic   (not (genl p2 other)) monotonic
  ;;
  ;; A denial of the whole denies both parts, so (p2 Kit) and either denial refute the
  ;; cover.  CxA reads a dilemma.  CxB reads the denial :monotonic, takes (p2 Kit) OUT,
  ;; and withdraws the ground (genl p2 other).
  (tu/with-terms [whole p1 p2 other Kit CxA CxB]
    (let [denial   (list 'not (list whole Kit))
          wiring   [(w (list 'genlCx CxB CxA) U :monotonic)
                    (w (list 'covering whole p1 p2) CxA)
                    (w (list 'genl p2 other) CxA)]
          content  [(w denial CxA)
                    (w denial CxB :monotonic)
                    (w (list p2 Kit) CxA)
                    (w (list 'not (list 'genl p2 other)) CxB :monotonic)]
          world    {:contexts #{U CxA CxB} :writes (into wiring content)}
          expected {CxA {(list p2 Kit) true denial true}
                    CxB {(list p2 Kit) false denial true}}
          orders   (mapv #(into wiring %) (gen/permutations content))
          {fails :failures known :known} (expected-failures world orders expected)]
      (is (= [] (reference-agrees world expected)))
      (print-known "cover denial in two contexts" known)
      (is (empty? fails) (failure-text "cover denial in two contexts" fails (count orders))))))

;; Random reference world 286: a firing whose ingredients meet only once a `genlCx` edge
;; joins the two contexts, with the `genl` edge the match reads on the other side of it
;; from the rule and the fact.
(deftest a-genl-edge-across-a-late-genlcx-edge-licenses-the-firing-in-every-order
  ;;   CxLow sees CxHigh
  ;;   edge below:  CxHigh  (dog Rex) monotonic, (animal ?x) => (pet ?x)   CxLow  (genl dog animal)
  ;;   edge above:  CxLow   (dog Rex) monotonic, (animal ?x) => (pet ?x)   CxHigh (genl dog animal)
  ;;
  ;; CxLow sees all three, so it believes (pet Rex) whichever write arrives last.
  (tu/with-terms [dog animal pet Rex CxHigh CxLow]
    (doseq [[label home edge-at] [["edge below the rule" CxHigh CxLow]
                                  ["edge above the rule" CxLow CxHigh]]]
      (let [ws       [(w (list 'genlCx CxLow CxHigh) U)
                      (w (list 'genl dog animal) edge-at :monotonic)
                      (w (list dog Rex) home :monotonic)
                      (w (gen/forward (list 'implies (list animal '?x) (list pet '?x))) home)]
            world    {:contexts #{U CxHigh CxLow} :writes ws}
            expected {CxLow {(list pet Rex) true}}
            orders   (gen/permutations ws)
            {fails :failures known :known} (expected-failures world orders expected)]
        (is (= [] (reference-agrees world expected)))
        (print-known label known)
        (is (empty? fails) (failure-text label fails (count orders)))))))

;; Random reference world 392: a fact stated above a merge stays believed where it lives,
;; and the reader below the merge retires its spelling through the read filter
;; (docs/equality.md, "The reader is not the fact's own context").
(deftest a-fact-stored-above-a-merge-is-no-displaced-spelling-below-in-every-order
  ;;   CxA  (dog Cc) monotonic
  ;;   CxB sees CxA: (anti_symmetric aboveOf) (aboveOf Cc Aa) (aboveOf Aa Cc), all monotonic
  ;;
  ;; The converse pair merges Aa and Cc at CxB, and Aa sorts first.
  (tu/with-terms [dog aboveOf Aa Cc CxA CxB]
    (let [wiring  [(w (list 'genlCx CxB CxA) U)]
          content [(w (list dog Cc) CxA :monotonic)
                   (w (list 'anti_symmetric aboveOf) CxB :monotonic)
                   (w (list aboveOf Cc Aa) CxB :monotonic)
                   (w (list aboveOf Aa Cc) CxB :monotonic)]
          world   {:contexts #{U CxA CxB} :writes (into wiring content)}
          runs    (mapv #(gen/run-order world (into wiring %) {}) (gen/permutations content))
          wrong   (into [] (keep (fn [{:keys [order beliefs merges displaced]}]
                                   (when-not (and (empty? displaced)
                                                  (= #{#{Aa Cc}} (get merges CxB))
                                                  (contains? (get beliefs CxA) (list dog Cc))
                                                  (contains? (get beliefs CxB) (list dog Aa)))
                                     {:order (mapv :sentence order) :displaced displaced
                                      :merges merges})))
                        runs)]
      (is (empty? wrong) (failure-text "fact above a merge" wrong (count runs))))))

;; A converse reached by argument preservation under an `asymmetric` mark on the tuple's
;; functor or on a super-predicate of it (docs/inherit.md, "The converse of an inherited
;; claim"):
;;
;;   CxUniverse  (asymmetric touchesX) or (asymmetric nudgesX)   (genl nudgesX touchesX)
;;               (transitiveInArgInverse nudgesX 1 genl)   (genl chix dogx)
;;               (nudgesX dogx Fido) monotonic, which reaches (nudgesX chix Fido)
;;               (nudgesX Fido chix) default
;;
;; The mark forbids (nudgesX chix Fido) beside (nudgesX Fido chix), so the default converse
;; is OUT and the inherited claim holds.

(defn- inherited-converse-orders
  "`[world expected asks orders]` of the inherited-converse world with the mark on
  `marked`: every order of the six writes when `all?`, else the declaration first and every
  order of the other five."
  [{:keys [touches nudges chi dog Fido]} marked all?]
  (let [decl     (w (list 'transitiveInArgInverse nudges 1 'genl) U :monotonic)
        content  [(w (list 'asymmetric marked) U :monotonic)
                  (w (list 'genl nudges touches) U :monotonic)
                  (w (list 'genl chi dog) U :monotonic)
                  (w (list nudges dog Fido) U :monotonic)
                  (w (list nudges Fido chi) U)]
        world    {:contexts #{U} :writes (into [decl] content)}
        reached  (list nudges chi Fido)]
    [world
     {U {(list nudges Fido chi) false reached true}}
     {U #{reached}}
     (if all?
       (gen/permutations (:writes world))
       (mapv #(into [decl] %) (gen/permutations content)))]))

(defn- inherited-converse-failures
  "The failures of the inherited-converse world under each mark, over the orders
  `inherited-converse-orders` picks."
  [all?]
  (tu/with-terms [touchesX nudgesX chix dogx Fido]
    (let [terms {:touches touchesX :nudges nudgesX :chi chix :dog dogx :Fido Fido}]
      (into {}
            (for [marked [touchesX nudgesX]
                  :let [[world expected asks orders] (inherited-converse-orders terms marked all?)
                        {fails :failures} (expected-failures world orders expected asks)]]
              [(if (= marked touchesX) :super :own)
               {:reference (reference-agrees world expected)
                :failures  (failure-text "inherited converse" fails (count orders))
                :failed?   (boolean (seq fails))}])))))

(deftest a-converse-an-inherited-claim-reaches-under-a-super-predicate-s-mark-is-out
  (doseq [[k {:keys [reference failures failed?]}] (inherited-converse-failures false)]
    (is (= [] reference) (name k))
    (is (not failed?) (str (name k) " " failures))))

(deftest ^:slow a-converse-an-inherited-claim-reaches-under-a-mark-is-out-in-every-order
  (doseq [[k {:keys [failures failed?]}] (inherited-converse-failures true)]
    (is (not failed?) (str (name k) " " failures))))

;; A merge restates each stored sentence naming the displaced term under the
;; representative and supersedes the original, both members of a disjoint clash included,
;; and a member OUT when the merge arrives as well, so no spelling naming the displaced
;; term stays believed and the clash is decided at the representative in every order.
;;
;;   CxZoo  (disjoint dog cat) monotonic   (dog Bea) default   (cat Bea) <strength>
;;          (equals Ann Bea) monotonic, or (functional motherOf) with the :monotonic
;;          (motherOf Kid Ann) and (motherOf Kid Bea)
;;
;; Ann sorts before Bea, so Ann is the representative: (cat Ann) alone when (cat Bea) is
;; :monotonic, both memberships (a dilemma) when both are :default.  The reference gives
;; the collision the verdict :merge and so has no reading here.
(defn- merged-clash-failures
  "`expected-failures` of the merged-clash world above for each strength of `(cat Bea)`
  and each merge, over `gen/orders-for` with `order-opts`, as `[label failures n]`."
  [order-opts]
  (for [cat-strength [:monotonic :default]
        merge-by     [:equals :functional]]
    (tu/with-terms [dog cat motherOf Kid Ann Bea CxZoo]
      (let [merge  (if (= :equals merge-by)
                     [(w (list 'equals Ann Bea) CxZoo :monotonic)]
                     [(w (list 'functional motherOf) CxZoo :monotonic)
                      (w (list motherOf Kid Ann) CxZoo :monotonic)
                      (w (list motherOf Kid Bea) CxZoo :monotonic)])
            ws     (into [(w (list 'disjoint dog cat) CxZoo :monotonic)
                          (w (list dog Bea) CxZoo)
                          (w (list cat Bea) CxZoo cat-strength)]
                         merge)
            world  {:contexts #{CxZoo} :writes ws}
            orders (gen/orders-for world order-opts)
            {fails :failures} (expected-failures world orders
                                                 {CxZoo {(list dog Bea) false
                                                         (list cat Bea) false
                                                         (list dog Ann) (= :default cat-strength)
                                                         (list cat Ann) true}})]
        [(str "merge by " (name merge-by) ", (cat Bea) " (name cat-strength))
         fails (count orders)]))))

(deftest a-merge-restates-both-members-of-a-disjoint-clash-in-every-order
  ;; the equality merge in all 24 orders, the collision in a seeded 24 of its 720
  (doseq [[label fails n] (merged-clash-failures {:exhaustive-up-to 4 :sample 24})]
    (is (empty? fails) (failure-text label fails n))))

(deftest ^:slow a-merge-restates-both-members-of-a-disjoint-clash-in-all-720-collision-orders
  (doseq [[label fails n] (merged-clash-failures {:exhaustive-up-to 6})]
    (is (empty? fails) (failure-text label fails n))))

;; A `siblingDisjointException` exempts its pair at the readers that see it.  CxU sees the
;; mark and both memberships and not the declaration, so it reads the pair as a nogood; CxE
;; sees the declaration too and reads none.
;;
;;   CxUniverse
;;     └─ CxU  (sibling_disjoint col) (genl ta col) (genl tb col)
;;             (ta X) default   (tb X) default or monotonic
;;          └─ CxE  (siblingDisjointException ta tb)
;;
;; With (tb X) :default, CxU reads a dilemma (decision 7): both stay believed and one
;; report names the pair with vantage CxU.  With (tb X) :monotonic, (ta X) is OUT at CxU
;; and believed at CxE.  The reference models no `sibling_disjoint`, so the expected
;; belief is written out.
(defn- sibling-exception-failures
  "`[label failures n]` of the world above with `(tb X)` at `strength`: the `genlCx` edges
  first, then with `fixed?` the two `genl` edges, then every order of the other writes.
  At `:default` the failures also hold each order whose reports differ from the one
  dilemma at CxU."
  [fixed? strength]
  (tu/with-terms [col ta tb X CxU CxE]
    (let [edges   [(w (list 'genlCx CxU U) U) (w (list 'genlCx CxE CxU) U)]
          subtype [(w (list 'genl ta col) CxU :monotonic) (w (list 'genl tb col) CxU :monotonic)]
          content [(w (list 'sibling_disjoint col) CxU :monotonic)
                   (w (list ta X) CxU)
                   (w (list tb X) CxU strength)
                   (w (list 'siblingDisjointException ta tb) CxE :monotonic)]
          [wiring content] (if fixed? [(into edges subtype) content] [edges (into subtype content)])
          world   {:contexts #{CxU CxE} :writes (into wiring content)}
          orders  (mapv #(into wiring %) (gen/permutations content))
          {fails :failures} (expected-failures world orders
                                               {CxU {(list ta X) (= :default strength)
                                                     (list tb X) true}
                                                CxE {(list ta X) true (list tb X) true}})
          want    #{{:members #{(list ta X) (list tb X)} :vantages #{CxU}}}
          reports (when (= :default strength)
                    (keep (fn [order]
                            (let [got (into #{} (map #(select-keys % [:members :vantages]))
                                            (:reports (:reports (gen/run-order world order {}))))]
                              (when (not= want got)
                                {:order (mapv :sentence order) :reports got})))
                          orders))]
      [(str "sibling exception below the pair, (tb X) " (name strength))
       (into fails reports) (count orders)])))

(deftest a-sibling-exception-exempts-its-pair-only-where-it-is-seen-in-every-order
  ;; the two `genl` edges first, every order of the other four writes
  (doseq [strength [:default :monotonic]]
    (let [[label fails n] (sibling-exception-failures true strength)]
      (is (empty? fails) (failure-text label fails n)))))

(deftest ^:slow a-sibling-exception-exempts-its-pair-only-where-it-is-seen-in-all-720-orders
  (doseq [strength [:default :monotonic]]
    (let [[label fails n] (sibling-exception-failures false strength)]
      (is (empty? fails) (failure-text label fails n)))))

;; A `disjoint` over `genl`-related types, and a cover naming a part the `disjoint`
;; separates from its whole (the ruling on settle prompt 54, item 3): each is a hard clash
;; of its declarations, listed by `conflicts` in every order, and no belief moves.
;;
;;   CxUniverse  (genl animalw thing)   (genl dogw animalw)   (disjoint dogw animalw)
;;               (dogw Fido) default
;;   CxUniverse  (genl animalw thing)   (covering animalw dogw catw)   (disjoint dogw animalw)
;;
;; The cover states the edge from each part to the whole, so the second world's `disjoint`
;; is over related types too and reports its one-member clash beside the cover's.

(defn- related-declaration-runs
  "Every order of `writes` in CxUniverse, as `[beliefs report-member-sets]` per order, and
  the member sets the reference names at CxUniverse."
  [writes]
  (let [world {:contexts #{U} :writes writes}
        runs  (for [o (gen/permutations writes)]
                (let [r (gen/run-order world o {} {})]
                  [(get-in r [:beliefs U]) (into #{} (map :members) (get-in r [:reports :reports]))]))
        ref   (into #{} (map :members) (get-in (believe/believe world nogoods/families) [U :nogoods]))]
    [(frequencies runs) ref]))

(deftest a-disjoint-over-related-types-is-a-hard-clash-of-the-declaration-in-every-order
  (tu/with-terms [animalw dogw catw Fido]
    (let [base  [(w (list 'genl animalw 'thing) U :monotonic)
                 (w (list 'disjoint dogw animalw) U :monotonic)]
          decl  (list 'disjoint dogw animalw)
          cover (list 'covering animalw dogw catw)]
      (testing "over a genl edge, beside a default membership"
        (let [[runs ref] (related-declaration-runs
                          (conj base (w (list 'genl dogw animalw) U :monotonic) (w (list dogw Fido) U)))]
          (is (= 1 (count runs)) (pr-str runs))
          (is (= #{#{decl}} (second (ffirst runs))))
          (is (every? (first (ffirst runs)) [decl (list dogw Fido)]) "no belief moves")
          (is (contains? ref #{decl}))))
      (testing "a cover naming the part the disjoint separates from its whole"
        (let [[runs ref] (related-declaration-runs (conj base (w cover U :monotonic)))]
          (is (= 1 (count runs)) (pr-str runs))
          (is (= #{#{decl} #{cover decl}} (second (ffirst runs))))
          (is (every? (first (ffirst runs)) [decl cover]) "no belief moves")
          (is (every? ref [#{decl} #{cover decl}])))))))

;; ---- random worlds -----------------------------------------------------

(defn- check-seed
  "Generate the world for `seed`, check it in the orders `order-opts` selects, and return
  `{:runs :refused :store-split :merge-skips :divergences}`, each divergence carrying its
  `:seed`.  A world the reference refuses as outside its fragment (`:unsupported`, such
  as a rule set that is not stratified) is checked in no order and answers
  `{:unsupported? true}` with no runs."
  [seed order-opts]
  (let [world (gen/gen-world seed {})]
    (try
      (let [orders (gen/orders-for world (assoc order-opts :seed seed))
            check  (gen/check-world world orders judges)]
        {:runs        (:runs check)
         :refused     (:refused check)
         :store-split (:store-split check)
         :merge-skips (count (:merge-skips check))
         :divergences (mapv #(assoc % :seed seed) (gen/divergences world check judges))})
      (catch clojure.lang.ExceptionInfo e
        (if (= :unsupported (:type (ex-data e)))
          {:unsupported? true :runs 0 :refused [] :merge-skips 0 :divergences []}
          (throw e))))))

(defn- random-worlds
  "Check every seed of `seeds`, print one line with the number of worlds and runs, the
  worlds the reference refuses as `:unsupported`, the refusals counted by `:type` and the
  refused sentence's functor, the number of worlds whose orders stored different content,
  the contexts skipped for a `:merge` verdict and the wall time, then one line per kind of
  `known-divergences` with its count.  Returns the report lines of every divergence of a
  kind outside `known-divergences`."
  [label seeds order-opts]
  (let [t0      (System/nanoTime)
        results (mapv #(check-seed % order-opts) seeds)
        divs    (mapcat :divergences results)
        counts  (frequencies (map :kind divs))]
    (println (str label ": " (count seeds) " worlds, "
                  (reduce + (map :runs results)) " runs, unsupported "
                  (count (filter :unsupported? results)) ", refusals "
                  (pr-str (frequencies (for [{:keys [type refused]} (mapcat :refused results)]
                                         [type (first (:sentence refused))])))
                  ", store splits " (count (filter :store-split results))
                  ", merge skips " (reduce + (map :merge-skips results))
                  ", " (quot (- (System/nanoTime) t0) 1000000) " ms"))
    (print-known label (into (sorted-map) (for [k (keys known-divergences)] [k (get counts k 0)])))
    (into [] (for [d divs
                   :when (not (contains? known-divergences (:kind d)))]
               (gen/report! (:seed d) d)))))

;; A run (open, load, read, close) costs about 3.7 ms.  Twenty worlds walked whole up to
;; six writes are about 3,000 runs and 11 s, so the sampled test walks every order only
;; up to four writes; the slow twin walks two hundred worlds whole up to six.

(deftest a-random-world-settles-as-the-reference-says
  (let [unknown (random-worlds "reference sampled" (range 1 21)
                               {:exhaustive-up-to 4 :sample 8})]
    (is (empty? unknown) (str/join "\n" unknown))))

(deftest ^:slow two-hundred-random-worlds-settle-as-the-reference-says
  (let [unknown (random-worlds "reference slow" (range 1 201)
                               {:exhaustive-up-to 6 :sample 8})]
    (is (empty? unknown) (str/join "\n" unknown))))
