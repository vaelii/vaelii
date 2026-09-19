;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.special-table-test
  "The special-predicate dispatch table's structural guarantees.

  The table (`vaelii.impl.special/entries`) is the one enumeration of the functors
  the engine interprets: integrate, disintegrate, rebuild and wff all walk it.  What
  makes that safe is `check-entries`, which runs at namespace load and refuses an
  entry whose cache arms are partial — the add/remove/rebuild mirroring the old
  hand-written conds left to review is now a build failure.  These tests pin the
  validator's enforcement and the table's required contents; no KB is involved, so no
  fixture is either."
  (:require [clojure.spec.alpha :as s]
            [clojure.test :refer [deftest is testing]]
            [vaelii.impl.predicates :as pr]
            [vaelii.impl.spec :as vspec]
            [vaelii.impl.special :as special]))

(deftest an-asymmetric-entry-fails-at-load
  (let [f (fn [_ _ _])]
    (testing "an integrate arm without its removal half throws"
      (is (thrown? clojure.lang.ExceptionInfo
                   (special/check-entries [['brokenPred {:integrate f}]]))))
    (testing "a disintegrate arm alone throws — the asymmetry cuts both ways"
      (is (thrown? clojure.lang.ExceptionInfo
                   (special/check-entries [['brokenPred {:disintegrate f}]]))))
    (testing "add and remove without the rebuild half throws — recover would forget it"
      (is (thrown? clojure.lang.ExceptionInfo
                   (special/check-entries [['brokenPred {:integrate f :disintegrate f}]]))))
    (testing "an entry with no arm at all throws — it can only be a typo"
      (is (thrown? clojure.lang.ExceptionInfo
                   (special/check-entries [['emptyPred {}]]))))
    (testing "the throw names the functor and the missing arms"
      (let [data (try (special/check-entries [['brokenPred {:integrate f}]])
                      (catch clojure.lang.ExceptionInfo e (ex-data e)))]
        (is (= :bad-table-entry (:type data)))
        (is (= :partial-cache-triple (:mismatch data)))
        (is (= 'brokenPred (:functor data)))
        (is (= [:disintegrate :rebuild] (:missing data)))))
    (testing "and the empty entry carries the same :type — one word for one bad table,
              whichever way it is bad, since the caller catching it is the namespace load —
              with `:mismatch` saying which way, the discriminant every `:bad-table-entry`
              in the tree carries and `type_contract_test` holds all of them to"
      (let [data (try (special/check-entries [['emptyPred {}]])
                      (catch clojure.lang.ExceptionInfo e (ex-data e)))]
        (is (= :bad-table-entry (:type data)))
        (is (= :no-arm (:mismatch data)))
        (is (= 'emptyPred (:functor data)))))))

(deftest well-formed-entries-pass
  (let [f (fn [_ _ _])]
    (testing "the full cache triple passes"
      (is (special/check-entries [['okPred {:integrate f :disintegrate f :rebuild f}]])))
    (testing "a wff-only entry passes — arg and different maintain no cache"
      (is (special/check-entries [['okPred {:wff f}]])))))

(deftest the-live-table-passes-its-own-check
  ;; `entries` is defined through `check-entries`, so namespace load already proves
  ;; this — asserting it here keeps the wiring itself pinned (a refactor that stops
  ;; routing the def through the validator would pass load and fail here).
  (is (= special/entries (special/check-entries special/entries)))
  (is (= special/table (into {} special/entries))))

(deftest the-vocabulary-the-engine-interprets-is-present
  (testing "every cache-maintaining special predicate has an entry"
    (doseq [f '[genl genlCx disjoint disjoint_metatype
                transitive symmetric reflexive functional inverse
                decontextualized_predicate forced_decontextualized_predicate]]
      (is (contains? special/table f) (str f " missing from the table"))))
  (testing "the equality relations are entries too"
    (doseq [f '[rewriteOf sameAs equals]]
      (is (contains? special/table f) (str f " missing from the table"))))
  (testing "the wff-only vocabulary is dispatched through the same table"
    (doseq [f '[arg different]]
      (is (contains? special/table f) (str f " missing from the table")))))

(deftest the-property-kinds-marked-and-the-ones-specced-are-the-same-set
  ;; `has-prop?` and `props` are specced on `::vspec/prop-kind`, and the table is what
  ;; decides which kinds exist — a mark declares its kind through the `:prop` storage
  ;; target on its declaration, which is where the spec now reads them from too.  So the
  ;; drift this held in both directions is gone rather than tested: a kind the spec names
  ;; and nothing marks cannot be written, and a kind the table marks and the spec omits
  ;; cannot either.  What is left to check is that the generated spec is a live one — a
  ;; computed `s/def` that registered nothing would refuse every call instead.
  (let [marked (into #{} (keep :prop) (vals special/table))]
    (is (contains? marked :transitive) "the table declares its kinds through :prop")
    (doseq [k marked]
      (is (s/valid? ::vspec/prop-kind k) (str k " is marked and must be a legal call")))
    (is (not (s/valid? ::vspec/prop-kind :declares-max-cardinality))
        "and the spec still refuses a kind nothing declares")))

(def ^:private frozen-table
  "The table as it stood before the enumeration moved to `vaelii.impl.predicates` —
  every functor in order, the arm columns it fills, the `:props` kind it maintains and
  whether its arms run on the derivation path.

  Frozen deliberately, and it is the only statement of these four facts that the
  declaration cannot make true by construction.  `entries` is now a *join*: the order,
  the `:prop` and the `:derived?` are read off the declaration, so a reconstruction test
  that derives them from the declaration and compares them to the table proves the join
  is wired and nothing more.  This says what the values are.

  A red line here means one of four things happened — a functor moved in the replay
  order, an arm column was gained or lost, a mark's kind changed, or a declaration
  started or stopped reaching the derivation path.  Each is a deliberate change and each
  is a change to recovery, so each rewrites this literal in the same commit that makes
  it.  It is not a golden to regenerate when it goes red."
  '[[genl                             [:integrate :disintegrate :rebuild :wff]       nil                        true]
    [genlCx                           [:integrate :disintegrate :rebuild :wff]       nil                        true]
    [disjoint                         [:integrate :disintegrate :rebuild :wff]       nil                        true]
    [disjoint_metatype                 [:integrate :disintegrate :rebuild :wff]       nil                        true]
    [sibling_disjoint                  [:integrate :disintegrate :rebuild :wff]       nil                        true]
    [siblingDisjointException         [:integrate :disintegrate :rebuild :wff]       nil                        true]
    [transitive                       [:integrate :disintegrate :rebuild :wff]       :transitive                true]
    [symmetric                        [:integrate :disintegrate :rebuild :wff]       :symmetric                 true]
    [commutative                      [:integrate :disintegrate :rebuild :wff]       :commutative               true]
    [asymmetric                       [:integrate :disintegrate :rebuild :wff]       :asymmetric                true]
    [reflexive                        [:integrate :disintegrate :rebuild :wff]       :reflexive                 true]
    [functional                       [:integrate :disintegrate :rebuild :wff]       :functional                true]
    [irreflexive                      [:integrate :disintegrate :rebuild :wff]       :irreflexive               true]
    [anti_symmetric                    [:integrate :disintegrate :rebuild :wff]       :anti-symmetric            true]
    [anti_transitive                   [:integrate :disintegrate :rebuild :wff]       :anti-transitive           true]
    [arity                            [:integrate :disintegrate :rebuild]            nil                        true]
    [functionalInArg                  [:integrate :disintegrate :rebuild :wff]       nil                        true]
    [commutativeInArgAndRest          [:integrate :disintegrate :rebuild :wff]       nil                        true]
    [commutativeInArgs                [:integrate :disintegrate :rebuild :wff]       nil                        true]
    [inverse                          [:integrate :disintegrate :rebuild :wff]       nil                        true]
    [decontextualized_predicate        [:integrate :disintegrate :rebuild :wff]       :decontextualized          false]
    [forced_decontextualized_predicate  [:integrate :disintegrate :rebuild :wff]       :forced-decontextualized   true]
    [target_following_predicate         [:integrate :disintegrate :rebuild :wff]       :target-following          true]
    [abducible_predicate               [:integrate :disintegrate :rebuild :wff]       :abducible                 true]
    [closed_extent_predicate            [:integrate :disintegrate :rebuild :wff]       :closed-extent             true]
    [modal_predicate                   [:integrate :disintegrate :rebuild :wff]       :modal                     true]
    [reifiable_function                [:integrate :disintegrate :rebuild :wff]       :reifiable                 true]
    [unreifiable_function              [:integrate :disintegrate :rebuild :wff]       :unreifiable               true]
    [quoting_function                  [:integrate :disintegrate :rebuild :wff]       :quoting                   true]
    [context_denoting_function          [:integrate :disintegrate :rebuild :wff]       :context-denoting          true]
    [contextArgSubrelation            [:wff]                                         nil                        false]
    [functionCorrespondingPredicate   [:wff]                                         nil                        false]
    [equals                           [:integrate :disintegrate :rebuild :wff]       nil                        false]
    [rewriteOf                        [:integrate :disintegrate :rebuild :wff]       nil                        false]
    [sameAs                           [:integrate :disintegrate :rebuild :wff]       nil                        false]
    [arg                              [:integrate :disintegrate :rebuild :wff]       :declares-arg-isa          true]
    [genlArg                          [:integrate :disintegrate :rebuild :wff]       :declares-arg-genl         true]
    [quotedArg                        [:integrate :disintegrate :rebuild :wff]       :declares-quoted-arg       true]
    [interArg                         [:integrate :disintegrate :rebuild :wff]       :declares-inter-arg-isa    true]
    [args                             [:integrate :disintegrate :rebuild :wff]       :declares-args-isa         true]
    [argsGenl                         [:integrate :disintegrate :rebuild :wff]       :declares-args-genl        true]
    [argAndRest                       [:integrate :disintegrate :rebuild :wff]       :declares-arg-and-rest-isa true]
    [argAndRestGenl                   [:integrate :disintegrate :rebuild :wff]       :declares-arg-and-rest-genl true]
    [transitiveInArg                  [:wff]                                         nil                        false]
    [transitiveInArgInverse           [:wff]                                         nil                        false]
    [defnNecessary                    [:wff]                                         nil                        false]
    [defnSufficient                   [:wff]                                         nil                        false]
    [defnIff                          [:wff]                                         nil                        false]
    [different                        [:wff]                                         nil                        false]
    [unknown                          [:wff]                                         nil                        false]
    [thereExists                      [:wff]                                         nil                        false]
    [forall                           [:wff]                                         nil                        false]
    [bravely                          [:wff]                                         nil                        false]
    [cautiously                       [:wff]                                         nil                        false]
    [agg/count                        [:wff]                                         nil                        false]
    [agg/sum                          [:wff]                                         nil                        false]
    [agg/min                          [:wff]                                         nil                        false]
    [agg/max                          [:wff]                                         nil                        false]
    [agg/avg                          [:wff]                                         nil                        false]])

(deftest the-table-still-holds-what-it-held-before-the-enumeration-moved
  ;; `entries` joins the arms in `special` to the declarations in
  ;; `vaelii.impl.predicates`, and `check-declarations` refuses a disagreement at
  ;; namespace load.  What neither validator can see is an arm attached to the *wrong*
  ;; functor, or a whole entry that slid past in the join — both of which pass load,
  ;; pass every in-process test that does not exercise that predicate, and come back
  ;; wrong after a restart, because `rebuild-taxonomy` is this vector replayed.
  (is (= frozen-table
         (mapv (fn [[f spec]]
                 [f (vec (filter #(get spec %) [:integrate :disintegrate :rebuild :wff]))
                  (:prop spec)
                  (boolean (:derived? spec))])
               special/entries))))

(deftest the-declaration-and-the-arms-are-one-enumeration
  (testing "a table that enumerates different functors than the declarations is refused"
    ;; the mirror of `check-entries`: that one refuses an entry whose arms disagree with
    ;; each other, this one refuses a table that disagrees with what the predicates say.
    (let [data (try (special/check-declarations [['brokenPred {:wff (fn [_ _])}]])
                    (catch clojure.lang.ExceptionInfo e (ex-data e)))]
      (is (= :bad-table-entry (:type data))
          "one word for one bad table — the caller catching it is the namespace load")
      (is (= :enumeration (:mismatch data))
          ":mismatch is what says which validator refused it")))
  (testing "an arm keyed on a functor no declaration places in the table is refused —
            the direction the live join reads off the arms map, since a stray arm never
            reaches the filtered entries the one-argument arity would read"
    ;; The two-argument arity is the one `entries` calls, handing it `(set (keys arms))`.
    ;; A stray functor in that set is armed with no declaration, and must be refused rather
    ;; than dropped from the join.
    (let [data (try (special/check-declarations
                     special/entries
                     (conj (set (map first special/entries)) 'strayArm))
                    (catch clojure.lang.ExceptionInfo e (ex-data e)))]
      (is (= :enumeration (:mismatch data)))
      (is (= '[strayArm] (:undeclared data)))))
  (testing "the live table passes, which namespace load already proved"
    (is (= special/entries (special/check-declarations special/entries)))))

(deftest the-live-join-reads-every-arm-off-a-declaration
  ;; `entries` filters `predicates/entries` to `pr/in-special-table` before it looks an
  ;; arm up, so an arm keyed on a functor absent from that set is dropped from the join.
  ;; The load check reads the arm functors off the `arms` map — not off the filtered
  ;; vector — so such a stray arm is refused rather than left out unreported.
  (testing "no stray arm today: every armed functor is a declared table functor"
    (is (= (set (keys @#'special/arms)) pr/in-special-table)))
  (testing "and the construction refuses one that is added"
    ;; the def is evaluated once at load, so rebuild the exact construction it uses with
    ;; one stray arm and drive the same check the def drives.
    (let [arms  @#'special/arms
          dh    #'special/declared-half
          stray (assoc arms 'strayArm {:wff (fn [_ _ _])})
          built (into [] (comp (map first)
                               (filter pr/in-special-table)
                               (map (fn [f] [f (merge (dh f) (stray f))])))
                      pr/entries)
          data  (try (special/check-declarations built (set (keys stray)))
                     (catch clojure.lang.ExceptionInfo e (ex-data e)))]
      (is (= :bad-table-entry (:type data)))
      (is (= :enumeration (:mismatch data)))
      (is (= '[strayArm] (:undeclared data)))
      (is (not (some #(= 'strayArm (first %)) built))
          "the stray arm was dropped from the join, which is why the check must read the
           arms map and not the filtered vector"))))
