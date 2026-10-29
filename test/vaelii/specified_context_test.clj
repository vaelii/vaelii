;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.specified-context-test
  (:require [clojure.test :refer [is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.budget :as budget]
            [vaelii.impl.defining :as defining]
            [vaelii.impl.predall :as predall]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (tu/load-core!))))

(defn- note [functor pred subject]
  (if (= functor 'predAllSpecified)
    (list pred subject "A direct fictional note.")
    (list pred "A direct fictional note." subject)))

(defn- schema [kb functor pred kind]
  (v/assert kb (list 'binary_predicate pred) 'CxUniverse)
  (v/assert kb (list 'unary_predicate kind) 'CxUniverse)
  (v/assert kb (list 'arg pred (if (= functor 'predAllSpecified) 2 1) 'string) 'CxUniverse))

(defn- result [kb functor pred kind context]
  (get (v/all-specified-violations kb context) [functor pred kind]
       {:status :audited :violations #{}}))

(tu/deftest-kb hidden-readers-still-consume-the-audits-work-budget
  (tu/with-terms [CxParent CxHidden notes item_kind]
    (doseq [max-work [0 160]]
      (let [checks (atom 0)]
        (with-redefs [tax/common-descendants (fn [_ _] (repeat 64 CxHidden))
                      res/matches-visible (fn [_ _ _] (swap! checks inc) [])]
          (let [outcome (try
                          (budget/metered
                           (budget/meter {:max-work max-work})
                           #(doall (#'predall/specified-context-audits
                                    kb 'predAllSpecified :second [[notes item_kind CxParent 1]])))
                          :unexpected-completion
                          (catch clojure.lang.ExceptionInfo e (budget/exhausted e)))]
            (is (= :max-work outcome))
            (is (< @checks 64)
                "readers hidden before emission cannot bypass the bound")
            (when (pos? max-work)
              (is (pos? @checks) "the positive-budget control reaches the visibility checks"))))))))

(tu/deftest-kb visibility-record-pulls-consume-the-audits-work-budget
  (tu/with-terms [CxParent notes item_kind]
    (let [pulls (atom 0)]
      (with-redefs [tax/common-descendants (fn [_ _] [CxParent])
                    res/matches-visible (fn [_ _ _]
                                          (repeatedly 256
                                                      #(do (swap! pulls inc)
                                                           [{} 2 {:id 2}])))]
        (let [outcome (try
                        (budget/metered
                         (budget/meter {:max-work 64})
                         #(doall (#'predall/specified-context-audits
                                  kb 'predAllSpecified :second [[notes item_kind CxParent 1]])))
                        :unexpected-completion
                        (catch clojure.lang.ExceptionInfo e (budget/exhausted e)))]
          (is (= :max-work outcome))
          (is (<= @pulls 64)
              "a single hidden reader cannot scan every returned visibility record")
          (is (pos? @pulls) "the control reaches the visibility provider's lazy records"))))))

(tu/deftest-kb defining-home-unions-consume-the-audits-work-budget
  (tu/with-terms [CxParent CxReader Subject]
    (let [checks (atom 0)
          homes (set (map #(symbol (str "FictionalHome" %)) (range 256)))]
      (with-redefs [defining/definition-evidence (fn [_ _] {:contexts homes :skeletal-only? false})
                    tax/common-descendants (fn [_ _] (swap! checks inc) [])]
        (let [outcome (try
                        (budget/metered (budget/meter {:max-work 32})
                                        #((#'predall/member-selector kb) CxParent CxReader Subject))
                        :unexpected-completion
                        (catch clojure.lang.ExceptionInfo e (budget/exhausted e)))]
          (is (= :max-work outcome))
          (is (<= @checks 32)
              "an empty home-to-reader join cannot scan every home before checking the bound")
          (is (pos? @checks) "the positive-budget control reaches the home joins"))))))

(tu/deftest-kb global-type-bookkeeping-does-not-require-a-child-definition-at-the-root
  (tu/with-terms [CxHome relation_kind nearbyRel notes]
    (v/assert kb (list 'genlCx CxHome 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'binary_predicate notes) 'CxUniverse)
    (v/assert kb (list 'arg notes 2 'string) 'CxUniverse)
    (v/assert kb (list 'decontextualized_predicate relation_kind) 'CxUniverse)
    (v/assert kb (list 'genl relation_kind 'binary_predicate) CxHome {:strength :monotonic})
    (v/assert kb (list relation_kind nearbyRel) CxHome {:strength :monotonic})
    (v/assert kb (list 'predAllSpecified notes relation_kind) 'CxUniverse)
    (v/assert kb (note 'predAllSpecified notes nearbyRel) CxHome)
    (is (v/ask? kb (list relation_kind nearbyRel) 'CxUniverse))
    (is (v/ask? kb (list 'binary_predicate nearbyRel) 'CxUniverse))
    (is (not (v/ask? kb (note 'predAllSpecified notes nearbyRel) 'CxUniverse)))
    (is (= {:status :audited :violations #{}}
           (result kb 'predAllSpecified notes relation_kind 'CxUniverse)))
    (v/assert kb (list 'binary_predicate nearbyRel) 'CxUniverse)
    (is (= {:status :audited :violations #{nearbyRel}}
           (result kb 'predAllSpecified notes relation_kind 'CxUniverse)))))

(tu/deftest-kb a-child-comment-exception-is-checked-after-the-parent-passes
  (doseq [functor '[predAllSpecified predSpecifiedAll]]
    (tu/with-terms [CxParent CxChild Subject notes item_kind]
      (schema kb functor notes item_kind)
      (v/assert kb (list 'genlCx CxParent 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxChild CxParent) 'CxUniverse)
      (v/assert kb (list functor notes item_kind) CxParent)
      (v/assert kb (list item_kind Subject) CxParent)
      (let [sentence (note functor notes Subject)
            h (v/assert kb sentence CxParent)]
        (is (= {:status :audited :violations #{}} (result kb functor notes item_kind CxParent)))
        (v/assert kb (list 'except (list 'sentexHandle h)) CxChild)
        (is (true? (v/ask? kb sentence CxParent)))
        (is (false? (v/ask? kb sentence CxChild)))
        (is (= {:status :audited :violations #{Subject}}
               (result kb functor notes item_kind CxParent)))
        (let [requirement (list functor notes item_kind)
              mark (v/handle-of kb requirement CxParent)]
          (v/assert kb (list 'except (list 'sentexHandle mark)) CxChild)
          (is (false? (v/ask? kb requirement CxChild)))
          (is (= {:status :audited :violations #{}}
                 (result kb functor notes item_kind CxParent))))))))

(tu/deftest-kb a-child-only-member-is-checked-in-its-own-eligible-reader
  (tu/with-terms [CxParent CxChild Subject notes item_kind]
    (schema kb 'predAllSpecified notes item_kind)
    (v/assert kb (list 'genlCx CxParent 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxChild CxParent) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified notes item_kind) CxParent)
    (v/assert kb (list item_kind Subject) CxChild)
    (is (false? (v/ask? kb (list item_kind Subject) CxParent)))
    (is (true? (v/ask? kb (list item_kind Subject) CxChild)))
    (is (= {:status :audited :violations #{Subject}}
           (result kb 'predAllSpecified notes item_kind CxParent)))
    (v/assert kb (note 'predAllSpecified notes Subject) CxChild)
    (is (= {:status :audited :violations #{}}
           (result kb 'predAllSpecified notes item_kind CxParent)))))

(tu/deftest-kb requirement-and-definition-intersections-include-the-diamond-reader
  (doseq [functor '[predAllSpecified predSpecifiedAll]]
    (tu/with-terms [CxRequirement CxDefinition CxLeft CxRight CxBottom Subject notes item_kind]
      (schema kb functor notes item_kind)
      (doseq [[sub super] [[CxRequirement 'CxUniverse] [CxDefinition 'CxUniverse]
                           [CxLeft CxRequirement] [CxLeft CxDefinition]
                           [CxRight CxRequirement] [CxRight CxDefinition]
                           [CxBottom CxLeft] [CxBottom CxRight]]]
        (v/assert kb (list 'genlCx sub super) 'CxUniverse))
      (v/assert kb (list functor notes item_kind) CxRequirement)
      (v/assert kb (list item_kind Subject) CxDefinition)
      (is (= {:status :audited :violations #{Subject}}
             (result kb functor notes item_kind CxRequirement)))
      (let [sentence (note functor notes Subject)
            left (v/assert kb sentence CxLeft)
            right (v/assert kb sentence CxRight)]
        (is (= {:status :audited :violations #{}} (result kb functor notes item_kind CxRequirement)))
        (doseq [h [left right]]
          (v/assert kb (list 'except (list 'sentexHandle h)) CxBottom))
        (is (true? (v/ask? kb sentence CxLeft)))
        (is (true? (v/ask? kb sentence CxRight)))
        (is (false? (v/ask? kb sentence CxBottom)))
        (is (= {:status :audited :violations #{Subject}}
               (result kb functor notes item_kind CxRequirement)))))))

(tu/deftest-kb only-proven-skeletal-population-is-exempt
  (tu/with-terms [CxRequirement Namespace LookupFn lookupOf namespace_kind access_kind usedBy Observer notes]
    (schema kb 'predAllSpecified notes namespace_kind)
    (v/assert kb (list 'genlCx CxRequirement 'CxUniverse) 'CxUniverse)
    (doseq [sentence [(list 'reifiable_function LookupFn)
                      (list 'result LookupFn access_kind)
                      (list 'functionCorrespondingPredicate LookupFn lookupOf)
                      (list 'arg lookupOf 1 namespace_kind)]]
      (v/assert kb sentence 'CxUniverse))
    (v/assert kb (list usedBy (list LookupFn Namespace) Observer) CxRequirement)
    (v/assert kb (list 'predAllSpecified notes namespace_kind) CxRequirement)
    (is (true? (v/ask? kb (list namespace_kind Namespace) CxRequirement)))
    (is (= #{} (v/defining-contexts kb Namespace)))
    (is (= {:status :audited :violations #{}}
           (result kb 'predAllSpecified notes namespace_kind CxRequirement)))
    (v/assert kb (list namespace_kind Namespace) CxRequirement)
    (is (= {:status :audited :violations #{Namespace}}
           (result kb 'predAllSpecified notes namespace_kind CxRequirement)))
    (v/assert kb (note 'predAllSpecified notes Namespace) CxRequirement)
    (is (= {:status :audited :violations #{}}
           (result kb 'predAllSpecified notes namespace_kind CxRequirement)))))

(tu/deftest-kb native-population-with-no-stored-home-is-not-exempt
  (tu/with-terms [CxRequirement Subject notes item_kind]
    (schema kb 'predAllSpecified notes item_kind)
    (v/assert kb (list 'genlCx CxRequirement 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified notes item_kind) CxRequirement)
    (v/add-prover kb
                  (v/prover {:applicable? (fn [_ goal _]
                                            (and (= item_kind (first goal))
                                                 (or (sx/variable? (second goal))
                                                     (= Subject (second goal)))))
                             :solve (fn [_ goal _]
                                      (if (sx/variable? (second goal))
                                        [{(second goal) Subject}] [{}]))}))
    (is (= #{} (v/defining-contexts kb Subject)))
    (is (= {:status :audited :violations #{Subject}}
           (result kb 'predAllSpecified notes item_kind CxRequirement)))
    (v/assert kb (note 'predAllSpecified notes Subject) CxRequirement)
    (is (= {:status :audited :violations #{}}
           (result kb 'predAllSpecified notes item_kind CxRequirement)))))

(tu/deftest-kb unclassified-defining-support-is-a-gap-when-the-filler-is-missing
  (tu/with-terms [CxOrigin Subject Marker Other liftedTrigger prerequisite notes item_kind]
    (schema kb 'predAllSpecified notes item_kind)
    (v/assert kb (list 'genlCx CxOrigin 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'decontextualized_predicate liftedTrigger) 'CxUniverse)
    (v/assert kb (list liftedTrigger Marker) CxOrigin)
    (v/assert kb (list prerequisite Other) 'CxUniverse)
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list 'and (list liftedTrigger Marker)
                                            (list prerequisite Other))
                             (list item_kind Subject))) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified notes item_kind) 'CxUniverse)
    (is (true? (v/ask? kb (list item_kind Subject) 'CxUniverse)))
    (let [audit (result kb 'predAllSpecified notes item_kind 'CxUniverse)]
      (is (= :gap (:status audit)))
      (is (= :incomplete-defining-contexts (:gap audit)))
      (is (= Subject (:term audit)))
      (is (seq (:handles audit)))
      (is (not (contains? audit :violations))))
    (v/add-prover kb
                  (v/prover {:applicable? (fn [_ goal _]
                                            (and (= notes (first goal))
                                                 (= Subject (second goal))))
                             :solve (fn [_ goal _]
                                      (if (sx/variable? (nth goal 2))
                                        [{(nth goal 2) "A native filler."}]
                                        (if (= "A native filler." (nth goal 2)) [{}] [])))}))
    (is (true? (v/ask? kb (list notes Subject "A native filler.") 'CxUniverse)))
    (is (= {:status :audited :violations #{}}
           (result kb 'predAllSpecified notes item_kind 'CxUniverse)))
    (let [failure (try (v/defining-contexts kb Subject) nil
                       (catch clojure.lang.ExceptionInfo e (ex-data e)))]
      (is (= :incomplete-defining-contexts (:type failure))))))
