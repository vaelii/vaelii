;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.nat-value-maintenance-test
  "A correspondence keeps the mint map its own supported rewrite supersedes."
  (:require [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.oplog :as oplog]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(defn- application-maps
  "Every stored map of expression, including retired maps, not only believed ones."
  [kb expression]
  (filter #(let [[f _ e] (:sentence %)] (and (= 'natFormula f) (= expression e)))
          (v/find-sentexes kb 'natFormula)))

(defn- declare-function!
  "Declare one application, its result/projection, and two sibling readers on a bare KB."
  ([kb] (declare-function! kb 'CxUniverse 'CxUniverse))
  ([kb result-context projection-context]
   (doseq [s '[(reifiable_function QualifierFn)
               (genlCx CxStory CxUniverse)
               (genlCx CxOther CxUniverse)]]
     (v/assert kb s 'CxUniverse))
   (v/assert kb '(result QualifierFn qualified_relation) result-context)
   (v/assert kb '(functionCorrespondingPredicate QualifierFn qualifierOf 2) projection-context)))

(defn- named-answers
  "The named target's result membership, correspondence projection and original use."
  ([kb context] (named-answers kb 'namedRoot context))
  ([kb target context]
   (mapv #(v/ask? kb % context)
         [(list 'qualified_relation target)
          (list 'qualifierOf 'base target)
          (list 'related target 'Other)])))

(deftest a-compound-rewrite-keeps-its-projection-through-a-deferred-settle
  (doseq [deferred? [false true]
          context '[CxUniverse CxStory]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (declare-function! kb)
      (let [h (atom nil)
            write! #(do (v/assert kb '(related (QualifierFn base) Other) 'CxUniverse)
                        (reset! h (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) context)))]
        (if deferred? (v/with-deferred-settle kb (write!)) (write!))
        (is (= [true true true] (named-answers kb context)))
        (when (= 'CxStory context)
          (is (= [false false false] (named-answers kb 'CxOther)))
          (is (= [false false false] (named-answers kb 'CxUniverse))))
        (v/retract! kb @h)
        (is (= [false false false] (named-answers kb context)))
        (is (true? (v/ask? kb '(related (QualifierFn base) Other) context)))))))

(deftest a-retired-map-does-not-keep-a-withdrawn-correspondence
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (declare-function! kb)
    (v/with-deferred-settle kb
      (v/assert kb '(related (QualifierFn base) Other) 'CxUniverse)
      (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxUniverse))
    (is (= [true true true] (named-answers kb 'CxUniverse)))
    (v/retract! kb (v/handle-of kb '(functionCorrespondingPredicate QualifierFn qualifierOf 2) 'CxUniverse))
    (is (= [true false true] (named-answers kb 'CxUniverse)))))

(deftest a-named-result-does-not-rest-on-its-independent-premise
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (declare-function! kb)
    (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxUniverse)
    (let [use (v/assert kb '(qualified_relation namedRoot) 'CxUniverse)]
      (is (true? (v/ask? kb '(qualifierOf base namedRoot) 'CxUniverse)))
      (is (empty? (for [id (p/justification-ids (:records kb))
                        :let [j (p/get-justification (:records kb) id)]
                        :when (some #{(:consequence j)} (:antecedents j))]
                    id)))
      (v/retract! kb use)
      (is (= [false false false] (named-answers kb 'CxUniverse))))))

(deftest independent-proof-changes-on-an-existing-row-refresh-named-demand
  (doseq [mode [:eager :deferred :replay :except]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (declare-function! kb)
      (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxUniverse)
      (v/assert-rule kb '[(qualified_relation ?x)] '(shadow ?x) 'CxUniverse {:direction :forward})
      ;; Neither this rule nor its trigger names the target. Its conclusion is
      ;; reified onto an already IN row, so support changes without a label move.
      (if (= :except mode)
        (v/assert kb (tu/except-rule '(muted ?x) '[(signal ?x)] '(shadow (QualifierFn ?x))) 'CxUniverse)
        (v/assert-rule kb '[(signal ?x)] '(shadow (QualifierFn ?x)) 'CxUniverse {:direction :forward}))
      (is (false? (v/ask? kb '(qualified_relation namedRoot) 'CxUniverse)))
      (let [use (v/assert kb '(marked namedRoot) 'CxUniverse)
            shadow (v/handle-of kb '(shadow namedRoot) 'CxUniverse)
            result (v/handle-of kb '(qualified_relation namedRoot) 'CxUniverse)
            shadow-support? #(boolean
                              (some (fn [id]
                                      (let [j (p/get-justification (:records kb) id)]
                                        (and (= result (:consequence j))
                                             (some #{shadow} (:antecedents j)))))
                                    (p/justification-ids (:records kb))))
            before (set (p/justification-ids (:records kb)))
            signal (atom nil)]
        (is (true? (v/ask? kb '(shadow namedRoot) 'CxUniverse)))
        (is (false? (shadow-support?)))
        (case mode
          :deferred (v/with-deferred-settle kb (reset! signal (v/assert kb '(signal base) 'CxUniverse)))
          :replay (do (oplog/replay! kb [{:op :assert :args ['(signal base) 'CxUniverse]
                                          :in {:defer-settle? true :sweep? true}}
                                         {:op :settle :args [] :in {:seed-moves? true}}])
                      (reset! signal (v/handle-of kb '(signal base) 'CxUniverse)))
          (:eager :except) (reset! signal (v/assert kb '(signal base) 'CxUniverse)))
        (is (= shadow (v/handle-of kb '(shadow namedRoot) 'CxUniverse)))
        (is (true? (shadow-support?)))
        (is (empty? @(reasoning/respell kb)))
        (when (= :except mode)
          (let [blocker (v/assert kb '(muted base) 'CxUniverse)]
            (is (true? (v/ask? kb '(shadow namedRoot) 'CxUniverse)))
            (is (false? (shadow-support?)))
            (v/retract! kb blocker)
            (is (true? (shadow-support?)))))
        (v/retract! kb @signal)
        (is (true? (v/ask? kb '(shadow namedRoot) 'CxUniverse)))
        (is (false? (shadow-support?)))
        (is (= before (set (p/justification-ids (:records kb)))))
        (is (empty? @(reasoning/respell kb)))
        (v/retract! kb use)
        (is (false? (v/ask? kb '(qualified_relation namedRoot) 'CxUniverse)))
        (is (false? (v/ask? kb '(shadow namedRoot) 'CxUniverse)))))))

(deftest record-only-direction-edits-refresh-named-support-when-settled
  (tu/with-cleared-kb [kb tu/isolated-fresh]
    (declare-function! kb)
    (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxUniverse)
    (v/assert-rule kb '[(qualified_relation ?x)] '(shadow ?x) 'CxUniverse {:direction :forward})
    (let [use (v/assert kb '(marked namedRoot) 'CxUniverse)
          signal (v/assert kb '(signal base) 'CxUniverse)
          rule (v/assert-rule kb '[(signal ?x)] '(shadow (QualifierFn ?x))
                              'CxUniverse {:direction :backward})
          shadow (v/handle-of kb '(shadow namedRoot) 'CxUniverse)
          result (v/handle-of kb '(qualified_relation namedRoot) 'CxUniverse)
          records (:records kb)
          shadow-support? #(boolean
                            (some (fn [id]
                                    (let [j (p/get-justification records id)]
                                      (and (= result (:consequence j))
                                           (some #{shadow} (:antecedents j)))))
                                  (p/justification-ids records)))
          reopened (tu/isolated-test-kb)
          blind (assoc reopened :reasoning
                       (reify clojure.lang.IDeref
                         (deref [_] (throw (ex-info "record-only edit read belief" {})))))]
      (is (true? (v/in? kb shadow)))
      (is (false? (shadow-support?)))
      (let [edit (v/edit-records! blind {:direction {rule :forward}})]
        (is (= 1 (:redirected edit)))
        (is (false? (shadow-support?)))
        (v/settle-record-edits! reopened {:seeds (:seeds edit) :arg-types? false})
        (is (true? (shadow-support?)))
        (is (empty? @(reasoning/respell reopened)))
        (v/retract! reopened use)
        (is (true? (v/ask? reopened '(qualified_relation namedRoot) 'CxUniverse)))
        (v/retract! reopened signal)
        (is (false? (v/ask? reopened '(qualified_relation namedRoot) 'CxUniverse)))
        (is (false? (v/ask? reopened '(shadow namedRoot) 'CxUniverse)))))))

(deftest nested-write-observers-reuse-the-owner-and-ignore-other-networks
  (tu/with-neutral-kb [a tu/isolated-fresh]
    (tu/with-neutral-kb [b tu/isolated-fresh]
      (#'v/with-support-observer
       a
       (fn []
         (let [outer jtms/*support-observer*]
           (#'v/with-support-observer a #(is (identical? outer jtms/*support-observer*)))
           (#'v/with-support-observer
            b
            (fn []
              (is (identical? (reasoning/tms b) (:tms jtms/*support-observer*)))
              (is (identical? outer (:previous jtms/*support-observer*)))
              (#'v/with-support-observer
               a
               (fn []
                 (is (identical? (reasoning/tms a) (:tms jtms/*support-observer*)))
                 (is (not (identical? outer jtms/*support-observer*)))))))
           (is (identical? outer jtms/*support-observer*))))))))

(deftest a-private-guard-does-not-globally-invalidate-an-independent-use
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (declare-function! kb)
    (v/assert kb '(genlCx CxSecret CxUniverse) 'CxUniverse)
    (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxUniverse)
    (v/assert-rule kb '[(qualified_relation ?x)] '(shadow ?x) 'CxUniverse {:direction :forward})
    (v/assert kb (tu/except-rule '(muted ?x) '[(signal ?x)] '(shadow (QualifierFn ?x))) 'CxUniverse)
    (let [signal (v/assert kb '(signal base) 'CxUniverse)
          before (tu/baseline kb)
          blocker (v/assert kb '(muted base) 'CxSecret)]
      (is (true? (v/ask? kb '(qualified_relation namedRoot) 'CxUniverse)))
      (is (true? (v/ask? kb '(qualified_relation namedRoot) 'CxOther)))
      (is (false? (v/ask? kb '(qualified_relation namedRoot) 'CxSecret)))
      (is (false? (v/ask? kb '(qualifierOf base namedRoot) 'CxSecret)))
      (v/retract! kb blocker)
      (is (true? (v/ask? kb '(qualified_relation namedRoot) 'CxSecret)))
      (is (= before (tu/baseline kb)))
      (v/retract! kb signal)
      (is (false? (v/ask? kb '(qualified_relation namedRoot) 'CxUniverse))))))

(deftest distinct-genl-uses-keep-their-own-named-supports
  (doseq [parents ['[first_parent second_parent] '[second_parent first_parent]]
          remove-first? [false true]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (declare-function! kb)
      (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxUniverse)
      (let [write! #(v/assert kb (list 'genl 'namedRoot %) 'CxUniverse
                              {:max-ms 1000 :max-derivations 100})
            a (write! (first parents))
            b (atom nil)
            status (try (reset! b (write! (second parents))) :returned
                        (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))
            proofs #(filter (fn [j] (= :vaelii.impl.named-application/named-application (:informant j)))
                            (v/supporting-justifications
                             kb (v/handle-of kb '(qualified_relation namedRoot) 'CxUniverse)))]
        (is (= :returned status) "two genuine uses must not cause a support-only replacement loop")
        (is (some? @b))
        (is (= #{#{a} #{@b}}
               (into #{} (map (fn [j] (into #{} (filter #{a @b}) (:antecedents j)))) (proofs))))
        (let [ids (set (map :id (proofs)))
              removed (if remove-first? a @b)
              remaining (if remove-first? @b a)
              survivor (into #{} (comp (filter #(some #{remaining} (:antecedents %))) (map :id)) (proofs))]
          (is (false? (:truncated? (v/forward-chain kb {:max-ms 1000 :max-derivations 100}))))
          (is (= ids (set (map :id (proofs)))))
          (when removed (v/retract! kb removed))
          (is (= survivor (set (map :id (proofs))))
              "removing either arrival removes only the proof using it")
          (is (true? (v/ask? kb '(qualifierOf base namedRoot) 'CxUniverse))))))))

(deftest compound-binding-presence-follows-support-and-belief
  (let [tx (tax/create-taxonomy)]
    (is (false? (tax/compound-rewrites? tx)))
    (tax/mark-compound-rewrite tx 'namedRoot 10 'CxUniverse)
    (tax/mark-compound-rewrite tx 'namedRoot 11 'CxStory)
    (tax/unmark-compound-rewrite! tx 'namedRoot 10)
    (is (true? (tax/compound-rewrites? tx)))
    (tax/refresh-beliefs tx #{} #{11})
    (is (false? (tax/compound-rewrites? tx)))
    (tax/refresh-beliefs tx #{11} #{11})
    (is (true? (tax/compound-rewrites? tx)))
    (tax/clear-relations! tx)
    (is (false? (tax/compound-rewrites? tx)))
    (tax/mark-compound-rewrite tx 'namedRoot 11 'CxStory)
    (is (true? (tax/compound-rewrites? tx)))
    (tax/unmark-compound-rewrite! tx 'namedRoot 11)
    (is (false? (tax/compound-rewrites? tx)))))

(deftest named-binding-presence-survives-recovery-and-preview-rollback
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (declare-function! kb)
    (let [global (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxUniverse)
          local (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxStory)]
      (v/assert kb '(related namedRoot Other) 'CxUniverse)
      (v/retract! kb global)
      (is (true? (nat-read/named-values-reachable? kb)))
      (is (= [true true true] (named-answers kb 'CxStory)))
      (v/recover kb)
      (is (true? (nat-read/named-values-reachable? kb)))
      (is (= [true true true] (named-answers kb 'CxStory)))
      (let [seen (atom #{})
            present? nat-read/named-values-reachable?
            before (tu/baseline kb)]
        (with-redefs [nat-read/named-values-reachable?
                      (fn [candidate]
                        (let [answer (present? candidate)]
                          (when (identical? kb candidate) (swap! seen conj answer))
                          answer))]
          (v/preview kb {:remove [local]}))
        (is (contains? @seen false) "suspending the last alias makes the actual presence cache empty")
        (is (true? (present? kb)) "rollback revives its supporter")
        (is (= before (tu/baseline kb)))
        (is (= [true true true] (named-answers kb 'CxStory))))
      (v/preview kb {:add [['(rewriteOf rivalRoot (QualifierFn base)) 'CxStory]]})
      (is (= [true true true] (named-answers kb 'CxStory)))
      (v/retract! kb local)
      (is (false? (nat-read/named-values-reachable? kb)))
      (is (= [false false true] (named-answers kb 'CxStory))))))

(deftest a-retired-map-does-not-keep-an-ambiguous-rewrite
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (declare-function! kb)
    (v/with-deferred-settle kb
      (v/assert kb '(related (QualifierFn base) Other) 'CxUniverse)
      (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxUniverse))
    (is (= [true true true] (named-answers kb 'CxUniverse)))
    (let [rival (v/assert kb '(rewriteOf rivalRoot (QualifierFn base)) 'CxUniverse)]
      (is (= [false false false] (named-answers kb 'CxUniverse)))
      (is (false? (v/ask? kb '(related rivalRoot Other) 'CxUniverse)))
      (is (true? (v/ask? kb '(related (QualifierFn base) Other) 'CxUniverse)))
      (v/retract! kb rival)
      (is (= [true true true] (named-answers kb 'CxUniverse))))))

(deftest an-actually-used-compound-rewrite-target-has-the-same-result-and-projection-in-either-order
  (doseq [alias-first? [true false]
          deferred? [false true]
          context '[CxUniverse CxStory]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (declare-function! kb)
      (let [alias '(rewriteOf namedRoot (QualifierFn base))
            use   '(related (QualifierFn base) Other)
            load! #(doseq [s (if alias-first? [alias use] [use alias])]
                     (v/assert kb s context))]
        (if deferred? (v/with-deferred-settle kb (load!)) (load!))
        (is (= [true true true] (named-answers kb context))
            (pr-str {:alias-first? alias-first? :deferred? deferred? :context context}))
        (when alias-first?
          (is (zero? (count (application-maps kb '(QualifierFn base))))))
        (when (= 'CxStory context)
          (is (= [false false false] (named-answers kb 'CxOther)))
          (is (= [false false false] (named-answers kb 'CxUniverse))))))))

(deftest named-results-are-structural-but-the-projection-declaration-is-contextual
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (declare-function! kb 'CxOther 'CxOther)
    (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxStory)
    (v/assert kb '(related (QualifierFn base) Other) 'CxStory)
    (is (= [true false true] (named-answers kb 'CxStory)))
    (is (= [false false false] (named-answers kb 'CxOther)))
    (let [edge (v/assert kb '(genlCx CxStory CxOther) 'CxUniverse)]
      (is (= [true true true] (named-answers kb 'CxStory)))
      (v/retract! kb edge)
      (is (= [true false true] (named-answers kb 'CxStory))))))

(deftest a-used-named-target-takes-late-declarations-and-loses-their-derived-facts
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (v/assert kb '(reifiable_function QualifierFn) 'CxUniverse)
    (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxUniverse)
    (v/assert kb '(related (QualifierFn base) Other) 'CxUniverse)
    (is (= [false false true] (named-answers kb 'CxUniverse)))
    (let [result (v/assert kb '(result QualifierFn qualified_relation) 'CxUniverse)
          projection (v/assert kb '(functionCorrespondingPredicate QualifierFn qualifierOf 2) 'CxUniverse)]
      (is (= [true true true] (named-answers kb 'CxUniverse)))
      (v/retract! kb result)
      (is (= [false true true] (named-answers kb 'CxUniverse)))
      (v/retract! kb projection)
      (is (= [false false true] (named-answers kb 'CxUniverse))))))

(deftest derived-metadata-is-not-its-own-demand-and-independent-uses-are-retained
  (doseq [deferred? [false true]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (declare-function! kb)
      (v/assert-rule kb '[(qualified_relation ?x)] '(shadow ?x) 'CxUniverse {:direction :forward})
      (v/assert-rule kb '[(shadow ?x)] '(qualified_relation ?x) 'CxUniverse {:direction :forward})
      (let [alias (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxUniverse)
            h (atom nil)
            use! #(reset! h (v/assert kb '(related (QualifierFn base) Other) 'CxUniverse))]
        (v/assert kb '(comment Example (Quote namedRoot)) 'CxUniverse)
        (is (= [false false false] (named-answers kb 'CxUniverse)))
        (v/preview kb {:add [['(related (QualifierFn base) Other) 'CxUniverse]]})
        (is (= [false false false] (named-answers kb 'CxUniverse)))
        (if deferred? (v/with-deferred-settle kb (use!)) (use!))
        (is (= [true true true] (named-answers kb 'CxUniverse)))
        (is (true? (v/ask? kb '(shadow namedRoot) 'CxUniverse)))
        (let [independent (v/assert kb '(shadow namedRoot) 'CxUniverse)]
          (v/retract! kb @h)
          (is (= [true true false] (named-answers kb 'CxUniverse)))
          (v/retract! kb independent)
          (is (= [false false false] (named-answers kb 'CxUniverse)))
          (is (false? (v/ask? kb '(shadow namedRoot) 'CxUniverse))))
        (v/retract! kb alias)))))

(deftest an-ambiguous-alias-withdraws-derived-metadata-not-the-captured-user-tuple
  (doseq [deferred? [false true]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (declare-function! kb)
      (let [alias (atom (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxUniverse))
            rival (atom nil)]
        (v/assert kb '(related (QualifierFn base) Other) 'CxUniverse)
        (is (= [true true true] (named-answers kb 'CxUniverse)))
        (let [add! #(do (reset! rival (v/assert kb '(rewriteOf rivalRoot (QualifierFn base)) 'CxUniverse))
                        (v/assert kb '(marked rivalRoot) 'CxUniverse))]
          (if deferred? (v/with-deferred-settle kb (add!)) (add!)))
        (is (= [false false true] (named-answers kb 'CxUniverse)))
        (is (= [false false false] (named-answers kb 'rivalRoot 'CxUniverse)))
        (v/retract! kb @alias)
        (is (= [true true false] (named-answers kb 'rivalRoot 'CxUniverse)))
        (reset! alias (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxUniverse))
        (is (= [false false true] (named-answers kb 'CxUniverse)))
        (is (= [false false false] (named-answers kb 'rivalRoot 'CxUniverse)))
        (v/retract! kb @rival)
        (is (= [true true true] (named-answers kb 'CxUniverse)))
        (is (= [false false false] (named-answers kb 'rivalRoot 'CxUniverse)))
        (v/retract! kb @alias)
        (is (= [false false true] (named-answers kb 'CxUniverse)))))))

(deftest an-excepted-alias-withdraws-and-restores-the-named-metadata
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (declare-function! kb)
    (let [alias (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxUniverse)]
      (v/assert kb '(related (QualifierFn base) Other) 'CxStory)
      (is (= [true true true] (named-answers kb 'CxStory)))
      (let [except (v/assert kb (list 'except (list 'sentexHandle alias)) 'CxStory)]
        (is (= [false false true] (named-answers kb 'CxStory)))
        (v/retract! kb except)
        (is (= [true true true] (named-answers kb 'CxStory)))))))

(deftest named-support-is-owned-after-a-contextual-target-normalization
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (declare-function! kb)
    (let [alias (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxStory)]
      (v/assert kb '(related (QualifierFn base) Other) 'CxStory)
      (v/assert kb '(rewriteOf preferredRoot namedRoot) 'CxStory)
      (is (true? (v/ask? kb '(qualified_relation preferredRoot) 'CxStory)))
      (is (true? (v/ask? kb '(qualifierOf base preferredRoot) 'CxStory)))
      (is (false? (v/ask? kb '(qualified_relation preferredRoot) 'CxOther)))
      (v/retract! kb alias)
      (is (false? (v/ask? kb '(qualified_relation preferredRoot) 'CxStory)))
      (is (false? (v/ask? kb '(qualifierOf base preferredRoot) 'CxStory)))
      (is (true? (v/ask? kb '(related preferredRoot Other) 'CxStory))))))

(deftest an-admissible-genlresult-is-derived-and-withdrawn-with-its-support
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (doseq [s '[(reifiable_function TypeQualifierFn)
                (rewriteOf named_type (TypeQualifierFn base))
                (related (TypeQualifierFn base) Other)]]
      (v/assert kb s 'CxUniverse))
    (let [declaration (v/assert kb '(genlResult TypeQualifierFn super_type) 'CxUniverse)]
      (is (true? (v/ask? kb '(genl named_type super_type) 'CxUniverse)))
      (v/retract! kb declaration)
      (is (false? (v/ask? kb '(genl named_type super_type) 'CxUniverse)))
      (is (true? (v/ask? kb '(related named_type Other) 'CxUniverse))))))

(deftest named-materialization-keeps-the-existing-forced-output-restriction
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (doseq [s '[(reifiable_function PredicateQualifierFn)
                (rewriteOf namedPredicate (PredicateQualifierFn base))
                (related (PredicateQualifierFn base) Other)
                (genlResult PredicateQualifierFn superPredicate)]]
      (v/assert kb s 'CxUniverse))
    (is (true? (v/ask? kb '(genlResult PredicateQualifierFn superPredicate) 'CxUniverse)))
    (is (true? (v/ask? kb '(related namedPredicate Other) 'CxUniverse)))
    (is (false? (v/ask? kb '(genl namedPredicate superPredicate) 'CxUniverse)))))

(deftest commuting-alias-peers-are-invalidated-on-alias-and-mark-changes
  (doseq [mark '[(commutative PairFn) (commutativeInArgs PairFn 1 2)]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (doseq [s '[(binary_function PairFn) (reifiable_function PairFn)
                  (result PairFn qualified_relation)
                  (functionCorrespondingPredicate PairFn pairProjection 3)]]
        (v/assert kb s 'CxUniverse))
      (let [m (atom (v/assert kb mark 'CxUniverse))
            first-alias (v/assert kb '(rewriteOf firstPair (PairFn A B)) 'CxUniverse)]
        (v/assert kb '(marked firstPair) 'CxUniverse)
        (is (true? (v/ask? kb '(qualified_relation firstPair) 'CxUniverse)))
        (let [second-alias (v/assert kb '(rewriteOf secondPair (PairFn B A)) 'CxUniverse)]
          (v/assert kb '(marked secondPair) 'CxUniverse)
          (is (= (nat-read/sorted-expression kb '(PairFn A B))
                 (nat-read/sorted-expression kb '(PairFn B A))))
          (is (nil? (nat-read/rewrite-target kb '(PairFn A B) nat-read/nat-namespace 'CxUniverse)))
          (is (false? (v/ask? kb '(qualified_relation firstPair) 'CxUniverse)))
          (is (false? (v/ask? kb '(qualified_relation secondPair) 'CxUniverse)))
          (v/retract! kb @m)
          (is (true? (v/ask? kb '(qualified_relation firstPair) 'CxUniverse)))
          (is (true? (v/ask? kb '(qualified_relation secondPair) 'CxUniverse)))
          (reset! m (v/assert kb mark 'CxUniverse))
          (is (false? (v/ask? kb '(qualified_relation firstPair) 'CxUniverse)))
          (v/retract! kb first-alias)
          (is (true? (v/ask? kb '(qualified_relation secondPair) 'CxUniverse)))
          (is (true? (v/ask? kb '(pairProjection A B secondPair) 'CxUniverse)))
          (v/retract! kb second-alias))))))

(deftest named-projections-reify-nested-arguments-and-reach-a-fixed-point
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (doseq [s '[(reifiable_function InnerFn) (reifiable_function OuterFn)
                (result OuterFn qualified_relation)
                (functionCorrespondingPredicate OuterFn outerProjection 2)
                (functionCorrespondingPredicate InnerFn innerProjection 2)
                (rewriteOf namedRoot (OuterFn (InnerFn X)))
                (marked namedRoot)]]
      (v/assert kb s 'CxUniverse))
    (is (true? (v/ask? kb '(outerProjection (InnerFn X) namedRoot) 'CxUniverse)))
    (is (= 1 (count (application-maps kb '(InnerFn X)))))
    (is (zero? (count (application-maps kb '(OuterFn (InnerFn X))))))
    (is (false? (:truncated? (v/forward-chain kb {:max-derivations 100 :max-ms 10000}))))
    (let [n (count (p/justification-ids (:records kb)))]
      (is (false? (:truncated? (v/forward-chain kb {:max-derivations 100 :max-ms 10000}))))
      (is (= n (count (p/justification-ids (:records kb)))))
      (is (= 1 (count (application-maps kb '(InnerFn X))))))))

(deftest private-identity-is-a-private-demand-witness-not-public-authority
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (declare-function! kb)
    (v/assert kb '(genlCx CxSecret CxUniverse) 'CxUniverse)
    (v/assert kb '(genlCx CxVia CxUniverse) 'CxUniverse)
    (v/assert kb '(rewriteOf namedRoot (QualifierFn base)) 'CxUniverse)
    (v/assert kb '(related publicPeer Other) 'CxUniverse)
    (let [goals #(mapv (fn [c] (take 2 (named-answers kb c))) '[CxUniverse CxSecret CxOther])
          private-answer [[false false] [true true] [false false]]
          h (atom nil)]
      (is (= [[false false] [false false] [false false]] (goals)))
      (reset! h (v/assert kb '(rewriteOf publicPeer namedRoot) 'CxSecret))
      (is (= private-answer (goals)))
      (let [a (v/assert kb '(equals namedRoot intermediatePeer) 'CxSecret)
            b (v/assert kb '(equals intermediatePeer publicPeer) 'CxSecret)]
        (v/retract! kb @h)
        (is (= private-answer (goals)))
        (v/retract! kb a)
        (v/retract! kb b))
      (is (= [[false false] [false false] [false false]] (goals)))
      (reset! h (v/assert kb '(rewriteOf publicPeer namedRoot) 'CxVia))
      (is (= [[false false] [false false] [false false]] (goals)))
      (let [via (v/assert kb '(genlCx CxSecret CxVia) 'CxUniverse)]
        (is (= private-answer (goals)))
        (v/retract! kb via)
        (is (= [[false false] [false false] [false false]] (goals)))))))

(deftest a-nested-mint-is-not-its-outer-named-targets-independent-demand
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (doseq [s '[(reifiable_function InnerFn) (reifiable_function OuterFn)
                (result OuterFn qualified_relation)
                (functionCorrespondingPredicate OuterFn outerProjection 2)
                (functionCorrespondingPredicate InnerFn innerProjection 2)
                (rewriteOf namedRoot (OuterFn (InnerFn namedRoot)))]]
      (v/assert kb s 'CxUniverse))
    (doseq [[antecedent conclusion] '[[(innerProjection ?x ?k) (shadow ?x)]
                                      [(shadow ?x) (shadow_again ?x)]
                                      [(independentLink ?x ?k) (innerProjection ?x ?k)]]]
      (v/assert-rule kb [antecedent] conclusion 'CxUniverse {:direction :forward}))
    (let [use (v/assert kb '(marked namedRoot) 'CxUniverse)]
      (is (true? (v/ask? kb '(qualified_relation namedRoot) 'CxUniverse)))
      (is (true? (v/ask? kb '(shadow_again namedRoot) 'CxUniverse)))
      (let [inner-use (v/assert kb '(kept (InnerFn namedRoot)) 'CxUniverse)]
        (v/retract! kb use)
        (is (true? (v/ask? kb '(qualified_relation namedRoot) 'CxUniverse)))
        (v/retract! kb inner-use)
        (is (false? (v/ask? kb '(qualified_relation namedRoot) 'CxUniverse)))
        (let [independent (v/assert kb '(innerProjection namedRoot (InnerFn namedRoot)) 'CxUniverse)]
          (is (true? (v/ask? kb '(qualified_relation namedRoot) 'CxUniverse)))
          (v/retract! kb independent)
          (is (false? (v/ask? kb '(qualified_relation namedRoot) 'CxUniverse))))
        (let [independent (v/assert kb '(independentLink namedRoot (InnerFn namedRoot)) 'CxUniverse)]
          (is (true? (v/ask? kb '(qualified_relation namedRoot) 'CxUniverse)))
          (v/retract! kb independent)
          (is (false? (v/ask? kb '(qualified_relation namedRoot) 'CxUniverse))))
        (is (zero? (count (application-maps kb '(OuterFn (InnerFn namedRoot))))))))))
