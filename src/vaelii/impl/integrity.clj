;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.integrity
  "Bounded, read-only KB integrity reporting: the passes `kb-integrity` runs under a work
  meter (`vaelii.impl.budget`).  `vaelii.core` requires this namespace; it requires
  `predall` and `provers`, which also sit below `vaelii.core`.  See docs/integrity.md."
  (:require [clojure.string :as str]
            [vaelii.impl.budget :as budget]
            [vaelii.impl.decide.arity :as arity]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.predall :as predall]
            [vaelii.impl.predicates :as predicates]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.violations :as violations]))

(def integrity-opt-keys
  "The options `kb-integrity` reads: three cooperative bounds and the categories to run."
  #{:max-work :max-ms :max-results :categories})

(defn- specified-findings
  "Audit one declared predicate at a time, stopping after the first finding beyond
  `remaining` proves that the result bound truncated the sweep."
  [kb context remaining]
  (with-open [r (progress/start ::specified "integrity: audit the specified declarations" nil)]
    (loop [audits (predall/specified-declaration-audits kb context)
           findings {}]
      (if-let [[declaration result] (first audits)]
        (do
          (progress/tick! r)
          (if (or (= :gap (:status result)) (seq (:violations result)))
            (if (and remaining (>= (count findings) remaining))
              {:status :truncated :reason :max-results :findings findings}
              (do
                (budget/record! :all-specified-violations [declaration result])
                (recur (rest audits) (assoc findings declaration result))))
            (recur (rest audits) findings)))
        {:status :complete :findings findings}))))

;; ---- genl-arg-widening: a predicate genl edge that widens an argument type ----

(defn- constraining-arg-types
  "`[position type declaring-predicate]` for every `arg` declaration binding `pred`'s
  tuples from `context`: `pred`'s own and every visible super-predicate's, the
  one-position instance entries of `res/arg-constraints`.  A tail entry (`argAndRest`,
  `args`) names no one position for an edge to be compared at, so it is not read here."
  [kb pred context]
  (for [{:keys [from to type kind via]} (res/arg-constraints kb pred context)
        :when (do (budget/spend!) (and (= :instance kind) (= from to)))]
    [from type via]))

(defn- own-arg-types
  "`{position #{type …}}` from the `arg` declarations `context` sees written on `pred`
  itself — the domain its author declared, before any super-predicate's declaration is
  read into it."
  [kb pred context]
  (reduce (fn [m [n t via]] (if (= via pred) (update m n (fnil conj #{}) t) m))
          {}
          (constraining-arg-types kb pred context)))

(defn- declared-predicates
  "The predicates carrying a visible `arg` declaration of their own, in print order: the
  one open read of this pass, a census of declarations rather than of any extent."
  [kb context]
  (->> (res/matches-visible kb '(arg ?p ?n ?t) context)
       (keep (fn [[_ b]]
               (budget/spend!)
               (let [p (get b '?p)]
                 (when (and (symbol? p) (not (sx/variable? p))) p))))
       distinct
       (sort-by nm/print-key)))

(defn- edge-widenings
  "The findings for one visible edge `(genl spec super)`: each position where a type
  `spec` declares is subsumed by none of the types `super`'s constraint demands there.
  A `spec` position carrying several declared types is their intersection, so it is
  compatible with a demanded type as soon as one of them is subsumed by it."
  [kb tx spec own super context]
  (for [[n tq declared-on] (sort-by (fn [[n t p]] [n (nm/print-key t) (nm/print-key p)])
                                    (distinct (constraining-arg-types kb super context)))
        :let  [tps (get own n)]
        :when (seq tps)
        :when (do (budget/spend!)
                  (not-any? #(or (= % tq) (tax/genl? tx % tq context)) tps))
        tp    (sort-by nm/print-key tps)]
    (cond-> {:spec spec :genl super :arg n :spec-type tp :genl-type tq}
      (not= declared-on super) (assoc :genl-type-declared-on declared-on))))

(defn- widening-findings
  "Audit every visible predicate `genl` edge out of a predicate that declares its own
  argument types, one edge at a time, stopping after the first finding beyond
  `remaining` proves that the result bound truncated the sweep."
  [kb context remaining]
  (let [tx    (reasoning/taxonomy kb)
        preds (declared-predicates kb context)]
    (with-open [r (progress/start ::genl-arg-widening "integrity: audit the predicate genl edges"
                                  (count preds))]
      (loop [findings []
             units    (for [spec  (progress/each r preds)
                            :let  [own (own-arg-types kb spec context)]
                            super (sort-by nm/print-key (tax/direct-genls tx spec context))
                            :when (not= super spec)
                            finding (do (budget/spend!)
                                        (edge-widenings kb tx spec own super context))]
                        finding)]
        (if-let [finding (first units)]
          (if (and remaining (>= (count findings) remaining))
            {:status :truncated :reason :max-results :findings findings}
            (do
              (budget/record! :genl-arg-widening finding)
              (recur (conj findings finding) (rest units))))
          {:status :complete :findings findings})))))

;; ---- not-under-thing: a candidate type with no genl path to thing ----

(defn- unrooted-type?
  "Is `term` a type `context` sees declared `unary_predicate` that reaches `thing` by no
  `genl` path visible from `context`?  `thing` itself is the root, never unrooted."
  [kb tx term context]
  (and (not= 'thing term)
       (do (budget/spend!)
           (seq (res/matches-visible kb (list 'unary_predicate term) context)))
       (do (budget/spend!)
           (not (tax/genl? tx term 'thing context)))))

(defn- not-under-thing-findings
  "Audit each ground symbol of `candidate-terms` in print order, one term at a time,
  stopping after the first finding beyond `remaining` proves that the result bound
  truncated the sweep."
  [kb candidate-terms context remaining]
  (let [tx    (reasoning/taxonomy kb)
        terms (->> candidate-terms
                   (filter #(and (symbol? %) (not (sx/variable? %))))
                   (sort-by nm/print-key))]
    (with-open [r (progress/start ::not-under-thing "integrity: find the types not under thing"
                                  (count terms))]
      (loop [findings []
             units    (for [term  (progress/each r terms)
                            :when (unrooted-type? kb tx term context)]
                        {:term term})]
        (if-let [finding (first units)]
          (if (and remaining (>= (count findings) remaining))
            {:status :truncated :reason :max-results :findings findings}
            (do
              (budget/record! :not-under-thing finding)
              (recur (conj findings finding) (rest units))))
          {:status :complete :findings findings})))))

;; ---- implicit-genl: a genl edge a cover forces but the closure does not hold ----

(defn- stated-grounds
  "The believed sentences stating the flat-cache entries `ks` that `context` sees, in
  content order: what a reader is shown as the declarations a finding rests on."
  [kb tx ks context]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (->> ks
         (into #{} (mapcat #(tax/visible-supporters tx % context)))
         (into #{} (comp (filter #(jtms/in? tms %))
                         (keep #(p/get-sentex recs %))
                         (map sx/sentence-of)))
         (sort nm/compare-form)
         vec)))

(defn- visible-covers
  "The covering declarations `context` sees over `term`'s visible supertypes and over
  `thing`, as distinct `[whole parts]`: `thing` is read beside the closure because every
  type is a specialization of it, so a type the closure has not yet placed under `thing`
  is still covered by what covers `thing`."
  [tx term context]
  (->> (concat (tax/covers-over tx term context) (tax/covers-over tx 'thing context))
       distinct
       (sort-by (fn [[whole parts]] [(nm/print-key whole) (mapv nm/print-key parts)]))))

(defn- cover-sentences
  "The believed sentences declaring the cover `[whole parts]` that `context` sees."
  [kb tx whole parts context]
  (stated-grounds kb tx
                  (for [[ps kind] (tax/covers-of tx whole) :when (= ps parts)]
                    [:cover [whole parts] kind])
                  context))

(defn- suggestible-type?
  "Is `term` a type as `context` reads it: not a `kb/relation?`, and either the subtype
  of some visible `genl` edge or declared with arity one.  An individual, and a relation
  whose `genl` edges are predicate specializations, are never suggested a type edge."
  [kb tx term context]
  (and (not (do (budget/spend!) (kb/relation? kb term context)))
       (or (do (budget/spend!) (seq (tax/direct-genls tx term context)))
           (= 1 (do (budget/spend!) (kb/relation-arity kb term))))))

(defn- cover-suggestion
  "The suggestion one visible cover `[whole parts]` forces on `term`, or nil: when the
  disjointness test separates `term` from every part but one, every instance of `term`
  is an instance of the remaining part, so `(genl term part)` holds; it is a finding
  only when the `genl` closure does not already hold it.  A term separated from every
  part is empty and forced under none; one left two parts or more is forced under none."
  [kb tx term [whole parts] context]
  (when-not (or (= term whole) (some #{term} parts))
    (let [excluded (filterv (fn [part]
                              (budget/spend!)
                              (tax/disjoint? tx term part context))
                            parts)
          left     (remove (set excluded) parts)]
      (when (= 1 (count left))
        (let [part (first left)]
          (budget/spend!)
          (when-not (tax/genl? tx term part context)
            {:term term
             :genl part
             :cover (cover-sentences kb tx whole parts context)
             :disjoint-from (mapv (fn [x]
                                    {:part x
                                     :grounds (stated-grounds
                                               kb tx (tax/separating-keys tx term x context)
                                               context)})
                                  (sort-by nm/print-key excluded))}))))))

(defn- implicit-genl-findings
  "Audit each ground candidate that `suggestible-type?` accepts as a type in `context`,
  in print order, against each visible cover over it, one cover at a time, stopping after
  the first finding beyond `remaining` proves that the result bound truncated the sweep."
  [kb candidate-terms context remaining]
  (let [tx    (reasoning/taxonomy kb)
        terms (->> candidate-terms
                   (filter #(and (symbol? %) (not (sx/variable? %))))
                   (sort-by nm/print-key))]
    (with-open [r (progress/start ::implicit-genl "integrity: find the implicit genl edges"
                                  (count terms))]
      (loop [findings []
             units    (for [term  (progress/each r terms)
                            :when (suggestible-type? kb tx term context)
                            cover (visible-covers tx term context)
                            :let  [finding (do (budget/spend!)
                                               (cover-suggestion kb tx term cover context))]
                            :when finding]
                        finding)]
        (if-let [finding (first units)]
          (if (and remaining (>= (count findings) remaining))
            {:status :truncated :reason :max-results :findings findings}
            (do
              (budget/record! :implicit-genl finding)
              (recur (conj findings finding) (rest units))))
          {:status :complete :findings findings})))))

;; ---- implicit-arity-class: an exact-arity class a kind and an arity force ----

(def ^:private arity-class-mappings
  "Each kind the pass reads, with the mapping predicate whose facts name its exact-arity
  classes: the two generators whose generated rules core.txt writes inert."
  [['predicate 'predicateTypeByArity]
   ['function 'functionTypeByArity]])

(defn- arity-class-table
  "`[[kind mapping {arity #{class …}}] …]` from the mapping facts `context` sees, in
  `arity-class-mappings` order: the one census this pass reads."
  [kb context]
  (vec (for [[kind mapping] arity-class-mappings]
         [kind mapping
          (reduce (fn [m [_ b]]
                    (budget/spend!)
                    (let [t (get b '?t) n (get b '?n)]
                      (if (and (symbol? t) (not (sx/variable? t)) (integer? n))
                        (update m n (fnil conj #{}) t)
                        m)))
                  {}
                  (res/matches-visible kb (list mapping '?t '?n) context))])))

(defn- arity-class-units
  "The findings for `term`: for each kind in `table` that `term` is an instance of, the
  class its mapping names for `term`'s exact length that `term` is not an instance of.
  The length is `arity/relation-length`'s, read the same at every context; the kind and
  the class are the memberships `context` sees, through the `genl` closure."
  [kb table term context]
  (when-let [n (do (budget/spend!) (:exact (arity/relation-length kb term)))]
    (for [[kind mapping classes] table
          :let  [cs (get classes n)]
          :when (seq cs)
          :when (do (budget/spend!) (kb/isa? kb term kind context))
          class (sort-by nm/print-key cs)
          :when (not (do (budget/spend!) (kb/isa? kb term class context)))]
      {:term term :kind kind :arity n :class class
       :mapping (list mapping class n)})))

(defn- implicit-arity-class-findings
  "Audit each ground symbol candidate, in print order, against the visible
  `predicateTypeByArity` and `functionTypeByArity` facts, one term at a time, stopping
  after the first finding beyond `remaining` proves that the result bound truncated the
  sweep."
  [kb candidate-terms context remaining]
  (let [table (arity-class-table kb context)]
    (loop [findings []
           units    (for [term    (->> candidate-terms
                                       (filter #(and (symbol? %) (not (sx/variable? %))))
                                       (sort-by nm/print-key))
                          finding (arity-class-units kb table term context)]
                      finding)]
      (if-let [finding (first units)]
        (if (and remaining (>= (count findings) remaining))
          {:status :truncated :reason :max-results :findings findings}
          (do
            (budget/record! :implicit-arity-class finding)
            (recur (conj findings finding) (rest units))))
        {:status :complete :findings findings}))))

;; ---- orthogonal-over-separation: an orthogonal over a stated separation ----

(defn- stated-records
  "The believed sentexes stating the flat-cache entries `ks` that `context` sees, as
  `{:handle :sentence :context}` maps in content order — the shape `conflicts` names a
  clash's grounds in, so a reader can drop one by its handle."
  [kb tx ks context]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (->> ks
         (into #{} (mapcat #(tax/visible-supporters tx % context)))
         (into [] (comp (filter #(jtms/in? tms %))
                        (keep #(p/get-sentex recs %))
                        (map (fn [s] {:handle (:id s) :sentence (sx/sentence-of s)
                                      :context (:context s)}))))
         (sort-by (juxt :sentence :context) nm/compare-form)
         vec)))

(defn- visible-orthogonals
  "Every believed `(f a b)` over two ground symbols that `context` sees, `f` being
  `orthogonal` or a predicate the `genl` edges `context` sees place under it
  (`siblingDisjointException`), as `[a b record]` in content order: the one open read of
  this pass, a census of declarations, which are few, rather than of any extent."
  [kb context]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (->> (tax/specs (reasoning/taxonomy kb) 'orthogonal context)
         (sort-by nm/name-key)
         (mapcat #(res/matches-visible kb (list % '?a '?b) context))
         (keep (fn [[h b]]
                 (budget/spend!)
                 (let [a (get b '?a) c (get b '?b)]
                   (when (and (symbol? a) (not (sx/variable? a))
                              (symbol? c) (not (sx/variable? c))
                              (jtms/in? tms h))
                     (when-let [s (p/get-sentex recs h)]
                       [a c {:handle h :sentence (sx/sentence-of s) :context (:context s)}])))))
         (into [] (distinct))
         (sort-by (fn [[_ _ r]] [(:sentence r) (:context r)]) nm/compare-form))))

(defn- orthogonal-separation
  "The finding for one visible orthogonal declaration over `a` and `b`, or nil: the stated
  separations `context` sees over the pair with no exception exempting any of them — an
  explicit `disjoint`, a `partition` or `separating` declaration, a `sibling_disjoint` parent or
  a `disjoint_metatype` — over `a` and `b` or over a supertype of each.  A
  `siblingDisjointException` lifts the marks among these, so `disjoint?` reads the pair
  apart and cannot show them."
  [kb tx [a b orthogonal] context]
  (budget/spend!)
  (let [ks (tax/separating-keys tx a b context (constantly false))]
    (when (seq ks)
      (let [separated-by (stated-records kb tx ks context)]
        (when (seq separated-by)
          {:orthogonal orthogonal :separated-by separated-by})))))

(defn- orthogonal-over-separation-findings
  "Audit every visible `orthogonal` declaration, one at a time, stopping after the first
  finding beyond `remaining` proves that the result bound truncated the sweep."
  [kb context remaining]
  (let [tx    (reasoning/taxonomy kb)
        decls (visible-orthogonals kb context)]
    (with-open [r (progress/start ::orthogonal-over-separation
                                  "integrity: check the orthogonal declarations" (count decls))]
      (loop [findings []
             units    (keep #(orthogonal-separation kb tx % context) (progress/each r decls))]
        (if-let [finding (first units)]
          (if (and remaining (>= (count findings) remaining))
            {:status :truncated :reason :max-results :findings findings}
            (do
              (budget/record! :orthogonal-over-separation finding)
              (recur (conj findings finding) (rest units))))
          {:status :complete :findings findings})))))

;; ---- shared by the three ontology-engineering passes below ----

(defn- bounded-findings
  "Record each finding of the lazy `units` under `category`, one at a time, stopping
  after the first finding beyond `remaining` proves that the result bound truncated
  the sweep."
  [category units remaining]
  (loop [findings []
         units    units]
    (if-let [finding (first units)]
      (if (and remaining (>= (count findings) remaining))
        {:status :truncated :reason :max-results :findings findings}
        (do
          (budget/record! category finding)
          (recur (conj findings finding) (rest units))))
      {:status :complete :findings findings})))

(defn- handle-records
  "The believed sentexes among `handles`, as `{:handle :sentence :context}` maps in
  content order — the shape `stated-records` names a declaration in."
  [kb handles]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (->> handles
         (into [] (comp (filter #(jtms/in? tms %))
                        (keep #(p/get-sentex recs %))
                        (map (fn [s] {:handle (:id s) :sentence (sx/sentence-of s)
                                      :context (:context s)}))))
         (sort-by (juxt :sentence :context) nm/compare-form)
         vec)))

(defn- stated-pairs
  "Every believed **premise** `(functor a b)` over two distinct ground symbols that
  `context` sees, as `[a b record]` in content order: the one open read of a pass over
  stated declarations, a census of declarations rather than of any extent.  A sentence a
  rule derived is no premise and is not read."
  [kb functor context]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (->> (res/matches-visible kb (list functor '?a '?b) context)
         (keep (fn [[h b]]
                 (budget/spend!)
                 (let [a (get b '?a) c (get b '?b)]
                   (when (and (symbol? a) (not (sx/variable? a))
                              (symbol? c) (not (sx/variable? c))
                              (not= a c)
                              (jtms/in? tms h)
                              (jtms/premise? tms h))
                     (when-let [s (p/get-sentex recs h)]
                       [a c {:handle h :sentence (sx/sentence-of s) :context (:context s)}])))))
         (into [] (distinct))
         (sort-by (fn [[_ _ r]] [(:sentence r) (:context r)]) nm/compare-form))))

;; ---- twin-genls: sibling types with one direct genl set, a missing common parent ----

(defn- twin-groups
  "`{genl-set #{type …}}` over every type the taxonomy holds whose direct `genl` set, as
  `context` reads it, names two types or more besides `thing`.  A type is read as
  `suggestible-type?` reads one."
  [kb tx context]
  (let [ts (tax/types tx)]
    (with-open [r (progress/start ::twin-genls "integrity: group the types by direct genls"
                                  (count ts))]
      (reduce (fn [groups t]
                (budget/spend!)
                (progress/tick! r)
                (let [gs (when (symbol? t) (tax/direct-genls tx t context))]
                  (if (and (>= (count (disj (set gs) 'thing)) 2)
                           (suggestible-type? kb tx t context))
                    (update groups (set gs) (fnil conj #{}) t)
                    groups)))
              {}
              ts))))

(defn- twin-genls-findings
  "Group every type by its direct `genl` set, and report each set two types or more
  share, in print order of the set and then of its types."
  [kb context remaining]
  (let [tx (reasoning/taxonomy kb)]
    (bounded-findings
     :twin-genls
     (->> (twin-groups kb tx context)
          (keep (fn [[gs ts]]
                  (when (> (count ts) 1)
                    {:types (vec (sort-by nm/print-key ts))
                     :genls (vec (sort-by nm/print-key gs))})))
          (sort-by (fn [{:keys [types genls]}]
                     [(mapv nm/print-key genls) (mapv nm/print-key types)])))
     remaining)))

;; ---- derivable-stated-edge: a stated genl or disjoint that holds without itself ----

(defn- path-avoiding
  "The shortest visible `genl` path `[a … b]` from `a` to `b` that does not walk the
  edge `a`→`b` itself, or nil."
  [tx a b context]
  (loop [frontier [a] parent {a nil}]
    (when (seq frontier)
      (let [step (for [n frontier
                       g (sort-by nm/print-key (tax/direct-genls tx n context))
                       :when (not (and (= n a) (= g b)))
                       :when (not (contains? parent g))]
                   (do (budget/spend!) [g n]))
            parent' (reduce (fn [m [g n]] (if (contains? m g) m (assoc m g n))) parent step)]
        (if (contains? parent' b)
          (vec (reverse (take-while some? (iterate parent' b))))
          (recur (vec (distinct (map first step))) parent'))))))

(defn- derivable-genl
  "The finding for one stated `(genl a b)`, or nil: another believed supporter of the
  edge (the same sentence stated again, a rule's derivation, a cover declaration installing it), or
  another `genl` path from `a` to `b` that does not walk the edge."
  [kb tx [a b stated] context]
  (budget/spend!)
  (let [others (handle-records kb (disj (tax/genl-edge-supporters tx a b context)
                                        (:handle stated)))]
    (if (seq others)
      {:stated stated :also-stated-by others}
      (when (some (fn [p]
                    (budget/spend!)
                    (and (not= p b) (tax/genl? tx p b context)))
                  (tax/direct-genls tx a context))
        (when-let [path (path-avoiding tx a b context)]
          {:stated stated :path path})))))

(defn- derivable-disjoint
  "The finding for one stated `(disjoint a b)`, or nil: the separations `context` sees
  over the pair, or over a supertype of each, besides this one statement — another
  supporter of the same pair, a separation of two supertypes, a `partition` or
  `separating` declaration, a `sibling_disjoint` parent or a `disjoint_metatype`."
  [kb tx [a b stated] context]
  (budget/spend!)
  (let [k    [:disjoint #{a b}]
        same (handle-records kb (disj (tax/visible-supporters tx k context)
                                      (:handle stated)))
        apart (stated-records kb tx (disj (tax/separating-keys tx a b context) k) context)]
    (when (or (seq same) (seq apart))
      {:stated stated :separated-by (vec (concat same apart))})))

(defn- derivable-stated-edge-findings
  "Audit every visible stated `genl`, then every visible stated `disjoint`, one at a
  time, in content order."
  [kb context remaining]
  (let [tx        (reasoning/taxonomy kb)
        genls     (stated-pairs kb 'genl context)
        disjoints (stated-pairs kb 'disjoint context)]
    (with-open [r (progress/start ::derivable-stated-edge "integrity: find the derivable stated edges"
                                  (+ (count genls) (count disjoints)))]
      (bounded-findings
       :derivable-stated-edge
       (concat (keep #(derivable-genl kb tx % context) (progress/each r genls))
               (keep #(derivable-disjoint kb tx % context) (progress/each r disjoints)))
       remaining))))

;; ---- disjoint-could-be-partition: a disjoint whose pair a known cover exhausts ----

(defn- partition-sentence [whole parts]
  (apply list 'partition whole (sort-by nm/print-key parts)))

(defn- pairwise-disjoint?
  "Does `context` read every two of `parts` apart?"
  [tx parts context]
  (every? (fn [[x y]] (budget/spend!) (tax/disjoint? tx x y context))
          (for [x parts y parts :when (neg? (compare (nm/print-key x) (nm/print-key y)))]
            [x y])))

(defn- partition-candidates
  "The suggestions one stated `(disjoint a b)` gives, in print order of the whole: each
  visible `covering` naming both whose parts `context` reads pairwise apart (basis
  `:covering`), and each common direct parent whose direct specs are exactly the pair
  and that no visible cover already names them under (basis `:sole-specs`)."
  [kb tx [a b stated] context]
  (budget/spend!)
  (let [covers   (tax/covers-naming-visible tx a context)
        named?   (fn [whole kind]
                   (some (fn [[w ps k]] (and (= w whole) (= k kind) (some #{b} ps)))
                         covers))
        covering (for [[whole parts kind] covers
                       :when (and (= :covering kind) (some #{b} parts)
                                  (not= whole a) (not= whole b)
                                  (not (named? whole :partition))
                                  (pairwise-disjoint? tx parts context))]
                   {:disjoint stated :suggest (partition-sentence whole parts)
                    :basis :covering
                    :cover (cover-sentences kb tx whole parts context)})
        covered  (into #{} (map #(second (:suggest %))) covering)
        sole     (for [c (sort-by nm/print-key
                                  (filter (set (tax/direct-genls tx b context))
                                          (tax/direct-genls tx a context)))
                       :when (and (not= c a) (not= c b)
                                  (not (covered c))
                                  (not (named? c :partition))
                                  (do (budget/spend!)
                                      (= #{a b} (disj (set (tax/direct-specs tx c context))
                                                      c))))]
                   {:disjoint stated :suggest (partition-sentence c [a b])
                    :basis :sole-specs})]
    (sort-by #(nm/print-key (second (:suggest %))) (concat covering sole))))

(defn- disjoint-could-be-partition-findings
  "Audit every visible stated `disjoint`, one at a time, in content order."
  [kb context remaining]
  (let [tx        (reasoning/taxonomy kb)
        disjoints (stated-pairs kb 'disjoint context)]
    (with-open [r (progress/start ::disjoint-could-be-partition
                                  "integrity: find the disjoints that could be partitions"
                                  (count disjoints))]
      (bounded-findings
       :disjoint-could-be-partition
       (mapcat #(partition-candidates kb tx % context) (progress/each r disjoints))
       remaining))))

;; ---- missing-arg: a declared argument position no declaration types ----

(defn- typed-positions
  "`{:at #{n …} :from n-or-nil}` for `pred` as `context` reads its declarations, through
  `res/arg-constraints`: the positions a one-position declaration types, and the first
  position a tail declaration types onward.  Every kind counts — an instance, a type-level
  or a quoted constraint all say what fills the position — and `argsGenl` arrives as a
  tail from 1, `args` and the `argN` projections (`sx/arg-projections`) as the
  `argAndRest` and `arg` their forward rules store."
  [kb pred context]
  (let [es (res/arg-constraints kb pred context)]
    (doseq [_ es] (budget/spend!))
    {:at   (into #{} (keep #(when (:to %) (:from %))) es)
     :from (some->> es (remove :to) (map :from) seq (apply min))}))

(defn- arity-census
  "`{pred n-or-:variable}` over every predicate `context` sees declared an arity: an
  `(arity P n)`, an exact-arity class membership, or `variable_arity_predicate`.  A
  predicate told two different arities is skipped, as `kb/relation-arity` reads it."
  [kb context]
  (let [subjects (fn [pattern]
                   (keep (fn [[_ b]]
                           (budget/spend!)
                           (let [p (get b '?p)]
                             (when (and (symbol? p) (not (sx/variable? p))) p)))
                         (res/matches-visible kb pattern context)))
        fixed    (distinct (concat (subjects '(arity ?p ?n))
                                   (mapcat #(subjects (list % '?p))
                                           (keys tax/exact-arity-classes))))]
    (merge (into {} (map (fn [p] [p :variable])) (subjects '(variable_arity_predicate ?p)))
           (into {} (keep (fn [p]
                            (budget/spend!)
                            (when-let [n (kb/relation-arity kb p)] [p n])))
                 fixed))))

(defn- arity-min
  "The least `arityMin` `context` sees declared of `pred`, or 1."
  [kb pred context]
  (or (some->> (res/matches-visible kb (list 'arityMin pred '?n) context)
               (keep (fn [[_ b]] (let [n (get b '?n)] (when (integer? n) n))))
               seq (apply min))
      1))

(defn- untyped-positions
  "Each position 1..n of `pred` (1..`arityMin` for a variable arity, and `:rest` for its
  tail) no declaration `context` sees types, as a vector.  A unary predicate's one
  position is typed by any visible `genl` edge out of it, which says of its members what
  `(arg P 1 T)` would."
  [kb tx pred arity context]
  (let [{:keys [at from]} (typed-positions kb pred context)
        typed?  (fn [n] (or (contains? at n) (and from (>= n from))))
        n       (if (= :variable arity) (arity-min kb pred context) arity)
        missing (cond-> (vec (remove typed? (range 1 (inc n))))
                  (and (= :variable arity) (not (and from (<= from (inc n)))))
                  (conj :rest))
        missing (if (and (= 1 arity) (= [1] missing)
                         (seq (disj (set (tax/direct-genls tx pred context)) pred)))
                  []
                  missing)]
    missing))

(defn- declaring-contexts
  "The contexts other than `context` that see it and store a declaration typing a
  position of `pred`: an `arg`-family declaration on `pred` (`res/arg-constraint-kinds`),
  or a supporter of a `genl` edge out of it, which types a unary predicate's position and
  imports a super-predicate's declarations.  An edge's supporters are the engine's own
  (`tax/genl-edge-supporters`): a stated `(genl pred super)`, and each `covering`,
  `separating` or `partition` declaration naming `pred` as a part
  (`tax/installed-edges`), so a part whose one edge is such a declaration's is declared
  where that declaration is stated.  In name order.

  The edges out of `pred` are read globally (`tax/direct-genls-global`) because the
  contexts this looks for sit below `context` and state what `context` does not see; the
  supporters' contexts are then narrowed to the ones that see `context`."
  [kb pred context]
  (let [tx     (reasoning/taxonomy kb)
        down   (set (tax/context-down tx context))
        stated (for [[k [_ shape]] res/arg-constraint-kinds]
                 (if (= :every shape) (list k pred '?t) (list k pred '?n '?t)))
        edges  (mapcat (fn [super] (budget/spend!) (tax/genl-edge-supporters tx pred super nil))
                       (disj (set (tax/direct-genls-global tx pred)) pred))]
    (->> (concat (keep (fn [[_ _ s]] (budget/spend!) (:context s))
                       (mapcat #(res/matches-visible kb % '?ctx) stated))
                 (map :context (handle-records kb edges)))
         (filter #(and (not= context %) (contains? down %)))
         distinct
         (sort-by nm/print-key))))

(defn- missing-positions
  "The finding for one predicate of declared arity `arity`, or nil: each position
  `untyped-positions` reports from `context` that some context declaring the predicate
  (`declaring-contexts`) also leaves untyped.  A relation declared in a context below the
  audit context has its arity class placed in CxUniverse (`chain/place-arity-class!`,
  the starter's unary batch) while its declarations stay where they are written, so the
  audit reads them from there; a position typed in every such context is not missing.
  With no such context, what `context` sees is the whole answer."
  [kb tx pred arity context]
  (budget/spend!)
  (let [missing (untyped-positions kb tx pred arity context)
        missing (if-let [ds (seq (when (seq missing) (declaring-contexts kb pred context)))]
                  (let [below (into #{} (mapcat #(untyped-positions kb tx pred arity %)) ds)]
                    (filterv below missing))
                  missing)]
    (when (seq missing)
      {:predicate pred :arity arity :missing missing})))

(defn- missing-arg-findings
  "Audit every predicate `context` sees declared an arity, one at a time, in print order."
  [kb context remaining]
  (let [tx    (reasoning/taxonomy kb)
        preds (sort-by (comp nm/print-key key) (arity-census kb context))]
    (with-open [r (progress/start ::missing-arg "integrity: find the untyped argument positions"
                                  (count preds))]
      (bounded-findings
       :missing-arg
       (keep (fn [[pred arity]] (missing-positions kb tx pred arity context))
             (progress/each r preds))
       remaining))))

;; ---- rule-macro: a stored rule a declaration the engine implements states ----

(defn- positions-vars
  "`n` distinct shape variables `?o1 … ?on`, the arguments a shape leaves free."
  [n]
  (mapv #(symbol (str "?o" %)) (range 1 (inc n))))

(defn- swapped
  "`xs` with the elements at the 0-based indexes `i` and `j` exchanged."
  [xs i j]
  (assoc xs i (nth xs j) j (nth xs i)))

(defn- macro-shapes
  "The macro shapes a rule whose consequent has `n` arguments can match, each
  `{:macro m :antecedent [...] :consequent c :meta #{...} :declaration f}`.  A symbol in
  `:meta` stands for a ground term of the rule (a predicate, a relation, a fixed filler);
  every other shape variable stands for a variable of the rule, one for one.
  `:declaration` builds the suggested declaration from the bindings of the meta symbols.
  `:defeasible` is the rule class the macro's conclusions carry."
  [n]
  (let [os (positions-vars n)]
    (concat
     (for [i      (range n)
           [m inv?] [['transitiveInArg false] ['transitiveInArgInverse true]]]
       ;; transitiveInArg carries (P … W …) along R's arrow, (R W A); the inverse against it
       {:macro       m
        :antecedent  [(list* '?mP (assoc os i '?w))
                      (if inv? (list '?mR (nth os i) '?w) (list '?mR '?w (nth os i)))]
        :consequent  (list* '?mP os)
        :meta        '#{?mP ?mR}
        :defeasible  false
        :declaration (fn [b] (list m (b '?mP) (inc i) (b '?mR)))})
     (when (= 2 n)
       [{:macro       'symmetric
         :antecedent  [(list* '?mP os)]
         :consequent  (list* '?mP (swapped os 0 1))
         :meta        '#{?mP}
         :defeasible  false
         :declaration (fn [b] (list 'symmetric (b '?mP)))}
        {:macro       'transitive
         :antecedent  ['(?mP ?o1 ?w) '(?mP ?w ?o2)]
         :consequent  '(?mP ?o1 ?o2)
         :meta        '#{?mP}
         :defeasible  false
         :declaration (fn [b] (list 'transitive (b '?mP)))}
        {:macro       'inverse
         :antecedent  [(list* '?mP os)]
         :consequent  (list* '?mQ (swapped os 0 1))
         :meta        '#{?mP ?mQ}
         :defeasible  false
         :declaration (fn [b] (list 'inverse (b '?mP) (b '?mQ)))}
        {:macro       'predAllInstance
         :antecedent  ['(?mC ?o1)]
         :consequent  '(?mP ?o1 ?mK)
         :meta        '#{?mP ?mC ?mK}
         :defeasible  true
         :declaration (fn [b] (list 'predAllInstance (b '?mP) (b '?mC) (b '?mK)))}
        {:macro       'predInstanceAll
         :antecedent  ['(?mC ?o1)]
         :consequent  '(?mP ?mK ?o1)
         :meta        '#{?mP ?mC ?mK}
         :defeasible  true
         :declaration (fn [b] (list 'predInstanceAll (b '?mP) (b '?mK) (b '?mC)))}])
     (when (<= 3 n)
       (for [i (range n) j (range (inc i) n)]
         {:macro       'commutativeInArgs
          :antecedent  [(list* '?mP os)]
          :consequent  (list* '?mP (swapped os i j))
          :meta        '#{?mP}
          :defeasible  false
          :declaration (fn [b] (list 'commutativeInArgs (b '?mP) (inc i) (inc j)))}))
     [{:macro       'genl
       :antecedent  [(list* '?mP os)]
       :consequent  (list* '?mQ os)
       :meta        '#{?mP ?mQ}
       :defeasible  false
       :declaration (fn [b] (list 'genl (b '?mP) (b '?mQ)))}])))

(defn- freezing
  "The rule's variables, each mapped to a namespaced symbol no sentence can spell.  The
  match below is one-way, the shape's variables bound and the rule's held fixed, and
  freezing the rule's variables into constants makes the two-way `res/unify` run that
  way."
  [forms]
  (into {}
        (map-indexed (fn [i v] [v (symbol "vaelii.impl.integrity" (str "frozen" i))]))
        (sort (reduce into #{} (map sx/form-variables forms)))))

(defn- frozen? [x] (and (symbol? x) (= "vaelii.impl.integrity" (namespace x))))

(defn- freeze
  "`form` with every variable `m` names replaced by its frozen symbol."
  [form m]
  (cond
    (contains? m form) (get m form)
    (sequential? form) (apply list (map #(freeze % m) form))
    :else              form))

(defn- antecedents-matched
  "A binding extending `b` under which each of `shape-antes` unifies with a distinct
  literal of `antes`, or nil.  Backtracking, since which literal one shape antecedent
  takes decides what the next can take."
  [shape-antes antes b]
  (if (empty? shape-antes)
    b
    (some (fn [i]
            (when-let [b' (res/unify (first shape-antes) (nth antes i) b)]
              (antecedents-matched (rest shape-antes)
                                   (vec (concat (subvec antes 0 i) (subvec antes (inc i))))
                                   b')))
          (range (count antes)))))

(defn- shape-bindings
  "The bindings of `shape`'s meta symbols when the frozen rule `antes` ⇒ `conseq` is the
  shape with its variables renamed, or nil.  Each other shape variable must take a
  frozen rule variable, and no two of them the same one, so a rule that repeats a
  variable or fixes a constant where the shape has a free argument is not the shape.
  Each meta symbol must take a ground term that is not a frozen rule variable."
  [shape antes conseq]
  (when (= (count antes) (count (:antecedent shape)))
    (when-let [b (some->> (res/unify (:consequent shape) conseq {})
                          (antecedents-matched (:antecedent shape) antes))]
      (let [vars    (reduce into #{} (map sx/form-variables
                                          (cons (:consequent shape) (:antecedent shape))))
            objects (remove (:meta shape) vars)
            value   #(res/substitute % b)
            taken   (map value objects)]
        (when (and (every? frozen? taken)
                   (apply distinct? taken)
                   (every? #(let [x (value %)]
                              (and (sx/ground-term? x) (not (frozen? x))))
                           (:meta shape)))
          (into {} (map (juxt identity value)) (:meta shape)))))))

(defn- arity-is?
  "Does `pred`, read from `context`, take exactly `n` arguments: declared with arity `n`,
  or, with `unknown-ok?`, declared with no arity and no variable arity?"
  [kb pred n context unknown-ok?]
  (budget/spend!)
  (let [declared (kb/relation-arity kb pred)]
    (if declared
      (= n declared)
      (and unknown-ok?
           (do (budget/spend!) (not (kb/isa? kb pred 'variable_arity context)))))))

(defn- universal?
  "Is a rule stored in `rule-ctx` read wherever a relation mark is: is it visible from
  `special/universal-context`, the context a mark is lifted into?"
  [kb rule-ctx]
  (tax/sees? (reasoning/taxonomy kb) special/universal-context rule-ctx))

(defn- converse-rule
  "A believed premise rule visible from `context`, other than `handle`, of the class
  `defeasible` names, stating `(Q ?y ?x)` ⇒ `(P ?x ?y)` with no other condition, or nil:
  the other half of an `inverse`.  Read off the consequent index under `p`."
  [kb rule-ok? handle p q defeasible]
  (some (fn [h]
          (budget/spend!)
          (when-let [rsx (and (not= h handle) (p/get-sentex (:records kb) h))]
            (when (and (rule-ok? h rsx) (= defeasible (boolean (:defeasible rsx))))
              (let [m      (freezing (cons (:consequent rsx) (:antecedent rsx)))
                    shape  {:antecedent [(list q '?o1 '?o2)] :consequent (list p '?o2 '?o1)
                            :meta #{}}]
                (when (shape-bindings shape (mapv #(freeze % m) (:antecedent rsx))
                                      (freeze (:consequent rsx) m))
                  {:rule h :sentence (sx/authored-sentence rsx) :context (:context rsx)})))))
        (sort (reads/as-stored-rules-by-consequent-global (:index kb) p))))

(defn- macro-holds?
  "The conditions beside the shape under which the macro `m` bound by `b` says exactly
  what the rule `rsx` says, read from the rule's context.  A relation mark is read from
  every context, so the rule must be visible from the context marks are lifted into;
  `genl` and the two preservation declarations are read where they are stated."
  [kb rsx {m :macro} b n]
  (let [ctx (:context rsx)
        tx  (reasoning/taxonomy kb)
        P   (b '?mP)]
    (and (symbol? P)
         (case m
           (transitiveInArg transitiveInArgInverse)
           (let [R (b '?mR)]
             (and (symbol? R) (not= R P)
                  (do (budget/spend!) (inherit/usable-relation? tx R ctx))))

           (symmetric transitive)
           (and (universal? kb ctx) (arity-is? kb P 2 ctx false))

           commutativeInArgs
           (and (universal? kb ctx) (arity-is? kb P n ctx false))

           inverse
           (let [Q (b '?mQ)]
             (and (symbol? Q) (not= P Q) (universal? kb ctx)
                  (arity-is? kb P 2 ctx false) (arity-is? kb Q 2 ctx false)))

           (predAllInstance predInstanceAll)
           (and (symbol? (b '?mC)) (arity-is? kb P 2 ctx true))

           genl
           (let [Q (b '?mQ)]
             (and (symbol? Q) (not= P Q)
                  (nil? (predicates/entry Q))
                  (arity-is? kb P n ctx true) (arity-is? kb Q n ctx true)))))))

(defn- macro-candidate?
  "May the stored rule `rsx` at handle `h` be read as a macro's spelling: a believed
  premise, visible from `context`, run by a chainer to derive its head, with no
  `exceptWhen`, `unknown`, aggregate or other re-checked condition?  A rule a generator
  generated is a conclusion, not a premise, and is skipped."
  [kb context h rsx]
  (let [tms (reasoning/tms kb)]
    (and (rules/rule? rsx)
         (= :derive (:effect rsx))
         (rules/chains? rsx)
         (not (rules/rechecked? rsx))
         (not (reads/watched-rule? (:index kb) h))
         (jtms/premise? tms h)
         (jtms/in? tms h)
         (res/rule-visible-from? kb context (:context rsx)))))

(defn- contrary-rule?
  "Is the stored rule at `h` a believed rule concluding `(not (g …))` for a `g` of
  `preds`, in a context that sees `ctx` or that `ctx` sees?"
  [kb preds ctx h]
  (budget/spend!)
  (when-let [rsx (p/get-sentex (:records kb) h)]
    (let [c  (:consequent rsx)
          tx (reasoning/taxonomy kb)]
      (and (rules/rule? rsx)
           (sx/negation? c)
           (contains? preds (nm/functor (second c)))
           (res/rule-believed? kb h)
           (or (tax/sees? tx (:context rsx) ctx) (tax/sees? tx ctx (:context rsx)))))))

(defn- known-exception?
  "Does the KB hold a claim that overrides the default rule `rsx`: a believed `(not (g …))`
  in a context that sees the rule's, or a rule concluding one, for `g` the rule's
  consequent predicate or a `genl` of it read from the rule's context?  A default with an
  `exceptWhen` is not read at all (`macro-candidate?`)."
  [kb rsx]
  (let [ctx   (:context rsx)
        tx    (reasoning/taxonomy kb)
        c     (:consequent rsx)
        vars  (positions-vars (nm/arity c))
        preds (do (budget/spend!) (set (tax/genls tx (nm/functor c) ctx)))]
    (or (some (fn [g]
                (budget/spend!)
                (some (fn [[_ _ sx']]
                        (tax/sees? tx (:context sx') ctx))
                      (res/matches-visible kb (list 'not (list* g vars)) '?ctx)))
              (sort-by nm/print-key preds))
        (some #(contrary-rule? kb preds ctx %)
              (sort (reads/as-stored-rules-by-consequent-global (:index kb) sx/not-functor))))))

(def ^:private declined-marker
  "The predicate a reviewer states of a suggested declaration to record that the rule
  it was suggested for stays as written."
  'declined_rule_macro)

(defn- declined?
  "Does the rule's context see `(declined_rule_macro decl)`?"
  [kb rsx decl]
  (budget/spend!)
  (seq (res/matches-visible kb (list declined-marker decl) (:context rsx))))

(defn- rule-macro-units
  "The findings for one rule `rsx` at handle `h`: one per macro shape the rule is, with
  the conditions `macro-holds?` reads.  A shape matches a rule of its own class; a
  `set/defaultRule` matching a monotonic shape is a `:default-shaped` finding unless
  `known-exception?` holds.  A suggestion the rule's context declines is not a finding."
  [kb context h rsx]
  (let [m      (freezing (cons (:consequent rsx) (:antecedent rsx)))
        antes  (mapv #(freeze % m) (:antecedent rsx))
        conseq (freeze (:consequent rsx) m)
        n      (nm/arity conseq)
        dflt?  (boolean (:defeasible rsx))
        ok?    #(macro-candidate? kb context %1 %2)
        excused (delay (known-exception? kb rsx))]
    (when (and (seq? conseq) (integer? n) (not (sx/negation? conseq)))
      (for [shape (macro-shapes n)
            :let  [shaped? (and dflt? (not (:defeasible shape)))]
            :when (or (= dflt? (:defeasible shape)) shaped?)
            :let  [b (do (budget/spend!) (shape-bindings shape antes conseq))]
            :when (and b (macro-holds? kb rsx shape b n))
            :let  [partner (when (= 'inverse (:macro shape))
                             (converse-rule kb ok? h (b '?mP) (b '?mQ) dflt?))]
            :when (or partner (not= 'inverse (:macro shape)))
            :let  [decl ((:declaration shape) b)]
            :when (not (declined? kb rsx decl))
            :when (not (and shaped? @excused))]
        (cond-> {:rule h
                 :sentence (sx/authored-sentence rsx)
                 :context (:context rsx)
                 :macro (:macro shape)
                 :declaration decl}
          shaped? (assoc :default-shaped true)
          partner (assoc :converse partner)
          (do (budget/spend!) (seq (res/matches-visible kb decl (:context rsx))))
          (assoc :stated true))))))

(defn- rule-macro-findings
  "Audit every stored rule `macro-candidate?` accepts from `context`, in print order of
  its sentence, one rule at a time, stopping after the first finding beyond `remaining`
  proves that the result bound truncated the sweep.  The rules are read off the rule
  extent (`reads/as-stored-rules-in`), the census `chain/rule-firing-report` takes."
  [kb context remaining]
  (let [idx  (:index kb)
        recs (:records kb)
        hs   (into (sorted-set) (reads/as-stored-rules-in-global idx :rule))
        rows (with-open [r (progress/start ::rule-macro-candidates
                                           "integrity: select the macro candidate rules" (count hs))]
               (->> hs
                    (keep (fn [h]
                            (budget/spend!)
                            (progress/tick! r)
                            (when-let [rsx (p/get-sentex recs h)]
                              (when (macro-candidate? kb context h rsx)
                                [h rsx]))))
                    (sort-by (fn [[h rsx]]
                               [(nm/print-key (sx/authored-sentence rsx))
                                (nm/print-key (:context rsx)) h]))))]
    (with-open [r (progress/start ::rule-macro "integrity: match the rules against the macro shapes"
                                  (count rows))]
      (loop [findings []
             units    (for [[h rsx] (progress/each r rows)
                            finding (rule-macro-units kb context h rsx)]
                        finding)]
        (if-let [finding (first units)]
          (if (and remaining (>= (count findings) remaining))
            {:status :truncated :reason :max-results :findings findings}
            (do
              (budget/record! :rule-macro finding)
              (recur (conj findings finding) (rest units))))
          {:status :complete :findings findings})))))

;; ---- undeclared-arity: a genl node no length binds ----

(defn- genl-nodes
  "The ground symbols at either end of a `genl` edge `context` sees, in print order: the
  one open read of this pass, a census of the edges rather than of any extent."
  [kb context]
  (->> (res/matches-visible kb '(genl ?a ?b) context)
       (mapcat (fn [[_ b]]
                 (budget/spend!)
                 [(get b '?a) (get b '?b)]))
       (filter #(and (symbol? %) (not (sx/variable? %))))
       distinct
       (sort-by nm/print-key)))

(defn- undeclared-arity?
  "Is `term` bound to no exact length, its own or one it inherits through `genl`
  (`arity/relation-length`), and released by no `variable_arity` binding
  (`arity/released?`), each read the same at every context?"
  [kb term]
  (budget/spend!)
  (not (or (arity/released? kb term) (:exact (arity/relation-length kb term)))))

(defn- undeclared-arity-findings
  "Audit each `genl` node `context` sees, in print order, one term at a time, stopping
  after the first finding beyond `remaining` proves that the result bound truncated the
  sweep."
  [kb context remaining]
  (let [nodes (genl-nodes kb context)]
    (with-open [r (progress/start ::undeclared-arity "integrity: find the genl nodes with no arity"
                                  (count nodes))]
      (loop [findings []
             units    (for [term  (progress/each r nodes)
                            :when (undeclared-arity? kb term)]
                        {:term term})]
        (if-let [finding (first units)]
          (if (and remaining (>= (count findings) remaining))
            {:status :truncated :reason :max-results :findings findings}
            (do
              (budget/record! :undeclared-arity finding)
              (recur (conj findings finding) (rest units))))
          {:status :complete :findings findings})))))

(defn- uncorresponded-units
  "`{:function f :rules [handle …]}` for each `reifiable_function` an open application in
  a held rule `context` sees names while the KB believes no correspondence of it
  (`nat/held-application?`, docs/nat.md, The corresponding predicate), in print order of
  the function, the rules in handle order.  The mark is
  read unscoped because the hold reads it so; `context` narrows the rules."
  [kb context]
  (let [tax    (reasoning/taxonomy kb)
        r?     #(tax/has-prop? tax :reifiable %)
        corrs  (memoize (fn [f] (count (res/believed-correspondences kb #(= f (first %))))))
        by-f   (reduce (fn [m sx]
                         (budget/spend!)
                         (if (tax/sees? tax context (:context sx))
                           (reduce #(update %1 %2 (fnil conj (sorted-set)) (:id sx))
                                   m
                                   (into #{} (comp (mapcat #(res/open-applications r? %))
                                                   (map first)
                                                   (filter #(zero? (corrs %))))
                                         (conj (vec (:antecedent sx)) (:consequent sx))))
                           m))
                       {} (nat/held-application-rules kb))]
    (for [f (sort-by nm/print-key (keys by-f))]
      {:function f :rules (vec (by-f f))})))

(defn- uncorresponded-function-findings
  "Report each function `uncorresponded-units` names, stopping after the first finding
  beyond `remaining` proves that the result bound truncated the sweep."
  [kb context remaining]
  (loop [findings [] units (uncorresponded-units kb context)]
    (if-let [finding (first units)]
      (if (and remaining (>= (count findings) remaining))
        {:status :truncated :reason :max-results :findings findings}
        (do (budget/record! :uncorresponded-function finding)
            (recur (conj findings finding) (rest units))))
      {:status :complete :findings findings})))

(def ^:private passes
  "The passes in run order, `[category audit]`: `audit` takes `kb candidate-terms context
  remaining` and answers `{:status :complete|:truncated :findings …}`.  `:max-results`
  counts findings in this order."
  [[:definition-inconsistencies provers/definition-inconsistencies]
   [:all-specified-violations (fn [kb _ context remaining]
                                (specified-findings kb context remaining))]
   [:genl-arg-widening (fn [kb _ context remaining]
                         (widening-findings kb context remaining))]
   [:not-under-thing not-under-thing-findings]
   [:implicit-genl implicit-genl-findings]
   [:implicit-arity-class implicit-arity-class-findings]
   [:orthogonal-over-separation (fn [kb _ context remaining]
                                  (orthogonal-over-separation-findings kb context remaining))]
   [:rule-macro (fn [kb _ context remaining]
                  (rule-macro-findings kb context remaining))]
   [:undeclared-arity (fn [kb _ context remaining]
                        (undeclared-arity-findings kb context remaining))]
   [:uncorresponded-function (fn [kb _ context remaining]
                               (uncorresponded-function-findings kb context remaining))]
   [:twin-genls (fn [kb _ context remaining]
                  (twin-genls-findings kb context remaining))]
   [:derivable-stated-edge (fn [kb _ context remaining]
                             (derivable-stated-edge-findings kb context remaining))]
   [:disjoint-could-be-partition (fn [kb _ context remaining]
                                   (disjoint-could-be-partition-findings kb context remaining))]
   [:missing-arg (fn [kb _ context remaining]
                   (missing-arg-findings kb context remaining))]])

(def ^:private review-categories
  "The review-only categories: a sweep runs their passes only when `:categories` names
  them, so a finding of one never turns an otherwise clean default sweep into `:gap`."
  #{:twin-genls :derivable-stated-edge :disjoint-could-be-partition :missing-arg})

(defn- check-args!
  "Refuse a `candidate-terms` that is not a set of ground terms (`:bad-args`), and a
  `:categories` that is not a set of the categories `passes` names (`:unknown-option`)."
  [candidate-terms categories]
  (when-not (set? candidate-terms)
    (throw (ex-info "kb-integrity candidate-terms must be a finite set"
                    {:type :bad-args :op 'kb-integrity :arg :candidate-terms})))
  (when-let [term (first (remove sx/ground-term? candidate-terms))]
    (throw (ex-info "kb-integrity candidate-terms must all be ground"
                    {:type :bad-args :op 'kb-integrity :arg :candidate-terms :term term})))
  (let [known (mapv first passes)]
    (when-not (or (nil? categories) (and (set? categories) (every? (set known) categories)))
      (throw (ex-info (str "kb-integrity :categories must be a set of "
                           (str/join ", " known) ", got " (pr-str categories))
                      {:type :unknown-option :mismatch :bad-value
                       :option :categories :value categories})))))

(defn- run-passes
  "Run the `passes` that `categories` names (every one but the `review-categories` when
  nil) in order, each with what is left of `max-results`: nil when every pass completed,
  `:max-results` when one stopped at the cap."
  [kb candidate-terms context max-results categories]
  (let [selected (filterv #(if (nil? categories)
                             (not (review-categories (first %)))
                             (categories (first %)))
                          passes)]
    (with-open [r (progress/start ::run-passes "integrity: run the passes" (count selected))]
      (loop [[[_ audit] & more] selected
             remaining          max-results]
        (when audit
          (let [result (audit kb candidate-terms context remaining)]
            (progress/tick! r)
            (if (= :truncated (:status result))
              :max-results
              (recur more (some-> remaining (- (count (:findings result))))))))))))

(defn- report-categories
  "The non-empty categories of a meter's findings, the specified category as a map."
  [found]
  (into {}
        (keep (fn [[k xs]]
                (when (seq xs)
                  [k (if (= :all-specified-violations k) (into {} xs) xs)])))
        found))

(defn kb-integrity
  "Run the bounded integrity sweep in `context` over the finite set of ground
  `candidate-terms`.  Answers `{:status :audited :candidate-count n}` when no pass finds
  anything, `:status :gap` with the non-empty categories otherwise, and `:status
  :truncated` with its `:reason`, `:work`, `:elapsed-ms` and the findings kept before a
  bound in `options` (`integrity-opt-keys`) ran out.  `:categories`, a set of category
  keys, runs those passes alone; without it the sweep runs every pass but the
  `review-categories`.  Reads only: a diagnostic raised by
  evaluating a condition goes to a sink local to the call.  See docs/integrity.md."
  ([kb candidate-terms context]
   (kb-integrity kb candidate-terms context nil))
  ([kb candidate-terms context options]
   (budget/check-budget! options integrity-opt-keys "kb-integrity")
   (check-args! candidate-terms (:categories options))
   (let [candidate-count (count candidate-terms)
         m               (budget/meter options)
         reason          (binding [violations/*report-sink* (atom [])]
                           (budget/metered
                            m #(try (run-passes kb candidate-terms context
                                                (:max-results options) (:categories options))
                                    (catch clojure.lang.ExceptionInfo e
                                      (or (budget/exhausted e) (throw e))))))
         found           (report-categories (budget/found m))]
     (cond
       reason      (merge {:status :truncated :reason reason :candidate-count candidate-count}
                          (budget/snapshot m) found)
       (seq found) (merge {:status :gap :candidate-count candidate-count} found)
       :else       {:status :audited :candidate-count candidate-count}))))
