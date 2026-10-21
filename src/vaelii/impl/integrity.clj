;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.integrity
  "Bounded, read-only KB integrity reporting: the passes `kb-integrity` runs under a work
  meter (`vaelii.impl.budget`).  `vaelii.core` requires this namespace; it requires
  `predall` and `provers`, which also sit below `vaelii.core`.  See docs/integrity.md."
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [vaelii.impl.budget :as budget]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide.arity :as arity]
            [vaelii.impl.except :as exc]
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

(defn- own-arg-types
  "`{position #{type …}}` from the `arg` declarations `context` sees written on `pred`
  itself — the domain its author declared, before any super-predicate's declaration is
  read into it."
  [kb pred context]
  (reduce (fn [m [_ b]]
            (budget/spend!)
            (let [n (get b '?n) t (get b '?t)]
              (if (and (integer? n) (symbol? t) (not (sx/variable? t)))
                (update m n (fnil conj #{}) t)
                m)))
          {}
          (res/matches-visible kb (list 'arg pred '?n '?t) context)))

(defn- constraining-arg-types
  "`[position type declaring-predicate]` for every `arg` declaration binding `pred`'s
  tuples from `context`: `pred`'s own and every visible super-predicate's, read through
  `res/constraining-predicates`, the closure `assert`'s argument check reads."
  [kb pred context]
  (for [p     (res/constraining-predicates kb 'arg pred context)
        [_ b] (res/matches-visible kb (list 'arg p '?n '?t) context)
        :let  [n (get b '?n) t (get b '?t)]
        :when (and (integer? n) (symbol? t) (not (sx/variable? t)))]
    [n t p]))

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

(def ^:private positional-kinds
  "The declarations that type one numbered position, `(K P n T)`."
  '[arg genlArg quotedArg])

(def ^:private rest-kinds
  "The declarations that type position `n` and every later one, `(K P n T)`."
  '[argAndRest argAndRestGenl])

(def ^:private every-kinds
  "The declarations that type every position, `(K P T)`."
  '[args argsGenl])

(defn- declared-rows
  "The ground `[pos type]` rows of every `(kind q pos type)` (or `(kind q type)`, `pos`
  nil, when `pos?` is false) visible from `context` over `pred` and each super-predicate
  `res/constraining-predicates` reads for `kind`."
  [kb kind pred pos? context]
  (for [q     (distinct (cons pred (res/constraining-predicates kb kind pred context)))
        [_ b] (res/matches-visible kb (if pos? (list kind q '?n '?t) (list kind q '?t))
                                   context)
        :let  [n (get b '?n) t (get b '?t)]
        :when (and (some? t) (not (sx/variable? t))
                   (or (not pos?) (integer? n)))]
    (do (budget/spend!) [n t])))

(defn- typed-positions
  "`{:at #{n …} :from n-or-nil :every? bool}` for `pred` as `context` reads its
  declarations: the positions one declaration types, the first position a rest form
  types onward, and whether a form types them all.  The binary `arg1` through `arg5`
  projections are read on `pred` itself."
  [kb pred context]
  {:at     (into (set (for [k positional-kinds [n _] (declared-rows kb k pred true context)] n))
                 (for [[k n] sx/arg-projections
                       :when (do (budget/spend!)
                                 (seq (res/matches-visible kb (list k pred '?t) context)))]
                   n))
   :from   (some->> (for [k rest-kinds [n _] (declared-rows kb k pred true context)] n)
                    seq (apply min))
   :every? (boolean (some #(seq (declared-rows kb % pred false context)) every-kinds))})

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

(defn- missing-positions
  "The finding for one predicate of declared arity `arity`, or nil: each position 1..n
  (1..`arityMin` for a variable arity, and `:rest` for its tail) no declaration types.
  A unary predicate's one position is typed by any visible `genl` edge out of it, which
  says of its members what `(arg P 1 T)` would."
  [kb tx pred arity context]
  (budget/spend!)
  (let [{:keys [at from every?]} (typed-positions kb pred context)
        typed?  (fn [n] (or every? (contains? at n) (and from (>= n from))))
        n       (if (= :variable arity) (arity-min kb pred context) arity)
        missing (cond-> (vec (remove typed? (range 1 (inc n))))
                  (and (= :variable arity) (not every?) (not (and from (<= from (inc n)))))
                  (conj :rest))
        missing (if (and (= 1 arity) (= [1] missing)
                         (seq (disj (set (tax/direct-genls tx pred context)) pred)))
                  []
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

;; ---- taxonomy-island: a type with a genl edge that does not reach the root ----

(defn- taxonomy-reach
  "The type nodes `context` sees, the root and how many nodes reach it, and the two readers
  the counting used: `:candidate?`, which excludes a `kb/relation?` name, and `:reaches?`,
  whether a node reaches a given type.  A nil `context` reads every node through the
  unscoped closures, for `taxonomy-coverage`: a report on the whole taxonomy has no
  vantage to read from.

  The root is *found*, not assumed — `thing` is this engine's and a converted corpus
  brings its own — so whatever type the most nodes reach is the root, ties broken by print
  order.  Reachability is **reflexive**, as `genls` is: the root reaches itself, so
  `:rooted` counts it.  A name with no stored arity stays a candidate rather than hiding a
  disconnected type island.

  Each node's up-closure is read to find the root, so a chain of V types costs Θ(V²)
  where it has V−1 edges.  `progress!` is called with `{:done 0 :total n}` once the nodes
  are known."
  [kb context progress!]
  (let [taxo       (reasoning/taxonomy kb)
        ;; Memoized: the reach walk asks this once per node AND once per ancestor of every
        ;; node, over a name set far smaller than that count, and the answer cannot move
        ;; inside one reading.
        candidate? (memoize #(not (kb/relation? kb % nil)))
        nodes      (into #{} (filter candidate?)
                         (if context (tax/types taxo context) (tax/types taxo)))
        up         (fn [t]
                     (budget/spend!)
                     (filter candidate? (if context
                                          (tax/genls taxo t context)
                                          (tax/genls-global taxo t))))
        _          (progress! {:done 0 :total (count nodes)})
        reach      (with-open [r (progress/start ::taxonomy
                                                 "integrity: walk the type ancestor sets"
                                                 (count nodes))]
                     (frequencies (mapcat up (progress/each r nodes))))
        [root rooted] (first (sort-by (juxt (comp - val) (comp nm/print-key key)) reach))]
    {:candidate? candidate?
     :nodes      nodes
     :root       root
     :rooted     (or rooted 0)
     :reaches?   (fn [t r]
                   (budget/spend!)
                   (if context (tax/genl? taxo t r context) (tax/genl?-global taxo t r)))}))

(defn taxonomy-coverage
  "Two numbers, not one: how many type names carry a `genl` edge at all, and how many
  reach the root — `{:names :edged :root :rooted :islands}`, read from every context.
  `:islands` is the edged types that do not reach the root, the `:taxonomy-island`
  findings counted, and **the gap between the two numbers is the finding**.

  `type-names` is the denominator's vocabulary: every type-shaped name, which by
  `docs/naming.md` includes a bare lowercase word (`likes` is a legal predicate *and* a
  legal type name), filtered as the nodes are.  `progress!` is `taxonomy-reach`'s."
  [kb type-names progress!]
  (let [{:keys [candidate? nodes root rooted]} (taxonomy-reach kb nil progress!)
        named (into #{} (filter candidate?) type-names)]
    {:names   (count (into named nodes))
     :edged   (count nodes)
     :root    root
     :rooted  rooted
     :islands (max 0 (- (count nodes) rooted))}))

(defn- taxonomy-island-findings
  "Every type node `context` sees that does not reach the root, as `{:term :root}` in
  print order."
  [kb context remaining]
  (let [{:keys [nodes root reaches?]} (taxonomy-reach kb context (fn [_] nil))]
    (bounded-findings
     :taxonomy-island
     (when root
       (for [t     (sort-by nm/print-key nodes)
             :when (not (reaches? t root))]
         {:term t :root root}))
     remaining)))

;; ---- stranded-declaration: an argument constraint past its predicate's arity ----
;;
;; `(arg parentOf 3 person)` is admitted while `parentOf` has no declared length —
;; open-world, and the highest position a declaration names is a lower bound on the arity
;; rather than a claim about it.  Then a length arrives, by any of the routes
;; `arity/relation-length` reads, and the declaration is left constraining a position the
;; predicate provably does not have.  It is not refused: refusing it would make the
;; *binding's* arrival order decide what the KB holds.  It simply stops meaning anything,
;; while the entry point refuses the identical sentence one line later.
;;
;; A `variable_arity` predicate is the case where the length is not the last word, and the
;; entry point's arm releases it: such a predicate reads a tuple of any length from its
;; declared arity upward, so a position past that length is one its tuples really do
;; reach.  Nothing of its is a finding, however high the position, because nothing of its
;; is stranded.
;;
;; **A sweep rather than a settle-ledger entry.**  A wrong-length *fact* is a claim each
;; reader believes or withdraws (`vaelii.impl.decide`).  A stranded declaration is inert:
;; it constrains nothing, refuses nothing and mints nothing, and it reads the same an hour
;; later as at the moment it went stale.  There is no newly to report, so paying per write
;; buys nothing a sweep does not give for free — and a per-declaration ledger entry would
;; compete for the 1,000 slots `violations` keeps and log a `:warn` line each.

(def ^:private declaration-functors
  "The argument constraints, in the order this walks them.  A vector rather than the
  set in `checks`, because this is a walk order and that is a membership test."
  '[arg genlArg interArg interArgEqual])

(defn- thing-typed
  "The type a declaration's `sentence` mints in is `thing`: the last argument of `arg` and
  `genlArg`, the fifth of `interArg` and `interArgEqual`."
  [sentence]
  (= 'thing (if (contains? '#{interArg interArgEqual} (nm/functor sentence))
              (nth sentence 5 nil)
              (last sentence))))

(defn stranded-declarations
  "Which argument constraints name a position their predicate does not have —
  `{:total n :stranded [entry …] :typed-thing [entry …]}`, `:total` counting the
  declarations walked and the `:stranded` entries
  `{:handle :sentence :context :predicate :position :arity :via :message}` in content
  order.  `:typed-thing` lists, in the same order, the declarations that type a position
  `thing`, each `{:handle :sentence :context :facts}` with `:facts` its predicate's stored
  extent: a declaration typing `thing` mints nothing (`arity/mintable-type?`), so the
  remedy is a narrower type in the declaration.  With a `context`, only the declarations
  it sees are walked; with nil, every stored one.

  **Enumerated, not probed per predicate.**  Declarations are vocabulary and vocabulary is
  small, so reading all of them and asking each about its own predicate is cheaper than
  asking each predicate what declares it, and it does not grow with the spec subtree
  underneath.  What it does grow with is the hierarchy *above*: `arity/relation-length` is
  a binding read for a predicate carrying a length of its own and a walk of the supers for
  one that inherits its length, so the walk is `O(declarations × super-predicates)`.

  Belief-filtered: a stored, disbelieved declaration constrains nothing for a reason that
  has nothing to do with its position, and listing it would name the wrong defect.

  `:message` is the one `checks` wrote when it convicted, **carried rather than
  re-derived**: a caller reading this map and a caller reading `check`'s answer are told
  the same thing in the same words, and there is no second wording to drift from it.

  One membership reader per context met: a reader memoizes for the life of one caller, so
  building one per declaration pays the retrieval every time and throws the memo away
  unread.  `progress!` is called with `{:done 0 :total n}` once the declarations are
  known."
  [kb context progress!]
  (let [taxo   (reasoning/taxonomy kb)
        reader (let [cache (volatile! {})]
                 (fn [ctx]
                   (or (get @cache ctx)
                       (let [r (kb/membership-reader kb ctx)]
                         (vswap! cache assoc ctx r)
                         r))))
        stored (into []
                     (comp (mapcat #(reads/as-stored-with-functor (:index kb) %))
                           (distinct)
                           (keep #(p/get-sentex (:records kb) %))
                           (filter #(not (sx/negative? %)))
                           (filter #(or (nil? context) (tax/sees? taxo context (:context %))))
                           (filter #(exc/believed-own? kb (:id %))))
                     declaration-functors)]
    (progress! {:done 0 :total (count stored)})
    (let [found (with-open [r (progress/start ::declarations
                                              "integrity: check the argument declarations"
                                              (count stored))]
                  (into []
                        (keep (fn [sx]
                                (budget/spend!)
                                (progress/tick! r)
                                (let [ctx (:context sx)]
                                  (when-let [v (checks/arg-position-violation
                                                kb (:sentence sx) ctx (reader ctx))]
                                    {:handle    (:id sx)
                                     :sentence  (:sentence sx)
                                     :context   ctx
                                     :predicate (:predicate v)
                                     :position  (:position v)
                                     :arity     (:arity v)
                                     :via       (:via v)
                                     :message   (:message v)}))))
                        stored))
          ;; content order, so the listed set is a function of the vocabulary rather than
          ;; of the handle order the index walked
          order #(nm/sort-by-content-key
                  (juxt (comp nm/print-key :sentence) (comp nm/print-key :context))
                  compare %)]
      {:total       (count stored)
       :stranded    (order found)
       :typed-thing (order (for [sx stored :when (thing-typed (:sentence sx))]
                             {:handle   (:id sx)
                              :sentence (:sentence sx)
                              :context  (:context sx)
                              :facts    (reads/stored-count-with-functor
                                         (:index kb) (second (:sentence sx)))}))})))

(defn- stranded-declaration-findings
  "Every stranded declaration `context` sees, in content order."
  [kb context remaining]
  (bounded-findings :stranded-declaration
                    (:stranded (stranded-declarations kb context (fn [_] nil)))
                    remaining))

;; ---- rule-clash: two rules whose conclusions would contradict if both fired ----
;;
;; Static analysis of the rules: one record read per rule, and a unification per candidate
;; pair the consequent index brings together.  Nothing is derived, nothing believed and no
;; fact consulted, so a pair is a contradiction the rules *admit* rather than one that has
;; formed — a formed one is in `(contradictions kb)`.
;;
;; Read **as stored**: a rule the KB currently disbelieves is still a rule somebody wrote.
;; The declarations the pairing consults — `genl`, `disjoint`, `functional`, `asymmetric`,
;; `genlCx` — follow belief, because a separation nobody believes separates nothing.
;;
;; A rule whose consequent functor is a **variable** is outside the pairing: it concludes
;; whatever binds, so it would clash with every other rule, which is a page of findings
;; about one rule.
;;
;; The rule rows below are public because `vaelii.impl.quality`'s subsumption reading
;; pairs the same rows, read once for both.

(def ^:private progress-every
  "How many rules a rule-row read or a pairing covers between progress calls."
  4096)

(defn rule-variables
  "Every variable across a rule's patterns, **sorted by name** — so a renaming is a
  function of the rule's content rather than of a set's iteration order, and two loads of
  the same KB report the same substitution."
  [forms]
  (sort (reduce into #{} (map sx/form-variables forms))))

(defn- renaming
  "A rule's variables renamed apart from any other rule's.  Every stored rule is numbered
  `?var0 …` (docs/canonicalization.md), so unifying two of them untouched would join
  variables that share a name and nothing else."
  [forms]
  (into {}
        (map-indexed (fn [i v] [v (symbol (str "?other" i))]))
        (rule-variables forms)))

(defn- rule-row
  "One rule as the pairings read it: the decomposition off the record, the consequent
  split into polarity and body, and the sentence as its author wrote it."
  [sx]
  (let [conseq (:consequent sx)
        neg?   (sx/negation? conseq)
        body   (if neg? (second conseq) conseq)
        sent   (sx/authored-sentence sx)]
    {:handle     (:id sx)
     :context    (:context sx)
     :varmap     (:varmap sx)
     :sentence   sent
     :sort-key   [(nm/print-key sent) (nm/print-key (:context sx))]
     :antecedent (vec (:antecedent sx))
     :consequent conseq
     :body       body
     :polarity   (if neg? :negative :positive)
     :functor    (nm/functor body)
     :arity      (nm/arity body)
     :engines    (:engines sx)
     :defeasible (boolean (:defeasible sx))
     :effect     (:effect sx)}))

(defn rule-rows
  "Every rule of `handles` as a `rule-row`: the one record read per rule a pairing pays.
  `progress!` is called with `{:done i :total n}` before the loop and every
  `progress-every` rules.

  A negated implication and a variable-functor consequent are dropped here: the first
  concludes nothing to cover or clash with, and the second concludes anything."
  [kb handles progress!]
  (let [hs    (vec handles)
        total (count hs)]
    (progress! {:done 0 :total total})
    (with-open [r (progress/start ::rule-rows "integrity: read the rule records" total)]
      (loop [i 0, out (transient [])]
        (if (= i total)
          (persistent! out)
          (let [sx (do (budget/spend!) (p/get-sentex (:records kb) (nth hs i)))
                v  (when (and sx (some? (:antecedent sx)))
                     (rule-row sx))]
            (when (and (pos? i) (zero? (mod i progress-every)))
              (progress! {:done i :total total}))
            (progress/tick! r)
            (recur (inc i)
                   (if (and v (symbol? (:functor v)) (not (sx/variable? (:functor v))))
                     (conj! out v)
                     out))))))))

(defn by-consequent
  "`[polarity functor] -> rule rows` — the pruning index a pairing reads, and the reason
  neither pairing is a cross product over the rule set."
  [rows]
  (group-by (juxt :polarity :functor) rows))

(defn rule-exception-conjuncts
  "The `exceptWhen` conjunctions in force for a rule, or nil.  Read only for a rule the
  watched-rule set holds, so an ordinary rule — every rule, on nearly every KB — pays one
  O(1) membership read and no term lookup."
  [kb handle]
  (when (reads/watched-rule? (:index kb) handle)
    (seq (provers/rule-exceptions kb handle))))

(defn- renamed
  "The rule row `v` with its patterns renamed apart, for a pairing that unifies two rules rather
  than matching one against the other."
  [v]
  (let [m (renaming (cons (:consequent v) (:antecedent v)))]
    (assoc v
           :consequent (sx/rename-vars (:consequent v) m)
           :body       (sx/rename-vars (:body v) m)
           :antecedent (mapv #(sx/rename-vars % m) (:antecedent v))
           :rename     m)))

(defn- pair-context
  "The context a nogood between two rules could form in — a **common descendant** of the
  two, since a clash is a clash where both halves are visible (docs/nmtms.md, \"Which
  contexts can contradict each other\").  Asking only whether one sees the other would
  exempt every sibling pair.  nil when no context sees both, which is the pair that is not
  a finding: neither rule's conclusion is anywhere near the other's.  The least of the
  maxima by content, so the reported context does not depend on a set's iteration order."
  [kb a b]
  (nm/min-by-content-key
   nm/print-key compare
   ;; `into #{}` and not the set literal: two rules in one context is the ordinary case,
   ;; and `#{x x}` is a duplicate-key throw rather than a one-element set
   (tax/maximal-common-descendant-contexts
    (reasoning/taxonomy kb) (into #{} [(:context a) (:context b)]))))

(defn- functional-marks-by-position
  "`{1 #{pred …} 2 #{pred …}}` — the predicates carrying a functional-family mark on each
  position of a **binary** tuple, at or above `f`.

  `(functional P)` joins position 2, being `(functionalInArg P 2)` written the arity-2
  way.  A mark at position 3 or beyond appears in neither: it constrains a slot a binary
  literal does not have, and pairing two conclusions on a constraint neither is subject
  to would be a report about nothing.

  Split by position because the pairwise test is not symmetric in the two: the mark names
  the constrained slot, so position 2 unifies argument 1 and compares argument 2, and
  position 1 does the mirror.  One read of the table serves both."
  [tax f context]
  (let [inarg (tax/functional-in-arg-over tax f context)
        at    (fn [n] (into #{} (comp (filter #(= n (second %))) (map first)) inarg))]
    {1 (at 1)
     2 (into (at 2) (tax/props-over tax :functional f context))}))

(defn- marks-over
  "The predicates a `kind` mark reaches at or above `f`, as one set — **the one place the
  clash detector spells a mark's reach**, read by all three of the sites that need it.

  For `:asymmetric` that is `tax/props-over` and nothing more.  For `:functional` it is
  both spellings and **both positions a binary tuple has**, which is
  `functional-marks-by-position` unioned.

  A mark names the *constrained* slot and the rest of the tuple is its determinant, so on
  a binary conclusion position 2 is the familiar reading — subject in argument 1, value in
  argument 2 — and position 1 is its mirror, the subject in argument 2.  Only position 3
  and up are genuinely out of reach here, constraining a slot these literals do not have.

  Unioned rather than kept apart because this answers *candidate* questions: which pairs
  are formed and which groups a rule row joins.  An over-approximated candidate merely fails
  `consequent-clash` and yields nothing, where a missing one is never asked at all.  The
  pairwise test is the caller that has to know which position it is looking at, and it
  reads the split map directly.

  **Three callers, which is why this is a function and not three expressions.**  The
  reach is asked at the candidate filter (`marked-groups`, does the KB declare any and
  which group does a binary conclusion join), at the lookup (`clash-partners`, which groups does this rule's
  functor reach) and at the pairwise test (`consequent-clash`, do these two share one).
  #56 was found and half-fixed twice before that was noticed: widening the pairwise test
  alone left the candidate filter answering nil, and widening the filter too left the
  lookup finding no group.  A mark family reaches a pass through every one of its reads or through none."
  [tax kind f context]
  (if (= :functional kind)
    (let [by-pos (functional-marks-by-position tax f context)]
      (into (get by-pos 1) (get by-pos 2)))
    (tax/props-over tax kind f context)))

(defn- marks-declared?
  "Does the KB declare any `kind` mark at all?  `marked-groups` runs this O(1) check
  first, and the check reads the same two `:props` sets `marks-over` reads.

  The `:functional` arm is `tax/functional-family-declared?` rather than the `or` written
  out here, because that question — does the taxonomy hold a functional mark of *either*
  spelling — is asked by every entry point of the family (`special`'s three `equate-*` lanes as
  well as this pass), and spelling it per caller is what #52, #54 and #56 each were: one
  reader of a two-spelling family that had only learned one.  A third spelling joins the
  family there and reaches all of them."
  [tax kind]
  (if (= :functional kind)
    (tax/functional-family-declared? tax)
    (boolean (seq (tax/props tax kind)))))

(defn- consequent-clash
  "How `a`'s consequent and `b`'s would clash if both rules fired — `[kind σ]`, or nil.
  `b`'s variables are renamed apart from `a`'s, so σ is over both.

  Four kinds, asked in a fixed order so a pair that answers to two — a predicate declared
  both `functional` and `asymmetric` — lands under one of them rather than under whichever
  a map iterated to first:

  - **`:negation`** — one concludes `S` and the other `(not T)` where `S` entails `T`.
    The genl fan runs one way here: `(dog X)` contradicts `(not (animal X))` and
    `(animal X)` does not contradict `(not (dog X))`.
  - **`:disjoint`** — two unary type conclusions about one term whose types a `disjoint`,
    `sibling_disjoint` or `disjoint_metatype` declaration separates.
  - **`:functional`** — two conclusions filling one functional slot for one subject with
    values that are not the same term.  The mark is read **up** the predicate hierarchy,
    so two `fatherOf` conclusions clash against `(functional parentOf)`, and it is read
    in **both** spellings: `(functionalInArg parentOf 2)` says the same thing about the
    same slot, so a detector reading only `:props` was blind to a KB that spells it that
    way (#56).  Read per **position**: the mark names the constrained slot, so a
    position-2 mark unifies the subjects and compares the values and a position-1 mark
    mirrors that, and only position 3 and up is out of reach — a slot these two literals
    do not have.
  - **`:asymmetric`** — one tuple concluded both ways round, under a predicate declared
    `asymmetric` anywhere above either.  A self tuple `(P a a)` is not one: the ontology
    admits it, so a σ identifying the two arguments is no clash."
  [kb a b context]
  (let [tax (reasoning/taxonomy kb)
        fa  (:functor a)
        fb  (:functor b)]
    (cond
      (not= (:polarity a) (:polarity b))
      (let [[pos neg] (if (= :positive (:polarity a)) [a b] [b a])]
        (when-let [s (res/subsuming-unify kb (:body neg) (:consequent pos)
                                          res/no-bindings context)]
          [:negation s]))

      (= :negative (:polarity a)) nil    ; two negations agree about everything

      :else
      (or
       (when (and (= 1 (:arity a)) (= 1 (:arity b)) (not= fa fb)
                  (tax/disjoint? tax fa fb context))
         (when-let [s (res/unify (second (:body a)) (second (:body b)))]
           [:disjoint s]))
       (when (and (= 2 (:arity a)) (= 2 (:arity b)))
         ;; Per position, because the mark names the CONSTRAINED slot and the rest of the
         ;; tuple is its determinant: a position-2 mark unifies the subjects and compares
         ;; the values, and a position-1 mark is that read in the mirror.  Reading
         ;; position 2 alone left `(functionalInArg P 1)` enforced by
         ;; `checks/functional-clashes` and invisible to this pass.
         (let [pa (functional-marks-by-position tax fa context)
               pb (functional-marks-by-position tax fb context)
               [s1 v1] (nm/args (:body a))
               [s2 v2] (nm/args (:body b))
               clash (fn [det-a det-b val-a val-b]
                       (when-let [s (res/unify det-a det-b)]
                         (when (not= (res/substitute val-a s) (res/substitute val-b s))
                           [:functional s])))]
           (or (when (seq (set/intersection (get pa 2) (get pb 2)))
                 (clash s1 s2 v1 v2))
               (when (seq (set/intersection (get pa 1) (get pb 1)))
                 (clash v1 v2 s1 s2)))))
       (when (and (= 2 (:arity a)) (= 2 (:arity b))
                  (seq (set/intersection (marks-over tax :asymmetric fa context)
                                         (marks-over tax :asymmetric fb context))))
         (let [[x1 y1] (nm/args (:body a))
               [x2 y2] (nm/args (:body b))]
           (when-let [s (res/unify-args (list x1 y1) (list y2 x2))]
             (when (not= (res/substitute x1 s) (res/substitute y1 s))
               [:asymmetric s]))))))))

(defn- separated-antecedents?
  "Do two of these literals claim one term is of two types a declaration separates?  The
  one thing the joint-satisfiability test reads a declaration for, and it reads the same
  one the consequent side does."
  [kb lits context]
  (let [tax     (reasoning/taxonomy kb)
        by-term (reduce (fn [m l]
                          (let [f (nm/functor l)]
                            (if (and (= 1 (nm/arity l)) (symbol? f) (not (sx/variable? f)))
                              (update m (second l) (fnil conj #{}) f)
                              m)))
                        {} lits)]
    (boolean (some (fn [[_ ts]]
                     (let [ts (vec ts)]
                       (some (fn [[x y]] (tax/disjoint? tax x y context))
                             (for [i (range (count ts)), j (range (inc i) (count ts))]
                               [(nth ts i) (nth ts j)]))))
                   by-term))))

(defn- literal-arity-claim
  "The arity `lit` binds its first argument to, or nil — the two spellings `checks`
  reads, asked of a *literal* rather than of the store.

  `(arity ?p n)` says it outright.  A unary `(T ?p)` says it whenever `T` reaches one of
  the exact-arity classes up `genl`, which is what makes `(symmetric ?p)` a claim of arity
  2: `symmetric` is a kind of `binary_predicate`.  The table is
  `tax/exact-arity-classes`, read here rather than copied, since a table copied twice
  is a table that drifts, and read in key order so a term reaching two that disagree —
  itself incoherent — reports the same one every run."
  [tax lit context]
  (let [f (nm/functor lit)]
    (when (and (symbol? f) (not (sx/variable? f)))
      (cond
        (and (= 'arity f) (= 2 (nm/arity lit)))
        (let [n (last (nm/args lit))] (when (integer? n) n))

        (= 1 (nm/arity lit))
        (let [supers (tax/genls tax f context)]
          (some (fn [[t n]] (when (contains? supers t) n))
                (sort-by key tax/exact-arity-classes)))))))

(defn- arity-conflicted?
  "Do two of these literals bind one term to two arities?  A predicate takes one number of
  arguments — `(functional arity)` says so of the table, and the relation-wide classes are
  pairwise `disjoint`, which their kind specializations inherit (docs/taxonomy.md) — so no
  term satisfies both, whichever of the two spellings each literal used.  `(arity ?p 1)` beside `(arity ?p 2)`, and `(arity ?p 1)`
  beside `(equivalence_relation ?p)`, are the same finding read two ways.

  A declaration read, not an inference: nothing is derived and no fact is consulted, the
  same standing `separated-antecedents?` has beside it."
  [kb lits context]
  (let [tax     (reasoning/taxonomy kb)
        by-term (reduce (fn [m l]
                          (if-let [n (literal-arity-claim tax l context)]
                            (update m (second l) (fnil conj #{}) n)
                            m))
                        {} lits)]
    (boolean (some (fn [[_ ns]] (> (count ns) 1)) by-term))))

(defn- lower-bounds
  "The integers `k` the literals `lits` state `v` exceeds: `(lessThan k v)` and
  `(greaterThan v k)`."
  [lits v]
  (keep (fn [l]
          (let [[f x y] l]
            (when (= 3 (count l))
              (cond (and (= 'lessThan f) (= v y) (integer? x))    x
                    (and (= 'greaterThan f) (= v x) (integer? y)) y))))
        lits))

(defn- arity-floor-conflicted?
  "Does a literal bound a term's length above the exact arity another literal claims?
  `(arity ?p ?n)` beside `(lessThan k ?n)` says ?p takes more than k places, and
  `(arityMin ?p ?n)` beside it says ?p requires more than k.  A term `literal-arity-claim`
  binds to exactly n places, with n at most k, satisfies neither: the arity table is
  functional, and a minimum above the exact length admits no application.  The floor
  rules core.txt states over `arity` and `arityMin` read that way beside every rule that
  concludes an exact class.

  A declaration read, as `arity-conflicted?` is beside it."
  [kb lits context]
  (let [tax   (reasoning/taxonomy kb)
        exact (reduce (fn [m l]
                        (if-let [n (literal-arity-claim tax l context)]
                          (update m (second l) (fnil conj #{}) n)
                          m))
                      {} lits)]
    (boolean
     (some (fn [l]
             (let [[f p v] l]
               (when (and (#{'arity 'arityMin} f) (= 3 (count l)) (sx/variable? v))
                 (some (fn [n] (some #(>= % n) (lower-bounds lits v)))
                       (get exact p)))))
           lits))))

(defn- declared-arg-types
  "The `[position type]` pairs the instance-type declarations bind a `pred` literal of
  `arity` arguments to: `arg`, and the covering `args` / `argAndRest` at every position
  of the literal they reach.  Read through `checks/instance-type-declarations`, the one
  reading of the three spellings, so a declaration the entry point honors is one this
  honors; up the predicate hierarchy, so a super-predicate's declaration types a
  sub-predicate's tuple.  A declaration read, not an inference: nothing is derived and no
  fact is consulted, the same standing `separated-antecedents?` and `arity-conflicted?`
  have beside it."
  [kb pred arity context]
  (for [{:keys [from to type]} (checks/instance-type-declarations kb pred context)
        n (range from (inc (min (or to arity) arity)))]
    [n type]))

(def ^:private relation-wide-arity-classes
  "Each length's relation-wide class in `tax/exact-arity-classes`, the one the predicate
  and function classes of that length specialize."
  (into {} (keep (fn [c] (when-let [n (get tax/exact-arity-classes c)] [n c])))
        '[unary binary ternary quaternary quinary]))

(defn- genl-arity-class
  "The relation-wide exact-arity class `(genl a P)` demands of `a`, or nil: a spec of `P`
  has `P`'s length, read by `kb/relation-arity`."
  [kb l]
  (let [[f _ p] l]
    (when (and (= 'genl f) (= 3 (count l)) (symbol? p) (not (sx/variable? p)))
      (some-> (kb/relation-arity kb p) relation-wide-arity-classes))))

(defn- application-demands
  "`[term [type :declared]]` for each application `(F …)` written in the arguments `as` of a
  `pred` literal, at any depth: `F`'s `result` types the application (`nat/result-types`)
  and `F`'s instance-type declarations type its arguments (`declared-arg-types`).  A
  formula is not an application: a connective's argument, and a compound whose head is a
  `predicate`, are not read.  An argument of a quoting predicate or quoting function, or at
  a position a `quotedArg` declaration types (`checks/quoted-positions`), is a mention and
  is not descended into."
  [kb pred as context]
  (letfn [(used [f xs]
            (if (some sequential? xs)
              (let [qs (checks/quoted-positions kb f context)]
                (keep-indexed (fn [i x] (when-not (contains? qs (inc i)) x)) xs))
              xs))
          (walk [x]
            (let [f (when (sequential? x) (first x))]
              (when (and (symbol? f) (not (sx/variable? f))
                         (not (contains? provers/formula-heads f))
                         (not (kb/isa? kb f 'predicate context)))
                (let [xs (vec (rest x))]
                  (concat
                   (when (nat/any-result-declarations? kb)
                     (for [t (nat/result-types kb x context)
                           :when (and (symbol? t) (not (sx/variable? t)))]
                       [x [t :declared]]))
                   (for [[n t] (declared-arg-types kb f (count xs) context)]
                     [(nth xs (dec n)) [t :declared]])
                   (when-not (sx/quoting-functor? f) (mapcat walk (used f xs))))))))]
    (when-not (or (contains? provers/formula-heads pred)
                  (contains? res/nat-quoting-predicates pred)
                  (sx/quoting-functor? pred))
      (mapcat walk (used pred as)))))

(defn- arg-type-conflicted?
  "Does a declaration demand a term be of a type disjoint from another type the two rules
  place that term in?  `lits` are the positive antecedents of both rules and both
  consequents, already under σ, so a variable the two rules unify appears once.  Each term
  collects `[type source]` pairs: `:stated` for a type a unary literal names, `:declared`
  for a type one of these declarations demands:

  * an instance-type declaration of the literal's predicate on the term's position, `arg`
    and its covering forms `args` / `argAndRest` alike (`declared-arg-types`);
  * the relation-wide arity class of `P`'s length, for `a` in `(genl a P)`
    (`genl-arity-class`);
  * for an application written at any depth, its function's `result`, and its function's
    instance-type declarations on the application's arguments (`application-demands`).

  True when one term holds two disjoint types and at least one of them is `:declared`.
  `genlArg` and `genlResult` are not read: each bounds a subtype rather than a membership.
  See docs/quality.md, \"Contradictions in waiting\"."
  [kb lits context]
  (let [tax     (reasoning/taxonomy kb)
        demands (reduce
                 (fn [m l]
                   (let [f  (nm/functor l)
                         as (vec (nm/args l))]
                     (if (or (sx/negation? l) (not (symbol? f)) (sx/variable? f))
                       m
                       (let [m (if (= 1 (count as))
                                 (update m (first as) (fnil conj #{}) [f :stated])
                                 m)
                             m (if-let [c (genl-arity-class kb l)]
                                 (update m (first as) (fnil conj #{}) [c :declared])
                                 m)]
                         (reduce (fn [m [x d]] (update m x (fnil conj #{}) d))
                                 m (concat (for [[n t] (declared-arg-types kb f (count as) context)]
                                             [(nth as (dec n)) [t :declared]])
                                           (application-demands kb f as context)))))))
                 {} lits)]
    (boolean
     (some (fn [[_ ts]]
             (let [ts (vec ts)]
               (some (fn [[i j]]
                       (let [[t1 s1] (nth ts i), [t2 s2] (nth ts j)]
                         (and (not= t1 t2)
                              (or (= :declared s1) (= :declared s2))
                              (tax/disjoint? tax t1 t2 context))))
                     (for [i (range (count ts)), j (range (inc i) (count ts))] [i j]))))
           demands))))

(defn- negation-met-by-a-spec?
  "Does a positive literal over a spec of `P` stand beside `(not (P …))` with the same
  arguments?  A tuple of a spec is a tuple of `P` (`genl` between predicates), so the two
  cannot both hold: `(properPartOf a b)` beside `(not (partOf a b))`.  The equal-literal case
  is the reflexive edge of the same read."
  [kb pos neg context]
  (let [tax (reasoning/taxonomy kb)]
    (boolean
     (some (fn [n]
             (let [p (nm/functor n)]
               (and (symbol? p) (not (sx/variable? p))
                    (some (fn [l]
                            (let [q (nm/functor l)]
                              (and (symbol? q) (not (sx/variable? q))
                                   (= (nm/args l) (nm/args n))
                                   (contains? (tax/genls tax q context) p))))
                          pos))))
           neg))))

(defn- jointly-satisfiable?
  "Could both antecedent sets hold at once — **shallowly**?

  Five things rule it out and nothing else does: a literal appearing under σ together with
  its own negation, or with the negation of a predicate it is a spec of; one term claimed to
  be of two separated types; one term bound to two arities; one term bounded above the
  exact arity it is claimed to have; and one term a declaration demands be of a type
  disjoint from one the two rules place it in: an `arg` declaration, a `genl` literal's
  second argument by its arity, or an application's function.  **No
  inference is run and no fact is consulted** — each of the five is a declaration read.  This is what the rules say about each other, and a pair it admits
  is a clash that *could* form rather than one that will — which is the whole reading,
  since a clash that had already formed would be in `(contradictions kb)` instead.

  The fifth reads the consequents beside the antecedents, since the type an `arg`
  declaration demands of one rule's variable is disjoint from the type the **other** rule
  *concludes* about the unified term (`arg-type-conflicted?`)."
  [kb a b sigma context]
  (let [subst #(res/substitute % sigma)
        lits  (into (mapv subst (:antecedent a)) (map subst) (:antecedent b))
        pos   (into #{} (remove sx/negation?) lits)
        neg   (into #{} (comp (filter sx/negation?) (map second)) lits)
        heads (conj pos (subst (:consequent a)) (subst (:consequent b)))]
    (and (empty? (set/intersection pos neg))
         (not (negation-met-by-a-spec? kb pos neg context))
         (not (separated-antecedents? kb pos context))
         (not (arity-conflicted? kb pos context))
         (not (arity-floor-conflicted? kb pos context))
         (not (arg-type-conflicted? kb heads context)))))

(defn- rule-functors
  "Every predicate a rule names — its consequent's and its antecedents', a negation
  unwrapped."
  [v]
  (into #{(:functor v)}
        (keep (fn [l] (let [f (nm/functor (if (sx/negation? l) (second l) l))]
                        (when (symbol? f) f))))
        (:antecedent v)))

(defn- exception-names-other?
  "Does `a`'s `exceptWhen` name a predicate `b` is about?  That is the form a stated
  exception has — \"birds fly, unless penguins\" beside \"penguins do not fly\" — and it is
  why such a pair is reported as `:excepted` rather than hidden: a reader wants to see
  which clashes are already handled, not to be told there are none."
  [kb a b]
  (when-let [cs (rule-exception-conjuncts kb (:handle a))]
    (let [fs (rule-functors b)]
      (boolean (some (fn [c]
                       (some #(contains? fs (nm/functor (if (sx/negation? %) (second %) %))) c))
                     cs)))))

(defn- readable-unifier
  "σ in the two rules' own variable names, the **second** rule's carrying a trailing `'`.

  Both authors are free to write `?x`, and a map holding two of them says nothing; primed,
  `{?x' ?x}` reads as what it is — the second rule's `?x` is the first's."
  [sigma a b]
  (let [back (into (or (:varmap a) {})
                   (map (fn [[v r]]
                          [r (symbol (str (name (get (:varmap b) v v)) "'"))]))
                   (:rename b))]
    (into (sorted-map)
          (map (fn [[v t]]
                 [(get back v v) (sx/rename-vars (res/substitute t sigma) back)]))
          sigma)))

(defn- marked-groups
  "`marked predicate -> the binary-conclusion rule rows under it`, for one property.  nil
  when the KB declares none, which is the presence check that keeps the pairing off a KB with
  nothing to say — one map read.

  **`:functional` reads both spellings, here as well as in `consequent-clash`** (#56).
  This is the candidate filter that decides which pairs are ever *formed*, so widening only the
  pairwise test left it answering nil for a KB whose sole mark is `(functionalInArg P 2)`
  — no candidate pair, and nothing for the widened test to run on.  The reach is
  `marks-over`, which is where the two spellings and the position-2 filter are
  stated once; `:asymmetric` has one spelling and keeps the plain read."
  [tax kind rows]
  (when (marks-declared? tax kind)
    (reduce (fn [m v]
              (reduce (fn [m q] (update m q (fnil conj []) v)) m
                      (marks-over tax kind (:functor v) nil)))
            {}
            (filter #(and (= :positive (:polarity %)) (= 2 (:arity %))) rows))))

(defn- clash-index
  "What `clash-partners` looks a rule's candidates up in — the consequent index, the
  distinct unary conclusion functors (only where the KB declares some separation at all),
  and the marked groups for the two predicate properties."
  [kb rows]
  (let [tax (reasoning/taxonomy kb)
        pos (filterv #(= :positive (:polarity %)) rows)]
    {:by-key   (by-consequent rows)
     :unary-fs (when (or (seq (tax/disjoint-pairs tax))
                         (seq (tax/disjoint-metatypes tax))
                         (seq (tax/sibling-disjoints tax)))
                 (into #{} (comp (filter #(= 1 (:arity %))) (map :functor)) pos))
     :marked   {:functional (marked-groups tax :functional pos)
                :asymmetric (marked-groups tax :asymmetric pos)}}))

(defn- clash-partners
  "The rules worth asking `consequent-clash` about beside `a`.

  The **negation fan is global** and the pair is decided scoped, which is the form a
  candidate read has everywhere in the engine: the vantage a clash is asked from is a
  common descendant of the two rules' contexts and belongs to neither of them, so fanning
  from either would drop a pair the context that can see both would find.  An
  over-approximated candidate merely fails `consequent-clash` and yields nothing."
  [kb {:keys [by-key unary-fs marked]} a]
  (let [tax  (reasoning/taxonomy kb)
        f    (:functor a)
        pos? (= :positive (:polarity a))]
    (distinct
     (concat
      (if pos?
        (mapcat #(get by-key [:negative %]) (tax/genls-global tax f))
        (mapcat #(get by-key [:positive %]) (tax/specs-global tax f)))
      (when (and pos? unary-fs (= 1 (:arity a)))
        (for [g unary-fs
              :when (and (not= g f) (tax/disjoint? tax f g nil))
              b (get by-key [:positive g])]
          b))
      (when (and pos? (= 2 (:arity a)))
        (for [kind  [:functional :asymmetric]
              :let  [groups (get marked kind)]
              :when groups
              q     (marks-over tax kind f nil)
              b     (get groups q)]
          b))))))

(defn- clash-entry
  "The finding for one candidate pair, or nil."
  [kb a b0]
  (when-let [ctx (pair-context kb a b0)]
    (let [b (renamed b0)]
      (when-let [[kind s] (consequent-clash kb a b ctx)]
        (when (jointly-satisfiable? kb a b s ctx)
          {:rules     [(:handle a) (:handle b0)]
           :kind      kind
           :unifier   (readable-unifier s a b)
           :context   ctx
           :sentences [(:sentence a) (:sentence b0)]
           :excepted  (boolean (or (exception-names-other? kb a b0)
                                   (exception-names-other? kb b0 a)))})))))

(defn- clash-units
  "`[a b finding]` for every clashing pair of `rows`, lazily, in content order: a pair is
  taken once, a rule is never paired with itself — the reading is about two rules
  disagreeing — and `progress!` is called with `{:done i :total n}` before the walk and
  every `progress-every` rules."
  [kb rows progress!]
  (let [index   (clash-index kb rows)
        ordered (nm/sort-by-content-key :sort-key compare rows)
        total   (count ordered)]
    (progress! {:done 0 :total total})
    (letfn [(step [i]
              (lazy-seq
               (when (< i total)
                 (let [a (nth ordered i)]
                   (when (and (pos? i) (zero? (mod i progress-every)))
                     (progress! {:done i :total total}))
                   (concat
                    (keep (fn [b] (budget/spend!)
                            (when-let [e (clash-entry kb a b)] [a b e]))
                          (nm/sort-by-content-key
                           :sort-key compare
                           (filter #(neg? (compare (:sort-key a) (:sort-key %)))
                                   (clash-partners kb index a))))
                    (step (inc i)))))))]
      (step 0))))

(defn clash-pairs
  "Rule pairs of `rows` whose consequents would clash if both fired and whose
  antecedents could shallowly hold at once, as findings in content order:
  `{:rules [h1 h2] :kind :unifier :context :sentences :excepted}`.  `progress!` is called
  as `clash-units` says.

  **Static analysis of the rules**, which is what makes it a different question from
  `(contradictions kb)`: nothing here is derived, nothing believed and nothing asked of the
  KB's facts.  A pair is a clash the rules *admit*, and whether it ever forms depends on
  content nobody has asserted yet."
  [kb rows progress!]
  (map peek (clash-units kb rows progress!)))

(defn- inert-row?
  "Does `v` run in neither engine — a `set/inertRule`, documentation?"
  [v]
  (empty? (:engines v)))

(defn- rule-clash-findings
  "The clashing pairs among the stored rules `context` sees, in content order: the live
  pairs no `exceptWhen` handles under `:rule-clash`, and under `:rule-clash-review` (when
  `review?`) the pairs either rule of which is a `set/inertRule`, marked `:inert true`, and
  the `:excepted` ones.  An inert rule chains in neither engine, so its pair is a clash the
  rules would admit if the rule were switched on, a suggestion rather than a violation; an
  excepted pair is one the author already handled.

  The rules are read off the rule extent in every context (`reads/as-stored-rules-in-global`),
  the census `rule-macro-findings` takes, and kept when `context` sees the rule's context:
  the pairing needs every rule's row before it can ask where a pair is seen, so the read
  is the whole extent and the visibility a filter over it.  A pair's
  `:context` is where its nogood could form, a common descendant of the two rules'
  contexts, which need not be `context` itself."
  [kb context remaining review?]
  (let [taxo  (reasoning/taxonomy kb)
        rows  (filterv #(tax/sees? taxo context (:context %))
                       (rule-rows kb
                                  (into (sorted-set)
                                        (reads/as-stored-rules-in-global (:index kb) :rule))
                                  (fn [_] nil)))]
    (bounded-findings
     (if review? :rule-clash-review :rule-clash)
     (keep (fn [[a b e]]
             (let [inert? (or (inert-row? a) (inert-row? b))]
               (when (= review? (boolean (or inert? (:excepted e))))
                 (cond-> e inert? (assoc :inert true)))))
           (clash-units kb rows (fn [_] nil)))
     remaining)))

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
   [:stranded-declaration (fn [kb _ context remaining]
                            (stranded-declaration-findings kb context remaining))]
   [:rule-clash (fn [kb _ context remaining]
                  (rule-clash-findings kb context remaining false))]
   [:twin-genls (fn [kb _ context remaining]
                  (twin-genls-findings kb context remaining))]
   [:derivable-stated-edge (fn [kb _ context remaining]
                             (derivable-stated-edge-findings kb context remaining))]
   [:disjoint-could-be-partition (fn [kb _ context remaining]
                                   (disjoint-could-be-partition-findings kb context remaining))]
   [:missing-arg (fn [kb _ context remaining]
                   (missing-arg-findings kb context remaining))]
   [:taxonomy-island (fn [kb _ context remaining]
                       (taxonomy-island-findings kb context remaining))]
   [:rule-clash-review (fn [kb _ context remaining]
                         (rule-clash-findings kb context remaining true))]])

(def ^:private review-categories
  "The review-only categories: a sweep runs their passes only when `:categories` names
  them, so a finding of one never turns an otherwise clean default sweep into `:gap`."
  #{:twin-genls :derivable-stated-edge :disjoint-could-be-partition :missing-arg
    :taxonomy-island :rule-clash-review})

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
