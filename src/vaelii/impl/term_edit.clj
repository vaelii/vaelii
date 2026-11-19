;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.term-edit
  "The batch a term operation runs: every stored sentence that uses a term, restated with
  another term in its place or retracted, as one `edit!`.  `problems` answers what an
  operation refuses before a batch is built; `batch` builds the edit.  Nothing here
  writes.  See docs/api.md, \"Contract notes: term operations\"."
  (:require [vaelii.impl.io.shipped :as shipped]
            [vaelii.impl.io.text :as text]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.quasiquote :as qq]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.types.reasoning :as reasoning]))

(def ops
  "The term operations, each by the keyword `batch` takes."
  #{:rename :merge :copy :remove})

;; ---- the substitution ----------------------------------------------------

(defn- walk-uses
  "`form` with `f` applied to each symbol at a use position: everywhere outside a
  quotation, and inside an `(Unquote …)` hole of a `(Quasiquote …)`.  The argument of a
  `(Quote …)` or a `(Quasiquote …)` is a mention and is left as written, and so is a
  `Quasiquote` nested in a mention, holes included (`qq/strip-unquotes`).  A list rebuilds
  as a list and a vector as a vector."
  [f form]
  (letfn [(use [x] (cond
                     (symbol? x) (f x)
                     (and (seq? x) (= sx/quote-functor (first x))) x
                     (and (seq? x) (= sx/quasiquote-functor (first x)))
                     (apply list (first x) (map mention (rest x)))
                     (seq? x)    (apply list (map use x))
                     (vector? x) (mapv use x)
                     :else       x))
          (mention [x] (cond
                         (and (seq? x) (= sx/quasiquote-functor (first x))) x
                         (and (seq? x) (= qq/unquote-marker (first x)))
                         (apply list (first x) (map use (rest x)))
                         (seq? x)    (apply list (map mention x))
                         (vector? x) (mapv mention x)
                         :else       x))]
    (use form)))

(defn substitute
  "`form` with each symbol `smap` maps replaced at its use positions (`walk-uses`)."
  [smap form]
  (walk-uses #(get smap % %) form))

(defn- uses?
  "Does `form` hold a symbol of the set `syms` at a use position?"
  [syms form]
  (let [hit (volatile! false)]
    (walk-uses #(do (when (contains? syms %) (vreset! hit true)) %) form)
    @hit))

;; ---- what an operation refuses -------------------------------------------

(defn- term?
  "Does a stored sentex use `t`: as its context, or in its sentence outside a quotation?"
  [kb t]
  (boolean (some #(or (= t (:context %)) (uses? #{t} (sx/sentence-of %)))
                 (kb/find-sentexes kb t))))

(defn- reserved-problem
  "Why `t` is no term an operation can take: not a symbol, a variable, or a namespaced
  symbol outside `lex/` (a reified constant, a wrapper)."
  [t]
  (cond
    (not (symbol? t))
    {:type :reserved-term :term t :message (str (pr-str t) " is not a symbol")}
    (sx/variable? t)
    {:type :reserved-term :term t :message (str t " is a variable")}
    (and (namespace t) (not (nm/lexeme? t)))
    {:type :reserved-term :term t
     :message (str t " is a namespaced symbol the engine owns; a reified constant follows"
                   " the terms its expression names")}))

(defn- spelled-roles
  "The roles `t`'s spelling admits: a predicate or a type for a bare lowercase word, whose
  arity decides between the two (docs/naming.md); a type for a sense; else the one role
  `nm/term-role` reads, or none."
  [t]
  (cond
    (and (nm/predicate? t) (nm/type-symbol? t)) #{:predicate :type}
    (nm/sense? t)                               #{:type}
    :else (if-let [r (nm/term-role t)] #{r} #{})))

(defn- role-phrase [t]
  (case (sort (spelled-roles t))
    []                  "a name of no role"
    [:individual]       "an individual"
    [:predicate :type]  "a predicate or a type"
    (str "a " (name (first (spelled-roles t))))))

(defn- merge-problem
  "Why `from` cannot be merged or copied into the stored term `into`: a relation and a
  type, two relations of different arities, or two disjoint types.  Disjointness is read
  KB-wide: a merge restates the premises of every context, so a declaration in any one of
  them makes the merged term a member of two disjoint types there."
  [kb from into]
  (let [rel? #(kb/relation? kb % nil)
        ar   #(kb/relation-arity kb %)]
    (cond
      (not= (rel? from) (rel? into))
      {:type :incompatible-terms :term from
       :message (str "one of " from " and " into " is a relation and the other is not")}
      (and (rel? from) (ar from) (ar into) (not= (ar from) (ar into)))
      {:type :incompatible-terms :term from
       :message (str from " takes " (ar from) " arguments and " into " takes " (ar into))}
      (and (not (rel? from)) (kb/disjoint? kb from into))
      {:type :incompatible-terms :term from
       :message (str from " and " into " are disjoint, so nothing can be both")})))

(defn- shape-problems
  "The problems with `mapping`'s shape for `op`.  `:remove` takes a non-empty collection
  of symbols.  The others take a non-empty map of symbol to symbol, none mapped to itself
  or to a term the map also changes.  `:rename` maps no two terms to one."
  [op mapping]
  (let [bad #(vector {:type :shape :term nil :message %})]
    (cond
      (not (contains? ops op))
      (bad (str "the term operation is one of " (sort ops) ", not " (pr-str op)))
      (= :remove op)
      (when-not (and (coll? mapping) (not (map? mapping)) (seq mapping))
        (bad "remove takes a non-empty collection of terms"))
      (not (and (map? mapping) (seq mapping)))
      (bad (str (name op) " takes a non-empty map of each term to its new term"))
      :else
      (concat
       (for [[a b] mapping :when (= a b)]
         {:type :shape :term a :message (str a " is mapped to itself")})
       (for [b (distinct (vals mapping)) :when (contains? mapping b)]
         {:type :shape :term b :message (str b " is both a target and a term the operation changes")})
       (when (= :rename op)
         (for [[b as] (group-by val mapping) :when (< 1 (count as))]
           {:type :shape :term b
            :message (str (sort (map key as)) " are all renamed to " b "; merge-terms! joins terms")}))))))

(defn problems
  "What term operation `op` over `mapping` refuses before it builds a batch, as
  `[{:type :term :message} …]`, empty when it would run.  docs/api.md's table under
  \"Contract notes: term operations\" lists each `:type`."
  [kb op mapping]
  (or (seq (shape-problems op mapping))
      (let [froms (if (= :remove op) (seq mapping) (keys mapping))
            pairs (when-not (= :remove op) (seq mapping))]
        (or (seq (keep reserved-problem (concat froms (map val pairs))))
            (seq (for [[a b] pairs
                       :let [ra (spelled-roles a)]
                       :when (and (seq ra) (not-any? ra (spelled-roles b)))]
                   {:type :role-change :term b
                    :message (str b " is spelled as " (role-phrase b) " and " a " as "
                                  (role-phrase a) "; a new name keeps its role")}))
            (seq (for [a froms :when (and (not= :copy op) (shipped/shipped-term? a))]
                   {:type :shipped-term :term a
                    :message (str a " is named by the shipped ontology, which sync restates;"
                                  " merge a term into it instead")}))
            (seq (for [a froms :when (not (term? kb a))]
                   {:type :unknown-term :term a :message (str "no stored sentex names " a)}))
            (seq (for [[a b] pairs :when (and (= :rename op) (term? kb b))]
                   {:type :term-exists :term b
                    :message (str b " is a term already; merge-terms! joins " a " into it")}))
            (seq (for [[a b] pairs :when (and (= :merge op) (not (term? kb b)))]
                   {:type :unknown-term :term b
                    :message (str "no stored sentex names " b "; rename-terms! gives " a
                                  " that name")}))
            (seq (keep (fn [[a b]]
                         (when (or (= :merge op) (and (= :copy op) (term? kb b)))
                           (merge-problem kb a b)))
                       pairs))
            []))))

;; ---- the records an operation reaches ------------------------------------

(defn- written?
  "Is `sx` a record a text KB writes: a premise, or an inert sentex the TMS holds no node
  for?"
  [kb sx]
  (or (some? (:strength sx)) (not (jtms/known-datum? (reasoning/tms kb) (:id sx)))))

(defn- reach
  "`[records constants]`: every stored record using a term of `froms`, and the reified
  constants whose `natFormula` expression uses one of them or another such constant,
  except a writer-spelled one (`nat/writer-spelled?`), whose map is a record restated as
  written.  A context's extent is included, since the term index posts each sentex under
  its context.  The walk follows each constant to the records using it, to a fixpoint."
  [kb froms]
  (loop [frontier (set froms) seen #{} recs {} consts #{}]
    (if (empty? frontier)
      [recs consts]
      (let [found (into {} (comp (mapcat #(kb/find-sentexes kb %)) (map (juxt :id identity)))
                        frontier)
            uses  (into (set froms) consts)
            fresh (into #{} (keep (fn [sx]
                                    (let [s (:sentence sx)]
                                      (when (and (seq? s) (= 'natFormula (first s))
                                                 (nm/reified-constant? (second s))
                                                 (uses? (into uses frontier) (nth s 2 nil))
                                                 (not (nat/writer-spelled? kb (second s))))
                                        (second s)))))
                        (vals found))
            seen  (into seen frontier)]
        (recur (into #{} (remove seen) fresh) seen (merge recs found) (into consts fresh))))))

(defn- with-metas
  "`recs` and every stored record naming one of them by handle, an `exceptWhen`'s rule
  with its exception, to a fixpoint; and `{handle #{meta handle …}}`, who names whom."
  [kb recs]
  (let [get-sx #(p/get-sentex (:records kb) %)]
    (loop [frontier (vec (vals recs)) recs recs named {}]
      (if (empty? frontier)
        [recs named]
        (let [namers (for [sx frontier
                           h  (reads/as-stored-naming-handle (:index kb) (:id sx))
                           :let [m (get-sx h)] :when m]
                       [sx m])
              rules  (keep #(some-> (sx/exceptWhen-rule-handle (:sentence %)) get-sx) frontier)
              named  (reduce (fn [acc [sx m]] (update acc (:id sx) (fnil conj #{}) (:id m)))
                             named namers)
              new    (into {} (comp (remove #(contains? recs (:id %))) (map (juxt :id identity)))
                           (concat (map second namers) rules))]
          (recur (vec (vals new)) (merge recs new) named))))))

(defn- bookkeeping
  "The handles of each of `consts`' own bookkeeping records (`nat/bookkeeping-handles`),
  which the orphan sweep collects once the constant's last use goes."
  [kb consts]
  (into #{} (mapcat #(nat/bookkeeping-handles kb %)) consts))

;; ---- the batch -----------------------------------------------------------

(def ^:private tautology-functors
  "Relations whose `(P x x)` a merge or a copy drops: the closures the engine holds reflexive, whose
  reflexive tuple `assert` refuses or stores as a tautology."
  (into '#{genl genlCx} kb/equality-predicates))

(defn tautology?
  "Has the substitution turned `sentence` into `(P x x)` of a `tautology-functors` relation?"
  [sentence]
  (let [[f a b :as s] (when (seq? sentence) sentence)]
    (and (= 3 (count s)) (some? a) (= a b) (contains? tautology-functors f))))

(defn- restated
  "An entry of `premise-entries` with its affected constants expanded and `smap` applied,
  `:changed?` when the substitution moved it."
  [kb consts smap {:keys [context form] :as e}]
  (let [x   #(nat/expand-expression kb % consts)
        f0  (x form)
        c0  (if (contains? consts context) (x context) context)
        f1  (substitute smap f0)
        c1  (substitute smap c0)]
    (assoc e :new-form f1 :new-context c1 :changed? (or (not= f0 f1) (not= c0 c1)))))

(defn- close-over-names
  "`es` with `:moved` on each changed entry, the handles the batch retracts: the record its
  form states, and each record the form carries beside it (an `exceptWhen`'s rule) that
  `moved?` answers changed.  An entry whose record names a moved handle is marked changed
  and moved too, to a fixpoint, so a meta naming a restated record names the new one."
  [es named moved?]
  (let [head  #(first (:handles %))
        es    (mapv #(cond-> % (:changed? %)
                             (assoc :moved (into [(head %)] (filter moved?) (rest (:handles %)))))
                    es)
        by-h  (into {} (map-indexed #(vector (head %2) %1)) es)]
    (loop [es es todo (into [] (keep-indexed #(when (:changed? %2) %1)) es)]
      (if-let [i (peek todo)]
        (let [ms (into [] (comp (mapcat #(get named %)) (keep by-h) (distinct)
                                (remove #(:changed? (es %))))
                       (:moved (es i)))]
          (recur (reduce (fn [es j] (update es j #(assoc % :changed? true :moved [(head %)])))
                         es ms)
                 (into (pop todo) ms)))
        es))))

(defn batch
  "The `edit!` batch term operation `op` runs over `mapping` (`problems` empty), as
  `{:add [[sentence context opts?] …] :remove [handle …] :restates [[handle …] …]}`,
  `:restates` naming the records each add restates, in step with `:add`.  The records are
  the premises using a mapped term and the metas naming them, each written as
  `premise-entries` writes it, the adds in the originals' assertion order (docs/api.md,
  \"Contract notes: term operations\").  Throws `:nat-map-outside-universe` when a
  `natFormula` premise it reaches is stored outside CxUniverse, and `:unrestatable-sentex`
  when a record to restate has no text form or is inert."
  [kb op mapping]
  (let [froms           (if (= :remove op) (set mapping) (set (keys mapping)))
        smap            (if (= :remove op) {} mapping)
        [found consts]  (reach kb froms)
        _               (when-let [maps (seq (filter #(and (= 'natFormula (first (:sentence %)))
                                                           (not= sx/root-context (:context %))
                                                           (written? kb %))
                                                     (vals found)))]
                          (throw (ex-info (str (count maps) " natFormula premise(s) the operation"
                                               " reaches are stored outside CxUniverse, and a term"
                                               " operation restates a map in CxUniverse only")
                                          {:type    :nat-map-outside-universe
                                           :handles (mapv :id (nm/sort-by-content-key
                                                               (juxt :sentence :context) maps))})))
        [recs named]    (with-metas kb found)
        books           (bookkeeping kb consts)
        written         (into [] (filter #(and (written? kb %) (not (contains? books (:id %)))))
                              (vals recs))
        [entries skipped] (text/premise-entries kb written)
        uses-from       (into froms consts)
        mark            (if (= :remove op)
                          (fn [{:keys [context form] :as e}]
                            (assoc e :changed? (or (uses? uses-from form)
                                                   (contains? uses-from context))))
                          #(restated kb consts smap %))
        ;; a record an entry carries beside its own is retracted only when its own entry
        ;; changes, so an `exceptWhen` whose query alone uses the term keeps its rule
        moved?          #(boolean (some->> (recs %) vector (text/premise-entries kb) ffirst
                                           mark :changed?))
        ;; a record with no text form is an entry of its own handle, which a remove
        ;; retracts and every other operation refuses
        lone            (mapv #(hash-map :handles [(:id %)] :lone? true
                                         :changed? (or (uses? uses-from (sx/sentence-of %))
                                                       (contains? uses-from (:context %))))
                              skipped)
        es              (filterv :changed? (close-over-names (into (mapv mark entries) lone)
                                                             named moved?))]
    (when-let [bad (seq (when-not (= :remove op)
                          (for [e es h (:moved e) :let [sx (p/get-sentex (:records kb) h)]
                                :when (or (:lone? e) (nil? (:strength sx)))]
                            sx)))]
      (throw (ex-info (str (count bad) " stored sentex(es) using the term cannot be restated by"
                           " an edit: a sentence with no text form or an inert sentex; retract"
                           " them first")
                      {:type :unrestatable-sentex
                       :handles (vec (distinct (map :id bad)))})))
    (if (= :remove op)
      {:add [] :remove (into [] (comp (mapcat :moved) (distinct)) es) :restates []}
      (let [es    (sort-by #(reduce min (:handles %)) es)
            adds  (remove #(tautology? (first (text/peel-form (:new-form %)))) es)]
        {:add      (mapv (fn [{:keys [new-form new-context]}]
                           (let [[s o] (text/peel-form new-form)]
                             (cond-> [s new-context] o (conj o))))
                         adds)
         :remove   (if (= :copy op) [] (into [] (comp (mapcat :moved) (distinct)) es))
         :restates (mapv :moved adds)}))))
