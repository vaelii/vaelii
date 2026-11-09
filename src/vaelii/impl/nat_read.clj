;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.nat-read
  "The read-mode reify of a ground NAT: the reserved namespaces, the `reifiable_function`
  mark, the `natFormula` and correspondence lookups a reader or writer in a context
  resolves an application through, and the walk both reify modes share.  Below `provers`,
  so the belief projection reifies a proposition in the agent's context.  See docs/nat.md."
  (:require [vaelii.impl.decide.tuple :as tuple]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.wiring :as wiring]))

(def nat-namespace
  "Reserved namespace of an object reified constant, which a ground application of a
  `(reifiable_function F)` in argument position mints."
  "nat")

(def context-namespace
  "Reserved namespace of a context reified constant, which a ground application in a
  sentex's context slot mints, whatever is declared about its head (docs/context-nat.md)."
  "cx")

(def universal-context
  "The context every NAT bookkeeping fact is stored in."
  sx/root-context)

(def no-match
  "The reserved constant a read-mode reify resolves a never-minted NAT to (`sx/no-match`)."
  sx/no-match)

(defn reified-nat-symbol?
  "True iff `term` is a reified constant: a symbol in `nat/` or `cx/`."
  [term]
  (nm/reified-constant? term))

(defn reified-context-symbol?
  "True iff `term` is a reified context constant, a symbol in `cx/`."
  [term]
  (and (symbol? term) (= context-namespace (namespace term))))

(defn reified-object-symbol?
  "True iff `term` is a reified object constant, a symbol in `nat/`."
  [term]
  (and (symbol? term) (= nat-namespace (namespace term))))

(defn computed-genlCx-edge?
  "Is `sx` a `genlCx` edge the structural producer computed: not a premise, and every
  support under the `contextArgSubrelation` informant (docs/context-nat.md, Orphan
  collection)?  Belief is not read.  The orphan sweep reads such an edge as the engine's
  own wiring, and a declaration's sweep over stored facts draws nothing from it
  (`special/entail-existing`)."
  [kb sx]
  (let [s (:sentence sx)]
    (and (= 'genlCx (nm/functor s))
         (= universal-context (:context sx))
         (let [tms (reasoning/tms kb)
               h   (:id sx)
               js  (jtms/supports tms h)]
           (and (not (jtms/premise? tms h))
                (seq js)
                (every? #(= 'contextArgSubrelation (:informant (jtms/justification tms %)))
                        js))))))

(defn any-reifiable-functions?
  "Does the KB declare a `reifiable_function`?  One in-memory taxonomy prop read.  False
  means no sentence holds a reifiable NAT, and every reify pass returns its input."
  [kb]
  (boolean (seq (tax/props (reasoning/taxonomy kb) :reifiable))))

(def ^:dynamic *withheld*
  "The `reifiable_function` functions whose ground applications stay as written while
  bound: the ones a reader does not believe the mark of (`withheld-at`), so the reconcile
  stores, and a read looks up, the spelling that reader reads (`chain/reconcile-reified!`)."
  #{})

(defn reifiable-function?
  "True iff `head` reifies its ground applications in argument position: a believed
  `(reifiable_function head)`, and `head` not in `*withheld*`.  The mark is read
  unscoped; a reader that does not believe it binds `*withheld*`."
  [kb head]
  (and (symbol? head)
       (not (reified-nat-symbol? head))
       (not (contains? *withheld* head))
       (tax/has-prop? (reasoning/taxonomy kb) :reifiable head)))

(defn reifiable-entries
  "`{[:prop :reifiable f] {handle context}}`, the `reifiable_function` mark of `f` and its
  supporters, in `res/mark-entries`' shape."
  [kb f]
  (let [k [:prop :reifiable f]]
    {k (tax/supporters (reasoning/taxonomy kb) k)}))

(defn split-reifiable?
  "Does some reader not believe `f`'s stored `reifiable_function` mark
  (`res/uniform-marks?`)?"
  [kb f]
  (let [e (reifiable-entries kb f)]
    (boolean (and (seq (val (first e))) (not (res/uniform-marks? kb e))))))

(defn withheld-at
  "The reifiable functions `reader` does not believe the mark of while another reader
  does, as a set: what `*withheld*` holds to spell a sentence as `reader` reads it.
  Empty for a variable or nil `reader`."
  [kb reader]
  (if (and (symbol? reader) (not (sx/variable? reader)))
    (into #{} (filter #(and (split-reifiable? kb %)
                            (empty? (res/entries-at kb (reifiable-entries kb %) reader))))
          (tax/props (reasoning/taxonomy kb) :reifiable))
    #{}))

(def ^:dynamic *sorted-by*
  "`{f entries}`: while bound, `sorted-expression` sorts an application of each key `f` by
  the `symmetric` and commuting marks of `f` its `entries` list (`res/mark-entries`' keys)
  and no others, the marks one reader believes (`sorted-by-at`), so the reconcile stores,
  and a read looks up, the constant that reader names the application by."
  {})

(defn sorted-by-at
  "The `*sorted-by*` binding that names an application as `reader` names it: each
  reifiable function some reader does not believe a permuting mark of
  (`res/split-mark-entries`), with the marks `reader` believes.  Empty for a variable or
  nil `reader`.  The `reifiable_function` mark is read unscoped, a superset of the
  functions `reader` names an application of, and a function it does not believe
  reifiable is withheld (`withheld-at`) before its marks are read."
  [kb reader]
  (if (and (symbol? reader) (not (sx/variable? reader)))
    (into {} (keep #(when-let [e (res/split-mark-entries kb %)] [% (res/entries-at kb e reader)]))
          (tax/props (reasoning/taxonomy kb) :reifiable))
    {}))

(defn reifiable-ground-nat?
  "True iff `form` is a ground `(F …)` whose head is a reifiable function: a NAT the
  argument-position reify mints to a `nat/` constant."
  [kb form]
  ;; `sequential?`: reification runs before `canon`, which makes `[F a]` and `(F a)` one
  ;; sentence, so both spellings reify
  (and (sequential? form)
       (seq form)
       (reifiable-function? kb (first form))
       (sx/ground-term? form)))

(defn in-namespace?
  "Does the term `k` a `natFormula` map names belong to reify namespace `ns`?  A context
  slot's constant is a context (`nm/context?`), and an argument's is any other term."
  [ns k]
  (= (= context-namespace ns) (nm/context? k)))

(defn any-result-declarations?
  "Does the KB declare any `result`, `genlResult` or `resultArg`?  Three O(1) functor
  counts."
  [kb]
  (let [ix (:index kb)]
    (or (pos? (reads/stored-count-with-functor ix 'result))
        (pos? (reads/stored-count-with-functor ix 'genlResult))
        (pos? (reads/stored-count-with-functor ix 'resultArg)))))

(defn visible-result-targets
  "The distinct arg2s of the believed `(<pred> head ?t)` facts visible from `context`
  (`res/matches-visible`), as a check and a goal read a declaration (docs/nat.md, Typing
  an application that is never minted)."
  [kb pred head context]
  (->> (res/matches-visible kb (list pred head '?t) context)
       (keep #(get (nth % 1) '?t))
       distinct))

(defn result-arg-types
  "The symbols application `E` holds at the positions `ns` its function's `(resultArg F
  n)` declarations name.  A position `E` lacks, or a non-symbol there, names no type."
  [E ns]
  (let [as (vec (rest E))]
    (distinct
     (for [n     ns
           :let  [t (when (and (integer? n) (<= 1 n (count as))) (nth as (dec n)))]
           :when (and (symbol? t) (not (sx/variable? t)))]
       t))))

(defn visible-result-types
  "Types `T` with a `(result head T)` visible from `context`: what an application of
  `head` is an instance of.  Given an application `(head a…)` in place of `head`, adds the
  argument at each position a visible `(resultArg head n)` declares, behind one O(1)
  functor count."
  [kb head context]
  (let [f  (if (sequential? head) (first head) head)
        rs (visible-result-targets kb 'result f context)]
    (if (and (sequential? head) (pos? (reads/stored-count-with-functor (:index kb) 'resultArg)))
      (distinct (concat rs (result-arg-types head (visible-result-targets kb 'resultArg f context))))
      rs)))

(defn- reader-of
  "The context a NAT lookup reads from: `context`, or CxUniverse when nil."
  [context]
  (or context universal-context))

(defn- class-spellings
  "Every spelling of the ground NAT expression `E` with each symbol argument replaced by a
  member of its equality class as the merges `visible?` admits group it: one spelling,
  `E`, when no argument has merged."
  [kb E visible?]
  (let [tx  (reasoning/taxonomy kb)
        cls (fn [a]
              (cond (not (and (symbol? a) (tax/merged? tx a))) [a]
                    (tax/class-fully-visible? tx a visible?)    (tax/equiv-class tx a)
                    :else                                       (first (tax/scoped-class tx a visible?))))]
    (map #(apply list %)
         (reduce (fn [acc a] (for [s acc m (cls a)] (conj s m))) [[(first E)]] (rest E)))))

(defn- permuting-marks
  "The `symmetric` and commuting marks of taxonomy `tax`, in the shape `sx/permute-args`
  and `sx/every-order` take: those of a key of `*sorted-by*` the entries it lists, and
  every other function's read unscoped, since a constant's name is a stored key every
  reader shares."
  [tax]
  (let [by *sorted-by*]
    {:symmetric? #(if-let [e (get by %)]
                    (contains? e [:prop :symmetric %])
                    (tax/has-prop? tax :symmetric %))
     :groups-of  (fn [g _] (if-let [e (get by g)]
                             (into #{} (filter #(contains? e [:commuting g %])) (tax/commuting-groups tax g))
                             (tax/commuting-groups tax g)))}))

(defn sorted-expression
  "Ground application `E` with its own arguments in the order its `symmetric` and
  commuting marks give it (`sx/permute-args`, `permuting-marks`): the expression a reified
  constant is named by and found under, so both spellings of a commuted application name
  one constant.  The associative, idempotent and meet arms are not applied, since they can
  collapse an application to one argument."
  [kb E]
  (let [tax (reasoning/taxonomy kb)
        f   (first E)]
    (if (or (tax/has-prop? tax :symmetric f) (seq (tax/commuting-groups tax f)))
      (sx/permute-args E (permuting-marks tax))
      E)))

(defn- map-rows
  "The `pred` rows (`natFormula` or a compound `rewriteOf`) a reader in `context` reads
  as naming the ground NAT expression `E` at argument 2: a row whose expression,
  normalized under `context`'s merges, is `E`'s normal form, stated (a premise,
  superseded or not) or seen and believed from `context`.  A stated `natFormula` row
  answers in every context, a stated `rewriteOf` row where `context` sees its context or
  `context` is a `?var`, and a migration twin where its merge is visible (docs/nat.md, A
  NAT resolves under the reader's merges).  Stated rows are probed for each
  `class-spellings` spelling, a `rewriteOf` row in each `sx/every-order`, compared sorted."
  [kb pred E context]
  (let [ctx      (reader-of context)
        tx       (reasoning/taxonomy kb)
        tms      (reasoning/tms kb)
        visible? (res/visible-supporter-fn kb ctx)
        rw?      (= 'rewriteOf pred)
        norm     #(cond->> (res/normal-form kb % visible?) rw? (sorted-expression kb))
        orders   (if rw? #(sx/every-order % (permuting-marks tx)) vector)
        N        (norm E)
        rows     (fn [S] (->> (reads/as-stored-with-args (:index kb) pred {2 S})
                              (keep #(p/get-sentex (:records kb) %))
                              (filter #(= S (nth (:sentence %) 2 nil)))))
        stated?  #(and (jtms/premise? tms (:id %)) (jtms/network-in? tms (:id %))
                       (or (= 'natFormula pred) (nil? visible?) (tax/sees? tx ctx (:context %))))
        seen?    #(and (tax/sees? tx ctx (:context %)) (jtms/in? tms (:id %)))]
    (distinct
     (concat (filter #(or (stated? %) (seen? %)) (mapcat rows (orders N)))
             (for [C     (class-spellings kb E visible?)
                   S     (orders C)
                   :when (not= S N)
                   sx    (rows S)
                   :when (and (stated? sx) (= N (norm S)))]
               sx)))))

(defn dedup-constant
  "The existing reified constant for the ground NAT expression `E` in reify namespace `ns`
  (default `nat/`) for a reader in `context` (CxUniverse when nil), or nil: the
  `natFormula` rows `map-rows` reads.  Where several constants map `E` in one namespace
  (an import restores what the dump held, or a merge the reader sees joins two
  expressions), the lexicographically smallest, the survivor `group-collisions` elects.
  With `write?`, a `nat/` expression answers only a reified constant, never a term a
  merge's twin of the map names: a write names the application's own constant."
  ([kb E] (dedup-constant kb E nat-namespace nil))
  ([kb E ns context] (dedup-constant kb E ns context false))
  ([kb E ns context write?]
   (->> (map-rows kb 'natFormula E context)
        (map #(second (:sentence %)))
        (filter #(and (in-namespace? ns %)
                      (or (not write?) (= context-namespace ns) (reified-object-symbol? %))))
        sort
        first)))

(defn rewrite-target
  "The real term `T` a `(rewriteOf T E)` a reader in `context` (CxUniverse when nil)
  reads (`map-rows`) reifies NAT expression `E` to, spelled under `context`'s merges, or
  nil.  Nil when the declarations name more than one target (docs/nat.md, The
  corresponding predicate), and when the one `T` lies outside reify namespace `ns`
  (`in-namespace?`).  Every row `map-rows` reads is a stored `rewriteOf`, so a KB storing
  none answers nil off one functor count, before `E` is normalized and spelled."
  [kb E ns context]
  (when (pos? (reads/stored-count-with-functor (:index kb) 'rewriteOf))
    (let [ts (into #{} (comp (map #(second (:sentence %)))
                             (map #(res/normal-form kb % (res/visible-supporter-fn kb (reader-of context))))
                             (distinct)
                             (take 2))
                   (map-rows kb 'rewriteOf E context))]
      (when (= 1 (count ts))
        (let [t (first ts)]
          (when (in-namespace? ns t) t))))))

(defn- sole-value
  "`[value facts]` when the corresponding facts visible from `context` name exactly one
  value for `E` (`res/corresponding-values`, through `cor` where the caller holds it),
  else nil."
  ([kb E context] (sole-value kb E nil context))
  ([kb E cor context]
   (let [vs (if cor (res/corresponding-values kb E cor context) (res/corresponding-values kb E context))]
     (when (= 1 (count vs)) (first vs)))))

(defn- computed-value
  "The one ground value the prover registry binds at position `pos` of `(pr a… ?v)` for
  the ground NAT expression `E` = `(F a…)`, solved in `context`, or nil."
  [kb E [pr pos] context]
  (let [ctx (if (sx/variable? context) universal-context context)
        vs  (into [] (comp (map #(get % '?v)) (filter sx/ground-term?) (distinct) (take 2))
                  (wiring/solve-goal kb (apply list pr (res/insert-at (rest E) pos '?v)) ctx))]
    (when (= 1 (count vs)) (first vs))))

(defn correspondence-value
  "The term a `:monotonic` corresponding fact visible from `context` (CxUniverse when nil)
  names as the value of the ground NAT expression `E`, spelled under `context`'s merges,
  when the visible facts name that one value and no other, or nil.  Where the
  corresponding predicate is `not_assertible`, a mark read KB-wide as `assert`'s refusal
  reads it, the value is the prover registry's (`computed-value`).  With `write?`, only
  that prover value: a write names the application's own constant, which a stored value
  reaches through `chain/sync-values!`'s merge (docs/nat.md, The corresponding predicate)."
  ([kb E context] (correspondence-value kb E context false))
  ([kb E context write?]
   (let [ctx (reader-of context)]
     (when-let [[pr :as cor] (res/correspondence-of kb (first E) (count (rest E)) ctx)]
       (cond
         (tax/has-prop? (reasoning/taxonomy kb) :not-assertible pr) (computed-value kb E cor ctx)
         write? nil
         :else (when-let [[v hs] (sole-value kb E cor ctx)]
                 (let [tms (reasoning/tms kb)]
                   (when (some #(tuple/monotonic-member? tms %) hs) v))))))))

(defn reify-in
  "Reify every reifiable ground NAT subterm of literal/sentence `s`, calling `nat-fn` (a
  `(fn [kb form])`) at each one, and `head-fn` (default `nat-fn`) at a literal's head that
  is one; each returns the NAT's term, having reified its nested NAT arguments itself.  A
  symbol head, a quoting-predicate argument and a `modal_predicate`'s proposition
  (`res/attitude-application?`) stay opaque.  The modal mark is read KB-wide, once per
  walk: whether an argument is a mention is a fact about the sentence
  (`tax/mention-marks`).  A vector is descended element by element (docs/nat.md, Write
  path)."
  ([kb s nat-fn] (reify-in kb s nat-fn nat-fn))
  ([kb s nat-fn head-fn]
   (let [modal (:modal (tax/mention-marks (reasoning/taxonomy kb)))]
     (letfn [(walk [s]
               (cond
                 (reifiable-ground-nat? kb s) (nat-fn kb s)
                 (vector? s) (mapv walk s)
                 (and (seq? s) (seq s))
                 (cond
                   (contains? res/nat-quoting-predicates (first s)) s
                   (res/attitude-application? modal s) (list (first s) (walk (second s)) (nth s 2))
                   :else (apply list (head (first s)) (map walk (rest s))))
                 :else s))
             (head [h] (if (reifiable-ground-nat? kb h) (head-fn kb h) h))]
       (walk s)))))

(defn existing-term
  "The term ground NAT expression `E` already resolves to in reify namespace `ns` for a
  reader in `context`, or nil: a `rewriteOf` target, the value its corresponding
  predicate names where `context` reads it (`correspondence-value`), else the constant
  `dedup-constant` finds.  With `write?`, the term a write in `context` stores: the
  value and the constant as `correspondence-value` and `dedup-constant` read them for a
  write.  A context slot (`cx/`) takes no correspondence value, which names an object."
  ([kb E ns context] (existing-term kb E ns context false))
  ([kb E ns context write?]
   (if (= context-namespace ns)
     (or (rewrite-target kb E ns context) (dedup-constant kb E ns context))
     (or (rewrite-target kb E ns context) (correspondence-value kb E context write?)
         (dedup-constant kb E ns context write?)))))

(defn reify-nat-for-read
  "Read-mode leaf: reify nested NAT arguments, then resolve the expression, in its
  `sorted-expression` order, to its existing term in reify namespace `ns` for a reader in
  `context` (`existing-term`, with `write?` as a write in `context` stores it), or to
  `no-match`.  Never mints.  A quoting function's argument stays opaque, as
  `reify-or-mint-nat` holds it."
  ([kb form ns context] (reify-nat-for-read kb form ns context false))
  ([kb form ns context write?]
   (let [E (if (sx/quoting-functor? (first form))
             (apply list form)
             (sorted-expression
              kb (apply list (first form)
                        (map #(if (reifiable-ground-nat? kb %)
                                (reify-nat-for-read kb % nat-namespace context write?)
                                %)
                             (rest form)))))]
     (or (existing-term kb E ns context write?) no-match))))

(defn- read-leaf
  "`reify-in`'s leaf for a read in `context`: the existing term, else the one value the
  corresponding facts visible from `context` name for an application nothing minted, or
  `no-match`.  With `write?`, the term a write in `context` stores, or `no-match`.  A
  never-minted quoting application stays as written: a mention names its own syntax."
  [context write?]
  (fn [kb form]
    (let [k (reify-nat-for-read kb form nat-namespace context write?)]
      (cond
        (not= no-match k)                    k
        (sx/quoting-functor? (first form))   form
        write?                               k
        :else (or (when (res/any-corresponding-predicates? kb)
                    (first (sole-value kb (apply list (first form)
                                                 (map #(if (reifiable-ground-nat? kb %)
                                                         (reify-nat-for-read kb % nat-namespace context)
                                                         %)
                                                      (rest form)))
                                       context)))
                  k)))))

(defn reify-existing
  "Reify every reifiable ground NAT subterm of `sentence` that has an existing term for a
  reader in `context` (CxUniverse when nil) to that term, and leave every other one as
  written.  With `write?`, the existing term a write in `context` stores
  (`existing-term`).  Never mints.  `vaelii.core/check` and a firing's conclusion read a
  sentence through this with `write?` (docs/nat.md, Typing an application that is never
  minted)."
  ([kb sentence context] (reify-existing kb sentence context false))
  ([kb sentence context write?]
   (if (any-reifiable-functions? kb)
     (reify-in kb sentence (fn [kb form]
                             (let [k (reify-nat-for-read kb form nat-namespace context write?)]
                               (if (= no-match k) form k))))
     sentence)))

(defn maybe-reify-for-read
  "Reify every reifiable ground NAT subterm of a query `sentence` to its existing term for
  a reader in `context` (CxUniverse when nil), never minting; a never-minted NAT resolves
  to `no-match`, except a quoting application, which stays as written.  With `write?`,
  each resolves to the term a write in `context` stores (`read-leaf`), the reading a
  lookup of a stored sentex takes.  An application of a function `context` does not
  believe reifiable stays as written (`withheld-at`), and an application of a function
  whose permuting marks some reader does not believe is sorted by the ones `context`
  believes (`sorted-by-at`)."
  ([kb sentence context] (maybe-reify-for-read kb sentence context false))
  ([kb sentence context write?]
   (if (any-reifiable-functions? kb)
     (binding [*withheld* (withheld-at kb context) *sorted-by* (sorted-by-at kb context)]
       (reify-in kb sentence (read-leaf context write?)))
     sentence)))

(defn- has-no-match?
  "Does `form` hold the `no-match` sentinel in a list or vector, at any nesting?"
  [form]
  (or (= form no-match)
      (and (or (seq? form) (vector? form))
           (boolean (some has-no-match? form)))))

(defn resolve-for-read
  "The read-mode reify of `sentence` for a reader in `context` (`maybe-reify-for-read`,
  with `write?` as given) when every reifiable NAT in it has a stored term, else nil."
  ([kb sentence context] (resolve-for-read kb sentence context false))
  ([kb sentence context write?]
   (let [r (maybe-reify-for-read kb sentence context write?)]
     (when-not (has-no-match? r) r))))

;; ---- the constants a value can reach -------------------------------------
;; docs/nat.md, The corresponding predicate.  The queue `chain/sync-values!` drains.

(def ^:dynamic *minting?*
  "True while `nat/mint-nat!` stores a constant's bookkeeping: its asserts queue nothing,
  and the mint queues the constant once its bookkeeping is stored."
  false)

(defn values-reachable?
  "Can a corresponding fact reach a minted constant: does the KB declare a reifiable
  function (`any-reifiable-functions?`) and store a correspondence declaration and a
  `natFormula` map?  One set read, then two O(1) functor counts."
  [kb]
  (and (any-reifiable-functions? kb)
       (res/any-corresponding-predicates? kb)
       (pos? (reads/stored-count-with-functor (:index kb) 'natFormula))))

(defn rewrites-reachable?
  "Can a compound `rewriteOf` reach a minted constant: does the KB declare a reifiable
  function and store a `rewriteOf` and a `natFormula` map?  One set read, then two O(1)
  functor counts."
  [kb]
  (and (any-reifiable-functions? kb)
       (pos? (reads/stored-count-with-functor (:index kb) 'rewriteOf))
       (pos? (reads/stored-count-with-functor (:index kb) 'natFormula))))

(defn- declared-function?
  "Does a stored correspondence declaration declare function `f`?"
  [kb f]
  (pos? (count (reads/as-stored-with-args (:index kb) res/correspondence-predicate {1 f}))))

(defn- rewritten?
  "Does a stored compound `(rewriteOf T E)` name the expression `E`?"
  [kb E]
  (pos? (count (reads/as-stored-with-args (:index kb) 'rewriteOf {2 E}))))

(defn- valued-constants
  "The reified object constants `sentence` names whose function a stored correspondence
  declaration declares, when `corr?`, or whose expression a stored compound `rewriteOf`
  names, when `rw?` (a delay) holds.  Empty with no walk of `sentence` when neither does."
  [kb sentence corr? rw?]
  (if-not (or corr? @rw?)
    #{}
    (into #{} (filter #(and (reified-object-symbol? %)
                            (when-let [E (res/minted-expression kb %)]
                              (or (and corr? (declared-function? kb (first E)))
                                  (and @rw? (rewritten? kb E))))))
          (tree-seq sequential? seq sentence))))

(defn fact-constants
  "The constants minted for the applications the positive literal `sentence` names a value
  of under each stored correspondence declaration of its functor, read off the map
  (`dedup-constant`)."
  [kb sentence]
  (when (and (seq? sentence) (symbol? (first sentence)) (not= 'not (first sentence)))
    (let [recs (:records kb)
          args (vec (rest sentence))
          m    (dec (count args))]
      (into #{}
            (keep (fn [h]
                    (let [s   (:sentence (p/get-sentex recs h))
                          f   (second s)
                          pos (res/stated-position s)]
                      (when (and pos (<= 0 m) (<= pos (inc m)))
                        (dedup-constant kb (apply list f (concat (subvec args 0 (dec pos)) (subvec args pos)))
                                        nat-namespace nil)))))
            (reads/as-stored-with-args (:index kb) res/correspondence-predicate {2 (first sentence)})))))

(defn- declared-predicates
  "The predicates the stored correspondence declarations name."
  [kb]
  (let [recs (:records kb)]
    (into #{} (comp (keep #(p/get-sentex recs %)) (keep #(nth (:sentence %) 2 nil)) (filter symbol?))
          (reads/as-stored-with-args (:index kb) res/correspondence-predicate {}))))

(defn named-values-reachable?
  "Does the KB store rewriteOf rows: the coarse named-application presence check."
  [kb]
  (pos? (reads/stored-count-with-functor (:index kb) 'rewriteOf)))

(defn- named-value-events
  "The named targets affected by these uses, compound rewrites or function declarations."
  [kb sentences]
  (when (or (named-values-reachable? kb)
            (some #(and (seq? %) (= 'rewriteOf (first %)) (seq? (nth % 2 nil))) sentences))
    (let [idx (:index kb)
          recs (:records kb)
          use-terms (fn [form]
                      (loop [todo (vec (filter symbol? (tree-seq sequential? seq form))), seen #{}]
                        (if-let [term (peek todo)]
                          (if (contains? seen term)
                            (recur (pop todo) seen)
                            (let [expressions (keep #(some-> (p/get-sentex recs %) :sentence (nth 2 nil))
                                                    (reads/as-stored-with-args idx 'natFormula {1 term}))]
                              (recur (into (pop todo) (filter symbol? (mapcat #(tree-seq sequential? seq %) expressions)))
                                     (conj seen term))))
                          seen)))
          of-function (fn [f]
                        (into #{} (comp (keep #(p/get-sentex recs %))
                                        (keep #(let [[p t e] (:sentence %)]
                                                 (when (and (= 'rewriteOf p) (symbol? t) (seq? e)) t))))
                              (mapcat #(reads/as-stored-with-term idx %)
                                      (tax/equiv-class (reasoning/taxonomy kb) f))))]
      (into #{}
            (mapcat (fn [s]
                      (let [direct (when (and (seq? s) (= 'rewriteOf (first s))
                                              (symbol? (second s)) (seq? (nth s 2 nil)))
                                     (cons (second s)
                                           (of-function (first (nth s 2)))))
                            declared (when (and (seq? s)
                                                (contains? '#{result genlResult reifiable_function functionCorrespondingPredicate
                                                              symmetric commutative commutativeInArgs commutativeInArgAndRest} (first s)))
                                       (of-function (second s)))
                            merged (when (and (seq? s) (contains? '#{equals sameAs rewriteOf} (first s)))
                                     (into #{} (comp (mapcat #(reads/as-stored-with-term idx %))
                                                     (keep #(p/get-sentex recs %))
                                                     (keep #(let [[p t e] (:sentence %)]
                                                              (when (and (= 'rewriteOf p) (symbol? t) (seq? e)) t))))
                                           (filter symbol? (rest s))))
                            used (filter #(seq (reads/as-stored-with-args idx 'rewriteOf {1 %}))
                                         (use-terms s))]
                        (map #(vector :named-valued %) (concat direct declared merged used)))))
            sentences))))

(defn note-values
  "Queue affected named targets (`:named-valued`) and minted constants on `:respell`:
  `[:valued-fn f]` for a correspondence declaration of `f`, `[:valued k]` for
  each constant a corresponding fact names a value of (`fact-constants`) and for each
  constant minted for the expression of a compound `rewriteOf`, and with `uses?` for each
  constant a sentence names whose function is declared or whose expression a compound
  `rewriteOf` names (`valued-constants`).  Answers whether it queued anything.  The
  correspondence arms are behind `values-reachable?`, a use's `rewriteOf` arm behind
  `rewrites-reachable?`, read once and only for a use naming a reified constant; nothing
  while `*minting?*`."
  [kb sentences uses?]
  (when-not *minting?*
    (let [corr? (values-reachable? kb)
          rw?   (delay (rewrites-reachable? kb))
          preds (delay (declared-predicates kb))
          es    (into (or (named-value-events kb sentences) #{})
                      (mapcat (fn [s]
                                (cond
                                  (not (seq? s)) nil
                                  (= res/correspondence-predicate (first s))
                                  (when (and corr? (symbol? (second s))) [[:valued-fn (second s)]])
                                  (and (= 'rewriteOf (first s)) (seq? (nth s 2 nil)))
                                  (keep #(let [k (some-> (p/get-sentex (:records kb) %) :sentence second)]
                                           (when (reified-object-symbol? k) [:valued k]))
                                        (reads/as-stored-with-args (:index kb) 'natFormula {2 (nth s 2)}))
                                  :else
                                  (map #(vector :valued %)
                                       (into (if (and corr? (contains? @preds (first s))) (fact-constants kb s) #{})
                                             (when uses? (valued-constants kb s corr? rw?)))))))
                      sentences)]
      (when (seq es)
        (swap! (reasoning/respell kb) into es)
        true))))
