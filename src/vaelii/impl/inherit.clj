;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.inherit
  "**Argument-position preservation**: `(transitiveInArg P n R)` and
  `(transitiveInArgInverse P n R)` license a stored claim about the term at argument `n`
  of `P` for every term `R`'s reach names from it.  This namespace reads the declared
  positions and their reaches, finds the claims bearing on a ground goal and decides
  which a more specific one undercuts, names what an inherited reading rests on for a
  justification or a nogood, and answers which rules and stored facts a sentence moves.
  See docs/inherit.md."
  (:require [vaelii.impl.budget :as budget]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.except :as exc]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.strength :as st]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(def declarations
  "The two declaration functors, mapped to the `along?` flag of the walk that serves
  them: true licenses `a` from `w` when `(R w a)` (along `R`'s arrow, `transitiveInArg`),
  false when `(R a w)` (against it, `transitiveInArgInverse`)."
  '{transitiveInArgInverse false, transitiveInArg true})

;; ---- one question, one set of closure reads ------------------------------

(def ^:dynamic *memo*
  "A per-question cache, an atom of `{[:positions pred context concluding] -> …,
  [:reach rel along? x context] -> set, …}`, or nil for no memoization.  A question
  moves no belief, so the memo needs no invalidation (docs/inherit.md, \"What one
  question costs\")."
  nil)

(defmacro with-memo
  "Answers `body` under a memo, reusing the enclosing one when there is one.  `body` must
  be eager: a lazy seq handed back realizes after the binding pops, and walks every
  `positions` and `reach` read again with the same answers (`laziness_test`)."
  [& body]
  `(binding [*memo* (or *memo* (atom {}))] ~@body))

(defn- memoized [k f]
  (if-let [m *memo*]
    (if (contains? @m k)
      (get @m k)
      (let [v (f)] (swap! m assoc k v) v))
    (f)))

(def virtual-relations
  "The relations `witness-terms` reads from the engine's cached closures
  (`tax/closure-relations`) rather than from stored `(R a b)` facts.  A declaration along
  any other relation needs `(transitive R)` (`wff/arg-preserving-problems`,
  `usable-relation?`)."
  tax/closure-relations)

;; ---- the declared positions ---------------------------------------------

(defn usable-relation?
  "May a declaration's `R` be walked from `context`?  True for a `virtual-relations`
  member, and for an `R` whose `(transitive R)` `context` sees.  Read at use, so
  retracting `(transitive R)` withdraws the reach (docs/inherit.md, \"The transitivity
  has to have been declared\")."
  [tax rel context]
  (boolean (or (contains? virtual-relations rel)
               (tax/has-prop? tax :transitive rel context))))

(def ^:private declaration-functors
  "`declarations`' keys, held rather than re-`keys`-ed: `declared-anywhere?` runs on
  every `applicable?` of a preservation-aware prover."
  (vec (keys declarations)))

(defn declared-about?
  "Could any stored declaration name `pred`?  The declaration functors' extents are
  counted, and a non-empty one is intersected with the argument root at position 1,
  where a declaration's predicate sits.  A presence check, neither belief-filtered nor
  context-scoped: true says only that `positions` is worth reading, and false is exact.
  `recheck/cross-argument-predicate?` reads it as a conservative test
  (docs/inherit.md, \"Reading it back\")."
  [kb pred]
  (let [idx (:index kb)]
    (boolean
     (some (fn [f]
             (and (pos? (reads/stored-count-with-functor idx f))
                  (seq (reads/as-stored-with-args idx f {1 pred}))))
           declaration-functors))))

(def ^:dynamic *concluding*
  "The consequent predicate of the forward rule whose antecedent is being joined, or nil.
  `positions` leaves out the self relation of a `pred` the rule concludes on or below
  (`chain/walks-its-own-conclusion?` draws the same line for the transitive walk): such a
  rule stores its conclusions inside the closure the self relation walks."
  nil)

(defn- self-positions
  "The self relation of a binary `pred` declared `(transitive pred)` visible from
  `context`: `pred` itself at each position 1 or 2 in `ns`, along its own arrow at 2 and
  against it at 1, since `(P a w)` and `(P w b)` compose to `(P a b)`.  `:self?` marks
  them, and they carry no `:handle`: the composition rests on `(transitive pred)` and the
  edges, which `move-supports` names.  Empty under `*concluding*` on `pred` or below it;
  that `genls` read is unscoped for `chain/walks-its-own-conclusion?`'s reason, a property
  of the rule and not of one reader."
  [kb pred ns context]
  (let [tx (reasoning/taxonomy kb)]
    (when (and (not (contains? virtual-relations pred))
               (tax/has-prop? tx :transitive pred context)
               (not (when-let [c *concluding*] (contains? (tax/genls-global tx c) pred))))
      (for [n (sort (distinct ns)) :when (<= n 2)]
        {:n n :rel pred :along? (= 2 n) :self? true}))))

(defn positions
  "`[{:n :rel :along? :handle :in} …]`: the preserved argument positions declared for
  `pred` visible from `context` whose relation `usable-relation?` admits, and the self
  relation (`self-positions`) at each of them.  Empty when `pred` inherits nothing.
  Several declarations at one position stay apart, since their reaches compose (`reach`).
  `:handle` is the declaration's, which `supports-for` names; `:in` is its asserting
  context, on which `move-supports` orders two statements of one declaration.  Read only
  past `declared-about?`; realized, and memoized on `[pred context *concluding*]`."
  [kb pred context]
  (when (and (symbol? pred) (declared-about? kb pred))
    (memoized [:positions pred context *concluding*]
              (fn []
                (let [ds (vec (for [[f along?] declarations
                                    [h b] (res/matches-visible kb (list f pred '?n '?rel) context)
                                    :let  [n (get b '?n) rel (get b '?rel)]
                                    :when (and (integer? n) (pos? n) (symbol? rel)
                                               (usable-relation? (reasoning/taxonomy kb) rel context))]
                                {:n n :rel rel :along? along? :handle h
                                 :in (:context (p/get-sentex (:records kb) h))}))]
                  (into ds
                        (remove (fn [{:keys [n along?]}]
                                  (some #(and (= n (:n %)) (= pred (:rel %)) (= along? (:along? %))) ds)))
                        (self-positions kb pred (map :n ds) context)))))))

(defn declarations-exist?
  "Does this KB store any declaration?  One set-cardinality read per declaration
  functor, neither belief-filtered nor context-scoped, so false is exact.
  `chain/preserving-antecedent?` and `declaration-index` read this presence check first."
  [kb]
  (let [idx (:index kb)]
    (boolean (some #(pos? (reads/stored-count-with-functor idx %)) declaration-functors))))

(defn declared
  "Every stored declaration's `[P R]` pair, read off the declaration functors' extents
  with no context scope and no belief filter: the callers (`special`'s exception
  re-checks, `declaration-index`) are triggers, which must over-select.  A negated
  declaration, or one of another arity, drops out on its shape.  One set-cardinality
  read per functor, and a record fetch per stored declaration."
  [kb]
  (let [recs (:records kb) idx (:index kb)]
    (into #{}
          (comp (filter #(pos? (reads/stored-count-with-functor idx %)))
                (mapcat #(reads/as-stored-with-functor idx %))
                (keep #(p/get-sentex recs %))
                (keep (fn [sxr]
                        (let [s (:sentence sxr) [_ pred _ rel] s]
                          (when (and (= 4 (count s)) (symbol? pred) (symbol? rel))
                            [pred rel])))))
          declaration-functors)))

;; ---- the reach of one argument ------------------------------------------

(defn- fact-reach
  "Reflexive-transitive reach of `x` over the declared-transitive `rel`, read from the
  believed facts `context` sees.  A step of the walk asks one literal of a term, and a
  `genl` reach joined with this one (`reach`) asks it of every term of a type's closure,
  few of which any fact of `rel` names: each literal's fan is cut by the slot predicate
  sets whatever its size (`res/*cut-every-fan?*`), so a term no member holds costs the
  slot reads rather than a read of every member."
  [kb rel along? x context]
  (let [step (fn [n]
               (into #{} (keep #(get (second %) '?rv))
                     (res/matches-visible
                      kb (if along? (list rel '?rv n) (list rel n '?rv)) context)))]
    (binding [res/*cut-every-fan?* true]
      (loop [seen #{x}, frontier [x]]
        (if-let [n (peek frontier)]
          (let [fresh (remove seen (step n))]
            (recur (into seen fresh) (into (pop frontier) fresh)))
          seen)))))

(def ^:private bounded-reach-limit
  "The most terms a `genl` reach is walked for and held as a set.  Past it a membership
  is a walk per term (`witness?`) and the closure is never built."
  1024)

(def ^:private walks-before-reach
  "How many memberships past the bound one term's reach answers by walking before the
  question reads the reach whole (`witness?`).  A walk toward a shallow term climbs
  about as much of the ancestry as the whole reach does, so each walk past the first
  few costs what reading the reach once would: a term asked twice pays at most twice,
  and one asked often stops walking early."
  2)

(def ^:private whole-reach-limit
  "The most terms one whole reach is walked for (`whole-reach`).  Past it the walk stops,
  holds nothing, and the term's memberships stay a walk each: a broad type's down-closure
  is most of the KB's types."
  65536)

(def ^:private whole-reach-budget
  "The most terms the whole reaches one memo holds may come to together (`whole-reach`):
  past it the least recently read are dropped, and a term read again is walked again.
  The memo lives for one question or one discovery pass, and is dropped with it."
  1048576)

(defn- unscoped? [context] (or (nil? context) (sx/variable? context)))

(defn- scoped
  "`(f)` with the scoped walks' neighbours held for the question or pass
  (`tax/with-neighbours`): a discovery pass tests the reach of every argument term of
  every stored claim from a context, each test a walk whose every edge asks whether a
  supporter is believed there, and belief does not move while the pass asks."
  [f]
  (tax/with-neighbours (memoized [:neighbours] #(atom {})) f))

(defn- bounded-reach
  "The `genl` reach of `x` from `context` when it holds at most `bounded-reach-limit`
  terms, else nil: a walk of the edges `context` sees (every active edge when unscoped)
  that stops at the limit and stores nothing in the closure cache (`tax/genls-within`),
  held in the memo."
  [kb along? x context]
  (let [cx (when-not (unscoped? context) context)]
    (memoized [:bounded-reach along? x cx]
              #(let [tx (reasoning/taxonomy kb)]
                 (scoped (fn []
                           (if along?
                             (tax/specs-within tx x cx bounded-reach-limit)
                             (tax/genls-within tx x cx bounded-reach-limit))))))))

(defn witness-terms
  "The terms a claim's argument may be stated of for it to reach `x` under one
  declaration: `{w : (rel x w)}` for `transitiveInArgInverse`, `{w : (rel w x)}` for
  `transitiveInArg`.  Reflexive, so `x` is always a member.  The `genl` and fact-relation
  walks are scoped to `context`, and `genlCx` is read globally (docs/inherit.md, \"From
  whose vantage\").  A position's reach over all its declarations is `reach`.  Memoized
  on `[rel along? x context]`."
  [kb {:keys [rel along?]} x context]
  (memoized [:reach rel along? x context]
            (fn []
              (let [tx (reasoning/taxonomy kb)]
                (case rel
                  ;; a reach within the bound is walked and not built through the
                  ;; closure cache (`bounded-reach`): the same set
                  genl        (or (bounded-reach kb along? x context)
                                  (scoped #(if along?
                                             (tax/specs tx x context)
                                             (tax/genls tx x context))))
                  genlCx (if along? (tax/context-down tx x) (tax/context-up tx x)) ; global on purpose
                  (fact-reach kb rel along? x context))))))

(defn- relation-keys
  "The distinct `{:rel :along?}` walks the declarations `poss` at one position name: two
  statements of one declaration in two contexts walk the same relation."
  [poss]
  (into #{} (map #(select-keys % [:rel :along?])) poss))

(defn- reach
  "The terms one argument may be stated of over every declaration `poss` at its position:
  the closure of `x` under the union of their relations, since a claim one declaration
  carries to a term, another carries on from there.  Each relation's step is
  `witness-terms`, already closed, so a term is not expanded again along the relation
  that reached it.  Memoized."
  [kb poss x context]
  (let [ks (relation-keys poss)]
    (if (= 1 (count ks))
      (witness-terms kb (first ks) x context)   ; the common case: no set to rebuild
      (memoized [:joint-reach ks x context]
                #(loop [seen #{x}, todo [x], done (zipmap ks (repeat #{}))]
                   (if-let [n (peek todo)]
                     (let [[seen todo done]
                           (reduce (fn [[seen todo done] k]
                                     (if (contains? (done k) n)
                                       [seen todo done]
                                       (let [r     (witness-terms kb k n context)
                                             fresh (remove seen r)]
                                         [(into seen fresh) (into todo fresh) (update done k into r)])))
                                   [seen (pop todo) done]
                                   ks)]
                       (recur seen todo done))
                     seen))))))

(defn- licensed-reach
  "The terms a claim stated at `w` reaches at a position declared by `poss`: `reach` with
  every declaration's direction flipped.  `reach` asks what a *goal* may be stated of;
  the forward join and the re-join triggers ask what a *claim* licenses, and `(rel a w)`
  is one relation read from either end."
  [kb poss w context]
  (reach kb (map #(update % :along? not) poss) w context))

(defn- whole-reach
  "The `genl` reach of `x` from `cx`, whole, walked through the edges `cx` sees and held
  only in the memo's weighted LRU, bounded by `whole-reach-budget` and evicting the least
  recently read.  nil, and remembered as nil, past `whole-reach-limit` terms."
  [kb along? x cx]
  (let [lru (memoized [:whole-reach]
                      #(caches/weighted-lru (constantly whole-reach-budget)
                                            (fn [r] (if (set? r) (max 1 (count r)) 1))))
        k   [along? x cx]
        hit (caches/lru-get lru k)]
    (cond
      (identical? ::past hit) nil
      (some? hit)             hit
      :else
      (let [tx (reasoning/taxonomy kb)
            r  (scoped (fn []
                         (if along?
                           (tax/specs-within tx x cx whole-reach-limit)
                           (tax/genls-within tx x cx whole-reach-limit))))]
        (caches/lru-put! lru k (if (some? r) r ::past))
        r))))

(defn- witness?
  "Is `t` among `witness-terms` of `x` at one declaration?  A `genl` reach is read
  bounded (`bounded-reach`); past the bound the membership is a reachability walk of the
  edges `context` sees (`tax/genl?`, `tax/genl?-global` unscoped), memoized, so the
  closure is never built.  A term asked more than `walks-before-reach` such memberships
  has its reach read whole once (`whole-reach`) when it holds few enough terms.  Every
  other relation reads `witness-terms`."
  [kb {:keys [rel along?] :as pos} x t context]
  (if (= 'genl rel)
    (if-some [r (bounded-reach kb along? x context)]
      (contains? r t)
      (let [cx (when-not (unscoped? context) context)
            [sub super] (if along? [t x] [x t])
            n  (memoized [:walks along? x cx] #(volatile! 0))]
        (if-some [r (when (>= @n walks-before-reach) (whole-reach kb along? x cx))]
          (contains? r t)
          (memoized [:witness? sub super cx]
                    #(let [tx (reasoning/taxonomy kb)]
                       (vswap! n inc)
                       (if cx
                         (scoped (fn [] (tax/genl? tx sub super cx)))
                         (tax/genl?-global tx sub super)))))))
    (contains? (witness-terms kb pos x context) t)))

(defn- held-reach
  "`reach` of `x` over the declarations `poss` as a set, when they walk one relation and
  its `genl` reach holds at most `whole-reach-limit` terms (`bounded-reach`, else
  `whole-reach`), or nil when it holds more.  Over several relations, `reach` itself.
  Read through the memo, so a pass walks each term's reach once."
  [kb poss x context]
  (let [ks (relation-keys poss)]
    (if (next ks)
      (reach kb poss x context)
      (let [{:keys [rel along?] :as pos} (first ks)]
        (if (= 'genl rel)
          (or (bounded-reach kb along? x context)
              (whole-reach kb along? x (when-not (unscoped? context) context)))
          (witness-terms kb pos x context))))))

(defn- reaches?
  "Is `t` in `reach` of `x` over the declarations `poss`: a walk per membership over one
  relation (`witness?`), the closure over several."
  [kb poss x t context]
  (let [ks (relation-keys poss)]
    (if (next ks)
      (contains? (reach kb poss x context) t)
      (witness? kb (first ks) x t context))))

(defn- reach-size
  "How many terms `reach` of `x` holds, when it holds at most `limit`, else ##Inf.  Only
  ever weighed against an extent to pick a retrieval path, which never changes the
  answer.  A `genl` reach is counted bounded (`bounded-reach`, then a walk of the edges
  `context` sees that stops at `limit`, `tax/genls-within`), so the closure is not built
  to be counted.  Over several relations, the size of `reach` itself."
  [kb poss x context limit]
  (let [ks (relation-keys poss)
        {:keys [rel along?] :as pos} (first ks)
        n  (cond
             (next ks)    (count (reach kb poss x context))
             (= 'genl rel) (if-some [r (bounded-reach kb along? x context)]
                             (count r)
                             (let [tx  (reasoning/taxonomy kb)
                                   cx  (when-not (unscoped? context) context)
                                   lim (long (min limit Long/MAX_VALUE))]
                               (if-let [c (if along?
                                            (tax/specs-within tx x cx lim)
                                            (tax/genls-within tx x cx lim))]
                                 (count c)
                                 ##Inf)))
             :else        (count (witness-terms kb pos x context)))]
    (if (> n limit) ##Inf n)))

;; ---- the claims bearing on a goal ---------------------------------------

(defn- by-position
  "The declarations grouped by the argument position they preserve, dropping any
  position the goal does not have — a declaration naming argument 3 of a binary
  predicate is ill-advised but stored, and reading past the tuple's end is not the
  way to report it."
  [positions arity]
  (into {} (filter (fn [[n _]] (<= n arity))) (group-by :n positions)))

(defn- slots
  "What a claim's argument may be, per argument position of the goal: at a preserved
  position `{:reach terms :in? member? :size size :held held}`, `terms` a delay of the
  reach and `held` a thunk of `held-reach`, and `{:ground term}` where the goal's own
  argument stands.  The product of the reaches is the set of tuples a claim could be
  stated at; `:in?` and `:size` let the extent path test membership and weigh the paths
  without reading a reach whole."
  [kb positions args context]
  (let [by-n (by-position positions (count args))]
    (mapv (fn [i]
            (if-let [poss (by-n (inc i))]
              (let [x (nth args i)]
                {:reach (delay (reach kb poss x context))
                 :in?   #(reaches? kb poss x % context)
                 :size  #(reach-size kb poss x context %)
                 :held  #(held-reach kb poss x context)})
              {:ground (nth args i)}))
          (range (count args)))))

(defn- product-tuples
  "Every argument tuple a claim could be stated at — the product of the reaches, and the
  goal's own term at every other position."
  [slots]
  (reduce (fn [tuples s]
            (let [terms (if-let [r (:reach s)] @r #{(:ground s)})]
              (for [t tuples, w terms] (conj t w))))
          [[]]
          slots))

(def ^:private product-ceiling
  "Past this an extent stops being counted and is simply *large*.  The extent is counted
  first, and the product's size only up to it (`product-size`), so no reach is read whole
  to weigh the two; no extent reaches this."
  1e12)

(defn- product-size
  "How many tuples the product holds — the count the extent is weighed against — or
  ##Inf once it passes `limit`, since the caller asks only which is smaller."
  ^double [slots ^double limit]
  (reduce (fn [^double n s]
            (if (> n limit)
              (reduced ##Inf)
              (* n (double (if-let [size (:size s)] (size (/ limit n)) 1)))))
          1.0 slots))

(defn- extent-size
  "How many stored sentexes one open probe would walk: the predicate extents of every
  predicate the matcher fans the probe over (`res/sub-predicates` for a positive probe,
  `res/contrapositive-predicates` for a negated one, which counts stored denials alone),
  capped by the most selective ground argument position.  The ground position is read
  through `order`, where the probe puts it.  The sum stops past `limit`, the product's
  size (docs/inherit.md, \"What one question costs\")."
  [kb pred slots order negated? context limit]
  (let [idx  (:index kb)
        fan  (if negated?
               (first (res/contrapositive-predicates kb pred context))
               (res/sub-predicates kb pred context))
        rows (reduce (fn [n f]
                       (let [n (+ n (if negated?
                                      (reads/stored-count-denials-global idx f)
                                      (reads/stored-count-with-functor idx f)))]
                         (if (> n limit) (reduced n) n)))
                     0 (or (not-empty fan) [pred]))]
    (double
     (reduce (fn [n j]
               (let [s (nth slots (nth order j))]
                 (if-some [t (:ground s)] (min n (reads/stored-count-with-arg-global idx (inc j) t)) n)))
             rows
             (range (count order))))))

;; ---- the two ways to find them (docs/inherit.md, "What one question costs") --

(defn- probe-var [j] (symbol (str "?w" j)))

(defn- probe-sentence
  "The sentence to look up.  `order` maps each argument position of the *sentence* to
  the tuple index it fills: the identity for a claim read forwards, `[1 0]` for the
  converse an asymmetric predicate is denied by.  `terms` supplies a term for a tuple
  index, or nil to leave a variable there."
  [pred slots order terms]
  (cons pred (map-indexed (fn [j ti]
                            (let [s (nth slots ti)]
                              (if (:reach s) (or (terms ti) (probe-var j)) (:ground s))))
                          order)))

(defn- in-product?
  "Is `tuple` one of the tuples a claim bearing on the goal could be stated at?  Asked
  of every position, ground ones included: the symmetric mirror can hand back a match
  whose arguments sit in the other order, and a ground position is ground only in the
  pattern."
  [slots tuple]
  (and (= (count tuple) (count slots))
       (every? (fn [i]
                 (let [s (nth slots i) t (nth tuple i)]
                   (if-let [in? (:in? s)] (in? t) (= t (:ground s)))))
               (range (count slots)))))

(defn- bound-tuple
  "The tuple a match is a statement about, read back through `order` — the bindings at
  the preserved positions, the goal's own terms at the ground ones.  nil when a
  preserved position came back unbound, which no match of this pattern can do."
  [bindings slots order]
  (reduce (fn [t j]
            (let [ti (nth order j) s (nth slots ti)]
              (if (:reach s)
                (if-some [v (get bindings (probe-var j))] (assoc t ti v) (reduced nil))
                (assoc t ti (:ground s)))))
          (vec (repeat (count slots) nil))
          (range (count order))))

(def ^:dynamic *deadline*
  "The `System/nanoTime` instant a claim walk stops at, bound only by
  `provers/TransitiveInArgProver` from `budget/*deadline*`.  nil for every other reader of
  `claims` (the asymmetry check at `assert`, settle, forward chaining), which walk to the
  end whatever deadline an enclosing `ask` holds."
  nil)

(defn- believed-matches
  "`[tuple handle sentex]` for every believed sentex matching `sentence` that states
  something about a tuple in the product.  `known` is the tuple when the caller
  already has it — a ground probe binds nothing to read one back from.  `strong?` keeps
  the known-true sentexes alone.  `dl` is checked per probe and per row read
  (`budget/check-deadline!`)."
  [kb sentence slots order context known strong? dl]
  (budget/check-deadline! dl)
  (let [tms (reasoning/tms kb)]
    (for [[h b] (res/matches-visible kb sentence context)
          :let  [_     (budget/check-deadline! dl)
                 _     (budget/check-unit!)
                 tuple (or known (bound-tuple b slots order))]
          :when (and tuple
                     (or (not strong?) (st/known-true? (jtms/defeat-class tms h)))
                     (in-product? slots tuple))
          :let  [sxr (p/get-sentex (:records kb) h)]
          :when (and sxr (jtms/in? tms h))]
      [tuple h sxr])))

(defn- extent-key [sentence order context strong?]
  [:extent-index sentence order context strong?])

(defn- extent-index
  "The matches of the open probe `sentence` from `context`, as `[tuple handle]`, grouped
  by the term at each preserved tuple index: `{ti {term [[tuple h] …]}}`, the known-true
  ones alone under `strong?`.  Held in the memo, so the questions of one discovery pass
  read a predicate's extent once between them.  The grouping reads no goal: the probe
  binds the ground positions, and `slots` says only which tuple indices are preserved."
  [kb sentence slots order context strong?]
  (memoized (extent-key sentence order context strong?)
            #(let [tms  (reasoning/tms kb)
                   rows (into [] (keep (fn [[h b]]
                                         (budget/check-unit!)
                                         (when (or (not strong?)
                                                   (st/known-true? (jtms/defeat-class tms h)))
                                           (when-let [t (bound-tuple b slots order)] [t h]))))
                              (res/matches-visible kb sentence context))]
               (into {}
                     (comp (filter (fn [ti] (:reach (nth slots ti))))
                           (map (fn [ti] [ti (group-by (fn [[t]] (nth t ti)) rows)])))
                     (range (count slots))))))

(defn- indexed-rows
  "The rows of `extent-index` whose term at one preserved tuple index lies in that slot's
  `held-reach`, read from whichever of the reach and the index's terms is smaller, at the
  tuple index where that is smallest; nil when no preserved slot's reach is held.  A
  tuple index with no rows reads no reach."
  [slots index]
  (let [cost (fn [[ti groups]]
               (if (empty? groups)
                 [0 groups #{}]
                 (when-some [r ((:held (nth slots ti)))]
                   [(min (count r) (count groups)) groups r])))
        best (reduce (fn [b x] (if (or (nil? b) (< (first x) (first b))) x b))
                     nil (keep cost index))]
    (when-let [[_ groups r] best]
      (if (< (count r) (count groups))
        (into [] (mapcat #(get groups %)) r)
        (into [] (comp (filter #(contains? r (key %))) (mapcat val)) groups)))))

(defn- indexed-matches
  "`believed-matches` over the open probe `sentence`, read through `extent-index` and
  `indexed-rows`, then `in-product?` over the rest of each tuple.  nil when no preserved
  slot's reach is held, for the caller to read the extent row by row."
  [kb sentence slots order context strong?]
  (when-let [rows (indexed-rows slots (extent-index kb sentence slots order context strong?))]
    (let [tms (reasoning/tms kb)]
      (for [[tuple h] rows
            :when (in-product? slots tuple)
            :let  [sxr (p/get-sentex (:records kb) h)]
            :when (and sxr (jtms/in? tms h))]
        [tuple h sxr]))))

(def ^:dynamic *retrieval*
  "Which retrieval path finds the claims: `:auto` weighs the extent against the product
  per goal, and `:extent` and `:product` force one, so `inherit_oracle_test` can hold the
  two against each other on one KB."
  :auto)

(defn- found-claims
  "Every believed statement bearing on the goal at `order` and `negated?`, the known-true
  ones alone under `strong?`, by whichever of the two retrieval paths is cheaper for this
  KB.  Either path throws `budget/check-deadline!`'s signal once `*deadline*` passes."
  [kb pred slots order negated? context strong?]
  (let [wrap (fn [s] (if negated? (list 'not s) s))
        dl   *deadline*
        open (delay (wrap (probe-sentence pred slots order (constantly nil))))]
    ;; the index reads the extent whole before its first row, so a reader under a
    ;; deadline reads it row by row.  A known-true read takes an index the memo already
    ;; holds before the two paths are weighed: it holds the known-true statements alone,
    ;; and weighing the product walks the reaches an empty index does not read
    (or (when (and strong? (not dl) (not= :product *retrieval*)
                   (some-> *memo* deref (contains? (extent-key @open order context true))))
          (indexed-matches kb @open slots order context true))
        (if (case *retrieval*
              :extent  true
              :product false
              (let [extent (extent-size kb pred slots order negated? context product-ceiling)]
                (<= extent (product-size slots extent))))
          (or (when-not dl (indexed-matches kb @open slots order context strong?))
              (believed-matches kb @open slots order context nil strong? dl))
          (mapcat (fn [tuple]
                    (believed-matches kb (wrap (probe-sentence pred slots order tuple))
                                      slots order context tuple strong? dl))
                  (product-tuples slots))))))

(defn- strongest-per-tuple
  "One claim per tuple: the believed statement of it with the highest defeat class, ties
  broken on the context name and then the printed sentence, so the choice is a function
  of content (docs/inherit.md, \"Four things that follow from reading claims out of
  belief\").  The tuple's other statements ride along as `:also`, in the same order, and
  only `supports-for` reads them: a statement in a context the winner's does not see
  licenses a reader the winner does not reach.  Every other decision reads the winner."
  [kb polarity found]
  (->> found
       (map (fn [[tuple h sxr]]
              {:polarity polarity :handle h :sentence (:sentence sxr)
               :context (:context sxr) :tuple tuple
               :class (or (jtms/defeat-class (reasoning/tms kb) h) :default)}))
       (group-by :tuple)
       (map (fn [[_ cs]]
              ;; the key is built once per claim; `nm/print-key` keeps an ambient
              ;; `*print-length*` out of it
              (let [k (juxt #(- (st/rank-of (:class %)))
                            #(nm/name-key (:context %))
                            #(nm/print-key (:sentence %)))
                    w (nm/min-by-content-key k compare cs)]
                (if (next cs)
                  (let [others (into [] (comp (remove #(= (:handle w) (:handle %)))
                                              (distinct))
                                     cs)]
                    (cond-> w
                      (seq others) (assoc :also (nm/sort-by-content-key k compare others))))
                  w))))))

(defn- separation-test
  "`tax/separation-test` for the type `a` at `context`, honouring the
  `siblingDisjointException`s it reads; at an unscoped `context`, the unscoped test that
  exempts no pair, the union of what every reader separates, for a caller that asks on
  behalf of every reader (a trigger, the discovery pass)."
  [tax a context]
  (if (unscoped? context)
    (tax/separation-test tax a nil (constantly false))
    (tax/separation-test tax a context)))

(defn- separated-denials
  "`[tuple handle sentex]` for each believed membership `(S x)` `context` sees whose type
  `S` the taxonomy separates from `pred` there: a denial of `(pred x)`, since no term is a
  member of two separated types.  The candidate types are the predicates holding a stored
  fact at `x` (`reads/as-stored-predicates-at-arg`), each read through
  `believed-matches`.  Nothing is read when no separation reaches `pred`."
  [kb pred x slots context dl]
  (when-let [sep? (separation-test (reasoning/taxonomy kb) pred context)]
    (into []
          (mapcat #(believed-matches kb (list % x) slots [0] context [x] false dl))
          (into (sorted-set)
                (filter #(and (symbol? %) (not= pred %) (sep? %)))
                (reads/as-stored-predicates-at-arg (:index kb) 1 x)))))

(defn- goal-probes
  "What `claims` reads of the ground goal: `[probe sl nsl asym?]`, where `(probe sl order
  negated? polarity)` makes one probe over the slots `sl` and `nsl` are the slots a denial
  moves along."
  [kb goal context strong?]
  (let [pred  (nm/functor goal)
        args  (vec (nm/args goal))
        poss  (positions kb pred context)
        asym? (tax/has-prop? (reasoning/taxonomy kb) :asymmetric pred context)
        ;; With no preserved position the product is the goal's own arguments alone,
        ;; so this still answers "what is believed about exactly this tuple" — which
        ;; is what the asymmetry check needs of a predicate that inherits nothing.
        sl    (slots kb poss args context)
        ;; a denial moves along the declared relations and not along the self
        ;; relation: `(P a w)` and `(not (P w b))` leave `(P a b)` open
        nsl   (if (some :self? poss) (slots kb (into [] (remove :self?) poss) args context) sl)]
    [(fn [sl order negated? polarity]
       (strongest-per-tuple
        kb polarity (found-claims kb pred sl order negated? context strong?)))
     sl nsl asym?]))

(defn- stated-denials
  "The `:against` claims on the ground goal that a statement makes rather than a
  separation: an explicit `(not (P …))` at a tuple in range and, for a binary goal on an
  `asymmetric` `P`, the converse.  Held in the memo, so `claims` and `answers?` read them
  once between them."
  [kb goal context strong?]
  (memoized [::stated-denials goal context strong? *concluding*]
            (fn []
              (let [[probe _ nsl asym?] (goal-probes kb goal context strong?)]
                (vec
                 (concat
                  (probe nsl (vec (range (count (nm/args goal)))) true :against)
                  ;; The converse is read with the tuple indices swapped, so a stored
                  ;; `(P x y)` is filed against the tuple `[y x]` it denies.
                  (when (and asym? (= 2 (count (nm/args goal))))
                    (remove #(= (first (:tuple %)) (second (:tuple %)))
                            (probe nsl [1 0] false :against)))))))))

(defn claims
  "Every believed claim bearing on the ground goal `(P a1 … an)`, each tagged with the
  argument tuple it is stated at and whether it argues `:for` or `:against`.

  Against comes from three places: an explicit `(not (P …))` at a tuple in range; for a
  binary goal on an `asymmetric` `P`, the converse `(P … y … x …)` (the two are
  `stated-denials`); and, for a unary goal `(P x)` with a preserved position, a
  membership `(S x)` of a type a separation holds apart from `P` at `context`
  (`separated-denials`), at the goal's own tuple, tagged `:separated?`.

  Every probe is made, so a tuple believed in both polarities yields both claims and
  `verdict` answers `:ambiguous`.  The converse is not read at a self tuple `[a a]`
  (docs/inherit.md, \"Four things that follow from reading claims out of belief\").

  `strong?` reads the known-true statements alone, which are all a caller keeping only
  known-true claims needs: `undercut?` drops none of them, and a tuple's strongest
  statement is known-true whenever one of its statements is.  It reads no separated
  membership: each `strong?` caller pairs a stored claim with a claim at another tuple."
  ([kb goal context] (claims kb goal context false))
  ([kb goal context strong?]
   (with-memo
     (let [args  (vec (nm/args goal))
           [probe sl nsl] (goal-probes kb goal context strong?)]
       ;; realized here, inside the memo (`with-memo`): the probes read the store and
       ;; `strongest-per-tuple` groups lazily, so a seq handed back unrealized does all
       ;; of that with the memo gone
       (vec
        (concat
         (probe sl (vec (range (count args))) false :for)
         (stated-denials kb goal context strong?)
         (when (and (= 1 (count args)) (seq (positions kb (nm/functor goal) context)) (not strong?))
           (map #(assoc % :separated? true)
                (strongest-per-tuple
                 kb :against
                 (separated-denials kb (nm/functor goal) (first args) nsl context *deadline*))))))))))

;; ---- specificity ---------------------------------------------------------

(defn- below?
  "Is tuple `t1` at or below `t2` — for every preserved position, is `t2`'s term one
  of the terms `t1`'s can be stated of?  The order is read off the same relations the
  inheritance travels, never off a score."
  [kb positions t1 t2 context]
  (every? (fn [[n poss]]
            (reaches? kb poss (nth t1 (dec n)) (nth t2 (dec n)) context))
          (by-position positions (count t1))))

(defn- undercut?
  "Is `c` displaced by a strictly more specific claim?  Only a `:default` claim can
  be: a `:monotonic` one is known-true, so a contrary specific claim is a
  contradiction to report rather than a refinement to defer to."
  [kb positions c others context]
  (and (= :default (:class c))
       (boolean (some (fn [o] (and (not= (:tuple o) (:tuple c))
                                   (below? kb positions (:tuple o) (:tuple c) context)))
                      others))))

(def ^:dynamic *default-contraries-set-aside*
  "True while `chain` reads a preserved antecedent: a `:default` claim that denies the
  goal is left out before the survivors are read, so a firing it alone undercuts is made,
  and stored with a defeat of its conclusion resting on that claim (`contraries`).
  The prover reads every claim."
  false)

(defn surviving
  "The believed claims bearing on `goal` that a strictly more specific one has not
  displaced, each carrying its `:polarity` and `:class`.  The raw material both
  consumers read: the prover turns it into a verdict, and `checks/asymmetry-problem`
  asks the narrower question of whether any survivor is **known-true**.  Under
  `*default-contraries-set-aside*` a `:default` claim against the goal is not read."
  [kb goal context]
  (with-memo
    (let [poss (positions kb (nm/functor goal) context)
          cs   (cond->> (claims kb goal context)
                 *default-contraries-set-aside*
                 (into [] (remove #(and (not= :for (:polarity %)) (= :default (:class %))))))]
      ;; realized inside the memo: `undercut?` walks a `reach` per comparison
      (into [] (remove #(undercut? kb poss % cs context)) cs))))

(defn verdict
  "What the preserved claims say about the ground goal:

    `:for`       — some claim reaches it and nothing surviving disagrees
    `:against`   — the surviving claims deny it
    `:ambiguous` — surviving claims disagree at incomparable specificity
    `nil`        — nothing bears on it, or the predicate declares no preserved position

  Claims a strictly more specific one displaces drop out first (`surviving`)."
  [kb goal context]
  ;; This runs only when a position is declared: without one there is no inheritance to
  ;; perform, and an answer from the goal's own tuple would repeat `FactProver`'s.
  (with-memo
    (when (seq (positions kb (nm/functor goal) context))
      (let [polarity (into #{} (map :polarity) (surviving kb goal context))]
        (cond
          (= polarity #{:for})     :for
          (= polarity #{:against}) :against
          (seq polarity)           :ambiguous)))))

(defn contraries
  "The surviving claims (`surviving`, every claim read) that do not argue for `goal` in
  `context`: what keeps a `:for` verdict from it.  A firing over `goal` whose contraries
  are all `:default` is stored with a defeat resting on each."
  [kb goal context]
  (binding [*default-contraries-set-aside* false]
    (with-memo
      (into [] (remove #(= :for (:polarity %))) (surviving kb goal context)))))

(defn ground-goal?
  "A closed positive literal this can speak about.  A forward join reads claims on a
  positive antecedent alone; `goal-verdict` reads a `(not …)` over one for the prover."
  [goal]
  (and (sequential? goal) (seq goal)
       (symbol? (nm/functor goal))
       (not= 'not (nm/functor goal))
       (seq (nm/args goal))
       (every? sx/ground-term? (nm/args goal))))

(defn goal-verdict
  "`[verdict literal]` for a goal the prover answers: `[:for g]` for a `ground-goal?` `g`,
  `[:against g]` for `(not g)` over one, else nil.  `answers?` compares the first member
  with `verdict` of the literal, so a surviving denial answers the negation as a surviving
  claim answers the positive (docs/inherit.md, \"Reading it back\")."
  [goal]
  (cond
    (ground-goal? goal)                                   [:for goal]
    (and (sx/negation? goal) (ground-goal? (second goal))) [:against (second goal)]))

(defn answers?
  "Does the prover answer `goal` (`goal-verdict`)?  A negation needs a surviving denial
  other than a `:separated?` membership.  The separation that undercuts a claim does not
  apply the soundness rule `res/separation-denials` applies to a refutation, and
  `provers/DisjointnessNegationProver` answers a denial that meets it."
  [kb goal context]
  (boolean
   (when-let [[holds lit] (goal-verdict goal)]
     (with-memo
       (and (or (= :for holds)
                ;; the denial this needs is a stated one: with none, the verdict is not
                ;; read, and neither is the extent of the claims for the goal
                (seq (stated-denials kb lit context false)))
            (= holds (verdict kb lit context))
            (or (= :for holds)
                (some #(and (= :against (:polarity %)) (not (:separated? %)))
                      (surviving kb lit context))))))))

;; ---- what an inherited claim rests on ------------------------------------
;; docs/inherit.md, "Forward chaining on a claim nobody stored"

(defn- supporter-rank
  "The strength rank of handle `h` under `sclass` (`handle → defeat class`, `:default`
  where it answers nil), or nil when `sclass` is nil and strength takes no part."
  [sclass h]
  (when sclass (st/rank-of (or (sclass h) :default))))

(defn- reading-rank
  "The rank of the weakest of handles `hs` under `sclass` — a reading's floor class — or
  nil when `sclass` is nil.  `:monotonic`'s rank for no handles."
  [sclass hs]
  (when sclass (reduce min (st/rank-of :monotonic) (map #(supporter-rank sclass %) hs))))

(defn- hidable-of
  "The members of `hs` that `hid` (`handle → boolean`, nil for none) marks as hidable by
  an except, as a set, or nil when none: the third member of a `tax/uncovered` label."
  [hid hs]
  (when hid (not-empty (into #{} (filter hid) hs))))

(defn- general-supporters
  "The believed sentexes supporting `sentence` visible from `context` that no other one
  covers (`tax/uncovered`, weighing strength under `sclass`), as `[handle ctx]` pairs: the
  one stated most generally where their contexts are comparable, and one per context
  where neither sees the other.  Ordered on the context name and the printed sentence,
  never the handle; the sentence is in the key because a sub-predicate's sentex answers
  the same query from one context.  Of two that cover each other the earlier is kept.
  `hid` is `claim-supports`'."
  [kb sentence context sclass hid]
  (let [tx (reasoning/taxonomy kb)]
    (->> (res/matches-visible kb sentence context)
         (keep (fn [[h _]]
                 (when-let [sxr (p/get-sentex (:records kb) h)]
                   (when (jtms/in? (reasoning/tms kb) h)
                     [[(str (:context sxr)) (nm/print-key (:sentence sxr))]
                      [h (:context sxr)]]))))
         (sort-by first)
         (mapv second)
         (tax/uncovered tx (fn [[h c]] [(supporter-rank sclass h) (if (nil? c) #{} #{c})
                                        (hidable-of hid [h])])))))

(defn- with-supporters
  "Each of `alts` (`{:hs :ctxs}`) once per supporter in `sups` (`[handle ctx]` pairs),
  that supporter appended; `alts` unchanged when `sups` is empty."
  [alts sups]
  (if (empty? sups)
    alts
    (vec (for [{:keys [hs ctxs]} alts, [h c] sups]
           {:hs (conj hs h) :ctxs (conj ctxs c)}))))

(defn- fact-steps
  "`step` for `tax/uncovered-routes` over the declared-transitive `rel` as `context` sees
  it, from the goal's end toward the claim's (`fact-paths`): from a node, each neighbour
  once per believed fact stating the step that no other covers, with its rank under
  `sclass`, whether `hid` marks it, and its content key."
  [kb rel along? context sclass hid]
  (let [tx    (reasoning/taxonomy kb)
        label (fn [[h c]] [(supporter-rank sclass h) (if (nil? c) #{} #{c}) (hidable-of hid [h])])]
    (fn [n]
      (->> (res/matches-visible
            kb (if along? (list rel '?rv n) (list rel n '?rv)) context)
           (keep (fn [[h b]]
                   (let [v (get b '?rv)]
                     (when (and v (not= v n))
                       (when-let [sxr (p/get-sentex (:records kb) h)]
                         [v [h (:context sxr)]
                          (str (:context sxr))
                          (nm/print-key (:sentence sxr))])))))
           (nm/sort-by-content-key
            (juxt #(nm/print-key (nth % 0)) #(nth % 2) #(nth % 3))
            compare)
           (partition-by first)
           (mapcat (fn [steps]
                     (let [keys (into {} (map (fn [[_ sw c t]] [sw [c t]])) steps)]
                       (for [sw (tax/uncovered tx label (mapv second steps))]
                         [(first (first steps)) sw (supporter-rank sclass (first sw))
                          (boolean (and hid (hid (first sw)))) (keys sw)]))))))))

(defn- fact-paths
  "The paths from `a` to `w` over the declared-transitive `rel` that `context` sees and
  no other path covers (`tax/uncovered-routes`), each the `[handle ctx]` of the stored
  fact stating each step; `[[]]` when `a` is `w`, `[]` when no path exists.  What
  `taxonomy/general-reach-supports` is for the virtual relations, over the adjacency
  `fact-reach` walks, so the two agree on what a context reaches.  Each step names the
  facts stating it that no other covers, ordered on the context name and then the printed
  sentence.  Under `sclass` a route is labelled with its weakest fact; `hid` is
  `claim-supports`'."
  [kb rel along? a w context sclass hid]
  (tax/uncovered-routes (reasoning/taxonomy kb) a w (fact-steps kb rel along? context sclass hid)))

(defn- joint-move-supports
  "`move-supports` at a position whose declarations `poss` walk several relations: the
  routes from `a` to `w` over the union of the relations (`reach`), each naming, for every
  relation it walks, the declaration that permits it (none for the self relation,
  `self-positions`) and, for a fact relation, an uncovered statement of `(transitive R)`,
  beside the edges.  One `tax/uncovered-routes` walk over `[term relation]` nodes, where
  entering a relation at a term is a step resting on those statements, so a route through
  general contexts covers one through a specific context across relations as along one."
  [kb poss a w context sclass hid]
  (let [tx      (reasoning/taxonomy kb)
        rank    #(supporter-rank sclass %)
        hid?    #(boolean (and hid (hid %)))
        enter   (fn [[h] k] [(rank h) (hid? h) k])
        trans   (memoize (fn [rel] (general-supporters kb (list 'transitive rel) context sclass hid)))
        ks      (vec (relation-keys poss))
        edges   (into {}
                      (map (fn [{:keys [rel along?] :as k}]
                             [k (if (contains? virtual-relations rel)
                                  (tax/edge-steps tx (keyword rel) (when (= 'genl rel) context)
                                                  sclass hid (if along? :rev :fwd))
                                  (fact-steps kb rel along? context sclass hid))]))
                      ks)
        ;; entering relation `k` at a term: [stage supporter content-key] per statement
        entries (into {}
                      (map (fn [k]
                             [k (->> poss
                                     (filter #(= k (select-keys % [:rel :along?])))
                                     (keep (fn [{:keys [handle in]}] (when handle [[handle in] (str in)])))
                                     (nm/sort-by-content-key second compare))]))
                      ks)
        step    (fn [[n k stage]]
                  (if (= ::declared stage)
                    (for [sw (trans (:rel k))]
                      (into [[n k] sw] (enter sw (str (second sw)))))
                    (concat
                     (when (map? k)
                       (for [[n2 sw r h? key] ((edges k) n)]
                         [[n2 k] sw r h? key]))
                     (for [k2 ks :when (not= k k2)
                           :let [virtual? (contains? virtual-relations (:rel k2))]
                           e (if (seq (entries k2))
                               (for [[sw key] (entries k2)]
                                 (into [(if virtual? [n k2] [n k2 ::declared]) sw] (enter sw key)))
                               ;; the self relation: no declaration, only its transitivity
                               (for [sw (trans (:rel k2))]
                                 (into [[n k2] sw] (enter sw (str (second sw))))))]
                       e))))
        routes  (tax/uncovered-routes tx [a ::start] #(and (= w (first %)) (nil? (nth % 2 nil))) step)]
    (tax/uncovered tx (fn [{:keys [hs ctxs]}]
                        [(reading-rank sclass hs) (tax/context-floor tx ctxs) (hidable-of hid hs)])
                   (mapv (fn [route] {:hs (mapv first route) :ctxs (mapv second route)}) routes))))

(defn- move-supports
  "The alternative supports licensing the step from the claim's term `w` to the goal's `a`
  at one preserved position, each `{:hs [handle …] :ctxs [ctx …]}`: the declaration that
  permits the move, the relation edges the reach travelled, and for a fact relation an
  uncovered statement of `(transitive R)` (`general-supporters`); `:ctxs` are the
  contexts those sentexes were asserted in.  Empty when no declaration at this position
  reaches from one to the other through edges `context` sees, and one alternative with no
  handles when `a` is `w`.

  Every declaration that reaches contributes its routes, taken in content order (`[rel
  along? in]`), and an alternative another covers is dropped (`tax/uncovered`), so of two
  statements of one declaration the more general one stays and a tie keeps the earlier.
  Under `sclass` (`handle → defeat class`) a stronger alternative stays beside a weaker
  one its contexts cover; nil leaves strength out.  `hid` is `claim-supports`'."
  [kb poss a w context sclass hid]
  (cond
    (= a w)
    [{:hs [] :ctxs []}]

    (next (relation-keys poss))
    (joint-move-supports kb poss a w context sclass hid)

    :else
    (let [tx   (reasoning/taxonomy kb)
          alts (into []
                     (mapcat
                      (fn [{:keys [rel along? handle in]}]
                        (let [[sub super] (if along? [w a] [a w])]
                          (if (contains? virtual-relations rel)
                            (for [route (let [k (keyword rel) v (when (= 'genl rel) context)]
                                          (if (or sclass hid)
                                            (tax/reach-supports tx k sub super v sclass hid)
                                            (tax/general-reach-supports tx k sub super v)))]
                              {:hs   (into [handle] (map first) route)
                               :ctxs (into [in] (map second) route)})
                            (when-let [routes (seq (fact-paths kb rel along? a w context sclass hid))]
                              (with-supporters
                                (mapv (fn [route]
                                        {:hs   (into [handle] (map first) route)
                                         :ctxs (into [in] (map second) route)})
                                      routes)
                                (general-supporters kb (list 'transitive rel) context sclass hid))))))
                      (nm/sort-by-content-key
                       (juxt #(str (:rel %)) #(str (:along? %)) #(str (:in %))) compare poss)))]
      (tax/uncovered tx (fn [{:keys [hs ctxs]}]
                          [(reading-rank sclass hs) (tax/context-floor tx ctxs) (hidable-of hid hs)])
                     alts))))

(defn- claim-supports
  "The alternative readings of claim `c` at the goal's arguments `args`, each `{:hs
  [handle …] :ctxs [ctx …]}`: the declaration permitting each move, the relation edges the
  reach travelled, and for a mirrored reading the `(symmetric …)` on the stored sentence's
  functor, with the contexts those were asserted in.  nil when no declaration reaches from
  the claim's tuple to `args` through edges `context` sees; one alternative with no
  handles when the claim is stated at the goal's own tuple.  The products another reading
  covers are dropped (`tax/uncovered`).

  The claim's own handle is absent, since `supports-for` names it as `:claim` and
  `clashing-claim` makes it a nogood member.  `by-n` is `by-position`'s grouping, and
  `sclass` is `move-supports`'.  `hid` (`handle → boolean`, or nil) marks the handles an
  except can hide: a reading resting on one covers only the readings resting on it too."
  [kb by-n args c context sclass hid]
  (when-let [alts (reduce (fn [acc i]
                            ;; a denial moved along the declared relations alone (`claims`)
                            (if-let [ps (cond->> (by-n (inc i))
                                          (= :against (:polarity c)) (filterv (complement :self?))
                                          true                      not-empty)]
                              (let [ms (move-supports kb ps (nth args i) (nth (:tuple c) i) context
                                                      sclass hid)]
                                (if (seq ms)
                                  (vec (for [x acc, m ms]
                                         {:hs   (into (:hs x) (:hs m))
                                          :ctxs (into (:ctxs x) (:ctxs m))}))
                                  (reduced nil)))
                              acc))
                          [{:hs [] :ctxs []}]
                          (range (count args)))]
    ;; A claim whose stored orientation is not the tuple it was read at came through the
    ;; symmetric mirror, and that reading rests on a `(symmetric …)` declaration exactly
    ;; as a fact-relation reach rests on `(transitive R)`: name it, so retracting the
    ;; symmetry withdraws what only the mirror licensed.  The matcher mirrors each fanned
    ;; literal on *its own* declaration, so the one named is the stored sentence's
    ;; functor's — the goal predicate's only when they coincide.
    (let [sups (when (and (= 2 (count args))
                          (not= (vec (nm/args (:sentence c))) (:tuple c)))
                 (general-supporters kb (list 'symmetric (nm/functor (:sentence c))) context
                                     sclass hid))
          alts (mapv #(update % :hs (fn [hs] (into [] (distinct) hs)))
                     (with-supporters alts sups))
          tx   (reasoning/taxonomy kb)]
      (tax/uncovered tx (fn [{:keys [hs ctxs]}]
                          [(reading-rank sclass hs) (tax/context-floor tx ctxs) (hidable-of hid hs)])
                     alts))))

(defn- defeat-classes
  "`kb`'s `handle → defeat class` read, the `sclass` the opposing readings are weighed
  under."
  [kb]
  (let [tms (reasoning/tms kb)] #(jtms/defeat-class tms %)))

(defn- strongest-reading
  "The reading of claim `c` whose weakest member is strongest, as `[rank handles]`, or nil
  when none reaches: the one reading a caller that opposes the claim to a stored one
  takes, since the claim holds as strongly as its strongest reading.  Of two at one rank
  the earlier in `claim-supports`' content order is kept."
  [kb by-n args c context]
  (let [sclass (defeat-classes kb)]
    (reduce (fn [best {:keys [hs]}]
              (let [r (reading-rank sclass hs)]
                (if (or (nil? best) (> r (first best))) [r hs] best)))
            nil
            (claim-supports kb by-n args c context sclass nil))))

(defn claim-reading
  "The handles of claim `c`'s `strongest-reading`, `c` a `surviving` claim bearing on the
  ground `goal`, read at `goal`'s arguments from `context`: the reading `clashing-claim`
  pairs a stored claim with.  nil when no declaration reaches."
  [kb goal c context]
  (with-memo
    (let [args (vec (nm/args goal))
          poss (positions kb (nm/functor goal) context)]
      (when (seq poss)
        (second (strongest-reading kb (by-position poss (count args)) args c context))))))

(defn supports-for
  "What licenses the ground goal `(P a1 … an)` by preservation: a vector of `{:claim
  handle :handles [handle …]}`, each the claim it was read off and every sentex the
  reading rests on, empty when nothing does.  The semantics are `verdict`'s: the
  surviving claims must agree.

  A goal the KB states directly licenses nothing: the stored claim is the diagonal of the
  reflexive reach, and the ordinary matcher already justifies it.

  Each surviving claim, and each other statement of its tuple (`:also`), contributes its
  readings (`claim-supports`).  A reading is dropped when another is at least as strong
  (the claim's defeat class) and seen from every reader that sees it (`tax/uncovered`), so
  routes stated in sibling contexts license one reading each.  The survivors are ordered
  on defeat class, then the tuple, the context and the sentence, all spellings; of two
  readings that cover each other the earlier is kept."
  [kb goal context]
  (with-memo
    (let [pred (nm/functor goal)
          args (vec (nm/args goal))
          poss (positions kb pred context)]
      (or (when (seq poss)
            (let [sv (surviving kb goal context)]
              (when (and (seq sv)
                         (= #{:for} (into #{} (map :polarity) sv))
                         (not-any? #(= (:tuple %) args) sv))
                (let [by-n (by-position poss (count args))
                      tx   (reasoning/taxonomy kb)
                      alts (into []
                                 (mapcat (fn [c]
                                           (for [c                 (cons c (:also c))
                                                 {:keys [hs ctxs]} (claim-supports kb by-n args c context nil nil)]
                                             {:claim   (:handle c)
                                              :handles (into [] (distinct) (cons (:handle c) hs))
                                              ::rank   (st/rank-of (:class c))
                                              ::ctxs   (cons (:context c) ctxs)})))
                                 ;; the key is built once per survivor, through
                                 ;; `nm/print-key`: the chosen handle lands in a
                                 ;; recorded justification
                                 (nm/sort-by-content-key (juxt #(- (st/rank-of (:class %)))
                                                               #(nm/print-key (:tuple %))
                                                               #(nm/name-key (:context %))
                                                               #(nm/print-key (:sentence %)))
                                                         compare
                                                         sv))]
                  (mapv #(dissoc % ::rank ::ctxs)
                        (tax/uncovered tx (fn [a] [(::rank a) (tax/context-floor tx (::ctxs a))])
                                       alts))))))
          []))))

(defn- strongest-claim
  "Of the surviving claims `sv` bearing on the tuple `args`, the one whose
  `strongest-reading`, capped at the claim's class, is strongest, as `[claim handles]`, or
  nil when no reading reaches or the strongest is not known-true: a reading is as strong
  as its weakest reason, so one resting on a `:default` declaration or edge is undercut
  as a `:default` claim is.  Of two at one rank the first on content: the tuple, then
  the asserting context, then what the claim says, all spellings rather than handles,
  since the chosen handle lands in a reported nogood."
  [kb by-n args sv context]
  (when-let [[r c hs]
             (reduce (fn [best c]
                       (if-let [[r hs] (strongest-reading kb by-n args c context)]
                         (let [r (min r (st/rank-of (:class c)))]
                           (if (or (nil? best) (> r (first best))) [r c hs] best))
                         best))
                     nil
                     (nm/sort-by-content-key (juxt #(nm/print-key (:tuple %))
                                                   #(nm/name-key (:context %))
                                                   #(nm/print-key (:sentence %)))
                                             compare
                                             sv))]
    (when (st/known-true? (st/class-of-rank r)) [c hs])))

(defn clashing-claim
  "The known-true claim that reaches `sentence`'s own tuple by preservation and denies
  it, as `{:sentence :context :claim handle :handles [handle …] :class}`, or nil.

  `sentence` is a stored fact of a preserved predicate, in either polarity; the claim
  looked for is the opposite one.  Known-true, because `undercut?` leaves no `:default`
  general claim beside a nearer contrary one (docs/inherit.md, \"A contrary claim against
  a known-true one is a contradiction, and is reported\").  A claim stated at
  `sentence`'s own tuple is excluded, since the negation family pairs two stored
  sentexes (`decide/note-candidate!`), and so is a claim stating `sentence` itself.

  `:handles` is the reading's support and not the claim: the declaration permitting each
  move, the relation edges the reach travelled, the `(transitive R)` a fact-relation
  reach is closed under, and the `(symmetric …)` behind a mirrored reading.  One claim is
  named where several reach (`strongest-claim`).  Asked from `context`."
  [kb sentence context]
  (with-memo
    (let [neg? (and (sequential? sentence) (= 'not (nm/functor sentence))
                    (= 2 (count sentence)))
          body (if neg? (second sentence) sentence)]
      (when (ground-goal? body)
        (let [pred (nm/functor body)
              args (vec (nm/args body))
              poss (positions kb pred context)]
          (when (seq poss)
            (let [want (if neg? :for :against)
                  ;; known-true claims alone, which `undercut?` never drops
                  sv   (->> (claims kb body context true)
                            (filter #(and (= want (:polarity %))
                                          (st/known-true? (:class %))
                                          (not= (:tuple %) args)
                                          (not= (:sentence %) sentence))))]
              (when-let [[c hs] (strongest-claim kb (by-position poss (count args)) args sv
                                                 context)]
                {:sentence (if neg? body (list 'not body))
                 :context  context
                 :claim    (:handle c)
                 :handles  hs
                 :class    (:class c)}))))))))

(defn- converse-goal
  "`(P b a)` for a ground positive binary `sentence` `(P a b)` with `a` distinct from `b`
  whose functor `P`, or a super-predicate of it, carries an `asymmetric` mark
  (`tax/props-over`, read from `context`, or anywhere for `'?ctx`), else nil."
  [kb sentence context]
  (when (and (ground-goal? sentence) (= 3 (count sentence)))
    (let [[pred a b] sentence
          tax        (reasoning/taxonomy kb)]
      (when (and (not= a b)
                 (seq (tax/props tax :asymmetric))
                 (seq (tax/props-over tax :asymmetric pred (when-not (= '?ctx context) context))))
        (list pred b a)))))

(defn converse-claim
  "The **known-true** claim that reaches the converse `(P b a)` of the stored `sentence`
  `(P a b)` by preservation, while an `asymmetric` mark on `P` or on a super-predicate of
  it holds at `context` — `{:sentence (P b a) :context :claim handle :handles [handle …]
  :class}` — or nil.  The mark says the two tuples cannot both hold, so the inherited
  converse and the stored tuple are a nogood as `clashing-claim`'s pair is.  A claim
  stated at `(P b a)` itself is a stored converse, which the `asymmetric` family pairs
  (`decide/note-candidate!`), and is excluded.  The reading and the choice among several
  claims are `clashing-claim`'s (`strongest-claim`)."
  [kb sentence context]
  (with-memo
    (when-let [goal (converse-goal kb sentence context)]
      (let [pred (nm/functor goal)
            args (vec (nm/args goal))
            poss (positions kb pred context)]
        (when (seq poss)
          (let [sv (filter #(and (= :for (:polarity %))
                                 (st/known-true? (:class %))
                                 (not= (:tuple %) args))
                           (claims kb goal context true))]
            (when-let [[c hs] (strongest-claim kb (by-position poss 2) args sv context)]
              {:sentence goal
               :context  context
               :claim    (:handle c)
               :handles  hs
               :class    (:class c)})))))))

(defn claims-stored?
  "Does the store hold a sentex whose functor is `pred` or a predicate below it
  (`tax/specs-global`), in either polarity, in any context, believed or not?  False means
  `claims` of `pred` is empty for every goal and every reader, since every claim is a
  stored statement on a predicate the matcher fans `pred` over.  The closure is unscoped
  because it answers for every reader: a scoped fan is a subset of it.  One index count
  per predicate in the closure, memoized on `pred`."
  [kb pred]
  (memoized [::claims-stored pred]
            #(let [idx (:index kb)]
               (boolean (some (fn [f] (pos? (reads/stored-count-with-functor idx f)))
                              (tax/specs-global (reasoning/taxonomy kb) pred))))))

(defn separated-preserved
  "The predicates a stored declaration names (`declared`) that the taxonomy separates from
  the type `s` at `context` (`tax/separation-test`) and that some stored claim states
  (`claims-stored?`), sorted: a membership `(s x)` denies `(P x)` for each.  At `'?ctx`
  the read is unscoped and exempts no pair, the union of what every reader separates.  A
  type no separation reaches reads no declaration.  Memoized on `[s context]`."
  [kb s context]
  (memoized [::separated s context]
            #(when (symbol? s)
               (when-let [sep? (separation-test (reasoning/taxonomy kb) s context)]
                 (filterv (fn [p] (and (sep? p) (claims-stored? kb p)))
                          (into (sorted-set) (comp (map first) (remove #{s}))
                                (memoized [::declared] (fn [] (declared kb)))))))))

(defn separated-claims
  "The **known-true** claims that reach `(P x)` by preservation, for each `P` the taxonomy
  separates at `context` from the type `S` of the stored membership `sentence` `(S x)`
  (`separated-preserved`), as `clashing-claim` answers: one `{:sentence (P x) :context
  :claim :handles :class}` per `P` some claim reaches.  A claim stated at `(P x)` itself
  is a stored membership the `disjoint` family pairs with `sentence`, and is excluded.
  The separating declarations are not among `:handles`: each asker reads the separation
  again, as `converse-claim`'s reads the `asymmetric` mark."
  [kb sentence context]
  (with-memo
    (when (and (ground-goal? sentence) (= 2 (count sentence)))
      (let [[s x] sentence]
        (into []
              (keep (fn [pred]
                      (let [poss (positions kb pred context)]
                        (when (seq poss)
                          (let [sv (filter #(and (= :for (:polarity %))
                                                 (st/known-true? (:class %))
                                                 (not= (:tuple %) [x]))
                                           (claims kb (list pred x) context true))]
                            (when-let [[c hs] (strongest-claim kb (by-position poss 1) [x] sv
                                                               context)]
                              {:sentence (list pred x)
                               :context  context
                               :claim    (:handle c)
                               :handles  hs
                               :class    (:class c)}))))))
              (separated-preserved kb s context))))))

(defn- separation-supports
  "Each way a reader can see the type `s` separated from `pred`, as `{:handles :contexts}`:
  the contexts of one derivation (`tax/disjointness-witnesses`), and the supporters stated
  in them of the declarations separating the two (`tax/separating-keys`, unscoped and
  exempting nothing).  Memoized per pair: discovery asks one pair once per membership of
  `s` it reads."
  [kb s pred]
  (memoized [::separation-supports s pred]
            (fn []
              (let [tax  (reasoning/taxonomy kb)
                    recs (:records kb)
                    sups (into [] (comp (mapcat #(tax/visible-supporters tax % nil))
                                        (distinct)
                                        (map (fn [h] [h (:context (p/get-sentex recs h))])))
                               (tax/separating-keys tax s pred nil (constantly false)))]
                (into #{}
                      (map (fn [w]
                             {:handles  (into #{} (keep (fn [[h c]] (when (or (nil? c) (contains? w c)) h)))
                                              sups)
                              :contexts w}))
                      (tax/disjointness-witnesses tax s pred))))))

(defn denial-readings
  "Each reading of a claim that denies `sentence` by preservation, read from every
  context at once, as `{:handles :contexts}`: the claim and what the reading rests on
  (`claim-supports`), and the contexts those are stated in.  Empty when nothing reaches
  `sentence`'s tuple to deny it.  `discovery/preserving-entry` asks `clashing-claim` from
  the most general contexts that see a reading with `sentence` and no except hiding one of
  them.

  Read at `'?ctx`, unscoped throughout, and over-approximating: every class of claim, and
  claims `undercut?` would drop, since a claim undercut in the whole KB can survive in a
  reader that does not see the claim undercutting it.  The claim's own tuple and a claim
  stating `sentence` are excluded, as `clashing-claim` excludes them.  The readings of
  `converse-claim`'s converse are named too, each joined by an `asymmetric` statement,
  and those of `separated-claims`' claims, each joined by a way to see the separation
  (`separation-supports`)."
  [kb sentence]
  (with-memo
    (let [neg?  (and (sequential? sentence) (= 'not (nm/functor sentence))
                     (= 2 (count sentence)))
          body  (if neg? (second sentence) sentence)
          cls   (defeat-classes kb)
          hid   (memoize #(exc/closure-excepted-anywhere? kb %))
          reads (fn [goal want]
                  (let [args (vec (nm/args goal))
                        poss (positions kb (nm/functor goal) '?ctx)]
                    (if (empty? poss)
                      #{}
                      (let [by-n (by-position poss (count args))]
                        (into #{}
                              (comp (filter #(and (= want (:polarity %)) (not= (:tuple %) args)))
                                    (mapcat #(cons % (:also %)))
                                    (remove #(= (:sentence %) sentence))
                                    (mapcat (fn [c]
                                              (for [{:keys [hs ctxs]} (claim-supports kb by-n args c '?ctx
                                                                                      cls hid)]
                                                {:handles  (into #{(:handle c)} hs)
                                                 :contexts (into #{(:context c)} ctxs)}))))
                              (claims kb goal '?ctx))))))]
      (if-not (ground-goal? body)
        #{}
        (-> (reads body (if neg? :for :against))
            (into (when-let [goal (when-not neg? (converse-goal kb body '?ctx))]
                    (let [tax  (reasoning/taxonomy kb)
                          mark (into #{}
                                     (mapcat #(tax/prop-supporter-contexts tax :asymmetric %))
                                     (tax/props-over tax :asymmetric (nm/functor body)))]
                      (for [r (reads goal :for), [h c] mark]
                        (-> (update r :handles conj h)
                            (update :contexts #(cond-> % c (conj c))))))))
            (into (when (and (not neg?) (= 2 (count body)))
                    (let [[s x] body]
                      (for [pred (separated-preserved kb s '?ctx)
                            :let [sups (separation-supports kb s pred)]
                            r    (reads (list pred x) :for)
                            w    sups]
                        (-> (update r :handles into (:handles w))
                            (update :contexts into (:contexts w))))))))))))

;; ---- enumerating what a claim licenses -----------------------------------

(defn- goal-bindings
  "The bindings making the literal's argument list `args` the tuple `t`, or nil where
  they cannot: a ground argument must be the tuple's term, and a variable written twice
  must take one value."
  [args t]
  (reduce (fn [b i]
            (let [a (nth args i) v (nth t i)]
              (if (and (symbol? a) (sx/variable? a))
                (if-let [prev (get b a)]
                  (if (= prev v) b (reduced nil))
                  (assoc b a v))
                (if (= a v) b (reduced nil)))))
          {}
          (range (count args))))

(defn- stated-claims
  "`[tuple handle]` for every believed claim of `pred` this literal could inherit from:
  the predicate's extent, with the literal's own ground arguments bound at the positions
  that preserve nothing.  A preserved position is left open even where the literal binds
  it, since the claim licensing that term is stated above it.

  A claim whose stored sentence's own functor is declared symmetric is also read
  backwards, kept where the pattern's ground positions still agree: an open probe
  surfaces only the stored orientation, as the mirror shares its handle.  The `symmetric`
  mark is read unscoped, a superset that `supports-for` narrows at `context`."
  [kb pred args poss context]
  (let [by-n (by-position poss (count args))
        pat  (mapv (fn [i]
                     (let [a (nth args i)]
                       (if (or (by-n (inc i)) (and (symbol? a) (sx/variable? a)))
                         (probe-var i)
                         a)))
                   (range (count args)))
        base (for [[h b] (res/matches-visible kb (cons pred pat) context)
                   :when (jtms/in? (reasoning/tms kb) h)
                   :let  [t (mapv (fn [i]
                                    (let [p (nth pat i)]
                                      (if (= p (probe-var i)) (get b p) p)))
                                  (range (count args)))]
                   :when (every? some? t)]
               [t h])]
    (if-not (= 2 (count args))
      base
      (let [tx   (reasoning/taxonomy kb)
            syms (into #{} (filter #(tax/has-prop? tx :symmetric %))
                       (res/sub-predicates kb pred nil))]
        (if (empty? syms)
          base
          (concat base
                  (for [[t h] base
                        :let  [sxr (p/get-sentex (:records kb) h)
                               f   (some-> sxr :sentence nm/functor)]
                        :when (and f (contains? syms f))
                        :let  [rt [(nth t 1) (nth t 0)]]
                        :when (and (not= rt t)
                                   (every? #(let [pp (nth pat %)]
                                              (or (= pp (probe-var %)) (= pp (nth rt %))))
                                           (range 2)))]
                    [rt h])))))))

(defn- licensed-product
  "Every tuple a claim stated at `w` licenses that the literal's arguments admit — the
  product of the licensed terms at the preserved positions, the claim's own term
  elsewhere, and a ground argument of the literal bound wherever it has one."
  [kb by-n args w context]
  (reduce (fn [tuples i]
            (let [terms (if-let [ps (by-n (inc i))]
                          (let [r (licensed-reach kb ps (nth w i) context)
                                a (nth args i)]
                            (if (and (symbol? a) (sx/variable? a))
                              r
                              (when (contains? r a) #{a})))
                          #{(nth w i)})]
              (for [tp tuples, x terms] (conj tp x))))
          [[]]
          (range (count args))))

(defn solve-with-support
  "Solves the antecedent `literal` by preservation: a seq of `{:bindings :claim
  :handles}`, one per reading of an inherited claim it matches (`supports-for`).  A closed
  literal asks `supports-for` once; an open one enumerates every believed claim of the
  predicate and the tuples it licenses, and asks `supports-for` per tuple.  The diagonal is
  dropped, so the caller unions this with the ordinary matcher (docs/inherit.md,
  \"Forward chaining on a claim nobody stored\")."
  [kb literal context]
  (with-memo
    (when (and (sequential? literal) (seq literal) (symbol? (nm/functor literal))
               (not= 'not (nm/functor literal)) (seq (nm/args literal)))
      (let [pred (nm/functor literal)
            args (vec (nm/args literal))
            poss (positions kb pred context)]
        (when (seq poss)
          (if (every? sx/ground-term? args)
            (not-empty (mapv #(assoc % :bindings {}) (supports-for kb literal context)))
            (let [by-n (by-position poss (count args))]
              ;; realized inside the memo, so the tuples of one literal share its reads
              (into [] (distinct)
                    (for [[w _] (stated-claims kb pred args poss context)
                          t     (licensed-product kb by-n args w context)
                          :when (not= t w)
                          :let  [b (goal-bindings args t)]
                          :when b
                          s     (supports-for kb (cons pred t) context)]
                      (assoc s :bindings b))))))))))

;; ---- which rules an arriving sentence moves ------------------------------

(def crossing-closure-cap
  "The most closure terms `crossing-claim?` reads the slot predicate set at.  The closure is
  `specs-global` of a `genl` edge's lower term together with `genls-global` of its upper
  one, each walked by `tax/specs-global-within`, which stops one term past the cap.  An
  edge whose closure holds more is not narrowed: it moves every predicate preserved along
  `genl`, read off the declarations' relation index with no index read."
  512)

(def permuting-marks
  "The marks under which the matcher reads a stored fact in more than one argument order:
  the functors whose arms install `tax/props :symmetric` and the `:commuting` table, which
  are what `res/matches-hierarchical` permutes a literal by (`sx/commuting-arrangements`).
  A late one moves what a rule's antecedent reaches over facts already stored, so
  `moved-predicates` and `chain/permuting-rejoin-rules` both key on it."
  '[symmetric commutative commutativeInArgs commutativeInArgAndRest])

(def ^:private permuting-mark-set (set permuting-marks))

(defn permuting-mark?
  "Is `f` one of `permuting-marks`?  A set lookup: every placement asks it of its
  conclusion's functor (`special/deduce-lifts`)."
  [f]
  (contains? permuting-mark-set f))

(defn- mark-group
  "The commuting group descriptor a stored mark states, `[:args [p …]]` or `[:rest f]`, or
  nil for anything else — a negated mark included, whose functor is `not`.  The same
  descriptors `special`'s arms install, with `(symmetric P)` read as `[:args [1 2]]`."
  [sentence]
  (let [[f q & more] sentence]
    (when (symbol? q)
      (case f
        symmetric               [:args [1 2]]
        commutative             [:rest 1]
        commutativeInArgAndRest (let [n (first more)]
                                  (when (and (integer? n) (pos? n)) [:rest n]))
        commutativeInArgs       (let [ps (vec (sort (distinct more)))]
                                  (when (and (> (count ps) 1)
                                             (every? #(and (integer? %) (pos? %)) ps))
                                    [:args ps]))
        nil))))

(defn- rearranges?
  "Do the commuting `groups` rearrange the argument list `s` into `t`?  Every position
  outside their components holds the same term in both, and each component holds the
  same terms with the same multiplicity — the arrangements `sx/commuting-arrangements`
  probes, read from the other end."
  [groups s t]
  (let [comps (sx/commuting-components groups (count s))
        moved (into #{} cat comps)
        at    (fn [v c] (frequencies (map #(nth v (dec %)) c)))]
    (and (every? #(or (contains? moved (inc %)) (= (nth s %) (nth t %))) (range (count s)))
         (every? #(= (at s %) (at t %)) comps))))

(def ^:private universal-context
  "Where the engine lifts a permuting mark (`special/universal-context`, which requires this
  namespace and so cannot be read from it)."
  sx/root-context)

(def ^:private permuted-mark-cap
  "The most mark statements on one predicate `permuted-read-supports` searches the
  subsets of.  Past it the reading names every statement it found as one conjunction."
  8)

(defn permuted-read-supports
  "The alternative sets of mark sentexes a read of the stored `sentence` at the argument
  list `tuple` rests on, each a vector of handles, or nil when `tuple` is the stored
  argument list or no believed mark licenses the rearrangement (docs/inference.md,
  \"A fact read in another argument order names the mark that licenses the order\").

  One alternative per minimal set of statements licensing the rearrangement, read off the
  marks stored on the fact's own functor (`tax/prop-supporters`,
  `tax/commuting-supporters`), with no index read (`firing_cost_test`).  Each statement is
  named by the believed sentexes stating it that `context` sees and no other covers, the
  CxUniverse copy where it is believed.  The groups are read unscoped, a superset."
  [kb sentence tuple context]
  (let [s (vec (rest sentence))
        f (nm/functor sentence)]
    (when (and (symbol? f) (not= s tuple) (= (count s) (count tuple)))
      (let [tx    (reasoning/taxonomy kb)
            tms   (reasoning/tms kb)
            recs  (:records kb)
            up    (when-not (sx/variable? context) (tax/context-up tx context))
            ;; `[sentence group [[handle ctx] …]]` per statement, in content order
            marks (->> (concat (when (= 2 (count s)) (tax/prop-supporters tx :symmetric f))
                               (mapcat #(tax/commuting-supporters tx f %)
                                       (tax/commuting-groups tx f)))
                       distinct
                       (keep (fn [h]
                               (when (jtms/in? tms h)
                                 (let [sxr (p/get-sentex recs h)
                                       sen (:sentence sxr)
                                       g   (when (sequential? sen) (mark-group sen))]
                                   (when (and g (or (nil? up) (contains? up (:context sxr))))
                                     [sen g [h (:context sxr)]])))))
                       (group-by (juxt first second))
                       (map (fn [[[sen g] rows]]
                              [sen g (->> (let [rs (mapv #(nth % 2) rows)
                                                u  (filterv #(= universal-context (second %)) rs)]
                                            (if (seq u) u rs))
                                          (sort-by (comp nm/print-key second))
                                          (tax/uncovered tx (fn [[_ c]] [nil (if (nil? c) #{} #{c})])))]))
                       (sort-by (comp nm/print-key first))
                       vec)
            n     (count marks)
            ok?   (fn [idx] (rearranges? (map #(second (nth marks %)) idx) s tuple))
            sets  (if (> n permuted-mark-cap)
                    (let [all (range n)] (when (ok? all) [all]))
                    ;; by size, so a set holding one already found is not minimal
                    (reduce (fn [found mask]
                              (let [idx (filter #(bit-test mask %) (range n))]
                                (if (or (some (fn [fs] (every? (set idx) fs)) found)
                                        (not (ok? idx)))
                                  found
                                  (conj found (vec idx)))))
                            []
                            (sort-by #(Long/bitCount %) (range 1 (bit-shift-left 1 n)))))
            alts  (for [idx sets
                        alt (reduce (fn [alts i]
                                      (for [a alts, [h _] (nth (nth marks i) 2)] (conj a h)))
                                    [[]]
                                    idx)]
                    alt)]
        (not-empty (into [] (distinct) alts))))))

(defonce ^:private crossing-reads
  ;; `{kb-key -> {:decls postings :derived {k value} :read-under s :marks {q #{group}}}}`, one
  ;; entry per KB, keyed by `crossing-key`
  (atom {}))

(defn- crossing-key
  "The key `kb`'s `crossing-reads` entry is held under: its `:unrecovered` atom, which the
  KB owns and which holds a few flags, so an entry keeps no store reachable.  Nil for a
  KB value without one, whose reads are not cached."
  [kb]
  (:unrecovered kb))

(def ^:private crossing-reads-limit
  "How many KBs' entries `crossing-reads` holds before it is cleared wholesale."
  64)

(caches/register-cache
 {:cache    :preservation-crossing
  :label    "Preservation crossing reads"
  :scope    :process
  :unit     "KBs"
  :limit    (caches/limit-thunk :preservation-crossing crossing-reads-limit)
  :counters nil
  :note     (str "Per KB, the argument positions the declarations preserving along genl "
                 "name and the commuting groups the stored marks state, which a genl edge "
                 "reads to decide which preserved predicates it moves. An entry is re-read "
                 "when a declaration functor's or a mark functor's posting moves. Past the "
                 "limit it is cleared wholesale.")
  :read     (fn [_] {:entries (count @crossing-reads)})
  :clear    (fn [kb] (let [k (crossing-key kb)
                           n (if (contains? @crossing-reads k) 1 0)]
                       (swap! crossing-reads dissoc k)
                       n))
  :trim     (fn [_ target] (caches/trim-map! crossing-reads target))})

(defn- store-crossing-read!
  "Merge `f`'s result into `kb`'s `crossing-reads` entry, clearing the cache wholesale when a
  new KB's entry would take it past its bound.  Stores nothing for a KB with no
  `crossing-key`."
  [kb f]
  (when-let [k (crossing-key kb)]
    (swap! crossing-reads
           (fn [m]
             (if (contains? m k)
               (update m k f)
               (caches/assoc-bounded m (caches/limit-of :preservation-crossing crossing-reads-limit)
                                     k (f nil)))))))

(defn- declaration-postings
  "The declaration functors' postings, in `declaration-functors` order: two
  predicate-extent reads.  A declaration stored or removed changes its functor's posting,
  and a handle is never reused, so equal postings hold the same declarations."
  [kb]
  (mapv #(reads/as-stored-with-functor (:index kb) %) declaration-functors))

(defn- declarations-cached
  "The value `compute` answers for `k`, cached in `kb`'s `crossing-reads` entry and keyed on
  `decls`, the `declaration-postings` read before `compute` runs.  A write between the
  read and `compute` leaves an answer newer than its key, which the next read finds
  unequal and reads again."
  [kb decls k compute]
  (let [e (get @crossing-reads (crossing-key kb))]
    (if (and e (= decls (:decls e)) (contains? (:derived e) k))
      (get-in e [:derived k])
      (let [v (compute)]
        (store-crossing-read! kb (fn [e]
                                   (let [e (if (= decls (:decls e))
                                             e
                                             (-> e (assoc :decls decls) (dissoc :derived)))]
                                     (assoc-in e [:derived k] v))))
        v))))

(defn- positions-along
  "`{:preds {P #{n …}} :positions #{n …} :both #{P …}}` — the argument positions every
  stored declaration preserving along `rel` names, per predicate and as one set, and the
  predicates declaring one position along `rel` in both directions, read off the argument
  root at position 3 and one record fetch per declaration.  Global and not
  belief-filtered, for `declared`'s reason.  A negated declaration is in the same root and
  drops out on its shape.  Cached on the declaration postings (`declarations-cached`)."
  [kb rel]
  (declarations-cached
   kb (declaration-postings kb) [:along rel]
   #(let [idx  (:index kb)
          recs (:records kb)
          fs   (reduce (fn [m [f h]]
                         (let [[_ pred n] (:sentence (p/get-sentex recs h))]
                           (if (and (symbol? pred) (integer? n) (pos? n))
                             (update m [pred n] (fnil conj #{}) f)
                             m)))
                       {}
                       (for [f declaration-functors
                             h (reads/as-stored-with-args idx f [[3 rel]])]
                         [f h]))
          m    (reduce (fn [m [[pred n]]] (update m pred (fnil conj #{}) n)) {} fs)]
      {:preds     m
       :positions (into #{} (mapcat val) m)
       :both      (into #{} (keep (fn [[[pred] f]] (when (next f) pred))) fs)})))

(defn- commuting-marks
  "`{q #{group …}}`: the commuting groups every stored mark states, in any context and
  whatever its belief (`permuting-marks`, `mark-group`), a superset for
  `moved-predicates`' reason.  Four predicate-extent reads per call, and the record
  fetches only when a posting differs from the ones the cached answer was read off."
  [kb]
  (let [idx   (:index kb)
        posts (mapv #(reads/as-stored-with-functor idx %) permuting-marks)
        e     (get @crossing-reads (crossing-key kb))]
    (if (and e (contains? e :marks) (= posts (:read-under e)))
      (:marks e)
      (let [recs  (:records kb)
            marks (reduce (fn [m h]
                            (let [sen (:sentence (p/get-sentex recs h))]
                              (if-let [g (and (sequential? sen) (mark-group sen))]
                                (update m (second sen) (fnil conj #{}) g)
                                m)))
                          {}
                          (sequence cat posts))]
        (store-crossing-read! kb #(assoc % :read-under posts :marks marks))
        marks))))

(defn- reach-positions
  "The argument positions a claim on a predicate carrying the commuting groups `groups` can
  hold a term at and still be read at one of the preserved positions `ns`: `ns` itself and
  every position sharing a commuting component with one of them (`sx/commuting-components`,
  which merges overlapping groups as the matcher does).  `:any` when such a component
  reaches past every position named, which only a `:rest` group does — its extent is the
  claim's own arity, so no fixed set of positions covers it."
  [ns groups]
  (if (empty? groups)
    ns
    (let [top   (inc (long (reduce max 1 (concat ns (mapcat (fn [[k v]] (if (= :args k) v [v]))
                                                            groups)))))
          comps (filter #(some (set ns) %) (sx/commuting-components groups top))]
      (if (some #(some #{top} %) comps)
        :any
        (into (set ns) cat comps)))))

(defn- crossings
  "The set of predicates preserved along `genl` that the edge `a → b` moves, or nil where
  no narrowing is read: a closure past `crossing-closure-cap`, or an index store with no
  slot predicate set.  `crossing-claim?` states what it computes.

  The closures are unscoped: the moved set is a trigger over every reader, and each
  re-join reads its rule from the rule's own context."
  [kb a b]
  (let [tax   (reasoning/taxonomy kb)
        cap   (long crossing-closure-cap)
        below (tax/specs-global-within tax a cap)
        above (when below (tax/genls-global-within tax b (- cap (count below))))]
    (when above
      (let [idx    (:index kb)
            {along :preds poss0 :positions both :both} (positions-along kb 'genl)
            ;; {P {q positions-or-:any}}, for each marked sub-predicate q of a declared P
            marked (reduce-kv (fn [m q gs]
                                (reduce (fn [m pr]
                                          (if-let [ns (get along pr)]
                                            (assoc-in m [pr q] (reach-positions ns gs))
                                            m))
                                        m
                                        (tax/genls-global tax q)))
                              {}
                              (commuting-marks kb))
            any    (into both (keep (fn [[pr qs]] (when (some #{:any} (vals qs)) pr))) marked)
            poss   (into poss0 (comp (mapcat vals) (remove keyword?) cat) (vals marked))
            ;; {q #{n …}}: the positions each predicate holds a closure term at
            hits   (reduce (fn [m t]
                             (reduce (fn [m n]
                                       (let [qs (reads/as-stored-predicates-at-arg idx n t)]
                                         (if (nil? qs)
                                           (reduced (reduced nil))
                                           (reduce #(update %1 %2 (fnil conj #{}) n) m qs))))
                                     m
                                     poss))
                           {}
                           (into below above))]
        (when hits
          (reduce-kv
           (fn [acc q ns]
             (reduce (fn [acc pr]
                       (let [ok (or (get-in marked [pr q]) (get along pr))]
                         (if (and ok (or (= :any ok) (some ok ns)))
                           (conj acc pr)
                           acc)))
                     acc
                     (tax/genls-global tax q)))
           any
           hits))))))

(defn- crossing-claim?
  "For the `genl` edge in `body` (`(genl a b)`, or the body under a `not`), the set of
  predicates `P` preserved along `genl` for which a reach a claim on `P` licenses could
  pass through the edge.  A set, so it is also the test `moved-predicates` applies.  nil
  where no narrowing is read, which leaves every declaration on `genl` moved: the edge's
  terms are not both symbols, the closure holds more than `crossing-closure-cap` terms,
  or the index store keeps no slot predicate set.

  A walk through `a → b` runs from a term below `a` to a term above `b`, so a claim whose
  preserved argument lies in neither `specs-global` of `a` nor `genls-global` of `b` has no
  reach across the edge, before or after it changed.  The claim may be on `P` or a
  sub-predicate, in either polarity.  A permuting mark on the claim's predicate widens the
  positions read (`reach-positions`), and a `P` with a `:rest` component at a preserved
  position, or declared at one position in both directions, is in every answer.  The
  closures are global.  The cost is the closure's size times the distinct preserved
  positions, plus four predicate-extent reads for the marks.  Memoized per edge."
  [kb body]
  (let [[_ a b] body]
    (when (and (symbol? a) (symbol? b))
      (memoized [:crossings a b] #(crossings kb a b)))))

(defn- decl-index
  "`{:by-p {P #{R …}} :by-r {R #{P …}} :joint #{P …}}` over the `[P R]` pairs `decls`, so a
  channel reads the pairs naming one predicate or one relation with a map lookup rather
  than a pass over every declaration.  `:joint` holds the predicates preserved along two
  or more relations."
  [decls]
  (let [m (reduce (fn [m [pr r]]
                    (-> m
                        (update-in [:by-p pr] (fnil conj #{}) r)
                        (update-in [:by-r r] (fnil conj #{}) pr)))
                  {:by-p {} :by-r {}}
                  decls)]
    (assoc m :joint (into #{} (keep (fn [[pr rs]] (when (next rs) pr))) (:by-p m)))))

(defn- declaration-index
  "`decl-index` over the `[P R]` pairs `declared` reads, with the pairs under `:pairs`,
  cached on the declaration postings (`declarations-cached`); nil when no declaration is
  stored.  A KB that declares none pays `declarations-exist?`'s two predicate-extent counts,
  and one that does pays the two postings besides."
  [kb]
  (when (declarations-exist? kb)
    (let [di (declarations-cached kb (declaration-postings kb) :decl-index
                                  #(let [ps (declared kb)] (assoc (decl-index ps) :pairs ps)))]
      (when (seq (:pairs di)) di))))

(defn preserved-pairs
  "Every stored declaration's `[P R]` pair (`declared`), off `declaration-index`, or nil
  when none is stored."
  [kb]
  (:pairs (declaration-index kb)))

(defn- among
  "The members of `xs` that `in` holds, walking whichever of the two is smaller.  `in` is a
  set or a map, so membership is `contains?` on either."
  [xs in]
  (if (<= (count xs) (count in))
    (filter #(contains? in %) xs)
    (filter #(contains? xs %) (if (map? in) (keys in) in))))

(defn- joint-genl
  "The predicates of `ps`, each preserved along `genl`, whose reach can run through a
  `genl` edge from a term outside the edge's closures (`crossing-claim?`): those in
  `joint` (`decl-index`'s, preserved along a second relation) or declared `(transitive
  P)`, since a joint reach (`reach`) leaves the `genl` closure and comes back; `crossings`
  answers the predicates preserved along `genl` in both directions.  Read off the stored
  declarations and marks, globally, a superset for `moved-predicates`' reason.  Each
  intersection walks its smaller side (`among`), so the cost does not grow with `ps`."
  [kb joint ps]
  (concat (among ps joint) (among ps (tax/props (reasoning/taxonomy kb) :transitive))))

(defn- moved-in
  "`moved-predicates` over the declarations indexed as `decl-index` indexes them, as
  `[claimed other]`: the predicates moved through the claim channel, and those moved
  through every other channel.  The `genl` closures are global.  A `genl` edge is
  narrowed (`crossing-claim?`) only when `wanted` holds a predicate it would otherwise
  move; otherwise it moves every predicate preserved along `genl`."
  [kb sen {:keys [by-p by-r joint]} wanted]
  (let [body (or (sx/underlying-body sen) sen)
        f    (nm/functor body)
        arg1 (nth body 1 nil)]
    (when (symbol? f)
      (cond
        (contains? declarations f) [nil (when (symbol? arg1) #{arg1})]
        ;; the relations walked along it, and its own self relation
        (= 'transitive f)          [nil (cond-> (into #{} (get by-r arg1))
                                          (contains? by-p arg1) (conj arg1))]
        ;; the mark binds its spec subtree, whose converses `converse-claim` reads
        (= 'asymmetric f)          [nil (when (symbol? arg1)
                                          (into #{} (among (tax/specs-global
                                                            (reasoning/taxonomy kb) arg1)
                                                           by-p)))]
        ;; the permutation is applied per fanned literal on its own mark, so a mark on
        ;; a sub-predicate moves every preserved super it feeds
        (permuting-mark? f)        [nil (when (symbol? arg1)
                                          (into #{} (among (tax/genls-global
                                                            (reasoning/taxonomy kb) arg1)
                                                           by-p)))]
        :else (let [preds (tax/genls-global (reasoning/taxonomy kb) f)]
                ;; a claim on P or on a sub-predicate of it
                [(into #{} (among preds by-p))
                 ;; a fact on a relation some P is preserved along
                 (into #{}
                       (mapcat (fn [r]
                                 (let [ps (get by-r r)]
                                   (if-some [crosses (when (and (= 'genl f) (= 'genl r)
                                                                (some wanted ps))
                                                       (crossing-claim? kb body))]
                                     (into (set (among ps crosses)) (joint-genl kb joint ps))
                                     ps))))
                       (among preds by-r))])))))

(defn channels-read-arguments?
  "Does `moved-channels`' answer for a sentence with functor `f` read its arguments?  True
  for a declaration, `transitive`, `asymmetric`, a permuting mark and `genl`; every other
  functor's answer is a function of `f` alone."
  [f]
  (or (contains? declarations f) (contains? '#{transitive asymmetric genl} f)
      (permuting-mark? f)))

(defn moved-channels
  "`moved-predicates`' answer for `sen` over the `[P R]` pairs `decls`, split by channel:
  `[claimed other]`, the predicates a claim on one of them or on a sub-predicate moves,
  and the predicates every other channel moves.  A caller opens a `with-memo`, which
  indexes `decls` once."
  [kb sen decls wanted]
  (moved-in kb sen (memoized [:decl-index decls] #(decl-index decls)) wanted))

(defn- separation-moved
  "The predicates of `ps` whose `separated-denials` `sen` arriving or leaving can move, as
  `[member any]`: `member` those whose goal at `sen`'s own argument alone moves, and
  `any` those whose every goal may move.  Read unscoped and exempting no pair, a superset
  over every reader.

  * for a membership `(S x)`, in either polarity, those separated from `S`, in `member`;
  * for a `genl` edge `sen` installs (`tax/installed-edges`) whose upper end is
    `tax/separable?`, those separated from the upper end, and those at or below the
    lower end;
  * for any other sentence that moves a separation, those at or below a type
    `tax/sentence-separation-ends` names.

  Taxonomy reads alone, and none for a sentence of no such shape."
  [kb sen ps]
  (let [body (or (sx/underlying-body sen) sen)
        f    (when (seq? body) (nm/functor body))]
    (when (and (symbol? f) (seq ps))
      (let [tx       (reasoning/taxonomy kb)
            args     (nm/args body)
            unary?   (= 1 (count args))
            sep-from (fn [t] (when-let [sep? (separation-test tx t nil)] (filter sep? ps)))
            edges    (filter (fn [[_ b]] (tax/separable? tx b)) (tax/installed-edges body))
            ends     (tax/sentence-separation-ends tx body)]
        [(if unary? (set (sep-from f)) #{})
         (cond-> (into #{} (mapcat (fn [[_ b]] (sep-from b))) edges)
           (seq ends) (into (filter #(some ends (tax/genls-global tx %))) ps))]))))

(defn separation-moved-predicates
  "The preserved predicates whose goals' `separated-denials` `sen` arriving or leaving can
  move (`separation-moved`), for the exception re-check; empty when the KB declares no
  preservation."
  [kb sen]
  (if-let [di (declaration-index kb)]
    (into #{} cat (separation-moved kb sen (keys (:by-p di))))
    #{}))

(defn moved-goal-test
  "A test `(fn [goal] → boolean)`, false only for a goal on a preserved predicate whose
  verdict, and whether it is stated at its own tuple, `sen` arriving or leaving cannot
  move; or nil where every goal may have moved: a declaration, `transitive`,
  `asymmetric`, a permuting mark, a `genl` edge into a predicate some declaration names or
  sits below, an argument that is not a symbol.

  Read at `'?ctx` over the global `genls`.  A claim moves only a goal whose every argument
  is one of the claim's or a term one of them licenses.  A fact on a relation moves only
  a goal with some argument that is an end of the fact or a term one licenses over the
  relations at a position walking it.  A fact on a predicate with a self relation is read
  on both channels.  A membership, a separation or a `genl` edge moves the goals
  `separation-moved` names."
  [kb sen]
  (let [body   (or (sx/underlying-body sen) sen)
        f      (when (sequential? body) (nm/functor body))
        args   (when (symbol? f) (nm/args body))]
    (when-let [{:keys [by-p by-r]} (when (and (seq args) (every? symbol? args)
                                              (not (contains? declarations f))
                                              (not (contains? '#{transitive asymmetric} f))
                                              (not (permuting-mark? f)))
                                     (declaration-index kb))]
      (with-memo
        (let [tx      (reasoning/taxonomy kb)
              preds   (tax/genls-global tx f)
              claimed (among preds by-p)
              selfs   (filter #(some :self? (positions kb % '?ctx)) claimed)
              rels    (into (set (among preds by-r)) selfs)
              ;; a membership test over the reaches rather than their union: the reaches
              ;; are the memo's, which a caller asking for many sentences shares, and a
              ;; broad type's runs to the whole of its closure, which a union would copy
              ;; for each sentence
              reached (fn [prs keep-pos?]
                        (let [sets (into [(set args)]
                                         (map #(if (set? %) % (set %)))
                                         (for [pr prs, ps (vals (group-by :n (positions kb pr '?ctx)))
                                               :when (some keep-pos? ps)
                                               t args]
                                           (licensed-reach kb ps t '?ctx)))]
                          (fn [t] (boolean (some #(contains? % t) sets)))))]
          (when-not (and (= 'genl f)
                         (some #(seq (among (tax/genls-global tx %) by-p)) args))
            (let [every-t (when (seq claimed) (reached claimed any?))
                  some-t  (when (seq rels)
                            (reached (into (set selfs) (mapcat by-r) rels)
                                     #(contains? rels (:rel %))))
                  [member any] (separation-moved kb sen (keys by-p))]
              (when (or every-t some-t (seq member) (seq any))
                (fn [goal]
                  (let [gs (nm/args goal)
                        g  (nm/functor goal)]
                    (boolean (or (not-every? symbol? gs)
                                 (and every-t (every? every-t gs))
                                 (and some-t (some some-t gs))
                                 (contains? any g)
                                 (and (contains? member g) (= args gs))))))))))))))

(defn claim-reach-extent
  "The stored facts of the preserved predicate `pred`, in either polarity, whose tuple the
  claim `sen` (on `pred` or a sub-predicate of it, in either polarity) can reach by
  preservation from some context, as a superset: the handles holding at argument 1 one of
  `sen`'s arguments or a term a believed declaration of `pred` licenses from one
  (`licensed-reach`, read at `'?ctx`).  Every argument order the matcher reads a claim in
  holds its terms among these, and so does the converse an asymmetric predicate is denied
  by.  nil when an argument is not a symbol or the terms outnumber `pred`'s stored
  extent, for a caller to read the extent instead."
  [kb sen pred]
  (with-memo
    (let [args  (nm/args (or (sx/underlying-body sen) sen))
          idx   (:index kb)
          limit (reads/stored-count-with-functor idx pred)
          poss  (positions kb pred '?ctx)
          terms (when (every? symbol? args)
                  (reduce (fn [acc t]
                            (let [acc (into acc (mapcat #(licensed-reach kb % t '?ctx))
                                            (vals (group-by :n poss)))]
                              (if (> (count acc) limit) (reduced nil) acc)))
                          (set args)
                          args))]
      (when terms
        (into #{} (mapcat #(reads/as-stored-with-args idx pred {1 %})) terms)))))

(defn separated-types
  "The types the unscoped taxonomy, exempting no pair, separates from `pred`: each type at
  or below one `tax/separating-partners` names.  The functors of the stored memberships a
  claim of `pred` can deny (`separated-claims`), read as a superset over every reader,
  since the callers re-open candidates each asker reads again."
  [kb pred]
  (memoized [::separated-types pred]
            #(let [tax (reasoning/taxonomy kb)]
               (into #{} (mapcat (fn [y] (conj (tax/specs-global tax y) y)))
                     (tax/separating-partners tax pred nil (constantly false))))))

(defn claim-reach-separated
  "The stored memberships `(S x)` the claim `sen`, on the preserved `pred` or a
  sub-predicate of it, can deny by reaching `(pred x)` from some context
  (`separated-claims`), as a superset: the unary facts at an argument of `sen` or at a
  term a believed declaration of `pred` licenses from one (`licensed-reach`, read at
  `'?ctx`) whose type is one of `separated-types`, or the stored extents of those types
  when the terms outnumber them.  The unary facts are read in every context, a candidate
  set each asker reads again from its own."
  [kb sen pred]
  (with-memo
    (let [types (separated-types kb pred)]
      (if (empty? types)
        #{}
        (let [args  (nm/args (or (sx/underlying-body sen) sen))
              idx   (:index kb)
              recs  (:records kb)
              limit (reduce + (map #(reads/stored-count-with-functor idx %) types))
              poss  (positions kb pred '?ctx)
              terms (when (every? symbol? args)
                      (reduce (fn [acc t]
                                (let [acc (into acc (mapcat #(licensed-reach kb % t '?ctx))
                                                (vals (group-by :n poss)))]
                                  (if (> (count acc) limit) (reduced nil) acc)))
                              (set args)
                              args))]
          (if terms
            (into #{}
                  (filter #(let [s (some-> (p/get-sentex recs %) :sentence)]
                             (and (seq? s) (= 2 (count s)) (contains? types (first s)))))
                  (mapcat #(reads/as-stored-unary-with-arg-global idx %) terms))
            (into #{} (mapcat #(reads/as-stored-with-functor idx %)) types)))))))

(defn edge-reach
  "The stored facts whose questions the `genl` edge `(genl a b)` can move for `pred`, a
  predicate preserved along `genl`, as a superset: the facts of `pred`, in either
  polarity, holding a term of the edge's closure (`specs-global` of `a` with
  `genls-global` of `b`, the joint reaches at a position walking a second relation) at a
  position `pred` is preserved at along `genl` or at the other position of a binary
  converse, and, when a claim of `pred` is stored (`claims-stored?`), the unary facts at
  such a term whose type is one of `separated-types`.  The facts of `pred` are its stored
  extent when the closure reads would outnumber it.  nil when `pred` names no position
  along `genl` or a commuting mark stands on `pred` or below it, for the caller to
  re-open the extent.  Read unscoped."
  [kb a b pred]
  (with-memo
    (let [tax  (reasoning/taxonomy kb)
          poss (positions kb pred '?ctx)
          by-n (group-by :n poss)
          ns   (into #{} (comp (filter #(= 'genl (:rel %))) (map :n)) poss)]
      (when (and (seq ns)
                 (not-any? #(contains? (tax/genls-global tax %) pred) (keys (commuting-marks kb))))
        (let [idx   (:index kb)
              recs  (:records kb)
              ;; a walk against `genl` crosses the edge from `a` to `b`, one along it from
              ;; `b` to `a`
              terms (if (some #(next (relation-keys (by-n %))) ns)
                      (into #{}
                            (for [n ns, {:keys [rel along?]} (relation-keys (by-n n))
                                  :when (= 'genl rel)
                                  :let  [[from to] (if along? [b a] [a b])]
                                  t     (concat (licensed-reach kb (by-n n) from '?ctx)
                                                (reach kb (by-n n) to '?ctx))]
                              t))
                      (into (tax/specs-global tax a) (tax/genls-global tax b)))
              at    (into ns (comp (filter #{1 2}) (map #(- 3 %))) ns)
              types (when (claims-stored? kb pred) (separated-types kb pred))]
          (cond-> (if (> (* (count terms) (count at)) (reads/stored-count-with-functor idx pred))
                    (set (reads/as-stored-with-functor idx pred))
                    (into #{} (for [t terms, n at, h (reads/as-stored-with-args idx pred {n t})] h)))
            (seq types)
            (into (filter #(let [s (some-> (p/get-sentex recs %) :sentence)]
                             (and (seq? s) (= 2 (count s)) (contains? types (first s)))))
                  (mapcat #(reads/as-stored-unary-with-arg-global idx %) terms))))))))

(defn moved-predicates
  "The preserved predicates whose licensed claims `sen` may have moved, over five
  channels (docs/inherit.md, \"Forward chaining on a claim nobody stored\"):

  * a claim on `P` or a sub-predicate of it;
  * a fact on a relation `R` some `P` is preserved along, a `genl` or `genlCx` edge
    included; a `genl` edge moves only the `P` `crossing-claim?` names, unless its closure
    passes `crossing-closure-cap`;
  * the declaration itself, which names `P` at argument 1;
  * `(transitive R)`, `(asymmetric P)`, and a permuting mark (`permuting-marks`);
  * a membership of a type a separation holds apart from `P`, and a separation or `genl`
    edge that moves which types those are (`separation-moved`).

  The reads are global and not belief-filtered: over-selecting costs a join that derives
  what is already there.  The pairs are `declared`'s, indexed (`declaration-index`); a KB
  that declares nothing pays two predicate-extent counts.  The three-argument form takes
  the `[P R]` pairs, for a caller asking per member of a settle's region under one
  `with-memo`; `wanted` names the predicates whose `genl` narrowing the caller acts on."
  ([kb sen] (moved-predicates kb sen nil any?))
  ([kb sen decls] (moved-predicates kb sen decls any?))
  ([kb sen decls wanted]
   (if-let [di (when (and (sequential? sen) (seq sen))
                 (if decls
                   (memoized [:decl-index decls] #(decl-index decls))
                   (declaration-index kb)))]
     (let [[claimed other] (moved-in kb sen di wanted)]
       (-> (set claimed)
           (into other)
           (into cat (separation-moved kb sen (keys (:by-p di))))))
     #{})))

(defn rejoin-rules
  "The forward rules to re-join in full because `sen` moved what a preserved predicate
  licenses (every rule with an antecedent on a `moved-predicates` member), or nil.  Keyed
  on the antecedent index, since `(genl chihuahua dog)` moves a `typeLargerThan` antecedent
  whose predicate no walk from `genl` reaches."
  [kb sen]
  (let [idx      (:index kb)
        rules-on (memoize #(reads/as-stored-rules-by-antecedent-global idx %))]
    (when-let [ps (seq (moved-predicates kb sen nil #(seq (rules-on %))))]
      (let [rs (into #{} (mapcat rules-on) ps)]
        (when (seq rs) rs)))))

(defn licensing-functors
  "The functors whose facts move what a preserved predicate `preds` accepts (a set, or a
  membership test) licenses, or nil: `moved-predicates`' channels named as functors, for
  a caller that enumerates stored facts to hand to `rejoin-rules`.

  The declaration functors, `transitive`, `asymmetric`, and each relation some `P` in
  `preds` is preserved along with its sub-predicates over the global closure.  A claim on
  `P` is not named, since the caller reads those already, and the permuting marks are not
  named, since the engine lifts each into `CxUniverse`.  Where a separation holds a `P`
  apart from some type, the `separated-types`, `disjoint`, the
  `tax/separation-functors` and the disjoint metatypes are named too.  Two predicate-extent
  counts for a KB that declares nothing."
  [kb preds]
  (when-let [{:keys [by-p]} (declaration-index kb)]
    (let [tx   (reasoning/taxonomy kb)
          rels (into #{} (comp (filter #(preds (key %))) (mapcat val)) by-p)
          seps (into #{} (comp (map key) (filter preds)
                               (mapcat #(separated-types kb %)))
                     by-p)]
      (when (seq rels)
        (cond-> (into (into #{'transitive 'asymmetric} (keys declarations))
                      (mapcat #(tax/specs-global tx %))
                      rels)
          (seq seps) (-> (into seps)
                         (into tax/separation-functors)
                         (conj 'disjoint)
                         (into (tax/disjoint-metatypes tx))))))))

(caches/register-derived
 {:id :R5 :label "Inherit question memo" :kind :pass :keyed-by :value :reads [:index :T1]
  :holds-content? false
  :retired-by {} :computed :pass :imaged? false :var #'*memo*
  :note "positions, reach and whole reach for one question or one discovery pass; whole reach 1,048,576 terms, 65,536 a walk"})

(caches/register-derived
 {:id :R6 :label "Preservation crossing reads" :cache :preservation-crossing :kind :cache
  :holds-content? false
  :keyed-by :global :reads [:index :records]
  :retired-by {:stored :I :removed :I :respelled :I :caches-cleared :W :recover :W}
  :computed :read :imaged? false :var #'crossing-reads
  :value (fn [kb] (get @crossing-reads (crossing-key kb)))
  :note "keyed by the KB's `:unrecovered` atom: re-read when the declaration postings or the mark postings are not equal"})

;; ---- a second route at a reader -----------------------------------------
;; A rule firing whose witness path a reader hides stands there when each goal it matched
;; through a reach is reached by a believed claim over edges the reader does not hide: a
;; backward search from the goal, stopping at the first claim (docs/nmtms.md, "Where the
;; layer stops").

(defn- claim-in?
  "Does a claim stated of the term `t` reach the goal term `x` along the declaration
  `pos` from `context`: for `genl`, membership of the upper of the two in the lower's
  scoped ancestor set (`tax/genls`, held in the closure cache across reads), which reads
  the edges `context` sees and believes, and `witness-terms` for a fact relation."
  [kb {:keys [rel along?] :as pos} x t context]
  (if (= 'genl rel)
    (let [[sub super] (if along? [t x] [x t])]
      (scoped #(contains? (tax/genls (reasoning/taxonomy kb) sub context) super)))
    (contains? (witness-terms kb pos x context) t)))

(defn- stated-reached?
  "Is the ground `goal` stated at `context` of its own functor or of a sub-predicate the
  edges `context` believes and sees reach it from: the predicates the store holds a fact
  of with the goal's first argument (`reads/as-stored-predicates-at-arg`), each walked up
  to the goal's functor, when they number fewer than the functor's sub-predicates counted
  unscoped, and the matcher's sub-predicate fan otherwise.  The count is unscoped because
  it only weighs the two seeds, which answer the same; the walk up reads the scoped
  ancestor set, as `claim-in?` does."
  [kb goal context]
  (let [pred  (nm/functor goal)
        args  (nm/args goal)
        tx    (reasoning/taxonomy kb)
        preds (some-> (reads/as-stored-predicates-at-arg (:index kb) 1 (first args)) set)]
    (if (and preds (nil? (tax/specs-global-within tx pred (count preds))))
      (boolean (some (fn [l] (and (scoped #(contains? (tax/genls tx l context) pred))
                                  (seq (res/matches-visible kb (apply list l args) context))))
                     (sort preds)))
      (boolean (seq (res/matches-visible kb goal context))))))

(defn- goal-reached?
  "Is the ground positive `goal` reached at `context` by a believed claim: a stated match
  of its functor or a sub-predicate (`stated-reached?`), or, at a preserved position, a
  claim whose term reaches the goal's over edges `context` sees and believes
  (`claim-in?`, or `reach` at a position walking several relations).  Stops at the first
  claim found.  Seeded off the stored claims with the
  goal's ground arguments when they number no more than the goal term's reach
  (`extent-size`, `product-size`), and off the reach's terms otherwise.  The reach is
  weighed unscoped, an upper bound on the scoped one, since the weighing never changes the
  answer."
  [kb goal context]
  (binding [*memo* (atom {})]
    (let [pred (nm/functor goal)
          args (vec (nm/args goal))
          poss (positions kb pred context)
          by-n (by-position poss (count args))]
      (if (empty? by-n)
        (stated-reached? kb goal context)
        (let [tx   (reasoning/taxonomy kb)
              ;; a reach weighed by the unscoped walk, which stops at `limit` and reads no
              ;; edge's visibility: an upper bound on the scoped reach, and weighing never
              ;; changes the answer
              size (fn [i limit]
                     (let [x   (nth args i)
                           lim (long (min limit Long/MAX_VALUE))]
                       (reduce (fn [n {:keys [rel along?] :as pos}]
                                 (let [m (if (= 'genl rel)
                                           (if-let [c (if along?
                                                        (tax/specs-global-within tx x lim)
                                                        (tax/genls-global-within tx x lim))]
                                             (count c)
                                             ##Inf)
                                           (count (witness-terms kb pos x context)))
                                       n (+ n m)]
                                   (if (> n limit) (reduced ##Inf) n)))
                               0 (by-n (inc i)))))
              ;; a position walking several relations keeps `slots`' joint reach
              sl   (into [] (map-indexed
                             (fn [i s]
                               (if (and (:reach s) (not (next (relation-keys (by-n (inc i))))))
                                 (let [x (nth args i)]
                                   (assoc s
                                          :in?  (fn [t] (boolean (some #(claim-in? kb % x t context)
                                                                       (by-n (inc i)))))
                                          :size #(size i %)))
                                 s)))
                         (slots kb poss args context))
              fwd  (vec (range (count args)))
              ext  (extent-size kb pred sl fwd false context product-ceiling)]
          (boolean
           (seq (if (<= ext (product-size sl ext))
                  (believed-matches kb (probe-sentence pred sl fwd (constantly nil))
                                    sl fwd context nil false nil)
                  (mapcat (fn [tuple]
                            (believed-matches kb (probe-sentence pred sl fwd tuple)
                                              sl fwd context tuple false nil))
                          (product-tuples sl))))))))))

(defn- firing-goals
  "`[goals stated]` for the rule firing `j`: the antecedent literals of its rule that no
  antecedent of `j` states, instantiated from its conclusion and the stated antecedents,
  and the antecedent handles that state a literal.  nil when `j`'s informant is not a rule
  or a goal is left open."
  [kb j]
  (let [recs (:records kb)
        rsx  (when (integer? (:informant j)) (p/get-sentex recs (:informant j)))
        conc (some-> (p/get-sentex recs (:consequence j)) :sentence)]
    (when-let [lits (and conc (seq (:antecedent rsx)))]
      (let [antes (into [] (keep (fn [h] (when-let [x (p/get-sentex recs h)] [h (:sentence x)])))
                        (:antecedents j))
            [b open stated]
            (reduce (fn [[b open stated] lit]
                      (if-let [[h b'] (some (fn [[h s]] (when-let [b' (res/unify lit s b)] [h b']))
                                            antes)]
                        [b' open (conj stated h)]
                        [b (conj open lit) stated]))
                    [(res/unify (:consequent rsx) conc) [] #{}]
                    lits)
            ;; a variable only an open literal names takes its term from the claim the
            ;; literal was reached from: a stated antecedent of the literal's functor and
            ;; arity, read position by position past the positions the reach moved
            loose (fn [b lit]
                    (or (some (fn [[_ s]]
                                (when (and (seq? s) (= (nm/functor s) (nm/functor lit))
                                           (= (count s) (count lit)))
                                  (reduce (fn [b [l t]]
                                            (if (and (sx/variable? l) (not (contains? b l))) (assoc b l t) b))
                                          b (map vector (rest lit) (rest s)))))
                              antes)
                        b))
            goals (when b
                    (mapv (fn [lit] (let [g (res/substitute lit b)]
                                      (if (ground-goal? g) g (res/substitute lit (loose b lit)))))
                          open))]
        (when (and (seq goals) (every? ground-goal? goals))
          [goals stated])))))

#_{:clj-kondo/ignore [:unused-private-var]}
(def ^:private second-route
  "The walks `vaelii.impl.except`'s read walk asks for a second route, reached through
  `wiring/route-reach`, `wiring/firing-goals` and `wiring/goal-reach`: `:reach` answers
  whether `reader` reaches `b` from `a` over the fact relation `rel`, `:goals` a rule
  firing's goals, and `:goal-reach` whether `reader` reaches a ground goal from a claim."
  {:reach      (fn [kb rel a b reader]
                 (binding [*memo* (atom {})]
                   (contains? (witness-terms kb {:rel rel :along? false} a reader) b)))
   :goals      firing-goals
   :goal-reach goal-reached?})
