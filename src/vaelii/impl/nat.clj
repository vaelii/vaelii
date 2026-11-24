;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.nat
  "Non-atomic terms (NATs): the write-mode reify (mint, materialize result types), the
  `natFormula` map's `K → E` read, display expansion, the correspondence maintenance, and
  the reads the rename, orphan and re-spelling maintenance runs on.  The read mode and the
  `E → K` lookups are `nat-read`'s.  Stores through `wiring/assert-sentence`.  See
  docs/nat.md."
  (:require [vaelii.impl.datetime :as dt]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.wiring :as wiring]))

(def nat-scheme-tag
  "The one-letter scheme prefix of every content-named reified constant.  `a` is
  SHA-256 truncated to 96 bits in base62, so a name is this letter and 17 digits.  The
  letter keeps the name a readable token and versions the scheme (docs/nat.md, Write
  path)."
  "a")

(def ^:private base62-alphabet
  "The 62 digits in ASCII order (`0-9A-Za-z`), so a base62 name sorts as the bytes behind
  it."
  "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz")

(defn- base62
  "Byte array `b` as an unsigned big-endian integer, base62-encoded (`base62-alphabet`)
  and left-padded with `0` to `width` digits, so the name is fixed-length."
  [^bytes b width]
  (let [sixty-two (BigInteger/valueOf 62)]
    (loop [n (BigInteger. 1 b), acc ()]
      (if (pos? (.signum n))
        (recur (.divide n sixty-two)
               (cons (.charAt ^String base62-alphabet (.intValue (.mod n sixty-two))) acc))
        (let [s (apply str acc)]
          (str (apply str (repeat (max 0 (- width (count s))) \0)) s))))))

(defn- content-name
  "The constant name expression `E` reifies to: `nat-scheme-tag` and the first 96 bits
  of SHA-256 over `E`'s printed form, in base62 left-padded to 17 digits (62^17 > 2^96 ≥
  62^16).  Print limits are bound off, so an ambient `*print-length*` or `*print-level*`
  cannot elide part of `E` and give two expressions one name."
  [E]
  (let [s   (binding [*print-length* nil *print-level* nil *print-meta* false]
              (pr-str E))
        d   (.digest (java.security.MessageDigest/getInstance "SHA-256")
                     (.getBytes ^String s "UTF-8"))
        b96 ^bytes (java.util.Arrays/copyOf ^bytes d 12)]
    (str nat-scheme-tag (base62 b96 17))))

(defn constant-for
  "The reified constant expression `E` names in reserved namespace `ns` (`nat` or `cx`),
  a function of `E`'s content alone (`content-name`).  A hash collision gives one constant
  two expressions, the case `authoritative-expression` reads."
  [ns E]
  (symbol ns (content-name E)))

;; ---- the reifiable-function presence check --------------------------------
;; docs/nat.md, The reifiable-function presence check.

(defn any-reified-constants?
  "Does the KB declare a `reifiable_function` or store a `natFormula` map?  The presence
  check of the maintenance a reified constant owes.  The in-memory read first, then one
  O(1) functor count, which admits a KB whose only constants are `cx/` contexts."
  [kb]
  (or (nat-read/any-reifiable-functions? kb)
      (pos? (reads/stored-count-with-functor (:index kb) 'natFormula))))

(def context-type
  "The type a `(result F context)` declaration names (docs/context-nat.md)."
  'context)

(defn context-function-believed?
  "True iff CxUniverse believes a `(result head context)` declaration: stated in a
  context CxUniverse sees and hidden by no `except` or `defeat` in force at CxUniverse
  (`res/supporter-visible?`).  A read admits a context slot `(head a…)` on this."
  [kb head]
  (and (symbol? head)
       (boolean (some #(res/supporter-visible? kb (:id %) nat-read/universal-context)
                      (kb/sentexes-matching kb (list 'result head context-type) '?ctx)))))

;; ---- index-backed lookups: `E → K` and `K → E`, both `natFormula` reads ---

(defn authoritative-expression
  "The content-least of `exprs`: the one expression a reified constant denotes when an
  unrepaired collision maps it to several.  Every reader of the map takes this one
  (docs/nat.md, Rename and remove)."
  [exprs]
  (nm/min-by-content-key identity exprs))

(defn- own-maps
  "`k`'s own `natFormula` sentexes among `sentexes`: stored in CxUniverse and naming `k`."
  [k sentexes]
  (filter (fn [sx]
            (let [s (:sentence sx)]
              (and (= nat-read/universal-context (:context sx))
                   (= 'natFormula (nm/functor s))
                   (= k (second s)))))
          sentexes))

(defn- denoted-expression
  "The expression the `natFormula` rows `maps` give their constant: the authoritative one
  of the stated rows', else of every row's (`authoritative-expression`).  A merge's twin
  of another constant's map is not stated, and the constant does not name its expression."
  [kb maps]
  (let [tms (reasoning/tms kb)]
    (authoritative-expression
     (keep #(nth (:sentence %) 2 nil) (or (seq (filter #(jtms/premise? tms (:id %)) maps)) maps)))))

(defn nat-expression
  "The NAT expression a reified constant denotes, or nil: `denoted-expression` over the
  believed rows its map's match answers, a retired constant's being its representative's."
  [kb nat-sym]
  (when (nat-read/reified-nat-symbol? nat-sym)
    (denoted-expression kb (kb/sentexes-matching kb (list 'natFormula nat-sym '?e)
                                                 nat-read/universal-context))))

(defn- result-targets
  "The distinct arg2s of believed `(<pred> head ?t)` facts, read globally as the mint
  reads.  With `context`, through the declarations visible from it
  (`nat-read/visible-result-targets`), as a check reads (docs/nat.md, Typing an
  application that is never minted).  Globally, a KB storing no `pred` fact answers
  empty off one functor count, as `any-result-declarations?` reads it, before the match:
  every mint asks both `result` and `genlResult`."
  ([kb pred head]
   (when (pos? (reads/stored-count-with-functor (:index kb) pred))
     (->> (kb/sentexes-matching kb (list pred head '?t) '?ctx)
          (keep #(nth (:sentence %) 2))
          distinct)))
  ([kb pred head context]
   (nat-read/visible-result-targets kb pred head context)))

(defn- result-declarations
  "`{T [handle …]}` of the believed `(<pred> f T)` facts, read globally as `result-targets`
  reads them."
  [kb pred f]
  (when (pos? (reads/stored-count-with-functor (:index kb) pred))
    (reduce (fn [m sx] (update m (nth (:sentence sx) 2) (fnil conj []) (:id sx)))
            {} (kb/sentexes-matching kb (list pred f '?t) '?ctx))))

(defn- hold-on!
  "Store `sentence` in CxUniverse under `opts` and justify it by `[map-h d]` under
  `informant` for each handle `d` of `decls`, so it leaves when the map or the last
  declaration does.  A row stated before keeps its premise mark; any other is stored at
  the class the justifications confer, and the premise mark the store placed is dropped."
  [kb sentence opts informant map-h decls]
  (let [univ    nat-read/universal-context
        tms     (reasoning/tms kb)
        before  (kb/find-sentex-handle kb sentence univ)
        stated? (and before (jtms/premise? tms before))
        mono?   #(= :monotonic (jtms/defeat-class tms %))
        h       (if stated?
                  before
                  (wiring/assert-sentence kb sentence univ
                                          (if (and map-h (seq decls))
                                            (assoc opts :strength (if (and (mono? map-h) (some mono? decls))
                                                                    :monotonic
                                                                    :default))
                                            opts)))]
    (when (and (integer? h) map-h (seq decls))
      (doseq [d decls
              :let [antes (kb/antecedent-order kb [map-h d])]
              :when (not (jtms/has-justification? tms informant antes h))]
        (let [just (jtms/->just (p/next-id (:records kb)) informant antes h {} :monotonic)]
          (p/put-justification (:records kb) just)
          (jtms/add-justification tms just)))
      (when-not stated?
        (p/unmark-premise! (:records kb) h)
        (jtms/suspend-premise tms h)))
    h))

(defn- result-arg-declared
  "The positions the `(resultArg f n)` declarations stored anywhere name, behind the
  functor count `nat-read/visible-result-types` reads."
  [kb f]
  (when (pos? (reads/stored-count-with-functor (:index kb) 'resultArg))
    (result-targets kb 'resultArg f)))

(defn result-types
  "Types `T` with `(result head T)`: what an application of `head` is an instance of.
  Globally, or with `context` through the declarations visible from it
  (`nat-read/visible-result-types`).  Given an application `(head a…)` in place of
  `head`, adds the argument at each position a `(resultArg head n)` declares."
  ([kb head] (result-types kb head nil))
  ([kb head context]
   (if context
     (nat-read/visible-result-types kb head context)
     (let [rs (result-targets kb 'result (if (sequential? head) (first head) head))]
       (if (sequential? head)
         (distinct (concat rs (nat-read/result-arg-types head (result-arg-declared kb (first head)))))
         rs)))))

(defn genl-result-types
  "Types `T` with `(genlResult head T)`: what an application of `head` is a subtype of.
  Globally, or with `context` through the declarations visible from it.  `head` may be an
  application, as `result-types` takes it."
  ([kb head] (result-targets kb 'genlResult (if (sequential? head) (first head) head)))
  ([kb head context]
   (result-targets kb 'genlResult (if (sequential? head) (first head) head) context)))

(def any-result-declarations?
  "`nat-read/any-result-declarations?`."
  nat-read/any-result-declarations?)

;; ---- the corresponding predicate (docs/nat.md, The corresponding predicate) ---

(defn minted-applications
  "The `[expression constant]` pairs minted for function `f` in argument position, read
  off the inverted term index for `f`."
  [kb f]
  (->> (kb/find-sentexes kb f)
       (filter #(and (= nat-read/universal-context (:context %))
                     (= 'natFormula (nm/functor (:sentence %)))
                     (jtms/in? (reasoning/tms kb) (:id %))))
       (keep (fn [{[_ k E] :sentence}]
               (when (and (seq? E) (= f (first E)) (nat-read/reified-object-symbol? k)) [E k])))
       distinct))

;; ---- display / export ----------------------------------------------------

(defn- contains-reified-nat?
  "True iff `form` contains a reified NAT constant anywhere.  `sequential?` so the
  walk descends a rule's antecedent vector, the one vector `canon` keeps."
  [form]
  (boolean (some nat-read/reified-nat-symbol? (tree-seq sequential? seq form))))

(defn- expand-through
  "`form` with every constant `expand?` accepts replaced, recursively, by the expression
  `expression-of` answers for it, kept where that is nil.  A vector rebuilds as a vector."
  [expression-of form expand?]
  (cond
    (expand? form) (if-let [e (expression-of form)]
                     (expand-through expression-of e expand?)
                     form)
    (and (seq? form) (contains-reified-nat? form))
    (apply list (map #(expand-through expression-of % expand?) form))
    (and (vector? form) (contains-reified-nat? form))
    (mapv #(expand-through expression-of % expand?) form)
    :else form))

(defn expand-expression
  "`form` with every reified constant replaced, recursively, by the expression it maps
  to.  `form` itself, the same object, when it holds no reified constant.  A vector
  rebuilds as a vector.  `expand?` narrows which constants are expanded."
  ([kb form] (expand-expression kb form nat-read/reified-nat-symbol?))
  ([kb form expand?] (expand-through #(nat-expression kb %) form expand?)))

;; ---- the reify walk: one walk, a mint leaf and a read leaf ---------------

(defn- permuted-reifiable?
  "Is `f` a `reifiable_function` a `symmetric` or commuting mark holds of: one whose
  constant is named by its expression sorted (`nat-read/sorted-expression`), so a row
  naming it keeps no written argument order?  Read unscoped, as the store spells."
  [tax f]
  (and (symbol? f) (tax/has-prop? tax :reifiable f)
       (or (tax/has-prop? tax :symmetric f) (boolean (seq (tax/commuting-groups tax f))))))

(defn permuted-reifiable-functions
  "The `reifiable_function` functions `permuted-reifiable?` holds of, as a set."
  [kb]
  (let [tax (reasoning/taxonomy kb)]
    (into #{} (filter #(permuted-reifiable? tax %)) (tax/props tax :reifiable))))

(defn permutes-reified?
  "Does `form` hold an application of a function `permuted-reifiable?` holds of, at any
  nesting?"
  [kb form]
  (let [tax (reasoning/taxonomy kb)]
    (boolean (some #(and (sequential? %) (seq %) (permuted-reifiable? tax (first %)))
                   (tree-seq sequential? seq form)))))

(defn names-reifiable-nat?
  "Does sentence `s` hold a ground reifiable NAT the write-mode reify would replace, at a
  position `nat-read/reify-in` visits?  False on a KB declaring no reifiable function, and
  otherwise one walk that rebuilds nothing.  The modal mark is read KB-wide, as
  `reify-in` reads it."
  [kb s]
  (and (nat-read/any-reifiable-functions? kb)
       (let [modal (:modal (tax/mention-marks (reasoning/taxonomy kb)))]
         ((fn walk [s]
            (cond
              (nat-read/reifiable-ground-nat? kb s) true
              (vector? s) (boolean (some walk s))
              (and (seq? s) (seq s))
              (cond
                (contains? res/nat-quoting-predicates (first s)) false
                (res/attitude-application? modal s) (walk (second s))
                :else (boolean (some walk (rest s))))
              :else false))
          s))))

(defn queue-split-uses!
  "Queue `[:reifiable-use f]` on `:respell` for each function `f` a ground application in
  `sentence` names whose `reifiable_function` mark, or a permuting mark of which, some
  reader does not believe (`split-reifiable?`, `res/split-mark-entries`): the write
  stores the use reified, and the settle's reconcile stores the spelling each reader
  reads (`chain/reconcile-reified!` with `marks-moved?` false).  One walk and no index
  read on a KB whose reifiable and permuting marks every reader believes."
  [kb sentence]
  (when (names-reifiable-nat? kb sentence)
    (let [fs (into #{} (comp (filter #(and (sequential? %) (seq %) (symbol? (first %))))
                             (map first)
                             (filter #(tax/has-prop? (reasoning/taxonomy kb) :reifiable %)))
                   (tree-seq sequential? seq sentence))
          split (filter #(or (nat-read/split-reifiable? kb %) (res/split-mark-entries kb %)) fs)]
      (when (seq split)
        (swap! (reasoning/respell kb) into (map #(vector :reifiable-use %)) split)))))

;; ---- rename / remove detection (docs/nat.md, Rename and remove) ----------

(defn writer-spelled?
  "Does a premise in CxUniverse, believed or not, map reified constant `k` to an expression
  whose content name (`constant-for`) is another constant?  A term operation restates such
  a map as written and leaves the rows naming `k` alone (docs/nat.md, Rename and remove)."
  [kb k]
  (let [tms (reasoning/tms kb)]
    (boolean (some #(let [sx (p/get-sentex (:records kb) %) [f c E] (:sentence sx)]
                      (and (= 'natFormula f) (= k c) (= nat-read/universal-context (:context sx))
                           (jtms/premise? tms %) (not= k (constant-for (namespace k) E))))
                   (reads/as-stored-with-args (:index kb) 'natFormula {1 k})))))

(defn- collision-key
  "A `natFormula` sentence's expression and whether its constant is a `cx/` one: two
  constants collide only under one key, so an expression's `nat/` and `cx/` constants are
  no collision (`in-namespace?`)."
  [[_ k e]]
  [(nm/context? k) e])

(defn- collision-groups
  "`[key [k …]]` per `collision-key` that more than one constant among the `natFormula`
  sentences maps, the constants sorted."
  [nat-formula-sentences]
  (keep (fn [[key sents]]
          (let [ks (sort (distinct (map second sents)))]
            (when (next ks) [key ks])))
        (group-by collision-key nat-formula-sentences)))

(defn- group-collisions
  "`[survivor [dup …]]` per expression that more than one constant names in one reify
  namespace, survivor lexicographically smallest so the choice is content-keyed."
  [nat-formula-sentences]
  (map (fn [[_ ks]] [(first ks) (rest ks)]) (collision-groups nat-formula-sentences)))

(defn colliding-constant-groups
  "`[survivor [dup …]]` per expression more than one believed constant maps.  Reads the
  whole map in CxUniverse; the maintenance after a write reads `collision-merges`'s rows."
  [kb]
  (group-collisions (map :sentence (kb/sentexes-matching kb '(natFormula ?k ?e) nat-read/universal-context))))

(defn- formula-rows
  "The believed `natFormula` sentexes, in any context, naming a member of the equality
  class of one of `terms`.  A migration twin restates its expression under a class member,
  so every row of a collision a merge of `terms` can have created is among them.  One
  term-index intersection per member."
  [kb terms]
  (let [tx  (reasoning/taxonomy kb)
        tms (reasoning/tms kb)]
    (into #{} (comp (mapcat #(tax/equiv-class tx %))
                    (distinct)
                    (mapcat #(kb/find-sentexes-all kb ['natFormula %]))
                    (filter #(and (= 'natFormula (nm/functor (:sentence %)))
                                  (jtms/in? tms (:id %)))))
          terms)))

(defn- formula-rows-joined
  "The believed `natFormula` sentexes a `genlCx` edge can have joined into a collision.
  `shown` holds the contexts a reader under the edge's lower context sees through the edge
  alone, and `terms` the merged terms the edge shows or derived.  The rows are those stored
  in `shown`, each row sharing a constant with one of them (a twin migration restated at a
  reader), the rows `formula-rows` reads for `terms`, and each row sharing an expression
  with one of those.  No row below the lower context is read unless one of them names it."
  [kb shown terms]
  (let [tms   (reasoning/tms kb)
        ix    (:index kb)
        fetch (fn [hs] (keep #(let [sx (p/get-sentex (:records kb) %)]
                                (when (and sx (jtms/in? tms (:id sx))) sx))
                             hs))
        at    (fn [pos xs] (mapcat #(fetch (reads/as-stored-with-args ix 'natFormula {pos %}))
                                   (distinct xs)))
        rows  (when (seq shown) (fetch (reads/as-stored-with-args-in ix 'natFormula {} (set shown))))]
    (into #{} (at 2 (map #(nth (:sentence %) 2)
                         (concat (at 1 (map #(second (:sentence %)) rows))
                                 (formula-rows kb terms)))))))

(defn- minted-for
  "The sentences `mint-nat!` writes about the constant `k` it minted for expression `E`,
  re-derived from the declarations the mint read: `(T k)` per believed `(result F T)` and
  `(genl k T)` per `(genlResult F T)`, `F` being `E`'s function.  Empty for a `cx/`
  constant, whose mint writes only its map."
  [kb k E]
  (if (nat-read/reified-context-symbol? k)
    #{}
    (into #{}
          (when (any-result-declarations? kb)
            (let [head (first E)]
              (concat (map #(list % k) (result-types kb head))
                      (map #(list 'genl k %) (genl-result-types kb head))))))))

(defn- nat-bookkeeping-of?
  "Is `sx` one of constant `k`'s bookkeeping sentexes: its `natFormula` map, or a sentence
  `minted` (a delay of `minted-for`) holds?  The delay is forced only for a sentex that is
  not the map."
  [k minted sx]
  (let [s (:sentence sx)]
    (or (and (= 'natFormula (nm/functor s)) (= k (first (nm/args s))))
        (and (= nat-read/universal-context (:context sx)) (contains? @minted s)))))

(defn- minted-delay
  "A delay of `minted-for` over the expression `k` denotes, empty when it denotes none."
  [kb k]
  (delay (if-let [E (nat-expression kb k)] (minted-for kb k E) #{})))

(defn- entailed-from?
  "Is `sx` a record the argument-type entailment derives from sources `own-source?`
  accepts alone: not a premise, and every justification a mint (`kb/mint-informant?`,
  under an argument declaration's or a `resultArg`'s rule) whose source handle
  `own-source?` accepts?  A symbol informant an argument declaration names
  (`tax/arg-declaration-props`) counts as a mint too."
  [kb own-source? sx]
  (let [tms (reasoning/tms kb)
        h   (:id sx)
        js  (keep #(jtms/justification tms %) (jtms/supports tms h))]
    (and (not (jtms/premise? tms h))
         (seq js)
         (every? #(let [i (:informant %)]
                    (and (or (kb/mint-informant? kb i)
                             (and (symbol? i) (contains? tax/arg-declaration-props i)))
                         (own-source? (first (:antecedents %)))))
                 js))))

(defn- projected-from?
  "Is `sx` a projection of a constant's map: not a premise, and every justification
  drawn under the correspondence (`res/correspondence-predicate`) from a source handle
  `map?` accepts (docs/nat.md, The corresponding predicate)?"
  [kb map? sx]
  (let [tms (reasoning/tms kb)
        h   (:id sx)
        js  (keep #(jtms/justification tms %) (jtms/supports tms h))]
    (and (not (jtms/premise? tms h))
         (seq js)
         (every? #(and (= res/correspondence-predicate (:informant %)) (some map? (:antecedents %)))
                 js))))

(defn own-sentex-test
  "A test of whether a stored sentex naming constant `k` is `k`'s own rather than a use:
  its bookkeeping (`nat-bookkeeping-of?`), a projection of its map (`projected-from?`),
  for a context a `genlCx` edge the structural producer computed
  (`nat-read/computed-genlCx-edge?`), or a record the argument-type entailment derives
  from `k`'s own sentexes alone (`entailed-from?`), read transitively over `sentexes`.
  `E` is the expression `k` maps to, and `sentexes` the term-index answer for `k`."
  [kb k E sentexes]
  (let [minted (delay (minted-for kb k E))
        by-id  (delay (into {} (map (juxt :id identity)) sentexes))
        map?   (fn [h] (when-let [m (get @by-id h)]
                         (let [s (:sentence m)] (and (= 'natFormula (nm/functor s)) (= k (second s))))))
        ctx?   (nat-read/reified-context-symbol? k)]
    (letfn [(own? [seen sx]
              (or (nat-bookkeeping-of? k minted sx)
                  (projected-from? kb map? sx)
                  (and ctx? (nat-read/computed-genlCx-edge? kb sx))
                  (entailed-from? kb
                                  (fn [h] (and (not (contains? seen h))
                                               (when-let [src (get @by-id h)]
                                                 (own? (conj seen h) src))))
                                  sx)))]
      (fn [sx] (own? #{(:id sx)} sx)))))

(defn- own-reading
  "`k`'s stored sentexes and its own-sentex test (`own-sentex-test`).  Nil when no
  believed `natFormula` maps `k`, or when `k` is a `cx/` constant with a non-empty extent,
  read by one `count-in-context` before the term-index read."
  [kb k]
  (let [ctx? (nat-read/reified-context-symbol? k)]
    (when-not (and ctx? (pos? (long (reads/stored-count-in-context (:index kb) k))))
      (let [all  (kb/find-sentexes kb k)
            live (filterv #(jtms/in? (reasoning/tms kb) (:id %)) all)]
        (when-let [E (denoted-expression kb (own-maps k live))]
          {:all all :own? (own-sentex-test kb k E all)})))))

(defn- every-own?
  "Is every sentex of `reading` (`own-reading`) its constant's own, or a handle
  `own-handle?` accepts?"
  [{:keys [all own?]} own-handle?]
  (every? #(or (own-handle? (:id %)) (own? %)) all))

(defn orphan?
  "Is the reified constant `k` an orphan: is every stored sentex naming it one of its own
  (`own-sentex-test`)?  False when no believed `natFormula` maps `k`, and for a `cx/`
  constant with a non-empty extent.  Uses count by storage; only the map read follows
  belief.  Decided against the authoritative expression, the one `bookkeeping-handles`
  retracts for (docs/nat.md, Rename and remove).  A handle `own-handle?` accepts counts
  as `k`'s own."
  ([kb k] (orphan? kb k (constantly false)))
  ([kb k own-handle?]
   (boolean (some-> (own-reading kb k) (every-own? own-handle?)))))

(defn orphaned-constants
  "Every reified constant the KB maps that is an orphan (`orphan?`).  Reads the whole
  map; a teardown reads `orphans-named-by`."
  [kb]
  (->> (kb/sentexes-matching kb '(natFormula ?k ?e) nat-read/universal-context)
       (map (fn [{[_ k _] :sentence}] k))
       distinct
       (filter nat-read/reified-nat-symbol?)
       (filterv #(orphan? kb %))))

(defn reified-nats-in
  "Every reified constant `form` names, at any nesting, in a list or a vector."
  [form]
  (into #{} (filter nat-read/reified-nat-symbol?) (tree-seq sequential? seq form)))

(defn- constants-named-by
  "Every reified constant the `sentexes` name: in the sentence at any nesting, and a
  `cx/` constant in the context slot."
  [sentexes]
  (into #{} (mapcat (fn [sx]
                      (cond-> (reified-nats-in (sx/sentence-of sx))
                        (nat-read/reified-context-symbol? (:context sx)) (conj (:context sx)))))
        sentexes))

(defn bookkeeping-handles
  "The handles of constant `k`'s bookkeeping sentexes, stored, believed or not: its
  `natFormula` map and what `minted-for` says the mint wrote.  A `cx/` constant's is its
  map alone; the computed `genlCx` edges go by the dependency-directed sweep.  Realized
  before it returns, because the caller retracts what it lists and the bookkeeping test
  reads `k`'s map (docs/nat.md, Rename and remove)."
  [kb k]
  (let [minted (minted-delay kb k)]
    (into [] (comp (filter #(nat-bookkeeping-of? k minted %))
                   (map :id)
                   (distinct))
          (kb/find-sentexes kb k))))

(defn bookkeeping-of?
  "Is the sentex `sx` one of constant `k`'s bookkeeping sentexes (`bookkeeping-handles`)?"
  [kb k sx]
  (nat-bookkeeping-of? k (minted-delay kb k) sx))

;; ---- write-mode reify: mint + result-type materialization ----------------

(defn departed-map
  "`[k E]` for `sentence` `(natFormula k E)` with `k` an object constant, else nil: the
  pair a map leaving the store takes with it."
  [sentence]
  (when (and (seq? sentence) (= 'natFormula (first sentence)))
    (let [[_ k E] sentence]
      (when (and (nat-read/reified-object-symbol? k) (sequential? E)) [k E]))))

(defn support-maps
  "The object constants whose `natFormula` map is a premise the support of the believed
  handles among `hs` reaches, read up the justifications of every handle that is no
  premise."
  [kb hs]
  (let [tms (reasoning/tms kb)]
    (loop [seen #{}, stack (filterv #(jtms/in? tms %) hs), ks #{}]
      (if-let [h (peek stack)]
        (let [stack (pop stack)]
          (cond
            (contains? seen h)    (recur seen stack ks)
            (jtms/premise? tms h) (recur (conj seen h) stack
                                         (if-let [[k] (some-> (p/get-sentex (:records kb) h) :sentence departed-map)]
                                           (conj ks k)
                                           ks))
            :else                 (recur (conj seen h)
                                         (into stack (comp (keep #(jtms/justification tms %))
                                                           (mapcat #(cond-> (vec (:antecedents %))
                                                                      (integer? (:informant %)) (conj (:informant %)))))
                                               (jtms/supports tms h))
                                         ks)))
        ks))))

(defn orphans-in-cycle
  "The orphans among `candidates`, read jointly.  A constant is one when every stored
  sentex naming it is its own (`orphan?`), or is derived and read OUT by
  `jtms/grounded-in-region` with the bookkeeping of every orphan forced OUT.  A candidate
  with a premise use, a use believed without that bookkeeping, or a stored use OUT that
  is not its own, is none (docs/nat.md, Rename and remove)."
  [kb candidates]
  (let [tms         (reasoning/tms kb)
        derived-in? #(and (jtms/in? tms %) (not (jtms/premise? tms %)))
        readings    (into {} (keep #(some->> (own-reading kb %) (vector %)))
                          (into #{} (filter nat-read/reified-nat-symbol?) candidates))
        plain       (into #{} (keep (fn [[k r]] (when (every-own? r (constantly false)) k))) readings)
        open        (into #{} (keep (fn [[k r]] (when (and (not (plain k)) (every-own? r derived-in?)) k)))
                          readings)]
    (loop [ks open]
      (if (empty? ks)
        (vec (sort plain))
        (let [{:keys [region in]} (jtms/grounded-in-region
                                   tms (into #{} (mapcat #(bookkeeping-handles kb %)) (into plain ks)))
              rests-on? #(and (contains? region %) (not (contains? in %)) (not (jtms/premise? tms %)))
              ks'       (into #{} (filter #(orphan? kb % rests-on?)) ks)]
          (if (= ks' ks)
            (vec (sort (into plain ks)))
            (recur ks')))))))

(defn orphans-named-by
  "The orphans among the constants the removed `sentexes` named and the constants `extra`
  names, read jointly (`orphans-in-cycle`): the candidate set of one round of a
  teardown's sweep."
  ([kb sentexes] (orphans-named-by kb sentexes nil))
  ([kb sentexes extra]
   (orphans-in-cycle kb (into (constants-named-by sentexes) extra))))

(defn- hold-result-types!
  "Materialize the types the `result` and `genlResult` declarations of `head` give the
  `nat/` constant `k`: `(T k)` and `(genl k T)`, each justified by `k`'s map `mh` and its
  declaration (`hold-on!`), stored under `opts`."
  [kb k head mh opts]
  (let [rs (result-declarations kb 'result head)]
    (doseq [t (result-types kb head)]
      (hold-on! kb (list t k) opts 'result mh (get rs t))))
  (let [gs (result-declarations kb 'genlResult head)]
    (doseq [t (genl-result-types kb head)]
      (hold-on! kb (list 'genl k t) opts 'genlResult mh (get gs t)))))

(defn mint-nat!
  "Mint the reified constant `K` for the ground NAT expression `E` in reify namespace `ns`
  (`cx/` for a context slot, `nat/` for an argument) and return it.  Asserts `(natFormula
  K E)` in CxUniverse at `:monotonic` and, for a `nat/` constant, the materialized result
  types, each justified by the map and its declaration (`hold-on!`), then queues `K` for the correspondence derivations (`nat-read/note-values`,
  the projection among them).  The result types chain as `chain?` says; the map chains
  only when a `resultArg` of `E`'s function is declared (docs/defenses.md, The mint's
  natFormula fact does not chain)."
  ([kb E] (mint-nat! kb E nat-read/nat-namespace true))
  ([kb E ns chain?]
   (let [head (first E)
         ctx? (= nat-read/context-namespace ns)
         k    (constant-for ns E)
         univ nat-read/universal-context
         opts {:strength :monotonic :chain? chain?}]
     (binding [nat-read/*minting?* true nat-read/*mint-chains?* chain?]
       ;; a `resultArg` of `head` types `k` off this fact (`checks/result-arg-rows`)
       (let [mh (wiring/assert-sentence kb (list 'natFormula k E) univ
                                        (assoc opts :chain? (and chain? (not ctx?)
                                                                 (boolean (seq (result-arg-declared kb head))))))]
         (when-not ctx?
           (hold-result-types! kb k head mh opts))))
     ;; after the result types, which the projection is arg-checked against
     (when-not ctx? (nat-read/note-values kb [(list 'natFormula k E)] true))
     k)))

(defn reify-or-mint-nat
  "Reify a ground NAT `form` to its term in reify namespace `ns` (default `nat/`) for a
  write stored in `context` (CxUniverse when nil): nested NAT arguments first, then the
  existing term of the expression in its `nat-read/sorted-expression` order
  (`existing-term`), else a fresh mint of that expression (`mint-nat!`).  A quoting
  function's argument is a mention and is not reified (docs/nat.md, Typing an application
  that is never minted)."
  ([kb form] (reify-or-mint-nat kb form nat-read/nat-namespace true nil))
  ([kb form ns chain? context]
   (let [E (if (sx/quoting-functor? (first form))
             (apply list form)
             (nat-read/sorted-expression
              kb (apply list (first form)
                        (map #(if (nat-read/reifiable-ground-nat? kb %)
                                (reify-or-mint-nat kb % nat-read/nat-namespace chain? context)
                                %)
                             (rest form)))))]
     (or (nat-read/existing-term kb E ns context true) (mint-nat! kb E ns chain?)))))

(defn maybe-reify-nats
  "Replace every ground reifiable NAT subterm of `sentence`, written in `context`
  (CxUniverse when nil), with its reified constant, minting as needed.  Returns
  `sentence` on a KB declaring no `reifiable_function`."
  ([kb sentence context] (maybe-reify-nats kb sentence true context))
  ([kb sentence chain? context]
   (if (nat-read/any-reifiable-functions? kb)
     (nat-read/reify-in kb sentence #(reify-or-mint-nat %1 %2 nat-read/nat-namespace chain? context))
     sentence)))

(defn context-application?
  "True iff `form` is a ground application headed by a symbol: what a context slot reifies
  to a `cx/` constant, whatever is declared about the head.  Decided by the form alone,
  so a write stores the same set in every arrival order (docs/context-nat.md)."
  [form]
  (and (sequential? form) (seq form) (symbol? (first form)) (sx/ground-term? form)))

(defn readable-context-application?
  "True iff `form` is a `context-application?` whose head CxUniverse believes denotes
  contexts (`context-function-believed?`): what a read admits as a context slot."
  [kb form]
  (and (context-application? form) (context-function-believed? kb (first form))))

(defn- fold-declarations
  "`[position fold]` of each believed `(contextArgFold f position fold)`, in content order."
  [kb f]
  (when (pos? (reads/stored-count-with-functor (:index kb) 'contextArgFold))
    (->> (kb/sentexes-matching kb (list 'contextArgFold f '?p '?g) '?ctx)
         (map #(vec (drop 2 (:sentence %))))
         distinct
         (nm/sort-by-content-key identity))))

(defn- spelling-positions
  "The position of each believed `(contextArgCalendarSpelling f position)`, as a set."
  [kb f]
  (when (pos? (reads/stored-count-with-functor (:index kb) 'contextArgCalendarSpelling))
    (into #{} (comp (map #(nth (:sentence %) 2)) (filter int?))
          (kb/sentexes-matching kb (list 'contextArgCalendarSpelling f '?p) '?ctx))))

(defn- inner-application
  "The application of `f` the term `x` names, or nil: `x` itself, or the expression a
  stated `natFormula` row of a `cx/` constant gives it (`nat-read/stated-map-expression`),
  else its `nat-expression`.  A fold spells no slice through a merge's twin of its map."
  [kb f x]
  (let [e (if (nat-read/reified-context-symbol? x)
            (or (authoritative-expression
                 (keep #(nat-read/stated-map-expression kb x %)
                       (reads/as-stored-with-args (:index kb) 'natFormula {1 x})))
                (nat-expression kb x))
            x)]
    (when (and (seq? e) (= f (first e))) e)))

(defn context-form
  "The context application `form` in the spelling it reifies under: the argument at each
  believed `(contextArgCalendarSpelling F p)` position in its `datetime/calendar-spelling`,
  every argument in the store's canonical form (`sx/canonical-subterm` under
  `res/store-marks`), and while argument `p` names an application of the same function,
  for a believed `(contextArgFold F p G)`, the inner application's argument `p` with each
  other argument the `G` application of the inner and the outer argument there.  Any
  other term is itself (docs/context-nat.md)."
  [kb form]
  (if-not (context-application? form)
    form
    (let [f     (first form)
          marks (res/store-marks kb)
          spell (spelling-positions kb f)
          canon #(sx/canonical-subterm
                  (if (seq spell)
                    (apply list (map-indexed (fn [i a] (if (spell i) (dt/calendar-spelling a) a)) %))
                    %)
                  marks)
          decls (fold-declarations kb f)
          fold  (fn [form]
                  (some (fn [[p g]]
                          (when-let [inner (and (int? p) (< 0 p (count form))
                                                (inner-application kb f (nth form p)))]
                            (when (= (count inner) (count form))
                              (canon (apply list f (for [j (range 1 (count form))]
                                                     (if (= j p)
                                                       (nth inner j)
                                                       (list g (nth inner j) (nth form j)))))))))
                        decls))]
      (loop [form (canon form) seen #{}]
        (let [folded (when-not (contains? seen form) (fold form))]
          (if folded (recur folded (conj seen form)) form))))))

(defn maybe-reify-context
  "Reify a context slot `(F …)` to its `cx/` constant, in its `context-form` spelling
  (docs/context-nat.md).  With `mint?` (the write path) any `context-application?`
  reifies, minting as needed.  Without it (a read) only a
  `readable-context-application?` does, resolving to an existing term or `no-match`.  Any
  other slot passes through unchanged.  `chain?` is the write's `:chain?`, which a mint
  takes (`mint-nat!`)."
  ([kb context mint?] (maybe-reify-context kb context mint? false))
  ([kb context mint? chain?]
   (if (if mint? (context-application? context) (readable-context-application? kb context))
     (if mint?
       (reify-or-mint-nat kb (context-form kb context) nat-read/context-namespace chain? nil)
       ;; the read leaf, so a slot the write path stored under a `rewriteOf` target
       ;; resolves to it
       (nat-read/reify-nat-for-read kb (context-form kb context) nat-read/context-namespace nil))
     context)))

(defn existing-context
  "The `cx/` constant (or `rewriteOf` target) the context application `form` already
  resolves to, or nil when none was minted — the dedup half of `maybe-reify-context`'s
  write path, read in its `context-form` spelling and without the declaration a read
  needs."
  [kb form]
  (let [k (nat-read/reify-nat-for-read kb (context-form kb form) nat-read/context-namespace nil true)]
    (when-not (= nat-read/no-match k) k)))

(defn context-for-check
  "The context `assert` stores a sentex in for the slot `context`, minting nothing: for a
  `context-application?`, its `existing-context`, else the `cx/` constant `constant-for`
  names for the expression, which no stored sentex names.  Any other slot passes through.
  `vaelii.core/check` reads the slot through this, so its checks read the context
  `maybe-reify-context` mints."
  [kb context]
  (if (context-application? context)
    (or (existing-context kb context)
        (constant-for nat-read/context-namespace (context-form kb context)))
    context))

(defn term-for-check
  "The term `assert` reifies the ground reifiable application `form` written in `context`
  to, minting nothing: its existing term, else the `nat/` constant `constant-for` names for
  `form` as written, which no stored sentex names."
  [kb form context]
  (let [k (nat-read/reify-nat-for-read kb form nat-read/nat-namespace context true)]
    (if (= nat-read/no-match k) (constant-for nat-read/nat-namespace form) k)))

(defn heads-for-check
  "`sentence` with each literal head that is a ground reifiable application read as
  `term-for-check` reads it, and every argument as written.  `vaelii.core/check`,
  `assert-inert` and the application-input check read a head through this, so they read
  the predicate `maybe-reify-nats` gives the sentence."
  [kb sentence context]
  (if (nat-read/any-reifiable-functions? kb)
    (nat-read/reify-in kb sentence (fn [_ form] form) #(term-for-check %1 %2 context))
    sentence))

(defn- collisions-among
  "The merges that restore the 1:1 constant↔expression map in each context reading a
  collision among the believed `natFormula` sentexes `rows`: there, each other constant
  is equated with the lexicographically smallest one.  One `[(equals survivor dup) L
  [row row]]` per pair of rows mapping the two to one expression.  A context reads the rows
  stored in the contexts it sees, and a pair a visible equality already merges is skipped.
  A context that does not see CxUniverse reads no collision among CxUniverse's rows
  (docs/nat.md, Rename and remove).  Only a row whose `collision-key` another row's
  constant shares is tested against a context's view."
  [kb rows]
  (let [tx     (reasoning/taxonomy kb)
        shared (into #{} (map first) (collision-groups (map :sentence rows)))
        cands  (filterv #(shared (collision-key (:sentence %))) rows)]
    (for [L               (when (seq cands)
                            (nm/sort-by-content-key (juxt #(count (tax/context-up tx %)) nm/print-key)
                                                    compare
                                                    (into #{} (map :context) rows)))
          :let            [seen   (filterv #(tax/sees? tx L (:context %)) cands)
                           groups (group-collisions (map :sentence seen))
                           ;; `seen` by constant, each group in `seen`'s order
                           by-k   (when (seq groups) (group-by #(second (:sentence %)) seen))]
          [survivor dups] groups
          dup             dups
          :when           (not (res/same-class-in? kb survivor dup L))
          rs              (by-k survivor)
          rd              (by-k dup)
          :when           (= (nth (:sentence rs) 2) (nth (:sentence rd) 2))]
      [(list 'equals survivor dup) L [(:id rs) (:id rd)]])))

(defn collision-merges
  "The collision repair a just-asserted `sentence` owes, as `collisions-among`'s merges.
  An equality reads the rows naming its terms' classes, a `natFormula` the rows naming its
  expression's merged arguments, and a `genlCx` edge `formula-rows-joined`'s rows for
  `edge-joins`, a delay of `{:shown contexts :terms merged-terms}`.  A `natFormula` also
  reads the rows of its expression as spelled when a merge's twin is among them
  (docs/nat.md, Rename and remove).  Reads only what the sentence can have joined, so a
  collision an import stored stays until something asks `colliding-constant-groups`.
  `nat-maintenance` derives each merge from its two rows."
  [kb sentence edge-joins]
  (let [tx (reasoning/taxonomy kb)]
    (cond
      (kb/equality-sentence? sentence)
      (collisions-among kb (formula-rows kb (filter symbol? (rest sentence))))

      (and (= 'natFormula (first sentence)) (seq? (nth sentence 2 nil)))
      (let [[_ _ E] sentence
            tms     (reasoning/tms kb)
            ts      (filter #(and (symbol? %) (tax/merged? tx %)) (rest E))
            spelled (filterv #(jtms/in? tms (:id %)) (nat-read/rows-naming kb 'natFormula E))]
        (when (or (seq ts) (some #(not (jtms/premise? tms (:id %))) spelled))
          (collisions-among kb (into (formula-rows kb ts) spelled))))

      (and (= 'genlCx (first sentence)) (symbol? (second sentence))
           (seq (tax/equality-edges tx)))
      (let [{:keys [shown terms]} @edge-joins]
        (collisions-among kb (formula-rows-joined kb shown terms))))))

(defn- reconcile-declared-result!
  "Materialize a `(result F T)` or `(genlResult F T)` that arrived *after* constants were
  minted for `F`: each one gets the `(T K)` or `(genl K T)` the mint writes when the
  declaration comes first, justified as the mint justifies it (`hold-on!`).  A no-op for any other
  sentence, and for a function nothing has been minted for.  A late `resultArg` reaches
  the `natFormula` facts through `special/entail-existing`."
  [kb sentence]
  (when (and (contains? '#{result genlResult} (first sentence))
             (= 3 (count sentence)))
    (let [[p f t] sentence]
      (when (and (symbol? f) (symbol? t) (nat-read/reifiable-function? kb f))
        (let [decls (get (result-declarations kb p f) t)]
          (doseq [[E k] (minted-applications kb f)]
            (hold-on! kb (if (= 'genlResult p) (list 'genl k t) (list t k)) {:strength :monotonic}
                      p (kb/find-sentex-handle kb (list 'natFormula k E) nat-read/universal-context)
                      decls)))))))

(defn- reconcile-stated-map!
  "Materialize the result types of a `nat/` constant `K` whose `(natFormula K E)` map is
  asserted rather than minted, as a text KB's reload asserts a mint's map.  `K` gets the
  `(T K)` and `(genl K T)` the mint writes (`hold-result-types!`), justified by the stored
  map.  So a map stated after `E`'s function's `result` declaration holds the
  justifications a mint or a late declaration (`reconcile-declared-result!`) leaves.  Only
  a mint's own map is read: one whose `K` is the constant `E` names (`constant-for`).  A
  no-op for any other sentence or map, and for an `E` whose function is not a reifiable
  function."
  [kb sentence]
  (when (and (= 'natFormula (first sentence)) (= 3 (count sentence)))
    (let [k (second sentence)]
      (when (nat-read/reified-object-symbol? k)
        (doseq [{mh :id [_ _ E] :sentence} (own-maps k (kb/find-sentexes kb k))
                :when (and (seq? E)
                           (= k (constant-for nat-read/nat-namespace E))
                           (nat-read/reifiable-function? kb (first E)))]
          (hold-result-types! kb k (first E) mh {:strength :monotonic}))))))

(defn reconcile-nats!
  "The reified-constant maintenance a just-asserted `sentence` owes beside the collision
  repair (`collision-merges`): a result declaration reaching the constants minted before
  it, and a stated map reaching the result declarations stored before it.
  `nat-maintenance/reconcile-assert` calls it behind `any-reified-constants?`, and queues
  the correspondence derivations itself."
  [kb sentence]
  (reconcile-declared-result! kb sentence)
  (reconcile-stated-map! kb sentence))

;; ---- a reifiable mark moving: the reads `chain/reconcile-reified!` runs on --
;; docs/nat.md, A reifiable mark moving.

(defn respelled
  "`sentence` as the write path spells it under the marks believed now: every object
  constant expanded to the expression it maps to, then every ground reifiable application
  reified again (`maybe-reify-nats`), minting what has no term yet.  Equal to `sentence`
  when no mark it depends on has moved.  `context` is where the row is stored."
  [kb sentence context]
  (maybe-reify-nats kb (expand-expression kb sentence nat-read/reified-object-symbol?) context))

(defn applies?
  "Does `sentence` hold an application of `f`, at any nesting?"
  [f sentence]
  (boolean (some #(and (sequential? %) (= f (first %))) (tree-seq sequential? seq sentence))))

(defn written-as
  "`form` with every object constant expanded, recursively, to the expression it maps to,
  each key of `departed` (`{k E}`, constants whose map left the store) to its value."
  [kb form departed]
  (expand-through #(or (get departed %) (nat-expression kb %)) form nat-read/reified-object-symbol?))

(defn- quoting-row?
  "Is `sx` a quoting predicate's row, whose payload is a mention and does not move?"
  [sx]
  (contains? res/nat-quoting-predicates (nm/functor (sx/sentence-of sx))))

(defn- region-from
  "The stored sentexes a walk from term `root` reaches, believed or not: the rows
  `(root-uses sxs)` picks out of `root`'s term-index answer, and each use of an object
  constant whose stored map's expression holds a term already reached, at any nesting.
  Left out: a quoting predicate's row, a constant's own sentexes (`own-sentex-test`), and
  the uses of a constant an equality retired.  Nil when `root-uses` answers nil.  One
  term-index read per term reached."
  [kb root root-uses]
  (loop [todo [root] seen #{root} rows {}]
    (if (empty? todo)
      (vals rows)
      (let [t    (peek todo)
            sxs  (vec (kb/find-sentexes kb t))
            maps (fn [sx] (let [s (:sentence sx)]
                            (when (and (= 'natFormula (nm/functor s))
                                       (= nat-read/universal-context (:context sx))
                                       (nat-read/reified-object-symbol? (second s))
                                       (some #{t} (tree-seq sequential? seq (nth s 2 nil))))
                              (second s))))
            ;; a constant an equality retired is not re-spelled (docs/nat.md, What
            ;; reification does not cover)
            rep  #(tax/representative (reasoning/taxonomy kb) %)
            ks   (into [] (comp (keep maps) (remove seen) (filter #(= % (rep %))) (distinct)) sxs)
            uses (if (= t root)
                   (root-uses sxs)
                   (let [own? (if-let [E (denoted-expression
                                          kb (own-maps t (filter #(jtms/in? (reasoning/tms kb) (:id %)) sxs)))]
                                (own-sentex-test kb t E sxs)
                                (constantly false))]
                     (into [] (remove #(or (quoting-row? %) (own? %))) sxs)))]
        (when uses
          (recur (into (pop todo) ks) (into seen ks) (into rows (map (juxt :id identity)) uses)))))))

(defn stranded-uses
  "The stored uses, believed or not, of object constant `k` once no stored `natFormula`
  maps it, `E` being the expression its departed map held: every sentex naming `k` that
  is neither a quoting predicate's row nor `k`'s own (`own-sentex-test`), and every use
  of a constant whose stored map's expression names `k`, at any nesting (`region-from`).
  Nil while a map of `k` is stored, since `respell-region` reaches those uses."
  [kb k E]
  (region-from kb k (fn [sxs]
                      (when (empty? (own-maps k sxs))
                        (let [own? (own-sentex-test kb k E sxs)]
                          (into [] (remove #(or (quoting-row? %) (own? %))) sxs))))))

(defn respell-region
  "The stored sentexes a `reifiable_function` mark on `f` moving can re-spell: each one
  holding an application of `f`, and each use of an object constant whose expression
  holds one, at any nesting (`region-from`)."
  [kb f]
  (region-from kb f (fn [sxs]
                      (into [] (filter #(and (not (quoting-row? %)) (applies? f (sx/sentence-of %))))
                            sxs))))

;; ---- a rule's open application (docs/nat.md, The corresponding predicate) -------

(defn names-open-application?
  "Does `form` hold an open application of a `reifiable_function` (the mark read
  unscoped), outside a mention: a quoting position or a `modal_predicate`'s proposition
  (`res/open-applications`)?  False on a KB declaring none, with no walk."
  [kb form]
  (and (nat-read/any-reifiable-functions? kb)
       (let [tax (reasoning/taxonomy kb)]
         (boolean (seq (res/open-applications (:modal (tax/mention-marks tax))
                                              #(tax/has-prop? tax :reifiable %) form))))))

(defn held-application?
  "Does stored rule `sx` hold an open application in an antecedent that
  `res/respell-applications` left as written, so the rule is held in the `:held` forced
  set: one of a `reifiable_function` (the mark read unscoped), or a variable-functor
  application outside a sentence position (`res/holds-variable-application?`)?  The
  consequent is not read: a firing mints its applications (docs/nat.md, Derivation
  path)."
  [kb sx]
  (and (some? (:antecedent sx))
       (let [ls (:antecedent sx)]
         (boolean (or (some #(names-open-application? kb %) ls)
                      (some #(res/holds-variable-application? kb %) ls))))))

(defn held-application-rules
  "The stored rules `held-application?` holds, read off the rule extent of every context
  (the `:held` forced set is one record every reader shares)."
  [kb]
  (->> (reads/as-stored-rules-in-global (:index kb) :rule)
       (keep #(p/get-sentex (:records kb) %))
       (filter #(held-application? kb %))))

(defn formula-declared-predicates
  "The predicates whose `formula` positions (`res/formula-position?`) the stored or
  removed `sentences` can move, sorted: `P` of an `arg`, `quotedArg` or `argN`
  declaration typed `formula` or under it, and for a `genl` edge `(genl A B)` with `B`
  `formula` or under it, `P` of each stored such declaration typed `A` or under it.
  Reads the taxonomy and the declaration index unscoped, as `res/formula-position?` does."
  [kb sentences]
  (let [ix    (:index kb)
        typed (fn [t] (concat (reads/as-stored-with-args ix 'arg {3 t})
                              (reads/as-stored-with-args ix 'quotedArg {3 t})
                              (mapcat #(reads/as-stored-with-args ix % {2 t}) (sort (keys sx/arg-projections)))))
        pred  (fn [s] (let [p (second s)] (when (and (symbol? p) (not (sx/variable? p))) p)))]
    (->> sentences
         (mapcat (fn [s]
                   (when (and (seq? s) (symbol? (first s)))
                     (let [f (first s)]
                       (cond
                         (and (#{'arg 'quotedArg} f) (= 4 (count s)) (res/formula-type? kb (nth s 3)))
                         [(pred s)]
                         (and (contains? sx/arg-projections f) (= 3 (count s)) (res/formula-type? kb (nth s 2)))
                         [(pred s)]
                         (and (= 'genl f) (= 3 (count s)) (symbol? (second s)) (res/formula-type? kb (nth s 2)))
                         (into [] (comp (mapcat typed) (distinct)
                                        (keep #(some-> (p/get-sentex (:records kb) %) :sentence pred)))
                               (sort (tax/specs-global (reasoning/taxonomy kb) (second s)))))))))
         (remove nil?)
         distinct
         sort)))

(defn formula-position-rules
  "The stored rules with an antecedent or a consequent on one of `preds` that name a
  variable-functor application (`res/names-variable-application?`), in content order:
  the rules whose hold a `formula` position of one of `preds` decides
  (`held-application?`).  Reads every context, and the `modal_predicate` mark KB-wide
  (`tax/mention-marks`): the hold is one record every reader shares."
  [kb preds]
  (let [ix    (:index kb)
        modal (:modal (tax/mention-marks (reasoning/taxonomy kb)))]
    (->> (sort preds)
         (mapcat #(concat (reads/as-stored-rules-by-antecedent-global ix %)
                          (reads/as-stored-rules-by-consequent-global ix %)))
         distinct
         (keep #(p/get-sentex (:records kb) %))
         (filter #(res/names-variable-application? modal (sx/sentence-of %)))
         (nm/sort-by-content-key #(vector (sx/sentence-of %) (:context %))))))

(defn corresponded-rules
  "The stored rules a correspondence of `f` moving can re-spell back: each rule with an
  antecedent on a predicate of a stored correspondence declaration of `f`, or on one of
  `preds`, whose premise assertions record a written spelling (`spelled?`).  Reads every
  context: a stored rule's spelling is one row every reader shares."
  [kb f preds spelled?]
  (let [ix (:index kb)
        ps (into (set preds)
                 (comp (keep #(p/get-sentex (:records kb) %))
                       (map :sentence)
                       (filter #(= f (second %)))
                       (map #(nth % 2 nil))
                       (filter symbol?))
                 (when (res/any-corresponding-predicates? kb)
                   (reads/as-stored-with-args ix res/correspondence-predicate {})))]
    (->> (sort ps)
         (mapcat #(reads/as-stored-rules-by-antecedent-global ix %))
         distinct
         (keep #(p/get-sentex (:records kb) %))
         (filter #(spelled? (:id %))))))
