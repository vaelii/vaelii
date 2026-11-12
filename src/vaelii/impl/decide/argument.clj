;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide.argument
  "The argument family: a stored fact whose argument fails a declared argument type, and a
  stored rule whose variable no term can fill, read as `assert` reads them
  (`checks/argument-conviction`), are held in the `:out` forced set.  This namespace
  keeps the held sentexes and the queue of what can move a verdict; the settle drains the
  queue (`checks/refresh-argument-holds!`).  See docs/argtypes.md, \"An argument that
  fails its declared type is held inert\"."
  (:require [vaelii.impl.caches :as caches]
            [vaelii.impl.config :as config]
            [vaelii.impl.predicates :as predicates]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- the reading an argument declaration is under ---------------------------

(def ^:dynamic *assertive-arg-types?*
  "Do the argument constraints *entail* as well as constrain?

  **On by default.**  The entailment is additive — it mints the type a declaration
  already constrains, as a justified, retractable sentex — and off leaves the constraint
  reading alone (docs/argtypes.md).

  `binding` it is the ordinary way in.  `VAELII_ASSERTIVE_ARG_TYPES=0` sets the root
  value off instead, which is what lets the whole suite be run under the constraint-only
  reading — the parity run that shows the entailment is additive rather than a different
  engine."
  (config/assertive-arg-types?))

;; ---- the held facts and the queue ---------------------------------------------
;;
;; `::held` is `{h functor}`, the stored sentexes the family holds in `:out`, with a nil
;; functor for a rule.  A write queues what can move a verdict: an argument declaration
;; stored or removed queues `[predicate context]` under `::decls`, a membership `(T x)`
;; stored or removed queues `x` under `::terms`, and under `::kinds` as well when `T` is
;; `type_relation_predicate`, which constrains a rule's variables at every position of
;; `x`, and a definition `(defnSufficient T C)`, `(defnNecessary T C)` or
;; `(defnIff T C)` stored, removed or relabelled queues `T` under `::defns`, since it can
;; decide a value under a type at or below or above `T` (`provers/value-definition`).  `::read-under` holds the taxonomy generations the last drain read
;; (`special/conviction-generations` with the `genlCx` generation), and `::owed` marks a
;; recover, after which the first drain reads every declaration whole.  `::adopt` marks an
;; installed image that carries no `::read-under`: the first drain takes the generations as read and
;; reads only what the queue names (`installed!`).

(def declaration-functors
  "The argument declarations, each naming the predicate it constrains at argument 1
  (`predicates/:argument-constraint`)."
  (predicates/family :argument-constraint))

(defn- declaration-of
  "`[P context]` for a stored fact `sx` declaring an argument constraint of `P`, else nil."
  [sx]
  (let [s (:sentence sx)]
    (when (and (nil? (:antecedent sx)) (seq? s) (contains? declaration-functors (first s)))
      (let [p (second s)]
        (when (and (symbol? p) (not (sx/variable? p)))
          [p (:context sx)])))))

(defn- member-of
  "The term `x` of a stored fact `sx` whose sentence is the membership `(T x)` of a symbol,
  else nil."
  [sx]
  (let [s (:sentence sx)]
    (when (and (nil? (:antecedent sx)) (seq? s) (= 2 (count s)))
      (let [[t x] s]
        (when (and (symbol? t) (not= 'not t) (not (sx/variable? t))
                   (symbol? x) (not (sx/variable? x)))
          x)))))

(defn- kind-of
  "The predicate `P` of a stored fact `sx` whose sentence is `(type_relation_predicate P)`,
  else nil."
  [sx]
  (let [s (:sentence sx)]
    (when (and (seq? s) (= 'type_relation_predicate (first s)))
      (member-of sx))))

(defn- defined-of
  "The type `T` a stored definition `sx`, `(defnSufficient T C)`, `(defnNecessary T C)` or
  `(defnIff T C)`, states a condition of, else nil."
  [sx]
  (let [s (:sentence sx)]
    (when (and (nil? (:antecedent sx)) (sx/defn-sentence? s))
      (let [t (second s)]
        (when (and (symbol? t) (not (sx/variable? t))) t)))))

(defn held?
  "Is the stored sentex at `h` held for an argument conviction?"
  [kb h]
  (contains? (::held @(reasoning/nogood-candidates kb)) h))

(defn held
  "`{h functor}` of every sentex the family holds."
  [kb]
  (::held @(reasoning/nogood-candidates kb) {}))

(defn set-held!
  "Record the sentex at `h`, of functor `f` (nil for a rule), as held (`on?`) or not."
  [kb h f on?]
  (swap! (reasoning/nogood-candidates kb)
         #(if on? (assoc-in % [::held h] f) (update % ::held dissoc h))))

(defn note!
  "Queue what the fact `sx` stored or removed (`stored?`) can move: a declaration's
  predicate and context, a membership's term, a definition's type.  A term is queued under
  the constraint-only reading alone, the one the drain reads it under
  (`checks/refresh-argument-holds!`).  A removed fact leaves `::held`."
  [kb sx stored?]
  (let [d  (declaration-of sx)
        x  (when-not d (member-of sx))
        xq (when-not *assertive-arg-types?* x)
        k  (when x (kind-of sx))
        t  (when-not (or d x) (defined-of sx))]
    (when (or d xq k t (and (not stored?) (contains? (::held @(reasoning/nogood-candidates kb)) (:id sx))))
      (swap! (reasoning/nogood-candidates kb)
             #(cond-> %
                d                (update ::decls (fnil conj #{}) d)
                xq               (update ::terms (fnil conj #{}) xq)
                k                (update ::kinds (fnil conj #{}) k)
                t                (update ::defns (fnil conj #{}) t)
                (not stored?)    (update ::held dissoc (:id sx)))))))

(defn note-relabelled!
  "Queue the declarations, memberships and definitions among the stored facts `sxs` whose
  label moved."
  [kb sxs]
  (let [ds (into #{} (keep declaration-of) sxs)
        xs (when-not *assertive-arg-types?* (into #{} (keep member-of) sxs))
        ks (into #{} (keep kind-of) sxs)
        ts (into #{} (keep defined-of) sxs)]
    (when (or (seq ds) (seq xs) (seq ks) (seq ts))
      (swap! (reasoning/nogood-candidates kb)
             #(cond-> %
                (seq ds) (update ::decls (fnil into #{}) ds)
                (seq xs) (update ::terms (fnil into #{}) xs)
                (seq ks) (update ::kinds (fnil into #{}) ks)
                (seq ts) (update ::defns (fnil into #{}) ts))))))

(defonce ^{:private true
           :doc "`[props answer]` of the last `declares-any?` read: the answer is a function of
  the taxonomy's `:props` value alone, which a write that marks no predicate leaves identical."}
  declares-memo
  (java.util.concurrent.atomic.AtomicReference. nil))

(defn declares-any?
  "Does any stored declaration name a predicate (`tax/arg-declaration-props`)?  Asked on
  every write and every argument check, so it is answered off the last read while the
  taxonomy's `:props` value stands."
  [tax]
  (let [props (:props @tax)
        [p b] (.get ^java.util.concurrent.atomic.AtomicReference declares-memo)]
    (if (and (some? p) (identical? p props))
      b
      (let [b (boolean (some #(seq (get props %)) (vals tax/arg-declaration-props)))]
        (.set ^java.util.concurrent.atomic.AtomicReference declares-memo [props b])
        b))))

(defn installed!
  "Mark the family of a just-installed reasoning image adopted (`::adopt`) when the image
  carries no `::read-under`, as an image written by a build without this family does.  The
  first drain then records the generations it reads under and decides only the queued
  declarations and terms, so the open runs no whole read and every stored fact keeps the
  label the image gives it until a write reaches it, as `:recover? :trust` keeps every
  other label (docs/storage.md, \"Trusting an image\").  `recover` reads it whole.  An
  image holding no held fact and no declaration is not adopted: its first declaration
  reads whole, as in the writer."
  [kb]
  (let [declares? (declares-any? (reasoning/taxonomy kb))]
    (swap! (reasoning/nogood-candidates kb)
           #(if (or (contains? % ::read-under) (::owed %) (and (empty? (::held %)) (not declares?)))
              %
              (assoc % ::adopt true)))))

(defn- queued?
  "Does the state `c` hold a queued declaration, kind or definition, a queued term under
  the constraint-only reading (the one that reads it), a recover's whole read or an
  adopted image's first drain?"
  [c]
  (boolean (or (::owed c) (::adopt c) (seq (::decls c))
               (and (not *assertive-arg-types?*) (seq (::terms c)))
               (seq (::kinds c)) (seq (::defns c)))))

(defn moved?
  "Does the drain owe a read: `queued?`, or taxonomy generations `read-under` other than
  the last drain's while some fact is held or some declaration is stored?"
  [tax c read-under]
  (boolean (or (queued? c)
               (and (or (seq (::held c)) (declares-any? tax))
                    (not= read-under (::read-under c))))))

(defn idle?
  "Can `moved?` answer true under no `read-under` at all: is nothing `queued?`, no fact
  held, and no declaration stored?  A caller asks it before building the generations
  `moved?` compares (`special/conviction-generations`)."
  [tax c]
  (not (or (queued? c) (seq (::held c)) (declares-any? tax))))

(defn- queue-of
  "The queue the state `c` holds, as `take!` answers it under `read-under`."
  [c read-under]
  {:decls (::decls c #{}) :terms (::terms c #{}) :kinds (::kinds c #{}) :defns (::defns c #{})
   :from  (if (::adopt c) read-under (::read-under c)) :owed? (boolean (::owed c))})

(defn queued
  "`take!`'s answer with the queue left in place, for a drain that can stop before it
  takes the queue."
  [kb read-under]
  (queue-of @(reasoning/nogood-candidates kb) read-under))

(defn take!
  "The queue since the last call, emptied, with the taxonomy generations `read-under` recorded:
  `{:decls #{[P context]} :terms #{x} :kinds #{P} :defns #{T} :from old-read-under :owed? bool}`.  An
  adopted image's first call answers `read-under` itself as `:from` (`installed!`)."
  [kb read-under]
  (let [[old _] (swap-vals! (reasoning/nogood-candidates kb)
                            #(-> % (dissoc ::decls ::terms ::kinds ::defns ::owed ::adopt) (assoc ::read-under read-under)))]
    (queue-of old read-under)))

(def family
  "The argument family's entry in `decide/registry`: the write hook that queues what a
  write can move (`note!`).  A recover empties `::held` and owes a whole read."
  {:note!     (fn [kb _w sx stored?] (note! kb sx stored?))
   :recovered (fn [kb _]
                (swap! (reasoning/nogood-candidates kb) #(-> % (dissoc ::held) (assoc ::owed true))))})

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(caches/register-derived
 {:id :N10 :label "Argument holds" :kind :cache :keyed-by :handle
  :holds-content? false
  :reads [:index :records :M1 :T1 :J5]
  :retired-by {:stored :K :removed :K :relabelled :K :edge :G :edge-belief :G
               :settle-pass :Q :recover :R :image-install :R}
  :computed :write :imaged? :state
  :at [[:nogood-candidates ::held] [:nogood-candidates ::decls] [:nogood-candidates ::terms]
       [:nogood-candidates ::kinds] [:nogood-candidates ::defns] [:nogood-candidates ::read-under] [:nogood-candidates ::owed] [:nogood-candidates ::adopt]]
  :bound "one entry per stored fact or rule held for an argument conviction, one per declaration, per membership term, per `type_relation_predicate` member and per defined type stored, removed or relabelled since the last settle pass"
  :note "the stored facts and rules held in `:out` for an argument conviction (`checks/argument-conviction`), recorded as a fact or rule is stored and at each drain; the declarations, membership terms, `type_relation_predicate` members and defined types a write or relabel queued, and the taxonomy generations the last drain read, which the settle drains (`checks/refresh-argument-holds!`); a recover owes a whole read (`::owed`), and an installed image carrying no generations is adopted as read (`::adopt`)"})

(caches/register-derived
 {:id :X4 :label "Declaration presence memo" :kind :cache :keyed-by :global :reads [:T2]
  :holds-content? false
  :retired-by (caches/on-every :I) :computed :read :imaged? false :var #'declares-memo
  :value (fn [_] (.get ^java.util.concurrent.atomic.AtomicReference declares-memo))
  :note "one slot for the process: the taxonomy's `:props` value of the last `declares-any?` read and its answer, compared by identity; another KB's read evicts it"})
