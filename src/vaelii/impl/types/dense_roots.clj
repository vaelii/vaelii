;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.types.dense-roots
  "The columnar index's key-interning root backend, as a held namespace
  (`vaelii.impl.types.prover` states what that means).  `DenseRoots` mutates its own
  fields, which only its inline methods can do, so the type and the code it calls live
  here together; it calls only held namespaces.  Building one, and the snapshot sections
  it is written into, are `vaelii.impl.dense-roots`."
  (:require [clojure.set :as set]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.tokens :as tok]
            [vaelii.impl.types.postings :as postings]
            [vaelii.impl.types.snapshot :as snapshot-types])
  (:import [it.unimi.dsi.fastutil.longs Long2ObjectOpenHashMap]
           [java.nio IntBuffer LongBuffer]))

;; family tags (bits 56-63); pos in bits 32-55; term-id in bits 0-31 (≫ 100M)
(def ^:private ^:const F-CTX     0)
;; The leaves of the count tries ending in the context.  `[:argument-root :handles [pred
;; pos term ctx]]` carries three names beside the term, and the packed long has one term
;; field — so the `(pred, pos, ctx)` scope is interned to an id of its own and rides `pos`,
;; which the flat families do not use (they pass 0).  Every other count trie's leaf
;; `[key ctx]` rides the context's scope `(ctx, 0, ctx)` the same way, its term field
;; holding `key`; no argument position is 0, so the two scope shapes cannot meet.  See
;; `argfam-id`.
(def ^:private ^:const F-PEXT    1)
(def ^:private ^:const F-ARG     2)
(def ^:private ^:const F-TERM    3)
(def ^:private ^:const F-RULE-A  4)
(def ^:private ^:const F-RULE-C  5)
(def ^:private ^:const F-EXC-P   6)
(def ^:private ^:const F-WATCHED 7)
;; The count tries' nodes, from 8 up: their members are contexts, held as their ids in the
;; shared dictionary (`token-members?`).  `[:argument-root :children [pred pos term]]` rides
;; the `(pred, pos)` scope; the other three nodes `[key]` hold `key` in the term field and
;; 0 in `pos`.  An argument node's count is not stored: it is the sum of its leaves' sizes
;; (`counted-count`).  The other three counts are vocabulary-scaled, one per predicate or
;; rule key, and are ordinary counters in the fallback.
(def ^:private ^:const F-ARG-CTX    8)
(def ^:private ^:const F-PEXT-CTX   9)
(def ^:private ^:const F-RULE-A-CTX 10)
(def ^:private ^:const F-RULE-C-CTX 11)
;; The rule extent, `[:rule-extent :handles [kind ctx]]` and its node's children, numbered
;; after the others so no family above changes its number.
(def ^:private ^:const F-RULE-X     12)
(def ^:private ^:const F-RULE-X-CTX 13)
;; The opposed family: a body's leaf `[:opposed :handles [body ctx]]` and its node's
;; children, then the members by context `[:opposed-in ctx]`, a flat family like the
;; context root.
(def ^:private ^:const F-OPP        14)
(def ^:private ^:const F-OPP-CTX    15)
(def ^:private ^:const F-OPP-IN     16)
;; The mint family: the `:mint` trie's leaf `[term ctx]` and its node's children, and the
;; `:mint-in` leaf `[ctx]`, a flat posting under the context alone.  The `:mint-in` node's
;; children and count stay in the fallback, one entry each; a `:mint` node's count is read
;; off its leaves.
(def ^:private ^:const F-MINT       17)
(def ^:private ^:const F-MINT-CTX   18)
(def ^:private ^:const F-MINT-IN    19)
;; The self-tuple trie: a functor's leaf `[:self-tuple :handles [pred ctx]]` and its node's
;; children.
(def ^:private ^:const F-SELF       20)
(def ^:private ^:const F-SELF-CTX   21)
;; The two count tries whose node is several tokens, the taxonomy's supporters (a node is a
;; taxonomy key such as `[:genl a b]`) and the length bindings (`[pred kind value]`): the
;; node is interned to the shared dictionary whole, so its leaf rides the context scope
;; and its children the term field as the one-token nodes do.
(def ^:private ^:const F-TAX        22)
(def ^:private ^:const F-TAX-CTX    23)
(def ^:private ^:const F-ABIND      24)
(def ^:private ^:const F-ABIND-CTX  25)
;; The name sets, their members held as ids in the shared dictionary: the keys a handle
;; installs `[:tax-installs h]`, its term field the handle itself (`raw-term?`); the slot
;; predicate set `[:argument-slot pos term]`, its position in `pos`; one family per `[tag name]`
;; set; and every one-key set `[tag]` under one family, its term the tag.
(def ^:private ^:const F-TAX-INST   26)
(def ^:private ^:const F-SLOT       27)
(def ^:private ^:const F-USLOT      28)
(def ^:private ^:const F-UKEPT      29)
(def ^:private ^:const F-UDENIED    30)
(def ^:private ^:const F-ABKINDS    31)
(def ^:private ^:const F-SHAPELEN   32)
(def ^:private ^:const F-SINGLE     33)
;; The shape, calendar and `natFormula` argument tries, nodes `[f n]`, `[f frame y m]` and
;; `[f pos term]` interned whole as the length bindings' are: each a leaf and its children.
(def ^:private ^:const F-SHAPE      34)
(def ^:private ^:const F-SHAPE-CTX  35)
(def ^:private ^:const F-CAL        38)
(def ^:private ^:const F-CAL-CTX    39)
(def ^:private ^:const F-NATARG     41)
(def ^:private ^:const F-NATARG-CTX 42)
;; The opposed bodies and the calendar months by functor, name sets `[tag f]`.
(def ^:private ^:const F-OFUNC      36)
(def ^:private ^:const F-OBETWEEN   37)
(def ^:private ^:const F-CALMONTHS  40)

(def ^:private watched-key (bit-shift-left (long F-WATCHED) 56))  ; the watched-rule set, a single posting

;; Each field is masked to its own width, and those widths are the invariant that makes
;; `unpack` the *exact* inverse of `route` rather than an inverse over the values the
;; callers happen to pass.  A value one bit past its field would carry into the next one
;; and the key would decode as another family's — `[:argument-root …]` at a scope id of
;; 2²⁴ reads back as `[:term-index …]`, and a routed read answers a posting that is not
;; its own with nothing to signal it.  `argfam-id`'s ceiling is what keeps the scope in
;; range; the masks make the failure unrepresentable rather than merely unreached.  Three
;; `bit-and`s are free on a path every routed read and write takes, where a runtime width
;; assert would not be.
(defn- packed [family pos id]
  (bit-or (bit-shift-left (bit-and (long family) 0xff) 56)
          (bit-shift-left (bit-and (long pos) 0xffffff) 32)
          (bit-and (long id) 0xffffffff)))

(defn- fam-key
  "The packed long for a family key over `term`, or `:absent` when a *read* names a term
  the dictionary has never interned (so the posting cannot exist).  `intern?` allocates."
  [dict family pos term intern?]
  (let [id (if intern? (tok/intern-token! dict term) (tok/token-id dict term))]
    (if (neg? id) :absent (packed family pos id))))            ; auto-boxes to Long

;; ---- the scoped families ------------------------------------------------
;; The argument trie's keys carry two or three names beside the term — a node
;; `[pred pos term]`, a leaf `[pred pos term ctx]` — and `packed` has one term field.  The
;; room is in `pos`: 24 bits reserved for an argument position, which never exceeds an
;; arity, and which every flat family passes 0.  So the *scope* — `[pred pos]` for a
;; node, `[pred pos ctx]` for a leaf — is interned, in one dictionary of its own, and
;; rides those 24 bits.  Every other count trie's leaf `[key ctx]` takes its context's
;; scope `[ctx 0 ctx]`, whatever the key: a mint's term and an opposed body are content,
;; and a scope per key would grow with them.
;;
;; The scope space is bounded by (distinct predicates × their arities × the contexts each
;; is stated in, plus one per context), never by facts, so a 24-bit field is the right
;; size rather than a lucky one: tens of thousands of predicates of small arity, each
;; stated in a handful of contexts, sit well under 16.7M scopes.  `argfam-ceiling` asserts
;; that instead of assuming it.

(def ^:private ^:const argfam-bits 24)
;; a var rather than a `^:const`, so the refusal can be driven in a test by lowering it
;; instead of by minting 16.7M scopes.  It is read once per scope intern, against the
;; dictionary's size.
(def ^:private argfam-ceiling (bit-shift-left 1 argfam-bits))

(defn- argfam-id
  "The dense id for an argument-trie key's scope (`[pred pos]` or `[pred pos ctx]`): `-1`
  when a *read* names a scope nothing has interned (so the posting cannot exist), else the
  id.

  `intern?` allocates, and allocating also interns the scope's `pred` and `ctx` into the
  **term** dictionary.  That is not incidental — a snapshot writes this table as durable
  token ids, so a scope whose names the term dictionary never saw would have no id to
  write.  Every predicate carrying an argument root already has a predicate extent, and
  every context a context root, so the intern is almost always a lookup; doing it here is what
  makes \"almost\" unnecessary to reason about.

  **The ceiling is consulted before the scope is minted, and that ordering is the whole
  of the refusal.**  An id allocated and *then* refused stays in the dictionary, where
  the read path — which does not intern and so never reaches the ceiling — finds it and
  packs a scope past 24 bits into a 24-bit field; `argfam-table` would write it into a
  snapshot too, and `load-argfam!`'s count check restores it happily.  So a caller that
  swallows the throw turns a refusal into a routed read answering another family's
  posting.  `token-count` is the id the dictionary hands out next (`vaelii.impl.tokens`:
  ids count up from 0, first-writer-wins), so asking it first costs one array-size read
  and mints nothing."
  [dict argfam scope intern?]
  (letfn [(names! [] (doseq [n (cons (nth scope 0) (drop 2 scope))] (tok/intern-token! dict n)))]
    (if-not intern?
      (long (tok/token-id argfam scope))
      (if (< (long (tok/token-count argfam)) (long argfam-ceiling))
        (let [id (long (tok/intern-token! argfam scope))]
          (names!)
          id)
        ;; full, which refuses a *new* scope and not a held one: every id already handed
        ;; out is inside the field, so a scope the dictionary holds still answers.
        (let [id (long (tok/token-id argfam scope))]
          (when (neg? id)
            (throw (ex-info (str "the argument-root scope dictionary is full: "
                                 (inc (long (tok/token-count argfam)))
                                 " distinct (predicate, position[, context]) scopes against a"
                                 " ceiling of " argfam-ceiling ". The scope rides 24 bits of the"
                                 " packed root key, so a KB past this cannot int-route its"
                                 " argument roots — take the reference index (`:index"
                                 " :memory`), whose keys are boxed vectors and have no such"
                                 " ceiling.")
                            {:type :argument-family-ceiling :pred (nth scope 0)
                             :position (nth scope 1) :scope scope
                             :pairs (inc (long (tok/token-count argfam)))
                             :ceiling argfam-ceiling
                             :remedy {:index :memory}})))
          (names!)
          id)))))

(defn- arg-key
  "The packed long for an argument-trie key — a leaf `[pred pos term ctx]` under `F-ARG`,
  a node's children `[pred pos term]` under `F-ARG-CTX` — or `:absent`.  The scope
  first: it is the half that can be absent without the term being, and a read of an
  unscoped key has no posting to find."
  [dict argfam family path intern?]
  (let [[pred pos term] path
        af (argfam-id dict argfam (if (= family F-ARG) [pred pos (nth path 3)] [pred pos]) intern?)]
    (if (neg? af) :absent (fam-key dict family af term intern?))))

(defn- ctx-leaf-key
  "The packed long for a count trie's leaf `[key ctx]` under `family`, its scope the
  context's `[ctx 0 ctx]`, or `:absent`."
  [dict argfam family [k ctx] intern?]
  (let [af (argfam-id dict argfam [ctx 0 ctx] intern?)]
    (if (neg? af) :absent (fam-key dict family af k intern?))))

(defn- ctx-trie-key
  "`route`'s answer for a key of a count trie whose node is `[key]`: the leaf under
  `leaf-family`, the node's children under `node-family`, and the count — read off the
  leaves when `counted?`, else a counter in the fallback."
  [dict argfam leaf-family node-family counted? k intern?]
  (case (nth k 1)
    :handles  (ctx-leaf-key dict argfam leaf-family (nth k 2) intern?)
    :children (fam-key dict node-family 0 (nth (nth k 2) 0) intern?)
    :count    (if counted? :count :fallback)
    :fallback))

(defn- node-token
  "The token a several-token node is interned as.  Wrapped, because the shared dictionary
  keys on Clojure equality and a bare node vector `[pred kind value]` would be one token
  with a trie path's literal list `(pred kind value)`, so whichever arrived first would
  decode for both: the wrapper's namespaced head occurs in no sentence."
  [node]
  [::node (vec node)])

(defn- node-trie-key
  "`route`'s answer for a key of a count trie whose node is several tokens, interned whole
  (`node-token`): the leaf `(conj node ctx)` under `leaf-family` and its context's scope,
  the node's children under `node-family`, and the count read off the leaves."
  [dict argfam leaf-family node-family k intern?]
  (case (nth k 1)
    :handles  (let [path (vec (nth k 2))]
                (ctx-leaf-key dict argfam leaf-family [(node-token (pop path)) (peek path)] intern?))
    :children (fam-key dict node-family 0 (node-token (nth k 2)) intern?)
    :count    :count
    :fallback))

(def ^:private routes
  "Family tag (`kv/index-families`) -> how `route` packs its keys:

  - `[:flat f]` — `[tag name]` under family `f`, a set of handles;
  - `[:ctx-trie leaf node counted?]` — a count trie whose node is `[key]` (`ctx-trie-key`);
  - `[:node-trie leaf node]` — a count trie whose node is several tokens
    (`node-trie-key`);
  - `[:leaf-only f]` — a count trie whose leaf `[ctx]` packs under `f`, its node and
    count in the fallback;
  - `[:arg leaf node]` — the argument trie, its count read off the leaves;
  - `[:exception f]` — `[tag pred]` under `f`, and the watched-rule key;
  - `[:names f]` — `[tag name]` under `f`, a set of names;
  - `[:slot f]` — `[tag pos name]` under `f`, `pos` in the position field, a set of names;
  - `[:by-handle f]` — `[tag h]` under `f`, the handle in the term field, a set of names;
  - `[:single f]` — `[tag]` under `f` with the tag as its term, a set of names.

  A name set holds each member as its id in the shared dictionary (`token-members?`).  A
  family absent from the table, and a `:ctx-trie` count that is not `counted?`, goes to the
  fallback: the counters, one per predicate, functor, rule key or kind."
  {:context-root         [:flat F-CTX]
   :predicate-extent     [:ctx-trie F-PEXT F-PEXT-CTX false]
   :rule-antecedent      [:ctx-trie F-RULE-A F-RULE-A-CTX false]
   :rule-consequent      [:ctx-trie F-RULE-C F-RULE-C-CTX false]
   :rule-extent          [:ctx-trie F-RULE-X F-RULE-X-CTX false]
   :opposed              [:ctx-trie F-OPP F-OPP-CTX true]
   :opposed-in           [:flat F-OPP-IN]
   :mint                 [:ctx-trie F-MINT F-MINT-CTX true]
   :mint-in              [:leaf-only F-MINT-IN]
   :self-tuple           [:ctx-trie F-SELF F-SELF-CTX false]
   :tax-support          [:node-trie F-TAX F-TAX-CTX]
   :arity-binding        [:node-trie F-ABIND F-ABIND-CTX]
   :shape-tuple          [:node-trie F-SHAPE F-SHAPE-CTX]
   :calendar             [:node-trie F-CAL F-CAL-CTX]
   :nat-argument         [:node-trie F-NATARG F-NATARG-CTX]
   :argument-root        [:arg F-ARG F-ARG-CTX]
   :term-index           [:flat F-TERM]
   :exception-index      [:exception F-EXC-P]
   :tax-installs         [:by-handle F-TAX-INST]
   :argument-slot        [:slot F-SLOT]
   :unary-slot           [:names F-USLOT]
   :unary-kept           [:names F-UKEPT]
   :unary-denied         [:names F-UDENIED]
   :opposed-functor      [:names F-OFUNC]
   :opposed-between      [:names F-OBETWEEN]
   :arity-binding-kinds  [:names F-ABKINDS]
   :shape-lengths        [:names F-SHAPELEN]
   :calendar-buckets     [:names F-CALMONTHS]
   :term-names           [:single F-SINGLE]
   :unary-multi          [:single F-SINGLE]
   :unary-kept-types     [:single F-SINGLE]
   :unary-denied-types   [:single F-SINGLE]
   :opposed-bodies       [:single F-SINGLE]
   :mint-terms           [:single F-SINGLE]
   :mint-rules           [:single F-SINGLE]
   :rule-antecedent-keys [:single F-SINGLE]
   :arity-bound          [:single F-SINGLE]})

(defn- route
  "Map a structured index key to its packed long (a `Long`), `:absent` (a read of an
  unknown term), `:count` (a node's count that is answered from its leaves), or
  `:fallback` (a family `routes` does not pack, a scalar or a counter)."
  [dict argfam k intern?]
  (if-not (vector? k)
    :fallback
    (if-let [r (routes (nth k 0))]
      (case (nth r 0)
        :flat      (fam-key dict (nth r 1) 0 (nth k 1) intern?)
        :ctx-trie  (ctx-trie-key dict argfam (nth r 1) (nth r 2) (nth r 3) k intern?)
        :node-trie (node-trie-key dict argfam (nth r 1) (nth r 2) k intern?)
        :leaf-only (if (= :handles (nth k 1))
                     (fam-key dict (nth r 1) 0 (nth (nth k 2) 0) intern?)
                     :fallback)
        :arg       (case (nth k 1)
                     :handles  (arg-key dict argfam (nth r 1) (nth k 2) intern?)
                     :children (arg-key dict argfam (nth r 2) (nth k 2) intern?)
                     :count    :count
                     :fallback)
        :exception (if (= :rules (nth k 1))
                     watched-key                                    ; already a boxed Long
                     (fam-key dict (nth r 1) 0 (nth k 1) intern?))
        :names     (fam-key dict (nth r 1) 0 (nth k 1) intern?)
        :slot      (fam-key dict (nth r 1) (nth k 1) (nth k 2) intern?)
        ;; a handle fits the term field; a probe's non-integer stand-in takes the fallback
        :by-handle (let [h (nth k 1)]
                     (if (and (integer? h) (<= 0 (long h) 0xffffffff)) (packed (nth r 1) 0 h) :fallback))
        :single    (fam-key dict (nth r 1) 0 (nth k 0) intern?))
      :fallback)))

(defn- family-flags
  "A `boolean-array` indexed by family byte, true at each family `pick` names for a
  `routes` row."
  [pick]
  (let [a (boolean-array 256)]
    (doseq [r (vals routes), f (pick r)] (aset a (int f) true))
    a))

(def ^:private token-member-families
  "True where the family's postings hold token ids rather than handles: the node family
  of every count trie (its contexts), and every name set."
  (family-flags (fn [[kind f node]]
                  (case kind
                    (:ctx-trie :node-trie :arg) [node]
                    (:names :slot :by-handle :single) [f]
                    []))))

(def ^:private counted-node-families
  "True at the node family of every count trie whose count is read off its leaves."
  (family-flags (fn [[kind _ node counted?]]
                  (when (or (#{:node-trie :arg} kind) (and (= :ctx-trie kind) counted?)) [node]))))

(def ^:private raw-term-families
  "True where the packed key's term field is not a token id, so a snapshot's remap leaves
  it alone: the watched-rule set's key, and a handle's installed keys."
  (doto (boolean-array 256) (aset (int F-WATCHED) true) (aset (int F-TAX-INST) true)))

(defn- token-members?
  "Does packed key `pk` hold token ids (a node's contexts, a set's names) rather than
  handles?"
  [^long pk]
  (aget ^booleans token-member-families (int (bit-shift-right pk 56))))

(defn- unpack
  "The inverse of `route`'s packing: a packed long back to the structured key it stands
  for.  It covers every family `packed` can construct, so the two are each other's
  inverse whatever `route` chooses to send to the fallback — a family routed there
  instead comes back from the fallback's own enumeration, verbatim, and neither path can
  drop an entry."
  [dict argfam ^long pk]
  (let [family (bit-shift-right pk 56)
        ;; a raw term field is no token id, and decoding it as one could read past the
        ;; dictionary
        term   (when-not (aget ^booleans raw-term-families (int family))
                 (tok/id-token dict (int (bit-and pk 0xffffffff))))
        ;; the scope dictionary is consulted on the way back out, which is what makes this
        ;; the inverse of `route` rather than a partial one: the scope id in `pos` decodes
        ;; to the names the key spells around the term.
        scope  #(tok/id-token argfam (int (bit-and (bit-shift-right pk 32) 0xffffff)))
        leaf   (fn [tag] [tag :handles [term (nth (scope) 2)]])
        node   #(nth term 1)                             ; a `node-token`'s node
        nleaf  (fn [tag] [tag :handles (conj (node) (nth (scope) 2))])]
    (case (int family)
      0  [:context-root term]
      1  (leaf :predicate-extent)
      2  (let [[pred pos ctx] (scope)] [:argument-root :handles [pred pos term ctx]])
      3  [:term-index term]
      4  (leaf :rule-antecedent)
      5  (leaf :rule-consequent)
      6  [:exception-index term]
      7  [:exception-index :rules]
      8  (let [[pred pos] (scope)] [:argument-root :children [pred pos term]])
      9  [:predicate-extent :children [term]]
      10 [:rule-antecedent :children [term]]
      11 [:rule-consequent :children [term]]
      12 (leaf :rule-extent)
      13 [:rule-extent :children [term]]
      14 (leaf :opposed)
      15 [:opposed :children [term]]
      16 [:opposed-in term]
      17 (leaf :mint)
      18 [:mint :children [term]]
      19 [:mint-in :handles [term]]
      20 (leaf :self-tuple)
      21 [:self-tuple :children [term]]
      22 (nleaf :tax-support)
      23 [:tax-support :children (node)]
      24 (nleaf :arity-binding)
      25 [:arity-binding :children (node)]
      26 [:tax-installs (bit-and pk 0xffffffff)]
      27 [:argument-slot (bit-and (bit-shift-right pk 32) 0xffffff) term]
      28 [:unary-slot term]
      29 [:unary-kept term]
      30 [:unary-denied term]
      31 [:arity-binding-kinds term]
      32 [:shape-lengths term]
      33 [term]
      34 (nleaf :shape-tuple)
      35 [:shape-tuple :children (node)]
      36 [:opposed-functor term]
      37 [:opposed-between term]
      38 (nleaf :calendar)
      39 [:calendar :children (node)]
      40 [:calendar-buckets term]
      41 (nleaf :nat-argument)
      42 [:nat-argument :children (node)])))

;; ---- the mapped tail ----------------------------------------------------
;; A snapshot's roots are three columns: the packed keys sorted ascending (`mkeys`), the
;; start of each key's handle run (`moff`, one longer than the keys), and one shared run of
;; handles (`mhandles`) — the same CSR shape the trie's leaves take, over vocabulary-keyed
;; postings instead of path-keyed ones.  The keys and offsets are vocabulary-scaled and
;; resident; `mhandles` is the fact-scaled mass and is where the file is.
;;
;; While mapped, `m` is empty and every routed read binary-searches the key column.  A
;; **write thaws wholesale**: there is no mapped-plus-delta mode, because a delta would
;; need its own tombstones to hide a mapped entry and that is a second representation of
;; the same posting.  So the snapshot is a read-phase structure, exactly as the trie's is.

(defprotocol PMappedRoots
  (^:private -find-key [b pk] "Index of packed key `pk` in the mapped column, or -1.")
  (^:private -slice    [b i]  "The i'th mapped posting as `[lo hi)` into the handle run.")
  (^:private mapped-members [b i] "The i'th mapped posting as a Clojure set of Longs.")
  (^:private mapped-ints [b i]
    "The i'th mapped posting copied out of the buffer as an ascending `int[]` — the
    boxing-free read beside `mapped-members`, for the intersection, which discards most of
    what it reads and would otherwise box every handle on the way past.")
  (^:private -thaw-roots! [b] "Materialize every mapped posting into `m` and drop the map.")
  (sections [b]
    "What this backend **holds**, by section — `{:routed :keys :offsets :handles :argfam
    :fallback}` — for a residency measurement (`vaelii.bench.budget`).  The objects
    themselves, never a copy: `snapshot-read` builds fresh heap arrays to write, and
    sizing those would size a temporary rather than what a running KB holds.

    Which section carries the mass is the whole reading, so each says what it scales
    with:

    - `:routed` — the mutable map the routed families use before a snapshot is installed
      and after a write thaws one.  **Fact-scaled**: every handle family is in here.
    - `:keys` / `:offsets` / `:handles` — the installed columns.  The first two are
      vocabulary-scaled, `:handles` is the fact-scaled mass, and all three are buffers
      over the image, so they belong in a caller's *mapped* total rather than its heap
      one.
    - `:argfam` — the scope dictionary the packed argument and leaf keys cite
      (`argfam-id`).  **Vocabulary-scaled**, bounded by distinct predicates × their
      arities × their contexts, plus one per context.
    - `:fallback` — the backend under everything the routed families do not claim: the
      counters keyed by a predicate, functor, rule key or kind (`fallback-entries`).
      **Vocabulary-scaled**, which is what lets a snapshot write it as one nippy blob.

    The heap/mapped split is the caller's to make from the objects — a buffer says
    whether it is direct — so this reports the shape and judges nothing."))

(defn- packed-members
  "The set at a packed key, mapped or heap."
  [this ^Long2ObjectOpenHashMap m pk]
  (if (snapshot-types/snapshot-mapped? this)
    (let [i (-find-key this (long pk))]
      (if (neg? i) #{} (mapped-members this i)))
    (let [p (.get m (long pk))] (if p (postings/pmembers p) #{}))))

(defn- packed-posting
  "The posting at a packed key in the representation it is stored in, or nil — the
  boxing-free twin of `packed-members`, for the narrowing."
  [this ^Long2ObjectOpenHashMap m pk]
  (if (snapshot-types/snapshot-mapped? this)
    (let [i (-find-key this (long pk))]
      (when-not (neg? i) (mapped-ints this i)))
    (.get m (long pk))))

(defn- packed-count
  "The cardinality at a packed key — a slice width while mapped, a posting's own count
  on the heap."
  [this ^Long2ObjectOpenHashMap m pk]
  (if (snapshot-types/snapshot-mapped? this)
    (let [i (-find-key this (long pk))]
      (if (neg? i) 0 (let [[lo hi] (-slice this i)] (- (long hi) (long lo)))))
    (let [p (.get m (long pk))] (if p (postings/pcard p) 0))))

(defn- ctx-ids
  "The context ids a node's children posting at packed key `pk` holds, as an `int[]`, or
  nil when it holds none."
  ^ints [this ^Long2ObjectOpenHashMap m pk]
  (if (snapshot-types/snapshot-mapped? this)
    (let [i (-find-key this (long pk))]
      (when-not (neg? i) (mapped-ints this i)))
    (some-> (.get m (long pk)) postings/pints)))

(defn- ctx-members
  "A node's children as the context tokens its ids name."
  [dict ids]
  (into #{} (map #(tok/id-token dict (int %))) ids))

(defn- arg-node-count
  "The count at argument node `[pred pos term]`: the sum of its leaves' sizes, one leaf
  per context its children posting names."
  [this dict argfam m [pred pos term]]
  (let [pair (long (argfam-id dict argfam [pred pos] false))
        tid  (long (tok/token-id dict term))]
    (if (or (neg? pair) (neg? tid))
      0
      (let [ids (ctx-ids this m (packed F-ARG-CTX pair tid))]
        (if (nil? ids)
          0
          (reduce (fn [n id]
                    (let [sc (long (argfam-id dict argfam [pred pos (tok/id-token dict (int id))] false))]
                      (if (neg? sc) n (+ (long n) (long (packed-count this m (packed F-ARG sc tid)))))))
                  0 ids))))))

(defn- ctx-node-count
  "The count at the node whose term field holds `term`, in a count trie whose leaves ride
  the context scope: the sum of its leaves' sizes, one per context its children name."
  [this dict argfam m leaf-family node-family term]
  (let [tid (long (tok/token-id dict term))]
    (if (neg? tid)
      0
      (let [ids (ctx-ids this m (packed node-family 0 tid))]
        (if (nil? ids)
          0
          (reduce (fn [n id]
                    (let [c  (tok/id-token dict (int id))
                          sc (long (argfam-id dict argfam [c 0 c] false))]
                      (if (neg? sc) n (+ (long n) (long (packed-count this m (packed leaf-family sc tid)))))))
                  0 ids))))))

(defn- counted-count
  "The count at `k` when it is a node's count this backend reads off the node's leaves
  (`route` answers `:count`), else nil.  Computed rather than stored, so a count cannot
  disagree with the leaves, and a snapshot carries no column for it."
  [this dict argfam m k]
  (when (and (vector? k) (= :count (nth k 1 nil)))
    (when-let [[kind leaf node counted?] (routes (nth k 0))]
      (case kind
        :arg       (arg-node-count this dict argfam m (nth k 2))
        :node-trie (ctx-node-count this dict argfam m leaf node (node-token (nth k 2)))
        :ctx-trie  (when counted? (ctx-node-count this dict argfam m leaf node (nth (nth k 2) 0)))
        nil))))

(defn- members
  "The set at `k`, from whichever place the routed families live in."
  [this dict argfam ^Long2ObjectOpenHashMap m fallback k]
  (let [r (route dict argfam k false)]
    (cond
      (instance? Long r) (if (token-members? r)
                           (ctx-members dict (ctx-ids this m r))
                           (packed-members this m r))
      (= :fallback r)    (p/kv-members fallback k)
      :else              #{})))                                  ; :absent, :count

(defn- posting
  "The set at `k` in the representation it is *stored* in — an `IntPostings` (heap), an
  ascending `int[]` (a mapped run), a Clojure set (a fallback family, or a node's
  contexts decoded from their ids), or `nil` when the key holds nothing at all.
  `kv-intersect` reads this rather than `members`, so a routed family never boxes a handle
  the narrowing is about to throw away."
  [this dict argfam ^Long2ObjectOpenHashMap m fallback k]
  (let [r (route dict argfam k false)]
    (cond
      (instance? Long r) (if (token-members? r)
                           (some->> (ctx-ids this m r) (ctx-members dict))
                           (packed-posting this m r))
      (= :fallback r)    (p/kv-members fallback k)
      :else              nil)))                                  ; :absent, :count

;; The writes to a packed key `r`, which `route` has already answered: the methods below
;; and `kv-batch` share them, so a batch routes each op once.  A node's children and a
;; name set hold each member as its id in the shared dictionary, interned on the add and
;; the put and looked up on the remove.  Each write thaws a mapped tail first.

(defn- put-packed! [this dict ^Long2ObjectOpenHashMap m r v]
  (-thaw-roots! this)
  (.put m (long r) (reduce postings/padd! (postings/int-postings)
                           (if (token-members? r) (map #(tok/intern-token! dict %) v) v))))

(defn- delete-packed! [this ^Long2ObjectOpenHashMap m r]
  (-thaw-roots! this)
  (.remove m (long r)))

(defn- add-packed! [this dict ^Long2ObjectOpenHashMap m r mem]
  (-thaw-roots! this)
  (let [pk (long r)
        p  (or (.get m pk) (let [p (postings/int-postings)] (.put m pk p) p))]
    (postings/padd! p (if (token-members? pk) (tok/intern-token! dict mem) mem))))

(defn- remove-packed! [this dict ^Long2ObjectOpenHashMap m r mem]
  (let [mem (if (token-members? r) (tok/token-id dict mem) mem)]
    (-thaw-roots! this)
    (when-let [p (when-not (neg? (long mem)) (.get m (long r)))]
      (postings/prem! p mem)
      (when (zero? (postings/pcard p)) (.remove m (long r))))))

(deftype DenseRoots [dict argfam ^Long2ObjectOpenHashMap m fallback
                     ^:unsynchronized-mutable mkeys      ; LongBuffer | nil
                     ^:unsynchronized-mutable moff       ; IntBuffer  | nil
                     ^:unsynchronized-mutable mhandles   ; IntBuffer  | nil
                     ^:unsynchronized-mutable ^int mn]   ; mapped key count
  PMappedRoots
  (-find-key [_ pk]
    (let [pk (long pk)
          ^LongBuffer ks mkeys]
      (loop [lo 0, hi (dec mn)]
        (if (> lo hi)
          -1
          (let [mid (unsigned-bit-shift-right (+ lo hi) 1)
                v   (.get ks (int mid))]
            (cond (< v pk) (recur (inc mid) hi)
                  (> v pk) (recur lo (dec mid))
                  :else    mid))))))

  (-slice [_ i]
    (let [^IntBuffer o moff, i (int i)]
      [(.get o i) (.get o (inc i))]))

  (mapped-members [this i]
    (let [[lo hi] (-slice this i)
          ^IntBuffer hs mhandles]
      (loop [e (long lo), s (transient #{})]
        (if (< e (long hi)) (recur (inc e) (conj! s (long (.get hs (int e))))) (persistent! s)))))

  (mapped-ints [this i]
    (let [[lo hi] (-slice this i)
          ^IntBuffer hs mhandles
          lo  (long lo)
          out (int-array (- (long hi) lo))]
      (dotimes [e (alength out)] (aset out e (.get hs (int (+ lo e)))))
      out))

  (-thaw-roots! [this]
    (when mkeys
      (let [^LongBuffer ks mkeys
            ^IntBuffer  hs mhandles]
        (dotimes [i mn]
          (let [[lo hi] (-slice this i)
                p       (postings/int-postings)]
            (loop [e (long lo)] (when (< e (long hi)) (postings/padd! p (.get hs (int e))) (recur (inc e))))
            (.put m (.get ks (int i)) p))))
      (set! mkeys nil) (set! moff nil) (set! mhandles nil) (set! mn (int 0)))
    nil)

  (sections [_]
    {:routed m :keys mkeys :offsets moff :handles mhandles
     :argfam argfam :fallback fallback})

  snapshot-types/SnapshotSections
  (snapshot-mapped? [_] (some? mkeys))

  ;; The routed families as heap arrays, keys sorted and their term ids taken through
  ;; `:remap` (an `int[]` from this dictionary's ids to the durable ones).  A raw term
  ;; field (`raw-term-families`) is no token id, so it is passed through unmapped.  The columns are read off the live
  ;; representation, so a mapped backend thaws first.
  (snapshot-read [this {remap :remap}]
    (-thaw-roots! this)
    (let [^ints rm remap
          re  (fn ^long [^long pk]
                (if (aget ^booleans raw-term-families (int (bit-shift-right pk 56)))
                  pk                                      ; no term in it to remap
                  (bit-or (bit-and pk (bit-not 0xffffffff))
                          (long (aget rm (int (bit-and pk 0xffffffff)))))))
          ks  (.toLongArray (.keySet m))
          n   (alength ks)
          out (long-array n)]
      (dotimes [i n] (aset out i ^long (re (aget ks i))))
      (let [order (let [^longs o (aclone ^longs out)]     ; sorted copy, so a read binary-searches
                    (java.util.Arrays/sort o) o)          ; Arrays/sort on the primitives — no boxing
            back  (java.util.HashMap.)]                   ; remapped key -> its posting
        (dotimes [i n] (.put back (aget out i) (.get m (aget ks i))))
        (let [^ints offs (int-array (inc n))
              total      (volatile! 0)]
          (dotimes [i n]
            (vswap! total + (long (postings/pcard (.get back (aget order i)))))
            (aset offs (inc i) (int @total)))
          (let [^ints hs (int-array (aget offs n))]
            (dotimes [i n]
              (let [pk       (aget order i)
                    ^ints ph (postings/pints (.get back pk))
                    base     (aget offs i)]
                (if (token-members? pk)
                  ;; a node's contexts and a set's names are token ids, taken through the
                  ;; same remap as the keys' term halves and re-sorted, since a mapped probe
                  ;; binary-searches the run
                  (let [^ints rs (int-array (alength ph))]
                    (dotimes [e (alength ph)] (aset rs e (aget rm (aget ph e))))
                    (java.util.Arrays/sort rs)
                    (System/arraycopy rs 0 hs base (alength rs)))
                  (System/arraycopy ph 0 hs base (alength ph)))))
            {:keys order :offsets offs :handles hs})))))

  ;; A `LongBuffer` and two `IntBuffer`s over the image, plus the key count they are
  ;; sized by.  The routed map is emptied: the columns answer every routed read until a
  ;; write thaws them back into it.
  (snapshot-install! [_ {ks :keys, offsets :offsets, handles :handles, n :n}]
    (.clear m)
    (set! mkeys ks) (set! moff offsets) (set! mhandles handles) (set! mn (int n))
    nil)

  p/KvBackend
  ;; `kv-get` reads the fallback alone, and that is the contract rather than an omission:
  ;; a routed family holds a posting, never a scalar, so `kv-get` on one is nil — which is
  ;; what `dense_routing_test` reads to tell a routed key from a fallback key.  Counters
  ;; are scalars and route nowhere, so the two increments follow it down.  A node count read
  ;; off the leaves is the exception (`counted-count`): an increment or decrement stores
  ;; nothing and replies with the count the leaf write before it in the batch left
  ;; (`kv/flat-family-adds` orders them so).
  (kv-get  [this k]
    (if-some [n (counted-count this dict argfam m k)] n (p/kv-get fallback k)))
  (kv-increment [this k]
    (if-some [n (counted-count this dict argfam m k)] n (p/kv-increment fallback k)))
  (kv-decrement [this k]
    (if-some [n (counted-count this dict argfam m k)] n (p/kv-decrement fallback k)))

  ;; A whole-posting put and a delete are the two ops the index's own writes never issue
  ;; on a root family — `index-sentex` adds and removes members — so only `kv_backend_test`
  ;; exercises them, and only there does a routed key that took the fallback's answer show
  ;; up: it would write a boxed entry the routed reads cannot see, and leave the packed
  ;; posting standing under a key a dump reports as deleted.
  (kv-put [this k v]
    (let [r (route dict argfam k true)]                          ; intern ⇒ never :absent
      (cond
        (instance? Long r) (put-packed! this dict m r v)
        (= :count r)       nil                                   ; read off the leaves
        :else              (p/kv-put fallback k v)))
    nil)
  (kv-delete [this k]
    (let [r (route dict argfam k false)]
      (cond
        (instance? Long r) (delete-packed! this m r)
        (= :fallback r)    (p/kv-delete fallback k)))           ; :absent, :count ⇒ nothing to drop
    nil)
  (kv-add-to-set [this k mem]
    (let [r (route dict argfam k true)]                                 ; intern ⇒ never :absent
      (if (instance? Long r)
        (add-packed! this dict m r mem)
        (p/kv-add-to-set fallback k mem)))
    nil)
  (kv-remove-from-set [this k mem]
    (let [r (route dict argfam k false)]
      (cond
        (instance? Long r) (remove-packed! this dict m r mem)
        (= :fallback r)    (p/kv-remove-from-set fallback k mem)))          ; :absent ⇒ nothing to remove
    nil)
  (kv-members [this k] (members this dict argfam m fallback k))
  ;; the probe routes exactly as `kv-count` does — a term the dictionary never interned
  ;; has no posting, so `:absent` is a false rather than a lookup
  (kv-member? [this k mem]
    (let [r   (route dict argfam k false)
          mem (if (and (instance? Long r) (token-members? r)) (tok/token-id dict mem) mem)]
      (cond
        (and (instance? Long r) (neg? (long mem))) false            ; a context never interned
        (instance? Long r) (if (snapshot-types/snapshot-mapped? this)
                             (let [i (-find-key this (long r))]
                               (if (neg? i)
                                 false
                                 (let [[lo hi] (-slice this i)
                                       ^IntBuffer hs mhandles
                                       h  (int mem)]
                                   ;; the run is sorted (a posting's own order), so the
                                   ;; probe stays the binary search the heap posting is
                                   (loop [lo (long lo), hi (dec (long hi))]
                                     (if (> lo hi)
                                       false
                                       (let [mid (unsigned-bit-shift-right (+ lo hi) 1)
                                             v   (.get hs (int mid))]
                                         (cond (< v h) (recur (inc mid) hi)
                                               (> v h) (recur lo (dec mid))
                                               :else   true)))))))
                             (let [p (.get m (long r))]
                               (boolean (and p (postings/pcontains? p mem)))))
        (= :fallback r)    (p/kv-member? fallback k mem)
        :else              false)))
  (kv-count [this k]
    (let [r (route dict argfam k false)]
      (cond
        (instance? Long r) (packed-count this m r)
        (= :fallback r)    (p/kv-count fallback k)
        :else              0)))
  ;; The narrowing runs in the postings' own representation (`postings/intersect-postings`),
  ;; which is what `sentexes-with-args` and `sentexes-with-terms` bottom out in.  A name
  ;; set or a fallback key holds something other than handles, so a list containing one
  ;; falls back to folding sets — it cannot arise from an index read, only from a caller
  ;; intersecting keys that hold no handles.
  (kv-intersect [this ks]
    (if (empty? ks)
      #{}
      (let [ps (mapv #(posting this dict argfam m fallback %) ks)]
        (cond
          (some nil? ps) #{}                                     ; a key holding nothing
          (some set? ps) (reduce set/intersection
                                 (sort-by count
                                          (map #(if (set? %) % (postings/postings-set %)) ps)))
          :else          (postings/intersect-postings ps)))))
  ;; Each op is routed once.  A packed op applies in place, in order; the fallback's ops
  ;; are gathered and handed to it as one batch at the end, which the in-memory fallback
  ;; folds through one transient (`vaelii.impl.memory`), where an op at a time would copy
  ;; a path through its map per op.  The two halves touch disjoint keys and no reply of
  ;; one reads the other — a counted node's count reads the leaves, a fallback counter
  ;; the fallback — so the replies are the ops' in order.
  (kv-batch [this ops]
    (let [ops (vec ops)
          n   (count ops)
          out (object-array n)
          fb  (java.util.ArrayList.)
          at  (java.util.ArrayList.)
          defer! (fn [i o] (.add fb o) (.add at i))]
      (dotimes [i n]
        (let [[op k a :as o] (nth ops i)]
          (case op
            (:increment :decrement)
            (if-some [c (counted-count this dict argfam m k)] (aset out i c) (defer! i o))
            (:put :delete :add-to-set :remove-from-set)
            (let [r (route dict argfam k (or (identical? op :put) (identical? op :add-to-set)))]
              (cond
                (instance? Long r) (case op
                                     :put             (put-packed! this dict m r a)
                                     :delete          (delete-packed! this m r)
                                     :add-to-set      (add-packed! this dict m r a)
                                     :remove-from-set (remove-packed! this dict m r a))
                (= :fallback r)    (defer! i o)))                ; :absent, :count ⇒ nothing
            ;; the one refusal every adapter spells — see `vaelii.impl.dense-kv`
            (p/unknown-op! op))))
      (when (pos? (.size fb))
        (let [rs (p/kv-batch fallback (vec fb))]
          (dotimes [j (.size at)] (aset out (int (.get at j)) (nth rs j)))))
      (vec out)))
  ;; The portable projection has to undo *both* of this backend's compressions: the
  ;; interned key (through `unpack`, against the shared dictionary) and the `IntPostings`
  ;; value.  The two sides are enumerated together because a key routed to the fallback
  ;; is as much an index entry as a packed one.
  ;; A node's children and a set's names decode from ids to tokens, and a node count read
  ;; off the leaves, which is not stored, is emitted beside its children so the
  ;; projection is the flat map's.
  (kv-entries [this]
    (concat (mapcat (fn [pk]
                      (let [pk  (long pk)
                            k   (unpack dict argfam pk)]
                        (cond
                          (aget ^booleans counted-node-families (int (bit-shift-right pk 56)))
                          (let [ck (assoc k 1 :count)]
                            [[k (ctx-members dict (ctx-ids this m pk))]
                             [ck (counted-count this dict argfam m ck)]])
                          (token-members? pk) [[k (ctx-members dict (ctx-ids this m pk))]]
                          :else            [[k (packed-members this m pk)]])))
                    (if (snapshot-types/snapshot-mapped? this)
                      (map (fn [i] (.get ^LongBuffer mkeys (int i))) (range mn))
                      (iterator-seq (.iterator (.keySet m)))))
            (p/kv-entries fallback)))
  ;; a node's count entry is dropped: the count is read off the leaves the load installs.
  ;; The fallback's entries load as one `kv-load`.
  (kv-load [this entries]
    (-thaw-roots! this)
    (p/kv-load fallback
               (into [] (keep (fn [[k v :as e]]
                                (let [r (route dict argfam k true)]      ; intern ⇒ never :absent
                                  (cond
                                    (instance? Long r) (do (put-packed! this dict m r v) nil)
                                    (= :count r)       nil
                                    :else              e))))
                     entries))
    nil)

  (kv-clear! [_]
    (.clear m)
    (set! mkeys nil) (set! moff nil) (set! mhandles nil) (set! mn (int 0))
    ;; the scope ids are only meaningful against the keys citing them, and every one of
    ;; those has just gone — a surviving dictionary would hand the next load ids nothing
    ;; decodes.
    (tok/clear-tokens! argfam)
    (p/kv-clear! fallback)
    nil))
