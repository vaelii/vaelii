;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.padding-blindness-test
  "No write reads a standing set whole.  World W is a seeded write stream over four
  contexts and five types; world W′ is the same stream run after a padding P: n copies of
  every standing kind (a placed `contradicts`, a placed `defeat`, a waiting mint and lift,
  a firing held by the argument hold, an inherited-clash entry over a separated membership,
  a rule, a deep type branch), each copy in a context of its own under CxPad, over types and individuals
  the stream never names.  Each write of the stream runs with `prof/*handle-sink*` bound:
  the handles it fetches or a posting read answers, during the write and its settle,
  share nothing with P, and belief over the stream's own content after it equals W's.
  A site that reads P today is a row of `known-padding-reads`, matched by a frame of the
  stack at the read; a read no row names fails the test (docs/nmtms.md, \"Linear in the
  standing set\")."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.ref.gen :as gen]
            [vaelii.test-util :as tu])
  (:import [java.util Random]))

;; ---- the padding ----------------------------------------------------------------
;;
;; Copy k of a kind writes into `CxPad<k><kind>` (and one context below it for the
;; held firing) and names only symbols spelled with its own `k`, so no two copies
;; and no stream write share a term.

(def ^:private mono {:strength :monotonic})

(def pad-kinds
  "The standing kinds one padding copy holds."
  [:contradicts :defeat :mint :held :sep :rule :deep])

(defn- sym [fmt k] (symbol (format fmt k)))

(defn- pad-copy!
  "Write copy `k` of padding `kind` into `kb`."
  [kb kind k]
  (let [cx  (sym (str "CxPad%d" (str/capitalize (name kind))) k)
        t   #(sym (str "pad%d_" %) k)
        i   #(sym (str "Pad%d" %) k)
        r   #(sym (str "pad%d" %) k)
        in! (fn [s & [c o]] (v/assert kb s (or c cx) o))]
    (v/assert kb (list 'genlCx cx 'CxPad) 'CxUniverse mono)
    (case kind
      ;; a placed `contradicts` between two defaults of disjoint types
      :contradicts (do (in! (list 'genl (t "ca") 'thing) cx mono)
                       (in! (list 'genl (t "cb") 'thing) cx mono)
                       (in! (list 'disjoint (t "ca") (t "cb")) cx mono)
                       (in! (list (t "ca") (i "C")))
                       (in! (list (t "cb") (i "C"))))
      ;; a placed `defeat` of a default by a known-true member of a disjoint type
      :defeat      (do (in! (list 'genl (t "da") 'thing) cx mono)
                       (in! (list 'genl (t "db") 'thing) cx mono)
                       (in! (list 'disjoint (t "da") (t "db")) cx mono)
                       (in! (list (t "da") (i "D")))
                       (in! (list (t "db") (i "D")) cx mono))
      ;; a declaration whose type is bound to two arguments, which mints nothing
      :mint        (do (in! (list 'binary_predicate (sym "pad%dfloating" k)) 'CxUniverse mono)
                       (in! (list (r "MintRel") (i "Ma") (i "Mb")))
                       (in! (list 'arg (r "MintRel") 1 (sym "pad%dfloating" k))))
      ;; a firing whose number argument the argument constraint convicts, stored and
      ;; held by the argument hold
      :held        (let [below (sym "CxPad%dHeldBelow" k)]
                     (v/assert kb (list 'genlCx below cx) 'CxUniverse mono)
                     (in! (list 'genl (t "animal") 'thing) cx mono)
                     (in! (list 'arg (r "OwnsPet") 2 (t "animal")))
                     (in! (gen/forward (list 'implies (list (r "PetOf") '?x '?y)
                                             (list (r "OwnsPet") '?y '?x)))
                          below)
                     (in! (list (r "PetOf") 5 (i "Ann")) below))
      ;; a membership of a type separated from a preserved one: an inherited-clash entry
      ;; with `:sep?`, and its placed `contradicts`
      :sep         (do (in! (list 'transitiveInArgInverse (t "down") 1 'genl) cx mono)
                       (in! (list 'disjoint (t "down") (t "plain")) cx mono)
                       (in! (list 'genl (t "lower") (t "upper")) cx mono)
                       (in! (list (t "down") (t "upper")) cx mono)
                       (in! (list (t "plain") (t "lower")) cx mono))
      ;; a forward rule and a fact it fired on
      :rule        (do (in! (gen/forward (list 'implies (list (t "ra") '?x) (list (t "rb") '?x))))
                       (in! (list (t "ra") (i "R"))))
      ;; a type branch six deep under `thing`
      :deep        (reduce (fn [up d]
                             (let [s (sym (str "pad%d_deep" d) k)]
                               (in! (list 'genl s up) cx mono)
                               s))
                           'thing (range 6)))))

(defn- pad!
  "Write `n` copies of each of `kinds` into `kb` under CxPad, and answer the handles the
  KB stores after the padding settles that it did not store before."
  [kb kinds n]
  (let [before (set (p/sentex-ids (:records kb)))]
    (v/assert kb '(genlCx CxPad CxUniverse) 'CxUniverse mono)
    (doseq [k (range n) kind kinds] (pad-copy! kb kind k))
    (into #{} (remove before) (p/sentex-ids (:records kb)))))

;; ---- the stream -----------------------------------------------------------------

(def ^:private stream-contexts '[CxStA CxStB CxStC CxStD])
(def ^:private stream-types '[st_a st_b st_c st_d st_e])
(def ^:private stream-individuals '[StAnn StBob StCy])

(defn- setup!
  "The stream's base, written before the padding: each context under CxUniverse and the
  first three types under `thing`.  `st_d` and `st_e` reach `thing` only through an edge
  the stream writes."
  [kb]
  (doseq [c stream-contexts] (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse mono))
  (doseq [t (take 3 stream-types)] (v/assert kb (list 'genl t 'thing) 'CxUniverse mono)))

(defn- ordered-pair
  "Two distinct members of `coll`, the later one first, so edges between them stay
  acyclic."
  [^Random rng coll]
  (let [a (.nextInt rng (count coll))
        b (.nextInt rng (dec (count coll)))
        b (if (>= b a) (inc b) b)]
    [(nth coll (max a b)) (nth coll (min a b))]))

(defn gen-stream
  "`n` writes for `seed`, each one of `[:assert S C opts]`, `[:retract j]` (the write at
  op `j`), `[:except j C]`, or `[:preview S C]`."
  [seed n]
  (let [rng (Random. (long seed))
        st  #(if (zero? (.nextInt rng 3)) mono {})]
    (loop [ops [] i 0]
      (if (= i n)
        ops
        (let [asserts (keep-indexed #(when (= :assert (first %2)) %1) ops)
              facts   (filter #(not (#{'genl 'genlCx 'disjoint 'set/forwardRule} (first (second (nth ops %)))))
                              asserts)
              op (case (.nextInt rng 13)
                   (0 1 2) [:assert (list (tu/pick rng stream-types) (tu/pick rng stream-individuals))
                            (tu/pick rng stream-contexts) (st)]
                   3       [:assert (list 'not (list (tu/pick rng stream-types) (tu/pick rng stream-individuals)))
                            (tu/pick rng stream-contexts) (st)]
                   4       (let [[a b] (ordered-pair rng stream-types)]
                             [:assert (gen/forward (list 'implies (list b '?x) (list a '?x)))
                              (tu/pick rng stream-contexts) {}])
                   5       (let [[a b] (ordered-pair rng stream-types)]
                             [:assert (list 'genl a b) (tu/pick rng stream-contexts) (st)])
                   6       (let [[a b] (ordered-pair rng stream-contexts)]
                             [:assert (list 'genlCx a b) 'CxUniverse mono])
                   7       (let [[a b] (ordered-pair rng stream-types)]
                             [:assert (list 'disjoint a b) (tu/pick rng stream-contexts) (st)])
                   (8 9)   (if (seq asserts) [:retract (tu/pick rng (vec asserts))] [:noop])
                   10      (if (seq facts) [:except (tu/pick rng (vec facts)) (tu/pick rng stream-contexts)] [:noop])
                   11      [:preview (list (tu/pick rng stream-types) (tu/pick rng stream-individuals))
                            (tu/pick rng stream-contexts)]
                   12      (let [[a b] (ordered-pair rng stream-individuals)]
                             [:assert (list 'sameAs a b) (tu/pick rng stream-contexts) (st)]))]
          (recur (conj ops op) (inc i)))))))

;; ---- running a world --------------------------------------------------------------

(defonce ^:private space-counter (atom 0))

(defn- open-kb []
  (let [space [::padding (swap! space-counter inc)]]
    {:kb (v/open-kb {:backend :memory :space space :recover? false}) :space space}))

(defn- close! [{:keys [kb space]}]
  (try (v/close! kb)
       (finally (mem/drop-record-space! space) (mem/drop-index-space! space))))

(defn- apply-op!
  "Run one op of a stream, `hs` the handles of the ops before it."
  [kb hs op]
  (try
    (case (first op)
      :assert  (let [[_ s c o] op] (v/assert kb s c o))
      :retract (when-let [h (get hs (second op))]
                 (when (v/sentex kb h) (v/retract! kb h))
                 nil)
      :except  (when-let [h (get hs (second op))]
                 (when (v/sentex kb h)
                   (v/assert kb (list 'except (v/sentex-handle h)) (nth op 2))))
      :preview (let [[_ s c] op] (v/preview kb {:add [[s c]]}) nil)
      :noop    nil)
    (catch clojure.lang.ExceptionInfo _ nil)))

(def ^:private stream-ctx-set (set stream-contexts))

(defn- belief
  "The believed content the stream's contexts hold, without handles."
  [kb]
  (let [recs (:records kb)]
    (into #{}
          (comp (keep #(p/get-sentex recs %))
                (filter #(contains? stream-ctx-set (:context %)))
                (map #(tu/handle-free kb [(:sentence %) (:context %)])))
          (jtms/in-datums (reasoning/tms kb)))))

(defn- site-of
  "The row of `rows` whose frame names the innermost frame of the current stack any row
  names, or the stack's vaelii frames when no row names one."
  [rows]
  (let [frames (mapv #(.getClassName ^StackTraceElement %) (.getStackTrace (Thread/currentThread)))]
    (or (some (fn [f] (some (fn [[k {:keys [frame]}]] (when (str/starts-with? f frame) k)) rows))
              frames)
        (into [] (comp (filter #(str/starts-with? % "vaelii.impl")) (dedupe) (take 14)) frames))))

(defn run-world
  "Run `ops` on a KB holding `kinds` padding at `n` copies (none when `n` is 0).  Answers
  `{:reads [{:op i :sites #{site}}] :beliefs [belief-after-op-i]}`."
  [kinds n ops rows]
  (let [w (open-kb) kb (:kb w)]
    (try
      (setup! kb)
      (let [padded (if (pos? n) (pad! kb kinds n) #{})]
        (loop [i 0 hs {} reads [] beliefs []]
          (if (= i (count ops))
            {:reads reads :beliefs beliefs}
            (let [sites (volatile! #{})
                  h     (binding [prof/*handle-sink* (fn [h] (when (contains? padded h)
                                                               (vswap! sites conj (site-of rows))))]
                          (apply-op! kb hs (nth ops i)))]
              (recur (inc i)
                     (cond-> hs (int? h) (assoc i h))
                     (cond-> reads (seq @sites) (conj {:op i :sites @sites}))
                     (conj beliefs (belief kb)))))))
      (finally (close! w)))))

;; ---- the sites that read P at HEAD ------------------------------------------------

(def ^:private genl-edge [[:assert '(genl st_d st_a) 'CxStA {}]])

(def ^:private disjoint-edge [[:assert '(disjoint st_b st_a) 'CxStA {}]])

(def ^:private except-fact [[:assert '(st_a StAnn) 'CxStA {}] [:except 0 'CxStB]])

(def ^:private rule-fire
  [[:assert '(st_b StAnn) 'CxStA {}]
   [:assert (gen/forward '(implies (st_b ?x) (st_a ?x))) 'CxStA {}]])

(def ^:private rule-below-genlcx
  [[:assert (gen/forward '(implies (st_a ?x) (st_b ?x))) 'CxStA {}]
   [:assert '(st_c StCy) 'CxStD {}]
   [:assert '(genlCx CxStD CxStC) 'CxUniverse mono]
   [:assert '(genlCx CxStC CxStA) 'CxUniverse mono]])

(def ^:private rule-below-full-genlcx
  "`rule-below-genlcx` with the moved context holding more facts than there are antecedent
  keys, so the seeding builds the key fan (`special/key-fan`)."
  (into [(first rule-below-genlcx)]
        (concat (for [i (range 64)] [:assert (list 'st_c (symbol (str "StCy" i))) 'CxStD {}])
                (drop 2 rule-below-genlcx))))

(def ^:private except-beside-sameas
  [[:assert '(st_a StCy) 'CxStB {}]
   [:assert '(sameAs StCy StAnn) 'CxStB {}]
   [:assert '(st_d StAnn) 'CxStA {}]
   [:assert '(genlCx CxStC CxStA) 'CxUniverse mono]
   [:except 1 'CxStD]
   [:assert '(st_a StAnn) 'CxStB mono]
   [:assert (gen/forward '(implies (st_a ?x) (st_b ?x))) 'CxStB {}]
   [:assert '(genlCx CxStC CxStB) 'CxUniverse mono]
   [:assert '(genlCx CxStD CxStB) 'CxUniverse mono]
   [:assert '(disjoint st_d st_a) 'CxStB {}]
   [:except 2 'CxStA]])

(def known-padding-reads
  "Each site that reads a handle of P during a stream write at HEAD: the frame prefix that
  names it (the innermost frame of the stack at the read that any row names), what it
  reads, and a world it reads P on, `{:pad kinds :ops stream}` at one copy.  A change that
  removes a site fails `every-known-padding-read-fires-on-its-world` until its row is
  deleted."
  {:decide-synced
   {:frame "vaelii.impl.decide$synced"
    :reads "the related family's re-sync on a taxonomy move: every `disjoint` and its arguments"
    :world {:pad [:contradicts] :ops genl-edge}}
   :declaration-index
   {:frame "vaelii.impl.inherit$declaration_index"
    :reads "every preservation declaration (`transitiveInArgInverse` and its kin), on any write"
    :world {:pad [:sep] :ops disjoint-edge}}
   :excepted-edges
   {:frame "vaelii.impl.special$excepted_edges"
    :reads "every `except` and every placement an except write could reach"
    :world {:pad [:contradicts] :ops except-fact}}
   :move-except-contexts
   {:frame "vaelii.impl.special$move_except_contexts"
    :reads "every `except`, on a `genlCx` edge under a context an except is stated in"
    :world {:pad [:contradicts] :ops except-beside-sameas}}
   :place-inherited
   {:frame "vaelii.impl.chain$place_inherited_BANG_"
    :reads "every inherited-clash nogood and its placed justifications, republished whole"
    :world {:pad [:sep] :ops disjoint-edge}}
   :post-defeat-moves
   {:frame "vaelii.impl.settle$post_defeat_moves_BANG_"
    :reads "every stored `defeat`, when fewer are stored than the pass touched"
    :world {:pad [:defeat] :ops rule-fire}}
   :preserving-entries
   {:frame "vaelii.impl.discovery$preserving_entries"
    :reads "every inherited-clash entry over a separation, re-asked on a separation write (`sep-moved?`)"
    :world {:pad [:sep] :ops disjoint-edge}}
   :seeds-in
   {:frame "vaelii.impl.special$seeds_in"
    :reads "every forward rule, on a `genlCx` edge that moves a rule's context holding more facts than there are rule keys"
    :world {:pad [:rule] :ops rule-below-full-genlcx}}
   :supporter-summary
   {:frame "vaelii.impl.taxonomy$supporter_summary"
    :reads "a relation's whole stored extent, when a separation's supporter is read indirectly"
    :world {:pad [:contradicts] :ops except-beside-sameas}}})

(defn- sites
  "The sites of `known-padding-reads` and the unnamed stacks the stream's writes read P
  at, over `kinds` at `n` copies."
  [kinds n ops]
  (into #{} (mapcat :sites) (:reads (run-world kinds n ops known-padding-reads))))

(deftest every-known-padding-read-fires-on-its-world
  ;; forces the entailing reading: under constraints only nothing mints, so the mint rows have no world
  (tu/with-shipped-config
    (tu/with-entailing
      (doseq [[row {{:keys [pad ops]} :world}] (sort-by key known-padding-reads)]
        (is (contains? (sites pad 1 ops) row) (str row " reads no handle of P on its world"))))))

(deftest a-genlcx-edge-below-a-rule-reads-no-padding
  ;; the seeding reads the moved contexts' postings, which are fewer than the antecedent
  ;; keys, and so builds no key fan over the padding's rules (`special/key-fan`)
  (tu/with-shipped-config
    (is (= #{} (sites [:rule] 1 rule-below-genlcx)))))

(defn- stream-findings
  "For each seed, a `[seed n op site]` per read of P at `n` copies that no row names, and a
  `[seed n op]` per write after which belief over the stream's contexts differs from the
  run without P."
  [seeds nops ns]
  (vec (for [seed seeds
             :let [ops  (gen-stream seed nops)
                   bare (:beliefs (run-world pad-kinds 0 ops known-padding-reads))]
             n ns
             :let [{:keys [reads beliefs]} (run-world pad-kinds n ops known-padding-reads)]
             finding (concat (for [{:keys [op sites]} reads
                                   s sites
                                   :when (not (keyword? s))]
                               [seed n op s])
                             (for [i (range nops)
                                   :when (not= (nth bare i) (nth beliefs i))]
                               [seed n i :belief]))]
         finding)))

(deftest no-write-reads-padding-outside-a-known-site
  ;; forces the entailing reading: under constraints only nothing mints, and the stream reaches no mint
  (tu/with-shipped-config
    (tu/with-entailing (is (= [] (stream-findings [1 2 3] 30 [2]))))))

(deftest ^:slow no-write-reads-padding-outside-a-known-site-wide
  ;; forces the entailing reading: under constraints only nothing mints, and the stream reaches no mint
  (tu/with-shipped-config
    (tu/with-entailing (is (= [] (stream-findings (range 4 16) 60 [1 3]))))))
