;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.inherited-clash-oracle-test
  "The carried inherited clashes are the ones a full re-ask finds, and the ones a KB built
  from scratch finds.

  A randomized oracle runs one operation stream into two KBs, one with
  `discovery/*incremental-preserving*` bound false, and compares believed content, dilemmas,
  conflicts and refusals after every step, so a divergence names its operation.  A second
  replays what a stream left stored into a fresh KB in content order and compares the
  final readings, since both arms of the first ask through `discovery/preserving-entry`.  A
  third closes a `:disk-snapshot` KB after every write and reopens it from its reasoning
  image, so the memo the incremental arm carries crosses an install.  The
  stream writes claims of a preserved asymmetric predicate in three contexts, the `genl`
  edges and declarations the readings travel, and the `genlCx` edge that brings two
  contexts' claims into one reader (docs/nmtms.md, \"What qualifies as a nogood\")."
  (:require [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.test :refer [deftest is]]
            [clojure.walk :as walk]
            [vaelii.core :as v]
            [vaelii.impl.decide.inherited :as inherited]
            [vaelii.impl.discovery :as discovery]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu])
  (:import [java.io File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

;; ---- the shared ontology ------------------------------------------------
;;
;;   CxIcBase   ibig binary, asymmetric, preserved along genl at both positions
;;     ├─ CxIcLeft
;;     └─ CxIcRight
;;   CxIcJoin sees both once the stream writes its two edges
;;
;;   ic_top ← ic_mid ← ic_low, ic_top ← ic_side, and ic_far on its own

(def ^:private ctxs '[CxIcBase CxIcLeft CxIcRight])
(def ^:private types '[ic_top ic_mid ic_low ic_side ic_far])
(def ^:private edges '[[ic_mid ic_top] [ic_low ic_mid] [ic_side ic_top] [ic_far ic_side]])

(defn- build-ontology! [kb]
  (v/with-deferred-settle kb
    (doseq [c (rest ctxs)]
      (v/assert kb (list 'genlCx c (first ctxs)) 'CxUniverse {:strength :monotonic}))
    (doseq [d '[(binary_predicate ibig) (asymmetric ibig)]]
      (v/assert kb d (first ctxs) {:strength :monotonic}))
    (doseq [t types]
      (v/assert kb (list 'genl t 'thing) (first ctxs) {:strength :monotonic}))))

;; ---- the operation stream -----------------------------------------------

(defn- rand-op
  "One write: a claim or its denial at a random tuple, context and strength, a `genl`
  edge, a declaration, a statement of the `asymmetric` mark or a separation asserted or
  retracted, or a `genlCx` edge to `CxIcJoin`."
  [^java.util.Random rng]
  (let [pick (fn [xs] (nth xs (.nextInt rng (count xs))))
        ctx  #(pick ctxs)
        str8 #(if (zero? (.nextInt rng 2)) {:strength :monotonic} {})
        claim #(list 'ibig (pick types) (pick types))
        edge #(let [[a b] (pick edges)] (list 'genl a b))
        decl #(list 'transitiveInArgInverse 'ibig (inc (.nextInt rng 2)) 'genl)]
    (case (.nextInt rng 16)
      (0 1 2) [:assert (claim) (ctx) (str8)]
      3       [:assert (list 'not (claim)) (ctx) (str8)]
      4       [:retract (claim) (ctx)]
      (5 6)   [:assert (edge) (ctx) (str8)]
      7       [:retract (edge) (ctx)]
      8       [:assert (decl) (first ctxs) (str8)]
      9       [:retract (decl) (first ctxs)]
      10      [:assert (list 'genlCx 'CxIcJoin (nth ctxs 1)) 'CxUniverse {:strength :monotonic}]
      11      [:assert (list 'genlCx 'CxIcJoin (nth ctxs 2)) 'CxUniverse {:strength :monotonic}]
      ;; the build's own statement in `CxIcBase` stays, so a replay builds what streamed
      12      [:assert '(asymmetric ibig) (pick (rest ctxs)) (str8)]
      13      [:retract '(asymmetric ibig) (pick (rest ctxs))]
      14      [:assert '(disjoint ic_far ic_mid) (ctx) (str8)]
      15      [:retract '(disjoint ic_far ic_mid) (ctx)])))

(defn- apply-op!
  "Run one op, returning a refusal's `:type` as an observation the two KBs must agree on."
  [kb [kind sentence context opts]]
  (try (case kind
         :assert  (do (v/assert kb sentence context opts) :ok)
         :retract (if-let [h (v/handle-of kb sentence context)]
                    (do (v/retract! kb h) :ok)
                    :absent))
       (catch clojure.lang.ExceptionInfo e
         [:refused (:type (ex-data e))])))

;; ---- the observation ----------------------------------------------------

(defn- clash-key
  "A reported clash as content, without handles, which differ between the two KBs."
  [e]
  [(:priority e) (:kind e) (:sentence e) (:sentence (:inherited e))
   (into #{} (map (juxt :sentence :context :defeat-class)) (:sides e))])

(defn- snapshot [kb]
  {:believed  (into #{}
                    (comp (filter #(v/in? kb %))
                          (keep #(p/get-sentex (:records kb) %))
                          (map (juxt :sentence :context))
                          (map #(tu/handle-free kb %)))
                    (jtms/in-datums (reasoning/tms kb)))
   :standing  (into #{}
                    (for [[_ ng] (inherited/inherited-clashes kb)]
                      [(:sentence ng) (:vantages ng)]))
   :members   (into #{}
                    (comp (keep #(p/get-sentex (:records kb) %))
                          (map (juxt :sentence :context))
                          (map #(tu/handle-free kb %)))
                    (:members (:inherited @(reasoning/nogood-candidates kb))))
   :dilemmas  (into #{} (map clash-key) (v/contradictions kb))
   :conflicts (into #{} (map clash-key) (v/conflicts kb))
   :joined    (into #{} (map clash-key) (v/contradictions kb 'CxIcJoin))})

(defn- diff
  "`{key {la only-in-a lb only-in-b}}` over the snapshot keys where `a` and `b` differ; a
  map-valued key (`reader-snapshot`'s `:reads`) diffs per entry."
  ([a b] (diff a b :incremental-only :exhaustive-only))
  ([a b la lb]
   (into {} (keep (fn [k]
                    (let [x (get a k) y (get b k)]
                      (when (not= x y)
                        [k (if (map? x)
                             (diff x y la lb)
                             {la (set/difference x y) lb (set/difference y x)})]))))
         (keys a))))

(defn- run-stream
  "The same ops into both KBs, comparing after every write.  Returns `[step op
  incremental-snapshot exhaustive-snapshot]` for the first divergence, or nil."
  [ops]
  (let [inc-kb (tu/empty-kb)
        exh-kb (tu/isolated-fresh)]
    (try
      (binding [discovery/*incremental-preserving* true]  (build-ontology! inc-kb))
      (binding [discovery/*incremental-preserving* false] (build-ontology! exh-kb))
      (loop [step 0, [op & more] ops]
        (if-not op
          nil
          (let [ri (binding [discovery/*incremental-preserving* true]  (apply-op! inc-kb op))
                re (binding [discovery/*incremental-preserving* false] (apply-op! exh-kb op))
                si (snapshot inc-kb)
                se (snapshot exh-kb)]
            (if (and (= ri re) (= si se))
              (recur (inc step) more)
              [step op si se]))))
      (finally (tu/clear-kb! inc-kb) (tu/clear-kb! exh-kb)))))

(defn- settled
  "`ops` into one KB under `incremental?`, returning `(observe kb)` after the last,
  `snapshot` by default."
  ([ops incremental?] (settled ops incremental? snapshot))
  ([ops incremental? observe]
   (let [kb (if incremental? (tu/empty-kb) (tu/isolated-fresh))]
     (try
       (binding [discovery/*incremental-preserving* incremental?]
         (build-ontology! kb)
         (run! #(apply-op! kb %) ops)
         (observe kb))
       (finally (tu/clear-kb! kb))))))

(defn- divergence [[step op si se]]
  (str "diverged at step " step " on " (pr-str op) "\n" (pr-str (diff si se))))

;; ---- oracle 1: randomized operation streams -----------------------------

(deftest randomized-streams-find-the-same-inherited-clashes
  (doseq [seed (range 10)]
    (let [rng (java.util.Random. (long seed))
          r   (run-stream (repeatedly 40 #(rand-op rng)))]
      (is (nil? r) (str "seed " seed " " (when r (divergence r)))))))

(defn- rand-separated-op
  "One write over memberships of the shared types in three metatypes, `ic_down` preserved
  down `genl` and `ic_up` up it: a membership or its retraction at a random context and
  strength, a `genl` edge, a declaration, a separation of two of the metatypes asserted or
  retracted, or a `genlCx` edge to `CxIcJoin`.  Three writes in four are `:monotonic`, so
  a reading is often known-true."
  [^java.util.Random rng]
  (let [pick   (fn [xs] (nth xs (.nextInt rng (count xs))))
        ctx    #(pick ctxs)
        str8   #(if (zero? (.nextInt rng 4)) {} {:strength :monotonic})
        member #(list (pick '[ic_down ic_up ic_plain]) (pick types))
        edge   #(let [[a b] (pick edges)] (list 'genl a b))
        sep    #(pick '[(disjoint ic_down ic_up) (disjoint ic_down ic_plain)
                        (partition ic_whole ic_up ic_plain)])]
    (case (.nextInt rng 12)
      (0 1 2) [:assert (member) (ctx) (str8)]
      3       [:retract (member) (ctx)]
      (4 5)   [:assert (edge) (ctx) (str8)]
      6       [:retract (edge) (ctx)]
      7       [:assert (pick '[(transitiveInArgInverse ic_down 1 genl) (transitiveInArg ic_up 1 genl)])
               (first ctxs) (str8)]
      8       [:assert (sep) (ctx) (str8)]
      9       [:retract (sep) (ctx)]
      10      [:assert (list 'genlCx 'CxIcJoin (nth ctxs 1)) 'CxUniverse {:strength :monotonic}]
      11      [:assert (list 'genlCx 'CxIcJoin (nth ctxs 2)) 'CxUniverse {:strength :monotonic}])))

(def ^:private separated-declarations
  '[[:assert (transitiveInArgInverse ic_down 1 genl) CxIcBase {:strength :monotonic}]
    [:assert (transitiveInArg ic_up 1 genl) CxIcBase {:strength :monotonic}]])

(deftest randomized-streams-over-separated-memberships-find-the-same-inherited-clashes
  (doseq [seed (range 10)]
    (let [rng (java.util.Random. (long seed))
          r   (run-stream (into separated-declarations
                                (repeatedly 60 #(rand-separated-op rng))))]
      (is (nil? r) (str "seed " seed " " (when r (divergence r)))))))

(defn- rand-type-edge-op
  "`rand-separated-op`, or in one write in three a membership of `ic_sub` or a `genl` edge
  between the membership types, asserted or retracted: `ic_sub` below a part of the
  partition, and the preserved `ic_down` below `ic_dsup`, which goes below a part."
  [^java.util.Random rng]
  (let [pick (fn [xs] (nth xs (.nextInt rng (count xs))))
        edge #(let [[a b] (pick '[[ic_sub ic_plain] [ic_sub ic_up] [ic_down ic_dsup]
                                  [ic_dsup ic_plain] [ic_dsup ic_whole]])]
                (list 'genl a b))]
    (case (.nextInt rng 9)
      0 [:assert (list 'ic_sub (pick types)) (pick ctxs) {:strength :monotonic}]
      1 [:assert (edge) (pick ctxs) {:strength :monotonic}]
      2 [:retract (edge) (pick ctxs)]
      (rand-separated-op rng))))

(defn- type-edge-streams [seeds]
  (doseq [seed seeds]
    (let [rng (java.util.Random. (long seed))
          r   (run-stream (into separated-declarations
                                (repeatedly 60 #(rand-type-edge-op rng))))]
      (is (nil? r) (str "seed " seed " " (when r (divergence r)))))))

(deftest a-sample-of-streams-over-edges-between-membership-types-finds-the-same-inherited-clashes
  (type-edge-streams (range 3)))

(deftest ^:slow streams-over-edges-between-membership-types-find-the-same-inherited-clashes
  (type-edge-streams (range 3 20)))

;; ---- oracle 2: directed streams -----------------------------------------

(deftest a-second-known-true-claim-is-read-where-the-first-was-carried
  ;; the declarations, edges and stored claim `:monotonic`, so the clash is a conflict and
  ;; its report names the claim read; `(ibig ic_mid ic_side)` arrives reaching the same
  ;; tuple and sorts before `(ibig ic_top ic_side)`, with nothing of the standing clash
  ;; moving
  (is (nil? (run-stream
             [[:assert '(transitiveInArgInverse ibig 1 genl) 'CxIcBase {:strength :monotonic}]
              [:assert '(transitiveInArgInverse ibig 2 genl) 'CxIcBase {:strength :monotonic}]
              [:assert '(genl ic_mid ic_top) 'CxIcBase {:strength :monotonic}]
              [:assert '(genl ic_low ic_mid) 'CxIcBase {:strength :monotonic}]
              [:assert '(ibig ic_side ic_low) 'CxIcBase {:strength :monotonic}]
              [:assert '(ibig ic_top ic_side) 'CxIcBase {:strength :monotonic}]
              [:assert '(ibig ic_far ic_far) 'CxIcBase {}]
              [:assert '(ibig ic_mid ic_side) 'CxIcBase {:strength :monotonic}]
              [:assert '(ibig ic_far ic_top) 'CxIcBase {}]]))))

(deftest a-reading-withdrawn-at-the-vantage-is-read-again-there
  ;; the stored claim is known-true, so the reading's `:default` edge is the pair's unique
  ;; weakest member and loses at CxIcJoin alone; CxIcJoin then reads the second route, and
  ;; every later settle clears the scoped defeats and decides them again
  (is (nil? (run-stream
             [[:assert '(genlCx CxIcJoin CxIcLeft) 'CxUniverse {:strength :monotonic}]
              [:assert '(genlCx CxIcJoin CxIcRight) 'CxUniverse {:strength :monotonic}]
              [:assert '(transitiveInArgInverse ibig 1 genl) 'CxIcBase {:strength :monotonic}]
              [:assert '(transitiveInArgInverse ibig 2 genl) 'CxIcBase {:strength :monotonic}]
              [:assert '(genl ic_low ic_mid) 'CxIcLeft {}]
              [:assert '(genl ic_mid ic_top) 'CxIcLeft {:strength :monotonic}]
              [:assert '(genl ic_low ic_far) 'CxIcLeft {}]
              [:assert '(genl ic_far ic_top) 'CxIcLeft {:strength :monotonic}]
              [:assert '(ibig ic_side ic_low) 'CxIcRight {:strength :monotonic}]
              [:assert '(ibig ic_top ic_side) 'CxIcLeft {:strength :monotonic}]
              [:assert '(ibig ic_far ic_far) 'CxIcBase {}]
              [:assert '(ibig ic_side ic_far) 'CxIcBase {}]]))))

(deftest a-clash-split-across-contexts-is-carried-through-its-scoped-defeat
  ;; the stored default in CxIcRight loses at CxIcJoin only, so every settle re-decides it
  ;; there while it stays believed in CxIcRight
  (is (nil? (run-stream
             [[:assert '(transitiveInArgInverse ibig 1 genl) 'CxIcBase {:strength :monotonic}]
              [:assert '(transitiveInArgInverse ibig 2 genl) 'CxIcBase {:strength :monotonic}]
              [:assert '(genl ic_low ic_mid) 'CxIcLeft {:strength :monotonic}]
              [:assert '(genl ic_mid ic_top) 'CxIcLeft {:strength :monotonic}]
              [:assert '(ibig ic_side ic_low) 'CxIcRight {}]
              [:assert '(genlCx CxIcJoin CxIcLeft) 'CxUniverse {:strength :monotonic}]
              [:assert '(genlCx CxIcJoin CxIcRight) 'CxUniverse {:strength :monotonic}]
              [:assert '(ibig ic_top ic_side) 'CxIcLeft {:strength :monotonic}]
              [:assert '(ibig ic_far ic_far) 'CxIcBase {}]
              [:retract '(genl ic_mid ic_top) 'CxIcLeft]
              [:assert '(ibig ic_far ic_side) 'CxIcBase {}]]))))

(deftest a-route-edge-raised-to-known-true-is-read-again
  ;; every route rests on a `:default` edge, so the reading opposes nothing until the
  ;; route through ic_mid is raised to `:monotonic`; the claim then opposes the stored
  ;; converse at that route, and the converse loses
  (let [ops '[[:assert (transitiveInArgInverse ibig 1 genl) CxIcBase {:strength :monotonic}]
              [:assert (transitiveInArgInverse ibig 2 genl) CxIcBase {:strength :monotonic}]
              [:assert (genl ic_low ic_mid) CxIcBase {}]
              [:assert (genl ic_mid ic_top) CxIcBase {}]
              [:assert (genl ic_low ic_top) CxIcBase {}]
              [:assert (ibig ic_side ic_low) CxIcBase {}]
              [:assert (ibig ic_top ic_side) CxIcBase {:strength :monotonic}]
              [:assert (genl ic_low ic_mid) CxIcBase {:strength :monotonic}]
              [:assert (genl ic_mid ic_top) CxIcBase {:strength :monotonic}]]]
    (is (nil? (run-stream ops)))
    (is (= [#{} false]
           ((juxt :dilemmas #(contains? (:believed %) '[(ibig ic_side ic_low) CxIcBase]))
            (settled ops true))))))

(def ^:private joined-last
  "Two known-true claims in CxIcLeft and CxIcRight that clash through `(genl ic_low
  ic_mid)` in a reader that sees both, with that reader's second `genlCx` edge written
  last.  The `icAgeOf` pair gives CxIcLeft a scoped defeat, and the `anti_transitive`
  writes are settles whose region holds nothing of the clash."
  '[[:assert (functional icAgeOf) CxIcBase {:strength :monotonic}]
    [:assert (genl ic_low ic_mid) CxIcBase {:strength :monotonic}]
    [:assert (ibig ic_mid ic_low) CxIcRight {:strength :monotonic}]
    [:assert (icAgeOf IcI2 0) CxIcBase {}]
    [:assert (ibig ic_low ic_low) CxIcLeft {:strength :monotonic}]
    [:assert (icAgeOf IcI2 2) CxIcLeft {:strength :monotonic}]
    [:assert (genlCx CxIcJoin CxIcLeft) CxUniverse {:strength :monotonic}]
    [:assert (transitiveInArgInverse ibig 2 genl) CxIcBase {:strength :monotonic}]
    [:assert (anti_transitive icPrecedes) CxIcBase {:strength :monotonic}]
    [:assert (transitiveInArgInverse ibig 2 genl) CxIcBase {}]
    [:assert (anti_transitive icPrecedes) CxIcBase {:strength :monotonic}]
    [:assert (genlCx CxIcJoin CxIcRight) CxUniverse {:strength :monotonic}]])

(deftest a-genlCx-edge-that-joins-a-denial-and-its-claim-forms-the-pair-in-either-order
  (let [joins?    #(= 'genlCx (first (second %)))
        reference (settled (into (filterv joins? joined-last) (remove joins?) joined-last)
                           true)]
    (is (seq (:conflicts reference)))
    (is (nil? (run-stream joined-last)))
    (is (= reference (settled joined-last true) (settled joined-last false)))))

(def ^:private guarded-claim
  "A standing clash whose stored side a guarded rule concludes, beside a second entry.
  The reading is known-true and the conclusion `:default`, so the conclusion loses the
  clash and nothing is reported.  A `:monotonic` blocker stores the conclusion with a
  guard defeat, and its retraction withdraws the defeat."
  '[[:assert (transitiveInArgInverse ibig 1 genl) CxIcBase {:strength :monotonic}]
    [:assert (genl ic_mid ic_top) CxIcBase {:strength :monotonic}]
    [:assert (genl ic_low ic_mid) CxIcBase {:strength :monotonic}]
    [:assert (ibig ic_top ic_side) CxIcBase {:strength :monotonic}]
    [:assert (exceptWhen (ic_skip ?x)
                         (set/defaultRule
                          (set/forwardRule (implies (and (icLink ?x ?y)) (ibig ?x ?y)))))
     CxIcBase {}]
    [:assert (icLink ic_side ic_low) CxIcBase {}]
    [:assert (ibig ic_far ic_side) CxIcBase {}]
    [:assert (ic_skip ic_side) CxIcBase {:strength :monotonic}]
    [:retract (ic_skip ic_side) CxIcBase]
    [:retract (icLink ic_side ic_low) CxIcBase]])

(def ^:private hidden-claim
  "`guarded-claim` with its blocker `:default`: the firing is stored, and its guard defeat at
  the firing's own placement joins the nogood's defeat of the same loser as one `defeat`
  handle.  The clash stands, since detection reads the network and no placed defeat."
  (assoc-in guarded-claim [7 3] {}))

(defn- hidden-reads
  "The conclusion `(ibig ic_side ic_low)` at CxIcBase: whether it is stored and believed,
  the informants of its `defeat`'s justifications, and the standing clashes."
  [kb]
  (let [f (v/handle-of kb '(ibig ic_side ic_low) 'CxIcBase)
        d (when f (v/handle-of kb (list 'defeat (list 'sentexHandle f)) 'CxIcBase))]
    {:stored?    (some? f)
     :believed?  (boolean (and f (v/believed? kb f 'CxIcBase)))
     :informants (into #{} (map :informant) (when d (:support (tu/why-root kb d))))
     :standing   (:standing (snapshot kb))}))

(defn- below-reads
  "Whether CxIcBelow, under CxIcBase and excepting the blocker, believes the blocker and
  the conclusion."
  [kb]
  (let [b (v/handle-of kb '(ic_skip ic_side) 'CxIcBase)
        f (v/handle-of kb '(ibig ic_side ic_low) 'CxIcBase)]
    (v/assert kb '(genlCx CxIcBelow CxIcBase) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'except (list 'sentexHandle b)) 'CxIcBelow {})
    {:blocker (v/believed? kb b 'CxIcBelow) :claim (v/believed? kb f 'CxIcBelow)}))

(deftest a-guard-defeat-joins-the-nogoods-defeat-and-the-clash-stands
  (let [clash (:standing (settled (take 7 hidden-claim) true))
        r8    (settled (take 8 hidden-claim) true hidden-reads)
        r9    (settled (take 9 hidden-claim) true hidden-reads)]
    (is (seq clash))
    (is (= {:stored? true :believed? false :informants '#{guard nogood} :standing clash} r8))
    (is (= {:stored? true :believed? false :informants '#{nogood} :standing clash} r9)
        "the blocker's retraction takes the guard justification")
    (is (= {:blocker false :claim false} (settled (take 8 hidden-claim) true below-reads))
        "the guard is out of force at CxIcBelow, and the nogood's defeat keeps the claim out")
    (is (nil? (run-stream hidden-claim)))))

(defn- verdict-reads
  "The rows where the justification verdicts disagree with belief over every sentex
  stored in the four contexts, at each of them (`tu/verdict-violations`)."
  [kb]
  (let [cs (conj ctxs 'CxIcJoin)]
    (tu/verdict-violations kb (into [] (comp (mapcat #(v/sentexes-in-context kb %)) (map :id)) cs) cs)))

(deftest every-prefix-of-the-hidden-claim-stream-reads-its-verdicts-as-its-belief
  (is (= (repeat (count hidden-claim) [])
         (map #(settled (take % hidden-claim) true verdict-reads)
              (range 1 (inc (count hidden-claim)))))))

(deftest a-guard-defeat-reads-alike-whatever-its-blocker-is-spelled
  ;; `ia_skip` sorts before the claim's functor and `ic_skip` after it
  (let [spelled (walk/postwalk-replace {'ic_skip 'ia_skip} hidden-claim)]
    (doseq [n [8 9]]
      (is (= (settled (take n hidden-claim) true hidden-reads)
             (settled (take n spelled) true hidden-reads))
          (str "step " n)))))

(def ^:private retracted-reasons
  "A standing conflict beside a second entry, its members `:monotonic`, then the mark, the
  declaration and an edge the reading rests on retracted and the first two asserted
  again: each retraction's region holds a handle with no record."
  '[[:assert (transitiveInArgInverse ibig 1 genl) CxIcBase {:strength :monotonic}]
    [:assert (genl ic_mid ic_top) CxIcBase {:strength :monotonic}]
    [:assert (genl ic_low ic_mid) CxIcBase {:strength :monotonic}]
    [:assert (ibig ic_side ic_low) CxIcBase {:strength :monotonic}]
    [:assert (ibig ic_top ic_side) CxIcBase {:strength :monotonic}]
    [:assert (ibig ic_far ic_side) CxIcBase {}]
    [:retract (asymmetric ibig) CxIcBase]
    [:assert (asymmetric ibig) CxIcBase {:strength :monotonic}]
    [:retract (transitiveInArgInverse ibig 1 genl) CxIcBase]
    [:assert (transitiveInArgInverse ibig 1 genl) CxIcBase {:strength :monotonic}]
    [:retract (genl ic_low ic_mid) CxIcBase]])

(deftest a-retracted-reason-leaves-the-clash-it-read
  (is (seq (:conflicts (settled (take 6 retracted-reasons) true))) "the clash stands")
  (is (empty? (:conflicts (settled (take 7 retracted-reasons) true))) "the mark leaves it")
  (is (nil? (run-stream retracted-reasons))))

(def ^:private predicate-edge-streams
  "A standing clash that a `genl` edge between predicates carries, then that edge
  retracted.  In the first stream the edge carries the `asymmetric` mark down to `icSub`
  (`tax/props-over`); in the second it makes `icSub`'s claim one of `ibig`'s.  The edge is
  neither a member of the entry nor its stored claim, and moves no input of the memo's
  key, so the entry is re-asked only because the retracted edge's sentence, kept under
  `:left` (`discovery/note-removed!`), reaches it."
  (let [edges '[[:assert (genl ic_low ic_mid) CxIcBase {:strength :monotonic}]
                [:assert (genl ic_mid ic_top) CxIcBase {:strength :monotonic}]
                [:assert (genl icSub ibig) CxIcBase {}]
                [:assert (icSub ic_top ic_side) CxIcBase {:strength :monotonic}]]
        drop  '[:retract (genl icSub ibig) CxIcBase]]
    [(-> '[[:assert (transitiveInArgInverse icSub 1 genl) CxIcBase {:strength :monotonic}]]
         (into edges)
         (conj '[:assert (icSub ic_side ic_low) CxIcBase {}] drop))
     (-> '[[:assert (transitiveInArgInverse ibig 1 genl) CxIcBase {:strength :monotonic}]]
         (into edges)
         (conj '[:assert (ibig ic_side ic_low) CxIcBase {}] drop))]))

(deftest a-retracted-genl-edge-between-predicates-leaves-the-clash-it-carried
  (doseq [ops predicate-edge-streams]
    (is (seq (:standing (settled (pop ops) true))) "the clash stands")
    (is (nil? (run-stream ops)))))

;; ---- oracle 3: the stored set replayed from scratch ----------------------

(defn- stored-set
  "The sentences `ops` name that `kb` still stores as premises, `[sentence context
  strength]`, in content order."
  [kb ops]
  (let [tms (reasoning/tms kb)]
    (->> (distinct (map (fn [[_ s c]] [s c]) ops))
         (keep (fn [[s c]]
                 (when-let [h (v/handle-of kb s c)]
                   (when-let [st (jtms/premise-strength tms h)] [s c st]))))
         (sort-by (fn [[s c]] [(pr-str s) (str c)])))))

(defn- replay-divergence
  "Run `ops` into one KB, replay its `stored-set` into a fresh KB one write at a time, and
  return the stored set and where the two final snapshots differ, or nil."
  [ops]
  (let [kb (tu/empty-kb)]
    (try
      (build-ontology! kb)
      (run! #(apply-op! kb %) ops)
      (let [streamed (snapshot kb)
            ws       (stored-set kb ops)
            rk       (tu/isolated-fresh)]
        (try
          (build-ontology! rk)
          (doseq [[s c st] ws] (v/assert rk s c {:strength st}))
          (let [replayed (snapshot rk)]
            (when (not= streamed replayed)
              {:stored ws :diff (diff streamed replayed :streamed-only :replayed-only)}))
          (finally (tu/clear-kb! rk))))
      (finally (tu/clear-kb! kb)))))

(defn- replayed-streams [seeds]
  (doseq [seed seeds]
    (let [rng (java.util.Random. (long seed))
          r   (replay-divergence (repeatedly 40 #(rand-op rng)))]
      (is (nil? r) (str "seed " seed " " (pr-str r))))))

(deftest ^:slow streams-replayed-from-scratch-read-as-streamed
  (replayed-streams (range 100 130)))

(deftest a-sample-of-streams-replayed-from-scratch-reads-as-streamed
  (replayed-streams (range 100 103)))

;; ---- a later pass of one settle -----------------------------------------

(defn- two-pass-settle
  "One settle over a batch that stores `n` claims and a standing clash beside a fact that
  blocks a guarded firing, so the settle runs a second pass whose touched set still holds every
  claim.  `[snapshot questions passes]` under `incremental?`, `questions` the
  `preserving-entry` calls the settle made."
  [n incremental?]
  (let [kb    (if incremental? (tu/empty-kb) (tu/isolated-fresh))
        calls (atom 0)
        orig  @#'discovery/preserving-entry]
    (try
      (binding [discovery/*incremental-preserving* incremental?]
        (build-ontology! kb)
        (v/assert kb '(exceptWhen (ic_skip ?x)
                                  (set/defaultRule
                                   (set/forwardRule (implies (and (ic_probe ?x)) (ic_seen ?x)))))
                  'CxIcBase)
        (doseq [x '[IcA IcB]] (v/assert kb (list 'ic_probe x) 'CxIcBase))
        (with-redefs [discovery/preserving-entry (fn [kb s] (swap! calls inc) (orig kb s))]
          (v/with-deferred-settle kb
            (run! #(apply-op! kb %)
                  (concat [[:assert '(transitiveInArgInverse ibig 1 genl) 'CxIcBase {:strength :monotonic}]
                           [:assert '(genl ic_mid ic_top) 'CxIcBase {:strength :monotonic}]
                           [:assert '(genl ic_low ic_mid) 'CxIcBase {:strength :monotonic}]
                           [:assert '(ibig ic_side ic_low) 'CxIcBase {:strength :monotonic}]
                           [:assert '(ibig ic_top ic_side) 'CxIcBase {:strength :monotonic}]]
                          (for [i (range n)]
                            [:assert (list 'ibig 'ic_far (symbol (str "ic_far_" i))) 'CxIcBase {}])
                          [[:assert '(ic_skip IcA) 'CxIcBase {}]]))))
        [(snapshot kb) @calls (:passes (v/settle-stats kb))])
      (finally (tu/clear-kb! kb)))))

(deftest a-later-pass-asks-only-the-claims-an-earlier-pass-moved
  ;; The touched set a pass reads spans the settle, so a second pass that read it whole would
  ;; ask every claim the first asked again; the discovery reads what the touched set recorded
  ;; since its own last mark (`jtms/touched-since`).  The exhaustive arm asks every pass.
  (let [n 60
        [si qi pi] (two-pass-settle n true)
        [se qe pe] (two-pass-settle n false)]
    (is (= 2 pi pe) "the batch's settle runs a second pass in each arm")
    (is (= si se) (pr-str (diff si se)))
    (is (seq (:conflicts si)) "the standing clash is read in the batch")
    (is (< qi (+ n 10)) (str "the incremental arm asked " qi " questions over two passes"))
    (is (> qe (* 2 n)) (str "the exhaustive arm asks each pass whole: " qe))))

;; ---- a retraction in the region -----------------------------------------

(defn- entry-settles
  "`n` stored claims that each keep an entry, each reached by a `:default` reading of a
  claim on `ic_top`, beside a guarded firing per term of `ic_probe`.  Then each op of
  `ops` under its own settle.  `[snapshot entries questions]` under `incremental?`,
  `questions` the `preserving-entry` calls each op's settle made."
  [n ops incremental?]
  (let [kb    (if incremental? (tu/empty-kb) (tu/isolated-fresh))
        calls (atom 0)
        orig  @#'discovery/preserving-entry]
    (try
      (binding [discovery/*incremental-preserving* incremental?]
        (build-ontology! kb)
        (v/assert kb '(exceptWhen (ic_skip ?x)
                                  (set/defaultRule
                                   (set/forwardRule (implies (and (ic_probe ?x)) (ic_seen ?x)))))
                  'CxIcBase)
        (v/with-deferred-settle kb
          (run! #(apply-op! kb %)
                (concat [[:assert '(transitiveInArgInverse ibig 1 genl) 'CxIcBase {}]
                         [:assert '(genl ic_mid ic_top) 'CxIcBase {}]
                         [:assert '(genl ic_low ic_mid) 'CxIcBase {}]
                         [:assert '(ic_probe IcA) 'CxIcBase {}]
                         [:assert '(ic_probe IcB) 'CxIcBase {}]]
                        (for [i (range n), :let [t (symbol (str "ic_s_" i))]]
                          [:assert (list 'ibig t 'ic_low) 'CxIcBase {}])
                        (for [i (range n), :let [t (symbol (str "ic_s_" i))]]
                          [:assert (list 'ibig 'ic_top t) 'CxIcRight {}]))))
        (let [entries (count (:entries @(reasoning/preserved-clashes kb)))
              qs      (with-redefs [discovery/preserving-entry
                                    (fn [kb s] (swap! calls inc) (orig kb s))]
                        (mapv (fn [op] (reset! calls 0) (apply-op! kb op) @calls) ops))]
          [(snapshot kb) entries qs]))
      (finally (tu/clear-kb! kb)))))

(deftest a-retraction-in-the-region-asks-only-what-it-moved
  ;; Each op's region holds a handle whose record is gone: a retracted fact with its
  ;; conclusion, a firing the guard block sweeps on a second pass, and a stored claim
  ;; holding an entry.  The exhaustive arm asks every entry on every settle.
  (let [n   40
        ops '[[:retract (ic_probe IcB) CxIcBase]
              [:assert (ic_skip IcA) CxIcBase {}]
              [:retract (ibig ic_s_0 ic_low) CxIcBase]]
        [si ni qi] (entry-settles n ops true)
        [se _  qe] (entry-settles n ops false)]
    (is (= si se) (pr-str (diff si se)))
    (is (>= ni n) (str ni " entries stand before the retractions"))
    (is (every? #(< % 10) qi) (str "the incremental arm asked " qi))
    (is (every? #(>= % (dec n)) qe) (str "the exhaustive arm asks every entry: " qe))))

;; ---- the republish ------------------------------------------------------------

(defn- standing-clashes!
  "Build `n` standing inherited clashes in CxIcBase: each `:default` `(ibig ic_lotwo_i
  ic_lo_i)` against the monotonic `(ibig ic_hi_i ic_hitwo_i)`, which reaches its converse
  through `(genl ic_lo_i ic_hi_i)` and `(genl ic_lotwo_i ic_hitwo_i)` with both positions
  preserved along `genl`."
  [kb n]
  (let [M {:strength :monotonic}
        t (fn [s i] (symbol (str s i)))]
    (build-ontology! kb)
    (doseq [d '[(type_relation_predicate ibig) (transitiveInArgInverse ibig 1 genl)
                (transitiveInArgInverse ibig 2 genl)]]
      (v/assert kb d 'CxIcBase M))
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'genl (t "ic_lo_" i) (t "ic_hi_" i)) 'CxIcBase M)
        (v/assert kb (list 'genl (t "ic_lotwo_" i) (t "ic_hitwo_" i)) 'CxIcBase M)
        (v/assert kb (list 'ibig (t "ic_lotwo_" i) (t "ic_lo_" i)) 'CxIcBase {})
        (v/assert kb (list 'ibig (t "ic_hi_" i) (t "ic_hitwo_" i)) 'CxIcBase M)))))

(defn- republished
  "`[snapshot standing per-settle]` for `ops` after `n` standing clashes under
  `incremental?`: the standing clashes before the ops, and per settle the clashes the
  candidate index took (`install-inherited!`) or the member sets it read again
  (`update-inherited!`)."
  [n ops incremental?]
  (let [kb      (if incremental? (tu/empty-kb) (tu/isolated-fresh))
        settles (atom [])
        install inherited/install-inherited!
        revise  inherited/update-inherited!]
    (try
      (binding [discovery/*incremental-preserving* incremental?]
        (standing-clashes! kb n)
        (let [standing (count (inherited/inherited-clashes kb))]
          (with-redefs [inherited/install-inherited!
                        (fn [kb ngs] (swap! settles conj (count ngs)) (install kb ngs))
                        inherited/update-inherited!
                        (fn [kb changes sets-of] (swap! settles conj (count changes))
                          (revise kb changes sets-of))]
            (run! #(apply-op! kb %) ops))
          [(snapshot kb) standing @settles]))
      (finally (tu/clear-kb! kb)))))

(deftest a-write-beside-standing-clashes-republishes-only-the-sets-it-moved
  ;; An unrelated fact, its retraction and a claim of the preserved predicate no clash
  ;; reads hand the candidate index no set; retracting and restoring one clash's claim
  ;; hands it that clash's set.  The exhaustive arm hands it every standing clash.
  (let [n   40
        ops '[[:assert (ic_probe IcC) CxIcBase {}]
              [:retract (ic_probe IcC) CxIcBase]
              [:assert (ibig ic_pu ic_pv) CxIcLeft {}]
              [:retract (ibig ic_lotwo_0 ic_lo_0) CxIcBase]
              [:assert (ibig ic_lotwo_0 ic_lo_0) CxIcBase {}]]
        [si ni ri] (republished n ops true)
        [se _ re]  (republished n ops false)]
    (is (= si se) (pr-str (diff si se)))
    (is (= n ni) (str ni " clashes stand before the ops"))
    (is (every? #(<= % 1) ri) (str "the incremental arm republished " ri))
    (is (every? #(>= % (dec n)) re) (str "the exhaustive arm republishes every clash: " re))))

;; ---- a declaration in the region -------------------------------------------

(deftest a-separation-no-entry-reads-asks-no-entry
  ;; A `disjoint` moves a flat-cache entry no question of a binary claim reads, so the
  ;; settles of its assert and its retract ask no entry.  A second statement of the
  ;; preserved predicate's `asymmetric` mark moves an entry every question reads, and
  ;; asks them again.  The exhaustive arm asks every entry on every settle.
  (let [n   40
        ops '[[:assert (disjoint ic_far ic_side) CxIcBase {}]
              [:retract (disjoint ic_far ic_side) CxIcBase]
              [:assert (asymmetric ibig) CxIcLeft {}]]
        [si ni qi] (entry-settles n ops true)
        [se _  qe] (entry-settles n ops false)]
    (is (= si se) (pr-str (diff si se)))
    (is (>= ni n) (str ni " entries stand before the declarations"))
    (is (= [0 0] (subvec qi 0 2)) (str "the incremental arm asked " qi))
    (is (>= (qi 2) n) (str "the mark's settle asks the entries again: " qi))
    (is (every? #(>= % (dec n)) qe) (str "the exhaustive arm asks every entry: " qe))))

;; ---- a separation a membership entry reads --------------------------------

(defn- membership-settles
  "Three stored memberships `(ic_red w)` of a predicate preserved along `icPartOf`, each
  reached by `(not (ic_red IcCar))` through `(icPartOf w IcCar)`, so each keeps an entry
  that reads the types of its term: `IcMw0` in `ic_wheel`, `IcMw1` in `ic_wheel_sub`
  below it, `IcMw2` in `ic_spoke`.  Then each op of `ops` under its own settle.
  `[snapshot questions]` under `incremental?`, `questions` the `preserving-entry` calls
  each op's settle made."
  [ops incremental?]
  (let [kb    (if incremental? (tu/empty-kb) (tu/isolated-fresh))
        calls (atom 0)
        orig  @#'discovery/preserving-entry]
    (try
      (binding [discovery/*incremental-preserving* incremental?]
        (build-ontology! kb)
        (v/with-deferred-settle kb
          (run! #(apply-op! kb %)
                (concat '[[:assert (transitive icPartOf) CxIcBase {:strength :monotonic}]
                          [:assert (transitiveInArgInverse ic_red 1 icPartOf) CxIcBase {}]
                          [:assert (genl ic_wheel thing) CxIcBase {}]
                          [:assert (genl ic_wheel_sub ic_wheel) CxIcBase {}]
                          [:assert (genl ic_spoke thing) CxIcBase {}]
                          [:assert (genl ic_hub thing) CxIcBase {}]
                          [:assert (not (ic_red IcCar)) CxIcBase {}]]
                        (for [[t i] '[[ic_wheel 0] [ic_wheel_sub 1] [ic_spoke 2]]
                              :let  [w (symbol (str "IcMw" i))]
                              s     [(list t w) (list 'icPartOf w 'IcCar) (list 'ic_red w)]]
                          [:assert s 'CxIcBase {}]))))
        (let [qs (with-redefs [discovery/preserving-entry
                               (fn [kb s] (swap! calls inc) (orig kb s))]
                   (mapv (fn [op] (reset! calls 0) (apply-op! kb op) @calls) ops))]
          [(snapshot kb) qs]))
      (finally (tu/clear-kb! kb)))))

(deftest a-moved-separation-asks-the-membership-entries-below-its-types
  ;; No inherited reading reads a separation, so a `disjoint` over `ic_wheel` arriving and
  ;; leaving asks no entry, and neither does one over two types no entry names.
  (let [ops '[[:assert (disjoint ic_wheel ic_hub) CxIcBase {}]
              [:retract (disjoint ic_wheel ic_hub) CxIcBase]
              [:assert (disjoint ic_far ic_side) CxIcBase {}]]
        [si qi] (membership-settles ops true)
        [se]    (membership-settles ops false)]
    (is (= si se) (pr-str (diff si se)))
    (is (= [0 0 0] qi) (str "the incremental arm asked " qi))))

;; ---- a `genl` edge into a separated type ----------------------------------

(defn- edge-settles
  "`n` stored memberships `(ic_wheel w)` of a type `disjoint` from `ic_red`, a predicate
  preserved along `icPartOf` whose claim `(ic_red IcCar)` reaches `(ic_red IcHw)`
  through `(icPartOf IcHw IcCar)`, the membership `(ic_hub IcHw)` and the sentences
  `extra`, every sentence `:monotonic`.  Then each op of `ops` under its own settle.
  `[snapshot questions]` under `incremental?`, `questions` the `preserving-entry` calls
  each op's settle made."
  [n extra ops incremental?]
  (let [kb    (if incremental? (tu/empty-kb) (tu/isolated-fresh))
        calls (atom 0)
        orig  @#'discovery/preserving-entry
        m     {:strength :monotonic}]
    (try
      (binding [discovery/*incremental-preserving* incremental?]
        (build-ontology! kb)
        (v/with-deferred-settle kb
          (run! #(apply-op! kb %)
                (concat (for [s (concat '[(transitive icPartOf) (transitiveInArgInverse ic_red 1 icPartOf)
                                          (genl ic_wheel thing) (genl ic_hub thing)
                                          (disjoint ic_red ic_wheel) (ic_red IcCar)
                                          (icPartOf IcHw IcCar) (ic_hub IcHw)]
                                        extra)]
                          [:assert s 'CxIcBase m])
                        (for [i (range n)]
                          [:assert (list 'ic_wheel (symbol (str "IcEw" i))) 'CxIcBase m]))))
        (let [qs (with-redefs [discovery/preserving-entry
                               (fn [kb s] (swap! calls inc) (orig kb s))]
                   (mapv (fn [op] (reset! calls 0) (apply-op! kb op) @calls) ops))]
          [(snapshot kb) qs]))
      (finally (tu/clear-kb! kb)))))

(defn- edge-questions
  "`edge-settles` over 8 and over 32 memberships for `(genl ic_hub ic_wheel)` written,
  retracted and written again: `{n questions}`, with each snapshot asserted equal to the
  exhaustive arm's and holding the edge's clash."
  [extra]
  (let [edge '(genl ic_hub ic_wheel)
        ops  [[:assert edge 'CxIcBase {:strength :monotonic}]
              [:retract edge 'CxIcBase]
              [:assert edge 'CxIcBase {:strength :monotonic}]]]
    (into {} (for [n [8 32]
                   :let [[si qi] (edge-settles n extra ops true)
                         [se]    (edge-settles n extra ops false)]]
               (do (is (= si se) (pr-str (diff si se)))
                   (is (seq (:conflicts si)) "the edge's clash stands")
                   [n qi])))))

(deftest a-genl-edge-asks-the-memberships-below-its-lower-end-and-none-below-its-upper
  ;; `(genl ic_hub ic_wheel)` places `ic_hub` under a type separated from `ic_red`, so
  ;; `(ic_hub IcHw)` beside the reached `(ic_red IcHw)` is a clash.  The edge moves the
  ;; separations of the types at or below `ic_hub` alone, so its settles ask as many
  ;; entries over 8 memberships of `ic_wheel` as over 32.
  (let [qs (edge-questions [])]
    (is (= (qs 8) (qs 32)) (str "questions per settle " qs))))

(deftest a-genl-edge-asks-a-predicate-preserved-along-genl-at-its-closure-terms-alone
  ;; With `ic_red` preserved along `genl` too and the crossing narrowing off, the edge moves
  ;; `ic_red`, and its questions are the facts at the terms of the edge's closure, not
  ;; `ic_red`'s extent and the memberships of every type separated from it.
  (with-redefs [inherit/crossing-closure-cap 0]
    (let [qs (edge-questions '[(transitiveInArgInverse ic_red 1 genl)])]
      (is (= (qs 8) (qs 32)) (str "questions per settle " qs)))))

(deftest a-genl-edge-above-a-preserved-type-places-the-clash-of-the-memberships-it-separates-in-either-order
  ;; `(genl ic_dsup ic_hard)` places the preserved `ic_dn`, below `ic_dsup`, under
  ;; `ic_hard`, which is disjoint from `ic_plain`, so the stored `(ic_plain ic_mid)` beside
  ;; the reached `(ic_dn ic_mid)` is a clash.  Neither end of the edge is separated from a
  ;; preserved predicate.
  (let [w    #(vector :assert % 'CxIcBase {:strength :monotonic})
        edge (w '(genl ic_dsup ic_hard))
        base (mapv w '[(transitiveInArgInverse ic_dn 1 genl) (genl ic_mid ic_top)
                       (disjoint ic_hard ic_plain) (genl ic_dn ic_dsup) (ic_dn ic_top)
                       (ic_plain ic_mid)])
        late (settled (conj base edge) true)]
    (is (seq (:conflicts late)) "the clash stands")
    (is (= (settled (into [edge] base) true) late) "the edge written first or last")))

(defn- build-route!
  "The shared ontology, and a membership predicate `ic_red` preserved along `icPartOf`:
  the stored `(ic_red IcLa)` and the claim `(not (ic_red IcLcar))` are known-true; the
  `:default` route `(icPartOf IcLa IcLcar)` between them loses in `CxIcBase` to a
  monotonic denial, which an `except` in `CxIcLeft` hides there.  The route is a
  `:default` reason, so the reading over it is undercut and forms no inherited clash in
  any context.  `IcLa` is held `ic_blue`."
  [kb]
  (let [m {:strength :monotonic}]
    (build-ontology! kb)
    (doseq [s '[(transitive icPartOf) (transitiveInArgInverse ic_red 1 icPartOf) (genl ic_red thing)
                (genl ic_blue thing) (ic_red IcLa) (not (ic_red IcLcar))]]
      (v/assert kb s 'CxIcBase m))
    (v/assert kb '(icPartOf IcLa IcLcar) 'CxIcBase {})
    (v/assert kb '(ic_blue IcLa) 'CxIcBase {})
    (let [denial (v/assert kb '(not (icPartOf IcLa IcLcar)) 'CxIcBase m)]
      (v/assert kb (list 'except (list 'sentexHandle denial)) 'CxIcLeft {}))))

(defn- restored-at-left
  "Whether `(ic_red IcLa)` is believed at `[CxIcLeft CxIcBase]` before each op and after
  the last, under `incremental?`: the claim `(not (ic_red IcLcar))` and the route
  `(icPartOf IcLa IcLcar)` are known-true in `CxIcBase` and the stored `(ic_red IcLa)` is
  `:default`, so the inherited clash defeats it.  `:except` hides the route at `CxIcBase`,
  `:meta` excepts that except in `CxIcLeft`, and `:unmeta` retracts it."
  [ops incremental?]
  (let [kb (if incremental? (tu/empty-kb) (tu/isolated-fresh))
        m  {:strength :monotonic}]
    (try
      (binding [discovery/*incremental-preserving* incremental?]
        (build-ontology! kb)
        (doseq [s '[(transitive icPartOf) (transitiveInArgInverse ic_red 1 icPartOf)
                    (genl ic_red thing) (not (ic_red IcLcar))]]
          (v/assert kb s 'CxIcBase m))
        (let [route  (v/assert kb '(icPartOf IcLa IcLcar) 'CxIcBase m)
              stored (v/assert kb '(ic_red IcLa) 'CxIcBase {})
              hs     (atom {})
              read   #(mapv (fn [c] (v/believed? kb stored c)) '[CxIcLeft CxIcBase])]
          (into [(read)]
                (map (fn [op]
                       (case op
                         :except (swap! hs assoc :except
                                        (v/assert kb (list 'except (list 'sentexHandle route)) 'CxIcBase {}))
                         :meta   (swap! hs assoc :meta
                                        (v/assert kb (list 'except (list 'sentexHandle (:except @hs))) 'CxIcLeft {}))
                         :unmeta (v/retract! kb (:meta @hs)))
                       (read)))
                ops)))
      (finally (tu/clear-kb! kb)))))

(deftest a-meta-except-restoring-a-reason-below-a-membership-entry-decides-its-clash-there
  ;; The except hides the known-true route at `CxIcBase`, which takes the clash away
  ;; there; the meta-except shows the route at `CxIcLeft` alone, and the carried entry is
  ;; asked again there, which the exhaustive arm asks every settle.
  (let [ops [:except :meta :unmeta]
        re  (restored-at-left ops false)]
    (is (= [[false false] [true true] [false true] [true true]] re) "the exhaustive arm")
    (is (= re (restored-at-left ops true)) "the incremental arm")))

;; ---- oracle 4: randomized streams over a preserved membership ------------------

(defn- build-membership-world!
  "`build-route!`, a disjoint metatype `ic_kind`, the type `ic_green`, and `CxIcJoin`
  below `CxIcLeft`."
  [kb]
  (build-route! kb)
  (doseq [[s c] '[[(disjoint_metatype ic_kind) CxIcBase] [(genl ic_green thing) CxIcBase]
                  [(genlCx CxIcJoin CxIcLeft) CxUniverse]]]
    (v/assert kb s c {:strength :monotonic})))

(defn- rand-membership-op
  "One write over `build-membership-world!`: a metatype membership of a type, `:default`
  in half the writes, or its monotonic denial, asserted or retracted; a `disjoint` of
  `ic_red` with another type; a membership, a claim, a route or an unrelated fact; or
  the `genlCx` edge from `CxIcJoin` to `CxIcRight`."
  [^java.util.Random rng]
  (let [pick (fn [xs] (nth xs (.nextInt rng (count xs))))
        ctx  #(pick ctxs)
        str8 #(if (zero? (.nextInt rng 2)) {:strength :monotonic} {})
        term #(pick '[IcLa IcLb IcLcar])
        kind #(list 'ic_kind (pick '[ic_red ic_blue ic_green]))
        type #(pick '[ic_blue ic_green])]
    (case (.nextInt rng 12)
      0  [:assert (kind) (ctx) (str8)]
      1  [:retract (kind) (ctx)]
      2  [:assert (list 'not (kind)) (ctx) {:strength :monotonic}]
      3  [:retract (list 'not (kind)) (ctx)]
      4  [:assert (list 'disjoint 'ic_red (type)) (ctx) {}]
      5  [:retract (list 'disjoint 'ic_red (type)) (ctx)]
      6  [:assert (list (type) (term)) (ctx) (str8)]
      7  [:assert (list 'ic_red (term)) (ctx) (str8)]
      8  [:assert (list 'icPartOf (term) (term)) (ctx) (str8)]
      9  [:retract (list 'icPartOf (term) (term)) (ctx)]
      10 [:assert (list 'icUnrel (term) (term)) (ctx) {}]
      11 [:assert '(genlCx CxIcJoin CxIcRight) 'CxUniverse {:strength :monotonic}])))

(defn- reader-snapshot
  "`snapshot`, with what each context reads of the routes and the memberships."
  [kb]
  (assoc (snapshot kb) :reads
         (into {} (for [c (conj ctxs 'CxIcJoin)
                        g '[(icPartOf ?x ?y) (ic_red ?x) (not (ic_red ?x)) (ic_blue ?x)
                            (ic_green ?x) (ic_kind ?x)]]
                    [[c g] (set (v/query kb g c))]))))

(defn- membership-stream-divergence
  "`ops` into an incremental and an exhaustive `build-membership-world!`, comparing their
  `reader-snapshot`s after every write: the first `[step op incremental exhaustive]` that
  differs, or nil."
  [ops]
  (let [inc-kb (tu/empty-kb)
        exh-kb (tu/isolated-fresh)]
    (try
      (binding [discovery/*incremental-preserving* true]  (build-membership-world! inc-kb))
      (binding [discovery/*incremental-preserving* false] (build-membership-world! exh-kb))
      (loop [step 0, [op & more] ops]
        (when op
          (let [ri (binding [discovery/*incremental-preserving* true]  (apply-op! inc-kb op))
                re (binding [discovery/*incremental-preserving* false] (apply-op! exh-kb op))
                si (reader-snapshot inc-kb)
                se (reader-snapshot exh-kb)]
            (if (and (= ri re) (= si se))
              (recur (inc step) more)
              [step op si se]))))
      (finally (tu/clear-kb! inc-kb) (tu/clear-kb! exh-kb)))))

(defn- membership-streams [seeds]
  (doseq [seed seeds]
    (let [rng (java.util.Random. (long seed))
          r   (membership-stream-divergence (repeatedly 30 #(rand-membership-op rng)))]
      (is (nil? r) (str "seed " seed " " (when r (divergence r)))))))

(deftest a-sample-of-membership-streams-reads-as-the-exhaustive-arm
  (membership-streams (range 3)))

(deftest ^:slow membership-streams-read-as-the-exhaustive-arm
  (membership-streams (range 3 40)))

;; ---- across an image install ----------------------------------------------

(defn- reopened-stream
  "`ops` into a `:disk-snapshot` KB that is closed after every write and reopened from
  its own reasoning image, and into an exhaustive KB, comparing after every write.
  Returns `[installs divergence]`: whether each reopen installed the image (an install
  leaves the manifest as it was), and `run-stream`'s divergence or nil."
  [ops]
  (let [dir    (str (Files/createTempDirectory "vaelii-ic-image-" (into-array FileAttribute [])))
        mf     (io/file dir "reasoning" "manifest.edn")
        text   #(when (.exists mf) (slurp mf))
        open   #(v/open-kb {:backend :disk-snapshot :dir dir})
        exh-kb (tu/isolated-fresh)]
    (try
      (binding [discovery/*incremental-preserving* false] (build-ontology! exh-kb))
      (let [kb (open)] (build-ontology! kb) (v/close! kb))
      (loop [step 0, [op & more] ops, installs []]
        (if-not op
          [installs nil]
          (let [before   (text)
                kb       (open)
                installs (conj installs (= before (text)))
                [ri si]  (try [(apply-op! kb op) (snapshot kb)] (finally (v/close! kb)))
                re       (binding [discovery/*incremental-preserving* false] (apply-op! exh-kb op))
                se       (snapshot exh-kb)]
            (if (and (= ri re) (= si se))
              (recur (inc step) more installs)
              [installs [step op si se]]))))
      (finally
        (tu/clear-kb! exh-kb)
        (doseq [^File f (reverse (file-seq (io/file dir)))] (.delete f))))))

(defn- reopened-streams
  "Each seed's stream of `n` writes through `reopened-stream`."
  [seeds n]
  ;; Each session's one write is its network's first settle, the settle a mark the image
  ;; carried from the session before would name.
  (doseq [seed seeds]
    (let [rng (java.util.Random. (long seed))
          [installs r] (reopened-stream (repeatedly n #(rand-op rng)))]
      (is (every? true? installs) (str "seed " seed " recovered on a reopen: " installs))
      (is (nil? r) (str "seed " seed " " (when r (divergence r)))))))

(deftest ^:slow streams-reopened-from-the-image-after-every-write-find-the-same-inherited-clashes
  (reopened-streams (range 200 210) 20))

(deftest a-sampled-stream-reopened-from-the-image-finds-the-same-inherited-clashes
  (tu/with-snapshot-platform
    ;; seed 201's eighteenth write is a denial whose clash a mark carried across the install
    ;; hid
    (reopened-streams [201] 18)))

(deftest a-monotonic-blocker-reads-as-a-default-one-and-the-clash-stands
  (is (seq (:standing (settled (take 7 guarded-claim) true))) "the derived claim clashes")
  (is (= (settled (take 8 hidden-claim) true hidden-reads)
         (settled (take 8 guarded-claim) true hidden-reads)))
  (is (nil? (run-stream guarded-claim))))
