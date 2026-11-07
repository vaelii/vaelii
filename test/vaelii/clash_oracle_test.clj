;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.clash-oracle-test
  "A membership clash stream read as it arrives equals the same writes loaded from
  scratch.  Each test runs one operation sequence into a KB and compares its believed
  content, dilemmas and conflicts with a second KB holding the stream's net writes, the
  sentences stored and not retracted at their strongest strength, written in content
  order after the ontology.  A divergence names the operation after which the two
  readings differ (docs/nmtms.md, \"The nogood families\").  The streams draw
  the membership families alone: the tuple marks' nogoods are compared with the belief
  reference by `reference_test`'s random worlds, which cover `disjoint` and `covering`
  too.

  No `transitiveInArg` declaration is made, since a claim read through argument
  preservation convicts one way only (docs/nmtms.md, \"Where conviction is one-sided\").
  A `sameAs` merge of two individuals and a `rewriteOf` merge of two types arrive and
  leave, so a clash also forms across two spellings of one term.  A pair across a
  visibility edge is covered: individuals are written in either context."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

;; ---- the shared ontology ------------------------------------------------

(def ^:private ctxs '[CxClashBase CxClashSub])

(def ^:private types
  '[animal mammal reptile dog cat snake wolf plant])

(def ^:private inds
  "One pool of individuals for both contexts, so a term routinely holds one membership
  either side of the `genlCx` edge — the pair only `CxClashSub` can see whole
  (see the namespace docstring)."
  '[CI0 CI1 CI2 CI3 CI4 CI5])

(defn- build-ontology!
  "A hierarchy a separation closes over several levels of, and two contexts.
  `(disjoint dog cat)`, `(genl snake animal)` and `(sibling_disjoint animal)` are left
  for the stream,
  so declarations also arrive over stored content.  Two rules conclude `(dog ?x)`, so a
  second route from a `:monotonic` premise can lift a standing pair's `:priority` while
  both its handles sit still.  A third reads `animal`, a clash member a defeat can hide,
  above the `genl` chain `wolf`, `canid`, `animal` that a `(rewriteOf canis canid)` merge
  restates.  No membership names `canid`, so the type merge restates edges alone."
  [kb]
  (v/with-deferred-settle kb
    (v/assert kb (list 'genlCx (second ctxs) (first ctxs)) 'CxUniverse)
    (doseq [[sub sup] '[[mammal animal] [reptile animal] [dog mammal] [cat mammal]
                        [wolf canid] [canid animal]]]
      (v/assert kb (list 'genl sub sup) (first ctxs) {:strength :monotonic}))
    (v/assert kb '(disjoint mammal reptile) (first ctxs) {:strength :monotonic})
    (v/assert kb '(disjoint animal plant)   (first ctxs) {:strength :monotonic})
    (doseq [from '[pet canine]]
      (v/assert kb (list 'set/forwardRule (vr/rule-sentence [(list from '?x)] '(dog ?x)))
                (first ctxs) {:strength :monotonic}))
    (v/assert kb (list 'set/forwardRule (vr/rule-sentence ['(animal ?x)] '(breather ?x)))
              (first ctxs) {:strength :monotonic})))

;; ---- the operation stream -----------------------------------------------

(defn- rand-op
  "One write, drawn over every route a membership clash arrives by: a membership, a
  retraction, a premise a rule derives a membership from, a declaration arriving after the content it convicts, a
  sibling-disjoint exception arriving and leaving, an individual or a type merge arriving
  and leaving."
  [^java.util.Random rng]
  (let [ctx  (nth ctxs (.nextInt rng (count ctxs)))
        ind  #(nth inds  (.nextInt rng (count inds)))
        typ  #(nth types (.nextInt rng (count types)))
        str8 #(if (zero? (.nextInt rng 3)) {:strength :monotonic} {})]
    (case (.nextInt rng 22)
      (0 1 2 3 4 5 6) [:assert (list (typ) (ind)) ctx (str8)]
      7       [:retract (list (typ) (ind)) ctx]
      8       [:assert '(disjoint dog cat) (first ctxs) {:strength :monotonic}]
      9       [:assert '(genl snake animal) (first ctxs) {:strength :monotonic}]
      (10 11) [:assert (list (if (even? (.nextInt rng 2)) 'pet 'canine) (ind)) ctx (str8)]
      12      [:retract (list (if (even? (.nextInt rng 2)) 'pet 'canine) (ind)) ctx]
      (13 14) [:retract (list (typ) (ind)) ctx]
      15      [:assert '(sibling_disjoint animal) (first ctxs) {:strength :monotonic}]
      16      [:assert '(siblingDisjointException dog cat) (first ctxs) {:strength :monotonic}]
      17      [:retract '(siblingDisjointException dog cat) (first ctxs)]
      18      [:assert (list 'sameAs (ind) (ind)) (first ctxs) {:strength :monotonic}]
      19      [:retract (list 'sameAs (ind) (ind)) (first ctxs)]
      20      [:assert '(rewriteOf canis canid) (first ctxs) {:strength :monotonic}]
      21      [:retract '(rewriteOf canis canid) (first ctxs)])))

(defn- apply-op!
  "Run one op, returning a refusal as an observation the two KBs must agree on."
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
  "A reported pair as content: kind, rank, `contradicts` form and sides, without the
  handles, which differ between the two KBs."
  [e]
  [(:kind e) (:priority e) (:sentence e)
   (into #{} (map (juxt :sentence :context :defeat-class)) (:sides e))])

(defn- snapshot
  "The network's believed sentexes, which of the stream's own a reader believes at read
  time (`[sentence context reader]`, each reader seeing the context), the reports and the
  violations ledger.  `keep?` filters the handles both belief sets read."
  ([kb] (snapshot kb (constantly true)))
  ([kb keep?]
   (let [in   (filterv keep? (jtms/in-datums (reasoning/tms kb)))
         sxs  (keep #(p/get-sentex (:records kb) %) in)
         free #(tu/handle-free kb %)]
     {:believed   (into #{} (map (comp free (juxt v/sentence-of :context))) sxs)
      :read       (into #{}
                        (for [sx sxs
                              :let [c (:context sx)]
                              :when (some #{c} ctxs)
                              r (if (= c (first ctxs)) ctxs [c])
                              :when (v/believed? kb (:id sx) r)]
                          (free [(v/sentence-of sx) c r])))
      :dilemmas   (into #{} (map clash-key) (v/contradictions kb))
      :conflicts  (into #{} (map clash-key) (v/conflicts kb))
      :violations (into #{} (map :violation) (v/violations kb))})))

(defn- diff [a b]
  (into {} (keep (fn [k]
                   (let [x (get a k) y (get b k)]
                     (when (not= x y)
                       [k {:arrived-only      (set/difference x y)
                           :from-scratch-only (set/difference y x)}]))))
        (keys a)))

;; ---- randomized operation streams -----------------------------------------

(defn- trial-ops
  "`steps` ops of `seed`'s stream in arrival order `order`: 0 as drawn, any other a
  seeded shuffle of the same ops."
  [seed steps order]
  (let [rng (java.util.Random. (long seed))
        ops (vec (repeatedly steps #(rand-op rng)))]
    (if (zero? (long order))
      ops
      (let [l (java.util.ArrayList. ^java.util.Collection ops)]
        (java.util.Collections/shuffle l (java.util.Random. (+ (* 1000 (long seed)) (long order))))
        (vec l)))))

(defn- step-net
  "`net` (`{[sentence context] opts-or-:gone}`) after op `[kind sentence context opts]`
  answered `result`: a stored assert keeps the stronger of two strengths, and a retract
  marks the sentence gone."
  [net [kind sentence context opts] result]
  (if (not= :ok result)
    net
    (case kind
      :assert  (update net [sentence context]
                       (fn [was] (if (or (= :monotonic (:strength opts))
                                         (and (map? was) (= :monotonic (:strength was))))
                                   {:strength :monotonic}
                                   {})))
      :retract (assoc net [sentence context] :gone))))

(defn- from-scratch
  "The reading `read` (`snapshot` by default) of a KB holding `net`'s writes: the
  ontology, its retracted sentences retracted, then every stored sentence of `net` in
  content order."
  ([net] (from-scratch net snapshot))
  ([net read]
   (let [kb (tu/isolated-fresh)]
     (try
       (build-ontology! kb)
       (doseq [[[s c] opts] (sort-by (comp pr-str key) net)]
         (if (= :gone opts)
           (when-let [h (v/handle-of kb s c)] (v/retract! kb h))
           (v/assert kb s c opts)))
       (read kb)
       (finally (tu/clear-kb! kb))))))

(defn- reading
  "A reading compared across the two KBs: `snapshot` without the violations ledger,
  which records the order the writes arrived in."
  [kb]
  (dissoc (snapshot kb) :violations))

(defn- trial-snapshot
  "`snapshot` without the placed `contradicts` and `defeat` sentexes that name a superseded
  member.  Whether such a member is stored depends on whether a firing or a restatement
  over its spelling was made before the merge, so for it the trial compares the belief of
  every other sentex and the reports, which leave it out."
  [kb]
  (let [tms  (reasoning/tms kb)
        sup? (fn [h]
               (when-let [s (:sentence (p/get-sentex (:records kb) h))]
                 (and (seq? s) (contains? #{'contradicts 'defeat} (first s))
                      (some #(jtms/superseded? tms %) (keep sx/handle-id (rest s))))))]
    (snapshot kb (complement sup?))))

(defn- run-trial
  "`ops` into one KB, comparing its reading with `from-scratch` after every `every`th
  write and the last.  Returns `[step op arrived from-scratch]` for the first divergence,
  or nil."
  [ops every]
  (let [kb (tu/empty-kb)]
    (try
      (build-ontology! kb)
      (loop [step 0, net {}, [op & more] ops]
        (when op
          (let [net (step-net net op (apply-op! kb op))]
            (if (or (empty? more) (zero? (mod (inc step) every)))
              (let [si (dissoc (trial-snapshot kb) :violations)
                    se (dissoc (from-scratch net trial-snapshot) :violations)]
                (if (= si se)
                  (recur (inc step) net more)
                  [step op si se]))
              (recur (inc step) net more)))))
      (finally (tu/clear-kb! kb)))))

(defn- stream-reading
  "One KB's reading after `steps` of `seed`'s stream, on whatever retrieval strategy is
  bound around the call."
  [seed steps]
  (let [kb (tu/empty-kb)]
    (try
      (build-ontology! kb)
      (let [rng (java.util.Random. (long seed))]
        (dotimes [_ steps] (apply-op! kb (rand-op rng))))
      (snapshot kb)
      (finally (tu/clear-kb! kb)))))

(defn- directed-stream
  "A fixed op sequence into one KB, its reading compared with `from-scratch` after every
  write, one `is` per write.  Returns the stream KB's last contradictions."
  [ops]
  (let [kb (tu/empty-kb)]
    (try
      (build-ontology! kb)
      (let [net (reduce (fn [net [i op]]
                          (let [net (step-net net op (apply-op! kb op))
                                si  (reading kb)
                                se  (dissoc (from-scratch net) :violations)]
                            (is (= si se) (str "step " i " " (pr-str op) ": " (pr-str (diff si se))))
                            net))
                        {} (map-indexed vector ops))]
        (when (seq net) (v/contradictions kb)))
      (finally (tu/clear-kb! kb)))))

(deftest the-retrieval-strategy-does-not-change-what-clashes
  ;; `matches-visible` returns `(animal CI2)` beside the `(dog CI2)` that implies it, in
  ;; an order each retrieval path chooses, and `checks/membership-handles` names one of
  ;; them.  In the default suite because only the weekly `deep.yml` runs `VAELII_HIER=0`.
  (doseq [seed (range 4)]
    (is (= (binding [res/*hierarchical-retrieval* true]  (stream-reading seed 24))
           (binding [res/*hierarchical-retrieval* false] (stream-reading seed 24)))
        (str "seed " seed ": the retrieval strategy changed the clash reading"))))

(deftest the-lead-side-does-not-change-what-clashes
  ;; `checks/membership-handles` leads from the `matches-visible` reference under
  ;; `:scoped` and from the term's own postings under `:auto` / `:agnostic`, and
  ;; arbitration turns belief on the handle it names.
  (doseq [seed (range 4)]
    (let [scoped   (binding [res/*lead-side* :scoped]   (stream-reading seed 24))
          auto     (binding [res/*lead-side* :auto]     (stream-reading seed 24))
          agnostic (binding [res/*lead-side* :agnostic] (stream-reading seed 24))]
      (is (= scoped auto agnostic)
          (str "seed " seed ": the lead side changed the clash reading"
               "\n  scoped vs auto:     " (pr-str (diff scoped auto))
               "\n  scoped vs agnostic: " (pr-str (diff scoped agnostic)))))))

(deftest ^:slow randomized-streams-read-as-their-writes-loaded-from-scratch
  (doseq [seed (range 12), order (range 3)]
    (let [[step op si se] (run-trial (trial-ops seed 45 order) 15)]
      (is (nil? step)
          (str "seed " seed " order " order " diverged at step " step " on " (pr-str op) "\n"
               (pr-str (diff si se)))))))

(deftest a-seeded-stream-reads-as-its-writes-loaded-from-scratch
  ;; one seed of the `^:slow` sweep, so `:default` runs the harness: its stream merges
  ;; `canid` after a firing of the `animal` rule climbed `(genl wolf canid)`
  (let [[step op si se] (run-trial (trial-ops 11 45 1) 15)]
    (is (nil? step)
        (str "seed 11 diverged at step " step " on " (pr-str op) "\n" (pr-str (diff si se))))))

;; ---- a declaration arriving over stored content ---------------------------
;;
;; A separation arriving over content stored long before it, a shape a random stream may
;; not draw.

(deftest a-separation-arriving-last-finds-what-it-convicts
  (let [pool inds]
    (directed-stream
     (concat
      (for [x pool] [:assert (list 'dog x) (first ctxs) {}])
      (for [x pool] [:assert (list 'cat x) (first ctxs) {}])
      [[:assert '(disjoint dog cat) (first ctxs) {:strength :monotonic}]]
      ;; and a settle after it, where a dropped pair would vanish
      [[:assert (list 'plant (first pool)) (first ctxs) {}]]))))

;; ---- a vocabulary moving under standing memberships ------------------------
;;
;; A `genl` edge or a separation moving under standing memberships that sit still.

(deftest vocabulary-moving-under-standing-content-agrees
  (directed-stream
   [;; content first, and nothing about it moves again
    [:assert '(dog CI0)   'CxClashBase {}]
    [:assert '(snake CI0) 'CxClashBase {}]
    [:assert '(dog CI1)   'CxClashBase {}]
    [:assert '(cat CI1)   'CxClashBase {}]
    ;; …then the vocabulary moves under it, twice
    [:assert '(genl snake reptile) 'CxClashBase {:strength :monotonic}]
    [:assert '(disjoint dog cat)   'CxClashBase {:strength :monotonic}]
    ;; a settle that touches neither pair: both must still be reported
    [:assert '(plant CI4) 'CxClashBase {}]
    ;; and the separations leaving again
    [:retract '(disjoint dog cat) 'CxClashBase]
    [:retract '(genl snake reptile) 'CxClashBase]
    [:assert '(plant CI5) 'CxClashBase {}]]))

;; ---- a length arriving after the declaration that minted under it ---------
;;
;; The declaration entails `(unary_predicate kindC)` and mints `(kindC CI0)`.  A
;; `(binary_predicate kindC)` arriving after it withdraws the entailment and the minted
;; membership breaks the length and is held inert; arriving before it, the declaration
;; waits and mints neither.  The binding leaving re-asks the declaration in every order.

(deftest a-length-arriving-after-a-minting-declaration-reads-as-one-arriving-before-it
  (tu/with-entailing
    (let [decl   [:assert '(arg usesKindC 1 kindC) 'CxClashBase {}]
          fact   [:assert '(usesKindC CI0 CI1) 'CxClashBase {}]
          bind   [:assert '(binary_predicate kindC) 'CxClashBase {:strength :monotonic}]
          unbind [:retract '(binary_predicate kindC) 'CxClashBase]]
      (doseq [ops [[decl fact bind unbind] [bind decl fact unbind] [decl bind fact unbind]]]
        (directed-stream ops)))))

;; ---- a genl edge under a standing pair -----------------------------------
;;
;; Four shapes of a `genl` edge moving under a pair, one test each.

(deftest a-genl-edge-elsewhere-leaves-a-standing-pair-alone
  ;; the count at the end fails a reading that dropped every pair
  (let [cs (directed-stream
            [;; a standing pair on `mammal` / `reptile`, and nothing about it moves again
             [:assert '(mammal CI0)  'CxClashBase {}]
             [:assert '(reptile CI0) 'CxClashBase {}]
             ;; edges arriving and leaving under types the pair does not name
             [:assert '(genl snake reptile) 'CxClashBase {:strength :monotonic}]
             [:assert '(genl plant thing)   'CxClashBase {:strength :monotonic}]
             [:assert '(cat CI3) 'CxClashBase {}]
             [:retract '(genl plant thing) 'CxClashBase]
             [:retract '(genl snake reptile) 'CxClashBase]
             [:assert '(cat CI4) 'CxClashBase {}]])]
    (is (= 1 (count cs))
        "the pair the edges were never about is still the one standing dilemma")))

(deftest a-genl-edge-the-pair-rests-on-withdraws-it-when-it-goes
  ;; the clash `(dog CI0)` / `(plant CI0)` rests on `(genl mammal animal)`, an edge
  ;; between types neither sentence names, so a reading of the two functors alone would
  ;; carry the pair after the edge goes
  (directed-stream
   [[:assert '(dog CI0)   'CxClashBase {}]
    [:assert '(plant CI0) 'CxClashBase {}]
    ;; a settle that touches neither, so the pair is standing rather than arriving
    [:assert '(cat CI3) 'CxClashBase {}]
    ;; ...and the edge the separation reaches `dog` through goes
    [:retract '(genl mammal animal) 'CxClashBase]
    [:assert '(cat CI4) 'CxClashBase {}]
    ;; and comes back, so the pair has to be found a second time
    [:assert '(genl mammal animal) 'CxClashBase {:strength :monotonic}]
    [:assert '(cat CI5) 'CxClashBase {}]]))

(deftest an-edge-relating-two-supertypes-withdraws-their-separation
  ;; `clsh_amphi_t` stands under both `clsh_car_t` and `clsh_boat_t`, so the closing edge
  ;; between them moves neither member's closure.  `tax/disjointness-test`'s
  ;; genl-relatedness guard reads that edge.  In the sibling row the exceptions leave the
  ;; pair of the two supertypes as the one separating the members.
  (doseq [[arm decls]
          {:sibling '[(sibling_disjoint clsh_craft_t)
                      (genl clsh_car_t clsh_craft_t)
                      (genl clsh_boat_t clsh_craft_t)
                      (siblingDisjointException clsh_amphi_t clsh_yacht_t)
                      (siblingDisjointException clsh_car_t clsh_yacht_t)]
           :metatype '[(disjoint_metatype clsh_kind_t)
                       (clsh_kind_t clsh_car_t)
                       (clsh_kind_t clsh_boat_t)]
           :partition '[(partition clsh_craft_t clsh_car_t clsh_boat_t)]}]
    (let [m   {:strength :monotonic}
          ops (-> (mapv (fn [d] [:assert d 'CxClashBase m]) decls)
                  (into [[:assert '(genl clsh_amphi_t clsh_car_t) 'CxClashBase m]
                         [:assert '(genl clsh_amphi_t clsh_boat_t) 'CxClashBase m]
                         [:assert '(genl clsh_yacht_t clsh_boat_t) 'CxClashBase m]
                         [:assert '(clsh_amphi_t CI0) 'CxClashBase {}]
                         [:assert '(clsh_yacht_t CI0) 'CxClashBase {}]
                         ;; a settle that touches neither, so the pair is standing
                         [:assert '(cat CI3) 'CxClashBase {}]]))
          end (into ops [[:assert '(genl clsh_car_t clsh_boat_t) 'CxClashBase m]
                         [:assert '(cat CI4) 'CxClashBase {}]])]
      (is (= 1 (count (directed-stream ops))) (str arm ": the pair stands before the edge"))
      (is (empty? (directed-stream end)) (str arm ": the edge leaves nothing separating it")))))

(deftest an-edge-two-contexts-support-is-read-from-each-of-them
  ;; the edge keeps its `CxClashSub` supporter, so the relation stands while the base
  ;; context's pair loses its separation
  (directed-stream
   [[:assert '(genl mammal animal) 'CxClashSub {:strength :monotonic}]
    [:assert '(dog CI0)   'CxClashBase {}]
    [:assert '(plant CI0) 'CxClashBase {}]
    [:assert '(dog CI1)   'CxClashSub {}]
    [:assert '(plant CI1) 'CxClashSub {}]
    [:assert '(cat CI3) 'CxClashBase {}]
    ;; the base supporter goes; the sub one keeps the edge alive
    [:retract '(genl mammal animal) 'CxClashBase]
    [:assert '(cat CI4) 'CxClashBase {}]]))

(deftest a-metatype-member-leaving-withdraws-what-it-was-separating
  ;; a member arriving over content already stored separates the pair; a member leaving,
  ;; with the mark still standing, separates it no longer
  (is (empty? (directed-stream
               [[:assert '(disjoint_metatype clsh_kind_t) 'CxClashBase {:strength :monotonic}]
                [:assert '(clsh_kind_t clsh_a_t) 'CxClashBase {:strength :monotonic}]
                [:assert '(clsh_a_t CI0) 'CxClashBase {}]
                [:assert '(clsh_b_t CI0) 'CxClashBase {}]
                [:assert '(clsh_kind_t clsh_b_t) 'CxClashBase {:strength :monotonic}]
                [:assert '(plant CI4) 'CxClashBase {}]
                [:retract '(clsh_kind_t clsh_b_t) 'CxClashBase]
                [:assert '(plant CI5) 'CxClashBase {}]]))
      "with the member gone the two types are separated by nothing"))

(deftest the-contradictions-list-is-ordered-by-content-not-arrival
  ;; three independent dilemmas in three assertion orders; the nogoods are handle-keyed
  (let [pairs  '[[(clsh_p CA) (not (clsh_p CA))]
                 [(clsh_q CB) (not (clsh_q CB))]
                 [(clsh_r CC) (not (clsh_r CC))]]
        read!  (fn [sentences]
                 (let [kb (tu/fresh)]
                   (try
                     (doseq [s sentences] (v/assert kb s 'CxClashBase))
                     (mapv (fn [r] (mapv :sentence (:sides r))) (v/contradictions kb))
                     (finally (tu/clear-kb! kb)))))
        fwd    (read! (apply concat pairs))
        rev    (read! (apply concat (reverse pairs)))
        rot    (read! (apply concat (take 3 (drop 1 (cycle pairs)))))]
    (is (= 3 (count fwd)) "three standing dilemmas")
    (is (= fwd rev rot) "every assertion order publishes one list")
    (is (= fwd (vec (sort-by pr-str fwd))) "and it is the content order, stated directly")))

(deftest a-sides-derivations-are-ordered-by-content-not-arrival
  ;; the derivations inside a side come off `jtms/supports`, a set of allocation-ordered
  ;; ids.  The two arms share one term set, since the readings are compared as values.
  (tu/with-terms [seenA seenB derivedQ Subject CxBase]
    (let [ops   {:fA  #(v/assert % (list seenA Subject) CxBase)
                 :fB  #(v/assert % (list seenB Subject) CxBase)
                 :r1  #(v/assert-rule % [(list seenA '?x)] (list derivedQ '?x) CxBase {:direction :forward})
                 :r2  #(v/assert-rule % [(list seenB '?x)] (list derivedQ '?x) CxBase {:direction :forward})
                 :neg #(v/assert % (list 'not (list derivedQ Subject)) CxBase)}
          sent  (fn [kb x] (if (integer? x) (v/sentence-of (v/sentex kb x)) x))
          read! (fn [order]
                  (let [kb (tu/fresh)]
                    (try
                      (doseq [o order] ((ops o) kb))
                      (mapv (fn [report]
                              (mapv (fn [side]
                                      [(:sentence side)
                                       (mapv (fn [j] [(sent kb (:informant j))
                                                      (mapv #(sent kb %) (:antecedents j))])
                                             (:justifications side))])
                                    (:sides report)))
                            (v/contradictions kb))
                      (finally (tu/clear-kb! kb)))))
          fwd   (read! [:r1 :r2 :fA :fB :neg])
          rev   (read! [:neg :fB :fA :r2 :r1])]
      (is (= 1 (count fwd)) "one standing dilemma")
      (is (some (fn [[_ js]] (= 2 (count js))) (first fwd))
          "and one side of it is derived twice — else there is no list to order")
      (is (= fwd rev) "every assertion order publishes one reading"))))
