;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.genlcx-move-oracle-test
  "The `genlCx` move oracle: a KB built by a random order of writes and retractions holds
  what a fresh KB loaded with the final premises in content order holds
  (docs/contexts.md, \"One context move\").  A world is a context DAG under CxUniverse,
  memberships, forward rules (one may conclude a `genlCx` edge), `genlCx` edges, an
  except of an edge, an except of a fact stated in another context, and an except of an
  except.  The judge compares, per context of the world: `ask?` over every membership of
  the world's types and individuals, the stored sentences, and each stored sentex's
  justification antecedents the network does not hold blocked, every handle read by
  content.  A blocked justification and a firing refused at its placement read alike.  The `genlCx` edges a firing names as its witness path are left out of its
  antecedents: a firing names one path, the first it found (docs/nmtms.md), so two
  orders can name two paths that both stand.  A stored firing the
  KB keeps below a placement the other KB holds is history (docs/nmtms.md, \"Where the
  layer stops\"), in either KB, and is not a disagreement.  A red world is shrunk to the
  fewest operations that keep it red."
  (:require [clojure.string :as str]
            [clojure.test :refer [is]]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.special :as special]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.ref.gen :as gen]
            [vaelii.test-util :as tu])
  (:import [java.util Random]))

;; ---- the world ---------------------------------------------------------

(defn- chance [^Random rng p] (< (.nextDouble rng) p))

(defn- depth [writes i]
  (if-let [t (:except (nth writes i))] (inc (depth writes t)) 0))

(defn gen-world
  "A world for `seed`: `{:writes [{:id i :sentence S :context C} | {:id i :except j
  :context C}] :ops [[:assert i] [:retract i] …] :contexts [C …] :types :individuals}`.
  Every write is `:monotonic`.  An except names the write it excepts by id, and a write
  some except names is never retracted."
  [seed]
  (let [rng   (Random. (long seed))
        cxs   (vec (for [c ["A" "B" "C" "D"]] (tu/fresh-term :context (str "Cx" c))))
        tys   (vec (for [t ["ta" "tb" "tc"]] (tu/fresh-term :type t)))
        inds  (vec (for [i ["IndA" "IndB"]] (tu/fresh-term :individual i)))
        ;; each context under CxUniverse or an earlier context, and two edges more
        dag   (vec (for [i (range (count cxs))]
                     [(nth cxs i) (if (or (zero? i) (chance rng 0.4)) 'CxUniverse (nth cxs (.nextInt rng i)))]))
        extra (vec (for [_ (range 2)
                         :let [i (inc (.nextInt rng (dec (count cxs))))]]
                     [(nth cxs i) (nth cxs (.nextInt rng i))]))
        edges (into [] (distinct) (concat dag extra))
        facts (vec (distinct (for [_ (range (+ 2 (.nextInt rng 3)))]
                               [(list (tu/pick rng tys) (tu/pick rng inds)) (tu/pick rng cxs)])))
        rules (vec (concat
                    (for [_ (range (inc (.nextInt rng 2)))
                          :let [[a b c] (tu/shuffled rng tys)]]
                      [(if (chance rng 0.5)
                         (list 'implies (list a '?x) (list b '?x))
                         (let [[a b] (sort-by str [a b])]
                           (list 'implies (list 'and (list a '?x) (list b '?x)) (list c '?x))))
                       (tu/pick rng cxs)])
                    ;; the edges point to earlier contexts, so y after x keeps the DAG
                    (when (chance rng 0.4)
                      (let [[x y] (sort-by #(.indexOf ^java.util.List cxs %) (take 2 (tu/shuffled rng cxs)))]
                        [[(list 'implies (list 'genlCx x '?b) (list 'genlCx y '?b)) 'CxUniverse]]))))
        plain (into [] (distinct) (concat (map (fn [[s b]] [(list 'genlCx s b) 'CxUniverse]) edges) facts rules))
        base  (vec (map-indexed (fn [i [s c]] {:id i :sentence s :context c}) plain))
        n     (count base)
        edge-ids (vec (keep #(when (= 'genlCx (first (:sentence %))) (:id %)) base))
        fact-ids (vec (keep #(when (contains? (set tys) (first (:sentence %))) (:id %)) base))
        ex1   (when (chance rng 0.8) {:id n :except (tu/pick rng edge-ids) :context (tu/pick rng cxs)})
        ex2   (when (chance rng 0.6) {:id (count (cond-> base ex1 (conj ex1)))
                                      :except (tu/pick rng fact-ids) :context (tu/pick rng cxs)})
        ex3   (when (and ex1 (chance rng 0.4)) {:id (count (cond-> base ex1 (conj ex1) ex2 (conj ex2)))
                                                :except (:id ex1) :context (tu/pick rng cxs)})
        writes (into base (remove nil?) [ex1 ex2 ex3])
        named (into #{} (keep :except) writes)
        ;; an except is moved to just after its target until none precedes it
        order (loop [o (tu/shuffled rng (mapv :id writes))]
                (let [pos  #(.indexOf ^java.util.List o %)
                      late (first (filter #(when-let [t (:except (nth writes %))] (< (pos %) (pos t))) o))]
                  (if-not late
                    o
                    (let [t  (:except (nth writes late))
                          o' (into [] (remove #{late}) o)
                          at (inc (.indexOf ^java.util.List o' t))]
                      (recur (into (conj (subvec o' 0 at) late) (subvec o' at)))))))
        retracts (vec (for [i (remove named order)
                            :when (chance rng 0.25)]
                        i))
        ops   (reduce (fn [ops r]
                        (let [at  (inc (.indexOf ^java.util.List ops [:assert r]))
                              pos (+ at (.nextInt rng (inc (- (count ops) at))))]
                          (into (conj (subvec ops 0 pos) [:retract r]) (subvec ops pos))))
                      (mapv #(vector :assert %) order)
                      retracts)]
    {:writes writes :ops ops :contexts cxs :types tys :individuals inds}))

;; ---- loading -----------------------------------------------------------

(defonce ^:private space-counter (atom 0))

(def ^:private ^:dynamic *deferred?*
  "True while `run-ops!` applies its ops as one `with-deferred-settle` batch, where a
  retraction settles eagerly and every assert settles at the batch's close."
  false)

(defn- run-ops!
  "A fresh KB on a space of its own with `genlCx` forced monotonic, `ops` applied, in one
  deferred batch under `*deferred?*`.  Returns `{:kb :space :handles {id handle}}`."
  [world ops]
  (let [space [::oracle (swap! space-counter inc)]
        kb    (v/open-kb {:backend :memory :space space :recover? false})
        hs    (volatile! {})
        apply! (fn []
                 (doseq [[op i] ops
                         :let [w (nth (:writes world) i)]]
                   (case op
                     :assert  (when-let [s (if-let [t (:except w)]
                                             (when-let [h (get @hs t)] (list 'except (v/sentex-handle h)))
                                             (gen/forward (:sentence w)))]
                                (vswap! hs assoc i (v/assert kb s (:context w) {:strength :monotonic})))
                     :retract (when-let [h (get @hs i)]
                                (when (v/sentex kb h) (v/retract! kb h))
                                (vswap! hs dissoc i)))))]
    (v/assert kb '(forced_monotonic_predicate genlCx) 'CxRefForced)
    (if *deferred?* (v/with-deferred-settle kb (apply!)) (apply!))
    {:kb kb :space space :handles @hs}))

(defn- close! [{:keys [kb space]}]
  (try (v/close! kb)
       (finally (mem/drop-record-space! space) (mem/drop-index-space! space))))

(defn- final-ops
  "The final premises of `ops` in content order: the writes asserted and not retracted,
  the excepts after the writes they name."
  [world ops]
  (let [live (reduce (fn [s [op i]] (if (= op :assert) (conj s i) (disj s i))) #{} ops)
        key  (fn [i] (let [w (nth (:writes world) i)]
                       [(depth (:writes world) i) (pr-str (or (:sentence w) (:except w))) (str (:context w))]))]
    (mapv #(vector :assert %) (sort-by key live))))

;; ---- reading -----------------------------------------------------------

(defn- render
  "`form` with every `(sentexHandle h)` replaced by the content of the sentex it names."
  [kb form]
  (cond
    (and (seq? form) (= 'sentexHandle (first form)))
    (let [sx (v/sentex kb (second form))]
      [:h (when sx (render kb (v/sentence-of sx))) (:context sx)])
    (seq? form) (apply list (map #(render kb %) form))
    :else form))

(defn- reading
  "Per context of `world`: `{C {:asked #{S} :stored #{S} :justs {S #{#{antecedent}}}}}`,
  over the justifications whose verdict at C neither blocks, guards, voids nor exempts
  (`v/justification-verdicts`), a `genlCx` antecedent left out."
  [world kb]
  (let [tms     (reasoning/tms kb)
        recs    (:records kb)
        invalid #{:blocked :guard :void :exempt}
        key     (fn [h] (when-let [sx (p/get-sentex recs h)]
                          (let [s (v/sentence-of sx)]
                            (when-not (and (seq? s) (= 'genlCx (first s)))
                              [(render kb s) (:context sx)]))))]
    (into {}
          (for [c (:contexts world)
                :let [sxs (vec (v/sentexes-in-context kb c))]]
            [c {:asked  (into #{} (for [t (:types world) i (:individuals world)
                                        :let [s (list t i)]
                                        :when (v/ask? kb s c)]
                                    s))
                :stored (into #{} (map #(render kb (v/sentence-of %))) sxs)
                :justs  (into {} (for [sx sxs
                                       :let [vs (v/justification-verdicts kb (:id sx) c)]]
                                   [(render kb (v/sentence-of sx))
                                    (into #{} (keep (fn [jid]
                                                      (when-let [j (when-not (invalid (get vs jid))
                                                                     (jtms/justification tms jid))]
                                                        (into #{} (keep key) (:antecedents j)))))
                                          (jtms/supports tms (:id sx)))]))}]))))

(defn- disagreements
  "Where the incremental reading `inc` and the fresh one `fresh` disagree, as a vector of
  `[context kind detail]`.  A sentence one KB stores at C that the other stores in a
  context C sees is history and not counted, nor is a justification of a sentence the
  other KB stores there."
  [world kb-inc inc fresh]
  (vec (for [c (:contexts world)
             :let [i (get inc c) f (get fresh c)
                   history? (fn [other s] (some (fn [c'] (and (not= c c') (contains? (:stored (get other c')) s)
                                                              (v/sees? kb-inc c c')))
                                                (:contexts world)))
                   ;; a justification resting on a copy the same KB holds above it is history too
                   copy?   (fn [rd j] (some (fn [[s c1]] (some (fn [c2] (and (not= c1 c2) (contains? (:stored (get rd c2)) s)
                                                                             (v/sees? kb-inc c1 c2)))
                                                               (:contexts world)))
                                            j))
                   live    (fn [rd js] (into #{} (remove #(copy? rd %)) js))
                   extra   (into #{} (remove #(or (contains? (:stored f) %) (history? fresh %))) (:stored i))
                   missing (into #{} (remove #(or (contains? (:stored i) %) (history? inc %))) (:stored f))
                   justs   (into {} (for [s (:stored f)
                                          :when (contains? (:stored i) s)
                                          :let [a (live inc (get-in i [:justs s])) b (live fresh (get-in f [:justs s]))]
                                          :when (not (and (or (every? b a) (history? fresh s))
                                                          (or (every? a b) (history? inc s))))]
                                      [s [a b]]))]
             [kind detail] [[:asked (when (not= (:asked i) (:asked f)) [(:asked i) (:asked f)])]
                            [:stored-extra (not-empty extra)]
                            [:stored-missing (not-empty missing)]
                            [:justifications (not-empty justs)]]
             :when detail]
         [c kind detail])))

(defn- verdict-rows
  "`[context :verdicts [handle kind]]` per row where the verdicts `kb` reads disagree with
  its belief over the sentexes of `world`'s contexts (`tu/verdict-violations`)."
  [world kb]
  (let [cs (:contexts world)]
    (mapv (fn [[h c kind]] [c :verdicts [h kind]])
          (tu/verdict-violations
           kb (into [] (comp (mapcat #(v/sentexes-in-context kb %)) (map :id)) cs) cs))))

(defn judge
  "The disagreements of `world` run by `ops` against its final premises in content
  order, and the rows where the run's verdicts disagree with its belief."
  [world ops]
  (let [a (run-ops! world ops)
        b (binding [*deferred?* false] (run-ops! world (final-ops world ops)))]
    (try (into (disagreements world (:kb a) (reading world (:kb a)) (reading world (:kb b)))
               (verdict-rows world (:kb a)))
         (finally (close! a) (close! b)))))

(defn shrink
  "`ops` with operations dropped one at a time while `world` stays red under `judge`."
  [world ops]
  (loop [ops ops, i 0]
    (if (>= i (count ops))
      ops
      (let [op  (nth ops i)
            ;; dropping an assert drops its retraction, and its excepts' ops
            gone (if (= :assert (first op))
                   (let [dead (loop [d #{(second op)}]
                                (let [d' (into d (keep #(when (contains? d (:except %)) (:id %))) (:writes world))]
                                  (if (= d d') d (recur d'))))]
                     #(contains? dead (second %)))
                   #(= % op))
            fewer (into [] (remove gone) ops)]
        (if (and (< (count fewer) (count ops)) (seq (judge world fewer)))
          (recur fewer 0)
          (recur ops (inc i)))))))

(defn- describe [world ops]
  (str/join "\n" (for [[op i] ops :let [w (nth (:writes world) i)]]
                   (str op " " (or (:sentence w) (str "except of #" (:except w))) " in " (:context w) " #" i))))

(defn check-seeds
  "Judge the worlds of `seeds`; a red world is shrunk and reported."
  [seeds]
  (doseq [seed seeds
          :let [world (gen-world seed)
                d     (judge world (:ops world))]]
    (when (seq d)
      (let [ops (shrink world (:ops world))]
        (is (empty? d) (str "seed " seed ", shrunk to:\n" (describe world ops) "\n"
                            (pr-str (judge world ops))))))))

(tu/deftest-kb a-genlCx-move-leaves-the-state-a-fresh-build-holds
  ;; Sampled twin of the ^:slow sweep below.
  (check-seeds (range 0 40)))

(tu/deftest-kb ^:slow a-genlCx-move-leaves-the-state-a-fresh-build-holds-over-many-worlds
  (check-seeds (range 40 600)))

(tu/deftest-kb a-deferred-batch-of-genlCx-moves-leaves-the-state-a-fresh-build-holds
  (binding [*deferred?* true] (check-seeds (range 0 40))))

(tu/deftest-kb an-edge-in-a-deferred-batch-draws-the-same-whatever-the-order-of-the-three
  ;; The drain reads only what was stored before the edge arrived (`special/seed-floor`):
  ;; a fact, a rule or a declaration stored after it was chained, joined or drawn with the
  ;; edge in place.  Each row is a rule or an `arg` declaration in the lower context, a
  ;; fact in the upper one, and the edge, in every order.
  ;; Forced to the entailing reading: the constraint-only reading draws no `(dfo_kind DfoAnn)`.
  (tu/with-entailing
    (doseq [[upper opts conclusion] [['(implies (dfo_low ?x) (dfo_high ?x)) {:direction :forward}
                                      '(dfo_high DfoAnn)]
                                     ['(arg dfoLink 1 dfo_kind) {:strength :monotonic}
                                      '(dfo_kind DfoAnn)]]
            order (for [a [:upper :fact :edge] b [:upper :fact :edge] c [:upper :fact :edge]
                        :when (= 3 (count (hash-set a b c)))]
                    [a b c])]
      (let [space [::oracle (swap! space-counter inc)]
            kb    (v/open-kb {:backend :memory :space space :recover? false})]
        (try
          (v/with-deferred-settle kb
            (v/assert kb '(genl dfo_kind thing) 'CxDfoLow {:strength :monotonic})
            (doseq [w order]
              (case w
                :upper (v/assert kb upper 'CxDfoLow opts)
                :fact  (do (v/assert kb '(dfo_low DfoAnn) 'CxDfoMid)
                           (v/assert kb '(dfoLink DfoAnn DfoBo) 'CxDfoMid))
                :edge  (v/assert kb '(genlCx CxDfoLow CxDfoMid) 'CxUniverse))))
          (is (seq (v/sentexes-matching kb conclusion 'CxDfoLow)) (pr-str upper order))
          (finally (close! {:kb kb :space space})))))))

;; ---- the read bound ----------------------------------------------------

(defn- named-by
  "The contexts of the `genlCx` facts stating the edges of the moves `ms`, and of their
  consequence closure."
  [kb ms]
  (let [recs (:records kb)
        hs   (mapcat (fn [{[a b] :edge}] (reads/as-stored-with-args (:index kb) 'genlCx [[1 a] [2 b]])) ms)]
    (into #{} (keep #(:context (p/get-sentex recs %)))
          (jtms/consequence-closure (reasoning/tms kb) hs))))

(defn- drained-reads
  "`ops` of `world` run with every drain of `genlCx` moves (`special/drain-context-moves!`)
  tallied, one `{:read #{context} :named #{context}}` per drain that computed a move:
  `:read` the contexts the drain read by context (`reads/*contexts-read*`), the
  computation of each move left out, and `:named` the contexts the moves name
  (`context-move`'s `:raw`, `:moved`, `:readers`, `:under`, `:below` and `:up`, each
  edge's ends, and `named-by`).  `:up` is in the bound because a firing seed joins a fact
  the edge shows with the other antecedents its reader already sees there."
  [world ops]
  (let [drains (volatile! [])
        moves  (volatile! nil)
        drain  @#'special/drain-context-moves!
        cmove  @#'special/context-move*]
    (with-redefs [special/drain-context-moves!
                  (fn [kb read rebuilding?]
                    (let [t (volatile! #{})]
                      (vreset! moves [])
                      (let [r (binding [reads/*contexts-read* t] (drain kb read rebuilding?))]
                        (when (seq @moves)
                          (vswap! drains conj
                                  {:read  @t
                                   :named (into (named-by kb @moves)
                                                (mapcat #(concat (:raw %) (:moved %) (:readers %) (:up %)
                                                                 @(:under %) @(:below %) (:edge %)))
                                                @moves)}))
                        (vreset! moves nil)
                        r)))
                  special/context-move*
                  (fn [kb ctxs sub super off]
                    ;; the move's own walk reads `sub`'s ancestor set without the edge,
                    ;; which the bound is not about
                    (let [m (binding [reads/*contexts-read* nil] (cmove kb ctxs sub super off))]
                      (when @moves (vswap! moves conj m))
                      m))]
      (close! (run-ops! world ops)))
    @drains))

(tu/deftest-kb a-drain-of-genlCx-moves-reads-only-the-contexts-its-moves-name
  (let [runs (mapv #(let [world (gen-world %)] [% (drained-reads world (:ops world))]) (range 0 40))]
    ;; the tally reads something, so an empty excess is not an empty tally
    (is (some (comp seq :read) (mapcat second runs)))
    (doseq [[seed ds] runs]
      (is (empty? (into [] (keep #(not-empty (remove (:named %) (:read %)))) ds)) (str "seed " seed)))))
