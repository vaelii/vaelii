;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.arity-inert-test
  "A relation's length against one definition, and what the KB does with it.

  The readers of a relation's length (`arity/relation-length`, `kb/relation-arity`) are
  held to a definition read off the believed bindings.  A stored tuple whose argument
  count breaks its functor's length is in the `:out` forced set, and each two exact
  bindings stored in CxUniverse whose lengths differ, of one predicate or of two along a
  `genl` edge, are one placed `contradicts` in CxUniverse (docs/taxonomy.md, \"Arity\").
  The oracle reads the stored records and one closure per functor, and the KB must match
  it after every write, after a recover and after retractions."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.decide.arity :as arity]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.predicates :as predicates]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.order-independence-test :as oi]
            [vaelii.test-util :as tu]))

;; ---- a metatype membership binds a length ----------------------------------------
;;
;; `(kindRel likesRel)` and `(genl kindRel binary_predicate)`, each `:monotonic`, bind
;; likesRel to two arguments, so a ternary likesRel fact is inert.

(defn- metatype-reading
  "Assert the ops of `order` in CxUniverse, the edge and the membership at the strengths
  `strengths` names, and answer whether the ternary tuple is believed there, read in the
  KB and in a KB recovered from its dump records-only, before and after a write."
  [kb order strengths]
  (tu/with-terms [kindRel likesRel A B C D]
    (let [ss {:edge   (list 'genl kindRel 'binary_predicate)
              :member (list kindRel likesRel)
              :tuple  (list likesRel A B C)}
          hs (mapv #(v/assert kb (ss %) 'CxUniverse {:strength (get strengths % :default)}) order)
          rs (tu/recovered-readings kb false [(ss :tuple) 'CxUniverse]
                                    #(v/assert % (list likesRel A D) 'CxUniverse))]
      (doseq [h (rseq hs)] (v/retract! kb h))
      (mapv :loser rs))))

(deftest a-monotonic-metatype-membership-binds-the-length-of-its-exact-class
  (tu/with-neutral-kb [kb tu/fresh]
    (let [mono {:edge :monotonic :member :monotonic}]
      (is (= #{[false false false]}
             (into #{} (map #(metatype-reading kb % mono)) (oi/permutations [:edge :member :tuple])))
          "in all six orders, before and after recover")
      (is (= [true true true] (metatype-reading kb [:edge :member :tuple] (assoc mono :edge :default)))
          "a :default edge binds nothing")
      (is (= [true true true] (metatype-reading kb [:edge :member :tuple] (assoc mono :member :default)))
          "a :default membership binds nothing"))))

(deftest a-class-membership-derived-in-one-context-binds-the-length-at-every-context
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [kindRel likesRel A B C CxMa CxMb CxMc]
      (let [m  {:strength :monotonic}
            hs [(v/assert kb (list 'genlCx CxMa 'CxUniverse) 'CxUniverse)
                (v/assert kb (list 'genlCx CxMb 'CxUniverse) 'CxUniverse)
                (v/assert kb (list 'genlCx CxMc CxMa) 'CxUniverse)
                (v/assert kb (list 'genlCx CxMc CxMb) 'CxUniverse)
                (v/assert kb (list 'genl kindRel 'binary_predicate) CxMb m)
                (v/assert kb (list kindRel likesRel) CxMa m)]
            t  (v/assert kb (list likesRel A B C) CxMa)]
        ;; CxMc sees the membership and the edge, and CxMa sees no edge
        (is (= [false false] [(v/believed? kb t CxMa) (v/believed? kb t CxMc)]))
        (doseq [h (cons t (rseq hs))] (v/retract! kb h))))))

(deftest a-re-assert-raising-a-membership-or-edge-to-monotonic-binds-the-length
  (tu/with-neutral-kb [kb tu/fresh]
    (doseq [raised [:edge :member]]
      (tu/with-terms [kindRel likesRel A B C]
        (let [ss {:edge (list 'genl kindRel 'binary_predicate) :member (list kindRel likesRel)}
              m  {:strength :monotonic}
              hs [(v/assert kb (ss :edge) 'CxUniverse (if (= raised :edge) {} m))
                  (v/assert kb (ss :member) 'CxUniverse (if (= raised :member) {} m))]
              t  (v/assert kb (list likesRel A B C) 'CxUniverse)
              before (v/believed? kb t 'CxUniverse)]
          (v/assert kb (ss raised) 'CxUniverse m)
          (is (= [true false] [before (v/believed? kb t 'CxUniverse)]) (name raised))
          (doseq [h (cons t (rseq hs))] (v/retract! kb h)))))))

;; ---- the readers of a relation's length against one definition -----------------------
;;
;; One function answers "what length binds P": `arity/relation-length`, which the
;; argument-position check, the inert-tuple test, `admitsArgnum` and `kb/relation-arity` (its
;; `:exact`) read.  The definition below reads only
;; what is stored and believed and takes no context: a relation has one binding, read the
;; same at every context.  Its own binding is its `arity` declarations, its exact-class
;; memberships and each `:monotonic` metatype membership whose metatype reaches an exact
;; class through `:monotonic` `genl` edges.  `variable_arity` leaves one `arityMin` floor
;; and no exact length, two own lengths leave the relation unbound, and a relation with no
;; own binding takes the one exact length the predicates above it agree on, none of them
;; `variable_arity`.  An engine term's length is the argument count of its `:shape`.
;;
;; `kb/relation-arity` claims the whole's exact length and `relation-length` the whole, and
;; a disagreement of either fails the test.  A `covering` installs a `genl` edge per part.

(def ^:private exact-class-names (vec (sort (keys sx/exact-arity-classes))))

(defn- length-world
  "A vector of ops over six predicates `p0`..`p5`, two metatypes `k0` `k1` and `ncx`
  contexts: `genl` edges, `arity`, exact-class, `arityMin` and `variable_arity`
  declarations, a metatype membership `(K P)` and a metatype edge `(genl K C)`, each at a
  context index and a strength."
  [^java.util.Random rnd ncx]
  (let [r  #(.nextInt rnd (int %))
        at (fn [m] (assoc m :cx (r ncx) :st (if (zero? (r 4)) :monotonic :default)))
        p  #(r 6)]
    (into []
          (concat
           (for [_ (range (+ 2 (r 6))) :let [i (p) j (p)] :when (not= i j)]
             (at {:op :edge :sub i :sup j}))
           (for [_ (range (+ 1 (r 5)))]
             (at (case (int (r 5))
                   (0 1) {:op :arity :p (p) :n (inc (r 3))}
                   2     {:op :class :p (p) :c (exact-class-names (r 9))}
                   3     {:op :var :p (p)}
                   4     {:op :member :k (r 2) :p (p)})))
           (for [k (range 2) :when (< (r 3) 2)]
             (at {:op :route :k k :c (exact-class-names (r 9))}))
           (for [_ (range (r 2))] (at {:op :min :p (p) :n (inc (r 3))}))))))

(defn- length-sentence [{:keys [ps ks]} op]
  (case (:op op)
    :edge   (list 'genl (ps (:sub op)) (ps (:sup op)))
    :arity  (list 'arity (ps (:p op)) (:n op))
    :class  (list (:c op) (ps (:p op)))
    :min    (list 'arityMin (ps (:p op)) (:n op))
    :var    (list 'variable_arity (ps (:p op)))
    :member (list (ks (:k op)) (ps (:p op)))
    :route  (list 'genl (ks (:k op)) (:c op))
    :engine (list (ks (:k op)) (:t op))))

(defn- length-build!
  "Assert `world` into `kb` in order, over fresh terms, and answer `{:ps :ks :ctx :hs}`,
  `hs` mapping each op the KB stored to its handle."
  [kb world]
  (let [ps  (vec (repeatedly 6 #(tu/fresh-term :predicate 'rel)))
        ks  (vec (repeatedly 2 #(tu/fresh-term :predicate 'kindrel)))
        cxs (vec (repeatedly 3 #(tu/fresh-term :context 'Cx)))
        ctx (into ['CxUniverse] cxs)
        env {:ps ps :ks ks :ctx ctx}]
    (v/assert kb (list 'genlCx (cxs 0) 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx (cxs 1) (cxs 0)) 'CxUniverse)
    (v/assert kb (list 'genlCx (cxs 2) 'CxUniverse) 'CxUniverse)
    (assoc env :hs
           (into {}
                 (keep (fn [op]
                         (when-let [h (try (v/assert kb (length-sentence env op) (ctx (:cx op))
                                                     {:strength (:st op)})
                                           (catch clojure.lang.ExceptionInfo _))]
                           [op h])))
                 world))))

(defn- believed-with-functor [kb f] (v/sentexes-with-functor kb f {:believed? true}))

(defn- genl-edges
  "`{sub #{super}}` over the believed `genl` and `covering` sentexes in any context,
  `:monotonic` ones only when `mono?`."
  [kb mono?]
  (let [ok? #(or (not mono?) (= :monotonic (:strength %)))]
    (as-> {} m
      (reduce (fn [m s] (let [[_ a b] (:sentence s)] (cond-> m (ok? s) (update a (fnil conj #{}) b))))
              m (believed-with-functor kb 'genl))
      (reduce (fn [m s] (let [[_ whole & parts] (:sentence s)]
                          (cond-> m (ok? s) (#(reduce (fn [m p] (update m p (fnil conj #{}) whole)) % parts)))))
              m (believed-with-functor kb 'covering)))))

(defn- reachable-from [edges t]
  (let [walk (fn walk [seen u] (reduce (fn [s w] (if (s w) s (walk (conj s w) w))) seen (get edges u)))]
    (disj (walk #{} t) t)))

(defn- own-bindings
  "`{:exact #{n} :min #{m} :var? bool}` of `q`, as the definition reads it.  A believed
  metatype membership binds when it is `:monotonic`, or at any strength with `any-route?`,
  and its metatype reaches an exact class over `genl` edges of the same strengths."
  [kb q ks any-route?]
  (let [route? #(or any-route? (= :monotonic (:strength %)))
        edges  (genl-edges kb (not any-route?))
        about  (fn [f] (keep #(let [[_ p x] (:sentence %)] (when (= p q) x)) (believed-with-functor kb f)))
        unary? (fn [f] (some #(= (list f q) (:sentence %)) (believed-with-functor kb f)))]
    {:exact (into (into #{} (filter #(and (integer? %) (pos? %))) (about 'arity))
                  (concat (for [[c n] sx/exact-arity-classes :when (unary? c)] n)
                          (for [k ks
                                :when (some #(and (route? %) (= (list k q) (:sentence %)))
                                            (believed-with-functor kb k))
                                c (conj (reachable-from edges k) k)
                                :let [n (sx/exact-arity-classes c)] :when n]
                            n)))
     :min   (into #{} (about 'arityMin))
     :var?  (boolean (some unary? sx/variable-arity-classes))}))

(defn- own-length
  "What own bindings `b` bind: `{:exact n}`, or `{:min m}` under `variable_arity`, else nil."
  [b]
  (cond
    (:var? b)        (when (= 1 (count (:min b))) {:min (first (:min b))})
    (seq (:exact b)) (when (= 1 (count (:exact b))) {:exact (first (:exact b))})))

(defn- engine-length [q] (some-> (predicates/shape-of q) :args count))

(defn- defined-length
  "The definition's answer for `q`, `{:exact n}`, `{:min m}` or nil.  With `any-route?`,
  the same definition counting a metatype route at any strength."
  ([kb q ks] (defined-length kb q ks false))
  ([kb q ks any-route?]
   (if-let [n (engine-length q)]
     {:exact n}
     (let [b (own-bindings kb q ks any-route?)]
       (if (or (:var? b) (seq (:exact b)))
         (own-length b)
         (let [bs    (filter #(or (:var? %) (seq (:exact %)))
                             (map #(own-bindings kb % ks any-route?)
                                  (reachable-from (genl-edges kb false) q)))
               exact (into #{} (mapcat :exact) bs)]
           (when (and (= 1 (count exact)) (not-any? :var? bs))
             {:exact (first exact)})))))))

(defn- length-readers
  "What each reader answers for `q`: `kb/relation-arity` an exact length or nil,
  `relation-length` `{:exact n}` or `{:min m}` or nil."
  [kb q]
  {:kb-relation-arity (kb/relation-arity kb q)
   :relation-length   (not-empty (select-keys (arity/relation-length kb q) [:exact :min]))})

(defn- length-disagreements
  "Every disagreement between a reader and the definition over the predicates of `env`
  and `extra`.  No reader takes a context, so one reading per predicate answers every
  context."
  [kb {:keys [ps ks]} extra]
  (for [[qi q] (concat (map-indexed vector ps) (map (fn [t] [t t]) extra))
        :let   [whole (defined-length kb q ks)
                r     (length-readers kb q)]
        [k want] [[:kb-relation-arity (:exact whole)] [:relation-length whole]]
        :when  (not= want (r k))]
    {:reader k :qi qi :want want :got (r k)}))

(defn- length-run
  "Build `world` in a fresh KB and answer `{:ds the disagreements :answers every reader's
  answer :stored the ops stored}`, then `:after` the disagreements once a third of the
  stored ops are retracted."
  [^java.util.Random rnd world extra]
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [b  (length-build! kb world)
          ds (vec (length-disagreements kb b extra))
          an (into {} (for [[qi q] (map-indexed vector (:ps b))
                            [k a] (length-readers kb q)]
                        [[k qi] a]))]
      (doseq [[_ h] (sort-by (fn [_] (.nextInt rnd)) (:hs b)) :when (zero? (.nextInt rnd 3))]
        (v/retract! kb h))
      {:ds ds :answers an :stored (set (keys (:hs b)))
       :after (vec (length-disagreements kb b extra))})))

(defn- length-sweep
  "Run `n` seeded worlds over `ncx` contexts in `orders` shuffled arrival orders each,
  and answer the disagreements, the answers that differ between two orders storing the
  same ops, and the disagreements after retractions."
  [seed ncx n orders]
  (let [rnd (java.util.Random. seed)
        out (atom {:ds [] :order [] :after []})]
    (dotimes [_ n]
      (let [world (length-world rnd ncx)
            runs  (vec (for [_ (range orders)] (length-run rnd (vec (shuffle world)) nil)))]
        (doseq [{:keys [ds after]} runs]
          (swap! out update :ds into (map #(hash-map :world world :d %)) ds)
          (swap! out update :after into (map #(hash-map :world world :d %)) after))
        (doseq [[a b] (partition 2 1 runs)
                :when (and (= (:stored a) (:stored b)) (not= (:answers a) (:answers b)))]
          (swap! out update :order conj world))))
    @out))

(deftest the-readers-of-a-relation-s-length-agree-with-its-definition
  (doseq [[ncx n] [[1 4] [4 3]]]
    (let [{:keys [ds order after]} (length-sweep (+ 6101 ncx) ncx n 2)]
      (is (= [] ds) (str ncx " contexts"))
      (is (= [] order) (str ncx " contexts: an answer that depends on arrival order"))
      (is (= [] after) (str ncx " contexts: after retractions")))))

(deftest ^:slow the-readers-of-a-relation-s-length-agree-with-its-definition-over-many-worlds
  (doseq [[seed ncx] [[6201 1] [6202 4]]]
    (let [{:keys [ds order after]} (length-sweep seed ncx 60 3)]
      (is (= [] (take 3 ds)) (str ncx " contexts"))
      (is (= [] (take 3 order)) (str ncx " contexts"))
      (is (= [] (take 3 after)) (str ncx " contexts")))))

(deftest an-engine-term-s-length-is-its-shape-whatever-the-kb-binds
  ;; `assert` refuses `(arity genl 3)` (`:length-against-shape`), so the binding arrives
  ;; as `(ternary_predicate genl)` the settle stores off a `:monotonic` metatype route
  (doseq [world [[{:op :engine :t 'genl :k 0 :cx 0 :st :monotonic}
                  {:op :route :k 0 :c 'ternary_predicate :cx 0 :st :monotonic}]
                 []]]
    (let [{:keys [ds stored]} (length-run (java.util.Random. 1) world '[genl arity])]
      (is (= [] ds))
      (is (= (set world) stored) "every op is stored"))))

;; ---- the inert tuples and the pairs against their definition ----------------------

(defn- breaks?
  "Does a tuple of `n` arguments break the length `l` (`defined-length`)?"
  [l n]
  (boolean (or (some-> (:exact l) (not= n)) (some-> (:min l) (> n)))))

(defn- stored-tuples
  "`{h [f n]}` of every stored fact of `n` arguments whose functor `f` has no engine shape."
  [kb]
  (let [recs  (:records kb)
        shape sx/fact-shape]
    (into {} (keep (fn [h] (when-let [[f :as fs] (some-> (p/get-sentex recs h) shape)]
                             (when-not (predicates/shape-of f) [h fs]))))
          (p/sentex-ids recs))))

(defn- root-exact-bindings
  "`{q {h n}}`: the exact bindings stored in CxUniverse of each predicate no stored
  `variable_arity` binding releases."
  [kb]
  (let [recs (:records kb)
        rs   (keep (fn [h] (let [r (p/get-sentex recs h)]
                             (when-let [[q kind n] (when (and r (nil? (:antecedent r))) (sx/arity-binding (:sentence r)))]
                               [h q kind n (:context r)])))
                   (p/sentex-ids recs))
        free (into #{} (keep (fn [[_ q kind]] (when (= :var kind) q))) rs)]
    (reduce (fn [m [h q kind n cx]]
              (cond-> m (and (= :exact kind) (= 'CxUniverse cx) (not (free q))) (assoc-in [q h] n)))
            {} rs)))

(defn- oracle
  "`{:out #{h} :pairs #{#{h h'}}}` by definition: the stored tuples breaking their
  functor's length (`defined-length`), and each two exact bindings in CxUniverse of
  different lengths, of one predicate or of two the closure of the lower one joins."
  [kb]
  (let [bs  (root-exact-bindings kb)
        tax (reasoning/taxonomy kb)]
    {:out   (into #{} (keep (fn [[h [f n]]] (when (breaks? (defined-length kb f []) n) h)))
                  (stored-tuples kb))
     :pairs (into #{} (for [[q hs] bs
                            g      (conj (set (tax/genls-global tax q)) q)
                            :let   [gs (get bs g)]
                            [x a] hs, [y b] gs
                            :when  (not= a b)]
                        #{x y}))}))

(defn- held
  "What `kb` holds: the stored tuples in the `:out` forced set, and the member sets of the
  justified `contradicts` that pair two arity bindings (`arity/kind-of`), each in
  CxUniverse."
  [kb]
  (let [tms (reasoning/tms kb)
        ts  (stored-tuples kb)]
    {:out   (into #{} (filter ts) (jtms/forced-members tms :out))
     :pairs (into #{} (comp (filter #(seq (jtms/supports tms (:id %))))
                            (map (fn [s] [(:context s) (into #{} (keep sx/handle-id) (rest (:sentence s)))]))
                            (filter #(arity/kind-of kb (second %)))
                            (map (fn [[cx ms]] (if (= 'CxUniverse cx) ms [cx ms]))))
                  (v/sentexes-with-functor kb 'contradicts))}))

(defn- random-stream
  "A seeded shuffle of predicate and type `genl` edges (mostly downhill, some closing a
  cycle), length bindings in every spelling, and tuples of one to three arguments."
  [^java.util.Random rnd]
  (let [pick  (fn [v] (v (.nextInt rnd (count v))))
        preds (vec (repeatedly 8 #(tu/fresh-term :predicate 'rel)))
        types (vec (repeatedly 10 #(tu/fresh-term :predicate 'kind)))
        inds  (vec (repeatedly 4 #(tu/fresh-term :individual 'Thing)))
        edge  (fn [v] (let [i (.nextInt rnd (count v))
                            j (if (< (.nextInt rnd 10) 1)
                                (.nextInt rnd (count v))
                                (+ i (.nextInt rnd (- (count v) i))))]
                        (when (not= i j) (list 'genl (v i) (v j)))))
        bind  (fn [] (let [q (pick (if (< (.nextInt rnd 4) 1) types preds))]
                       (case (int (.nextInt rnd 5))
                         0 (list 'arity q (inc (.nextInt rnd 3)))
                         1 (list 'arity q (inc (.nextInt rnd 3)))
                         2 (list 'binary_predicate q)
                         3 (list 'arityMin q (inc (.nextInt rnd 3)))
                         4 (list 'variable_arity q))))
        tuple (fn [] (let [q (pick (if (< (.nextInt rnd 2) 1) types preds))]
                       (apply list q (repeatedly (inc (.nextInt rnd 3)) #(pick inds)))))]
    (->> (concat (keep (fn [_] (edge preds)) (range 10))
                 (keep (fn [_] (edge types)) (range 14))
                 (repeatedly 8 bind)
                 (repeatedly 24 tuple))
         (sort-by (fn [_] (.nextInt rnd))))))

(defn- assert-all!
  "Assert each of `stream`, and answer the handles stored, by sentence."
  [kb stream]
  (into {}
        (keep (fn [s]
                ;; a refused sentence (a cycle a wff check turns away) is simply not stored
                (when-let [h (try (v/assert kb s 'CxUniverse) (catch clojure.lang.ExceptionInfo _))]
                  [s h])))
        stream))

(def ^:private binding-functors '#{arity arityMin binary_predicate variable_arity})

(deftest the-inert-tuples-and-pairs-match-their-definition-kept-recovered-and-after-retractions
  (let [rnd     (java.util.Random. 5772)
        seen    (atom {:out 0 :pairs 0 :pairs-dropped 0})
        handles (volatile! {})]
    (doseq [deferred? [false true], trial (range 10)]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (let [stream (random-stream rnd)
              where  (str (if deferred? "deferred" "plain") " trial " trial)]
          (vreset! handles (if deferred?
                             (v/with-deferred-settle kb (assert-all! kb stream))
                             (assert-all! kb stream)))
          (let [o (oracle kb)]
            (swap! seen #(merge-with + % {:out (count (:out o)) :pairs (count (:pairs o))})))
          (testing "kept up as facts arrive"
            (is (= (oracle kb) (held kb)) where))
          (v/recover kb)
          (testing "recovered from storage"
            (is (= (oracle kb) (held kb)) where))
          (testing "kept up as bindings leave"
            (let [before (:pairs (held kb))]
              (doseq [[s h] (sort-by (fn [_] (.nextInt rnd)) @handles)
                      :when (and (binding-functors (first s)) (< (.nextInt rnd 2) 1))]
                (v/retract! kb h))
              (swap! seen update :pairs-dropped + (count (remove (:pairs (held kb)) before)))
              (is (= (oracle kb) (held kb)) where))))))
    (is (every? pos? (vals @seen)) (str "the streams reach both halves: " @seen))))

;; Each write is checked, so a refresh that stops early, a pair not placed or an inert
;; tuple a departure leaves behind shows at the write that caused it, where the
;; end-of-stream comparison above sees only what the later writes did not repair.

(defn- write-checked!
  "Write each step of `steps` (a sentence to assert, or `[:retract s]`) and answer the
  steps after which the KB differs from the definition."
  [kb steps]
  (let [stored (volatile! {})]
    (into []
          (keep (fn [step]
                  (if (vector? step)
                    (when-let [h (get @stored (second step))] (v/retract! kb h))
                    (when-let [h (try (v/assert kb step 'CxUniverse) (catch clojure.lang.ExceptionInfo _))]
                      (vswap! stored assoc step h)))
                  (when (not= (oracle kb) (held kb)) step)))
          steps)))

(def ^:private fixed-streams
  "Shapes a random stream reaches rarely, over the types `a` < `b` < `c` and the
  individuals `x`, `y`."
  {:joins-the-pair-of-a-functor-that-held-the-length
   (fn [a b c x _] [(list 'genl a b) (list 'genl b c) (list 'arity a 2) (list 'arity b 1)
                    (list 'arity c 1) (list a x) (list b x)])
   :joins-it-when-the-edge-arrives-last
   (fn [a b c _ _] [(list 'genl b c) (list 'arity a 2) (list 'arity b 1) (list 'arity c 3)
                    (list 'genl a b)])
   :joins-an-upper-end-with-no-new-length-for-a-conflict-below
   (fn [a b c _ _] [(list 'genl a b) (list 'arity a 2) (list 'arity b 1) (list 'arity c 1)
                    (list 'genl b c)])
   :keeps-a-length-from-above-after-the-binding-that-stopped-its-walk-leaves
   (fn [a b c x _] [(list 'genl a b) (list 'genl b c) (list a x) (list 'arity b 2)
                    (list 'arity c 2) [:retract (list 'arity b 2)] [:retract (list 'arity c 2)]])
   :two-lengths-on-one-predicate
   (fn [a b _ x y] [(list 'genl a b) (list 'arity b 1) (list 'arity b 2) (list a x)
                    (list 'arity a 1) [:retract (list 'arity b 2)] (list a x y)])
   :a-cycle
   (fn [a b c x y] [(list 'genl a b) (list 'arity c 2) (list 'genl b c) (list b x y)
                    (list 'genl b a) (list 'arity a 1) (list a x) [:retract (list 'genl b c)]])
   :a-cover-arriving-after-the-tuple
   (fn [a b c x _] [(list 'arity c 2) (list a x) (list 'covering c a b) (list b x)
                    [:retract (list 'covering c a b)]])
   :a-tuple-arriving-after-the-cover
   (fn [a b c x _] [(list 'arity c 2) (list 'covering c a b) (list a x)])
   :an-edge-leaving-below-a-conflict
   (fn [a b c x _] [(list 'arity c 2) (list 'arity b 1) (list 'genl b c) (list 'genl a b)
                    (list 'arity a 3) (list a x) [:retract (list 'genl a b)]])})

(deftest the-inert-tuples-and-pairs-match-their-definition-after-every-write
  (testing "the fixed shapes"
    (doseq [[k stream] fixed-streams]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (let [[a b c] (repeatedly 3 #(tu/fresh-term :predicate 'kind))
              [x y]   (repeatedly 2 #(tu/fresh-term :individual 'Thing))]
          (is (= [] (write-checked! kb (stream a b c x y))) (name k))))))
  (testing "seeded streams, their edges and bindings then leaving in a random order"
    (let [rnd (java.util.Random. 1729)
          bad (atom [])]
      (doseq [trial (range 12)]
        (tu/with-neutral-kb [kb tu/isolated-fresh]
          (let [stream (concat (random-stream rnd) (random-stream rnd))
                leave  (->> stream
                            (filter #(or (= 'genl (first %)) (binding-functors (first %))))
                            (sort-by (fn [_] (.nextInt rnd)))
                            (keep #(when (< (.nextInt rnd 3) 2) [:retract %])))]
            (swap! bad into (map #(vector trial %)) (write-checked! kb (concat stream leave))))))
      (is (= [] @bad)))))

(deftest a-cover-binds-its-parts-in-every-order
  ;; A cover installs a `genl` edge per part against its own handle, so a length bound on
  ;; the whole binds a part as an asserted edge would, whichever of the three arrives last.
  (let [answers (atom #{})]
    (doseq [order (oi/permutations [:bind :tuple :cover])]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (let [[whole part other] (repeatedly 3 #(tu/fresh-term :predicate 'kind))
              [x y]              (repeatedly 2 #(tu/fresh-term :individual 'Thing))
              s                  {:bind  (list 'arity whole 1)
                                  :cover (list 'covering whole part other)
                                  :tuple (list part x y)}
              hs                 (into {} (for [k order] [k (v/assert kb (s k) 'CxUniverse)]))]
          (swap! answers conj [(v/believed? kb (:tuple hs) 'CxUniverse)
                               (= (oracle kb) (held kb))]))))
    (is (= #{[false true]} @answers))))

(deftest a-reader-stops-reading-the-bindings-above-once-two-lengths-show
  ;; q binds nothing and sits under a chain of twenty predicates bound to one argument
  ;; with one bound to two at its top: two lengths above leave q unbound, which the
  ;; reader learns from two of the twenty-one bindings
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [q     (tu/fresh-term :predicate 'rel)
          chain (vec (repeatedly 20 #(tu/fresh-term :predicate 'rel)))
          top   (tu/fresh-term :predicate 'rel)
          ind   #(tu/fresh-term :individual 'Thing)]
      (doseq [[a b] (partition 2 1 (concat [q] chain [top]))]
        (v/assert kb (list 'genl a b) 'CxUniverse))
      (doseq [p chain] (v/assert kb (list 'arity p 1) 'CxUniverse))
      (v/assert kb (list 'arity top 2) 'CxUniverse)
      (v/assert kb (list q (ind) (ind) (ind)) 'CxUniverse)
      (let [calls (atom 0)
            real  @#'arity/held-bindings]
        (with-redefs [arity/held-bindings (fn [& args] (swap! calls inc) (apply real args))]
          (is (nil? (arity/relation-length kb q)) "q is unbound, so its tuple breaks nothing"))
        (is (<= @calls 3) (str @calls " bindings read"))))))

(deftest a-functor-s-bound-predicates-are-read-off-one-walk-up-from-it
  ;; q → p0 → … → p5, each p bound to two arguments, the edges stated alternately in CxAr
  ;; and CxCr so no context sees the chain whole: one walk up from q over the unscoped
  ;; closure answers the whole cut, where a walk per bound predicate costs the cut times
  ;; the reach
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (tu/with-terms [CxAr CxCr]
      (doseq [c [CxAr CxCr]] (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
      (let [q  (tu/fresh-term :predicate 'rel)
            ps (vec (repeatedly 6 #(tu/fresh-term :predicate 'rel)))]
        (doseq [[i [a b]] (map-indexed vector (partition 2 1 (cons q ps)))]
          (v/assert kb (list 'genl a b) (if (even? i) CxAr CxCr)))
        (doseq [p ps] (v/assert kb (list 'arity p 2) 'CxUniverse))
        (let [walks  (atom {})
              built  (atom 0)
              count! (fn [k real] (fn [& args] (swap! walks update k (fnil inc 0)) (apply real args)))
              union  tax/genls-global-union]
          (with-redefs [tax/genl-path           (count! :path @#'tax/genl-path)
                        tax/reachable-filtered? (count! :walk @#'tax/reachable-filtered?)
                        tax/genls-global-union  (fn [tx t xf memo]
                                                  (swap! walks update :union (fnil inc 0))
                                                  (let [r (union tx t xf memo)]
                                                    (swap! built + (count @memo))
                                                    r))]
            (is (= 6 (count (:grounds (arity/relation-length kb q true))))
                "every bound predicate above q grounds the length"))
          (is (nil? (:path @walks)) "no path is read per bound predicate")
          (is (nil? (:walk @walks)) "and no pair walks")
          (is (= 1 (:union @walks)) "one walk up from q")
          (is (<= @built 7) "the walk builds q and each of its six supers once"))))))

;; A placed defeat or an except of a `genl` edge hides the edge at a vantage and leaves it
;; IN, so the length it carries stays bound, as a hidden binding's does (docs/taxonomy.md,
;; "Arity").  An equality superseding the edge's spelling takes it out of the closure, and
;; its retraction brings it back with no write to the edge.

(defn- edge-belief-trial
  "Write `order` (a permutation of :binding :edge :tuple :hide), the hide as `how` says: a
  monotonic denial of the `genl` edge, whose placed nogood defeats it, an except of it, or
  a `rewriteOf` deprecating its lower end.  Then lift the hide, and answer
  `[believed-while-hidden believed-after]` for the ternary tuple under the binary super."
  [order how]
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (tu/with-terms [parentOf motherOf motherOfX Ada Bea Cy]
      (let [M    {:strength :monotonic}
            edge (list 'genl motherOfX parentOf)
            hs   (volatile! {})
            w    {:binding #(v/assert kb (list 'arity parentOf 2) 'CxUniverse M)
                  :edge    #(v/assert kb edge 'CxUniverse)
                  :tuple   #(v/assert kb (list motherOfX Ada Bea Cy) 'CxUniverse)
                  :hide    #(v/assert kb (case how
                                           :deny    (list 'not edge)
                                           :except  (list 'except (list 'sentexHandle (:edge @hs)))
                                           :rewrite (list 'rewriteOf motherOf motherOfX))
                                      'CxUniverse M)}]
        (doseq [k order] (vswap! hs assoc k ((w k))))
        (let [hidden (v/believed? kb (:tuple @hs) 'CxUniverse)]
          (v/retract! kb (:hide @hs))
          [hidden (v/believed? kb (:tuple @hs) 'CxUniverse)])))))

(deftest ^:slow a-tuple-under-a-hidden-edge-stays-inert-in-every-order
  (let [ks     [:binding :edge :tuple :hide]
        orders (for [a ks, b ks, c ks, d ks
                     :let [o [a b c d]]
                     :when (= 4 (count (set o)))]
                 o)
        before (fn [^java.util.List o] (< (.indexOf o :edge) (.indexOf o :hide)))]
    (doseq [[how os] [[:deny orders] [:except (filter before orders)]]]
      (is (= {[false false] (count os)} (frequencies (map #(edge-belief-trial % how) os)))
          (name how)))
    ;; a superseded spelling is not believed, so only the answer after the lift is asserted
    (is (= {false (count orders)}
           (frequencies (map #(second (edge-belief-trial % :rewrite)) orders)))
        "rewrite")))

(deftest a-tuple-under-a-hidden-edge-stays-inert
  ;; the sampled twin of the sweep above: the orders where the edge or the tuple arrives
  ;; after the equality, and one denial order
  (is (= [false false false false]
         (mapv #(second (edge-belief-trial % :rewrite))
               [[:binding :edge :hide :tuple] [:hide :edge :tuple :binding]
                [:edge :hide :binding :tuple] [:tuple :hide :edge :binding]])))
  (is (= [false false] (edge-belief-trial [:binding :edge :hide :tuple] :deny))))

(deftest a-defeat-placed-on-the-edge-after-the-tuple-leaves-it-inert
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (tu/with-terms [parentOf motherOf Ada Bea Cy]
      (let [M {:strength :monotonic}]
        (v/assert kb (list 'arity parentOf 2) 'CxUniverse M)
        (v/assert kb (list 'genl motherOf parentOf) 'CxUniverse)
        (let [t (v/assert kb (list motherOf Ada Bea Cy) 'CxUniverse)]
          (is (not (v/believed? kb t 'CxUniverse)))
          (v/assert kb (list 'not (list 'genl motherOf parentOf)) 'CxUniverse M)
          (is (not (v/believed? kb t 'CxUniverse))))))))

(deftest a-binding-leaving-fires-over-the-tuple-it-released-at-that-write-in-either-order
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (doseq [tuple-first? [true false]]
      (tu/with-terms [q r A B C]
        (v/assert kb (list 'set/forwardRule (list 'implies (list q '?x '?y '?z) (list r '?x '?z)))
                  'CxUniverse)
        (let [b     (v/assert kb (list 'arity q 2) 'CxUniverse)
              tuple #(v/assert kb (list q A B C) 'CxUniverse)
              free  #(v/retract! kb b)]
          (if tuple-first? (do (tuple) (free)) (do (free) (tuple)))
          (let [c (v/handle-of kb (list r A C) 'CxUniverse)]
            (is (and c (v/in? kb c))
                (if tuple-first? "the tuple before the release" "the release before the tuple"))))))))

(defn- descension-pairs
  "Six predicates bound to three arguments under one bound to two, every binding and
  edge a `:monotonic` premise in CxUniverse: six `:arity-descension` pairs."
  [kb]
  (let [M   {:strength :monotonic}
        hi  (tu/fresh-term :predicate 'rel)
        los (vec (repeatedly 6 #(tu/fresh-term :predicate 'rel)))]
    (v/assert kb (list 'arity hi 2) 'CxUniverse M)
    (doseq [lo los]
      (v/assert kb (list 'arity lo 3) 'CxUniverse M)
      (v/assert kb (list 'genl lo hi) 'CxUniverse M))))

(deftest a-pair-sync-takes-out-only-the-pairs-it-placed
  ;; A CxUniverse binding and one of another length stated below CxUniverse, under two
  ;; disjoint supertypes of their classes, are the disjointness nogood, placed where both
  ;; are seen.  The sync over the binding's predicate asks no removal of that pair.
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (tu/with-terms [relA CxWellA two three]
      (let [M     {:strength :monotonic}
            place @#'chain/place-justified!
            asked (atom [])]
        (v/assert kb (list 'genlCx CxWellA 'CxUniverse) 'CxUniverse M)
        (v/assert kb (list 'genl 'binary_predicate two) 'CxUniverse M)
        (v/assert kb (list 'genl 'ternary_predicate three) 'CxUniverse M)
        (v/assert kb (list 'disjoint two three) 'CxUniverse M)
        (let [hw (v/assert kb (list 'ternary_predicate relA) CxWellA)
              hu (v/assert kb (list 'binary_predicate relA) 'CxUniverse M)]
          (is (some #(and (= CxWellA (:context %))
                          (= #{hu hw} (into #{} (keep sx/handle-id) (rest (:sentence %)))))
                    (v/sentexes-with-functor kb 'contradicts))
              "the pair is placed in the context below")
          (with-redefs [chain/place-justified! (fn [kb ms placements & more]
                                                 (when (empty? placements) (swap! asked conj (set ms)))
                                                 (apply place kb ms placements more))]
            (v/assert kb (list 'arity relA 2) 'CxUniverse M))
          (is (not-any? #{#{hu hw}} @asked)))))))

(deftest a-reader-reads-each-pair-of-monotonic-bindings-as-hard
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (descension-pairs kb)
    (is (= 6 (count (filter #(= :arity-descension (:kind %)) (v/conflicts kb)))))
    (is (= 6 (count (v/sentexes-with-functor kb 'contradicts))) "each pair is placed")
    (is (empty? (v/sentexes-with-functor kb 'defeat)) "and defeats no binding")))
