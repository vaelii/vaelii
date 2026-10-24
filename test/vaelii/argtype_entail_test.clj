;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.argtype-entail-test
  "Assertive argument types: `(arg parentOf 1 animal)` read as an entailment about
  the argument, not only as a constraint on it.

  The check's open-world floor is what this fills — an argument with no visible place
  in the genl hierarchy cannot violate anything, so it passes and the KB learns
  nothing, however many times it has been told that the slot holds an animal.  The
  entailment is drawn exactly there and nowhere else, and it is drawn as a **derived,
  justified** sentex: retract the fact or the declaration and the type goes with it.

  On by default (`argument/*assertive-arg-types?*`), and every test here binds it anyway, so
  a run under `VAELII_ASSERTIVE_ARG_TYPES=0` still measures the entailment."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [is testing use-fixtures]]
            [clojure.walk :as walk]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu])
  (:import [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defmacro with-entailing
  "Run the body with assertive argument types on."
  [& body]
  `(binding [argument/*assertive-arg-types?* true] ~@body))

(defmacro with-pruning
  "Run the body with the entailment on and subsumed mints pruned — the default reading,
  bound so a run under `VAELII_PRUNE_SUBSUMED_MINTS=0` still measures it."
  [& body]
  `(binding [argument/*assertive-arg-types?* true
             checks/*prune-subsumed-mints?* true]
     ~@body))

(defmacro with-mints-kept
  "Run the body with the entailment on and pruning off — the reading
  `VAELII_PRUNE_SUBSUMED_MINTS=0` selects."
  [& body]
  `(binding [argument/*assertive-arg-types?* true
             checks/*prune-subsumed-mints?* false]
     ~@body))

(defmacro without-entailing
  "Run the body with them off — bound rather than assumed, since the root value is
  what `VAELII_ASSERTIVE_ARG_TYPES` sets to run the whole suite under the feature."
  [& body]
  `(binding [argument/*assertive-arg-types?* false] ~@body))

(defn- a-type
  "Place `t` under `thing`: an edge some tests read, and one a mint does not need
  (`arity/mintable-type?` reads `t`'s arity alone)."
  [kb t ctx]
  (v/assert kb (list 'genl t 'thing) ctx))

(defn- a-context
  "Hang `ctx` under CxUniverse, so what is declared universally is visible from
  it.  A `fresh` KB has no context edges, and a context wired to nothing sees nothing —
  which would make every argument outside the hierarchy and every test here trivially
  true."
  [kb ctx]
  (v/assert kb (list 'genlCx ctx 'CxUniverse) 'CxUniverse))

(defn- entailed
  "The handle of the **stored, believed** sentex for `sentence` in `ctx`, or nil.

  Deliberately not `ask`.  `provers/ArgTypeProver` already answers a ground
  `(Type Individual)` goal off the very declaration under test — arg read as an
  inference is not what is new here.  What is new is that the type becomes a
  **record**: a handle, a justification naming what it rests on, a place in the
  taxonomy that `isa?` and the definitional checks read, and a datum the agenda can
  fire rules on.  A prover's answer is none of those, and a test that asked one could
  not tell the two apart."
  [kb sentence ctx]
  (let [h (v/handle-of kb sentence ctx)]
    (when (and h (v/in? kb h)) h)))

(defn- believed? [kb sentence ctx] (some? (entailed kb sentence ctx)))

(defn- permutations
  [coll]
  (if (< (count coll) 2)
    (list coll)
    (for [i (range (count coll))
          p (permutations (concat (take i coll) (drop (inc i) coll)))]
      (cons (nth coll i) p))))

;; ---- the headline --------------------------------------------------------

(tu/deftest-kb a-declaration-entails-the-type-it-constrains
  (tu/with-terms [animal parentOf Fred Mary CxWorld]
    (a-context kb CxWorld)
    (a-type kb animal CxWorld)
    (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
    (testing "with the entailment off, the constraint passes and stores nothing"
      (without-entailing
       (v/assert kb (list parentOf Fred Mary) CxWorld)
       (is (not (believed? kb (list animal Fred) CxWorld)))
       (is (not (v/isa? kb Fred animal CxWorld))
           "and the taxonomy has not learned what the declaration says")
       (is (empty? (v/types-of kb Fred CxWorld)))))
    (v/retract! kb (v/handle-of kb (list parentOf Fred Mary) CxWorld))
    (with-entailing
      (v/assert kb (list parentOf Fred Mary) CxWorld)
      (testing "with it on, the type is a stored, believed datum"
        (is (believed? kb (list animal Fred) CxWorld)))
      (testing "so the taxonomy — and everything reading it — now says so"
        (is (v/isa? kb Fred animal CxWorld))
        (is (= [animal] (vec (v/types-of kb Fred CxWorld)))))
      (testing "and the second argument, which nothing constrains, is untouched"
        (is (not (believed? kb (list animal Mary) CxWorld)))))))

(tu/deftest-kb why-names-the-fact-and-the-declaration
  (tu/with-terms [animal parentOf Fred Mary CxWorld]
    (a-type kb animal CxWorld)
    (a-context kb CxWorld)
    (let [dh (v/assert kb (list 'arg parentOf 1 animal) CxWorld)]
      (with-entailing
        (let [fh (v/assert kb (list parentOf Fred Mary) CxWorld)
              th (v/handle-of kb (list animal Fred) CxWorld)
              w  (v/why kb th)
              sup (first (:support w))]
          (is (some? th) "the type is stored")
          (is (false? (:premise? w)) "and derived, not asserted")
          (is (= 'arg (:informant sup)) "the declaring predicate is the informant")
          (is (= #{fh dh} (set (map :handle (:because sup))))
              "resting on the triggering fact and the declaration, and nothing else"))))))

;; ---- both directions reach one KB ---------------------------------------

(tu/deftest-kb a-declaration-reaches-the-facts-already-stored
  (tu/with-terms [animal parentOf Fred Mary Ann Bob CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (v/assert kb (list parentOf Fred Mary) CxWorld)
      (v/assert kb (list parentOf Ann Bob) CxWorld)
      (is (not (believed? kb (list animal Fred) CxWorld))
          "nothing is entailed while nothing is declared")
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
      (testing "the declaration arriving last reaches every fact already stored"
        (is (believed? kb (list animal Fred) CxWorld))
        (is (believed? kb (list animal Ann) CxWorld))))))

(tu/deftest-kb the-two-arrival-orders-reach-the-same-belief
  ;; declaration-then-fact and fact-then-declaration are the same knowledge
  (doseq [order [:declaration-first :facts-first]]
    (tu/with-neutral-kb [kb tu/fresh]
      (tu/with-terms [animal parentOf Fred Mary CxWorld]
        (with-entailing
          (a-context kb CxWorld)
          (a-type kb animal CxWorld)
          (let [decl #(v/assert kb (list 'arg parentOf 1 animal) CxWorld)
                fact #(v/assert kb (list parentOf Fred Mary) CxWorld)]
            (if (= order :declaration-first) (do (decl) (fact)) (do (fact) (decl))))
          (is (believed? kb (list animal Fred) CxWorld)
              (str "entailed under " (name order)))
          (is (= 1 (count (:support (v/why kb (v/handle-of kb (list animal Fred)
                                                           CxWorld)))))
              (str "with one justification under " (name order))))))))

;; ---- a declaration's sweep over stored facts ------------------------------

(defn- walks-to-thing
  "The types asked whether they reach `thing` through `genl` while `f` runs, with the
  number of reachability walks each took."
  [f]
  (let [real   @#'tax/reachable?
        walked (atom [])]
    (with-redefs [tax/reachable? (fn
                                   ([a b adj depth] (real a b adj depth nil))
                                   ([a b adj depth scc]
                                    (when (= 'thing b) (swap! walked conj a))
                                    (real a b adj depth scc)))]
      (f))
    (frequencies @walked)))

(tu/deftest-kb a-declaration-over-stored-facts-walks-no-type-to-thing
  ;; `low_t` sits at the bottom of a chain not under `thing`, and the predicate already
  ;; declares it at position 1.  The declaration arriving at position 2 mints over every
  ;; fact whether or not `new_t` is under `thing`, and asks no type whether it reaches
  ;; `thing` (`arity/mintable-type?` reads the type's arity).
  (doseq [under-thing? [false true]]
    (let [reading (fn [n]
                    (tu/with-neutral-kb [kb tu/fresh]
                      (tu/with-terms [rel top_t low_t mid_t new_t CxWorld]
                        (with-entailing
                          (a-context kb CxWorld)
                          (v/assert kb (list 'genl mid_t top_t) CxWorld)
                          (v/assert kb (list 'genl low_t mid_t) CxWorld)
                          (when under-thing? (a-type kb new_t CxWorld))
                          (v/assert kb (list 'arg rel 1 low_t) CxWorld)
                          (dotimes [_ n]
                            (v/assert kb (list rel (tu/tmp-ind "A") (tu/tmp-ind "B")) CxWorld))
                          (let [w (walks-to-thing #(v/assert kb (list 'arg rel 2 new_t) CxWorld))]
                            {:walks (reduce + 0 (vals w))
                             :mints (count (v/sentexes-matching kb (list new_t '?x) CxWorld))})))))]
      (is (= [{:walks 0 :mints 4} {:walks 0 :mints 16}]
             [(reading 4) (reading 16)])
          (if under-thing? "a type under thing" "a type no edge places")))))

(tu/deftest-kb a-declaration-s-entailments-are-the-ones-every-declaration-draws-under-it
  ;; One fact of each shape below every entailing kind, through a local, an inherited and
  ;; a super-predicate declaration, with mintable and unmintable types and every trigger
  ;; held.
  (tu/with-terms [rel super kinds a_t u0_t u1_t g_t trig_t tu_t all_t rest_t ag_t arg_t
                  hom_t hom2_t s_t kind_t kind2_t A B C E CxUp CxDown]
    (with-entailing
      (v/assert kb (list 'genlCx CxUp 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxDown CxUp) 'CxUniverse)
      (doseq [t [a_t g_t trig_t tu_t all_t rest_t ag_t arg_t hom_t hom2_t s_t kind_t kind2_t]]
        (a-type kb t CxUp))
      (v/assert kb (list 'genl u1_t u0_t) CxUp)
      (v/assert kb (list 'genl rel super) CxUp)
      (let [dhs   (mapv #(v/assert kb % CxUp)
                        [(list 'arg rel 1 a_t) (list 'arg rel 2 u1_t) (list 'genlArg rel 3 g_t)
                         (list 'interArg rel 1 trig_t 2 tu_t) (list 'interArg rel 1 trig_t 2 u1_t)
                         (list 'argAndRest rel 1 all_t) (list 'argAndRest rel 1 u0_t)
                         (list 'argAndRest rel 2 rest_t) (list 'argAndRestGenl rel 3 arg_t)
                         (list 'interArgs rel hom_t) (list 'interArgAndRest rel 2 hom2_t)
                         (list 'argsGenl kinds ag_t) (list 'arg super 2 s_t)])
            _     (doseq [m [(list trig_t A) (list hom_t B) (list hom2_t B)]]
                    (v/assert kb m CxUp))
            facts [[(list rel A B kind_t) CxDown] [(list rel C B kind2_t) CxUp]
                   [(list rel A E kind_t) CxUp] [(list kinds kind_t kind2_t) CxDown]]]
        (doseq [[s c] facts] (v/assert kb s c))
        (let [all (mapv (fn [[s c]] (checks/constraint-entailments kb s c)) facts)]
          ;; `args` is no kind of its own: it entails through the `argAndRest` twin
          ;; core.txt's forward rule stores (covering_arg_test)
          (is (= '#{arg genlArg interArg argAndRest argAndRestGenl interArgs
                    interArgAndRest argsGenl}
                 (into #{} (comp cat (map :kind)) all))
              "every entailing kind draws over the facts")
          (doseq [[[s c] es] (map vector facts all)
                  dh dhs]
            (is (= (filterv #(= dh (first (:because %))) es)
                   (checks/declaration-entailments kb s c dh))
                (str s " under " (:sentence (v/sentex kb dh))))))))))

;; ---- whose declarations a membership reads -----------------------------

(defn- counting-set
  "`s`, with every element it hands out and every membership asked of it added to `n`."
  [s n]
  (reify
    clojure.lang.IPersistentSet
    (disjoin [_ x] (disj s x))
    (contains [_ x] (swap! n inc) (contains? s x))
    (get [_ x] (swap! n inc) (get s x))
    (count [_] (count s))
    (cons [_ x] (conj s x))
    (empty [_] #{})
    (equiv [_ o] (= s o))
    (seq [_] (seq (map (fn [x] (swap! n inc) x) s)))
    java.lang.Iterable
    (iterator [_]
      (let [it (.iterator ^Iterable s)]
        (reify java.util.Iterator
          (hasNext [_] (.hasNext it))
          (next [_] (swap! n inc) (.next it)))))))

(defn- ancestors-read
  "How many elements of the `genl` up-closures `res/constraining-predicates` reads while
  `f` runs."
  [f]
  (let [n      (atom 0)
        inside (atom false)
        cp     res/constraining-predicates
        genls  tax/genls]
    (with-redefs [res/constraining-predicates (fn [& args]
                                                (reset! inside true)
                                                (try (apply cp args) (finally (reset! inside false))))
                  tax/genls (fn [t pred ctx]
                              (cond-> (genls t pred ctx) @inside (counting-set n)))]
      (f))
    @n))

(tu/deftest-kb a-membership-reads-the-declaring-props-set-not-its-type-s-ancestors
  ;; One predicate declares `arg`; the membership's type sits 8 and then 64 below a type
  ;; under `thing`, so its own functor's declaration read meets a closure of 10 and of 66.
  (let [reading (fn [depth]
                  (tu/with-neutral-kb [kb tu/fresh]
                    (tu/with-terms [rel top_t CxWorld]
                      (with-entailing
                        (a-context kb CxWorld)
                        (a-type kb top_t CxWorld)
                        (v/assert kb (list 'arg rel 1 top_t) CxWorld)
                        (let [ts (vec (repeatedly depth #(tu/tmp-type "deep_t")))]
                          (doseq [[sub super] (map vector ts (cons top_t ts))]
                            (v/assert kb (list 'genl sub super) CxWorld))
                          (ancestors-read
                           #(v/assert kb (list (peek ts) (tu/tmp-ind "A")) CxWorld)))))))]
    (is (= (reading 8) (reading 64)))))

(tu/deftest-kb constraining-predicates-are-the-declaring-supers-in-content-order
  ;; A predicate chain declaring at every other link, an edge only `CxSide` sees, and the
  ;; same reads again once the declaring `:props` set outgrows every closure here.
  (tu/with-terms [pa pb pc pd pe px a_t CxWorld CxSide]
    (a-context kb CxWorld)
    (v/assert kb (list 'genlCx CxSide CxWorld) 'CxUniverse)
    (a-type kb a_t CxWorld)
    (doseq [[sub super] [[pa pb] [pb pc] [pc pd] [pd pe]]]
      (v/assert kb (list 'genl sub super) CxWorld))
    (v/assert kb (list 'genl pa px) CxSide)
    (doseq [p [pa pc pe px]]
      (v/assert kb (list 'arg p 1 a_t) CxWorld))
    (let [tax       (reasoning/taxonomy kb)
          reference (fn [pred ctx]
                      (let [d (tax/props tax (tax/arg-declaration-props 'arg))]
                        (into (if (contains? d pred) [pred] [])
                              (comp (remove #{pred}) (filter d))
                              (sort (tax/genls tax pred ctx)))))
          readings  (fn []
                      (let [memos (volatile! {})]
                        (for [pred [pa pb pc pd pe px], ctx [CxWorld CxSide]]
                          [[(res/constraining-predicates kb 'arg pred ctx)
                            (res/constraining-predicates kb 'arg pred ctx memos)]
                           (repeat 2 (reference pred ctx))])))]
      (is (= (into [pa] (sort [pc pe px])) (res/constraining-predicates kb 'arg pa CxSide)))
      (doseq [[got want] (readings)] (is (= want got)))
      (dotimes [_ 8]
        (v/assert kb (list 'arg (tu/tmp-pred "other") 1 a_t) CxWorld))
      (doseq [[got want] (readings)] (is (= want got))))))

(tu/deftest-kb constraining-predicates-under-a-pass-memo-read-no-genl-closure
  ;; A chain of 64 types under one declaring predicate, each read from a context that
  ;; sees the chain and from one that adds an edge to a second declaring predicate.
  (tu/with-terms [side top_t a_t CxWorld CxSide]
    (a-context kb CxWorld)
    (v/assert kb (list 'genlCx CxSide CxWorld) 'CxUniverse)
    (a-type kb a_t CxWorld)
    (a-type kb top_t CxWorld)
    (let [ts (vec (repeatedly 64 #(tu/tmp-type "deep_t")))]
      (doseq [[sub super] (map vector ts (cons top_t ts))]
        (v/assert kb (list 'genl sub super) CxWorld))
      (v/assert kb (list 'genl (peek ts) side) CxSide)
      (doseq [p [top_t side]]
        (v/assert kb (list 'arg p 1 a_t) CxWorld))
      (let [memos (volatile! {})
            got   (atom nil)]
        (is (zero? (ancestors-read
                    #(reset! got (vec (for [t ts, ctx [CxWorld CxSide]]
                                        (res/constraining-predicates kb 'arg t ctx memos)))))))
        (is (= (vec (for [t ts, ctx [CxWorld CxSide]]
                      (res/constraining-predicates kb 'arg t ctx)))
               @got))
        (is (= [[top_t] (vec (sort [top_t side]))] (subvec @got 126)))))))

;; ---- the type is held by its supporters ---------------------------------

(tu/deftest-kb retracting-either-supporter-takes-the-type-back
  (doseq [drop [:the-fact :the-declaration]]
    (tu/with-neutral-kb [kb tu/fresh]
      (tu/with-terms [animal parentOf Fred Mary CxWorld]
        (with-entailing
          (a-context kb CxWorld)
          (a-type kb animal CxWorld)
          (let [dh (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
                fh (v/assert kb (list parentOf Fred Mary) CxWorld)]
            (is (believed? kb (list animal Fred) CxWorld))
            (v/retract! kb (if (= drop :the-fact) fh dh))
            (is (not (believed? kb (list animal Fred) CxWorld))
                (str "the type goes when " (name drop) " goes"))
            (is (nil? (v/handle-of kb (list animal Fred) CxWorld))
                "swept, not merely disbelieved — its only justification is invalid")))))))

(tu/deftest-kb a-type-survives-while-anything-supports-it
  (tu/with-terms [animal parentOf childOf Fred Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
      (v/assert kb (list 'arg childOf 1 animal) CxWorld)
      (let [fh (v/assert kb (list parentOf Fred Mary) CxWorld)]
        (v/assert kb (list childOf Fred Mary) CxWorld)
        (is (believed? kb (list animal Fred) CxWorld))
        (testing "two independent facts entail it; dropping one leaves the other"
          (v/retract! kb fh)
          (is (believed? kb (list animal Fred) CxWorld)))))))

(defn- two-route-steps
  "The eight sentences of the two-route shape, keyed for an arrival order: `(arg pd 1
  tt)` declared on `pd`, and `(pa Xone)` a `pd` tuple over two `genl` paths, `pa → pb →
  pd` and `pa → pc → pd`."
  [kb tt pa pb pc pd Xone ctx]
  {:tt   #(a-type kb tt ctx)
   :pd   #(a-type kb pd ctx)
   :ab   #(v/assert kb (list 'genl pa pb) ctx)
   :ac   #(v/assert kb (list 'genl pa pc) ctx)
   :bd   #(v/assert kb (list 'genl pb pd) ctx)
   :cd   #(v/assert kb (list 'genl pc pd) ctx)
   :decl #(v/assert kb (list 'arg pd 1 tt) ctx)
   :fact #(v/assert kb (list pa Xone) ctx)})

(def ^:private two-route-orders
  "Six arrival orders of the two-route shape: the fact last, the declaration first and
  last, the declaration before either path is whole, and each path's edges arriving
  after the declaration."
  {:fact-last         [:tt :pd :ab :ac :bd :cd :decl :fact]
   :decl-first        [:decl :fact :tt :pd :ab :bd :ac :cd]
   :decl-last         [:fact :tt :pd :ab :ac :bd :cd :decl]
   :decl-before-paths [:fact :tt :pd :decl :ab :bd :ac :cd]
   :pc-path-last      [:fact :tt :pd :ab :bd :decl :ac :cd]
   :pb-path-last      [:fact :tt :pd :ac :cd :decl :ab :bd]})

(tu/deftest-kb a-type-entailed-over-two-routes-survives-either-route-going
  ;; The mint names one route (`checks/edge-support`), so retracting an edge on that
  ;; route sweeps the record, and defeating one takes it OUT.  The other route still
  ;; entails the type, so the removal or the defeat re-derives it from the taxonomy it
  ;; left (`special/rederive-descended`), and `isa?` agrees with `ask?` whichever edge
  ;; went, however it went, and whatever the arrival order.
  (let [results
        (for [[order steps] (sort two-route-orders)
              [how via]     [nil [:retract :ab] [:retract :ac] [:defeat :ab] [:defeat :ac]]]
          (tu/with-neutral-kb [kb tu/fresh]
            (tu/with-terms [tt pa pb pc pd Xone CxProbe]
              (with-entailing
                (a-context kb CxProbe)
                (let [step (two-route-steps kb tt pa pb pc pd Xone CxProbe)]
                  (run! #((step %)) steps))
                (let [edge (list 'genl pa (if (= via :ab) pb pc))]
                  (case how
                    nil      nil
                    :retract (v/retract! kb (v/handle-of kb edge CxProbe))
                    :defeat  (v/assert kb (list 'not edge) CxProbe {:strength :monotonic})))
                [order how via {:stored (believed? kb (list tt Xone) CxProbe)
                                :isa    (v/isa? kb Xone tt CxProbe)
                                :ask    (v/ask? kb (list tt Xone) CxProbe)}]))))]
    (is (= #{{:stored true :isa true :ask true}} (set (map last results)))
        (str "a route's edge going took the type with it: "
             (pr-str (remove #(= {:stored true :isa true :ask true} (last %)) results))))))

(tu/deftest-kb defeating-the-fact-takes-the-type-out-with-it
  (tu/with-terms [animal parentOf Fred Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld {:strength :monotonic})
      (v/assert kb (list parentOf Fred Mary) CxWorld)
      (is (believed? kb (list animal Fred) CxWorld))
      ;; a known-true negation defeats the default fact; the type is derived from it,
      ;; so belief follows without anything arranging for it
      (v/assert kb (list 'not (list parentOf Fred Mary)) CxWorld
                {:strength :monotonic})
      (is (not (believed? kb (list animal Fred) CxWorld))
          "the minted type follows the belief of what it rests on"))))

;; ---- where it does *not* mint -------------------------------------------

(tu/deftest-kb an-inherited-declaration-derives-and-a-disjoint-type-is-a-clash
  ;; An argument constraint only adds support: the ancestor's declaration derives in the
  ;; descendant as a local one does, and an argument the KB places in a disjoint type is
  ;; stored with its derived membership, the pair listed as a contradiction.
  (tu/with-terms [animal rock parentOf Fred Mary Rex CxSchema CxStory]
    (with-entailing
      (a-type kb animal 'CxUniverse)
      (a-type kb rock 'CxUniverse)
      (a-context kb CxSchema)
      (v/assert kb (list 'genlCx CxStory CxSchema) 'CxUniverse)
      (v/assert kb (list 'arg parentOf 1 animal) CxSchema)
      (v/assert kb (list parentOf Fred Mary) CxStory)
      (testing "the ancestor's declaration derives in the descendant"
        (is (believed? kb (list animal Fred) CxStory)))
      (testing "a disjoint membership is a clash, not a refusal"
        (v/assert kb (list rock Rex) CxStory)
        (v/assert kb (list 'disjoint animal rock) 'CxUniverse)
        (v/assert kb (list parentOf Rex Mary) CxStory)
        (is (some? (v/handle-of kb (list parentOf Rex Mary) CxStory)))
        (is (some? (v/handle-of kb (list animal Rex) CxStory)))
        (is (= 1 (count (v/contradictions kb))))))))

(tu/deftest-kb one-sentex-however-many-declarations-entail-it
  ;; Deduplication is by content, and only by content: one record for the sentence, one
  ;; justification per (fact, declaration) pair.  Nothing is withheld because the type
  ;; was already reachable — see `checks/constraint-entailments` for why any such
  ;; narrowing would make the answer depend on arrival order.
  (tu/with-terms [animal parentOf childOf Fred Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
      (v/assert kb (list 'arg childOf 1 animal) CxWorld)
      (v/assert kb (list parentOf Fred Mary) CxWorld)
      (v/assert kb (list childOf Fred Mary) CxWorld)
      (is (= 1 (count (v/sentexes-with-functor kb animal))) "one record")
      (is (= 2 (count (:support (v/why kb (entailed kb (list animal Fred) CxWorld)))))
          "two justifications — each fact holds it up on its own"))))

(tu/deftest-kb a-subsuming-membership-does-not-suppress-the-entailment
  ;; The stance with pruning off, stated as a test: `(dog Muffet)` under `(genl dog animal)`
  ;; already *reaches* `animal` by subsumption, and the entailment is drawn anyway.
  ;; Withholding it is what `*prune-subsumed-mints?*` does, by default
  ;; (`a-subsuming-membership-withholds-the-entailment-when-pruning`).
  (tu/with-terms [animal dog parentOf Muffet Mary CxWorld]
    (with-mints-kept
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (v/assert kb (list 'genl dog animal) CxWorld)
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
      (v/assert kb (list dog Muffet) CxWorld)
      (v/assert kb (list parentOf Muffet Mary) CxWorld)
      (is (believed? kb (list animal Muffet) CxWorld))
      (testing "and it is derived, so retracting the fact takes it back"
        (v/retract! kb (v/handle-of kb (list parentOf Muffet Mary) CxWorld))
        (is (nil? (v/handle-of kb (list animal Muffet) CxWorld)))
        (is (v/isa? kb Muffet animal CxWorld)
            "while subsumption, which never needed the record, still answers")))))

;; ---- pruning: a mint the KB says more specifically is not stored --------------

(tu/deftest-kb a-subsuming-membership-withholds-the-entailment-when-pruning
  ;; `(dog Muffet)` reaches `animal` by subsumption, so a minted `(animal Muffet)` beside
  ;; it is the same claim one step vaguer — and with pruning on it is withheld.  What the
  ;; KB answers is untouched, since subsumption never needed the record.
  (tu/with-terms [animal dog parentOf Muffet Mary CxWorld]
    (with-pruning
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (v/assert kb (list 'genl dog animal) CxWorld)
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
      (v/assert kb (list dog Muffet) CxWorld)
      (v/assert kb (list parentOf Muffet Mary) CxWorld)
      (is (nil? (v/handle-of kb (list animal Muffet) CxWorld))
          "no record: the KB says it more specifically")
      (is (v/isa? kb Muffet animal CxWorld) "and answers the membership regardless")
      (testing "the specific membership leaving draws the mint after all"
        (v/retract! kb (v/handle-of kb (list dog Muffet) CxWorld))
        (is (believed? kb (list animal Muffet) CxWorld))
        (is (v/isa? kb Muffet animal CxWorld)))
      (testing "and it is derived, so retracting the fact takes it back"
        (v/retract! kb (v/handle-of kb (list parentOf Muffet Mary) CxWorld))
        (is (nil? (v/handle-of kb (list animal Muffet) CxWorld)))
        (is (not (v/isa? kb Muffet animal CxWorld))
            "with the specific membership gone too, nothing says it any more")))))

(tu/deftest-kb a-membership-leaving-reads-its-types-ancestors-once-for-every-fact-naming-its-term
  ;; the settle asks of each mint the facts naming Muffet draw again whether `(dog
  ;; Muffet)` leaving can have withheld it, and the answer is `animal` above `dog`
  (tu/with-terms [animal dog parentOf Muffet CxWorld]
    (with-pruning
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (v/assert kb (list 'genl dog animal) CxWorld)
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
      (v/assert kb (list dog Muffet) CxWorld)
      (dotimes [_ 12]
        (v/assert kb (list parentOf Muffet (tu/fresh-term :individual 'Kid)) CxWorld))
      (is (nil? (v/handle-of kb (list animal Muffet) CxWorld)))
      (let [reads (atom 0)
            count-in (fn [v] (let [orig @v]
                               [v (fn [t sub & more]
                                    (when (= dog sub) (swap! reads inc))
                                    (apply orig t sub more))]))]
        (with-redefs-fn (into {} (map count-in) [#'tax/genl?-global #'tax/genls-global])
          #(v/retract! kb (v/handle-of kb (list dog Muffet) CxWorld)))
        (is (believed? kb (list animal Muffet) CxWorld))
        (is (<= @reads 2) (str @reads " reads of dog's ancestors"))))))

(tu/deftest-kb a-membership-arriving-after-the-mint-withdraws-it
  ;; The other arrival order of `a-subsuming-membership-withholds-the-entailment`: the
  ;; record is already stored when the specific membership lands, so it has to leave —
  ;; `settle` blocks the justifications that hold it up and the sweep collects it, the
  ;; way it collects an excepted conclusion.
  (tu/with-terms [animal dog parentOf Muffet Mary CxWorld]
    (with-pruning
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (v/assert kb (list 'genl dog animal) CxWorld)
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
      (v/assert kb (list parentOf Muffet Mary) CxWorld)
      (is (believed? kb (list animal Muffet) CxWorld) "minted while nothing says more")
      (v/assert kb (list dog Muffet) CxWorld)
      (is (nil? (v/handle-of kb (list animal Muffet) CxWorld)) "and withdrawn once one does")
      (is (v/isa? kb Muffet animal CxWorld) "while the answer is unchanged")
      (testing "retracting the specific membership draws it again"
        (v/retract! kb (v/handle-of kb (list dog Muffet) CxWorld))
        (is (believed? kb (list animal Muffet) CxWorld))))))

(tu/deftest-kb a-subsumer-resting-on-the-mint-does-not-keep-it
  ;; `(awake Fido)`, `(alert Fido)`, `(calm Fido)` and `(fed Fido)` are derived from the
  ;; mint by forward rules and sit under `animal`, so each subsumes it while resting on it.
  ;; The `genl` edge arriving last makes `(dog Fido)` a subsumer that rests on nothing
  ;; minted, and that one withdraws the mint, as the order stating the edge first
  ;; withholds it.  The subsumption search meets the term's types in hash order, so four
  ;; rows of fresh names make it near certain that one row meets a resting subsumer
  ;; before `(dog Fido)`.
  (with-pruning
    (dotimes [_ 4]
      (tu/with-terms [animal dog awake alert calm fed eats Fido Bone CxWorld]
        (a-context kb CxWorld)
        (a-type kb animal CxWorld)
        (doseq [w [awake alert calm fed]]
          (v/assert kb (list 'genl w animal) CxWorld)
          (v/assert-rule kb [(list animal '?x)] (list w '?x) CxWorld {:direction :forward}))
        (v/assert kb (list 'arg eats 1 animal) CxWorld)
        (v/assert kb (list dog Fido) CxWorld)
        (v/assert kb (list eats Fido Bone) CxWorld)
        (is (believed? kb (list animal Fido) CxWorld) "minted while dog reaches no animal")
        (v/assert kb (list 'genl dog animal) CxWorld)
        (is (nil? (v/handle-of kb (list animal Fido) CxWorld)))
        (is (every? #(believed? kb (list % Fido) CxWorld) [awake alert calm fed])
            "each resting subsumer stands on the route through dog")
        (is (v/isa? kb Fido animal CxWorld))))))

(tu/deftest-kb a-withdrawn-mint-returns-with-every-support-it-had
  ;; Two facts entail `(animal Fred)`, so the record leaves only when both justifications
  ;; are blocked and comes back holding both — the count of supports is a property of what
  ;; entails it, never of what moved last.
  (tu/with-terms [animal dog parentOf childOf Fred Mary CxWorld]
    (with-pruning
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (v/assert kb (list 'genl dog animal) CxWorld)
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
      (v/assert kb (list 'arg childOf 1 animal) CxWorld)
      (v/assert kb (list parentOf Fred Mary) CxWorld)
      (v/assert kb (list childOf Fred Mary) CxWorld)
      (is (= 2 (count (:support (v/why kb (entailed kb (list animal Fred) CxWorld))))))
      (v/assert kb (list dog Fred) CxWorld)
      (is (nil? (v/handle-of kb (list animal Fred) CxWorld)) "both supports blocked, record swept")
      (v/retract! kb (v/handle-of kb (list dog Fred) CxWorld))
      (is (= 2 (count (:support (v/why kb (entailed kb (list animal Fred) CxWorld)))))
          "and both are back — each fact holds it up on its own again"))))

(tu/deftest-kb a-record-stored-by-another-route-takes-the-justification
  ;; The mint is withheld, and then the sentence arrives as a premise.  A record is
  ;; justified by everything that entails it, so the declaration's justification lands on
  ;; it.  Retracting the premise leaves the record on that justification alone, a mint
  ;; `(dog Fred)` says more specifically, so it goes as the withheld mint never came: the
  ;; KB holds what the same content without the premise holds, and still answers the type.
  (tu/with-terms [animal dog parentOf Fred Mary CxWorld]
    (with-pruning
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (v/assert kb (list 'genl dog animal) CxWorld)
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
      (v/assert kb (list dog Fred) CxWorld)
      (v/assert kb (list parentOf Fred Mary) CxWorld)
      (is (nil? (v/handle-of kb (list animal Fred) CxWorld)) "withheld")
      (v/retract! kb (v/assert kb (list animal Fred) CxWorld))
      (is (not (believed? kb (list animal Fred) CxWorld))
          "the premise is gone and the specific membership withholds the mint again")
      (is (v/isa? kb Fred animal CxWorld)))))

(tu/deftest-kb a-departure-under-the-switch-owes-its-mint-until-release-withheld
  ;; `special/*release-withheld?*` false is how an open, a recover and a bulk load settle:
  ;; `(dog Fred)` leaving draws nothing and is counted, and `release-withheld!` draws what
  ;; a settle per fact would have drawn at the retraction, in either arrival order
  (doseq [type-first? [true false]]
    (tu/with-terms [animal dog parentOf Fred Mary CxWorld]
      (with-pruning
        (a-context kb CxWorld)
        (a-type kb animal CxWorld)
        (v/assert kb (list 'genl dog animal) CxWorld)
        (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
        (doseq [s (cond-> [(list dog Fred) (list parentOf Fred Mary)] (not type-first?) rseq)]
          (v/assert kb s CxWorld))
        (is (nil? (v/handle-of kb (list animal Fred) CxWorld)))
        (binding [special/*release-withheld?* false]
          (v/retract! kb (v/handle-of kb (list dog Fred) CxWorld)))
        (is (= [1 false] [(v/owed-releases kb) (believed? kb (list animal Fred) CxWorld)])
            (str "type first: " type-first?))
        (is (= [false []] [(v/isa? kb Fred animal CxWorld) (vec (v/query kb (list animal '?x) CxWorld))])
            "an owed mint is missing from isa? and from matching")
        (is (= {:terms 1 :released 1} (select-keys (v/release-withheld! kb) [:terms :released])))
        (is (= [0 true] [(v/owed-releases kb) (believed? kb (list animal Fred) CxWorld)]))
        (is (= [true [{'?x Fred}]] [(v/isa? kb Fred animal CxWorld) (vec (v/query kb (list animal '?x) CxWorld))]))
        (is (= {:terms 0 :released 0} (select-keys (v/release-withheld! kb) [:terms :released]))
            "a second run draws nothing")))))

(tu/deftest-kb a-defeated-membership-gives-the-mint-back
  ;; Belief, not storage, is what withholds: a `(dog Fred)` the KB stops believing
  ;; licenses nothing, so the type it displaced is minted while it is out.
  (tu/with-terms [animal dog parentOf Fred Mary CxWorld]
    (with-pruning
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (v/assert kb (list 'genl dog animal) CxWorld)
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
      (v/assert kb (list dog Fred) CxWorld)
      (v/assert kb (list parentOf Fred Mary) CxWorld)
      (is (nil? (v/handle-of kb (list animal Fred) CxWorld)))
      (v/assert kb (list 'not (list dog Fred)) CxWorld {:strength :monotonic})
      (is (not (v/ask? kb (list dog Fred) CxWorld)) "the specific membership is out")
      (is (believed? kb (list animal Fred) CxWorld) "so the general one is minted"))))

(tu/deftest-kb a-minted-edge-gives-way-to-a-longer-route
  ;; `genlArg` mints a `genl` edge, and an edge a two-edge route already provides says
  ;; nothing the closure does not: `wheel_kind → axle_kind → physical_thing` makes the
  ;; minted `wheel_kind → physical_thing` redundant, and reachability is what a redundant
  ;; edge does not change.
  (tu/with-terms [physical_thing wheel_kind axle_kind partType CxWorld]
    (with-pruning
      (a-context kb CxWorld)
      (a-type kb physical_thing CxWorld)
      (v/assert kb (list 'genl axle_kind physical_thing) CxWorld)
      (v/assert kb (list 'genlArg partType 1 physical_thing) CxWorld)
      (v/assert kb (list partType wheel_kind axle_kind) CxWorld)
      (is (believed? kb (list 'genl wheel_kind physical_thing) CxWorld) "minted")
      (v/assert kb (list 'genl wheel_kind axle_kind) CxWorld)
      (is (nil? (v/handle-of kb (list 'genl wheel_kind physical_thing) CxWorld))
          "withdrawn: the route through axle_kind says it")
      (is (v/genl? kb wheel_kind physical_thing CxWorld) "and the closure still answers"))))

(tu/deftest-kb a-minted-edge-gives-way-to-a-route-a-declaration-installs
  ;; The route of `a-minted-edge-gives-way-to-a-longer-route` with its first edge
  ;; installed by a `separating` declaration rather than stated: `wheel_kind →
  ;; axle_kind` comes from the declaration, `axle_kind → physical_thing` is stated.  The
  ;; declaration's edge is a route like a stated one, so the minted `wheel_kind →
  ;; physical_thing` is withheld when the declaration is there first, withdrawn when it
  ;; arrives second, and drawn again when it leaves.
  (doseq [declaration-first? [true false]]
    (tu/with-neutral-kb [kb tu/fresh]
      (tu/with-terms [physical_thing wheel_kind spoke_kind axle_kind partType CxWorld]
        (with-pruning
          (a-context kb CxWorld)
          (a-type kb physical_thing CxWorld)
          (v/assert kb (list 'genl axle_kind physical_thing) CxWorld)
          (v/assert kb (list 'genlArg partType 1 physical_thing) CxWorld)
          (let [decl   #(v/assert kb (list 'separating axle_kind wheel_kind spoke_kind) CxWorld)
                fact   #(v/assert kb (list partType wheel_kind axle_kind) CxWorld)
                rh     (if declaration-first?
                         (let [h (decl)] (fact) h)
                         (do (fact)
                             (is (believed? kb (list 'genl wheel_kind physical_thing) CxWorld)
                                 "minted while no route holds it")
                             (decl)))]
            (testing (str "declaration " (if declaration-first? "first" "second"))
              (is (nil? (v/handle-of kb (list 'genl wheel_kind physical_thing) CxWorld))
                  "no record: the declaration's edge and the stated one say it")
              (is (v/genl? kb wheel_kind physical_thing CxWorld) "and the closure still answers")
              (v/retract! kb rh)
              (is (believed? kb (list 'genl wheel_kind physical_thing) CxWorld)
                  "the declaration gone, the mint is drawn again"))))))))

(tu/deftest-kb a-query-mints-nothing
  (tu/with-terms [animal parentOf Fred Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
      (let [before (tu/content-count kb)]
        (v/ask kb (list parentOf Fred Mary) CxWorld)
        (v/ask kb (list animal Fred) CxWorld)
        (v/sentexes-matching kb (list parentOf '?x '?y) CxWorld)
        (is (= before (tu/content-count kb)) "asking is not telling")
        (is (nil? (v/handle-of kb (list animal Fred) CxWorld)))))))

(tu/deftest-kb a-type-no-edge-places-mints-and-is-entailed-a-unary-predicate
  ;; `orphan_t` has no `genl` edge and no arity statement.  A type is a unary predicate,
  ;; so the declaration mints `(orphan_t Fred)` and entails `(unary_predicate orphan_t)`,
  ;; each held by what it rests on
  (tu/with-terms [parentOf orphan_t Fred Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (let [dh (v/assert kb (list 'arg parentOf 1 orphan_t) CxWorld)]
        (v/assert kb (list parentOf Fred Mary) CxWorld)
        (is (entailed kb (list orphan_t Fred) CxWorld) "the membership is minted")
        (is (not (v/genl? kb orphan_t 'thing)) "with no path to thing")
        (let [uh (entailed kb (list 'unary_predicate orphan_t) CxWorld)]
          (is uh "the declaration entails the type's unary_predicate membership")
          (is (= #{[dh]} (into #{} (map :antecedents) (v/supporting-justifications kb uh)))
              "justified by the declaration alone"))
        (v/retract! kb dh)
        (is (nil? (entailed kb (list 'unary_predicate orphan_t) CxWorld))
            "retracting the declaration takes the membership back")))))

;; ---- argArg: the type read off the sentence -----------------------------

(tu/deftest-kb an-arg-arg-entails-the-type-the-sentence-names
  (tu/with-terms [kindOf dog Rex CxWorld]
    (a-context kb CxWorld)
    (a-type kb dog CxWorld)
    (let [dh (v/assert kb (list 'argArg kindOf 1 2) CxWorld)]
      (with-entailing
        (let [fh  (v/assert kb (list kindOf Rex dog) CxWorld)
              th  (entailed kb (list dog Rex) CxWorld)
              sup (first (:support (v/why kb th)))]
          (is (some? th) "the type at argument 2 is a stored, believed membership of argument 1")
          (is (= 'argArg (:informant sup)))
          (is (= #{fh dh} (set (map :handle (:because sup))))
              "resting on the fact and the declaration")
          (v/retract! kb dh)
          (is (not (believed? kb (list dog Rex) CxWorld))
              "and retracting the declaration takes the membership back"))))))

(tu/deftest-kb every-arrival-order-of-an-arg-arg-reaches-the-same-belief
  ;; The declaration, the fact, and the retraction of the binding that gives the named
  ;; type two arguments.  With the retraction last the fact names a type that is not
  ;; mintable yet, so it waits on its own handle and is minted when the binding leaves.
  (doseq [order (permutations [:declaration :fact :type])]
    (tu/with-neutral-kb [kb tu/fresh]
      (tu/with-terms [kindOf dog Rex CxWorld]
        (with-entailing
          (a-context kb CxWorld)
          (let [bh (v/assert kb (list 'binary_predicate dog) 'CxUniverse)]
            (doseq [step order]
              (case step
                :declaration (v/assert kb (list 'argArg kindOf 1 2) CxWorld)
                :fact        (v/assert kb (list kindOf Rex dog) CxWorld)
                :type        (v/retract! kb bh))))
          (is (believed? kb (list dog Rex) CxWorld) (str "entailed under " (vec order))))))))

;; `(interArgEqual grants 2 3 1 t)` types argument 1 of the `grants` tuples holding 3 at
;; argument 2 and no other tuple, in every order of the declaration and two tuples, one
;; holding 3 and one holding 4.  The membership rests on the declaration.
(tu/deftest-kb an-inter-arg-equal-types-the-tuples-its-value-triggers-in-every-order
  (doseq [order (permutations [:declaration :three :four])]
    (tu/with-neutral-kb [kb tu/fresh]
      (tu/with-terms [grants t Rex Fido CxWorld]
        (with-entailing
          (a-context kb CxWorld)
          (a-type kb t CxWorld)
          (let [dh (volatile! nil)]
            (doseq [step order]
              (case step
                :declaration (vreset! dh (v/assert kb (list 'interArgEqual grants 2 3 1 t) CxWorld))
                :three       (v/assert kb (list grants Rex 3) CxWorld)
                :four        (v/assert kb (list grants Fido 4) CxWorld)))
            (is (= [true false] (mapv #(believed? kb (list t %) CxWorld) [Rex Fido])) (str (vec order)))
            (is (= 'interArgEqual
                   (:informant (first (:support (v/why kb (v/handle-of kb (list t Rex) CxWorld))))))
                (str (vec order)))
            (v/retract! kb @dh)
            (is (not (believed? kb (list t Rex) CxWorld))
                (str (vec order) " the declaration's retraction takes the membership back"))))))))

;; Under the constraint-only reading a tuple the value triggers is held inert when its
;; argument 1 is separated from the type, in either order, and one holding another value
;; is not.  `try-assert` refuses the later write in either order, under both readings.
(tu/deftest-kb an-inter-arg-equal-convicts-the-tuples-its-value-triggers-in-either-order
  (doseq [entail?      [true false]
          [v refused?] [[3 true] [4 false]]
          decl-first?  [true false]]
    (binding [argument/*assertive-arg-types?* entail?]
      (tu/with-neutral-kb [kb tu/fresh]
        (tu/with-terms [grants t u Rex]
          (doseq [s [(list 'genl t 'thing) (list 'genl u 'thing) (list 'disjoint t u) (list u Rex)]]
            (v/assert kb s 'CxUniverse))
          (let [decl  (list 'interArgEqual grants 2 3 1 t)
                tuple (list grants Rex v)
                [w1 w2] (if decl-first? [decl tuple] [tuple decl])
                tag   (pr-str [entail? v decl-first?])
                _     (v/assert kb w1 'CxUniverse)
                e     (try (v/try-assert kb w2 'CxUniverse) :stored
                           (catch clojure.lang.ExceptionInfo e [(:type (ex-data e)) (:violation (ex-data e))]))]
            (is (= (if refused? [:definitional-clash :arg-type] :stored) e) (str tag " try-assert"))
            (when-not (v/handle-of kb w2 'CxUniverse) (v/assert kb w2 'CxUniverse))
            (is (= (not (and refused? (not entail?)))
                   (boolean (v/believed? kb (v/handle-of kb tuple 'CxUniverse) 'CxUniverse)))
                (str tag " assert holds a convicted tuple inert under the constraint-only reading"))))))))

(tu/deftest-kb an-inter-arg-equal-names-a-value-at-its-trigger
  ;; the equality partition holds symbols only, so a value is the one trigger no merge moves
  (tu/with-terms [grants t HostA]
    (is (= [:not-well-formed :stored]
           (mapv #(try (v/assert kb (list 'interArgEqual grants 2 % 1 t) 'CxUniverse) :stored
                       (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))
                 [HostA "host-a"])))))

;; `(resultArg MemberFn 1)` types the constant `(MemberFn x)` mints by the type `x` names,
;; derived off the `natFormula` fact as an `argArg` mint is off its fact.  A row is the
;; steps in order, the name the application holds, and whether `(name K)` is believed
;; after them.  A name bound to two arguments waits on the fact and mints nothing, and the
;; binding's retraction releases the mint, across a recover too.  An individual's name
;; mints nothing in any order.
(tu/deftest-kb a-result-arg-types-a-minted-constant-in-every-order
  (let [orders (permutations [:declaration :write :type])
        rows   (concat (for [o orders] [o :kind true])
                       (for [o orders] [(concat o [:recover]) :kind true])
                       (for [o orders] [(concat (butlast o) [:recover (last o)]) :kind true])
                       [[[:declaration :type :write :retract] :kind false]
                        [[:declaration :type :write] :individual false]])]
    (doseq [[steps named holds?] rows]
      (tu/with-neutral-kb [kb tu/fresh]
        (tu/with-terms [MemberFn kind studies Alice Bob]
          (tu/with-entailing
            (v/assert kb (list 'reifiable_function MemberFn) 'CxUniverse)
            (v/assert kb (list 'binary_predicate kind) 'CxUniverse)
            (let [t    (if (= :kind named) kind Bob)
                  app  (list MemberFn t)
                  decl (volatile! nil)
                  k    (volatile! nil)]
              (doseq [step steps]
                (case step
                  :declaration (vreset! decl (v/assert kb (list 'resultArg MemberFn 1) 'CxUniverse))
                  :write       (let [h (v/assert kb (list studies Alice app) 'CxUniverse)]
                                 (vreset! k (nth (:sentence (v/sentex kb h)) 2)))
                  :type        (v/retract! kb (v/handle-of kb (list 'binary_predicate kind) 'CxUniverse))
                  :recover     (v/recover kb)
                  :retract     (v/retract! kb @decl)))
              (is (some? (v/handle-of kb (list 'natFormula @k app) 'CxUniverse))
                  (str "the write is stored whole under " (vec steps)))
              (is (= holds? (believed? kb (list t @k) 'CxUniverse))
                  (str (vec steps) " over the " (name named))))))))))

(tu/deftest-kb an-arg-arg-convicts-under-the-constraint-reading
  (tu/with-terms [kindOf dog cat Rex CxWorld]
    (without-entailing
     (a-context kb CxWorld)
     (a-type kb dog CxWorld)
     (a-type kb cat CxWorld)
     (v/assert kb (list 'disjoint dog cat) CxWorld)
     (v/assert kb (list cat Rex) CxWorld)
     (v/assert kb (list 'argArg kindOf 1 2) CxWorld)
     (let [h (v/assert kb (list kindOf Rex dog) CxWorld)
           e (:conviction (v/why-not kb (list kindOf Rex dog) CxWorld))]
       (is (not (v/believed? kb h CxWorld)))
       (is (= [:arg-type dog 1] [(:type e) (:expected e) (:position e)])
           "Rex is a cat, which is disjoint from dog"))
     (is (v/believed? kb (v/assert kb (list kindOf Rex cat) CxWorld) CxWorld)
         "and the sentence naming a type Rex holds is believed"))))

(tu/deftest-kb an-arg-arg-naming-one-position-twice-is-not-well-formed
  (tu/with-terms [kindOf CxWorld]
    (a-context kb CxWorld)
    (is (= :not-well-formed
           (try (v/assert kb (list 'argArg kindOf 1 1) CxWorld) nil
                (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))))

;; ---- the minted type is ordinary content --------------------------------

(tu/deftest-kb a-minted-type-is-a-chaining-seed
  (tu/with-terms [animal mortal parentOf Fred Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (a-type kb mortal CxWorld)
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
      (v/assert-rule kb [(list animal '?x)] (list mortal '?x) CxWorld {:direction :forward})
      (testing "the rule fires off the minted type within the same assert"
        (v/assert kb (list parentOf Fred Mary) CxWorld)
        (is (believed? kb (list mortal Fred) CxWorld))))))

(tu/deftest-kb the-cascade-closes
  ;; A declaration whose own conclusion is constrained: `(rel …)` mints `(t1 x)`, `t1`'s
  ;; own declaration mints `(t2 x)`, and t2's points back at t1 — which is already
  ;; there.  It has to cascade (the retroactive direction does, so the forward one must
  ;; agree), and it has to stop: every mint is find-or-create and every justification is
  ;; content-keyed, so the cycle has nothing new to produce on the second lap.
  (tu/with-terms [t1 t2 rel Fred Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb t1 CxWorld)
      (a-type kb t2 CxWorld)
      (v/assert kb (list 'arg rel 1 t1) CxWorld)
      (v/assert kb (list 'arg t1 1 t2) CxWorld)
      (v/assert kb (list 'arg t2 1 t1) CxWorld)
      (v/assert kb (list rel Fred Mary) CxWorld)
      (is (believed? kb (list t1 Fred) CxWorld))
      (is (believed? kb (list t2 Fred) CxWorld))
      (is (= 1 (count (v/sentexes-with-functor kb t1)))
          "one sentex per type, however many times the cycle is traversed"))))

(tu/deftest-kb the-cascade-crosses-an-argument-that-already-holds-a-type
  ;; The cascade closed only for an argument with no type at all until the symbol arm
  ;; yielded: the mint `(t1 Fred)` re-entered the check, `t1`'s own declaration read Fred
  ;; as typed-and-not-a-`t2`, and the conclusion `(t2 Fred)` would have come from was
  ;; dropped.  `dog` is neither a `t1` nor a `t2` and is disjoint from neither, so under
  ;; the entailment reading it is no obstacle to either mint.
  (tu/with-terms [t1 t2 dog rel Fred Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb t1 CxWorld)
      (a-type kb t2 CxWorld)
      (a-type kb dog CxWorld)
      (v/assert kb (list 'arg rel 1 t1) CxWorld)
      (v/assert kb (list 'arg t1 1 t2) CxWorld)
      (v/assert kb (list dog Fred) CxWorld)
      (v/assert kb (list rel Fred Mary) CxWorld)
      (is (believed? kb (list t1 Fred) CxWorld) "the first link")
      (is (believed? kb (list t2 Fred) CxWorld) "and the second, off the first")
      (testing "each link rests on the one before it, so retracting the fact takes both"
        (v/retract! kb (v/handle-of kb (list rel Fred Mary) CxWorld))
        (is (nil? (v/handle-of kb (list t1 Fred) CxWorld)))
        (is (nil? (v/handle-of kb (list t2 Fred) CxWorld)))))))

(tu/deftest-kb a-unary-declaration-entails-what-genl-would-and-re-asserts-cleanly
  ;; `(arg p1 1 p2)` on a *unary* predicate says what `(genl p1 p2)` says, and the
  ;; conviction reading could not hold it: `(p1 Fred)` types Fred a `p1`, so the identical
  ;; assertion a second time convicted Fred for not being a `p2` — a sentence refused by
  ;; the fact it had itself created.  The entailment reading mints the `p2` instead, which
  ;; is what makes the second assert the no-op it has to be.
  (tu/with-terms [p1 p2 Fred CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb p1 CxWorld)
      (a-type kb p2 CxWorld)
      (v/assert kb (list 'arg p1 1 p2) CxWorld)
      (let [h (v/assert kb (list p1 Fred) CxWorld)]
        (is (believed? kb (list p2 Fred) CxWorld) "the type the declaration entails")
        (is (= h (v/assert kb (list p1 Fred) CxWorld))
            "and the same sentence again is the same handle, not a refusal")))))

(tu/deftest-kb a-mint-clashing-with-a-stored-membership-is-stored-beside-the-fact
  ;; Bert is a `rock`, `rock` and `animal` are disjoint, and the fact's mint `(animal
  ;; Bert)` clashes with the membership.  The clash names a stored member, so the fact
  ;; and its mint are stored and the pair is a nogood the settle decides.  What must not
  ;; happen is storing the fact and dropping the mint, which leaves the KB believing a
  ;; fact whose declared consequence it rejects.
  (tu/with-terms [animal rock parentOf Bert Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (a-type kb rock CxWorld)
      (v/assert kb (list 'disjoint animal rock) CxWorld)
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
      (v/assert kb (list rock Bert) CxWorld)
      (is (some? (v/assert kb (list parentOf Bert Mary) CxWorld)))
      (is (some? (v/handle-of kb (list animal Bert) CxWorld)) "the mint is stored")
      (is (= [#{(v/handle-of kb (list animal Bert) CxWorld)
                (v/handle-of kb (list rock Bert) CxWorld)}]
             (mapv :nogood (v/contradictions kb)))
          "and the two `:default` memberships are a dilemma"))))

(tu/deftest-kb a-clash-between-the-fact-and-its-own-mint-is-stored
  ;; Neither side of this pair is stored when the check runs: `(p1 Fred)` is the sentence
  ;; being asserted and `(p2 Fred)` is what it entails.  The materializer places the mint
  ;; beside the stored sentence, and the settle finds the pair.
  (tu/with-terms [p1 p2 Fred CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb p1 CxWorld)
      (a-type kb p2 CxWorld)
      (v/assert kb (list 'disjoint p1 p2) CxWorld)
      (v/assert kb (list 'arg p1 1 p2) CxWorld)
      (is (some? (v/assert kb (list p1 Fred) CxWorld)))
      (is (= #{p1 p2} (set (v/types-of kb Fred CxWorld))))
      (is (= 1 (count (v/contradictions kb)))))))

(tu/deftest-kb a-clash-between-two-mints-of-one-cascade-is-stored
  ;; Both sides come from the cascade this time, two links apart, and the triggering fact
  ;; is a binary relation that types nothing itself.
  (tu/with-terms [t1 t2 rel Fred Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb t1 CxWorld)
      (a-type kb t2 CxWorld)
      (v/assert kb (list 'disjoint t1 t2) CxWorld)
      (v/assert kb (list 'arg rel 1 t1) CxWorld)
      (v/assert kb (list 'arg t1 1 t2) CxWorld)
      (is (some? (v/assert kb (list rel Fred Mary) CxWorld)))
      (is (= [#{(v/handle-of kb (list t1 Fred) CxWorld)
                (v/handle-of kb (list t2 Fred) CxWorld)}]
             (mapv :nogood (v/contradictions kb)))))))

(tu/deftest-kb try-assert-refuses-a-fact-whose-mint-clashes
  ;; The three clashes the tests above store: a mint against a stored membership, the
  ;; fact against its own mint, and two mints of one cascade.  `try-assert` refuses each,
  ;; and neither the fact nor a mint is stored.  Against a stored membership the refusal
  ;; is the argument conviction, which reads the membership the mint would clash with.
  (doseq [row [:stored :own :cascade]]
    (tu/with-terms [t1 t2 rel Fred Mary CxWorld]
      (with-entailing
        (a-context kb CxWorld)
        (a-type kb t1 CxWorld)
        (a-type kb t2 CxWorld)
        (v/assert kb (list 'disjoint t1 t2) CxWorld)
        (let [fact (case row
                     :stored  (do (v/assert kb (list 'arg rel 1 t1) CxWorld)
                                  (v/assert kb (list t2 Fred) CxWorld)
                                  (list rel Fred Mary))
                     :own     (do (v/assert kb (list 'arg t1 1 t2) CxWorld)
                                  (list t1 Fred))
                     :cascade (do (v/assert kb (list 'arg rel 1 t1) CxWorld)
                                  (v/assert kb (list 'arg t1 1 t2) CxWorld)
                                  (list rel Fred Mary)))
              e    (try (v/try-assert kb fact CxWorld)
                        (catch clojure.lang.ExceptionInfo e (ex-data e)))]
          (testing (name row)
            (is (= (if (= row :stored)
                     [:definitional-clash :arg-type nil]
                     [:definitional-clash :disjoint fact])
                   [(:type e) (:violation e) (:entailed-from e)]))
            (is (nil? (v/handle-of kb fact CxWorld)))
            (is (= (if (= row :stored) #{(list t2 Fred)} #{})
                   (set (filter #(v/handle-of kb % CxWorld) [(list t1 Fred) (list t2 Fred)])))
                "only the memberships the setup wrote are stored")))))))

(defn- outcome
  "`:stored`, or the refusal's `:type`."
  [kb s c]
  (try (v/assert kb s c) :stored
       (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(tu/deftest-kb a-fact-under-an-inherited-declaration-is-stored-before-and-after-its-type
  ;; `Bert` is a `pet` and nothing says a pet is not an animal, so the inherited
  ;; declaration derives `(animal Bert)` beside it and refuses nothing, whether
  ;; `(animal Bert)` is stated before the fact or after it.
  (doseq [order [[:fact :type] [:type :fact]]]
    (tu/with-neutral-kb [kb tu/fresh]
      (tu/with-terms [animal pet parentOf Bert Mary CxUp CxDown]
        (with-entailing
          (v/assert kb (list 'genlCx CxUp 'CxUniverse) 'CxUniverse)
          (v/assert kb (list 'genlCx CxDown CxUp) 'CxUniverse)
          (a-type kb animal CxUp)
          (a-type kb pet CxUp)
          (v/assert kb (list 'arg parentOf 1 animal) CxUp)
          (v/assert kb (list pet Bert) CxDown)
          (let [step {:fact (list parentOf Bert Mary) :type (list animal Bert)}]
            (testing (str order)
              (is (= [:stored :stored] (mapv #(outcome kb (step %) CxDown) order)))
              (is (believed? kb (list parentOf Bert Mary) CxDown))
              (is (believed? kb (list animal Bert) CxDown))
              (is (empty? (v/contradictions kb))))))))))

;; ---- a derived membership under an inherited declaration -------------------
;; `(achieves A B)` under `(genl achieves accomplishes)` and `(arg accomplishes 2 tt)`
;; derives `(tt B)`; `(genl tt assoc)` with `(arg assoc 1 sub)` inherited from `CxUp`
;; derives `(sub B)` from it.

(defn- chain-premises
  "The premises of the derived-membership chain, as `[step sentence context]` rows, every
  step but the facts."
  [{:keys [tt assoc sub accomplishes achieves CxUp CxDown]}]
  [[:up       (list 'genlCx CxUp 'CxUniverse) 'CxUniverse]
   [:cx       (list 'genlCx CxDown CxUp) 'CxUniverse]
   [:types    (list 'genl assoc 'thing) 'CxUniverse]
   [:types    (list 'genl tt assoc) 'CxUniverse]
   [:types    (list 'genl sub 'thing) 'CxUniverse]
   [:sub-decl (list 'arg assoc 1 sub) CxUp]
   [:pred     (list 'genl achieves accomplishes) 'CxUniverse]
   [:acc-decl (list 'arg accomplishes 2 tt) CxDown]])

(defn- chain-terms
  "Fresh terms for the chain, keyed by name."
  []
  (tu/with-terms [tt assoc sub accomplishes achieves Ann Bee Cal Dee CxUp CxDown]
    {:tt tt :assoc assoc :sub sub :accomplishes accomplishes :achieves achieves
     :Ann Ann :Bee Bee :Cal Cal :Dee Dee :CxUp CxUp :CxDown CxDown}))

(tu/deftest-kb two-facts-deriving-one-membership-are-both-stored-in-either-order
  (doseq [order [[:ann :dee] [:dee :ann]]]
    (tu/with-neutral-kb [kb tu/fresh]
      (let [{:keys [tt sub achieves Ann Bee Dee CxDown] :as t} (chain-terms)]
        (with-entailing
          (doseq [[_ s c] (chain-premises t)] (v/assert kb s c))
          (let [subject {:ann Ann :dee Dee}
                got     (mapv #(outcome kb (list achieves (subject %) Bee) CxDown) order)]
            (testing (str order)
              (is (= [:stored :stored] got))
              (is (believed? kb (list tt Bee) CxDown))
              (is (believed? kb (list sub Bee) CxDown)
                  "the inherited declaration derives over the derived membership")
              (is (= 2 (count (:support (v/why kb (v/handle-of kb (list tt Bee) CxDown)))))))))))))

(tu/deftest-kb a-stored-membership-re-asserts-as-it-first-asserted
  (tu/with-neutral-kb [kb tu/fresh]
    (let [{:keys [tt sub Bee CxDown] :as t} (chain-terms)]
      (with-entailing
        (doseq [[_ s c] (chain-premises t)] (v/assert kb s c))
        (is (= [:stored :stored] [(outcome kb (list tt Bee) CxDown)
                                  (outcome kb (list tt Bee) CxDown)]))
        (is (believed? kb (list sub Bee) CxDown))))))

(defn- inherited-chain-results
  "Per order of the two declarations, the predicate edge, the context edge and the fact:
  `(tt Bee)` and `(sub Bee)` believed once all have arrived, and again after the context
  edge is retracted."
  [orders]
  (for [order orders]
    (tu/with-neutral-kb [kb tu/fresh]
      (let [{:keys [tt sub achieves Ann Bee CxUp CxDown] :as t} (chain-terms)]
        (with-entailing
          (let [rows (group-by first (chain-premises t))]
            (doseq [[_ s c] (concat (rows :up) (rows :types))] (v/assert kb s c))
            (doseq [step order]
              (if (= :fact step)
                (v/assert kb (list achieves Ann Bee) CxDown)
                (doseq [[_ s c] (rows step)] (v/assert kb s c))))
            (let [standing {:tt  (believed? kb (list tt Bee) CxDown)
                            :sub (believed? kb (list sub Bee) CxDown)}]
              (v/retract! kb (v/handle-of kb (list 'genlCx CxDown CxUp) 'CxUniverse))
              [order [standing {:tt  (believed? kb (list tt Bee) CxDown)
                                :sub (some? (v/handle-of kb (list sub Bee) CxDown))}]])))))))

(def ^:private chain-orders (permutations [:cx :sub-decl :pred :acc-decl :fact]))

(defn- one-reading?
  "Every order reached the KB that derives both memberships, and retracting the context
  edge took back only the one derived through the declaration it made visible."
  [results]
  (let [want [{:tt true :sub true} {:tt true :sub false}]]
    (is (= #{want} (set (map second results)))
        (str "the derivations varied by arrival order: "
             (pr-str (take 4 (remove #(= want (second %)) results)))))))

(tu/deftest-kb ^:slow every-arrival-order-derives-through-an-inherited-declaration
  ;; All 120 orders.
  (one-reading? (inherited-chain-results chain-orders)))

(tu/deftest-kb sampled-arrival-orders-derive-through-an-inherited-declaration
  ;; The sampled twin: every tenth order, the context edge first and last among them.
  (one-reading? (inherited-chain-results (take-nth 10 chain-orders))))

(defn- loaded-reading
  "The chain's facts loaded with `bulk-assert-facts!`, then `record-arg-types` when
  `record?`; then the stored `(tt Bee)` and `(sub Bee)`, and the check of `(achieves Dee
  Bee)`, before and after `(achieves Cal Bee)` is added and retracted."
  [record?]
  (tu/with-neutral-kb [kb tu/fresh]
    (let [{:keys [tt sub achieves Ann Bee Cal Dee CxDown] :as t} (chain-terms)]
      (with-entailing
        (doseq [[_ s c] (chain-premises t)] (v/assert kb s c))
        (v/bulk-assert-facts! kb [(list achieves Ann Bee)] CxDown)
        (when record? (v/record-arg-types kb))
        (let [read (fn [] {:tt    (some? (v/handle-of kb (list tt Bee) CxDown))
                           :sub   (some? (v/handle-of kb (list sub Bee) CxDown))
                           :check (mapv :type (v/check kb (list achieves Dee Bee) CxDown))})
              before (read)]
          (v/retract! kb (v/assert kb (list achieves Cal Bee) CxDown))
          [before (read)])))))

(tu/deftest-kb a-bulk-loaded-store-records-its-derivations-once
  ;; Without the pass the store lacks `(tt Bee)` and a write's add-and-remove cycle draws
  ;; it; after the pass the store holds what a per-fact load holds and the cycle changes
  ;; nothing.
  (let [per-fact (tu/with-neutral-kb [kb tu/fresh]
                   (let [{:keys [tt sub achieves Ann Bee Dee CxDown] :as t} (chain-terms)]
                     (with-entailing
                       (doseq [[_ s c] (chain-premises t)] (v/assert kb s c))
                       (v/assert kb (list achieves Ann Bee) CxDown)
                       {:tt    (some? (v/handle-of kb (list tt Bee) CxDown))
                        :sub   (some? (v/handle-of kb (list sub Bee) CxDown))
                        :check (mapv :type (v/check kb (list achieves Dee Bee) CxDown))})))]
    (is (= {:tt false :sub false :check []} (first (loaded-reading false)))
        "the bulk load skips the derivations")
    (is (= [per-fact per-fact] (loaded-reading true)))))

(tu/deftest-kb a-bulk-loaded-declaration-and-edge-draw-nothing-until-recorded
  ;; The fact is stored first, so the declaration and the predicate edge are the arrivals
  ;; that draw `(tt Bee)` and `(sub Bee)`.
  (let [reading (fn [record?]
                  (tu/with-neutral-kb [kb tu/fresh]
                    (let [{:keys [tt sub achieves Ann Bee CxDown] :as t} (chain-terms)]
                      (with-entailing
                        (v/assert kb (list achieves Ann Bee) CxDown)
                        (binding [v/*bulk-load?* true]
                          (doseq [[_ s c] (chain-premises t)] (v/assert kb s c)))
                        (when record? (v/record-arg-types kb))
                        {:tt  (some? (v/handle-of kb (list tt Bee) CxDown))
                         :sub (some? (v/handle-of kb (list sub Bee) CxDown))}))))]
    (is (= {:tt false :sub false} (reading false)))
    (is (= {:tt true :sub true} (reading true)))))

(tu/deftest-kb a-bulk-loaded-genlCx-edge-draws-nothing-until-recorded
  ;; Every other premise and the fact are stored first, so the `genlCx` edge that shows
  ;; `CxUp`'s declaration to `CxDown` is the arrival that draws `(sub Bee)`, in the settle
  ;; that drains it: the batch's closing settle when `deferred?`, the assert's own when not.
  (doseq [deferred? [true false]]
    (let [reading (fn [bulk? record?]
                    (tu/with-neutral-kb [kb tu/fresh]
                      (let [{:keys [sub achieves Ann Bee CxDown] :as t} (chain-terms)
                            ps          (chain-premises t)
                            [_ edge cx] (first (filter #(= :cx (first %)) ps))]
                        (with-entailing
                          (doseq [[_ s c] (remove #(= :cx (first %)) ps)] (v/assert kb s c))
                          (v/assert kb (list achieves Ann Bee) CxDown)
                          (binding [v/*bulk-load?* bulk?]
                            (if deferred?
                              (v/with-deferred-settle kb (v/assert kb edge cx))
                              (v/assert kb edge cx)))
                          (when record? (v/record-arg-types kb))
                          (some? (v/handle-of kb (list sub Bee) CxDown))))))]
      (testing (str "deferred? " deferred?)
        (is (= [true false true]
               [(reading false false) (reading true false) (reading true true)]))))))

(tu/deftest-kb record-arg-types-is-idempotent
  (tu/with-neutral-kb [kb tu/fresh]
    (let [{:keys [achieves Ann Bee CxDown] :as t} (chain-terms)]
      (with-entailing
        (doseq [[_ s c] (chain-premises t)] (v/assert kb s c))
        (v/bulk-assert-facts! kb [(list achieves Ann Bee)] CxDown)
        (is (= 2 (:recorded (v/record-arg-types kb))))
        (is (= 0 (:recorded (v/record-arg-types kb))))))))

(tu/deftest-kb a-symmetric-fact-derives-at-its-stored-positions-in-either-spelling
  ;; Both spellings of a `symmetric` fact store as one sentex in sorted order, and each
  ;; argument's type rests on the declaration of the position it is stored at, so the two
  ;; spellings store the same justifications and `record-arg-types` adds none to either.
  (let [support (fn [written]
                  (tu/with-neutral-kb [kb tu/fresh]
                    (tu/with-terms [t rel Abe Zed CxWorld]
                      (a-type kb t CxWorld)
                      (a-context kb CxWorld)
                      (v/assert kb (list 'symmetric rel) CxWorld)
                      (v/assert kb (list 'arg rel 1 t) CxWorld)
                      (v/assert kb (list 'arg rel 2 t) CxWorld)
                      (with-entailing
                        (v/assert kb (written rel Abe Zed) CxWorld)
                        (let [read (fn []
                                     (into {}
                                           (for [[k x] {:abe Abe :zed Zed}]
                                             [k (mapv (fn [j] (mapv #(v/sentence-of (v/sentex kb %))
                                                                    (rest (:antecedents j))))
                                                      (v/supporting-justifications
                                                       kb (v/handle-of kb (list t x) CxWorld)))])))
                              loaded (read)]
                          (v/record-arg-types kb)
                          [(update-vals loaded #(mapv (fn [antes] (mapv (juxt first (fn [d] (nth d 2))) antes)) %))
                           (= loaded (read))])))))]
    (is (= (support (fn [r a z] (list r a z)))
           (support (fn [r a z] (list r z a)))))
    (is (true? (second (support (fn [r a z] (list r z a))))))))

(tu/deftest-kb a-type-bound-to-another-length-mints-nothing-and-records-nothing
  ;; `t` is declared binary, so `(t Rex)` would be a tuple of a length its binding denies:
  ;; `arity/mintable-type?` reads `t`'s arity and the declaration mints nothing.  No
  ;; refusal reads a binding (docs/taxonomy.md, "Arity"): the fact stands, and the
  ;; refusal record holds nothing for the declaration.  The binding leaving mints.
  (tu/with-terms [t rel Rex Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb t CxWorld)
      (let [bh (v/assert kb (list 'binary_predicate t) CxWorld)
            dh (v/assert kb (list 'arg rel 1 t) CxWorld)]
        (v/assert kb (list rel Rex Mary) CxWorld)
        (is (v/ask? kb (list rel Rex Mary) CxWorld) "the fact stands")
        (is (nil? (v/handle-of kb (list t Rex) CxWorld)) "no membership in t is stored")
        (is (nil? (get @(reasoning/refused kb) dh)) "nothing is recorded")
        (v/retract! kb bh)
        (is (some? (v/handle-of kb (list t Rex) CxWorld)) "the binding leaving mints"))))
  (testing "with the entailment off, the constraint reading admits it — Rex is untyped"
    (tu/with-terms [t rel Rex Mary CxWorld]
      (without-entailing
       (a-context kb CxWorld)
       (a-type kb t CxWorld)
       (v/assert kb (list 'binary_predicate t) CxWorld)
       (v/assert kb (list 'arg rel 1 t) CxWorld)
       (is (some? (v/assert kb (list rel Rex Mary) CxWorld)))))))

(tu/deftest-kb a-type-bound-to-another-length-mints-nothing-on-the-derivation-path
  ;; The same declaration, reached by a rule firing instead of by a caller: the
  ;; conclusion stands and mints nothing, as at the entry point, with nothing in the
  ;; ledger.
  (tu/with-terms [t rel trigger Rex Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb t CxWorld)
      (v/assert kb (list 'binary_predicate t) CxWorld)
      (v/assert kb (list 'arg rel 1 t) CxWorld)
      (v/assert-rule kb [(list trigger '?x '?y)] (list rel '?x '?y) CxWorld {:direction :forward})
      (v/clear-violations! kb)
      (v/assert kb (list trigger Rex Mary) CxWorld)
      (is (some? (v/handle-of kb (list rel Rex Mary) CxWorld))
          "the conclusion stands")
      (is (nil? (v/handle-of kb (list t Rex) CxWorld)) "no membership in t is stored")
      (is (empty? (v/violations kb))))))

(tu/deftest-kb a-declaration-arriving-over-stored-facts-closes-the-whole-chain
  ;; The retroactive direction has to reach as far as the forward one, or which order the
  ;; three declarations arrived in decides how many links the KB ends up holding.
  ;; `entail-existing` walks the stored facts and each mint draws its own entailments, so
  ;; the chain closes from either end.
  (tu/with-terms [t1 t2 t3 rel Fred Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb t1 CxWorld)
      (a-type kb t2 CxWorld)
      (a-type kb t3 CxWorld)
      (v/assert kb (list rel Fred Mary) CxWorld)
      (v/assert kb (list 'arg t1 1 t2) CxWorld)
      (v/assert kb (list 'arg t2 1 t3) CxWorld)
      (v/assert kb (list 'arg rel 1 t1) CxWorld)
      (is (believed? kb (list t1 Fred) CxWorld))
      (is (believed? kb (list t2 Fred) CxWorld))
      (is (believed? kb (list t3 Fred) CxWorld) "the far end, reached by the last arrival"))))

(tu/deftest-kb retracting-a-middle-declaration-takes-the-link-below-it
  ;; Each link is justified by the link above it and its own declaration, so the cascade
  ;; comes apart where the support goes and nowhere else.
  (tu/with-terms [t1 t2 rel Fred Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb t1 CxWorld)
      (a-type kb t2 CxWorld)
      (v/assert kb (list 'arg rel 1 t1) CxWorld)
      (v/assert kb (list 'arg t1 1 t2) CxWorld)
      (v/assert kb (list rel Fred Mary) CxWorld)
      (is (believed? kb (list t2 Fred) CxWorld))
      (v/retract! kb (v/handle-of kb (list 'arg t1 1 t2) CxWorld))
      (is (nil? (v/handle-of kb (list t2 Fred) CxWorld)) "the link the declaration held")
      (is (believed? kb (list t1 Fred) CxWorld) "and only that one"))))

(tu/deftest-kb a-mint-clashing-with-a-membership-is-stored-in-either-order
  ;; The entry point stores the fact whichever of the fact and the declaration arrives
  ;; second, and the mint's clash with the membership is weighed at settle, as a rule's
  ;; conclusion is: two `:default` members are a dilemma.
  (letfn [(run [order]
            (tu/with-neutral-kb [kb tu/fresh]
              (tu/with-terms [p_a p_b rel Bert Mary CxWorld]
                (with-entailing
                  (a-context kb CxWorld)
                  (a-type kb p_a CxWorld)
                  (a-type kb p_b CxWorld)
                  (v/assert kb (list 'disjoint p_a p_b) CxWorld)
                  (v/assert kb (list p_b Bert) CxWorld)
                  (doseq [step order]
                    (case step
                      :decl (v/assert kb (list 'arg rel 1 p_a) CxWorld)
                      :fact (v/assert kb (list rel Bert Mary) CxWorld)))
                  {:fact  (some? (v/handle-of kb (list rel Bert Mary) CxWorld))
                   :mint  (believed? kb (list p_a Bert) CxWorld)
                   :clash (count (v/contradictions kb))}))))]
    (is (= {:fact true :mint true :clash 1} (run [:decl :fact])))
    (is (= {:fact true :mint true :clash 1} (run [:fact :decl])))))

(defn- mint-clash
  "Belief in the fact, the mint and the membership, and the contradictions count, after
  `order`, with `(coll_t Foo)` at `strength` and `coll_t`/`rel_t`
  disjoint at `:monotonic`."
  [order strength]
  (tu/with-neutral-kb [kb #(v/open-kb (tu/scratch-space))]
    (tu/with-terms [rel_t coll_t pp Foo Bar]
      (with-entailing
        (doseq [s [(list 'genl rel_t 'thing) (list 'genl coll_t 'thing) (list 'disjoint rel_t coll_t)]]
          (v/assert kb s 'CxUniverse {:strength :monotonic}))
        (doseq [step order]
          (case step
            :member (v/assert kb (list coll_t Foo) 'CxUniverse {:strength strength})
            :decl   (v/assert kb (list 'arg pp 1 rel_t) 'CxUniverse)
            :fact   (v/assert kb (list pp Foo Bar) 'CxUniverse)))
        {:fact   (believed? kb (list pp Foo Bar) 'CxUniverse)
         :mint   (believed? kb (list rel_t Foo) 'CxUniverse)
         :member (believed? kb (list coll_t Foo) 'CxUniverse)
         :clash  (count (v/contradictions kb))}))))

(tu/deftest-kb a-minted-membership-clashing-with-a-believed-one-is-weighed-at-settle
  ;; The mint is placed and the pair is arbitrated as two stated memberships are: an
  ;; equal `:default` pair stays believed and is listed, a `:monotonic` membership takes
  ;; the `:default` mint OUT.  The same in every arrival order.
  (doseq [[strength want] [[:default   {:fact true :mint true :member true :clash 1}]
                           [:monotonic {:fact true :mint false :member true :clash 0}]]
          order [[:member :decl :fact] [:decl :fact :member] [:member :fact :decl]]]
    (testing (str strength " " order)
      (is (= want (mint-clash order strength))))))

(tu/deftest-kb a-derived-declaration-mints-what-its-text-reload-mints
  ;; A declaration a forward rule derives reaches the stored facts through
  ;; `entail-existing`, after the clashing membership is believed; the text export
  ;; reloads the same content in content order, where the declaration is derived before
  ;; the fact arrives.  The two hold the same sentences and believe the same ones.  arg
  ;; is forced-monotonic, so the rule concluding it reads a forced-monotonic marker
  ;; too: a firing from an antecedent off it would be void.
  (let [build #(tu/isolated-fresh)
        dir   (.toFile (Files/createTempDirectory "argtype-clash" (make-array FileAttribute 0)))
        rows  (fn [kb pick]
                (set (for [h (v/handles kb) :when (pick h)
                           :let [sx (v/sentex kb h)]]
                       (tu/handle-free kb [(v/sentence-of sx) (:context sx)]))))
        seen  (fn [kb] [(rows kb any?) (rows kb #(v/in? kb %))])]
    (try
      (tu/with-terms [rel_t coll_t pp marked Foo Bar]
        (with-entailing
          (let [chained (tu/with-cleared-kb [kb build]
                          (doseq [s [(list 'forced_monotonic_predicate marked)
                                     (list 'genl rel_t 'thing) (list 'genl coll_t 'thing)
                                     (list 'disjoint rel_t coll_t) (list coll_t Foo)
                                     (list pp Foo Bar) (list marked pp)
                                     (list 'set/forwardRule
                                           (list 'implies (list marked '?p) (list 'arg '?p 1 rel_t)))]]
                            (v/assert kb s 'CxUniverse))
                          (v/export-text! kb (.getPath dir))
                          (seen kb))
                reloaded (tu/with-cleared-kb [kb build]
                           (v/load-text! kb (.getPath dir))
                           (seen kb))]
            (is (contains? (first chained) [(list rel_t Foo) 'CxUniverse]))
            (is (= reloaded chained)))))
      (finally
        (run! #(io/delete-file % true) (reverse (file-seq dir)))))))

(tu/deftest-kb a-clash-the-asserting-context-cannot-see-is-no-clash-there
  ;; The mint is placed in the asserting context and tested against what that context
  ;; sees, so a disjointness declared in a context this one does not reach convicts
  ;; nothing here (docs/contexts.md).
  (tu/with-terms [p_a p_b rel Bert Mary CxLeft CxRight]
    (with-entailing
      (v/assert kb (list 'genlCx CxLeft 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxRight 'CxUniverse) 'CxUniverse)
      (a-type kb p_a 'CxUniverse)
      (a-type kb p_b 'CxUniverse)
      (v/assert kb (list 'arg rel 1 p_a) 'CxUniverse)
      (v/assert kb (list p_b Bert) 'CxUniverse)
      (v/assert kb (list 'disjoint p_a p_b) CxLeft)
      (testing "the sibling that cannot see the disjointness mints with no clash"
        (is (some? (v/assert kb (list rel Bert Mary) CxRight)))
        (is (believed? kb (list p_a Bert) CxRight))
        (is (empty? (v/contradictions kb))))
      (testing "and the one that can see it stores the fact and a dilemma"
        (is (some? (v/assert kb (list rel Bert 'TmpOther) CxLeft)))
        (is (= 1 (count (v/contradictions kb))))))))

;; ---- placement at the most general contexts that see both ------------------
;; CxTop sits under CxUniverse, CxMid under CxTop and CxLow under CxMid; CxL and CxR
;; sit under CxTop and join in CxJoin.  Each row states `(P A B)` in one context and
;; `(arg P 1 tt)` in others, and holds back one `genlCx` edge, which arrives in every
;; position of the order and is retracted at the end.

(def ^:private placement-graph
  [[:top :universe] [:mid :top] [:low :mid] [:l :top] [:r :top] [:join :l] [:join :r]])

(def ^:private placement-rows
  ;; fact context, declaration contexts, the edge held back, placements with it,
  ;; placements once it is retracted
  [[:top [:mid]  [:mid :top]  #{:mid}    #{}]
   [:mid [:top]  [:mid :top]  #{:mid}    #{}]
   ;; with CxL off CxTop, CxJoin sees CxTop through CxR and CxL directly
   [:top [:l :r] [:l :top]    #{:l :r}   #{:r :join}]
   [:l   [:r]    [:join :r]   #{:join}   #{}]
   [:l   [:r]    [:r :l]      #{:r}      #{:join}]])

(defn- placement-readings
  "Per order of the fact, the declarations and the held-back edge of `row`: the contexts
  storing a believed `(tt A)`, whether every context at or below one of them reads it
  and no other context does, and the contexts storing it once the edge is retracted."
  [[fact-cx decl-cxs held _ _]]
  (for [order (permutations (into [:fact :edge] (map-indexed (fn [i _] i) decl-cxs)))]
    (tu/with-neutral-kb [kb tu/fresh]
      (tu/with-terms [rel tt A B CxTop CxMid CxLow CxL CxR CxJoin]
        (with-entailing
          (let [cx    {:universe 'CxUniverse :top CxTop :mid CxMid :low CxLow
                       :l CxL :r CxR :join CxJoin}
                edge  (fn [[s g]] (list 'genlCx (cx s) (cx g)))
                ctxs  (dissoc cx :universe)
                mint  (list tt A)
                where (fn [] (into #{} (keep (fn [[k c]] (when (entailed kb mint c) k))) ctxs))]
            (doseq [e (remove #{held} placement-graph)] (v/assert kb (edge e) 'CxUniverse))
            (a-type kb tt 'CxUniverse)
            (doseq [step order]
              (case step
                :fact (v/assert kb (list rel A B) (cx fact-cx))
                :edge (v/assert kb (edge held) 'CxUniverse)
                (v/assert kb (list 'arg rel 1 tt) (cx (nth decl-cxs step)))))
            (let [placed (where)
                  tax    (reasoning/taxonomy kb)
                  reads  (every? (fn [[_ c]]
                                   (= (boolean (some #(tax/sees? tax c (cx %)) placed))
                                      (v/isa? kb A tt c)))
                                 ctxs)]
              (v/retract! kb (v/handle-of kb (edge held) 'CxUniverse))
              [order placed reads (where)])))))))

(tu/deftest-kb a-mint-is-placed-at-the-most-general-contexts-that-see-the-fact-and-the-declaration
  (doseq [[fact-cx decl-cxs held want after :as row] placement-rows
          [order placed reads retracted] (placement-readings row)]
    (testing (pr-str [fact-cx decl-cxs held order])
      (is (= want placed))
      (is reads "a context reads the mint exactly when it sees a placement")
      (is (= after retracted)))))

;; CxL and CxR sit under CxTop, and CxJ and CxK each under both.  `(genlCx CxK CxJ)` makes
;; CxJ the one maximal common descendant of CxL and CxR while it stands.  With pruning on,
;; `(dog A)` in CxJ withholds the mint there and not in CxK.

(tu/deftest-kb a-genlCx-edge-leaving-places-the-mint-at-the-common-descendants-it-gives-back
  (doseq [[prune? dog? want] [[false false #{:j :k}] [true false #{:j :k}]
                              [true true #{:k}] [false true #{:j :k}]]]
    (let [readings
          (for [order (cons [:fact :decl]
                            (filter #(< (.indexOf ^java.util.List % :edge)
                                        (.indexOf ^java.util.List % :unedge))
                                    (permutations [:fact :decl :edge :unedge])))]
            (tu/with-neutral-kb [kb tu/fresh]
              (tu/with-terms [rel tt dog A B CxTop CxL CxR CxJ CxK]
                (binding [argument/*assertive-arg-types?*  true
                          checks/*prune-subsumed-mints?* prune?]
                  (let [edge (list 'genlCx CxK CxJ)]
                    (doseq [[s g] [[CxTop 'CxUniverse] [CxL CxTop] [CxR CxTop]
                                   [CxJ CxL] [CxJ CxR] [CxK CxL] [CxK CxR]]]
                      (v/assert kb (list 'genlCx s g) 'CxUniverse))
                    (a-type kb tt 'CxUniverse)
                    (when dog?
                      (v/assert kb (list 'genl dog tt) 'CxUniverse)
                      (v/assert kb (list dog A) CxJ))
                    (doseq [step order]
                      (case step
                        :fact   (v/assert kb (list rel A B) CxL)
                        :decl   (v/assert kb (list 'arg rel 1 tt) CxR)
                        :edge   (v/assert kb edge 'CxUniverse)
                        :unedge (v/retract! kb (v/handle-of kb edge 'CxUniverse))))
                    [order
                     (into #{} (keep (fn [[k c]] (when (believed? kb (list tt A) c) k)))
                           {:l CxL :r CxR :j CxJ :k CxK})
                     (v/isa? kb A tt CxK)])))))]
      (testing (pr-str [prune? dog?])
        (is (= #{[want true]} (set (map rest readings)))
            (pr-str (remove #(= [want true] (rest %)) readings)))))))

(tu/deftest-kb a-route-edge-or-trigger-below-the-placement-places-the-mint-where-it-is-seen
  ;; The fact and the declaration are in CxTop.  The ingredient a row names, a `genl` route
  ;; from the fact's predicate to the declared one or the trigger membership an `interArg`
  ;; waits on, is stated in CxMid below them, so CxMid is the one context that draws the
  ;; mint; stated in CxTop as well, it places the mint there.  The ingredient is then
  ;; retracted, CxTop's first.
  (doseq [prune? [true false]
          kind [:route :trigger]
          [cxs want after] [[[:mid] #{:mid} [#{}]]
                            [[:mid :top] #{:top} [#{:mid} #{}]]]]
    (let [readings
          (for [order (permutations (into [:fact :decl] cxs))]
            (tu/with-neutral-kb [kb tu/fresh]
              (tu/with-terms [rel sup tt carnivore A B CxTop CxMid]
                (binding [argument/*assertive-arg-types?*  true
                          checks/*prune-subsumed-mints?* prune?]
                  (v/assert kb (list 'genlCx CxTop 'CxUniverse) 'CxUniverse)
                  (v/assert kb (list 'genlCx CxMid CxTop) 'CxUniverse)
                  (a-type kb tt 'CxUniverse)
                  (a-type kb carnivore 'CxUniverse)
                  (let [cx    {:top CxTop :mid CxMid}
                        [ingredient decl mint]
                        (case kind
                          :route   [(list 'genl rel sup) (list 'arg sup 1 tt) (list tt A)]
                          :trigger [(list carnivore A) (list 'interArg rel 1 carnivore 2 tt)
                                    (list tt B)])
                        x     (second mint)
                        where (fn [] (into #{} (keep (fn [[k c]] (when (believed? kb mint c) k))) cx))
                        reads (fn []
                                (every? (fn [[_ c]]
                                          (let [r (boolean (some #(tax/sees? (reasoning/taxonomy kb) c (cx %))
                                                                 (where)))]
                                            (= [r r] [(v/ask? kb mint c) (v/isa? kb x tt c)])))
                                        cx))]
                    (doseq [step order]
                      (case step
                        :fact (v/assert kb (list rel A B) CxTop)
                        :decl (v/assert kb decl CxTop)
                        (v/assert kb ingredient (cx step))))
                    (let [held [(where) (reads)]]
                      [order held
                       (vec (for [c (sort-by #(if (= :top %) 0 1) cxs)]
                              (do (v/retract! kb (v/handle-of kb ingredient (cx c)))
                                  [(where) (reads)])))]))))))]
      (testing (pr-str [prune? kind cxs])
        (is (= #{[[want true] (mapv #(vector % true) after)]} (set (map rest readings)))
            (pr-str readings))))))

(tu/deftest-kb an-except-at-the-placement-places-the-mint-where-the-fact-is-given-back
  ;; CxTop > CxMid > CxLow.  `(rel A B)` is in CxTop and `(arg rel 1 tt)` in the row's
  ;; declaration context, which is the mint's placement; an `except` of the fact there
  ;; hides it, and an `except` of that `except` in CxLow gives it back.  Then either `except`
  ;; is retracted.
  (doseq [[decl-cx want gone-inner gone-outer] [[:mid #{:low} #{} #{:mid}]
                                                [:top #{:low} #{} #{:top}]]
          leave [:inner :outer]]
    (let [readings
          (for [order (filter #(< (.indexOf ^java.util.List % :fact)
                                  (.indexOf ^java.util.List % :ex1)
                                  (.indexOf ^java.util.List % :ex2))
                              (permutations [:fact :decl :ex1 :ex2]))]
            (tu/with-neutral-kb [kb tu/fresh]
              (tu/with-terms [rel tt A B CxTop CxMid CxLow]
                (with-entailing
                  (v/assert kb (list 'genlCx CxTop 'CxUniverse) 'CxUniverse)
                  (v/assert kb (list 'genlCx CxMid CxTop) 'CxUniverse)
                  (v/assert kb (list 'genlCx CxLow CxMid) 'CxUniverse)
                  (a-type kb tt 'CxUniverse)
                  (let [cx    {:top CxTop :mid CxMid :low CxLow}
                        fact  (list rel A B)
                        mint  (list tt A)
                        ex    (fn [h] (list 'except (list 'sentexHandle h)))
                        ex1   #(ex (v/handle-of kb fact CxTop))
                        ex2   #(ex (v/handle-of kb (ex1) (cx decl-cx)))
                        where (fn [] (into #{} (keep (fn [[k c]] (when (believed? kb mint c) k))) cx))
                        reads (fn []
                                (every? (fn [[_ c]]
                                          (let [r (boolean (some #(tax/sees? (reasoning/taxonomy kb) c (cx %))
                                                                 (where)))]
                                            (= [r r] [(v/ask? kb mint c) (v/isa? kb A tt c)])))
                                        cx))]
                    (doseq [step order]
                      (case step
                        :fact (v/assert kb fact CxTop)
                        :decl (v/assert kb (list 'arg rel 1 tt) (cx decl-cx))
                        :ex1  (v/assert kb (ex1) (cx decl-cx))
                        :ex2  (v/assert kb (ex2) CxLow)))
                    (let [held [(where) (reads)]]
                      (if (= :inner leave)
                        (v/retract! kb (v/handle-of kb (ex2) CxLow))
                        (v/retract! kb (v/handle-of kb (ex1) (cx decl-cx))))
                      [order held [(where) (reads)]]))))))
          after (if (= :inner leave) gone-inner gone-outer)]
      (testing (pr-str [decl-cx leave])
        (is (= #{[[want true] [after true]]} (set (map rest readings)))
            (pr-str readings))))))

;; ---- genlArg -------------------------------------------------------------

(tu/deftest-kb genlArg-entails-a-genl-edge
  (tu/with-terms [physical_object partType wheel_kind axle_kind CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb physical_object CxWorld)
      (v/assert kb (list 'genlArg partType 1 physical_object) CxWorld)
      (v/assert kb (list partType wheel_kind axle_kind) CxWorld)
      (is (v/genl? kb wheel_kind physical_object)
          "the argument named a kind of physical object, and now the taxonomy says so")
      (testing "and the edge is held by its supporters like any other entailment"
        (v/retract! kb (v/handle-of kb (list partType wheel_kind axle_kind) CxWorld))
        (is (not (v/genl? kb wheel_kind physical_object)))))))

(tu/deftest-kb an-individual-in-an-genlArg-position-is-convicted-not-given-an-edge
  (tu/with-terms [physical_object partType Wheel axle_kind CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb physical_object CxWorld)
      (v/assert kb (list 'genlArg partType 1 physical_object) CxWorld)
      (let [h (v/assert kb (list partType Wheel axle_kind) CxWorld)
            w (v/why-not kb (list partType Wheel axle_kind) CxWorld)]
        (is (not (v/believed? kb h CxWorld)))
        (is (= [:inert :arg-genl] [(:reason w) (-> w :conviction :type)]))
        (is (re-find #"never be a subtype" (-> w :conviction :message))))
      (is (not (v/genl? kb Wheel physical_object))))))

(tu/deftest-kb a-position-typed-thing-mints-nothing
  ;; A membership in `thing`, or an edge to it, says nothing about a term, so a
  ;; declaration typing a position `thing` derives nothing in either reading, leaves no
  ;; waiting entry, and is named by the quality report.  `(genl thing thing)` is
  ;; not-well-formed, so `thing` in the position records no violation either.
  (tu/with-terms [partType likes wheel_kind axle_kind Widget Fred Ann CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb wheel_kind CxWorld)
      (v/assert kb (list 'genlArg partType 2 'thing) CxWorld)
      (v/assert kb (list likes Fred Ann) CxWorld)
      (v/assert kb (list 'arg likes 1 'thing) CxWorld)
      (v/assert kb (list partType Widget axle_kind) CxWorld)
      (v/assert kb (list partType Widget 'thing) CxWorld)
      (is (nil? (v/handle-of kb (list 'thing Fred) CxWorld)) "no (thing Fred) is stored")
      (is (nil? (v/handle-of kb (list 'genl axle_kind 'thing) CxWorld)) "no edge to thing")
      (is (nil? (v/handle-of kb (list 'genl 'thing 'thing) CxWorld)) "no reflexive edge")
      (is (nil? (v/handle-of kb (list 'unary_predicate 'thing) CxWorld))
          "and no arity statement of thing")
      (is (empty? (v/violations kb)) "the ledger stays clean")
      (is (= #{[(list 'arg likes 1 'thing) 1] [(list 'genlArg partType 2 'thing) 2]}
             (into #{} (map (juxt :sentence :facts))
                   (:typed-thing (:declarations (v/kb-quality kb)))))
          "the quality report names each declaration with its predicate's stored extent"))))

(tu/deftest-kb a-symmetric-fact-mints-over-its-stored-spelling
  ;; `(symmetric relates)` stores `(relates a b)` and `(relates b a)` as one sentex, so
  ;; the declaration a mint rests on is read off that one spelling.  Read off the
  ;; spelling written, the fact arriving after `(genlArg relates 1 kind)` drew
  ;; `(genl b kind)` over position 2 or position 1 by how it was written, while the
  ;; declarations arriving after the fact read the stored spelling — two justifications
  ;; for one content, and a text export reloading in content order kept the other one.
  (tu/with-terms [kind relates a_kind b_kind CxWorld]
    (let [run (fn [fact-first? fact]
                (tu/with-neutral-kb [kb tu/fresh]
                  (with-entailing
                    (a-context kb CxWorld)
                    (a-type kb kind CxWorld)
                    (v/assert kb (list 'symmetric relates) 'CxUniverse)
                    (let [decls #(doseq [n [1 2]]
                                   (v/assert kb (list 'genlArg relates n kind) CxWorld))
                          state #(v/assert kb fact CxWorld)]
                      (if fact-first? (do (state) (decls)) (do (decls) (state))))
                    (into {}
                          (for [t [a_kind b_kind]
                                :let [h (v/handle-of kb (list 'genl t kind) CxWorld)]]
                            [t (set (for [s (:support (v/why kb h))]
                                      (set (map #(v/sentence-of (v/sentex kb (:handle %)))
                                                (:because s)))))])))))
          results (for [fact-first? [true false]
                        fact [(list relates a_kind b_kind) (list relates b_kind a_kind)]]
                    [[fact-first? fact] (run fact-first? fact)])]
      (is (every? (fn [[_ r]] (every? seq (vals r))) results)
          "each argument is minted a subtype of kind")
      (is (= 1 (count (set (map second results))))
          (str "the mints' justifications varied by spelling or order: " (pr-str results))))))

;; ---- a relation named where a type is declared ----------------------------
;;
;; CxUniverse declares every argument of the separation family a subtype of `thing`
;; (`(genlArg disjoint 1 thing)`, `(argAndRestGenl partition 2 thing)`), and
;; `(unary_predicate thing)` binds `thing` to one argument.  A relation named in one of them
;; is minted below `thing`, so it meets the arity content stored of it.  Each case
;; states those declarations by hand over a fresh KB, in every arrival order.

(defn- support-by-content
  "The justifications of `sentence` in `ctx`, each as its informant (a rule read as its
  sentence) and the sentences of its antecedents, nil for an antecedent with no record.
  With `roles`, a map from each temporary to the symbol it was written as, the
  temporaries read as those symbols, so readings over fresh terms compare."
  ([kb sentence ctx] (support-by-content kb sentence ctx {}))
  ([kb sentence ctx roles]
   (let [read #(some-> (v/sentex kb %) v/sentence-of)]
     (walk/postwalk-replace
      roles
      (set (for [j (some->> (v/handle-of kb sentence ctx) (v/supporting-justifications kb))]
             [(if (integer? (:informant j)) (read (:informant j)) (:informant j))
              (into #{} (map read) (:antecedents j))]))))))

(tu/deftest-kb a-symmetric-mark-arriving-after-its-facts-leaves-the-mints-of-the-mark-arriving-first
  ;; The mark arriving last re-spells a row written the other way round, and folds the two
  ;; rows two rules concluded, one per spelling (`integrate/move-row!`).  Each mint then
  ;; rests on the declaration of the position the stored spelling holds its argument at,
  ;; and no justification names the folded row.
  (doseq [shape [:written-reversed :both-spellings-concluded]]
    (tu/with-terms [rel a_kind b_kind t1 t2 top_t]
      (let [facts (case shape
                    :written-reversed [(list rel b_kind a_kind)]
                    :both-spellings-concluded
                    [(list 'set/forwardRule (list 'implies (list t1 '?x) (list rel '?x a_kind)))
                     (list 'set/forwardRule (list 'implies (list t2 '?x) (list rel a_kind '?x)))
                     (list t1 b_kind) (list t2 b_kind)])
            run   (fn [mark-first?]
                    (tu/with-neutral-kb [kb tu/fresh]
                      (with-entailing
                        (let [mark #(v/assert kb (list 'symmetric rel) 'CxUniverse)]
                          (when mark-first? (mark))
                          (doseq [s (concat (for [n [1 2]] (list 'genlArg rel n top_t)) facts)]
                            (v/assert kb s 'CxUniverse))
                          (when-not mark-first? (mark)))
                        (into {} (for [x [a_kind b_kind]]
                                   [x (support-by-content kb (list 'genl x top_t) 'CxUniverse)])))))
            early (run true)
            late  (run false)]
        (testing (name shape)
          (is (every? seq (vals early)))
          (is (= early late))
          (is (not-any? #(contains? (second %) nil) (mapcat val late))))))))

(defn- separation-row
  "The belief and the clash grounds the separation `sep` leaves over the tuple `fact` of a
  relation it names, as a value the fresh terms of one order do not vary: whether `fact`
  is believed (nil when it is not stored), the grounds of the binding `why-not` names for
  it inert, and the grounds of each `:arity-descension` report, with `sep` and
  `(unary_predicate top)` read as `:separation` and `:binding`."
  [kb sep fact ctx top]
  (let [sep   (some->> (v/handle-of kb sep ctx) (v/sentex kb) :sentence)
        named #(cond (= sep %) :separation (= (list 'unary_predicate top) %) :binding :else %)
        h     (v/handle-of kb fact ctx)]
    {:fact     (when h (believed? kb fact ctx))
     :inert    (when (and h (not (believed? kb fact ctx)))
                 (into #{} (map #(named (:sentence (v/sentex kb %))))
                       (:grounds (:binding (v/why-not kb h)))))
     :descends (into #{} (comp (filter #(= :arity-descension (:kind %)))
                               (map #(into #{} (map (comp named :sentence)) (:grounds %))))
                     (concat (v/conflicts kb) (v/contradictions kb)))}))

(tu/deftest-kb a-tuple-of-a-relation-a-separation-names-is-inert-naming-the-separation-in-every-order
  (doseq [[decls sep-of] [[['(genlArg disjoint 1 top)]
                           (fn [r s _] (list 'disjoint r s))]
                          [['(genlArg partition 1 top) '(argAndRestGenl partition 2 top)]
                           (fn [r s w] (list 'partition w r s))]]]
    (let [results
          (for [order (permutations [:decl :bind :sep :fact])]
            (tu/with-neutral-kb [kb tu/fresh]
              (tu/with-terms [animal gladdenOf saddenOf outputOf Cal Dee CxWorld top_t]
                (with-entailing
                  (a-context kb CxWorld)
                  (a-type kb animal CxWorld)
                  (let [sep   (sep-of gladdenOf saddenOf outputOf)
                        decls (walk/postwalk-replace {'top top_t} decls)]
                    (doseq [step order]
                      (case step
                        :decl (doseq [d decls] (v/assert kb d CxWorld {:strength :monotonic}))
                        :bind (v/assert kb (list 'unary_predicate top_t) CxWorld {:strength :monotonic})
                        :sep  (v/assert kb sep CxWorld)
                        :fact (v/assert kb (list gladdenOf Cal Dee) CxWorld)))
                    [order (separation-row kb sep (list gladdenOf Cal Dee) CxWorld top_t)])))))]
      (is (= #{{:fact false :inert #{:separation :binding} :descends #{}}}
             (set (map second results)))
          (str (first decls) ": " (pr-str (remove #(= {:fact false :inert #{:separation :binding}
                                                       :descends #{}}
                                                      (second %))
                                                  results)))))))

(tu/deftest-kb a-relation-a-separation-names-pairs-its-own-binding-with-the-one-above-in-every-order
  ;; the separation's mint puts parentOf under top_t, and the two CxUniverse bindings
  ;; are one pair, which names its members and no path (docs/taxonomy.md, "Arity")
  (let [results
        (for [order (permutations [:decl :bind :own :sep])]
          (tu/with-neutral-kb [kb tu/fresh]
            (tu/with-terms [animal parentOf childOf Cal Dee CxWorld top_t]
              (with-entailing
                (a-context kb CxWorld)
                (a-type kb animal CxWorld)
                (let [sep (list 'disjoint parentOf childOf)]
                  (doseq [step order]
                    (case step
                      :decl (v/assert kb (list 'genlArg 'disjoint 1 top_t) CxWorld {:strength :monotonic})
                      :bind (v/assert kb (list 'unary_predicate top_t) 'CxUniverse {:strength :monotonic})
                      :own  (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse {:strength :monotonic})
                      :sep  (v/assert kb sep CxWorld)))
                  [order (separation-row kb sep (list parentOf Cal Dee) CxWorld top_t)])))))]
    (is (= #{{:fact nil :inert nil :descends #{#{}}}} (set (map second results)))
        (pr-str (remove #(= {:fact nil :inert nil :descends #{#{}}} (second %)) results)))))

;; ---- order independence --------------------------------------------------

(defn- believed-shape
  "The belief the three sentences leave, as a value order cannot vary."
  [kb animal dog parentOf Fred Mary ctx]
  {:animal (believed? kb (list animal Fred) ctx)
   :dog    (believed? kb (list dog Fred) ctx)
   :fact   (believed? kb (list parentOf Fred Mary) ctx)})

(tu/deftest-kb every-arrival-order-reaches-the-same-belief
  ;; the declaration, the fact, and a competing type the argument already holds —
  ;; in all six orders.  `dog` is under `animal`, so the competing type is what makes
  ;; the entailment redundant, and *when* it arrives must not decide whether the KB
  ;; ends up believing a minted `(animal Fred)` on top of it.  The pruning reading asks
  ;; the same question the other way round and gets the same answer in all six —
  ;; `every-arrival-order-prunes-the-same-way`.
  (let [results
        (for [order (permutations [:decl :fact :type])]
          (tu/with-neutral-kb [kb tu/fresh]
            (tu/with-terms [animal dog parentOf Fred Mary CxWorld]
              (with-mints-kept
                (a-context kb CxWorld)
                (a-type kb animal CxWorld)
                (v/assert kb (list 'genl dog animal) CxWorld)
                (doseq [step order]
                  (case step
                    :decl (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
                    :fact (v/assert kb (list parentOf Fred Mary) CxWorld)
                    :type (v/assert kb (list dog Fred) CxWorld)))
                [order (assoc (believed-shape kb animal dog parentOf Fred Mary CxWorld)
                              :support (support-by-content
                                        kb (list animal Fred) CxWorld
                                        {animal 'animal dog 'dog parentOf 'parentOf Fred 'Fred
                                         Mary 'Mary CxWorld 'CxWorld}))]))))]
    (is (= 1 (count (set (map second results))))
        (str "belief or the mint's justifications varied by arrival order: " (pr-str results)))
    (is (every? (comp :animal second) results)
        "and every order believes the entailed type")))

(tu/deftest-kb a-minted-genl-edge-fires-the-rules-it-connects-in-every-order
  ;; A `genlArg` mint is a `genl` edge, so it brings the facts under its sub-type into a
  ;; rule keyed on the super-type exactly as a stated edge does.  All 120 orders of the
  ;; five ingredients: the fact last mints on `assert`, the declaration last mints through
  ;; `entail-existing`, and `(genl animal thing)` last mints when the settle releases the
  ;; declaration that could not mint before its type reached `thing`.
  (let [results
        (for [order (permutations [:type :decl :fact :member :rule])]
          (tu/with-neutral-kb [kb tu/fresh]
            (tu/with-terms [animal noted kindUnder wolf Rex Zoo CxWorld]
              (with-entailing
                (a-context kb CxWorld)
                (doseq [step order]
                  (case step
                    :type   (a-type kb animal CxWorld)
                    :decl   (v/assert kb (list 'genlArg kindUnder 1 animal) CxWorld)
                    :fact   (v/assert kb (list kindUnder wolf Zoo) CxWorld)
                    :member (v/assert kb (list wolf Rex) CxWorld)
                    :rule   (v/assert-rule kb [(list animal '?x)] (list noted '?x) CxWorld
                                           {:direction :forward})))
                [order {:edge  (v/genl? kb wolf animal)
                        :noted (believed? kb (list noted Rex) CxWorld)}]))))]
    (is (= #{{:edge true :noted true}} (set (map second results)))
        (str "the minted edge or its firing varied by arrival order: "
             (pr-str (remove #(= {:edge true :noted true} (second %)) results))))))

(tu/deftest-kb a-mint-over-a-retired-spelling-is-believed-at-the-elected-name-in-every-order
  ;; The merge supersedes the fact spelled at the retired name, and a supersession is not
  ;; a label, so the mint a declaration draws over that fact after the merge is restated
  ;; as it is stored, and the merge arriving last migrates the mint with the fact.  The
  ;; reading is taken under the merge and again after retracting it.
  (let [results
        (for [order (permutations [:decl :fact :merge])]
          (tu/with-neutral-kb [kb tu/fresh]
            (tu/with-terms [person ownerOf Kip Kipper Rex CxWorld]
              (with-entailing
                (a-context kb CxWorld)
                (doseq [step order]
                  (case step
                    :decl  (v/assert kb (list 'arg ownerOf 1 person) CxWorld)
                    :fact  (v/assert kb (list ownerOf Kipper Rex) CxWorld {:strength :monotonic})
                    :merge (v/assert kb (list 'equals Kip Kipper) CxWorld {:strength :monotonic})))
                (let [rep     (v/representative kb Kipper CxWorld)
                      retired (if (= rep Kip) Kipper Kip)
                      merged  {:elected (believed? kb (list person rep) CxWorld)
                               :retired (believed? kb (list person retired) CxWorld)}]
                  (v/retract! kb (v/handle-of kb (list 'equals Kip Kipper) CxWorld))
                  [order {:merged   merged
                          :unmerged {:fact-subject (believed? kb (list person Kipper) CxWorld)
                                     :other        (believed? kb (list person Kip) CxWorld)}}])))))]
    (is (= #{{:merged   {:elected true :retired false}
              :unmerged {:fact-subject true :other false}}}
           (set (map second results)))
        (str "the membership varied by arrival order: " (pr-str results)))))

(tu/deftest-kb every-arrival-order-prunes-the-same-way
  ;; The same orders with the `genl` edge that makes `dog` more specific than `animal` among
  ;; them.  Whether the KB *keeps* the minted `(animal Fred)` is then a question about what
  ;; it believes rather than about what arrived first: with pruning on the mint is withheld
  ;; where `(dog Fred)` and the edge came before it and withdrawn where either came after,
  ;; with every mint kept it holds the same justifications in every order, and each reading
  ;; ends its twenty-four orders at one KB.
  (doseq [prune? [true false]]
    (let [results
          (for [order (permutations [:edge :decl :fact :type])]
            (tu/with-neutral-kb [kb tu/fresh]
              (tu/with-terms [animal dog parentOf Fred Mary CxWorld]
                (binding [argument/*assertive-arg-types?*  true
                          checks/*prune-subsumed-mints?* prune?]
                  (a-context kb CxWorld)
                  (a-type kb animal CxWorld)
                  (doseq [step order]
                    (case step
                      :edge (v/assert kb (list 'genl dog animal) CxWorld)
                      :decl (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
                      :fact (v/assert kb (list parentOf Fred Mary) CxWorld)
                      :type (v/assert kb (list dog Fred) CxWorld)))
                  [order (assoc (believed-shape kb animal dog parentOf Fred Mary CxWorld)
                                :support (support-by-content
                                          kb (list animal Fred) CxWorld
                                          {animal 'animal dog 'dog parentOf 'parentOf Fred 'Fred
                                           Mary 'Mary CxWorld 'CxWorld}))]))))]
      (testing (if prune? "pruned" "kept")
        (is (= 1 (count (set (map second results))))
            (str "belief or the mint's justifications varied by arrival order: " (pr-str results)))
        (is (= #{(not prune?)} (set (map (comp :animal second) results)))
            "the type the specific membership already says is kept exactly when pruning is off")
        (is (every? (comp :dog second) results)
            "which is the membership every order does keep")))))

(tu/deftest-kb a-record-a-rule-concludes-takes-the-withheld-mints-in-every-order
  ;; The route through `mid` says `(genl kind top_t)`, so the mint `(kindOf kind Zoo)`
  ;; draws is withheld while no record holds it.  `(marker kind)` concludes the record by
  ;; rule, and one firing later `(nested kind Zoo)` mints onto it, so a mint justification
  ;; concludes the record when the settle reads it.  The record takes the justification of
  ;; each fact that entails it, the withheld one included, whichever arrives first.
  (tu/with-terms [kindOf nested mid kind marker marker2 Zoo top_t]
    (let [results
          (for [order (permutations [:route :fact :marker])]
            (tu/with-neutral-kb [kb tu/fresh]
              (with-pruning
                (doseq [s [(list 'genlArg kindOf 1 top_t) (list 'genlArg nested 1 top_t)
                           (list 'set/forwardRule (list 'implies (list marker '?x) (list 'genl '?x top_t)))
                           (list 'set/forwardRule (list 'implies (list marker '?x) (list marker2 '?x)))
                           (list 'set/forwardRule (list 'implies (list marker2 '?x) (list nested '?x Zoo)))]]
                  (v/assert kb s 'CxUniverse))
                (doseq [step order]
                  (case step
                    :route  (doseq [s [(list 'genl mid top_t) (list 'genl kind mid)]]
                              (v/assert kb s 'CxUniverse))
                    :fact   (v/assert kb (list kindOf kind Zoo) 'CxUniverse)
                    :marker (v/assert kb (list marker kind) 'CxUniverse)))
                [order (support-by-content kb (list 'genl kind top_t) 'CxUniverse)])))]
      (is (some #(= 'genlArg (first %)) (second (first results))))
      (is (= 1 (count (set (map second results))))
          (str "the record's justifications varied by arrival order: " (pr-str results))))))

(tu/deftest-kb every-arrival-order-prunes-the-same-way-under-a-cover
  ;; The edge that puts `dog` under `animal` is a cover's: with pruning on the mint is
  ;; withheld in every order while the cover stands, and drawn again in every order once
  ;; it is retracted; with every mint kept it stands throughout on the same justifications.
  (doseq [[prune? want] [[true  [{:animal false :dog true :fact true} {:animal true :dog true :fact true}]]
                         [false [{:animal true :dog true :fact true} {:animal true :dog true :fact true}]]]]
    (let [results
          (for [order (permutations [:edge :decl :fact :type])]
            (tu/with-neutral-kb [kb tu/fresh]
              (tu/with-terms [animal dog cat parentOf Fred Mary CxWorld]
                (binding [argument/*assertive-arg-types?*  true
                          checks/*prune-subsumed-mints?* prune?]
                  (a-context kb CxWorld)
                  (a-type kb animal CxWorld)
                  (doseq [step order]
                    (case step
                      :edge (v/assert kb (list 'covering animal dog cat) CxWorld)
                      :decl (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
                      :fact (v/assert kb (list parentOf Fred Mary) CxWorld)
                      :type (v/assert kb (list dog Fred) CxWorld)))
                  (let [read     #(assoc (believed-shape kb animal dog parentOf Fred Mary CxWorld)
                                         :support (support-by-content
                                                   kb (list animal Fred) CxWorld
                                                   {animal 'animal dog 'dog cat 'cat parentOf 'parentOf
                                                    Fred 'Fred Mary 'Mary CxWorld 'CxWorld}))
                        standing (read)]
                    (v/retract! kb (v/handle-of kb (list 'covering animal dog cat) CxWorld))
                    [order [standing (read)]])))))]
      (testing (if prune? "pruned" "kept")
        (is (= 1 (count (set (map second results))))
            (str "the mint's justifications varied by arrival order: " (pr-str results)))
        (is (= #{want} (set (map #(mapv (fn [r] (dissoc r :support)) (second %)) results)))
            (str "the mint varied by arrival order: " (pr-str results)))))))

(tu/deftest-kb every-arrival-order-prunes-the-same-way-across-contexts
  ;; `(dog Fred)` is stated in CxDogs and the mint lands in CxWorld, so what makes the mint
  ;; redundant is the `genlCx` edge that lets CxWorld see CxDogs.  With pruning on, an edge
  ;; arriving last withdraws the mint that an edge arriving first withholds; with every mint
  ;; kept, every order holds it on the same justifications.
  (doseq [prune? [true false]]
    (let [results
          (for [order (permutations [:cx :decl :fact :type])]
            (tu/with-neutral-kb [kb tu/fresh]
              (tu/with-terms [animal dog parentOf Fred Mary CxWorld CxDogs]
                (binding [argument/*assertive-arg-types?*  true
                          checks/*prune-subsumed-mints?* prune?]
                  (a-context kb CxWorld)
                  (a-context kb CxDogs)
                  (a-type kb animal 'CxUniverse)
                  (v/assert kb (list 'genl dog animal) 'CxUniverse)
                  (doseq [step order]
                    (case step
                      :cx   (v/assert kb (list 'genlCx CxWorld CxDogs) 'CxUniverse)
                      :decl (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
                      :fact (v/assert kb (list parentOf Fred Mary) CxWorld)
                      :type (v/assert kb (list dog Fred) CxDogs)))
                  [order [(believed? kb (list animal Fred) CxWorld)
                          (support-by-content kb (list animal Fred) CxWorld
                                              {animal 'animal dog 'dog parentOf 'parentOf Fred 'Fred
                                               Mary 'Mary CxWorld 'CxWorld CxDogs 'CxDogs})]]))))]
      (testing (if prune? "pruned" "kept")
        (is (= 1 (count (distinct (map second results))))
            (str "the mint's record varied by arrival order: " (pr-str results)))
        (is (= #{(not prune?)} (set (map (comp first second) results)))
            "the mint stands exactly when pruning is off")))))

(tu/deftest-kb a-membership-a-rule-concludes-withholds-the-mint-in-every-order
  ;; `(dog Fred)` is a rule's conclusion, and the subsumption check reads the candidate
  ;; subtypes off the term's unary predicate set, so a derived membership has to be listed there
  ;; as a stated one is.  A binary fact beside it puts `Fred` at argument 1 of a predicate
  ;; no subtype test reads.
  (let [results
        (for [order (permutations [:rule :decl :fact :marker])]
          (tu/with-neutral-kb [kb tu/fresh]
            (tu/with-terms [animal dog puppy parentOf likes Fred Mary]
              (with-pruning
                (a-type kb animal 'CxUniverse)
                (v/assert kb (list 'genl dog animal) 'CxUniverse)
                (v/assert kb (list likes Fred Mary) 'CxUniverse)
                (doseq [step order]
                  (case step
                    :rule   (v/assert kb (list 'set/forwardRule (list 'implies (list puppy '?x) (list dog '?x)))
                                      'CxUniverse)
                    :decl   (v/assert kb (list 'arg parentOf 1 animal) 'CxUniverse)
                    :fact   (v/assert kb (list parentOf Fred Mary) 'CxUniverse)
                    :marker (v/assert kb (list puppy Fred) 'CxUniverse)))
                [order [(believed? kb (list dog Fred) 'CxUniverse)
                        (believed? kb (list animal Fred) 'CxUniverse)]]))))]
    (is (= #{[true false]} (set (map second results)))
        (str "the mint varied by arrival order: " (pr-str results)))))

(tu/deftest-kb a-recovered-kb-withdraws-the-mint-a-membership-makes-redundant
  ;; The mints a membership can displace are read off the mint family kept in memory, so a KB
  ;; rebuilt from its store has to rebuild that family, or the membership arriving after the
  ;; restart would leave the mint standing that the same membership withdraws without one.
  (let [space {:space [::recovered-mints]}]
    (tu/with-terms [animal dog parentOf Fred Mary CxWorld]
      (let [kb (doto (v/open-kb (assoc space :recover? false)) (tu/clear-kb!))]
        (try
          (with-pruning
            (a-context kb CxWorld)
            (a-type kb animal CxWorld)
            (v/assert kb (list 'genl dog animal) CxWorld)
            (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
            (v/assert kb (list parentOf Fred Mary) CxWorld)
            (is (believed? kb (list animal Fred) CxWorld) "minted before the restart")
            (let [re (v/open-kb (assoc space :recover? :auto))]
              (v/assert re (list dog Fred) CxWorld)
              (is (nil? (v/handle-of re (list animal Fred) CxWorld))
                  "withdrawn by the membership that arrives after it")))
          (finally (tu/clear-kb! kb)))))))

;; ---- an argument that fails its declared type is held inert ----------------------
;;
;; A value argument under `arg`, and a separated symbol under the constraint-only reading,
;; are stored and held in the `:out` forced set (docs/argtypes.md, "An argument that fails
;; its declared type is held inert"), so the stored set and belief do not depend on
;; whether the declaration or the fact arrived first.

(defn- held-reading
  "Assert `setup` and then the sentences of `order` (keys of `ss`) in CxUniverse, and
  answer `{key [stored? believed?]}` for every key of `ss`, with `:violations` the
  `:inert-argument` entries' `[sentence type]`.  Retracts what it wrote."
  [kb setup ss order]
  (let [sh (mapv #(v/assert kb % 'CxUniverse) setup)
        hs (mapv #(v/assert kb (ss %) 'CxUniverse) order)
        r  (into {:violations (into #{} (comp (filter #(= :inert-argument (:violation %)))
                                              (map (juxt :sentence (comp :type :detail))))
                                    (v/violations kb))}
                 (for [[k s] ss :let [h (v/handle-of kb s 'CxUniverse)]]
                   [k [(some? h) (boolean (and h (v/believed? kb h 'CxUniverse)))]]))]
    (doseq [h (rseq (into sh hs))] (v/retract! kb h))
    r))

(tu/deftest-kb a-value-argument-under-a-declared-type-is-inert-in-either-order
  (doseq [entail? [true false]]
    (binding [argument/*assertive-arg-types?* entail?]
      (tu/with-terms [vdog vneeds]
        (let [ss    {:decl (list 'arg vneeds 1 vdog) :fact (list vneeds 5)}
              setup [(list 'genl vdog 'thing) (list 'unary_predicate vneeds)]]
          (is (= #{{:decl [true true] :fact [true false]
                    :violations #{[(list vneeds 5) :arg-type]}}}
                 (into #{} (map #(held-reading kb setup ss %)) (permutations [:decl :fact])))
              (str "entailing " entail?))
          (let [hs (mapv #(v/assert kb % 'CxUniverse) (concat setup [(ss :fact) (ss :decl)]))
                why (v/why-not kb (ss :fact) 'CxUniverse)]
            (is (= [:inert :arg-type 5] [(:reason why) (-> why :conviction :type) (-> why :conviction :arg)]))
            (is (= [false false false]
                   (mapv :loser (tu/recovered-readings kb false [(ss :fact) 'CxUniverse]
                                                       #(v/assert % (list vneeds 6) 'CxUniverse))))
                "held after a recover, and after a write over the recovered KB")
            (v/retract! kb (peek hs))
            (is (v/believed? kb (v/handle-of kb (ss :fact) 'CxUniverse) 'CxUniverse)
                "the declaration's retraction releases the fact")
            (doseq [h (rseq (pop hs))] (v/retract! kb h))))))))

;; The fact is stated in a context below the declaration's, and the `genl` edge that
;; places the declared type under `thing` is visible from the fact's context alone.
(tu/deftest-kb a-value-argument-below-the-declaration-s-context-is-inert-in-every-order
  (doseq [entail? [true false]]
    (binding [argument/*assertive-arg-types?* entail?]
      (tu/with-terms [vdog vneeds CxLow]
        (let [ss {:decl [(list 'arg vneeds 1 vdog) 'CxUniverse]
                  :edge [(list 'genl vdog 'thing) CxLow]
                  :fact [(list vneeds 5) CxLow]}
              sh (mapv #(v/assert kb % 'CxUniverse)
                       [(list 'genlCx CxLow 'CxUniverse) (list 'unary_predicate vneeds)])]
          (is (= #{false}
                 (into #{} (for [order (permutations [:decl :edge :fact])]
                             (let [hs (mapv #(apply v/assert kb (ss %)) order)
                                   in (boolean (v/believed? kb (v/handle-of kb (list vneeds 5) CxLow) CxLow))]
                               (doseq [h (rseq hs)] (v/retract! kb h))
                               in))))
              (str "entailing " entail?))
          (doseq [h (rseq sh)] (v/retract! kb h)))))))

;; A declared type that refines the value's kind leaves the value possibly a member, so
;; only a separation from one of its kinds convicts it.  The setup places the value kinds
;; as core.txt does.
(tu/deftest-kb a-value-is-held-only-where-the-declared-type-excludes-it
  (doseq [[decl t-of v sub held?] [['arg :sub "192.0.2.1" 'string false]
                                   ['arg :sub 5 'integer false]
                                   ['arg :sub 5 'string true]
                                   ['arg 'negative_integer 5 nil true]
                                   ['quotedArg :sub "192.0.2.1" 'string false]
                                   ['quotedArg 'negative_integer 5 nil true]]]
    (tu/with-terms [vaddr vneeds]
      (let [t     (if (= :sub t-of) vaddr t-of)
            ss    {:decl (list decl vneeds 1 t) :fact (list vneeds v)}
            setup (cond-> ['(genl string thing) '(genl number thing) '(genl integer number)
                           '(partition integer negative_integer non_negative_integer)
                           (list 'unary_predicate vneeds)]
                    sub (conj (list 'genl vaddr sub)))
            kind  ('{arg :arg-type quotedArg :quoted-arg-type} decl)]
        (is (= #{(if held?
                   {:decl [true true] :fact [true false] :violations #{[(ss :fact) kind]}}
                   {:decl [true true] :fact [true true] :violations #{}})}
               (into #{} (map #(held-reading kb setup ss %)) (permutations [:decl :fact])))
            (pr-str [decl t-of v sub]))))))

;; The edge `(genl vmid vk)` places the declared type `vdog`, two steps below it, under a
;; kind of the value, and neither end of the edge is at or above a value kind.  A limit of
;; 1 gives both ends more specializations than the refresh walks, so it finds the
;; declaration in its one pass over every declaration; 512 finds it off the index.
(tu/deftest-kb an-edge-above-the-declared-type-moves-the-value-s-hold-at-either-spec-count
  (doseq [entail? [true false]
          limit   [1 512]]
    (binding [argument/*assertive-arg-types?* entail?]
      (with-redefs-fn {#'checks/spec-walk-limit limit}
        #(tu/with-terms [vdog vmid vk vneeds]
           (let [hs (mapv (fn [s] (v/assert kb s 'CxUniverse))
                          [(list 'genl vk 'integer) (list 'genl vmid 'thing) (list 'genl vdog vmid)
                           (list 'unary_predicate vneeds) (list 'arg vneeds 1 vdog) (list vneeds 5)])
                 fh (peek hs)
                 in (fn [] (boolean (v/believed? kb fh 'CxUniverse)))
                 r  [(in) (let [e (v/assert kb (list 'genl vmid vk) 'CxUniverse)]
                            [(in) (do (v/retract! kb e) (in))])]]
             (is (= [false [true false]] r) (pr-str [entail? limit]))
             (doseq [h (rseq hs)] (v/retract! kb h))))))))

;; A `:monotonic` definition states the kind of value a type's members are, so it decides a
;; value under a type no kind reaches (`vtext`) and under one refining a kind (`vpos`); a
;; `:default` one decides nothing, and the definition's retraction gives the value back to
;; the kind's reading.  Each row is `[declaration relation defined condition strength
;; declared value believed-with believed-without]`.
(tu/deftest-kb a-monotonic-definition-decides-a-value-under-the-declared-type
  (doseq [[decl rel on cnd strength t-of v with without]
          [['arg 'defnIff :text '(string ?x) :monotonic :text "Foo" true false]
           ['arg 'defnIff :text '(string ?x) :monotonic :text 5 false false]
           ['arg 'defnSufficient :text '(string ?x) :monotonic :text "Foo" true false]
           ['arg 'defnIff :text '(string ?x) :default :text "Foo" false false]
           ['arg 'defnNecessary :pos '(and (integer ?x) (greaterThan ?x 0)) :monotonic :pos -3 false true]
           ['arg 'defnNecessary :pos '(and (integer ?x) (greaterThan ?x 0)) :monotonic :pos 7 true true]
           ['arg 'defnNecessary :pos '(and (integer ?x) (greaterThan ?x 0)) :monotonic :sub -3 false true]
           ['arg 'defnNecessary :pos '(and (integer ?x) (greaterThan ?x 0)) :default :pos -3 true true]
           ['quotedArg 'defnNecessary :pos '(and (integer ?x) (greaterThan ?x 0)) :monotonic :pos -3 false true]]
          entail?     [true false]
          defn-first? [true false]]
    (binding [argument/*assertive-arg-types?* entail?]
      (tu/with-terms [vtext vpos vsub vneeds]
        (let [ty    {:text vtext :pos vpos :sub vsub}
              setup [(list 'genl vtext 'thing) '(genl string thing) '(genl number thing)
                     '(genl integer number) (list 'genl vpos 'integer) (list 'genl vsub vpos)
                     (list 'unary_predicate vneeds) (list decl vneeds 1 (ty t-of))]
              sh    (mapv #(v/assert kb % 'CxUniverse) setup)
              put-d #(v/assert kb (list rel (ty on) cnd) 'CxUniverse {:strength strength})
              put-f #(v/assert kb (list vneeds v) 'CxUniverse)
              [dh fh] (if defn-first?
                        (let [d (put-d)] [d (put-f)])
                        (let [f (put-f)] [(put-d) f]))
              in?   #(boolean (v/believed? kb fh 'CxUniverse))
              w     (in?)
              _     (v/retract! kb dh)
              wo    (in?)]
          (doseq [h (rseq (conj sh fh))] (v/retract! kb h))
          (is (= [with without] [w wo])
              (pr-str [decl rel strength t-of v entail? defn-first?])))))))

;; Class (b) of a store's departures: a value under a type no kind reaches holds its fact
;; inert, and the fact's argument-1 mint leaves at the recover's settle.  Under a
;; `:monotonic` definition stating the type's kind, the recover keeps the fact and the
;; mint and owes no release.
(tu/deftest-kb a-value-a-monotonic-definition-admits-owes-no-release-after-a-recover
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [animal vtext labelOf Fred]
      (with-pruning
        (a-type kb animal 'CxUniverse)
        (a-type kb vtext 'CxUniverse)
        (v/assert kb (list 'arg labelOf 1 animal) 'CxUniverse)
        (v/assert kb (list 'arg labelOf 2 vtext) 'CxUniverse)
        (v/assert kb (list 'defnSufficient vtext '(string ?x)) 'CxUniverse {:strength :monotonic})
        (v/assert kb (list labelOf Fred "Foo") 'CxUniverse)
        (v/recover kb)
        (is (= [0 true true]
               [(v/owed-releases kb)
                (believed? kb (list labelOf Fred "Foo") 'CxUniverse)
                (believed? kb (list animal Fred) 'CxUniverse)]))))))

(tu/deftest-kb a-separated-symbol-argument-is-inert-in-every-order-under-the-constraint-reading
  (tu/with-terms [vdog vcat vneeds Rex Tom]
    (let [setup [(list 'genl vdog 'thing) (list 'genl vcat 'thing) (list 'disjoint vdog vcat)
                 (list 'binary_predicate vneeds)]
          ss    {:decl (list 'arg vneeds 1 vdog) :fact (list vneeds Rex Tom)
                 :other (list vcat Rex) :own (list vdog Rex)}
          every (fn [] (into #{} (map #(held-reading kb setup ss %))
                             (permutations [:decl :fact :other :own])))]
      (is (= #{{:decl [true true] :fact [true false] :other [true true] :own [true true]
                :violations #{[(list vneeds Rex Tom) :arg-type]}}}
             (tu/without-entailing (every)))
          "Rex is a vcat, which vdog excludes, so the fact is held whether or not (vdog Rex) is stored")
      (is (= #{{:decl [true true] :fact [true true] :other [true true] :own [true true]
                :violations #{}}}
             (tu/with-entailing (every)))
          "the entailing reading weighs the membership and holds nothing"))))

(tu/deftest-kb a-declaration-draws-no-type-from-an-inert-fact
  ;; An inert sentex claims nothing, so it is no fact a declaration's sweep reads.  The
  ;; fact-side path already draws nothing from one, and the declaration-side sweep has to
  ;; agree with it, or a rechain mints what the load did not.
  (with-entailing
    (tu/with-terms [animal parentOf Fred Mary Ann Bob CxWorld]
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (testing "the declaration arriving after the inert fact"
        (v/assert-inert kb (list parentOf Fred Mary) CxWorld)
        (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
        (is (nil? (v/handle-of kb (list animal Fred) CxWorld))))
      (testing "and a rechain after an inert fact arriving under the declaration"
        (v/assert-inert kb (list parentOf Ann Bob) CxWorld)
        (v/forward-chain kb {})
        (is (nil? (v/handle-of kb (list animal Ann) CxWorld)))
        (is (nil? (v/handle-of kb (list animal Fred) CxWorld)))))))
