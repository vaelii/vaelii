;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.absent-type-order-test
  "Order independence where a derivation reads the **absence** of a type.

  An argument constraint convicts a sentence when the argument's types have no path to
  the declared one, and `mintable-type?` declines a mint whose type an arity statement
  binds to another length.  Both read the KB as it stands, so each needs a way back for the order
  where the missing edge or membership arrives later: a convicted rule conclusion is stored
  and held by the argument hold (docs/argtypes.md), and an unminted declaration is read again when its type's own bindings
  move (`special/mints-on-lengths`).  And a
  `forced_decontextualized_predicate` declaration moves the extent stored before it.

  Each test runs the same sentences in both orders on a fresh KB and compares what the
  KB holds, stored and believed.  `starter-in-any-order` is the same claim over the
  whole shipped ontology."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.host.seed :as seed]
            [vaelii.impl.io.text :as text]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.special :as special]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.order-independence-test :as oi]
            [vaelii.test-util :as tu]))

(defn- held
  "What `kb` stores, as a multiset of printed `[sentence context]` pairs with the rule
  handle an `exceptWhen` meta names blanked — the one place content carries a handle,
  and handles are allocated in arrival order."
  [kb]
  (frequencies
   (for [h (p/sentex-ids (:records kb))
         :let [sx (p/get-sentex (:records kb) h)]]
     [(str/replace (pr-str (:sentence sx)) #"\(sentexHandle \d+\)" "(sentexHandle _)")
      (str (:context sx))
      (v/in? kb h)])))

(defn- in-both-orders
  "Run `steps` (a map of step name to a fn of the KB) in `first-steps` then the rest, and
  in the reverse, each on a fresh KB after `setup`; return `[reading-a reading-b]`, each
  `(observe kb)`."
  [setup steps order-a observe]
  (for [order [order-a (reverse order-a)]]
    (tu/with-neutral-kb [kb tu/fresh]
      (setup kb)
      (doseq [s order] ((steps s) kb))
      (observe kb))))

(defn- a-type [kb t ctx] (v/assert kb (list 'genl t 'thing) ctx {:strength :monotonic}))

(defn- a-binary [kb t] (v/assert kb (list 'binary_predicate t) 'CxUniverse {:strength :monotonic}))

(defn- unbind [kb t] (v/retract! kb (v/handle-of kb (list 'binary_predicate t) 'CxUniverse)))

(defn- a-context [kb ctx super] (v/assert kb (list 'genlCx ctx super) 'CxUniverse {:strength :monotonic}))

(tu/deftest-kb a-forced-declaration-arriving-last-rehomes-what-was-stored-before-it
  ;; The declaration forces the storage context of every `(P …)` asserted after it; one
  ;; asserted before it stayed where it was written, so which context held the fact —
  ;; and the entailments a fact there draws — was the order.
  (tu/with-terms [linkedTo Alpha Beta CxWorld]
    (let [readings (in-both-orders
                    #(a-context % CxWorld 'CxUniverse)
                    {:decl #(v/assert % (list 'forced_decontextualized_predicate linkedTo) 'CxUniverse)
                     :fact #(v/assert % (list linkedTo Alpha Beta) CxWorld)}
                    [:decl :fact]
                    (fn [kb] {:contexts (mapv :context (v/sentexes-matching
                                                        kb (list linkedTo Alpha Beta) '?ctx))
                              :held     (held kb)}))]
      (is (apply = readings) "both orders hold the same sentexes")
      (is (= '[CxUniverse] (:contexts (first readings)))
          "the fact lives in CxUniverse and not where it was written"))))

(tu/deftest-kb a-conclusion-convicted-by-a-missing-edge-is-placed-once-the-edge-arrives
  ;; `(arg ownsPet 2 animal)` is written in CxTheory, above the rule's context, so there
  ;; it constrains without entailing.  Rex is a `poodleKind`, and until the edge
  ;; `(genl poodleKind animal)` arrives nothing reaches `animal` from there.  Arriving
  ;; first, the same edge lets the firing through, so a KB that holds it OUT for good
  ;; believes less in one order than the other.
  (tu/with-terms [animal poodleKind petOf ownsPet Rex Ann CxTheory CxWorld]
    (let [readings (in-both-orders
                    (fn [kb]
                      (a-context kb CxTheory 'CxUniverse)
                      (a-context kb CxWorld CxTheory)
                      (a-type kb animal CxTheory)
                      (a-type kb poodleKind CxTheory)
                      (v/assert kb (list 'arg ownsPet 2 animal) CxTheory)
                      (v/assert kb (list 'set/forwardRule
                                         (list 'implies (list petOf '?x '?y) (list ownsPet '?y '?x)))
                                CxWorld))
                    {:edge #(v/assert % (list 'genl poodleKind animal) CxTheory)
                     :fact #(do (v/assert % (list poodleKind Rex) CxWorld)
                                (v/assert % (list petOf Rex Ann) CxWorld))}
                    [:edge :fact]
                    (fn [kb] {:owns (boolean (v/ask? kb (list ownsPet Ann Rex) CxWorld))
                              :held (held kb)}))]
      (is (:owns (first readings)) "the edge first: the conclusion is placed")
      (is (apply = readings) "and the edge last reaches the same KB"))))

(tu/deftest-kb a-declaration-whose-type-loses-its-other-arity-mints-then
  ;; `mintable-type?` reads the declared type's own arity.  The declaration and the fact
  ;; arriving while `(binary_predicate gadgetKind)` stands mint nothing and wait; the
  ;; settle after the binding leaves re-asks them.  Forced to the entailing reading, since
  ;; the mint is what it asks about.
  (tu/with-entailing
    (doseq [kind ['arg 'genlArg]]
      (testing (str kind)
        (tu/with-terms [gadgetKind usesTool Ann Widget widgetKind CxWorld]
          (let [arg?     (= 'arg kind)
                ;; `genlArg` types a position that names a kind, so its argument is a type
                used     (if arg? Widget widgetKind)
                decl     (list kind usesTool 2 gadgetKind)
                minted   (if arg? (list gadgetKind Widget) (list 'genl widgetKind gadgetKind))
                readings (in-both-orders
                          #(do (a-context % CxWorld 'CxUniverse) (a-binary % gadgetKind))
                          {:unbind #(unbind % gadgetKind)
                           :rest   #(do (v/assert % decl CxWorld)
                                        (v/assert % (list usesTool Ann used) CxWorld))}
                          [:unbind :rest]
                          (fn [kb] {:minted (some? (v/handle-of kb minted CxWorld))
                                    :held   (held kb)}))]
            (is (:minted (first readings)) "the binding gone first: the declaration mints")
            (is (apply = readings) "and the binding gone last reaches the same KB")))))))

(tu/deftest-kb a-length-arriving-after-a-mint-holds-it-out-at-that-write
  ;; The binding withdraws the `(unary_predicate t)` the declaration entailed, and that
  ;; removal moves `t`'s length after the settle's arity refresh read it.  Read right after
  ;; the binding's write, `(t Rex)` is believed in neither order.
  (tu/with-entailing
    (tu/with-terms [t rel Rex Mary CxWorld]
      (let [readings (in-both-orders
                      #(do (a-context % CxWorld 'CxUniverse) (a-type % t CxWorld))
                      {:bind #(a-binary % t)
                       :rest #(do (v/assert % (list 'arg rel 1 t) CxWorld)
                                  (v/assert % (list rel Rex Mary) CxWorld))}
                      [:rest :bind]
                      (fn [kb] (boolean (some->> (v/handle-of kb (list t Rex) CxWorld) (v/in? kb)))))]
        (is (= [false false] readings))))))

(tu/deftest-kb a-length-arriving-after-a-mint-removes-it-from-the-store
  ;; A mint stored before its type's conflicting length arrived is removed, so the store
  ;; holds what the order with the binding first holds.  Each row is the declaration, the
  ;; fact, and the mint it draws.
  (tu/with-entailing
    (tu/with-terms [t rel Rex Mary widgetKind CxWorld]
      (doseq [[decl fact minted] [[(list 'arg rel 1 t) (list rel Rex Mary) (list t Rex)]
                                  [(list 'genlArg rel 2 t) (list rel Rex widgetKind) (list 'genl widgetKind t)]
                                  [(list 'argArg rel 1 2) (list rel Rex t) (list t Rex)]]]
        (let [readings (in-both-orders
                        #(do (a-context % CxWorld 'CxUniverse) (a-type % t CxWorld)
                             (a-type % widgetKind CxWorld))
                        {:bind #(a-binary % t)
                         :rest #(do (v/assert % decl CxWorld) (v/assert % fact CxWorld))}
                        [:rest :bind]
                        (fn [kb] {:minted (some? (v/handle-of kb minted CxWorld)) :held (held kb)}))]
          (is (= [false false] (mapv :minted readings)) (str decl))
          (is (apply = readings) (str decl " stores the same in both orders")))))))

(tu/deftest-kb a-type-with-two-in-lengths-mints-in-no-order
  ;; `(unary_predicate t)` and `(binary_predicate t)` both `:default` stay IN as one
  ;; `contradicts`.  A type mints only when every IN length admits length one, so no
  ;; order of the two bindings, the declaration and the fact stores the mint, before or
  ;; after `recover`.
  (tu/with-entailing
    (tu/with-terms [t rel Rex Mary widgetKind CxWorld]
      (doseq [[decl fact minted] [[(list 'arg rel 1 t) (list rel Rex Mary) (list t Rex)]
                                  [(list 'genlArg rel 2 t) (list rel Rex widgetKind) (list 'genl widgetKind t)]
                                  [(list 'argArg rel 1 2) (list rel Rex t) (list t Rex)]]]
        (let [steps    {:unary  #(v/assert % (list 'unary_predicate t) 'CxUniverse)
                        :binary #(v/assert % (list 'binary_predicate t) 'CxUniverse)
                        :decl   #(v/assert % decl CxWorld)
                        :fact   #(v/assert % fact CxWorld)}
              stored?  #(some? (v/handle-of % minted CxWorld))
              readings (for [order (oi/permutations [:unary :binary :decl :fact])]
                         (tu/with-neutral-kb [kb tu/fresh]
                           (a-context kb CxWorld 'CxUniverse)
                           (a-type kb t CxWorld)
                           (a-type kb widgetKind CxWorld)
                           (doseq [s order] ((steps s) kb))
                           (let [written (stored? kb)]
                             (v/recover kb)
                             [order written (stored? kb)])))]
          (is (= [] (into [] (filter #(or (second %) (last %))) readings))
              (str decl ": the orders storing " minted ", as [order written recovered]")))))))

;; ---- the rebuild after recover ---------------------------------------------------

(tu/deftest-kb a-declaration-arriving-after-its-facts-lifts-each-of-them
  ;; six facts of a predicate over two contexts, then its `decontextualized_predicate`
  ;; declaration: the sweep copies every one into CxUniverse, unchecked, since each
  ;; stating context sees CxUniverse
  (tu/with-terms [liftedRel Alpha CxWorld CxOther]
    (tu/with-neutral-kb [kb tu/fresh]
      (a-context kb CxWorld 'CxUniverse)
      (a-context kb CxOther 'CxUniverse)
      (doseq [i (range 6)]
        (v/assert kb (list liftedRel Alpha (tu/fresh-term :individual 'Beta))
                  (if (even? i) CxWorld CxOther)))
      (v/assert kb (list 'decontextualized_predicate liftedRel) 'CxUniverse
                {:strength :monotonic})
      (is (= 6 (count (v/sentexes-matching kb (list liftedRel Alpha '?b) 'CxUniverse)))))))

;; ---- the settle's re-ask ---------------------------------------------------------

(defn- sweeps
  "How many times `special/entail-existing` sweeps a declaration of `dhs` while `f` runs."
  [dhs f]
  (let [n (atom 0) real special/entail-existing]
    (with-redefs [special/entail-existing (fn [kb s dh]
                                            (when (contains? dhs dh) (swap! n inc))
                                            (real kb s dh))]
      (f))
    @n))

(tu/deftest-kb a-write-that-moves-no-waiting-type-s-length-reads-no-declaration
  ;; four declarations name a type bound to two arguments, and the refusal record holds
  ;; nothing for them.  A membership, a `genl` edge between two other types and a
  ;; rolled-back preview sweep none of them; the binding leaving sweeps each once, and
  ;; the declarations mint over the fact stored while the type was bound.
  (tu/with-entailing
    (tu/with-terms [orphan toolKind partKind qKind Widget Gear Bolt CxWorld]
      (tu/with-neutral-kb [kb tu/fresh]
        (a-context kb CxWorld 'CxUniverse)
        (a-type kb toolKind CxWorld)
        (a-binary kb orphan)
        (let [rels  (into [] (repeatedly 4 #(tu/fresh-term :predicate 'usesKind)))
              dhs   (into #{} (map #(v/assert kb (list 'arg % 1 orphan) CxWorld)) rels)
              _     (v/assert kb (list (first rels) Bolt Widget) CxWorld)
              fact  (sweeps dhs #(v/assert kb (list toolKind Widget) CxWorld))
              edge  (sweeps dhs #(v/assert kb (list 'genl partKind toolKind) CxWorld))
              prev  (sweeps dhs #(v/preview kb {:add [[(list 'genl qKind 'thing) CxWorld]]}))
              after (sweeps dhs #(v/assert kb (list toolKind Gear) CxWorld))]
          (is (= [0 0 0 0] [fact edge prev after]))
          (is (every? #(nil? (get @(reasoning/refused kb) %)) dhs) "the record holds nothing")
          (is (nil? (v/handle-of kb (list orphan Bolt) CxWorld)) "and nothing is minted")
          (is (= 4 (sweeps dhs #(unbind kb orphan))) "the binding leaving sweeps each")
          (is (some? (v/handle-of kb (list orphan Bolt) CxWorld))
              "and the declarations mint over the fact"))))))

;; ---- a convicted lift ---------------------------------------------------------

(tu/deftest-kb a-fact-whose-lift-the-argument-constraint-convicts-is-refused-at-the-assert
  ;; The declaration and the argument constraint are in CxUniverse, which the stating
  ;; context sees, so the source assert reads the conviction (5 being a number) and
  ;; stores neither the fact nor a copy, and the refusal record holds nothing for it.
  (tu/with-terms [lanimal lifted L CxOut]
    (tu/with-neutral-kb [kb tu/fresh]
      (a-type kb lanimal 'CxUniverse)
      (v/assert kb (list 'arg lifted 2 lanimal) 'CxUniverse)
      (v/assert kb (list 'decontextualized_predicate lifted) CxOut)
      (let [before @(reasoning/refused kb)]
        (v/assert kb (list lifted L 5) CxOut)
        (is (empty? (v/sentexes-matching kb (list lifted L 5) '?ctx)))
        (is (= before @(reasoning/refused kb)))))))

;; ---- the whole shipped ontology -----------------------------------------------

(defn- starter-entries
  "Every sentence the starter loads, as `[sentence context]`, in the shipped loader's
  order: the upper files into CxUniverse, then the middle contexts."
  []
  (concat (for [f (core-context/upper-files)    s (seed/read-sentences f "upper")]  [s 'CxUniverse])
          (for [c (seed/layer-contexts "middle") s (seed/read-sentences c "middle")] [s c])))

(defn- load-shuffled!
  "The starter's sentences in the order `seed` shuffles them to, through the text
  loader, then the starter's closing `unary_predicate` batch."
  [kb seed]
  (let [l (java.util.ArrayList. ^java.util.Collection (vec (starter-entries)))]
    (java.util.Collections/shuffle l (java.util.Random. (long seed)))
    (v/with-deferred-settle kb
      (text/load-entries! (fn [s c o] (v/assert kb s c (or o {})))
                          (fn [s c] (v/assert-inert kb s c))
                          (vec l)))
    (v/with-deferred-settle kb
      (doseq [t (nm/by-print-key (v/specs kb 'thing))]
        (v/assert kb (list 'unary_predicate t) 'CxUniverse)))
    kb))

(defn- held-after
  "`(held kb)` after `load!` on a cleared KB of its own, cleared again after."
  [load!]
  (let [kb (tu/isolated-fresh)]
    (try (held (load! kb)) (finally (tu/clear-kb! kb)))))

(defn- starter-in-orders
  "Each shuffled order in `seeds` against the shipped one.  The shipped reading is the
  restored starter dump — `starter/load-into`'s KB, which `starter_copy_test` tests — so
  a run pays for the shuffled loads alone."
  [seeds]
  (let [shipped (held-after tu/load-starter!)]
    (doseq [s seeds]
      (let [shuffled (held-after #(load-shuffled! % s))]
        (is (= shipped shuffled)
            (str "seed " s ": held only by the shipped order "
                 (pr-str (take 5 (remove (set (keys shuffled)) (keys shipped))))
                 ", only by the shuffled one "
                 (pr-str (take 5 (remove (set (keys shipped)) (keys shuffled))))))))))

(deftest starter-in-any-order
  ;; one shuffled order at :default; `starter-in-many-orders` runs twenty
  (starter-in-orders [7]))

(deftest ^:slow starter-in-many-orders
  (starter-in-orders (range 100 120)))
