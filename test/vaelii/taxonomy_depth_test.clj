;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.taxonomy-depth-test
  "The `genl` / `genlCx` **depth potential** — the topological ranking that lets
  `reachable?` reject most pairs in O(1) — and what a deferred batch does to it.

  The potential is derived state with one invariant, over the **condensation**:
  `edge x→y ⇒ depth[x] > depth[y]`, except inside a strongly connected component,
  where the two are equal and mutual reachability is read off `:scc` instead.  Every
  test here checks reads against the invariant rather than against particular depth
  numbers, because the numbers legitimately differ between an incremental build
  (`raise-depth` / `local-lift`, which only ever grow a depth) and a from-scratch one
  (`repair-depths`, which computes each component's exact height).  What must never
  differ is the answers.

  Three costs are in tension and each has its own test:

    * repairing per edge is O(that edge's descendants) — quadratic when edges arrive
      child-first, which is why a batch defers it;
    * a `:loose?` relation makes every read an unpruned walk, and `wff` runs one per
      taxonomy edge asserted — which is why deferring must not simply go loose;
    * `local-lift` is the middle: O(1) plus the source's in-degree, sound for the
      parent-before-child order a hierarchy usually arrives in."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- reading the potential ----------------------------------------------

(defn- rel [t k] (get @t k))

(defn- violations
  "Active edges the potential does not rank — the invariant, as data.  An edge inside
  a component is ranked by being *level*: the potential ranks the condensation, and
  within one component there is nothing to rank."
  [t k]
  (let [{:keys [edges depth scc]} (rel t k)
        same-comp? (fn [a b] (let [ca (get scc a)] (and (some? ca) (= ca (get scc b)))))]
    (into #{} (remove (fn [[a b]]
                        (if (same-comp? a b)
                          (= (get depth a -1) (get depth b -1))
                          (> (get depth a -1) (get depth b -1)))))
          edges)))

(defn- sound? [t k] (empty? (violations t k)))
(defn- loose? [t k] (boolean (:loose? (rel t k))))

(defn- ty [i] (symbol (str "d" i "_t")))
(defn- ctx [i] (symbol (str "CxD" i)))

(defn- chain-edges
  "A `d0 ← d1 ← … ← dn` chain as `[sub super handle]` triples, parent-first (the order
  a hierarchy is normally written in) or child-first (`raise-depth`'s worst case)."
  [n order]
  (let [es (map (fn [i] [(ty i) (ty (dec i)) i]) (range 1 (inc n)))]
    (if (= :child-first order) (reverse es) es)))

(defn- build
  "A taxonomy holding `edges`, inserted eagerly or under `*defer-depths?*`."
  [edges defer?]
  (let [t (tax/create-taxonomy)]
    (binding [tax/*defer-depths?* defer?]
      (doseq [[a b h] edges] (tax/add-genl t a b h)))
    t))

;; ---- the invariant, whichever way the edges arrive -----------------------

(deftest a-deferred-batch-leaves-a-potential-that-ranks-every-edge
  (doseq [order [:parent-first :child-first]
          :let  [edges (chain-edges 40 order)]]
    (testing (str "eager insert keeps the invariant — " order)
      (is (sound? (build edges false) :genl)))
    (testing (str "deferred insert plus one repair keeps it — " order)
      (let [t (build edges true)]
        (tax/restore-depths t)
        (is (sound? t :genl))
        (is (not (loose? t :genl)) "the repair clears the loose mark")))))

(deftest parent-first-arrival-never-goes-loose
  ;; The whole point of `local-lift`: a hierarchy loaded the way hierarchies are
  ;; written keeps a sound potential *during* the batch, so reads stay pruned.  A
  ;; blanket `:loose?` would have made every `wff` cycle check walk unpruned instead.
  (let [t (build (chain-edges 40 :parent-first) true)]
    (is (not (loose? t :genl)))
    (is (sound? t :genl) "sound without any repair having run"))
  (testing "a wide shallow hierarchy — every child of one root — stays sound too"
    (let [t (build (map (fn [i] [(ty i) (ty 0) i]) (range 1 40)) true)]
      (is (not (loose? t :genl)))
      (is (sound? t :genl))))
  (testing "child-first arrival is the case that does go loose, and reads survive it"
    (let [t (build (chain-edges 40 :child-first) true)]
      (is (loose? t :genl))
      (is (tax/genl?-global t (ty 40) (ty 0)) "reachability is answered unpruned, not wrongly")
      (is (not (tax/genl?-global t (ty 0) (ty 40))))
      (is (= (into #{} (map ty) (range 0 41)) (tax/genls-global t (ty 40)))))))

(deftest genlCx-gets-the-same-treatment-as-genl
  ;; Both relations run through one `activate`, so the deferral covers both — and
  ;; `genlCx` is the one that matters most for a corpus load, whose topology file
  ;; is written depth-sorted, i.e. exactly parent-first.
  (let [edges (map (fn [i] [(ctx i) (ctx (dec i)) i]) (range 1 41))
        build-ctx (fn [es defer?]
                    (let [t (tax/create-taxonomy)]
                      (binding [tax/*defer-depths?* defer?]
                        (doseq [[a b h] es] (tax/add-genlCx t a b h)))
                      t))]
    (testing "parent-first stays sound with no repair"
      (let [t (build-ctx edges true)]
        (is (not (loose? t :genlCx)))
        (is (sound? t :genlCx))
        (is (tax/sees? t (ctx 40) (ctx 0)))))
    (testing "child-first goes loose, reads survive, and the repair fixes it"
      (let [t (build-ctx (reverse edges) true)]
        (is (loose? t :genlCx))
        (is (tax/sees? t (ctx 40) (ctx 0)))
        (is (not (tax/sees? t (ctx 0) (ctx 40))))
        (tax/restore-depths t)
        (is (sound? t :genlCx))
        (is (not (loose? t :genlCx)))
        (is (tax/sees? t (ctx 40) (ctx 0)))))
    (testing "the two relations go loose independently"
      (let [t (tax/create-taxonomy)]
        (binding [tax/*defer-depths?* true]
          (doseq [[a b h] (reverse edges)] (tax/add-genlCx t a b h))   ; child-first
          (doseq [[a b h] (chain-edges 40 :parent-first)] (tax/add-genl t a b h)))
        (is (loose? t :genlCx))
        (is (not (loose? t :genl)) "a loose genlCx does not drag genl down with it")
        (tax/restore-depths t)
        (is (sound? t :genl))
        (is (sound? t :genlCx))))))

(deftest deferred-and-eager-agree-whatever-the-arrival-order
  ;; Belief must not depend on arrival order.  Depth *numbers* may; the relation the
  ;; potential prunes must not.
  (let [n     30
        base  (chain-edges n :parent-first)
        pairs (for [a (range 0 (inc n)) b (range 0 (inc n))] [(ty a) (ty b)])
        answers (fn [t] (into #{} (filter (fn [[a b]] (tax/genl?-global t a b))) pairs))
        want  (answers (build base false))]
    (doseq [trial (range 6)
            :let  [order (shuffle base)]]
      (testing (str "shuffled order " trial)
        (is (= want (answers (build order false))) "eager")
        (is (= want (answers (build order true)))  "deferred, mid-batch")
        (let [t (build order true)]
          (tax/restore-depths t)
          (is (= want (answers t)) "deferred, after the repair")
          (is (sound? t :genl)))))))

(deftest a-repair-is-idempotent-and-free-when-nothing-is-loose
  (let [t (build (chain-edges 20 :child-first) true)]
    (is (loose? t :genl))
    (tax/restore-depths t)
    (let [after (:depth (rel t :genl))]
      (tax/restore-depths t)
      (tax/restore-depths t)
      (is (= after (:depth (rel t :genl))))
      (is (sound? t :genl)))))

(deftest an-insert-onto-a-loose-relation-does-not-build-on-the-stale-potential
  ;; `activate` reads `:loose?`, not just the dynamic var: an eager insert arriving
  ;; while the potential is unrepaired must not run `raise-depth` on a stale base
  ;; (its termination argument rests on a cycle check made *with* that base), and
  ;; must not silently re-enable pruning.
  (let [t      (build (chain-edges 20 :child-first) true)
        before (:depth (rel t :genl))]
    (is (loose? t :genl))
    ;; a new *supertype* above the chain's root: the one shape whose eager repair
    ;; would push a lift down through every node already in the relation
    (tax/add-genl t (ty 0) 'droot_t 999)              ; eager: *defer-depths?* is false
    (is (= before (dissoc (:depth (rel t :genl)) 'droot_t))
        "nothing moved — pushing a lift through a stale potential is work that repairs
         nothing, and the cycle check licensing it was made with that same stale base")
    (is (loose? t :genl) "still loose — the repair is `restore-depths`'s to make")
    (is (tax/genl?-global t (ty 20) 'droot_t) "and the read is still right")
    (tax/restore-depths t)
    (is (sound? t :genl))
    (is (tax/genl?-global t (ty 20) 'droot_t))))

(deftest a-cycle-closed-while-loose-is-condensed-where-it-closes
  ;; The loose short-circuit governs the **acyclic** repair and nothing else.  `:scc` is
  ;; not a pruning — `tax/placement-rep` collapses a mutually-visible group of contexts
  ;; to one name through it — and a firing seeded by the closing edge reads it before
  ;; the batch settles, so a component discovered only by `restore-depths` puts one
  ;; claim in two contexts that see each other.
  (let [t (tax/create-taxonomy)]
    (binding [tax/*defer-depths?* true]
      (tax/add-genlCx t (ctx 1) (ctx 2) 1)
      (tax/add-genlCx t (ctx 2) (ctx 3) 2)
      (is (loose? t :genlCx) "child-first: the second edge breaks the one above it")
      (tax/add-genlCx t (ctx 3) (ctx 1) 3))           ; closes the cycle, still in the batch
    (let [scc (:scc (rel t :genlCx))]
      (is (= 3 (count scc)) "all three are in a component, inside the batch")
      (is (= 1 (count (set (vals scc)))) "and they answer to one representative"))
    (is (not (loose? t :genlCx))
        "the cycle's own repair is the whole relation's, so it lifts the loose mark")
    (is (sound? t :genlCx))
    (testing "and the batch repair has nothing left to find"
      (let [before (:scc (rel t :genlCx))]
        (tax/restore-depths t)
        (is (= before (:scc (rel t :genlCx))))))))

(deftest a-cycle-is-ranked-as-one-component
  ;; `wff` refuses a cyclic `genl` or `genlCx` edge, but the *taxonomy* must hold one
  ;; anyway: a recovered or foreign store replays whatever is stored, past the checks.
  ;; The pass condenses, so it terminates **and** leaves a sound potential —
  ;; the members level with each other, everything else strictly ranked around them —
  ;; and the depth-pruned reads stay exact, which the old raw-graph pass could not
  ;; promise.
  (let [t (tax/create-taxonomy)]
    (binding [tax/*defer-depths?* true]
      (tax/add-genl t 'ca_t 'cb_t 1)
      (tax/add-genl t 'cb_t 'cc_t 2)
      (tax/add-genl t 'cc_t 'ca_t 3)                  ; closes the cycle
      (tax/add-genl t 'cd_t 'ca_t 4)                  ; below it
      (tax/add-genl t 'cc_t 'ce_t 5))                 ; above it
    (tax/restore-depths t)                            ; terminates, which was the claim
    (is (sound? t :genl) "the potential ranks the condensation")
    (is (not (loose? t :genl)))
    (testing "the cycle is one component, level with itself"
      (let [{:keys [depth scc]} (rel t :genl)]
        (is (= 1 (count (distinct (map scc '[ca_t cb_t cc_t])))))
        (is (every? some? (map scc '[ca_t cb_t cc_t])))
        (is (nil? (scc 'cd_t)) "a lone node is in no component")
        (is (apply = (map depth '[ca_t cb_t cc_t])))
        (is (> (depth 'cd_t) (depth 'ca_t)))
        (is (> (depth 'ca_t) (depth 'ce_t)))))
    (testing "and the pruned reads answer the cycle exactly"
      (is (= '#{ca_t cb_t cc_t ce_t} (tax/genls-global t 'ca_t)) "reach stays cycle-safe")
      (is (= '#{ca_t cb_t cc_t cd_t} (tax/specs-global t 'ca_t)))
      (is (tax/genl?-global t 'ca_t 'cc_t))
      (is (tax/genl?-global t 'cc_t 'ca_t) "mutual, and answered without a walk")
      (is (tax/genl?-global t 'cd_t 'ce_t) "through the whole component")
      (is (not (tax/genl?-global t 'ce_t 'ca_t))))))

(deftest a-belief-move-remakes-a-component
  ;; `refresh-beliefs` is the one path that changes the active edge set with no sentex
  ;; added or removed, and it moves a component both ways: an edge leaving one splits
  ;; it, an edge revived into a cycle closes a new one.  The two are not symmetric.  A
  ;; split is answered where it happens — the component's own members are all that can
  ;; have changed — so the relation stays ranked.  A merge is a question about the
  ;; whole graph, so `activate` condenses the whole relation on the spot: the relation
  ;; is never loose across it and `:scc` holds the merged component the moment the
  ;; edge is active, which is what a forward placement reading it inside the same
  ;; assert needs.
  (let [t   (tax/create-taxonomy)
        scc #(:scc (rel t :genlCx))]
    (tax/add-genlCx t 'CxCyA 'CxCyB 1)
    (tax/add-genlCx t 'CxCyB 'CxCyA 2)
    (is (not (loose? t :genlCx)) "the closing edge repaired in place")
    (is (sound? t :genlCx))
    (is (= 1 (count (distinct (map (scc) '[CxCyA CxCyB])))))
    (testing "the edge leaving splits the component, and the split is repaired in place"
      (tax/refresh-beliefs t #(not= % 2))
      (is (empty? (scc)) "not trusted: a split is the one staleness that answers true")
      (is (not (loose? t :genlCx)) "and the rest of the relation was never in doubt")
      (is (sound? t :genlCx) "the two are ranked against each other again")
      (is (tax/sees? t 'CxCyA 'CxCyB))
      (is (not (tax/sees? t 'CxCyB 'CxCyA)))
      (tax/restore-depths t)
      (is (empty? (scc)) "and there is genuinely no component to find"))
    (testing "and it coming back closes one again, repaired as it closes"
      (tax/refresh-beliefs t (constantly true))
      (is (not (loose? t :genlCx)) "the reconcile condensed rather than surrendering")
      (is (sound? t :genlCx))
      (is (= 1 (count (distinct (map (scc) '[CxCyA CxCyB]))))
          "one component again, and one name for it")
      (tax/restore-depths t)
      (is (= 1 (count (distinct (map (scc) '[CxCyA CxCyB]))))
          "and the batch repair has nothing left to do"))))

;; ---- a lift out of a component ------------------------------------------

(defn- within?
  "Run `f` on a daemon thread and wait `ms` for it; true if it finished.  The one
  operation here that can fail by **not returning at all** is bounded rather than
  trusted, because a suite that hangs reports nothing — and the thread is a daemon so
  the JVM can still exit out from under a runaway one."
  [ms f]
  (let [th (doto (Thread. ^Runnable f) (.setDaemon true) (.start))]
    (.join th (long ms))
    (not (.isAlive th))))

(deftest an-edge-out-of-a-cycle-lifts-the-whole-component
  ;; The potential ranks the **condensation**, so a lift is a claim about a component
  ;; rather than about a node: raising one member alone would leave it above its own
  ;; mates, each of which then forces the next one round the cycle, and the lift never
  ;; comes back.  The whole component moves together, which both terminates and stays
  ;; sound.
  (let [t (tax/create-taxonomy)]
    (tax/add-genlCx t 'CxLfA 'CxLfB 1)
    (tax/add-genlCx t 'CxLfB 'CxLfA 2)
    (tax/restore-depths t)
    (is (within? 10000 #(tax/add-genlCx t 'CxLfA 'CxLfZ 3))
        "the lift terminates")
    (is (sound? t :genlCx))
    (is (not (loose? t :genlCx)))
    (testing "both members sit above what one of them points at"
      (let [{:keys [depth]} (rel t :genlCx)]
        (is (= (depth 'CxLfA) (depth 'CxLfB)) "level, as one component")
        (is (> (depth 'CxLfA) (depth 'CxLfZ)))))
    (testing "and the pruned reads answer through the component"
      (is (tax/sees? t 'CxLfA 'CxLfZ))
      (is (tax/sees? t 'CxLfB 'CxLfZ))
      (is (not (tax/sees? t 'CxLfZ 'CxLfA))))))

(deftest a-deletion-that-cannot-split-a-component-leaves-it-alone
  ;; A component's strong connectivity is a property of its own induced subgraph, so an
  ;; edge with an endpoint outside it is not a member of that subgraph and cannot break
  ;; it.  Neither the component nor the ranking is touched, which is what keeps the
  ;; cost of a deletion the size of what it removed rather than the size of the
  ;; relation.
  (let [t   (tax/create-taxonomy)
        scc #(:scc (rel t :genlCx))]
    (tax/add-genlCx t 'CxDsA 'CxDsB 1)
    (tax/add-genlCx t 'CxDsB 'CxDsA 2)
    (tax/add-genlCx t 'CxDsA 'CxDsTop 3)     ; out of the component
    (tax/add-genlCx t 'CxDsLow 'CxDsA 4)     ; into it
    (tax/restore-depths t)
    (let [before (scc)]
      (doseq [[a b h] '[[CxDsA CxDsTop 3] [CxDsLow CxDsA 4]]]
        (tax/del-genlCx! t a b h))
      (is (= before (scc)) "the component is exactly the one it was")
      (is (not (loose? t :genlCx)))
      (is (sound? t :genlCx))
      (is (tax/sees? t 'CxDsA 'CxDsB))
      (is (tax/sees? t 'CxDsB 'CxDsA))
      (is (not (tax/sees? t 'CxDsA 'CxDsTop))))))

(deftest a-split-ranks-the-pieces-against-each-other-without-going-loose
  ;; The measured case: a three-context ring, one edge of it retracted.  What is left
  ;; is a chain, and the chain has to be ranked — the members were level as one
  ;; component and a level pair reads as mutually reachable.  The repair is scoped to
  ;; the component that split, so the relation keeps its pruning and every unrelated
  ;; context is untouched.
  (let [t   (tax/create-taxonomy)
        scc #(:scc (rel t :genlCx))]
    (tax/add-genlCx t 'CxSpA 'CxSpB 1)
    (tax/add-genlCx t 'CxSpB 'CxSpC 2)
    (tax/add-genlCx t 'CxSpC 'CxSpA 3)
    (tax/add-genlCx t 'CxSpA 'CxSpTop 4)
    (dotimes [i 20] (tax/add-genlCx t (ctx (+ 100 i)) 'CxSpTop (+ 200 i)))
    (tax/restore-depths t)
    (is (= 1 (count (distinct (map (scc) '[CxSpA CxSpB CxSpC])))))
    (tax/del-genlCx! t 'CxSpC 'CxSpA 3)
    (testing "the ring is a chain now, and nothing claims a component"
      (is (empty? (scc)))
      (is (not (loose? t :genlCx)))
      (is (sound? t :genlCx)))
    (testing "and the chain reads one way only"
      (is (tax/sees? t 'CxSpA 'CxSpC))
      (is (not (tax/sees? t 'CxSpC 'CxSpA)))
      (is (tax/sees? t 'CxSpA 'CxSpTop))
      (is (not (tax/sees? t 'CxSpC 'CxSpTop))
          "the ring was what carried SpC up to the top")
      (is (not (tax/sees? t 'CxSpTop 'CxSpA))))))

;; ---- the same thing through the KB ---------------------------------------

(defn- kb-sound? [kb] (and (sound? (reasoning/taxonomy kb) :genl)
                           (sound? (reasoning/taxonomy kb) :genlCx)))

(tu/deftest-kb a-batch-through-the-kb-leaves-a-sound-potential
  (tu/with-terms [a_t b_t c_t]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl a_t b_t) 'CxUniverse)
      (v/assert kb (list 'genl b_t c_t) 'CxUniverse))
    (is (kb-sound? kb))
    (is (not (loose? (reasoning/taxonomy kb) :genl)))
    (is (v/genl? kb a_t c_t))))

(tu/deftest-kb an-aborted-batch-still-repairs-the-depth-potential
  ;; The settle that would have repaired never runs — a cancelled load is exactly this
  ;; shape — so the macro repairs on the way out.  Left loose, every later `genl?` and
  ;; `sees?` would walk unpruned for the life of the KB.
  (tu/with-terms [p_t q_t r_t s_t]
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/with-deferred-settle kb
                   ;; child-first, so the batch is genuinely loose when it aborts
                   (v/assert kb (list 'genl r_t s_t) 'CxUniverse)
                   (v/assert kb (list 'genl q_t r_t) 'CxUniverse)
                   (v/assert kb (list 'genl p_t q_t) 'CxUniverse)
                   (throw (ex-info "cancelled" {:type :cancelled})))))
    (is (not (loose? (reasoning/taxonomy kb) :genl)) "repaired on the way out")
    (is (kb-sound? kb))
    (is (v/genl? kb p_t s_t) "and everything the batch did land is still reachable")))

(tu/deftest-kb a-revived-context-cycle-is-one-place-to-stand-again-in-its-own-settle
  ;; Two contexts that see each other are **one** place for a firing to put its
  ;; conclusion, and which of their names stands for the group is read off `:scc`
  ;; (`placement-rep`).  A defeat splits the component where it happens and a revival
  ;; condenses the relation as the edge activates, so `:scc` holds the group — or
  ;; nothing — at the end of the settle that moved the edge, never a settle later.
  ;; Otherwise how many settles have run would decide where a conclusion lands, which
  ;; is exactly what content-keyed placement exists to rule out (docs/contexts.md).
  (tu/with-terms [CxAlpha CxBeta]
    (let [tx    (reasoning/taxonomy kb)
          place #(tax/maximal-common-descendant-contexts tx [%])]
      (v/assert kb (list 'genlCx CxBeta CxAlpha) 'CxUniverse)   ; b sees a
      ;; a → b closes the cycle, which `wff` refuses at assert; form it the way a belief
      ;; race does (docs/taxonomy.md) — defeat b → a, assert a → b while it is inactive,
      ;; then revive b → a, so both stand and the two contexts see each other.
      (let [d (v/assert kb (list 'not (list 'genlCx CxBeta CxAlpha))
                        'CxUniverse {:strength :monotonic})]
        (v/assert kb (list 'genlCx CxAlpha CxBeta) 'CxUniverse) ; a sees b — no active cycle
        (v/retract! kb d))
      (let [group (place CxBeta)]
        (is (= 1 (count group)) "the cycle is one place to stand")
        (is (= group (place CxAlpha)) "wearing one name")
        (let [h (v/assert kb (list 'not (list 'genlCx CxAlpha CxBeta))
                          'CxUniverse {:strength :monotonic})]
          (is (= #{CxBeta} (place CxBeta))
              "with one edge defeated there is no cycle and no group")
          (v/retract! kb h)
          (is (not (loose? tx :genlCx)) "the revival repaired in the settle that made it")
          (is (= group (place CxBeta)) "and the group answers to one name again")
          (is (= group (place CxAlpha))))))))

(tu/deftest-kb recover-rebuilds-a-sound-potential
  ;; `recover` replays every stored edge, which is a bulk load and is deferred like
  ;; one; the repair runs before anything reads the relation back.
  (tu/with-terms [w_t x_t y_t z_t]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl w_t x_t) 'CxUniverse)
      (v/assert kb (list 'genl x_t y_t) 'CxUniverse)
      (v/assert kb (list 'genl y_t z_t) 'CxUniverse))
    (let [before (into {} (for [t [w_t x_t y_t z_t]] [t (v/genls kb t)]))]
      (v/recover kb)
      (is (not (loose? (reasoning/taxonomy kb) :genl)))
      (is (kb-sound? kb))
      (is (= before (into {} (for [t [w_t x_t y_t z_t]] [t (v/genls kb t)])))
          "the closure survives the rebuild"))))

(deftest a-deferred-cycle-close-marks-loose-instead-of-repairing
  ;; `*defer-cycle-scc?*` is recovery's replay flag: the first cycle-closing edge marks
  ;; the relation `:loose?`, every edge after it skips the detection walk (the branch is
  ;; `loose?` either way), and `restore-depths` computes `:scc` once for the whole batch
  ;; — instead of `activate` repairing the whole relation per cycle-closing edge.  The
  ;; chain arrives parent-first (each edge's sub is a fresh node), so `local-lift` keeps
  ;; it sound and never loose until the closing edge, which is the only operation the
  ;; flag changes.  Two further chords then land while the relation is already loose.
  ;; The one deferred repair must reach the same condensation the eager per-edge repair
  ;; builds, whichever path got there.
  (letfn [(chain! [t]
            (tax/add-genl t 'h1_t 'h0_t 1)
            (tax/add-genl t 'h2_t 'h1_t 2)
            (tax/add-genl t 'h3_t 'h2_t 3))
          (more! [t]                                    ; two more cycle-closers + a fresh sub
            (tax/add-genl t 'h0_t 'h2_t 5)              ; chord, back into the component
            (tax/add-genl t 'h1_t 'h3_t 6)              ; chord, back into the component
            (tax/add-genl t 'h4_t 'h0_t 7))]            ; below the component, acyclic
    (let [eager    (tax/create-taxonomy)
          deferred (tax/create-taxonomy)
          build!   (fn [t defer?]
                     (binding [tax/*defer-depths?* true tax/*defer-cycle-scc?* defer?]
                       (chain! t) (tax/add-genl t 'h0_t 'h3_t 4)))]  ; closes h0→h3→h2→h1→h0
      (build! eager false)
      (build! deferred true)
      (testing "the flag alone decides whether the first cycle-close repairs now or defers"
        (is (not (loose? eager :genl))        "eager repairs the cycle outright")
        (is (seq (:scc (rel eager :genl)))    "eager already holds the component")
        (is (loose? deferred :genl)           "deferred marks loose and waits")
        (is (empty? (:scc (rel deferred :genl))) "deferred has not computed :scc yet"))
      (binding [tax/*defer-depths?* true]
        (binding [tax/*defer-cycle-scc?* false] (more! eager))
        (binding [tax/*defer-cycle-scc?* true]  (more! deferred)))
      (is (loose? deferred :genl)
          "deferred is still loose after two more cycles, having skipped their detection")
      (tax/restore-depths eager)
      (tax/restore-depths deferred)
      (testing "the single deferred repair lands the eager path's condensation"
        (is (not (loose? deferred :genl)))
        (is (not (loose? eager :genl)))
        (is (sound? eager :genl))
        (is (sound? deferred :genl))
        (is (= (:scc (rel eager :genl)) (:scc (rel deferred :genl)))
            "same component, same representative")
        (is (= (:depth (rel eager :genl)) (:depth (rel deferred :genl)))
            "same depth potential"))
      (testing "and the pruned reads answer the cycle the same either way"
        (doseq [t [eager deferred]]
          (is (= 1 (count (distinct (map (:scc (rel t :genl)) '[h0_t h1_t h2_t h3_t])))))
          (is (tax/genl?-global t 'h0_t 'h3_t))
          (is (tax/genl?-global t 'h3_t 'h0_t) "mutual, answered off :scc")
          (is (tax/genl?-global t 'h4_t 'h3_t) "the sub below reaches through the component"))))))

(tu/deftest-kb recover-rebuilds-a-cyclic-context-potential
  ;; The acyclic recover test above never reaches the cyclic branch of `activate`.  A
  ;; `genlCx` cycle is refused at assert, so it reaches the taxonomy only from a
  ;; recovered or foreign store; the cycle below is formed the way a belief race does
  ;; (defeat an edge, assert its reverse, revive the first — docs/taxonomy.md), which
  ;; leaves all three positive edges stored for `recover` to replay.  Recovery defers
  ;; the repair through `*defer-cycle-scc?*`, so `restore-depths` is what has to land the
  ;; component.  The recovered condensation and visibility must match the live build's.
  (v/assert kb '(genlCx CxCycLo CxCycMid) 'CxUniverse)
  (v/assert kb '(genlCx CxCycMid CxCycHi) 'CxUniverse)      ; mid sees hi
  ;; hi → mid closes CxCycMid ⇄ CxCycHi; break mid → hi, assert hi → mid, revive mid → hi
  (let [d (v/assert kb '(not (genlCx CxCycMid CxCycHi)) 'CxUniverse {:strength :monotonic})]
    (v/assert kb '(genlCx CxCycHi CxCycMid) 'CxUniverse)    ; hi sees mid — no active cycle
    (v/retract! kb d))
  (let [tax    (reasoning/taxonomy kb)
        scc-of #(:scc (rel tax :genlCx))
        before {:scc    (scc-of)
                :mid-hi (tax/sees? tax 'CxCycMid 'CxCycHi)
                :hi-mid (tax/sees? tax 'CxCycHi 'CxCycMid)
                :lo-hi  (tax/sees? tax 'CxCycLo 'CxCycHi)}]
    (testing "the live build makes the cycle one mutually-visible component"
      (is (= 1 (count (distinct (map (scc-of) '[CxCycMid CxCycHi])))))
      (is (every? some? (map (scc-of) '[CxCycMid CxCycHi])))
      (is (true? (:mid-hi before)))
      (is (true? (:hi-mid before))))
    (v/recover kb)
    (testing "recover rebuilds the same condensation, sound and not loose"
      (is (not (loose? tax :genlCx)))
      (is (sound? tax :genlCx))
      (is (= (:scc before) (scc-of)) "same component, same representative")
      (is (= (:mid-hi before) (tax/sees? tax 'CxCycMid 'CxCycHi)))
      (is (= (:hi-mid before) (tax/sees? tax 'CxCycHi 'CxCycMid)))
      (is (= (:lo-hi before) (tax/sees? tax 'CxCycLo 'CxCycHi))
          "reach into the cycle survives the rebuild"))))
