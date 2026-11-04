;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.taxonomy-test
  "Pure unit tests for the genl / genlCx closures and context placement.

  Edges are *supported*: every mutation names the sentex handle asserting the edge,
  and the edge is active while at least one supporter is believed.  The handles here
  are bare integers — the closure math does not care where they came from."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]))

(deftest min-genls-and-max-specs-leave-out-a-neighbour-another-stands-between
  (let [t (tax/create-taxonomy)]
    (tax/add-genl t 'mammal 'animal 1)
    (tax/add-genl t 'dog 'mammal 2)
    (tax/add-genl t 'dog 'animal 3)
    (tax/add-genl t 'dog 'pet 4)
    (testing "the one-step adjacency holds the redundant edge"
      (is (= '#{mammal animal pet} (tax/direct-genls-global t 'dog)))
      (is (= '#{mammal dog} (tax/direct-specs-global t 'animal))))
    (testing "the nearest neighbours do not, and two incomparable ones both stay"
      (is (= '#{mammal pet} (tax/min-genls-global t 'dog)))
      (is (= '#{mammal} (tax/max-specs-global t 'animal))))
    (testing "a type that is not a node has none"
      (is (= #{} (tax/min-genls-global t 'rock)))
      (is (= #{} (tax/max-specs-global t 'rock))))
    (testing "removing the nearer edge makes the farther neighbour the nearest"
      (tax/del-genl! t 'dog 'mammal 2)
      (is (= '#{animal pet} (tax/min-genls-global t 'dog)))
      (is (= '#{mammal dog} (tax/max-specs-global t 'animal))))))

(deftest min-types-and-max-types-keep-the-ends-of-the-order-among-the-members
  (let [t (tax/create-taxonomy)]
    (tax/add-genl t 'mammal 'animal 1)
    (tax/add-genl t 'dog 'mammal 2)
    (tax/add-genl t 'dog 'pet 3)
    (tax/add-genl t 'rock 'mineral 4)
    (testing "a chain keeps one end"
      (is (= '#{dog} (tax/min-types-global t '[dog mammal animal])))
      (is (= '#{animal} (tax/max-types-global t '[dog mammal animal])))
      (is (= '#{mammal} (tax/min-types-global t '[animal mammal])))
      (is (= '#{dog} (tax/min-types-global t '[animal dog])) "with no member between"))
    (testing "members no path relates all stay"
      (is (= '#{mammal pet rock} (tax/min-types-global t '[mammal pet rock])))
      (is (= '#{mammal pet rock} (tax/max-types-global t '[mammal pet rock]))))
    (testing "a chain beside an unrelated member keeps one end and that member"
      (is (= '#{dog rock} (tax/min-types-global t '[dog mammal animal rock])))
      (is (= '#{animal pet rock} (tax/max-types-global t '[dog mammal animal pet rock]))))
    (testing "a supertype outside the members drops no member"
      ;; `dog` has the parents `mammal` and `pet`, and neither is a member.  `dog`'s
      ;; up-closure is smaller than the six members
      (is (= '#{dog c2 c3 c4 c5 c6} (tax/max-types-global t '[dog c2 c3 c4 c5 c6])))
      (is (= '#{dog c2 c3 c4 c5 c6} (tax/min-types-global t '[dog c2 c3 c4 c5 c6])))
      (is (= '#{dog rock} (tax/max-types-global t '[dog rock]))))
    (testing "a subtype outside the members drops no member"
      (is (= '#{animal pet mineral} (tax/min-types-global t '[animal pet mineral]))))
    (testing "a member that is not a node stays, and a repeat is one member"
      (is (= '#{dog unheard} (tax/min-types-global t '[dog unheard mammal dog]))))
    (testing "the scoped arities with a nil context read every edge"
      (is (= '#{dog} (tax/min-types t '[dog mammal animal] nil)))
      (is (= '#{animal} (tax/max-types t '[dog mammal animal] nil))))
    (testing "an empty or one-member collection makes no closure read"
      (with-redefs [tax/closure-of (fn [& _] (throw (ex-info "closure read" {})))]
        (is (= #{} (tax/min-types-global t [])))
        (is (= #{} (tax/max-types-global t nil)))
        (is (= '#{dog} (tax/min-types-global t '[dog])))
        (is (= '#{dog} (tax/max-types-global t '[dog dog])))
        (is (thrown? clojure.lang.ExceptionInfo (tax/min-types-global t '[dog mammal])))))))

(deftest extremal-keeps-two-members-that-subsume-each-other
  ;; the closures are given as a map, so the cycle needs no taxonomy that admits one
  (let [ends  @#'tax/extremal
        above '{a #{a b top} b #{a b top} top #{top} low #{low a b top}}]
    (is (= '#{a b} (ends above true '[a b])))
    (is (= '#{a b} (ends above false '[a b])))
    (is (= '#{a b} (ends above true '[a b top])))
    (is (= '#{top} (ends above false '[a b top])))
    (is (= '#{low} (ends above true '[a b low])))
    (is (= '#{a b} (ends above false '[a b low])))))

(deftest max-specs-keeps-a-child-that-has-a-second-parent-outside-the-neighbours
  ;; `c1` is also a subtype of `other`, which is no neighbour of `hub`
  (let [t (tax/create-taxonomy)]
    (doseq [[i c] (map-indexed vector '[c1 c2 c3 c4 c5])]
      (tax/add-genl t c 'hub (inc i)))
    (tax/add-genl t 'c1 'other 10)
    (is (= '#{c1 c2 c3 c4 c5} (tax/max-specs-global t 'hub)))
    (is (= '#{c1} (tax/max-specs-global t 'other)))
    (testing "and going up, a parent with a parent of its own outside the neighbours stays"
      (doseq [[i p] (map-indexed vector '[p1 p2 p3 p4 p5])]
        (tax/add-genl t 'leaf p (+ 20 i)))
      (tax/add-genl t 'p1 'beyond 30)
      (is (= '#{p1 p2 p3 p4 p5} (tax/min-genls-global t 'leaf))))))

(deftest min-context-parents-and-max-context-children-leave-out-a-neighbour-another-stands-between
  (let [t (tax/create-taxonomy)]
    (tax/add-genlCx t 'CxMid 'CxTop 1)
    (tax/add-genlCx t 'CxLeaf 'CxMid 2)
    (tax/add-genlCx t 'CxLeaf 'CxTop 3)
    (tax/add-genlCx t 'CxLeaf 'CxAside 4)
    (testing "the one-step adjacency holds the redundant edge"
      (is (= '#{CxMid CxTop CxAside} (tax/context-parents-global t 'CxLeaf)))
      (is (= '#{CxMid CxLeaf} (tax/context-children-global t 'CxTop))))
    (testing "the nearest neighbours do not, and two incomparable ones both stay"
      (is (= '#{CxMid CxAside} (tax/min-context-parents t 'CxLeaf)))
      (is (= '#{CxMid} (tax/max-context-children t 'CxTop))))
    (testing "a context with one neighbour has that one, and a context that is no node has CxUniverse"
      (is (= '#{CxTop} (tax/min-context-parents t 'CxMid)))
      (is (= '#{CxLeaf} (tax/max-context-children t 'CxMid)))
      (is (= '#{CxUniverse} (tax/min-context-parents t 'CxUnheard)) "the implicit root")
      (is (= #{} (tax/max-context-children t 'CxUnheard))))
    (testing "removing the nearer edge makes the farther neighbour the nearest"
      (tax/del-genlCx! t 'CxLeaf 'CxMid 2)
      (is (= '#{CxTop CxAside} (tax/min-context-parents t 'CxLeaf)))
      (is (= '#{CxMid CxLeaf} (tax/max-context-children t 'CxTop))))))

(deftest min-context-parents-and-max-context-children-keep-both-sides-of-a-diamond
  ;; `CxLeaf` reaches `CxTop` through `CxLeft` and through `CxRight`, and the edge from
  ;; `CxLeaf` to `CxTop` is held beside them
  (let [t (tax/create-taxonomy)]
    (tax/add-genlCx t 'CxLeft 'CxTop 1)
    (tax/add-genlCx t 'CxRight 'CxTop 2)
    (tax/add-genlCx t 'CxLeaf 'CxLeft 3)
    (tax/add-genlCx t 'CxLeaf 'CxRight 4)
    (tax/add-genlCx t 'CxLeaf 'CxTop 5)
    (is (= '#{CxLeft CxRight} (tax/min-context-parents t 'CxLeaf)))
    (is (= '#{CxLeft CxRight} (tax/max-context-children t 'CxTop)))
    (is (= '#{CxLeaf} (tax/max-context-children t 'CxLeft)))
    (is (= '#{CxTop} (tax/min-context-parents t 'CxRight)))
    (testing "the nearest neighbours of a context are among the contexts it sees or is seen by"
      (is (every? (set (tax/context-up t 'CxLeaf)) (tax/min-context-parents t 'CxLeaf)))
      (is (every? (set (tax/context-down t 'CxTop)) (tax/max-context-children t 'CxTop))))))

(deftest a-context-is-a-maximal-child-of-exactly-its-minimal-parents
  ;; over acyclic edge sets, which is what `wff` admits: an edge runs from a lower index
  ;; to a higher one
  (let [rnd (java.util.Random. 20261011)
        cx  (fn [i] (symbol (str "CxNode" i)))
        n   9]
    (dotimes [trial 200]
      (let [t     (tax/create-taxonomy)
            edges (into #{} (for [a (range n), b (range (inc a) n)
                                  :when (< (.nextDouble rnd) 0.35)]
                              [a b]))]
        (doseq [[i [a b]] (map-indexed vector (sort edges))]
          (tax/add-genlCx t (cx a) (cx b) (inc i)))
        (is (every? (fn [c]
                      (= (tax/max-context-children t c)
                         (into #{} (filter #(contains? (tax/min-context-parents t %) c))
                               (tax/context-children-global t c))))
                    (map cx (range n)))
            (str "trial " trial " edges " (sort edges)))
        (is (every? (fn [c]
                      (let [near (tax/min-context-parents t c)
                            up   (disj (set (tax/context-up t c)) c)]
                        (= up (into #{} (mapcat #(tax/context-up t %)) near))))
                    (map cx (range n)))
            "every context a context sees is seen through a minimal parent")))))

(deftest nearest-of-keeps-mutually-subsuming-neighbours
  ;; the closures are given as a map, so the cycle needs no taxonomy that admits one
  (let [ends    @#'tax/extremal
        nearest (fn [above up? node nbrs]
                  (@#'tax/nearest-of above #(ends above up? %) up? node nbrs))]
    (testing "two neighbours that subsume each other are both kept, and drop a farther one"
      (let [above '{n #{n a b top} a #{a b top} b #{a b top} top #{top}}]
        (is (= '#{a b} (nearest above true 'n '#{a b top})))
        (is (= '#{a b} (nearest above false 'top '#{a b n})))))
    (testing "a neighbour that subsumes and is subsumed by the node drops nothing"
      (let [above '{n #{n twin top} twin #{n twin top} top #{top} low #{low n twin top}}]
        (is (= '#{twin top} (nearest above true 'n '#{twin top})))
        (is (= '#{twin low} (nearest above false 'n '#{twin low})))))
    (testing "the neighbour that subsumes and is subsumed by the node is kept beside the rest"
      ;; the reduction alone would keep `twin` and drop `top`
      (let [above '{n #{n twin top} twin #{n twin top} top #{top}}]
        (is (= '#{twin} (ends above true '#{twin top})))
        (is (= '#{twin top} (nearest above true 'n '#{twin top})))))
    (testing "a type that is not a neighbour drops nothing, whichever set is the smaller"
      ;; `c1` and `p1` have an up-closure smaller than the five neighbours
      (let [above '{n #{n} c1 #{c1 n x} c2 #{c2 n} c3 #{c3 n} c4 #{c4 n} c5 #{c5 n} x #{x}}]
        (is (= '#{c1 c2 c3 c4 c5} (nearest above false 'n '#{c1 c2 c3 c4 c5})))
        (is (= '#{c1 c2} (nearest above false 'n '#{c1 c2}))))
      (let [above '{n #{n p1 p2 p3 p4 p5 x} p1 #{p1 x} p2 #{p2} p3 #{p3} p4 #{p4} p5 #{p5}
                    x #{x}}]
        (is (= '#{p1 p2 p3 p4 p5} (nearest above true 'n '#{p1 p2 p3 p4 p5})))
        (is (= '#{p1 p2} (nearest above true 'n '#{p1 p2})))))
    (testing "one neighbour, or none, costs no closure read"
      (let [above (fn [_] (throw (ex-info "read" {})))]
        (is (= '#{a} (nearest above true 'n '#{a})))
        (is (= #{} (nearest above false 'n #{})))))))

(deftest genl-closures
  (let [t (tax/create-taxonomy)]
    (tax/add-genl t 'dog 'animal 1)
    (tax/add-genl t 'animal 'thing 2)
    (tax/add-genl t 'cat 'animal 3)
    (testing "reflexive-transitive up/down"
      (is (= '#{dog animal thing} (tax/genls-global t 'dog)))
      (is (= '#{animal dog cat} (tax/specs-global t 'animal)))
      (is (tax/genl?-global t 'dog 'thing))
      (is (not (tax/genl?-global t 'thing 'dog))))
    (testing "removing an edge recomputes the closure"
      (tax/del-genl! t 'dog 'animal 1)
      (is (not (tax/genl?-global t 'dog 'thing)))
      (is (= '#{dog} (tax/genls-global t 'dog))))))

(deftest an-edge-survives-while-any-supporter-remains
  (let [t (tax/create-taxonomy)]
    (testing "two sentexes assert the same edge — dropping one keeps it"
      (tax/add-genl t 'dog 'animal 1)
      (tax/add-genl t 'dog 'animal 2)
      (tax/del-genl! t 'dog 'animal 1)
      (is (tax/genl?-global t 'dog 'animal)))
    (testing "dropping the last supporter removes it"
      (tax/del-genl! t 'dog 'animal 2)
      (is (not (tax/genl?-global t 'dog 'animal))))))

(deftest closures-follow-belief
  (let [t (tax/create-taxonomy)]
    (tax/add-genl t 'dog 'animal 1)
    (tax/add-genl t 'animal 'thing 2)
    (testing "a disbelieved supporter withdraws its edge"
      (tax/refresh-beliefs t #{2})                    ; only #2 is IN
      (is (not (tax/genl?-global t 'dog 'animal)))
      (is (tax/genl?-global t 'animal 'thing)))
    (testing "and believing it again revives the edge"
      (tax/refresh-beliefs t #{1 2})
      (is (tax/genl?-global t 'dog 'thing)))
    (testing "an edge with one believed supporter of two stays active"
      (tax/add-genl t 'dog 'animal 9)
      (tax/refresh-beliefs t #{2 9})                  ; #1 out, #9 in
      (is (tax/genl?-global t 'dog 'animal)))))

(deftest clear-relations-keeps-the-stored-supporters-a-refresh-installs-from
  ;; `recover` is a clear and a refresh with no region: the supporters are stored content
  ;; in the index, so the clear leaves them and the refresh installs what belief admits
  (let [t (tax/create-taxonomy)]
    (tax/add-genl t 'dog 'animal 1)
    (tax/add-genlCx t 'CxBio 'CxUniverse 2)
    (tax/clear-relations! t)
    (testing "both transitive relations are empty"
      (is (empty? (tax/genl-edges t)))
      (is (empty? (tax/genlCx-edges t)))
      (is (not (tax/genl?-global t 'dog 'animal))))
    (testing "a refresh installs the believed supporters' edges"
      (tax/refresh-beliefs t #{2})
      (is (= #{'[CxBio CxUniverse]} (tax/genlCx-edges t)))
      (is (empty? (tax/genl-edges t))))))

;; ---- the four flat caches follow belief the same way --------------------
;; `refresh-beliefs` reconciles `disjoint`, the disjoint metatypes + members, the
;; predicate properties, and `inverse` against belief, keyed on the supporters stored
;; under each key.  Bare integer handles again — the belief question is the same wherever
;; they came from.

(defn- transpose-supporters
  "The supporter family of `t`'s store read the other way: which keys each handle
  supports, as `{handle #{k}}`."
  [t]
  (reduce-kv (fn [m k supporters]
               (reduce (fn [m h] (update m h (fnil conj #{}) k)) m (keys supporters)))
             {} (reads/as-stored-supporter-map (:index @t))))

(defn- installed-keys
  "`[:tax-installs h]` for every handle `handles` names, as `{handle #{k}}`, the empty
  sets left out."
  [t handles]
  (into {} (keep (fn [h] (let [ks (reads/as-stored-installed-keys (:index @t) h)]
                           (when (seq ks) [h ks]))))
        handles))

(deftest disjoint-follows-belief
  (let [t (tax/create-taxonomy)]
    (tax/add-disjoint t 'dog 'cat 1)
    (is (tax/disjoint? t 'dog 'cat))
    (testing "a disbelieved supporter drops the pair"
      (tax/refresh-beliefs t #{})
      (is (not (tax/disjoint? t 'dog 'cat))))
    (testing "and believing it again revives it"
      (tax/refresh-beliefs t #{1})
      (is (tax/disjoint? t 'dog 'cat)))))

(deftest disjoint-refcount-crosses-belief
  (let [t (tax/create-taxonomy)]
    (tax/add-disjoint t 'dog 'cat 1)
    (tax/add-disjoint t 'dog 'cat 2)                    ; two contexts, one pair
    (testing "one of two supporters disbelieved: the pair stands"
      (tax/refresh-beliefs t #{2})
      (is (tax/disjoint? t 'dog 'cat)))
    (testing "both disbelieved: it drops"
      (tax/refresh-beliefs t #{})
      (is (not (tax/disjoint? t 'dog 'cat))))
    (testing "retracting one supporter leaves the other to hold it"
      (tax/refresh-beliefs t #{1 2})
      (tax/del-disjoint! t 'dog 'cat 1)
      (is (tax/disjoint? t 'dog 'cat)))))

(deftest predicate-property-follows-belief
  (let [t (tax/create-taxonomy)]
    (tax/mark-prop t :symmetric 'siblingOf 1)
    (is (tax/has-prop? t :symmetric 'siblingOf))
    (tax/refresh-beliefs t #{})
    (is (not (tax/has-prop? t :symmetric 'siblingOf)))
    (tax/refresh-beliefs t #{1})
    (is (tax/has-prop? t :symmetric 'siblingOf))))

(deftest inverse-follows-belief
  (let [t (tax/create-taxonomy)]
    (tax/add-inverse t 'parentOf 'childOf 1)
    (is (= 'childOf (tax/inverse-of t 'parentOf)))
    (is (= 'parentOf (tax/inverse-of t 'childOf)))
    (testing "defeat drops both directions"
      (tax/refresh-beliefs t #{})
      (is (nil? (tax/inverse-of t 'parentOf)))
      (is (nil? (tax/inverse-of t 'childOf))))
    (testing "revival restores both"
      (tax/refresh-beliefs t #{1})
      (is (= 'childOf (tax/inverse-of t 'parentOf)))
      (is (= 'parentOf (tax/inverse-of t 'childOf))))))

(deftest disjoint-metatype-follows-belief
  (let [t (tax/create-taxonomy)]
    (tax/mark-disjoint-metatype t 'species 1)
    (tax/add-metatype-member t 'species 'dog 2)
    (tax/add-metatype-member t 'species 'cat 3)
    (is (tax/disjoint? t 'dog 'cat))
    (testing "defeating the metatype mark stops it separating anyone"
      (tax/refresh-beliefs t #{2 3})                    ; #1 (the mark) out
      (is (not (tax/disjoint? t 'dog 'cat))))
    (testing "reviving the mark brings the whole clique back — members were kept"
      (tax/refresh-beliefs t #{1 2 3})
      (is (tax/disjoint? t 'dog 'cat)))
    (testing "defeating one member releases only that member's pairs"
      (tax/add-metatype-member t 'species 'fish 4)
      (tax/refresh-beliefs t #{1 2 4})                  ; cat (#3) out
      (is (not (tax/disjoint? t 'dog 'cat)))
      (is (tax/disjoint? t 'dog 'fish)))))

(deftest unmarking-a-metatype-takes-its-members-handles-with-it
  ;; Unmarking is the one teardown that retires supporters the caller never named: every
  ;; member's, with the mark's last.  The installed-key family is not decoration:
  ;; `refresh-beliefs` reads it forward to decide which flat-cache entries a settle has to
  ;; reconcile, so a stale handle puts a key nothing supports into the scope of every
  ;; settle that relabels *that* sentex — for the life of the KB, since nothing ever
  ;; removes it.
  (let [t       (tax/create-taxonomy)
        handles #(installed-keys t (range 1 7))
        dirty   #(:cache-dirty @t)]
    (tax/mark-disjoint-metatype t 'species 1)
    (doseq [[h ty] (map vector [2 3 4] '[dog cat fish])]
      (tax/add-metatype-member t 'species ty h))
    (tax/add-disjoint t 'plant 'mineral 5)
    ;; a second supporter for one member, so the entry is *shared* — which is the only
    ;; shape a belief-blind writer marks dirty, and so the only shape whose mark this
    ;; teardown can strand
    (tax/add-metatype-member t 'species 'dog 6)
    (is (= '{1 #{[:metatype species]} 2 #{[:member species dog]}
             3 #{[:member species cat]} 4 #{[:member species fish]}
             5 #{[:disjoint #{plant mineral}]} 6 #{[:member species dog]}}
           (handles)))
    (is (contains? (dirty) '[:member species dog])
        "the shared entry owes a reconcile before the teardown")
    (tax/unmark-disjoint-metatype! t 'species 1)
    (testing "the mark, the members, and every handle behind them are gone"
      (is (empty? (tax/disjoint-metatypes t)))
      (is (empty? (tax/metatype-members t 'species)))
      (is (= '{5 #{[:disjoint #{plant mineral}]}} (handles))
          "and only the unrelated declaration's handle is left"))
    (testing "and the dirty mark goes with them, not just the handles"
      ;; `:cache-dirty` names keys too, and a mark left on a key nothing supports is
      ;; worse than a stranded handle: a stranded handle only
      ;; widens the scope of a settle that relabels *that* sentex, where a stranded mark
      ;; widens **every** settle, moved or not, for the life of the KB.
      (is (not (contains? (dirty) '[:member species dog])))
      (is (empty? (dirty))))
    (testing "the invariant behind the scope: the installed keys are the supporters, transposed"
      (is (= (handles) (transpose-supporters t))))))

(deftest the-last-supporter-of-an-entry-takes-its-dirty-mark-with-it
  ;; The `support-drop` half of the claim above.  A shared entry is marked dirty by the
  ;; belief-blind writers, and the mark is discharged by a reconcile — but an entry whose
  ;; last supporter is retracted is never reconciled again, because `refresh-cache-support`
  ;; skips a key with no stored supporter.  So the drop has to clear the mark
  ;; itself; left behind, it is in the scope of every settle from then on and nothing ever
  ;; takes it out.  Costs work rather than answers, which is exactly why no other test
  ;; would notice.
  (let [t     (tax/create-taxonomy)
        dirty #(:cache-dirty @t)
        k     '[:disjoint #{dog cat}]]
    (tax/add-disjoint t 'dog 'cat 1 'CxA)
    (is (empty? (dirty)) "one supporter is exact, so nothing is owed")
    (tax/add-disjoint t 'dog 'cat 2 'CxB)
    (is (= #{k} (dirty)) "a second supporter makes the recorded contexts a superset")
    (testing "dropping one of two leaves the entry standing, and still owing"
      (tax/del-disjoint! t 'dog 'cat 1)
      (is (= #{k} (dirty)))
      (is (tax/disjoint? t 'dog 'cat)))
    (testing "dropping the last takes the entry, and the mark with it"
      (tax/del-disjoint! t 'dog 'cat 2)
      (is (not (tax/disjoint? t 'dog 'cat)))
      (is (empty? (tax/supporters t k)) "the entry is gone")
      (is (empty? (dirty)) "so nothing is left owing a reconcile it can never get"))))

;; ---- the incremental closure, checked against the reference ---------------

(defn- oracle
  "What a from-scratch materialized rebuild says about the current edge set — the
  reference `closures`, keyed by node."
  [t rel-key]
  (select-keys (tax/closures (get-in @t [rel-key :edges])) [:up :down]))

(defn- incremental
  "What the live on-demand accessors say, one up/down closure per node the reference
  build knows about.  The taxonomy does not materialize `:up` / `:down`; it stores
  adjacency and answers `genls` / `specs` on demand, so the oracle compares those
  answers against the reference rather than a stored map."
  [t rel-key]
  (let [[up-fn dn-fn] (if (= rel-key :genlCx)
                        [tax/context-up tax/context-down]
                        [tax/genls-global tax/specs-global])
        nodes (into #{} (mapcat identity) (get-in @t [rel-key :edges]))]
    {:up   (into {} (map (fn [n] [n (up-fn t n)])) nodes)
     :down (into {} (map (fn [n] [n (dn-fn t n)])) nodes)}))

(defn- agrees?
  "Does the incrementally-maintained adjacency answer every closure exactly as a
  from-scratch materialized rebuild would?"
  [t rel-key] (= (incremental t rel-key) (oracle t rel-key)))

(deftest incremental-closure-agrees-with-a-full-rebuild
  ;; The interesting cases are the ones where a pair survives an edge deletion by an
  ;; alternative path, and where deleting an edge isolates a node entirely.
  (testing "a diamond: removing one side keeps what the other still proves"
    (let [t (tax/create-taxonomy)]
      (tax/add-genl t 'd 'l 1) (tax/add-genl t 'd 'r 2)
      (tax/add-genl t 'l 'top 3) (tax/add-genl t 'r 'top 4)
      (is (agrees? t :genl))
      (tax/del-genl! t 'l 'top 3)
      (is (agrees? t :genl))
      (is (tax/genl?-global t 'd 'top))                        ; still reachable via r
      (tax/del-genl! t 'r 'top 4)
      (is (agrees? t :genl))
      (is (not (tax/genl?-global t 'd 'top)))))
  (testing "deleting the only edge at a node drops it from the taxonomy entirely"
    (let [t (tax/create-taxonomy)]
      (tax/add-genl t 'x 'y 1)
      (is (some #{'x} (tax/types t)))
      (tax/del-genl! t 'x 'y 1)
      (is (agrees? t :genl))
      (is (empty? (tax/types t)))))                     ; not merely isolated — gone
  (testing "inserting into the middle of a chain rewires both ancestor sets"
    (let [t (tax/create-taxonomy)]
      (tax/add-genl t 'a 'b 1) (tax/add-genl t 'c 'd 2)
      (tax/add-genl t 'b 'c 3)                          ; joins the two chains
      (is (agrees? t :genl))
      (is (tax/genl?-global t 'a 'd)))))

(deftest incremental-closure-survives-random-edit-sequences
  ;; Oracle comparison over pseudo-random DAGs. Edges only ever point from a lower
  ;; index to a higher one, so no sequence can produce a cycle — `reachable?`'s depth
  ;; pruning assumes acyclicity, and `wff` enforces it for real genl edges.
  ;; Deletion is the half that leaves depths loose, so the walk deletes from the
  ;; *live* set rather than hoping to re-pick an existing edge — otherwise deletions
  ;; are a few percent of the edits and the risky path is barely covered.
  (let [nodes (mapv #(symbol (str "n_" %)) (range 12))
        rnd   (java.util.Random. 42)                    ; fixed seed: a failure reproduces
        edge  (fn [] (let [i (.nextInt rnd (count nodes))
                           j (.nextInt rnd (count nodes))]
                       (when (< i j) [(nodes i) (nodes j)])))]
    (dotimes [trial 25]
      (let [t (tax/create-taxonomy), live (atom #{})]
        (dotimes [_ 40]
          (let [delete? (and (seq @live) (< (.nextInt rnd 10) 4))
                [a b]   (if delete?
                          (nth (sort @live) (.nextInt rnd (count @live)))
                          (edge))]
            (when a
              (if delete?
                (do (tax/del-genl! t a b 1) (swap! live disj [a b]))
                (do (tax/add-genl t a b 1) (swap! live conj [a b])))
              ;; the invariant, after every single edit
              (is (agrees? t :genl)
                  (str "trial " trial " diverged after "
                       (if delete? "deleting " "adding ") [a b]
                       "\n  incremental: " (pr-str (incremental t :genl))
                       "\n  oracle:      " (pr-str (oracle t :genl)))))))))))

(deftest the-closure-cache-bound-follows-the-node-count
  (let [t      (tax/create-taxonomy)
        bound  #((:limit (:closure-lru @t)))
        per    @#'tax/closure-terms-per-node
        floor  (caches/limit-of :taxonomy-closures @#'tax/closure-terms-floor)
        n      (inc (quot @#'tax/closure-terms-floor per))
        node   #(symbol (str "n_" %))]
    (is (= floor (bound)))
    (dotimes [i n] (tax/add-genl t (node i) (node (inc i)) i))
    (is (= (caches/limit-of :taxonomy-closures (* per (inc n))) (bound)))
    (dotimes [i n] (tax/del-genl! t (node i) (node (inc i)) i))
    (is (= floor (bound)))))

(deftest an-up-closure-built-from-its-parents-agrees-under-any-bound
  ;; `reach-by-parents` builds an up-closure from the closures of its parents, which the
  ;; LRU holds: under a roomy bound every ancestor is found built, under a tight one a
  ;; parent is evicted between the reads and the build falls back to the walk.  Cycles
  ;; are walked as components; under `*defer-cycle-scc?*` a cycle closed since the last
  ;; `restore-depths` is missing from `:scc`, and the build falls back to the walk.  Every
  ;; answer is the reference rebuild's, over random edit sequences with diamonds and
  ;; cycles.
  (let [nodes (mapv #(symbol (str "d_" %)) (range 14))
        rnd   (java.util.Random. 271828)]
    (doseq [bound [nil 7 1], defer? [false true]]
      (caches/set-limit :taxonomy-closures bound)
      (try
        (binding [tax/*defer-depths?*    defer?
                  tax/*defer-cycle-scc?* defer?]
          (dotimes [trial 12]
            (let [t (tax/create-taxonomy), live (atom #{})]
              (dotimes [_ 40]
                (let [delete? (and (seq @live) (< (.nextInt rnd 10) 3))
                      i       (.nextInt rnd (count nodes))
                      ;; mostly downhill, so components are the exception they are
                      j       (if (< (.nextInt rnd 10) 2)
                                (.nextInt rnd (count nodes))
                                (+ i (.nextInt rnd (- (count nodes) i))))
                      [a b]   (if delete?
                                (nth (sort @live) (.nextInt rnd (count @live)))
                                (when (not= i j) [(nodes i) (nodes j)]))]
                  (when a
                    (if delete?
                      (do (tax/del-genl! t a b 1) (swap! live disj [a b]))
                      (do (tax/add-genl t a b 1) (swap! live conj [a b])))
                    ;; the upward reads first, in a seeded order, so a closure is built
                    ;; before the ancestors whose closures it is built from
                    (doseq [n (sort-by (fn [_] (.nextInt rnd)) nodes)] (tax/genls-global t n))
                    (is (agrees? t :genl)
                        (str "bound " bound " defer " defer? " trial " trial " after "
                             (if delete? "deleting " "adding ") [a b]))))))))
        (finally (caches/set-limit :taxonomy-closures nil))))))

;; ---- genls-global-among ---------------------------------------------------

(deftest a-closure-cut-to-marked-terms-agrees-with-the-cut-reference
  ;; `genls-global-among` and `genls-global-union` build each answer from its parents' cuts, never the closure,
  ;; so it is checked against the reference closure cut to the marks: over the same
  ;; random edits as the up-closure build, diamonds and cycles, with cycles `:scc` has
  ;; not recorded under `*defer-cycle-scc?*` (the build falls back to cutting the
  ;; closure).  One memo shared across every node's read, in a seeded order so a cut is
  ;; built before the ancestors it is built from, a fresh memo per read, and no memo (the
  ;; walk down from the marks, pruned by the depth potential and unpruned while it is
  ;; loose); the marks are none, a few, or all.
  (let [nodes (mapv #(symbol (str "c_" %)) (range 14))
        rnd   (java.util.Random. 161803)]
    (doseq [defer? [false true]]
      (binding [tax/*defer-depths?*    defer?
                tax/*defer-cycle-scc?* defer?]
        (dotimes [trial 12]
          (let [t (tax/create-taxonomy), live (atom #{})]
            (dotimes [_ 40]
              (let [delete? (and (seq @live) (< (.nextInt rnd 10) 3))
                    i       (.nextInt rnd (count nodes))
                    j       (if (< (.nextInt rnd 10) 2)
                              (.nextInt rnd (count nodes))
                              (+ i (.nextInt rnd (- (count nodes) i))))
                    [a b]   (if delete?
                              (nth (sort @live) (.nextInt rnd (count @live)))
                              (when (not= i j) [(nodes i) (nodes j)]))]
                (when a
                  (if delete?
                    (do (tax/del-genl! t a b 1) (swap! live disj [a b]))
                    (do (tax/add-genl t a b 1) (swap! live conj [a b])))
                  (let [up (:up (oracle t :genl))]
                    (doseq [among [#{} (into #{} (filter (fn [_] (< (.nextInt rnd 4) 1))) nodes)
                                   (set nodes)]]
                      (let [memo (volatile! {})
                            cut  #(into #{} (filter among) (get up % #{%}))]
                        (doseq [n (sort-by (fn [_] (.nextInt rnd)) nodes)]
                          (is (= (cut n) (tax/genls-global-among t n among memo))
                              (str "shared memo, defer " defer? " trial " trial " node " n
                                   " marks " (sort among)))
                          (is (= (cut n) (tax/genls-global-among t n among (volatile! {})))
                              (str "fresh memo, defer " defer? " trial " trial " node " n
                                   " marks " (sort among)))
                          (is (= (cut n) (tax/genls-global-among t n among))
                              (str "walked down, defer " defer? " trial " trial " node " n
                                   " marks " (sort among))))))
                    ;; and a union of what a mapping makes of each term: labels of a few
                    ;; values each, as the arity index asks for the lengths bound above
                    (let [labels (into {} (keep (fn [n] (when (< (.nextInt rnd 3) 1)
                                                          [n (into #{} (filter (fn [_] (< (.nextInt rnd 2) 1))) [1 2 3])])))
                                       nodes)
                          memo   (volatile! {})]
                      (doseq [n (sort-by (fn [_] (.nextInt rnd)) nodes)]
                        (is (= (into #{} (mapcat labels) (get up n #{n}))
                               (tax/genls-global-union t n (mapcat labels) memo))
                            (str "union, defer " defer? " trial " trial " node " n
                                 " labels " (into (sorted-map) labels)))))))))))))))

(deftest genl?-agrees-with-reference-under-loose-depths
  ;; `genl?` / `sees?` answer reachability with a depth-pruned early-exit walk, *not*
  ;; by building the full closure `agrees?` compares.  The prune is sound only while
  ;; the depth potential holds (`edge x→y ⇒ depth[x] > depth[y]`); deletion leaves
  ;; depths loose, so this hammers `genl?` for **every ordered pair** against the
  ;; reference closure's membership after every add/delete — the direct regression test that a
  ;; loose depth never yields a wrong reachability verdict.
  (let [nodes (mapv #(symbol (str "m_" %)) (range 12))
        rnd   (java.util.Random. 314159)
        edge  (fn [] (let [i (.nextInt rnd (count nodes))
                           j (.nextInt rnd (count nodes))]
                       (when (< i j) [(nodes i) (nodes j)])))
        ref-up (fn [t] (:up (tax/closures (get-in @t [:genl :edges]))))]
    (dotimes [trial 25]
      (let [t (tax/create-taxonomy), live (atom #{})]
        (dotimes [_ 45]
          (let [delete? (and (seq @live) (< (.nextInt rnd 10) 5))  ; deletion-heavy
                [a b]   (if delete?
                          (nth (sort @live) (.nextInt rnd (count @live)))
                          (edge))]
            (when a
              (if delete?
                (do (tax/del-genl! t a b 1) (swap! live disj [a b]))
                (do (tax/add-genl t a b 1) (swap! live conj [a b])))
              (let [up (ref-up t)]
                (is (every? (fn [x] (every? (fn [y]
                                              (= (tax/genl?-global t x y)
                                                 (contains? (get up x #{x}) y)))
                                            nodes))
                            nodes)
                    (str "trial " trial " genl? diverged after "
                         (if delete? "deleting " "adding ") [a b]))))))))))

(deftest sees?-agrees-with-reference-over-cyclic-context-graphs
  ;; The `genlCx` twin of the test above, with the acyclicity restriction lifted —
  ;; `wff` refuses a context cycle at assert, but the taxonomy must still hold one a
  ;; recovered or foreign store presents, and this exercises the taxonomy layer directly
  ;; (`tax/add-genlCx`), past that check.  So the edge generator is free to point either
  ;; way, every trial closes cycles and splits them again, and `sees?` is checked for
  ;; **every ordered pair** against the reference closure.
  ;;
  ;; That is the regression test on the condensation potential.  A stale component would answer
  ;; *true* for a pair a deletion has just separated; a stale depth would answer
  ;; *false* for a real path.  Both are invisible to a closure comparison that only
  ;; ever reads a repaired taxonomy, so the pairs are checked while the relation is
  ;; still loose as well as after `restore-depths` has run.
  (let [nodes (mapv #(symbol (str "CxC" %)) (range 10))
        rnd   (java.util.Random. 271828)
        edge  (fn [] (let [i (.nextInt rnd (count nodes))
                           j (.nextInt rnd (count nodes))]
                       (when (not= i j) [(nodes i) (nodes j)])))
        ref-up (fn [t] (:up (tax/closures (get-in @t [:genlCx :edges]))))
        check  (fn [t trial what]
                 (let [up (ref-up t)]
                   (is (every? (fn [x] (every? (fn [y]
                                                 (= (tax/sees? t x y)
                                                    (contains? (get up x #{x}) y)))
                                               nodes))
                               nodes)
                       (str "trial " trial " sees? diverged " what))))]
    (dotimes [trial 20]
      (let [t (tax/create-taxonomy), live (atom #{})]
        (dotimes [step 40]
          (let [delete? (and (seq @live) (< (.nextInt rnd 10) 4))
                [a b]   (if delete?
                          (nth (sort @live) (.nextInt rnd (count @live)))
                          (edge))]
            (when a
              (if delete?
                (do (tax/del-genlCx! t a b 1) (swap! live disj [a b]))
                (do (tax/add-genlCx t a b 1) (swap! live conj [a b])))
              (check t trial (str (if delete? "deleting " "adding ") [a b]))
              (when (zero? (mod step 7))
                (tax/restore-depths t)
                (check t trial (str "repairing after " [a b]))))))
        (tax/restore-depths t)
        (check t trial "the final repair")))))

(deftest a-context-cycle-is-one-component-and-splits-when-an-edge-goes
  ;; BaseKB's own shape: a cycle admitted, read both ways, then broken.
  (let [t (tax/create-taxonomy)]
    (tax/add-genlCx t 'CxBaseKB 'CxUniversalVocabulary 1)
    (tax/add-genlCx t 'CxUniversalVocabulary 'CxBaseKB 2)
    (tax/add-genlCx t 'CxSomeTheory 'CxBaseKB 3)
    (tax/restore-depths t)
    (testing "the cycle is mutual visibility, and it composes with the rest of the ancestor set"
      (is (tax/sees? t 'CxBaseKB 'CxUniversalVocabulary))
      (is (tax/sees? t 'CxUniversalVocabulary 'CxBaseKB))
      (is (tax/sees? t 'CxSomeTheory 'CxUniversalVocabulary))
      (is (not (tax/sees? t 'CxUniversalVocabulary 'CxSomeTheory)))
      (is (= '#{CxBaseKB CxUniversalVocabulary CxUniverse}
             (tax/context-up t 'CxBaseKB)))
      (is (= '#{CxSomeTheory CxBaseKB CxUniversalVocabulary}
             (tax/context-down t 'CxUniversalVocabulary))))
    (testing "and dropping the back edge separates them again, immediately"
      ;; immediately: the answer may not wait for a settle, so the component is
      ;; dissolved by the deletion itself rather than by the repair that follows it
      (tax/del-genlCx! t 'CxUniversalVocabulary 'CxBaseKB 2)
      (is (not (tax/sees? t 'CxUniversalVocabulary 'CxBaseKB)))
      (is (tax/sees? t 'CxBaseKB 'CxUniversalVocabulary))
      (tax/restore-depths t)
      (is (not (tax/sees? t 'CxUniversalVocabulary 'CxBaseKB))))))

(deftest incremental-closure-agrees-through-belief-changes
  ;; refresh-beliefs applies the difference edge by edge; the result must still match
  ;; a rebuild of whatever edge set ends up active.
  (let [t (tax/create-taxonomy)]
    (tax/add-genl t 'p 'q 1)
    (tax/add-genl t 'q 'r 2)
    (tax/add-genl t 'p 'q 3)                            ; a second supporter for p->q
    (testing "withdrawing one supporter of a doubly-supported edge changes nothing"
      (tax/refresh-beliefs t #{2 3})
      (is (agrees? t :genl))
      (is (tax/genl?-global t 'p 'r)))
    (testing "withdrawing the last supporter drops the edge"
      (tax/refresh-beliefs t #{2})
      (is (agrees? t :genl))
      (is (not (tax/genl?-global t 'p 'r))))
    (testing "and restoring belief brings it back"
      (tax/refresh-beliefs t #{1 2 3})
      (is (agrees? t :genl))
      (is (tax/genl?-global t 'p 'r)))))

;; ---- the derived context state -------------------------------------------
;; `:edge-ctxs` carries each active edge's supporting contexts, a function of
;; `:support` and belief the way `:edges` is — the oracle at the end recomputes exactly
;; that.

(deftest edge-contexts-track-supporters
  (let [t (tax/create-taxonomy)]
    (tax/add-genl t 'dog 'animal 1 'CxA)
    (is (= '#{CxA} (tax/edge-contexts t :genl '[dog animal])))
    (tax/add-genl t 'dog 'animal 2 'CxB)
    (is (= '#{CxA CxB} (tax/edge-contexts t :genl '[dog animal])))
    (tax/del-genl! t 'dog 'animal 1)
    (is (= '#{CxB} (tax/edge-contexts t :genl '[dog animal])))
    (tax/del-genl! t 'dog 'animal 2)
    (is (= #{} (tax/edge-contexts t :genl '[dog animal])))
    (testing "a contextless supporter records nil — the constrains-everywhere reading"
      (tax/add-genl t 'dog 'animal 3)
      (is (= #{nil} (tax/edge-contexts t :genl '[dog animal]))))))

(deftest a-context-only-belief-move-retargets-the-edge
  ;; the case the two-arm liveness diff cannot see: an edge supported from two
  ;; contexts keeps its liveness while one supporter's belief moves.  Its context
  ;; must leave `:edge-ctxs`, or a scoped read from there would answer through a
  ;; defeated supporter.
  (let [t (tax/create-taxonomy)]
    (tax/add-genl t 'dog 'animal 1 'CxA)
    (tax/add-genl t 'dog 'animal 2 'CxB)
    (is (= '#{CxA CxB} (tax/edge-contexts t :genl '[dog animal])))
    (tax/refresh-beliefs t #{1})
    (testing "the edge stays active while B's support leaves"
      (is (tax/genl?-global t 'dog 'animal))
      (is (= '#{CxA} (tax/edge-contexts t :genl '[dog animal]))))
    (tax/refresh-beliefs t #{2})
    (is (= '#{CxB} (tax/edge-contexts t :genl '[dog animal])))
    (tax/refresh-beliefs t #{})
    (is (= #{} (tax/edge-contexts t :genl '[dog animal])))
    (tax/refresh-beliefs t #{1 2})
    (is (= '#{CxA CxB} (tax/edge-contexts t :genl '[dog animal])))))

(deftest a-context-only-move-retires-the-read-memo
  ;; a scoped closure read is a function of `:edge-ctxs`, so a context-only move
  ;; must bump `:gen` exactly as an edge change does — and a belief-preserving
  ;; refresh must not, or every settle would empty the memo.
  (let [t (tax/create-taxonomy)
        gen #(get-in @t [:genl :gen])]
    (tax/add-genl t 'dog 'animal 1 'CxA)
    (tax/add-genl t 'dog 'animal 2 'CxB)
    (let [g (gen)]
      (tax/refresh-beliefs t #{1})
      (is (> (gen) g) "a context-only move bumps"))
    (let [g (gen)]
      (tax/refresh-beliefs t #{1})
      (is (= g (gen)) "a belief-preserving refresh does not"))))

(defn- edge-ctxs-oracle
  "What `:edge-ctxs` must equal after a refresh under `believed?`: the believed
  supporters' contexts of every edge that has at least one, straight off the stored
  supporters."
  [t rel-key believed?]
  (reduce-kv (fn [m [kind a b] hs]
               (let [cs (reduce-kv (fn [s h c] (if (believed? h) (conj s c) s)) #{} hs)]
                 (if (and (= rel-key kind) (seq cs)) (assoc m [a b] cs) m)))
             {} (reads/as-stored-supporter-map (:index @t))))

(deftest derived-context-state-agrees-with-a-recompute-after-random-edits
  ;; the phase oracle: after ANY edit sequence the keys of `:edge-ctxs` are exactly
  ;; `:edges`, and after each
  ;; refresh `:edge-ctxs` equals the believed-supporter contexts recomputed from
  ;; scratch.  Deterministic seed; edges only ever point up the node order, so the
  ;; graph stays a DAG and the depth machinery is exercised on its own terms.
  (let [t      (tax/create-taxonomy)
        rnd    (java.util.Random. 42)
        nodes  '[na nb nc nd ne nf ng]
        ctxs   ['CxA 'CxB 'CxC nil]
        live   (atom {})                                     ; handle -> [sub super]
        next-h (atom 0)]
    (dotimes [_ 400]
      (let [op (.nextInt rnd 3)]
        (cond
          (or (zero? op) (empty? @live))
          (let [i (.nextInt rnd (dec (count nodes)))
                j (+ i 1 (.nextInt rnd (- (count nodes) i 1)))
                h (swap! next-h inc)
                c (nth ctxs (.nextInt rnd (count ctxs)))]
            (tax/add-genl t (nth nodes i) (nth nodes j) h c)
            (swap! live assoc h [(nth nodes i) (nth nodes j)]))

          (= 1 op)
          (let [[h [x y]] (nth (vec @live) (.nextInt rnd (count @live)))]
            (tax/del-genl! t x y h)
            (swap! live dissoc h))

          :else
          (let [believed (into #{} (filter (fn [_] (.nextBoolean rnd))) (keys @live))]
            (tax/refresh-beliefs t believed)
            (is (= (edge-ctxs-oracle t :genl believed)
                   (get-in @t [:genl :edge-ctxs]))
                "after a refresh, :edge-ctxs is the believed recompute")))
        (is (= (set (keys (get-in @t [:genl :edge-ctxs])))
               (get-in @t [:genl :edges]))
            ":edge-ctxs keys are exactly the active edges")))))

(deftest the-handle-index-is-the-exact-reverse-of-support
  ;; The installed-key family is what scopes the belief reconcile to the moved region, and
  ;; it is only sound while it is *exact*: a supporter missing from it is an edge a settle
  ;; would skip, which shows up as a stale closure and not as a crash.  It is the
  ;; transpose of the supporter family after every edit — including the two that are easy
  ;; to get wrong, a shared edge losing one of its supporters and a supporter re-asserting
  ;; an edge it already holds.
  (let [exact? (fn [t] (= (transpose-supporters t) (installed-keys t (range 100))))
        t      (tax/create-taxonomy)]
    (tax/add-genl t 'p 'q 1)
    (tax/add-genl t 'q 'r 2)
    (tax/add-genl t 'p 'q 3)                            ; a second supporter for p->q
    (is (exact? t))
    (testing "a redundant re-assert of an edge a handle already supports"
      (tax/add-genl t 'p 'q 3)
      (is (exact? t)))
    (testing "the shared edge loses one supporter and keeps the other"
      (tax/del-genl! t 'p 'q 1)
      (is (exact? t))
      (is (tax/genl?-global t 'p 'r)))
    (testing "and the last supporter of an edge takes its entry with it"
      (tax/del-genl! t 'p 'q 3)
      (is (exact? t))
      (is (empty? (reads/as-stored-installed-keys (:index @t) 3))))
    (testing "a delete naming a handle that never supported the edge changes nothing"
      (tax/del-genl! t 'q 'r 99)
      (is (exact? t))
      (is (tax/genl?-global t 'q 'r)))))

(deftest a-scoped-reconcile-answers-as-an-unconditional-one-does
  ;; `refresh-beliefs` is handed the region a settle relabelled and reconciles only the
  ;; edges a handle in it supports — an edge no moved handle touches cannot have changed
  ;; which of its supporters are believed, so it is left alone.  That is the locality
  ;; claim for this cache, and the way it fails is silent: a stale edge answers `isa?`
  ;; for a type nothing believes any more.
  ;;
  ;; So drive the *scoped* arity, which the oracles above do not — they pass no moved set
  ;; and take the unconditional pass — and check the same two references after every
  ;; step: the believed recompute of `:edge-ctxs`, and the from-scratch closure over
  ;; whatever edge set survived.  `moved` is the exact flip set, computed as a diff
  ;; against the previous belief, and a handle joins it on the edit that creates it —
  ;; which is what `settle` hands over, an assert being believed as it integrates.
  (let [nodes  (mapv #(symbol (str "s_" %)) (range 9))
        ctxs   ['CxA 'CxB nil]
        rnd    (java.util.Random. 1234)]                ; fixed seed: a failure reproduces
    (dotimes [trial 30]
      (let [t        (tax/create-taxonomy)
            live     (atom {})                          ; handle -> [sub super]
            believed (atom #{})
            next-h   (atom 0)]
        (dotimes [_ 120]
          (let [op (.nextInt rnd 4)]
            (cond
              ;; a fresh supporter arrives believed, and says so
              (or (zero? op) (empty? @live))
              (let [i (.nextInt rnd (dec (count nodes)))
                    j (+ i 1 (.nextInt rnd (- (count nodes) i 1)))
                    h (swap! next-h inc)
                    c (nth ctxs (.nextInt rnd (count ctxs)))]
                (tax/add-genl t (nth nodes i) (nth nodes j) h c)
                (swap! live assoc h [(nth nodes i) (nth nodes j)])
                (swap! believed conj h)
                (tax/refresh-beliefs t @believed #{h}))

              ;; ...and a retraction takes its support out from under the edge
              (= 1 op)
              (let [[h [x y]] (nth (sort-by key @live) (.nextInt rnd (count @live)))]
                (tax/del-genl! t x y h)
                (swap! live dissoc h)
                (swap! believed disj h))

              ;; the case this test exists for: some supporters flip, most do not
              :else
              (let [ks      (sort (keys @live))
                    flipped (into #{} (filter (fn [_] (< (.nextInt rnd 4) 1))) ks)
                    now     (reduce (fn [b h] (if (b h) (disj b h) (conj b h)))
                                    @believed flipped)]
                (reset! believed now)
                (tax/refresh-beliefs t now flipped)
                (is (= (edge-ctxs-oracle t :genl now)
                       (get-in @t [:genl :edge-ctxs]))
                    (str "trial " trial ": a scoped refresh left :edge-ctxs stale"
                         "\n  flipped: " (pr-str flipped)
                         "\n  believed: " (pr-str now)))))
            (tax/restore-depths t)
            (is (agrees? t :genl)
                (str "trial " trial ": the closure disagreed with a rebuild after op " op))
            (is (= (set (keys (get-in @t [:genl :edge-ctxs])))
                   (get-in @t [:genl :edges]))
                ":edge-ctxs keys are exactly the active edges")))))))

(deftest cache-contexts-track-supporters-and-belief
  ;; the flat-cache twin: same discipline, point lookups instead of closures.
  (let [t (tax/create-taxonomy)
        k [:disjoint #{'dog 'cat}]]
    (tax/add-disjoint t 'dog 'cat 1 'CxA)
    (tax/add-disjoint t 'dog 'cat 2 'CxB)
    (is (= '#{CxA CxB} (tax/cache-contexts t k)))
    (testing "a context-only belief move retargets the entry"
      (tax/refresh-beliefs t #{1})
      (is (tax/disjoint? t 'dog 'cat) "the pair still constrains")
      (is (= '#{CxA} (tax/cache-contexts t k))))
    (testing "no believed supporter: inactive, and the contexts say so"
      (tax/refresh-beliefs t #{})
      (is (not (tax/disjoint? t 'dog 'cat)))
      (is (= #{} (tax/cache-contexts t k))))
    (testing "retracting the last supporter drops the entry whole"
      (tax/refresh-beliefs t #{1 2})
      (tax/del-disjoint! t 'dog 'cat 1)
      (tax/del-disjoint! t 'dog 'cat 2)
      (is (= #{} (tax/cache-contexts t k)))
      (is (nil? (get-in @t [:cache-ctxs k]))))))

;; ---- the flat caches, scoped to the moved region -------------------------

(def ^:private flat-decls
  "A pool of flat-cache declarations, deliberately overlapping: the driver below draws
  from it with repeats, so an entry routinely carries two or three supporters.  That is
  the form the belief-blind writers take for a superset, and the only shape `:cache-dirty`
  is about — a single-supporter entry is exact without it."
  '[[:disjoint d_a d_b]
    [:disjoint d_a d_c]
    [:disjoint d_b d_c]
    [:prop :symmetric relP]
    [:prop :transitive relP]
    [:prop :symmetric relQ]
    ;; two partners for one predicate, which nothing refuses: `:inverse` is many-to-many,
    ;; so defeating one of them must leave the other standing rather than clear `relP`
    [:inverse relP relQ]
    [:inverse relP relR]
    [:arity relP 2]
    [:arity relQ 3]
    [:metatype meta_m]
    [:member meta_m d_a]
    [:member meta_m d_b]])

(defn- decl-add [t [kind a b] h ctx]
  (case kind
    :disjoint (tax/add-disjoint t a b h ctx)
    :prop     (tax/mark-prop t a b h ctx)
    :inverse  (tax/add-inverse t a b h ctx)
    :arity    (tax/add-arity t a b h ctx)
    :metatype (tax/mark-disjoint-metatype t a h ctx)
    :member   (tax/add-metatype-member t a b h ctx)))

(defn- decl-del [t [kind a b] h]
  (case kind
    :disjoint (tax/del-disjoint! t a b h)
    :prop     (tax/unmark-prop! t a b h)
    :inverse  (tax/del-inverse! t a b h)
    :arity    (tax/del-arity! t a b h)
    :metatype (tax/unmark-disjoint-metatype! t a h)
    :member   (tax/del-metatype-member! t a b h)))

(def ^:private flat-cache-fields
  "Every answer the flat caches give, so the oracle compares the whole derived surface
  rather than the one entry a driver step happened to touch."
  [:disjoint :disjoint-index :disjoint-metatypes :metatype-members
   :props :inverse :arity :cache-ctxs])

(defn- flat-cache-oracle
  "What the flat caches must hold under `believed`: the **unconditional** reconcile of
  the very same stored supporters, run on a detached copy so the live taxonomy learns
  nothing of it.  That arm walks every entry and evaluates belief for each, which is the
  reference the scoped arm has to agree with entry for entry."
  [t believed]
  (let [ref (tax/detached-copy t)]
    (tax/refresh-beliefs ref believed nil)
    (select-keys @ref flat-cache-fields)))

(deftest a-scoped-flat-cache-reconcile-answers-as-an-unconditional-one-does
  ;; `refresh-beliefs` is handed the region a settle relabelled and reconciles only the
  ;; flat-cache entries a handle in it supports — an entry no moved handle supports cannot
  ;; have changed which of its supporters are believed, so it is left alone.  That is the
  ;; locality claim for these caches, and the way it fails is silent: a defeated
  ;; `(disjoint dog cat)` keeps refusing a membership, or a defeated `(inverse P Q)` keeps
  ;; answering the swapped goal.
  ;;
  ;; So drive the *scoped* arity, which the flat-cache tests above do not — they pass no
  ;; moved set and take the unconditional pass — and check the whole derived surface after
  ;; every reconcile against that same unconditional pass over a detached copy.  `moved`
  ;; is the exact flip set, computed as a diff against the previous belief, and a handle
  ;; joins it on the edit that creates it: what `settle` hands over, an assert being
  ;; believed as it integrates.  A *retraction* names nothing, which is the case
  ;; `:cache-dirty` exists for and the one this fails without.
  (let [ctxs ['CxA 'CxB nil]
        rnd  (java.util.Random. 90210)]                 ; fixed seed: a failure reproduces
    (dotimes [trial 25]
      (let [t        (tax/create-taxonomy)
            live     (atom {})                          ; handle -> declaration
            believed (atom #{})
            next-h   (atom 0)
            check!   (fn [step]
                       (is (= (flat-cache-oracle t @believed)
                              (select-keys @t flat-cache-fields))
                           (str "trial " trial ": a scoped reconcile left a flat cache "
                                "stale after " step "\n  believed: " (pr-str @believed))))]
        (dotimes [_ 100]
          (let [op (.nextInt rnd 4)]
            (cond
              ;; a fresh supporter arrives believed, and the settle that stores it says so
              (or (zero? op) (empty? @live))
              (let [d (nth flat-decls (.nextInt rnd (count flat-decls)))
                    h (swap! next-h inc)
                    c (nth ctxs (.nextInt rnd (count ctxs)))]
                (decl-add t d h c)
                (swap! live assoc h d)
                (swap! believed conj h)
                (tax/refresh-beliefs t @believed #{h})
                (check! "an assert"))

              ;; ...and a retraction takes its support out from under the entry, with no
              ;; reconcile of its own — exactly as the retract path leaves it
              (= 1 op)
              (let [[h d] (nth (sort-by key @live) (.nextInt rnd (count @live)))]
                (decl-del t d h)
                ;; Whatever is left supporting something is read back off the taxonomy
                ;; rather than tracked: unmarking the *last* supporter of a metatype drops
                ;; its members' entries wholesale, so handles the driver never named stop
                ;; being supporters in the same call.
                (let [alive (into #{} (keys (transpose-supporters t)))]
                  (swap! live #(into {} (filter (comp alive key)) %))
                  (swap! believed #(into #{} (filter alive) %))))

              ;; the case this test exists for: some supporters flip, most do not
              :else
              (let [ks      (sort (keys @live))
                    flipped (into #{} (filter (fn [_] (< (.nextInt rnd 4) 1))) ks)
                    now     (reduce (fn [b h] (if (b h) (disj b h) (conj b h)))
                                    @believed flipped)]
                (reset! believed now)
                (tax/refresh-beliefs t now flipped)
                (check! (str "a flip of " (pr-str flipped)))))
            (is (= (transpose-supporters t) (installed-keys t (range (inc @next-h))))
                (str "trial " trial ": the installed keys are not the transpose of "
                     "the supporters after op " op))))))))

(deftest genlCx-visibility
  (let [t (tax/create-taxonomy)]
    (tax/add-genlCx t 'CxBio 'CxUniverse 1)
    (tax/add-genlCx t 'CxChem 'CxUniverse 2)
    (testing "a specific context sees the general one"
      (is (tax/sees? t 'CxBio 'CxUniverse))
      (is (not (tax/sees? t 'CxUniverse 'CxBio))))))

(deftest placement
  (let [t (tax/create-taxonomy)]
    (tax/add-genlCx t 'CxBio 'CxUniverse 1)
    (tax/add-genlCx t 'CxChem 'CxUniverse 2)
    (testing "rule + facts all in the top context place at the top"
      (is (= '#{CxUniverse} (tax/maximal-common-descendant-contexts t '[CxUniverse CxUniverse]))))
    (testing "universal rule + specific facts place in the specific context"
      (is (= '#{CxBio} (tax/maximal-common-descendant-contexts t '[CxUniverse CxBio]))))
    (testing "incomparable contexts have no common view"
      (is (= #{} (tax/maximal-common-descendant-contexts t '[CxBio CxChem]))))))

(deftest placement-through-the-seeing-member
  ;; a member of `ctxs` that sees every other member is the unique maximum, answered
  ;; by sees? probes alone; the closure fallback must agree wherever both apply.
  (let [t (tax/create-taxonomy)]
    (tax/add-genlCx t 'CxBio 'CxUniverse 1)
    (tax/add-genlCx t 'CxChem 'CxUniverse 2)
    (tax/add-genlCx t 'CxWell 'CxBio 3)
    (tax/add-genlCx t 'CxWell 'CxChem 4)
    (tax/add-genlCx t 'CxLeft 'CxBio 5)
    (tax/add-genlCx t 'CxLeft 'CxChem 6)
    (testing "a chain places at its most specific member"
      (is (= '#{CxWell} (tax/maximal-common-descendant-contexts
                         t '[CxUniverse CxBio CxWell]))))
    (testing "duplicates collapse before the probes"
      (is (= '#{CxBio} (tax/maximal-common-descendant-contexts
                        t '[CxBio CxBio CxUniverse]))))
    (testing "incomparable maxima both survive the fallback"
      ;; Well and Left each see both siblings, neither sees the other — no seeing
      ;; member exists among [Bio Chem], so this is the closure path
      (is (= '#{CxWell CxLeft}
             (tax/maximal-common-descendant-contexts t '[CxBio CxChem]))))))

(deftest placement-over-mutually-visible-contexts
  ;; Two contexts in a `genlCx` cycle are equally general, so each is an ancestor
  ;; of the other and the maximality filter would strike both out — a firing with
  ;; nowhere to land.  They are one place to stand, and the one is chosen by content.
  (let [t (tax/create-taxonomy)]
    (tax/add-genlCx t 'CxAlpha 'CxBeta 1)
    (tax/add-genlCx t 'CxBeta 'CxAlpha 2)   ; the cycle
    (tax/add-genlCx t 'CxAlpha 'CxUniverse 3)
    (tax/restore-depths t)
    (testing "a cycle is one maximum, not two and not none"
      (is (= '#{CxAlpha}
             (tax/maximal-common-descendant-contexts t '[CxAlpha CxBeta]))))
    (testing "and which one does not depend on the order they were handed in"
      (is (= (tax/maximal-common-descendant-contexts t '[CxAlpha CxBeta])
             (tax/maximal-common-descendant-contexts t '[CxBeta CxAlpha]))))
    (testing "a rule above the cycle still places inside it"
      (is (= '#{CxAlpha}
             (tax/maximal-common-descendant-contexts t '[CxUniverse CxBeta]))))
    (testing "and a descendant of the cycle still wins, being strictly more specific"
      (tax/add-genlCx t 'CxWell 'CxAlpha 4)
      (tax/restore-depths t)
      (is (= '#{CxWell}
             (tax/maximal-common-descendant-contexts t '[CxWell CxBeta]))))))

(deftest placement-by-walk-matches-the-filtered-intersection
  ;; With no member seeing the others, the maxima are found by walking down from one
  ;; member; they must be the maxima of the whole intersection, cycles included.
  (let [rnd (java.util.Random. 57721)]                   ; fixed seed: a failure reproduces
    (dotimes [trial 40]
      (let [t  (tax/create-taxonomy)
            cx (vec (for [i (range 14)] (symbol (str "CxR" i))))]
        (doseq [i (range 1 14)]
          (tax/add-genlCx t (cx i) 'CxUniverse (* 100 i)))
        (dotimes [e 30]
          (let [a (.nextInt rnd 14) b (.nextInt rnd 14)]
            (when (not= a b) (tax/add-genlCx t (cx a) (cx b) (+ 10000 (* 100 trial) e)))))
        (tax/restore-depths t)
        (dotimes [_ 20]
          (let [cs (vec (repeatedly (+ 2 (.nextInt rnd 2)) #(cx (.nextInt rnd 14))))]
            (is (= (tax/max-cxs t (tax/common-descendants t cs))
                   (tax/maximal-common-descendant-contexts t cs))
                (str "trial " trial " " (pr-str cs)))))))))

(deftest common-descendant-existence
  ;; the boolean sibling of the placement function, for the callers that only ever
  ;; ask existence — asserted shape by shape, then against the full function wholesale.
  (let [t (tax/create-taxonomy)]
    (tax/add-genlCx t 'CxBio 'CxUniverse 1)
    (tax/add-genlCx t 'CxChem 'CxUniverse 2)
    (tax/add-genlCx t 'CxWell 'CxBio 3)
    (tax/add-genlCx t 'CxWell 'CxChem 4)
    (tax/add-genlCx t 'CxDeep 'CxWell 5)
    (tax/add-genlCx t 'CxOrphan 'CxElsewhere 6)
    (testing "a comparable pair answers through the seeing member"
      (is (tax/common-descendant? t '[CxUniverse CxBio]))
      (is (tax/common-descendant? t '[CxBio CxDeep])))
    (testing "incomparable siblings share their child"
      (is (tax/common-descendant? t '[CxBio CxChem])))
    (testing "no context sees both arms of a disconnected pair"
      (is (not (tax/common-descendant? t '[CxBio CxOrphan]))))
    (testing "every context sees CxUniverse, so it joins any pair one context sees"
      (is (tax/common-descendant? t '[CxUniverse CxElsewhere CxOrphan])))
    (testing "the empty family has no witness, a singleton is its own"
      (is (not (tax/common-descendant? t [])))
      (is (tax/common-descendant? t '[CxBio])))
    (testing "agreement with the maximal set over every context triple"
      (let [cs (vec (tax/contexts t))]
        (doseq [a cs, b cs, c cs]
          (is (= (boolean (seq (tax/maximal-common-descendant-contexts t [a b c])))
                 (tax/common-descendant? t [a b c]))
              (str "disagree on " [a b c])))))))

;; ---- equality: the partition over rewriteOf / sameAs / equals -------------
;;
;; `add-equality` takes the two terms, the handle of the sentex asserting the merge,
;; and which term (if either) that sentex names *preferred* — nil for `sameAs` and
;; `equals`, which merge without deprecating a name.

(deftest merging-two-terms
  (let [t (tax/create-taxonomy)]
    (tax/add-equality t 'Obama 'BarackObama 1 nil)
    (testing "both names now denote one thing"
      (is (tax/same-class? t 'Obama 'BarackObama))
      (is (= '#{Obama BarackObama} (tax/equiv-class t 'Obama)))
      (is (= (tax/representative t 'Obama) (tax/representative t 'BarackObama))))
    (testing "an unmerged term represents itself and is its own class"
      (is (= 'Biden (tax/representative t 'Biden)))
      (is (= '#{Biden} (tax/equiv-class t 'Biden)))
      (is (not (tax/same-class? t 'Obama 'Biden))))
    (testing "and same-class? is reflexive without any edge"
      (is (tax/same-class? t 'Biden 'Biden)))))

(deftest merges-chain-into-one-class
  (let [t (tax/create-taxonomy)]
    (tax/add-equality t 'A 'B 1 nil)
    (tax/add-equality t 'B 'C 2 nil)
    (tax/add-equality t 'C 'D 3 nil)
    (testing "transitivity: the chain is one class, not three pairs"
      (is (tax/same-class? t 'A 'D))
      (is (= '#{A B C D} (tax/equiv-class t 'D)))
      (is (= 1 (count (distinct (map #(tax/representative t %) '[A B C D]))))))))

(deftest a-rewriteOf-head-represents-the-whole-class
  (let [t (tax/create-taxonomy)]
    (testing "chains compose: rewriteOf A B + rewriteOf B C makes A represent all three"
      (tax/add-equality t 'A 'B 1 'A)                   ; (rewriteOf A B)
      (tax/add-equality t 'B 'C 2 'B)                   ; (rewriteOf B C)
      (is (= 'A (tax/representative t 'C)))
      (is (= 'A (tax/representative t 'B)))
      (is (= 'A (tax/representative t 'A))))
    (testing "a plain sameAs joining the class does not unseat the head"
      ;; Zulu sorts after A, so this only passes because the head rule beats the
      ;; lexicographic fallback rather than merely agreeing with it.
      (tax/add-equality t 'C 'Zulu 3 nil)
      (is (= 'A (tax/representative t 'Zulu))))
    (testing "nor does a sameAs member that sorts *before* the head"
      (tax/add-equality t 'C 'Aardvark 4 nil)
      (is (= 'A (tax/representative t 'Aardvark))))))

(deftest deprecated-marks-only-the-rewriteOf-loser
  (let [t (tax/create-taxonomy)]
    (tax/add-equality t 'Preferred 'Stale 1 'Preferred)
    (tax/add-equality t 'Xray 'Yankee 2 nil)            ; (sameAs Xray Yankee)
    (testing "the dispreferred side of a rewriteOf is deprecated"
      (is (tax/deprecated? t 'Stale)))
    (testing "the preferred side is not"
      (is (not (tax/deprecated? t 'Preferred))))
    (testing "a sameAs / equals member never is — neither name is being migrated off"
      (is (not (tax/deprecated? t 'Xray)))
      (is (not (tax/deprecated? t 'Yankee))))
    (testing "nor is a term nobody has merged"
      (is (not (tax/deprecated? t 'Untouched))))
    (testing "and a sameAs joining the deprecated term does not deprecate the joiner"
      (tax/add-equality t 'Stale 'Zulu 3 nil)
      (is (not (tax/deprecated? t 'Zulu)))
      (is (tax/deprecated? t 'Stale)))))

(deftest deprecation-follows-belief-and-support
  (let [t (tax/create-taxonomy)]
    (testing "one edge asserted twice — once as sameAs, once as rewriteOf"
      (tax/add-equality t 'Alpha 'Beta 1 nil)           ; (sameAs Alpha Beta)
      (tax/add-equality t 'Alpha 'Beta 2 'Beta)         ; (rewriteOf Beta Alpha)
      (is (tax/deprecated? t 'Alpha))
      (is (= 'Beta (tax/representative t 'Alpha))))
    (testing "disbelieving the rewriteOf withdraws the preference, not the merge"
      (tax/refresh-beliefs t #{1})
      (is (tax/same-class? t 'Alpha 'Beta))
      (is (not (tax/deprecated? t 'Alpha)))
      (is (= 'Alpha (tax/representative t 'Beta))))     ; lexicographic fallback
    (testing "and believing it again restores both"
      (tax/refresh-beliefs t #{1 2})
      (is (tax/deprecated? t 'Alpha))
      (is (= 'Beta (tax/representative t 'Alpha))))))

(deftest lexicographic-fallback
  (let [t (tax/create-taxonomy)]
    (testing "with no rewriteOf at all, the smallest symbol represents the class"
      (tax/add-equality t 'Yankee 'Alpha 1 nil)
      (tax/add-equality t 'Yankee 'Mike 2 nil)
      (is (= 'Alpha (tax/representative t 'Yankee))))
    (testing "a later, smaller member takes over — the rep is a function of content"
      (tax/add-equality t 'Mike 'Aardvark 3 nil)
      (is (= 'Aardvark (tax/representative t 'Yankee))))
    (testing "and it breaks a tie between two rewriteOf heads"
      (let [t (tax/create-taxonomy)]
        (tax/add-equality t 'Zulu 'Common 1 'Zulu)      ; (rewriteOf Zulu Common)
        (tax/add-equality t 'Mike 'Common 2 'Mike)      ; (rewriteOf Mike Common)
        (is (= 'Mike (tax/representative t 'Common)))
        (is (tax/deprecated? t 'Common))
        (is (not (tax/deprecated? t 'Zulu)))))))

;; The representative must be a function of the class's *content*.  Handles are
;; allocated in assertion order, so anything keyed on them smuggles arrival order
;; back into belief — the Nixon-diamond bug in docs/nmtms.md.  Permuting the edges
;; of a class is the direct test of that, and it is the property most likely to
;; break, so it gets an exhaustive one rather than a sampled one.

(defn- build
  "Apply `edits` (each [a b handle preferred]) to a fresh taxonomy."
  [edits]
  (let [t (tax/create-taxonomy)]
    (doseq [[a b h p] edits] (tax/add-equality t a b h p))
    t))

;; The representative is a function of the class's content.  Handles follow assertion
;; order, so a key on them lets arrival order into belief (docs/nmtms.md, the Nixon-diamond
;; tie-break).  Permuting the edges tests that directly, and it is the property most likely to
;; break, so the walk is exhaustive and not sampled.
(deftest representative-is-the-same-under-every-permutation
  (testing "a rewriteOf chain plus plain merges, however the edges arrive"
    (let [edits '[[Bravo Charlie 1 nil]                 ; (sameAs Bravo Charlie)
                  [Alpha Bravo 2 Alpha]                 ; (rewriteOf Alpha Bravo)
                  [Charlie Delta 3 nil]
                  [Delta Aardvark 4 nil]]]              ; sorts before the head
      (doseq [p (tu/permutations edits)]
        (let [t (build p)]
          (is (= 'Alpha (tax/representative t 'Delta))
              (str "permutation " (pr-str (mapv #(vec (take 2 %)) p))))
          (is (= '#{Alpha Bravo Charlie Delta Aardvark} (tax/equiv-class t 'Bravo)))))))
  (testing "two rewriteOf heads tie-broken lexicographically, however they arrive"
    (let [edits '[[Zulu Common 1 Zulu]
                  [Mike Common 2 Mike]
                  [Common Xray 3 nil]]]
      (doseq [p (tu/permutations edits)]
        (let [t (build p)]
          (is (= 'Mike (tax/representative t 'Xray))
              (str "permutation " (pr-str (mapv #(vec (take 2 %)) p))))))))
  (testing "the whole partition, not just the rep, is permutation-invariant"
    (let [edits '[[A B 1 nil] [C D 2 nil] [B C 3 nil] [E F 4 E]]]
      (is (= 1 (count (distinct (for [p (tu/permutations edits)]
                                  (select-keys (:equality @(build p))
                                               [:class :members :edges])))))))))

(deftest an-equality-survives-while-any-supporter-remains
  (let [t (tax/create-taxonomy)]
    (testing "two sentexes assert the same merge — dropping one keeps it"
      (tax/add-equality t 'Alpha 'Bravo 1 nil)
      (tax/add-equality t 'Alpha 'Bravo 2 nil)
      (tax/del-equality! t 'Alpha 'Bravo 1)
      (is (tax/same-class? t 'Alpha 'Bravo)))
    (testing "dropping the last supporter unmerges them"
      (tax/del-equality! t 'Alpha 'Bravo 2)
      (is (not (tax/same-class? t 'Alpha 'Bravo)))
      (is (= '#{Alpha} (tax/equiv-class t 'Alpha)))
      (is (empty? (tax/equality-edges t))))
    (testing "and the argument order of the retraction does not matter"
      (tax/add-equality t 'Alpha 'Bravo 3 nil)
      (tax/del-equality! t 'Bravo 'Alpha 3)             ; mirrored
      (is (not (tax/same-class? t 'Alpha 'Bravo))))))

(deftest equality-follows-belief
  (let [t (tax/create-taxonomy)]
    (tax/add-equality t 'Alpha 'Bravo 1 nil)
    (tax/add-equality t 'Bravo 'Charlie 2 nil)
    (testing "a disbelieved supporter withdraws its merge"
      (tax/refresh-beliefs t #{2})                      ; only #2 is IN
      (is (not (tax/same-class? t 'Alpha 'Bravo)))
      (is (tax/same-class? t 'Bravo 'Charlie))
      (is (= '#{Bravo Charlie} (tax/equiv-class t 'Charlie))))
    (testing "and believing it again revives the whole class"
      (tax/refresh-beliefs t #{1 2})
      (is (tax/same-class? t 'Alpha 'Charlie)))
    (testing "an edge with one believed supporter of two stays active"
      (tax/add-equality t 'Alpha 'Bravo 9 nil)
      (tax/refresh-beliefs t #{2 9})                    ; #1 out, #9 in
      (is (tax/same-class? t 'Alpha 'Charlie)))))

(deftest deleting-an-equality-can-split-a-class
  (testing "a split rebuilds both halves, each with its own representative"
    (let [t (tax/create-taxonomy)]
      (tax/add-equality t 'Zulu 'Alpha 1 'Zulu)         ; (rewriteOf Zulu Alpha)
      (tax/add-equality t 'Alpha 'Bravo 2 nil)          ; the bridge
      (tax/add-equality t 'Bravo 'Gamma 3 nil)
      (tax/add-equality t 'Delta 'Gamma 4 'Delta)       ; (rewriteOf Delta Gamma)
      (testing "one class, two heads, lexicographic tie-break"
        (is (= '#{Zulu Alpha Bravo Gamma Delta} (tax/equiv-class t 'Bravo)))
        (is (= 'Delta (tax/representative t 'Zulu))))
      (tax/del-equality! t 'Alpha 'Bravo 2)
      (testing "the class splits at the bridge"
        (is (not (tax/same-class? t 'Alpha 'Bravo)))
        (is (= '#{Zulu Alpha} (tax/equiv-class t 'Alpha)))
        (is (= '#{Bravo Gamma Delta} (tax/equiv-class t 'Gamma))))
      (testing "and each half recomputes its own head — no stale representative"
        (is (= 'Zulu (tax/representative t 'Alpha)))
        (is (= 'Delta (tax/representative t 'Gamma))))
      (testing "deprecation is recomputed with them"
        (is (tax/deprecated? t 'Alpha))
        (is (tax/deprecated? t 'Gamma))
        (is (not (tax/deprecated? t 'Bravo))))))
  (testing "a deletion with an alternative path does not split"
    (let [t (tax/create-taxonomy)]
      (tax/add-equality t 'Alpha 'Bravo 1 nil)
      (tax/add-equality t 'Bravo 'Charlie 2 nil)
      (tax/add-equality t 'Alpha 'Charlie 3 nil)        ; closes a triangle
      (tax/del-equality! t 'Alpha 'Charlie 3)
      (is (tax/same-class? t 'Alpha 'Charlie))
      (is (= '#{Alpha Bravo Charlie} (tax/equiv-class t 'Alpha)))
      (is (= 'Alpha (tax/representative t 'Charlie)))))
  (testing "a deletion that isolates a term drops it from the partition entirely"
    (let [t (tax/create-taxonomy)]
      (tax/add-equality t 'Alpha 'Bravo 1 nil)
      (tax/del-equality! t 'Alpha 'Bravo 1)
      (is (= {} (get-in @t [:equality :class])))        ; not merely singleton classes
      (is (= {} (get-in @t [:equality :members])))
      (is (= '#{Alpha} (tax/equiv-class t 'Alpha))))))

(deftest clear-relations-drops-the-equality-partition-too
  (let [t (tax/create-taxonomy)]
    (tax/add-equality t 'Alpha 'Bravo 1 'Alpha)
    (tax/clear-relations! t)
    (testing "edges, classes and deprecation are all gone"
      (is (empty? (tax/equality-edges t)))
      (is (not (tax/same-class? t 'Alpha 'Bravo)))
      (is (= 'Bravo (tax/representative t 'Bravo)))
      (is (not (tax/deprecated? t 'Bravo))))
    (testing "and a refresh cannot resurrect them — support went with the rest"
      (tax/refresh-beliefs t (constantly true))
      (is (empty? (tax/equality-edges t)))
      (is (not (tax/same-class? t 'Alpha 'Bravo))))))

;; ---- the incremental partition, checked against the reference -------------

(defn- eq-oracle
  "What a from-scratch rebuild says about the currently active edges and preferences."
  [t]
  (let [rel (:equality @t)]
    (tax/equality-partition (:edges rel) (into #{} cat (vals (:edge-prefs rel))))))

(defn- eq-incremental [t] (select-keys (:equality @t) [:class :members]))

(defn- eq-agrees? [t] (= (eq-incremental t) (eq-oracle t)))

(deftest incremental-partition-agrees-with-a-full-rebuild
  (testing "a union, a rep change, a split and an isolation each land where a rebuild does"
    (let [t (tax/create-taxonomy)]
      (tax/add-equality t 'Bravo 'Charlie 1 nil)   (is (eq-agrees? t))
      (tax/add-equality t 'Alpha 'Bravo 2 'Alpha)  (is (eq-agrees? t))
      (tax/add-equality t 'Delta 'Echo 3 nil)      (is (eq-agrees? t))
      (tax/add-equality t 'Charlie 'Delta 4 nil)   (is (eq-agrees? t))  ; joins both classes
      (tax/del-equality! t 'Charlie 'Delta 4)      (is (eq-agrees? t))  ; splits them again
      (tax/del-equality! t 'Delta 'Echo 3)         (is (eq-agrees? t))  ; isolates both
      (tax/del-equality! t 'Alpha 'Bravo 2)        (is (eq-agrees? t))))
  (testing "a second supporter adding a preference to a live edge"
    (let [t (tax/create-taxonomy)]
      (tax/add-equality t 'Alpha 'Bravo 1 nil)
      (is (= 'Alpha (tax/representative t 'Bravo)))
      (tax/add-equality t 'Alpha 'Bravo 2 'Bravo)       ; (rewriteOf Bravo Alpha)
      (is (= 'Bravo (tax/representative t 'Alpha)))
      (is (eq-agrees? t)))))

(deftest incremental-partition-survives-random-edit-sequences
  ;; The same oracle discipline the genl closures get, over pseudo-random merge
  ;; sequences with a fixed seed so a failure reproduces.  Deletion is the risky
  ;; half — insertion is a union, deletion can split a class and union-find cannot
  ;; undo a union — so the walk deletes from the *live* set rather than hoping to
  ;; re-pick an existing edge, and does so 40% of the time.  Roughly a third of the
  ;; merges carry a preference, so representatives churn as classes merge and split.
  (let [terms (mapv #(symbol (str "t_" %)) (range 10))
        rnd   (java.util.Random. 4242)]
    (dotimes [trial 25]
      (let [t (tax/create-taxonomy), live (atom {}), h (atom 0)]
        (dotimes [_ 45]
          (let [delete? (and (seq @live) (< (.nextInt rnd 10) 4))]
            (if delete?
              (let [[[a b :as e] hs] (nth (sort-by key @live) (.nextInt rnd (count @live)))
                    handle (first (sort hs))
                    left   (disj hs handle)]
                (tax/del-equality! t a b handle)
                (swap! live #(if (seq left) (assoc % e left) (dissoc % e)))
                (is (eq-agrees? t)
                    (str "trial " trial " diverged after deleting " (pr-str e)
                         " handle " handle)))
              (let [a    (terms (.nextInt rnd (count terms)))
                    b    (terms (.nextInt rnd (count terms)))
                    pref (case (.nextInt rnd 3) 0 a, 1 b, 2 nil)
                    hn   (swap! h inc)]
                (when (not= a b)
                  (tax/add-equality t a b hn pref)
                  (swap! live update (if (neg? (compare (str a) (str b))) [a b] [b a])
                         (fnil conj #{}) hn)
                  (is (eq-agrees? t)
                      (str "trial " trial " diverged after merging " a " " b
                           " preferring " pref)))))))
        ;; ...and belief withdrawal over whatever the sequence built
        (let [hs (into #{} (mapcat val) @live)
              believed (into #{} (filter even?) hs)]
          (tax/refresh-beliefs t believed)
          (is (eq-agrees? t) (str "trial " trial " diverged after a belief refresh"))
          (tax/refresh-beliefs t (constantly true))
          (is (eq-agrees? t) (str "trial " trial " diverged after restoring belief")))))))

;; ---- schematic rewrite rules: content order, memoized on the rule set -----
;;
;; The order `rewrite-rules` hands back is required — normalization tries rules in
;; it at each redex, so two rules that could rewrite one term must be ordered by content
;; or the stored normal form would depend on which equation arrived first.  Memoizing
;; that order is what keeps a `query` from re-sorting it per call, so the tests below ask
;; the two questions a memo owes: that it answers what the sort would have, and that
;; every writer of the rule set retires it.

(defn- rewrite-lhss [t] (mapv :lhs (tax/rewrite-rules t)))

(deftest rewrite-rules-are-content-ordered-however-they-arrive
  (letfn [(lhss [rs]
            (let [t (tax/create-taxonomy)]
              (doseq [[h l r] rs] (tax/add-rewrite-rule t h l r 'CxA))
              (rewrite-lhss t)))]
    (let [a [1 '(ff (ff ?x)) '(gg ?x)]
          b [2 '(hh (hh ?x)) '(ii ?x)]]
      (is (= (lhss [a b]) (lhss [b a]))
          "the same rule set in either order sorts to the same sequence")
      (is (= '[(ff (ff ?x)) (hh (hh ?x))] (lhss [b a]))
          "and that sequence is the content one, not the arrival one"))))

(deftest the-rewrite-order-is-memoized-until-the-rule-set-moves
  (let [t (tax/create-taxonomy)]
    (tax/add-rewrite-rule t 1 '(ff (ff ?x)) '(gg ?x) 'CxA)
    (is (identical? (tax/rewrite-rules t) (tax/rewrite-rules t))
        "with the rule set unmoved, a second read hands back the seq the first sorted")
    (testing "a second rule retires it"
      (tax/add-rewrite-rule t 2 '(hh (hh ?x)) '(ii ?x) 'CxA)
      (is (= '[(ff (ff ?x)) (hh (hh ?x))] (rewrite-lhss t))))
    (testing "defeating one retires it — the rule stops rewriting"
      (tax/refresh-beliefs t #{1})
      (is (= '[(ff (ff ?x))] (rewrite-lhss t))))
    (testing "and reviving it brings the rule back"
      (tax/refresh-beliefs t #{1 2})
      (is (= '[(ff (ff ?x)) (hh (hh ?x))] (rewrite-lhss t))))
    (testing "retracting the equation drops it outright"
      (tax/del-rewrite-rule! t 1)
      (is (= '[(hh (hh ?x))] (rewrite-lhss t))))
    (testing "and clear-relations! empties the set the memo answered from"
      (tax/clear-relations! t)
      (is (empty? (tax/rewrite-rules t))))))

(deftest a-detached-probe-cannot-poison-the-live-rewrite-order
  ;; A probe exists to be mutated where nothing learns of it, so it needs its own side
  ;; atom for the same reason `:closure-memo` does — a shared one would have the probe's
  ;; hypothetical rule answering a real read.
  (let [t (tax/create-taxonomy)]
    (tax/add-rewrite-rule t 1 '(ff (ff ?x)) '(gg ?x) 'CxA)
    (is (= '[(ff (ff ?x))] (rewrite-lhss t)))
    (let [probe (tax/detached-copy t)]
      (is (not (identical? (:rewrite-order @t) (:rewrite-order @probe)))
          "the copy's memo is its own atom, not the live one by reference")
      (tax/add-rewrite-rule probe 2 '(hh (hh ?x)) '(ii ?x) 'CxA)
      (is (= '[(ff (ff ?x)) (hh (hh ?x))] (rewrite-lhss probe)) "the probe sees its rule")
      (is (= '[(ff (ff ?x))] (rewrite-lhss t)) "and the live taxonomy does not")
      (testing "the live memo still answers its own rule set after the probe read"
        (tax/add-rewrite-rule t 3 '(jj (jj ?x)) '(kk ?x) 'CxA)
        (is (= '[(ff (ff ?x)) (jj (jj ?x))] (rewrite-lhss t)))))))

(deftest a-held-asserted-in-reach-answers-what-the-scoped-closure-holds
  ;; `genl-asserted-in?` is held in the closure cache under the relation's `:gen` and the
  ;; context set: every answer, asked twice and again after an edge moves, is membership
  ;; in the closure over the edges stated in the set
  (let [rnd  (java.util.Random. 5039)
        ns   (mapv #(symbol (str "n" %)) (range 10))
        sets [#{:a} #{:a :b} #{:b :c} #{:a :b :c}]
        seen (atom 0)]
    (dotimes [trial 8]
      (let [t     (tax/create-taxonomy)
            edges (atom [])
            h     (atom 0)
            add!  (fn [] (let [i (.nextInt rnd 9) j (+ i 1 (.nextInt rnd (- 9 i)))
                               c ([:a :b :c] (.nextInt rnd 3))
                               e [(ns i) (ns j) (swap! h inc)]]
                           (tax/add-genl t (ns i) (ns j) (peek e) c)
                           (swap! edges conj e)))
            check (fn [phase]
                    (doseq [ctxs sets, a ns, b ns]
                      (let [want (contains? (tax/genls-asserted-in t a ctxs) b)]
                        (when want (swap! seen inc))
                        (dotimes [_ 2]
                          (is (= want (tax/genl-asserted-in? t a b (set (seq ctxs))))
                              (str "trial " trial " " phase " " a " " b " " ctxs))))))]
        (dotimes [_ 14] (add!))
        (check :before)
        (let [[a b hd] (@edges (.nextInt rnd (count @edges)))]
          (tax/del-genl! t a b hd))
        (add!)
        (check :after)))
    (is (pos? @seen) "the taxonomies reach some pairs")))

(deftest an-asserted-among-reach-answers-what-the-scoped-closure-holds
  ;; `genls-asserted-among` is the scoped closure over the edges stated in the set, cut to
  ;; `among`: random taxonomies, some edges closing a cycle, every node against random
  ;; subsets and against every node, before and after an edge moves
  (let [rnd  (java.util.Random. 7211)
        ns   (mapv #(symbol (str "n" %)) (range 10))
        sets [#{:a} #{:a :b} #{:b :c} #{:a :b :c}]
        seen (atom 0)]
    (dotimes [trial 8]
      (let [t     (tax/create-taxonomy)
            edges (atom [])
            h     (atom 0)
            add!  (fn [] (let [i (.nextInt rnd 10)
                               j (if (< (.nextInt rnd 6) 1)
                                   (.nextInt rnd 10)
                                   (min 9 (+ i 1 (.nextInt rnd (max 1 (- 9 i))))))
                               c ([:a :b :c] (.nextInt rnd 3))]
                           (when (not= i j)
                             (let [e [(ns i) (ns j) (swap! h inc)]]
                               (tax/add-genl t (ns i) (ns j) (peek e) c)
                               (swap! edges conj e)))))
            check (fn [phase]
                    (doseq [ctxs sets, a ns
                            among (cons (set ns)
                                        (repeatedly 3 #(into #{} (filter (fn [_] (.nextBoolean rnd))) ns)))]
                      (let [want (into #{} (filter among) (tax/genls-asserted-in t a ctxs))]
                        (swap! seen + (count (disj want a)))
                        (is (= want (tax/genls-asserted-among t a among (set (seq ctxs))))
                            (str "trial " trial " " phase " " a " " among " " ctxs)))))]
        (dotimes [_ 16] (add!))
        (check :before)
        (when (seq @edges)
          (let [[a b hd] (@edges (.nextInt rnd (count @edges)))]
            (tax/del-genl! t a b hd)))
        (add!)
        (check :after)))
    (is (pos? @seen) "the taxonomies reach some terms")))

(deftest an-asserted-in-reach-walks-only-where-its-witness-path-cannot-answer
  ;; one path x → y → z, its edges stated in :a and :b
  (let [t     (tax/create-taxonomy)
        walks (atom 0)
        real  @#'tax/reachable-filtered?]
    (tax/add-genl t 'x 'y 1 :a)
    (tax/add-genl t 'y 'z 2 :b)
    (with-redefs [tax/reachable-filtered? (fn [& args] (swap! walks inc) (apply real args))]
      (is (tax/genl-asserted-in? t 'x 'z #{:a :b}))
      (is (zero? @walks) "a set stating the whole path is answered off it")
      (is (not (tax/genl-asserted-in? t 'z 'x #{:a :b})))
      (is (zero? @walks) "and a pair with no path through any edge walks nothing")
      (is (not (tax/genl-asserted-in? t 'x 'z #{:a :c})))
      (is (= 1 @walks) "a set stating part of the path walks")
      (is (not (tax/genl-asserted-in? t 'x 'z (set [:c :a]))))
      (is (= 1 @walks) "once for every reader asserting those contexts")
      (tax/add-genl t 'x 'z 3 :c)
      (is (tax/genl-asserted-in? t 'x 'z #{:a :c}))
      (is (= 1 @walks) "and an edge change reads the new path"))))

(deftest a-walk-up-over-the-missed-memo-answers-what-the-closure-answers
  ;; random graphs of 40 types, some edges closing a cycle, and targets at varied depths:
  ;; every type asked in a shuffled order over one memo per target set, against the closure
  (let [rnd (java.util.Random. 4902)
        hit (atom 0)]
    (dotimes [trial 20]
      (let [t  (tax/create-taxonomy)
            ts (mapv #(symbol (str "mw" %)) (range 40))]
        (dotimes [h 70]
          (let [i (.nextInt rnd 40) j (.nextInt rnd 40)]
            (when (and (not= i j) (or (< i j) (zero? (.nextInt rnd 8))))
              (tax/add-genl t (ts i) (ts j) h))))
        (doseq [n [1 3 8]]
          (let [among  (into #{} (repeatedly n #(ts (.nextInt rnd 40))))
                missed (volatile! #{})
                want   (into #{} (filter #(some among (tax/genls-global t %))) ts)]
            (swap! hit + (count want))
            (is (= want (into #{} (filter #(tax/genls-global-meets? t % among missed)) (shuffle ts)))
                (str "trial " trial ", " n " targets"))))))
    (is (pos? @hit) "some types meet a target")))

(deftest a-witness-walk-past-its-pruning-names-the-path-an-unpruned-walk-names
  ;; random graphs of 160 types where most types fan out to many parents, so walks pass
  ;; their first 64 expansions: each witness, pruned to the types between the two ends,
  ;; against the walk that never prunes, with and without supporter classes
  (let [rnd   (java.util.Random. 4905)
        found (atom 0)]
    (dotimes [trial 6]
      (let [t  (tax/create-taxonomy)
            ts (mapv #(symbol (str "pw" %)) (range 160))]
        (dotimes [h 900]
          (let [i (.nextInt rnd 160) j (.nextInt rnd 160)]
            (when (and (not= i j) (or (< i j) (zero? (.nextInt rnd 12))))
              (tax/add-genl t (ts i) (ts j) h))))
        (dotimes [_ 30]
          (let [sub   (ts (.nextInt rnd 40))
                super (ts (+ 80 (.nextInt rnd 80)))
                walk  #(tax/with-neighbours (atom {})
                         (fn [] [(tax/reach-support t :genl sub super nil)
                                 (tax/reach-support t :genl sub super nil (constantly :default))]))
                want  (with-redefs [tax/prune-after Long/MAX_VALUE] (walk))]
            (when (first want) (swap! found inc))
            (is (= want (walk)) (str "trial " trial " " sub " " super))))))
    (is (pos? @found) "some pairs have a path")))

(deftest a-witness-read-off-held-route-lengths-names-the-path-the-walk-names
  ;; random graphs of 120 types, a few edges closing cycles, edges in four contexts and
  ;; some with a second supporter of the other class: every witness asked of one router
  ;; per supporter-class reading, from three vantages, against the walk asked alone
  (let [rnd   (java.util.Random. 6017)
        found (atom 0)
        cls   #(if (even? %) :monotonic :default)]
    (dotimes [trial 6]
      (let [t   (tax/create-taxonomy)
            ts  (mapv #(symbol (str "rl" %)) (range 120))
            cxs [nil 'CxRlA 'CxRlB 'CxRlC]]
        (tax/add-genlCx t 'CxRlA 'CxUniverse 1)
        (tax/add-genlCx t 'CxRlB 'CxUniverse 2)
        (tax/add-genlCx t 'CxRlC 'CxRlA 3)
        (dotimes [h 500]
          (let [i (.nextInt rnd 120) j (.nextInt rnd 120)]
            (when (and (not= i j) (or (< i j) (zero? (.nextInt rnd 40))))
              (tax/add-genl t (ts i) (ts j) (+ 10 h) (cxs (.nextInt rnd 4)))
              (when (zero? (.nextInt rnd 4))
                (tax/add-genl t (ts i) (ts j) (+ 1000 h) (cxs (.nextInt rnd 4)))))))
        (let [routers {nil (java.util.HashMap.) cls (java.util.HashMap.)}]
          (tax/with-neighbours
            (atom {})
            (fn []
              (dotimes [_ 60]
                (let [sub   (ts (.nextInt rnd 60))
                      super (ts (+ 60 (.nextInt rnd 60)))]
                  (doseq [ctx [nil 'CxRlA 'CxRlC] c [nil cls]]
                    (let [want (tax/reach-support t :genl sub super ctx c [:monotonic :default])]
                      (when (seq want) (swap! found inc))
                      (is (= want (tax/reach-support t :genl sub super ctx c [:monotonic :default]
                                                     (routers c)))
                          (str "trial " trial " " sub " " super " " ctx)))))))))))
    (is (pos? @found) "some pairs have a path")))

(deftest a-routed-witness-walk-builds-no-up-closure-of-the-types-it-enters
  ;; a braid of 40 levels of four types, each under two of the level above and a side
  ;; type of its level, which is under another root: walks from the four bottom types to
  ;; the root over one router compute no closure, where a test of each entered type's
  ;; up-closure computes one per type the walk enters
  (let [t    (tax/create-taxonomy)
        node #(symbol (str "rb" %1 "_" %2))
        h    (atom 0)
        add  #(tax/add-genl t %1 %2 (swap! h inc))]
    (dotimes [j 4] (add (node 0 j) 'rbroot))
    (doseq [i (range 1 40) j (range 4)]
      (add (node i j) (node (dec i) j))
      (add (node i j) (node (dec i) (mod (inc j) 4)))
      (add (node i j) (symbol (str "rbside" i))))
    (dotimes [i 40] (add (symbol (str "rbside" i)) 'rbother))
    (let [misses #(get (caches/tally-map (:tally (:closure-lru @t))) :misses 0)
          before (misses)
          router (java.util.HashMap.)
          ws     (mapv #(tax/reach-support t :genl (node 39 %) 'rbroot nil (constantly :monotonic)
                                           [:monotonic :default] router)
                       (range 4))
          after  (misses)]
      (is (= before after))
      (is (every? #(= 40 (count %)) ws))
      (is (= ws (mapv #(tax/reach-support t :genl (node 39 %) 'rbroot nil (constantly :monotonic))
                      (range 4)))))))

(deftest the-separation-routes-of-two-types-build-the-closure-of-neither
  ;; each type under two types of a braid of 20 levels of four types below a root, the
  ;; roots disjoint: the routes read both types' supertypes cut to the separable ones, so
  ;; no type of either braid holds a closure after the read
  (let [t      (tax/create-taxonomy)
        h      (atom 0)
        add    #(tax/add-genl t %1 %2 (swap! h inc))
        node   #(symbol (str "srb" %1 "_" %2 "_" %3))]
    (doseq [s ["a" "b"]]
      (dotimes [j 4] (add (node s 0 j) (symbol (str "srb" s "root"))))
      (doseq [i (range 1 20) j (range 4)]
        (add (node s i j) (node s (dec i) j))
        (add (node s i j) (node s (dec i) (mod (inc j) 4))))
      (add (symbol (str "srb" s "leaf")) (node s 19 0))
      (add (symbol (str "srb" s "leaf")) (node s 19 1)))
    (tax/add-disjoint t 'srbaroot 'srbbroot (swap! h inc))
    (let [routes (tax/separation-routes t 'srbaleaf 'srbbleaf)
          lru    (:closure-lru @t)
          held   (fn [n] (caches/lru-get lru [:genl (:gen (:genl @t)) :fwd n]))]
      (is (= [{:keys #{[:disjoint #{'srbaroot 'srbbroot}]} :pair ['srbaroot 'srbbroot]
               :links [['srbaleaf 'srbaroot] ['srbbleaf 'srbbroot]]}]
             (vec routes)))
      (is (not-any? held (for [s ["a" "b"], n (cons (symbol (str "srb" s "leaf"))
                                                    (for [i (range 20) j (range 4)] (node s i j)))]
                           n))))))

(deftest the-uncovered-routes-a-pass-reads-over-held-neighbours-are-those-read-alone
  ;; random graphs of 60 types, edges stated in four contexts (one with none) under two
  ;; branches, some edges with two supporters of two classes: the uncovered routes, with
  ;; and without supporter classes, read inside one reading pass after a witness walk
  ;; over the same edges, against the same reads outside any pass
  (let [rnd   (java.util.Random. 4906)
        found (atom 0)
        cls   #(if (even? %) :monotonic :default)]
    (dotimes [trial 8]
      (let [t   (tax/create-taxonomy)
            ts  (mapv #(symbol (str "ur" %)) (range 60))
            cxs [nil 'CxUrA 'CxUrB 'CxUrC]]
        (tax/add-genlCx t 'CxUrA 'CxUniverse 1)
        (tax/add-genlCx t 'CxUrB 'CxUniverse 2)
        (tax/add-genlCx t 'CxUrC 'CxUrA 3)
        (dotimes [h 220]
          (let [i (.nextInt rnd 60) j (.nextInt rnd 60)]
            (when (and (not= i j) (or (< i j) (zero? (.nextInt rnd 10))))
              (tax/add-genl t (ts i) (ts j) (+ 10 h) (cxs (.nextInt rnd 4)))
              (when (zero? (.nextInt rnd 4))
                (tax/add-genl t (ts i) (ts j) (+ 1000 h) (cxs (.nextInt rnd 4)))))))
        (dotimes [_ 25]
          (let [sub   (ts (.nextInt rnd 30))
                super (ts (+ 30 (.nextInt rnd 30)))
                walk  (fn [] [(tax/reach-supports t :genl sub super nil cls)
                              (tax/general-reach-supports t :genl sub super nil)])
                want  (walk)]
            (when (seq (first want)) (swap! found inc))
            (is (= want (tax/with-neighbours (atom {})
                          (fn [] (tax/reach-support t :genl sub super nil cls) (walk))))
                (str "trial " trial " " sub " " super))))))
    (is (pos? @found) "some pairs have routes")))

(deftest a-walk-from-a-source-one-edge-from-its-target-names-what-the-full-walk-names
  ;; random graphs of 50 types, edges in four contexts, some with two supporters of two
  ;; classes, and many sources one edge from their target: the witness and every
  ;; uncovered route, read from three vantages, with the one-edge answers and without
  (let [rnd   (java.util.Random. 5001)
        ;; seeded, so the cases asked, and the assertion count, are the same every run
        pick  (fn [n xs] (let [l (java.util.ArrayList. ^java.util.Collection (sort xs))]
                           (java.util.Collections/shuffle l rnd)
                           (take n l)))
        short (atom 0)
        cls   #(if (even? %) :monotonic :default)]
    (dotimes [trial 8]
      (let [t   (tax/create-taxonomy)
            ts  (mapv #(symbol (str "dw" %)) (range 50))
            cxs [nil 'CxDwA 'CxDwB 'CxDwC]]
        (tax/add-genlCx t 'CxDwA 'CxUniverse 1)
        (tax/add-genlCx t 'CxDwB 'CxUniverse 2)
        (tax/add-genlCx t 'CxDwC 'CxDwA 3)
        (dotimes [h 120]
          (let [i (.nextInt rnd 50) j (.nextInt rnd 50)]
            (when (and (not= i j) (or (< i j) (zero? (.nextInt rnd 10))))
              (tax/add-genl t (ts i) (ts j) (+ 10 h) (cxs (.nextInt rnd 4)))
              (when (zero? (.nextInt rnd 3))
                (tax/add-genl t (ts i) (ts j) (+ 1000 h) (cxs (.nextInt rnd 4)))))))
        (doseq [sub   (pick 25 ts)
                super (pick 3 (tax/direct-genls-global t sub))
                ctx   [nil 'CxDwA 'CxDwC]
                :when (not= sub super)]
          (let [walk #(tax/with-neighbours (atom {})
                        (fn [] [(tax/reach-support t :genl sub super ctx)
                                (tax/reach-support t :genl sub super ctx cls)
                                (tax/reach-supports t :genl sub super ctx cls)
                                (tax/general-reach-supports t :genl sub super ctx)]))
                want (with-redefs [tax/direct-witness        (constantly nil)
                                   tax/every-uncovered-route @#'tax/uncovered-routes]
                       (walk))]
            (swap! short inc)
            (is (= want (walk)) (str "trial " trial " " sub " " super " " ctx))))))
    (is (pos? @short) "some sources sit one edge from a target")))

(deftest the-routes-a-search-keeps-do-not-depend-on-edges-off-every-route
  ;; random graphs of 40 types, edges in four contexts and half with a second supporter,
  ;; then the same graphs with three dead-end parents added to every type: the edges off
  ;; every route enter the queue and move nothing a route search returns
  (let [build (fn [seed dead?]
                (let [rnd (java.util.Random. seed)
                      t   (tax/create-taxonomy)
                      ts  (mapv #(symbol (str "lk" %)) (range 40))
                      cxs [nil 'CxLkA 'CxLkB 'CxLkC]]
                  (tax/add-genlCx t 'CxLkA 'CxUniverse 1)
                  (tax/add-genlCx t 'CxLkB 'CxUniverse 2)
                  (tax/add-genlCx t 'CxLkC 'CxLkA 3)
                  (dotimes [h 150]
                    (let [i (.nextInt rnd 40) j (.nextInt rnd 40)]
                      (when (< i j)
                        (tax/add-genl t (ts i) (ts j) (+ 10 h) (cxs (.nextInt rnd 4)))
                        (when (zero? (.nextInt rnd 2))
                          (tax/add-genl t (ts i) (ts j) (+ 1000 h) (cxs (.nextInt rnd 4)))))))
                  (when dead?
                    (dotimes [i 40]
                      (dotimes [d 3]
                        (tax/add-genl t (ts i) (symbol (str "lkdead" i "x" d)) (+ 5000 (* 3 i) d) (cxs d)))))
                  [t ts]))
        cls   #(if (even? %) :monotonic :default)
        found (atom 0)]
    (doseq [seed (range 10)]
      (let [[t ts] (build seed false)
            [t2]   (build seed true)]
        (doseq [i (range 15) j (range 25 40)
                :let [a (ts i) b (ts j)
                      r (tax/reach-supports t :genl a b nil cls)]]
          (when (seq r) (swap! found inc))
          (is (= r (tax/reach-supports t2 :genl a b nil cls)) (str "seed " seed " " a " " b))
          (is (= (tax/general-reach-supports t :genl a b nil) (tax/general-reach-supports t2 :genl a b nil))
              (str "seed " seed " " a " " b)))))
    (is (pos? @found) "some pairs have routes")))
