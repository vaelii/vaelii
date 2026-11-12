;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.graph
  "Graph walks over a caller-supplied neighbour fn: reachable set, reachability between two
  nodes and strongly connected components.
  A walk visits neighbours in the order `step` yields them and never sorts. See docs/namespaces.md.")

(defn scc
  "Tarjan's strongly connected components over the nodes reachable from `roots` under
  `step` (node -> seq of neighbours), on an explicit stack. `step` is called once per
  node, at its discovery. Calls `(on-component members)` once per component, `members`
  a vector with the component's root last, in completion order. Returns nil."
  [roots step on-component]
  (let [idx (java.util.HashMap.)              ; node -> discovery index
        low (java.util.HashMap.)
        on  (java.util.HashSet.)              ; nodes on the Tarjan stack
        stk (java.util.ArrayDeque.)
        n   (volatile! 0)]
    (doseq [root roots :when (not (.containsKey idx root))]
      (let [work  (java.util.ArrayDeque.)     ; frames [node remaining-neighbours]
            visit (fn [v]
                    (.put idx v @n) (.put low v @n) (vswap! n inc)
                    (.push stk v) (.add on v)
                    (.push work (object-array [v (seq (step v))])))]
        (visit root)
        (while (not (.isEmpty work))
          (let [^objects frame (.peek work)
                v              (aget frame 0)
                remaining      (aget frame 1)]
            (if-let [w (first remaining)]
              (do (aset frame 1 (next remaining))
                  (cond
                    (not (.containsKey idx w)) (visit w)
                    (.contains on w)           (.put low v (min (long (.get low v))
                                                                (long (.get idx w))))))
              (do (.pop work)
                  (when (= (.get low v) (.get idx v))
                    (on-component (loop [acc []]
                                    (let [w (.pop stk)]
                                      (.remove on w)
                                      (if (= w v) (conj acc w) (recur (conj acc w)))))))
                  (when-let [^objects parent (.peek work)]
                    (let [p (aget parent 0)]
                      (.put low p (min (long (.get low p)) (long (.get low v))))))))))))
    nil))

(defn reach-all
  "Reflexive-transitive reachable set from every node of `starts` over `adj` (node ->
  neighbours). Each node is expanded once, so a cyclic `adj` terminates."
  [starts adj]
  (loop [seen (transient (set starts)), stack (vec starts)]
    (if-let [n (peek stack)]
      (let [fresh (remove #(get seen %) (adj n))]
        (recur (reduce conj! seen fresh) (into (pop stack) fresh)))
      (persistent! seen))))

(defn bfs-tree
  "Breadth-first walk that records how each node was first reached. `seeds` is a seq of
  `[node entry]` pairs; `(step node tree)` yields `[child entry]` pairs in the caller's
  order, and `tree` (node -> entry) lets it skip the children already reached. A child
  already in the tree keeps its first entry. Stops at the first dequeued node satisfying
  `stop?`. Returns `{:found node-or-nil :tree {node entry}}`."
  [seeds step stop?]
  (let [add (fn [[q tree] [n e]]
              (if (contains? tree n) [q tree] [(conj q n) (assoc tree n e)]))]
    (loop [[q tree] (reduce add [clojure.lang.PersistentQueue/EMPTY {}] seeds)]
      (if-let [n (peek q)]
        (if (stop? n)
          {:found n :tree tree}
          (recur (reduce add [(pop q) tree] (step n tree))))
        {:tree tree}))))

(defn reaches?
  "Does a path lead from `a` to the distinct node `b`, `succ` and `pred` giving a node's
  successors and predecessors?  Walks from both ends, each step widening the smaller
  frontier by one level, and answers false once either frontier is empty, so a node with
  few successors or `b` with few predecessors answers in few steps whatever lies beyond.
  With `open?`, a walk that ends having reached a node `open?` accepts answers true, for a
  caller that decides through those nodes by other means."
  ([succ pred a b] (reaches? succ pred a b (constantly false)))
  ([succ pred a b open?]
   (loop [fseen #{a} front [a] fo (open? a) bseen #{b} back [b] bo (open? b)]
     (cond
       (empty? front) (boolean fo)
       (empty? back)  (boolean bo)
       (<= (count front) (count back))
       (let [nx (into [] (comp (mapcat succ) (remove fseen) (distinct)) front)]
         (or (boolean (some bseen nx))
             (recur (into fseen nx) nx (or fo (boolean (some open? nx))) bseen back bo)))
       :else
       (let [nx (into [] (comp (mapcat pred) (remove bseen) (distinct)) back)]
         (or (boolean (some fseen nx))
             (recur fseen front fo (into bseen nx) nx (or bo (boolean (some open? nx))))))))))
