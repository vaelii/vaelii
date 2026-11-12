;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.point-order
  "The order over time points: the `≤` and `<` links that stated facts and the point
  terms themselves give, and `path`, which decides whether one point lies at or before
  another and names the stated facts behind the answer.  A calendar moment compares with
  another by its fields and carries no link.  `TightestStartBoundProver` answers
  `tightestStartBoundOf` from the order.  See docs/time.md, \"The order over time
  points\"."
  (:require [vaelii.impl.datetime :as dt]
            [vaelii.impl.graph :as graph]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.stp :as stp]
            [vaelii.impl.timepoint :as tp]
            [vaelii.impl.types.prover :as prover-types]))

(defn calendar-moment
  "`[frame fields]` of the node `x` when the calendar places it (`timepoint/moment`, or a
  point of an `InstantFn` moment), else nil."
  [x]
  (or (tp/moment x)
      (some->> (tp/thing-of x) dt/instant-fields (vector :local))))

;; ---- the links ------------------------------------------------------------

(def ^:private instant-heads
  "Each stated order between two moments, `{functor [[lower upper strict?] …]}` by
  argument position."
  '{instantBefore    [[1 2 true]]
    instantAfter     [[2 1 true]]
    instantNotAfter  [[1 2 false]]
    instantNotBefore [[2 1 false]]
    instantEqual     [[1 2 false] [2 1 false]]})

(def ^:private bound-heads
  "The stated bounds, each equating a thing's point with a moment."
  '{startOf :start endOf :end})

(def ^:private inclusion-heads
  "The stated inclusions `(P thing moment)`, each placing the moment at or after the
  thing's start and before its end, the half-open convention of the calendar terms."
  '#{includesInstant})

(def link-heads
  "The functors of every fact `sentence-links` reads a link from."
  (into (set (keys instant-heads))
        (concat (keys bound-heads) inclusion-heads (keys stp/interval-denotation))))

(def ^:private convex-links
  "An endpoint comparison's possible orderings, when convex, as `[from to strict?]` over
  the comparison's two points `[x y]` (0 and 1).  Any other union gives no link."
  {#{:before}        [[0 1 true]]
   #{:before :equal} [[0 1 false]]
   #{:equal}         [[0 1 false] [1 0 false]]
   #{:after}         [[1 0 true]]
   #{:after :equal}  [[1 0 false]]})

(defn- interval-fact-links
  "The links the interval fact `(P a b)` gives the start and end of `a` and `b`: each of
  the four endpoint comparisons whose union over P's denotation is convex."
  [[p a b]]
  (let [den  (stp/interval-denotation p)
        ends #(vector (tp/point :start %) (tp/point :end %))]
    (for [[k xy] (stp/endpoint-gaps (ends a) (ends b))
          [i j s] (convex-links (into #{} (map #(get-in stp/endpoint-signature [% k])) den))]
      [(nth xy i) (nth xy j) s])))

(defn sentence-links
  "The links the stated fact `sentence` gives, `[lower upper strict?]`, or nil when its
  functor is not among `link-heads` or its arity does not fit."
  [sentence]
  (when (and (seq? sentence) (= 3 (count sentence)))
    (let [[h a b] sentence]
      (cond
        (instant-heads h)        (for [[lo hi s] (instant-heads h)] [(nth sentence lo) (nth sentence hi) s])
        (bound-heads h)          (let [pt (tp/point (bound-heads h) a)] [[pt b false] [b pt false]])
        (inclusion-heads h)      [[(tp/point :start a) b false] [b (tp/point :end a) true]]
        (stp/interval-denotation h) (interval-fact-links sentence)))))

(def ^:dynamic *context*
  "nil, or the context whose visible facts the links read.  nil reads every context's
  believed facts, as the slice ordering does."
  nil)

(defn- believed
  "The believed facts matching `pattern` that `*context*` sees, or none without a read
  when the KB stores no fact of its functor."
  [kb pattern]
  (when (pos? (reads/stored-count-with-functor (:index kb) (first pattern)))
    (if-let [c *context*]
      (for [m (res/matches-visible kb pattern c)]
        (or (nth m 2 nil) (p/get-sentex (:records kb) (first m))))
      (kb/sentexes-matching kb pattern '?ctx))))

(defn- stated-links
  "Each `[node strict? sentex]` one stated link from `n`: the nodes `n` lies at or before
  when `later?`, else those that lie at or before `n`.  Reads the facts naming `n` as a
  moment, and, for a thing's start or end, the bound, inclusion and interval facts naming
  the thing."
  [kb later? n]
  (let [x     (tp/thing-of n)
        which (when x (tp/point-functions (first n)))
        reads (concat (for [h (keys instant-heads), pos [1 2]]
                        (if (= 1 pos) (list h n '?o) (list h '?o n)))
                      (for [h (concat (keys bound-heads) inclusion-heads)] (list h '?o n))
                      (when (#{:start :end} which)
                        (concat (for [[h w] bound-heads :when (= w which)] (list h x '?o))
                                (for [h inclusion-heads] (list h x '?o))
                                (for [h (keys stp/interval-denotation), pat [(list h x '?o) (list h '?o x)]]
                                  pat))))]
    (distinct
     (for [pat reads
           sx  (believed kb pat)
           [lo hi s] (sentence-links (:sentence sx))
           :when (= n (if later? lo hi))]
       [(if later? hi lo) s sx]))))

(defn- own-links
  "Each `[node strict? nil]` one link from `n` that the point terms give alone: a point of
  a moment is that moment, and a thing's six points keep `timepoint/thing-order`.  A
  calendar thing's points compare by their fields instead."
  [later? n]
  (when-let [x (tp/thing-of n)]
    (cond
      (or (tp/point-term? x) (dt/instant-term? x)) [[x false nil]]
      (calendar-moment n)                          nil
      :else (let [w (tp/point-functions (first n))]
              (for [[lo hi s] tp/thing-order :when (= w (if later? lo hi))]
                [(tp/point (if later? hi lo) x) s nil])))))

(def ^:private within-orders
  "The orders a meet of which lies within each argument: it starts at or after each
  argument's start and ends at or before each argument's end."
  '[subintervalOf subtimeOf])

(defn- meet-links
  "Each `[node false sentex]` link from `n`, the start or end of an application `(G a …)`
  that a believed `(meetFunctionOf G R)`, `R` in `within-orders`, declares a meet: back
  from its start to each argument's start, and on from its end to each argument's end.
  The sentex is the first such declaration in content order."
  [kb later? n]
  (let [x (tp/thing-of n)]
    (when (and (seq? x) (symbol? (first x))
               (= (if later? :end :start) (tp/point-functions (first n))))
      (when-let [sx (first (nm/sort-by-content-key (juxt :context :sentence)
                                                   (mapcat #(believed kb (list 'meetFunctionOf (first x) %))
                                                           within-orders)))]
        (for [a (rest x)] [(tp/point (tp/point-functions (first n)) a) false sx])))))

(defn- links
  "Each `[node strict? sentex-or-nil]` one link from `n` (`stated-links`' direction): the
  point terms' own links first, then the stated and meet ones in content order."
  [kb later? n]
  (concat (own-links later? n)
          (nm/sort-by-content-key (fn [[m _ sx]] [(:context sx) (:sentence sx) m])
                                  (concat (stated-links kb later? n) (meet-links kb later? n)))))

(defn- next-nodes
  "The nodes one link from `n` reaches (`links`' direction), unordered."
  [kb later? n]
  (map first (concat (own-links later? n) (stated-links kb later? n) (meet-links kb later? n))))

;; ---- the walk -------------------------------------------------------------

(def ^:dynamic *memo*
  "nil, or an atom of the walks `reach` has made, keyed `[*context* later? start]`, for a
  caller that asks several questions over one belief state (`with-memo`)."
  nil)

(defmacro with-memo
  "Run `body` with the walks shared across its `path` questions.  The caller holds belief
  fixed over `body`'s reads of the links."
  [& body]
  `(binding [*memo* (or *memo* (atom {}))] ~@body))

(defn- reach*
  [kb later? start]
  (loop [queue (conj clojure.lang.PersistentQueue/EMPTY [start false []])
         seen  {}]
    (if-let [[n s path] (peek queue)]
      (let [queue (pop queue)]
        (if (or (contains? seen [n s]) (and (not s) (contains? seen [n true])))
          (recur queue seen)
          (recur (into queue (for [[m s2 sx] (links kb later? n)]
                               [m (or s s2) (cond-> path sx (conj sx))]))
                 (assoc seen [n s] path))))
      seen)))

(defn reach
  "Every node a breadth-first walk from `start` reaches over the links (later nodes when
  `later?`), as `{[node strict?] path}`: the first path reaching the node, and the first
  reaching it across a strict link, each the vector of sentexes its stated links read.
  `start` itself is `[start false]` with an empty path."
  [kb later? start]
  (if-let [m *memo*]
    (let [k [*context* later? start]]
      (or (get @m k)
          (let [r (reach* kb later? start)] (swap! m assoc k r) r)))
    (reach* kb later? start)))

(defn- shorter
  "The path of `ps` with the fewest distinct sentexes, then first in content order."
  [ps]
  (first (nm/sort-by-content-key (fn [p] [(count p) (mapv (juxt :context :sentence) p)])
                                 (map (comp vec distinct) ps))))

(defn- calendar-paths
  "The paths `fwd` (from `p`) and `bwd` (to `q`) show through the calendar: a calendar
  moment `p` reaches lying at or before, by its fields, one that reaches `q`.  The earliest
  moment `p` reaches and the latest that reaches `q` decide it, and for `strict?` also the
  earliest reached across a strict link and the latest reaching across one."
  [strict? fwd bwd]
  (let [ends    (fn [reached] (for [[[n s] path] reached
                                    :let [[frame fields] (calendar-moment n)]
                                    :when frame]
                                {:frame frame :fields fields :strict s :path path}))
        content (fn [e] [(count (:path e)) (mapv (juxt :context :sentence) (:path e))])
        extreme (fn [cmp es] (first (sort (fn [a b] (let [c (cmp (:fields a) (:fields b))]
                                                      (if (zero? c) (nm/compare-form (content a) (content b)) c)))
                                          es)))
        bs      (group-by :frame (ends bwd))]
    (for [[frame fs] (group-by :frame (ends fwd))
          :let [es    fs
                ls    (get bs frame)
                early (extreme compare es)
                late  (extreme #(compare %2 %1) ls)]
          [e l] (cond-> [[early late]]
                  strict? (conj [(extreme compare (filter :strict es)) late]
                                [early (extreme #(compare %2 %1) (filter :strict ls))]))
          :when (and e l)
          :let [c (compare (:fields e) (:fields l))]
          :when (if strict?
                  (or (neg? c) (and (zero? c) (or (:strict e) (:strict l))))
                  (not (pos? c)))]
      (into (:path e) (:path l)))))

(def ^:dynamic *through*
  "nil, or a delay of `[[back on] …]`, the walks back and on (`reach`) from each node a
  caller reconciles at, such as each end of the links arriving.  `holds?` answers `p` at
  or before `q` without a walk of its own when one node's walks reach `p` back and `q` on."
  nil)

(defn- by-terms
  "`[]` when the terms alone place `p` before `q` (`strict?`) or at or before it: two
  calendar moments by their fields, or one node at itself.  false when two calendar
  moments refuse it, nil when only the links decide."
  [strict? p q]
  (let [cp (calendar-moment p)
        cq (calendar-moment q)]
    (cond
      (and cp cq) (if (and (= (first cp) (first cq))
                           ((if strict? neg? (complement pos?)) (compare (second cp) (second cq))))
                    []
                    false)
      (and (= p q) (not strict?)) [])))

(defn- through?
  [strict? p q]
  (let [at #(or (contains? %1 [%2 false]) (contains? %1 [%2 true]))]
    (some (fn [[back on]]
            (and (at back p) (at on q)
                 (or (not strict?) (contains? back [p true]) (contains? on [q true]))))
          (some-> *through* deref))))

(defn holds?
  "Presence check before `path`: false when `path` answers nil for these arguments, true
  when it may answer.  Decides by the terms (`by-terms`), then by the walks `*through*`
  holds, then by `graph/reaches?` over the links, where a node the calendar places counts
  as reaching."
  [kb strict? p q]
  (let [t (by-terms strict? p q)]
    (if (some? t)
      (boolean t)
      (boolean (or (through? strict? p q)
                   (graph/reaches? (partial next-nodes kb true) (partial next-nodes kb false)
                                   p q (comp some? calendar-moment)))))))

(defn path
  "The sentexes showing the node `p` lies before `q` (`strict?`) or at or before it, or
  nil when neither the links nor the calendar show it.  Two calendar moments compare by
  their fields alone, with no sentex; any other pair by a walk from each end
  (`reach`), joined at a node both reach or through the calendar (`calendar-paths`), when
  `holds?` answers true.  Of several, the path with the fewest sentexes, then first in
  content order.  Reads the facts `*context*` sees."
  [kb strict? p q]
  (let [t (by-terms strict? p q)]
    (cond
      (some? t) (or t nil)
      (holds? kb strict? p q)
      (let [fwd (reach kb true p)
            bwd (reach kb false q)]
        (shorter (concat (for [[[n s1] pa] fwd
                               s2 [false true]
                               :let [pb (get bwd [n s2])]
                               :when (and pb (or (not strict?) s1 s2))]
                           (into pa pb))
                         (calendar-paths strict? fwd bwd)))))))

;; ---- the tightest known lower bound -----------------------------------------

(defn readings
  "The `[start end]` pairs of nodes the time `x` can be read as: `[x x]` for an
  `InstantFn` moment, the term's own start and end points for any other ground compound,
  and both for a symbol, which can name a moment or a thing with extent."
  [x]
  (let [ends [(tp/point :start x) (tp/point :end x)]]
    (cond
      (dt/instant-term? x) [[x x]]
      (symbol? x)          [ends [x x]]
      (sequential? x)      [ends])))

(defn tightest-start-bounds
  "The nodes a start of `x` (`readings`) lies at or after through at least one stated
  fact, kept when every other such node lies at or before it (`path`), in content order.
  Two unordered bounds keep neither.  Reads the facts visible from `context`, or every
  context's when it is a variable."
  [kb context x]
  (binding [*context* (when-not (sx/variable? context) context)]
    (with-memo
      (let [starts (into #{} (map first) (readings x))
            bounds (into #{} (for [s starts
                                   [[n _] facts] (reach kb false s)
                                   :when (and (seq facts) (not (starts n)))]
                               n))]
        (nm/sort-by-content-key identity
                                (filter (fn [n] (every? #(path kb false % n) (disj bounds n)))
                                        bounds))))))

(defrecord TightestStartBoundProver []
  prover-types/Prover
  ;; complete: `tightestStartBoundOf` is not_assertible, so no stored fact answers it
  (applicable? [_ _ goal _]
    (and (sequential? goal) (= 3 (count goal)) (= 'tightestStartBoundOf (first goal))
         (sx/ground-term? (second goal))))
  (est-bindings [_ _ _ _] 1)
  (cost [_ _ _ _] :compute)
  (completeness [_ _ _ _] 100)
  (solve [_ kb [_ x t] context]
    (keep #(res/unify t % {}) (tightest-start-bounds kb context x))))

(defn tightest-start-bound-prover
  "The prover answering `tightestStartBoundOf` from this order, which `add-reasoner
  :tightest-start-bound` registers."
  []
  (->TightestStartBoundProver))
