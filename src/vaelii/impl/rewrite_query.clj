;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.rewrite-query
  "Positive rewriteOf queries over reader representatives, above raw fact retrieval."
  (:require [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(defn endpoint
  "A rewriteOf endpoint read as a term by `reader`, never as an equation mention.
  Existing closed applications may resolve, but unknown ones remain written and no
  placeholder is allocated. The second representative walk covers a resolved alias.
  This does not change raw storage or the mention policy of any other equation."
  [kb reader term]
  (let [visible? (res/visible-supporter-fn kb reader)
        term (res/representative-term kb visible? term)]
    (binding [nat-read/*withheld* (nat-read/withheld-at kb reader)]
      (res/representative-term kb visible?
                               (nat-read/reify-existing kb term reader)))))

(defn- spellings
  "An index-discovery superset, not a reader's equality authority."
  [kb term]
  (if (and (symbol? term) (not (sx/variable? term)))
    (conj (tax/equiv-class (reasoning/taxonomy kb) term) term)
    #{term}))

(defn- application-heads
  "Possible raw application heads whose value can read as `term`.
  Maps and correspondence value slots are identity witnesses only for discovery.
  Nothing here licenses a match: endpoint and stored visibility are checked later.
  Following heads also covers a raw compound function position reifying to a symbol."
  [kb term]
  (let [idx (:index kb)
        recs (:records kb)
        declarations (delay (res/believed-correspondences kb '?ctx (constantly true)))
        heads (fn heads [x]
                (cond
                  (and (symbol? x) (not (sx/variable? x))) #{x}
                  (seq? x) (heads (first x))
                  :else #{}))]
    (loop [todo [term], seen #{}, found #{}]
      (if (seq todo)
        (let [node (peek todo)]
          (if (contains? seen node)
            (recur (pop todo) seen found)
            (let [names (spellings kb node)
                  maps (for [name names
                             h (reads/as-stored-with-args idx 'natFormula {1 name})
                             :let [[_ _ e] (:sentence (p/get-sentex recs h))]
                             :when (seq? e)]
                         (first e))
                  functions (for [[f pred pos] @declarations
                                  :when (some #(seq (reads/as-stored-with-args idx pred {pos %})) names)]
                              f)
                  next-heads (into (heads node) (mapcat heads) (concat maps functions))]
              (recur (into (pop todo) next-heads) (conj seen node)
                     (into found next-heads)))))
        found))))

(defn- candidate-handles
  "Indexed positive rewrite candidates. A goal with no usable endpoint lead enumerates
  the rewrite extent, not the whole KB.
  The stored lhs is not compound (wff/equality-problems), so a bound canonical lhs leads
  directly from its spellings. A right-bound goal also discovers compound rhs heads
  through existing maps/correspondence value slots, including ambiguous alias cases."
  [kb [_ left right]]
  (let [idx (:index kb)
        grounded? sx/ground-term?]
    (cond
      (sequential? left) #{}

      (grounded? left)
      (into #{} (mapcat #(reads/as-stored-with-args idx 'rewriteOf {1 %}))
            (spellings kb left))

      (grounded? right)
      (let [names (spellings kb right)]
        (into (into #{} (mapcat #(concat (reads/as-stored-with-args idx 'rewriteOf {1 %})
                                        (reads/as-stored-with-args idx 'rewriteOf {2 %}))) names)
              (mapcat #(reads/as-stored-with-term idx %))
              (application-heads kb right)))

      (and (seq? right) (grounded? (first right)))
      (into #{} (mapcat #(reads/as-stored-with-term idx %))
            (application-heads kb (first right)))

      :else (reads/as-stored-with-functor idx 'rewriteOf))))

(defn matches
  "Positive rewrite witnesses as `[handle bindings stored-record]` for `goal`.
  Canonicalize before unifying, including repeated variables and closed endpoints.
  Returned records are the actual as-authored rows, never fabricated self edges.
  This is a read computation only; callers deriving facts must additionally carry the
  normalization supports rather than treating a canonical sentence as stored."
  [kb goal reader]
  (let [[pred left right] goal
        canonical (list pred (endpoint kb reader left) (endpoint kb reader right))
        recs (:records kb)]
    (for [h (candidate-handles kb canonical)
          :let [record (p/get-sentex recs h)
                [f a b :as stored] (:sentence record)]
          :when (and (= 'rewriteOf f) (= 3 (count stored)))
          ;; Reuse raw retrieval's visibility/exception/retirement contract. Asking
          ;; the exact ground row does not claim the canonical row was stored.
          [visible-h context-bindings] (res/matches-visible kb stored reader)
          :when (= h visible-h)
          :let [fact (list f (endpoint kb reader a) (endpoint kb reader b))
                bindings (res/match1 kb canonical fact reader)]
          :when bindings]
      [h (merge context-bindings bindings) record])))

(defn applicable?
  "Can this positive binary goal read an actual rewriteOf row, including an open head?"
  [kb goal reader]
  (and (sequential? goal) (= 3 (count goal))
       (let [f (first goal)]
         (or (= 'rewriteOf f)
             (sx/variable? f)
             (and (symbol? f)
                  (contains? (res/sub-predicates kb f reader) 'rewriteOf))))))

(defn fact-matches
  "The public fact leaf reading positive rewrite witnesses through representatives.
  Other stored predicates retain the existing retrieval path, including negation and
  sameAs/equals. Do not union a second raw rewrite channel with canonical bindings."
  [kb goal reader]
  (let [raw (res/matches-visible kb goal reader)]
    (if (applicable? kb goal reader)
      (concat
       (remove (fn [[h _ stored]]
                 (let [sentence (or (:sentence stored)
                                    (:sentence (p/get-sentex (:records kb) h)))]
                   (= 'rewriteOf (first sentence)))) raw)
       (matches kb goal reader))
      raw)))
