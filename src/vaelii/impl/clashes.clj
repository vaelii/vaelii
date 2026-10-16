;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.clashes
  "The clashes a reader reads: the hard clashes and dilemmas of every placed nogood as
  reports, each with the declarations it convicts through, and the disjointness clashes
  no single writer could see.  Nothing here writes belief.  See docs/nmtms.md, \"The clash
  reports\"."
  (:require [clojure.set :as set]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.arity :as arity]
            [vaelii.impl.decide.inherited :as inherited]
            [vaelii.impl.except :as exc]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- the reports -----------------------------------------------------------

(defn- clash-report
  "A clash as a report map, the shape docs/nmtms.md (\"The clash
  reports\") shows: the members as `:sides` in content order, each with its
  justifications.  `:kind` is the definitional violation's `:type`, `:inherited`, or nil
  for a rebuttal.  `:inherited` and `:vantages` appear only on the reports that carry
  them; the weighing contexts ride the metadata (`report-vantages`)."
  [kb {:keys [nogood priority sentence kind inherited vantages] ::keys [vantage-verdicts]}]
  (let [tms   (reasoning/tms kb)
        recs  (:records kb)
        ;; a side's justifications in `core/supporting-justifications`' content order
        jkey  (kb/justification-content-key kb)
        ;; Sides by sentence then context, which identify a sentex, so no handle enters
        ;; the key; `report_order_test` scans the `sort-by` line below for one.
        sides (->> nogood
                   (map (fn [h]
                          (let [s (p/get-sentex recs h)]
                            {:handle h :sentence (sx/sentence-of s) :context (:context s)
                             :defeat-class (jtms/defeat-class tms h)
                             :justifications (->> (jtms/supports tms h)
                                                  (keep #(p/get-justification recs %))
                                                  ;; keyed once per justification
                                                  (nm/sort-by-content-key jkey nm/compare-form))})))
                   (sort-by (juxt :sentence :context) nm/compare-form)
                   vec)]
    (-> (cond-> {:nogood nogood :priority priority :sentence sentence
                 :handles (mapv :handle sides)
                 :kind kind
                 :sides sides}
          inherited (assoc :inherited inherited)
          ;; `{vantage handle}`, on a vantage disagreement only
          vantage-verdicts (assoc :vantages vantage-verdicts))
        ;; metadata stays off the wire and out of `=`
        (vary-meta assoc ::vantages vantages))))

(defn report-vantages
  "The placement contexts report `r` was read at (`reports-over`, `contradictions-at`), or
  nil for a report built elsewhere.  `clash-grounds` reads the declarations each of them
  sees."
  [r]
  (::vantages (meta r)))

(defn- marks-over-all
  "The predicates carrying prop mark `kind` over every functor of `tuples` at `v`."
  [tax kind tuples v]
  (reduce set/intersection (map #(set (tax/props-over tax kind (nm/functor %) v)) tuples)))

(defn- chain?
  "Do the binary `tuples` fill the three roles of an `anti_transitive` chain, `(a b)`, `(b c)`
  and `(a c)`, with no tuple left over?"
  [tuples]
  (let [ts (set tuples)]
    (boolean (some (fn [[t1 t2 t3]]
                     (let [[a b] (nm/args t1) [b' c] (nm/args t2) [a' c'] (nm/args t3)]
                       (and (= b b') (= a a') (= c c') (= ts (hash-set t1 t2 t3)))))
                   (for [x ts y ts z ts] [x y z])))))

(defn- ground-keys
  "The flat-cache keys a definitional conviction of the member sentences `sens` reads at
  vantage `v`, found from the members' shape: the separations of two memberships of one
  term; the `functional` and `functionalInArg` marks over two tuples differing at one
  position; the `asymmetric` and `anti_symmetric` marks over a converse pair, the
  `irreflexive` mark over a self tuple and the `anti_transitive` mark over a chain; the
  covers whose every part a denial in `sens` rules out for the whole's member; and the
  separations of the two types a lone `(orthogonal a b)` names, or a lone fact whose
  functor is a `genl` of `orthogonal`.  A `genl` edge is no flat-cache entry, so an
  `orthogonal` convicted through one alone reads nothing, as a `disjoint` over related
  types does.  A shape no conviction has reads nothing."
  [tax sens v]
  (let [pos    (filterv #(not (sx/negation? %)) sens)
        denied (mapv second (filter sx/negation? sens))
        args   #(vec (nm/args %))
        binary (and (empty? denied) (every? #(= 2 (nm/arity %)) pos))
        marks  (fn [kinds] (for [k kinds, q (marks-over-all tax k pos v)] [:prop k q]))]
    (into #{}
          cat
          [(when (and (empty? denied) (= 2 (count pos)) (apply = (map nm/arity pos)))
             (let [[s t] pos
                   diff  (keep-indexed (fn [i [x y]] (when (not= x y) (inc i)))
                                       (map vector (args s) (args t)))
                   n     (first diff)]
               (cond
                 (and (= 1 (nm/arity s)) (= (args s) (args t)) (not= (nm/functor s) (nm/functor t)))
                 (tax/separating-keys tax (nm/functor s) (nm/functor t) v)

                 (= 1 (count diff))
                 (concat (when (= 2 n (nm/arity s)) (marks [:functional]))
                         (for [[q m :as qm] (tax/functional-in-arg-over tax (nm/functor s) v)
                               :when (and (= m n)
                                          (contains? (set (tax/functional-in-arg-over
                                                           tax (nm/functor t) v))
                                                     qm))]
                           [:functional-in-arg q n])))))
           (when (and binary (= 2 (count pos)))
             (let [[[a b] [c d]] (map args pos)]
               (when (and (not= a b) (= a d) (= b c))
                 (marks [:asymmetric :anti-symmetric]))))
           (when (and binary (= 1 (count pos)) (apply = (args (first pos))))
             (marks [:irreflexive]))
           (when (and (empty? denied) (= 1 (count pos)) (= 2 (nm/arity (first pos)))
                      (let [f (nm/functor (first pos))]
                        (or (= 'orthogonal f) (tax/genl? tax f 'orthogonal v))))
             (let [[a b] (args (first pos))]
               (tax/separating-keys tax a b v)))
           (when (and binary (<= 2 (count pos) 3) (chain? pos))
             (marks [:anti-transitive]))
           (when (and (= 1 (count pos)) (seq denied) (= 1 (nm/arity (first pos)))
                      (every? #(and (= 1 (nm/arity %))
                                    (= (args (first pos)) (args %)))
                              denied))
             (let [w (nm/functor (first pos))
                   ds (map nm/functor denied)]
               (for [[whole parts] (tax/covers-over tax w v)
                     :when (every? (fn [p] (some #(contains? (tax/genls tax p v) %) ds)) parts)
                     [ps kind] (tax/covers-of tax whole)
                     :when (= ps parts)]
                 [:cover [whole parts] kind])))])))

(defn- separated-cover-keys
  "The flat-cache keys of a cover refuted through a separation's denial over the member
  sentences `sens`, at vantage `v` (`membership/term-nogoods`' cover arm): for a
  membership `(s x)` under a cover's whole each of whose parts a denial among `sens` or
  another membership among them denies, the cover's key and the keys of each route a
  separation denies a part through under the soundness rule of `res/separation-denials`
  (`tax/monotonic-route-witness`).  Empty unless `sens` holds two memberships of one
  term."
  [kb sens v]
  (let [tax    (reasoning/taxonomy kb)
        pos    (filterv #(and (not (sx/negation? %)) (= 1 (nm/arity %))) sens)
        denied (mapv second (filter sx/negation? sens))
        x      (first (nm/args (first pos)))]
    (when (and (< 1 (count pos)) (= (count pos) (count (remove sx/negation? sens)))
               (every? #(= [x] (vec (nm/args %))) (concat pos denied))
               (every? #(symbol? (nm/functor %)) pos))
      (let [cls   (res/holding-class kb)
            types (mapv nm/functor pos)
            ds    (map nm/functor denied)]
        (into #{}
              cat
              (for [s             types
                    [whole parts] (tax/covers-over tax s v)
                    :let [per (for [p parts]
                                (if (some #(contains? (tax/genls tax p v) %) ds)
                                  [#{}]
                                  (for [d types
                                        :when (not= d s)
                                        r (tax/separation-routes-held tax d p)
                                        :when (tax/monotonic-route-witness tax r v cls)]
                                    (:keys r))))]
                    :when (every? seq per)
                    [ps kind] (tax/covers-of tax whole)
                    :when (= ps parts)]
                (into #{[:cover [whole parts] kind]} (comp cat cat) per)))))))

(defn- minted-from
  "The handles of the sentences the `genl` edges among `hs` were minted from: the source
  of each justification of such an edge an argument declaration's entailment holds up
  (`special/mint-informant?`), which `special/entail-arg-type` stores first among its
  antecedents.  `(disjoint gladdens saddens)` over `(genlArg disjoint 1 thing)` mints
  `(genl gladdens thing)`, so a clash that edge convicts through names the `disjoint`."
  [kb hs]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (into #{}
          (comp (filter #(= 'genl (some-> (p/get-sentex recs %) :sentence nm/functor)))
                (mapcat #(jtms/supports tms %))
                (keep #(jtms/justification tms %))
                (filter #(special/mint-informant? (:informant %)))
                (keep #(first (:antecedents %))))
          hs)))

(defn- placed-grounds
  "The grounds the arity nogood over `members` is placed through at the context `v`, or
  at every context for a nil `v`, read off the antecedents of each justification of its
  placed `(contradicts …)`: the bindings (`arity/binding-grounds`) that are not members,
  and the sentences the `genl` edges among them were minted from (`minted-from`)."
  [kb members v]
  (let [tms   (reasoning/tms kb)
        recs  (:records kb)
        antes (into []
                    (comp (keep #(p/get-sentex recs %))
                          (filter #(and (= 'contradicts (nm/functor (:sentence %)))
                                        (or (nil? v) (= v (:context %)))
                                        (= members (into #{} (map sx/handle-id) (rest (:sentence %))))))
                          (mapcat #(jtms/supports tms (:id %)))
                          (keep #(jtms/justification tms %))
                          (filter #(= exc/nogood-informant (:informant %)))
                          (map :antecedents))
                    (when (seq members)
                      (reads/as-stored-with-term (:index kb) (sx/sentex-handle (first members)))))]
    (-> #{}
        (into (comp (mapcat #(arity/binding-grounds kb %)) (remove members)) antes)
        (into (minted-from kb (into #{} cat antes))))))

(defn clash-grounds
  "The declarations report `r` convicts through, as `{:handle :sentence :context}` maps in
  content order: the believed supporters of the flat-cache entries its conviction reads
  (`ground-keys`, and `separated-cover-keys` for a cover refuted through a separation's
  denial) that one of its vantages sees, or the whole KB for a report weighed at
  none; for an arity clash, the grounds it is placed through at each vantage
  (`placed-grounds`).  No `genl` edge is named; an edge an argument declaration minted is
  named by the sentence it was minted from.  Empty for a rebuttal and an `:inherited`
  clash, whose reasons are members (docs/nmtms.md, \"The clash reports\")."
  [kb r]
  (if (contains? #{nil :inherited} (:kind r))
    []
    (let [tax  (reasoning/taxonomy kb)
          tms  (reasoning/tms kb)
          recs (:records kb)
          sens (mapv :sentence (:sides r))
          at   (fn [v]
                 (if (contains? #{:arity :arity-descension} (:kind r))
                   (placed-grounds kb (set (:nogood r)) (when (symbol? v) v))
                   (mapcat #(tax/visible-supporters tax % v)
                           (into (ground-keys tax sens v) (separated-cover-keys kb sens v)))))]
      (->> (or (seq (report-vantages r)) [nil])
           (into #{} (mapcat at))
           (into [] (comp (filter #(jtms/in? tms %))
                          (keep #(p/get-sentex recs %))
                          (map (fn [s] {:handle (:id s) :sentence (sx/sentence-of s)
                                        :context (:context s)}))))
           (sort-by (juxt :sentence :context) nm/compare-form)
           vec))))

(defn defeat-grounds
  "The grounds (`clash-grounds`) of the placed nogoods behind the `defeat` and
  `(contradicts …)` handles `ds` (`exc/defeats-of`), each read at the context it is
  placed in, in content order: what `why-not` names beside a placed defeat."
  [kb ds]
  (let [recs (:records kb)]
    (->> ds
         (mapcat (fn [d]
                   (let [s (p/get-sentex recs d)]
                     (mapcat (fn [ms]
                               (clash-grounds kb (with-meta {:kind   (decide/placed-kind kb ms)
                                                             :nogood ms
                                                             :sides  (mapv #(hash-map :sentence %)
                                                                           (sort nm/compare-form
                                                                                 (map #(sx/sentence-of (p/get-sentex recs %)) ms)))}
                                                   {::vantages #{(:context s)}})))
                             (if (= 'defeat (nm/functor (:sentence s)))
                               (exc/defeat-member-sets kb d)
                               [(into #{} (map sx/handle-id) (rest (:sentence s)))])))))
         distinct
         (sort-by (juxt :sentence :context) nm/compare-form)
         vec)))

(defn with-grounds
  "`reports` with each one's `clash-grounds` under `:grounds`, read now: a declaration
  can move under a report whose members did not, so the grounds ride no memo."
  [kb reports]
  (mapv #(assoc % :grounds (clash-grounds kb %)) reports))

(defn- report-order
  "One clash report's sort key: each side's sentence then its context, in side order.
  Compared by `nm/compare-form`; no handle enters it."
  [r]
  (mapv (juxt :sentence :context) (:sides r)))

(defn ranked
  "`reports` in content order (`report-order`).  Every reader of `conflicts-of` or
  `contradictions-of` owes this call, since those hold the order the candidate index
  answered in."
  [reports]
  (nm/sort-by-content-key report-order nm/compare-form reports))

(defn- placed-verdicts
  "`{[kind members] {context verdict}}` over the stored `(contradicts …)` handles `hs`: each
  one IN under the informant `nogood`, naming no superseded member (the restated
  spellings' nogood reports that clash), of a kind `decide/placed-kind` names, and kept by
  `seen?` (`(fn [handle context])`), with the verdict its own context reads
  (`exc/verdict-at-reader`): `:hard`, `:dilemma` or `{:defeat h}`.  An inherited clash's
  discovery entry goes into `found-by` (`inherited/inherited-clashes`)."
  [kb found-by seen? hs]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (reduce (fn [acc h]
              (let [sx (p/get-sentex recs h)
                    s  (:sentence sx)
                    v  (:context sx)
                    ms (when (and (seq? s) (= 'contradicts (first s)) (jtms/in? tms h)
                                  (some #(= exc/nogood-informant (:informant (jtms/justification tms %)))
                                        (jtms/supports tms h)))
                         (into #{} (map sx/handle-id) (rest s)))
                    k  (when (and ms (not-any? #(jtms/superseded? tms %) ms))
                         (decide/placed-kind kb ms))]
                (if (and k (seen? h v))
                  (let [km [k ms]]
                    (when (= :inherited k)
                      (vswap! found-by assoc km (get (inherited/inherited-clashes kb) ms)))
                    (assoc-in acc [km v] (exc/verdict-at-reader kb ms v)))
                  acc)))
            {} hs)))

(defn- general
  "The members of the contexts `vs` that see no other member of `vs`."
  [tax vs]
  (into #{} (remove (fn [v] (some #(and (not= v %) (tax/sees? tax v %)) vs))) vs))

(defn- split-of
  "`{context handle}` over the placement verdicts `vm` when they defeat two members or
  more, each defeat at the most general contexts reading it, or nil."
  [tax vm]
  (let [by (reduce (fn [m [v d]] (if (map? d) (update m (:defeat d) (fnil conj #{}) v) m)) {} vm)]
    (when (< 1 (count by))
      (into {} (for [[h vs] by, v (general tax vs)] [v h])))))

(defn- report-of
  "The report of the placed nogood `[kind members]` weighed at `vantages`, carrying the
  `{context handle}` map `split` when its placements disagree."
  [kb found-by [kind members :as km] vantages split]
  (let [recs      (:records kb)
        tms       (reasoning/tms kb)
        rebuttal? (contains? #{:negation :inherited} kind)
        sens      (sort nm/compare-form (map #(:sentence (p/get-sentex recs %)) members))
        rank      (reduce max (map #(strength/rank-of (jtms/defeat-class tms %)) members))
        inh       (get found-by km)]
    ;; a negation pair reports as a rebuttal with no `:kind` and the body first; an
    ;; inherited clash in the rebuttal range, as its discovery stated it
    (clash-report kb (cond-> {:nogood   members
                              :kind     (when-not (= :negation kind) kind)
                              :vantages vantages
                              :priority (if rebuttal? rank (+ 2 rank))
                              :sentence (cond
                                          inh (:sentence inh)
                                          (= :negation kind)
                                          (let [b (first (remove sx/negation? sens))]
                                            (list 'contradicts b (list 'not b)))
                                          :else (apply list 'contradicts sens))}
                       inh   (assoc :inherited (:inherited inh))
                       split (assoc ::vantage-verdicts split)))))

(defn- reports-over
  "`{:conflicts [report] :contradictions [report]}` for the placed `(contradicts …)` handles
  `hs`, each read at the context it is placed in and kept where that context believes and
  sees it.  A nogood is a conflict at the most general of its placement contexts that read
  it hard, and a dilemma at those that read it as a tie.  A nogood whose placement contexts
  defeat different members is a dilemma carrying `{context handle}`, and that report stands
  for the dilemma a reader below the disagreeing contexts reads."
  [kb hs]
  (let [tax      (reasoning/taxonomy kb)
        found-by (volatile! {})
        hid      (memoize #(exc/hidden-fn kb %))
        placed   (placed-verdicts kb found-by
                                  (fn [h v] (not (when-let [hidden? (hid v)] (hidden? h))))
                                  hs)
        at       (fn [vm verdict] (not-empty (into #{} (keep (fn [[v d]] (when (= verdict d) v))) vm)))]
    (reduce (fn [acc [km vm]]
              (let [split (split-of tax vm)
                    hard  (at vm :hard)
                    tie   (at vm :dilemma)]
                (cond-> acc
                  hard  (update :conflicts conj (report-of kb @found-by km (general tax hard) nil))
                  split (update :contradictions conj (report-of kb @found-by km (set (keys split)) split))
                  (and tie (not split))
                  (update :contradictions conj (report-of kb @found-by km (general tax tie) nil)))))
            {:conflicts [] :contradictions []}
            placed)))

(defn read-clashes
  "The hard clashes and the dilemmas of every placed nogood, as `{:conflicts [report]
  :contradictions [report]}` in `clash-report`'s shape, each report's vantages the most
  general placement contexts that read it so (`reports-over`)."
  [kb]
  (if (zero? (reads/stored-count-with-functor (:index kb) 'contradicts))
    {:conflicts [] :contradictions []}
    (reports-over kb (reads/as-stored-with-functor (:index kb) 'contradicts))))

(defn conflicts-of
  "The conflict reports (`read-clashes`), unordered: `ranked` orders them."
  [kb] (:conflicts (read-clashes kb)))

(defn contradictions-of
  "The dilemma reports (`read-clashes`), unordered: `ranked` orders them."
  [kb] (:contradictions (read-clashes kb)))

(defn- placements-seen
  "The stored `(contradicts …)` handles stated in a context `ctx` sees (`tax/context-up`),
  read from the smaller of two sides, compared by index counts: the extents of those
  contexts, or the `contradicts` extent.  So the read costs the lesser of what `ctx` sees
  and the placed nogoods, and never a nogood placed outside both."
  [kb ctx]
  (let [idx   (:index kb)
        recs  (:records kb)
        cs    (set (tax/context-up (reasoning/taxonomy kb) ctx))
        by-f  (reads/stored-count-with-functor idx 'contradicts)
        by-c  (transduce (map #(reads/stored-count-in-context idx %)) + cs)
        placed? (fn [h] (let [s (:sentence (p/get-sentex recs h))]
                          (and (seq? s) (= 'contradicts (first s)))))]
    (if (< by-c by-f)
      (into [] (comp (mapcat #(reads/as-stored-in-context idx %)) (filter placed?)) cs)
      (into [] (filter #(contains? cs (:context (p/get-sentex recs %))))
            (reads/as-stored-with-functor idx 'contradicts)))))

(defn contradictions-at
  "The dilemma reports a reader at `ctx` reads, unordered: one per placed nogood whose
  `(contradicts …)` `ctx` believes and sees at some placement (`exc/hidden-fn`), whose
  verdict at `ctx` is a tie (`exc/verdict-at-reader`), and every member of which `ctx`
  believes and sees.  Each report's vantages are the most general of those placements,
  with `{context handle}` where they defeat different members (`reports-over`)."
  [kb ctx]
  (if (zero? (reads/stored-count-with-functor (:index kb) 'contradicts))
    []
    (let [tax      (reasoning/taxonomy kb)
          hidden?  (or (exc/hidden-fn kb ctx) (constantly false))
          found-by (volatile! {})
          placed   (placed-verdicts kb found-by (fn [h _] (not (hidden? h)))
                                    (placements-seen kb ctx))]
      (into [] (keep (fn [[[_ ms :as km] vm]]
                       (when (and (= :dilemma (exc/verdict-at-reader kb ms ctx))
                                  (not-any? hidden? ms))
                         (report-of kb @found-by km (general tax (keys vm)) (split-of tax vm)))))
            placed))))

(defn- placements-of
  "The stored `(contradicts …)` handles whose sentence is one of `sentences`: every
  placement of those nogoods, read off the term index of each sentence's first member."
  [kb sentences]
  (let [recs (:records kb)
        idx  (:index kb)]
    (into #{} (mapcat (fn [s] (filter #(= s (:sentence (p/get-sentex recs %)))
                                      (reads/as-stored-with-term idx (second s)))))
          sentences)))

;; ---- the dilemmas a batch opens ------------------------------------------
;; `core/preview`'s `:contradictions` (docs/preview.md, "Cost").

(defn opened
  "The dilemma reports of the KB as a batch left it, for `standing-removed` to subtract
  the standing ones from after the rollback, read on the KB with the batch in force.
  `window` is every handle the batch relabelled, stored or suspended.  The reports are
  those of the nogoods a placed `(contradicts …)` in `window` belongs to, each over every
  placement of its sentence (`placements-of`), in content order with its `:grounds`."
  [kb window]
  (let [sents (into #{} (keep #(let [s (:sentence (p/get-sentex (:records kb) %))]
                                 (when (and (seq? s) (= 'contradicts (first s)) (second s)) s)))
                    window)
        rs    (ranked (:contradictions (reports-over kb (placements-of kb sents))))]
    {:sentences sents
     :reports   (mapv vector rs (with-grounds kb rs))}))

(defn standing-removed
  "The reports of `opened` that the KB as it stands now, after the rollback, does not
  hold, with their `:grounds`, in content order: the dilemmas the batch opens.  The
  standing reports are read over the placements of `opened`'s sentences that stand now."
  [kb {:keys [sentences reports]}]
  (let [standing (set (:contradictions (reports-over kb (placements-of kb sentences))))]
    (into [] (keep (fn [[r g]] (when-not (contains? standing r) g))) reports)))

;; ---- the clash no single writer could see ---------------------------------
;;
;; `exposed-clashes`' per-term clash reader and the believed-content reads it takes
;; (docs/contexts.md).

(defn- believed-xf
  "A transducer from handles to the believed, positive sentexes among them.  Belief is
  `jtms/in?`, so a superseded spelling drops out with a defeated one."
  [kb]
  (comp (filter #(jtms/in? (reasoning/tms kb) %))
        (keep #(p/get-sentex (:records kb) %))
        (filter #(not (sx/negative? %)))))

(defn- believed-at-arg1
  "The believed, positive sentexes posted on `term`'s argument-1 root, or nil for a
  non-symbol `term`."
  [kb term]
  (when (symbol? term)
    (into [] (believed-xf kb) (reads/as-stored-with-arg-global (:index kb) 1 term))))

(defn believed-memberships
  "The believed positive unary memberships of `x`, as `[type context handle]` triples,
  in content order."
  [kb x]
  ;; `compare` on the symbols: a keyfn runs per comparison and would allocate each time.
  ;; Symbols order by namespace then name.
  (sort (fn [[t1 c1] [t2 c2]]
          (let [r (compare t1 t2)] (if (zero? r) (compare c1 c2) r)))
        (into []
              (keep (fn [s]
                      (let [sen (:sentence s)]
                        (when (and (sequential? sen) (= 2 (count sen))
                                   (symbol? (first sen))
                                   (= x (second sen)))
                          [(first sen) (:context s) (:id s)]))))
              (believed-at-arg1 kb x))))

(defn- exposure-probes
  "`{:disjoint? (fn [t1 t2]) :visible-from (fn [t1 c1 t2 c2])}` over the taxonomy `tax`,
  each memoized for one pass.  `:disjoint?` reads no `siblingDisjointException` exemption, since a
  reader that does not see one reads the pair separated.  `:visible-from` is the maximal
  common descendant contexts of the first disjointness witness that shares one with `c1`
  and `c2`, kept where the scoped `disjoint?` holds, or nil; it enumerates witnesses only
  after the scoped `disjoint?` at some common descendant of `c1` and `c2` says one exists
  (docs/contexts.md).

  `:disjoint?` reads the declarations unscoped, a superset that `:visible-from`
  narrows to the contexts where the scoped `disjoint?` holds."
  [tax]
  (let [dj  (volatile! {})
        vis (volatile! {})
        memo (fn [v k f]
               (if-let [e (find @v k)]
                 (val e)
                 (let [r (f)] (vswap! v assoc k r) r)))]
    {:disjoint?
     (fn [t1 t2] (memo dj [t1 t2] #((tax/disjointness-test tax t1 nil (constantly false)) t2)))
     :visible-from
     (fn [t1 c1 t2 c2]
       (memo vis [t1 c1 t2 c2]
             #(when (some (fn [k] (tax/disjoint? tax t1 t2 k))
                          (tax/common-descendants tax [c1 c2]))
                (some (fn [w]
                        (let [m (into #{} (filter (fn [k] (tax/disjoint? tax t1 t2 k)))
                                      (tax/maximal-common-descendant-contexts
                                       tax (into [c1 c2] w)))]
                          (when (seq m) m)))
                      (distinct (tax/disjointness-witnesses tax t1 t2))))))}))

(defn- exposed-clashes-for-term
  "The `:disjoint` entries for the jointly-visible clashes among `x`'s believed
  memberships.  `probes` is `exposure-probes`' answer."
  [kb x {:keys [disjoint? visible-from]}]
  (let [ms (believed-memberships kb x)]
    (for [i (range (count ms))
          j (range (inc i) (count ms))
          :let  [[t1 c1] (nth ms i)
                 [t2 c2] (nth ms j)]
          :when (and (not= t1 t2) (disjoint? t1 t2))
          :let  [mx (visible-from t1 c1 t2 c2)]
          :when mx]
      {:violation :disjoint
       :detail    {:term         x
                   :held         [[t1 c1] [t2 c2]]
                   :visible-from mx
                   :message      (str "disjointness clash exposed: " x " holds " t1
                                      " (in " c1 ") and " t2 " (in " c2
                                      "), jointly visible from "
                                      (pr-str (vec (sort nm/compare-form mx))))}})))

(defn separations?
  "Does the KB separate any two types, by a `disjoint` pair, a disjoint metatype, a
  `sibling_disjoint` parent or a `partition`/`separating` cover?  Four set-emptiness reads
  and no walk.  The covers are read because `separation-frame` reads them
  (docs/taxonomy.md)."
  [tax]
  (boolean (or (seq (tax/disjoint-pairs tax))
               (seq (tax/disjoint-metatypes tax))
               (seq (tax/sibling-disjoints tax))
               (seq (tax/separating-covers tax)))))

(defn exposed-clashes
  "`core/exposed-clashes`' body: every jointly-visible disjointness clash the KB holds,
  in `violations`' entry shape, filed nowhere.  A term is a candidate iff it holds two
  believed memberships, so the walk over every stored sentex finds each candidate and
  takes no instance budget.  The `separations?` gate answers `[]` with no record fetched
  for a KB that separates nothing."
  [kb]
  (let [tax (reasoning/taxonomy kb)]
    (if-not (separations? tax)
      []                                             ; nothing separates anything
      (let [probes (exposure-probes tax)
            terms  (into #{}
                         (comp (believed-xf kb)
                               (keep (fn [s]
                                       (let [sen (:sentence s)]
                                         (when (and (sequential? sen) (= 2 (count sen))
                                                    (symbol? (first sen))
                                                    (symbol? (second sen)))
                                           (second sen))))))
                         (p/sentex-ids (:records kb)))]
        (into [] (comp (mapcat #(exposed-clashes-for-term kb % probes))
                       (distinct))
              ;; terms are symbols — a bare sort is the same content order
              (sort terms))))))
