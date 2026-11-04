;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.vantage
  "The joint reading of `CxInference` and a variable context: which readers can answer a
  goal, and the two strategies that answer it, `:fan` (the reference) and `:post-hoc`,
  which return the same answers and witnesses.  See docs/contexts.md."
  (:require [vaelii.impl.except :as exc]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.impl.types.reasoning :as reasoning]))

(def witness-key
  "The key a `CxInference` answer reports its witness under: `:context`, beside the
  bindings.  A variable context unifies the witness into that variable instead."
  :context)

(def ^:dynamic *strategy*
  "Which implementation answers a joint read: `:fan` (the reference) or `:post-hoc` (the
  default).  A cost decision that must not change the answer set; outside post-hoc's
  domain the fan answers whatever this says
  (docs/defenses.md#post-hoc-placement-is-the-default-because-it-is-bounded)."
  :post-hoc)

;; ---- the readers --------------------------------------------------------

(defn- candidate-contexts
  "The contexts holding a stored fact some literal of `goals` matches, read unscoped:
  one record fetch per match."
  [kb goals]
  (into #{}
        (comp (mapcat (fn [g] (res/matches-visible kb g '?ctx)))
              (map first)
              (keep (fn [h] (:context (p/get-sentex (:records kb) h)))))
        goals))

(defn readers
  "Every context that could witness a joint answer to `goals`: the `genlCx` lattice's
  contexts, plus each context outside it holding a fact the goals match
  (`candidate-contexts`) or an ingredient of a computed answer to one of them
  (`provers/ingredient-contexts`).

  The union is closed under `tax/meet-closure` as it stands.  A context outside the
  lattice sees only itself and no context sees it, so it meets no other context, and a
  common descendant of two lattice contexts is a lattice context."
  [kb goals]
  (into (set (tax/contexts (reasoning/taxonomy kb)))
        (concat (candidate-contexts kb goals)
                (mapcat #(provers/ingredient-contexts kb %) goals))))

;; ---- (a) the fan --------------------------------------------------------

(defn- attach-witness
  "`(fn [answer w])` that attaches the witness `w` to one answer, or returns nil to drop
  it.  A variable `witness` unifies into the binding map, inside `:bindings` for a
  `:proof?` answer, and drops an answer whose goal already binds it to another context.
  `CxInference` puts `w` under `witness-key` at the answer's top level."
  [witness]
  (if (sx/variable? witness)
    (fn [b w]
      (let [inner (get b :bindings b)]
        (when (= w (get inner witness w))
          (if (identical? inner b)
            (assoc b witness w)
            (assoc b :bindings (assoc inner witness w))))))
    (fn [b w] (assoc b witness-key w))))

(defn- witnessed
  "`by-binding` (`answer -> #{contexts that answered it}`) as one answer per maximal
  witness (`tax/max-cxs`), witnesses in sorted order.  Both strategies call it.
  Under `:proof?` an answer is one derivation, so two proofs of one binding keep a witness
  each."
  [kb witness by-binding]
  (let [t      (reasoning/taxonomy kb)
        attach (attach-witness witness)]
    (vec (mapcat (fn [[b ws]]
                   (keep (fn [w] (attach b w)) (sort (tax/max-cxs t ws))))
                 by-binding))))

(defn fan
  "Ask every reader the scoped question through `run-at`, a fn of the context to read in,
  and return the witnessed answers.  With no reader at all, `run-at` reads at `'?ctx`
  under `exc/*unscoped-own*` and the answers carry no witness."
  [kb goals witness run-at]
  (let [rs (readers kb goals)]
    (if (empty? rs)
      (binding [exc/*unscoped-own* true] (vec (run-at '?ctx)))
      (witnessed kb witness
                 (reduce (fn [acc reader]
                           (reduce (fn [m b] (update m b (fnil conj #{}) reader))
                                   acc (run-at reader)))
                         {} rs)))))

(defn fan-distinct
  "The fan for a read answering sentex records (`sentexes-matching`): the distinct records
  some reader returns, with no witness attached.  Lazy over the readers; the `readers`
  seed is paid before the first element."
  [kb goals run-at]
  (let [rs (readers kb goals)]
    (if (empty? rs)
      (binding [exc/*unscoped-own* true] (vec (distinct (run-at '?ctx))))
      (sequence (comp (mapcat run-at) (distinct)) rs))))

;; ---- (b) post-hoc placement ---------------------------------------------

(def ^:dynamic *rows-per-reader*
  "The join rows post-hoc builds per lattice context (at least one context) before it
  abandons the pass to the fan.  A cost decision that changes no answer
  (docs/defenses.md#post-hoc-placement-is-the-default-because-it-is-bounded)."
  20)

(def ^:private abandoned
  "What the join returns once it passes its budget."
  ::abandoned)

(defn- placing-provers
  "The provers the literal `g` dispatches to at `'?ctx` when every one of them is
  `provers/placeable-prover?`, else nil.  The answer changes under substitution, since
  `applicable?` tests groundness: `(zt_t ?a)` reaches the stored-fact prover alone and
  `(zt_t ZX)` reaches `ArgTypeProver` as well."
  [kb reg g]
  (when (and (sequential? g) (not (sx/deferred-literal? g)))
    (let [ps (provers/applicable-provers kb reg g '?ctx)]
      (when (and (seq ps) (every? provers/placeable-prover? ps))
        ps))))

(defn placeable?
  "Is every literal of `goals` answered by `provers/placeable-prover?`s alone, as
  `provers/applicable-provers` dispatches it?  Post-hoc answers only such a goal, and the
  join re-asks `placing-provers` of each literal it substitutes."
  [kb goals]
  (let [reg (provers/registry kb)]
    (every? #(placing-provers kb reg %) goals)))

(defn- literal-rows
  "The unscoped answers `ps` give the literal `g`, as `[bindings handles contexts]`, one per
  derivation: a stored match once per `genl` route it subsumes through
  (`provers/subsumption-routes`, memoized in the volatile `routes` by functor pair), or a
  `SupportingProver` answer with its support, with the contexts of every handle.  Lazy."
  [kb routes ps g]
  (let [recs  (:records kb)
        gf    (nm/functor g)
        route (fn [sf]
                (or (get @routes [gf sf])
                    (let [r (provers/subsumption-routes kb gf sf)]
                      (vswap! routes assoc [gf sf] r)
                      r)))]
    (mapcat
     (fn [pr]
       (if (provers/fact-prover? pr)
         (for [[h b] (res/matches-visible kb g '?ctx)
               :let  [sx (p/get-sentex recs h)]
               :when sx
               r     (route (nm/functor (:sentence sx)))]
           [b (into #{h} (map first) r) (into #{(:context sx)} (keep second) r)])
         (map (fn [[b sup]]
                [b sup (into #{} (keep #(:context (p/get-sentex recs %))) sup)])
              (prover-types/solve-with-support pr kb g '?ctx))))
     ps)))

(defn- join-carrying-contexts
  "The conjunctive join of `goals` answered at `'?ctx`, as `[bindings handles contexts]`
  rows: each row carries the sentexes its derivation rests on (`literal-rows`) and their
  contexts.  A row whose contexts have no common descendant is dropped at the stage it
  dies.  Returns `abandoned` once a stage after the first builds more than `budget` rows,
  or a substituted literal dispatches to other provers than the literal as written.  A
  reader's scoped read plans the literals in its own order, and a plan that leads with
  `(t1 ?a)` never reaches the argument-type prover that `(t1 X)` reaches here."
  [kb goals budget]
  (let [tax    (reasoning/taxonomy kb)
        reg    (provers/registry kb)
        routes (volatile! {})
        built  (volatile! 0)
        ;; the first stage is not metered (docs/defenses.md, "Post-hoc placement is the
        ;; default because it is bounded")
        stage  (volatile! 0)]
    (reduce
     (fn [sols literal]
       (vswap! stage inc)
       (let [metered? (> @stage 1)
             written  (placing-provers kb reg literal)
             out
             (reduce
              (fn [acc [b hs ctxs]]
                (let [g  (res/substitute literal b)
                      ps (placing-provers kb reg g)]
                  (if (or (nil? ps) (not= ps written))
                    (reduced abandoned)
                    (reduce
                     (fn [acc [b' hs' ctxs']]
                       (if (and metered? (> @built budget))
                         ;; doubly reduced: stops this reduce and the one over `sols`
                         (reduced (reduced abandoned))
                         (let [ctxs' (into ctxs ctxs')]
                           (when metered? (vswap! built inc))
                           (if (or (= ctxs' ctxs) (tax/common-descendant? tax ctxs'))
                             (conj acc [(merge b b') (into hs hs') ctxs'])
                             acc))))
                     acc
                     (literal-rows kb routes ps g)))))
              []
              sols)]
         ;; the sentinel arrives bare from the two inner reduces; stop the goals reduce on it
         (if (identical? abandoned out) (reduced abandoned) out)))
     [[res/no-bindings #{} #{}]]
     goals)))

(defn- retires-an-ingredient?
  "Does the reader `w` retire the stored spelling of one of `supporters`
  (`res/retired-for?`)?  Called on a KB holding a merge only."
  [kb merged? supporters w]
  (let [visible (delay (res/visible-supporter-fn kb w))
        recs    (:records kb)]
    (some (fn [h]
            (when-let [sx (p/get-sentex recs h)]
              (res/retired-for? kb visible merged? (sx/sentence-of sx))))
          supporters)))

(defn- placements
  "The contexts an answer resting on `supporters`, stored in `ctxs`, is read from:
  `tax/maximal-common-descendant-contexts` of `ctxs`, or, when a supporter is defeated or
  closure-excepted anywhere, the maximal common descendants that see every supporter
  (`res/supporter-visible?`), the descent `res/exception-aware-placements` makes forward.
  On a KB holding a merge, a context that retires an ingredient is dropped."
  [kb supporters ctxs]
  (let [tax     (reasoning/taxonomy kb)
        merged? (tax/merged-term-pred tax)
        base    (if (some #(or (exc/defeated-anywhere? kb %) (exc/closure-excepted-anywhere? kb %))
                          supporters)
                  (tax/max-cxs
                   tax (filterv (fn [c] (every? #(res/supporter-visible? kb % c) supporters))
                                (tax/common-descendants tax ctxs)))
                  (tax/maximal-common-descendant-contexts tax ctxs))]
    (cond->> base
      merged? (remove #(retires-an-ingredient? kb merged? supporters %)))))

(defn post-hoc
  "The witnessed answers of `goals` from one unscoped join, each row placed by
  `placements` and its bindings projected onto the goals' variables before grouping.
  Returns `abandoned` when the join abandons, or when `prepared-at` prepares the goal at
  `CxNothing` differently from `goals`, which means a merge rewrote it."
  [kb goals witness budget prepared-at]
  (let [vars (or (sx/symbols-where sx/variable? goals) #{})
        ;; a reader above a merge asks the goal as written, so one unscoped pass cannot
        ;; answer for it; `CxNothing` sees no equality and prepares the goal as written
        rewritten? (and prepared-at (not= goals (prepared-at 'CxNothing)))
        rows (if rewritten? abandoned (join-carrying-contexts kb goals budget))]
    (if (identical? abandoned rows)
      abandoned
      ;; projected first: each raw row binds the `?ctx` its match came from, and two
      ;; derivations of one answer would otherwise never group
      (witnessed kb witness (reduce (fn [acc [b hs ctxs]]
                                      (let [b (select-keys b vars)]
                                        (reduce (fn [m w] (update m b (fnil conj #{}) w))
                                                acc (placements kb hs ctxs))))
                                    {} rows)))))

;; ---- the entry point -----------------------------------------------------------

(defn- nothing-to-witness?
  "Is every literal of `goals` deferred (`sx/deferred-literal?`: `different`, `evaluate`,
  `unknown`, …), so that no literal names a context to witness?
  (docs/defenses.md#a-goal-every-literal-of-which-is-computed-names-no-context)"
  [goals]
  (every? #(and (sequential? %) (sx/deferred-literal? %)) goals))

(defn answers
  "`goals` answered as a joint read, as `{:answers [...] :strategy s}`.  `s` is `:unscoped`
  for a goal every literal of which is deferred (read at `'?ctx`, no witness), `:post-hoc`,
  or `:fan`; `:abandoned-post-hoc true` sits beside `:fan` when post-hoc abandoned the
  pass.  Each answer carries its maximal witness (`attach-witness`).

  `run-at` reads the goal at one named context.  Options: `:witness` (default
  `CxInference`, or the caller's variable), `:expands-rules?` (true puts the read outside
  post-hoc's domain: an expanded rule's antecedent facts are not among `goals`, so their
  contexts never reach a placement), and `:prepared-at` (the goal as prepared at a given
  context)."
  [kb goals run-at {:keys [expands-rules? witness prepared-at]}]
  (let [witness (or witness 'CxInference)]
    (cond
      (nothing-to-witness? goals)
      {:answers (binding [exc/*unscoped-own* true] (vec (run-at '?ctx))) :strategy :unscoped}

      (and (= :post-hoc *strategy*) (not expands-rules?) (placeable? kb goals))
      ;; the budget is sized off the lattice, not `readers`, which scans the match set
      (let [budget (* (max 1 (count (tax/contexts (reasoning/taxonomy kb)))) *rows-per-reader*)
            rows   (post-hoc kb goals witness budget prepared-at)]
        (if (identical? abandoned rows)
          {:answers (fan kb goals witness run-at) :strategy :fan :abandoned-post-hoc true}
          {:answers rows :strategy :post-hoc}))

      :else
      {:answers (fan kb goals witness run-at) :strategy :fan})))
