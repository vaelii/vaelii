;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.prover
  "The `(bravely S)` / `(cautiously S)` prover, opted into with `(add-reasoner kb
  :brave-cautious)`: `S` is in some, or every, optimal labeling of the dilemmas the asking
  context reads, from `label/classify-datum`.  The read commits nothing.  Ground `S` only;
  the answer carries no support, so as a rule antecedent it derives nothing.  See
  docs/labeling.md, \"Reading brave/cautious without committing\"."
  (:require
   [vaelii.impl.asp.label :as label]
   [vaelii.impl.kb :as kb]
   [vaelii.impl.resolution :as res]
   [vaelii.impl.sentex :as sx]
   [vaelii.impl.taxonomy :as tax]
   [vaelii.impl.types.prover :as prover-types]
   [vaelii.impl.types.reasoning :as reasoning]))

(defn- modal-goal? [goal]
  (and (sequential? goal)
       (contains? #{'bravely 'cautiously} (first goal))
       (= 2 (count goal))
       (sx/ground-term? (second goal))))

(defn- visible-handles
  "The handles of `s` stored in `context`'s `genlCx` ancestor set that `context` believes
  (`res/believed-at?`): what a ground `ask` of `s` reads at `ask`'s level (what is
  stored, no rule expansion).  Empty at a variable context."
  [kb s context]
  (when-not (sx/variable? context)
    (into [] (comp (keep #(kb/find-sentex-handle kb s %))
                   (filter #(res/believed-at? kb % context)))
          (tax/context-up (reasoning/taxonomy kb) context))))

(defn- class-at
  "The class of `s` at `context`: the strongest (`:true` over `:supportable` over
  `:false`) of its visible handles' classes (`label/classify-datum` at `context`), since
  `s` holds in a labeling when one of them does.  A handle no dilemma the context reads
  classifies is believed in every labeling, so it reads `:true`.  Nil when no handle is
  visible."
  [kb s context]
  (let [cs (into #{} (map #(or (label/classify-datum kb % context) :true))
                 (visible-handles kb s context))]
    (some cs [:true :supportable :false])))

(defn- holds?
  "Does `(<modal> s)` hold in `context`?"
  [kb modal s context]
  (case (class-at kb s context)
    :true        true                            ; every resolution: brave & cautious
    :supportable (= modal 'bravely)              ; some only: brave, not cautious
    false))                                      ; no resolution, or not believed

(defrecord BraveCautiousProver []
  prover-types/Prover
  (applicable?  [_ _ goal _] (modal-goal? goal))
  (est-bindings [_ _ _ _] 1)          ; a ground modal check: it holds or it does not
  (cost         [_ _ _ _] :compute)   ; a backend solve (brave + cautious), or the solve-free bracket
  ;; Authoritative for its shape: `bravely`/`cautiously` are not assertible and no rule
  ;; concludes one, so the superset claim holds against an empty field — as it does for
  ;; `different` — and `sole-prover` guards it like any other claimant regardless.
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context]
    (let [[modal s] goal]
      (if (holds? kb modal s context) [{}] []))))

(defn brave-cautious-prover
  "The `(bravely S)` / `(cautiously S)` prover, for `add-prover` — or, the ordinary way in,
  `(add-reasoner kb :brave-cautious)`."
  []
  (->BraveCautiousProver))
