;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.violations
  "The dropped-conclusion ledger: what the derivation path refused to store, kept as a
  value a caller can read afterwards instead of thrown at whoever happened to be
  writing.

  A namespace of its own because of **who writes it**.  Two paths file entries and they
  sit on opposite sides of the engine: the forward chainer
  (`vaelii.impl.chain`) files a conclusion it dropped, and the prover registry
  (`vaelii.impl.provers`) files an aggregate's numeric error — and the chainer is built
  *on* the registry, so the registry cannot name it.  The ledger reads nothing from
  either, only `(reasoning/violations kb)` and `(reasoning/chain-stats kb)`, so it sits
  below both and the edge runs the one direction the layering allows.

  Why a ledger rather than a throw: an entry is recorded from inside the semi-naive
  fixpoint and from inside a relabel, and neither may abort — a definitional check that
  aborted mid-fixpoint would leave belief half-computed, which is the failure the value-
  first checks (`vaelii.impl.checks`) exist to avoid.  So a violation is *reported*, and
  the run continues without the conclusion.

  It reads the record store for one thing only: an entry names the rule that concluded
  the dropped sentence by **handle**, and a handle is not something an operator reading
  a log can look up.  So at `:debug` the drop is followed by the rule itself."
  (:require [taoensso.trove :as trove]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.types.reasoning :as reasoning]))

(def ^:private max-violations
  "The ledger accumulates across chaining runs (see `vaelii.core/violations`); this caps
  it so a pathological load cannot grow it unbounded — newest entries win."
  1000)

(def ^:dynamic *report-sink*
  "When bound to an atom, reports accumulate there instead of in the KB ledger or logs.
  Read-only audits use this so evaluative conditions keep their ordinary truth value
  without making merely asking the question mutate live diagnostics."
  nil)

(defn- report-target [kb]
  (or *report-sink* (reasoning/violations kb)))

(defn- newest
  "The ledger `v` cut to its newest `max-violations` entries."
  [v]
  (let [n (count v)]
    (if (<= n max-violations)
      v
      ;; `vec` *over* the `subvec`, not the subvec itself: a subvec holds a reference to
      ;; the vector it was cut from, so returning one would pin every entry it just
      ;; dropped — on a ledger that trims again on the next overflow, the cap would bound
      ;; the count and nothing else.
      (vec (subvec v (- n max-violations))))))

(def ^:dynamic *batch-entries*
  "The entries filed by a batch that can be rolled back, as an identity set, or nil outside
  one.  `vaelii.core`'s `edit!`, `preview` and single `assert` bind it on the thread that
  runs the batch (`batch-entries`), `report` and `report-unstamped` add each entry they
  append, and the rollback removes exactly those (`restore!`).

  Bound per thread, so an entry a reader thread appends while the batch runs is not the
  batch's: the qualitative, metric and sign calculi file their inconsistencies from inside
  a read, and a rollback on the writer's thread leaves what a concurrent `query` filed.
  An identity set, because an entry a reader files can be equal to one the batch filed and
  is still the reader's."
  nil)

(defn batch-entries
  "An empty identity set for `*batch-entries*`, synchronized, since a batch that hands
  work to a `bound-fn` files from that thread too."
  ^java.util.Set []
  (java.util.Collections/synchronizedSet
   (java.util.Collections/newSetFromMap (java.util.IdentityHashMap.))))

(defn- note-batch!
  "Add `entries` to the batch's identity set when a batch is running on this thread."
  [entries]
  (when-let [^java.util.Set filed *batch-entries*]
    (doseq [e entries] (.add filed e))))

(defn restore!
  "Put `kb`'s ledger back to `baseline`, the value it held when a batch began, and keep
  every entry appended since that the batch did not file.  `filed` is the batch's
  `*batch-entries*` set.

  The entries the batch appended are removed and the entries it withdrew or cut off at
  the cap come back, so the ledger holds what it held when the batch began plus what
  other threads filed while it ran.  The restore is one `swap!`, so an entry a reader
  appends during the restore is kept too.  A reader's entry the cap evicted while the batch ran does not come back."
  [kb baseline ^java.util.Set filed]
  (when-let [v (reasoning/violations kb)]
    (let [ours (doto (java.util.Collections/newSetFromMap (java.util.IdentityHashMap.))
                 (.addAll ^java.util.Collection baseline)
                 (.addAll (or filed #{})))]
      (swap! v (fn [cur] (newest (into baseline (remove #(.contains ours %)) cur))))))
  nil)

(defn filed-by-batch
  "The entries of `kb`'s ledger that are in `filed`, the batch's `*batch-entries*` set, in
  ledger order."
  [kb ^java.util.Set filed]
  (filterv #(.contains filed %) (some-> (reasoning/violations kb) deref)))

(defn- dropping-rule
  "The rule an entry blames, as the sentence its author wrote — variable names restored,
  since a rule is stored canonically numbered.  Nil for an entry that names no rule and
  for a rule that has since been retracted, which is itself the answer to why the
  conclusion stopped arriving.

  A rule is named when a *derivation* was refused, which is what the chainer files.  Three
  families name none: an aggregate's numeric refusal and the post-join literal declined
  for answering two ways, both of which are about a *literal* and not a firing; and the
  notice that a sweep stopped short of what it might have said, which is about a bound
  rather than about a firing.
  This reads `(:rule entry)` rather than a roster of kinds."
  [kb entry]
  (when-let [h (:rule entry)]
    (let [rsx (p/get-sentex (:records kb) h)]
      {:rule h
       :sentence (when rsx (sx/authored-sentence rsx))})))

(defn report
  "Append dropped-conclusion entries to the accumulating ledger, stamped with the
  chaining run that dropped them, and log each at :warn — a drop must be visible even to
  a caller who never reads the ledger (a bulk load polls nothing).

  The `:warn` line carries the entry as filed, which names the rule by handle.  At
  `:debug` each drop that blames a rule is followed by that rule's own sentence: the
  handle is what the ledger stores and the sentence is what the operator was going to go
  looking for, and the lookup rides inside Trove's payload delay, so a run at `:warn`
  pays for none of it.

  No `!`: this accumulates a report and destroys nothing, and the ledger it appends to is
  emptied only by `vaelii.core/clear-violations!`, which does."
  [kb entries]
  (when (seq entries)
    (let [run     (:runs @(reasoning/chain-stats kb))
          stamped (mapv #(assoc % :run run) entries)]
      (if *report-sink*
        (swap! *report-sink* #(newest (into % stamped)))
        (do
          (doseq [e stamped]
            (trove/log! {:level :warn :id ::dropped-conclusion :data e})
            (when (:rule e)
              (trove/log! {:level :debug :id ::dropping-rule :data (dropping-rule kb e)})))
          (note-batch! stamped)
          (swap! (reasoning/violations kb) #(newest (into % stamped))))))))

(defn report-unstamped
  "Append one entry to the ledger as it is, with no chaining-run stamp and no log line:
  `report` for a reading no firing reaches, so there is no run to name.  The
  qualitative, metric and sign calculi file their inconsistencies here and log them
  themselves.  A KB with no ledger answers nil."
  [kb entry]
  (if *report-sink*
    (swap! *report-sink* #(newest (conj % entry)))
    (when-let [v (reasoning/violations kb)]
      (note-batch! [entry])
      (swap! v #(newest (conj % entry))))))

(defn report-once
  "`report` one entry, unless an entry equal to it (`:run` aside) already stands in the
  ledger.

  For a refusal that is **recomputed rather than remembered**: a count is reduced again
  on every query, every re-check and every settle pass, and a post-join literal is
  re-solved on every firing attempt of its rule.  Recording each occurrence would fill a
  ledger capped at its newest 1000 entries with copies of one defect and evict the
  derivation-path drops it exists to report.  `:run` is ignored in the comparison because
  a later run meeting the same defect is the same defect, not a second one."
  [kb entry]
  (when-not (some #(= (dissoc % :run) entry) (some-> (report-target kb) deref))
    (report kb [entry]))
  nil)

(defn withdraw!
  "Remove the entries rule `rule` filed for dropping `sentence` in `context`, once the
  conclusion has been placed after all.

  The one entry a later event retracts.  A firing dropped on an argument constraint is
  remembered and re-asked (`chain/release-refusal!`), and when the type it lacked
  arrives the conclusion is stored — the KB an arrival order that brought the type first
  would have built, which files nothing.  Left standing, the entry would report which
  order this KB was loaded in rather than anything wrong with it."
  [kb sentence context rule]
  (swap! (reasoning/violations kb)
         (fn [v]
           (into [] (remove #(and (= rule (:rule %)) (= sentence (:sentence %))
                                  (= context (:context %))))
                 v))))
