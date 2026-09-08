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
  either, only `(:violations kb)` and `(:chain-stats kb)`, so it sits below both and the
  edge runs the one direction the layering allows.

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
            [vaelii.impl.sentex :as sx]))

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
  (or *report-sink* (:violations kb)))

(defn- dropping-rule
  "The rule an entry blames, as the sentence its author wrote — variable names restored,
  since a rule is stored canonically numbered.  Nil for an entry that names no rule and
  for a rule that has since been retracted, which is itself the answer to why the
  conclusion stopped arriving.

  A rule is named when a *derivation* was refused, which is what the chainer files.  Three
  families name none: an aggregate's numeric refusal and the post-join literal declined
  for answering two ways, both of which are about a *literal* and not a firing; the five notices that a pass stopped
  short of what it might have said — `:exposure-truncated`, `:arbitration-truncated` and
  `:arity-truncated`, where a budget ran out before the work was done, and
  `:constraint-exposure-truncated` and `:arity-report-truncated`, where the work *was* done
  and a cap on entries kept the rest of it unnamed — all of which are about a bound rather
  than about a firing; and what the settle reports about content that was already stored,
  the cross-context `:disjoint` / `:functional` / `:asymmetric` / `:anti-transitive`
  clashes and the `:arity`
  reach over facts a later arity binding convicts.  Those last kinds also arrive *with* a
  rule when the chainer drops a conclusion under one of them, so the discriminant is the
  key rather than the kind — which is why this reads `(:rule entry)` and not a roster."
  [kb entry]
  (when-let [h (:rule entry)]
    (let [rsx (p/get-sentex (:records kb) h)]
      {:rule h
       :sentence (when rsx (if-let [vm (:varmap rsx)]
                             (sx/originalize (:sentence rsx) vm)
                             (:sentence rsx)))})))

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
    (let [run     (:runs @(:chain-stats kb))
          stamped (mapv #(assoc % :run run) entries)]
      (when-not *report-sink*
        (doseq [e stamped]
          (trove/log! {:level :warn :id ::dropped-conclusion :data e})
          (when (:rule e)
            (trove/log! {:level :debug :id ::dropping-rule :data (dropping-rule kb e)}))))
      (swap! (report-target kb)
             (fn [v]
               (let [v' (into v stamped)
                     n  (count v')]
                 (if (<= n max-violations)
                   v'
                   ;; `vec` *over* the `subvec`, not the subvec itself: a subvec holds a
                   ;; reference to the vector it was cut from, so returning one would pin
                   ;; every entry it just dropped — on a ledger that trims again on the
                   ;; next overflow, the cap would bound the count and nothing else.
                   (vec (subvec v' (- n max-violations))))))))))

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
  (when-not (some #(= (dissoc % :run) entry) @(report-target kb))
    (report kb [entry]))
  nil)
