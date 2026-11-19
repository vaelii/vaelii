;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.types.prover
  "The prover protocols, as a held namespace.

  A held namespace is one the development browser's reloader never re-evaluates
  (docs/web.md, *Hot reload*).  Re-evaluating a `defprotocol` defines a new interface and
  empties the protocol's extension map, and re-evaluating a `defrecord` defines a new
  class, so a loaded KB's registered provers would stop answering both.  This namespace
  requires no vaelii namespace, so an edit elsewhere never reloads it as a dependent.

  The prover records are defined, with their methods inline, in the namespaces that
  implement them (`vaelii.impl.provers`, `vaelii.impl.calendar`, …).  The reloader leaves
  a record that exists as it was loaded, so those namespaces reload too.")

(defprotocol Prover
  (applicable?  [prover kb goal context])
  (est-bindings [prover kb goal context])
  (cost         [prover kb goal context])
  (completeness [prover kb goal context])
  (solve        [prover kb goal context]))

(defprotocol SupportingProver
  "A prover whose answer is a function of **stored facts** rather than of the goal's own
  arguments alone, and which can say which facts — the unit table a measure comparison
  normalizes through, the constraints a metric bound is closed out of, the lengths a
  duration sums.

  A separate protocol rather than a sixth `Prover` method, because implementing it is a
  choice: `EvaluableProver` computes `(lessThan 3 5)` from the numbers in front of it and
  has no support to report, while `QuantityProver` reads a `conversionFactor` row before
  it can compare two masses.  Only the second is here.

  **Forward chaining is what needs it.**  A rule antecedent discharged by a prover
  contributes no matched fact, so a firing that rested on one lists the rule and whatever
  the *other* antecedents matched — and a `conversionFactor` row behind the answer is
  supported by nothing the JTMS can reach.  Retracting it then leaves the conclusion
  believed.  `solve-with-support` closes that: each answer carries the handles it was read
  from, the join adds them to the firing's antecedents, and the ordinary relabel withdraws
  the conclusion when any of them goes.  It is the same contract
  `qcn-kb/solve-with-support` and `inherit/solve-with-support` already meet for a
  qualitative and an inherited antecedent.

    support-functors     the functors this prover answers with support, as a set
    support-sources      the functors it *reads* to answer them, as a set
    solve-with-support   the solutions of `Prover/solve`, each as `[bindings support]`

  `support-sources` is what keeps the firing order-independent.  A rule whose antecedent
  this prover answers is triggered by the facts its *other* antecedents match, and a
  `conversionFactor` row is not one of them — so a unit table stated after the rule and
  the facts would never reach a join, and the same three sentences would derive a
  conclusion or not depending on which arrived last.  Naming the sources puts such a datum
  in front of the rules carrying a `support-functors` antecedent, re-joined in full
  (`chain/rejoin-in-full`), exactly as a `(symmetric P)` declaration is.

  Two obligations on an implementer, and both are what makes the protocol sound:

  * **`solve-with-support` answers exactly what `solve` answers.**  The bindings are the
    same solutions in the same order; only the support rides alongside.  A binding several
    derivations give may appear once per derivation, each with its own support
    (`ArgTypeProver`), and its first appearance keeps `solve`'s order.  A prover whose
    two methods disagreed would make a rule fire differently forward and backward.
  * **The support is enough to have produced the answer on its own.**  It may
    over-approximate — a reading taken over a set of declarations names all of them — but
    it may never omit a fact the answer moved with, since that is the fact whose
    retraction would leave a stale conclusion standing.

  An answer with **empty** support is one nothing stored licensed — the diagonal of a
  metric network, an arithmetic identity — and the forward join drops it rather than
  building a justification that names the rule alone while looking as though it named the
  facts (`qcn-kb/solve-with-support` gives the qualitative version of the same case)."
  (support-functors   [prover])
  (support-sources    [prover])
  (solve-with-support [prover kb goal context]))

(defn merge-source-roles
  "Join two proof-local role readings; a local/scoped use wins over a structural use.
  Nil stays nil on the ordinary no-role path. Nonplacing sources constrain no placement
  context; label-only sources retain the primitive's network read. Every source remains
  a dependency and class cap. Reader constraints and actual rewrite-read associations
  are proof metadata, never logical bindings or a whole-row exemption."
  [old-supports old-roles added-supports added-roles]
  (when (or (seq old-roles) (seq added-roles))
    (let [old (set old-supports)
          added (set added-supports)]
      (cond-> (into {}
                    (keep (fn [axis]
                            (let [a (get old-roles axis #{})
                                  b (get added-roles axis #{})
                                  strict (into (into #{} (remove a) old) (remove b) added)
                                  relaxed (into (into #{} (remove strict) a) (remove strict) b)]
                              (when (seq relaxed) [axis relaxed]))))
                    [:nonplacing :label-only])
        (or (seq (:readers old-roles)) (seq (:readers added-roles)))
        (assoc :readers (into (or (:readers old-roles) #{}) (:readers added-roles)))
        (or (seq (:rewrite-reads old-roles)) (seq (:rewrite-reads added-roles)))
        (assoc :rewrite-reads (into (or (:rewrite-reads old-roles) #{})
                                    (:rewrite-reads added-roles)))))))
