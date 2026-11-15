;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.vocabulary
  "What the engine does with each term of its own grammar — the answer to \"is this
  declaration enforced?\", which is otherwise only readable by grepping `special.clj` and
  `checks.clj`.

  The question exists because nothing about a declaration's *shape* says whether anything
  reads it.  A naming invariant passes on anything correctly spelled, so
  `(maxCardinality parentOf 2)` is a well-formed ternary fact, storable, believed, and
  read by nobody — and a KB author gets identical silence from a constraint that is
  enforced and one that was never implemented.  A classification table is what turns that silence into
  an answer.

  **Population: the `definitional_predicate` members and the `syncategorematic`
  constants.**  Not every predicate in the KB — a domain relation is *supposed* to be
  inert, and `(likes Fred Mary)` asks nothing of the engine.  A `definitional_predicate`
  is a predicate a term's definitional block is written in
  (`handbook/06-definitional-block.md`), so one declared and read by nothing is a defect
  rather than the normal case.  `Quote` and the `set/*` wrappers are syntax the engine
  reads rather than block predicates, and the KB marks each one `syncategorematic`.  The
  classification answers for every grammar term core.txt comments; the audit requires an
  answer only of the population.

  **Two classes, and the distinction is the point.**  `:enforced` means some code path
  reads it and the KB will refuse, derive, or answer differently because of it — the
  string under that key says which path, and whether that path is keyed on this functor
  by name or is a generic mechanism the declaration merely enrols in.  `:inert` means nothing does,
  with `:why` recording that this is a decision rather than an omission: most of the
  inert entries are *derived* predicate types, which exist so a KB can be queried for
  what a mark implies, and are read by no check because the mark itself is what the
  checks read.

  **Where the answer is written.**  Not here: each term's prose sits on its own entry in
  `vaelii.impl.predicates`, beside that term's shape, storage kind and facets, and this
  table is that field read back.  One entry per term is what stops the answer being a
  second list keyed by the same functors — the failure the declaration namespace exists
  to end — and the *class* is read off the `:facets` rather than off which key the prose
  was written under, so a term the engine demonstrably reads cannot be classified inert
  by writing different prose beside it.

  **`audit` checks the classification**, with two tests over it: a term of the population
  with no classification entry fails, and an entry naming a term core.txt no longer
  comments fails.  So the next plausible-looking functor cannot land unimplemented in
  silence, and a retired one cannot leave a stale claim behind.  `:contradicted` is the
  third, and the one that needs no judgement: a functor some data structure in the tree
  proves has behaviour — the special table's keys, the aggregates, the evaluables, the
  rule wrappers — and the table calls inert is a contradiction, not a matter of
  opinion.

  **Why the answer does not live in the ontology.**  A `(notEnforced P)` marker was the
  obvious alternative and is self-defeating — it would be a declaration the engine does
  not read, which is the exact defect this namespace exists to find.  Putting it in each
  term's `comment` prose is worse: nothing can check prose without matching strings, so it
  would drift the first time a check was added and the sentence was not.  A table in code
  drifts too, but a test can see it drift."
  (:require [clojure.java.io :as io]
            [vaelii.impl.io.text :as text]
            [vaelii.impl.predicates :as pr]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]))

(def vocabulary-context
  "The context the vocabulary file loads into."
  sx/root-context)

(def vocabulary-file
  "The classpath path of the KB file whose `comment` sentences name the terms this
  table may answer for."
  "kb/upper/core.txt")

(def population-markers
  "The memberships that name the audit's population: `definitional_predicate`, whose
  members' sentences make up a term's definitional block, and `syncategorematic`, the
  syntax constants the engine reads, which are no predicate of a block."
  '[definitional_predicate syncategorematic])

(def ^:private file-terms
  "Every term `vocabulary-file` comments, read once: the terms a classification entry may
  name without being `:retired`."
  (delay (into #{}
               (keep (fn [form]
                       (let [[s _] (text/peel-form form)]
                         (when (and (seq? s) (= 'comment (first s)) (symbol? (second s)))
                           (second s)))))
               (text/read-forms (io/resource vocabulary-file)))))

(def classification
  "`term -> {:enforced \"where\"}` or `term -> {:inert \"why\"}`, over the grammar terms
  core.txt comments.

  The `:enforced` prose names a code path, so it is the thing to update when one moves —
  and `audit` is what notices when a *term* moves without it.  Both live on the term's
  entry in `vaelii.impl.predicates`; this is that field read back, keyed and shaped the
  way `classify`, `audit` and `core/interpreted` have always read it.

  **The class comes from the facets**, not from which key the prose was written under: a
  term carrying `:cached`, `:convicts`, `:answers` or any other lane is enforced whatever
  is written beside it, and only a term whose facets say `:inert` — which the `inert`
  constructor is the sole way to write — is classified inert.

  **The population is the ontology's**, and stays a question about the KB rather than
  about the declaration: a term the KB marks `definitional_predicate` or
  `syncategorematic` and nobody answers for lands in `audit`'s `:unclassified`, which is
  the whole mechanism."
  (into {}
        (keep (fn [[term spec]]
                (when-let [prose (or (:enforced spec) (:inert spec))]
                  [term {(if (contains? (:facets spec) :inert) :inert :enforced) prose}])))
        pr/entries))

(defn classify
  "What the engine does with vocabulary term `term`: `{:enforced \"where\"}`,
  `{:inert \"why\"}`, or nil for a term the table does not cover.

  Nil is **not** \"nothing reads it\" — the table answers for core.txt's grammar, so an
  ordinary domain predicate is simply not a term this question is asked about."
  [term]
  (get classification term))

(defn- declared-terms
  "The audit's population in `kb`: every term a `(definitional_predicate ?term)` or
  `(syncategorematic ?term)` query answers in `vocabulary-context`
  (`population-markers`).  Read off the loaded KB, so the audit is about what this KB
  has.  **Answered**, not stored: a membership a `genl` edge or a rule derives, as core.txt
  derives the orders' through `type_type_by_order`, puts its term in the population as a
  stated one does.  **Believed**, since a membership is a claim about the term: a KB that
  retracts one no longer asks the term to be answered for."
  [kb]
  (into (sorted-set)
        (comp (mapcat #(provers/ask kb (list % '?term) vocabulary-context))
              (keep #(get % '?term))
              (filter symbol?))
        population-markers))

(def ^:private machine-readable-enforced
  "The functors whose behaviour is provable from a data structure rather than from prose:
  the special-predicate table's own keys, the aggregate table, the evaluable comparisons,
  and the rule wrappers.  `audit` reports a classification entry that calls one of these inert,
  which is the one kind of wrong answer here that does not need a human to notice — and
  every table the engine already keeps as data belongs in it, since each one added is a
  claim nobody has to review again."
  (delay (-> #{}
             (into (map first) special/entries)
             (into (keys sx/aggregate-functors))
             (into provers/evaluable-predicates)
             (into (keys sx/rule-direction-wrappers))
             (conj sx/default-rule-wrapper))))

(defn audit
  "Classify every term of the population `kb` declares (`declared-terms`):

      {:enforced    [[term \"where\"] …]
       :inert       [[term \"why\"] …]
       :unclassified [term …]      ; in the population, and the table says nothing — the defect
       :retired      [term …]      ; the table claims a term core.txt no longer comments
       :contradicted [term …]}     ; called inert, but the special table gives it an arm

  `:unclassified` is what this exists for: a block predicate or syntax constant that
  landed without anybody deciding whether the engine reads it.  `:retired` is the mirror —
  a claim about a term that is gone, which is how a hand-kept table goes quietly wrong.  `:contradicted` is the check
  that needs no judgement at all.

  Vectors sorted by term, so two runs over one KB compare."
  [kb]
  (let [declared (declared-terms kb)
        entry    (fn [t] [t (or (:enforced (classification t)) (:inert (classification t)))])]
    {:enforced     (mapv entry (filter #(:enforced (classification %)) declared))
     :inert        (mapv entry (filter #(:inert (classification %)) declared))
     :unclassified (vec (remove classification declared))
     :retired      (vec (remove @file-terms (sort (keys classification))))
     :contradicted (vec (filter #(and (:inert (classification %))
                                      (contains? @machine-readable-enforced %))
                                declared))}))
