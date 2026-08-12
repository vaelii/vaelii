;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.llm.score
  "Scoring a set of candidate entries against a hand-written one.

  `vaelii.impl.llm.text` produces candidates and `vaelii.core/check-edit` says whether each
  is *admissible*.  Neither says whether it is **right**, and nothing in the engine can:
  the whole reason the reading direction needs a reviewer is that every check passes on a
  well-formed translation of a claim the text did not make.  So the only honest measure is
  against knowledge somebody wrote by hand, and this is the arithmetic for that.

  ## The gold set is read out of a KB, never transcribed

  A second copy of the fables' sentexes in a scoring fixture would drift from the ones the
  suite actually loads, and a score against a stale gold set is worse than no score.  So
  the gold is a set of **handles** in a loaded KB, and a candidate matches when
  `vaelii.core/handle-of` finds it under one of them.

  That also means the comparison uses the engine's **own** canonical form rather than a
  reimplementation of it: a rule whose variables are named differently, whose antecedents
  arrive in another order, or whose symmetric arguments are the other way round is the same
  sentence to `handle-of` and is therefore the same sentence here (docs/canonicalization.md).
  Nothing about matching is this namespace's opinion.

  ## Two scores, because the constants are unrecoverable

  A fable introduces its characters by kind — *a lion*, *a mouse* — so the names in the
  formal version (`LionA`, `MouseA`) are the modeller's, and no reader of the text could
  produce them.  A strict score therefore reads zero on stories whose structure was
  recovered perfectly, which measures the naming convention rather than the reading.

  So `score` reports both, and the pair is the finding:

  * **strict** — the candidate matched a gold handle as written;
  * **aligned** — the same comparison after renaming the candidate's *introduced*
    individuals onto the gold's, one-for-one, by the types each is asserted to have
    (`alignment`).  A renaming is a bijection or it is not applied, so alignment can never
    merge two characters into one to score better.

  Nothing here writes: `handle-of` is find-only, and the alignment is arithmetic over
  sentences."
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [vaelii.core :as v]
            [vaelii.impl.sentex :as sx]))

;; ---- the gold set --------------------------------------------------------

(defn gold-handles
  "The hand-written version of one document, as handles: every **premise** stored in
  `context`.

  Two filters, both load-bearing.  **Its own context**, not the cone above it — a story
  context sees the upper ontology through `genlCx`, and scoring a reader of one fable
  against the whole shipped schema would measure a recall it was never asked for.  And
  **premises only**: a forward-chained conclusion like `(repaidKindness MouseA LionA)` is
  the engine's contribution rather than the modeller's, so asking a reader to produce it
  would score the chaining twice.  `exceptWhen` meta-sentexes stay, because a rule's
  exception is something the modeller wrote.

  `derived-handles` is the other half — what the KB stores and nobody wrote."
  [kb context]
  (into #{} (comp (map :id) (filter #(v/premise? kb %)))
        (v/sentexes-in-context kb context)))

(defn derived-handles
  "The sentexes `context` holds that nobody asserted — what forward chaining put there.
  A candidate landing on one of these is neither right nor wrong but **not news**: it is
  the same no-op re-assert `vaelii.impl.llm.session/new-assertions` counts as `:known` on
  the page path, and it is scored the same way — out of precision's denominator rather than
  against it."
  [kb context]
  (into #{} (comp (map :id) (remove #(v/premise? kb %)))
        (v/sentexes-in-context kb context)))

;; ---- the individuals a candidate set introduced -------------------------

(defn- typed-as
  "`{individual -> #{predicate …}}` over a set of sentences: every **one-place claim** made
  of each individual.

  Its kind, and also what it did — `(criesWolf BoyA)` counts alongside `(human BoyA)`.
  That is deliberate.  A fable's characters are as much identified by what happens to them
  as by their type, and the type is exactly what a reader is most likely to get differently
  (`boy` where the modeller wrote `human`); an alignment on kind alone would then fail on
  a character the reading recovered completely.  Binary facts are left out because their
  argument order is a second thing to be wrong about, and an alignment that used them would
  start fitting the candidates to the gold."
  [sentences]
  (reduce (fn [acc s]
            (if (and (sequential? s) (= 2 (count s))
                     (symbol? (first s)) (symbol? (second s))
                     (= :individual (v/term-role (second s))))
              (update acc (second s) (fnil conj #{}) (first s))
              acc))
          {}
          sentences))

(defn alignment
  "A renaming of the candidates' introduced individuals onto the gold's, or `{}`.

  Matched by **overlap in the one-place claims made of each** (`typed-as`): a candidate
  individual said to be a `lion` aligns with the gold individual said to be a `lion`.
  Overlap rather than equality, because a candidate that also invented a claim about its
  character — `(has_black_and_white_feathers Lion1)` beside `(lion Lion1)` — is a character
  the reading did recover, and scoring it as unrecovered would count the spurious claim
  twice.

  A **bijection**: pairs are taken greedily in descending overlap, each side used once, so
  no renaming can collapse two characters into one to make more sentences match.  Ties break
  on the two names, so the answer is a function of the two sentence sets and of nothing else.
  A candidate that used a name the gold uses is left alone, whatever the gold says about it
  — that candidate got the name right, and renaming it onto a different gold character
  would turn a wrong claim into a matching one.

  Deliberately narrow.  Aligning on anything richer — the relations a character stands in,
  say — would start fitting the candidate set to the gold, and a score that repairs its own
  input measures the repair."
  [gold-sentences candidate-sentences]
  (let [gold-types (typed-as gold-sentences)
        cand-types (typed-as candidate-sentences)
        ;; every individual the gold names anywhere, not only those it makes a one-place
        ;; claim about: a candidate that used a gold name is a candidate that got the name
        ;; right, and renaming it onto a *different* gold character would score a wrong
        ;; claim as a right one.
        gold-named (into #{} (comp (filter symbol?)
                                   (filter #(= :individual (v/term-role %))))
                         (mapcat #(tree-seq sequential? seq %) gold-sentences))
        pairs (sort-by (fn [[g c n]] [(- n) (str g) (str c)])
                       (for [[g gt] gold-types
                             [c ct] cand-types
                             :let [n (count (set/intersection gt ct))]
                             :when (and (pos? n)
                                        (not= g c)
                                        (not (contains? gold-named c)))]
                         [g c n]))]
    (first (reduce (fn [[m used] [g c _]]
                     (if (or (used g) (used c) (contains? m c))
                       [m used]
                       [(assoc m c g) (conj used g c)]))
                   [{} #{}]
                   pairs))))

(defn rename
  "`sentence` with every symbol `m` maps replaced, at any depth.  Goes through
  `vaelii.impl.sentex/canon` so the result is the shape the store keys on: a lazy seq, a
  `PersistentList` and a vector are all `=` and freeze to *different* bytes, so a renamed
  sentence built out of lazy seqs would miss a `handle-of` match that is really there."
  [m sentence]
  (sx/canon (if (sequential? sentence)
              (map #(rename m %) sentence)
              (get m sentence sentence))))

;; ---- matching -----------------------------------------------------------

(defn- handle-in
  "The handle storing `sentence` in `context`, or nil.  `handle-of` finds without creating,
  and a candidate is arbitrary text's output — so a sentence too malformed to look up simply
  does not match."
  [kb context sentence]
  ;; `Throwable`, not `Exception`: canonicalizing recurses a level per level of nesting,
  ;; so a candidate a few hundred deep — well inside what the reader that produced it
  ;; reads without complaint — overflows the stack, and an `Exception` catch lets that
  ;; `StackOverflowError` out of a lookup whose whole answer for a sentence it cannot key
  ;; on is nil, killing the scoring run instead.
  (try (v/handle-of kb sentence context)
       (catch Throwable _ nil)))

(defn- counts
  "Precision, recall and F1 from three counts.  `derivable` comes **out of precision's
  denominator**: a candidate restating something the KB already derives is not a wrong
  answer, it is a no-op re-assert, and scoring it either way would be a claim this
  arithmetic has no basis for."
  [matched n-gold n-cand derivable]
  (let [judged (- n-cand derivable)
        p (if (pos? judged) (/ (double matched) judged) 0.0)
        r (if (pos? n-gold) (/ (double matched) n-gold) 0.0)]
    {:matched matched
     :candidates n-cand
     :derivable derivable
     :gold n-gold
     :precision p
     :recall r
     :f1 (if (pos? (+ p r)) (/ (* 2 p r) (+ p r)) 0.0)}))

(defn score
  "Score `sentences` — a candidate set, all filed in `context` — against the hand-written
  sentexes in that context.

      {:strict  {:matched 3 :candidates 11 :derivable 1 :gold 6 :precision .3 :recall .5 :f1 .38}
       :aligned {:matched 5 …}
       :renaming {Lion1 LionA, Mouse1 MouseA}
       :missing [(repaidKindness …) …]        gold nobody produced, as readable sentences
       :spurious [(hunter Hunter1) …]         produced, matching nothing stored}

  `:missing` and `:spurious` are the aligned pass's, since those are the confusions worth a
  reader's time: the strict pass's misses are dominated by the naming of characters, which
  is a fact about the convention and not about the reading.  Both are sorted by their
  printed form, so a report is a function of the score and not of arrival order.

  A duplicate candidate matching an already-matched handle counts **once**: recall counts
  gold covered, so writing the same sentence twice cannot buy a second match."
  [kb context sentences]
  (let [gold      (gold-handles kb context)
        derived   (derived-handles kb context)
        gold-sent (map #(v/readable-sentence (v/sentex kb %)) gold)
        cands     (vec (distinct sentences))
        renaming  (alignment gold-sent cands)
        pass      (fn [ss]
                    (let [hits (into {} (for [s ss :let [h (handle-in kb context s)] :when h]
                                          [s h]))]
                      {:hits hits
                       :gold-hit (set (filter gold (vals hits)))
                       :derivable (count (filter derived (vals hits)))}))
        strict    (pass cands)
        renamed   (mapv #(if (seq renaming) (rename renaming %) %) cands)
        aligned   (pass renamed)]
    {:strict   (counts (count (:gold-hit strict)) (count gold) (count cands)
                       (:derivable strict))
     :aligned  (counts (count (:gold-hit aligned)) (count gold) (count cands)
                       (:derivable aligned))
     :renaming renaming
     :missing  (vec (sort-by pr-str (for [h gold :when (not ((:gold-hit aligned) h))]
                                      (v/readable-sentence (v/sentex kb h)))))
     ;; `distinct` after the renaming, not before it: two candidates that named one
     ;; character two ways collapse to one sentence once they are aligned, and reporting
     ;; the same spurious claim twice would read as two mistakes.
     :spurious (vec (sort-by pr-str (distinct (remove #(get (:hits aligned) %) renamed))))}))

;; ---- reporting ----------------------------------------------------------

(defn- pct [x] (format "%.0f%%" (* 100.0 (double x))))

(defn line
  "One scored document as a table row — `name`, then the aligned pass's numbers with the
  strict ones beside them, because the gap between the two *is* the finding."
  [name {:keys [strict aligned]}]
  (format "| %-22s | %2d | %2d | %5s | %5s | %5s | %5s |"
          (str name) (:gold aligned) (:candidates aligned)
          (pct (:precision aligned)) (pct (:recall aligned))
          (pct (:precision strict)) (pct (:recall strict))))

(defn table
  "Several scored documents — `[[name score] …]` — as a markdown table, with a total row.
  The total is computed from the summed counts rather than by averaging the rates, so a
  short document cannot weigh as much as a long one."
  [scored]
  (let [sum (fn [k f] (reduce + (map (comp f k second) scored)))
        tot (fn [k] (counts (sum k :matched) (sum k :gold) (sum k :candidates)
                            (sum k :derivable)))]
    (str/join
     "\n"
     (concat
      ["| document | gold | cand | prec | rec | strict prec | strict rec |"
       "|---|---|---|---|---|---|---|"]
      (for [[nm s] scored] (line nm s))
      [(line "**all four**" {:strict (tot :strict) :aligned (tot :aligned)})]))))
