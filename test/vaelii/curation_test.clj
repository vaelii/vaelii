;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.curation-test
  "KB-curation vocabulary.

  Two families, both declared in CxUniverse beside `comment`:

    * cross-reference — `seeAlso`, a directional binary predicate relating two terms,
      alongside `termsRelated`, a symmetric variable-arity grouping for a reader.
    * in-KB worked examples — `positiveExample` / `negativeExample` / `borderlineExample`,
      whose second argument is a quoted sentence, `(positiveExample ip_address (Quote
      (ip_address \"192.0.2.1\")))`.  The example names no sentex, so none of the three is
      `target_following_predicate`.

  The required check is the examples' integrity, read in each example's own context:
  every believed `positiveExample` quotes a closed sentence the KB proves, and every
  believed `negativeExample` one it does not prove (unknown is enough) — so an example
  that states a verdict the ontology no longer gives turns a test red.
  `borderlineExample` is truth-agnostic and is not checked."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (tu/load-core!))))

;; ---- Piece 1: seeAlso, a directional cross-reference ----------------------

(tu/deftest-kb cross-reference-vocab-is-documented
  (doseq [term '[seeAlso termsRelated]]
    (is (= 1 (count (core-context/comment-of kb term))) (str "comment for " term))
    (is (string? (first (core-context/comment-of kb term))))))

(tu/deftest-kb see-also-is-a-directional-binary-predicate
  (is (v/ask? kb '(binary_predicate seeAlso) 'CxUniverse) "seeAlso is a binary predicate")
  (is (not (v/has-prop? kb :symmetric 'seeAlso))
      "and NOT symmetric — a 'see also' points one way; the reverse is a separate assertion"))

(tu/deftest-kb see-also-relates-two-terms-directionally
  (tu/with-terms [parentOf childOf]
    (v/assert kb (list 'seeAlso parentOf childOf) 'CxUniverse)
    (is (v/ask? kb (list 'seeAlso parentOf childOf) 'CxUniverse)
        "the asserted direction is retrievable")
    (is (not (v/ask? kb (list 'seeAlso childOf parentOf) 'CxUniverse))
        "and the converse is NOT implied — seeAlso is directional, unlike a symmetric relation")))

;; ---- Piece 2: positiveExample / negativeExample / borderlineExample -------
;; The second argument is a quoted sentence, (Quote S).  positiveExample's S is provable
;; in the example's context; negativeExample's S is not; borderlineExample's S is not
;; read.  `example-violations` is the check, and the tests below run it over small
;; fixtures and over the shipped starter KB.

(defn- scratch
  "A context below CxUniverse, taken away by the neutral fixture."
  [kb]
  (let [c (tu/fresh-term :context :Curation)]
    (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse)
    c))

(defn- quote-of
  "`(Quote s)`, the second argument of an example about `s`."
  [s]
  (list 'Quote s))

(defn- quoted-sentence
  "The sentence an example's second argument `q` quotes: S of a `(Quote S)` written there,
  or of the `(Quote S)` that a reified constant stands for in a KB that declares `Quote`
  reifiable.  nil when `q` quotes nothing."
  [kb q]
  (let [form (if (nat-read/reified-nat-symbol? q) (nat/nat-expression kb q) q)]
    (when (sx/quote-form? form) (second form))))

(defn- examples-of
  "Every *believed* `pred` sentex in the KB, wherever it lives — asserted or deduced, and
  excepted ones excluded, because `sentexes-matching` returns believed sentexes.  Given
  `ctx`, only those stated in `ctx`: the fixture's own, apart from the shipped ones."
  ([kb pred]
   (v/sentexes-matching kb (list pred '?term '?q) '?ctx))
  ([kb pred ctx]
   (filterv #(= ctx (:context %)) (examples-of kb pred))))

(defn- example-problem
  "Why the believed example `e` of `pred` fails its obligation, or nil when it holds.  The
  quoted sentence is asked in `e`'s own context."
  [kb pred e]
  (let [s (quoted-sentence kb (nth (:sentence e) 2))]
    (cond
      (nil? s)                             :quotes-no-sentence
      (seq (sx/unquoted-free-vars s))      :quotes-an-open-sentence
      (= 'borderlineExample pred)          nil
      (= 'positiveExample pred)            (when-not (true? (v/ask? kb s (:context e))) :not-provable)
      (= 'negativeExample pred)            (when (true? (v/ask? kb s (:context e))) :provable))))

(defn- example-violations
  "Every believed example in `kb` that fails its obligation, as `[problem sentence
  context]`.  A `positiveExample` must quote a closed sentence the KB proves, a
  `negativeExample` a closed sentence it does not prove, and a `borderlineExample` a
  closed sentence whatever its truth.  Given `ctx`, only the examples stated in `ctx`."
  ([kb]
   (vec (for [pred '[positiveExample negativeExample borderlineExample]
              e    (examples-of kb pred)
              :let [problem (example-problem kb pred e)]
              :when problem]
          [problem (:sentence e) (:context e)])))
  ([kb ctx]
   (filterv #(= ctx (nth % 2)) (example-violations kb))))

;; ---- the vocabulary loads and names no target ------------------------------

(tu/deftest-kb example-vocab-is-documented-and-names-no-target
  (doseq [term '[positiveExample negativeExample borderlineExample]]
    (is (= 1 (count (core-context/comment-of kb term))) (str "comment for " term))
    (is (v/ask? kb (list 'binary_predicate term) 'CxUniverse) (str term " is binary"))
    (is (not (v/has-prop? kb :target-following term))
        (str term " quotes its example sentence and names no sentex, so it has no target"))))

(tu/deftest-kb the-example-family-is-grouped-by-termsRelated
  (is (seq (v/sentexes-matching
            kb '(termsRelated positiveExample negativeExample borderlineExample) 'CxUniverse))
      "the three example predicates are asserted one termsRelated family in CxUniverse"))

;; ---- the string siblings: an example carried as text ----------------------

(tu/deftest-kb the-string-example-siblings-are-documented-and-name-no-target
  (doseq [term '[positiveExampleComment negativeExampleComment borderlineExampleComment]]
    (is (= 1 (count (core-context/comment-of kb term))) (str "comment for " term))
    (is (v/ask? kb (list 'binary_predicate term) 'CxUniverse) (str term " is binary"))
    (is (v/ask? kb (list 'arg term 2 'string) 'CxUniverse) (str term " takes its text as a string"))
    (is (not (v/has-prop? kb :target-following term))
        (str term " names no sentex, so it has no target to follow"))))

(tu/deftest-kb each-example-predicate-is-related-to-its-string-sibling
  ;; A star of pairs, each example predicate to its string sibling, beside the two
  ;; triangles: the three example predicates and the three string siblings.
  (doseq [form '[(termsRelated positiveExample positiveExampleComment)
                 (termsRelated negativeExample negativeExampleComment)
                 (termsRelated borderlineExample borderlineExampleComment)
                 (termsRelated positiveExample negativeExample borderlineExample)
                 (termsRelated positiveExampleComment negativeExampleComment
                               borderlineExampleComment)]]
    (is (= 1 (count (v/sentexes-matching kb form 'CxUniverse))) (pr-str form))))

(tu/deftest-kb a-string-example-is-stored-and-believed-whatever-its-text
  ;; Nothing checks the text against the KB, so a string example of a term is stored and
  ;; believed whatever it says.
  (let [ctx (scratch kb)]
    (tu/with-terms [gadget]
      (doseq [[p text] [['positiveExampleComment "a pocket calculator"]
                        ['negativeExampleComment "a pebble"]
                        ['borderlineExampleComment "a calculator with a dead battery"]]]
        (v/assert kb (list p gadget text) ctx)
        (is (true? (v/ask? kb (list p gadget text) ctx)) (str p " is believed"))))))

;; ---- positiveExample: the quoted sentence is provable ----------------------

(tu/deftest-kb a-positive-example-quotes-a-sentence-the-kb-proves
  (let [ctx (scratch kb)]
    (tu/with-terms [parentOf Abe Homer]
      (let [s (list parentOf Abe Homer)]
        (v/assert kb s ctx)
        (v/assert kb (list 'positiveExample parentOf (quote-of s)) ctx)
        (is (= [(quote-of s)] (map #(nth (:sentence %) 2) (examples-of kb 'positiveExample ctx)))
            "the example is stored with its quoted sentence as written")
        (is (empty? (example-violations kb ctx)) "the quoted sentence holds, so the example does")))))

(tu/deftest-kb a-positive-example-the-kb-does-not-prove-fails-the-check
  (let [ctx (scratch kb)]
    (tu/with-terms [parentOf Abe Homer]
      (v/assert kb (list parentOf Abe Homer) ctx)
      (let [wrong (list parentOf Homer Abe)]
        (v/assert kb (list 'positiveExample parentOf (quote-of wrong)) ctx)
        (is (= [[:not-provable (list 'positiveExample parentOf (quote-of wrong)) ctx]]
               (example-violations kb ctx))
            "a positive example whose sentence the KB does not prove is reported")))))

(tu/deftest-kb a-positive-example-is-checked-in-its-own-context
  ;; The sentence holds in a context the example's context does not see, so it is not
  ;; provable where the example is stated.
  (let [ctx   (scratch kb)
        other (scratch kb)]
    (tu/with-terms [parentOf Abe Homer]
      (let [s (list parentOf Abe Homer)]
        (v/assert kb s other)
        (v/assert kb (list 'positiveExample parentOf (quote-of s)) ctx)
        (is (= [:not-provable] (map first (example-violations kb ctx))))))))

;; ---- negativeExample: the quoted sentence is not provable ------------------

(tu/deftest-kb a-negative-example-quotes-a-sentence-the-kb-does-not-prove
  (let [ctx (scratch kb)]
    (tu/with-terms [parentOf Abe Homer Bea]
      (v/assert kb (list parentOf Abe Homer) ctx)
      ;; unknown is enough: nothing is stated about Homer and Abe's other direction
      (v/assert kb (list 'negativeExample parentOf (quote-of (list parentOf Homer Abe))) ctx)
      ;; and a sentence whose negation the KB proves is not provable either
      (v/assert kb (list 'not (list parentOf Bea Abe)) ctx {:strength :monotonic})
      (v/assert kb (list 'negativeExample parentOf (quote-of (list parentOf Bea Abe))) ctx)
      (is (= 2 (count (examples-of kb 'negativeExample ctx))))
      (is (empty? (example-violations kb ctx))
          "neither quoted sentence is provable, so both negative examples hold"))))

(tu/deftest-kb a-negative-example-the-kb-proves-fails-the-check
  (let [ctx (scratch kb)]
    (tu/with-terms [parentOf Abe Homer]
      (let [s (list parentOf Abe Homer)]
        (v/assert kb s ctx)
        (v/assert kb (list 'negativeExample parentOf (quote-of s)) ctx)
        (is (= [[:provable (list 'negativeExample parentOf (quote-of s)) ctx]]
               (example-violations kb ctx))
            "a negative example whose sentence the KB proves is reported")))))

;; ---- borderlineExample: unchecked ------------------------------------------

(tu/deftest-kb a-borderline-example-is-not-checked
  ;; One quoted sentence the KB proves and one it does not: neither is reported.
  (let [ctx (scratch kb)]
    (tu/with-terms [likes Cara Dora]
      (v/assert kb (list likes Cara Dora) ctx)
      (v/assert kb (list 'borderlineExample likes (quote-of (list likes Cara Dora))) ctx)
      (v/assert kb (list 'borderlineExample likes (quote-of (list likes Dora Cara))) ctx)
      (is (= 2 (count (examples-of kb 'borderlineExample ctx))))
      (is (empty? (example-violations kb ctx)) "the truth of a borderline example is not read"))))

;; ---- the second argument must quote a closed sentence ----------------------

(tu/deftest-kb an-example-that-quotes-no-sentence-fails-the-check
  (let [ctx (scratch kb)]
    (tu/with-terms [parentOf Abe]
      (v/assert kb (list 'borderlineExample parentOf Abe) ctx)
      (is (= [:quotes-no-sentence] (map first (example-violations kb ctx)))
          "a bare term in the second position is reported, even for borderlineExample"))))

(tu/deftest-kb an-example-that-quotes-an-open-sentence-fails-the-check
  ;; Asked, the open sentence would be a query, answered by any one binding.
  (let [ctx (scratch kb)]
    (tu/with-terms [parentOf Abe Homer]
      (v/assert kb (list parentOf Abe Homer) ctx)
      (v/assert kb (list 'positiveExample parentOf (quote-of (list parentOf Abe '?child))) ctx)
      (is (= [:quotes-an-open-sentence] (map first (example-violations kb ctx)))))))

;; ---- believed, not merely asserted: deduced in, excepted out -------------

(tu/deftest-kb a-deduced-example-is-checked
  ;; An example the KB *derives* is believed, so the check reads it.
  (let [ctx (scratch kb)]
    (tu/with-terms [parentOf Abe Homer marks_example]
      (v/assert kb (list 'unary_predicate marks_example) 'CxUniverse)
      (v/assert kb (list parentOf Abe Homer) ctx)
      (v/assert kb (list 'implies (list marks_example '?t)
                         (list 'positiveExample '?t (quote-of (list parentOf Homer Abe))))
                ctx {:direction :forward})
      (v/assert kb (list marks_example parentOf) ctx)
      (is (= 1 (count (examples-of kb 'positiveExample ctx))) "the deduced example is believed")
      (is (= [:not-provable] (map first (example-violations kb ctx)))
          "and checked like an asserted one"))))

(tu/deftest-kb a-negated-example-is-not-checked
  ;; An example whose negation the KB believes is not itself believed, so the check skips
  ;; it.
  (let [ctx (scratch kb)]
    (tu/with-terms [parentOf Abe Homer]
      (let [e (list 'positiveExample parentOf (quote-of (list parentOf Homer Abe)))]
        (v/assert kb e ctx {:strength :default})
        (is (= 1 (count (example-violations kb ctx))) "checked while believed")
        (v/assert kb (list 'not e) ctx {:strength :monotonic})
        (is (empty? (example-violations kb ctx)) "not believed once negated, so not checked")))))

(tu/deftest-kb an-excepted-example-is-not-checked
  ;; An example an (except (sentexHandle H)) hides is not believed, so the check skips it.
  (let [ctx (scratch kb)]
    (tu/with-terms [parentOf Abe Homer]
      (let [h (v/assert kb (list 'positiveExample parentOf (quote-of (list parentOf Homer Abe)))
                        ctx)]
        (is (= 1 (count (example-violations kb ctx))) "checked before the except")
        (v/assert kb (list 'except (sx/sentex-handle h)) ctx {:strength :monotonic})
        (is (empty? (example-violations kb ctx)) "not believed once excepted, so not checked")))))

;; ---- the example names no sentex, so nothing tears it down -----------------

(tu/deftest-kb an-example-outlives-the-sentence-it-quotes-and-the-check-reports-it
  ;; Retracting the sentence leaves the example stored, quoting a sentence the KB no
  ;; longer proves: the check, not a teardown, catches it.
  (let [ctx (scratch kb)]
    (tu/with-terms [parentOf Abe Homer]
      (let [s (list parentOf Abe Homer)
            p (v/assert kb s ctx)
            e (v/assert kb (list 'positiveExample parentOf (quote-of s)) ctx)]
        (is (empty? (example-violations kb ctx)))
        (v/retract! kb p)
        (is (some? (v/sentex kb e)) "the example is still stored")
        (is (= [:not-provable] (map first (example-violations kb ctx)))
            "and the check reports that its sentence no longer holds")))))

;; ---- a KB that reifies Quote ------------------------------------------------

(tu/deftest-kb a-reified-quoted-sentence-is-read-back-through-its-constant
  ;; Where Quote is declared reifiable, the stored example holds a constant whose
  ;; natFormula is the (Quote S) form, and the check reads S from it.
  (let [ctx (scratch kb)]
    (tu/with-terms [parentOf Abe Homer]
      (v/assert kb '(reifiable_function Quote) 'CxUniverse)
      (v/assert kb (list parentOf Abe Homer) ctx)
      (v/assert kb (list 'positiveExample parentOf (quote-of (list parentOf Abe Homer))) ctx)
      (v/assert kb (list 'positiveExample parentOf (quote-of (list parentOf Homer Abe))) ctx)
      (is (every? #(nat-read/reified-nat-symbol? (nth (:sentence %) 2))
                  (examples-of kb 'positiveExample ctx))
          "both quoted sentences are reified")
      (is (= [:not-provable] (map first (example-violations kb ctx)))
          "the provable one holds and the other is reported"))))

;; ---- the KB-integrity sweep over a fixture of every kind -------------------

(tu/deftest-kb every-believed-example-holds-as-stated
  ;; This test is a generative check over whatever examples the KB believes.
  (let [ctx (scratch kb)]
    (tu/with-terms [parentOf Abe Homer sibling Bea]
      (v/assert kb (list parentOf Abe Homer) ctx)
      (v/assert kb (list sibling Homer Bea) ctx)
      (v/assert kb (list 'positiveExample parentOf (quote-of (list parentOf Abe Homer))) ctx)
      (v/assert kb (list 'positiveExample sibling (quote-of (list sibling Homer Bea))) ctx)
      (v/assert kb (list 'negativeExample parentOf (quote-of (list parentOf Homer Abe))) ctx)
      (v/assert kb (list 'borderlineExample parentOf (quote-of (list parentOf Bea Abe))) ctx)
      (is (= 2 (count (examples-of kb 'positiveExample ctx))) "the sweep found both positive examples")
      (is (= 1 (count (examples-of kb 'negativeExample ctx))) "and the negative one")
      (is (empty? (example-violations kb ctx)) (pr-str (example-violations kb ctx))))))

;; ---- the shipped examples -------------------------------------------------

(deftest the-shipped-examples-hold-as-stated
  ;; Every example the starter KB states, each asked in the context its file loads into.
  ;; The starter is built on the isolated space, since the fixture's KB holds the scratch
  ;; one.
  (let [kb (doto (tu/isolated-fresh) (tu/load-starter!))]
    (try
      (is (<= 31 (count (examples-of kb 'positiveExample)))
          "the starter states its formal positive examples")
      (is (<= 7 (count (examples-of kb 'negativeExample)))
          "and its formal negative examples")
      (is (empty? (example-violations kb)) (pr-str (example-violations kb)))
      (finally (tu/clear-kb! kb)))))

;; ---- kb-has-integrity: the umbrella the scope card checks against ---------

(tu/deftest-kb kb-has-integrity
  ;; The KB-integrity umbrella.  Examples retain their independent oracle above; the
  ;; public sweep composes the declared-population audit with the bounded query-only
  ;; definition check.  These are known ground candidates exercised by CxUniverse's numeric
  ;; definitions, not a request for the query engine to enumerate a domain.
  (every-believed-example-holds-as-stated)
  ;; Classifying every relation by rigidity_kind is open work, so the one finding is
  ;; core.txt's (typeAllSpecified rigidity_kind relation), and every other pass is clean.
  (let [report (v/kb-integrity kb #{-212 0 212} 'CxUniverse)]
    (is (= {:status :gap :candidate-count 3}
           (dissoc report :type-specified-violations))
        (pr-str (dissoc report :type-specified-violations)))
    (is (= ['[typeAllSpecified rigidity_kind relation]]
           (keys (:type-specified-violations report))))))
