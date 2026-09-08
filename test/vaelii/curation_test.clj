;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.curation-test
  "KB-curation vocabulary.

  Two families, both declared in CxCore beside `comment`:

    * cross-reference — `seeAlso`, a directional binary predicate relating two terms,
      alongside `termsRelated`, a symmetric variable-arity grouping for a reader.
    * in-KB worked examples — `positiveExample` / `negativeExample` / `borderlineExample`,
      meta-sentexes that name an example sentex by handle, the same
      `(sentexHandle H)` + `target_following_predicate` pointing pattern koinii's reply acts
      use (`target_following_meta_test`, `koinii_speech_acts_test`).

  The required check is the examples' integrity: every `positiveExample` names a
  sentex the KB can prove, and every `negativeExample` names one whose negation it can
  prove — so a card that states a verdict the ontology no longer gives turns a test red.
  `borderlineExample` is truth-agnostic and carries no such obligation."
  (:require [clojure.test :refer [is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (core-context/load-into))))

;; ---- Piece 1: seeAlso, a directional cross-reference ----------------------

(tu/deftest-kb cross-reference-vocab-is-documented
  (doseq [term '[seeAlso termsRelated]]
    (is (= 1 (count (core-context/comment-of kb term))) (str "comment for " term))
    (is (string? (first (core-context/comment-of kb term))))))

(tu/deftest-kb see-also-is-a-directional-binary-predicate
  (is (v/ask? kb '(binary_predicate seeAlso) 'CxCore) "seeAlso is a binary predicate")
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
;; Meta-sentexes naming an example sentex by handle (sx/sentex-handle), the same
;; pointing pattern koinii's reply acts use.  positiveExample names a provable sentex;
;; negativeExample names one whose negation is provable; borderlineExample is
;; truth-agnostic and carries no such obligation.

(defn- scratch
  "A context below CxUniverse (which sees CxCore in a core-only KB), taken away by the
  neutral fixture."
  [kb]
  (let [c (tu/fresh-term :context :Curation)]
    (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse)
    c))

;; ---- the vocabulary loads and carries the pointing mark -------------------

(tu/deftest-kb example-vocab-is-documented-and-target-following
  (doseq [term '[positiveExample negativeExample borderlineExample]]
    (is (= 1 (count (core-context/comment-of kb term))) (str "comment for " term))
    (is (v/ask? kb (list 'binary_predicate term) 'CxCore) (str term " is binary"))
    (is (v/has-prop? kb :target-following term)
        (str term " names its target sentex by handle and does not outlive it"))))

(tu/deftest-kb the-example-family-is-grouped-by-termsRelated
  (is (seq (v/sentexes-matching
            kb '(termsRelated positiveExample negativeExample borderlineExample) 'CxCore))
      "the three example predicates are asserted one termsRelated family in CxCore"))

;; ---- a positive example names a provable sentex --------------------------

(tu/deftest-kb a-positive-example-names-a-sentex-the-kb-proves
  (let [ctx (scratch kb)]
    (tu/with-terms [parentOf Abe Homer]
      (let [p (v/assert kb (list parentOf Abe Homer) ctx)]
        (v/assert kb (list 'positiveExample parentOf (sx/sentex-handle p)) ctx)
        (is (v/ask? kb (list parentOf Abe Homer) ctx)
            "the named sentex holds, so it is a true example of parentOf")))))

;; ---- a negative example names a sentex whose negation the KB proves -------

(tu/deftest-kb a-negative-example-names-a-sentex-whose-negation-the-kb-proves
  (let [ctx (scratch kb)]
    (tu/with-terms [parentOf Abe Homer]
      ;; the false-direction sentence is stored (default) and then defeated by the
      ;; monotonic negation, so it keeps a handle to name while (not C) is what holds.
      (let [c (list parentOf Homer Abe)
            neg (v/assert kb c ctx {:strength :default})]
        (v/assert kb (list 'not c) ctx {:strength :monotonic})
        (v/assert kb (list 'negativeExample parentOf (sx/sentex-handle neg)) ctx)
        (is (some? (v/sentex kb neg)) "the named sentex is stored, so its handle resolves")
        (is (not (v/ask? kb c ctx)) "it does not hold — a false example")
        (is (v/ask? kb (list 'not c) ctx) "and its negation is what the KB proves")))))

;; ---- the KB-integrity sweep: every asserted example checks out -----------

(defn- handle-content
  "The stored content of the sentex a `(pred term (sentexHandle H))` meta names."
  [kb sentex]
  (let [target (sx/handle-id (nth (:sentence sentex) 2))]
    (:sentence (v/sentex kb target))))

(defn- examples-of
  "Every *believed* `pred` meta-sentex in the KB, wherever it lives — asserted or deduced,
  and excepted ones excluded, because `sentexes-matching` returns believed sentexes."
  [kb pred]
  (v/sentexes-matching kb (list pred '?term '?h) '?ctx))

(tu/deftest-kb every-believed-example-holds-as-stated
  ;; The generative gate, data-driven over whatever examples the KB *believes* — asserted
  ;; OR deduced, with excepted ones excluded, because `examples-of` reads believed sentexes.
  ;; A positive example's target is provable, a negative example's target is provable as
  ;; its negation.  borderlineExample is deliberately NOT swept — it is truth-agnostic.
  (let [ctx (scratch kb)]
    (tu/with-terms [parentOf Abe Homer sibling Bea]
      ;; a positive example
      (let [p (v/assert kb (list parentOf Abe Homer) ctx)]
        (v/assert kb (list 'positiveExample parentOf (sx/sentex-handle p)) ctx))
      ;; a second positive example on a different predicate
      (let [s (v/assert kb (list sibling Homer Bea) ctx)]
        (v/assert kb (list 'positiveExample sibling (sx/sentex-handle s)) ctx))
      ;; a negative example (stored-then-defeated)
      (let [c (list parentOf Homer Abe)
            neg (v/assert kb c ctx {:strength :default})]
        (v/assert kb (list 'not c) ctx {:strength :monotonic})
        (v/assert kb (list 'negativeExample parentOf (sx/sentex-handle neg)) ctx))
      ;; a borderlineExample pointing at a sentex with no provability guarantee — it must
      ;; be ignored by the sweep, not fail it
      (let [c (list parentOf Bea Abe)
            b (v/assert kb c ctx {:strength :default})]
        (v/assert kb (list 'not c) ctx {:strength :monotonic})       ; b is in fact defeated
        (v/assert kb (list 'borderlineExample parentOf (sx/sentex-handle b)) ctx))

      (let [pos (examples-of kb 'positiveExample)
            neg (examples-of kb 'negativeExample)]
        (is (= 2 (count pos)) "the sweep found both positive examples")
        (is (= 1 (count neg)) "and the negative one")
        (doseq [e pos]
          (is (v/ask? kb (handle-content kb e) ctx)
              (str "positive example must prove its target: " (pr-str (:sentence e)))))
        (doseq [e neg]
          (is (v/ask? kb (list 'not (handle-content kb e)) ctx)
              (str "negative example must prove its target's negation: "
                   (pr-str (:sentence e)))))))))

;; ---- believed, not merely asserted: deduced in, excepted out -------------

(tu/deftest-kb a-deduced-example-meta-is-swept
  ;; An example meta the KB *derives* (never directly asserted) is believed, so the sweep
  ;; sees and checks it.  This is why the terminology is "believed", not "asserted".
  (let [ctx (scratch kb)]
    (tu/with-terms [parentOf Abe Homer marks_example]
      (v/assert kb (list 'unary_predicate marks_example) 'CxUniverse)
      (let [p (v/assert kb (list parentOf Abe Homer) ctx)
            h (sx/sentex-handle p)]
        ;; a rule concluding the positiveExample meta from a trigger — the meta is DEDUCED
        (v/assert kb (list 'implies (list 'marks_example '?t)
                           (list 'positiveExample '?t h)) ctx)
        (v/assert kb (list 'marks_example parentOf) ctx)
        (let [found (examples-of kb 'positiveExample)]
          (is (= 1 (count found)) "the deduced example meta is believed and swept")
          (doseq [e found]
            (is (v/ask? kb (handle-content kb e) ctx)
                "and its target proves, exactly as an asserted example's would")))))))

(tu/deftest-kb a-negated-example-meta-is-not-swept
  ;; A negated example meta — one whose negation is what the KB believes — is not itself
  ;; believed, so the sweep must not see it.  The "excepted examples should not be
  ;; checked" half, realized by asserting the meta's negation.
  (let [ctx (scratch kb)]
    (tu/with-terms [parentOf Abe Homer]
      (let [p    (v/assert kb (list parentOf Abe Homer) ctx)
            meta (list 'positiveExample parentOf (sx/sentex-handle p))]
        (v/assert kb meta ctx {:strength :default})
        (is (= 1 (count (examples-of kb 'positiveExample))) "believed while unnegated")
        (v/assert kb (list 'not meta) ctx {:strength :monotonic})   ; negate the meta itself
        (is (empty? (examples-of kb 'positiveExample))
            "a negated example meta is not believed, so the sweep skips it")))))

(tu/deftest-kb an-excepted-example-meta-is-not-swept
  ;; An example meta defeated by an (except (sentexHandle H)) — the targeted except
  ;; machinery, NOT a (not …) assertion — is not believed, so the sweep skips it.
  ;; (except P) is not (not P): the except retracts the meta's own support rather than
  ;; asserting a contrary proposition.
  (let [ctx (scratch kb)]
    (tu/with-terms [parentOf Abe Homer]
      (let [p  (v/assert kb (list parentOf Abe Homer) ctx)
            mh (v/assert kb (list 'positiveExample parentOf (sx/sentex-handle p)) ctx)]
        (is (= 1 (count (examples-of kb 'positiveExample))) "believed before the except")
        (v/assert kb (list 'except (sx/sentex-handle mh)) ctx {:strength :monotonic})
        (is (empty? (examples-of kb 'positiveExample))
            "an excepted example meta is not believed, so the sweep skips it")))))

;; ---- kb-has-integrity: the umbrella the scope card checks against ---------

(tu/deftest-kb kb-has-integrity
  ;; The KB-integrity umbrella.  Examples retain their independent oracle above; the
  ;; public sweep composes the declared-population audit with the bounded query-only
  ;; definition check.  These are known ground candidates exercised by CxCore's numeric
  ;; definitions, not a request for the query engine to enumerate a domain.
  (every-believed-example-holds-as-stated)
  (let [report (v/kb-integrity kb #{-212 0 212} 'CxUniverse)]
    (is (= :audited (:status report)) (pr-str report))
    (is (= 3 (:candidate-count report)))))

;; ---- borderline carries no obligation ------------------------------------

(tu/deftest-kb a-borderline-example-is-truth-agnostic
  ;; It names a sentex that is neither believed true nor its negation proven, and nothing
  ;; refuses it — no regression reads its target.
  (let [ctx (scratch kb)]
    (tu/with-terms [likes Cara Dora]
      (let [c (list likes Cara Dora)
            h (v/assert kb c ctx {:strength :default})]
        (v/assert kb (list 'borderlineExample likes (sx/sentex-handle h)) ctx)
        (is (seq (v/sentexes-matching
                  kb (list 'borderlineExample likes (sx/sentex-handle h)) ctx))
            "the borderline annotation is stored, whatever the truth of its target")))))

;; ---- the pointing pattern cascades: retract the target, the example goes -

(tu/deftest-kb an-example-does-not-outlive-the-sentex-it-names
  (let [ctx (scratch kb)]
    (tu/with-terms [parentOf Abe Homer]
      (let [p (v/assert kb (list parentOf Abe Homer) ctx)
            e (v/assert kb (list 'positiveExample parentOf (sx/sentex-handle p)) ctx)]
        (is (some? (v/sentex kb e)))
        (v/retract! kb p)
        (is (nil? (v/sentex kb p)) "the example sentex is gone")
        (is (nil? (v/sentex kb e))
            "and the positiveExample naming it cascaded — target_following_predicate")))))
