;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.conceptual-work-test
  "The content, carrier and claim vocabulary of CxTra: `conceptual_work` below
  `information`, `carries` from a temporal carrier to the information it holds,
  `encodes` from one piece of information to another, `intangiblePartOf` and its spec
  `subInformationOf`, `agentClaims` from an agent to a sentex handle, and `dataContent` /
  `propositionalContent`, stated directly and never derived. `carries` admits both a
  tangible and an intangible carrier; nothing concludes `agentClaims` from `carries`, and
  nothing derives either content relation from an information's author, encoding or
  context. The red tests below each name the link a future derivation would need and show
  today's KB answers it unknown rather than with the fixture's intended answer."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private CPT 'CxTra)

(defn- holds-ask  [s ctx]         (boolean (v/ask? tu/*kb* s ctx)))
(defn- holds-genl [sub super ctx] (boolean (v/genl? tu/*kb* sub super ctx)))
(defn- holds-isa  [x t ctx]       (boolean (v/isa? tu/*kb* x t ctx)))
(defn- following? [p]             (boolean (v/has-prop? tu/*kb* :target-following p)))
(defn- bound-value
  "The value `v` binds to in `kb`'s answers to `goal` in `ctx`, or nil for no answer."
  [kb goal ctx v]
  (get (first (v/ask kb goal ctx)) v))

(defn- desk!
  "A fresh context below CxWell and CxTra, the way a user's context opts in."
  [ctx]
  (v/assert tu/*kb* (list 'genlCx ctx 'CxWell) 'CxUniverse)
  (v/assert tu/*kb* (list 'genlCx ctx CPT) 'CxUniverse)
  ctx)

(defn- claimed!
  "Store `sentence` in `story`, a context the desk does not see, so the desk can name the
  sentence by handle without believing the sentence.  Returns the handle term."
  [story sentence]
  (v/assert tu/*kb* (list 'genlCx story 'CxUniverse) 'CxUniverse)
  (sx/sentex-handle (v/assert tu/*kb* sentence story)))

(tu/deftest-kb the-kinds-and-relations-are-declared-in-the-theory
  (doseq [k '[conceptual_work]]
    (is (= 1 (count (v/sentexes-matching kb (list 'comment k '?c) CPT)))
        (str k " carries one comment in the theory"))
    (is (holds-genl k 'thing CPT) (str k " reaches thing from the theory")))
  (doseq [p '[carries encodes subInformationOf agentClaims dataContent propositionalContent]]
    (is (holds-ask (list 'binary_predicate p) CPT) (str p " is binary in the theory"))
    (is (= 1 (count (v/sentexes-matching kb (list 'comment p '?c) CPT)))
        (str p " carries one comment in the theory")))
  (testing "intangiblePartOf is declared in the upper ontology and seen from the theory"
    (is (holds-ask '(binary_predicate intangiblePartOf) CPT))
    (is (= 1 (count (v/sentexes-matching kb '(comment intangiblePartOf ?c) 'CxUniverse)))))
  (testing "a conceptual work is information, and information is the content, not the medium"
    (is (holds-genl 'conceptual_work 'information CPT))
    (is (holds-genl 'conceptual_work 'intangible CPT)))
  (testing "carries types a temporal carrier against the information it holds"
    (is (holds-ask '(arg carries 1 temporal) CPT))
    (is (holds-ask '(arg carries 2 information) CPT)))
  (testing "encodes relates one piece of information to another, never a carrier to its content"
    (is (holds-ask '(arg encodes 1 information) CPT))
    (is (holds-ask '(arg encodes 2 information) CPT)))
  (testing "intangiblePartOf specializes partOf and subInformationOf specializes it again"
    (is (holds-genl 'intangiblePartOf 'partOf CPT))
    (is (holds-genl 'subInformationOf 'intangiblePartOf CPT))
    (is (holds-genl 'subInformationOf 'partOf CPT))
    (is (holds-ask '(arg intangiblePartOf 1 intangible) CPT))
    (is (holds-ask '(arg subInformationOf 1 information) CPT)))
  (testing "agentClaims is typed and marked as the old claims relation was"
    (is (holds-ask '(arg agentClaims 1 thing) CPT))
    (is (holds-ask '(arg agentClaims 2 thing) CPT))
    (is (following? 'agentClaims)))
  (testing "dataContent is functional over a string; propositionalContent is not functional over a proposition"
    (is (holds-ask '(quotedArg dataContent 2 string) CPT))
    (is (v/has-prop? tu/*kb* :functional 'dataContent))
    (is (holds-ask '(arg propositionalContent 2 proposition) CPT))
    (is (not (v/has-prop? tu/*kb* :functional 'propositionalContent))))
  (testing "neither CxWell nor CxUniverse reads the vocabulary"
    (is (empty? (v/sentexes-matching kb (list 'comment 'conceptual_work '?c) 'CxUniverse)))))

;; ---- carries: a temporal carrier, tangible or intangible, holds information ----------

(tu/deftest-kb a-tangible-copy-and-an-intangible-chirp-both-carry-information
  (tu/with-terms [CxDesk Article PaperCopy Chirp]
    (desk! CxDesk)
    (tu/with-entailing
      (v/assert kb (list 'conceptual_work Article) CxDesk)
      (v/assert kb (list 'tangible PaperCopy) CxDesk)
      (v/assert kb (list 'event Chirp) CxDesk)
      (v/assert kb (list 'carries PaperCopy Article) CxDesk)
      (v/assert kb (list 'carries Chirp Article) CxDesk))
    (testing "both the tangible copy and the intangible chirp carry the work"
      (is (holds-ask (list 'carries PaperCopy Article) CxDesk))
      (is (holds-ask (list 'carries Chirp Article) CxDesk)))
    (testing "carrying fixes nothing about the carrier's mass"
      (is (holds-isa PaperCopy 'tangible CxDesk))
      (is (holds-isa Chirp 'intangible CxDesk)))
    (testing "no clash is reported over the two carriers of one work"
      (is (empty? (filter #(some #{Article PaperCopy Chirp} (flatten (map :sentence (:sides %))))
                          (concat (v/contradictions kb) (v/conflicts kb))))))))

(tu/deftest-kb destroying-a-carrier-does-not-destroy-what-it-carries
  (tu/with-terms [CxDesk Article PaperCopy Burning]
    (desk! CxDesk)
    (tu/with-entailing
      (v/assert kb (list 'conceptual_work Article) CxDesk)
      (v/assert kb (list 'tangible PaperCopy) CxDesk)
      (v/assert kb (list 'carries PaperCopy Article) CxDesk)
      (v/assert kb (list 'event Burning) CxDesk)
      (v/assert kb (list 'destroyedInput Burning PaperCopy) CxDesk))
    (testing "the carrier's end is bounded by the burning"
      (is (holds-ask (list 'instantNotAfter (list 'EndFn PaperCopy) (list 'EndFn Burning)) CxDesk)))
    (testing "nothing concludes the work destroyed or bounds its end"
      (is (not (holds-ask (list 'destroyedInput Burning Article) CxDesk)))
      (is (not (holds-ask (list 'instantNotAfter (list 'EndFn Article) (list 'EndFn Burning)) CxDesk))))
    (testing "the carrier still carries the work"
      (is (holds-ask (list 'carries PaperCopy Article) CxDesk)))))

;; ---- encodes: information to information, never a carrier to its content -------------

(tu/deftest-kb encodes-relates-information-to-information-not-a-carrier-to-its-content
  (tu/with-terms [CxDesk Ciphertext Plaintext Disk]
    (desk! CxDesk)
    (tu/with-entailing
      (v/assert kb (list 'conceptual_work Plaintext) CxDesk)
      (v/assert kb (list 'conceptual_work Ciphertext) CxDesk)
      (v/assert kb (list 'encodes Ciphertext Plaintext) CxDesk)
      (v/assert kb (list 'tangible Disk) CxDesk)
      (v/assert kb (list 'carries Disk Ciphertext) CxDesk))
    (testing "the ciphertext encodes the plaintext"
      (is (holds-ask (list 'encodes Ciphertext Plaintext) CxDesk)))
    (testing "the disk carries the ciphertext, and nothing concludes it carries the plaintext"
      (is (holds-ask (list 'carries Disk Ciphertext) CxDesk))
      (is (not (holds-ask (list 'carries Disk Plaintext) CxDesk))))))

;; ---- intangiblePartOf and subInformationOf -------------------------------------------

(tu/deftest-kb subinformationof-reaches-partof-through-intangiblepartof
  (tu/with-terms [CxDesk Book Chapter]
    (desk! CxDesk)
    (tu/with-entailing
      (v/assert kb (list 'conceptual_work Book) CxDesk)
      (v/assert kb (list 'conceptual_work Chapter) CxDesk)
      (v/assert kb (list 'subInformationOf Chapter Book) CxDesk))
    (testing "the chapter is a part of the book through each spec in the chain"
      (is (holds-ask (list 'subInformationOf Chapter Book) CxDesk))
      (is (holds-ask (list 'intangiblePartOf Chapter Book) CxDesk))
      (is (holds-ask (list 'partOf Chapter Book) CxDesk))))
  (tu/with-terms [CxDesk2 Book Frontmatter Preface]
    (desk! CxDesk2)
    (tu/with-entailing
      (v/assert kb (list 'conceptual_work Book) CxDesk2)
      (v/assert kb (list 'conceptual_work Frontmatter) CxDesk2)
      (v/assert kb (list 'conceptual_work Preface) CxDesk2)
      (v/assert kb (list 'subInformationOf Preface Frontmatter) CxDesk2)
      (v/assert kb (list 'subInformationOf Frontmatter Book) CxDesk2))
    (testing "subInformationOf is transitive"
      (is (holds-ask (list 'subInformationOf Preface Book) CxDesk2)))))

(tu/deftest-kb a-mixed-tangible-and-intangible-part-pair-holds-neither-spec
  (tu/with-terms [CxDesk Soul Body]
    (desk! CxDesk)
    (tu/with-entailing
      (v/assert kb (list 'intangible Soul) CxDesk)
      (v/assert kb (list 'tangible Body) CxDesk)
      (v/assert kb (list 'partOf Soul Body) CxDesk))
    (testing "the mixed pair holds the general relation"
      (is (holds-ask (list 'partOf Soul Body) CxDesk)))
    (testing "neither spec is concluded, since their arg types do not admit this pair"
      (is (not (holds-ask (list 'intangiblePartOf Soul Body) CxDesk)))
      (is (not (holds-ask (list 'tangiblePartOf Soul Body) CxDesk))))))

;; ---- agentClaims: an agent presenting a sentex as true, independent of carries -------

(tu/deftest-kb carrying-does-not-by-itself-make-anything-agentclaims-it
  (tu/with-terms [CxDesk DnaMolecules DnaContent]
    (desk! CxDesk)
    (tu/with-entailing
      (v/assert kb (list 'tangible DnaMolecules) CxDesk)
      (v/assert kb (list 'carries DnaMolecules DnaContent) CxDesk))
    (testing "the molecules are a carrier and their content is information"
      (is (holds-ask (list 'carries DnaMolecules DnaContent) CxDesk))
      (is (holds-isa DnaContent 'information CxDesk)))
    (testing "no rule concludes agentClaims from carries, so neither claims anything"
      (doseq [x [DnaMolecules DnaContent]]
        (is (empty? (v/ask kb (list 'agentClaims x '?s) CxDesk)) (str x " claims nothing"))))))

;; ---- dataContent / propositionalContent: stated, never derived -----------------------

;; The green interpretation case: a message's own author states its propositional
;; content directly -- the content is supplied, not derived from the text, so no
;; fixture-assumed answer stands in for a missing link here.
(tu/deftest-kb author-declared-content-ingestion-states-its-own-propositional-content
  (tu/with-terms [CxDesk CxStory Msg Ann hungry]
    (desk! CxDesk)
    (let [h (claimed! CxStory (list hungry Ann))]
      (tu/with-entailing
        (v/assert kb (list 'digital_artifact Msg) CxDesk)
        (v/assert kb (list 'dataContent Msg "I am hungry.") CxDesk)
        (v/assert kb (list 'propositionalContent Msg (list hungry Ann)) CxDesk)
        (v/assert kb (list 'agentClaims Ann h) CxDesk))
      (testing "the author's declared data and propositional content both read back"
        (is (= "I am hungry." (bound-value kb (list 'dataContent Msg '?s) CxDesk '?s)))
        (is (holds-ask (list 'propositionalContent Msg (list hungry Ann)) CxDesk)))
      (testing "the author's claim is on record, and the desk does not believe it"
        (is (holds-ask (list 'agentClaims Ann h) CxDesk))
        (is (not (holds-ask (list hungry Ann) CxDesk)))))))

;; Test 1 (Iris): two files holding the same text share one data content.
(tu/deftest-kb two-files-with-the-same-text-share-data-content
  (tu/with-terms [CxDesk FileA FileB]
    (desk! CxDesk)
    (tu/with-entailing
      (v/assert kb (list 'digital_artifact FileA) CxDesk)
      (v/assert kb (list 'digital_artifact FileB) CxDesk)
      (v/assert kb (list 'dataContent FileA "The cat is black.") CxDesk)
      (v/assert kb (list 'dataContent FileB "The cat is black.") CxDesk))
    (testing "the two files' data content is equal, though the files are two things"
      (is (= "The cat is black." (bound-value kb (list 'dataContent FileA '?s) CxDesk '?s)))
      (is (= "The cat is black." (bound-value kb (list 'dataContent FileB '?s) CxDesk '?s)))
      (is (not= FileA FileB)))))

;; Test 2 (Iris; both sentences fix one referent): an English file and a French file about one
;; stipulated cat have different data content. No rule derives a shared propositional
;; content from a translation relationship vaelii does not represent, so the fixture
;; states only the data content each file holds, and the query below for the content a
;; translation-aware reading would derive comes back with no answer.
(tu/deftest-kb ^:red a-translation-shares-propositional-content-not-data-content
  (tu/with-terms [CxDesk FileEnglish FileFrench Cat1 catIsBlack]
    (desk! CxDesk)
    (tu/with-entailing
      (v/assert kb (list 'digital_artifact FileEnglish) CxDesk)
      (v/assert kb (list 'digital_artifact FileFrench) CxDesk)
      (v/assert kb (list 'dataContent FileEnglish "The cat is black.") CxDesk)
      (v/assert kb (list 'dataContent FileFrench "Le chat est noir.") CxDesk))
    (testing "the two files' data content differs, as the two sentences differ"
      (is (not= (bound-value kb (list 'dataContent FileEnglish '?s) CxDesk '?s)
                (bound-value kb (list 'dataContent FileFrench '?s) CxDesk '?s))))
    (testing "RED: nothing derives the one proposition both files state about Cat1"
      (is (and (holds-ask (list 'propositionalContent FileEnglish (list catIsBlack Cat1)) CxDesk)
               (holds-ask (list 'propositionalContent FileFrench (list catIsBlack Cat1)) CxDesk))
          "a translation-aware reading does not exist yet, so this fails until one is built"))))

;; Test 3 (Iris; chat messages per Iris): two messages with the same words from two
;; different speakers. The data content is supplied and equal; propositionalContent is
;; stated, never derived, so nothing in the KB resolves "I" to a speaker, and the query
;; for the two different propositions an indexical-aware reading would derive comes back
;; with no answer for either message.
(tu/deftest-kb ^:red the-same-words-from-two-speakers-diverge-in-propositional-content
  (tu/with-terms [CxDesk MsgFromAnn MsgFromBob Ann Bob hungry]
    (desk! CxDesk)
    (tu/with-entailing
      (v/assert kb (list 'digital_artifact MsgFromAnn) CxDesk)
      (v/assert kb (list 'digital_artifact MsgFromBob) CxDesk)
      (v/assert kb (list 'dataContent MsgFromAnn "I am hungry.") CxDesk)
      (v/assert kb (list 'dataContent MsgFromBob "I am hungry.") CxDesk))
    (testing "the two messages' data content is equal"
      (is (= (bound-value kb (list 'dataContent MsgFromAnn '?s) CxDesk '?s)
             (bound-value kb (list 'dataContent MsgFromBob '?s) CxDesk '?s))))
    (testing "RED: nothing derives which speaker the indexical in each message names"
      (is (and (holds-ask (list 'propositionalContent MsgFromAnn (list hungry Ann)) CxDesk)
               (holds-ask (list 'propositionalContent MsgFromBob (list hungry Bob)) CxDesk))
          "an indexical-resolving reading does not exist yet, so this fails until one is built"))))

;; The UTF-8/UTF-16 case: dataContent is the decoded text a file holds, independent
;; of the byte encoding that stores it. vaelii states no byte-level vocabulary at all, so
;; the only KB-expressible content of "stored under two encodings" is two files each
;; stating the one decoded string directly -- exactly what dataContent's declared meaning
;; requires, with no derivation attempted or needed.
(tu/deftest-kb decoded-text-fixes-data-content-not-the-byte-encoding
  (tu/with-terms [CxDesk Utf8File Utf16File]
    (desk! CxDesk)
    (tu/with-entailing
      (v/assert kb (list 'digital_artifact Utf8File) CxDesk)
      (v/assert kb (list 'digital_artifact Utf16File) CxDesk)
      (v/assert kb (list 'dataContent Utf8File "The library closes at dusk.") CxDesk)
      (v/assert kb (list 'dataContent Utf16File "The library closes at dusk.") CxDesk))
    (testing "the decoded text is equal regardless of which byte encoding stored it"
      (is (= "The library closes at dusk." (bound-value kb (list 'dataContent Utf8File '?s) CxDesk '?s)))
      (is (= "The library closes at dusk." (bound-value kb (list 'dataContent Utf16File '?s) CxDesk '?s))))))

;; opposite-day (Iris): Q sets a code under which a plain "no" answers
;; "yes". R's plain-English reading is stated directly (the positive control: nothing
;; needs deriving to read R in the language it is written in). carries stays binary, with
;; no code argument, so nothing derives the reading R has under Q's code, or the
;; agentClaims that reading would support, from the plain-English carries fact plus the
;; fact that Q set up a code. The KB must not conclude the plain reading as a claim
;; either -- agentClaims is never derived from carries at all.
(tu/deftest-kb ^:red opposite-day-s-code-is-not-derived-from-plain-carries
  (tu/with-terms [CxDesk Q R Cleo stillHere]
    (desk! CxDesk)
    (tu/with-entailing
      (v/assert kb (list 'digital_artifact Q) CxDesk)
      (v/assert kb (list 'digital_artifact R) CxDesk)
      (v/assert kb (list 'dataContent Q "Does Cleo still exist? Answer no if yes.") CxDesk)
      (v/assert kb (list 'dataContent R "No.") CxDesk)
      (v/assert kb (list 'propositionalContent R (list 'not (list stillHere Cleo))) CxDesk))
    (testing "the plain-English reading is the positive control, and it is in force"
      (is (holds-ask (list 'propositionalContent R (list 'not (list stillHere Cleo))) CxDesk)))
    (testing "RED: nothing derives the flipped reading Q's code gives R, or Cleo's claim of it"
      (is (and (holds-ask (list 'propositionalContent R (list stillHere Cleo)) CxDesk)
               (seq (v/ask kb (list 'agentClaims Cleo '?h) CxDesk)))
          "the carries code argument is punted, so this fails until it is un-punted"))
    (testing "the KB never concludes Cleo claims the plain negative reading either"
      (is (empty? (v/ask kb (list 'agentClaims Cleo '?h) CxDesk))))))
