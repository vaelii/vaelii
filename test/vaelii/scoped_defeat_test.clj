;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.scoped-defeat-test
  "A clash is decided at its vantage — the most general context that sees every member —
  and the loser is disbelieved there and in every context below it, and nowhere else.  A
  context's belief therefore never depends on what its spec contexts hold
  (docs/nmtms.md, \"A defeat is scoped to its vantage\").

  Every test states its lattice in a comment, since the answer is a function of it."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu])
  (:import [java.io File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

;; Cleared after opening, as `tu/fresh` is: the space is opened `:recover? false`, and on
;; a disk backend it holds what the previous test left, which a KB without a recover
;; refuses to write over.
(defn- arbitrating-kb []
  (doto (v/open-kb (assoc tu/scratch-space :constraints :arbitrate)) (tu/clear-kb!)))
(defn- refusing-kb []
  (doto (v/open-kb (assoc tu/scratch-space :constraints :refuse)) (tu/clear-kb!)))

(defn- permutations [xs]
  (if (empty? xs)
    [[]]
    (for [x xs, more (permutations (remove #{x} xs))] (cons x more))))

(defn- types! [kb & ts]
  (doseq [t ts] (v/assert kb (list 'genl t 'thing) 'CxUniverse)))

(deftest a-clash-seen-only-below-leaves-the-general-context-believing
  ;;   CxUniverse
  ;;     └─ CxA        (cat Rex) default
  ;;          └─ CxD   (dog Rex) monotonic
  ;;   (disjoint dog cat) in CxUniverse, asserted last so both policies admit the facts
  (doseq [[label build] [[":refuse" refusing-kb] [":arbitrate" arbitrating-kb]]]
    (testing label
      (tu/with-neutral-kb [kb build]
        (tu/with-terms [CxA CxD cat dog meows Rex]
          (types! kb cat dog)
          (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
          (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
          (v/assert kb (list 'set/forwardRule (list 'implies (list cat '?x) (list meows '?x))) CxA)
          (v/assert kb (list cat Rex) CxA)
          (v/assert kb (list dog Rex) CxD {:strength :monotonic})
          (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
          (testing "the general context never sees the monotonic claim, so it keeps its own"
            (is (v/ask? kb (list cat Rex) CxA))
            (is (v/ask? kb (list meows Rex) CxA)))
          (testing "the vantage and below disbelieve the loser"
            (is (v/ask? kb (list dog Rex) CxD))
            (is (not (v/ask? kb (list cat Rex) CxD))))
          (testing "a consequence stored above the vantage follows the reader"
            (is (not (v/ask? kb (list meows Rex) CxD))))
          (testing "the loser's raw label is IN: the defeat is contextual"
            (is (v/in? kb (v/handle-of kb (list cat Rex) CxA)))
            (is (v/believed? kb (v/handle-of kb (list cat Rex) CxA) CxA))
            (is (not (v/believed? kb (v/handle-of kb (list cat Rex) CxA) CxD))))
          (testing "retracting the stronger side revives the loser below"
            (v/retract! kb (v/handle-of kb (list dog Rex) CxD))
            (is (v/ask? kb (list cat Rex) CxD))
            (is (v/ask? kb (list meows Rex) CxD))))))))

(deftest a-loser-in-the-vantage-itself-is-defeated-for-every-reader
  ;;   CxUniverse
  ;;     └─ CxA        (dog Rex) monotonic
  ;;          └─ CxD   (cat Rex) default
  ;; The vantage is CxD, the loser's own context, so every reader of the loser is at or
  ;; below it and the defeat is the global one.
  (tu/with-neutral-kb [kb arbitrating-kb]
    (tu/with-terms [CxA CxD cat dog Rex]
      (types! kb cat dog)
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
      (v/assert kb (list dog Rex) CxA {:strength :monotonic})
      (v/assert kb (list cat Rex) CxD)
      (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
      (is (not (v/ask? kb (list cat Rex) CxD)))
      (is (not (v/in? kb (v/handle-of kb (list cat Rex) CxD)))))))

(deftest a-clash-between-siblings-is-decided-at-their-common-descendant
  ;;   CxUniverse
  ;;     ├─ CxB        (cat Rex) default
  ;;     └─ CxC        (dog Rex) monotonic
  ;;          CxE sees CxB and CxC
  (tu/with-neutral-kb [kb arbitrating-kb]
    (tu/with-terms [CxB CxC CxE cat dog Rex]
      (types! kb cat dog)
      (doseq [c [CxB CxC]] (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
      (v/assert kb (list 'genlCx CxE CxB) 'CxUniverse)
      (v/assert kb (list 'genlCx CxE CxC) 'CxUniverse)
      (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
      (v/assert kb (list cat Rex) CxB)
      (v/assert kb (list dog Rex) CxC {:strength :monotonic})
      (is (v/ask? kb (list cat Rex) CxB))
      (is (v/ask? kb (list dog Rex) CxE))
      (is (not (v/ask? kb (list cat Rex) CxE))))))

(defn- disagreement-world!
  "The lattice `a-reader-below-two-vantages-that-disagree-believes-every-member` draws, in
  `kb`: `(cat Rex)` in CxA and `(dog Rex)` in CxB, each with a `:default` assert and a
  `:monotonic` route a rule derives, and one `except` per route, each in its own context.
  A vantage that sees `CxHide1` reads cat as a default, so it defeats cat; one that sees
  `CxHide2` reads dog as a default and defeats dog.

  `vantages` is `{vantage [hide-context …]}` — each vantage is given a `genlCx` edge to
  CxA, to CxB and to every hide context named.  Returns `{:cat :dog}`, the two handles."
  [kb {:keys [CxA CxB CxHide1 CxHide2 cat dog mono_cat_src mono_dog_src Rex]} vantages]
  (types! kb cat dog)
  (doseq [c [CxA CxB CxHide1 CxHide2]]
    (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
  (doseq [[vantage hides] vantages
          up              (concat [CxA CxB] hides)]
    (v/assert kb (list 'genlCx vantage up) 'CxUniverse))
  (v/assert kb (list cat Rex) CxA)
  (v/assert kb (list 'set/forwardRule (list 'implies (list mono_cat_src '?x) (list cat '?x)))
            CxA {:strength :monotonic})
  (let [cat-src (v/assert kb (list mono_cat_src Rex) CxA {:strength :monotonic})]
    (v/assert kb (list dog Rex) CxB)
    (v/assert kb (list 'set/forwardRule (list 'implies (list mono_dog_src '?x) (list dog '?x)))
              CxB {:strength :monotonic})
    (let [dog-src (v/assert kb (list mono_dog_src Rex) CxB {:strength :monotonic})]
      (v/assert kb (list 'except (list 'sentexHandle cat-src)) CxHide1 {:strength :monotonic})
      (v/assert kb (list 'except (list 'sentexHandle dog-src)) CxHide2 {:strength :monotonic})
      (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
      {:cat (v/handle-of kb (list cat Rex) CxA)
       :dog (v/handle-of kb (list dog Rex) CxB)})))

(deftest a-reader-below-two-vantages-that-disagree-believes-every-member
  ;;   CxUniverse
  ;;     ├─ CxA       (cat Rex) default, and monotonic through (mono_cat_src Rex)
  ;;     ├─ CxB       (dog Rex) default, and monotonic through (mono_dog_src Rex)
  ;;     ├─ CxHide1   (except (sentexHandle (mono_cat_src Rex)))
  ;;     └─ CxHide2   (except (sentexHandle (mono_dog_src Rex)))
  ;;   CxW1 ─ sees CxA CxB CxHide1, so it reads cat as a default and dog as monotonic
  ;;   CxW2 ─ sees CxA CxB CxHide2, so it reads dog as a default and cat as monotonic
  ;;   CxZ  ─ sees CxW1 and CxW2, so it reads two verdicts and takes neither
  (tu/with-neutral-kb [kb arbitrating-kb]
    (tu/with-terms [CxA CxB CxHide1 CxHide2 CxW1 CxW2 CxZ cat dog mono_cat_src mono_dog_src Rex]
      (let [terms {:CxA CxA :CxB CxB :CxHide1 CxHide1 :CxHide2 CxHide2 :cat cat :dog dog
                   :mono_cat_src mono_cat_src :mono_dog_src mono_dog_src :Rex Rex}
            {cat-h :cat dog-h :dog} (disagreement-world! kb terms {CxW1 [CxHide1]
                                                                   CxW2 [CxHide2]})]
        (doseq [up [CxW1 CxW2]] (v/assert kb (list 'genlCx CxZ up) 'CxUniverse))
        (testing "each vantage defeats the member whose class is lower there"
          (is (not (v/ask? kb (list cat Rex) CxW1)))
          (is (v/ask? kb (list dog Rex) CxW1))
          (is (v/ask? kb (list cat Rex) CxW2))
          (is (not (v/ask? kb (list dog Rex) CxW2))))
        (testing "a reader below both takes neither verdict"
          (is (v/ask? kb (list cat Rex) CxZ))
          (is (v/ask? kb (list dog Rex) CxZ))
          (is (= {:withdrawn? false :scoped-vantages [] :believed? true}
                 (select-keys (v/belief-status kb cat-h CxZ)
                              [:withdrawn? :scoped-vantages :believed?])))
          (is (= {:withdrawn? false :scoped-vantages [] :believed? true}
                 (select-keys (v/belief-status kb dog-h CxZ)
                              [:withdrawn? :scoped-vantages :believed?]))))
        (testing "each vantage still names its own verdict"
          (is (= [CxW1] (:scoped-vantages (v/belief-status kb cat-h CxW1))))
          (is (= [CxW2] (:scoped-vantages (v/belief-status kb dog-h CxW2)))))
        (testing "the KB-wide reading reports the nogood and names what each vantage decided"
          (let [entry (first (filter #(= #{cat-h dog-h} (:nogood %)) (v/contradictions kb)))]
            (is (some? entry))
            (is (= {CxW1 cat-h CxW2 dog-h} (:vantages entry)))))
        (testing "the reader arity reports it for the reader it is a dilemma for, and no other"
          (is (some #(= #{cat-h dog-h} (:nogood %)) (v/contradictions kb CxZ)))
          (is (not-any? #(= #{cat-h dog-h} (:nogood %)) (v/contradictions kb CxW1)))
          (is (not-any? #(= #{cat-h dog-h} (:nogood %)) (v/contradictions kb CxW2)))
          (is (not-any? #(= #{cat-h dog-h} (:nogood %)) (v/contradictions kb CxA))))))))

(deftest vantages-that-agree-still-convict-for-a-reader-below-them
  ;;   CxW1 and CxW3 both see CxHide1, so both defeat (cat Rex); CxW2 sees CxHide2 and
  ;;   defeats (dog Rex).  CxY sees CxW1 and CxW3 — one verdict, twice — and CxZ sees all
  ;;   three, so it sees the disagreement.
  (tu/with-neutral-kb [kb arbitrating-kb]
    (tu/with-terms [CxA CxB CxHide1 CxHide2 CxW1 CxW2 CxW3 CxY CxZ
                    cat dog mono_cat_src mono_dog_src Rex]
      (let [terms {:CxA CxA :CxB CxB :CxHide1 CxHide1 :CxHide2 CxHide2 :cat cat :dog dog
                   :mono_cat_src mono_cat_src :mono_dog_src mono_dog_src :Rex Rex}
            {cat-h :cat dog-h :dog} (disagreement-world! kb terms {CxW1 [CxHide1]
                                                                   CxW2 [CxHide2]
                                                                   CxW3 [CxHide1]})]
        (doseq [[k up] [[CxY CxW1] [CxY CxW3] [CxZ CxW1] [CxZ CxW2] [CxZ CxW3]]]
          (v/assert kb (list 'genlCx k up) 'CxUniverse))
        (testing "two vantages that decided alike convict the member they both defeated"
          (is (not (v/ask? kb (list cat Rex) CxY)))
          (is (v/ask? kb (list dog Rex) CxY))
          (is (= [CxW1 CxW3] (sort (:scoped-vantages (v/belief-status kb cat-h CxY))))))
        (testing "a reader seeing the third vantage as well sees the disagreement"
          (is (v/ask? kb (list cat Rex) CxZ))
          (is (v/ask? kb (list dog Rex) CxZ))
          (is (= [] (:scoped-vantages (v/belief-status kb cat-h CxZ)))))
        (testing "the clash is a dilemma for the reader that sees the disagreement only"
          (is (some #(= #{cat-h dog-h} (:nogood %)) (v/contradictions kb CxZ)))
          (is (not-any? #(= #{cat-h dog-h} (:nogood %)) (v/contradictions kb CxY))))))))

(deftest a-defeat-outside-the-disagreement-still-withdraws-for-that-reader
  ;;   The CxW1/CxW2 disagreement over (cat Rex) and (dog Rex), plus a second clash:
  ;;   (fish Rex) is known-true in CxF and disjoint from cat, so the vantage that sees
  ;;   CxA and CxF defeats (cat Rex) on its own account.  CxZ sees that vantage too.
  (tu/with-neutral-kb [kb arbitrating-kb]
    (tu/with-terms [CxA CxB CxHide1 CxHide2 CxW1 CxW2 CxF CxV4 CxZ
                    cat dog fish mono_cat_src mono_dog_src Rex]
      (let [terms {:CxA CxA :CxB CxB :CxHide1 CxHide1 :CxHide2 CxHide2 :cat cat :dog dog
                   :mono_cat_src mono_cat_src :mono_dog_src mono_dog_src :Rex Rex}
            {cat-h :cat dog-h :dog} (disagreement-world! kb terms {CxW1 [CxHide1]
                                                                   CxW2 [CxHide2]})]
        (types! kb fish)
        (v/assert kb (list 'genlCx CxF 'CxUniverse) 'CxUniverse)
        ;; CxV4 sees CxHide1 too, so cat is a default there and fish's monotonic claim
        ;; outranks it; without that both sides are monotonic and the clash is hard
        (doseq [[k up] [[CxV4 CxA] [CxV4 CxF] [CxV4 CxHide1] [CxZ CxW1] [CxZ CxW2] [CxZ CxV4]]]
          (v/assert kb (list 'genlCx k up) 'CxUniverse))
        (v/assert kb (list fish Rex) CxF {:strength :monotonic})
        (v/assert kb (list 'disjoint fish cat) 'CxUniverse)
        (testing "the second clash defeats cat at a vantage outside the disagreement"
          (is (= [CxV4] (:scoped-vantages (v/belief-status kb cat-h CxV4)))))
        (testing "a reader seeing that vantage reads cat as withdrawn, disagreement or not"
          (is (not (v/ask? kb (list cat Rex) CxZ)))
          (is (= [CxV4] (:scoped-vantages (v/belief-status kb cat-h CxZ))))
          (is (true? (:withdrawn? (v/belief-status kb cat-h CxZ)))))
        (testing "and dog, whose only verdict came from the disagreement, stays believed"
          (is (v/ask? kb (list dog Rex) CxZ))
          (is (= [] (:scoped-vantages (v/belief-status kb dog-h CxZ)))))))))

(deftest a-pair-one-vantage-decided-is-no-dilemma-for-a-reader-that-defeat-reaches
  ;;   CxW1 sees CxHide1 only, so it reads cat as a default against a monotonic dog and
  ;;   defeats cat.  CxW3 sees CxHide1 and CxHide2, so it reads both as defaults and ties
  ;;   — it decides nothing.  CxZ sees CxW1 and CxW3: the standing defeat reaches it, so
  ;;   the pair is decided for CxZ and the tie at CxW3 does not revive it.
  (tu/with-neutral-kb [kb arbitrating-kb]
    (tu/with-terms [CxA CxB CxHide1 CxHide2 CxW1 CxW3 CxZ
                    cat dog mono_cat_src mono_dog_src Rex]
      (let [terms {:CxA CxA :CxB CxB :CxHide1 CxHide1 :CxHide2 CxHide2 :cat cat :dog dog
                   :mono_cat_src mono_cat_src :mono_dog_src mono_dog_src :Rex Rex}
            {cat-h :cat dog-h :dog} (disagreement-world! kb terms
                                                         {CxW1 [CxHide1]
                                                          CxW3 [CxHide1 CxHide2]})]
        (doseq [up [CxW1 CxW3]] (v/assert kb (list 'genlCx CxZ up) 'CxUniverse))
        (testing "the vantage that could rank the pair defeated the weaker member"
          (is (not (v/ask? kb (list cat Rex) CxW1)))
          (is (v/ask? kb (list dog Rex) CxW1)))
        (testing "the reader below both reads that defeat, since a tie decides nothing"
          (is (not (v/ask? kb (list cat Rex) CxZ)))
          (is (v/ask? kb (list dog Rex) CxZ))
          (is (true? (:withdrawn? (v/belief-status kb cat-h CxZ)))))
        (testing "so the pair is no dilemma for that reader, whatever the settle published"
          (is (not-any? #(= #{cat-h dog-h} (:nogood %)) (v/contradictions kb CxZ)))
          (is (not-any? #(= #{cat-h dog-h} (:nogood %)) (v/contradictions kb CxW1))))
        (testing "and the vantage that tied still reads both as believed, and reports it"
          (is (v/ask? kb (list cat Rex) CxW3))
          (is (v/ask? kb (list dog Rex) CxW3))
          (is (some #(= #{cat-h dog-h} (:nogood %)) (v/contradictions kb CxW3))))))))

(deftest a-disagreement-survives-the-reasoning-image-it-is-written-into
  ;; `:vantage-disagreements` is derived state the settle re-decides, and it rides in the
  ;; reasoning image beside the scoped defeats.  A store closed with a disagreement
  ;; standing and reopened on its image reads what it read before the close.
  (let [dir (str (Files/createTempDirectory "vaelii-disagreement-"
                                            (into-array FileAttribute [])))
        read-all (fn [kb CxZ CxW1 cat dog Rex cat-h dog-h]
                   {:cat-z  (v/ask? kb (list cat Rex) CxZ)
                    :dog-z  (v/ask? kb (list dog Rex) CxZ)
                    :cat-w1 (v/ask? kb (list cat Rex) CxW1)
                    :vant-z (:scoped-vantages (v/belief-status kb cat-h CxZ))
                    :dilemma-z (boolean (some #(= #{cat-h dog-h} (:nogood %))
                                              (v/contradictions kb CxZ)))
                    :vantages (:vantages (first (filter #(= #{cat-h dog-h} (:nogood %))
                                                        (v/contradictions kb))))})]
    (try
      (tu/with-terms [CxA CxB CxHide1 CxHide2 CxW1 CxW2 CxZ
                      cat dog mono_cat_src mono_dog_src Rex]
        (let [terms {:CxA CxA :CxB CxB :CxHide1 CxHide1 :CxHide2 CxHide2 :cat cat :dog dog
                     :mono_cat_src mono_cat_src :mono_dog_src mono_dog_src :Rex Rex}
              kb    (v/open-kb {:backend :disk-snapshot :dir dir :constraints :arbitrate})
              {cat-h :cat dog-h :dog} (disagreement-world! kb terms {CxW1 [CxHide1]
                                                                     CxW2 [CxHide2]})]
          (doseq [up [CxW1 CxW2]] (v/assert kb (list 'genlCx CxZ up) 'CxUniverse))
          (let [before (read-all kb CxZ CxW1 cat dog Rex cat-h dog-h)]
            (is (= {:cat-z true :dog-z true :cat-w1 false :vant-z []
                    :dilemma-z true :vantages {CxW1 cat-h CxW2 dog-h}}
                   before)
                "the disagreement stands before the close")
            (v/close! kb)
            (let [kb2   (v/open-kb {:backend :disk-snapshot :dir dir :constraints :arbitrate})
                  after (read-all kb2 CxZ CxW1 cat dog Rex cat-h dog-h)]
              (is (= before after) "and the reopened store reads it the same way")
              (v/close! kb2)))))
      (finally
        (doseq [f (reverse (file-seq (io/file dir)))] (.delete ^File f))))))

(deftest a-disagreement-is-still-reported-after-an-unrelated-settle
  ;; The report comes off the roster, not off the settle that weighed the nogood: a later
  ;; settle whose region does not reach the pair weighs it in no round.
  (tu/with-neutral-kb [kb arbitrating-kb]
    (tu/with-terms [CxA CxB CxHide1 CxHide2 CxW1 CxW2 CxZ CxFar
                    cat dog mono_cat_src mono_dog_src Rex bird Tweety]
      (let [terms {:CxA CxA :CxB CxB :CxHide1 CxHide1 :CxHide2 CxHide2 :cat cat :dog dog
                   :mono_cat_src mono_cat_src :mono_dog_src mono_dog_src :Rex Rex}
            {cat-h :cat dog-h :dog} (disagreement-world! kb terms {CxW1 [CxHide1]
                                                                   CxW2 [CxHide2]})
            reported? #(boolean (some (fn [r] (= #{cat-h dog-h} (:nogood r))) %))]
        (doseq [up [CxW1 CxW2]] (v/assert kb (list 'genlCx CxZ up) 'CxUniverse))
        (is (reported? (v/contradictions kb)) "after the settle that decided it")
        (testing "and after a write that touches nothing the clash holds"
          (types! kb bird)
          (v/assert kb (list 'genlCx CxFar 'CxUniverse) 'CxUniverse)
          (v/assert kb (list bird Tweety) CxFar)
          (is (reported? (v/contradictions kb)))
          (is (reported? (v/contradictions kb CxZ)))
          (is (v/ask? kb (list cat Rex) CxZ))
          (is (v/ask? kb (list dog Rex) CxZ))
          (is (not (v/ask? kb (list cat Rex) CxW1))))))))

(deftest a-disagreement-reads-the-same-in-every-arrival-order
  ;; The lattice as a list of steps, asserted in several orders.  A step naming an
  ;; `except` follows the fact whose handle it reads, which is the one dependency; every
  ;; other step is independent, and the permutations move them.  The answers are keyed on
  ;; content — `:cat`/`:dog` rather than the handles, which differ per order — since a
  ;; handle is allocated in assertion order and no answer may turn on one.
  (let [run (fn [order]
              (tu/with-neutral-kb [kb arbitrating-kb]
                (tu/with-terms [CxA CxB CxHide1 CxHide2 CxW1 CxW2 CxZ
                                cat dog mono_cat_src mono_dog_src Rex]
                  (let [edges (fn [] (doseq [[k up] [[CxA 'CxUniverse] [CxB 'CxUniverse]
                                                     [CxHide1 'CxUniverse] [CxHide2 'CxUniverse]
                                                     [CxW1 CxA] [CxW1 CxB] [CxW1 CxHide1]
                                                     [CxW2 CxA] [CxW2 CxB] [CxW2 CxHide2]
                                                     [CxZ CxW1] [CxZ CxW2]]]
                                       (v/assert kb (list 'genlCx k up) 'CxUniverse)))
                        types (fn [] (types! kb cat dog))
                        catf  (fn [] (v/assert kb (list cat Rex) CxA)
                                (v/assert kb (list 'set/forwardRule
                                                   (list 'implies (list mono_cat_src '?x)
                                                         (list cat '?x)))
                                          CxA {:strength :monotonic})
                                (let [h (v/assert kb (list mono_cat_src Rex) CxA
                                                  {:strength :monotonic})]
                                  (v/assert kb (list 'except (list 'sentexHandle h)) CxHide1
                                            {:strength :monotonic})))
                        dogf  (fn [] (v/assert kb (list dog Rex) CxB)
                                (v/assert kb (list 'set/forwardRule
                                                   (list 'implies (list mono_dog_src '?x)
                                                         (list dog '?x)))
                                          CxB {:strength :monotonic})
                                (let [h (v/assert kb (list mono_dog_src Rex) CxB
                                                  {:strength :monotonic})]
                                  (v/assert kb (list 'except (list 'sentexHandle h)) CxHide2
                                            {:strength :monotonic})))
                        decl  (fn [] (v/assert kb (list 'disjoint dog cat) 'CxUniverse))
                        steps {:edges edges :types types :cat catf :dog dogf :decl decl}]
                    (doseq [k order] ((steps k)))
                    (let [cat-h (v/handle-of kb (list cat Rex) CxA)
                          dog-h (v/handle-of kb (list dog Rex) CxB)
                          name* {cat-h :cat dog-h :dog}
                          entry (first (filter #(= #{cat-h dog-h} (:nogood %))
                                               (v/contradictions kb)))]
                      {:cat-z    (v/ask? kb (list cat Rex) CxZ)
                       :dog-z    (v/ask? kb (list dog Rex) CxZ)
                       :cat-w1   (v/ask? kb (list cat Rex) CxW1)
                       :dog-w1   (v/ask? kb (list dog Rex) CxW1)
                       :cat-w2   (v/ask? kb (list cat Rex) CxW2)
                       :dog-w2   (v/ask? kb (list dog Rex) CxW2)
                       ;; the vantage symbols are gensyms, fresh per run, so they are keyed
                       ;; by their place in the lattice rather than by their spelling
                       :vantages (into {} (map (fn [[v h]] [({CxW1 :w1 CxW2 :w2} v v) (name* h)]))
                                       (:vantages entry))
                       :dilemma-z (boolean (some #(= #{cat-h dog-h} (:nogood %))
                                                 (v/contradictions kb CxZ)))
                       :dilemma-w1 (boolean (some #(= #{cat-h dog-h} (:nogood %))
                                                  (v/contradictions kb CxW1)))})))))
        orders [[:types :edges :cat :dog :decl]
                [:edges :types :cat :dog :decl]
                [:types :cat :dog :decl :edges]
                [:types :dog :cat :edges :decl]
                [:types :decl :edges :cat :dog]
                [:edges :types :dog :decl :cat]]
        answers (mapv run orders)]
    (is (= {:cat-z true :dog-z true :cat-w1 false :dog-w1 true :cat-w2 true :dog-w2 false
            :dilemma-z true :dilemma-w1 false}
           (dissoc (first answers) :vantages))
        "the reader below both believes both; each vantage keeps its own verdict")
    (is (= {:w1 :cat :w2 :dog} (:vantages (first answers)))
        "and the two vantages decided differently, each naming what it defeated")
    (doseq [[order answer] (map vector (rest orders) (rest answers))]
      (is (= (first answers) answer) (str "order " (pr-str order) " read differently")))))

(deftest a-disagreement-is-the-same-whatever-order-it-arrives-in
  ;; The invariant the roster owes: belief is computed from current state, so building the
  ;; same lattice with the vantages declared in either order gives one answer.
  (let [world (fn [order]
                (tu/with-neutral-kb [kb arbitrating-kb]
                  (tu/with-terms [CxA CxB CxHide1 CxHide2 CxW1 CxW2 CxZ
                                  cat dog mono_cat_src mono_dog_src Rex]
                    (let [terms {:CxA CxA :CxB CxB :CxHide1 CxHide1 :CxHide2 CxHide2
                                 :cat cat :dog dog :mono_cat_src mono_cat_src
                                 :mono_dog_src mono_dog_src :Rex Rex}
                          vs    (if (= :forward order)
                                  (array-map CxW1 [CxHide1] CxW2 [CxHide2])
                                  (array-map CxW2 [CxHide2] CxW1 [CxHide1]))
                          {cat-h :cat dog-h :dog} (disagreement-world! kb terms vs)]
                      (doseq [up (if (= :forward order) [CxW1 CxW2] [CxW2 CxW1])]
                        (v/assert kb (list 'genlCx CxZ up) 'CxUniverse))
                      {:cat-at-z  (v/ask? kb (list cat Rex) CxZ)
                       :dog-at-z  (v/ask? kb (list dog Rex) CxZ)
                       :cat-at-w1 (v/ask? kb (list cat Rex) CxW1)
                       :dog-at-w2 (v/ask? kb (list dog Rex) CxW2)
                       :vantages  (set (keys (:vantages (first (filter #(= #{cat-h dog-h}
                                                                           (:nogood %))
                                                                       (v/contradictions kb))))))
                       :dilemma-at-z (boolean (some #(= #{cat-h dog-h} (:nogood %))
                                                    (v/contradictions kb CxZ)))}))))
        forward (world :forward)
        reverse (world :reverse)]
    (is (= {:cat-at-z true :dog-at-z true :cat-at-w1 false :dog-at-w2 false
            :dilemma-at-z true}
           (dissoc forward :vantages)))
    (is (= (dissoc forward :vantages) (dissoc reverse :vantages)))
    (is (= 2 (count (:vantages forward)) (count (:vantages reverse))))))

(deftest the-reader-arity-drops-a-dilemma-the-reader-cannot-see
  ;;   CxUniverse ─ CxGen ─ CxSpec, and CxOther beside CxGen.
  ;;   Two defaults rebut each other in CxGen: a dilemma for CxGen and CxSpec, and no
  ;;   business of CxOther, which sees neither member.
  (tu/with-neutral-kb [kb arbitrating-kb]
    (tu/with-terms [CxGen CxSpec CxOther wobbles Pip]
      (v/assert kb (list 'genlCx CxGen 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxSpec CxGen) 'CxUniverse)
      (v/assert kb (list 'genlCx CxOther 'CxUniverse) 'CxUniverse)
      (v/assert kb (list wobbles Pip) CxGen)
      (v/assert kb (list 'not (list wobbles Pip)) CxGen)
      (let [mine? (fn [c] (boolean (some #(= 2 (count (:sides %))) (v/contradictions kb c))))]
        (testing "the KB-wide reading holds the pair"
          (is (seq (v/contradictions kb))))
        (testing "the contexts that see both members read it"
          (is (mine? CxGen))
          (is (mine? CxSpec)))
        (testing "a context that sees neither does not"
          (is (not (mine? CxOther)))
          (is (not (mine? 'CxUniverse))))
        (testing "a nil context is the KB-wide reading"
          (is (= (v/contradictions kb) (v/contradictions kb nil))))))))

(deftest an-except-over-a-genlcx-edge-leaves-the-vantage-named
  ;;   CxUniverse
  ;;     └─ CxA        (cat Rex) default
  ;;          └─ CxD   (dog Rex) monotonic — the vantage, which scoped-defeats (cat Rex)
  ;;   CxR descends from CxA and from CxD by two edges; the CxR→CxD edge is excepted.
  ;; Belief reads the vantage set unfiltered, so CxR still reads the member as withdrawn.
  ;; The diagnostic reads the same set, so it still names CxD as the cause.
  (tu/with-neutral-kb [kb arbitrating-kb]
    (tu/with-terms [CxA CxD CxR cat dog Rex]
      (types! kb cat dog)
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
      (v/assert kb (list 'genlCx CxR CxA) 'CxUniverse)
      (let [edge (v/assert kb (list 'genlCx CxR CxD) 'CxUniverse)]
        (v/assert kb (list cat Rex) CxA)
        (v/assert kb (list dog Rex) CxD {:strength :monotonic})
        (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
        (let [h (v/handle-of kb (list cat Rex) CxA)]
          (is (= [CxD] (:scoped-vantages (v/belief-status kb h CxR))) "before the except")
          (v/assert kb (list 'except (list 'sentexHandle edge)) CxR {:strength :monotonic})
          (testing "the except holes the filtered read of the edge"
            (is (not (v/ask? kb (list dog Rex) CxR))))
          (testing "belief withdraws the member from CxR, and the status names the vantage"
            (is (false? (v/believed? kb h CxR)))
            (is (= {:withdrawn? true :scoped-vantages [CxD] :believed? false}
                   (select-keys (v/belief-status kb h CxR)
                                [:withdrawn? :scoped-vantages :believed?])))))))))

(deftest every-read-with-a-reader-applies-the-scoped-defeat
  ;;   CxUniverse
  ;;     └─ CxA        (cat Rex) default, (pet Rex), backward (pet ?x) ⇒ (cat ?x)
  ;;          └─ CxD   (dog Rex) monotonic, forward (cat ?x) ⇒ (purrs ?x)
  ;; The forward rule in CxD fires on (cat Rex) and stores (purrs Rex) in CxD, resting on
  ;; the member CxD disbelieves.
  (tu/with-neutral-kb [kb arbitrating-kb]
    (tu/with-terms [CxA CxD cat dog pet purrs Rex]
      (types! kb cat dog pet)
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
      (v/assert kb (list 'implies (list pet '?x) (list cat '?x)) CxA)
      (v/assert kb (list 'set/forwardRule (list 'implies (list cat '?x) (list purrs '?x))) CxD)
      (v/assert kb (list pet Rex) CxA)
      (v/assert kb (list cat Rex) CxA)
      (v/assert kb (list dog Rex) CxD {:strength :monotonic})
      (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
      (let [h (v/handle-of kb (list cat Rex) CxA)]
        (testing "a backward rule does not re-derive the member for a reader below the vantage"
          (is (not (v/ask? kb (list cat Rex) CxD)))
          (is (v/ask? kb (list cat Rex) CxA)))
        (testing "belief-status names the withdrawal and its vantage"
          (is (= {:withdrawn? true :scoped-vantages [CxD] :believed? false}
                 (select-keys (v/belief-status kb h CxD) [:withdrawn? :scoped-vantages :believed?])))
          (is (= {:withdrawn? false :scoped-vantages [] :believed? true}
                 (select-keys (v/belief-status kb h CxA) [:withdrawn? :scoped-vantages :believed?]))))
        (testing "a firing stored below the vantage on the member is stored and not believed"
          (is (some #(= (list purrs Rex) (:sentence %)) (v/sentexes-in-context kb CxD)))
          (is (not-any? #(= (list purrs Rex) (:sentence %))
                        (v/sentexes-in-context kb CxD {:believed? true})))
          (is (not (v/ask? kb (list purrs Rex) CxD))))
        (testing "why-not reads each sentex at its own context"
          (is (true? (:believed? (v/why-not kb h))) "the member is believed in CxA")
          (let [r (v/why-not kb (v/handle-of kb (list purrs Rex) CxD))]
            (is (= :withdrawn (:reason r)))
            (is (= [{:handle h :vantage CxD}]
                   (mapv #(select-keys % [:handle :vantage]) (:withdrawn-by r))))))
        (testing "why reads it the same way, so the two stay complements"
          (let [ph (v/handle-of kb (list purrs Rex) CxD)]
            (is (false? (:believed? (v/why kb ph)))
                "the conclusion its own context withdraws has no proof tree")
            (is (nil? (:support (v/why kb ph))))
            (is (= (:believed? (v/why kb ph)) (:believed? (v/why-not kb ph))))
            (is (true? (:believed? (v/why kb h))) "the member is believed in CxA")
            (is (true? (:premise? (v/why kb h))) "and asserted, so it rests on nothing")))))))

(deftest the-reports-of-a-write-name-what-a-scoped-defeat-moved
  ;;   CxUniverse
  ;;     └─ CxA        (cat Rex) default
  ;;          └─ CxD   forward (cat ?x) ⇒ (purrs ?x); the write adds (dog Rex) monotonic
  ;; The write defeats (cat Rex) at CxD, which withdraws (purrs Rex), stored in CxD, from
  ;; every context that can read it.  No relabel records that, and both reports name it.
  (doseq [[label report] [["edit-with-consequences!" v/edit-with-consequences!]
                          ["preview" v/preview]]]
    (testing label
      (tu/with-neutral-kb [kb arbitrating-kb]
        (tu/with-terms [CxA CxD cat dog purrs Rex]
          (types! kb cat dog)
          (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
          (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
          (v/assert kb (list 'set/forwardRule (list 'implies (list cat '?x) (list purrs '?x))) CxD)
          (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
          (v/assert kb (list cat Rex) CxA)
          (let [r       (report kb {:add [[(list dog Rex) CxD {:strength :monotonic}]]})
                removed (set (map :sentence (:believed-removed r)))]
            (is (contains? removed (list purrs Rex)) "the firing stored below the vantage")
            (is (not (contains? removed (list cat Rex))) "the member stays believed in CxA")))))))

(deftest the-same-knowledge-in-any-order-is-believed-the-same-way
  ;; The first test's lattice, every order of the four writes after the wiring.
  (let [outcomes
        (mapv
         (fn [order]
           (tu/with-neutral-kb [kb arbitrating-kb]
             (tu/with-terms [CxA CxD cat dog meows Rex]
               (types! kb cat dog)
               (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
               (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
               (doseq [w order]
                 (case w
                   :rule     (v/assert kb (list 'set/forwardRule
                                                (list 'implies (list cat '?x) (list meows '?x)))
                                       CxA)
                   :cat      (v/assert kb (list cat Rex) CxA)
                   :dog      (v/assert kb (list dog Rex) CxD {:strength :monotonic})
                   :disjoint (v/assert kb (list 'disjoint dog cat) 'CxUniverse)))
               (vec (for [s [(list cat Rex) (list meows Rex)] c [CxA CxD]]
                      (v/ask? kb s c))))))
         (permutations [:rule :cat :dog :disjoint]))]
    (is (= #{[true false true false]} (set outcomes)))))
