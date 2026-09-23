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

;; ---- the vantage decides under `:refuse` too ----------------------------

(defn- write!
  "One of the three writes `vantage-world!` permutes, returning `:refused` when the
  entry point turned it away and nil otherwise."
  [kb w {:keys [cat dog Rex]} cat-ctx dog-ctx]
  (try
    (case w
      :cat      (v/assert kb (list cat Rex) cat-ctx)
      :dog      (v/assert kb (list dog Rex) dog-ctx {:strength :monotonic})
      :disjoint (v/assert kb (list 'disjoint dog cat) 'CxUniverse))
    nil
    (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(deftest under-refuse-a-pair-split-across-a-visibility-edge-is-decided-at-its-vantage
  ;;   CxUniverse
  ;;     └─ CxA        (cat Rex) default
  ;;          └─ CxD   (dog Rex) monotonic
  ;;   (disjoint dog cat) in CxUniverse, which every context sees
  ;;
  ;; CxD is the vantage: CxA does not see CxD, so CxA holds the pair's near half only.
  ;; Cases b and d of the prompt's table — `(cat Rex)` written last, and the declaration
  ;; written last — and both policies decide them the same way.
  (doseq [[label build] [[":refuse" refusing-kb] [":arbitrate" arbitrating-kb]]]
    (testing label
      (let [outcomes
            (into #{}
                  (map (fn [order]
                         (tu/with-neutral-kb [kb build]
                           (tu/with-terms [CxA CxD cat dog Rex]
                             (let [world {:cat cat :dog dog :Rex Rex}]
                               (types! kb cat dog)
                               (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
                               (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
                               (if (some #(write! kb % world CxA CxD) order)
                                 :refused
                                 [(v/ask? kb (list cat Rex) CxA)
                                  (v/ask? kb (list cat Rex) CxD)
                                  (v/ask? kb (list dog Rex) CxD)
                                  (mapv :violation (v/violations kb))]))))))
                  (permutations [:cat :dog :disjoint]))]
        (testing "every order the entry point admits reaches one belief outcome"
          (is (= #{[true false true []]} (disj outcomes :refused))
              "the loser is defeated at the vantage and believed above it, and the
               ledger has nothing to say about a pair somebody decided"))
        (testing "and `:refuse` alone turns a writer away, on grounds that writer can see"
          ;; case a: `(dog Rex)` written into CxD, which reads `(cat Rex)` through the
          ;; edge — the one write of the six orders that is refused rather than weighed
          (is (= (if (= ":refuse" label) #{:refused} #{}) (disj outcomes [true false true []]))))))))

(deftest under-refuse-a-pair-two-sibling-contexts-wrote-is-decided-at-their-descendant
  ;;   CxUniverse
  ;;     ├─ CxB        (cat Rex) default
  ;;     └─ CxC        (dog Rex) monotonic
  ;;          CxE sees CxB and CxC
  ;;   (disjoint dog cat) in CxUniverse
  ;;
  ;; CxE is the vantage, and neither writer's own context sees the far half — so no
  ;; arrival order refuses, and case c reads the same under both policies.
  (doseq [[label build] [[":refuse" refusing-kb] [":arbitrate" arbitrating-kb]]]
    (testing label
      (let [outcomes
            (into #{}
                  (map (fn [order]
                         (tu/with-neutral-kb [kb build]
                           (tu/with-terms [CxB CxC CxE cat dog Rex]
                             (let [world {:cat cat :dog dog :Rex Rex}]
                               (types! kb cat dog)
                               (doseq [c [CxB CxC]]
                                 (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
                               (v/assert kb (list 'genlCx CxE CxB) 'CxUniverse)
                               (v/assert kb (list 'genlCx CxE CxC) 'CxUniverse)
                               (if (some #(write! kb % world CxB CxC) order)
                                 :refused
                                 [(v/ask? kb (list cat Rex) CxB)
                                  (v/ask? kb (list cat Rex) CxE)
                                  (v/ask? kb (list dog Rex) CxE)
                                  (mapv :violation (v/violations kb))]))))))
                  (permutations [:cat :dog :disjoint]))]
        (is (= #{[true false true []]} outcomes)
            "CxB keeps the claim it wrote, CxE reads the monotonic winner, and nothing
             is refused")))))

(deftest a-reader-that-disbelieves-a-genl-edge-stops-reaching-over-it
  ;;   CxUniverse    (genl chi thing) (genl dog thing) (chi Rex)
  ;;                 (transitiveInArg largerThan 1 genl)  (largerThan dog cat)
  ;;     └─ CxA      (genl chi dog)                 :default
  ;;          └─ CxB (not (genl chi dog))           :monotonic  ← the vantage
  ;;     └─ CxC      a sibling of CxB, which sees neither the denial nor the vantage
  ;; The edge is a supporter of the `genl` relation, so what the scoped defeat has to
  ;; reach is the taxonomy's closures and not only the network label: `believed?` of the
  ;; edge and every read that crosses it answer about one KB from one context.
  (doseq [edge-first? [true false]]
    (testing (if edge-first? "the edge arrives first" "the denial arrives first")
      (tu/with-neutral-kb [kb arbitrating-kb]
        (tu/with-terms [CxA CxB CxC chi_t dog_t cat_t largerThan Rex]
          (types! kb chi_t dog_t cat_t)
          (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
          (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)
          (v/assert kb (list 'genlCx CxC CxA) 'CxUniverse)
          (v/assert kb (list 'transitiveInArg largerThan 1 'genl) 'CxUniverse)
          (v/assert kb (list largerThan dog_t cat_t) 'CxUniverse)
          (v/assert kb (list chi_t Rex) 'CxUniverse)
          (let [edge!   #(v/assert kb (list 'genl chi_t dog_t) CxA)
                denial! #(v/assert kb (list 'not (list 'genl chi_t dog_t)) CxB
                                   {:strength :monotonic})
                _       (if edge-first? (do (edge!) (denial!)) (do (denial!) (edge!)))
                h       (v/handle-of kb (list 'genl chi_t dog_t) CxA)
                reads   (fn [rdr]
                          [(v/believed? kb h rdr)
                           (v/ask? kb (list 'genl chi_t dog_t) rdr)
                           (v/genl? kb chi_t dog_t rdr)
                           (v/isa? kb Rex dog_t rdr)
                           (v/ask? kb (list largerThan chi_t cat_t) rdr)])]
            (testing "the vantage disbelieves the edge and every read over it"
              (is (= [false false false false false] (reads CxB))))
            (testing "the context that states the edge reads all five as true"
              (is (= [true true true true true] (reads CxA))))
            (testing "and so does a sibling that sees neither the denial nor the vantage"
              (is (= [true true true true true] (reads CxC))))
            (testing "the context above the edge reaches over nothing, edge or no edge"
              (is (= [true false false false false] (reads 'CxUniverse)))
              "the edge is in CxA, which CxUniverse does not see")))))))

(deftest lifting-the-denial-returns-every-reader-to-reaching
  ;;   The lattice above, with the denial retracted.  The scoped closures are memoized
  ;;   under a key carrying the supporter-visibility generation, so a lift that empties
  ;;   the scoped-defeat roster has to move that generation or a reader keeps the closure
  ;;   the defeat is gone from.
  (tu/with-neutral-kb [kb arbitrating-kb]
    (tu/with-terms [CxA CxB chi_t dog_t cat_t largerThan Rex]
      (types! kb chi_t dog_t cat_t)
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)
      (v/assert kb (list 'transitiveInArg largerThan 1 'genl) 'CxUniverse)
      (v/assert kb (list largerThan dog_t cat_t) 'CxUniverse)
      (v/assert kb (list chi_t Rex) 'CxUniverse)
      (v/assert kb (list 'genl chi_t dog_t) CxA)
      (let [d     (v/assert kb (list 'not (list 'genl chi_t dog_t)) CxB {:strength :monotonic})
            h     (v/handle-of kb (list 'genl chi_t dog_t) CxA)
            reads (fn [rdr]
                    [(v/believed? kb h rdr)
                     (v/genl? kb chi_t dog_t rdr)
                     (v/isa? kb Rex dog_t rdr)
                     (v/ask? kb (list largerThan chi_t cat_t) rdr)])]
        ;; read from CxB while the defeat stands, so a stale memo would have something
        ;; to be stale from
        (is (= [false false false false] (reads CxB)))
        (v/retract! kb d)
        (testing "every read CxB lost comes back"
          (is (= [true true true true] (reads CxB))))
        (testing "and CxA is where it was"
          (is (= [true true true true] (reads CxA))))))))

(deftest a-context-that-disbelieves-a-genlcx-edge-stops-seeing-over-it
  ;;   CxUniverse  (genlCx CxB CxE), the edge under test
  ;;     ├─ CxE    (marker Pin) monotonic, and where the edge is written
  ;;     └─ CxB    (not (genlCx CxB CxE)) monotonic   ← the vantage
  ;; The genlCx twin of the `genl` case.  This namespace's KBs hold no shipped
  ;; ontology, so the mark CxCore declares is asserted here: `genlCx` is
  ;; forced-decontextualized, which stores the edge in CxUniverse whatever context it
  ;; is written into, and the test asserts that placement rather than hand-placing it.
  ;; The denial's functor is `not`, so it is not decontextualized and stays in CxB — the
  ;; asymmetry that gives a genlCx clash a vantage below CxUniverse at all.
  ;;
  ;; It is also the case the callback's recursion question is about: every ancestor-set
  ;; read inside the withdrawal answer takes `tax/context-up-global`, so the filtered
  ;; genlCx walk asks a question the unfiltered closure answers and never re-enters
  ;; itself.
  (doseq [edge-first? [true false]]
    (testing (if edge-first? "the edge arrives first" "the denial arrives first")
      (tu/with-neutral-kb [kb arbitrating-kb]
        (tu/with-terms [CxB CxE marker_t Pin]
          (types! kb marker_t)
          (v/assert kb '(forced_decontextualized_predicate genlCx) 'CxUniverse)
          (doseq [c [CxB CxE]] (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
          (v/assert kb (list marker_t Pin) CxE {:strength :monotonic})
          (let [edge!   #(v/assert kb (list 'genlCx CxB CxE) CxE)
                denial! #(v/assert kb (list 'not (list 'genlCx CxB CxE)) CxB
                                   {:strength :monotonic})
                _       (if edge-first? (do (edge!) (denial!)) (do (denial!) (edge!)))
                h       (v/handle-of kb (list 'genlCx CxB CxE) 'CxUniverse)]
            (testing "the mark stored the edge in CxUniverse, not in the context it was written into"
              (is (= ['CxUniverse]
                     (mapv :context (v/sentexes-matching kb (list 'genlCx CxB CxE)))))
              (is (some? h))
              (is (true? (v/in? kb h))) "and it stands in the network")
            (testing "the denial is not decontextualized, so the vantage is CxB"
              (is (= [CxB] (mapv :context
                                 (v/sentexes-matching
                                  kb (list 'not (list 'genlCx CxB CxE)))))))
            (testing "the vantage disbelieves the edge, and CxUniverse does not"
              (is (false? (v/believed? kb h CxB)))
              (is (true? (v/believed? kb h 'CxUniverse))))
            (testing "and stops seeing the context the edge put above it"
              (is (not (v/sees? kb CxB CxE)))
              (is (not (contains? (set (v/context-up kb CxB)) CxE)))
              (is (not (v/ask? kb (list marker_t Pin) CxB))))
            (testing "CxB keeps the ancestor the edge under test did not give it"
              (is (contains? (set (v/context-up kb CxB)) 'CxUniverse)))))))))

(deftest a-definitional-clash-is-decided-on-the-hierarchy-its-vantage-reads
  ;;   CxUniverse  (genl chi thing) (genl dog thing) (genl cat thing)  (disjoint dog cat)
  ;;     └─ CxA    (genl chi dog)                  :default
  ;;          └─ CxB (not (genl chi dog))          :monotonic   ← the vantage
  ;;                 (chi Kit)  (cat Kit)
  ;;
  ;; CxB disbelieves the edge, so from CxB `chi` is not a `dog` and the two memberships
  ;; of `Kit` clash with nothing.  No other context holds both, so no context sees a
  ;; complete clash: both are believed at CxB and nothing is reported.
  ;;
  ;; The settle empties the scoped defeats before it discovers, so its discovery reads
  ;; the hierarchy the KB holds globally and does mint the pair.  What keeps a verdict
  ;; off that hierarchy is the resolution: the denial's own defeat of the edge is scoped,
  ;; it is applied first and alone, and the round after it re-asks the pair's grounds at
  ;; CxB (`reads-clash?`), which no longer reads them.
  (doseq [cat-strength [:monotonic :default]]
    (testing (str "(cat Kit) is " cat-strength)
      (doseq [order (permutations [:denial :chi :cat])]
        (testing (pr-str (vec order))
          (tu/with-neutral-kb [kb arbitrating-kb]
            (tu/with-terms [CxA CxB chi_t dog_t cat_t Kit]
              (types! kb chi_t dog_t cat_t)
              (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
              (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)
              (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse {:strength :monotonic})
              (v/assert kb (list 'genl chi_t dog_t) CxA)
              (let [write!  {:denial #(v/assert kb (list 'not (list 'genl chi_t dog_t)) CxB
                                                {:strength :monotonic})
                             :chi    #(v/assert kb (list chi_t Kit) CxB)
                             :cat    #(v/assert kb (list cat_t Kit) CxB
                                                {:strength cat-strength})}
                    stored? (try (doseq [k order] ((write! k))) true
                                 (catch clojure.lang.ExceptionInfo _ false))]
                (if-not stored?
                  ;; The one order of the twelve the entry point refuses, and it is the
                  ;; entry point's own reading rather than this: `(chi Kit)` is offered
                  ;; while `(cat Kit)` is known-true and CxB still reads the separation,
                  ;; the denial not having been written yet.
                  (is (= [:monotonic [:cat :chi :denial]] [cat-strength (vec order)]))
                  (do
                    (testing "CxB reads no separation, so it believes both memberships"
                      (is (false? (v/disjoint? kb chi_t cat_t CxB)))
                      (is (true? (v/ask? kb (list chi_t Kit) CxB)))
                      (is (true? (v/ask? kb (list cat_t Kit) CxB))))
                    (testing "and nothing is reported, to CxB or to the KB"
                      (is (empty? (v/contradictions kb CxB)))
                      (is (empty? (v/contradictions kb))))
                    (testing "CxA keeps the edge it stated and the separation over it"
                      (is (contains? (set (v/genls kb chi_t CxA)) dog_t))
                      (is (true? (v/disjoint? kb chi_t cat_t CxA))))
                    (testing "and reads neither membership, which is written below it"
                      (is (false? (v/ask? kb (list chi_t Kit) CxA)))
                      (is (false? (v/ask? kb (list cat_t Kit) CxA))))))))))))))

(deftest the-entry-point-reads-the-grounds-and-not-only-what-they-separate
  ;;   The same lattice, written `(cat Kit)` known-true, then `(chi Kit)`, then the
  ;;   denial.  At the moment `(chi Kit)` is offered, CxB reads `chi \u2291 dog` and
  ;;   `dog \u2225 cat` and holds `(cat Kit)` as known-true — so what the membership opposes
  ;;   can never be given up.  What makes the two a **pair** can: the separation reaches
  ;;   `chi` over a `:default` `(genl chi dog)` edge, and a denial of that edge takes the
  ;;   pair out of CxB's view entirely.
  ;;
  ;;   So the sentence is admitted and weighed rather than refused, and the weighing
  ;;   gives the known-true side the belief until the denial arrives.  Refusing it would
  ;;   have thrown away, on the strength of what had not been written yet, content that
  ;;   five of the six write orders store and believe
  ;;   (`order_independence_test/a-definitional-refusal-does-not-follow-the-write-order`).
  (tu/with-neutral-kb [kb arbitrating-kb]
    (tu/with-terms [CxA CxB chi_t dog_t cat_t Kit]
      (types! kb chi_t dog_t cat_t)
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)
      (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'genl chi_t dog_t) CxA)
      (v/assert kb (list cat_t Kit) CxB {:strength :monotonic})
      (testing "admitted while CxB still reads the separation, and the known-true side wins"
        (is (some? (v/assert kb (list chi_t Kit) CxB)))
        (is (false? (v/ask? kb (list chi_t Kit) CxB)))
        (is (true? (v/ask? kb (list cat_t Kit) CxB))))
      (v/assert kb (list 'not (list 'genl chi_t dog_t)) CxB {:strength :monotonic})
      (testing "and believed once the denial has taken the pair away"
        (is (false? (v/disjoint? kb chi_t cat_t CxB)))
        (is (true? (v/ask? kb (list chi_t Kit) CxB)))
        (is (true? (v/ask? kb (list cat_t Kit) CxB)))
        (is (empty? (v/contradictions kb)))))))

(deftest a-separation-that-cannot-be-given-up-still-refuses-at-the-entry-point
  ;;   The control on the case above, and the line the reading does not cross.  Put the
  ;;   edge `(genl chi dog)` in known-true and nothing in the derivation is defeasible:
  ;;   no denial can retire the pair, so the membership is one the KB could never
  ;;   believe and the writer is told so.  Only the class of that one edge differs from
  ;;   the test above.
  (tu/with-neutral-kb [kb arbitrating-kb]
    (tu/with-terms [CxA CxB chi_t dog_t cat_t Kit]
      (types! kb chi_t dog_t cat_t)
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)
      (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'genl chi_t dog_t) CxA {:strength :monotonic})
      (v/assert kb (list cat_t Kit) CxB {:strength :monotonic})
      (is (thrown? clojure.lang.ExceptionInfo (v/assert kb (list chi_t Kit) CxB)))
      (is (empty? (v/sentexes-matching kb (list chi_t Kit)))))))

(deftest retracting-the-denial-returns-the-verdict-it-withheld
  ;;   The same lattice.  Retracting the denial puts `chi ⊑ dog` back in CxB's view, the
  ;;   separation with it, and the clash is decided again: `(cat Kit)` is known-true, so
  ;;   `(chi Kit)` is the loser.  Re-asserting the denial withdraws the grounds a second
  ;;   time and the membership comes back, which is what makes the answer a function of
  ;;   what stands rather than of what has happened.
  (tu/with-neutral-kb [kb arbitrating-kb]
    (tu/with-terms [CxA CxB chi_t dog_t cat_t Kit]
      (types! kb chi_t dog_t cat_t)
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)
      (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'genl chi_t dog_t) CxA)
      (let [denial! #(v/assert kb (list 'not (list 'genl chi_t dog_t)) CxB
                               {:strength :monotonic})
            d       (denial!)
            _       (v/assert kb (list chi_t Kit) CxB)
            _       (v/assert kb (list cat_t Kit) CxB {:strength :monotonic})
            reads   #(vector (v/disjoint? kb chi_t cat_t CxB)
                             (v/ask? kb (list chi_t Kit) CxB)
                             (v/ask? kb (list cat_t Kit) CxB))]
        (is (= [false true true] (reads)))
        (v/retract! kb d)
        (testing "the grounds are back, so the clash is decided and the default loses"
          (is (= [true false true] (reads))))
        (denial!)
        (testing "and withdrawn again, so the membership is believed again"
          (is (= [false true true] (reads))))))))

(deftest a-verdict-taken-at-a-vantage-reaches-the-contexts-below-it
  ;;   CxUniverse  (genl chi thing) (genl dog thing) (genl cat thing)  (disjoint dog cat)
  ;;     └─ CxA    (genl chi dog)                  :default
  ;;          └─ CxB (chi Kit)  (cat Kit) monotonic          ← the vantage
  ;;               └─ CxC  (not (genl chi dog))    :monotonic
  ;;
  ;;   The denial is now *below* both memberships.  CxB cannot see CxC, so CxB reads the
  ;;   separation, sees the whole pair and decides it; the loser's own context is CxB, so
  ;;   the defeat is the network's.  CxC reads no separation and would have decided
  ;;   nothing, and it still reads `(chi Kit)` as defeated — a defeat at a vantage reaches
  ;;   every context below it (docs/nmtms.md), and CxC is below.  The verdict rests on a
  ;;   hierarchy its own vantage reads, which is the whole of what is owed here.
  (tu/with-neutral-kb [kb arbitrating-kb]
    (tu/with-terms [CxA CxB CxC chi_t dog_t cat_t Kit]
      (types! kb chi_t dog_t cat_t)
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)
      (v/assert kb (list 'genlCx CxC CxB) 'CxUniverse)
      (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'genl chi_t dog_t) CxA)
      (v/assert kb (list 'not (list 'genl chi_t dog_t)) CxC {:strength :monotonic})
      (v/assert kb (list chi_t Kit) CxB)
      (v/assert kb (list cat_t Kit) CxB {:strength :monotonic})
      (testing "the vantage reads the separation and decides on it"
        (is (true? (v/disjoint? kb chi_t cat_t CxB)))
        (is (false? (v/ask? kb (list chi_t Kit) CxB)))
        (is (true? (v/ask? kb (list cat_t Kit) CxB))))
      (testing "and the context below it reads no separation and the same verdict"
        (is (false? (v/disjoint? kb chi_t cat_t CxC)))
        (is (false? (v/ask? kb (list chi_t Kit) CxC)))))))
