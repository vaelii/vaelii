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

(defn- permutations [xs]
  (if (empty? xs)
    [[]]
    (for [x xs, more (permutations (remove #{x} xs))] (cons x more))))

(defn- types! [kb & ts]
  (doseq [t ts] (v/assert kb (list 'genl t 'thing) 'CxUniverse)))

(defn- verdicts-agree!
  "Check the justification verdicts against belief over every sentex stored in `ctxs`, at
  each of them (`tu/verdict-violations`)."
  [kb ctxs]
  (is (= [] (tu/verdict-violations
             kb (into [] (comp (mapcat #(v/sentexes-in-context kb %)) (map :id)) ctxs) ctxs))))

(defn- status
  "`belief-status`' `:withdrawn?` and `:believed?` for `h` at `c`, with the contexts of the
  placed defeats of `h` in force there under `:defeat-vantages`."
  [kb h c]
  (assoc (select-keys (v/belief-status kb h c) [:withdrawn? :believed?])
         :defeat-vantages (tu/defeat-vantages kb h c)))

(deftest a-clash-seen-only-below-leaves-the-general-context-believing
  ;;   CxUniverse
  ;;     └─ CxA        (cat Rex) default
  ;;          └─ CxD   (dog Rex) monotonic
  ;;   (disjoint dog cat) in CxUniverse, asserted last
  (tu/with-neutral-kb [kb tu/fresh]
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
        (is (v/ask? kb (list meows Rex) CxD))))))

(deftest a-rule-answer-the-vantage-defeated-is-not-an-answer-below-it
  ;; the backward rule re-derives the loser at every reader; below the vantage the
  ;; derived answer is the stored sentex the scoped defeat withdrew there
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [CxA CxD cat dog kitty Rex]
      (types! kb cat dog)
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
      (v/assert kb (list 'set/backwardRule (list 'implies (list kitty '?x) (list cat '?x))) CxA)
      (v/assert kb (list kitty Rex) CxA)
      (v/assert kb (list cat Rex) CxA)
      (v/assert kb (list dog Rex) CxD {:strength :monotonic})
      (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
      (is (seq (v/query kb (list cat Rex) CxA {:max-depth 3})) "above the vantage it holds")
      (is (empty? (v/query kb (list cat Rex) CxD {:max-depth 3}))
          "and below it the rule answers nothing"))))

(deftest a-loser-in-the-vantage-itself-is-defeated-for-every-reader
  ;;   CxUniverse
  ;;     └─ CxA        (dog Rex) monotonic
  ;;          └─ CxD   (cat Rex) default
  ;; The vantage is CxD, the loser's own context, so every reader of the loser is at or
  ;; below it and the defeat is the global one.
  (tu/with-neutral-kb [kb tu/fresh]
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
  (tu/with-neutral-kb [kb tu/fresh]
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
  (tu/with-neutral-kb [kb tu/fresh]
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
          (is (= {:withdrawn? false :defeat-vantages [] :believed? true}
                 (status kb cat-h CxZ)))
          (is (= {:withdrawn? false :defeat-vantages [] :believed? true}
                 (status kb dog-h CxZ))))
        (testing "each vantage still names its own verdict"
          (is (= [CxW1] (tu/defeat-vantages kb cat-h CxW1)))
          (is (= [CxW2] (tu/defeat-vantages kb dog-h CxW2))))
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
  (tu/with-neutral-kb [kb tu/fresh]
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
          (is (= [CxW1 CxW3] (sort (tu/defeat-vantages kb cat-h CxY))))
          (is (= [] (tu/defeat-vantages kb cat-h '?ctx))
              "a variable context names no reader, so it sees neither vantage"))
        (testing "a reader seeing the third vantage as well sees the disagreement"
          (is (v/ask? kb (list cat Rex) CxZ))
          (is (v/ask? kb (list dog Rex) CxZ))
          (is (= [] (tu/defeat-vantages kb cat-h CxZ))))
        (testing "the clash is a dilemma for the reader that sees the disagreement only"
          (is (some #(= #{cat-h dog-h} (:nogood %)) (v/contradictions kb CxZ)))
          (is (not-any? #(= #{cat-h dog-h} (:nogood %)) (v/contradictions kb CxY))))))))

(deftest a-defeat-outside-the-disagreement-still-withdraws-for-that-reader
  ;;   The CxW1/CxW2 disagreement over (cat Rex) and (dog Rex), plus a second clash:
  ;;   (fish Rex) is known-true in CxF and disjoint from cat, so the vantage that sees
  ;;   CxA and CxF defeats (cat Rex) on its own account.  CxZ sees that vantage too.
  (tu/with-neutral-kb [kb tu/fresh]
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
          (is (= [CxV4] (tu/defeat-vantages kb cat-h CxV4))))
        (testing "a reader seeing that vantage reads cat as withdrawn, disagreement or not"
          (is (not (v/ask? kb (list cat Rex) CxZ)))
          (is (= [CxV4] (tu/defeat-vantages kb cat-h CxZ)))
          (is (true? (:withdrawn? (v/belief-status kb cat-h CxZ)))))
        (testing "and dog, whose only verdict came from the disagreement, stays believed"
          (is (v/ask? kb (list dog Rex) CxZ))
          (is (= [] (tu/defeat-vantages kb dog-h CxZ))))))))

(deftest a-reader-below-a-vantage-decides-the-pair-from-its-own-view
  ;;   CxW1 sees CxHide1 only, so it reads cat as a default against a monotonic dog and
  ;;   defeats cat.  CxW3 sees CxHide1 and CxHide2, so it reads both as defaults and ties.
  ;;   CxZ sees CxW1 and CxW3, so it sees both excepts: it reads the tie CxW3 reads, and
  ;;   CxW1's verdict does not bind it (docs/reference.md, decision 3).
  (tu/with-neutral-kb [kb tu/fresh]
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
          (is (v/ask? kb (list dog Rex) CxW1))
          (is (not-any? #(= #{cat-h dog-h} (:nogood %)) (v/contradictions kb CxW1))))
        (testing "the reader below both reads the tie its own view holds"
          (is (v/ask? kb (list cat Rex) CxZ))
          (is (v/ask? kb (list dog Rex) CxZ))
          (is (false? (:withdrawn? (v/belief-status kb cat-h CxZ))))
          (is (some #(= #{cat-h dog-h} (:nogood %)) (v/contradictions kb CxZ))))
        (testing "and the vantage that tied reads both as believed, and reports it"
          (is (v/ask? kb (list cat Rex) CxW3))
          (is (v/ask? kb (list dog Rex) CxW3))
          (is (some #(= #{cat-h dog-h} (:nogood %)) (v/contradictions kb CxW3))))))))

(deftest a-disagreement-survives-the-reasoning-image-it-is-written-into
  (tu/with-snapshot-platform
    ;; The candidate index is derived state, and it rides in the reasoning image.  A store closed with a disagreement standing and reopened on its
    ;; image reads what it read before the close.
    (let [dir (str (Files/createTempDirectory "vaelii-disagreement-"
                                              (into-array FileAttribute [])))
          read-all (fn [kb CxZ CxW1 cat dog Rex cat-h dog-h]
                     {:cat-z  (v/ask? kb (list cat Rex) CxZ)
                      :dog-z  (v/ask? kb (list dog Rex) CxZ)
                      :cat-w1 (v/ask? kb (list cat Rex) CxW1)
                      :vant-z (tu/defeat-vantages kb cat-h CxZ)
                      :dilemma-z (boolean (some #(= #{cat-h dog-h} (:nogood %))
                                                (v/contradictions kb CxZ)))
                      :vantages (:vantages (first (filter #(= #{cat-h dog-h} (:nogood %))
                                                          (v/contradictions kb))))})]
      (try
        (tu/with-terms [CxA CxB CxHide1 CxHide2 CxW1 CxW2 CxZ
                        cat dog mono_cat_src mono_dog_src Rex]
          (let [terms {:CxA CxA :CxB CxB :CxHide1 CxHide1 :CxHide2 CxHide2 :cat cat :dog dog
                       :mono_cat_src mono_cat_src :mono_dog_src mono_dog_src :Rex Rex}
                kb    (v/open-kb {:backend :disk-snapshot :dir dir})
                {cat-h :cat dog-h :dog} (disagreement-world! kb terms {CxW1 [CxHide1]
                                                                       CxW2 [CxHide2]})]
            (doseq [up [CxW1 CxW2]] (v/assert kb (list 'genlCx CxZ up) 'CxUniverse))
            (let [before (read-all kb CxZ CxW1 cat dog Rex cat-h dog-h)]
              (is (= {:cat-z true :dog-z true :cat-w1 false :vant-z []
                      :dilemma-z true :vantages {CxW1 cat-h CxW2 dog-h}}
                     before)
                  "the disagreement stands before the close")
              (v/close! kb)
              (let [kb2   (v/open-kb {:backend :disk-snapshot :dir dir})
                    after (read-all kb2 CxZ CxW1 cat dog Rex cat-h dog-h)]
                (is (= before after) "and the reopened store reads it the same way")
                (v/close! kb2)))))
        (finally
          (doseq [f (reverse (file-seq (io/file dir)))] (.delete ^File f)))))))

(deftest a-disagreement-is-still-reported-after-an-unrelated-settle
  ;; Every settle re-finds the standing nogoods, so a later settle whose region does not
  ;; reach the pair reports it again.
  (tu/with-neutral-kb [kb tu/fresh]
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
              (tu/with-neutral-kb [kb tu/fresh]
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
  ;; The order-independence invariant: belief is computed from current state, so building the
  ;; same lattice with the vantages declared in either order gives one answer.
  (let [world (fn [order]
                (tu/with-neutral-kb [kb tu/fresh]
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
  (tu/with-neutral-kb [kb tu/fresh]
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
  ;;          └─ CxD   (dog Rex) monotonic — the vantage, whose readers take (cat Rex) OUT
  ;;   CxR descends from CxA and from CxD by two edges; the CxR→CxD edge is excepted.
  ;; Belief reads the vantage set unfiltered, so CxR still reads the member as withdrawn.
  ;; The diagnostic reads the same set, so it still names CxD as the cause.
  (tu/with-neutral-kb [kb tu/fresh]
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
          (is (= [CxD] (tu/defeat-vantages kb h CxR)) "before the except")
          (v/assert kb (list 'except (list 'sentexHandle edge)) CxR {:strength :monotonic})
          (testing "the except holes the filtered read of the edge"
            (is (not (v/ask? kb (list dog Rex) CxR))))
          (testing "belief withdraws the member from CxR, and the status names the vantage"
            (is (false? (v/believed? kb h CxR)))
            (is (= {:withdrawn? true :defeat-vantages [CxD] :believed? false}
                   (status kb h CxR)))))))))

(deftest every-read-with-a-reader-applies-the-scoped-defeat
  ;;   CxUniverse
  ;;     └─ CxA        (cat Rex) default, (pet Rex), backward (pet ?x) ⇒ (cat ?x)
  ;;          └─ CxD   (dog Rex) monotonic, forward (cat ?x) ⇒ (purrs ?x)
  ;; The forward rule in CxD fires on (cat Rex) and stores (purrs Rex) in CxD, resting on
  ;; the member CxD disbelieves.
  (tu/with-neutral-kb [kb tu/fresh]
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
          (is (= {:withdrawn? true :defeat-vantages [CxD] :believed? false}
                 (status kb h CxD)))
          (is (= {:withdrawn? false :defeat-vantages [] :believed? true}
                 (status kb h CxA))))
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
            (is (false? (:believed? (tu/why-root kb ph)))
                "the conclusion its own context withdraws has no proof tree")
            (is (nil? (:support (tu/why-root kb ph))))
            (is (= (:believed? (tu/why-root kb ph)) (:believed? (v/why-not kb ph))))
            (is (true? (:believed? (tu/why-root kb h))) "the member is believed in CxA")
            (is (true? (:premise? (tu/why-root kb h))) "and asserted, so it rests on nothing")))))))

(deftest the-reports-of-a-write-name-what-a-scoped-defeat-moved
  ;;   CxUniverse
  ;;     └─ CxA        (cat Rex) default
  ;;          └─ CxD   forward (cat ?x) ⇒ (purrs ?x); the write adds (dog Rex) monotonic
  ;; The write defeats (cat Rex) at CxD, which withdraws (purrs Rex), stored in CxD, from
  ;; every context that can read it.  No relabel records that, and both reports name it.
  (doseq [[label report] [["edit-with-consequences!" v/edit-with-consequences!]
                          ["preview" v/preview]]]
    (testing label
      (tu/with-neutral-kb [kb tu/fresh]
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
           (tu/with-neutral-kb [kb tu/fresh]
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

;; ---- the vantage decides a pair its writers could not see ----------------

(defn- write!
  "One of the three writes `vantage-world!` permutes, returning the refusal's `:type`
  when the entry point turned it away and nil otherwise."
  [kb w {:keys [cat dog Rex]} cat-ctx dog-ctx]
  (try
    (case w
      :cat      (v/assert kb (list cat Rex) cat-ctx)
      :dog      (v/assert kb (list dog Rex) dog-ctx {:strength :monotonic})
      :disjoint (v/assert kb (list 'disjoint dog cat) 'CxUniverse))
    nil
    (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(deftest a-pair-split-across-a-visibility-edge-is-decided-at-its-vantage
  ;;   CxUniverse
  ;;     └─ CxA        (cat Rex) default
  ;;          └─ CxD   (dog Rex) monotonic
  ;;   (disjoint dog cat) in CxUniverse, which every context sees
  ;;
  ;; CxD is the vantage: CxA does not see CxD, so CxA holds the pair's near half only.
  (let [outcomes
        (into #{}
              (map (fn [order]
                     (tu/with-neutral-kb [kb tu/fresh]
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
    (is (= #{[true false true []]} outcomes)
        "every order reaches one belief outcome: the loser is defeated at the vantage
         and believed above it, and the ledger has nothing to say about a pair
         somebody decided")))

(deftest a-pair-two-sibling-contexts-wrote-is-decided-at-their-descendant
  ;;   CxUniverse
  ;;     ├─ CxB        (cat Rex) default
  ;;     └─ CxC        (dog Rex) monotonic
  ;;          CxE sees CxB and CxC
  ;;   (disjoint dog cat) in CxUniverse
  ;;
  ;; CxE is the vantage, and neither writer's own context sees the far half.
  (let [outcomes
        (into #{}
              (map (fn [order]
                     (tu/with-neutral-kb [kb tu/fresh]
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
         is refused")))

(deftest a-reader-that-disbelieves-a-genl-edge-stops-reaching-over-it
  ;;   CxUniverse    (genl chi thing) (genl dog thing) (chi Rex)
  ;;                 (transitiveInArgInverse typeLargerThan 1 genl)  (typeLargerThan dog cat)
  ;;     └─ CxA      (genl chi dog)                 :default
  ;;          └─ CxB (not (genl chi dog))           :monotonic  ← the vantage
  ;;     └─ CxC      a sibling of CxB, which sees neither the denial nor the vantage
  ;; The edge is a supporter of the `genl` relation, so what the scoped defeat has to
  ;; reach is the taxonomy's closures and not only the network label: `believed?` of the
  ;; edge and every read that crosses it answer about one KB from one context.
  (doseq [edge-first? [true false]]
    (testing (if edge-first? "the edge arrives first" "the denial arrives first")
      (tu/with-neutral-kb [kb tu/fresh]
        (tu/with-terms [CxA CxB CxC chi_t dog_t cat_t typeLargerThan Rex]
          (types! kb chi_t dog_t cat_t)
          (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
          (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)
          (v/assert kb (list 'genlCx CxC CxA) 'CxUniverse)
          (v/assert kb (list 'transitiveInArgInverse typeLargerThan 1 'genl) 'CxUniverse)
          (v/assert kb (list typeLargerThan dog_t cat_t) 'CxUniverse)
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
                           (v/ask? kb (list typeLargerThan chi_t cat_t) rdr)])]
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
  ;;   under a key carrying the change clock and the reading, so the retraction that
  ;;   empties the scoped-defeat entries retires every closure memoized while the defeat
  ;;   stood.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [CxA CxB chi_t dog_t cat_t typeLargerThan Rex]
      (types! kb chi_t dog_t cat_t)
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse typeLargerThan 1 'genl) 'CxUniverse)
      (v/assert kb (list typeLargerThan dog_t cat_t) 'CxUniverse)
      (v/assert kb (list chi_t Rex) 'CxUniverse)
      (v/assert kb (list 'genl chi_t dog_t) CxA)
      (let [d     (v/assert kb (list 'not (list 'genl chi_t dog_t)) CxB {:strength :monotonic})
            h     (v/handle-of kb (list 'genl chi_t dog_t) CxA)
            reads (fn [rdr]
                    [(v/believed? kb h rdr)
                     (v/genl? kb chi_t dog_t rdr)
                     (v/isa? kb Rex dog_t rdr)
                     (v/ask? kb (list typeLargerThan chi_t cat_t) rdr)])]
        ;; read from CxB while the defeat stands, so a stale memo would have something
        ;; to be stale from
        (is (= [false false false false] (reads CxB)))
        (v/retract! kb d)
        (testing "every read CxB lost comes back"
          (is (= [true true true true] (reads CxB))))
        (testing "and CxA is where it was"
          (is (= [true true true true] (reads CxA))))))))

(deftest a-denial-of-a-genlcx-edge-leaves-the-context-below-it-seeing-over-it
  ;;   CxUniverse  (genlCx CxB CxE), the edge under test
  ;;     ├─ CxE    (marker Marked) monotonic, and where the edge is written
  ;;     └─ CxB    (not (genlCx CxB CxE)) monotonic   ← the vantage
  ;; The genlCx twin of the `genl` case, with the opposite outcome: `genlCx` is in the
  ;; baseline forced-monotonic set, so the denial loses to the edge on this bare KB and no
  ;; vantage disbelieves the edge.  The KB holds no shipped ontology, so the CxUniverse mark is
  ;; asserted: `genlCx` is forced-decontextualized and stores in CxUniverse, while the
  ;; `not` denial stays in CxB.
  (doseq [edge-first? [true false]]
    (testing (if edge-first? "the edge arrives first" "the denial arrives first")
      (tu/with-neutral-kb [kb tu/fresh]
        (tu/with-terms [CxB CxE marker_t Marked]
          (types! kb marker_t)
          (v/assert kb '(forced_decontextualized_predicate genlCx) 'CxUniverse)
          (doseq [c [CxB CxE]] (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
          (v/assert kb (list marker_t Marked) CxE {:strength :monotonic})
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
            (testing "the denial is stored in CxB and loses to the edge, and both contexts believe it"
              (is (false? (v/in? kb (v/handle-of kb (list 'not (list 'genlCx CxB CxE)) CxB))))
              (is (true? (v/believed? kb h CxB)))
              (is (true? (v/believed? kb h 'CxUniverse))))
            (testing "so CxB sees the context the edge put above it"
              (is (v/sees? kb CxB CxE))
              (is (v/ask? kb (list marker_t Marked) CxB)))))))))

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
  ;; Discovery reads the global hierarchy and mints the pair; the denial's scoped defeat
  ;; of the edge is applied first and alone, and the next round's `reads-clash?` at CxB
  ;; finds no clash.
  (doseq [cat-strength [:monotonic :default]]
    (testing (str "(cat Kit) is " cat-strength)
      (doseq [order (permutations [:denial :chi :cat])]
        (testing (pr-str (vec order))
          (tu/with-neutral-kb [kb tu/fresh]
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
                ;; `:arbitrate` admits every order, since the `(genl chi dog)` edge that
                ;; makes the pair is `:default`
                (is stored?)
                (when stored?
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
                    (is (false? (v/ask? kb (list cat_t Kit) CxA)))))))))))))

(deftest the-entry-point-reads-the-grounds-and-not-only-what-they-separate
  ;;   The same lattice, written `(cat Kit)` known-true, then `(chi Kit)`, then the
  ;;   denial.  The separation reaches `chi` over a `:default` `(genl chi dog)` edge, so
  ;;   `(chi Kit)` is admitted and loses to the known-true side until the denial takes
  ;;   the pair out of CxB's view.
  (tu/with-neutral-kb [kb tu/fresh]
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

(deftest a-separation-that-cannot-be-given-up-is-stored-and-decided
  ;;   The control on the case above.  Put the edge `(genl chi dog)` in known-true and
  ;;   nothing in the derivation is defeasible: no denial can retire the pair.  The
  ;;   membership is stored all the same, and the known-true side wins.  Only the class of
  ;;   that one edge differs from the test above.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [CxA CxB chi_t dog_t cat_t Kit]
      (types! kb chi_t dog_t cat_t)
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)
      (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list 'genl chi_t dog_t) CxA {:strength :monotonic})
      (v/assert kb (list cat_t Kit) CxB {:strength :monotonic})
      (is (tu/stored-in-clash? kb (list chi_t Kit) CxB))
      (is (true? (v/ask? kb (list cat_t Kit) CxB))))))

(deftest retracting-the-denial-returns-the-verdict-it-withheld
  ;;   The same lattice.  Retracting the denial puts `chi ⊑ dog` back in CxB's view, the
  ;;   separation with it, and the clash is decided again: `(cat Kit)` is known-true, so
  ;;   `(chi Kit)` is the loser.  Re-asserting the denial withdraws the grounds a second
  ;;   time and the membership comes back, which is what makes the answer a function of
  ;;   what stands rather than of what has happened.
  (tu/with-neutral-kb [kb tu/fresh]
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

;; ---- a release only a context below the vantage can see ----
;;
;;   CxUniverse  (genl chi thing) (genl dog thing) (genl cat thing)  (disjoint dog cat)
;;     └─ CxA    (genl chi dog)                  :default
;;          └─ CxB (chi Kit) default  (cat Kit) monotonic
;;               └─ CxC
;;   the denial (not (genl chi dog)) monotonic sits in CxC (:below), or in a CxD that CxB
;;   sees (:above)
;;
;; With the denial below, CxB reads the separation, sees the whole pair and decides it.
;; CxC reads no separation and believes `(chi Kit)`: each reader decides from its own
;; view (docs/reference.md, decision 3).  With the denial above, CxB reads no separation
;; and nothing is decided.

(defn- release-steps [kb {:keys [CxA CxB CxC CxD chi_t dog_t cat_t Kit]} place]
  {:wiring #(do (types! kb chi_t dog_t cat_t)
                (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
                (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)
                (v/assert kb (list 'genlCx CxC CxB) 'CxUniverse)
                (v/assert kb (list 'genlCx CxD 'CxUniverse) 'CxUniverse)
                (when (= :above place) (v/assert kb (list 'genlCx CxB CxD) 'CxUniverse))
                (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse {:strength :monotonic})
                (v/assert kb (list 'genl chi_t dog_t) CxA))
   :denial #(v/assert kb (list 'not (list 'genl chi_t dog_t)) ({:below CxC :above CxD} place)
                      {:strength :monotonic})
   :chi    #(v/assert kb (list chi_t Kit) CxB)
   :cat    #(v/assert kb (list cat_t Kit) CxB {:strength :monotonic})})

(defn- release-reading
  "Per reader, `[(chi Kit) (cat Kit) chi-disjoint-from-cat]`."
  [kb {:keys [CxA CxB CxC CxD chi_t cat_t Kit]}]
  (verdicts-agree! kb [CxA CxB CxC CxD])
  (into {} (for [[r cx] [[:CxB CxB] [:CxC CxC]]]
             [r [(v/ask? kb (list chi_t Kit) cx) (v/ask? kb (list cat_t Kit) cx)
                 (v/disjoint? kb chi_t cat_t cx)]])))

(defn- with-release-kb
  "Call `f` with an arbitrating KB and the lattice's fresh terms."
  [f]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [CxA CxB CxC CxD chi_t dog_t cat_t Kit]
      (f kb {:CxA CxA :CxB CxB :CxC CxC :CxD CxD
             :chi_t chi_t :dog_t dog_t :cat_t cat_t :Kit Kit}))))

(def ^:private release-table
  {:below {:CxB [false true true] :CxC [true true false]}
   :above {:CxB [true true false] :CxC [true true false]}})

(deftest a-reader-below-a-vantage-that-reads-the-clash-released-believes-the-loser
  (doseq [[place expected] release-table
          order (permutations [:denial :chi :cat])]
    (with-release-kb
      (fn [kb ts]
        (let [steps (release-steps kb ts place)]
          ((:wiring steps))
          (doseq [k order] ((steps k)))
          (is (= expected (release-reading kb ts)) (pr-str place order)))))))

(deftest retracting-a-release-below-the-vantage-returns-every-reader
  ;; Each reader returns to what the KB without the denial reads, and the denial written
  ;; again restores the row.
  (doseq [place [:below :above]]
    (with-release-kb
      (fn [kb ts]
        (let [steps (release-steps kb ts place)]
          (doseq [k [:wiring :chi :cat]] ((steps k)))
          (let [without (release-reading kb ts)
                d       ((:denial steps))]
            (is (= {:CxB [false true true] :CxC [false true true]} without))
            (is (= (release-table place) (release-reading kb ts)) (pr-str place))
            (v/retract! kb d)
            (is (= without (release-reading kb ts)) (pr-str place))
            ((:denial steps))
            (is (= (release-table place) (release-reading kb ts)) (pr-str place))))))))

(deftest a-reader-below-a-vantage-that-excepts-the-winner-believes-the-loser
  ;; The release is an `except` in CxC of the winning membership: CxC sees no clash and
  ;; believes the membership CxB takes OUT.
  (with-release-kb
    (fn [kb {:keys [CxC] :as ts}]
      (let [steps (release-steps kb ts :below)]
        (doseq [k [:wiring :chi]] ((steps k)))
        (v/assert kb (list 'except (list 'sentexHandle ((:cat steps)))) CxC)
        (is (= {:CxB [false true true] :CxC [true false true]} (release-reading kb ts)))))))

(defn- shared-defeat-reading
  "Build the lattice of the test below with its four writes in `order`, then `(except
  winner)` in CxR, where `winner` is `:dog` or `:not`.  Answers `[CxD believes L, CxR
  believes L, the defeats of L stored at CxD]`."
  [order winner]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [CxD CxR cat dog Rex]
      (types! kb cat dog)
      (v/assert kb (list 'genlCx CxD 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxR CxD) 'CxUniverse)
      (let [hs (into {} (for [w order]
                          [w (case w
                               :cat      (v/assert kb (list cat Rex) CxD)
                               :dog      (v/assert kb (list dog Rex) CxD {:strength :monotonic})
                               :not      (v/assert kb (list 'not (list cat Rex)) CxD
                                                   {:strength :monotonic})
                               :disjoint (v/assert kb (list 'disjoint dog cat) 'CxUniverse))]))
            l  (hs :cat)]
        (v/assert kb (list 'except (list 'sentexHandle (hs winner))) CxR)
        (verdicts-agree! kb [CxD CxR])
        [(v/believed? kb l CxD) (v/believed? kb l CxR)
         (count (v/sentexes-matching kb (list 'defeat (list 'sentexHandle l)) CxD))]))))

(defn- shared-defeat-orders-agree [orders]
  (doseq [winner [:dog :not]]
    (is (= #{[false false 1]} (into #{} (map #(shared-defeat-reading % winner)) orders))
        (pr-str winner))))

;;   CxUniverse  (disjoint dog cat)
;;     └─ CxD    L (cat Rex) default, W1 (dog Rex) monotonic, W2 (not (cat Rex)) monotonic
;;          └─ CxR   (except W1) or (except W2), written last
;;
;; The membership nogood {W1 L} and the negation nogood {W2 L} store one defeat of L at
;; CxD with one justification each.  CxR excepts one winner; the other nogood still
;; convicts L there, whichever nogood is placed first.  The sample takes every fourth of
;; the 24 orders, which places each nogood first at least once.

(deftest a-defeat-two-nogoods-share-is-in-force-through-either-one
  (shared-defeat-orders-agree (take-nth 4 (permutations [:cat :dog :not :disjoint]))))

(deftest ^:slow a-defeat-two-nogoods-share-is-in-force-through-either-one-in-every-order
  (shared-defeat-orders-agree (permutations [:cat :dog :not :disjoint])))

(deftest a-sibling-exception-releases-the-pair-at-the-readers-that-see-it
  ;;   CxUniverse  (genl t1 col) (genl t2 col) (sibling_disjoint col)
  ;;     └─ CxB    (t1 Pip) default  (t2 Pip) monotonic
  ;;          └─ CxC
  ;;   CxE         sees CxUniverse and is seen by nothing
  ;;
  ;; The exception exempts the pair at the contexts that see it: written in CxC it releases
  ;; the pair at CxC and leaves CxB deciding it; written in CxE it releases the pair at CxE
  ;; alone.
  (doseq [[place dj believed]
          [[nil  {:CxB true :CxC true :CxE true}   {:CxB [false true] :CxC [false true]}]
           [:CxC {:CxB true :CxC false :CxE true}  {:CxB [false true] :CxC [true true]}]
           [:CxE {:CxB true :CxC true :CxE false}  {:CxB [false true] :CxC [false true]}]]]
    (tu/with-neutral-kb [kb tu/fresh]
      (tu/with-terms [CxB CxC CxE col t1 t2 Pip]
        (types! kb col)
        (v/assert kb (list 'genl t1 col) 'CxUniverse)
        (v/assert kb (list 'genl t2 col) 'CxUniverse)
        (v/assert kb (list 'sibling_disjoint col) 'CxUniverse {:strength :monotonic})
        (doseq [[k up] [[CxB 'CxUniverse] [CxC CxB] [CxE 'CxUniverse]]]
          (v/assert kb (list 'genlCx k up) 'CxUniverse))
        (v/assert kb (list t1 Pip) CxB)
        (v/assert kb (list t2 Pip) CxB {:strength :monotonic})
        (when place
          (v/assert kb (list 'siblingDisjointException t1 t2) ({:CxC CxC :CxE CxE} place)))
        (let [cx {:CxB CxB :CxC CxC :CxE CxE}]
          (is (= dj (into {} (for [[k c] cx] [k (v/disjoint? kb t1 t2 c)]))) (pr-str place))
          (is (= believed (into {} (for [k [:CxB :CxC]]
                                     [k [(v/ask? kb (list t1 Pip) (cx k))
                                         (v/ask? kb (list t2 Pip) (cx k))]])))
              (pr-str place)))))))

;; ---- a separation only a context below the members' maximum can see ----
;;
;;   CxUniverse   (genl t1 thing) (genl t2 thing)
;;     ├─ CxA     (t1 Pip) monotonic
;;     ├─ CxB     (t2 Pip) default
;;     └─ CxDecl  (disjoint t1 t2)
;;   CxW sees CxA and CxB       — the members' maximal common descendant; no separation
;;     ├─ CxX sees CxW          — a reader below CxW and outside CxV
;;     └─ CxV sees CxW, CxDecl  — sees the whole clash: the vantage
;;          └─ CxY sees CxV
;;
;; The vantage is the most general context seeing the members *and* the separation, so
;; CxV decides the pair and CxW, which reads no separation, keeps both memberships.

(defn- deep-steps
  "The lattice above as named steps, over the terms in `ts`.  `:reveal` is the edge that
  puts the separation in CxV's view, apart from `:edges` so it can arrive last."
  [kb {:keys [CxA CxB CxDecl CxW CxX CxV CxY t1 t2 Pip]}]
  {:types  #(types! kb t1 t2)
   :edges  #(doseq [[k up] [[CxA 'CxUniverse] [CxB 'CxUniverse] [CxDecl 'CxUniverse]
                            [CxW CxA] [CxW CxB] [CxX CxW] [CxV CxW] [CxY CxV]]]
              (v/assert kb (list 'genlCx k up) 'CxUniverse))
   :reveal #(v/assert kb (list 'genlCx CxV CxDecl) 'CxUniverse)
   :a      #(v/assert kb (list t1 Pip) CxA {:strength :monotonic})
   :b      #(v/assert kb (list t2 Pip) CxB)
   :decl   #(v/assert kb (list 'disjoint t1 t2) CxDecl)})

(defn- deep-reading
  "What each reader believes of the two memberships, whether it reads a dilemma, and the
  `:disjoint` entries on the ledger — keyed by the reader's place in the lattice, since
  the context symbols are fresh per run."
  [kb {:keys [t1 t2 Pip] :as ts}]
  {:beliefs  (into {} (for [r [:CxA :CxB :CxW :CxX :CxV :CxY]
                            :let [cx (ts r)]]
                        [r [(v/ask? kb (list t1 Pip) cx) (v/ask? kb (list t2 Pip) cx)]]))
   :dilemmas (into #{} (filter #(seq (v/contradictions kb (ts %))))
                   [:CxW :CxX :CxV :CxY])
   :reported (count (filter #(= :disjoint (:violation %)) (v/violations kb)))})

(defn- deep-run [build order]
  (tu/with-neutral-kb [kb build]
    (tu/with-terms [CxA CxB CxDecl CxW CxX CxV CxY t1 t2 Pip]
      (let [ts    {:CxA CxA :CxB CxB :CxDecl CxDecl :CxW CxW :CxX CxX :CxV CxV :CxY CxY
                   :t1 t1 :t2 t2 :Pip Pip}
            steps (deep-steps kb ts)]
        (doseq [k order] ((steps k)))
        (verdicts-agree! kb [CxA CxB CxDecl CxW CxX CxV CxY])
        (deep-reading kb ts)))))

(def ^:private deep-decided
  {:beliefs  {:CxA [true false] :CxB [false true]
              :CxW [true true]  :CxX [true true]
              :CxV [true false] :CxY [true false]}
   :dilemmas #{}
   :reported 0})

(defn- deep-orders-agree [orders]
  (doseq [order orders]
    (is (= deep-decided (deep-run tu/fresh order))
        (pr-str order))))

(deftest a-separation-only-a-lower-context-sees-is-decided-there
  ;; Every order of the four ingredients the lattice turns on, with the vocabulary and
  ;; the wiring first; the slow twin moves the wiring too.
  (deep-orders-agree (map #(into [:types :edges] %) (permutations [:a :b :decl :reveal]))))

(deftest ^:slow a-separation-only-a-lower-context-sees-is-decided-there-in-every-order
  (deep-orders-agree (map #(into [:types] %) (permutations [:edges :a :b :decl :reveal]))))

(deftest a-separation-only-a-lower-context-sees-leaves-a-dilemma-there-alone
  ;; Both memberships default: CxV cannot rank them, so the pair is a dilemma for CxV
  ;; and the reader below it, and no dilemma for CxW or CxX, which read no separation.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [CxA CxB CxDecl CxW CxX CxV CxY t1 t2 Pip]
      (let [ts    {:CxA CxA :CxB CxB :CxDecl CxDecl :CxW CxW :CxX CxX :CxV CxV :CxY CxY
                   :t1 t1 :t2 t2 :Pip Pip}
            steps (assoc (deep-steps kb ts) :a #(v/assert kb (list t1 Pip) CxA))]
        (doseq [k [:types :edges :a :b :decl :reveal]] ((steps k)))
        (let [r (deep-reading kb ts)]
          (is (= {:CxW [true true] :CxX [true true] :CxV [true true] :CxY [true true]}
                 (select-keys (:beliefs r) [:CxW :CxX :CxV :CxY])))
          (is (= #{:CxV :CxY} (:dilemmas r)))
          (is (zero? (:reported r))))))))

(deftest retracting-a-separation-only-a-lower-context-sees-returns-every-reader
  ;; The retraction returns each reader to what the KB that never held the declaration
  ;; reads.
  (let [without (deep-run tu/fresh [:types :edges :reveal :a :b])]
    (is (= {:CxA [true false] :CxB [false true] :CxW [true true] :CxX [true true]
            :CxV [true true] :CxY [true true]}
           (:beliefs without)))
    (tu/with-neutral-kb [kb tu/fresh]
      (tu/with-terms [CxA CxB CxDecl CxW CxX CxV CxY t1 t2 Pip]
        (let [ts    {:CxA CxA :CxB CxB :CxDecl CxDecl :CxW CxW :CxX CxX :CxV CxV :CxY CxY
                     :t1 t1 :t2 t2 :Pip Pip}
              steps (deep-steps kb ts)]
          (doseq [k [:types :edges :reveal :a :b :decl]] ((steps k)))
          (is (= deep-decided (deep-reading kb ts)) "decided while the declaration stands")
          (v/retract! kb (v/handle-of kb (list 'disjoint t1 t2) CxDecl))
          (is (= without (deep-reading kb ts)) "and every reader returns once it goes"))))))

(deftest every-kind-of-clash-is-decided-where-its-grounds-come-into-view
  ;; The same lattice for each ground a vantage can be missing: a `disjoint` declaration,
  ;; the `genl` edge that puts a type under a separated one, a `functional` mark and an
  ;; `asymmetric` mark.  The vocabulary a clash also needs sits in CxA, which CxW sees.
  ;; `a` is monotonic and `b` default, so CxV defeats `b`.
  (doseq [kind [:disjoint :genl-path :functional :asymmetric]]
    (testing (name kind)
      (tu/with-neutral-kb [kb tu/fresh]
        (tu/with-terms [CxA CxB CxDecl CxW CxX CxV t0 t1 t2 ageOf aboveOf Pip Pop]
          (let [[a b ground vocab]
                (case kind
                  :disjoint   [(list t1 Pip) (list t2 Pip) (list 'disjoint t1 t2)
                               [(list 'genl t1 'thing) (list 'genl t2 'thing)]]
                  :genl-path  [(list t1 Pip) (list t2 Pip) (list 'genl t1 t0)
                               [(list 'genl t0 'thing) (list 'genl t1 'thing)
                                (list 'genl t2 'thing) (list 'disjoint t0 t2)]]
                  :functional [(list ageOf Pip 3) (list ageOf Pip 4) (list 'functional ageOf)
                               [(list 'binary_predicate ageOf)]]
                  :asymmetric [(list aboveOf Pip Pop) (list aboveOf Pop Pip)
                               (list 'asymmetric aboveOf)
                               [(list 'binary_predicate aboveOf)]])]
            (doseq [[k up] [[CxA 'CxUniverse] [CxB 'CxUniverse] [CxDecl 'CxUniverse]
                            [CxW CxA] [CxW CxB] [CxX CxW] [CxV CxW] [CxV CxDecl]]]
              (v/assert kb (list 'genlCx k up) 'CxUniverse))
            (doseq [s vocab] (v/assert kb s CxA))
            (v/assert kb a CxA {:strength :monotonic})
            (v/assert kb b CxB)
            (v/assert kb ground CxDecl)
            (is (= {:CxW [true true] :CxX [true true] :CxV [true false]}
                   (into {} (for [[r cx] [[:CxW CxW] [:CxX CxX] [:CxV CxV]]]
                              [r [(v/ask? kb a cx) (v/ask? kb b cx)]]))))))))))

(deftest a-separation-declared-below-the-maximum-is-decided-where-it-is-declared
  ;;   CxA (t1 Pip) monotonic     CxB (t2 Pip) default
  ;;   CxW sees CxA and CxB
  ;;     ├─ CxX sees CxW, and holds (disjoint t1 t2)
  ;;     │    └─ CxY sees CxX
  ;;     └─ CxZ0 … CxZ3 see CxW
  ;; The ground sits inside the members' common descendants rather than beside them, so
  ;; the reader that first sees it is the context holding it.
  (doseq [order (permutations [:a :b :decl])]
    (tu/with-neutral-kb [kb tu/fresh]
      (tu/with-terms [CxA CxB CxW CxX CxY CxZ0 CxZ1 CxZ2 CxZ3 t1 t2 Pip]
        (types! kb t1 t2)
        (doseq [[k up] [[CxA 'CxUniverse] [CxB 'CxUniverse] [CxW CxA] [CxW CxB]
                        [CxX CxW] [CxY CxX] [CxZ0 CxW] [CxZ1 CxW] [CxZ2 CxW] [CxZ3 CxW]]]
          (v/assert kb (list 'genlCx k up) 'CxUniverse))
        (doseq [k order]
          (case k
            :a    (v/assert kb (list t1 Pip) CxA {:strength :monotonic})
            :b    (v/assert kb (list t2 Pip) CxB)
            :decl (v/assert kb (list 'disjoint t1 t2) CxX)))
        (is (= {:CxW [true true] :CxZ0 [true true] :CxZ3 [true true]
                :CxX [true false] :CxY [true false]}
               (into {} (for [[r cx] [[:CxW CxW] [:CxZ0 CxZ0] [:CxZ3 CxZ3] [:CxX CxX] [:CxY CxY]]]
                          [r [(v/ask? kb (list t1 Pip) cx) (v/ask? kb (list t2 Pip) cx)]])))
            (pr-str order))))))

;; ---- a clash of more than two members ---------------------------------------
;;
;;   CxUniverse  (binary_predicate nearP), (anti_transitive nearP)
;;     ├─ CxA  (nearP Aa Bb) monotonic
;;     ├─ CxB  (nearP Bb Cc) monotonic
;;     └─ CxC  (nearP Aa Cc) default
;;   CxAB sees CxA and CxB, CxBC sees CxB and CxC, CxAC sees CxA and CxC
;;     └─ CxW sees CxAB, CxBC and CxAC
;;
;; Each pair reader sees two steps and reads no chain; CxW sees all three.

(defn- chain-steps
  "The lattice above as named steps.  `:mark` is the `anti_transitive` declaration, apart
  from the rest of the vocabulary so it can arrive after the tuples."
  [kb {:keys [CxA CxB CxC CxAB CxBC CxAC CxW nearP Aa Bb Cc]}]
  {:edges #(do (doseq [[k up] [[CxA 'CxUniverse] [CxB 'CxUniverse] [CxC 'CxUniverse]
                               [CxAB CxA] [CxAB CxB] [CxBC CxB] [CxBC CxC]
                               [CxAC CxA] [CxAC CxC] [CxW CxAB] [CxW CxBC] [CxW CxAC]]]
                 (v/assert kb (list 'genlCx k up) 'CxUniverse))
               (v/assert kb (list 'binary_predicate nearP) 'CxUniverse))
   :mark  #(v/assert kb (list 'anti_transitive nearP) 'CxUniverse)
   :ab    #(v/assert kb (list nearP Aa Bb) CxA {:strength :monotonic})
   :bc    #(v/assert kb (list nearP Bb Cc) CxB {:strength :monotonic})
   :ac    #(v/assert kb (list nearP Aa Cc) CxC)})

(defn- chain-reading
  "What each reader of two or three steps believes of the three tuples, and which of them
  reads a dilemma."
  [kb {:keys [nearP Aa Bb Cc] :as ts}]
  {:beliefs  (into {} (for [r [:CxAB :CxBC :CxAC :CxW]]
                        [r (mapv #(v/ask? kb % (ts r))
                                 [(list nearP Aa Bb) (list nearP Bb Cc) (list nearP Aa Cc)])]))
   :dilemmas (into #{} (filter #(seq (v/contradictions kb (ts %))))
                   [:CxAB :CxBC :CxAC :CxW])})

(defn- chain-run [build order overrides]
  (tu/with-neutral-kb [kb build]
    (tu/with-terms [CxA CxB CxC CxAB CxBC CxAC CxW nearP Aa Bb Cc]
      (let [ts    {:CxA CxA :CxB CxB :CxC CxC :CxAB CxAB :CxBC CxBC :CxAC CxAC :CxW CxW
                   :nearP nearP :Aa Aa :Bb Bb :Cc Cc}
            steps (merge (chain-steps kb ts) (overrides kb ts))]
        (doseq [k order] ((steps k)))
        (verdicts-agree! kb [CxA CxB CxC CxAB CxBC CxAC CxW])
        (chain-reading kb ts)))))

(def ^:private chain-decided
  {:beliefs  {:CxAB [true true false] :CxBC [false true true] :CxAC [true false true]
              :CxW  [true true false]}
   :dilemmas #{}})

(defn- chain-orders-agree [orders]
  (doseq [order orders]
    (is (= chain-decided (chain-run tu/fresh order (constantly {}))) (pr-str order))))

(deftest a-chain-whose-steps-sit-in-three-contexts-is-decided-where-all-three-are-seen
  (chain-orders-agree (map #(into [:edges] %) (permutations [:mark :ab :bc :ac]))))

(deftest ^:slow a-chain-whose-steps-sit-in-three-contexts-is-decided-in-every-order
  ;; the wiring moves too; the predicate's arity declaration rides with it
  (chain-orders-agree (permutations [:edges :mark :ab :bc :ac])))

(deftest a-chain-whose-steps-sit-in-three-contexts-reads-as-one-context-reads-it
  ;; The three tuples in one context: what that context believes is what CxW believes of
  ;; the split chain.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [CxA nearP Aa Bb Cc]
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'binary_predicate nearP) 'CxUniverse)
      (v/assert kb (list 'anti_transitive nearP) 'CxUniverse)
      (v/assert kb (list nearP Aa Bb) CxA {:strength :monotonic})
      (v/assert kb (list nearP Bb Cc) CxA {:strength :monotonic})
      (try (v/assert kb (list nearP Aa Cc) CxA) (catch clojure.lang.ExceptionInfo _))
      (is (= (get-in chain-decided [:beliefs :CxW])
             (mapv #(v/ask? kb % CxA)
                   [(list nearP Aa Bb) (list nearP Bb Cc) (list nearP Aa Cc)]))))))

(deftest a-chain-whose-steps-sit-in-three-contexts-is-a-dilemma-where-all-three-are-seen
  ;; `(nearP Bb Cc)` default too: two defaults share the floor, so CxW reads a dilemma of
  ;; three and every reader keeps every step it sees.
  (let [r (chain-run tu/fresh [:edges :mark :ab :bc :ac]
                     (fn [kb {:keys [CxB nearP Bb Cc]}]
                       {:bc #(v/assert kb (list nearP Bb Cc) CxB)}))]
    (is (= {:CxAB [true true false] :CxBC [false true true] :CxAC [true false true]
            :CxW  [true true true]}
           (:beliefs r)))
    (is (= #{:CxW} (:dilemmas r)))))

;; ---- an inherited clash across contexts --------------------------------------
;;
;;   CxUniverse  bigP binary, a type_relation_predicate, asymmetric, and preserved along
;;               genl at both positions; monotonic
;;     ├─ CxA     (bigP mammal insect) monotonic
;;     ├─ CxB     the stored claim: (bigP ant dog), or (not (bigP dog insect)); default
;;     └─ CxDecl
;;   CxW sees CxA and CxB
;;     └─ CxV sees CxW and CxDecl
;;   (genl dog mammal) and (genl ant insect), monotonic, in CxA, CxB or CxDecl
;;   (`:grounds :default` asserts the declarations and the edges at the default strength;
;;   `:detour` routes dog to mammal through canine, monotonic, and writes the direct edge
;;   `:default`, `:first` or `:last` of all)
;;
;; `(bigP mammal insect)` reaches `(bigP dog ant)` and `(bigP dog insect)` wherever both
;; edges are seen, so a reader seeing the claim, the edges and the stored claim reads the
;; clash, and one context holding all of it reads it too.

(defn- inherit-run
  "Build the lattice above with the stored claim `stored` in `stored-in` and the edges in
  `edges-in` — roles, resolved against the run's terms — and answer, per reader, the
  stored claim and the tuple it denies, and whether the reader reads a dilemma."
  [build {:keys [stored stored-in edges-in claim-first? grounds detour]
          :or {grounds :monotonic}}]
  (tu/with-neutral-kb [kb build]
    (tu/with-terms [CxA CxB CxDecl CxW CxV bigP mammal_t insect_t dog_t ant_t canine_t]
      (let [cx      {:CxA CxA :CxB CxB :CxDecl CxDecl :CxW CxW :CxV CxV}
            M       {:strength :monotonic}
            G       {:strength grounds}
            [s q]   (case stored
                      :converse [(list bigP ant_t dog_t) (list bigP dog_t ant_t)]
                      :denial   [(list 'not (list bigP dog_t insect_t)) (list bigP dog_t insect_t)])
            claim   #(v/assert kb (list bigP mammal_t insect_t) CxA M)
            write-s #(try (v/assert kb s (cx stored-in)) (catch clojure.lang.ExceptionInfo _))
            direct  #(v/assert kb (list 'genl dog_t mammal_t) (cx edges-in)
                               (if detour {} G))]
        (doseq [[k up] [[CxA 'CxUniverse] [CxB 'CxUniverse] [CxDecl 'CxUniverse]
                        [CxW CxA] [CxW CxB] [CxV CxW] [CxV CxDecl]]]
          (v/assert kb (list 'genlCx k up) 'CxUniverse))
        (types! kb mammal_t insect_t dog_t ant_t canine_t)
        (doseq [d [(list 'binary_predicate bigP) (list 'type_relation_predicate bigP)
                   (list 'asymmetric bigP)
                   (list 'transitiveInArgInverse bigP 1 'genl) (list 'transitiveInArgInverse bigP 2 'genl)]]
          (v/assert kb d 'CxUniverse G))
        (when detour
          (v/assert kb (list 'genl dog_t canine_t) (cx edges-in) G)
          (v/assert kb (list 'genl canine_t mammal_t) (cx edges-in) G))
        (when-not (= :last detour) (direct))
        (v/assert kb (list 'genl ant_t insect_t) (cx edges-in) G)
        (if claim-first? (do (claim) (write-s)) (do (write-s) (claim)))
        (when (= :last detour) (direct))
        (verdicts-agree! kb (vals cx))
        (into {} (for [r (distinct [stored-in :CxW :CxV])]
                   [r [(v/ask? kb s (cx r)) (v/ask? kb q (cx r))
                       (boolean (seq (v/contradictions kb (cx r))))]]))))))

(deftest an-inherited-clash-across-contexts-is-decided-where-the-claim-comes-into-view
  ;; CxW sees the claim, the edges and the stored claim: the stored default loses there,
  ;; and CxB, which cannot see the general claim, keeps it.
  (doseq [stored   [:converse :denial]
          edges-in [:CxA :CxB]
          first?   [true false]
          :let [opts {:stored stored :stored-in :CxB :edges-in edges-in :claim-first? first?}]]
    (is (= {:CxB [true false false] :CxW [false true false] :CxV [false true false]}
           (inherit-run tu/fresh opts))
        (pr-str opts))))

(deftest an-inherited-clash-across-contexts-reads-as-one-context-reads-it
  ;; Everything in CxA: what CxW reads is what the split KB reads at CxW.
  (doseq [stored [:converse :denial]
          first? [true false]
          :let [opts {:stored stored :stored-in :CxA :edges-in :CxA :claim-first? first?}]]
    (is (= [false true false] (:CxW (inherit-run tu/fresh opts)))
        (pr-str opts))))

(deftest an-inherited-clash-whose-edges-only-a-lower-context-sees-is-decided-there
  ;; The edges in CxDecl: CxW reads no reach and so no clash, and keeps the stored claim;
  ;; CxV reads the whole clash and decides it.
  (doseq [stored [:converse :denial]
          first? [true false]
          :let [opts {:stored stored :stored-in :CxB :edges-in :CxDecl :claim-first? first?}]]
    (is (= {:CxB [true false false] :CxW [true false false] :CxV [false true false]}
           (inherit-run tu/fresh opts))
        (pr-str opts))))

(deftest an-inherited-claim-opposes-at-its-strongest-reading-in-every-order
  ;; A `:default` direct edge beside a known-true route through canine: the claim is read
  ;; over the known-true route, so the stored default loses wherever the whole clash is
  ;; seen, the direct edge written first or last.
  (doseq [stored [:converse :denial]
          detour [:first :last]
          first? [true false]
          [stored-in expected] [[:CxA {:CxA [false true false] :CxW [false true false]
                                       :CxV [false true false]}]
                                [:CxB {:CxB [true false false] :CxW [false true false]
                                       :CxV [false true false]}]]
          :let [opts {:stored stored :stored-in stored-in :edges-in :CxA :claim-first? first?
                      :detour detour}]]
    (is (= expected (inherit-run tu/fresh opts)) (pr-str opts))))

(deftest an-inherited-converse-over-default-grounds-opposes-nothing-in-every-order
  ;; The declarations and the edges `:default`: the reading is `:default`, so the stored
  ;; claim undercuts it, and the reader that sees the whole reach believes the stored
  ;; claim and reads no clash whichever claim arrives first — one context or split across
  ;; two (docs/inherit.md, "A contrary claim against a known-true one").
  (doseq [stored [:converse :denial]
          [stored-in reader] [[:CxA :CxA] [:CxB :CxW]]
          first? [true false]
          :let [opts {:stored stored :stored-in stored-in :edges-in :CxA :claim-first? first?
                      :grounds :default}]]
    (is (= [true false false] (get (inherit-run tu/fresh opts) reader))
        (pr-str opts))))
