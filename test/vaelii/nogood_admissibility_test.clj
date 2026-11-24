;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.nogood-admissibility-test
  "Which handles a nogood may name, and why the answer differs per source.

  A nogood is a set the settle may resolve by **defeating a member**, so admission to
  the set is a stronger question than incompatibility: a nogood must stay derivable
  exactly as long as what it convicts stands (docs/nmtms.md, *What qualifies as a
  nogood*).  The failure it is drawn from is a member the conviction is read *through* —
  defeat that and the clash becomes undetectable while the content it convicted goes on
  standing, so it is decided once and re-derived by nobody.

  The criterion is only a runtime property in one place: **which handles a source puts
  in `:nogood`**.  So that is what this asserts, for all three shipped sources, together
  with the consequence that makes the assertion matter — that acting on a definitional clash
  leaves the vocabulary that convicted it believed, and therefore leaves the verdict
  stable across the settles that follow.

  The three answers are deliberately not the same, which is why a test that assumed one
  rule for all three would be wrong:

  * a **rebuttal** names the two claims;
  * a **definitional clash** names the clashing sentexes and *not* the declaration,
    which is vocabulary read through;
  * an **inherited clash** names the stored claim *and its reasons*, because the claim
    it convicts has no sentex of its own for a defeat to reach instead.

  `constraint_nogood_test` and `inherited_clash_test` own the behaviour of each source;
  this namespace owns the one property that spans them."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(def ^:private U 'CxUniverse)
(def ^:private mono {:strength :monotonic})

(defn- the-clash
  "The single standing clash of either reading, or a failure if there is not exactly one."
  [kb]
  (let [cs (concat (v/conflicts kb) (v/contradictions kb))]
    (is (= 1 (count cs)) "exactly one clash is expected in this KB")
    (first cs)))

;; ---- a rebuttal names the two claims ------------------------------------

(tu/deftest-kb a-rebuttals-members-are-the-two-claims-and-nothing-else
  ;; The baseline shape.  A negation pair is read through joint visibility to decide
  ;; whether it clashes at all, and no member supports that verdict — so defeating either
  ;; side removes one of the two claims the pair was about, which is the whole of what
  ;; the criterion asks.
  (tu/with-terms [flies Tweety]
    (v/assert kb (list flies Tweety) U)
    (v/assert kb (list 'not (list flies Tweety)) U)
    (let [c (the-clash kb)]
      (is (= #{(v/handle-of kb (list flies Tweety) U)
               (v/handle-of kb (list 'not (list flies Tweety)) U)}
             (:nogood c))
          "a rebuttal names the two claims"))))

;; ---- a definitional clash does not name the declaration -----------------

(tu/deftest-kb a-definitional-clashs-members-exclude-the-declaration-it-was-read-through
  ;; The criterion's live case.  `(disjoint A B)` is what convicts the pair, and it is
  ;; read through `clash-vocabulary` rather than weighed with the members: putting it in
  ;; the set would let `decide/verdict` defeat it, after which nothing could look at the
  ;; pair again and both memberships would stand unconvicted.
  (tu/with-kb [kb]
    (tu/with-terms [dog_t fish_t Rex]
      (v/assert kb (list 'disjoint dog_t fish_t) U)
      (v/assert kb (list dog_t Rex) U)
      (v/assert kb (list fish_t Rex) U)
      (let [c    (the-clash kb)
            decl (v/handle-of kb (list 'disjoint dog_t fish_t) U)]
        (is (= :disjoint (:kind c)))
        (is (= #{(v/handle-of kb (list dog_t Rex) U)
                 (v/handle-of kb (list fish_t Rex) U)}
               (:nogood c))
            "the members are the two memberships")
        (is (not (contains? (:nogood c) decl))
            "the declaration convicts the pair; it is not one of the convicted")
        (is (v/believed? kb decl)
            "and it is believed, which is what makes the conviction re-derivable")))))

(tu/deftest-kb acting-on-a-definitional-clash-leaves-its-verdict-stable
  ;; What the exclusion buys, stated as behaviour rather than as membership.  With one
  ;; side known-true the settle has a unique weakest member and defeats it; the
  ;; declaration is untouched, so every settle that follows reaches the same verdict
  ;; rather than reviving the loser into a clash nothing can detect any more.
  ;;
  ;; The known-true side arrives **second** on purpose: arbitration refuses a claim
  ;; against content already known true (`constraint_nogood_test`), so this is the
  ;; arrival that leaves the settle a strength-differentiated pair to decide rather than
  ;; a writer to turn away.
  (tu/with-kb [kb]
    (tu/with-terms [dog_t fish_t Rex Bystander]
      (v/assert kb (list 'disjoint dog_t fish_t) U)
      (v/assert kb (list fish_t Rex) U)
      (v/assert kb (list dog_t Rex) U mono)
      (let [decl   (v/handle-of kb (list 'disjoint dog_t fish_t) U)
            winner (v/handle-of kb (list dog_t Rex) U)
            loser  (v/handle-of kb (list fish_t Rex) U)]
        (testing "the weakest member loses, and only it"
          (is (v/believed? kb winner))
          (is (not (v/believed? kb loser)))
          (is (v/believed? kb decl) "the declaration is not a member, so nothing defeats it"))
        (testing "and the verdict survives the settles that follow"
          ;; every assert re-settles, and the reader decides the pair again from
          ;; current state.  A declaration defeated along with the loser would leave
          ;; nothing able to do that.
          (dotimes [_ 3] (v/assert kb (list dog_t Bystander) U))
          (is (v/believed? kb decl))
          (is (v/believed? kb winner))
          (is (not (v/believed? kb loser))
              "the loser came back, so the clash stopped being derivable"))))))

;; ---- an inherited clash names its reasons, deliberately -----------------

(tu/deftest-kb an-inherited-clashs-members-include-the-reasons-it-was-read-through
  ;; The case that fixes the wording.  Here the reasons ARE members: the claim on the
  ;; other side was never stored, so its reasons are what the pair is about.  Every
  ;; sentence is known-true, since a reading with a `:default` reason opposes nothing, so
  ;; the clash is a conflict.
  (tu/with-terms [carriesLoad hauler_kind cart_kind]
    (v/assert kb (list 'binary_predicate carriesLoad) U)
    (v/assert kb (list 'transitiveInArgInverse carriesLoad 1 'genl) U mono)
    (v/assert kb (list 'genl hauler_kind 'animal) U)
    (v/assert kb (list 'genl cart_kind hauler_kind) U mono)
    (v/assert kb (list carriesLoad hauler_kind 'Bone1) U mono)
    (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) U mono)
    (let [c     (the-clash kb)
          claim (v/handle-of kb (list carriesLoad hauler_kind 'Bone1) U)
          decl  (v/handle-of kb (list 'transitiveInArgInverse carriesLoad 1 'genl) U)
          edge  (v/handle-of kb (list 'genl cart_kind hauler_kind) U)
          deny  (v/handle-of kb (list 'not (list carriesLoad cart_kind 'Bone1)) U)]
      (is (= :inherited (:kind c)))
      (testing "the stored claim and the general claim are members"
        (is (contains? (:nogood c) deny))
        (is (contains? (:nogood c) claim)))
      (testing "and so is everything the reading rests on — the exception the criterion names"
        (is (contains? (:nogood c) decl) "the declaration permitting the move")
        (is (contains? (:nogood c) edge)  "the relation edge the reach travelled")
        (is (= (set (:via (:inherited c))) #{decl edge})
            "`:via` and the members agree about what licensed the reach")))))
