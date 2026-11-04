;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.attitude-opacity-test
  "Attitude opacity — docs/belief.md, docs/equality.md.

  A `modal_predicate`'s proposition is a **mention**: what the *agent* holds true, named
  as syntax.  From *Oedipus believes he married Jocasta* and *Jocasta is his mother* it
  does not follow that he believes he married his mother, so an identity merge the asker
  can see must not rewrite a term inside `(believes Oedipus …)`.  The merge the *agent*
  holds does license it, and licenses it for that agent alone.

  Two halves, and they are separate mechanisms.  The **barrier** is congruence opacity in
  `res/representative-term`, which every read entry point and every migration goes through — so
  the question and the stored belief hold still together, and neither can retrieve what
  the other renamed.  The **licence** is `BeliefProjectionProver`, which normalizes the
  projected proposition against the agent's own partition, the ordinary rule that the
  reader is what elects, applied to the reader a projection actually has.

  The agent slot is *not* part of the quotation: it is a term the asker refers with, so
  merging two names for one agent is one agent under two names.  Nor is a non-sentence
  argument one, nor a predicate nobody granted the marker to."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.modal :as modal]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(def ^:private ask-ctx
  "Where the asker stands.  An agent context carries no `genlCx` edge to CxWell by
  default, so nothing asserted here reaches an agent that has not opted in — which is the
  configuration the unsoundness needed, and the one most of these tests hold."
  'CxWell)

(defn- loser
  "Whichever of `a` / `b` the partition did **not** elect, as `ask-ctx` sees it.  The
  election is content-keyed, so a test that hard-codes the retired spelling passes
  vacuously half the time; this asks."
  [kb a b]
  (if (= a (kb/rewrite-goal kb a ask-ctx)) b a))

;; ---- the headline: the asker's merge stops at the quotation ---------------

(tu/deftest-kb an-askers-merge-does-not-rewrite-what-an-agent-believes
  (tu/with-terms [Oedipus Jocasta MotherOf marriedTo]
    (let [actx    (modal/context-of-agent Oedipus)
          married (fn [who] (list 'believes Oedipus (list marriedTo Oedipus who)))]
      (v/assert kb (list marriedTo Oedipus Jocasta) actx)
      (testing "before any merge he believes the one and not the other"
        (is (v/ask? kb (married Jocasta) ask-ctx))
        (is (not (v/ask? kb (married MotherOf) ask-ctx))))
      (v/assert kb (list 'sameAs Jocasta MotherOf) ask-ctx)   ; the *asker* learns it
      (testing "and the asker learning the identity changes neither answer"
        (is (not (v/ask? kb (married MotherOf) ask-ctx))
            "the tragedy: he does not believe he married his mother")
        (is (v/ask? kb (married Jocasta) ask-ctx)
            "and the belief he does hold is still reachable under its own spelling")))))

(tu/deftest-kb an-identity-the-agent-holds-licenses-substitution-and-only-for-them
  (tu/with-terms [Oedipus Creon Jocasta MotherOf marriedTo]
    (let [oc (modal/context-of-agent Oedipus)
          cc (modal/context-of-agent Creon)]
      (v/assert kb (list marriedTo Oedipus Jocasta) oc)
      (v/assert kb (list marriedTo Creon   Jocasta) cc)
      (v/assert kb (list 'sameAs Jocasta MotherOf)  oc)      ; the *agent* holds it
      (testing "the agent's own merge licenses the substitution inside his belief"
        (is (v/ask? kb (list 'believes Oedipus (list marriedTo Oedipus MotherOf)) ask-ctx))
        (is (v/ask? kb (list 'believes Oedipus (list marriedTo Oedipus Jocasta))  ask-ctx)
            "under either spelling, since for him they are one term"))
      (testing "and licenses it for him alone"
        (is (not (v/ask? kb (list 'believes Creon (list marriedTo Creon MotherOf)) ask-ctx)))
        (is (v/ask? kb (list 'believes Creon (list marriedTo Creon Jocasta)) ask-ctx))))))

(tu/deftest-kb retracting-the-agents-merge-restores-the-pre-merge-answer
  (tu/with-terms [Oedipus Jocasta MotherOf marriedTo]
    (let [oc (modal/context-of-agent Oedipus)
          g  (list 'believes Oedipus (list marriedTo Oedipus MotherOf))]
      (v/assert kb (list marriedTo Oedipus Jocasta) oc)
      (v/assert kb (list 'sameAs Jocasta MotherOf)  oc)
      (is (v/ask? kb g ask-ctx))
      (v/retract! kb (v/handle-of kb (list 'sameAs Jocasta MotherOf) oc))
      (is (not (v/ask? kb g ask-ctx))
          "the licence goes with the identity that granted it"))))

(tu/deftest-kb an-agent-wired-to-base-does-inherit-the-merges-base-states
  ;; The common configuration, and the one that says the barrier is not too wide.  An agent
  ;; context is independent by default and opts into base with a `genlCx` edge; the agent
  ;; then sees every merge that context states, so the identity is one the agent holds and
  ;; the substitution is correct.  This is also the migration route out of the old answer.
  (tu/with-terms [Oedipus Jocasta MotherOf marriedTo]
    (let [oc (modal/context-of-agent Oedipus)]
      (v/assert kb (list 'genlCx oc ask-ctx)         ask-ctx)     ; he opts in
      (v/assert kb (list marriedTo Oedipus Jocasta)  oc)
      (v/assert kb (list 'sameAs Jocasta MotherOf)   ask-ctx)     ; base states the identity
      (is (v/ask? kb (list 'believes Oedipus (list marriedTo Oedipus MotherOf)) ask-ctx)
          "an agent who inherits the merge inherits the substitution it licenses")
      (is (v/ask? kb (list 'believes Oedipus (list marriedTo Oedipus Jocasta)) ask-ctx)))))

;; ---- what the barrier holds, and what it lets through ---------------------
;; Read at `kb/rewrite-goal`, which is the one entry point every read path prepares its goal
;; through, so these say exactly which positions move.

(tu/deftest-kb the-proposition-does-not-move-where-the-same-sentence-alone-does
  (tu/with-terms [Oedipus Jocasta MotherOf marriedTo]
    (let [dead (loser kb Jocasta MotherOf)
          prop (list marriedTo Oedipus dead)]
      (v/assert kb (list 'sameAs Jocasta MotherOf) ask-ctx)
      (testing "asked on its own the sentence is rewritten — that is ordinary congruence"
        (is (not= prop (kb/rewrite-goal kb prop ask-ctx))))
      (testing "asked as what an agent believes it is not touched at all"
        (is (= (list 'believes Oedipus prop)
               (kb/rewrite-goal kb (list 'believes Oedipus prop) ask-ctx)))))))

(tu/deftest-kb the-agent-slot-is-a-reference-and-stays-transparent
  (tu/with-terms [Oedipus King Jocasta MotherOf marriedTo]
    (v/assert kb (list 'sameAs Oedipus King)     ask-ctx)
    (v/assert kb (list 'sameAs Jocasta MotherOf) ask-ctx)
    (let [prop (list marriedTo Oedipus Jocasta)
          rw   (kb/rewrite-goal kb (list 'believes Oedipus prop) ask-ctx)]
      (is (= (kb/rewrite-goal kb Oedipus ask-ctx) (second rw))
          "merging two names for one agent is one agent under two names")
      (is (= prop (nth rw 2))
          "while the proposition keeps every spelling it was written with"))))

(tu/deftest-kb a-spelling-rename-does-reach-inside-the-quotation
  ;; The `spelling?` half, exactly as a quoting function's arguments take it: `rewriteOf`
  ;; retires a *name*, so the mention follows it; `sameAs` merges *referents*, so it does
  ;; not.  Both sides of a rename move, which is why the belief stays retrievable.
  (tu/with-terms [Oedipus Preferred Deprecated marriedTo]
    (v/assert kb (list 'rewriteOf Preferred Deprecated) ask-ctx)
    (is (= (list 'believes Oedipus (list marriedTo Oedipus Preferred))
           (kb/rewrite-goal kb (list 'believes Oedipus (list marriedTo Oedipus Deprecated))
                            ask-ctx)))))

(tu/deftest-kb an-ungranted-predicate-holds-nothing-opaque
  ;; Control.  Opacity is what the `modal_predicate` marker buys; a binary relation over a
  ;; sentence-shaped argument that nobody granted it to gets ordinary congruence, and must.
  (tu/with-terms [Oedipus Jocasta MotherOf marriedTo mutters]
    (let [dead (loser kb Jocasta MotherOf)
          g    (list mutters Oedipus (list marriedTo Oedipus dead))]
      (v/assert kb (list 'sameAs Jocasta MotherOf) ask-ctx)
      (is (not= g (kb/rewrite-goal kb g ask-ctx))))))

(tu/deftest-kb a-non-sentence-argument-refers-rather-than-quotes
  ;; `(believes A Foo)` names a term, not a proposition — the form the projector itself
  ;; declines — so nothing is held opaque and the merge reaches it.
  (tu/with-terms [Oedipus Jocasta MotherOf]
    (let [dead (loser kb Jocasta MotherOf)]
      (v/assert kb (list 'sameAs Jocasta MotherOf) ask-ctx)
      (is (= (kb/rewrite-goal kb dead ask-ctx)
             (nth (kb/rewrite-goal kb (list 'believes Oedipus dead) ask-ctx) 2))))))

(tu/deftest-kb opacity-holds-at-every-layer-of-a-nested-belief
  (tu/with-terms [Oedipus Creon Jocasta MotherOf marriedTo]
    (let [dead (loser kb Jocasta MotherOf)
          g    (list 'believes Oedipus (list 'believes Creon (list marriedTo Creon dead)))]
      (v/assert kb (list 'sameAs Jocasta MotherOf) ask-ctx)
      (is (= g (kb/rewrite-goal kb g ask-ctx))
          "the inner proposition is inside two quotations and moves for neither"))))

;; ---- the question and the storage hold still together --------------------

(tu/deftest-kb a-stored-belief-stays-retrievable-under-the-spelling-it-was-stored-in
  ;; `(believes A P)` is also an ordinary assertible fact, and the barrier sits in the one
  ;; congruence walk both migration and query use — so a merge migrates neither, and the
  ;; path-dependence `prepare-goal-for-read` exists to prevent does not open here.
  (tu/with-terms [Oedipus Jocasta MotherOf marriedTo]
    (let [dead (loser kb Jocasta MotherOf)
          fact (list 'believes Oedipus (list marriedTo Oedipus dead))]
      (v/assert kb fact ask-ctx)
      (v/assert kb (list 'sameAs Jocasta MotherOf) ask-ctx)
      (let [h (v/handle-of kb fact ask-ctx)]
        (is (some? h) "the stored sentex is still under the spelling it was asserted in")
        (is (v/in? kb h) "and still believed — no migration retired it"))
      (is (v/ask? kb fact ask-ctx) "so the question that stored it still answers"))))

(tu/deftest-kb a-quoted-term-is-not-reported-displaced
  ;; `why-not` names the representative that displaced a spelling.  The map is computed by
  ;; the traversal the rewrite actually takes, so a term held opaque is not in it.
  (tu/with-terms [Oedipus Jocasta MotherOf marriedTo]
    (let [dead (loser kb Jocasta MotherOf)
          prop (list marriedTo Oedipus dead)]
      (v/assert kb (list 'sameAs Jocasta MotherOf) ask-ctx)
      (is (seq (kb/displaced-terms kb prop ask-ctx))
          "the sentence alone reports the merge that moved it")
      (is (empty? (kb/displaced-terms kb (list 'believes Oedipus prop) ask-ctx))
          "and as a quotation it reports nothing, because nothing moved"))))

(tu/deftest-kb retired-for-agrees-with-the-congruence-walk-on-quoted-and-unquoted-mentions
  ;; `res/retired-for?` answers a sentence the flat read finds no displaced symbol in
  ;; false without asking whether it quotes, and reads every other one through the flat
  ;; or the mention-aware path.  All of them must answer what the congruence walk itself does: a sentence is
  ;; retired exactly when `representative-term` moves it.
  (tu/with-terms [Oedipus Creon Jocasta MotherOf Preferred Deprecated marriedTo says]
    (let [dead (loser kb Jocasta MotherOf)]
      (v/assert kb (list 'sameAs Jocasta MotherOf) ask-ctx)
      (v/assert kb (list 'rewriteOf Preferred Deprecated) ask-ctx)
      (let [vis      (res/visible-supporter-fn kb ask-ctx)
            merged?  (tax/merged-term-pred (reasoning/taxonomy kb))
            retired? #(res/retired-for? kb (delay vis) merged? %)
            moved?   #(not= % (res/representative-term kb vis %))
            plain    (list marriedTo Oedipus dead)
            cases    {plain                                                  true
                      (list marriedTo Oedipus Creon)                         false
                      (list says Creon (list 'Quote plain))                  false
                      (list says Creon (list 'Quasiquote plain))             false
                      (list 'believes Oedipus plain)                         false
                      (list says Creon (list 'Quote (list marriedTo Oedipus Deprecated))) true
                      (list 'believes Oedipus (list marriedTo Oedipus Deprecated))        true
                      (list 'and plain (list says Creon (list 'Quote plain)))             true
                      (list 'not (list 'sameAs Jocasta MotherOf))            false}]
        (doseq [[s expected] cases]
          (testing (pr-str s)
            (is (= expected (retired? s)))
            (is (= (moved? s) (retired? s))
                "the flat-read answer agrees with the walk")))))))

;; ---- a reifiable application in the proposition ----------------------------

(tu/deftest-kb an-askers-merge-does-not-reach-an-application-in-what-an-agent-believes
  ;; both routes: Ann's belief is projected from her context, Bob's is a stored fact
  (tu/with-terms [FruitFn TreeFn Apple Pomme Ann Bob Tom likes]
    (let [fruit  (fn [x] (list FruitFn (list TreeFn x)))
          belief (fn [agent x] (list 'believes agent (list likes Tom (fruit x))))]
      (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
      (v/assert kb (list 'reifiable_function TreeFn) 'CxUniverse)
      (v/assert kb (list likes Tom (fruit Apple)) (modal/context-of-agent Ann))
      (v/assert kb (belief Bob Apple) ask-ctx)
      (v/assert kb (list 'sameAs Apple Pomme) ask-ctx)
      (is (= [true false true false]
             (mapv #(v/ask? kb % ask-ctx)
                   [(belief Ann Apple) (belief Ann Pomme) (belief Bob Apple) (belief Bob Pomme)])))
      (is (= [(belief Bob Apple)] (mapv :sentence (v/sentexes-matching kb (list 'believes Bob '?p) ask-ctx)))
          "the stored belief keeps the application"))))

(tu/deftest-kb an-identity-the-agent-holds-reaches-an-application-in-their-belief
  (tu/with-terms [FruitFn Apple Pomme Ann Tom likes]
    (let [actx (modal/context-of-agent Ann)]
      (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
      (v/assert kb (list likes Tom (list FruitFn Apple)) actx)
      (v/assert kb (list 'sameAs Apple Pomme) actx)
      (is (v/ask? kb (list 'believes Ann (list likes Tom (list FruitFn Pomme))) ask-ctx))
      (is (not (v/ask? kb (list likes Tom (list FruitFn Pomme)) ask-ctx))))))

(tu/deftest-kb a-merge-of-two-applications-stops-at-the-quotation
  (tu/with-terms [WifeFn MotherFn Oedipus Ann Bob Tom likes]
    (let [wife   (list WifeFn Oedipus)
          mother (list MotherFn Oedipus)
          actx   (modal/context-of-agent Ann)]
      (v/assert kb (list 'reifiable_function WifeFn) 'CxUniverse)
      (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
      (v/assert kb (list likes Tom wife) actx)
      (v/assert kb (list 'believes Bob (list likes Tom wife)) ask-ctx)
      (v/assert kb (list 'sameAs wife mother) ask-ctx)
      (is (= [false false false true]
             [(v/ask? kb (list 'believes Ann (list likes Tom mother)) ask-ctx)
              (v/ask? kb (list 'believes Bob (list likes Tom mother)) ask-ctx)
              (v/ask? kb (list likes Tom mother) actx)
              (v/ask? kb (list likes Tom wife) actx)])))))
