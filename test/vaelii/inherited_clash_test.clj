;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.inherited-clash-test
  "A stored claim against a **known-true claim reached by argument preservation** — the
  one contradiction whose second side is not a sentex.

  `(carriesLoad hauler_kind Bone1)` asserted `{:strength :monotonic}` reaches
  `(carriesLoad cart_kind Bone1)`, and a stored `(not (carriesLoad cart_kind Bone1))`
  denies a claim that has no handle.  `inherit/undercut?` is what decides whether there is
  anything to say: a `:default` general claim yields to the nearer contrary one and never
  fires for that tuple, while a `:monotonic` one is \"a contradiction to report rather
  than a refinement to defer to\".

  What is pinned here is that the report exists, that it names enough to be acted on —
  the claim nobody wrote, the sentex it was read off, the declaration and the edge — and
  that it is a function of the knowledge rather than of the order it arrived in.  The
  belief consequence is pinned beside it, because the two are one decision: the nogood's
  members are the stored claim and everything the reading rests on, so `decide-nogood`
  weighs them as it weighs any other nogood and the **weakest member decides**
  (docs/inherit.md).

  `ontology_test` reads the same mechanism as a modelling claim about the shipped
  vocabulary; this namespace reads it as an engine contract."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(def ^:private U 'CxUniverse)
(def ^:private mono {:strength :monotonic})

(defn- vocabulary!
  "The declaration and the taxonomy the whole namespace runs on: `carriesLoad` preserves
  its first argument down `genl`, and `cart_kind` is a kind of `hauler_kind`.  Every
  sentence here is at the default `:default` unless a test says otherwise, which is what
  the shipped ontology's own edges and declarations are."
  [kb {:keys [pred hauler cart]} & {:keys [edge?] :or {edge? true}}]
  (v/assert kb (list 'binary_predicate pred) U)
  (v/assert kb (list 'transitiveInArg pred 1 'genl) U)
  (v/assert kb (list 'genl hauler 'animal) U)
  (when edge? (v/assert kb (list 'genl cart hauler) U)))

(defn- inherited-reports
  "Every standing clash of either reading whose second side is an inherited claim.

  With a `pred`, only the ones about that predicate — which is what lets several
  independent cases share one KB: `with-terms` gensyms a predicate per case, so two of
  them in one KB are two unrelated pieces of knowledge and the fixture's net-neutrality
  check still has one baseline to measure against."
  ([kb]
   (filterv #(= :inherited (:kind %)) (concat (v/conflicts kb) (v/contradictions kb))))
  ([kb pred]
   (filterv (fn [r] (let [s (:sentence (:inherited r))
                          s (if (= 'not (first s)) (second s) s)]
                      (= pred (first s))))
            (inherited-reports kb))))

;; ---- the report ----------------------------------------------------------

(tu/deftest-kb a-stored-claim-against-a-monotonic-inherited-claim-is-reported
  (tu/with-terms [carriesLoad hauler_kind cart_kind]
    (let [terms {:pred carriesLoad :hauler hauler_kind :cart cart_kind}]
      (vocabulary! kb terms)
      (v/assert kb (list carriesLoad hauler_kind 'Bone1) U mono)
      (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) U)
      (let [rs (inherited-reports kb)
            r  (first rs)]
        (testing "one report, and it is a represented dilemma rather than an unsolved clash"
          ;; the reading rests on a `:default` declaration and a `:default` edge, so the
          ;; floor of the nogood is shared and the engine defeats nothing
          (is (= 1 (count rs)))
          (is (= 1 (count (v/contradictions kb))))
          (is (empty? (v/conflicts kb))))
        (testing "it names the claim nobody wrote, and where it was read"
          (is (= (list carriesLoad cart_kind 'Bone1) (:sentence (:inherited r))))
          (is (= U (:context (:inherited r)))))
        (testing "it names the sentex the claim was inherited from, by handle"
          (is (= (v/handle-of kb (list carriesLoad hauler_kind 'Bone1) U)
                 (:claim (:inherited r))))
          (is (= (list carriesLoad hauler_kind 'Bone1)
                 (:sentence (first (filter #(= (:handle %) (:claim (:inherited r)))
                                           (:sides r)))))))
        (testing "and the genl path and the declaration, so `why` can explain the reach"
          (is (= (set (map #(v/handle-of kb % U)
                           [(list 'transitiveInArg carriesLoad 1 'genl)
                            (list 'genl cart_kind hauler_kind)]))
                 (set (:via (:inherited r))))))
        (testing "the sides are the stored sentexes, and the stored claim is among them"
          (is (contains? (set (map :sentence (:sides r)))
                         (list 'not (list carriesLoad cart_kind 'Bone1))))
          (is (= (set (:handles r)) (:nogood r))))
        (testing "and every side is a believed sentex, since a nogood is what cannot all hold"
          (is (every? some? (map :defeat-class (:sides r)))))))))

(tu/deftest-kb the-sentence-of-the-report-names-both-claims
  (tu/with-terms [carriesLoad hauler_kind cart_kind]
    (let [terms {:pred carriesLoad :hauler hauler_kind :cart cart_kind}]
      (vocabulary! kb terms)
      (v/assert kb (list carriesLoad hauler_kind 'Bone1) U mono)
      (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) U)
      ;; `contradicts`, with the two ordered by content like every other clash sentence
      ;; — never by which of them was stored, since only one of them was
      (is (= (list 'contradicts
                   (list 'not (list carriesLoad cart_kind 'Bone1))
                   (list carriesLoad cart_kind 'Bone1))
             (:sentence (first (inherited-reports kb))))))))

;; ---- arrival order -------------------------------------------------------

(tu/deftest-kb every-arrival-order-reports-the-same-clash
  ;; Three sentences and six orders.  The **edge last** case is the one that needs its
  ;; own trigger: neither the general claim nor the stored one goes near the region a
  ;; `(genl cart_kind hauler_kind)` moves, so a discovery driven off the arriving
  ;; sentence's own predicate would find the pair in five orders and miss it in one.
  ;;
  ;; One KB, a gensym'd vocabulary per order — six unrelated pieces of knowledge rather
  ;; than six KBs, so nothing here clears the space out from under the fixture.
  (let [answers
        ;; eager: the body writes to the KB, and a lazy seq would interleave six loads
        ;; with the reads that judge them
        (vec
         (for [order [[:src :neg :edge] [:src :edge :neg]
                      [:neg :src :edge] [:neg :edge :src]
                      [:edge :src :neg] [:edge :neg :src]]]
           (tu/with-terms [carriesLoad hauler_kind cart_kind]
             (let [terms {:pred carriesLoad :hauler hauler_kind :cart cart_kind}
                   write {:edge #(v/assert kb (list 'genl cart_kind hauler_kind) U)
                          :src  #(v/assert kb (list carriesLoad hauler_kind 'Bone1) U mono)
                          :neg  #(v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) U)}]
               (vocabulary! kb terms :edge? false)
               (doseq [k order] ((write k)))
               ;; the vocabulary is gensym'd per order, so what is compared is the report's
               ;; *shape*: how many, which sentences relative to this order's own terms,
               ;; which reading it landed in, and what the KB then believes
               (let [rs (inherited-reports kb carriesLoad)
                     r  (first rs)]
                 [(count rs)
                  (:kind r)
                  (= (list carriesLoad cart_kind 'Bone1) (:sentence (:inherited r)))
                  (set (map :sentence (:sides r)))
                  (v/ask? kb (list carriesLoad cart_kind 'Bone1) U)])))))
        shapes (map (fn [[n k inh sides believed]]
                      ;; the sides carry this order's own gensyms, so they are compared as
                      ;; the four *roles* they fill rather than as spellings
                      [n k inh (count sides) believed])
                    answers)]
    (is (= 1 (count (distinct shapes)))
        (str "the report must be a function of the knowledge, not of the order: "
             (pr-str (vec (distinct shapes)))))
    (is (= [1 :inherited true 4 false] (first shapes)))))

;; ---- withdrawal ----------------------------------------------------------

(tu/deftest-kb retracting-the-source-the-edge-or-the-declaration-withdraws-the-report
  ;; Every member of the nogood is a stored sentex, so `live-nogood?` and the settle's own
  ;; re-derivation take the report away between them — there is no separate teardown.
  (doseq [[label drop-key]
          [["the general claim" :src] ["the genl edge" :edge] ["the declaration" :decl]
           ["the stored claim itself" :neg]]]
    (tu/with-terms [carriesLoad hauler_kind cart_kind]
      (let [terms {:pred carriesLoad :hauler hauler_kind :cart cart_kind}
            which {:src  (list carriesLoad hauler_kind 'Bone1)
                   :edge (list 'genl cart_kind hauler_kind)
                   :decl (list 'transitiveInArg carriesLoad 1 'genl)
                   :neg  (list 'not (list carriesLoad cart_kind 'Bone1))}]
        (vocabulary! kb terms)
        (v/assert kb (which :src) U mono)
        (v/assert kb (which :neg) U)
        (is (= 1 (count (inherited-reports kb carriesLoad))) (str "before retracting " label))
        (v/retract! kb (v/handle-of kb (which drop-key) U))
        (is (empty? (inherited-reports kb carriesLoad)) (str "after retracting " label))))))

;; ---- context scoping -----------------------------------------------------

(tu/deftest-kb a-claim-in-a-context-that-cannot-see-the-general-one-is-not-paired
  ;; The pair is judged from the stored claim's own context, which is the vantage the
  ;; inherited claim exists in at all: a claim reaches a context that can see it and no
  ;; other.  So a general claim stated *below* the stored one denies nothing, and two
  ;; contexts neither of which sees the other pair nothing.
  (tu/with-terms [CxNarrow CxLeft CxRight]
    (doseq [c [CxNarrow CxLeft CxRight]]
      (v/assert kb (list 'genlCx c U) U))
    (doseq [[label src-ctx neg-ctx expected]
            [["the general claim above the stored one" U CxNarrow 1]
             ["the general claim below the stored one" CxNarrow U 0]
             ["two contexts neither of which sees the other" CxLeft CxRight 0]]]
      (tu/with-terms [carriesLoad hauler_kind cart_kind]
        (let [terms {:pred carriesLoad :hauler hauler_kind :cart cart_kind}]
          (vocabulary! kb terms)
          (v/assert kb (list carriesLoad hauler_kind 'Bone1) src-ctx mono)
          (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) neg-ctx)
          (is (= expected (count (inherited-reports kb carriesLoad))) label))))))

;; ---- what is not reported ------------------------------------------------

(tu/deftest-kb a-default-general-claim-is-undercut-and-reports-nothing
  ;; The existing behaviour, and the half of the contract that must not move: a `:default`
  ;; generality is something a nearer statement is entitled to override, so the general
  ;; claim does not fire for that tuple and no pair exists to report.
  (tu/with-terms [carriesLoad hauler_kind cart_kind]
    (let [terms {:pred carriesLoad :hauler hauler_kind :cart cart_kind}]
      (vocabulary! kb terms)
      (v/assert kb (list carriesLoad hauler_kind 'Bone1) U)
      (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) U)
      (is (empty? (inherited-reports kb)))
      (testing "the nearer claim wins and the general one still stands"
        (is (not (v/ask? kb (list carriesLoad cart_kind 'Bone1) U)))
        (is (v/ask? kb (list carriesLoad hauler_kind 'Bone1) U))))))

(tu/deftest-kb a-body-stored-in-both-polarities-is-reported-once-and-as-a-rebuttal
  ;; The diagonal.  `witness-terms` is reflexive, so the claim stated at the very tuple
  ;; the stored negation is about comes back through the reach too — and that pair is an
  ;; ordinary `P` beside an ordinary `(not P)`, which `negation-nogoods` already forms off
  ;; the `:opposed` set.  Reporting it here as well would report one pair twice.
  (tu/with-terms [carriesLoad hauler_kind cart_kind]
    (let [terms {:pred carriesLoad :hauler hauler_kind :cart cart_kind}]
      (vocabulary! kb terms)
      (v/assert kb (list carriesLoad cart_kind 'Bone1) U)
      (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) U)
      (is (empty? (inherited-reports kb)))
      (is (= 1 (count (v/contradictions kb))))
      (is (nil? (:kind (first (v/contradictions kb))))
          "a rebuttal, which is what two stored claims about one tuple are"))))

;; ---- the belief consequence ----------------------------------------------

(tu/deftest-kb a-known-true-reading-defeats-the-nearer-default
  ;; The whole reading is known-true — the general claim, the declaration and the edge —
  ;; so the stored `:default` claim is the nogood's unique weakest member and is defeated.
  ;; That is `decide-nogood`'s ordinary rule, and it is what "a monotonic claim is never
  ;; undercut" comes to: the general claim reaches the subkind and the nearer default
  ;; does not stop it.
  (tu/with-terms [carriesLoad hauler_kind cart_kind]
    (v/assert kb (list 'binary_predicate carriesLoad) U)
    (v/assert kb (list 'transitiveInArg carriesLoad 1 'genl) U mono)
    (v/assert kb (list 'genl hauler_kind 'animal) U mono)
    (v/assert kb (list 'genl cart_kind hauler_kind) U mono)
    (v/assert kb (list carriesLoad hauler_kind 'Bone1) U mono)
    (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) U)
    (testing "the inherited claim wins"
      (is (v/ask? kb (list carriesLoad cart_kind 'Bone1) U))
      (is (v/ask? kb (list carriesLoad hauler_kind 'Bone1) U)))
    (testing "and a resolved contradiction is reported by neither reading"
      (is (empty? (inherited-reports kb))))))

(tu/deftest-kb two-known-true-claims-are-an-irreducible-conflict
  ;; Both stored claims known-true, and the reading between them too: nothing may be
  ;; defeated, so it is a clash the engine hands back — a contradiction like any other.
  (tu/with-terms [carriesLoad hauler_kind cart_kind]
    (v/assert kb (list 'binary_predicate carriesLoad) U)
    (v/assert kb (list 'transitiveInArg carriesLoad 1 'genl) U mono)
    (v/assert kb (list 'genl hauler_kind 'animal) U mono)
    (v/assert kb (list 'genl cart_kind hauler_kind) U mono)
    (v/assert kb (list carriesLoad hauler_kind 'Bone1) U mono)
    (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) U mono)
    (is (= 1 (count (v/conflicts kb))))
    (is (= :inherited (:kind (first (v/conflicts kb)))))
    (is (empty? (v/contradictions kb)))
    (testing "both sides stay believed, which is what an unsolved clash means"
      (is (v/ask? kb (list carriesLoad hauler_kind 'Bone1) U))
      (is (v/ask? kb (list 'not (list carriesLoad cart_kind 'Bone1)) U)))))

(tu/deftest-kb a-default-declaration-leaves-the-clash-a-dilemma-however-strong-the-claims
  ;; The reading is capped by its weakest link exactly as a firing's strength is, so two
  ;; known-true claims bridged by a `:default` declaration are a dilemma and not a
  ;; conflict: what the engine has no grounds to choose between is which of the
  ;; declaration, the edge and the stored claim to give up.
  (tu/with-terms [carriesLoad hauler_kind cart_kind]
    (let [terms {:pred carriesLoad :hauler hauler_kind :cart cart_kind}]
      (vocabulary! kb terms)
      (v/assert kb (list carriesLoad hauler_kind 'Bone1) U mono)
      (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) U mono)
      (is (empty? (v/conflicts kb)))
      (is (= 1 (count (inherited-reports kb))))
      (is (= 2 (:priority (first (inherited-reports kb))))
          "the rebuttal range: two claims about the world, not a violated declaration"))))

;; ---- the other polarity --------------------------------------------------

(tu/deftest-kb a-stored-positive-claim-against-an-inherited-negation-is-reported-too
  ;; `claims` reads both polarities out of the reach, so a known-true `(not (P w b))`
  ;; above a stored `(P a b)` denies it the same way round.
  (tu/with-terms [carriesLoad hauler_kind cart_kind]
    (let [terms {:pred carriesLoad :hauler hauler_kind :cart cart_kind}]
      (vocabulary! kb terms)
      (v/assert kb (list 'not (list carriesLoad hauler_kind 'Bone1)) U mono)
      (v/assert kb (list carriesLoad cart_kind 'Bone1) U)
      (let [r (first (inherited-reports kb))]
        (is (some? r))
        (is (= (list 'not (list carriesLoad cart_kind 'Bone1)) (:sentence (:inherited r))))
        (is (= (v/handle-of kb (list 'not (list carriesLoad hauler_kind 'Bone1)) U)
               (:claim (:inherited r))))))))

;; ---- the roster survives a rebuild ---------------------------------------

(tu/deftest-kb a-rebuild-puts-the-preservation-roster-back
  ;; `:preserving` is derived from storage and no store holds it, so `recover` rebuilds it
  ;; beside `:opposed`, `:excepted` and the rule rosters.  A KB that came up without it
  ;; would answer `contradictions` differently either side of a restart — silently, since
  ;; the gate reads as "this KB declares no preservation" and stops.  Emptied by hand
  ;; here, which is the state a second KB over the same records comes up in.
  (tu/with-terms [carriesLoad hauler_kind cart_kind]
    (let [terms {:pred carriesLoad :hauler hauler_kind :cart cart_kind}]
      (vocabulary! kb terms)
      (v/assert kb (list carriesLoad hauler_kind 'Bone1) U mono)
      (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) U)
      (is (= 1 (count (inherited-reports kb carriesLoad))))
      (reset! (reasoning/preserving kb) {})
      (v/recover kb)
      (is (= 1 (count (inherited-reports kb carriesLoad)))
          "the rebuild re-derives the roster from the records"))))

;; ---- a KB that declares no preservation ----------------------------------

(tu/deftest-kb a-kb-declaring-no-preservation-reports-nothing-here
  ;; The gate, from the outside: with no declaration the reach does not exist, so the two
  ;; claims are about two different tuples and neither denies the other.
  (tu/with-terms [carriesLoad hauler_kind cart_kind]
    (v/assert kb (list 'binary_predicate carriesLoad) U)
    (v/assert kb (list 'genl hauler_kind 'animal) U)
    (v/assert kb (list 'genl cart_kind hauler_kind) U)
    (v/assert kb (list carriesLoad hauler_kind 'Bone1) U mono)
    (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) U)
    (is (empty? (inherited-reports kb)))
    (is (empty? (v/contradictions kb)))
    (is (empty? (v/conflicts kb)))))
