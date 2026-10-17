;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.inherited-clash-test
  "A stored claim against a **known-true claim reached by argument preservation** — the
  one contradiction whose second side is not a sentex.

  `(carriesLoad hauler_kind Bone1)` asserted `{:strength :monotonic}` reaches
  `(carriesLoad cart_kind Bone1)`, and a stored `(not (carriesLoad cart_kind Bone1))`
  denies a claim that has no handle.  A reading is as strong as its weakest reason: one
  whose general claim, declaration or `genl` edge is `:default` yields to the nearer
  contrary claim and forms no nogood, while a reading known-true throughout is \"a
  contradiction to report rather than a refinement to defer to\".

  What is pinned here is that the report exists, that it names enough to be acted on —
  the claim nobody wrote, the sentex it was read off, the declaration and the edge — and
  that it is a function of the knowledge rather than of the order it arrived in.  The
  belief consequence is pinned beside it, because the two are one decision: the nogood's
  members are the stored claim and everything the reading rests on, so `decide/verdict`
  weighs them as it weighs any other nogood and the **weakest member decides**
  (docs/inherit.md).

  `ontology_test` reads the same mechanism as a modelling claim about the shipped
  vocabulary; this namespace reads it as an engine contract."
  (:require [clojure.set :as set]
            [clojure.test :refer [is testing use-fixtures]]
            [clojure.walk :as walk]
            [taoensso.trove :as trove]
            [vaelii.core :as v]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.inherited :as inherited]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(def ^:private U 'CxUniverse)
(def ^:private mono {:strength :monotonic})

(defn- vocabulary!
  "The declaration and the taxonomy the whole namespace runs on: `carriesLoad` preserves
  its first argument down `genl`, and `cart_kind` is a kind of `hauler_kind`.  The
  declaration and the edges are `:monotonic`, so a reading off a `:monotonic` claim is
  known-true: against a `:monotonic` denial the pair is a conflict, and a `:default`
  denial loses to it unreported."
  [kb {:keys [pred hauler cart]} & {:keys [edge?] :or {edge? true}}]
  (v/assert kb (list 'binary_predicate pred) U)
  (v/assert kb (list 'transitiveInArgInverse pred 1 'genl) U mono)
  (v/assert kb (list 'genl hauler 'animal) U mono)
  (when edge? (v/assert kb (list 'genl cart hauler) U mono)))

(defn- about?
  "Whether the clash `r`'s inherited claim is about `pred`."
  [pred r]
  (let [s (:sentence (:inherited r))
        s (if (= 'not (first s)) (second s) s)]
    (= pred (first s))))

(defn- inherited-reports
  "Every standing clash of either reading whose second side is an inherited claim.

  With a `pred`, only the ones about that predicate — which is what lets several
  independent cases share one KB: `with-terms` gensyms a predicate per case, so two of
  them in one KB are two unrelated pieces of knowledge and the fixture's net-neutrality
  check still has one baseline to measure against."
  ([kb]
   (filterv #(= :inherited (:kind %)) (concat (v/conflicts kb) (v/contradictions kb))))
  ([kb pred]
   (filterv #(about? pred %) (inherited-reports kb))))

;; ---- the report ----------------------------------------------------------

(tu/deftest-kb a-stored-claim-against-a-monotonic-inherited-claim-is-reported
  (tu/with-terms [carriesLoad hauler_kind cart_kind]
    (let [terms {:pred carriesLoad :hauler hauler_kind :cart cart_kind}]
      (vocabulary! kb terms)
      (v/assert kb (list carriesLoad hauler_kind 'Bone1) U mono)
      (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) U mono)
      (let [rs (inherited-reports kb)
            r  (first rs)]
        (testing "one report, and it is an unsolved clash"
          ;; every member is `:monotonic`, so the engine defeats nothing
          (is (= 1 (count rs)))
          (is (= 1 (count (v/conflicts kb))))
          (is (empty? (v/contradictions kb))))
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
                           [(list 'transitiveInArgInverse carriesLoad 1 'genl)
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
      (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) U mono)
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
                   write {:edge #(v/assert kb (list 'genl cart_kind hauler_kind) U mono)
                          :src  #(v/assert kb (list carriesLoad hauler_kind 'Bone1) U mono)
                          :neg  #(v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) U mono)}]
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
                   :decl (list 'transitiveInArgInverse carriesLoad 1 'genl)
                   :neg  (list 'not (list carriesLoad cart_kind 'Bone1))}]
        (vocabulary! kb terms)
        (v/assert kb (which :src) U mono)
        (v/assert kb (which :neg) U mono)
        (is (= 1 (count (inherited-reports kb carriesLoad))) (str "before retracting " label))
        (v/retract! kb (v/handle-of kb (which drop-key) U))
        (is (empty? (inherited-reports kb carriesLoad)) (str "after retracting " label))))))

;; ---- context scoping -----------------------------------------------------

(tu/deftest-kb a-claim-is-paired-where-a-context-sees-the-general-one
  ;; The pair is judged at every context that sees the stored claim, the general claim and
  ;; the reading: the stored claim's own context when it sees them, and otherwise the most
  ;; general context below it that does.  The stored denial is `:default`, so it loses
  ;; the pair at the readers at and below that context and nothing is reported.  A
  ;; general claim stated *below* the stored one is paired there, and two contexts
  ;; neither of which sees the other, with nothing seeing both, pair nothing.
  ;;
  ;;   CxUniverse
  ;;     ├─ CxNarrow
  ;;     ├─ CxLeft
  ;;     └─ CxRight
  (tu/with-terms [CxNarrow CxLeft CxRight]
    (doseq [c [CxNarrow CxLeft CxRight]]
      (v/assert kb (list 'genlCx c U) U))
    (doseq [[label src-ctx neg-ctx expected readers]
            [["the general claim above the stored one" U CxNarrow 1 {CxNarrow false}]
             ["the general claim below the stored one" CxNarrow U 1 {CxNarrow false U true}]
             ["two contexts neither of which sees the other" CxLeft CxRight 0
              {CxRight true}]]]
      (tu/with-terms [carriesLoad hauler_kind cart_kind]
        (let [terms {:pred carriesLoad :hauler hauler_kind :cart cart_kind}]
          (vocabulary! kb terms)
          (v/assert kb (list carriesLoad hauler_kind 'Bone1) src-ctx mono)
          (let [d (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) neg-ctx)]
            (is (= expected (count (filter #(about? carriesLoad %)
                                           (vals (inherited/inherited-clashes kb)))))
                label)
            (is (empty? (inherited-reports kb carriesLoad)) label)
            (doseq [[reader in?] readers]
              (is (= in? (v/believed? kb d reader)) (str label ", read from " reader)))))))))

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
  ;; ordinary `P` beside an ordinary `(not P)`, which the negation family already forms off
  ;; the bodies stored in both polarities.  Reporting it here as well would report one pair
  ;; twice.
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
  ;; That is `decide/verdict`'s ordinary rule, and it is what "a monotonic claim is never
  ;; undercut" comes to: the general claim reaches the subkind and the nearer default
  ;; does not stop it.
  (tu/with-terms [carriesLoad hauler_kind cart_kind]
    (v/assert kb (list 'binary_predicate carriesLoad) U)
    (v/assert kb (list 'transitiveInArgInverse carriesLoad 1 'genl) U mono)
    (v/assert kb (list 'genl hauler_kind 'animal) U mono)
    (v/assert kb (list 'genl cart_kind hauler_kind) U mono)
    (v/assert kb (list carriesLoad hauler_kind 'Bone1) U mono)
    (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) U)
    (testing "the inherited claim wins"
      (is (v/ask? kb (list carriesLoad cart_kind 'Bone1) U))
      (is (v/ask? kb (list carriesLoad hauler_kind 'Bone1) U)))
    (testing "and a resolved contradiction is reported by neither reading"
      (is (empty? (inherited-reports kb))))))

(defn- orders
  "Every ordering of `xs`."
  [xs]
  (if (empty? xs) [()] (for [x xs, more (orders (remove #{x} xs))] (cons x more))))

(defn- placed-about
  "The member sentences of each stored sentence of functor `f` that names a sentex about
  `pred`, as a set of sets with `renames` applied."
  [kb f pred renames]
  (into #{}
        (comp (map (fn [sx] (into #{} (keep #(some->> (v/handle-id %) (v/sentex kb) :sentence))
                                  (rest (:sentence sx)))))
              (filter (fn [ss] (some #(= pred (if (= 'not (first %)) (first (second %)) (first %))) ss)))
              (map #(walk/postwalk-replace renames %)))
        (v/sentexes-with-functor kb f)))

(tu/deftest-kb a-declared-stored-claim-reads-and-stores-alike-in-every-arrival-order
  ;; The known-true reading of an inherited negation clashes with a :default stored claim
  ;; of `carriesLoad`, which a declaration in the clash's own context puts on the roster.
  ;; The stored claim is never the loser there, so it stays believed, and the placed
  ;; sentences are the same whether the declaration arrives first or last.
  (let [readings
        (vec (for [order (orders [:decl :general :stored])]
               (tu/with-terms [carriesLoad hauler_kind cart_kind]
                 (vocabulary! kb {:pred carriesLoad :hauler hauler_kind :cart cart_kind})
                 (let [stored  (list carriesLoad cart_kind 'Bone1)
                       renames {carriesLoad 'P hauler_kind 'H cart_kind 'C}
                       writes  {:decl    #(v/assert kb (list 'forced_monotonic_predicate carriesLoad) U)
                                :general #(v/assert kb (list 'not (list carriesLoad hauler_kind 'Bone1))
                                                    U mono)
                                :stored  #(v/assert kb stored U)}]
                   (doseq [k order] ((writes k)))
                   [(vec order)
                    [(v/ask? kb stored U)
                     (placed-about kb 'defeat carriesLoad renames)
                     (placed-about kb 'contradicts carriesLoad renames)]]))))]
    (is (= 1 (count (distinct (map second readings)))) (pr-str readings))
    (is (true? (first (second (first readings)))) "the declared stored claim is believed")))

(tu/deftest-kb two-known-true-claims-are-an-irreducible-conflict
  ;; Both stored claims known-true, and the reading between them too: nothing may be
  ;; defeated, so it is a clash the engine hands back — a contradiction like any other.
  (tu/with-terms [carriesLoad hauler_kind cart_kind]
    (v/assert kb (list 'binary_predicate carriesLoad) U)
    (v/assert kb (list 'transitiveInArgInverse carriesLoad 1 'genl) U mono)
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

(tu/deftest-kb a-reading-over-a-default-edge-between-two-known-true-claims-forms-no-nogood
  ;; The declaration is `:monotonic` and the edge `:default`, so the reading is
  ;; `:default` and the known-true denial undercuts it: nothing is reported, and the edge
  ;; and both known-true claims stay believed.
  (tu/with-terms [carriesLoad hauler_kind cart_kind]
    (let [terms {:pred carriesLoad :hauler hauler_kind :cart cart_kind}]
      (vocabulary! kb terms :edge? false)
      (v/assert kb (list 'genl cart_kind hauler_kind) U)
      (v/assert kb (list carriesLoad hauler_kind 'Bone1) U mono)
      (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) U mono)
      (is (empty? (v/conflicts kb)))
      (is (empty? (inherited-reports kb)))
      (is (v/ask? kb (list 'genl cart_kind hauler_kind) U))
      (is (v/ask? kb (list carriesLoad hauler_kind 'Bone1) U))
      (is (v/ask? kb (list 'not (list carriesLoad cart_kind 'Bone1)) U)))))

;; ---- the other polarity --------------------------------------------------

(tu/deftest-kb a-stored-positive-claim-against-an-inherited-negation-is-reported-too
  ;; `claims` reads both polarities out of the reach, so a known-true `(not (P w b))`
  ;; above a stored known-true `(P a b)` denies it the same way round.
  (tu/with-terms [carriesLoad hauler_kind cart_kind]
    (let [terms {:pred carriesLoad :hauler hauler_kind :cart cart_kind}]
      (vocabulary! kb terms)
      (v/assert kb (list 'not (list carriesLoad hauler_kind 'Bone1)) U mono)
      (v/assert kb (list carriesLoad cart_kind 'Bone1) U mono)
      (let [r (first (inherited-reports kb))]
        (is (some? r))
        (is (= (list 'not (list carriesLoad cart_kind 'Bone1)) (:sentence (:inherited r))))
        (is (= (v/handle-of kb (list 'not (list carriesLoad hauler_kind 'Bone1)) U)
               (:claim (:inherited r))))))))

;; ---- a genl cycle -------------------------------------------------------

(tu/deftest-kb a-reading-over-a-default-edge-closes-no-genl-cycle
  ;; The reading that carries `(outranks kind_b kind_a)`'s converse round `(genl kind_a
  ;; kind_b)` rests on that `:default` edge, so it is undercut and no nogood defeats the
  ;; edge: the edge stays believed, and the reverse edge is refused as a cycle in every
  ;; order.  A claim round a cycle therefore never reaches its own tuple from here.
  (let [writes (fn [kb P a b]
                 {:ab    #(v/assert kb (list 'genl a b) U)
                  :decl2 #(v/assert kb (list 'transitiveInArgInverse P 2 'genl) U mono)
                  :decl1 #(v/assert kb (list 'transitiveInArgInverse P 1 'genl) U)
                  :neg   #(v/assert kb (list 'not (list P b b)) U mono)
                  :claim #(v/assert kb (list P b a) U mono)
                  :ba    #(try (v/assert kb (list 'genl b a) U mono) nil
                               (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))})
        shapes
        (vec
         (for [order [[:ab :decl2 :decl1 :neg :claim] [:claim :neg :decl1 :decl2 :ab]
                      [:neg :claim :ab :decl1 :decl2] [:decl1 :claim :decl2 :neg :ab]
                      [:claim :ab :neg :decl2 :decl1] [:decl2 :neg :claim :ab :decl1]]]
           (tu/with-terms [outranks kind_a kind_b]
             (let [w   (writes kb outranks kind_a kind_b)
                   in? #(boolean (when-let [h (v/handle-of kb % U)] (v/believed? kb h U)))]
               (v/assert kb (list 'binary_predicate outranks) U)
               (v/assert kb (list 'asymmetric outranks) U mono)
               (doseq [t [kind_a kind_b]] (v/assert kb (list 'genl t 'thing) U mono))
               (doseq [k order] ((w k)))
               [((w :ba))
                (count (inherited-reports kb outranks))
                (mapv in? [(list 'genl kind_a kind_b) (list outranks kind_b kind_a)
                           (list 'not (list outranks kind_b kind_b))])]))))]
    (is (= #{[:not-well-formed 0 [true true true]]} (set shapes)))))

;; ---- the roster survives a rebuild ---------------------------------------

(tu/deftest-kb a-recover-reports-the-inherited-clash-again
  ;; The discovery's gate reads the declarations off the index, so a KB that comes up
  ;; over the same records answers `contradictions` the same either side of a restart.
  (tu/with-terms [carriesLoad hauler_kind cart_kind]
    (let [terms {:pred carriesLoad :hauler hauler_kind :cart cart_kind}]
      (vocabulary! kb terms)
      (v/assert kb (list carriesLoad hauler_kind 'Bone1) U mono)
      (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) U mono)
      (is (= 1 (count (inherited-reports kb carriesLoad))))
      (v/recover kb)
      (is (= 1 (count (inherited-reports kb carriesLoad)))
          "the recover reads the declarations from the index"))))

(tu/deftest-kb a-recover-asks-the-preserved-claims-and-not-every-stored-sentex
  ;; recover's settle reads the whole store as its region; its discovery asks the stored
  ;; extent of the preserved predicate, read off the index, and reads no record of the
  ;; facts beside it.  The `::asked` log line counts the questions.  One inert record is
  ;; in no region, so the region is a whole store only by reading it as inert.
  (tu/with-terms [carriesLoad hauler_kind cart_kind]
    (let [terms {:pred carriesLoad :hauler hauler_kind :cart cart_kind}
          asked (atom [])]
      (vocabulary! kb terms)
      (v/assert kb (list carriesLoad hauler_kind 'Bone1) U mono)
      (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) U mono)
      (dotimes [_ 40] (v/assert kb (list 'animal (tu/tmp-ind "Beast")) U))
      (let [inert (list 'animal (tu/tmp-ind "Inert"))]
        (v/assert-inert kb inert U)
        (binding [trove/*log-fn* (fn [_ns _coords _level id payload]
                                   (when (= :vaelii.impl.discovery/asked id)
                                     (swap! asked conj (:data (force payload)))))]
          (v/recover kb))
        (let [{:keys [region fresh] n :asked} (first @asked)]
          (is (= :whole-store fresh))
          (is (< 40 region))
          (is (= 2 n) "the two stored carriesLoad sentences"))
        (is (= 1 (count (inherited-reports kb carriesLoad))))
        (testing "the inert record is stored and OUT after the recover"
          (let [h (v/handle-of kb inert U)]
            (is (some? h))
            (is (not (v/believed? kb h U)))))))))

(tu/deftest-kb a-write-beside-a-standing-inherited-clash-journals-none-of-its-members
  ;; Each settle pass empties the inherited clashes and installs what its discovery finds
  ;; again.  A member of a clash that stands did not move, so no reader of the candidate
  ;; journal (`decide/moves`) reads it again.
  (tu/with-terms [carriesLoad hauler_kind cart_kind]
    (vocabulary! kb {:pred carriesLoad :hauler hauler_kind :cart cart_kind})
    (v/assert kb (list carriesLoad hauler_kind 'Bone1) U mono)
    (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) U mono)
    (let [members (into #{} cat (keys (inherited/inherited-clashes kb)))
          [_ at]  (decide/moves kb nil)]
      (is (seq members))
      (v/assert kb (list 'animal (tu/tmp-ind "Beast")) U)
      (let [[_ _ moved] (decide/moves kb at)]
        (is (some? moved) "the journal reaches back to the position")
        (is (= 0 (count (set/intersection members moved))))
        (is (= members (into #{} cat (keys (inherited/inherited-clashes kb)))))))))

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

(tu/deftest-kb a-reader-below-a-one-context-inherited-clash-that-reads-it-released-believes-the-loser
  ;;   CxUniverse  (transitiveInArgInverse carriesLoad 1 genl) (genl cart hauler)
  ;;               (carriesLoad hauler Bone), each :monotonic
  ;;    └─ CxA     (not (carriesLoad cart Bone)) :default — loses at CxA
  ;;        └─ CxB (except (sentexHandle <(carriesLoad hauler Bone)>))
  ;; CxB sees no claim to read the denial against, so it believes the denial whatever
  ;; arrived first (docs/reference.md, decision 3).
  (doseq [except-first? [false true]]
    (tu/with-terms [carriesLoad hauler_kind cart_kind Bone CxA CxB]
      (v/assert kb (list 'genlCx CxA U) U mono)
      (v/assert kb (list 'genlCx CxB CxA) U mono)
      (v/assert kb (list 'binary_predicate carriesLoad) U mono)
      (v/assert kb (list 'transitiveInArgInverse carriesLoad 1 'genl) U mono)
      (v/assert kb (list 'genl hauler_kind 'animal) U mono)
      (v/assert kb (list 'genl cart_kind hauler_kind) U mono)
      (let [claim  (v/assert kb (list carriesLoad hauler_kind Bone) U mono)
            except #(v/assert kb (list 'except (list 'sentexHandle claim)) CxB mono)
            denial #(v/assert kb (list 'not (list carriesLoad cart_kind Bone)) CxA)
            d      (if except-first? (do (except) (denial)) (let [d (denial)] (except) d))]
        (testing (if except-first? "the except first" "the denial first")
          (is (false? (v/believed? kb d CxA)) "CxA reads the known-true claim and the denial loses")
          (is (true? (v/believed? kb d CxB)) "CxB reads no claim, and believes the denial"))))))

(defn- default-reason-reading
  "`[T believed, denial believed, contradicts stored]` at CxR once `ops` run in order.

  ```
  CxUniverse
   └─ CxB   (binary_predicate bigOf) (genl side top) :monotonic       :edge
       │    (transitiveInArgInverse bigOf 1 genl) :default, T          :decl
       └─ CxR  (bigOf Side Mid) :monotonic, the claim                 :claim
               (not (bigOf Top Mid)) :monotonic, the stored denial    :denial
  ```"
  [ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [bigOf side top Mid CxB CxR]
      (v/assert kb (list 'genlCx CxB U) U)
      (v/assert kb (list 'genlCx CxR CxB) U)
      (v/assert kb (list 'binary_predicate bigOf) CxB mono)
      (let [hs (reduce (fn [hs op]
                         (assoc hs op
                                (case op
                                  :edge   (v/assert kb (list 'genl side top) CxB mono)
                                  :decl   (v/assert kb (list 'transitiveInArgInverse bigOf 1 'genl) CxB)
                                  :claim  (v/assert kb (list bigOf side Mid) CxR mono)
                                  :denial (v/assert kb (list 'not (list bigOf top Mid)) CxR mono))))
                       {} ops)]
        [(v/believed? kb (:decl hs) CxR)
         (v/believed? kb (:denial hs) CxR)
         (boolean (seq (v/sentexes-with-functor kb 'contradicts)))]))))

(defn- permutations [xs]
  (if (empty? xs)
    [[]]
    (for [x xs, more (permutations (remove #{x} xs))] (cons x more))))

(tu/deftest-kb a-reading-resting-on-a-default-reason-is-undercut-and-the-denial-stands
  ;; The claim is known-true and the declaration is :default, so the reading is :default
  ;; and the stored denial undercuts it: no nogood forms, in every arrival order.
  (is (= #{[true true false]}
         (into #{} (map default-reason-reading) (permutations [:edge :decl :claim :denial])))))

(tu/deftest-kb an-inherited-clash-is-placed-at-its-vantage-and-no-reader-decides-it
  ;;   CxUniverse  the vocabulary, every reason :monotonic
  ;;     ├─ CxHigh  (carriesLoad hauler_kind Bone1) :monotonic, the general claim
  ;;     └─ CxLow   (not (carriesLoad cart_kind Bone1)) :default, the stored denial
  ;;          CxJoin under both
  ;; The clash is read whole at CxJoin alone, so the `contradicts` and the denial's
  ;; `defeat` are placed there, justified by the members; retracting the general claim
  ;; takes both OUT.
  (tu/with-terms [carriesLoad hauler_kind cart_kind CxHigh CxLow CxJoin]
    (vocabulary! kb {:pred carriesLoad :hauler hauler_kind :cart cart_kind})
    (doseq [c [CxHigh CxLow]]
      (v/assert kb (list 'genlCx c U) U)
      (v/assert kb (list 'genlCx CxJoin c) U))
    (let [claim  (v/assert kb (list carriesLoad hauler_kind 'Bone1) CxHigh mono)
          deny   (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) CxLow)
          placed (fn [] (into #{} (for [f '[contradicts defeat]
                                        s (v/sentexes-with-functor kb f)
                                        :when (v/in? kb (:id s))]
                                    [f (:context s)])))]
      (is (= #{['contradicts CxJoin] ['defeat CxJoin]} (placed)))
      (is (false? (v/believed? kb deny CxJoin)))
      (is (true? (v/believed? kb deny CxLow)))
      (v/retract! kb claim)
      (is (= #{} (placed))))))

(defn- meta-except-reading
  "`[placed denial-at-below denial-at-base placed-after]` once `ops` run in order: the
  placed `contradicts` and `defeat` as `[functor :base|:below]`, the denial's belief at
  each context, and the placed set once the meta-except is retracted.

  ```
  CxUniverse  the declaration and (genl hauler animal), :monotonic
   └─ CxBase   (genl cart hauler) :monotonic, E                     :edge
       │       (carriesLoad hauler Bone1) :monotonic, the claim     :claim
       │       (not (carriesLoad cart Bone1)) :default, the denial  :deny
       │       (except E)                                           :except
       └─ CxBelow (except <the except of E>)                        :meta
  ```"
  [ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [carriesLoad hauler_kind cart_kind CxBase CxBelow]
      (vocabulary! kb {:pred carriesLoad :hauler hauler_kind :cart cart_kind} :edge? false)
      (v/assert kb (list 'genlCx CxBase U) U)
      (v/assert kb (list 'genlCx CxBelow CxBase) U)
      (let [hs     (reduce (fn [hs op]
                             (assoc hs op
                                    (case op
                                      :edge   (v/assert kb (list 'genl cart_kind hauler_kind) CxBase mono)
                                      :claim  (v/assert kb (list carriesLoad hauler_kind 'Bone1) CxBase mono)
                                      :deny   (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) CxBase)
                                      :except (v/assert kb (list 'except (list 'sentexHandle (:edge hs))) CxBase)
                                      :meta   (v/assert kb (list 'except (list 'sentexHandle (:except hs))) CxBelow))))
                           {} ops)
            names  {CxBase :base CxBelow :below}
            placed (fn [] (into #{} (for [f '[contradicts defeat]
                                          s (v/sentexes-with-functor kb f)
                                          :when (v/in? kb (:id s))]
                                      [f (names (:context s) (:context s))])))
            now    [(placed) (v/believed? kb (:deny hs) CxBelow) (v/believed? kb (:deny hs) CxBase)]]
        (v/retract! kb (:meta hs))
        (conj now (placed))))))

(tu/deftest-kb an-inherited-clash-a-meta-except-restores-below-its-members-is-placed-there
  ;; The except hides the reason edge at CxBase, so the clash is whole at CxBelow alone,
  ;; where the meta-except shows the edge again.  Every arrival order with the edge before
  ;; its except and the except before the meta-except.
  (let [orders (filter #(let [i (zipmap % (range))] (< (i :edge) (i :except) (i :meta)))
                       (permutations [:edge :except :meta :claim :deny]))]
    (is (= #{[#{['contradicts :below] ['defeat :below]} false true #{}]}
           (into #{} (map meta-except-reading) orders)))))

(defn- knocked-edge-reading
  "The placed `contradicts` and `defeat` sentexes as `[sentence context]`, each named
  handle spelled as its `[sentence context]` and each temporary by the name below, once
  `ops` run in order.

  ```
  CxUniverse  the declaration, (genl a mid) (genl mid hauler) :monotonic
   └─ CxBase   (genl a hauler) :default, G                               :edge
               (not (genl a hauler)) :monotonic, its negation defeat     :knock
               (carriesLoad hauler Bone1) :monotonic, the claim          :claim
               (not (carriesLoad a Bone1)) :default, the denial          :deny
  ```"
  [ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [carriesLoad hauler_kind mid_kind a_kind CxBase]
      (vocabulary! kb {:pred carriesLoad :hauler hauler_kind :cart a_kind} :edge? false)
      (v/assert kb (list 'genl a_kind mid_kind) U mono)
      (v/assert kb (list 'genl mid_kind hauler_kind) U mono)
      (v/assert kb (list 'genlCx CxBase U) U)
      (doseq [op ops]
        (case op
          :edge  (v/assert kb (list 'genl a_kind hauler_kind) CxBase)
          :knock (v/assert kb (list 'not (list 'genl a_kind hauler_kind)) CxBase mono)
          :claim (v/assert kb (list carriesLoad hauler_kind 'Bone1) CxBase mono)
          :deny  (v/assert kb (list 'not (list carriesLoad a_kind 'Bone1)) CxBase)))
      (let [names {a_kind 'a hauler_kind 'hauler mid_kind 'mid carriesLoad 'carriesLoad CxBase 'CxBase}
            spell (fn spell [x]
                    (cond (and (seq? x) (= 'sentexHandle (first x)))
                          (let [t (v/sentex kb (second x))] [(spell (:sentence t)) (spell (:context t))])
                          (seq? x) (map spell x)
                          :else    (names x x)))]
        (into #{} (for [f '[contradicts defeat]
                        s (v/sentexes-with-functor kb f)
                        :when (v/in? kb (:id s))]
                    [(spell (:sentence s)) (spell (:context s))]))))))

(tu/deftest-kb a-defeat-of-a-genl-edge-beside-an-inherited-clash-places-the-same-in-every-order
  ;; The reading climbs the known-true route through `mid`, and a placement reads no
  ;; defeat (ruling 13), so the defeat of G changes no inherited placement whichever
  ;; arrives first.
  (is (= #{#{'[(contradicts [(genl a hauler) CxBase] [(not (genl a hauler)) CxBase]) CxBase]
             '[(defeat [(genl a hauler) CxBase]) CxBase]
             '[(contradicts [(genl a mid) CxUniverse] [(genl mid hauler) CxUniverse]
                            [(not (carriesLoad a Bone1)) CxBase] [(carriesLoad hauler Bone1) CxBase]
                            [(transitiveInArgInverse carriesLoad 1 genl) CxUniverse])
               CxBase]
             '[(defeat [(not (carriesLoad a Bone1)) CxBase]) CxBase]}}
         (into #{} (map knocked-edge-reading) (permutations [:edge :knock :claim :deny])))))

(defn- hidden-cover-reading
  "`[placed denial-at-below denial-at-base placed-after]` once `ops` run in order: the
  placed `contradicts` and `defeat` as `[functor :base|:below]`, the denial's belief at
  each context, and the placed set once the except is retracted.  `shape` names what the
  covering reading differs in.

  ```
  CxUniverse  (genl hauler animal) :monotonic
   └─ CxBase   (carriesLoad hauler Bone1) :monotonic, the claim     :claim
       │       (not (carriesLoad cart Bone1)) :default, the denial  :deny
       │       :decl   the declaration, the cover; (genl cart hauler) beside it
       │       :route  (genl cart hauler), the cover; the declaration beside it
       │       :copy   (genl cart hauler), the cover; the declaration beside it
       └─ CxBelow  :decl   the declaration again                      :covered
                   :route  (genl cart mid) (genl mid hauler)          :covered
                   :copy   (genl cart hauler) again                   :covered
                   (except <the cover>)                               :except
  ```"
  [shape ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [carriesLoad hauler_kind mid_kind cart_kind CxBase CxBelow]
      (v/assert kb (list 'binary_predicate carriesLoad) U)
      (v/assert kb (list 'genl hauler_kind 'animal) U mono)
      (v/assert kb (list 'genlCx CxBase U) U)
      (v/assert kb (list 'genlCx CxBelow CxBase) U)
      (let [decl  (list 'transitiveInArgInverse carriesLoad 1 'genl)
            edge  (list 'genl cart_kind hauler_kind)
            _     (v/assert kb (if (= shape :decl) edge decl) CxBase mono)
            write (fn [hs op]
                    (case op
                      :cover   (v/assert kb (if (= shape :decl) decl edge) CxBase mono)
                      :covered (case shape
                                 :decl  (v/assert kb decl CxBelow mono)
                                 :copy  (v/assert kb edge CxBelow mono)
                                 :route (do (v/assert kb (list 'genl cart_kind mid_kind) CxBelow mono)
                                            (v/assert kb (list 'genl mid_kind hauler_kind) CxBelow mono)))
                      :claim   (v/assert kb (list carriesLoad hauler_kind 'Bone1) CxBase mono)
                      :deny    (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) CxBase)
                      :except  (v/assert kb (list 'except (list 'sentexHandle (:cover hs))) CxBelow)))
            hs    (reduce (fn [hs op] (assoc hs op (write hs op))) {} ops)
            names {CxBase :base CxBelow :below}
            placed (fn [] (into #{} (for [f '[contradicts defeat]
                                          s (v/sentexes-with-functor kb f)
                                          :when (v/in? kb (:id s))]
                                      [f (names (:context s) (:context s))])))
            now    [(placed) (v/believed? kb (:deny hs) CxBelow) (v/believed? kb (:deny hs) CxBase)]]
        (v/retract! kb (:except hs))
        (conj now (placed))))))

(tu/deftest-kb an-inherited-reading-whose-cover-an-except-hides-below-is-placed-there
  ;; At CxBase the clash rests on the cover.  At CxBelow the except hides the cover, so
  ;; CxBelow reads the covered reading, and a second clash is placed there.  Retracting
  ;; the except leaves the clash at CxBase alone.  Every arrival order with the cover
  ;; before its except.
  (let [orders (filter #(let [i (zipmap % (range))] (< (i :cover) (i :except)))
                       (permutations [:cover :covered :claim :deny :except]))]
    (doseq [shape [:decl :route :copy]]
      (is (= #{[#{['contradicts :base] ['defeat :base] ['contradicts :below] ['defeat :below]}
                false false #{['contradicts :base] ['defeat :base]}]}
             (into #{} (map #(hidden-cover-reading shape %)) orders))
          (str shape)))))

(tu/deftest-kb a-recovered-store-places-its-inherited-clashes-before-its-first-write
  ;; The known-true reading of (carriesLoad cart_kind Bone1) defeats the default denial.
  ;; The dump imported records-only holds the placed sentexes with no justification, so
  ;; the recover's discovery places the clash, in place and in a second KB opened over
  ;; the store.
  (tu/with-terms [carriesLoad hauler_kind cart_kind swims Nemo]
    (vocabulary! kb {:pred carriesLoad :hauler hauler_kind :cart cart_kind})
    (v/assert kb (list carriesLoad hauler_kind 'Bone1) U mono)
    (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) U)
    (doseq [reopen? [false true]]
      (testing (if reopen? "reopened" "in place")
        (let [[source recovered written]
              (tu/recovered-readings kb reopen? [(list 'not (list carriesLoad cart_kind 'Bone1)) U]
                                     #(v/assert % (list swims Nemo) U))]
          (is (false? (:loser source)))
          (is (= 2 (count (:placed source))))
          (is (= source recovered) "before any write")
          (is (= source written) "after an unrelated write"))))))

(defn- merged-reading
  "`{:reported :rr}` once `ops` run in order: the reported inherited clashes' sentences, and
  whether CxUniverse believes `(rr Aa)`.  `claimed` is the spelling the claim is written
  with: Zz, the denial's, or Aa, the representative's.

  ```
  CxUniverse  the declaration and (genl cart hauler) :monotonic
              (carriesLoad hauler <claimed>) :monotonic, the claim        :claim
              (not (carriesLoad cart Zz)) :default, the denial            :deny
              (not (carriesLoad ?k ?x)) => (rr ?x) forward                :rule
              (rewriteOf Aa Zz) :monotonic, the merge                     :merge
  ```"
  [claimed ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [carriesLoad hauler_kind cart_kind rr Aa Zz]
      (vocabulary! kb {:pred carriesLoad :hauler hauler_kind :cart cart_kind})
      (doseq [op ops]
        (case op
          :claim (v/assert kb (list carriesLoad hauler_kind ({:Zz Zz :Aa Aa} claimed)) U mono)
          :deny  (v/assert kb (list 'not (list carriesLoad cart_kind Zz)) U)
          :rule  (v/assert kb (list 'implies (list 'not (list carriesLoad '?k '?x)) (list rr '?x)) U
                           {:direction :forward})
          :merge (v/assert kb (list 'rewriteOf Aa Zz) U mono)))
      (let [names {carriesLoad 'carriesLoad hauler_kind 'hauler cart_kind 'cart Aa 'Aa Zz 'Zz}
            rr-aa (v/handle-of kb (list rr Aa) U)]
        {:reported (into #{} (map #(walk/postwalk (fn [x] (names x x)) (:sentence %)))
                         (inherited-reports kb))
         :rr       (boolean (and rr-aa (v/believed? kb rr-aa U)))}))))

(tu/deftest-kb an-inherited-clash-over-a-merged-term-reads-alike-in-every-arrival-order
  ;; The merge makes `(not (carriesLoad cart Zz))` and `(not (carriesLoad cart Aa))` one
  ;; sentence, which the known-true reading defeats unreported, so CxUniverse believes no
  ;; `(rr Aa)` in all 24 orders.  With the merge last, a stored
  ;; `(rr Zz)` restates as `(rr Aa)` under `[(rr Zz) (rewriteOf Aa Zz)]`.
  (doseq [claimed [:Zz :Aa]]
    (let [rs (into #{} (map #(merged-reading claimed %)) (permutations [:claim :deny :rule :merge]))]
      (is (= #{{:rr false :reported #{}}} rs)
          (str claimed)))))

;; ---- a membership of a separated type --------------------------------------

(defn- separated-reading
  "What a KB reads after `(partition whole_kind down_kind up_kind)`, `down_kind` preserved
  down `genl` and `up_kind` up it, `(genl lower upper)`, `(down_kind upper)` and `(up_kind
  lower)`, the writes in `order`: the inherited sentences reported, spelled by role, and
  whether `(up_kind lower)` and `(up_kind upper)` are believed.  `(up_kind lower)` is
  written at `strength`, and every other sentence `:monotonic`.  With `retract?`, the
  partition is retracted after the last write."
  [kb strength order & {:keys [retract?]}]
  (tu/with-terms [whole_kind down_kind up_kind upper_kind lower_kind]
    (v/assert kb (list 'transitiveInArgInverse down_kind 1 'genl) U mono)
    (v/assert kb (list 'transitiveInArg up_kind 1 'genl) U mono)
    (let [sep   (list 'partition whole_kind down_kind up_kind)
          write {:sep  #(v/assert kb sep U mono)
                 :edge #(v/assert kb (list 'genl lower_kind upper_kind) U mono)
                 :down #(v/assert kb (list down_kind upper_kind) U mono)
                 :up   #(v/assert kb (list up_kind lower_kind) U {:strength strength})}
          role  {down_kind 'down up_kind 'up upper_kind 'upper lower_kind 'lower}]
      (doseq [k order] ((write k)))
      (when retract? (v/retract! kb (v/handle-of kb sep U)))
      [(into #{}
             (map #(walk/postwalk-replace role (:sentence (:inherited %))))
             (concat (inherited-reports kb down_kind) (inherited-reports kb up_kind)))
       (v/ask? kb (list up_kind lower_kind) U)
       (v/ask? kb (list up_kind upper_kind) U)])))

(tu/deftest-kb a-membership-beside-a-known-true-inherited-membership-of-a-separated-type-is-a-nogood-in-every-order
  ;; `(down upper)` reaches `(down lower)`, and `(up lower)` reaches `(up upper)`, so each
  ;; type is a member of both parts.  Known-true throughout, the two clashes are conflicts
  ;; and every member stays believed, and `ask` answers `(up upper)` in neither direction,
  ;; since the stored `(down upper)` denies it.  With `(up lower)` a default, it is the
  ;; unique weakest member of the clash with `(down lower)` and goes OUT, taking `(up
  ;; upper)` with it, and the resolved clash is reported by neither reading.
  (is (= {:monotonic #{[#{'(down lower) '(up upper)} true false]}
          :default   #{[#{} false false]}}
         (into {}
               (for [strength [:monotonic :default]]
                 [strength (into #{} (map #(separated-reading kb strength %))
                                 (permutations [:sep :edge :down :up]))])))))

(tu/deftest-kb retracting-the-separation-withdraws-the-inherited-membership-clash
  (is (= #{[#{} true true]}
         (into #{} (map #(separated-reading kb :default % :retract? true))
               [[:sep :edge :down :up] [:edge :down :up :sep]]))))

(tu/deftest-kb a-membership-of-a-type-no-declaration-names-is-denied-by-a-separated-inherited-one
  ;; `plain_kind` carries nothing, so the one clash is `(plain lower)` beside the
  ;; `(down lower)` that `(down upper)` reaches.
  (is (= #{[#{'(down lower)} true]}
         (into #{}
               (for [order (permutations [:sep :edge :down :plain])]
                 (tu/with-terms [down_kind plain_kind upper_kind lower_kind]
                   (v/assert kb (list 'transitiveInArgInverse down_kind 1 'genl) U mono)
                   (let [write {:sep   #(v/assert kb (list 'disjoint down_kind plain_kind) U mono)
                                :edge  #(v/assert kb (list 'genl lower_kind upper_kind) U mono)
                                :down  #(v/assert kb (list down_kind upper_kind) U mono)
                                :plain #(v/assert kb (list plain_kind lower_kind) U mono)}]
                     (doseq [k order] ((write k)))
                     [(into #{}
                            (map #(walk/postwalk-replace {down_kind 'down lower_kind 'lower}
                                                         (:sentence (:inherited %))))
                            (inherited-reports kb down_kind))
                      (v/ask? kb (list plain_kind lower_kind) U)])))))))

(tu/deftest-kb a-recover-asks-the-memberships-stored-claims-reach-and-none-of-an-unclaimed-predicate
  ;; `disjoint` separates every `plain_kind` membership from the preserved `down_kind`.
  ;; With no `down_kind` claim stored, recover's discovery asks none of the 41; once
  ;; `(down upper)` is stored it asks that claim and `(plain lower)`, the one membership
  ;; it reaches.  The `::asked` log line counts the questions.
  (tu/with-terms [down_kind plain_kind upper_kind lower_kind]
    (let [recover! (fn []
                     (let [asked (atom [])]
                       (binding [trove/*log-fn* (fn [_ns _coords _level id payload]
                                                  (when (= :vaelii.impl.discovery/asked id)
                                                    (swap! asked conj (:data (force payload)))))]
                         (v/recover kb))
                       (:asked (first @asked))))]
      (v/assert kb (list 'transitiveInArgInverse down_kind 1 'genl) U mono)
      (v/assert kb (list 'disjoint down_kind plain_kind) U mono)
      (v/assert kb (list 'genl lower_kind upper_kind) U mono)
      (v/assert kb (list plain_kind lower_kind) U mono)
      (dotimes [_ 40] (v/assert kb (list plain_kind (tu/tmp-ind "Beast")) U))
      (is (= 0 (recover!)))
      (v/assert kb (list down_kind upper_kind) U mono)
      (is (= 1 (count (inherited-reports kb down_kind))))
      (is (= 2 (recover!)))
      (is (= 1 (count (inherited-reports kb down_kind)))))))
