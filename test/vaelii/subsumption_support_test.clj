;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.subsumption-support-test
  "**A firing that matched by subsumption rests on the `genl` edges it subsumed
  through**, and says so.

  Matching fans an antecedent's functor over its spec closure, so `(fatherOf Tom Bob)`
  satisfies a rule written about `(parentOf ?x ?y)` — on the strength of
  `(genl fatherOf parentOf)`, which is an ordinary sentex somebody asserted and can
  take back.  A justification that named only the fact and the rule left the conclusion
  standing on an edge that was gone.

  So the firing's justification names a **witness** for each subsumption: one `genl`
  path, one supporter per edge, drawn from what the *placement context* can see.  A
  section per consequence below — `why` shows the edges, retracting one withdraws what
  it licensed, defeating one puts the conclusion OUT (and its class is capped by the
  edge's own), a reachability that outlives the named witness re-derives, and the
  witness a placement names is one it can see and does not move with assertion order.

  A witness, not every witness: a second route (a second supporter of one edge, or a
  second path around it) does not carry a second justification, so it costs a
  re-derivation at a fresh handle rather than a justification per path through a
  hierarchy where paths multiply.  That is the same bargain the qualitative support
  makes (docs/qcn.md) and the same one `exceptWhen` revival makes."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.ref.gen :as gen]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defn- antecedent-sentences
  "The sentences of everything the (single) justification of `handle` rests on — what
  `why` walks into, the rule included."
  [kb handle]
  (->> (v/supporting-justifications kb handle)
       (mapcat :antecedents)
       (map #(:sentence (v/sentex kb %)))
       set))

;; ---- what the justification names ---------------------------------------

(tu/deftest-kb a-subsuming-firing-names-the-edge-it-subsumed-through
  (tu/with-terms [fatherOf parentOf ancestorOf Tom Bob]
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
    (v/assert kb (list 'implies (list parentOf '?x '?y) (list ancestorOf '?x '?y)) 'CxUniverse {:direction :forward})
    (v/assert kb (list fatherOf Tom Bob) 'CxUniverse)
    (let [derived (v/handle-of kb (list ancestorOf Tom Bob) 'CxUniverse)]
      (is (v/in? kb derived) "the rule fired by subsumption")
      (testing "the edge is an antecedent, beside the fact and the rule"
        (is (contains? (antecedent-sentences kb derived) (list 'genl fatherOf parentOf))))
      (testing "so `why` shows it, rather than a proof that skips how the fact matched"
        (let [because (->> (tu/why-root kb derived) :support first :because (map :sentence) set)]
          (is (contains? because (list 'genl fatherOf parentOf))))))))

(tu/deftest-kb an-ordinary-firing-names-no-edge
  ;; the control: subsumption is what pulls the taxonomy into a justification, so a
  ;; firing whose fact carries the antecedent's own functor must rest on nothing but
  ;; the fact and the rule — otherwise the section above proves only that the
  ;; antecedent list grew.
  (tu/with-terms [parentOf ancestorOf Tom Bob]
    (v/assert kb (list 'implies (list parentOf '?x '?y) (list ancestorOf '?x '?y)) 'CxUniverse {:direction :forward})
    (v/assert kb (list parentOf Tom Bob) 'CxUniverse)
    (let [derived (v/handle-of kb (list ancestorOf Tom Bob) 'CxUniverse)]
      (is (= 1 (count (:antecedents (first (v/supporting-justifications kb derived)))))
          "the fact, and nothing else beside the rule it names as informant"))))

(tu/deftest-kb every-edge-on-the-path-is-named
  ;; subsumption is transitive, so a two-step climb rests on two edges and either one
  ;; of them is enough to withdraw the conclusion
  (tu/with-terms [dog_t mammal_t animal_t breathes Muffet]
    (v/assert kb (list 'genl dog_t mammal_t) 'CxUniverse)
    (v/assert kb (list 'genl mammal_t animal_t) 'CxUniverse)
    (v/assert kb (list 'implies (list animal_t '?x) (list breathes '?x)) 'CxUniverse {:direction :forward})
    (v/assert kb (list dog_t Muffet) 'CxUniverse)
    (let [derived (v/handle-of kb (list breathes Muffet) 'CxUniverse)
          antes   (antecedent-sentences kb derived)]
      (is (v/in? kb derived))
      (is (contains? antes (list 'genl dog_t mammal_t)))
      (is (contains? antes (list 'genl mammal_t animal_t))))))

;; ---- retracting the edge withdraws what it licensed ----------------------

(tu/deftest-kb retracting-the-edge-withdraws-the-conclusion
  (tu/with-terms [fatherOf parentOf ancestorOf Tom Bob]
    (let [edge (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)]
      (v/assert kb (list 'implies (list parentOf '?x '?y) (list ancestorOf '?x '?y)) 'CxUniverse {:direction :forward})
      (v/assert kb (list fatherOf Tom Bob) 'CxUniverse)
      (is (seq (v/sentexes-matching kb (list ancestorOf Tom Bob) 'CxUniverse)))
      (v/retract! kb edge)
      (testing "with the edge gone the fact no longer satisfies the rule, so neither does the conclusion stand"
        (is (empty? (v/sentexes-matching kb (list ancestorOf Tom Bob) 'CxWell))))
      (testing "and the ingredients that were not retracted are all still believed"
        (is (seq (v/sentexes-matching kb (list fatherOf Tom Bob) 'CxUniverse)))))))

(tu/deftest-kb retracting-one-edge-of-a-chain-withdraws-the-conclusion
  (tu/with-terms [dog_t mammal_t animal_t breathes Muffet]
    (v/assert kb (list 'genl dog_t mammal_t) 'CxUniverse)
    (let [upper (v/assert kb (list 'genl mammal_t animal_t) 'CxUniverse)]
      (v/assert kb (list 'implies (list animal_t '?x) (list breathes '?x)) 'CxUniverse {:direction :forward})
      (v/assert kb (list dog_t Muffet) 'CxUniverse)
      (is (seq (v/sentexes-matching kb (list breathes Muffet) 'CxUniverse)))
      (v/retract! kb upper)
      (is (empty? (v/sentexes-matching kb (list breathes Muffet) 'CxUniverse))
          "the climb needed both edges, so losing the upper one is enough"))))

(tu/deftest-kb a-retracted-edge-takes-the-whole-cascade-with-it
  ;; the conclusion is an ordinary datum, so what rests on *it* goes too — the
  ;; dependency-directed sweep needs no special case for a taxonomy edge
  (tu/with-terms [fatherOf parentOf ancestorOf relatedTo Tom Bob]
    (let [edge (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)]
      (v/assert kb (list 'implies (list parentOf '?x '?y) (list ancestorOf '?x '?y)) 'CxUniverse {:direction :forward})
      (v/assert kb (list 'implies (list ancestorOf '?x '?y) (list relatedTo '?x '?y)) 'CxUniverse {:direction :forward})
      (v/assert kb (list fatherOf Tom Bob) 'CxUniverse)
      (is (seq (v/sentexes-matching kb (list relatedTo Tom Bob) 'CxUniverse)))
      (v/retract! kb edge)
      (is (empty? (v/sentexes-matching kb (list relatedTo Tom Bob) 'CxUniverse))))))

;; ---- the edge is an antecedent, so belief and strength both run through it ----

(tu/deftest-kb a-defeated-edge-puts-the-conclusion-out-and-a-revived-one-brings-it-back
  ;; defeat, not removal: the justification is structurally intact, so the sweep leaves
  ;; the conclusion alone, and the placed defeat of the edge removes it from belief.
  ;; Revival keeps the *same* handle, which is what distinguishes this from the
  ;; retraction cases below.
  (tu/with-terms [fatherOf parentOf ancestorOf Tom Bob]
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
    (v/assert kb (list 'implies (list parentOf '?x '?y) (list ancestorOf '?x '?y)) 'CxUniverse {:direction :forward})
    (v/assert kb (list fatherOf Tom Bob) 'CxUniverse {:strength :monotonic})
    (let [derived (v/handle-of kb (list ancestorOf Tom Bob) 'CxUniverse)
          nope    (v/assert kb (list 'not (list 'genl fatherOf parentOf)) 'CxUniverse
                            {:strength :monotonic})]
      (is (not (v/in? kb derived)) "the edge is not believed, so neither is what climbed it")
      (is (some? (v/sentex kb derived)) "stored all along — nothing was swept")
      (is (= :withdrawn (:reason (v/why-not kb derived))))
      (v/retract! kb nope)
      (is (v/in? kb derived) "and the edge coming back brings the conclusion back")
      (is (= derived (v/handle-of kb (list ancestorOf Tom Bob) 'CxUniverse))
          "at the same handle, not a re-derivation"))))

(tu/deftest-kb the-edge-caps-the-conclusion-s-defeat-class
  ;; a conclusion is never stronger than what it rests on, and the edge it climbed is
  ;; now one of those things: known-true fact + bare rule + *defeasible* edge is a
  ;; defeasible conclusion, however monotonic the fact.
  (tu/with-terms [fatherOf parentOf ancestorOf Tom Bob]
    (v/assert kb (list 'implies (list parentOf '?x '?y) (list ancestorOf '?x '?y)) 'CxUniverse {:direction :forward})
    (v/assert kb (list fatherOf Tom Bob) 'CxUniverse {:strength :monotonic})
    (testing "climbing a :default edge"
      (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
      (is (= :default (v/defeat-class kb (v/handle-of kb (list ancestorOf Tom Bob)
                                                      'CxUniverse)))))
    (testing "the control: no climb, and the conclusion is as strong as its grounds"
      (tu/with-terms [Ann Cat]
        (v/assert kb (list parentOf Ann Cat) 'CxUniverse {:strength :monotonic})
        (is (= :monotonic (v/defeat-class kb (v/handle-of kb (list ancestorOf Ann Cat)
                                                          'CxUniverse))))))))

;; ---- a reachability that outlives its named witness -----------------------

(tu/deftest-kb a-second-supporter-of-the-edge-keeps-the-conclusion
  ;; the same edge asserted from two contexts is two sentexes and one edge — both of
  ;; them visible from where the conclusion lands, or the second would license nothing
  ;; there anyway.  The justification names one, so retracting *that* one sweeps the
  ;; conclusion, and the surviving supporter re-derives it at a fresh handle.
  (tu/with-terms [fatherOf parentOf ancestorOf Tom Bob]
    (let [e1 (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
          e2 (v/assert kb (list 'genl fatherOf parentOf) 'CxWell)]
      (is (not= e1 e2) "two sentexes, one edge")
      (v/assert kb (list 'implies (list parentOf '?x '?y) (list ancestorOf '?x '?y)) 'CxWell {:direction :forward})
      (v/assert kb (list fatherOf Tom Bob) 'CxWell)
      (let [before (v/handle-of kb (list ancestorOf Tom Bob) 'CxWell)]
        (is (v/in? kb before))
        (v/retract! kb e1)
        (let [after (v/handle-of kb (list ancestorOf Tom Bob) 'CxWell)]
          (is (v/in? kb after)
              "the edge is still asserted, so the conclusion is still licensed")
          (is (not= before after)
              "as a re-derivation, not a survival: the sweep took the old record"))
        (v/retract! kb e2)
        (is (empty? (v/sentexes-matching kb (list ancestorOf Tom Bob) 'CxWell))
            "and only when the last supporter goes does the conclusion")))))

(tu/deftest-kb a-stated-edge-is-one-supporter-per-context-and-a-cover-is-one-more
  ;; The witness choice above keys on the asserting context first.  A sentence and a
  ;; context are what a handle is allocated for, so stating the edge twice from one context
  ;; is one sentex.  A `partition` installing the same edge is a second supporter in that
  ;; context, and `taxonomy/most-general-of` orders the two by the sentence each states.
  (tu/with-terms [dog_t pet_t cat_t]
    (let [a (v/assert kb (list 'genl dog_t pet_t) 'CxUniverse)
          b (v/assert kb (list 'genl dog_t pet_t) 'CxUniverse)
          c (v/assert kb (list 'genl dog_t pet_t) 'CxWell)
          p (v/assert kb (list 'partition pet_t dog_t cat_t) 'CxUniverse)
          support (tax/supporters (reasoning/taxonomy kb) [:genl dog_t pet_t])]
      (is (= a b) "one sentence in one context is one sentex, however often it is asserted")
      (is (not= a c) "a second context is a second sentex, and a second supporter")
      (is (= #{a c p} (set (keys support))))
      (is (= 'CxUniverse (support a) (support p))))))

(tu/deftest-kb a-second-path-around-the-edge-keeps-the-conclusion
  ;; multiple inheritance: dog reaches animal two ways.  Either edge can go.
  (tu/with-terms [dog_t mammal_t pet_t animal_t breathes Muffet]
    (v/assert kb (list 'genl dog_t mammal_t) 'CxUniverse)
    (v/assert kb (list 'genl dog_t pet_t) 'CxUniverse)
    (let [via-mammal (v/assert kb (list 'genl mammal_t animal_t) 'CxUniverse)
          via-pet    (v/assert kb (list 'genl pet_t animal_t) 'CxUniverse)]
      (v/assert kb (list 'implies (list animal_t '?x) (list breathes '?x)) 'CxUniverse {:direction :forward})
      (v/assert kb (list dog_t Muffet) 'CxUniverse)
      (is (seq (v/sentexes-matching kb (list breathes Muffet) 'CxUniverse)))
      (v/retract! kb via-mammal)
      (is (seq (v/sentexes-matching kb (list breathes Muffet) 'CxUniverse))
          "a dog is still an animal by the other route, so it still breathes")
      (v/retract! kb via-pet)
      (is (empty? (v/sentexes-matching kb (list breathes Muffet) 'CxUniverse))
          "with both routes gone the conclusion has nothing left to rest on"))))

(tu/deftest-kb a-derived-edge-a-partition-also-states-keeps-the-conclusion-when-its-premise-is-denied
  ;; the edge's rule firing goes OUT under the forced denial of its premise; the
  ;; `partition` still states the edge, so the firing that subsumed through it stands.
  ;; The last row states no `partition`, and the conclusion goes with the edge.
  (doseq [[order in?] [[[:rule :p :ev :fact :deny] true] [[:p :rule :fact :ev :deny] true]
                       [[:deny :ev :rule :p :fact] true] [[:rule :ev :fact :deny] false]]]
    (tu/with-terms [dog_t pet_t cat_t srcRel breathes Muffet]
      (doseq [s order]
        (case s
          :rule (v/assert kb (list 'implies (list srcRel '?a '?c) (list 'genl '?a '?c)) 'CxUniverse {:direction :forward})
          :ev   (v/assert kb (list srcRel dog_t pet_t) 'CxUniverse)
          :deny (v/assert kb (list 'not (list srcRel dog_t pet_t)) 'CxUniverse {:strength :monotonic})
          :p    (v/assert kb (list 'partition pet_t dog_t cat_t) 'CxUniverse)
          :fact (do (v/assert kb (list 'implies (list pet_t '?x) (list breathes '?x)) 'CxUniverse {:direction :forward})
                    (v/assert kb (list dog_t Muffet) 'CxUniverse))))
      (let [d (v/handle-of kb (list breathes Muffet) 'CxUniverse)]
        (is (= [order in? in?]
               [order (boolean (v/ask? kb (list breathes Muffet) 'CxUniverse)) (boolean (some->> d (v/in? kb)))]))))))

(tu/deftest-kb a-firing-stating-a-derived-edge-stands-only-where-its-second-supporter-is-believed
  ;; The rule states `(genl ?a pet_t)`, so its firing is read by its witness path.  The
  ;; edge's derivation goes OUT under the forced denial of its premise, and the
  ;; `partition` stating the edge too is visible (`:none`), hidden at CxEx by an except
  ;; (`:except`), or concluded from a `:default` premise (`:void`).  A `partition` is
  ;; forced-monotonic, so the `:void` firing is held void at every context
  ;; (`:forced-conclusion`), and the `partition` is OUT before and after `:hide`
  ;; denies the premise.
  (doseq [lose  [:none :except :void]
          order [[:edge :part :rule :deny :hide] [:rule :part :hide :deny :edge]
                 [:deny :part :hide :edge :rule] [:part :hide :rule :edge :deny]]]
    (tu/with-terms [dog_t pet_t cat_t srcRel srcPart tagged_t marked_t CxEx]
      (let [U    'CxUniverse
            part (list 'partition pet_t dog_t cat_t)]
        (v/assert kb (list 'genlCx CxEx U) U)
        (doseq [st order]
          (case st
            :edge (do (v/assert kb (list 'implies (list srcRel '?a '?c) (list 'genl '?a '?c)) U {:direction :forward})
                      (v/assert kb (list srcRel dog_t pet_t) U))
            :part (if (= :void lose)
                    (do (v/assert kb (list 'implies (list srcPart '?p '?a '?b) (list 'partition '?p '?a '?b)) U {:direction :forward})
                        (v/assert kb (list srcPart pet_t dog_t cat_t) U))
                    (v/assert kb part U))
            :rule (do (v/assert kb (list 'implies (list 'and (list 'genl '?a pet_t) (list tagged_t '?a)) (list marked_t '?a))
                                U {:direction :forward})
                      (v/assert kb (list tagged_t dog_t) U))
            :deny (v/assert kb (list 'not (list srcRel dog_t pet_t)) U {:strength :monotonic})
            :hide (case lose
                    :none   nil
                    :except (v/assert kb (list 'except (list 'sentexHandle (v/handle-of kb part U))) CxEx {:strength :monotonic})
                    :void   (v/assert kb (list 'not (list srcPart pet_t dog_t cat_t)) U {:strength :monotonic}))))
        (is (= [lose order (not= :void lose) (= :none lose)]
               [lose order (boolean (v/ask? kb (list marked_t dog_t) U))
                (boolean (v/ask? kb (list marked_t dog_t) CxEx))]))))))

(tu/deftest-kb the-edge-survives-a-rebuild-in-the-antecedent-list
  ;; a justification is a durable record, so the edges it names are durable state —
  ;; `recover` rebuilds the JTMS from those records and must hand back the same
  ;; dependency, or a restart would quietly restore the standing-on-nothing conclusion
  (tu/with-terms [fatherOf parentOf ancestorOf Tom Bob]
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
    (v/assert kb (list 'implies (list parentOf '?x '?y) (list ancestorOf '?x '?y)) 'CxUniverse {:direction :forward})
    (v/assert kb (list fatherOf Tom Bob) 'CxUniverse)
    (let [derived (v/handle-of kb (list ancestorOf Tom Bob) 'CxUniverse)
          before  (antecedent-sentences kb derived)]
      (v/recover kb)
      (is (= before (antecedent-sentences kb derived)))
      (is (v/in? kb derived) "and it is still believed")
      (v/retract! kb (v/handle-of kb (list 'genl fatherOf parentOf) 'CxUniverse))
      (is (empty? (v/sentexes-matching kb (list ancestorOf Tom Bob) 'CxUniverse))
          "so the rebuilt dependency still withdraws"))))

(tu/deftest-kb an-edit-that-removes-an-edge-settles-once-and-re-derives
  ;; the batch path owes the same re-chain the single retraction does — one settle,
  ;; adds before removes, and what the surviving route licenses is back at the end
  (tu/with-terms [dog_t mammal_t pet_t animal_t breathes Muffet Rex]
    (v/assert kb (list 'genl dog_t mammal_t) 'CxUniverse)
    (v/assert kb (list 'genl dog_t pet_t) 'CxUniverse)
    (let [via-mammal (v/assert kb (list 'genl mammal_t animal_t) 'CxUniverse)]
      (v/assert kb (list 'genl pet_t animal_t) 'CxUniverse)
      (v/assert kb (list 'implies (list animal_t '?x) (list breathes '?x)) 'CxUniverse {:direction :forward})
      (v/assert kb (list dog_t Muffet) 'CxUniverse)
      (is (seq (v/sentexes-matching kb (list breathes Muffet) 'CxUniverse)))
      (v/edit! kb {:add [[(list dog_t Rex) 'CxUniverse]] :remove [via-mammal]})
      (is (seq (v/sentexes-matching kb (list breathes Muffet) 'CxUniverse))
          "the other route survived the batch, so the old conclusion is back")
      (is (seq (v/sentexes-matching kb (list breathes Rex) 'CxUniverse))
          "and the added fact concluded through it too"))))

(tu/deftest-kb a-preview-of-removing-the-edge-reports-what-it-would-take
  ;; `preview` reads belief off a suspended premise rather than a retracted one, so it
  ;; can now answer "what does this taxonomy edge hold up?" — a question that had no
  ;; answer while the conclusion rested on the facts alone
  (tu/with-terms [fatherOf parentOf ancestorOf Tom Bob]
    (let [edge (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)]
      (v/assert kb (list 'implies (list parentOf '?x '?y) (list ancestorOf '?x '?y)) 'CxUniverse {:direction :forward})
      (v/assert kb (list fatherOf Tom Bob) 'CxUniverse)
      (let [removed (set (map :sentence (:believed-removed (v/preview kb {:remove [edge]} {}))))]
        (is (contains? removed (list ancestorOf Tom Bob))
            "the conclusion the edge licensed is named as a casualty"))
      (is (seq (v/sentexes-matching kb (list ancestorOf Tom Bob) 'CxUniverse))
          "and the preview put the KB back"))))

;; ---- the edge contexts are an ingredient of the placement ----------------
;;
;; A firing rests on three things — the rule, the antecedent facts, and the taxonomy it
;; climbed — and placement is the one rule that governs all three: the maximal contexts
;; that see every one of them.  So an edge stated where the natural placement cannot see
;; it does not kill the conclusion; it pulls it down to where it *can* be seen.

(defn- lattice!
  "Two incomparable contexts under CxUniverse and two incomparable contexts
  below both of them — the smallest shape in which an edge can be invisible from a
  placement and still visible from somewhere."
  [kb a b & belows]
  (v/assert kb (list 'genlCx a 'CxUniverse) 'CxUniverse)
  (v/assert kb (list 'genlCx b 'CxUniverse) 'CxUniverse)
  (doseq [d belows]
    (v/assert kb (list 'genlCx d a) 'CxUniverse)
    (v/assert kb (list 'genlCx d b) 'CxUniverse)))

(tu/deftest-kb an-edge-the-natural-placement-cannot-see-lowers-it-rather-than-killing-it
  (tu/with-terms [fatherOf parentOf ancestorOf Tom Bob
                  CxKin CxGeo CxSaga CxEpic]
    (lattice! kb CxKin CxGeo CxSaga CxEpic)
    ;; the taxonomy is Kin's; the rule and the fact are Geo's — no context is both
    (v/assert kb (list 'genl fatherOf parentOf) CxKin)
    (v/assert kb (list 'implies (list parentOf '?x '?y) (list ancestorOf '?x '?y)) CxGeo {:direction :forward})
    (v/assert kb (list fatherOf Tom Bob) CxGeo)
    (testing "not in Geo, which holds the rule and the fact but not the edge"
      (is (empty? (v/sentexes-matching kb (list ancestorOf Tom Bob) CxGeo))))
    (testing "but in every maximal context that sees all three"
      (is (= [CxEpic CxSaga]
             (sort (mapv :context (v/sentexes-matching kb (list ancestorOf Tom Bob) '?ctx))))))
    (testing "and each of them names the edge it climbed"
      (let [d (v/handle-of kb (list ancestorOf Tom Bob) CxSaga)]
        (is (contains? (antecedent-sentences kb d) (list 'genl fatherOf parentOf)))))
    (testing "so retracting the edge withdraws it from both"
      (v/retract! kb (v/handle-of kb (list 'genl fatherOf parentOf) CxKin))
      (is (empty? (v/sentexes-matching kb (list ancestorOf Tom Bob) '?ctx))))))

(tu/deftest-kb with-no-context-below-both-there-is-still-nothing-to-place
  ;; the control: descending is only possible where there is somewhere to descend *to*.
  ;; Two bare siblings and the conclusion evaporates, reported against the subsumption
  ;; rather than against the facts.
  (tu/with-terms [fatherOf parentOf ancestorOf Tom Bob CxA CxB]
    (lattice! kb CxA CxB)
    (v/assert kb (list 'genl fatherOf parentOf) CxA)
    (v/assert kb (list 'implies (list parentOf '?x '?y) (list ancestorOf '?x '?y)) CxB {:direction :forward})
    (v/assert kb (list fatherOf Tom Bob) CxB)
    (is (empty? (v/sentexes-matching kb (list ancestorOf Tom Bob) '?ctx)))
    (let [d (:detail (last (filter #(= :no-placement (:violation %)) (v/violations kb))))]
      (is (= [fatherOf] (:subsumed d)))
      (is (= [CxB] (:would-place d))
          "and the report names the context the edges cost it"))))

(tu/deftest-kb a-placement-that-already-sees-an-edge-does-not-descend
  ;; the edge is asserted in *both* contexts, so B — where the rule and fact are —
  ;; can see a witness of its own.  The edges add no constraint there, and the
  ;; conclusion stays as general as it was: in B, not below it.  Choosing one witness
  ;; globally would pick A's half the time and drop B out of the placement entirely.
  (tu/with-terms [fatherOf parentOf ancestorOf Tom Bob
                  CxA CxB CxSaga]
    (lattice! kb CxA CxB CxSaga)
    (v/assert kb (list 'genl fatherOf parentOf) CxA)
    (v/assert kb (list 'genl fatherOf parentOf) CxB)
    (v/assert kb (list 'implies (list parentOf '?x '?y) (list ancestorOf '?x '?y)) CxB {:direction :forward})
    (v/assert kb (list fatherOf Tom Bob) CxB)
    (is (= [CxB] (mapv :context (v/sentexes-matching kb (list ancestorOf Tom Bob) '?ctx))))))

(defn- descended-under-an-except
  "`[before after]`: is `(concl Fido)` believed at CxR once `order` runs, and again once
  the edge CxR does not except is retracted.  `(genl ta tb)` is stated in CxG and in CxS
  below it, CxR below CxS excepts the `hide` one, and the rule and `(ta Fido)` are in
  CxUniverse, so the conclusion descends to a context that sees an edge."
  [kb order hide]
  (tu/with-terms [CxG CxS CxR ta tb concl Fido]
    (v/assert kb (list 'genlCx CxG 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxS CxG) 'CxUniverse)
    (v/assert kb (list 'genlCx CxR CxS) 'CxUniverse)
    (let [hs       (atom {})
          step     {:hg     #(swap! hs assoc :hg (v/assert kb (list 'genl ta tb) CxG))
                    :hs     #(swap! hs assoc :hs (v/assert kb (list 'genl ta tb) CxS))
                    :fact   #(v/assert kb (list ta Fido) 'CxUniverse)
                    :rule   #(v/assert kb (list 'implies (list tb '?x) (list concl '?x))
                                       'CxUniverse {:direction :forward})
                    :except #(v/assert kb (list 'except (list 'sentexHandle (get @hs hide))) CxR)}
          believed (fn [] (boolean (some #(:believed? (v/belief-status kb (:id %) CxR))
                                         (v/sentexes-matching kb (list concl Fido) '?ctx))))]
      (doseq [s order] ((step s)))
      (let [before (believed)]
        (v/retract! kb (get @hs ({:hg :hs :hs :hg} hide)))
        [before (believed)]))))

(defn- except-orders
  "Every order of the five writes in which the except follows the edge it names."
  [hide]
  (filterv #(< (.indexOf ^java.util.List % hide) (.indexOf ^java.util.List % :except))
           (gen/permutations [:hg :hs :fact :rule :except])))

(tu/deftest-kb a-descended-conclusion-is-believed-where-an-except-hides-one-of-two-edges
  ;; CxR sees the edge it does not except, so it believes the conclusion, and retracting
  ;; that edge withdraws it there.  The sampled orders include the ones that place the
  ;; conclusion in CxS as well as CxG.
  (doseq [hide [:hg :hs]
          order [[:hg :hs :fact :rule :except] [:hs :fact :rule :hg :except]
                 [:rule :fact :hs :hg :except]]]
    (is (= [true false] (descended-under-an-except kb order hide)) (pr-str hide order))))

(tu/deftest-kb ^:slow a-descended-conclusion-is-believed-where-an-except-hides-one-of-two-edges-in-every-order
  (doseq [hide [:hg :hs]]
    (is (= #{[true false]} (into #{} (map #(descended-under-an-except kb % hide)) (except-orders hide)))
        (pr-str hide))))

;; ---- the witness is the placement's, and it is a function of content ------

(tu/deftest-kb the-named-edge-is-one-the-placement-can-see
  ;; the edge is asserted twice — once where the conclusion lands, once in a sibling
  ;; context the conclusion's context cannot see.  Naming the invisible one would
  ;; make the conclusion rest on something its own context does not hold.
  (tu/with-terms [fatherOf parentOf ancestorOf Tom Bob CxA CxB]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genl fatherOf parentOf) CxA)
    (v/assert kb (list 'genl fatherOf parentOf) CxB)
    (v/assert kb (list 'implies (list parentOf '?x '?y) (list ancestorOf '?x '?y)) CxB {:direction :forward})
    (v/assert kb (list fatherOf Tom Bob) CxB)
    (let [derived (v/handle-of kb (list ancestorOf Tom Bob) CxB)]
      (is (v/in? kb derived))
      (let [edges (->> (v/supporting-justifications kb derived)
                       (mapcat :antecedents)
                       (map #(v/sentex kb %))
                       (filter #(= 'genl (first (:sentence %)))))]
        (is (seq edges))
        (is (every? #(v/sees? kb CxB (:context %)) edges)
            "every edge the conclusion rests on is one its own context sees")))))

(tu/deftest-kb the-witness-does-not-depend-on-assertion-order
  ;; Which of two supporters gets named is keyed on the asserting **context**, never on
  ;; the handle — a handle is allocated in assertion order, and belief may not depend on
  ;; that (docs/nmtms.md).  Two independent predicate hierarchies, each supported from
  ;; the same two contexts, asserted in opposite orders: a handle-keyed choice would
  ;; name the first-asserted one and so answer differently for the two.
  ;;
  ;; The **placement** goes with it and is checked beside it, because that is what the
  ;; choice is for: a conclusion resting on an edge belongs no higher than a context that
  ;; can see the supporter named, so a witness that moved with arrival order would move
  ;; the conclusion's context with it.
  (let [above (tu/tmp-ctx "Mid") low (tu/tmp-ctx "Low")]
    (v/assert kb (list 'genlCx low above) 'CxUniverse)
    (letfn [(witness [ctx-a ctx-b]
              (tu/with-terms [fatherOf parentOf ancestorOf Tom Bob]
                (v/assert kb (list 'genl fatherOf parentOf) ctx-a)
                (v/assert kb (list 'genl fatherOf parentOf) ctx-b)
                (v/assert kb (list 'implies (list parentOf '?x '?y) (list ancestorOf '?x '?y))
                          low {:direction :forward})
                (v/assert kb (list fatherOf Tom Bob) low)
                (let [[concl & more] (v/sentexes-matching kb (list ancestorOf Tom Bob) low)
                      derived        (:id concl)]
                  (is (nil? more) "one conclusion, so reading it is not a choice between several")
                  (is (some? derived))
                  {:contexts  (->> (v/supporting-justifications kb derived)
                                   (mapcat :antecedents)
                                   (map #(v/sentex kb %))
                                   (filter #(= 'genl (first (:sentence %))))
                                   (map :context)
                                   set)
                   ;; the same choice as a caller reads it: `why` walks the justification
                   ;; into `:because`, so a witness that moved with arrival order would move
                   ;; the proof tree a reader is shown
                   :because   (->> (:support (tu/why-root kb derived))
                                   (mapcat :because)
                                   (filter #(= 'genl (first (:sentence %))))
                                   (map :context)
                                   set)
                   :placement (:context concl)})))]
      (is (= (witness above 'CxUniverse)
             (witness 'CxUniverse above))
          "the same two supporters, asserted in either order, name the same witness and
           land the conclusion in the same context"))))
