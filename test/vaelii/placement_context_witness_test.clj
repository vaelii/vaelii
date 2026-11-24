;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.placement-context-witness-test
  "A firing's justification names one `genlCx` path from its placement up to each
  ingredient context (docs/contexts.md, \"The consumers\").  A section per consequence:
  `why` shows the edges, retracting either side's edge withdraws what it licensed, an
  edge caps nothing, and a reachability that outlives the named path re-derives.  The
  `genl` counterpart is `subsumption_support_test`."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
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

(defn- edge-sentexes
  "The `genlCx` sentexes among a conclusion's antecedents."
  [kb handle]
  (->> (v/supporting-justifications kb handle)
       (mapcat :antecedents)
       (map #(v/sentex kb %))
       (filter #(= 'genlCx (first (:sentence %))))))

(defn- under!
  "Wire `sub` under each of `supers`, and every super under CxUniverse."
  [kb sub & supers]
  (doseq [s supers]
    (v/assert kb (list 'genlCx s 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx sub s) 'CxUniverse)))

;; ---- what the justification names ---------------------------------------

(tu/deftest-kb a-firing-placed-below-its-rule-names-the-edge-it-saw-the-rule-over
  (tu/with-terms [bird flies Tweety CxLow CxHigh]
    (under! kb CxLow CxHigh)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh {:direction :forward})
    (v/assert kb (list bird Tweety) CxLow)
    (let [derived (v/handle-of kb (list flies Tweety) CxLow)]
      (is (v/believed? kb derived) "the rule was inherited into the context holding the fact")
      (testing "the edge is an antecedent, beside the fact and the rule"
        (is (contains? (antecedent-sentences kb derived) (list 'genlCx CxLow CxHigh))))
      (testing "so `why` shows it, rather than a proof that skips how the rule was seen"
        (let [because (->> (tu/why-root kb derived) :support first :because (map :sentence) set)]
          (is (contains? because (list 'genlCx CxLow CxHigh))))))))

(tu/deftest-kb a-same-context-firing-names-no-edge
  ;; the control: a placement that reaches its ingredients reflexively rests on no
  ;; context edge at all, so this section proves something other than "the antecedent
  ;; list grew"
  (tu/with-terms [bird flies Tweety CxOne]
    (v/assert kb (list 'genlCx CxOne 'CxUniverse) 'CxUniverse)
    (let [rh      (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxOne
                            {:direction :forward})
          _       (v/assert kb (list bird Tweety) CxOne)
          derived (v/handle-of kb (list flies Tweety) CxOne)
          j       (first (v/supporting-justifications kb derived))
          named   (into #{} (map #(:sentence (v/sentex kb %))) (:antecedents j))]
      ;; which sentexes, not how many; the rule is the informant, not an antecedent
      (is (= #{(list bird Tweety)} named) "the fact itself, and nothing else")
      (is (= rh (:informant j)) "and the rule that fired, not some other justification's")
      (is (not-any? #(and (seq? %) (= 'genlCx (first %))) named)
          "and no context edge, the placement reaching its ingredients reflexively"))))

(tu/deftest-kb every-edge-on-the-path-is-named
  ;; visibility is transitive, so a rule two steps up is seen over two edges and either
  ;; one of them is enough to withdraw the conclusion
  (tu/with-terms [bird flies Tweety CxLow CxMid CxHigh]
    (v/assert kb (list 'genlCx CxHigh 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxMid CxHigh) 'CxUniverse)
    (v/assert kb (list 'genlCx CxLow CxMid) 'CxUniverse)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh {:direction :forward})
    (v/assert kb (list bird Tweety) CxLow)
    (let [derived (v/handle-of kb (list flies Tweety) CxLow)
          antes   (antecedent-sentences kb derived)]
      (is (v/believed? kb derived))
      (is (contains? antes (list 'genlCx CxLow CxMid)))
      (is (contains? antes (list 'genlCx CxMid CxHigh))))))

(tu/deftest-kb the-rule-side-and-the-fact-side-are-both-named
  ;; the placement descends below two incomparable contexts, so it sees the rule over one
  ;; edge and the fact over another — and rests on both
  (tu/with-terms [bird flies Tweety CxPlace CxRule CxFact]
    (under! kb CxPlace CxRule CxFact)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxRule {:direction :forward})
    (v/assert kb (list bird Tweety) CxFact)
    (let [[placed & more] (v/sentexes-matching kb (list flies Tweety) '?ctx)
          antes            (antecedent-sentences kb (:id placed))]
      (is (nil? more) "one placement, so reading it is not a choice between several")
      (is (= CxPlace (:context placed)) "the one context below both")
      (is (contains? antes (list 'genlCx CxPlace CxRule)))
      (is (contains? antes (list 'genlCx CxPlace CxFact))))))

(tu/deftest-kb the-named-edge-is-one-the-placement-can-see
  (tu/with-terms [bird flies Tweety CxLow CxHigh]
    (under! kb CxLow CxHigh)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh {:direction :forward})
    (v/assert kb (list bird Tweety) CxLow)
    (let [derived (v/handle-of kb (list flies Tweety) CxLow)
          edges   (edge-sentexes kb derived)]
      (is (seq edges))
      (is (every? #(v/sees? kb CxLow (:context %)) edges)
          "every edge the conclusion rests on is one its own context sees"))))

;; ---- retracting either side's edge withdraws what it licensed -------------

(tu/deftest-kb retracting-the-rule-side-edge-withdraws-the-conclusion
  (tu/with-terms [bird flies Tweety CxPlace CxRule CxFact]
    (under! kb CxPlace CxRule CxFact)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxRule {:direction :forward})
    (v/assert kb (list bird Tweety) CxFact)
    (is (seq (v/sentexes-matching kb (list flies Tweety) '?ctx)))
    (v/retract! kb (v/handle-of kb (list 'genlCx CxPlace CxRule) 'CxUniverse))
    (testing "with the edge gone the placement cannot see the rule, so neither does the conclusion stand"
      (is (empty? (v/sentexes-matching kb (list flies Tweety) '?ctx))))
    (testing "and the ingredients that were not retracted are all still believed"
      (is (seq (v/sentexes-matching kb (list bird Tweety) CxFact))))))

(tu/deftest-kb retracting-the-fact-side-edge-withdraws-the-conclusion
  (tu/with-terms [bird flies Tweety CxPlace CxRule CxFact]
    (under! kb CxPlace CxRule CxFact)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxRule {:direction :forward})
    (v/assert kb (list bird Tweety) CxFact)
    (is (seq (v/sentexes-matching kb (list flies Tweety) '?ctx)))
    (v/retract! kb (v/handle-of kb (list 'genlCx CxPlace CxFact) 'CxUniverse))
    (is (empty? (v/sentexes-matching kb (list flies Tweety) '?ctx)))))

(tu/deftest-kb retracting-one-edge-of-a-chain-withdraws-the-conclusion
  (tu/with-terms [bird flies Tweety CxLow CxMid CxHigh]
    (v/assert kb (list 'genlCx CxHigh 'CxUniverse) 'CxUniverse)
    (let [upper (v/assert kb (list 'genlCx CxMid CxHigh) 'CxUniverse)]
      (v/assert kb (list 'genlCx CxLow CxMid) 'CxUniverse)
      (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh {:direction :forward})
      (v/assert kb (list bird Tweety) CxLow)
      (is (seq (v/sentexes-matching kb (list flies Tweety) CxLow)))
      (v/retract! kb upper)
      (is (empty? (v/sentexes-matching kb (list flies Tweety) '?ctx))
          "the sighting needed both edges, so losing the upper one is enough"))))

(tu/deftest-kb a-retracted-edge-takes-the-whole-cascade-with-it
  ;; the conclusion is an ordinary datum, so what rests on *it* goes too — the
  ;; dependency-directed sweep needs no special case for a context edge
  (tu/with-terms [bird flies moves Tweety CxLow CxHigh]
    (under! kb CxLow CxHigh)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh {:direction :forward})
    (v/assert kb (list 'implies (list flies '?x) (list moves '?x)) CxHigh {:direction :forward})
    (v/assert kb (list bird Tweety) CxLow)
    (is (seq (v/sentexes-matching kb (list moves Tweety) CxLow)))
    (v/retract! kb (v/handle-of kb (list 'genlCx CxLow CxHigh) 'CxUniverse))
    (is (empty? (v/sentexes-matching kb (list moves Tweety) '?ctx)))))

(tu/deftest-kb a-retraction-lands-where-a-kb-that-never-had-the-edge-lands
  ;; one arm lost the edge and one never had it
  (letfn [(without-edge [] (tu/with-terms [bird flies Tweety CxLow CxHigh]
                             (v/assert kb (list 'genlCx CxHigh 'CxUniverse) 'CxUniverse)
                             (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh {:direction :forward})
                             (v/assert kb (list bird Tweety) CxLow)
                             (mapv :context (v/sentexes-matching kb (list flies Tweety) '?ctx))))
          (edge-then-gone [] (tu/with-terms [bird flies Tweety CxLow CxHigh]
                               (under! kb CxLow CxHigh)
                               (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh {:direction :forward})
                               (v/assert kb (list bird Tweety) CxLow)
                               (v/retract! kb (v/handle-of kb (list 'genlCx CxLow CxHigh) 'CxUniverse))
                               (mapv :context (v/sentexes-matching kb (list flies Tweety) '?ctx))))]
    (is (= [] (without-edge)) "no edge, no sighting, no conclusion")
    (is (= (without-edge) (edge-then-gone))
        "and losing the edge leaves exactly what never having it would have")))

(tu/deftest-kb the-witness-does-not-depend-on-assertion-order
  ;; the edge arriving last has to reach what is already stored (`special/visibility-seeds`)
  (letfn [(arm [edge-first?]
            (tu/with-terms [bird flies Tweety CxLow CxHigh]
              (v/assert kb (list 'genlCx CxHigh 'CxUniverse) 'CxUniverse)
              (when edge-first? (v/assert kb (list 'genlCx CxLow CxHigh) 'CxUniverse))
              (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh {:direction :forward})
              (v/assert kb (list bird Tweety) CxLow)
              (when-not edge-first? (v/assert kb (list 'genlCx CxLow CxHigh) 'CxUniverse))
              (let [derived (v/handle-of kb (list flies Tweety) CxLow)]
                {:asked   (v/ask? kb (list flies Tweety) CxLow)
                 :witness (contains? (antecedent-sentences kb derived)
                                     (list 'genlCx CxLow CxHigh))
                 ;; and the withdrawal reads the same from either build order
                 :after   (do (v/retract! kb (v/handle-of kb (list 'genlCx CxLow CxHigh)
                                                          'CxUniverse))
                              (v/ask? kb (list flies Tweety) CxLow))})))]
    (is (= {:asked true :witness true :after false} (arm true)))
    (is (= (arm true) (arm false)))))

;; ---- the edge is an antecedent, so strength runs through it ----

(tu/deftest-kb an-edge-written-default-leaves-the-conclusion-as-strong-as-its-grounds
  ;; a conclusion is never stronger than what it rests on, and the edge its placement
  ;; was seen over is one of those things — but a `genlCx` edge is stored `:monotonic`
  ;; whatever it was written at (docs/nmtms.md, "The forced-monotonic set"), so
  ;; known-true fact + bare rule + an edge written `:default` is a known-true conclusion
  (tu/with-terms [bird flies Tweety CxLow CxHigh]
    (under! kb CxLow CxHigh)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh {:direction :forward :strength :monotonic})
    (v/assert kb (list bird Tweety) CxLow {:strength :monotonic})
    (is (= :monotonic (v/defeat-class kb (v/handle-of kb (list flies Tweety) CxLow))))))

;; ---- a reachability that outlives its named witness -----------------------

(tu/deftest-kb an-edge-has-one-supporter-however-many-contexts-state-it
  ;; `genlCx` is a `forced_decontextualized_predicate`, so an edge stated from two
  ;; contexts is one sentex, and only a second path outlives the named edge
  (tu/with-terms [bird flies Tweety CxLow CxHigh]
    (v/assert kb (list 'genlCx CxHigh 'CxUniverse) 'CxUniverse)
    (let [e1 (v/assert kb (list 'genlCx CxLow CxHigh) 'CxUniverse)
          e2 (v/assert kb (list 'genlCx CxLow CxHigh) 'CxUniverse)]
      (is (= e1 e2) "one sentex, in CxUniverse, whichever context stated it")
      (is (= 'CxUniverse (:context (v/sentex kb e1))))
      (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh {:direction :forward})
      (v/assert kb (list bird Tweety) CxLow)
      (is (seq (v/sentexes-matching kb (list flies Tweety) CxLow)))
      (v/retract! kb e1)
      (is (empty? (v/sentexes-matching kb (list flies Tweety) '?ctx))
          "so retracting it takes the conclusion — there is no second supporter to keep it"))))

(tu/deftest-kb a-second-path-around-the-edge-keeps-the-conclusion
  ;; multiple inheritance between contexts: Low reaches High two ways.  Either middle
  ;; edge can go.
  (tu/with-terms [bird flies Tweety CxLow CxOne CxTwo CxHigh]
    (v/assert kb (list 'genlCx CxHigh 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxLow CxOne) 'CxUniverse)
    (v/assert kb (list 'genlCx CxLow CxTwo) 'CxUniverse)
    (let [via-one (v/assert kb (list 'genlCx CxOne CxHigh) 'CxUniverse)
          via-two (v/assert kb (list 'genlCx CxTwo CxHigh) 'CxUniverse)]
      (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh {:direction :forward})
      (v/assert kb (list bird Tweety) CxLow)
      (let [before (v/handle-of kb (list flies Tweety) CxLow)]
        (is (v/believed? kb before))
        (v/retract! kb via-one)
        (let [after (v/handle-of kb (list flies Tweety) CxLow)]
          (is (v/believed? kb after)
              "Low still sees High by the other route, so the rule still reaches the fact")
          (is (not= before after)
              "as a re-derivation, not a survival: the sweep took the old record")))
      (v/retract! kb via-two)
      (is (empty? (v/sentexes-matching kb (list flies Tweety) '?ctx))
          "with both routes gone the conclusion has nothing left to rest on"))))

(tu/deftest-kb a-second-path-keeps-the-conclusion-where-the-rule-sits-off-the-edge
  ;; the meet shape: the placement sees the rule down one branch and the fact down
  ;; another, and the departing edge is on neither, so a seeding check reading only the
  ;; departing edge's two ancestor sets seeds nothing
  (tu/with-terms [bird flies Tweety CxPlace CxRule CxVia CxFact]
    (v/assert kb (list 'genlCx CxRule 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxFact 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxPlace CxRule) 'CxUniverse)
    (v/assert kb (list 'genlCx CxPlace CxVia) 'CxUniverse)
    (v/assert kb (list 'genlCx CxVia CxFact) 'CxUniverse)
    (let [direct (v/assert kb (list 'genlCx CxPlace CxFact) 'CxUniverse)]
      (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxRule {:direction :forward})
      (v/assert kb (list bird Tweety) CxFact)
      (let [before (v/handle-of kb (list flies Tweety) CxPlace)]
        (is (v/believed? kb before)
            "CxPlace sees the rule one way and the fact the other, so it holds the conclusion")
        (is (contains? (set (map :id (edge-sentexes kb before))) direct)
            "and it named the direct edge as the witness for seeing CxFact")
        (v/retract! kb direct)
        (let [after (v/handle-of kb (list flies Tweety) CxPlace)]
          (is (v/believed? kb after)
              "CxPlace still reaches CxFact through CxVia, so the conclusion is still licensed")
          (is (not= before after)
              "as a re-derivation: the sweep took the record the named edge held up"))))))

(tu/deftest-kb the-revival-a-removal-owes-is-not-conditional-on-the-departing-edges-own-ancestor-sets
  ;; a KB that held the direct edge and lost it ends where a KB that never held it ends
  (tu/with-terms [bird flies Tweety CxPlace CxRule CxVia CxFact]
    (v/assert kb (list 'genlCx CxRule 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxFact 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxPlace CxRule) 'CxUniverse)
    (v/assert kb (list 'genlCx CxPlace CxVia) 'CxUniverse)
    (v/assert kb (list 'genlCx CxVia CxFact) 'CxUniverse)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxRule {:direction :forward})
    (v/assert kb (list bird Tweety) CxFact)
    (is (seq (v/sentexes-matching kb (list flies Tweety) CxPlace))
        "the direct edge was never needed to derive it")))

(tu/deftest-kb a-firing-over-a-stored-conclusion-records-its-justification
  ;; the revival re-seeds the antecedents of the removed firings that named the edge
  ;; (`special/sighting-seeds`), which reaches every licensed firing only if a firing
  ;; whose conclusion was already stored still records itself
  (tu/with-terms [bird flies Tweety CxLow CxHigh]
    (under! kb CxLow CxHigh)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxLow {:direction :forward})
    (v/assert kb (list bird Tweety) CxLow)
    (let [h (v/handle-of kb (list flies Tweety) CxLow)]
      (is (empty? (edge-sentexes kb h)) "the first firing is placed in its own context")
      (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh {:direction :forward})
      (is (= h (v/handle-of kb (list flies Tweety) CxLow)))
      (is (= 2 (count (v/supporting-justifications kb h))))
      (is (= #{(list 'genlCx CxLow CxHigh)}
             (set (map :sentence (edge-sentexes kb h))))))))

(tu/deftest-kb a-departing-edge-re-places-a-firing-whose-conclusion-survived
  ;; the sweep takes the firing that named the edge and keeps its conclusion, which a
  ;; premise holds in CxMid.  Without the edge the firing is placed in CxLow, which sees
  ;; the rule directly, so a KB that lost the edge holds the conclusion where one that
  ;; never had it does
  (letfn [(arm [edge?]
            (tu/with-terms [bird flies Tweety CxLow CxMid CxHigh]
              (v/assert kb (list 'genlCx CxHigh 'CxUniverse) 'CxUniverse)
              (v/assert kb (list 'genlCx CxMid 'CxUniverse) 'CxUniverse)
              (v/assert kb (list 'genlCx CxLow CxMid) 'CxUniverse)
              (v/assert kb (list 'genlCx CxLow CxHigh) 'CxUniverse)
              (let [e (when edge? (v/assert kb (list 'genlCx CxMid CxHigh) 'CxUniverse))]
                (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh {:direction :forward})
                (v/assert kb (list bird Tweety) CxMid)
                (v/assert kb (list flies Tweety) CxMid)
                (when e (v/retract! kb e))
                (into #{} (map #(get {CxLow 'low CxMid 'mid} (:context %)))
                      (v/sentexes-matching kb (list flies Tweety) '?ctx)))))]
    (is (= '#{low mid} (arm false)))
    (is (= (arm false) (arm true)))))

(tu/deftest-kb the-re-chain-a-removal-owes-files-no-dropped-conclusion
  ;; the revival pass re-asks every firing the sweep took, to find which of them a
  ;; surviving route still licenses — so the ones it cannot place are the retraction
  ;; restated, and reporting one apiece would displace the ledger's real entries
  (tu/with-terms [bird flies Tweety CxLow CxHigh]
    (under! kb CxLow CxHigh)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh {:direction :forward})
    (v/assert kb (list bird Tweety) CxLow)
    (is (seq (v/sentexes-matching kb (list flies Tweety) CxLow)))
    (let [before (count (filter #(= :no-placement (:violation %)) (v/violations kb)))]
      (v/retract! kb (v/handle-of kb (list 'genlCx CxLow CxHigh) 'CxUniverse))
      (is (empty? (v/sentexes-matching kb (list flies Tweety) '?ctx)))
      (is (= before (count (filter #(= :no-placement (:violation %)) (v/violations kb))))
          "the conclusion is gone and the ledger is as it was"))))

(tu/deftest-kb the-edge-survives-a-rebuild-in-the-antecedent-list
  ;; `recover` rebuilds the JTMS from the durable justification records
  (tu/with-terms [bird flies Tweety CxLow CxHigh]
    (under! kb CxLow CxHigh)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh {:direction :forward})
    (v/assert kb (list bird Tweety) CxLow)
    (let [derived (v/handle-of kb (list flies Tweety) CxLow)
          before  (antecedent-sentences kb derived)]
      (is (contains? before (list 'genlCx CxLow CxHigh)))
      (v/recover kb)
      (is (= before (antecedent-sentences kb derived)))
      (is (v/believed? kb derived) "and it is still believed")
      (v/retract! kb (v/handle-of kb (list 'genlCx CxLow CxHigh) 'CxUniverse))
      (is (empty? (v/sentexes-matching kb (list flies Tweety) '?ctx))
          "so the rebuilt dependency still withdraws"))))

(tu/deftest-kb a-preview-of-removing-the-edge-reports-what-it-would-take
  (tu/with-terms [bird flies Tweety CxLow CxHigh]
    (under! kb CxLow CxHigh)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh {:direction :forward})
    (v/assert kb (list bird Tweety) CxLow)
    (let [edge    (v/handle-of kb (list 'genlCx CxLow CxHigh) 'CxUniverse)
          removed (set (map :sentence (:believed-removed (v/preview kb {:remove [edge]} {}))))]
      (is (contains? removed (list flies Tweety))
          "the conclusion the edge licensed is named as a casualty"))
    (is (seq (v/sentexes-matching kb (list flies Tweety) CxLow))
        "and the preview put the KB back")))
