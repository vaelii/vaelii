;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.web-network-test
  "The /network page — the constraint network a qualitative calculus computes over one
  context — and the /signs page, its sign network, exercised as a pure request -> response
  with no live server.

  What the page is for is what these check: that the matrix, the satisfiability verdict
  and the scenario each say something the stored facts alone do not.  A relation nobody
  asserted has to appear in the matrix, or the page is only echoing the KB back."
  (:require [clojure.string :as str]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.browser.svg :as svg]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defn- GET
  ([kb uri] (GET kb uri nil))
  ([kb uri qs]
   ((web/app kb) (cond-> {:request-method :get :uri uri}
                   qs (assoc :query-string qs)))))

(defn- nest
  "Assert a chain of nested regions in a fresh context, and answer that context."
  [kb ctx & regions]
  (doseq [[a b] (partition 2 1 regions)]
    (v/assert kb (list 'nonTangentialProperPart a b) ctx {:strength :monotonic}))
  ctx)

(defn- story
  "Assert `facts` monotonic in the fresh context `ctx` under CxWell, and answer `ctx`."
  [kb ctx facts]
  (v/assert kb (list 'genlCx ctx 'CxWell) 'CxUniverse {:strength :monotonic})
  (doseq [f facts] (v/assert kb f ctx {:strength :monotonic}))
  ctx)

(defn- drawn
  "The /network page for `calc` over `ctx`, and the scenes `svg/scene` drew answering it."
  [kb ctx calc]
  (let [seen (atom [])
        orig svg/scene
        r    (with-redefs [svg/scene (fn [s] (swap! seen conj s) (orig s))]
               (GET kb "/network" (str "ctx=" ctx "&calc=" (name calc))))]
    [r @seen]))

(tu/deftest-kb the-network-page-lists-every-calculus-without-a-context
  (let [r (GET kb "/network")]
    (is (= 200 (:status r)))
    (testing "all six shipped algebras are offered, prover registered or not"
      (doseq [nm ["rcc8" "cardinal" "relative" "distance" "allen" "point"]]
        (is (re-find (re-pattern nm) (:body r)) (str nm " is listed"))))
    (testing "each is described by its base-relation count and its vocabulary"
      (is (re-find #"base" (:body r)))
      (is (re-find #"nonTangentialProperPart|partOfRegion" (:body r))))))

(tu/deftest-kb the-calculi-table-counts-each-calculus-stored-facts
  (let [none #"states no fact in any calculus"]
    (is (re-find none (:body (GET kb "/network"))))
    (tu/with-terms [RegA RegB CxSpaceStory]
      (nest kb CxSpaceStory RegA RegB)
      (let [b (:body (GET kb "/network"))]
        (is (not (re-find none b)))
        (is (re-find #"<th>rcc8</th>(<td class=\"num\">\d+</td>){2}<td class=\"num\">1</td>" b))))))

(tu/deftest-kb the-matrix-shows-a-relation-nobody-asserted
  (tu/with-terms [RegA RegB RegC CxSpaceStory]
    (v/assert kb (list 'genlCx CxSpaceStory 'CxWell) 'CxUniverse
              {:strength :monotonic})
    (nest kb CxSpaceStory RegA RegB RegC)
    (let [r (GET kb "/network" (str "ctx=" CxSpaceStory "&calc=rcc8"))]
      (is (= 200 (:status r)))
      (testing "the network is satisfiable and names its three regions"
        (is (re-find #"satisfiable" (:body r)))
        (doseq [t [RegA RegB RegC]]
          (is (re-find (re-pattern (str t)) (:body r)))))
      (testing "the A-to-C entailment is on the page, and it was never asserted"
        (is (nil? (v/handle-of kb (list 'nonTangentialProperPart RegA RegC)
                               CxSpaceStory))
            "the transitive relation is genuinely not stored")
        (is (= #{:ntpp} (v/possible-relations kb :rcc8 CxSpaceStory RegA RegC))))
      (testing "the scenario section renders one arrangement"
        (is (re-find #"One scenario" (:body r)))
        (is (re-find #"ntpp" (:body r)))))))

(tu/deftest-kb a-query-context-on-the-network-page-is-a-400-and-not-a-500
  ;; `qualitative-network` resolves no query context, so the engine refused with
  ;; `:unsupported-context` and Jetty answered 500 — the levels page's case, unguarded here
  (doseq [ctx ["CxEverything" "CxInference" "CxNothing"]]
    (let [r (GET kb "/network" (str "ctx=" ctx "&calc=rcc8"))]
      (is (= 400 (:status r)) ctx)
      (is (re-find (re-pattern ctx) (:body r)) (str "the refusal names " ctx))))
  (is (= 200 (:status (GET kb "/network" "ctx=CxWell&calc=rcc8"))) "a place still renders"))

(tu/deftest-kb a-calculus-name-no-algebra-answers-to-is-refused
  ;; The fallback picks the first calculus with a populated network, so `?calc=rcc9` drew a
  ;; matrix — a *different* algebra's, with nothing on the page to say so.  A reader
  ;; comparing two calculi by editing the URL is exactly who that misleads.
  (tu/with-terms [RegA RegB CxSpaceRefuse]
    (v/assert kb (list 'genlCx CxSpaceRefuse 'CxWell) 'CxUniverse {:strength :monotonic})
    (nest kb CxSpaceRefuse RegA RegB)
    (let [r (GET kb "/network" (str "ctx=" CxSpaceRefuse "&calc=rcc9"))]
      (is (= 400 (:status r)))
      (is (re-find #"<code>calc</code>" (:body r)))
      (is (re-find #"rcc9" (:body r)))
      (testing "and the refusal names every calculus that would have been legal"
        (doseq [nm (map (comp name :calculus) (v/calculi))]
          (is (re-find (re-pattern nm) (:body r)) (str nm " is offered by the refusal")))))
    (testing "a real one still renders, and so does the page with no calculus named"
      (is (= 200 (:status (GET kb "/network" (str "ctx=" CxSpaceRefuse "&calc=rcc8")))))
      (is (= 200 (:status (GET kb "/network" (str "ctx=" CxSpaceRefuse)))))
      (is (= 200 (:status (GET kb "/network" (str "ctx=" CxSpaceRefuse "&calc="))))
          "an empty control is the control not being submitted"))))

(tu/deftest-kb an-unsatisfiable-network-says-so-rather-than-answering
  (tu/with-terms [RegA RegB CxSpaceClash]
    (v/assert kb (list 'genlCx CxSpaceClash 'CxWell) 'CxUniverse
              {:strength :monotonic})
    (v/assert kb (list 'nonTangentialProperPart RegA RegB) CxSpaceClash
              {:strength :monotonic})
    (v/assert kb (list 'spatiallyDisconnected RegA RegB) CxSpaceClash
              {:strength :monotonic})
    (let [r (GET kb "/network" (str "ctx=" CxSpaceClash "&calc=rcc8"))]
      (is (= 200 (:status r)))
      (testing "the verdict is reported, not swallowed"
        (is (re-find #"unsatisfiable" (:body r))))
      (testing "and the pair to blame is named, since one pair carries the clash"
        (is (re-find (re-pattern (str RegA)) (:body r)))
        (is (false? (:consistent? (v/qualitative-network kb :rcc8 CxSpaceClash)))))
      (testing "no scenario is offered for a world that cannot exist"
        (is (nil? (v/qualitative-scenario kb :rcc8 CxSpaceClash)))))))

(tu/deftest-kb a-context-with-no-qualitative-facts-says-nothing-rather-than-erroring
  (tu/with-terms [CxEmptySpace]
    (v/assert kb (list 'genlCx CxEmptySpace 'CxWell) 'CxUniverse
              {:strength :monotonic})
    (let [r (GET kb "/network" (str "ctx=" CxEmptySpace))]
      (is (= 200 (:status r)))
      (is (re-find #"No calculus relates anything|relates nothing" (:body r))))))

(tu/deftest-kb the-menubar-reaches-the-page
  (let [r (GET kb "/")]
    (is (= 200 (:status r)))
    (is (re-find #"href=\"/network\"" (:body r)))
    (is (re-find #">Network<" (:body r)))))

;; ---- the network drawing ---------------------------------------------------

(tu/deftest-kb the-network-is-drawn-above-the-matrix-one-edge-per-related-pair
  (tu/with-terms [RegA RegB RegC CxSpaceDrawn]
    (story kb CxSpaceDrawn [(list 'nonTangentialProperPart RegA RegB)
                            (list 'nonTangentialProperPart RegB RegC)])
    (let [[r [scene]] (drawn kb CxSpaceDrawn :rcc8)
          b           (:body r)]
      (is (< (str/index-of b "kb-graph-fig") (str/index-of b "qcn-matrix")))
      (is (= #{RegA RegB RegC} (set (map :term (:nodes scene)))))
      (is (empty? (:frames scene)) "a consistent network has no frame")
      (testing "a pair and its converse are one edge, from the term that prints first"
        (is (= #{[RegA RegB ["ntpp"]] [RegA RegC ["ntpp"]] [RegB RegC ["ntpp"]]}
               (set (map (juxt :from :to :label) (:edges scene))))))
      (is (= [] (svg/faults scene))))))

(tu/deftest-kb a-pair-the-network-leaves-universal-has-no-edge-and-a-symmetric-set-no-head
  (tu/with-terms [Breakfast Lunch MeetA MeetB CxDay]
    (story kb CxDay [(list 'precedes Breakfast Lunch) (list 'intervalEqual MeetA MeetB)])
    (let [[_ [scene]] (drawn kb CxDay :allen)]
      (is (= #{[Breakfast Lunch ["before meets"] false] [MeetA MeetB ["equal"] true]}
             (set (map (juxt :from :to :label :undirected?) (:edges scene)))))
      (is (= 4 (count (:nodes scene))) "a node per term, related or not to the other part"))))

(tu/deftest-kb an-unsatisfiable-pair-is-drawn-dashed-and-the-caption-says-so
  (tu/with-terms [RegA RegB CxSpaceClashDrawn]
    (story kb CxSpaceClashDrawn [(list 'nonTangentialProperPart RegA RegB)
                                 (list 'spatiallyDisconnected RegA RegB)])
    (let [[r [scene]] (drawn kb CxSpaceClashDrawn :rcc8)]
      (is (= ["g-unsat"] (map :kind (:edges scene))))
      (is (= ["g-unsat"] (map :class (:frames scene))))
      (is (re-find #"the amber frame marks the network inconsistent" (:body r)))
      (is (= [] (svg/faults scene))))))

(defn- svg-of
  "The `<svg>` of the page's first figure, as the book cuts it out."
  [r]
  (re-find #"(?s)<svg.*?</svg>" (:body r)))

(tu/deftest-kb a-pair-the-network-leaves-no-relation-is-dashed-as-a-named-one-is
  ;; the point network's clash empties two Allen pairs, and `:unsatisfiable` names neither
  (tu/with-terms [Breakfast Snack Lunch CxClashDrawn]
    (story kb CxClashDrawn [(list 'before Breakfast Lunch) (list 'starts Snack Lunch)
                            (list 'meets Breakfast Snack)])
    (let [[r [scene]] (drawn kb CxClashDrawn :allen)
          {empty-set true other false} (group-by #(= "∅" (:label %)) (:edges scene))]
      (is (= ["g-unsat" "g-unsat"] (map :kind empty-set)))
      (is (= [nil] (map :kind other)))
      (is (re-find #"dashed: a pair left no relation" (svg-of r)))
      (is (= [] (svg/faults scene))))))

(tu/deftest-kb an-inconsistent-network-is-framed-inside-its-svg-with-no-pair-dashed
  (tu/with-terms [Nest Branch Trunk CxDistanceClash]
    (story kb CxDistanceClash [(list 'veryCloseTo Nest Branch) (list 'veryCloseTo Branch Trunk)
                               (list 'veryFarFrom Nest Trunk)])
    (let [[r [scene]] (drawn kb CxDistanceClash :distance)]
      (is (= [["inconsistent: no arrangement satisfies every believed fact"]] (map :lines (:frames scene))))
      (is (not-any? :kind (:edges scene)))
      (is (re-find #"inconsistent: no arrangement" (svg-of r)))
      (is (re-find #"no pair is dashed" (:body r)))
      (is (= [] (svg/faults scene))))))

(tu/deftest-kb the-network-drawing-is-the-same-bytes-whatever-the-assertion-order
  (tu/with-terms [Mill Village Ford Bridge CxMapOne CxMapTwo]
    (let [facts [(list 'northwardOf Mill Village) (list 'northOf Ford Bridge)
                 (list 'westOf Mill Ford)]
          fig   (fn [ctx] (-> (:body (first (drawn kb ctx :cardinal)))
                              (->> (re-find #"(?s)<figure class=\"kb-graph-fig\">.*?</figure>"))
                              (str/replace (str ctx) "CX")))]
      (story kb CxMapOne facts)
      (story kb CxMapTwo (reverse facts))
      (is (some? (fig CxMapOne)))
      (is (= (fig CxMapOne) (fig CxMapTwo))))))

(tu/deftest-kb no-drawing-of-the-handbook-sessions-has-an-overlap-or-a-crossing
  ;; one row per network the time, durations and space chapters draw, with their shapes and
  ;; how many drawings each gets: the graph, and the timeline where a part is determined
  (doseq [[calc n facts] [[:allen 1 (fn [a b c d] [(list 'during a b) (list 'during c d)
                                                   (list 'intervalEqual a c)])]
                          [:allen 2 (fn [a b c d] [(list 'during a b) (list 'meets c d)
                                                   (list 'intervalEqual b c)])]
                          [:point 2 (fn [a b c d] [(list 'during a b) (list 'during c d)])]
                          [:allen 1 (fn [a b c d] [(list 'precedes a b) (list 'not (list 'overlaps c d))
                                                   (list 'instantBefore (list 'EndFn c) (list 'EndFn d))])]
                          [:allen 1 (fn [a b c _] [(list 'before a b) (list 'starts c b) (list 'meets a c)])]
                          [:allen 2 (fn [a b c _] [(list 'meets a b) (list 'starts c b) (list 'meets a c)])]
                          [:rcc8 1 (fn [a b c d] [(list 'partOfRegion a b) (list 'nonTangentialProperPart b c)
                                                  (list 'spatiallyDisconnected c d)])]
                          [:cardinal 1 (fn [a b c d] [(list 'northwardOf a b) (list 'northOf c b)
                                                      (list 'westOf a c) (list 'eastOf d a)])]
                          [:relative 1 (fn [a b _ _] [(list 'leftOf a b)])]
                          [:distance 1 (fn [a b c d] [(list 'veryCloseTo a b) (list 'veryCloseTo a c)
                                                      (list 'coLocatedWith d b) (list 'closeTo c d)])]
                          [:distance 1 (fn [a b c d] [(list 'veryCloseTo a b) (list 'veryCloseTo b c)
                                                      (list 'coLocatedWith d a) (list 'veryFarFrom a c)])]]]
    (tu/with-terms [TermA TermB TermC TermD CxSession]
      (story kb CxSession (facts TermA TermB TermC TermD))
      (let [[r scenes] (drawn kb CxSession calc)]
        (is (= 200 (:status r)))
        (is (= n (count scenes)) (name calc))
        (is (= [] (mapcat svg/faults scenes)) (name calc))))))

;; ---- the timeline ----------------------------------------------------------

(defn- timeline-of
  "The timeline among `scenes`."
  [scenes]
  (first (filter #(str/includes? (:aria-label %) "timeline") scenes)))

(defn- marks
  "The timeline's bars and ticks in `scene`, by term."
  [scene]
  (into {} (for [n (:nodes scene) :when (:mark? n)] [(:term n) n])))

(tu/deftest-kb a-part-the-network-fixes-is-a-timeline-in-endpoint-order
  (tu/with-terms [Day Morning Breakfast Lunch CxDayline]
    (story kb CxDayline [(list 'during Morning Day) (list 'precedes Breakfast Lunch)])
    (let [[r scenes] (drawn kb CxDayline :allen)
          timeline   (timeline-of scenes)
          m          (marks timeline)
          span       (fn [t] [(- (:x (m t)) (/ (:w (m t)) 2)) (+ (:x (m t)) (/ (:w (m t)) 2))])]
      (is (= #{Day Morning} (set (keys m))) "the open pair is left out")
      (is (< (first (span Day)) (first (span Morning)) (second (span Morning)) (second (span Day))))
      (is (re-find (re-pattern (str "not drawn[^<]*" Breakfast ", " Lunch)) (:body r)))
      (is (= [] (svg/faults timeline))))))

(tu/deftest-kb the-point-timeline-draws-an-interval-s-two-endpoints-as-one-bar
  (tu/with-terms [Day Morning CxPointline]
    (story kb CxPointline [(list 'during Morning Day)])
    (let [timeline (timeline-of (second (drawn kb CxPointline :point)))]
      (is (= #{Day Morning} (set (keys (marks timeline)))))
      (is (= [] (svg/faults timeline))))))

(tu/deftest-kb a-metric-distance-is-drawn-between-neighbouring-endpoints
  (tu/with-terms [Standup Review StandupStart StandupEnd ReviewStart ReviewEnd CxMetricline]
    (story kb CxMetricline
           [(list 'before Standup Review)
            (list 'startOf Standup StandupStart) (list 'endOf Standup StandupEnd)
            (list 'startOf Review ReviewStart) (list 'endOf Review ReviewEnd)
            (list 'temporalDistance StandupStart StandupEnd '(QuantityFn 15 Minute))
            (list 'temporalDistance StandupEnd ReviewStart '(QuantityFn 1 Hour))
            (list 'temporalDistance ReviewStart ReviewEnd '(QuantityFn 30 Minute))])
    (let [timeline (timeline-of (second (drawn kb CxMetricline :allen)))
          spans    (sort-by (comp ffirst :points) (filter #(= "g-span" (:kind %)) (:edges timeline)))]
      (is (= 3 (count spans)) "one for each two neighbouring endpoints")
      (is (every? #(re-matches #"\d+ (Second|Minute|Hour)" (:label %)) spans))
      (is (= [] (svg/faults timeline))))))

;; ---- the sign network ------------------------------------------------------

(defn- signs-drawn
  "The /signs page over `ctx`, and the scenes `svg/scene` drew answering it."
  [kb ctx]
  (let [seen (atom [])
        orig svg/scene
        r    (with-redefs [svg/scene (fn [s] (swap! seen conj s) (orig s))]
               (GET kb "/signs" (str "ctx=" (java.net.URLEncoder/encode (pr-str ctx) "UTF-8"))))]
    [r @seen]))

(defn- bath
  "docs/sign.md's bath: a stated tap and drain, their sum, the sum as the level's rate, and
  the tap the larger."
  [tap drain net level]
  [(list 'signOf tap 'SignPositive) (list 'signOf drain 'SignNegative)
   (list 'qualitativeSum tap drain net) (list 'derivativeOf net level)
   (list 'greaterInMagnitudeThan tap drain)])

(defn- node-lines
  "Each node of `scene` by term, as its label's lines after the first and its class."
  [scene]
  (into {} (for [n (:nodes scene)] [(:term n) [(vec (rest (:lines n))) (:class n)]])))

(tu/deftest-kb the-sign-page-draws-each-quantity-with-what-the-reading-leaves-it
  (tu/with-terms [Tap Drain NetFlow Level CxTub]
    (story kb CxTub (bath Tap Drain NetFlow Level))
    (is (not (v/ask? kb (list 'signOf NetFlow 'SignPositive) CxTub))
        "the :sign reasoner is not registered, and the page reads the reading anyway")
    (let [[r [scene]] (signs-drawn kb CxTub)
          sum         (list 'qualitativeSum Tap Drain NetFlow)]
      (is (= 200 (:status r)))
      (is (str/starts-with? (:aria-label scene) "sign network over "))
      (is (= {Tap     [["sign + (stated)"] "g-stated"] Drain [["sign − (stated)"] "g-stated"]
              NetFlow [["sign +"] "g-derived"]         Level [["trend +"] "g-derived"]
              sum     [[] "g-rule"]}
             (node-lines scene)))
      (is (= #{[Tap sum nil] [Drain sum nil] [sum NetFlow nil] [NetFlow Level "derivativeOf"]
               [Tap Drain "greaterInMagnitudeThan"]}
             (set (map (juxt :from :to :label) (:edges scene)))))
      (is (= [] (svg/faults scene)))
      (is (empty? (:frames scene)) "a consistent reading has no frame")
      (is (< (str/index-of (:body r) "kb-graph-fig") (str/index-of (:body r) "stats-table"))
          "the table of quantities follows the drawing"))))

(tu/deftest-kb an-inconsistent-reading-is-framed-and-dashes-each-quantity-it-emptied
  (tu/with-terms [Tap Drain NetFlow Level CxTubClash]
    (story kb CxTubClash (conj (bath Tap Drain NetFlow Level) (list 'signOf NetFlow 'SignNegative)))
    (let [[r [scene]] (signs-drawn kb CxTubClash)
          lines       (node-lines scene)]
      (is (= [["sign ∅ (stated −)"] "g-stated g-unsat"] (lines NetFlow)))
      (is (= [["trend ∅"] "g-derived g-unsat"] (lines Level)))
      (is (= [["sign + (stated)"] "g-stated"] (lines Tap)) "a quantity the clash leaves keeps its set")
      (is (re-find #"inconsistent" (:body r)))
      (is (= [["inconsistent: no sign goal is answered in this context"
               "dashed: a quantity whose possible signs the reading emptied"]]
             (map :lines (:frames scene))))
      (is (re-find #"inconsistent: no sign goal" (svg-of r)) "the SVG cut from the page carries it")
      (is (= [] (svg/faults scene))))))

(tu/deftest-kb the-sign-drawing-is-the-same-bytes-whatever-the-assertion-order
  (tu/with-terms [Tap Drain NetFlow Level CxTubOne CxTubTwo]
    (let [facts (bath Tap Drain NetFlow Level)
          fig   (fn [ctx] (some-> (:body (first (signs-drawn kb ctx)))
                                  (->> (re-find #"(?s)<figure class=\"kb-graph-fig\">.*?</figure>"))
                                  (str/replace (str ctx) "CX")
                                  ;; an operator links to its stored sentex, whose handle is
                                  ;; the record's identity and not its content
                                  (str/replace #"/sentex/\d+" "/sentex/N")))]
      (story kb CxTubOne facts)
      (story kb CxTubTwo (reverse facts))
      (is (some? (fig CxTubOne)))
      (is (= (fig CxTubOne) (fig CxTubTwo))))))

(tu/deftest-kb no-sign-drawing-of-the-handbook-sessions-has-an-overlap-or-a-crossing
  ;; one row per sign network the signs chapter draws.  The first two are the bath beside a
  ;; second sum whose middle term is ordered against both addends, with and without the
  ;; bath's comparison.  The rest are a stated net sign the inputs contradict, a rate per
  ;; quantity, the outflow made a second rate of the level, and a product of rates
  (let [sums  (fn [[a b c _ e f g h]]
                [(list 'signOf a 'SignPositive) (list 'signOf b 'SignNegative)
                 (list 'qualitativeSum a b c) (list 'greaterInMagnitudeThan a b)
                 (list 'signOf e 'SignPositive) (list 'signOf g 'SignNegative)
                 (list 'greaterInMagnitudeThan e f) (list 'greaterInMagnitudeThan f g)
                 (list 'qualitativeSum e g h)])
        rates (fn [[a b c d e f g h i]]
                (into (bath a b c d)
                      [(list 'derivativeOf e f) (list 'trendOf f 'SignNegative)
                       (list 'qualitativeSum g h i) (list 'signOf i 'SignPositive)
                       (list 'signOf g 'SignNegative)]))
        heat  (fn [trend [a b c d e f g h i j]]
                [(list 'derivativeOf b c) (list 'derivativeOf d e) (list 'signOf a 'SignPositive)
                 (list 'qualitativeProduct a b d) (list 'trendOf c trend)
                 (list 'derivativeOf g h) (list 'derivativeOf i j) (list 'signOf f 'SignPositive)
                 (list 'qualitativeProduct f g i) (list 'trendOf j 'SignPositive)])]
    (doseq [[nm facts]
            [["two sums" sums]
             ["two sums, one unordered" (fn [qs] (remove #(= (list 'greaterInMagnitudeThan (qs 0) (qs 1)) %)
                                                         (sums qs)))]
             ["a stated net sign" (fn [[a b c]]
                                    [(list 'signOf a 'SignPositive) (list 'signOf b 'SignNegative)
                                     (list 'qualitativeSum a b c) (list 'signOf c 'SignPositive)
                                     (list 'greaterInMagnitudeThan b a)])]
             ["rates" rates]
             ["rates, the outflow one more" (fn [qs] (conj (rates qs) (list 'derivativeOf (qs 1) (qs 3))))]
             ["a product of rates" (partial heat 'SignPositive)]
             ["a product of steady rates" (partial heat 'SignZero)]]]
      (tu/with-terms [Inflow1 Outflow1 NetFlow1 Level1 FlowA FlowB FlowC FlowAC HeatRate1 Heat1
                      CxSigns]
        (story kb CxSigns (facts [Inflow1 Outflow1 NetFlow1 Level1 FlowA FlowB FlowC FlowAC
                                  HeatRate1 Heat1]))
        (let [[r scenes] (signs-drawn kb CxSigns)]
          (is (= 200 (:status r)) nm)
          (is (= 1 (count scenes)) nm)
          (is (= [] (mapcat svg/faults scenes)) nm))))))

(tu/deftest-kb the-sign-page-reads-a-time-slice-at-the-context-its-expression-names
  (tu/with-terms [Inflow Outflow NetFlow Level Bathing Filling Draining CxTubTime]
    (doseq [s [(list 'subintervalOf Filling Bathing) (list 'subintervalOf Draining Bathing)
               (list 'meets Filling Draining)]]
      (v/assert kb s 'CxUniverse {:strength :monotonic}))
    (v/assert kb (list 'genlCx CxTubTime 'CxWell) 'CxUniverse {:strength :monotonic})
    (doseq [s (butlast (bath Inflow Outflow NetFlow Level))]
      (v/assert kb s (list 'CxTimeFn CxTubTime Bathing) {:strength :monotonic}))
    (v/assert kb (list 'greaterInMagnitudeThan Inflow Outflow) (list 'CxTimeFn CxTubTime Filling)
              {:strength :monotonic})
    (v/assert kb (list 'greaterInMagnitudeThan Outflow Inflow) (list 'CxTimeFn CxTubTime Draining)
              {:strength :monotonic})
    (doseq [[slice level] [[Filling [["trend +"] "g-derived"]] [Draining [["trend −"] "g-derived"]]
                           [Bathing [["trend unread"] "g-out"]]]]
      (let [[r [scene]] (signs-drawn kb (list 'CxTimeFn CxTubTime slice))]
        (is (= 200 (:status r)))
        (is (= level ((node-lines scene) Level)) (str slice))
        (is (= [] (svg/faults scene)) (str slice))))))

(tu/deftest-kb the-sign-page-refuses-a-context-it-cannot-read
  (doseq [^String raw ["42" "?x" "(foo Bar)" "(" "[CxWell]" "CxEverything"]]
    (is (= 400 (:status (GET kb "/signs" (str "ctx=" (java.net.URLEncoder/encode raw "UTF-8")))))
        raw)))

(tu/deftest-kb the-sign-page-lists-the-vocabulary-without-a-context
  (let [b (:body (GET kb "/signs"))]
    (doseq [p ["signOf" "trendOf" "derivativeOf" "qualitativeSum" "qualitativeDifference"
               "qualitativeProduct" "greaterInMagnitudeThan"]]
      (is (str/includes? b p) p))))
