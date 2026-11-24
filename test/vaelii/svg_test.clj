;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.svg-test
  "The concept graph's drawing layer, on hand-built maps.  It takes no KB and reads
  nothing, so every claim here is arithmetic and there is no fixture."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [hiccup2.core :as h]
            [vaelii.browser.svg :as svg]))

(defn- html [hiccup] (str (h/html {:mode :html} hiccup)))

(defn- nodes [terms]
  (mapv (fn [t] (svg/measure {:term t :class "t-type" :href (str "/term?q=" t) :title (str t)}))
        terms))

;; ---- measurement --------------------------------------------------------

(deftest a-long-name-wraps-over-three-lines-and-past-them-is-cut
  (testing "a label at or under the cap is the term, on one line"
    (is (= ["CxNormalPhysicalConditions"] (:lines (svg/measure {:term 'CxNormalPhysicalConditions}))))
    (is (= [svg/label-cap] (map count (:lines (svg/measure {:term (symbol (apply str (repeat svg/label-cap "x")))}))))))
  (testing "a longer one wraps, inside a word only where the word is longer than a line"
    (is (= [32 28] (map count (:lines (svg/measure {:term (symbol (apply str (repeat 60 "x")))})))))
    (is (= ["(BloodKinFn parentOf)"] (:lines (svg/measure {:term 1 :display "(BloodKinFn parentOf)"})))))
  (testing "past the last line the label is cut with an ellipsis; the title holds the term"
    (let [ls (:lines (svg/measure {:term (symbol (apply str (repeat 200 "x")))}))]
      (is (= svg/label-lines (count ls)))
      (is (str/ends-with? (peek ls) "…"))
      (is (= svg/label-cap (count (peek ls)))))))

(deftest a-long-sentence-wraps-over-three-lines-before-it-is-cut
  (let [rule "(implies (and (parentOf ?x ?y) (parentOf ?y ?z)) (grandparentOf ?x ?z))"
        n    (svg/measure {:term 1 :display rule :cap svg/sentence-cap})]
    (is (= ["(implies (and (parentOf ?x ?y) (parentOf"
            "?y ?z)) (grandparentOf ?x ?z))"]
           (:lines n))
        "broken at spaces, so the consequent is drawn whole")
    (is (= (+ svg/node-h 18) (:h n)) "a second line makes the box one line taller")
    (is (= (:w n) (:w (svg/measure {:term 1 :display (first (:lines n)) :cap svg/sentence-cap})))
        "and the box is as wide as its widest line"))
  (let [n (svg/measure {:term 1 :display (str/join " " (repeat 40 "(p ?x)")) :cap svg/sentence-cap})]
    (is (= svg/label-lines (count (:lines n))))
    (is (str/ends-with? (peek (:lines n)) "…") "text past three lines is cut")))

(deftest a-vector-display-is-one-line-per-string-each-cut-at-the-cap
  (is (= ["Tap" "sign + (stated)"] (:lines (svg/measure {:term 'Tap :display ["Tap" "sign + (stated)"]}))))
  (is (= [(str (apply str (repeat 31 "x")) "…") "y"]
         (:lines (svg/measure {:term 1 :display [(apply str (repeat 40 "x")) "y"]})))))

(deftest measuring-is-idempotent-and-widens-with-the-label
  (let [a (svg/measure {:term 'ox})
        b (svg/measure {:term 'physical_object})]
    (is (= svg/node-h (:h a) (:h b)) "every node is the same height")
    (is (< (:w a) (:w b)) "a longer label needs a wider box")
    (is (= a (svg/measure a)) "measuring twice changes nothing")))

;; ---- layout -------------------------------------------------------------

(deftest a-row-is-centred-and-evenly-gapped
  (let [ns (svg/row (nodes '[a bb ccc]) 0 -50 20)]
    (is (= [-50 -50 -50] (map :y ns)) "one row, one height")
    (is (apply < (map :x ns)) "left to right in the order given")
    (testing "the row is centred on cx: its outer edges are equidistant"
      (let [left  (- (:x (first ns)) (/ (:w (first ns)) 2))
            right (+ (:x (last ns)) (/ (:w (last ns)) 2))]
        (is (< (Math/abs (double (+ left right))) 2))))
    (testing "and the gap between two boxes is the gap"
      (let [[p q] ns]
        (is (= 20 (- (- (:x q) (/ (:w q) 2)) (+ (:x p) (/ (:w p) 2))))))))
  (testing "a single node sits on the centre line, and no nodes place nothing"
    (is (= [0] (map :x (svg/row (nodes '[only]) 0 0 20))))
    (is (empty? (svg/row [] 0 0 20)))))

(defn- at-layer
  "Measured nodes for `layered`, each `[term layer]`, ordered by name."
  [& pairs]
  (mapv (fn [[t l]] (assoc (svg/measure {:term t :title (str t)}) :layer l :order (str t))) pairs))

(defn- edges [& pairs] (mapv (fn [[a b]] {:from a :to b}) pairs))

(defn- by-term [placed] (into {} (map (juxt :term identity)) (:nodes placed)))

(deftest a-layered-row-is-ordered-by-where-its-linked-nodes-sit-then-by-content
  (let [placed (svg/layered (at-layer '[r 0] '[b 1] '[a 1] '[x 2] '[y 2])
                            (edges '[b r] '[a r] '[x b] '[y a])
                            {:level 76 :gap 20})
        at     (by-term placed)]
    (is (= {'r 0 'a 76 'b 76 'x 152 'y 152} (into {} (map (fn [[t n]] [t (:y n)])) at))
        "a layer is one level below the one before")
    (testing "two nodes linked to one node are ordered by content"
      (is (< (:x (at 'a)) (:x (at 'b)))))
    (testing "a node is ordered by where its neighbour sits, before its own content"
      (is (< (:x (at 'y)) (:x (at 'x)))))))

(deftest a-layered-row-wraps-at-its-count-or-its-width
  (let [five  (fn [] (mapv (fn [t] (assoc (svg/measure {:term t}) :w 100 :layer 0 :order (str t)))
                           '[a b c d e]))
        lines (fn [opts]
                (map :y (sort-by :order (:nodes (svg/layered (conj (five) (first (at-layer '[z 1]))) []
                                                             (merge {:level 76 :gap 20 :line-gap 14} opts))))))]
    (is (= [0 0 42 42 84 160] (lines {:width 250}))
        "two boxes and a gap fit in 250, a third does not; the next layer starts under the last line")
    (is (= [0 0 42 42 84 160] (lines {:cap 2})))
    (is (= [0 0 0 0 0 76] (lines {})) "with neither, a layer is one line")))

(deftest an-edge-spanning-layers-bends-around-the-boxes-between
  ;; the closure of a type under two supertypes, one a layer deeper than the other:
  ;; `temporal → thing` spans the layer `spatial` sits on
  (let [placed (svg/layered (at-layer '[thing 0] '[spatial 1] '[physical 2] '[temporal 2]
                                      '[spatiotemporal 3] '[cavity 4])
                            (edges '[spatial thing] '[physical spatial] '[temporal thing]
                                   '[spatiotemporal physical] '[spatiotemporal temporal]
                                   '[cavity spatiotemporal])
                            {:level 76 :gap 20})
        long   (first (filter #(= ['temporal 'thing] [(:from %) (:to %)]) (:edges placed)))]
    (is (< 2 (count (:points long))) "the long edge bends")
    (is (= [] (svg/faults placed)) "and no edge crosses a box it does not end at")))

(deftest an-edge-label-sits-beside-its-line
  (testing "on a layered edge"
    (is (= [] (svg/faults (svg/layered (at-layer '[top 0] '[low 1])
                                       [{:from 'low :to 'top :label "not believed"}]
                                       {:level 76 :gap 20})))))
  (testing "on an edge with no placed label, at any slope"
    (doseq [to-x [0 60 300 -300]]
      (is (= [] (svg/faults {:edges [{:points [[0 0] [to-x -120]] :label "not believed"}]}))
          (str "to x " to-x)))))

(deftest a-label-another-edge-crosses-moves-clear-of-it
  (let [laid    (svg/layered (at-layer '[Inflow1 0] '[Outflow1 1] '[sum 2])
                             [{:from 'Inflow1 :to 'Outflow1 :label "greaterInMagnitudeThan"}
                              {:from 'Inflow1 :to 'sum} {:from 'Outflow1 :to 'sum}]
                             {:level 76 :gap 20})
        cleared (svg/clear-labels laid)]
    (is (seq (svg/faults laid)) "beside its own edge, the label lies across Inflow1 → sum")
    (is (= [] (svg/faults cleared)))
    (is (= cleared (svg/clear-labels cleared)) "a clear label stays where it is")))

(deftest edges-into-one-box-meet-it-at-separate-points
  (let [placed (svg/layered (at-layer '[top 0] '[a 1] '[b 1] '[c 1]) (edges '[a top] '[b top] '[c top])
                            {:level 76 :gap 20})]
    (is (= 3 (count (distinct (map (comp peek :points) (:edges placed))))))))

(deftest a-layered-row-frames-each-group-with-its-label-inside-and-keeps-groups-apart
  (let [ns     (-> (at-layer '[top 0] '[a 1] '[bb 1] '[ccc 1] '[dd 1])
                   (update 1 assoc :group 0) (update 2 assoc :group 0) (update 3 assoc :group 1))
        placed (svg/layered ns (edges '[a top] '[bb top] '[ccc top] '[dd top])
                            {:level 76 :gap 20 :group-gap 32
                             :groups {0 {:rank 0 :lines ["partition 1:" "covers, disjoint"]}
                                      1 {:rank 1 :lines ["covering:" "covers"]}}})
        at     (by-term placed)
        [f g]  (:frames placed)
        inside? (fn [fr n] (<= (:x fr) (- (:x n) (/ (:w n) 2)) (+ (:x n) (/ (:w n) 2)) (+ (:x fr) (:w fr))))]
    (is (= 2 (count (:frames placed))) "an ungrouped node has no frame")
    (testing "each frame encloses its own nodes and no other"
      (is (inside? f (at 'a)))
      (is (inside? f (at 'bb)))
      (is (inside? g (at 'ccc)))
      (is (not-any? #(inside? % (at 'dd)) [f g])))
    (testing "the groups are the group gap less the frames' padding apart"
      (is (= 20 (- (:x g) (+ (:x f) (:w f))))))
    (is (= [] (svg/faults placed)) "a label inside its frame, crossed by no edge")
    (let [s (html (svg/scene placed))]
      (is (re-find #"<rect class=\"g-frame\"" s))
      (is (re-find #"<tspan[^>]*>covers, disjoint</tspan>" s)))))

(deftest a-flank-label-sits-in-a-lane-clear-of-both-columns
  (let [centre (assoc (svg/measure {:term 'parentOf}) :x 0 :y 0)
        items  (for [[t label side] '[[childOf "inverse" -1] [fatherOf "genlInverse" -1]
                                      [(BloodKinFn parentOf) "bloodKinPredicateOf" 1]
                                      [causal "arg1, arg2" 1]]]
                 {:node (svg/measure {:term t}) :label label :side side})
        placed (svg/flank centre items {:gap 12 :reach 36 :lane-pad 8})
        scene  {:nodes (cons centre (map :node placed))
                :edges (map #(select-keys % [:points :label :label-at]) placed)}]
    (is (= [] (svg/faults scene)))
    (testing "each edge runs from its node to the centre's side"
      (is (every? #(= (- (/ (:w centre) 2)) (first (peek (:points %))))
                  (filter (comp neg? :side) placed))))
    (is (= (svg/flank-height items 12) (+ (* 2 svg/node-h) 12)) "two a side, one gap between")))

;; ---- what a finished picture holds ---------------------------------------

(deftest the-fault-check-names-overlaps-crossings-and-oversized-labels
  (let [[a b c] (svg/row (nodes '[a b c]) 0 0 20)]
    (is (= [] (svg/faults {:nodes [a b c] :edges [(assoc (svg/trim a b) :from 'a :to 'b)]})))
    (testing "two boxes that overlap"
      (is (= ["node a overlaps node b"] (svg/faults {:nodes [a (assoc b :x (:x a))]}))))
    (testing "an edge through a box it does not end at"
      (is (= ["edge a → c crosses node b"]
             (svg/faults {:nodes [a b c] :edges [{:from 'a :to 'c :points [[(:x a) 0] [(:x c) 0]]}]}))))
    (testing "an edge label over a box"
      (is (= ["node b overlaps edge label genl"]
             (svg/faults {:nodes [a b] :edges [{:points [[(:x b) -40] [(:x b) -20]] :label "genl"
                                                :label-at [(:x b) 4 "middle"]}]}))))
    (testing "an edge through its own label"
      (is (= ["edge a → b crosses edge label genl"]
             (svg/faults {:edges [{:from 'a :to 'b :points [[0 -100] [0 -40]] :label "genl"
                                   :label-at [0 -66 "middle"]}]}))))
    (testing "a label wider than its box"
      (is (= ["node a's label is larger than its box"] (svg/faults {:nodes [(assoc a :w 10)]}))))
    (testing "a frame label outside its frame"
      (is (= ["frame label covers is outside its frame"]
             (svg/faults {:frames [{:x 0 :y 0 :w 20 :h 20 :label "covers" :lines ["covers"]
                                    :label-at [30 0]}]}))))))

;; ---- a card -----------------------------------------------------------------

(defn- card []
  (assoc (svg/measure-card {:term 'CxStory :class "t-context" :href "/term?q=CxStory"
                            :rows [{:text "(dog Rex)" :notes ["stored here · stated · believed"]
                                    :class "g-stated" :href "/sentex/1" :title "dog"}
                                   {:text (apply str "(" (repeat 40 "x") ")")
                                    :notes [(str/join " " (repeat 20 "withdrawn"))]
                                    :class "g-out" :href "/sentex/2" :title "long"}]
                            :more "3 more not drawn"})
         :x 0 :y 0))

(deftest a-card-stacks-its-rows-inside-it-each-as-wide-as-the-widest
  (let [{:keys [rows w h more-at] :as c} (card)
        [a b] rows]
    (is (= [] (svg/faults {:nodes [c]})))
    (is (= (:w a) (:w b)))
    (is (< (:dy a) (+ (:dy a) (:h a)) (:dy b) (+ (:dy b) (:h b)) more-at h))
    (testing "a row's text wraps at the label cap, and its note at the note cap over note-lines"
      (is (< 1 (count (:lines b))))
      (is (every? #(<= (count %) svg/label-cap) (:lines b)))
      (is (= svg/note-lines (count (:notes b))))
      (is (every? #(<= (count %) svg/note-cap) (:notes b))))
    (is (= [w h] (map #(* 2 (quot % 2)) [w h])) "even sizes, so the centre is on a whole pixel")))

(deftest the-fault-check-names-a-card-row-larger-than-its-box
  (let [c (card)]
    (is (= ["row dog of node CxStory is larger than its box"]
           (svg/faults {:nodes [(update-in c [:rows 0 :w] - 200)]})))
    (is (= ["row long of node CxStory is larger than its box"]
           (svg/faults {:nodes [(assoc c :h (+ (:dy (second (:rows c))) 10))]})))))

(deftest a-card-draws-each-row-as-its-own-link-in-its-own-class
  (let [s (html (svg/scene {:nodes [(card)]}))]
    (is (re-find #"<g class=\"g-node g-card t-context\">" s))
    (is (re-find #"<a href=\"/sentex/1\"><g class=\"g-row g-stated\">" s))
    (is (re-find #"<a href=\"/sentex/2\"><g class=\"g-row g-out\">" s))
    (is (re-find #"class=\"g-row-note\"[^>]*>3 more not drawn<" s))))

(deftest a-column-mirrors-around-the-centre
  (let [right (svg/column (nodes '[a bb]) 100 0 12 1)
        left  (svg/column (nodes '[a bb]) -100 0 12 -1)]
    (testing "the inner edge of each column is the edge it was given"
      (is (= [100 100] (map #(- (:x %) (/ (:w %) 2)) right)))
      (is (= [-100 -100] (map #(+ (:x %) (/ (:w %) 2)) left))))
    (testing "stacked, centred on y, in the order given"
      (is (apply < (map :y right)))
      (is (< (Math/abs (double (reduce + (map :y right)))) 2)))))

(deftest a-ring-widens-rather-than-overlapping
  (testing "short labels sit on the minimum radius"
    (let [r (svg/ring (nodes '[a b c]) 0 0 150 0)]
      (is (= 3 (count r)))
      (is (every? #(< (Math/abs (- 150.0 (Math/hypot (double (:x %)) (double (:y %))))) 2) r))))
  (testing "many wide ones push the radius out until the arc between them clears the widest"
    (let [wide (repeat 8 'a_rather_long_type)
          r    (svg/ring (nodes wide) 0 0 150 0)
          rad  (Math/hypot (double (:x (first r))) (double (:y (first r))))
          arc  (/ (* 2 Math/PI rad) 8)]
      (is (> rad 150) "the minimum was not enough")
      (is (>= arc (:w (first (nodes [(first wide)])))) "and no two boxes can now overlap")))
  (is (empty? (svg/ring [] 0 0 150 0))))

(deftest an-arc-hangs-off-the-angle-it-was-given
  (let [a (/ Math/PI 2)                                     ; straight down in SVG's axes
        ns (svg/arc (nodes '[x y z]) 0 0 300 a)]
    (is (= 3 (count ns)))
    (is (every? #(< (Math/abs (- 300.0 (Math/hypot (double (:x %)) (double (:y %))))) 2) ns))
    (testing "centred on the angle: the middle one is on it"
      (is (< (Math/abs (double (:x (second ns)))) 2))
      (is (pos? (:y (second ns)))))
    (is (empty? (svg/arc [] 0 0 300 0)))))

(deftest an-edge-stops-at-the-boxes-it-joins
  (let [[a b] (svg/row (nodes '[aa bb]) 0 0 100)
        {:keys [x1 x2] :as seg} (svg/trim a b)]
    (is (some? seg))
    (testing "it starts on one box's boundary and ends on the other's"
      (is (= x1 (+ (:x a) (/ (:w a) 2))))
      (is (= x2 (- (:x b) (/ (:w b) 2)))))
    (is (< x1 x2) "and runs from the first to the second"))
  (testing "two nodes on one point have no direction to draw"
    (let [n (first (nodes '[a]))]
      (is (nil? (svg/trim (assoc n :x 0 :y 0) (assoc n :x 0 :y 0)))))))

;; ---- a constraint network ------------------------------------------------

(defn- network
  "Edges `[from to label]` over the measured nodes `terms`, every pair of them related."
  [terms label]
  (vec (for [[i a] (map-indexed vector terms), b (drop (inc i) terms)]
         {:from a :to b :label label})))

(deftest a-network-part-is-a-ring-with-every-label-clear
  (doseq [[terms label] [['[Bed1 Estate1 Garden1] "eq ntpp tpp"]
                         ['[Branch1 Egg1 Nest1 Trunk1] "close co very-close"]
                         ['[(EndFn Day1) (StartFn Day1) (EndFn Morning1) (StartFn Morning1)] "after"]
                         ['[(EndFn TmpDay190319) (StartFn TmpDay190319) (EndFn TmpMorning190320)
                            (StartFn TmpMorning190320)] "after"]
                         ['[Ann Bob Cy Dee Eve Fay] "after"]
                         ['[Ann Bob Cy] ["after contains met-by" "started-by"]]]]
    (let [g (svg/ring-graph (nodes terms) (network terms label) 720)]
      (is (some? g) (str terms))
      (is (= (count terms) (count (:nodes g))))
      (is (every? :label-at (:edges g)) "every label has a place")
      (is (= [] (svg/faults g)) (str terms)))))

(deftest a-wide-label-runs-along-a-side-of-the-ring
  (let [wide ["contains during equal" "finished-by finishes" "overlapped-by overlaps"
              "started-by starts"]
        es   [{:from 'A :to 'B :label "during"} {:from 'A :to 'C :label "equal"}
              {:from 'A :to 'D :label "during"} {:from 'B :to 'C :label "contains"}
              {:from 'B :to 'D :label wide} {:from 'C :to 'D :label "during"}]
        g    (svg/ring-graph (nodes '[A B C D]) es 720)
        at   (into {} (map (juxt :term (juxt :x :y))) (:nodes g))]
    (is (= [] (svg/faults g)))
    (testing "B and D, joined by the wide label, are neighbours: level or one above the other"
      (is (or (= (first (at 'B)) (first (at 'D))) (= (second (at 'B)) (second (at 'D))))))))

(deftest a-network-part-wider-than-the-drawing-is-not-drawn
  (let [wide (map #(symbol (str % (apply str (repeat 30 "x")))) '[a b c])]
    (is (nil? (svg/ring-graph (nodes wide) (network wide "ntpp") 300)))
    (is (some? (svg/ring-graph (nodes wide) (network wide "ntpp") 2000)))))

(deftest packed-parts-wrap-at-the-width-and-keep-their-labels
  (let [parts  (for [ts '[[a b] [c d] [e f] [g h]]]
                 (svg/ring-graph (nodes ts) (network ts "before meets") 720))
        packed (svg/pack parts 400 32)
        ys     (distinct (map :y (:nodes packed)))]
    (is (= 8 (count (:nodes packed))))
    (is (< 1 (count ys)) "four parts do not fit one row 400 px wide")
    (is (= [] (svg/faults packed)))))

(deftest a-framed-scene-sets-its-label-above-everything-it-draws
  (let [g (svg/ring-graph (nodes '[a b c]) (network '[a b c] "before") 720)
        f (svg/framed g ["inconsistent: no arrangement satisfies every believed fact" "dashed"] "g-unsat")
        [{:keys [x y w h label-at]}] (:frames f)]
    (is (= [] (svg/faults f)))
    (is (every? (fn [{nx :x ny :y nw :w nh :h}]
                  (and (< x (- nx (/ nw 2)) (+ nx (/ nw 2)) (+ x w))
                       (< (+ (second label-at) 28) (- ny (/ nh 2)) (+ ny (/ nh 2)) (+ y h))))
                (:nodes f)))))

(deftest a-symmetric-edge-has-no-head-and-a-long-label-draws-a-line-each
  (let [ns (svg/row (nodes '[a b]) 0 0 200)
        s  (html (svg/scene {:nodes ns :edges [(assoc (svg/trim (first ns) (second ns))
                                                      :undirected? true :label ["eq ntpp" "tpp"]
                                                      :label-at [0 -8 "middle"])]}))]
    (is (nil? (re-find #"marker-end" s)))
    (is (re-find #"<tspan[^>]*>eq ntpp</tspan><tspan[^>]*dy=\"\d+\"[^>]*>tpp</tspan>" s))))

;; ---- a timeline -----------------------------------------------------------

(deftest a-timeline-sets-each-mark-at-its-ranks-and-each-name-left-of-the-axis
  (let [[lec drill noon] (nodes '[Lecture1 Drill1 Noon1])
        t     (svg/timeline [{:lanes [{:node lec :from 0 :to 2 :mark {:term 'Lecture1}}
                                      {:node drill :from 1 :to 3 :mark {:term 'Drill1}}]
                              :spans [{:from 0 :to 1 :label "6300 Second"}]}
                             {:lanes [{:node noon :from 0 :to 0 :mark {:term 'Noon1}}]}]
                            {:unit 48 :name-gap 16 :band-gap 24 :lane-gap 6})
        mark  (into {} (for [n (:nodes t) :when (:mark? n)] [(:term n) n]))
        left  #(- (:x %) (/ (:w %) 2))]
    (is (every? #(<= (+ (:x %) (/ (:w %) 2)) -16) (remove :mark? (:nodes t))))
    (testing "a bar runs between its ranks, and a tick is centred on its rank"
      (is (== 0 (left (mark 'Lecture1))))
      (is (== (:w (mark 'Lecture1)) (:w (mark 'Drill1)) (* 2 (left (mark 'Drill1)))))
      (is (= [0 6] ((juxt :x :w) (mark 'Noon1)))))
    (testing "the span label widens the unit, and the second band is under the first"
      (is (< 48 (left (mark 'Drill1))))
      (is (< (:y (mark 'Drill1)) (:y (mark 'Noon1)))))
    (is (= [] (svg/faults t)))))

;; ---- emission -----------------------------------------------------------

(deftest nothing-to-draw-draws-nothing
  (is (nil? (svg/scene {:nodes [] :edges []})))
  (is (nil? (svg/scene {:nodes nil :edges nil :aria-label "x"}))))

(deftest the-viewbox-crops-to-what-was-drawn
  (let [ns  (svg/row (nodes '[a bbbbbbbb]) 0 0 20)
        s   (svg/scene {:nodes ns :edges [] :aria-label "x"})
        box (mapv #(Long/parseLong %) (str/split (get-in s [1 :viewBox]) #" "))
        [x y w h] box]
    (testing "the drawn extent is inside it, with a margin and no more"
      (is (< x (- (:x (first ns)) (/ (:w (first ns)) 2))))
      (is (> (+ x w) (+ (:x (last ns)) (/ (:w (last ns)) 2))))
      (is (< h 60) "one row of 24px pills does not need a tall canvas")
      (is (neg? y) "and the row is centred on the origin, so the crop reaches above it"))))

(deftest the-viewbox-holds-every-edge-label
  (let [ns (svg/row (nodes '[a b]) 0 0 20)
        s  (svg/scene {:nodes ns :edges [{:points [[0 0] [400 0]] :label "bloodKinPredicateOf"
                                          :label-at [400 -4 "start"]}]})
        [x _ w _] (mapv #(Long/parseLong %) (str/split (get-in s [1 :viewBox]) #" "))]
    (is (<= (+ 400 (* 8 (count "bloodKinPredicateOf"))) (+ x w)))))

(deftest the-picture-says-what-it-is-and-links-where-it-points
  (let [ns (svg/row (nodes '[dog mammal]) 0 0 20)
        s  (html (svg/scene {:nodes ns :edges [(assoc (svg/trim (first ns) (second ns))
                                                      :label 'genl :kind "g-genl")]
                             :aria-label "concept graph for dog"}))]
    (is (re-find #"role=\"img\"" s) "an image to a screen reader; the prose beside it is the answer")
    (is (re-find #"aria-label=\"concept graph for dog\"" s))
    (is (re-find #"<a href=\"/term\?q=dog\"" s) "every node is navigation")
    (is (re-find #"<title>mammal</title>" s) "the whole term is one hover away")
    (is (re-find #"marker-end=\"url\(#g-arrow\)\"" s) "direction is a head, not a colour")
    (is (re-find #"class=\"g-edge g-genl\"" s) "which subsumption relation it is, as a class")
    (is (re-find #">genl</text>" s))))

(deftest a-both-ways-edge-has-a-head-at-each-end
  (let [ns (svg/row (nodes '[a b]) 0 0 40)
        s  (html (svg/scene {:nodes ns :edges [(assoc (svg/trim (first ns) (second ns))
                                                      :back? true :kind "g-rel")]}))]
    (is (re-find #"marker-start=\"url\(#g-arrow\)\"" s))
    (is (re-find #"marker-end=\"url\(#g-arrow\)\"" s))))

(deftest no-attribute-is-ever-a-ratio
  ;; `/` on longs yields a Ratio, and `1/2` in an SVG attribute is not a coordinate — it
  ;; is silently dropped by every renderer, so the picture would be subtly wrong rather
  ;; than broken.  Odd widths and an odd node count are what would produce one.
  (let [ns (svg/row (nodes '[a bbb ccccc ddddddd]) 0 -37 21)
        rg (svg/ring (nodes '[eee ff g]) 0 0 151 0.37)
        es (keep #(svg/trim (first ns) %) (concat (rest ns) rg))
        s  (html (svg/scene {:nodes (concat ns rg) :edges (map #(assoc % :label 'p) es)
                             :aria-label "x"}))]
    (is (nil? (re-find #"=\"-?\d+/\d+" s)) s)))
