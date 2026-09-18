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

(deftest a-long-name-is-cut-and-kept
  (testing "a label at or under the cap is the term"
    (is (= "physical_object" (svg/label 'physical_object)))
    (is (= svg/label-cap (count (svg/label (symbol (apply str (repeat svg/label-cap "x"))))))))
  (testing "past it the label is cut with an ellipsis — the whole term goes in the title"
    (let [long-name (symbol (apply str (repeat 60 "x")))
          l         (svg/label long-name)]
      (is (= svg/label-cap (count l)))
      (is (str/ends-with? l "…"))
      (is (str/starts-with? (str long-name) (subs l 0 (dec (count l))))))))

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
