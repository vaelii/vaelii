;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.browser.svg
  "The inline-SVG primitives the term page's concept graph is drawn with: a node, an
  edge, an arrowhead, and the arithmetic that lays out a row, a column or a ring.

  **No graph library.**  The browser ships two JavaScript files and this adds none — a
  layout that is a fold over a row of boxes is a dozen lines, and a dependency that drew
  it would be the largest thing the client loads.  Nor a shell-out: a page that renders
  by starting a process is a page that cannot be served.

  Everything here is **pure** — no KB, no access facade, no belief — so it is tested on
  hand-built maps.  What a node *means* is the caller's: it supplies the term, the
  colour class, the link and the tooltip, and this decides only where the box goes and
  what shape it is.

  Coordinates live in one flat user space and may be negative; `scene` crops the
  `viewBox` to the union of what was actually drawn, so a sparse graph is centred rather
  than adrift in a fixed canvas and a long snake_case label is never clipped.  Every
  number reaching an attribute is a **long**: Clojure's `/` yields a ratio, and `1/2` in
  an SVG attribute is not a coordinate."
  (:require [clojure.string :as str]))

;; ---- measurement --------------------------------------------------------

(def label-cap
  "How many characters of a term's name a node label carries.  Past this it is cut and
  the whole term goes in the node's `title`, so nothing is lost — only moved one hover
  away.  Twenty-two holds `physical_object` and every predicate the shipped schema has,
  and is short enough that a row of eight still reads."
  22)

(def node-h
  "Every node is the same height.  A row is then a straight line of pills and the eye
  reads the row rather than the boxes."
  28)

(def ^:private char-w
  "Advance of one character in a node label.  A node label is a **term**, so it is set in
  the page's monospace face, where every character advances .6em and this is a width
  rather than an estimate: 13.5px (`--g-label`) raised by the sheet's `font-size-adjust`
  of .535 against Hasklig's own .486 x-height is 14.86px used, and .6 of that is 8.92.
  Nine leaves the eighth of a pixel per character as slack, on the side that matters —
  text narrower than its box is centred, text wider than it spills.  The sheet's
  `--g-label` and `--x-height` are the other two thirds of this number; all three move
  together or the pills stop fitting their labels."
  9.0)

(def ^:private pad 10)

(defn label
  "The text a node carries for `term`, cut to `label-cap` with an ellipsis."
  [term]
  (let [s (str term)]
    (if (<= (count s) label-cap) s (str (subs s 0 (dec label-cap)) "…"))))

(defn measure
  "Give a node its label and its box — `:label`, `:w`, `:h` — leaving *where* it goes to
  the layout fns below.  Idempotent, so a caller may measure once and place twice.

  The text is `:display` when the caller supplied one, else the term itself: what a term
  is *called* on the page is the caller's business (a reified term is indistinguishable from the
  expression it denotes), and `:term` stays the identity the layout dedups on.

  The width is rounded **up to an even number**, and `node-h` is even for the same reason:
  a box's edge is then an integer wherever its centre is, so `trim` lands an arrowhead
  exactly on the boundary instead of half a pixel inside it."
  [node]
  (let [l (label (or (:display node) (:term node)))]
    (assoc node
           :label l
           :w (long (* 2 (Math/ceil (/ (+ (* char-w (count l)) (* 2.0 pad)) 2.0))))
           :h node-h)))

;; ---- layout -------------------------------------------------------------
;;
;; Three shapes, and they are the whole layout engine.  A row for a taxonomy level, a
;; column for the relation flanks, a ring for the ego view.  None of them iterates to a
;; fixpoint or simulates anything: given the boxes, each is one pass of arithmetic, so
;; the picture is a pure function of what was read and re-renders identically.

(defn row
  "Place measured `nodes` left to right in a row centred on `cx` at height `y`, `gap`
  apart."
  [nodes cx y gap]
  (let [total (+ (reduce + 0 (map :w nodes)) (* gap (max 0 (dec (count nodes)))))]
    (first (reduce (fn [[out x] n]
                     [(conj out (assoc n :x (long (Math/round (+ x (/ (:w n) 2.0))))
                                       :y (long y)))
                      (+ x (:w n) gap)])
                   [[] (- cx (/ total 2.0))]
                   nodes))))

(defn column
  "Place measured `nodes` in a vertical column beside the centre, stacked `gap` apart and
  centred on `y`.  `side` is -1 for a column to the *left* of `x-edge` (its right edge
  there) and 1 for one to the right, so the two flanks mirror without the caller doing
  the arithmetic twice."
  [nodes x-edge y gap side]
  (let [n     (count nodes)
        total (+ (* n node-h) (* gap (max 0 (dec n))))
        top   (- y (/ total 2.0))]
    (map-indexed (fn [i node]
                   (assoc node
                          :x (long (Math/round (+ x-edge (* side (/ (:w node) 2.0)))))
                          :y (long (Math/round (+ top (* i (+ node-h gap)) (/ node-h 2.0))))))
                 nodes)))

(defn ring
  "Place measured `nodes` evenly around a circle centred at (`cx`, `cy`), starting at
  `start` radians and going clockwise.

  The radius is **computed, not given**: `min-r`, or whatever radius spaces the arc
  between neighbours at 1.15× the widest box — so eight long names spread onto a wider
  ring instead of overlapping, and two short ones do not fly apart.  That is the whole
  reason a ring is affordable without a force simulation."
  [nodes cx cy min-r start]
  (let [n (count nodes)]
    (if (zero? n)
      []
      (let [widest (reduce max 0 (map :w nodes))
            r      (max min-r (/ (* n widest 1.15) (* 2 Math/PI)))
            step   (/ (* 2 Math/PI) n)]
        (map-indexed (fn [i node]
                       (let [a (+ start (* i step))]
                         (assoc node
                                :x (long (Math/round (+ cx (* r (Math/cos a)))))
                                :y (long (Math/round (+ cy (* r (Math/sin a)))))
                                :angle a)))
                     nodes)))))

(defn arc
  "Place measured `nodes` on a short arc of radius `r` **centred on angle** `a` around
  (`cx`, `cy`) — a cluster hanging off one direction rather than a full ring, which is
  what puts a neighbour's own neighbours out past it instead of somewhere else entirely.

  The angular step is derived from the widest box exactly as `ring`'s radius is: the arc
  between two of them is 1.1× the widest, so a cluster of long names spreads and a pair of
  short ones stays tight."
  [nodes cx cy r a]
  (let [n (count nodes)]
    (if (zero? n)
      []
      (let [widest (reduce max 0 (map :w nodes))
            step   (/ (* widest 1.1) (double r))
            start  (- a (* step (/ (dec n) 2.0)))]
        (map-indexed (fn [i node]
                       (let [t (+ start (* i step))]
                         (assoc node
                                :x (long (Math/round (+ cx (* r (Math/cos t)))))
                                :y (long (Math/round (+ cy (* r (Math/sin t)))))
                                :angle t)))
                     nodes)))))

(defn trim
  "The visible segment between two **placed** nodes: the line between their centres,
  clipped at each one's box, so an arrowhead lands on the boundary of the node it points
  at rather than under its label.  Nil when the two centres coincide — there is no
  direction to draw."
  [a b]
  (let [dx (- (:x b) (:x a))
        dy (- (:y b) (:y a))]
    (when-not (and (zero? dx) (zero? dy))
      (let [clip (fn [node sign]
                   ;; the ray leaves a box through whichever pair of sides it reaches
                   ;; first, which is the smaller of the two axis ratios
                   (let [hw (/ (:w node) 2.0)
                         hh (/ (:h node) 2.0)
                         tx (if (zero? dx) Double/POSITIVE_INFINITY (/ hw (Math/abs (double dx))))
                         ty (if (zero? dy) Double/POSITIVE_INFINITY (/ hh (Math/abs (double dy))))
                         t  (min tx ty)]
                     [(long (Math/round (+ (:x node) (* sign t dx))))
                      (long (Math/round (+ (:y node) (* sign t dy))))]))
            [x1 y1] (clip a 1)
            [x2 y2] (clip b -1)]
        {:x1 x1 :y1 y1 :x2 x2 :y2 y2}))))

;; ---- emitters -----------------------------------------------------------

(defn- arrow-defs
  "The shared arrowhead marker.  One marker, referenced by every edge: direction is
  carried by the head and by the edge label, never by colour alone."
  []
  [:defs
   [:marker {:id "g-arrow" :viewBox "0 0 10 10" :refX "9" :refY "5"
             :markerWidth "5" :markerHeight "5" :orient "auto-start-reverse"}
    [:path {:d "M 0 0 L 10 5 L 0 10 z" :class "g-arrowhead"}]]])

(def ^:private node-corner
  "The corner radius of a node box.  A box, not a pill: a label is set flush left-to-right
  inside a rectangle, where a fully-rounded end eats the width a long term needs and makes
  two adjacent nodes read as one capsule.  Three pixels is a corner rather than a curve."
  3)

(defn- node-el
  "One placed node: a box in the term's role colour, labelled, and **linked to the
  term's page** — the graph is navigation, not decoration.  The colour is a class, so it
  resolves to the same CSS custom property the links beside it use and cannot drift from
  them."
  [{:keys [x y w h label class href title]}]
  (let [g [:g {:class (str "g-node " class)}
           [:rect {:x (long (Math/round (- x (/ w 2.0)))) :y (long (Math/round (- y (/ h 2.0))))
                   :width w :height h :rx node-corner :class "g-box"}]
           [:text {:x x :y (+ y 4) :text-anchor "middle" :class "g-label"} label]
           [:title (str title)]]]
    (if href [:a {:href href} g] g)))

(defn- edge-el
  "One edge: a line with the shared arrowhead, and — when it carries one — the relation
  name centred on it.  `:kind` becomes a class, which is how a `genlCx` edge is told
  from a `genl` edge without either of them being a different colour of the same claim.
  `:back?` puts a head at the other end too, for a pair related both ways."
  [{:keys [x1 y1 x2 y2 label kind back?]}]
  [:g {:class (str "g-edge " (or kind ""))}
   [:line (cond-> {:x1 x1 :y1 y1 :x2 x2 :y2 y2 :marker-end "url(#g-arrow)"}
            back? (assoc :marker-start "url(#g-arrow)"))]
   (when label
     [:text {:x (long (/ (+ x1 x2) 2)) :y (- (long (/ (+ y1 y2) 2)) 5)
             :text-anchor "middle" :class "g-edge-label"}
      (str label)])])

(defn- bbox
  "The rectangle everything drawn fits inside — node boxes, edge endpoints, and an edge
  label's own extent, which reaches past the segment it sits on."
  [nodes edges]
  (let [pts (concat (mapcat (fn [{:keys [x y w h]}]
                              [[(- x (/ w 2.0)) (- y (/ h 2.0))]
                               [(+ x (/ w 2.0)) (+ y (/ h 2.0))]])
                            nodes)
                    (mapcat (fn [{:keys [x1 y1 x2 y2 label]}]
                              (let [mx (/ (+ x1 x2) 2.0)
                                    my (/ (+ y1 y2) 2.0)
                                    lw (if label (/ (* char-w (count (str label))) 2.0) 0)]
                                [[x1 y1] [x2 y2]
                                 [(- mx lw) (- my 16)] [(+ mx lw) my]]))
                            edges))]
    (when (seq pts)
      (let [xs (map first pts) ys (map second pts)]
        [(apply min xs) (apply min ys) (apply max xs) (apply max ys)]))))

(def ^:private margin 14)

(defn scene
  "The whole picture as one `<svg>`, or **nil** when there is nothing to draw — a caller
  renders the nil and gets no empty frame.

  `aria-label` is what a screen reader is told the image shows; it is `role=\"img\"`
  because the prose above it, not the picture, is the accessible answer.  The `viewBox`
  is the crop, and an intrinsic pixel `width`/`height` (one user unit to one CSS px) draws
  the graph at its natural size — a wide one scrolls inside `.kb-graph-fig` rather than
  shrinking to an unreadable strip on a narrow column."
  [{:keys [nodes edges aria-label]}]
  (when (seq nodes)
    (let [[x0 y0 x1 y1] (bbox nodes edges)
          w (+ (- x1 x0) (* 2 margin))
          h (+ (- y1 y0) (* 2 margin))]
      [:svg {:class "kb-graph" :role "img" :aria-label (str aria-label)
             :xmlns "http://www.w3.org/2000/svg"
             :viewBox (str/join " " (map #(long (Math/round (double %)))
                                         [(- x0 margin) (- y0 margin) w h]))
             ;; an intrinsic pixel size (1 user unit = 1 CSS px) so the graph is drawn at
             ;; its natural width and a wide one scrolls inside `.kb-graph-fig` rather than
             ;; shrinking to an unreadable strip on a narrow (portrait) column
             :width w :height h :preserveAspectRatio "xMidYMid meet"}
       (arrow-defs)
       ;; edges first, so a line is never drawn over the label it connects
       (map edge-el edges)
       (map node-el nodes)])))
