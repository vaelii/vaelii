;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.browser.svg
  "The inline-SVG primitives the browser's graphs are drawn with: a node, an edge, an
  arrowhead, and the arithmetic that lays out layered rows, a relation flank, a column or
  a ring.  `faults` lists the overlaps and crossings in a finished picture.

  **No graph library.**  The browser ships two JavaScript files and this adds none, and
  no shell-out: a page that renders by starting a process is a page that cannot be served.

  Everything here is **pure** — no KB, no access facade, no belief — so it is tested on
  hand-built maps.  What a node *means* is the caller's: it supplies the term, the
  colour class, the link and the tooltip, and this decides only where the box goes and
  what shape it is.

  Coordinates live in one flat user space and may be negative; `scene` crops the
  `viewBox` to the union of what was actually drawn.  Every number reaching an attribute
  is a **long**: Clojure's `/` yields a ratio, and `1/2` in an SVG attribute is not a
  coordinate."
  (:require [clojure.string :as str]))

;; ---- measurement --------------------------------------------------------

(def label-cap
  "How many characters one line of a term's node label holds.  Thirty-two holds every
  name the shipped ontology has, `CxNormalPhysicalConditions` (26) among them, so a name
  is drawn whole; a longer label wraps (`wrap-text`), and the node's `title` holds the
  whole term."
  32)

(def sentence-cap
  "How many characters one line of a sentence's node label holds, for a node whose `:cap`
  is this: a proof's node is a sentence.  A node at the cap is 380 px wide (`char-w` × 40
  and the padding)."
  40)

(def label-lines
  "How many lines a node label wraps over.  Text past the last line is cut, and the last
  line ends in an ellipsis."
  3)

(def node-h
  "The height of a one-line node.  Each further line of a wrapped label adds `line-h`."
  28)

(def ^:private line-h
  "The distance between two lines of one node label: the label's 14.86 px used size and
  three pixels of leading, even so a box stays an even height."
  18)

(def ^:private char-w
  "Advance of one character in a node label.  A node label is a **term**, set in the
  page's monospace face, where every character advances .6em.  The used size is 14.86px:
  13.5px (`--g-label`) raised by the sheet's `font-size-adjust` of .535 against Hasklig's
  own .486 x-height.  Six tenths of that is 8.92.
  Nine leaves the eighth of a pixel per character as slack, on the side that matters —
  text narrower than its box is centred, text wider than it spills.  The sheet's
  `--g-label` and `--x-height` are the other two thirds of this number; all three move
  together or the boxes stop fitting their labels."
  9.0)

(def ^:private pad 10)

(def ^:private small-char-w
  "Advance of one character in an edge or frame label: `char-w` scaled from `--g-label`
  (13.5px) to `--g-edge` (12px), the size the sheet sets both at."
  8.0)

(def ^:private small-line-h
  "The distance between two lines of a frame label, set at `--g-edge`."
  14)

(defn- even-up [x] (long (* 2 (Math/ceil (/ (double x) 2.0)))))

(defn- rnd [x] (long (Math/round (double x))))

(defn wrap-text
  "`s` as at most `lines` lines of at most `cap` characters each: broken at spaces, and
  inside a word only where the word alone is longer than `cap`.  Text past the last line
  is cut, and the last line then ends in an ellipsis."
  [s cap lines]
  (let [words (mapcat (fn [w] (map #(apply str %) (partition-all cap w)))
                      (remove str/blank? (str/split (str s) #" ")))
        ls    (reduce (fn [ls w]
                        (let [l (peek ls)]
                          (if (and l (<= (+ (count l) 1 (count w)) cap))
                            (conj (pop ls) (str l " " w))
                            (conj ls w))))
                      [] words)]
    (cond (empty? ls)           [""]
          (<= (count ls) lines) ls
          :else (let [kept (subvec ls 0 lines)
                      l    (peek kept)]
                  (conj (pop kept) (str (subs l 0 (min (count l) (dec cap))) "…"))))))

(defn measure
  "Give a node its label lines and its box — `:lines`, `:w`, `:h` — leaving *where* it
  goes to the layout fns below.  Idempotent, so a caller may measure once and place twice.

  The text is `:display` when the caller supplied one, else the term itself, wrapped at
  the node's `:cap` (default `label-cap`) characters a line over at most `label-lines`
  lines.  A vector `:display` is one line per string, each cut at the cap.  `:term` stays
  the identity the layout places by.  The width and the height are even, so a box's edge
  is an integer wherever its centre is."
  [node]
  (let [d  (or (:display node) (:term node))
        c  (:cap node label-cap)
        ls (if (vector? d)
             (mapv #(first (wrap-text % c 1)) (take label-lines d))
             (wrap-text d c label-lines))]
    (assoc node
           :lines ls
           :w (even-up (+ (* char-w (reduce max 0 (map count ls))) (* 2.0 pad)))
           :h (+ node-h (* line-h (dec (count ls)))))))

(defn- small-text-w [s] (* small-char-w (count (str s))))

(defn- text-lines
  "An edge label's lines: a vector holds one string per line, anything else is one line."
  [l]
  (if (vector? l) l [(str l)]))

(defn- text-box
  "The box `--g-edge` text `s` (one line, or a vector of lines `small-line-h` apart) at
  `[x baseline anchor]` covers: from 10 px above the first baseline to 3 px under the last."
  [[x y anchor] s]
  (let [ls (text-lines s)
        w  (reduce max 0 (map small-text-w ls))
        x0 (case anchor "start" x "end" (- x w) (- x (/ w 2.0)))]
    [x0 (- y 10.0) (+ x0 w) (+ y 3.0 (* small-line-h (dec (count ls))))]))

(defn- crosses?
  "Does the segment from `p` to `q` pass through the inside of `box`, shrunk by a pixel so
  that touching an edge is not crossing it?  Liang–Barsky clipping."
  [[x1 y1] [x2 y2] [bx0 by0 bx1 by1]]
  (let [dx (- x2 x1) dy (- y2 y1)
        lim [[(- dx) (- x1 (+ bx0 1))] [dx (- (- bx1 1) x1)]
             [(- dy) (- y1 (+ by0 1))] [dy (- (- by1 1) y1)]]]
    (boolean
     (reduce (fn [[u0 u1] [p q]]
               (cond (zero? p) (if (neg? q) (reduced nil) [u0 u1])
                     :else (let [t (/ (double q) p)
                                 [u0 u1] (if (neg? p) [(max u0 t) u1] [u0 (min u1 t)])]
                             (if (< u0 u1) [u0 u1] (reduced nil)))))
             [0.0 1.0] lim))))

(defn- beside
  "The places a label of `n` lines goes `d` px from (`mx`, `my`), each `[x first-baseline
  anchor]`: right of the point, left of it, above it and below it."
  [mx my d n]
  (let [extra (* small-line-h (dec n))]
    [[(+ mx d) (- (+ my 4) (quot extra 2)) "start"] [(- mx d) (- (+ my 4) (quot extra 2)) "end"]
     [mx (- my d extra) "middle"] [mx (+ my d 10) "middle"]]))

(defn- label-beside
  "Where the label `s` of an edge through `pts` goes, `[x baseline anchor]`.  The label sits
  beside the middle of the segment `[p q]`, at the first of 6, 12, 24 and 48 px right, left,
  above or below it that no segment of the edge crosses, else 5 px above the middle."
  [pts [[ax ay] [bx by]] s]
  (let [mx (rnd (/ (+ ax bx) 2.0))
        my (rnd (/ (+ ay by) 2.0))]
    (or (first (for [d [6 12 24 48]
                     c (beside mx my d (count (text-lines s)))
                     :when (not-any? (fn [[p q]] (crosses? p q (text-box c s))) (partition 2 1 pts))]
                 c))
        [mx (- my 5) "middle"])))

;; ---- layout -------------------------------------------------------------
;;
;; Each layout is a bounded number of passes of arithmetic over the boxes, so the picture
;; is a pure function of what was read and re-renders identically.

(defn row
  "Place measured `nodes` left to right in a row centred on `cx` at height `y`, `gap`
  apart."
  [nodes cx y gap]
  (let [total (+ (reduce + 0 (map :w nodes)) (* gap (max 0 (dec (count nodes)))))]
    (first (reduce (fn [[out x] n]
                     [(conj out (assoc n :x (rnd (+ x (/ (:w n) 2.0))) :y (long y)))
                      (+ x (:w n) gap)])
                   [[] (- cx (/ total 2.0))]
                   nodes))))

(def ^:private frame-pad
  "The clear space between a group frame and the boxes it encloses."
  6)

(defn- wrap
  "`nodes` cut into lines in order, each of at most `cap` nodes and at most `width` wide
  with `gap` between boxes.  A node wider than `width` has a line to itself."
  [nodes cap width gap]
  (if (empty? nodes)
    []
    (first (reduce (fn [[ls w] n]
                     (let [l (peek ls), w' (+ w gap (:w n))]
                       (if (and (seq l) (or (>= (count l) cap) (> w' width)))
                         [(conj ls [n]) (:w n)]
                         [(conj (pop ls) (conj l n)) (if (seq l) w' (:w n))])))
                   [[[]] 0] nodes))))

(defn- mean [xs] (when (seq xs) (/ (reduce + 0.0 xs) (count xs))))

(defn- order-layers
  "Each layer of `by-layer` ({layer [node …]}) in an order that reduces crossings.  Three
  rounds of a downward and an upward sweep each sort a layer by the mean relative position
  of its neighbours (`nbrs`, term → nodes) in the layer the sweep came from.  A node with
  none keeps its own position.  A node's `:group` block, ranked by `ranks`, comes before
  the ungrouped nodes, and `:order` breaks every tie."
  [by-layer nbrs ranks]
  (let [layers (vec (sort (keys by-layer)))
        block  (fn [n] (if-let [g (:group n)] (ranks g 0) Long/MAX_VALUE))
        posmap (fn [order]
                 (into {} (for [[_ ns] order, [i n] (map-indexed vector ns)]
                            [(:term n) (/ (+ i 0.5) (count ns))])))
        sweep  (fn [order ls]
                 (reduce (fn [order [from layer]]
                           (let [pos (posmap order)
                                 key (fn [n] (or (mean (keep #(when (= from (:layer %)) (pos (:term %)))
                                                             (nbrs (:term n))))
                                                 (pos (:term n))))]
                             (assoc order layer (vec (sort-by (fn [n] [(block n) (key n) (:order n)])
                                                              (order layer))))))
                         order (map vector ls (rest ls))))
        start  (into {} (for [l layers]
                          [l (vec (sort-by (fn [n] [(block n) (:order n)]) (by-layer l)))]))]
    (reduce (fn [order _] (sweep (sweep order layers) (rseq layers))) start (range 3))))

(defn- separation
  "The least distance between the centres of two neighbouring items of one line: half of
  each width and the gap, `group-gap` where they belong to different group blocks."
  [a b gap group-gap]
  (+ (/ (+ (:w a) (:w b)) 2.0)
     (if (and (or (:group a) (:group b)) (not= (:group a) (:group b))) group-gap gap)))

(defn- place-line
  "The x of each of `items`, one line in order, as near `want` (a vector of desired x) as
  their separations allow: the mean of the leftmost and the rightmost placement that keeps
  every separation, which keeps them too."
  [items want gap group-gap]
  (let [n   (count items)
        sep (mapv #(separation (items %) (items (inc %)) gap group-gap) (range (dec n)))
        ltr (reduce (fn [xs i] (conj xs (max (want i) (+ (peek xs) (sep (dec i))))))
                    [(want 0)] (range 1 n))
        rtl (reduce (fn [xs i] (cons (min (want i) (- (first xs) (sep i))) xs))
                    (list (want (dec n))) (range (- n 2) -1 -1))]
    (mapv (fn [a b] (/ (+ a b) 2.0)) ltr rtl)))

(defn- slot-lines
  "The slots of a layered drawing, top to bottom: each layer's ordered nodes cut into lines
  (`wrap`), each line `{:layer :first? :items}`.  A group's frame label is an item of its
  own, before the group's first member."
  [ordered groups cap width gap]
  (vec (for [layer (sort (keys ordered))
             [i line] (map-indexed vector (wrap (ordered layer) cap width gap))]
         {:layer layer :first? (zero? i)
          :items (vec (mapcat (fn [prev n]
                                (let [g (:group n)]
                                  (if (and g (not= g (:group prev)))
                                    (let [ls (:lines (groups g))]
                                      [{:term [::label g] :group g :kind :label :lines ls
                                        :w (even-up (reduce max 0 (map small-text-w ls)))
                                        :h (* small-line-h (count ls))}
                                       n])
                                    [n])))
                              (cons nil line) line))})))

(defn- with-dummies
  "`slots` with a zero-width dummy item in every slot an edge passes through, and each
  edge's chain of items from its tail to its head.  A dummy goes before the first block
  (a group, or one ungrouped item) whose centre in a plain row lies right of the point
  where the straight line between the edge's ends crosses the slot."
  [slots edges gap]
  (let [slot-of (into {} (for [[s {:keys [items]}] (map-indexed vector slots), it items]
                           [(:term it) s]))
        x0      (into {} (for [{:keys [items]} slots, it (row items 0 0 gap)] [(:term it) (:x it)]))
        chains  (mapv (fn [i {:keys [from to]}]
                        (let [a (slot-of from), b (slot-of to), step (if (< a b) 1 -1)]
                          (vec (concat [from]
                                       (when (not= a b) (for [s (range (+ a step) b step)] [::dummy i s]))
                                       [to]))))
                      (range) edges)
        dx      (into {} (for [ch chains
                               :let [xa (x0 (first ch)), xb (x0 (peek ch)), k (dec (count ch))]
                               [j d] (map-indexed vector (subvec ch 1 k))]
                           [d (+ xa (* (- xb xa) (/ (inc j) (double k))))]))
        insert  (fn [slots [_ _ s :as d]]
                  (update-in slots [s :items]
                             (fn [items]
                               (let [x      (fn [it] (if (= :dummy (:kind it)) (dx (:term it)) (x0 (:term it))))
                                     blocks (partition-by #(or (:group %) (:term %)) items)
                                     [l r]  (split-with #(<= (mean (map x %)) (dx d)) blocks)]
                                 (vec (concat (apply concat l) [{:term d :kind :dummy :w 0 :h 0}]
                                              (apply concat r)))))))]
    [(reduce insert slots (sort-by (fn [[_ i s :as d]] [s (dx d) i]) (keys dx))) chains]))

(defn- x-place
  "The x of every item of `slots`, by term.  Each slot starts as a plain row.  Four rounds
  follow, each a downward sweep that places a slot under the mean x of its items'
  neighbours above and an upward sweep that places it over those below (`place-line`).
  An item with no neighbours on the side swept from stays put.  A frame label keeps its
  separation from its group's first member."
  [slots above below gap group-gap]
  (let [n     (count slots)
        place (fn [xs s side]
                (let [items (:items (slots s))
                      raw   (mapv #(or (mean (map xs (side (:term %)))) (xs (:term %))) items)
                      want  (vec (map-indexed
                                  (fn [i it]
                                    (if (= :label (:kind it))
                                      (- (raw (inc i)) (separation it (items (inc i)) gap group-gap))
                                      (raw i)))
                                  items))]
                  (into xs (map (fn [it x] [(:term it) x]) items (place-line items want gap group-gap)))))]
    (reduce (fn [xs _]
              (as-> xs xs
                (reduce #(place %1 %2 above) xs (range 1 n))
                (reduce #(place %1 %2 below) xs (range (- n 2) -1 -1))))
            (into {} (for [{:keys [items]} slots, it (row items 0 0 gap)] [(:term it) (:x it)]))
            (range 4))))

(defn- spread-ports
  "Where each edge meets a node: `{[term side other] x}`, `side` :top or :bottom.  A node's
  attachments on one side are ordered by the x of the item at their other end and spread
  10 px apart, inside the box, so arrowheads meeting one box do not stack."
  [placed links slot-ix]
  (let [att (reduce (fn [m [u v]]
                      (let [[hi lo] (if (<= (slot-ix u) (slot-ix v)) [u v] [v u])
                            same?   (= (slot-ix u) (slot-ix v))]
                        (-> m (update [hi :bottom] (fnil conj []) lo)
                            (update [lo (if same? :bottom :top)] (fnil conj []) hi))))
                    {} links)]
    (into {} (for [[[t side] others] att
                   :let [{:keys [x w]} (placed t)
                         os   (vec (sort-by (fn [o] [(:x (placed o)) (or (:order (placed o)) "")]) (distinct others)))
                         k    (count os)
                         span (min (- w 12) (* 10 (dec k)))]
                   [i o] (map-indexed vector os)]
               [[t side o] (if (= 1 k) x (rnd (+ (- x (/ span 2.0)) (* i (/ span (double (dec k)))))))]))))

(defn- straighten
  "`pts` less each point on the straight line between the points either side of it."
  [pts]
  (reduce (fn [out p]
            (let [n (count out)]
              (if (< n 2)
                (conj out p)
                (let [[ax ay] (out (- n 2)), [bx by] (out (dec n)), [cx cy] p]
                  (if (zero? (- (* (- bx ax) (- cy ay)) (* (- by ay) (- cx ax))))
                    (conj (pop out) p)
                    (conj out p))))))
          [] pts))

(defn- route
  "The points of the edge whose items are `chain`, tail first, and the segment its label
  goes on: `{:points :gap [p q]}`.  Each segment between two slots runs from the band edge
  of one to the band edge of the next, where no box is.  A node's port reaches its band
  edge straight up or down, and a dummy crosses its slot straight.  An edge between two
  items of one slot dips under the slot's band.  `:gap` is the segment out of the tail's
  slot."
  [chain placed slot-ix port band-edge]
  (let [legs (map
              (fn [[u v]]
                (let [su (slot-ix u), sv (slot-ix v), pu (placed u), pv (placed v)
                      same? (= su sv), down? (< su sv)
                      su-side (if (or same? down?) :bottom :top)
                      sv-side (cond same? :bottom down? :top :else :bottom)
                      xu (if (= :dummy (:kind pu)) (:x pu) (port [u su-side v]))
                      xv (if (= :dummy (:kind pv)) (:x pv) (port [v sv-side u]))
                      end (fn [p side] (+ (:y p) (* (if (= side :bottom) 1 -1) (quot (:h p) 2))))]
                  [(when (not= :dummy (:kind pu)) [[xu (end pu su-side)]])
                   (if same?
                     [[xu (+ 12 (band-edge su :bottom))] [xv (+ 12 (band-edge sv :bottom))]]
                     [[xu (band-edge su su-side)] [xv (band-edge sv sv-side)]])
                   (when (not= :dummy (:kind pv)) [[xv (end pv sv-side)]])]))
              (partition 2 1 chain))]
    {:points (straighten (mapv first (partition-by identity (mapcat #(apply concat %) legs))))
     :gap    (second (first legs))}))

(defn layered
  "Place a layered drawing.  Each of `nodes` is measured and has a `:term`, an integer
  `:layer` (a smaller layer is higher on the page) and a content key `:order`.  Each of
  `edges` has `:from` and `:to` terms and whatever else the caller puts on it.  Opts:
  `:level` (one-line rows' centre distance), `:gap`, `:cap` and `:width` past which a layer
  wraps onto lines `:line-gap` apart, and `:bands` {layer least-height}.  `:groups` is
  {group {:rank n :lines [s …]}}; a node's `:group` keeps it in a block `:group-gap` from
  its neighbours, framed with the lines as its label.  Returns `{:nodes :edges :frames}`,
  each edge with its `:points`."
  [nodes edges {:keys [level gap cap width line-gap bands groups group-gap]
                :or   {cap Long/MAX_VALUE width Long/MAX_VALUE line-gap 0 bands {} groups {}}}]
  (let [group-gap (or group-gap gap)
        by-term   (into {} (map (juxt :term identity)) nodes)
        edges     (vec (sort-by (fn [e] [(:order (by-term (:from e))) (:order (by-term (:to e)))])
                                (filter #(and (by-term (:from %)) (by-term (:to %))) edges)))
        nbrs      (reduce (fn [m {:keys [from to]}]
                            (-> m (update from (fnil conj []) (by-term to))
                                (update to (fnil conj []) (by-term from))))
                          {} edges)
        ordered   (order-layers (group-by :layer nodes) nbrs
                                (into {} (map (fn [[g v]] [g (:rank v)])) groups))
        [slots chains] (with-dummies (slot-lines ordered groups cap width gap) edges gap)
        slot-ix   (into {} (for [[s {:keys [items]}] (map-indexed vector slots), it items]
                             [(:term it) s]))
        links     (for [ch chains, [u v] (partition 2 1 ch)] [u v])
        side-of   (fn [pick] (reduce (fn [m [u v]]
                                       (let [[hi lo] (if (<= (slot-ix u) (slot-ix v)) [u v] [v u])
                                             [k o]   (pick hi lo)]
                                         (update m k (fnil conj []) o)))
                                     {} links))
        xs        (x-place slots (side-of (fn [hi lo] [lo hi])) (side-of (fn [hi lo] [hi lo]))
                           gap group-gap)
        band      (mapv (fn [{:keys [layer first? items]}]
                          (max (reduce max 0 (map :h items)) (if first? (bands layer 0) 0)))
                        slots)
        ys        (reduce (fn [ys s]
                            (conj ys (+ (peek ys) (/ (band (dec s)) 2.0)
                                        (if (= (:layer (slots (dec s))) (:layer (slots s)))
                                          line-gap
                                          (- level node-h))
                                        (/ (band s) 2.0))))
                          [0.0] (range 1 (count slots)))
        placed    (into {} (for [[s {:keys [items]}] (map-indexed vector slots), it items]
                             [(:term it) (assoc it :x (rnd (xs (:term it))) :y (rnd (ys s)))]))
        band-edge (fn [s side] (rnd ((if (= side :top) - +) (ys s) (/ (band s) 2.0))))
        port      (spread-ports placed links slot-ix)]
    {:nodes  (into [] (comp (mapcat :items) (remove :kind) (map (comp placed :term))) slots)
     :edges  (mapv (fn [e ch]
                     (let [{:keys [points] [[ax ay] [bx by]] :gap} (route ch placed slot-ix port band-edge)]
                       (cond-> (assoc e :points points)
                         (:label e)
                         (assoc :label-at (label-beside points [[ax ay] [bx by]] (:label e))))))
                   edges chains)
     :frames (vec (for [[g {:keys [lines]}] (sort-by (comp :rank val) groups)
                        :let [members (filter #(= g (:group %)) (vals placed))]
                        :when (seq members)
                        :let [s   (slot-ix (:term (first members)))
                              x0  (- (reduce min (map #(- (:x %) (/ (:w %) 2.0)) members)) frame-pad)
                              x1  (+ (reduce max (map #(+ (:x %) (/ (:w %) 2.0)) members)) frame-pad)
                              lbl (placed [::label g])]]
                    {:x (rnd x0) :y (rnd (- (ys s) (/ (band s) 2.0) frame-pad))
                     :w (rnd (- x1 x0)) :h (long (+ (band s) (* 2 frame-pad)))
                     :label (str/join " " lines) :lines lines
                     :label-at [(- (:x lbl) (quot (:w lbl) 2)) (- (:y lbl) (quot (:h lbl) 2))]}))}))

(defn column
  "Place measured `nodes` in a vertical column, stacked `gap` apart and centred on `y`.
  `side` is -1 for a column to the *left* of `x-edge` (its right edge there) and 1 for one
  to the right, so the two flanks mirror without the caller doing the arithmetic twice."
  [nodes x-edge y gap side]
  (let [total (+ (reduce + 0 (map :h nodes)) (* gap (max 0 (dec (count nodes)))))]
    (first (reduce (fn [[out top] node]
                     [(conj out (assoc node
                                       :x (rnd (+ x-edge (* side (/ (:w node) 2.0))))
                                       :y (rnd (+ top (/ (:h node) 2.0)))))
                      (+ top (:h node) gap)])
                   [[] (- y (/ total 2.0))]
                   nodes))))

(defn flank-height
  "How tall the taller of the two flank columns of `items` (see `flank`) stands."
  [items gap]
  (reduce max 0 (for [[_ side] (group-by :side items)]
                  (+ (reduce + 0 (map (comp :h :node) side)) (* gap (dec (count side)))))))

(defn flank
  "Place the relation flank beside the placed `centre`: each of `items` (`{:node measured
  :label s :side -1|1}`) in a column on its side, centred on the centre's height, `gap`
  apart.  Between a column and the centre is a lane as wide as that side's widest label
  plus `lane-pad` each side, then `reach` px of open space.  An item's route runs from its
  node's inner side straight across the lane, with the label over it, then to a port on
  the centre's side; ports are spread over the side in the columns' order.  Returns the
  items in order, each with its placed `:node`, its `:points` from the node to the centre
  and its `:label-at`."
  [centre items {:keys [gap reach lane-pad]}]
  (let [{cx :x cy :y cw :w ch :h} centre
        by-side (group-by :side items)
        placed  (into {}
                      (for [[side its] by-side
                            :let [lane  (+ (reduce max 0 (map (comp small-text-w :label) its)) (* 2 lane-pad))
                                  inner (+ cx (* side (+ (/ cw 2.0) reach lane)))
                                  col   (column (map :node its) inner cy gap side)
                                  k     (count its)]
                            [i [it n]] (map-indexed vector (map vector its col))
                            :let [py (if (= 1 k) cy
                                         (+ (- cy (/ ch 2.0) -6) (* i (/ (- ch 12) (double (dec k))))))]]
                        [it {:node n
                             :points [[(rnd inner) (:y n)]
                                      [(rnd (+ cx (* side (+ (/ cw 2.0) reach)))) (:y n)]
                                      [(rnd (+ cx (* side (/ cw 2.0)))) (rnd py)]]
                             :label-at [(rnd (- inner (* side lane-pad))) (- (:y n) 4)
                                        (if (neg? side) "start" "end")]}]))]
    (mapv #(merge % (placed %)) items)))

(defn ring
  "Place measured `nodes` evenly around a circle centred at (`cx`, `cy`), starting at
  `start` radians and going clockwise.

  The radius is computed: the larger of `min-r` and the radius that spaces the arc
  between neighbours at 1.15× the widest box.  Eight long names spread onto a wider ring
  instead of overlapping, and two short ones stay at `min-r`."
  [nodes cx cy min-r start]
  (let [n (count nodes)]
    (if (zero? n)
      []
      (let [widest (reduce max 0 (map :w nodes))
            r      (max min-r (/ (* n widest 1.15) (* 2 Math/PI)))
            step   (/ (* 2 Math/PI) n)]
        (map-indexed (fn [i node]
                       (let [a (+ start (* i step))]
                         (assoc node :x (rnd (+ cx (* r (Math/cos a)))) :y (rnd (+ cy (* r (Math/sin a))))
                                :angle a)))
                     nodes)))))

(defn arc
  "Place measured `nodes` on a short arc of radius `r` **centred on angle** `a` around
  (`cx`, `cy`).  An arc in one direction puts a neighbour's own neighbours out past it.

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
                         (assoc node :x (rnd (+ cx (* r (Math/cos t)))) :y (rnd (+ cy (* r (Math/sin t))))
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
                     [(rnd (+ (:x node) (* sign t dx))) (rnd (+ (:y node) (* sign t dy)))]))
            [x1 y1] (clip a 1)
            [x2 y2] (clip b -1)]
        {:x1 x1 :y1 y1 :x2 x2 :y2 y2}))))

(def note-cap
  "How many characters one line of a card row's note holds: a row's `label-cap` characters
  of label text, in the smaller face the note is set in."
  36)

(def note-lines
  "How many lines one card row's note wraps over before `wrap-text` cuts it.  A note names
  up to three things, a context, a source and a reading, so it takes more lines than a
  label."
  5)

(def ^:private card-pad
  "The clear space between a card's edge and the rows inside it."
  8)

(def ^:private row-gap
  "The space between two rows of a card."
  6)

(defn- row-height
  "The height of a card row of `n` text lines over `m` note lines.  The first text baseline
  is 18 px under the row's top, as in a one-line node, and each further text line is
  `line-h` lower.  The first note is 16 px under the last text line and each further note
  `small-line-h` lower.  The row ends 8 px under its last baseline."
  [n m]
  (+ 18 (* line-h (dec n)) (if (pos? m) (+ 16 (* small-line-h (dec m))) 0) 8))

(defn- text-w
  "The width a node or row label of `lines` needs: the longest at `w` px a character, and
  `pad` each side."
  [lines w]
  (+ (* w (reduce max 0 (map count lines))) (* 2 pad)))

(defn measure-card
  "Give a card its box and each of its rows a box inside it.  A card is a node whose header
  is its `:display` (else `:term`), wrapped as `measure` wraps a label.  A row's `:text`
  wraps at `label-cap` over `label-lines`, and each of its `:notes` at `note-cap` over
  `note-lines`.  `:more` is a note under the rows.  Every row is as wide as the card's
  widest line, and the card adds `card-pad` each side.  A row gets `:lines`, `:notes`,
  `:w`, `:h` and `:dy`, its top under the card's top.  The card gets `:lines`, `:w`, `:h`
  and, with a `:more`, `:more-lines` and `:more-at`, that line's baseline under its top."
  [card]
  (let [head   (wrap-text (or (:display card) (:term card)) label-cap label-lines)
        head-h (+ node-h (* line-h (dec (count head))))
        rows   (mapv (fn [r] (let [ls (wrap-text (:text r) label-cap label-lines)
                                   ns (into [] (mapcat #(wrap-text % note-cap note-lines)) (:notes r))]
                               (assoc r :lines ls :notes ns :h (row-height (count ls) (count ns)))))
                     (:rows card))
        more   (some-> (:more card) (wrap-text note-cap label-lines))
        inner  (reduce max (- (text-w head char-w) (* 2 card-pad))
                       (concat (when more [(text-w more small-char-w)])
                               (for [r rows] (max (text-w (:lines r) char-w) (text-w (:notes r) small-char-w)))))
        w      (even-up (+ inner (* 2 card-pad)))
        [rows y] (reduce (fn [[out y] r]
                           [(conj out (assoc r :dy y :w (- w (* 2 card-pad)))) (+ y (:h r) row-gap)])
                         [[] head-h] rows)
        y      (if (seq rows) (- y row-gap) head-h)]
    (cond-> (assoc card :lines head :rows rows :w w
                   :h (even-up (if more
                                 (+ y 16 (* small-line-h (dec (count more))) 8)
                                 (+ y card-pad))))
      more (assoc :more-lines more :more-at (+ y 16)))))

;; ---- what a finished picture holds ---------------------------------------

(defn- edge-points
  "An edge's points, tail first: its `:points`, or the two ends of a `trim` segment."
  [{:keys [points x1 y1 x2 y2]}]
  (or points [[x1 y1] [x2 y2]]))

(defn- label-anchor
  "Where an edge's label goes, `[x baseline anchor]`: its `:label-at`, else beside its
  middle segment (`label-beside`)."
  [e]
  (or (:label-at e)
      (let [pts (edge-points e)
            i   (quot (dec (count pts)) 2)]
        (label-beside pts [(pts i) (pts (inc i))] (:label e)))))

(defn- node-box [{:keys [x y w h]}]
  [(- x (/ w 2.0)) (- y (/ h 2.0)) (+ x (/ w 2.0)) (+ y (/ h 2.0))])

(defn- frame-label-box [{:keys [label-at lines]}]
  (let [[x y] label-at]
    [x y (+ x (reduce max 0 (map small-text-w lines))) (+ y (* small-line-h (count lines)))]))

(defn- overlap? [[a0 b0 a1 b1] [c0 d0 c1 d1]]
  (and (< a0 c1) (< c0 a1) (< b0 d1) (< d0 b1)))

(defn- near? [[px py] [x0 y0 x1 y1]]
  (and (<= (- x0 2) px (+ x1 2)) (<= (- y0 2) py (+ y1 2))))

(defn- bbox
  "The rectangle everything drawn fits inside — node boxes, frames, edge points and every
  label's own extent."
  [nodes edges frames]
  (let [rects (concat (map (fn [{:keys [x y w h]}] [x y (+ x w) (+ y h)]) frames)
                      (map node-box nodes)
                      (keep #(when (:label %) (text-box (label-anchor %) (:label %))) edges)
                      (map (fn [e] (let [ps (edge-points e)]
                                     [(reduce min (map first ps)) (reduce min (map second ps))
                                      (reduce max (map first ps)) (reduce max (map second ps))]))
                           edges))]
    (when (seq rects)
      [(reduce min (map #(% 0) rects)) (reduce min (map #(% 1) rects))
       (reduce max (map #(% 2) rects)) (reduce max (map #(% 3) rects))])))

(defn faults
  "The faults of the finished picture `scene`, one string each.  A fault is two boxes that
  overlap, an edge segment through a box it does not end at, a node label wider or taller
  than its box, or a frame label outside its frame.  A card row (`measure-card`) whose text
  is larger than the row, or which runs past its card, is a fault too.  A box is a node's,
  an edge label's or a frame label's, and a `:mark?` node has no label.  The vector is
  empty for a picture with none."
  [{:keys [nodes edges frames]}]
  (let [boxes (vec (concat
                    (for [n nodes] {:name (str "node " (or (:title n) (:term n))) :box (node-box n) :node? true})
                    (for [e edges :when (:label e)]
                      {:name (str "edge label " (str/join " " (text-lines (:label e))))
                       :box (text-box (label-anchor e) (:label e))})
                    (for [f frames] {:name (str "frame label " (:label f)) :box (frame-label-box f)})))
        n     (count boxes)]
    (vec (concat
          (for [i (range n), j (range (inc i) n)
                :let [a (boxes i), b (boxes j)]
                :when (overlap? (:box a) (:box b))]
            (str (:name a) " overlaps " (:name b)))
          (for [e edges
                :let [pts (edge-points e)]
                b boxes
                :when (and (not (and (:node? b) (or (near? (first pts) (:box b)) (near? (peek pts) (:box b)))))
                           (some (fn [[p q]] (crosses? p q (:box b))) (partition 2 1 pts)))]
            (str "edge " (or (:from e) (first pts)) " → " (or (:to e) (peek pts)) " crosses " (:name b)))
          (for [nd nodes
                :when (not (:mark? nd))
                :let [ls (or (:lines nd) [""])]
                :when (or (> (+ (* char-w (reduce max 0 (map count ls))) (* 2 pad)) (+ (:w nd) 1))
                          (> (+ node-h (* line-h (dec (count ls)))) (:h nd)))]
            (str "node " (or (:title nd) (:term nd)) "'s label is larger than its box"))
          (for [f frames
                :let [[x0 y0 x1 y1] (frame-label-box f)]
                :when (not (and (<= (:x f) x0) (<= x1 (+ (:x f) (:w f)))
                                (<= (:y f) y0) (<= y1 (+ (:y f) (:h f)))))]
            (str "frame label " (:label f) " is outside its frame"))
          (for [nd nodes, r (:rows nd)
                :when (or (> (text-w (:lines r) char-w) (+ (:w r) 1))
                          (> (text-w (:notes r) small-char-w) (+ (:w r) 1))
                          (> (row-height (count (:lines r)) (count (:notes r))) (:h r))
                          (> (+ (:dy r) (:h r)) (:h nd)))]
            (str "row " (or (:title r) (first (:lines r))) " of node " (or (:title nd) (:term nd))
                 " is larger than its box"))))))

(defn clear-labels
  "Move each edge label of `scene`, in edge order, to a place 3 px clear of every edge
  segment, every node and every label placed before it.  A label already clear stays at
  its `label-anchor`.  Otherwise it goes to the first clear place 6, 12, 24 or 48 px right
  of, left of, above or below the middle of a segment of its edge, tail first.  A label
  with no clear place stays where it was."
  [{:keys [nodes edges] :as scene}]
  (let [segs  (mapcat #(partition 2 1 (edge-points %)) edges)
        clear (fn [boxes at s]
                (let [[x0 y0 x1 y1] (text-box at s)
                      b             [(- x0 3) (- y0 3) (+ x1 3) (+ y1 3)]]
                  (and (not-any? (fn [[p q]] (crosses? p q b)) segs)
                       (not-any? #(overlap? b %) boxes))))
        place (fn [boxes {:keys [label] :as e}]
                (let [at (label-anchor e)]
                  (if (clear boxes at label)
                    at
                    (or (first (for [[[ax ay] [bx by]] (partition 2 1 (edge-points e))
                                     d [6 12 24 48]
                                     c (beside (rnd (/ (+ ax bx) 2.0)) (rnd (/ (+ ay by) 2.0)) d
                                               (count (text-lines label)))
                                     :when (clear boxes c label)]
                                 c))
                        at))))]
    (assoc scene :edges
           (:out (reduce (fn [{:keys [boxes out]} {:keys [label] :as e}]
                           (if label
                             (let [at (place boxes e)]
                               {:boxes (conj boxes (text-box at label))
                                :out   (conj out (assoc e :label-at at))})
                             {:boxes boxes :out (conj out e)}))
                         {:boxes (mapv node-box nodes) :out []}
                         edges)))))

;; ---- a constraint network and a timeline ---------------------------------

(defn- crossing
  "The point where the segments `[p q]` and `[r s]` cross, or nil when they do not."
  [[[px py] [qx qy]] [[rx ry] [sx sy]]]
  (let [ux (- qx px) uy (- qy py) vx (- sx rx) vy (- sy ry)
        d  (- (* ux vy) (* uy vx))]
    (when-not (zero? d)
      (let [wx (- rx px) wy (- ry py)
            t  (/ (- (* wx vy) (* wy vx)) d)
            u  (/ (- (* wx uy) (* wy ux)) d)]
        (when (and (< 0 t 1) (< 0 u 1))
          [(+ px (* t ux)) (+ py (* t uy))])))))

(defn- grow
  "The box `[x0 y0 x1 y1]` widened by `m` px on every side."
  [[x0 y0 x1 y1] m]
  [(- x0 m) (- y0 m) (+ x1 m) (+ y1 m)])

(defn- label-clear
  "Where the label `s` of the straight edge `[p q]` goes, `[x baseline anchor]`, or nil.
  A candidate is 6, 12 or 24 px beside a point 0.5, 0.4, 0.6, 0.3 or 0.7 of the way along.
  The first wins whose box stands 6 px clear of `boxes` and 20 px clear of a crossing with
  one of `segs`, and is 4 px nearer its own edge than any other of `segs`."
  [[[ax ay] [bx by] :as own] s boxes segs]
  (let [others  (remove #{own} segs)
        crosses (keep #(crossing own %) others)]
    (first (for [t [0.5 0.4 0.6 0.3 0.7]
                 d [6 12 24]
                 c (beside (rnd (+ ax (* t (- bx ax)))) (rnd (+ ay (* t (- by ay)))) d
                           (count (text-lines s)))
                 :let [b (text-box c s)]
                 :when (and (not-any? #(overlap? (grow b 6) %) boxes)
                            (not-any? #(near? % (grow b 18)) crosses)
                            (not (crosses? [ax ay] [bx by] b))
                            (let [wide (grow b (+ d 4))]
                              (not-any? (fn [[p q]] (crosses? p q wide)) others)))]
             c))))

(defn- longest-label-path
  "`nodes` in the order a path takes them: the first of `nodes`, then each time the node not
  yet taken whose edge to the last one taken carries the widest label, the first of `nodes`
  on a tie.  On a ring in that order a wide label runs along a side, where no edge crosses."
  [nodes edges]
  (let [width (into {} (for [e edges]
                         [#{(:from e) (:to e)} (reduce + (map small-text-w (text-lines (:label e))))]))]
    (loop [path (vec (take 1 nodes)) left (vec (rest nodes))]
      (if (empty? left)
        path
        (let [at   (:term (peek path))
              pick (reduce (fn [best nd] (if (> (width #{at (:term nd)} 0) (width #{at (:term best)} 0)) nd best))
                           left)]
          (recur (conj path pick) (filterv #(not= % pick) left)))))))

(defn ring-graph
  "Place one connected network: the measured `nodes` evenly on an ellipse round the origin
  in `longest-label-path` order, and each of `edges` (`:from`, `:to`, `:label`) straight,
  its label where `label-clear` puts it.  The ellipse starts where neighbouring boxes stand
  the widest label and 40 px apart across, and the tallest label and 40 px apart down.  Its
  radii grow by a quarter, at most eleven times, the across one only up to `max-w` px wide
  and the down one to `max-w` px tall, and a size putting two boxes within 6 px is skipped.
  Answers `{:nodes :edges}`, each edge with `:points` and `:label-at`, or nil when no size
  gives every label a place."
  [nodes edges max-w]
  (let [n      (count nodes)
        side   (* 2 (Math/sin (/ Math/PI (max n 2))))
        widest (reduce max 0 (map :w nodes))
        label  (reduce max 0 (for [e edges l (text-lines (:label e))] (small-text-w l)))
        rows   (reduce max 1 (for [e edges] (count (text-lines (:label e)))))
        rx0    (if (< n 2) 0.0 (/ (+ widest label 40) side))
        rx-max (/ (- max-w widest) 2.0)
        ry0    (min rx0 (/ (+ (reduce max 0 (map :h nodes)) (* 2 small-line-h rows) 40) side))
        start  (- (- (/ Math/PI 2)) (/ Math/PI (max n 1)))]
    (some (fn [[rx ry]]
            (let [placed (mapv (fn [nd] (let [a (+ start (* (:i nd) (/ (* 2 Math/PI) (max n 1))))]
                                          (assoc (dissoc nd :i) :x (rnd (* rx (Math/cos a))) :y (rnd (* ry (Math/sin a))))))
                               (map-indexed #(assoc %2 :i %1) (longest-label-path nodes edges)))
                  close? (some (fn [[i a]] (some #(overlap? (grow (node-box a) 6) (node-box %)) (subvec placed (inc i))))
                               (map-indexed vector placed))
                  at     (into {} (map (juxt :term identity)) placed)
                  lines  (mapv (fn [e] (let [{:keys [x1 y1 x2 y2]} (trim (at (:from e)) (at (:to e)))]
                                         (assoc e :points [[x1 y1] [x2 y2]])))
                               edges)
                  segs   (mapv :points lines)
                  laid   (when-not close?
                           (reduce (fn [acc e]
                                     (if-let [c (label-clear (:points e) (:label e) (:boxes acc) segs)]
                                       (-> acc
                                           (update :edges conj (assoc e :label-at c))
                                           (update :boxes conj (text-box c (:label e))))
                                       (reduced nil)))
                                   {:edges [] :boxes (mapv node-box placed)} lines))]
              (when laid {:nodes placed :edges (:edges laid)})))
          (when (or (< n 2) (pos? rx-max))
            (take-while (fn [[_ ry]] (<= (* 2 ry) max-w))
                        (take 12 (iterate (fn [[rx ry]] [(min rx-max (* 1.25 rx)) (* 1.25 ry)])
                                          [(min rx0 rx-max) ry0])))))))

(defn pack
  "Place `parts`, each `{:nodes :edges}` laid out on its own with every edge's `:points`,
  left to right in rows at most `width` wide, `gap` apart, each part's top on its row's top.
  Answers one `{:nodes :edges}`."
  [parts width gap]
  (let [shift (fn [{:keys [nodes edges]} dx dy]
                (let [mv (fn [[x y]] [(+ x dx) (+ y dy)])]
                  {:nodes (mapv #(-> % (update :x + dx) (update :y + dy)) nodes)
                   :edges (mapv (fn [e] (cond-> (update e :points #(mapv mv %))
                                          (:label-at e) (update :label-at (fn [[x y a]] (conj (mv [x y]) a)))))
                                edges)}))]
    (:out (reduce (fn [{:keys [x y row-h out]} p]
                    (let [[x0 y0 x1 y1] (bbox (:nodes p) (:edges p) nil)
                          w     (rnd (- x1 x0))
                          wrap? (and (pos? x) (> (+ x w) width))
                          [x y row-h] (if wrap? [0 (+ y row-h gap) 0] [x y row-h])
                          q     (shift p (rnd (- x x0)) (rnd (- y y0)))]
                      {:x (+ x w gap) :y y :row-h (max row-h (rnd (- y1 y0)))
                       :out (-> out (update :nodes into (:nodes q)) (update :edges into (:edges q)))}))
                  {:x 0 :y 0 :row-h 0 :out {:nodes [] :edges []}}
                  parts))))

(defn framed
  "`scene` (`{:nodes :edges}`) inside one frame of CSS `class`, 12 px clear of everything
  the scene draws, with `lines` as the frame's label at its top.  The frame is centred on
  the scene and as wide as the wider of the scene and the label."
  [{:keys [nodes edges] :as scene} lines class]
  (let [gap 12
        [x0 y0 x1 y1] (bbox nodes edges nil)
        w   (max (+ (- x1 x0) (* 2 gap)) (+ (reduce max 0 (map small-text-w lines)) (* 2 gap)))
        fx  (rnd (- (/ (+ x0 x1) 2.0) (/ w 2.0)))
        ly  (rnd (- y0 gap (* small-line-h (count lines))))
        fy  (- ly gap)]
    (assoc scene :frames [{:x fx :y fy :w (rnd w) :h (rnd (- (+ y1 gap) fy)) :class class
                           :label (str/join " " lines) :lines lines :label-at [(+ fx gap) ly]}])))

(def ^:private bar-h
  "The height of a timeline's bar or tick."
  14)

(def ^:private tick-w
  "The width of a timeline's tick, an instant's mark."
  6)

(defn timeline
  "Place a timeline.  Each of `bands`, `{:lanes [lane …] :spans [span …]}`, sits under the
  one before it, `band-gap` apart, its lanes `lane-gap` apart.  A lane `{:node :from :to
  :mark}` sets the measured `node` `name-gap` px left of x = 0, and its mark node as a bar
  from rank `:from` to rank `:to`, or a tick where the two are equal.  Rank r is at r × the
  band's unit: `unit`, widened to the widest span label and 16 px.  Under the lanes runs an
  axis marking each rank, and under the axis each span `{:from :to :label}` joins its two
  ranks.  Answers `{:nodes :edges}`."
  [bands {:keys [unit name-gap band-gap lane-gap]}]
  (dissoc
   (reduce
    (fn [{:keys [y] :as acc} {:keys [lanes spans]}]
      (let [u        (max unit (+ 16 (reduce max 0 (map (comp small-text-w :label) spans))))
            xr       #(* % u)
            [ns y']  (reduce (fn [[out y] {:keys [node from to mark]}]
                               (let [h  (max (:h node) bar-h)
                                     cy (rnd (+ y (/ h 2.0)))
                                     m  (if (= from to)
                                          (assoc mark :x (xr from) :w tick-w)
                                          (assoc mark :x (rnd (/ (+ (xr from) (xr to)) 2.0))
                                                 :w (- (xr to) (xr from))))]
                                 [(conj out
                                        (assoc node :x (rnd (- (+ name-gap (/ (:w node) 2.0)))) :y cy)
                                        (assoc m :y cy :h bar-h :mark? true))
                                  (+ y h lane-gap)]))
                             [[] y] lanes)
            last-r   (reduce max 0 (mapcat (juxt :from :to) lanes))
            ay       (+ y' (- lane-gap) 10)
            sy       (+ ay 26)]
        (-> acc
            (update :nodes into ns)
            (update :edges conj {:points [[-8 ay] [(+ (xr last-r) 20) ay]] :kind "g-axis"})
            (update :edges into (for [r (range (inc last-r))]
                                  {:points [[(xr r) (- ay 4)] [(xr r) (+ ay 4)]] :kind "g-axis"
                                   :undirected? true}))
            (update :edges into (for [{:keys [from to label]} spans
                                      :let [pts [[(inc (xr from)) sy] [(dec (xr to)) sy]]]]
                                  {:points pts :label label :kind "g-span" :back? true
                                   :label-at (label-beside pts pts label)}))
            (assoc :y (+ (if (seq spans) sy ay) 6 band-gap)))))
    {:nodes [] :edges [] :y 0}
    bands)
   :y))

;; ---- emitters -----------------------------------------------------------

(def arrow-tones
  "The arrowhead markers, one per stroke colour, keyed by the `:tone` an edge carries:
  nil for the muted stroke, `:sub` for a subsumption edge, `:disjoint` for a `disjoint`
  edge.  A marker paints its own fill, so each stroke colour needs its own marker."
  {nil "g-arrow" :sub "g-arrow-sub" :disjoint "g-arrow-disjoint"})

(defn- arrow-defs
  "The arrowhead markers.  Direction is carried by the head and by the edge label, never
  by colour alone; the colour repeats the edge's stroke."
  []
  (into [:defs]
        (for [[tone id] (sort-by val arrow-tones)]
          [:marker {:id id :viewBox "0 0 10 10" :refX "9" :refY "5"
                    :markerWidth "5" :markerHeight "5" :orient "auto-start-reverse"}
           [:path {:d "M 0 0 L 10 5 L 0 10 z"
                   :class (str "g-arrowhead" (when tone (str " g-" (name tone))))}]])))

(def ^:private node-corner
  "The corner radius of a node box.  A box rather than a capsule: a label is set flush
  left-to-right inside a rectangle, where a fully-rounded end takes the width a long term
  needs and makes two adjacent nodes read as one shape."
  3)

(defn- node-el
  "One placed node: a box in the term's role colour, its label one line or several, and
  **linked to the term's page** — the graph is navigation, not decoration.  The colour is
  a class, so it resolves to the same CSS custom property the links beside it use.  A
  `:mark?` node, a timeline's bar or tick, is the box alone."
  [{:keys [x y w h lines class href title mark?]}]
  (let [n (count lines)
        g [:g {:class (str "g-node " class)}
           [:rect {:x (rnd (- x (/ w 2.0))) :y (rnd (- y (/ h 2.0)))
                   :width w :height h :rx node-corner :class "g-box"}]
           (cond
             mark?    nil
             (<= n 1) [:text {:x x :y (+ y 4) :text-anchor "middle" :class "g-label"} (first lines)]
             :else    (into [:text {:x x :y (- (+ y 4) (* (quot line-h 2) (dec n))) :text-anchor "middle"
                                    :class "g-label"}]
                            (map-indexed (fn [i l] [:tspan {:x x :dy (if (zero? i) 0 line-h)} l]) lines)))
           [:title (str title)]]]
    (if href [:a {:href href} g] g)))

(defn- edge-el
  "One edge: a line, or a polyline where it bends, with an arrowhead, and — when it
  carries one — the relation name at `label-anchor`.  `:kind` becomes a class, which is
  how a `genlCx` edge is told from a `genl` edge (a dash) and a `disjoint` edge from
  another relation (a stroke colour).  `:back?` puts a head at the tail too, for a pair
  related both ways, and `:undirected?` draws no head.  `:tone` picks the arrowhead marker
  (`arrow-tones`).  A label that is a vector is drawn one line per string."
  [{:keys [label kind back? undirected? tone] :as e}]
  (let [head  (str "url(#" (arrow-tones tone "g-arrow") ")")
        pts   (edge-points e)
        attrs (cond-> {} (not undirected?) (assoc :marker-end head) back? (assoc :marker-start head))
        [lx ly anchor] (label-anchor e)
        ls    (text-lines label)]
    [:g {:class (str "g-edge " (or kind ""))}
     (if (= 2 (count pts))
       (let [[[x1 y1] [x2 y2]] pts] [:line (assoc attrs :x1 x1 :y1 y1 :x2 x2 :y2 y2)])
       [:polyline (assoc attrs :points (str/join " " (map (fn [[x y]] (str x "," y)) pts)))])
     (when label
       (into [:text {:x lx :y ly :text-anchor anchor :class "g-edge-label"}]
             (if (= 1 (count ls))
               ls
               (map-indexed (fn [i l] [:tspan {:x lx :dy (if (zero? i) 0 small-line-h)} l]) ls))))]))

(defn- frame-el
  "One frame: the box drawn behind the nodes it encloses, `g-frame` and its own `class`."
  [{:keys [x y w h class]}]
  [:rect {:x x :y y :width w :height h :rx node-corner :class (str/trim (str "g-frame " class))}])

(defn- frame-label-el
  "A frame's label, its lines set at `label-at` inside the frame, where no edge passes."
  [{:keys [label-at lines class]}]
  (let [[x y] label-at
        a     {:x x :y (+ y 11) :class (str/trim (str "g-frame-label " class))}]
    (if (= 1 (count lines))
      [:text a (first lines)]
      (into [:text a]
            (map-indexed (fn [i l] [:tspan {:x x :dy (if (zero? i) 0 small-line-h)} l]) lines)))))

(defn- lines-el
  "`lines` as one `<text>` of class `cls`, the first baseline at (`x`, `y`) and each further
  line `step` lower, set from `anchor`."
  [cls x y lines step anchor]
  (if (= 1 (count lines))
    [:text {:x x :y y :text-anchor anchor :class cls} (first lines)]
    (into [:text {:x x :y y :text-anchor anchor :class cls}]
          (map-indexed (fn [i l] [:tspan {:x x :dy (if (zero? i) 0 step)} l]) lines))))

(defn- card-el
  "One placed card (`measure-card`): its box in the card's class and its header centred at
  the top, linked to the card's `:href`.  Each row is a box of its own in the row's class,
  its text and notes set from the left and linked to the row's `:href`, and the `:more`
  line is under the rows."
  [{:keys [x y w h lines class href title rows more-lines more-at]}]
  (let [x0   (rnd (- x (/ w 2.0)))
        y0   (rnd (- y (/ h 2.0)))
        head [:g (lines-el "g-label" x (+ y0 18) lines line-h "middle") [:title (str title)]]]
    [:g {:class (str "g-node g-card " class)}
     [:rect {:x x0 :y y0 :width w :height h :rx node-corner :class "g-box"}]
     (if href [:a {:href href} head] head)
     (for [{:keys [dy] rw :w rh :h rl :lines :as r} rows
           :let [rx (+ x0 card-pad), ry (+ y0 dy)
                 g  [:g {:class (str "g-row " (:class r))}
                     [:rect {:x rx :y ry :width rw :height rh :rx node-corner :class "g-row-box"}]
                     (lines-el "g-label" (+ rx pad) (+ ry 18) rl line-h "start")
                     (when (seq (:notes r))
                       (lines-el "g-row-note" (+ rx pad) (+ ry 18 (* line-h (dec (count rl))) 16)
                                 (:notes r) small-line-h "start"))
                     [:title (str (:title r))]]]]
       (if (:href r) [:a {:href (:href r)} g] g))
     (when more-lines
       (lines-el "g-row-note" (+ x0 card-pad pad) (+ y0 more-at) more-lines small-line-h "start"))]))

(def ^:private margin 14)

(defn scene
  "The whole picture as one `<svg>`, or **nil** when there is nothing to draw — a caller
  renders the nil and gets no empty frame.

  `aria-label` is what a screen reader is told the image shows; it is `role=\"img\"`
  because the prose above it, not the picture, is the accessible answer.  The `viewBox`
  is the crop.  An intrinsic pixel `width`/`height` (one user unit to one CSS px) draws
  the graph at its natural size, so a wide one scrolls inside `.kb-graph-fig` rather than
  shrinking on a narrow column."
  [{:keys [nodes edges frames aria-label]}]
  (when (seq nodes)
    (let [[x0 y0 x1 y1] (bbox nodes edges frames)
          w (rnd (+ (- x1 x0) (* 2 margin)))
          h (rnd (+ (- y1 y0) (* 2 margin)))]
      [:svg {:class "kb-graph" :role "img" :aria-label (str aria-label)
             :xmlns "http://www.w3.org/2000/svg"
             :viewBox (str/join " " (map rnd [(- x0 margin) (- y0 margin) w h]))
             :width w :height h :preserveAspectRatio "xMidYMid meet"}
       (arrow-defs)
       ;; frames behind everything, so an edge crossing one stays visible
       (map frame-el frames)
       ;; edges first, so a line is never drawn over the label it connects
       (map edge-el edges)
       (map frame-label-el (filter :label-at frames))
       (map #(if (contains? % :rows) (card-el %) (node-el %)) nodes)])))
