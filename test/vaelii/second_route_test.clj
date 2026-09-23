;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.second-route-test
  "A reader that still reaches over a second route holds a forward firing, whatever took
  the route the firing named, and in every arrival order.

  A firing names one path per reachability it rests on — the `genl` path a subsumed match
  climbed, the `genlCx` path its placement is seen over, the path a `transitiveInArg` claim
  moved along — and a second route is paid for with a re-derivation when the named one
  goes (docs/nmtms.md, \"Where the layer stops\").  Each case below builds two routes
  between the same ends, knocks out an edge of the named one, and compares every reader's
  answer with a KB that never held that edge.

  Five lattices — a subsumed match, a claim preserved along `genl` and along a fact
  relation, the `genlCx` path a placement is seen over, and two routes that tie on
  generality — and four ways to knock an edge out:

    retract    the record goes; the sweep's re-join brings the firing back
    network    a monotonic negation in the edge's own context defeats it everywhere; the
               edge keeps its record and the settle's re-join (`settle/departed-seeds`)
               brings the firing back
    scoped     a monotonic negation in a context below the edge defeats it at that
               vantage and below; the network keeps the edge IN, and the settle
               re-derives the firing from each such reader's view
               (`settle/lost-firing-seeds`, `chain/*witness-view*`)
    except     an `(except (sentexHandle H))` hides the edge from its context and below,
               re-derived the same way

  A network knock is compared with a KB that never held the edge at every reader; a scoped
  or excepting one only at the readers at and below its context, and with the whole KB
  above it.

  The orders are every permutation of the named route, the other route, the knock and the
  claim or fact the rule fires on, after the contexts, declarations and rule; a knock that
  names the edge's handle follows the edge.  The whole roster is `^:slow`; four of its
  orders — the knock first and last, each with either route first — run at `:default`."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(defn- permutations [coll]
  (if (empty? coll)
    [[]]
    (mapcat (fn [x] (map #(vec (cons x %)) (permutations (remove #{x} coll)))) coll)))

(defn- terms
  "A fresh temporary for each symbol, keyed by the symbol."
  [syms]
  (zipmap syms (map #(tu/fresh-term (tu/term-role %) %) syms)))

(defn- sibling-contexts
  "Two sibling contexts under CxUniverse, neither of which sees the other, and a third
  below both, as `[sentence context]` pairs."
  [cx-a cx-b cx-d]
  [[(list 'genlCx cx-a 'CxUniverse) 'CxUniverse] [(list 'genlCx cx-b 'CxUniverse) 'CxUniverse]
   [(list 'genlCx cx-d cx-a) 'CxUniverse] [(list 'genlCx cx-d cx-b) 'CxUniverse]])

(defn- lattice
  "One witness kind's two-route KB as data, over fresh terms: `:base` (contexts,
  declarations, the rule), `:named` (the route the firing names, as `[sentence context]`
  pairs), `:other`, `:claim`, the `:knock`ed edge (a member of `:named`), the `:goal` and
  the `:readers`, most general first."
  [kind]
  (case kind
    :subsume
    (let [{:syms [dog mammal animal Fido alive_t CxA CxB]}
          (terms '[dog mammal animal Fido alive_t CxA CxB])]
      {:base    [[(list 'genlCx CxA 'CxUniverse) 'CxUniverse]
                 [(list 'genlCx CxB CxA) 'CxUniverse]
                 [(list 'genl dog 'thing) 'CxUniverse] [(list 'genl mammal 'thing) 'CxUniverse]
                 [(list 'genl animal 'thing) 'CxUniverse]
                 [(list 'set/forwardRule (list 'implies (list animal '?x) (list alive_t '?x)))
                  'CxUniverse]]
       :named   [[(list 'genl dog mammal) 'CxUniverse] [(list 'genl mammal animal) 'CxUniverse]]
       :other   [[(list 'genl dog animal) CxA]]
       :claim   [[(list dog Fido) 'CxUniverse]]
       :knock   [(list 'genl dog mammal) 'CxUniverse]
       :at      CxA
       :goal    (list alive_t Fido)
       :readers ['CxUniverse CxA CxB]
       :below   #{CxA CxB}})

    :preserve
    (let [{:syms [dog_t mid_t chi_t cat_t largerThan noted CxA CxB]}
          (terms '[dog_t mid_t chi_t cat_t largerThan noted CxA CxB])]
      {:base    [[(list 'genlCx CxA 'CxUniverse) 'CxUniverse]
                 [(list 'genlCx CxB CxA) 'CxUniverse]
                 [(list 'transitiveInArg largerThan 1 'genl) 'CxUniverse]
                 [(list 'set/forwardRule (list 'implies (list largerThan '?x '?y) (list noted '?x '?y)))
                  'CxUniverse]]
       :named   [[(list 'genl mid_t dog_t) 'CxUniverse] [(list 'genl chi_t mid_t) 'CxUniverse]]
       :other   [[(list 'genl chi_t dog_t) CxA]]
       :claim   [[(list largerThan dog_t cat_t) 'CxUniverse]]
       :knock   [(list 'genl chi_t mid_t) 'CxUniverse]
       :at      CxA
       :goal    (list noted chi_t cat_t)
       :readers ['CxUniverse CxA CxB]
       :below   #{CxA CxB}})

    ;; Both routes in CxA, so they tie on generality and the shorter one is named; the
    ;; knock lands in CxB below them (docs/nmtms.md, "Where the layer stops").
    :tie
    (let [{:syms [dog_t mid_t chi_t cat_t largerThan noted CxA CxB]}
          (terms '[dog_t mid_t chi_t cat_t largerThan noted CxA CxB])]
      {:base    [[(list 'genlCx CxA 'CxUniverse) 'CxUniverse]
                 [(list 'genlCx CxB CxA) 'CxUniverse]
                 [(list 'transitiveInArg largerThan 1 'genl) 'CxUniverse]
                 [(list 'set/forwardRule (list 'implies (list largerThan '?x '?y) (list noted '?x '?y)))
                  'CxUniverse]]
       :named   [[(list 'genl chi_t dog_t) CxA]]
       :other   [[(list 'genl chi_t mid_t) CxA] [(list 'genl mid_t dog_t) CxA]]
       :claim   [[(list largerThan dog_t cat_t) 'CxUniverse]]
       :knock   [(list 'genl chi_t dog_t) CxA]
       :at      CxB
       :goal    (list noted chi_t cat_t)
       :readers ['CxUniverse CxA CxB]
       :below   #{CxB}})

    :preserve-fact
    (let [{:syms [partOf rel noted A B C Z CxA CxB]}
          (terms '[partOf rel noted A B C Z CxA CxB])]
      {:base    [[(list 'genlCx CxA 'CxUniverse) 'CxUniverse]
                 [(list 'genlCx CxB CxA) 'CxUniverse]
                 [(list 'transitive partOf) 'CxUniverse]
                 [(list 'transitiveInArg rel 1 partOf) 'CxUniverse]
                 [(list 'set/forwardRule (list 'implies (list rel '?x '?y) (list noted '?x '?y)))
                  'CxUniverse]]
       :named   [[(list partOf B A) 'CxUniverse] [(list partOf C B) 'CxUniverse]]
       :other   [[(list partOf C A) CxA]]
       :claim   [[(list rel A Z) 'CxUniverse]]
       :knock   [(list partOf C B) 'CxUniverse]
       :at      CxA
       :goal    (list noted C Z)
       :readers ['CxUniverse CxA CxB]
       :below   #{CxA CxB}})

    ;; Sibling routes: the named route is stated in CxA, the other in CxB, and neither
    ;; context sees the other.  Each route places the conclusion in its own context, CxD
    ;; below both reads it over either, and the knock lands in CxD.
    :sibling
    (let [{:syms [low_t mid_t high_t val_t aRel noted CxA CxB CxD]}
          (terms '[low_t mid_t high_t val_t aRel noted CxA CxB CxD])]
      {:base    (into (sibling-contexts CxA CxB CxD)
                      [[(list 'transitiveInArg aRel 1 'genl) 'CxUniverse]
                       [(list 'set/forwardRule (list 'implies (list aRel '?x '?y) (list noted '?x '?y)))
                        'CxUniverse]])
       :named   [[(list 'genl low_t mid_t) CxA] [(list 'genl mid_t high_t) CxA]]
       :other   [[(list 'genl low_t high_t) CxB]]
       :claim   [[(list aRel high_t val_t) 'CxUniverse]]
       :knock   [(list 'genl low_t mid_t) CxA]
       :at      CxD
       :goal    (list noted low_t val_t)
       :readers ['CxUniverse CxA CxB CxD]
       :below   #{CxD}})

    :sibling-fact
    (let [{:syms [partOf rel noted A B C Z CxA CxB CxD]}
          (terms '[partOf rel noted A B C Z CxA CxB CxD])]
      {:base    (into (sibling-contexts CxA CxB CxD)
                      [[(list 'transitive partOf) 'CxUniverse]
                       [(list 'transitiveInArg rel 1 partOf) 'CxUniverse]
                       [(list 'set/forwardRule (list 'implies (list rel '?x '?y) (list noted '?x '?y)))
                        'CxUniverse]])
       :named   [[(list partOf C B) CxA] [(list partOf B A) CxA]]
       :other   [[(list partOf C A) CxB]]
       :claim   [[(list rel A Z) 'CxUniverse]]
       :knock   [(list partOf C B) CxA]
       :at      CxD
       :goal    (list noted C Z)
       :readers ['CxUniverse CxA CxB CxD]
       :below   #{CxD}})

    :sibling-subsume
    (let [{:syms [dog mammal animal Fido alive_t CxA CxB CxD]}
          (terms '[dog mammal animal Fido alive_t CxA CxB CxD])]
      {:base    (into (sibling-contexts CxA CxB CxD)
                      [[(list 'genl dog 'thing) 'CxUniverse] [(list 'genl mammal 'thing) 'CxUniverse]
                       [(list 'genl animal 'thing) 'CxUniverse]
                       [(list 'set/forwardRule (list 'implies (list animal '?x) (list alive_t '?x)))
                        'CxUniverse]])
       :named   [[(list 'genl dog mammal) CxA] [(list 'genl mammal animal) CxA]]
       :other   [[(list 'genl dog animal) CxB]]
       :claim   [[(list dog Fido) 'CxUniverse]]
       :knock   [(list 'genl dog mammal) CxA]
       :at      CxD
       :goal    (list alive_t Fido)
       :readers ['CxUniverse CxA CxB CxD]
       :below   #{CxD}})

    ;; The placement path: the fact sits in CxP, which sees the rule's context directly
    ;; and through CxM.  The direct edge is the shorter path and the one named.
    :sight
    (let [{:syms [cat_t pet_t Tom CxM CxP]} (terms '[cat_t pet_t Tom CxM CxP])]
      {:base    [[(list 'genlCx CxM 'CxUniverse) 'CxUniverse]
                 [(list 'genl cat_t 'thing) 'CxUniverse]
                 [(list 'set/forwardRule (list 'implies (list cat_t '?x) (list pet_t '?x)))
                  'CxUniverse]]
       :named   [[(list 'genlCx CxP 'CxUniverse) 'CxUniverse]]
       :other   [[(list 'genlCx CxP CxM) 'CxUniverse]]
       :claim   [[(list cat_t Tom) CxP]]
       :knock   [(list 'genlCx CxP 'CxUniverse) 'CxUniverse]
       :at      CxP
       :goal    (list pet_t Tom)
       :readers ['CxUniverse CxM CxP]
       :below   #{CxP}})))

(defn- answers [kb {:keys [goal readers]}]
  (mapv #(v/ask? kb goal %) readers))

(defn- knock! [kb how {[s c] :knock at :at}]
  (case how
    :retract (v/retract! kb (v/handle-of kb s c))
    :network (v/assert kb (list 'not s) c {:strength :monotonic})
    :scoped  (v/assert kb (list 'not s) at {:strength :monotonic})
    :except  (v/assert kb (list 'except (list 'sentexHandle (v/handle-of kb s c))) at)))

(defn- run-order
  "Build `kind`'s lattice with its four parts arriving in `order`, knocking the named
  edge out `how`, and return `[answers reference]`.  The reference reads, at each reader
  the knock reaches, the same lattice built without the knocked edge, and at each reader
  it does not, the lattice built whole.  Each build gets its own cleared KB, as an order
  sweep does (`except_recheck_test`), so none reads another's content."
  [kind how order]
  (let [whole (fn [drop?]
                (tu/with-cleared-kb [kb tu/isolated-fresh]
                  (let [r (lattice kind)]
                    (doseq [[s c] (concat (:base r) (:other r) (:claim r)
                                          (cond->> (:named r)
                                            drop? (remove #(= (first %) (first (:knock r))))))]
                      (v/assert kb s c))
                    (answers kb r))))
        l     (lattice kind)
        reach (if (#{:retract :network} how)
                (vec (repeat (count (:readers l)) true))
                (mapv #(contains? (:below l) %) (:readers l)))]
    [(tu/with-cleared-kb [kb tu/isolated-fresh]
       (let [l (lattice kind)]
         (doseq [[s c] (:base l)] (v/assert kb s c))
         (doseq [part order]
           (if (= :knock part)
             (knock! kb how l)
             (doseq [[s c] (get l part)] (v/assert kb s c))))
         (answers kb l)))
     (mapv (fn [knocked? without with] (if knocked? without with))
           reach (whole true) (whole false))]))

(defn- orders
  "The arrival orders `how` admits: a knock that names the edge's handle follows it."
  [how]
  (cond->> (permutations [:named :other :knock :claim])
    (#{:retract :except} how) (filter #(< (.indexOf ^java.util.List % :named) (.indexOf ^java.util.List % :knock)))))

(def ^:private sampled
  "The knock first and last, each with either route first."
  [[:knock :named :other :claim] [:knock :other :named :claim]
   [:named :other :claim :knock] [:other :named :claim :knock]])

(def ^:private kinds
  [:subsume :preserve :preserve-fact :sight :tie :sibling :sibling-fact :sibling-subsume])

(defn- agree-in [hows order-fn]
  (doseq [kind kinds, how hows, order (order-fn how)]
    (testing (str kind " " how " " order)
      (let [[built reference] (run-order kind how order)]
        (is (= reference built))))))

(deftest a-second-route-carries-the-firing-in-sampled-orders
  (agree-in [:network :scoped] (constantly sampled))
  (agree-in [:retract :except] (constantly (remove #(= :knock (first %)) sampled))))

(deftest ^:slow a-second-route-carries-the-firing-in-every-order
  (agree-in [:network :retract :scoped :except] orders))

(deftest the-reference-reads-the-second-route
  ;; The comparison above is only a claim about the second route if the reference holds the
  ;; conclusion where that route is visible; this pins the answers it is compared with.
  (doseq [kind kinds]
    (testing (str kind)
      (let [[_ reference] (run-order kind :network [:named :other :claim :knock])]
        (is (= (case kind
                 :sight                                    [false false true]
                 :tie                                      [false true true]
                 (:sibling :sibling-fact :sibling-subsume) [false false true true]
                 [false true true])
               reference))))))

(deftest the-reference-reads-each-sibling-route-above-the-knock
  ;; A scoped knock's reference reads the whole KB above CxD, so each sibling reads the
  ;; conclusion over its own route there; a reference that named one route alone would
  ;; leave CxA without it and agree with a build that did the same.
  (doseq [kind [:sibling :sibling-fact :sibling-subsume]]
    (testing (str kind)
      (let [[_ reference] (run-order kind :scoped [:named :other :claim :knock])]
        (is (= [false true true true] reference))))))

;; ---- sibling routes, with nothing knocked out ------------------------------
;;
;; Two routes stated in sibling contexts decide two placements, neither above the other,
;; so a firing that named one route alone left the other sibling without the conclusion
;; whenever the named route was already present when the rule fired.  Each shape below
;; builds its parts in every order and compares each order's answers with the pinned
;; answers at CxUniverse, CxA, CxB and CxD (below both siblings).

(defn- sibling-shape
  "One sibling shape as data, over fresh terms: `:base`, the `:parts` that arrive in some
  order (a vector of `[part [[sentence context] …]]`), the `:goal`, and the `:expect`ed
  answers at `:readers`."
  [shape]
  (let [{:syms [low_t mid_t high_t val_t aRel noted alive_t partOf P1 P2 P3 Fido CxA CxB CxD]}
        (terms '[low_t mid_t high_t val_t aRel noted alive_t partOf P1 P2 P3 Fido CxA CxB CxD])
        ctxs    (sibling-contexts CxA CxB CxD)
        pres    [[(list 'transitiveInArg aRel 1 'genl) 'CxUniverse]]
        noting  [[(list 'set/forwardRule (list 'implies (list aRel '?x '?y) (list noted '?x '?y)))
                  'CxUniverse]]
        long-a  [[:a1 [[(list 'genl low_t mid_t) CxA]]] [:a2 [[(list 'genl mid_t high_t) CxA]]]]
        short-b [:b [[(list 'genl low_t high_t) CxB]]]
        readers ['CxUniverse CxA CxB CxD]]
    (case shape
      ;; the claim in CxA: CxB reaches but does not see the claim, so the CxB route places
      ;; the conclusion in CxD and the CxA route places it in CxA
      :claim-in-sibling
      {:base  (concat ctxs pres noting)
       :parts (conj long-a short-b [:claim [[(list aRel high_t val_t) CxA]]])
       :goal  (list noted low_t val_t) :readers readers :expect [false true false true]}

      :claim-above
      {:base  (concat ctxs pres noting)
       :parts (conj long-a short-b [:claim [[(list aRel high_t val_t) 'CxUniverse]]])
       :goal  (list noted low_t val_t) :readers readers :expect [false true true true]}

      ;; one edge, stated in each sibling
      :one-edge-twice
      {:base  (concat ctxs pres noting)
       :parts [[:a [[(list 'genl low_t high_t) CxA]]] short-b
               [:claim [[(list aRel high_t val_t) 'CxUniverse]]]]
       :goal  (list noted low_t val_t) :readers readers :expect [false true true true]}

      ;; one declaration, stated in each sibling
      :declared-twice
      {:base  (concat ctxs noting [[(list 'genl low_t high_t) 'CxUniverse]])
       :parts [[:da [[(list 'transitiveInArg aRel 1 'genl) CxA]]]
               [:db [[(list 'transitiveInArg aRel 1 'genl) CxB]]]
               [:claim [[(list aRel high_t val_t) 'CxUniverse]]]]
       :goal  (list noted low_t val_t) :readers readers :expect [false true true true]}

      ;; one claim, stated in each sibling
      :claimed-twice
      {:base  (concat ctxs pres noting [[(list 'genl low_t high_t) 'CxUniverse]])
       :parts [[:ca [[(list aRel high_t val_t) CxA]]] [:cb [[(list aRel high_t val_t) CxB]]]]
       :goal  (list noted low_t val_t) :readers readers :expect [false true true true]}

      :fact-relation
      {:base  (concat ctxs noting [[(list 'transitive partOf) 'CxUniverse]
                                   [(list 'transitiveInArg aRel 1 partOf) 'CxUniverse]])
       :parts [[:a1 [[(list partOf P3 P2) CxA]]] [:a2 [[(list partOf P2 P1) CxA]]]
               [:b [[(list partOf P3 P1) CxB]]] [:claim [[(list aRel P1 val_t) 'CxUniverse]]]]
       :goal  (list noted P3 val_t) :readers readers :expect [false true true true]}

      :subsumed-match
      {:base  (concat ctxs
                      (for [t [low_t mid_t high_t]] [(list 'genl t 'thing) 'CxUniverse])
                      [[(list 'set/forwardRule (list 'implies (list high_t '?x) (list alive_t '?x)))
                        'CxUniverse]])
       :parts (conj long-a short-b [:claim [[(list low_t Fido) 'CxUniverse]]])
       :goal  (list alive_t Fido) :readers readers :expect [false true true true]}

      :subsumed-over-one-edge-twice
      {:base  (concat ctxs
                      (for [t [low_t high_t]] [(list 'genl t 'thing) 'CxUniverse])
                      [[(list 'set/forwardRule (list 'implies (list high_t '?x) (list alive_t '?x)))
                        'CxUniverse]])
       :parts [[:a [[(list 'genl low_t high_t) CxA]]] short-b [:claim [[(list low_t Fido) 'CxUniverse]]]]
       :goal  (list alive_t Fido) :readers readers :expect [false true true true]}

      ;; one `(transitive R)`, stated in each sibling, licensing a fact-relation reach
      ;; stated in CxUniverse.  CxUniverse sees neither statement, so it reads nothing.
      ;; The preservation is refused before any `(transitive R)` is stated
      ;; (`wff/arg-preserving-problems`), so only the orders that bring one first are
      ;; admitted.
      :transitive-twice
      {:base    (concat ctxs noting [[(list partOf P3 P1) 'CxUniverse]])
       :parts   [[:ta [[(list 'transitive partOf) CxA]]] [:tb [[(list 'transitive partOf) CxB]]]
                 [:decl [[(list 'transitiveInArg aRel 1 partOf) 'CxUniverse]]]
                 [:claim [[(list aRel P1 val_t) 'CxUniverse]]]]
       :admits  (fn [order]
                  (let [at #(.indexOf ^java.util.List order %)]
                    (> (at :decl) (min (at :ta) (at :tb)))))
       :sampled [[:ta :claim :decl :tb] [:tb :decl :claim :ta]]
       :goal    (list noted P3 val_t) :readers readers :expect [false true true true]})))

(def ^:private sibling-shapes
  [:claim-in-sibling :claim-above :one-edge-twice :declared-twice :claimed-twice :fact-relation
   :subsumed-match :subsumed-over-one-edge-twice :transitive-twice])

(defn- sibling-answers
  "`shape`'s answers at its readers with its parts arriving in `order`, in a cleared KB."
  [shape order]
  (tu/with-cleared-kb [kb tu/isolated-fresh]
    (let [{:keys [base parts goal readers]} (sibling-shape shape)
          by-part (into {} parts)]
      (doseq [[s c] base] (v/assert kb s c))
      (doseq [part order, [s c] (by-part part)] (v/assert kb s c))
      (mapv #(v/ask? kb goal %) readers))))

(defn- sibling-orders-agree
  "Every order `order-fn` gives for each shape's parts — or the shape's own `:sampled`
  orders where `sampled?` and it names some — that the shape `:admits`, answered as
  pinned."
  [order-fn sampled?]
  (doseq [shape sibling-shapes
          :let  [{:keys [parts expect admits sampled]} (sibling-shape shape)]
          order (if (and sampled? sampled)
                  sampled
                  (filter (or admits (constantly true)) (order-fn (mapv first parts))))]
    (testing (str shape " " order)
      (is (= expect (sibling-answers shape order))))))

(deftest a-sibling-route-carries-the-firing-in-sampled-orders
  ;; the parts in their written order, which brings the CxB route before the claim, and
  ;; reversed, which brings it after — or the shape's own sampled orders, where the
  ;; reversal is not an order it admits
  (sibling-orders-agree (fn [parts] [parts (vec (rseq parts))]) true))

(deftest ^:slow a-sibling-route-carries-the-firing-in-every-order
  (sibling-orders-agree permutations false))

;; ---- a permuting mark, stated in each sibling -----------------------------
;;
;; `(symmetric R)` and the commutativity marks decide the order a sentex's arguments are
;; stored in, and a sentex has one key for every context, so the store reads a mark stated
;; in either sibling from CxUniverse.  The engine lifts each statement into CxUniverse
;; (`special/deduce-lifts`), so a claim read through its mirror licenses the firing there
;; over the copy, and the copy rests on each sibling's statement in turn: the firing stands
;; while either statement does and goes with the last, to the answers of a KB that never
;; held the mark.  Two goals read it, one per path: the inherited firing at a term below
;; the claim, and the plain firing the rule makes over the claim's mirror, which the join
;; and the trigger reach by reading the stored fact the other way round
;; (`chain/read-marks`).

(defn- mark-shape
  "A claim stored in the order its mirror reverses, preserved down `genl` at argument 1 by
  a rule-bearing relation, with the mark `mark-of` builds stated in CxA as `:ma` and in CxB
  as `:mb`.  `:stored` is the claim's stored spelling, which both goals need reversed:
  the inherited one below the claim's first term, the plain one at the claim itself."
  [mark-of]
  (let [{:syms [low_t aval_t zhigh_t aRel noted CxA CxB CxD]}
        (terms '[low_t aval_t zhigh_t aRel noted CxA CxB CxD])
        m (mark-of aRel)]
    {:base    (concat (sibling-contexts CxA CxB CxD)
                      [[(list 'arity aRel 2) 'CxUniverse]
                       [(list 'transitiveInArg aRel 1 'genl) 'CxUniverse]
                       [(list 'genl low_t zhigh_t) 'CxUniverse]
                       [(list 'set/forwardRule (list 'implies (list aRel '?x '?y) (list noted '?x '?y)))
                        'CxUniverse]])
     :parts   [[:ma [[m CxA]]] [:mb [[m CxB]]] [:claim [[(list aRel aval_t zhigh_t) 'CxUniverse]]]]
     :stored  (list aRel aval_t zhigh_t)
     :goals   [(list noted low_t aval_t) (list noted zhigh_t aval_t)]
     :readers ['CxUniverse CxA CxB CxD]}))

(defn- mark-answers
  "The answers to each goal at `mark-of`'s readers with its parts arriving in `order`,
  then after each statement in `withdrawn` is retracted in turn, in a cleared KB."
  [mark-of order withdrawn]
  (tu/with-cleared-kb [kb tu/isolated-fresh]
    (let [{:keys [base parts stored goals readers]} (mark-shape mark-of)
          by-part (into {} parts)
          read    (fn [] (mapv (fn [g] (mapv #(v/ask? kb g %) readers)) goals))]
      (doseq [[s c] base] (v/assert kb s c))
      (doseq [part order, [s c] (by-part part)] (v/assert kb s c))
      (is (= stored (:sentence (v/sentex kb (v/handle-of kb stored 'CxUniverse))))
          "the claim is stored in the order the goal reverses, or this proves nothing")
      ;; the preservation re-check also withdraws the plain firing once no reading holds,
      ;; so what the answers alone cannot show is that the firing rests on the mark
      (let [sups (mapcat #(:support (v/why kb (:id %)))
                         (v/sentexes-matching kb (second goals) '?c))]
        (is (and (seq sups)
                 (every? (fn [s] (some #(= 'symmetric (first (:sentence %))) (:because s))) sups))
            "the plain firing names the mark it read the claim through"))
      (into [(read)]
            (for [part withdrawn]
              (do (doseq [[s c] (by-part part)] (v/retract! kb (v/handle-of kb s c)))
                  (read)))))))

(deftest a-permuting-mark-in-each-sibling-holds-the-mirrored-firing-until-the-last-goes
  (doseq [mark-of   [#(list 'symmetric %)]
          order     (permutations [:ma :mb :claim])
          withdrawn [[:ma :mb] [:mb :ma]]]
    (testing (str (first (mark-of 'r)) " " order " withdrawing " withdrawn)
      (is (= (mapv #(vec (repeat 2 (vec (repeat 4 %)))) [true true false])
             (mark-answers mark-of order withdrawn))))))
