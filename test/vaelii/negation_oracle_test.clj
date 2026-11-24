;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.negation-oracle-test
  "A negation pair is decided as the belief reference decides it after every write of a
  stream, retractions included.

  A randomized oracle runs one operation stream into a KB and, after every step, compares
  the belief at each context with `vaelii.ref.believe` over the writes standing, so a
  divergence names its operation.  The directed streams each move a pair one way no
  arrival order reaches: a retraction whose record is gone, a revival with nothing
  written on the body, and a `genlCx` edge arriving and leaving.  `vaelii.reference-test`
  covers the arrival orders of a set of writes; this covers the writes a stream removes."
  (:require [clojure.set]
            [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.ref.believe :as believe]
            [vaelii.ref.gen :as gen]
            [vaelii.ref.nogoods :as nogoods]
            [vaelii.test-util :as tu]))

;; ---- the shared ontology ------------------------------------------------

(def ^:private ctxs
  "Three contexts: `CxNegLeft` and `CxNegRight` both inherit `CxNegBase` and neither
  sees the other, so a pair straddling them pairs only once a context below both exists."
  '[CxNegBase CxNegLeft CxNegRight])

(def ^:private preds '[nflies nswims nsings])
(def ^:private inds  '[NA NB NC])

(def ^:private ontology
  "The writes every stream starts from: `CxNegLeft` and `CxNegRight` under `CxNegBase`."
  (for [c (rest ctxs)] [:assert (list 'genlCx c (first ctxs)) 'CxUniverse {}]))

(def ^:private world-contexts
  "The contexts each step compares."
  (into (set ctxs) '[CxNegJoin CxUniverse]))

(defn- rand-op
  "One write: either polarity of a shared body in any context, at either strength,
  retraction of either side, or a `genlCx` edge that makes standing pairs jointly visible."
  [^java.util.Random rng]
  (let [ctx  (nth ctxs (.nextInt rng (count ctxs)))
        pred #(nth preds (.nextInt rng (count preds)))
        ind  #(nth inds  (.nextInt rng (count inds)))
        str8 #(if (zero? (.nextInt rng 3)) {:strength :monotonic} {})
        body #(list (pred) (ind))]
    (case (.nextInt rng 10)
      (0 1 2) [:assert (body) ctx (str8)]
      (3 4 5) [:assert (list 'not (body)) ctx (str8)]
      6       [:retract (body) ctx]
      7       [:retract (list 'not (body)) ctx]
      ;; CxNegJoin below both sides exposes every standing left/right pair at once
      8       [:assert (list 'genlCx 'CxNegJoin (nth ctxs 1)) 'CxUniverse
               {:strength :monotonic}]
      9       [:assert (list 'genlCx 'CxNegJoin (nth ctxs 2)) 'CxUniverse
               {:strength :monotonic}])))

(defn- apply-op!
  "Run one op against `kb` and return `writes` (`{[sentence context] strength}`) as it
  stands after it, or `[:refused type]` for a write `assert` refuses.  A rule is written
  as the reference writes it and asserted in the engine's form (`gen/engine-form`)."
  [kb writes [kind sentence context opts]]
  (try (case kind
         :assert  (let [k (:strength opts :default)]
                    (v/assert kb (gen/engine-form sentence) context opts)
                    (update writes [sentence context]
                            #(if (= :monotonic %) % k)))
         :retract (if-let [h (v/handle-of kb (gen/engine-form sentence) context)]
                    (do (v/retract! kb h) (dissoc writes [sentence context]))
                    writes))
       (catch clojure.lang.ExceptionInfo e
         [:refused (:type (ex-data e))])))

(defn- world-of [writes]
  {:contexts world-contexts
   :writes   (vec (for [[[s c] k] (sort-by (comp pr-str key) writes)]
                    {:sentence s :context c :strength k}))})

(defn- run-stream
  "The ops into one KB, comparing it with the reference after every write.  Returns
  `[step op disagreements]` for the first step that disagrees or is refused, or nil."
  [ops]
  (let [loaded (gen/load-world! nil [] {})
        kb     (:kb loaded)]
    (try
      (loop [step 0, writes {}, [op & more] (concat ontology ops)]
        (if-not op
          nil
          (let [r (apply-op! kb writes op)]
            (if (vector? r)
              [step op r]
              (let [world (world-of r)
                    ds    (gen/compare world (believe/believe world nogoods/families)
                                       (gen/engine-beliefs kb world))]
                (if (seq ds)
                  [step op ds]
                  (recur (inc step) r more)))))))
      (finally (gen/close-kb! loaded)))))

;; ---- oracle 1: randomized operation streams -----------------------------

(deftest randomized-streams-pair-the-same-negations
  (doseq [seed (range 12)]
    (let [rng (java.util.Random. (long seed))
          [step op ds] (run-stream (repeatedly 45 #(rand-op rng)))]
      (is (nil? step)
          (str "seed " seed " diverged at step " step " on " (pr-str op) "\n"
               (pr-str ds))))))

;; ---- oracle 2: the removal whose record is already gone -----------------
;; The retracted handle's record is gone, so only the body's entry, read again at the
;; removal choke point, can drop the pair it formed and keep the one that stands.

(deftest a-retraction-re-derives-a-body-that-stays-opposed
  (let [[step op ds]
        (run-stream
         [;; CxNegBase is seen by both of the others, so all three pair
          [:assert '(nflies NA)             (first ctxs) {}]
          [:assert (list 'not '(nflies NA)) (nth ctxs 1) {}]
          [:assert (list 'not '(nflies NA)) (nth ctxs 2) {}]
          ;; unrelated traffic, so the survivors are long out of the region
          [:assert '(nswims NB) (first ctxs) {}]
          [:assert '(nsings NC) (first ctxs) {}]
          ;; one negation goes; the body is still stored in both polarities, so the
          ;; other pair stands and has to be re-derived without it
          [:retract (list 'not '(nflies NA)) (nth ctxs 2)]
          ;; one more settle, where a pair the retraction dropped would stay gone
          [:assert '(nsings NB) (first ctxs) {}]])]
    (is (nil? step)
        (str "diverged at step " step " on " (pr-str op) "\n" (pr-str ds)))))

;; ---- oracle 2b: the revival nothing writes ------------------------------
;; Retracting `(nq NA)` drops the monotonic route to `(nflies NA)`, which then stands at
;; :default and revives the defeated negation, with nothing stored or removed on the
;; body: the pair moves on a class alone.

(deftest a-revival-elsewhere-brings-a-pair-back
  (let [[step op ds]
        (run-stream
         [[:assert '(set/forwardRule (implies (nq ?x) (nflies ?x))) (first ctxs) {:strength :monotonic}]
          [:assert '(set/forwardRule (implies (nr ?x) (nflies ?x))) (first ctxs) {:strength :monotonic}]
          ;; known-true route: (nflies NA) is derived at :monotonic
          [:assert '(nq NA) (first ctxs) {:strength :monotonic}]
          ;; a second, defeasible route to the same conclusion — no new sentex, so
          ;; nothing is written about the body
          [:assert '(nr NA) (first ctxs) {}]
          ;; the negation ranks below the monotonic conclusion and is defeated
          [:assert (list 'not '(nflies NA)) (first ctxs) {}]
          ;; unrelated traffic, so the body is well out of the region
          [:assert '(nswims NB) (first ctxs) {}]
          ;; ...and now the known-true route goes.  (nflies NA) survives on the
          ;; defeasible one at :default, so the negation revives and the pair is a
          ;; dilemma again — with nothing stored or removed on its body.
          [:retract '(nq NA) (first ctxs)]
          [:assert '(nsings NC) (first ctxs) {}]])]
    (is (nil? step)
        (str "diverged at step " step " on " (pr-str op) "\n" (pr-str ds)))))

;; ---- oracle 3: the edge that makes a standing pair visible --------------
;; Nothing is stored or relabelled on either side: the pairs move on the `genlCx`
;; closure alone.

(deftest a-genlCx-edge-exposes-standing-pairs
  (let [[step op ds]
        (run-stream
         (concat
          (for [p preds] [:assert (list p 'NA) (nth ctxs 1) {}])
          (for [p preds] [:assert (list 'not (list p 'NA)) (nth ctxs 2) {}])
          ;; nothing above pairs: left and right are incomparable
          [[:assert '(genlCx CxNegJoin CxNegLeft) 'CxUniverse
            {:strength :monotonic}]
           ;; ...and this second edge is what puts a context below *both*
           [:assert '(genlCx CxNegJoin CxNegRight) 'CxUniverse
            {:strength :monotonic}]
           [:assert '(nswims NB) (nth ctxs 1) {}]]))]
    (is (nil? step)
        (str "diverged at step " step " on " (pr-str op) "\n" (pr-str ds)))))

(deftest a-genlCx-edge-leaving-withdraws-the-pairs-it-exposed
  ;; A verdict moving from true back to false: retracting one edge withdraws every pair
  ;; the join exposed.
  (let [[step op ds]
        (run-stream
         (concat
          (for [p preds] [:assert (list p 'NA) (nth ctxs 1) {}])
          (for [p preds] [:assert (list 'not (list p 'NA)) (nth ctxs 2) {}])
          [[:assert '(genlCx CxNegJoin CxNegLeft) 'CxUniverse
            {:strength :monotonic}]
           [:assert '(genlCx CxNegJoin CxNegRight) 'CxUniverse
            {:strength :monotonic}]
           ;; a settle in between, so the pairs are standing rather than arriving
           [:assert '(nswims NB) (nth ctxs 1) {}]
           [:retract '(genlCx CxNegJoin CxNegRight) 'CxUniverse]
           ;; one more settle, where a pair still read would keep showing up
           [:assert '(nsings NC) (nth ctxs 1) {}]
           ;; ...and back: the same verdict moving a second time
           [:assert '(genlCx CxNegJoin CxNegRight) 'CxUniverse
            {:strength :monotonic}]
           [:assert '(nflies NB) (nth ctxs 1) {}]]))]
    (is (nil? step)
        (str "diverged at step " step " on " (pr-str op) "\n" (pr-str ds)))))

;; ---- oracle 4: defeat, then revival -------------------------------------

(deftest a-defeated-pair-revives-when-its-defeater-goes
  (let [[step op ds]
        (run-stream
         [[:assert '(nflies NA) (first ctxs) {:strength :monotonic}]
          [:assert (list 'not '(nflies NA)) (first ctxs) {}]      ; default loses
          [:assert '(nswims NB) (first ctxs) {}]                   ; an unrelated settle
          [:retract '(nflies NA) (first ctxs)]                     ; ...and the winner goes
          [:assert '(nsings NC) (first ctxs) {}]])]
    (is (nil? step)
        (str "diverged at step " step " on " (pr-str op) "\n" (pr-str ds)))))

;; ---- the reports ---------------------------------------------------------
;; The reference compares belief; these hold the reports.

(defn- build-ontology! [kb]
  (v/with-deferred-settle kb
    (doseq [[_ s c] ontology] (v/assert kb s c))))

(defn- clash-key
  "A reported pair as content, without handles, which differ between two KBs."
  [e]
  [(:priority e) (:sentence e)
   (into #{} (map (juxt :sentence :context :defeat-class)) (:sides e))])

(defn- snapshot [kb]
  {:believed  (into #{}
                    (comp (keep #(p/get-sentex (:records kb) %))
                          (map (juxt :sentence :context))
                          (map #(tu/handle-free kb %)))
                    (jtms/in-datums (reasoning/tms kb)))
   :dilemmas  (into #{} (map clash-key) (v/contradictions kb))
   :conflicts (into #{} (map clash-key) (v/conflicts kb))})

(defn- diff [a b]
  (into {} (keep (fn [k]
                   (let [x (get a k) y (get b k)]
                     (when (not= x y)
                       [k {:first-only (clojure.set/difference x y)
                           :second-only (clojure.set/difference y x)}]))))
        (keys a)))

;; ---- the standing dilemma an unrelated assert must not erase ------------
;; Directed, because the oracle stays green if both KBs lose the dilemma.

(deftest a-standing-dilemma-survives-unrelated-asserts
  (let [kb (tu/fresh)]
    (try
      (build-ontology! kb)
      (v/assert kb '(nflies NA) (first ctxs) {})
      (v/assert kb (list 'not '(nflies NA)) (first ctxs) {})
      (let [reported (fn [] (into #{} (map :sentence) (v/contradictions kb)))
            standing (reported)]
        (is (= 1 (count standing)) "a default against a default is a represented dilemma")
        (doseq [i (range 5)]
          (v/assert kb (list 'nswims (symbol (str "NX" i))) (first ctxs) {})
          (is (= standing (reported))
              (str "the standing dilemma was dropped by unrelated assert " i))))
      (finally (tu/clear-kb! kb)))))

;; ---- order independence -------------------------------------------------

(deftest the-same-dilemmas-in-any-order
  (let [content [['(nflies NA)              (first ctxs) {:strength :monotonic}]
                 [(list 'not '(nflies NA))  (first ctxs) {}]
                 ['(nswims NB)              (nth ctxs 1) {}]
                 [(list 'not '(nswims NB))  (nth ctxs 1) {}]
                 ['(nsings NC)              (nth ctxs 2) {}]
                 [(list 'not '(nsings NC))  (nth ctxs 2) {:strength :monotonic}]]
        run! (fn [ops]
               (let [kb (tu/fresh)]
                 (try
                   (build-ontology! kb)
                   (doseq [[s c o] ops] (v/assert kb s c o))
                   (snapshot kb)
                   (finally (tu/clear-kb! kb)))))
        base (run! content)]
    (doseq [seed (range 6)]
      (let [shuffled (tu/shuffled seed content)]
        (is (= base (run! shuffled))
            (str "arrival order " seed " changed the answer\n"
                 (pr-str (diff base (run! shuffled)))))))))
