;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.negation-oracle-test
  "Incremental P/¬P pairing finds the same nogoods an exhaustive pass does.

  `settle` has to know which believed negations coexist with a believed positive of the
  same body, jointly visible from some context — and that question is exhaustive by
  nature: every doubly-stored body, every believed sentex of each polarity, crossed.
  Asking it that way costs two belief-filtered `query` calls and a cross product per
  opposed body per settle *round*, and a settle runs after every mutation, so a KB would
  load N contradictions in quadratic time even when no two of them share a term.

  So the engine narrows it twice, and each narrowing is a *claim* that what it skips
  cannot have changed the answer:

  * **`:opposed`** (`kb/note-opposed!`) — a body with no stored twin can pair with
    nothing, so it is never looked at.  That narrowing is old and this namespace takes it
    for granted; `lein perf`'s `negation-load` is what holds it.
  * **the per-body memo** (`settle/*incremental-negations*`) — only the opposed bodies
    this settle could have moved are re-derived, and every other body's pairs and
    priorities are carried forward from the last settle verbatim.  That is what these
    tests are about.

  A wrong narrowing is not a crash.  It is a dilemma that stops being reported, or a
  defeat that stops being applied, on a KB that looks entirely healthy — the failure mode
  a unit test written against a hand-built scenario is worst at catching, because the
  scenario names the very pair the narrowing would have to skip to be wrong.

  `settle/*incremental-negations*` bound to `false` is the exhaustive question, asked in
  full on every call.  The randomized oracle below runs the same operation sequence into
  two KBs, one each way, and compares **after every step**: believed content, the
  dilemmas, the conflicts, and whether the write was refused at all.  Step by step rather
  than at the end, so a divergence names the operation that caused it.

  ## What the memo has to be told, and by what

  Three things move a body's pairing, and no one of them sees the other two.  The
  directed tests after the oracle isolate each, because a random stream that happened not
  to generate one would report a clean run:

  * **a store or a removal** — a second `(not S)` arriving in another context pairs two
    sentexes that were *both already believed*, so no label moves and the relabelled
    region is empty.  `note-opposed!` posts the body as dirty.
  * **a relabel** — a defeat or a revival changes which pairs are believed while nothing
    is stored.  `jtms/touched` carries it.
  * **a genlCx edge** — joint visibility is read through that closure rather than
    through either side's handles, so an edge can make a pair visible that neither side
    went near.  Each entry records the visibility verdict for the contexts it crosses,
    and the entries whose verdicts moved are the ones re-derived.

  And one that is none of the three: a **supersession flip**, which subtracts a spelling
  from belief with no relabel to record it (docs/equality.md).  `settle-finish` hands
  those handles over by name, exactly as it does to the taxonomy reconcile beside it.

  ## What these tests reach, checked by breaking it

  Each of the three inputs above has a directed test that goes red when that input alone
  is removed — dropping `:dirty` reddens the retraction case, dropping `jtms/touched` the
  revival case, dropping the visibility verdicts the exposure and withdrawal cases — and
  the randomized oracle catches all three as well.

  The supersession hand-off is the one mechanism here that **nothing below reaches**, and
  the reason matters rather than leaving as a gap.  Displacing a body normally
  *carries* its entry rather than dropping it: migration writes the twins on the
  representative's body, so nothing stores, removes or relabels on the displaced one, and
  the carried entry is filtered out on belief while it is displaced and simply becomes
  live again when the merge goes.  The hand-off matters only when something *else*
  re-derives the displaced body mid-window and drops the entry — a shape these streams do
  not generate, since a rule firing at a displaced conclusion is placed at the
  representative rather than at the displaced spelling.  `settle/note-supersession-flips!`
  carries the argument; a stream that produced the shape would belong here."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

;; ---- the shared ontology ------------------------------------------------

(def ^:private ctxs
  "Three contexts, two of them **incomparable**: `CxNegLeft` and `CxNegRight`
  both inherit `CxNegBase` and neither sees the other.  A pair straddling them is
  invisible until something below both exists, which is the joint-visibility case
  `common-descendant?` answers and the `sees?` test alone would miss."
  '[CxNegBase CxNegLeft CxNegRight])

(def ^:private preds '[nflies nswims nsings])
(def ^:private inds  '[NA NB NC])

(defn- build-ontology! [kb]
  (v/with-deferred-settle kb
    (doseq [c (rest ctxs)]
      (v/assert kb (list 'genlCx c (first ctxs)) 'CxUniverse))))

;; ---- the operation stream -----------------------------------------------

(defn- rand-op
  "One write, drawn to hit every route a negation nogood can arrive, leave and come back
  by: either polarity of a shared body in any of the three contexts, at either strength
  (so a pair can be decided by rank or stand as a dilemma), retraction of either side,
  and — the case no store or relabel announces — a `genlCx` edge arriving *after* a
  pair that only it makes jointly visible."
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
      ;; the third context is dropped *below* the other two, which makes every
      ;; left/right pair standing at the time jointly visible at once — with no handle
      ;; of any of them stored or relabelled
      8       [:assert (list 'genlCx 'CxNegJoin (nth ctxs 1)) 'CxUniverse
               {:strength :monotonic}]
      9       [:assert (list 'genlCx 'CxNegJoin (nth ctxs 2)) 'CxUniverse
               {:strength :monotonic}])))

(defn- apply-op!
  "Run one op, reporting the refusal rather than propagating it — a refusal is an
  observation the two KBs must agree on, not a reason to stop the trial."
  [kb [kind sentence context opts]]
  (try (case kind
         :assert  (do (v/assert kb sentence context opts) :ok)
         :retract (if-let [h (v/handle-of kb sentence context)]
                    (do (v/retract! kb h) :ok)
                    :absent))
       (catch clojure.lang.ExceptionInfo e
         [:refused (:type (ex-data e))])))

;; ---- the observation ----------------------------------------------------

(defn- clash-key
  "A reported pair as content: the rank, the `contradicts` form and both sides.  Handles
  are dropped — they are allocated in arrival order, and the two KBs are compared on what
  they believe, not on where they put it."
  [e]
  [(:priority e) (:sentence e)
   (into #{} (map (juxt :sentence :context :defeat-class)) (:sides e))])

(defn- snapshot [kb]
  {:believed  (into #{}
                    (comp (keep #(p/get-sentex (:records kb) %))
                          (map (juxt :sentence :context)))
                    (jtms/in-datums (reasoning/tms kb)))
   :dilemmas  (into #{} (map clash-key) (v/contradictions kb))
   :conflicts (into #{} (map clash-key) (v/conflicts kb))})

(defn- diff [a b]
  (into {} (keep (fn [k]
                   (let [x (get a k) y (get b k)]
                     (when (not= x y)
                       [k {:incremental-only (set/difference x y)
                           :exhaustive-only  (set/difference y x)}]))))
        (keys a)))

(defn- run-stream
  "The same ops into both KBs, comparing after every write.  Returns `[step op
  incremental-snapshot exhaustive-snapshot]` for the first divergence, or nil."
  [ops]
  (let [inc-kb (tu/fresh)
        exh-kb (tu/isolated-fresh)]
    (try
      (binding [settle/*incremental-negations* true]  (build-ontology! inc-kb))
      (binding [settle/*incremental-negations* false] (build-ontology! exh-kb))
      (loop [step 0, [op & more] ops]
        (if-not op
          nil
          (let [ri (binding [settle/*incremental-negations* true]  (apply-op! inc-kb op))
                re (binding [settle/*incremental-negations* false] (apply-op! exh-kb op))
                si (snapshot inc-kb)
                se (snapshot exh-kb)]
            (if (and (= ri re) (= si se))
              (recur (inc step) more)
              [step op si se]))))
      (finally (tu/clear-kb! inc-kb) (tu/clear-kb! exh-kb)))))

;; ---- oracle 1: randomized operation streams -----------------------------

(deftest randomized-streams-pair-the-same-negations
  (doseq [seed (range 12)]
    (let [rng (java.util.Random. (long seed))
          [step op si se] (run-stream (repeatedly 45 #(rand-op rng)))]
      (is (nil? step)
          (str "seed " seed " diverged at step " step " on " (pr-str op) "\n"
               (pr-str (diff si se)))))))

;; ---- oracle 2: the removal whose record is already gone -----------------
;;
;; What only `:dirty` covers.  Three sentexes on one body across two contexts; retract one
;; and the body is still opposed, so its entry must be re-derived — but `note-opposed!`
;; has already dropped that entry, and the relabelled region cannot help, because the
;; retracted handle's record is deleted and the settle can no longer ask it which body it
;; was about.  A memo told only by `jtms/touched` loses the surviving pair here.

(deftest a-retraction-re-derives-a-body-that-stays-opposed
  (let [[step op si se]
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
          ;; one more settle, which is where a pair dropped by the retraction and never
          ;; re-derived would silently stay gone
          [:assert '(nsings NB) (first ctxs) {}]])]
    (is (nil? step)
        (str "diverged at step " step " on " (pr-str op) "\n" (pr-str (diff si se))))))

;; ---- oracle 2b: the revival nothing writes ------------------------------
;;
;; What only the relabelled region covers.  A defeated pair leaves the memo, because
;; re-derivation is belief-filtered and there is nothing believed to pair — so bringing it
;; back is not a stale entry to refresh but an absent one to find again.  Here the defeat
;; is lifted by retracting a *different* body: two rules conclude `(nflies NA)`, and
;; dropping the known-true route leaves the conclusion standing on the defeasible one at a
;; lower class, which revives the negation.  Nothing is stored or removed on `(nflies NA)`
;; — the write is a retraction of `(nq NA)` — so the dirty set is filtered empty and only
;; `clear-defeats!`'s relabel says the pair is back.
;;
;; Note what is *not* testable here, and why the memo need not carry it: a carried
;; entry's `:priority` cannot go stale in any way a caller can see.  `decide-nogood` reads
;; the defeat classes live rather than off the entry, and a pair that stays a dilemma has
;; both members at `:default` by definition — the moment either rises the pair stops being
;; a dilemma and is decided instead.  So what a carried entry has to get right is *which
;; pairs exist*, and belief is re-read at every decision.

(deftest a-revival-elsewhere-brings-a-pair-back
  (let [[step op si se]
        (run-stream
         [[:assert (list 'set/forwardRule (vr/rule-sentence ['(nq ?x)] '(nflies ?x)))
           (first ctxs) {:strength :monotonic}]
          [:assert (list 'set/forwardRule (vr/rule-sentence ['(nr ?x)] '(nflies ?x)))
           (first ctxs) {:strength :monotonic}]
          ;; known-true route: (nflies NA) is derived at :monotonic
          [:assert '(nq NA) (first ctxs) {:strength :monotonic}]
          ;; a second, defeasible route to the same conclusion — no new sentex, so
          ;; nothing is written about the body
          [:assert '(nr NA) (first ctxs) {}]
          ;; the negation ranks below the monotonic conclusion and is defeated, which
          ;; empties the body's memo entry
          [:assert (list 'not '(nflies NA)) (first ctxs) {}]
          ;; unrelated traffic, so the body is well out of the region
          [:assert '(nswims NB) (first ctxs) {}]
          ;; ...and now the known-true route goes.  (nflies NA) survives on the
          ;; defeasible one at :default, so the negation revives and the pair is a
          ;; dilemma again — with nothing stored or removed on its body.
          [:retract '(nq NA) (first ctxs)]
          [:assert '(nsings NC) (first ctxs) {}]])]
    (is (nil? step)
        (str "diverged at step " step " on " (pr-str op) "\n" (pr-str (diff si se))))))

;; ---- oracle 3: the edge that makes a standing pair visible --------------
;;
;; Two incomparable contexts each holding one polarity: no context sees both, so there is
;; no clash.  A context inheriting both then makes every such pair visible at once — with
;; nothing stored about them and no label moved.  Only the joint-visibility verdict the
;; memo recorded for the two contexts says so.

(deftest a-genlCx-edge-exposes-standing-pairs
  (let [[step op si se]
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
        (str "diverged at step " step " on " (pr-str op) "\n" (pr-str (diff si se))))))

(deftest a-genlCx-edge-leaving-withdraws-the-pairs-it-exposed
  ;; The other direction of the same claim, and one the exposure case does not imply.  A
  ;; memo told what to re-derive by the verdicts it recorded has to notice a verdict going
  ;; from true back to *false*: a pair that was jointly visible and is not any more must
  ;; stop being reported, with nothing stored, removed or relabelled on either side of it.
  ;; Retracting one of the two edges is enough — it makes left and right incomparable
  ;; again, and every pair the join exposed goes with it.
  (let [[step op si se]
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
           ;; one more settle, which is where a pair still carried would keep showing up
           [:assert '(nsings NC) (nth ctxs 1) {}]
           ;; ...and back, since a verdict that has moved twice is the one a stamp
           ;; comparing the wrong thing gets right by accident
           [:assert '(genlCx CxNegJoin CxNegRight) 'CxUniverse
            {:strength :monotonic}]
           [:assert '(nflies NB) (nth ctxs 1) {}]]))]
    (is (nil? step)
        (str "diverged at step " step " on " (pr-str op) "\n" (pr-str (diff si se))))))

;; ---- oracle 4: defeat, then revival -------------------------------------
;;
;; A default against known-true content loses, and the loser must come back when the
;; winner is retracted.  Re-derivation is belief-filtered, so the defeated pair leaves the
;; memo entirely while it is out; what brings it back is `clear-defeats!` relabelling the
;; region it sits in, which is the one narrowing input that is *not* a store.

(deftest a-defeated-pair-revives-when-its-defeater-goes
  (let [[step op si se]
        (run-stream
         [[:assert '(nflies NA) (first ctxs) {:strength :monotonic}]
          [:assert (list 'not '(nflies NA)) (first ctxs) {}]      ; default loses
          [:assert '(nswims NB) (first ctxs) {}]                   ; an unrelated settle
          [:retract '(nflies NA) (first ctxs)]                     ; ...and the winner goes
          [:assert '(nsings NC) (first ctxs) {}]])]
    (is (nil? step)
        (str "diverged at step " step " on " (pr-str op) "\n" (pr-str (diff si se))))))

;; ---- oracle 5: the belief change with no relabel behind it -------------
;;
;; A merge displaces a spelling: `in?` subtracts the superseded set, so both sides of a
;; standing pair stop being believed while neither label moves and nothing on their body
;; is stored or removed (the twins are written on the *representative's* body).  Dropping
;; the merge hands the spellings back the same way.  Neither direction reaches
;; `moved-bodies` through its own two inputs, which is why `settle-finish` posts the
;; flipped handles by name.

(deftest a-merge-and-its-undoing-move-a-pair
  (let [[step op si se]
        (run-stream
         [[:assert '(nflies NA)             (first ctxs) {}]
          [:assert (list 'not '(nflies NA)) (first ctxs) {}]     ; a standing dilemma
          [:assert '(nswims NB) (first ctxs) {}]                  ; unrelated traffic
          ;; NA is deprecated in favour of NB, so both sides of the pair are restated on
          ;; NB's body and the originals are superseded
          [:assert '(rewriteOf NB NA) (first ctxs) {:strength :monotonic}]
          [:assert '(nsings NC) (first ctxs) {}]
          ;; ...and the merge goes, which gives the original spellings back
          [:retract '(rewriteOf NB NA) (first ctxs)]
          [:assert '(nsings NB) (first ctxs) {}]])]
    (is (nil? step)
        (str "diverged at step " step " on " (pr-str op) "\n" (pr-str (diff si se))))))

;; ---- the standing dilemma an unrelated assert must not erase ------------
;;
;; The bug the carry-forward exists to prevent, stated directly rather than differentially:
;; `contradictions` is recomputed from scratch each settle, so a dilemma whose ingredients
;; sat still while something unrelated was asserted would be reported once and then
;; silently vanish.  Directed, because the oracle compares two KBs and would stay green if
;; *both* of them lost it.

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
      (let [shuffled (shuffle content)]
        (is (= base (run! shuffled))
            (str "arrival order " seed " changed the answer\n"
                 (pr-str (diff base (run! shuffled)))))))))
