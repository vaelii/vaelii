;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.clash-oracle-test
  "Incremental clash discovery finds the same nogoods an exhaustive pass does.

  `settle` has to know which pairs of believed sentexes violate a separation, a
  `functional` or an `asymmetric` declaration — and that question is exhaustive by
  nature: every believed sentex against every other.  Asking it that way costs an
  `arbitrable-violations` call per believed sentex per settle, and a settle runs after
  every mutation, so a KB would load its own content in quadratic time.

  So the engine narrows it three ways, and each narrowing is a *claim* that what it
  skips cannot have changed the answer:

  * **region + remembered pairs** (`clash-candidates`) — only what this settle moved,
    plus every pair already known to clash, plus what a declaration arriving in the
    region puts retroactively back in question;
  * **`could-clash?`** — a sentex that cannot be half of any pair is dropped before the
    check runs, on an O(1) root cardinality or property read;
  * **carry-forward** — a known pair neither of whose members moved keeps last settle's
    answer, priority and all.

  A wrong narrowing is not a crash.  It is a dilemma that stops being reported, or a
  defeat that stops being applied, on a KB that looks entirely healthy — the failure
  mode a unit test written against a hand-built scenario is worst at catching, because
  the scenario names the very pair the narrowing would have to skip to be wrong.

  `settle/*incremental-clashes*` bound to `false` is the exhaustive question, asked in
  full on every settle.  These tests run the same operation sequence into two KBs, one
  each way, and compare **after every step**: believed content, the dilemmas, the
  conflicts, and whether the write was refused at all.  Step-by-step rather than at the
  end, so a divergence names the operation that caused it rather than the run.

  Both KBs run under `checks/*arbitrate-constraints?*`, because that is the policy under
  which the claim is true.  With it off the assert path *refuses* a clash instead of
  admitting it, and the retroactive sweeps do not run — a declaration arriving over
  content stored long before it is deliberately left to the exposure pass — so the two
  discoveries answer different questions and comparing them would prove nothing.

  **Conviction has to be symmetric for the claim to hold.**  The discovery checks the
  sentexes the settle *moved*; where each side of a pair convicts the other that is
  enough, because whichever side arrives second finds the pair.  One shape convicts
  one-way only and is excluded here, because the incremental path is order-dependent on
  it for a reason that has nothing to do with the three narrowings above — see
  docs/nmtms.md, \"Where conviction is one-sided\":

  * **through argument preservation** — `(outranks animal cat)` denies the more specific
    `(outranks cat reptile)`, and preservation reads a goal's arguments upwards, so the
    specific claim asks about the general one and never the reverse.  So no
    `transitiveInArg` declaration is made here.

  That is an open question about *which* sentexes a settle owes a re-check, not about
  whether the narrowings are sound, and the exhaustive reference does not share it — a
  stream generating it would measure the open question instead of the three claims.

  The other one-sided shape, a pair **across a visibility edge**, is covered rather than
  excluded: a term's content is written in either context here, so `(animal X)` in the
  general context beside `(plant X)` in the one that sees it is an ordinary draw.
  Both paths ask each candidate's question from every context that can see a pair it
  could form (`settle/clash-askers`), so the two agree on it and the stream is what says
  so — the exhaustive reference reaches the pair from the specific side on every settle,
  and the incremental one has to reach it from whichever side moved.

  **What this reaches, checked by breaking it.**  Disabling either arm of `could-clash?`,
  forgetting the remembered pairs, or skipping the retroactive sweep each turns these
  streams red.  One mechanism it cannot reach is the carry-forward's `moved?` predicate,
  and the reason matters rather than leaving as a gap: a pair whose member the
  region holds is re-derived through the region anyway, and the fresh answer *overrides*
  the carried one, so within a single context `moved?` decides nothing that `stale?` and
  that override do not already decide.  It pays for itself only by handing the untouched
  member back as a candidate — which matters exactly where conviction is one-sided, and
  that is the regime excluded above.  `lein perf`'s `clash-arbitration` check is what
  holds it from the other side, since carrying is what keeps a settle off the standing
  set."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

;; ---- the shared ontology ------------------------------------------------

(def ^:private ctxs '[CxClashBase CxClashSub])

(def ^:private types
  '[animal mammal reptile dog cat snake plant])

(def ^:private inds
  "One pool of individuals for both contexts, so a term routinely holds one membership
  either side of the `genlCx` edge — the pair only `CxClashSub` can see whole
  (see the namespace docstring)."
  '[CI0 CI1 CI2 CI3 CI4 CI5])

(defn- build-ontology!
  "A hierarchy deep enough that a separation closes over several levels, two contexts so
  the scoping is exercised, and one declaration of each arbitrable kind.

  Deliberately *incomplete*: `(disjoint dog cat)`, `(genl snake animal)` and
  `(anti_transitive precedes)` are left for the operation stream to assert, since a
  declaration arriving over content already stored is the case the retroactive sweep
  exists for and the case a region-only discovery would miss.

  **Two rules concluding one literal**, so a clashing membership can be *derived* and can
  hold two justifications at once.  That is what lets a standing pair's `:priority` move
  while both its handles sit still: a second route arriving from a `:monotonic` premise
  lifts the conclusion's defeat class without storing anything new about it, which is the
  one thing the carry-forward has to notice and the one thing an all-premise stream can
  never produce."
  [kb]
  (v/with-deferred-settle kb
    (v/assert kb (list 'genlCx (second ctxs) (first ctxs)) 'CxUniverse)
    (doseq [[sub sup] '[[mammal animal] [reptile animal] [dog mammal] [cat mammal]]]
      (v/assert kb (list 'genl sub sup) (first ctxs) {:strength :monotonic}))
    (v/assert kb '(disjoint mammal reptile) (first ctxs) {:strength :monotonic})
    (v/assert kb '(disjoint animal plant)   (first ctxs) {:strength :monotonic})
    (v/assert kb '(functional ageOf)        (first ctxs) {:strength :monotonic})
    (v/assert kb '(asymmetric parentOf)     (first ctxs) {:strength :monotonic})
    ;; `precedes` carries no mark here: the stream asserts `(anti_transitive precedes)`
    ;; over chains already stored, which is the retroactive half of the one kind whose
    ;; nogood has three members rather than two.
    (doseq [from '[pet canine]]
      (v/assert kb (list 'set/forwardRule (vr/rule-sentence [(list from '?x)] '(dog ?x)))
                (first ctxs) {:strength :monotonic}))))

;; ---- the operation stream -----------------------------------------------

(defn- rand-op
  "One write, drawn to hit every route a clash can arrive by: a membership that
  separates against another, a second value for a functional slot, a converse of an
  asymmetric claim, a step of a chain an `anti_transitive` mark forbids closing, a
  retraction that can revive a defeated loser, a premise whose rule *derives* a clashing
  membership (and a second premise giving that conclusion a stronger second route), and —
  the retroactive cases — a separation, a genl edge or the chain mark itself arriving
  after the content it convicts."
  [^java.util.Random rng]
  (let [ctx  (nth ctxs (.nextInt rng (count ctxs)))
        ind  #(nth inds  (.nextInt rng (count inds)))
        typ  #(nth types (.nextInt rng (count types)))
        str8 #(if (zero? (.nextInt rng 3)) {:strength :monotonic} {})
        ;; a small pool for `precedes`, so random pairs close a two-step chain often
        ;; enough for the three-member nogood to be drawn rather than hoped for
        near #(nth inds (.nextInt rng 3))]
    (case (.nextInt rng 15)
      (0 1 2) [:assert (list (typ) (ind)) ctx (str8)]
      (3 4)   [:assert (list 'ageOf (ind) (.nextInt rng 4)) ctx (str8)]
      (5 6)   [:assert (list 'parentOf (ind) (ind)) ctx (str8)]
      7       [:retract (list (typ) (ind)) ctx]
      8       [:assert '(disjoint dog cat) (first ctxs) {:strength :monotonic}]
      9       [:assert '(genl snake animal) (first ctxs) {:strength :monotonic}]
      (10 11) [:assert (list (if (even? (.nextInt rng 2)) 'pet 'canine) (ind)) ctx (str8)]
      12      [:retract (list (if (even? (.nextInt rng 2)) 'pet 'canine) (ind)) ctx]
      13      [:assert (list 'precedes (near) (near)) ctx (str8)]
      14      [:assert '(anti_transitive precedes) (first ctxs) {:strength :monotonic}])))

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
  "A reported pair as content: the kind, the rank, the `contradicts` form (already
  content-ordered by the discovery) and both sides.  Handles are dropped — they are
  allocated in arrival order and the two KBs are compared on what they believe, not on
  where they put it."
  [e]
  [(:kind e) (:priority e) (:sentence e)
   (into #{} (map (juxt :sentence :context :defeat-class)) (:sides e))])

(defn- snapshot [kb]
  {:believed   (into #{}
                     (comp (keep #(p/get-sentex (:records kb) %))
                           (map (juxt v/sentence-of :context)))
                     (jtms/in-datums (reasoning/tms kb)))
   :dilemmas   (into #{} (map clash-key) (v/contradictions kb))
   :conflicts  (into #{} (map clash-key) (v/conflicts kb))
   :violations (into #{} (map :violation) (v/violations kb))})

(defn- diff [a b]
  (into {} (keep (fn [k]
                   (let [x (get a k) y (get b k)]
                     (when (not= x y)
                       [k {:incremental-only (set/difference x y)
                           :exhaustive-only  (set/difference y x)}]))))
        (keys a)))

;; ---- oracle 1: randomized operation streams -----------------------------

(defn- run-trial
  "The same op stream into both KBs, comparing after every write.  Returns
  `[step op incremental-snapshot exhaustive-snapshot]` for the first divergence, or nil."
  [seed steps]
  (let [inc-kb (tu/fresh)
        exh-kb (tu/isolated-fresh)]
    (try
      (binding [checks/*arbitrate-constraints?* true]
        (binding [settle/*incremental-clashes* true]  (build-ontology! inc-kb))
        (binding [settle/*incremental-clashes* false] (build-ontology! exh-kb))
        (let [rng (java.util.Random. (long seed))]
          (loop [step 0]
            (if (= step steps)
              nil
              (let [op (rand-op rng)
                    ri (binding [settle/*incremental-clashes* true]  (apply-op! inc-kb op))
                    re (binding [settle/*incremental-clashes* false] (apply-op! exh-kb op))
                    si (snapshot inc-kb)
                    se (snapshot exh-kb)]
                (if (and (= ri re) (= si se))
                  (recur (inc step))
                  [step op si se]))))))
      (finally (tu/clear-kb! inc-kb) (tu/clear-kb! exh-kb)))))

(defn- stream-reading
  "One KB's reading after `steps` of `seed`'s stream, on whatever retrieval strategy is
  bound around the call."
  [seed steps]
  (let [kb (tu/fresh)]
    (try
      (binding [checks/*arbitrate-constraints?* true
                settle/*incremental-clashes*    true]
        (build-ontology! kb)
        (let [rng (java.util.Random. (long seed))]
          (dotimes [_ steps] (apply-op! kb (rand-op rng))))
        (snapshot kb))
      (finally (tu/clear-kb! kb)))))

(deftest the-retrieval-strategy-does-not-change-what-clashes
  ;; `res/*hierarchical-retrieval*` picks how a context-scoped literal is answered, and
  ;; is documented as a pure cost decision that must never change the answer *set*.  It
  ;; kept that promise and the clash reading diverged anyway: `matches-visible` is
  ;; type-aware, so `(animal CI2)` comes back beside the `(dog CI2)` that implies it, the
  ;; two paths enumerate that set in two orders, and `checks/membership-handle` named
  ;; whichever came first — so the side a clash was *reported as*, and through
  ;; arbitration what the KB believed, turned on a cost flag.
  ;;
  ;; A **default-suite** test on purpose, for the reason `backend_parity_test` gives for
  ;; being one: the thorough gate is the whole suite under `VAELII_HIER=0`, and the only
  ;; workflow that sets it is `deep.yml`, which runs weekly rather than on a pull
  ;; request.  This fails in an ordinary `lein test` the day the two paths disagree
  ;; again, which is a week earlier than the sweep would say so.
  (doseq [seed (range 4)]
    (is (= (binding [res/*hierarchical-retrieval* true]  (stream-reading seed 24))
           (binding [res/*hierarchical-retrieval* false] (stream-reading seed 24)))
        (str "seed " seed ": the retrieval strategy changed the clash reading"))))

(deftest the-lead-side-does-not-change-what-clashes
  ;; The clash reading also flows through `checks/membership-handles`, whose lead
  ;; (`res/*lead-side*`) is a pure cost decision exactly as `*hierarchical-retrieval*` is:
  ;; `:scoped` reads the `matches-visible` reference (specs walked down), `:auto`/`:agnostic`
  ;; lead from the term's own postings.  A clash is reported *with* a handle that function
  ;; names and arbitration turns belief on it, so a lead that changed the answer set — or
  ;; its content-order choice among entailing memberships — would change what the KB
  ;; believes.  The three readings must be identical, on the same default-suite reasoning
  ;; the sibling test above gives.
  (doseq [seed (range 4)]
    (let [scoped   (binding [res/*lead-side* :scoped]   (stream-reading seed 24))
          auto     (binding [res/*lead-side* :auto]     (stream-reading seed 24))
          agnostic (binding [res/*lead-side* :agnostic] (stream-reading seed 24))]
      (is (= scoped auto agnostic)
          (str "seed " seed ": the lead side changed the clash reading"
               "\n  scoped vs auto:     " (pr-str (diff scoped auto))
               "\n  scoped vs agnostic: " (pr-str (diff scoped agnostic)))))))

(deftest ^:slow randomized-streams-discover-the-same-clashes
  (doseq [seed (range 12)]
    (let [[step op si se] (run-trial seed 45)]
      (is (nil? step)
          (str "seed " seed " diverged at step " step " on " (pr-str op) "\n"
               (pr-str (diff si se)))))))

(deftest a-seeded-stream-discovers-the-same-clashes
  ;; One seed of the `^:slow` sweep above, so `:default` runs its harness; the sweep
  ;; takes twelve.
  (let [[step op si se] (run-trial 0 45)]
    (is (nil? step)
        (str "seed 0 diverged at step " step " on " (pr-str op) "\n" (pr-str (diff si se))))))

;; ---- oracle 2: the retroactive declaration ------------------------------
;;
;; The narrowing most likely to be wrong, isolated: a separation arriving over content
;; stored long before it.  Neither membership is in the settle's region and the pair is
;; not yet remembered, so the *only* thing that finds it is the sweep — and a randomized
;; stream that happened not to generate this shape would report a clean run.

(deftest a-separation-arriving-last-finds-what-it-convicts
  (let [[step op si se]
        (let [inc-kb (tu/fresh)
              exh-kb (tu/isolated-fresh)]
          (try
            (binding [checks/*arbitrate-constraints?* true]
              (binding [settle/*incremental-clashes* true]  (build-ontology! inc-kb))
              (binding [settle/*incremental-clashes* false] (build-ontology! exh-kb))
              (let [pool inds
                    ops  (concat
                          ;; a dozen settles' worth of unrelated traffic, so the two
                          ;; memberships are long out of the region by the time the
                          ;; declaration lands
                          (for [x pool] [:assert (list 'dog x) (first ctxs) {}])
                          (for [x pool] [:assert (list 'cat x) (first ctxs) {}])
                          (for [x pool]
                            [:assert (list 'parentOf x (first pool)) (first ctxs) {}])
                          [[:assert '(disjoint dog cat) (first ctxs) {:strength :monotonic}]]
                          ;; and one more settle after it, which is where a pair that was
                          ;; found once and then dropped would silently vanish
                          [[:assert (list 'plant (first pool)) (first ctxs) {}]])]
                (loop [step 0 [op & more] ops]
                  (if-not op
                    nil
                    (let [ri (binding [settle/*incremental-clashes* true]
                               (apply-op! inc-kb op))
                          re (binding [settle/*incremental-clashes* false]
                               (apply-op! exh-kb op))
                          si (snapshot inc-kb)
                          se (snapshot exh-kb)]
                      (if (and (= ri re) (= si se))
                        (recur (inc step) more)
                        [step op si se]))))))
            (finally (tu/clear-kb! inc-kb) (tu/clear-kb! exh-kb))))]
    (is (nil? step)
        (str "diverged at step " step " on " (pr-str op) "\n" (pr-str (diff si se))))))

;; ---- oracle 3: the carry-forward, under a moving vocabulary -------------
;;
;; A pair is carried forward when neither member moved *and* the clash vocabulary is
;; unchanged.  The second half is the one with a long reach: a `genl` edge can make two
;; standing memberships clash without either of them being written, and a retracted
;; separation can stop a standing pair clashing the same way.  Both are vocabulary
;; movements over pairs whose members sit perfectly still.

(deftest vocabulary-moving-under-standing-content-agrees
  (let [inc-kb (tu/fresh)
        exh-kb (tu/isolated-fresh)
        ops    [;; content first, and nothing about it moves again
                [:assert '(dog CI0)   'CxClashBase {}]
                [:assert '(snake CI0) 'CxClashBase {}]
                [:assert '(dog CI1)   'CxClashBase {}]
                [:assert '(cat CI1)   'CxClashBase {}]
                ;; …then the vocabulary moves under it, twice
                [:assert '(genl snake reptile) 'CxClashBase {:strength :monotonic}]
                [:assert '(disjoint dog cat)   'CxClashBase {:strength :monotonic}]
                ;; a settle that touches neither pair: both must still be reported
                [:assert '(plant CI4) 'CxClashBase {}]
                ;; and the separations leaving again
                [:retract '(disjoint dog cat) 'CxClashBase]
                [:retract '(genl snake reptile) 'CxClashBase]
                [:assert '(plant CI5) 'CxClashBase {}]]]
    (try
      (binding [checks/*arbitrate-constraints?* true]
        (binding [settle/*incremental-clashes* true]  (build-ontology! inc-kb))
        (binding [settle/*incremental-clashes* false] (build-ontology! exh-kb))
        (doseq [[i op] (map-indexed vector ops)]
          (let [ri (binding [settle/*incremental-clashes* true]  (apply-op! inc-kb op))
                re (binding [settle/*incremental-clashes* false] (apply-op! exh-kb op))
                si (snapshot inc-kb)
                se (snapshot exh-kb)]
            (is (= ri re) (str "step " i " " (pr-str op) ": refusal differs"))
            (is (= si se) (str "step " i " " (pr-str op) ": " (pr-str (diff si se)))))))
      (finally (tu/clear-kb! inc-kb) (tu/clear-kb! exh-kb)))))

;; ---- oracle 4: a genl edge, weighed per pair ----------------------------
;;
;; The vocabulary above is compared as a value; the `genl` relation is not, and cannot be
;; — it is the one part of what decides a clash that is too big to compare.  So the carry
;; is abandoned per pair instead, on what the pair's own types read through that closure
;; (`settle/genl-view`), and the three claims that reading makes are each its own case.
;; Oracle 3 reaches none of them: its edge is under a type its standing pair names, so any
;; test at all — a counter included — gets it right.

(defn- directed-stream
  "A fixed op sequence into both KBs, compared after every write.  The randomized stream
  above draws from one vocabulary; these draw the shape they are about."
  [ops]
  (let [inc-kb (tu/fresh)
        exh-kb (tu/isolated-fresh)]
    (try
      (binding [checks/*arbitrate-constraints?* true]
        (binding [settle/*incremental-clashes* true]  (build-ontology! inc-kb))
        (binding [settle/*incremental-clashes* false] (build-ontology! exh-kb))
        (doseq [[i op] (map-indexed vector ops)]
          (let [ri (binding [settle/*incremental-clashes* true]  (apply-op! inc-kb op))
                re (binding [settle/*incremental-clashes* false] (apply-op! exh-kb op))
                si (snapshot inc-kb)
                se (snapshot exh-kb)]
            (is (= ri re) (str "step " i " " (pr-str op) ": refusal differs"))
            (is (= si se) (str "step " i " " (pr-str op) ": " (pr-str (diff si se))))))
        (v/contradictions inc-kb))
      (finally (tu/clear-kb! inc-kb) (tu/clear-kb! exh-kb)))))

(deftest a-genl-edge-elsewhere-leaves-a-standing-pair-alone
  ;; Edges arriving and leaving under types the standing pair does not name.  Nothing it
  ;; reads has moved, so nothing about it may move — and the pair is still there at the
  ;; end, which is the half a memo that silently dropped everything would also pass.
  (let [cs (directed-stream
            [;; a standing pair on `mammal` / `reptile`, and nothing about it moves again
             [:assert '(mammal CI0)  'CxClashBase {}]
             [:assert '(reptile CI0) 'CxClashBase {}]
             ;; edges arriving and leaving under types the pair does not name
             [:assert '(genl snake reptile) 'CxClashBase {:strength :monotonic}]
             [:assert '(genl plant thing)   'CxClashBase {:strength :monotonic}]
             [:assert '(cat CI3) 'CxClashBase {}]
             [:retract '(genl plant thing) 'CxClashBase]
             [:retract '(genl snake reptile) 'CxClashBase]
             [:assert '(cat CI4) 'CxClashBase {}]])]
    (is (= 1 (count cs))
        "the pair the edges were never about is still the one standing dilemma")))

(deftest a-genl-edge-the-pair-rests-on-withdraws-it-when-it-goes
  ;; `(disjoint animal plant)` separates nothing about `dog` until `dog` is under
  ;; `animal` — which it is, two edges up.  So the clash between `(dog CI0)` and
  ;; `(plant CI0)` rests on `(genl mammal animal)`, a type **neither sentence names**, and
  ;; retracting it must withdraw the pair with nothing stored, removed or relabelled on
  ;; either member.  A per-pair reading that stopped at the two functors rather than at
  ;; their closures would carry it for the rest of the KB's life.
  (directed-stream
   [[:assert '(dog CI0)   'CxClashBase {}]
    [:assert '(plant CI0) 'CxClashBase {}]
    ;; a settle that touches neither, so the pair is standing rather than arriving
    [:assert '(cat CI3) 'CxClashBase {}]
    ;; ...and the edge the separation reaches `dog` through goes
    [:retract '(genl mammal animal) 'CxClashBase]
    [:assert '(cat CI4) 'CxClashBase {}]
    ;; and comes back, so the pair has to be found a second time
    [:assert '(genl mammal animal) 'CxClashBase {:strength :monotonic}]
    [:assert '(cat CI5) 'CxClashBase {}]]))

(deftest an-edge-two-contexts-support-is-read-from-each-of-them
  ;; The scoped half of the same reading.  `(genl mammal animal)` is asserted from
  ;; `CxClashSub` as well, so one edge has two supporters and two asserting
  ;; contexts; retracting the base one leaves the edge **active** and visible from
  ;; `CxClashSub` alone.  So the relation as a whole did not move, while a pair in
  ;; the base context has stopped being separated through it and one in the sub context
  ;; has not — a reading taken globally and never checked against the asking context
  ;; would keep both.
  (directed-stream
   [[:assert '(genl mammal animal) 'CxClashSub {:strength :monotonic}]
    [:assert '(dog CI0)   'CxClashBase {}]
    [:assert '(plant CI0) 'CxClashBase {}]
    [:assert '(dog CI1)   'CxClashSub {}]
    [:assert '(plant CI1) 'CxClashSub {}]
    [:assert '(cat CI3) 'CxClashBase {}]
    ;; the base supporter goes; the sub one keeps the edge alive
    [:retract '(genl mammal animal) 'CxClashBase]
    [:assert '(cat CI4) 'CxClashBase {}]]))

(deftest a-metatype-member-leaving-withdraws-what-it-was-separating
  ;; The one ingredient of a separation that is neither a declaration nor a closure.
  ;; `(disjoint_metatype M)` separates M's members by being **consulted** — no `(disjoint
  ;; a b)` is ever written — so `(M b_t)` leaving stops separating `a_t` from `b_t` while
  ;; the mark is still there, the two closures still read the same, and neither member of
  ;; the standing pair is in the region.  Nothing else in the KB moves, which is exactly
  ;; what makes it the case a staleness test can miss.
  ;;
  ;; A member *arriving* is its own sentex and reaches its pairs through the retroactive
  ;; sweep, so the two directions do not check the same thing and both are here.
  (let [kb  (tu/fresh)
        exh (tu/isolated-fresh)
        ops [[:assert '(disjoint_metatype clsh_kind_t) 'CxClashBase {:strength :monotonic}]
             [:assert '(clsh_kind_t clsh_a_t) 'CxClashBase {:strength :monotonic}]
             [:assert '(clsh_a_t CI0) 'CxClashBase {}]
             [:assert '(clsh_b_t CI0) 'CxClashBase {}]
             ;; the member arrives over content already stored, and must reach it
             [:assert '(clsh_kind_t clsh_b_t) 'CxClashBase {:strength :monotonic}]
             ;; a settle that touches neither member of the pair
             [:assert '(plant CI4) 'CxClashBase {}]
             ;; ...and the member goes again, with the mark still standing
             [:retract '(clsh_kind_t clsh_b_t) 'CxClashBase]
             [:assert '(plant CI5) 'CxClashBase {}]]]
    (try
      (binding [checks/*arbitrate-constraints?* true]
        (doseq [[i op] (map-indexed vector ops)]
          (let [ri (binding [settle/*incremental-clashes* true]  (apply-op! kb op))
                re (binding [settle/*incremental-clashes* false] (apply-op! exh op))]
            (is (= ri re) (str "step " i " " (pr-str op) ": refusal differs"))
            (is (= (snapshot kb) (snapshot exh))
                (str "step " i " " (pr-str op) ": "
                     (pr-str (diff (snapshot kb) (snapshot exh)))))))
        (is (zero? (count (v/contradictions kb)))
            "with the member gone the two types are separated by nothing"))
      (finally (tu/clear-kb! kb) (tu/clear-kb! exh)))))

(deftest the-contradictions-list-is-ordered-by-content-not-arrival
  ;; `clash-report` orders the sides *inside* a report by content; the list one level
  ;; up came off a hash set of handle-keyed nogoods, so `(first (contradictions kb))`
  ;; — and any golden file or UI list over it — read whichever pair was typed first.
  ;; Three independent dilemmas, two assertion orders: the whole vector must agree,
  ;; position by position, when read through content rather than handles.
  (let [pairs  '[[(clsh_p CA) (not (clsh_p CA))]
                 [(clsh_q CB) (not (clsh_q CB))]
                 [(clsh_r CC) (not (clsh_r CC))]]
        read!  (fn [sentences]
                 (let [kb (tu/fresh)]
                   (try
                     (doseq [s sentences] (v/assert kb s 'CxClashBase))
                     (mapv (fn [r] (mapv :sentence (:sides r))) (v/contradictions kb))
                     (finally (tu/clear-kb! kb)))))
        fwd    (read! (apply concat pairs))
        rev    (read! (apply concat (reverse pairs)))
        rot    (read! (apply concat (take 3 (drop 1 (cycle pairs)))))]
    (is (= 3 (count fwd)) "three standing dilemmas")
    (is (= fwd rev rot) "every assertion order publishes one list")
    (is (= fwd (vec (sort-by pr-str fwd))) "and it is the content order, stated directly")))

(deftest a-sides-derivations-are-ordered-by-content-not-arrival
  ;; The same claim one level in.  A report orders its *sides* by content; the
  ;; derivations listed inside a side come off `jtms/supports`, which is a set of
  ;; allocation-ordered ids — so a side two rules concluded reads back in the order the
  ;; two firings happened to land.  Which derivation leads is what an application ranking
  ;; the argument shows first, and a caller comparing two reports is comparing the two
  ;; KBs' typing order along with everything else.
  ;;
  ;; One dilemma, one side of it derived twice, two assertion orders.  Read by content
  ;; throughout: the handles are what may legitimately differ between the two, so the
  ;; informant and the antecedents are named by their sentences.
  ;;
  ;; **The two arms share one term set**, exactly as `the-report-is-the-same-in-either-
  ;; arrival-order` in `exposure-test` does: the readings are compared as values, so an
  ;; arm-local `with-terms` would make them differ for a reason that has nothing to do
  ;; with order.  So the temporaries are minted once, outside `read!`.
  (tu/with-terms [seenA seenB derivedQ Subject CxBase]
    (let [ops   {:fA  #(v/assert % (list seenA Subject) CxBase)
                 :fB  #(v/assert % (list seenB Subject) CxBase)
                 :r1  #(v/assert-rule % [(list seenA '?x)] (list derivedQ '?x) CxBase {:direction :forward})
                 :r2  #(v/assert-rule % [(list seenB '?x)] (list derivedQ '?x) CxBase {:direction :forward})
                 :neg #(v/assert % (list 'not (list derivedQ Subject)) CxBase)}
          sent  (fn [kb x] (if (integer? x) (v/sentence-of (v/sentex kb x)) x))
          read! (fn [order]
                  (let [kb (tu/fresh)]
                    (try
                      (doseq [o order] ((ops o) kb))
                      (mapv (fn [report]
                              (mapv (fn [side]
                                      [(:sentence side)
                                       (mapv (fn [j] [(sent kb (:informant j))
                                                      (mapv #(sent kb %) (:antecedents j))])
                                             (:justifications side))])
                                    (:sides report)))
                            (v/contradictions kb))
                      (finally (tu/clear-kb! kb)))))
          fwd   (read! [:r1 :r2 :fA :fB :neg])
          rev   (read! [:neg :fB :fA :r2 :r1])]
      (is (= 1 (count fwd)) "one standing dilemma")
      (is (some (fn [[_ js]] (= 2 (count js))) (first fwd))
          "and one side of it is derived twice — else there is no list to order")
      (is (= fwd rev) "every assertion order publishes one reading"))))

;; ---- the argument-root readers are total --------------------------------

(deftest a-sentence-with-no-arity-on-an-argument-root-is-skipped-not-counted
  ;; `holds-two-members?` walks the postings at a term's own argument-1 root and asks each
  ;; sentence its arity.  Its three siblings on the same walk guard that with `sequential?`;
  ;; a sentence with no arity reaches `count` otherwise and throws
  ;; `UnsupportedOperationException` out of the settle, which is a mutation refused by
  ;; exception rather than a posting declined.
  ;;
  ;; Driven through `reify` stores rather than a redef, because a protocol-method redef
  ;; never intercepts a compiled `(p/method inst …)` call (testing.md).
  (let [tms (jtms/create-tms)
        recs #_{:clj-kondo/ignore [:missing-protocol-method]}
        (reify p/RecordStore
          (get-sentex [_ id]
            (case (long id)
              1 {:id 1 :sentence 'clshArityless    :context 'CxUniverse}
              2 {:id 2 :sentence '(clsh_member CK)  :context 'CxUniverse}
              nil)))
        idx #_{:clj-kondo/ignore [:missing-protocol-method]}
        (reify p/IndexStore
          (sentexes-with-arg [_ _pos _term] [1 2]))
        fake {:records recs :index idx :reasoning (volatile! {:tms tms})}]
    (jtms/add-premise tms 1 :monotonic)
    (jtms/add-premise tms 2 :monotonic)
    (is (false? (@#'settle/holds-two-members? fake '{clsh_member #{clsh_member}} 'CK))
        "the arity-less posting is skipped, and one real membership is not two members")))
