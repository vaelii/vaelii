;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.rete
  "Incremental forward-chaining match — a TREAT-style alpha network.

  The reference forward chainer (`vaelii.impl.chain`) is semi-naive: a new fact seeds
  the agenda, candidate rules are found by the rule index, and each candidate's
  non-trigger antecedents are re-joined against the store on every assert.  That
  re-join goes through `res/match-pattern`, which walks the **count-aware trie** —
  and the trie narrows strictly left to right, so a non-trigger antecedent with a
  *leading variable* (`(parentOf ?x Pi)`, the second half of a grandparent join) has
  no selective prefix.  The **secondary argument roots** answer that shape on the
  reference path, in one predicate-scoped set read (`res/*arg-root-retrieval*`, on by
  default, docs/indexing.md).

  This namespace keeps **alpha memories** in RAM — the stored facts grouped by
  functor and indexed by argument value — and answers a non-trigger antecedent with
  a hash lookup on its most selective ground argument: `(parentOf ?x Pi)` reads the
  bucket of facts with `Pi` in position 2 directly.

  What that is worth depends on the rule shape.  On the grandparent load
  (`lein bench-forward`) the two paths are level from n=2000 up, both flat at
  ~500µs/fact — the argument roots already answer what the alpha memories would.  On
  the OpenRuleBench join pyramid (`vaelii.bench.pyramid` at join.1k, C2, six
  interleaved runs a side) the alpha memories hold a thin lead on the identical
  answer set: 11.8s against 12.5s.  The predicate-scoped argument roots answer the
  same leading-variable shape with one bucket read of the literal's own predicate
  (docs/indexing.md), which is why the two candidate sources sit close; matching is
  ~12% of the run (`vaelii.bench.pyramid`'s `profile` mode measures it) and placement
  is the rest, which bounds what any matcher moves there.

  ## Correctness by reuse, not by reimplementation

  The one and only novelty here is *which stored facts a non-trigger antecedent
  finds*.  Everything else — the semi-naive agenda, the trigger match (`match1`),
  context placement, `exceptWhen` blocking, the definitional checks on the derivation
  path, justification dedup, functional-equality twins, the depth guard — is the
  reference's, reached by binding one seam (`chain/*matcher*`) and calling
  `chain/chain-all` unchanged.  So the network cannot diverge in *any* of those; it
  can only diverge in the match, and `rete-match-pattern` is written to return the
  **identical set** `res/match-pattern` returns — same belief filter, same
  polarity check, same symmetric mirror, same sub-predicate fan-out, same `?ctx`
  binding — differing only in the candidate source (a RAM bucket, a superset of the trie hits,
  filtered by the identical `unify`).  `rete_oracle_test` pins that equality directly
  (per pattern) and end to end (the derived sentex + justification sets over randomized
  assert/retract sequences must match the reference `chain`).

  ## The alpha memories

  A per-KB atom, `{:by-functor {f {:all {id sentex}
                                    :by-arg {[pos val] {id sentex}}}}}`.  Only ground
  **facts** live here (rules are matched by the rule index, not as facts, and never
  appear among a fact pattern's trie hits).  Belief is *not* baked in: a datum stays
  in its memory when it is defeated or superseded, and `in?` is consulted at read
  time exactly as `match-one` does — so a belief flip needs no memory update, and the
  only structural mutations are a stored fact arriving (`kb/create-sentex`) or leaving
  (`integrate/sentex-removed!`), routed here through `vaelii.impl.observe`.  Subtype
  and symmetric resolution also happen at read time (over the live taxonomy), so a
  `genl` or `symmetric` edge change needs no memory update either.

  See docs/inference.md, \"Incremental rule matching\"."
  (:require [vaelii.impl.chain :as chain]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]))

;; ---- the per-KB alpha registry ------------------------------------------
;; Keyed by KB **object identity**, not value: two KBs over the same space
;; can be `=` (their record stores wrap the same shared state) but must not share an
;; alpha.  A `java.util.IdentityHashMap` keys on `==`.
;;
;; Synchronized, unlike the alphas it holds.  The engine is single-writer and each alpha
;; is an atom, but this map is JVM-lifetime shared state reached from the store observer
;; hooks — which fire on whichever thread is writing — and a `HashMap` racing its own
;; rehash does not merely lose an entry: a reader can spin on a probe loop that never
;; terminates.  The cost is one uncontended monitor per lookup against a map with as many
;; entries as the process has live KBs.
(defonce ^:private ^java.util.Map registry
  (java.util.Collections/synchronizedMap (java.util.IdentityHashMap.)))

(defn- index-functor
  "The functor a fact is bucketed under: the functor of its positive atomic body, so
  a negative fact `(not (parentOf A B))` roots under `parentOf` — exactly as the store's
  `[:functor-root pred]` functor root does, and as a positive antecedent pattern will look for."
  [sentex]
  (nm/functor (sx/body sentex)))

(defn- ground-arg-buckets
  "The `[[pos val] …]` bucket keys a **fact** contributes: one per 1-based argument
  position of its positive body (facts are ground, so every position is a bucket)."
  [sentex]
  (keep-indexed (fn [i a] [(inc i) a]) (nm/args (sx/body sentex))))

(defn- alpha-add* [state sentex h]
  (if (rules/rule? sentex)
    state                                   ; rules are not matched as facts
    (if-let [f (index-functor sentex)]
      (-> (reduce (fn [st k] (assoc-in st [:by-functor f :by-arg k h] sentex))
                  state
                  (ground-arg-buckets sentex))
          (assoc-in [:by-functor f :all h] sentex))
      state)))

(defn- alpha-remove* [state sentex]
  (if (rules/rule? sentex)
    state
    (if-let [f (index-functor sentex)]
      (let [h (:id sentex)]
        (-> (reduce (fn [st k]
                      (update-in st [:by-functor f :by-arg k] dissoc h))
                    state
                    (ground-arg-buckets sentex))
            (update-in [:by-functor f :all] dissoc h)))
      state)))

(defn- sync-from-store!
  "Build `alpha` from every fact currently in `kb`'s record store — the one-time
  backfill so an alpha born after facts already exist still sees them.  Idempotent
  (keyed by id), so re-running it or racing an observer add cannot double-count."
  [kb alpha]
  (swap! alpha
         (fn [state]
           (reduce (fn [st id]
                     (if-let [s (p/get-sentex (:records kb) id)]
                       (alpha-add* st s id)
                       st))
                   state
                   (p/sentex-ids (:records kb))))))

(defn- alpha-for
  "This KB's alpha memories, built (and back-filled from the store) on first use."
  [kb]
  (or (.get registry kb)
      ;; Check, put and back-fill are one step: two callers racing here would each build
      ;; an alpha, and the loser's would be handed to its caller and then never updated
      ;; again — the observer hooks maintain whichever one the map holds.  The put stays
      ;; *before* the back-fill so a hook firing during the scan finds the alpha it is
      ;; meant to maintain, and the scan runs under the monitor so nobody is handed a
      ;; half-filled one.  Paid once per KB.
      (locking registry
        (or (.get registry kb)
            (let [a (atom {:by-functor {}})]
              (.put registry kb a)
              (sync-from-store! kb a)
              a)))))

;; ---- the observer hooks (installed by `engage!`) ------------------------
;; `engage!` is here because `track!` below it engages before it runs.  Its undo is not:
;; `disengage!` is a no-op while the global switch is on, so it reads `enabled?` and lives
;; with the switch at the foot of the file.

(defn- observe-add [kb sentex h]
  (when-let [a (.get registry kb)]        ; only maintain alphas that already exist
    (swap! a alpha-add* sentex h)))

(defn- observe-remove [kb sentex]
  (when-let [a (.get registry kb)]
    (swap! a alpha-remove* sentex)))

(defn engage!
  "Install the store observers so every alpha stays in step with the fact set.
  Idempotent.  Called by `track!` before it runs, by `enable!` when the switch goes on,
  and directly by the oracle test."
  []
  (when-not (observe/installed?)
    (observe/install! observe-add observe-remove)))

;; ---- the matcher: identical result set to `res/match-pattern` ---------

(defn- candidates
  "The stored facts to unify against `pat` (a canonicalized pattern sentex), read from
  the alpha memories.  A **superset** of `res/match-one`'s trie hits — the same set
  after the identical `unify` filter below — chosen selectively: the smallest bucket
  among the pattern's ground argument positions, or the whole functor extent when the
  pattern pins no argument.  A ground position whose bucket is empty means zero
  matches, which the min naturally returns."
  [by-functor pat]
  (let [pbody (sx/body pat)                       ; positive atomic body of the pattern
        f     (nm/functor pbody)]
    (cond
      ;; a variable (or absent) functor pins nothing — every fact is a candidate, as
      ;; the trie's wildcard root fan-out is; rare (a variable-predicate antecedent)
      (or (nil? f) (sx/variable? f))
      (mapcat (comp vals :all) (vals by-functor))

      :else
      (let [fb      (get by-functor f)
            ground  (keep-indexed (fn [i a] (when (sx/ground-term? a) [(inc i) a]))
                                  (nm/args pbody))]
        (cond
          (nil? fb)      nil
          (empty? ground) (vals (:all fb))
          :else          (->> ground
                              (map #(get-in fb [:by-arg %] {}))
                              (apply min-key count)
                              vals))))))

(defn- match-one-via-alpha
  "The RAM twin of `res/match-one`: same belief filter, same polarity check, same
  context unification (so a wildcard `?ctx` picks up the fact's context into the
  bindings exactly as the reference does).  Only the candidate source differs."
  [kb by-functor sentence context]
  (let [pat (res/kb-sentex kb sentence context)]
    (keep (fn [stored]
            ;; the exceptWhen guard is the reference's too (`res/match-one`): a rule's
            ;; exception meta-sentex is internal bookkeeping, stored Literal and so
            ;; admitted into the alpha memories, and must never surface as a fact
            (when (and (jtms/in? (:tms kb) (:id stored))
                       (not (sx/exceptWhen-meta? (:sentence stored))))
              (when (= (:truth pat) (:truth stored))
                (when-let [b (res/unify (:context pat) (:context stored)
                                        (res/unify (:sentence pat) (:sentence stored)))]
                  [(:id stored) b]))))
          (candidates by-functor pat))))

(defn- raw-match-via-alpha
  "The RAM twin of `res/raw-match`: one literal context, both argument orders for a
  symmetric predicate, **deduped by handle *and bindings***.  Keying on the handle
  alone drops the second answer an all-variable pattern gets from one stored fact —
  `(sibOf ?a ?b)` binds `(sibOf Rex Tib)` directly and again, differently, through
  the mirror — and a join led by such a literal then sees one orientation.  See
  `res/raw-match` for the whole of that reasoning; this must key it identically.

  Lazy through the mirror, as the reference is: the second probe and its `seen` set
  are deferred, so a consumer answered by the direct hits pays for neither."
  [kb by-functor sentence context]
  (let [hits (match-one-via-alpha kb by-functor sentence context)]
    (if (sx/symmetric-literal? sentence #(tax/has-prop? (:taxonomy kb) :symmetric %))
      (lazy-cat hits
                (let [seen (into #{} (map (fn [[h b]] [h b])) hits)]
                  (remove (fn [[h b]] (contains? seen [h b]))
                          (match-one-via-alpha kb by-functor (sx/mirror-literal sentence)
                                               context))))
      hits)))

(defn- match-pattern-via-alpha
  "The RAM twin of `res/match-pattern`: the functor fans out over its sub-predicate
  (genl spec) closure at **every arity** — a unary type literal over its subtypes, an
  n-ary literal over its predicate-genl specs — and a functor with a singleton closure
  is one raw match, which is the common case.  A variable or absent functor pins
  nothing and fans not at all, as the reference's does.  A **negation** fans its body's
  functor over the genl closure instead, the direction a `genl` edge carries through a
  negation, and rebuilds the `not` around each member."
  [kb by-functor sentence context]
  ;; the fan itself is the reference matcher's, not a copy of it — `res/fanned-match`
  ;; decides the decomposition, the direction a negation fans and the singleton
  ;; short-circuit, and this twin supplies only what is actually its own: the alpha-index
  ;; retrieval, and an eager `mapcat` where `match-pattern` wants a lazy one.  `chain`
  ;; only ever joins at `'?ctx`, so the closure here is the global one.
  (res/fanned-match kb sentence context
                    (fn [s] (raw-match-via-alpha kb by-functor s context))
                    mapcat))

(defn rete-match-pattern
  "The matcher `chain/*matcher*` is bound to when the network is engaged.  Signature
  and result are `res/match-pattern`'s — `(kb pattern context) -> ([handle bindings] …)`
  — answered from this KB's alpha memories."
  [kb pattern context]
  (match-pattern-via-alpha kb (:by-functor @(alpha-for kb)) pattern context))

;; ---- driving a KB through the network -----------------------------------
;; Two ways in, and neither wraps `chain`: `enable!` root-binds the matcher for the
;; process (the `VAELII_RETE=1` sweep), and `track!` plus the caller's own `binding`
;; scopes it to one KB (`vaelii.bench.pyramid`).  The scoped form stays the caller's to
;; write, because the caller is the one deciding what runs inside the binding — a
;; convenience that engaged, tracked and chained in one call would fix that choice for
;; them, and fix it to the one chain entry point it happened to name.

(defn track!
  "Engage the observers and materialize `kb`'s alpha memories now, so every fact
  `kb` already holds and every one it gains from here is in the memories.  After
  this, any operation on `kb` run under `(binding [chain/*matcher* rete-match-pattern] …)`
  is matched incrementally.  Exposed for tests and for a caller driving one KB
  through the network without flipping the global default."
  [kb]
  (engage!)
  (alpha-for kb)
  nil)

;; ---- the global switch (mirrors plan/*enabled*) -------------------------

(defn enable!
  "Route **all** forward chaining through the incremental matcher by installing it as
  `chain/*matcher*`'s root and engaging the observers.  Off by default: the reference
  matcher is the root, and this is the one switch that replaces it globally.  The
  oracle and the whole suite run through it (`VAELII_RETE=1 lein test`)."
  []
  (engage!)
  (alter-var-root #'chain/*matcher* (constantly rete-match-pattern)))

(defn enabled?
  "Is the incremental matcher currently installed as the global default?"
  []
  (identical? chain/*matcher* rete-match-pattern))

(defn disengage!
  "Uninstall the observers and drop every alpha, so the store choke points do nothing
  extra and the reference path is exactly as before.  A **no-op while the matcher is
  the global default** (`enable!`): a caller that merely `track!`ed one KB must not
  tear the network out from under a globally-enabled engine.

  The undo of `engage!`, and placed here rather than beside it because that no-op is the
  whole of its contract: it reads `enabled?`, which reads the matcher defined above."
  []
  (when-not (enabled?)
    (observe/uninstall!)
    (.clear registry)))

(defn disable!
  "Restore the reference trie matcher and drop the observers/alphas."
  []
  (alter-var-root #'chain/*matcher* (constantly res/match-pattern))
  (disengage!))
