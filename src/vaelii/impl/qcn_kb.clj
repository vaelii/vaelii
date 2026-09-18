;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.qcn-kb
  "The KB glue every relation algebra over `vaelii.impl.qcn` shares — reading believed
  facts into a network, and reading entailments back out as prover solutions.

  `qcn` itself knows nothing about a KB: an algebra is a parameter and a network is a
  value.  This namespace is the other half of that boundary, and it is the *same* half for
  every calculus, so it is written once here rather than three times over.  A **calculus**
  bundles what actually differs:

    {:name        a keyword, naming the cache and the parity oracle
     :algebra     the `qcn` relation algebra
     :denotation  {predicate -> #{base relations}} — base ones are the singletons,
                  derived ones the wider disjunctions
     :narrowing   an optional second reader (below), nil for a calculus that has none}

  Everything else — the reader, the two caches, the four goal shapes, the cost and
  completeness declarations — follows from those three.  `vaelii.impl.space`,
  `vaelii.impl.orientation` and `vaelii.impl.interval` each define an algebra and a
  vocabulary and call `calculus`; a fourth would be the same.

  **A narrowing is a second reader of the same network.**  Stored facts of the calculus
  are one source of constraint on a pair, and they need not be the only one: the interval
  algebra takes a second from `vaelii.impl.stp`, where a metric bound between two
  intervals' endpoints rules Allen relations out that no stored fact mentions.  A
  narrowing answers `{:net … :support …}` in exactly the shape `build-network`
  accumulates, so folding it in is one intersection per pair and one support union — and
  everything downstream (the pass, the entailment reading, the support, the delta join) is
  unchanged, because what it consumes is still one network value.  Sound for the same
  reason intersecting two stored facts is: a narrowing only ever removes relations the
  constraints it read exclude, and a pair it leaves at the universe it does not record.

  Both polarities are read and both are answered.  A believed `(not (P a b))` narrows the
  pair by the **complement** of P's denotation, and a goal `(not (P a b))` is answered by
  **refutation** — `possible ∩ denotation(P) = ∅`, where the positive goal needs the
  stronger `possible ⊆ denotation(P)`.  Both are licensed by the base relations being
  jointly exhaustive and pairwise disjoint, which is what makes \"not P\" a constraint
  here rather than an absence of information.

  Three caches, and they answer different questions:

  * the **network is resident**, on the KB's own `:qcn` atom, keyed `[calculus context]`
    and stamped with `observe/change-clock` — so it is read out of the KB once and then
    reused until the engine actually mutates something.  Building it is one
    belief-filtered read per predicate of the calculus per polarity (twenty-eight of them
    for RCC-8), and it is asked for constantly: a rule joining a qualitative antecedent
    asks per binding, and every settle re-checks `entailment-withdrawn?` once per firing
    of every rule that mentions the calculus.  Those are stretches in which nothing
    mutates at all, which is exactly what the clock recognises.
  * the **path-consistency pass** is memoized on the network *value*, in an atom the
    calculus owns.  That is sound across queries because the network is derived from the
    believed facts: any change to them yields a different map and so a different key.
  * the **support-carrying pass** — which stored sentexes an entailed relation rests on —
    is memoized separately, on the same network value, so an ordinary query never pays to
    propagate support nobody asked for.

  Beside those, and not a cache at all, the resident atom carries the **join baseline**:
  the network a calculus's forward rules were last re-joined over, which is what lets the
  next re-join run over the pairs that moved instead of over every pair the network
  entails (`join-delta`).  It deliberately outlives a clock tick — its job is to describe a
  moment the clock has moved past — and it is safe to lose, since losing it costs a full
  re-join and nothing else."
  (:require [clojure.set :as set]
            [taoensso.trove :as trove]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.qcn :as qcn]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.impl.types.reasoning :as reasoning]))

(def ^:private pc-cache-limit 256)

;; `{name calculus}` for every calculus value built in this process — what the two cache
;; rows at the bottom of this file sum over.  Keyed by name so reloading a calculus's
;; namespace replaces its entry rather than doubling it, and a `defonce` so reloading
;; *this* one does not forget the calculi already built against it.
(defonce ^:private built-calculi (atom {}))

(defn calculus
  "Bundle an algebra and its vocabulary into the value every function here takes.
  `denotation` maps each stored predicate to the set of base relations it denotes, so its
  keys are the predicates the prover claims.

  `narrowing` is the optional second reader — nil for a calculus that has none:

    {:fn        (fn [kb context] → {:net … :support …} | nil)
     :sources   every predicate whose arrival or departure moves what it answers
     :contexts  the subset that puts a NODE in the network, so names a reader context}

  The two predicate sets differ, and deliberately.  A `conversionFactor` moves what a
  metric bound comes to and so must re-check the rules concerned, but a context holding
  one and nothing else has an *empty* interval network, and enumerating it as a reader
  would cost a network build per goal to entail nothing.  Both are folded once here rather
  than per call: `calculus-triggered-by` runs per asserted sentence, and computing a union
  there would allocate a set per assert.

  The value carries the two caches its passes fill, so it is also registered in
  `built-calculi` on the way out — that is how a reader can be told what they hold
  without every calculus namespace having to say so itself."
  ([nm algebra denotation] (calculus nm algebra denotation nil))
  ([nm algebra denotation narrowing]
   (let [answered (set (keys denotation))
         c {:name       nm
            ;; the algebra is carried exactly as written — a plain value a test can reason
            ;; about.  `qcn` compiles it to bitmasks on first use and caches that by the
            ;; algebra itself, so composition is a table read without the calculus
            ;; arranging for anything.
            :algebra    algebra
            :denotation denotation
            :predicates answered
            :narrowing  narrowing
            :trigger-predicates (into answered (:sources narrowing))
            :context-predicates (into answered (:contexts narrowing))
            :pc-cache   (atom {})
            ;; a **separate** cache for the support-carrying pass, keyed on the same
            ;; network value.  Not a second field of one entry: `tighten` is on every
            ;; query's hot path and support is asked for rarely, so sharing an entry would
            ;; make every query pay to propagate support nobody reads.  Two caches, each
            ;; filled only when its own question is asked, and both sound for the same
            ;; reason — the network is derived from the believed facts, so any change to
            ;; them is a different key.
            :support-cache (atom {})}]
     (swap! built-calculi assoc nm c)
     c)))

;; ---- reading the KB into a network --------------------------------------

(defn- pvar? [x] (sx/variable? x))

(defn- node-term?
  "A term usable as a network node: a symbol that is not a variable.  Regions, places and
  intervals are all ordinary individuals, so this is the whole test."
  [x]
  (and (symbol? x) (not (pvar? x))))

(defn- asserted-pairs
  "Every `[handle a b]` for which `(pred a b)` is believed and visible from `context` —
  one belief- and context-filtered prover-level read, so a defeated or invisible fact
  never reaches the network.  The handle rides along because a constraint's *support* is
  the sentexes that produced it (`network-support`)."
  [kb pred context]
  (for [m (res/matches-visible kb (list pred '?a '?b) context)
        :let [bnd (second m), a (get bnd '?a), b (get bnd '?b)]
        :when (and (node-term? a) (node-term? b))]
    [(first m) a b]))

(defn- refuted-pairs
  "Every `[handle a b]` for which `(not (pred a b))` is believed and visible from
  `context` — the negative half of the read, and the same shape as `asserted-pairs`.

  Read from the **functor root** rather than through a `(not (pred ?a ?b))` pattern.  A
  negative fact's trie key carries its whole body as a single token (`[:false (pred a b)
  ctx]`), so the trie answers a *ground* negative lookup and nothing else: an open one
  compares the token `(pred ?0 ?1)` against `(pred A B)` and matches nothing.  The
  functor root indexes either polarity under the positive body's functor, so it is the
  one index that enumerates them, and belief, context visibility and `except` removal are
  applied here exactly as `matches-visible` applies them to the positive read.

  It is the predicate's **own** extent, with no fan over the genl spec closure — and that
  is not an omission.  Subsumption runs the other way under negation: a negated
  *super*-predicate entails the negated sub, never the reverse, so the positive read's
  spec fan would be unsound here.  Nothing is lost, because a wider predicate's negation
  contributes its own (larger) complement when that predicate is read in its turn.

  Retired spellings are dropped with `res/retired-for?` rather than
  `res/without-retired`, because the triples here carry no sentex at index 2 for that
  filter to read — but they are dropped: a reader below a merge that keeps the
  negative fact about a retired spelling while the positive read drops it would carry
  one constraint under two names it knows denote one thing."
  [kb pred context]
  (let [ix       (:index kb)
        up       (when-not (pvar? context) (tax/context-up (reasoning/taxonomy kb) context))
        merged?  (tax/merged-term-pred (reasoning/taxonomy kb))
        visible  (delay (res/visible-supporter-fn kb context))
        retired? (if (and merged? (symbol? context) (not (pvar? context)))
                   #(res/retired-for? kb visible merged? (sx/sentence-of %))
                   (constantly false))]
    (->> (reads/as-stored-with-functor ix pred)
         (keep (fn [h]
                 (when (jtms/in? (reasoning/tms kb) h)
                   (let [s (p/get-sentex (:records kb) h)
                         b (when s (sx/body s))]
                     (when (and (sx/negative? s)
                                (sequential? b) (= 3 (count b)) (= pred (first b))
                                (or (nil? up) (contains? up (:context s)))
                                (not (retired? s)))
                       (let [[_ a c] b]
                         (when (and (node-term? a) (node-term? c)) [h a c])))))))
         (res/without-excepted kb context))))

(defn- narrow
  "Intersect the `[a b]` constraint of `net` with `rels` and the `[b a]` constraint with
  its converse — the one operation both halves of the read perform, positive with a
  predicate's denotation and negative with its complement."
  [net universe converse rels a b]
  (-> net
      (update [a b] (fnil set/intersection universe) rels)
      (update [b a] (fnil set/intersection universe) (converse rels))))

(defn- support-pair
  "Record `handle` as a supporter of both directions of the `[a b]` constraint."
  [support handle a b]
  (-> support
      (update [a b] (fnil conj #{}) handle)
      (update [b a] (fnil conj #{}) handle)))

(defn- absorb-narrowing
  "Fold a narrowing's `{:net … :support …}` into the one read from stored facts: intersect
  each pair's constraint, union each pair's support.  `state` unchanged when there is
  nothing to fold.

  Each direction is taken **as given** rather than mirrored through the algebra's
  converse, which is what separates this from `narrow`.  A narrowing answers ordered
  pairs and answers both — it reads `[i j]` and `[j i]` off the same closure — so
  mirroring here would intersect a pair with the converse of a claim about itself."
  [state narrowed universe]
  (if-let [net (:net narrowed)]
    (let [support (:support narrowed)]
      (reduce-kv (fn [st pair rels]
                   (-> st
                       (update-in [:net pair] (fnil set/intersection universe) rels)
                       (update-in [:support pair] (fnil into #{}) (get support pair #{}))))
                 state net))
    state))

(defn- build-network
  "The read itself: `{:net <network> :support <{[a b] → #{handle}}>}`.  Support is
  collected on the way past rather than on demand — the reader is already holding the
  handle it matched, and finding it again later would mean a second read.

  The calculus's own predicates first, then the **narrowing** if it has one, which is the
  order intersection makes irrelevant: it is commutative and associative, so a network is
  a function of what both readers saw and never of which ran first."
  [kb {:keys [algebra denotation predicates narrowing]} context]
  (let [universe (:universe algebra)
        converse (:converse algebra)
        absorb   (fn [state rels [h a b]]
                   (-> state
                       (update :net narrow universe converse rels a b)
                       (update :support support-pair h a b)))
        stated
        (reduce
         (fn [state pred]
           (let [denot     (denotation pred)
                 ;; the base relations a believed `(not (pred a b))` rules out.  These
                 ;; algebras are jointly exhaustive and pairwise disjoint, so "not P" is
                 ;; exactly "one of the relations P does not denote" — a constraint, not an
                 ;; absence.  Converse commutes with complement (it is a bijection on the
                 ;; base relations), so `narrow` writes the mirror the same way for both.
                 ruled-out (set/difference universe denot)]
             (as-> state $
               (reduce #(absorb %1 denot %2) $ (asserted-pairs kb pred context))
               (reduce #(absorb %1 ruled-out %2) $ (refuted-pairs kb pred context)))))
         {:net {} :support {}}
         predicates)]
    (if-let [f (:fn narrowing)]
      (absorb-narrowing stated (f kb context) universe)
      stated)))

(defn- read-network
  "The **resident** read: `{:net … :support …}` for `calc` visible from `context`, built
  out of the KB the first time and then reused until the engine mutates something.

  What a network is a function of is exactly what the change clock covers: the stored
  sentexes (`kb/create-sentex`, `integrate/sentex-removed!`), their labels (every mutating
  `jtms` entry point), and the taxonomy the visibility and subsumption fans are read
  through (a watch on its atom).  Nothing else can move an answer here, so an unmoved
  clock is a proof that rebuilding would produce the identical map — and the clock is
  deliberately coarse, so it says so far less often than it could.

  Residency is not conditional on a prover being registered.  `qualitative-network` and
  `possible-relations` are reads, and a network is a property of the stored facts whether
  or not anybody opted in to reasoning with it."
  [kb calc context]
  (observe/cached (reasoning/qcn kb) [(:name calc) context]
                  (fn [_stale] (build-network kb calc context))))

(defn network
  "Read every believed relation of `calc` visible from `context` into a constraint
  network `{[a b] → #{base relations}}`, both directions stored.  Each asserted `(P a b)`
  intersects the (a b) constraint with P's denotation and the (b a) constraint with its
  converse; each believed `(not (P a b))` intersects them with the **complement** of that
  denotation and of its converse.  So several facts about one pair narrow it together,
  whatever their polarity — an unrecorded pair stays the full (unknown) set, and a pair
  narrowed to nothing is a contradiction `tighten` reports.

  Intersection is commutative and associative, so the network is a function of the
  believed facts alone, never of the order they were asserted or read in — negatives
  included, since a complement is a fixed function of the denotation.  Resident on the
  KB between reads (`read-network`).

  `context` is one **reader**, and a variable is not one: it reads every context's facts
  into a single network, which is a diagnostic view of everything stored rather than
  anything anybody can see — two incomparable contexts compose in it and for no
  reader.  A goal is therefore never answered off that network; the prover fans over
  `reader-contexts` instead, so \"in some context\" is the union of what the readers
  answer."
  [kb calc context]
  (:net (read-network kb calc context)))

(defn network-support
  "The **asserted** support of that network: `{[a b] → #{handle}}`, the sentexes whose
  denotations were intersected into each pair.  What `qcn/path-consistent-with-support`
  starts from, and what an entailed relation's support is ultimately unioned out of."
  [kb calc context]
  (:support (read-network kb calc context)))

(defn nodes
  "Every term named by a constraint in `net`."
  [net]
  (into #{} (mapcat identity) (keys net)))

;; ---- which readers there are ---------------------------------------------
;; There is one network per **reader**, not one per context that holds a fact.  A
;; reader sees the whole `genlCx` ancestor set above it, so a context inheriting two
;; contexts holds both their facts in one network and composes what neither
;; composes alone.  Both consumers of "the networks of this calculus" need that set:
;; forward chaining, which re-joins against each, and the prover answering a goal whose
;; context is a *variable* — which means "in some context", and so has to be the union
;; of what the readers answer rather than one read over the union of what they see.

(defn reader-contexts
  "Every context worth reading a network of `calc` at: the contexts holding one of its
  facts — or one of its narrowing's node-bearing facts, since a pair the metric layer
  pins down is as much a constraint as a stored one — and the contexts where two or more
  of those meet (`tax/meet-closure`, which a calculus whose facts all sit in one context
  closes without reading a closure).

  The contexts are read from the store rather than from belief, which over-approximates
  in the safe direction: a context whose only fact of this calculus is defeated is
  enumerated, reads an empty network there, and entails nothing.

  **Resident** on the KB's `:qcn` atom, stamped with the change clock exactly as the
  networks it names are.  Collecting the fact contexts is a record fetch per stored fact
  of the calculus — the same walk as reading one network, and answering the same
  question about the same content — so a caller asking per goal would pay the whole
  extent per goal.  Chaining keeps a per-run memo in front of this and is unaffected;
  the prover fanning a variable-context goal has no such run to memoize in, and is
  exactly the caller that would."
  [kb calc]
  (observe/cached
   (reasoning/qcn kb) [(:name calc) ::readers]
   (fn [_stale]
     (let [held (into #{}
                      (comp (mapcat (fn [pred] (reads/as-stored-with-functor (:index kb) pred)))
                            (keep (fn [h] (:context (p/get-sentex (:records kb) h)))))
                      (:context-predicates calc))]
       (tax/meet-closure (reasoning/taxonomy kb) held)))))

;; ---- the path-consistency pass, memoized on the network value -----------
;; The pass is the expensive part (O(n³) triples per iteration) and a query asks for
;; several constraints out of one network.  The key is the network alone, not the node
;; set: a node the caller adds because the goal names it is isolated, every constraint it
;; takes part in is the universe, and the universe composes to itself, so it can tighten
;; nothing.

(defn- report-inconsistency!
  "Append an unsatisfiable network to the KB's violations ledger, and log it at :warn.

  A qualitative inconsistency is an **irreducible clash among stored content** — several
  facts that cannot all hold, with nothing to prefer between them — so it belongs where
  the engine already reports dropped and impossible content rather than being thrown.
  Three reasons it is not a `wff` check:

  * `wff` **throws**, and which fact it would throw on is whichever arrived last.  The
    clash is a property of a *set*, so blaming a member of it makes the stored KB depend
    on assertion order — the one thing the engine does not allow.
  * the check costs a path-consistency fixpoint, and `wff` runs per assert.  Every
    spatial fact would pay an O(n³) pass to store.
  * the provers are **opt-in**.  A KB that never registered one would still be held to a
    calculus it never asked to reason with.

  Recorded here instead: on the way past, once per network **per KB and context**.  The
  pass itself is keyed on the network value and shared, so two KBs — or two contexts of one
  KB — reaching the same network run it once between them, and a report hung off that run
  would fire for whichever asked first and leave the rest answering nothing with an empty
  ledger.  A query loop still reports once, and a change of belief reports again."
  [kb calc context net]
  (when-let [v (reasoning/violations kb)]
    (let [bad   (qcn/unsatisfiable-pairs net (:algebra calc))
          entry {:violation :qualitative-inconsistency
                 :calculus  (:name calc)
                 :context   context
                 :sentence  nil
                 :detail    (cond-> {:message (str "the " (name (:name calc))
                                                   " network visible from " context
                                                   " is unsatisfiable, so no goal of that"
                                                   " calculus is answered there")
                                     ;; a node may be a NAT and a pair always is a vector,
                                     ;; so both are keyed through the guarded printer
                                     :nodes (nm/by-print-key (nodes net))}
                              (seq bad) (assoc :pairs (nm/by-print-key bad)))}]
      (trove/log! {:level :warn :id ::qualitative-inconsistency :data entry})
      (swap! v (fn [entries]
                 (let [e' (conj entries entry) n (count e')]
                   (if (> n 1000) (vec (subvec e' (- n 1000))) e')))))))

(defn- resident-pass
  "Hold the result of `build` on the KB beside the network it is a function of, under `k`
  and the change clock, and answer from there while both still hold.

  This sits *in front of* the content-keyed caches below rather than replacing them, and
  the reason is a cost the content key cannot avoid.  A network is a map of a pair per
  node pair, so looking one up as a key costs a full map comparison at every hit — at a
  hundred nodes that is more work than the read it was saving.  A resident network is the
  *same object* read after read, so `identical?` decides it in a reference compare.

  It is a fast path, never an authority: a caller passing some network other than the one
  resident for `[calculus context]` falls straight through to the content-keyed cache, and
  so is answered about the network it actually asked about.

  `build` is handed the entry this one replaces — `{:net … :result …}` for the network
  that was resident before, or nil — which is what lets a pass warm-start off its own
  previous answer."
  [kb k net build]
  (let [entry (observe/cached (reasoning/qcn kb) k (fn [stale] {:net net :result (build stale)}))]
    (if (identical? net (:net entry)) (:result entry) (build nil))))

(defn tighten
  "Path consistency over `net`, memoized on the network value and held resident on the KB
  in front of that.  An unsatisfiable network is reported through `report-inconsistency!`
  on the way past — the pass has just proved it, and the alternative is a query that
  silently answers nothing.  A cache hit of either kind does not re-record, so a query
  loop reports once and a change of belief reports again.

  When the last resident answer was computed for a network this one **narrows** — which is
  what an arriving fact does, and it is the ordinary case during a load — the pass is
  **warm-started** off it and revisits only the triples reading a pair that moved
  (`qcn/path-consistent-from`).  Same value, less of the cubic loop.  Widening — a
  retraction, a defeat — has no such shortcut and pays the whole pass; that is the honest
  trade rather than a gap, since a fixpoint cannot be run backwards.

  `extra` is the nodes the *goal* names and the network may not — `qcn/path-consistent`
  needs every node its triples are drawn from, and the ones the network mentions are read
  off it here.  Naming only the extras is what keeps a cache hit O(1): collecting a
  network's own nodes is a walk over every pair, which at a hundred nodes costs more than
  the pass lookup it precedes."
  [kb {:keys [algebra pc-cache] :as calc} context net extra]
  (let [result (resident-pass
                kb [(:name calc) context ::pass] net
                (fn [stale]
                  (caches/read-through
                   pc-cache (caches/limit-of :path-consistency pc-cache-limit) net
                   (fn []
                     (let [warm (when (and (map? (:result stale))
                                           (qcn/narrowing-of? net (:net stale) algebra))
                                  (:result stale))]
                       (if warm
                         (qcn/path-consistent-from net warm extra algebra)
                         (qcn/path-consistent net (into (nodes net) extra) algebra)))))))]
    (when (and (= :inconsistent result)
               (observe/newly-seen? (reasoning/qcn kb) [(:name calc) context ::reported] net))
      (report-inconsistency! kb calc context net))
    result))

(defn constraint
  "The constraint set on `[i j]` in `net`: the identity on the diagonal, the recorded
  set, else the universe (unknown)."
  [calc net i j]
  (qcn/constraint net (:algebra calc) i j))

(defn possible
  "The base relations still possible between `a` and `b` given everything believed in
  `context` — `#{}` when the network is inconsistent."
  [calc kb context a b]
  (let [net (network kb calc context)
        pc  (tighten kb calc context net [a b])]
    (if (= pc :inconsistent) #{} (constraint calc pc a b))))

(defn definite
  "The single base relation between `a` and `b` when path consistency pins it down;
  `:inconsistent` when the network contradicts itself, `:unknown` when two or more
  remain possible."
  [calc kb context a b]
  (let [poss (possible calc kb context a b)]
    (case (count poss)
      0 :inconsistent
      1 (first poss)
      :unknown)))

(defn inconsistent?
  "Is the network of `calc` visible from `context` unsatisfiable?  The question
  `possible` answers only obliquely, by going empty for every pair at once."
  [calc kb context]
  (let [net (network kb calc context)]
    (= :inconsistent (tighten kb calc context net nil))))

;; ---- support: which stored sentexes an entailment rests on ---------------

(defn- tighten-with-support
  "`tighten`'s support-carrying twin, memoized in the calculus's own `:support-cache`.

  The key is **the network and its asserted support together**, where `tighten`'s is the
  network alone.  That difference is required: retracting a fact and re-asserting the
  same sentence yields the identical network at a *different handle*, so the network alone
  does not determine the support and a network-keyed entry would answer with the retracted
  handle.  Both keys are still functions of the believed facts, which is what makes either
  cache sound across queries.

  It does **not** report an inconsistency to the violations ledger.  `tighten` is the
  reporting path, and a second cache reporting the same impossible network would make how
  many entries the ledger holds depend on which functions a caller happened to call.

  Held resident in front of that key for the same reason `tighten` is — a two-map key is
  the most expensive lookup in the engine, and this one is asked per entailed pair.
  `extra` names the goal's own nodes, exactly as it does there.

  It is **not** warm-started, and that is deliberate rather than unfinished.  A warm start
  keeps the supports the previous run accumulated, so which handles an entailment names
  would become a function of the order the facts arrived in — and these handles become a
  firing's antecedents.  The closed network is a unique greatest fixpoint and so is
  order-independent whichever way it is reached; the *support* is one witness among
  several, and only a run from nothing picks the same witness every time."
  [kb {:keys [algebra support-cache] :as calc} context net support extra]
  (resident-pass
   kb [(:name calc) context ::support-pass] net
   (fn [_stale]
     (caches/read-through
      support-cache (caches/limit-of :network-support pc-cache-limit) [net support]
      #(qcn/path-consistent-with-support net support (into (nodes net) extra) algebra)))))

(defn- resolved
  "The support-carrying pass over the network of `calc` visible from `context`, with
  `extra` folded into the node set (a goal may name a node no fact mentions)."
  [calc kb context extra]
  (let [{:keys [net support]} (read-network kb calc context)]
    (tighten-with-support kb calc context net support extra)))

;; ---- what has moved since a caller last joined over this network ---------
;; A forward rule with a qualitative antecedent is re-joined whenever a fact of the
;; calculus arrives, because the trigger index cannot connect a new `ntpp` fact to a
;; `partOfRegion` antecedent.  Re-joining over *every* pair the network entails means the
;; nth arriving fact redoes the work the (n-1)th already did, and the load is cubic in the
;; node count for it.  So a caller can ask what has changed since it last looked, and join
;; over that instead.
;;
;; The baseline is the network as of the last **join**, not the last pass.  Those are not
;; the same moment — a query, or a settle's `entailment-withdrawn?` re-check, runs a pass
;; without joining anything — and measuring against the wrong one silently drops the
;; firings that happened in between.  So the pass's own warm-start seed set, which is
;; exactly the delta against the last *pass*, is deliberately not what is reported here.
;;
;; Two things make a pair licence a firing it did not license before: its **constraint**
;; narrowed, or the **handles** behind it changed.  The first is a diff of the two closed
;; networks.  The second cannot be diffed pair by pair — a derived support is a union
;; along whatever chain narrowed it, so a handle swapped out at one pair moves the support
;; at pairs that did not themselves move — so it is answered coarsely and from the input:
;; if the handle set the network was read out of has **lost** a member, every pair is
;; suspect and the delta is `:all`.  Losing one is what invalidates a justification and
;; sweeps a conclusion, which is the case that must be re-derived; gaining one only ever
;; adds a second route to something already believed.

(defn- differing-pairs
  "The pairs at which two closed networks disagree, either of them recording what the
  other does not — an unrecorded pair being the universe."
  [a b]
  (let [diff (fn [acc m other]
               (reduce-kv (fn [acc pair rels]
                            (if (= rels (get other pair)) acc (conj acc pair)))
                          acc m))]
    (-> #{} (diff a b) (diff b a))))

(defn join-baseline
  "What a re-join is measured against: the handles the network of `calc` in `context` was
  read out of, and the network they close to.  Both are resident reads, so taking one
  inside a pinned step costs a map lookup and the handle union."
  [kb calc context]
  (let [{:keys [net support]} (read-network kb calc context)]
    {:handles (into #{} (mapcat val) support)
     :net     (tighten kb calc context net nil)}))

(defn join-delta
  "`{:moved … :baseline …}` for `calc` in `context` — the pairs that may license a firing
  the last re-join did not, and the baseline to hand back to `note-joined` once this
  re-join is done.

  `:moved` is `:all` — join over everything — whenever the delta cannot be trusted: no
  baseline recorded yet, either side unsatisfiable, or a handle gone from the network's
  input.  Otherwise it is the set of pairs, both directions, whose closed constraint
  differs."
  [kb calc context]
  (let [now  (join-baseline kb calc context)
        base (some-> (reasoning/qcn-joined kb) deref (get [(:name calc) context ::joined]))]
    {:baseline now
     :moved    (if (and base
                        (map? (:net base)) (map? (:net now))
                        (set/subset? (:handles base) (:handles now)))
                 (differing-pairs (:net base) (:net now))
                 :all)}))

(defn note-joined
  "Record `baseline` as the network every rule mentioning `calc` has now been joined over
  in `context`.  Only a caller that re-joins *all* of them may say so — a single rule's
  own full join (a rule arriving) does not, or the next delta would claim the others were
  covered too.

  The baselines live in `:qcn-joined`, their own map beside the resident network
  cache rather than inside it: the cache clears wholesale at its bound, and a
  baseline is bookkeeping, not a memo — losing one silently degrades every later
  delta join for that calculus and context to a full re-join.  The map is bounded by
  (calculi × reader contexts), which no eviction is needed for."
  [kb calc context baseline]
  (when-let [a (reasoning/qcn-joined kb)]
    (swap! a assoc [(:name calc) context ::joined] baseline))
  nil)

(defn support
  "The handles of the stored sentexes the relation between `a` and `b` rests on: the
  facts a reader intersected into that pair's constraint, plus — transitively — the facts
  behind every composition that narrowed it.  `#{}` when the pair is unconstrained (there
  is nothing to support \"unknown\") and when the network is inconsistent (an impossible
  theory entails nothing to support).

  This is the answer to \"why does the network say that?\", and it is the piece a
  justification would need: an entailed relation has no handle of its own, so a datum
  resting on it must rest on these instead.  It names **one** derivation and
  over-approximates *that* one, exactly as a justification names one support list —
  see `qcn/path-consistent-with-support` for both halves of that claim."
  [calc kb context a b]
  (let [r (resolved calc kb context [a b])]
    (if (:inconsistent r) #{} (get (:support r) [a b] #{}))))

(defn inconsistency-culprits
  "`{:pair [i j] :support #{handle}}` for an unsatisfiable network — the pair whose
  constraint emptied and the sentexes behind it — or nil when the network is satisfiable.

  Which pair is blamed for an inconsistency only *composition* finds depends on the order
  the fixpoint reaches it, so this is a diagnosis rather than a canonical explanation.
  The verdict itself does not depend on order; only the blame does.  For that reason it is
  the ledger's `unsatisfiable-pairs` — a function of the network alone — that
  `report-inconsistency!` records, and this that a caller asks for on demand."
  [calc kb context]
  (let [r (resolved calc kb context nil)]
    (when-let [pair (:inconsistent r)]
      {:pair pair :support (:culprits r)})))

;; ---- the prover ----------------------------------------------------------

(defn- negated-literal
  "The literal a `(not (P a b))` goal negates, or nil for anything else.  A goal reaches a
  prover in the form the caller wrote it — `FactProver` hands `(not …)` straight to
  `matches-visible`, which reads the `not` frame as the polarity of the pattern — so the
  same surface convention is read here rather than a second one being invented."
  [goal]
  (when (and (sequential? goal) (= 2 (count goal))
             (= sx/not-functor (first goal)) (sequential? (second goal)))
    (second goal)))

(defn- claimed-literal
  "The `(P a b)` literal a goal is about when `calc` claims it — the goal itself, or the
  literal under a `not` — else nil."
  [calc goal]
  (let [lit (or (negated-literal goal) goal)]
    (when (and (sequential? lit) (= 3 (count lit))
               (contains? (:predicates calc) (first lit)))
      lit)))

(defn- solve-goal
  "Solutions for a goal `(P a b)` — or `(not (P a b))` — in `context`, read off the
  path-consistent network.

  **Positive: entailment.**  `(P a b)` holds iff every relation still possible between a
  and b satisfies P, `possible ⊆ denotation(P)`.

  **Negative: refutation.**  `(not (P a b))` holds iff *no* relation still possible
  between a and b satisfies P, `possible ∩ denotation(P) = ∅`.  Note the asymmetry — the
  positive case needs containment and this one needs disjointness, and a pair the network
  leaves genuinely open satisfies neither.

  Refutation is available here precisely because these algebras are **jointly exhaustive
  and pairwise disjoint**: exactly one base relation holds of any pair, so ruling every
  member of P's denotation out of the possible set *proves* P false rather than merely
  failing to prove it.  That is a stronger claim than the engine's open-world default
  allows anywhere else, and it is licensed by the algebra, not by a closed world.  It
  stays sound in only one direction: a refutation is real, while a **failure** to refute
  is still \"not provable\", never \"provably true\".

  Four shapes, on which of the two arguments are bound, and they behave the same under
  either polarity: a ground pair is a check, one variable enumerates the nodes, and two
  distinct variables enumerate the pairs off the diagonal, which a denotation containing
  the identity would otherwise report for every node on its own.  Two *occurrences of the
  same* variable is the diagonal itself — `(partOfRegion ?x ?x)` answers every region,
  `(before ?x ?x)` none, and `(not (before ?x ?x))` every one.  Without that case the
  two-variable branch would bind the one variable twice, keeping only the second node, and
  so answer a goal nothing entails.

  `pairs`, when given, is the **narrowed** shape: enumerate those pairs rather than the
  nodes, keeping the ones the goal's ground arguments select.  It is a different question,
  not a filter over the answers — filtering afterwards still walks every pair, which is
  the O(n²) this exists to avoid — and it is the caller's to ask honestly: the answers it
  leaves out are real entailments, and only a caller that knows it has already acted on
  them (`join-delta`) may skip them."
  ([calc kb goal context] (solve-goal calc kb goal context nil))
  ([calc kb goal context pairs]
   (let [neg?  (some? (negated-literal goal))
         [pred a b] (claimed-literal calc goal)
         denot ((:denotation calc) pred)
         net   (network kb calc context)
         extra (remove pvar? [a b])
         pc    (tighten kb calc context net extra)]
     (when-not (= pc :inconsistent)
       (let [holds? (fn [x y]
                      (let [poss (constraint calc pc x y)]
                        (and (seq poss)
                             (if neg?
                               (empty? (set/intersection poss denot))
                               (set/subset? poss denot)))))
             answer (fn [x y] (cond-> {} (pvar? a) (assoc a x) (pvar? b) (assoc b y)))]
         (if pairs
           ;; the diagonal is asked for by `(P ?x ?x)` alone, and its constraint is the
           ;; algebra's identity whatever a pair records — so it never moves, and a
           ;; narrowed run correctly answers it with nothing
           (let [same-var? (and (pvar? a) (pvar? b) (= a b))]
             (for [[x y] pairs
                   :when (and (or (pvar? a) (= a x))
                              (or (pvar? b) (= b y))
                              (or (not same-var?) (= x y))
                              (holds? x y))]
               (answer x y)))
           ;; an open goal enumerates the nodes, so the network's own are needed here too
           (let [ns (into (nodes net) extra)]
             (cond
               (and (not (pvar? a)) (not (pvar? b)))
               (when (holds? a b) [{}])

               (not (pvar? a))
               (for [n ns :when (holds? a n)] (answer a n))

               (not (pvar? b))
               (for [n ns :when (holds? n b)] (answer n b))

               (= a b)                          ; (P ?x ?x) — the diagonal
               (for [n ns :when (holds? n n)] (answer n n))

               :else
               (for [x ns y ns :when (and (not= x y) (holds? x y))] (answer x y))))))))))

(defrecord CalculusProver [calculus]
  prover-types/Prover
  ;; both polarities: `(P a b)` is claimed by entailment and `(not (P a b))` by
  ;; refutation, and a believed negative literal is itself read into the network as a
  ;; constraint — so the goal and the fact meet in the same place.
  (applicable? [_ _ goal _]
    (some? (claimed-literal calculus goal)))
  ;; Cheap and honest: the node count bounds an open enumeration, and the number of
  ;; stored facts of this calculus bounds the node count.  That is a sum of O(1)
  ;; functor-root reads, where actually building the network is a query per predicate —
  ;; an estimate must not cost what it estimates.
  (est-bindings [_ kb goal _]
    (let [[_ a b] (claimed-literal calculus goal)
          n (max 1 (reduce + (map #(reads/stored-count-with-functor (:index kb) %)
                                  (:predicates calculus))))]
      (cond (and (pvar? a) (pvar? b)) (* n n)
            (or (pvar? a) (pvar? b))  n
            :else                     1)))
  ;; A fixpoint over the stored facts before the first answer — a closure, not a search.
  (cost [_ _ _ _] :compute)
  ;; Authoritative, under either polarity, over everything the network reads: the
  ;; answer is a property of the *whole* network rather than of any one stored fact, so
  ;; unioning a raw fact match in would add nothing this does not already entail — a
  ;; believed `(not (P a b))` is read into the network too, so the refutation it
  ;; licenses comes back out of the same pass, and the algebra's own composition and
  ;; converse cover what the transitive / symmetric / inverse provers would say.
  ;;
  ;; What the network cannot read is a claim nobody stored — which is `sole-prover`'s
  ;; question rather than this one's, asked once of the goal instead of once per
  ;; claimant.
  (completeness [_ _ _ _] 100)
  ;; A **variable** context means "in some context", and the honest answer to that is the
  ;; union of what the readers answer — not one read taken over the union of what they
  ;; see.  Those differ, and in the unsound direction: `(ntpp A B)` in one context and
  ;; `(ntpp B D)` in an incomparable one compose for nobody, since no context inherits
  ;; both, yet a single wildcard read holds them in one network and reports `A ⊏ D` as
  ;; entailed.  Every other prover reads a variable context as "any", and the fan is what
  ;; makes this one agree: each binding it yields is entailed for a reader that exists.
  (solve [_ kb goal context]
    (if (pvar? context)
      (distinct (mapcat #(solve-goal calculus kb goal %) (reader-contexts kb calculus)))
      (solve-goal calculus kb goal context))))

(defn prover
  "The entailment prover for `calc`, to register with `vaelii.core/add-prover`."
  [calc]
  (->CalculusProver calc))

(defn prover-for?
  "Is `pr` the prover of the calculus named `nm`?  How a caller asks which calculus a
  registered prover speaks for: the calculi share one record type, so a class test says
  only that some calculus is registered."
  [nm pr]
  (and (instance? CalculusProver pr) (= nm (:name (:calculus pr)))))

;; ---- what forward chaining joins on --------------------------------------
;; A forward rule's antecedents are matched against stored facts, so an *entailed*
;; relation could not fire one: it has no handle, and a justification with no antecedent
;; is a conclusion nothing can withdraw.  Support closes that — an entailment names the
;; stored facts it rests on, and those are what the justification lists.  These three
;; are the boundary chaining reaches through; the wiring itself is `vaelii.impl.chain`.

(defonce ^{:private true
           :doc "`registered-calculi`'s last answer as `[registry answer]`, held against the prover
  vector's IDENTITY.

  Registration is opt-in and happens at setup, so the answer is constant for the life of
  a registry value, while the callers are the engine's hottest paths — `calculus-for` is
  asked per asserted sentence (`special/recheck-on-qualitative`) and per antecedent
  literal (`chain/qualitative-antecedent`).  Unmemoized, a KB that registered nothing
  still paid an `instance?` per prover in the default registry of 18, plus a fresh
  vector, to be told nil again; at a 10M-fact bulk load that is the same nil computed
  10M times.

  **One entry, and identity rather than value.**  Every KB opens on the same
  `provers/default-provers` vector, so a single entry answers every KB that registered
  nothing *and* every stretch of writing on one that did — which is the whole of what is
  being saved.  A map keyed on the registry would instead hold every vector it ever saw
  alive for the process's life, one more per `add-prover`, and hashing such a key walks
  the vector, which is the cost being removed.  A `swap!` on the registry produces a new
  value, so it simply misses and recomputes.  Last write wins and the pair is written as
  one value, so a lost race costs a recomputation and cannot answer wrongly."}
  registry-calculi
  (volatile! nil))

(defn registered-calculi
  "The calculi whose prover is registered on `kb`.  Registration is the opt-in: with no
  prover, a calculus's facts are ordinary facts, matched and chained like any other.

  Memoized against the registry's identity (`registry-calculi`); a miss is a scan rather
  than an absence — an `instance?` test per prover in the registry plus a fresh vector.
  `calculus-for` is the only caller and the paths that ask it
  (`chain/qualitative-antecedent` per antecedent literal,
  `special/recheck-on-qualitative` per asserted sentence) each say what a miss costs
  them."
  [kb]
  (if-let [pv (some-> (:provers kb) deref)]
    (let [[reg answer] @registry-calculi]
      (if (identical? pv reg)
        answer
        (let [v (into [] (comp (filter #(instance? CalculusProver %)) (map :calculus)) pv)]
          (vreset! registry-calculi [pv v])
          v)))
    []))

(defn calculus-for
  "The registered calculus claiming `pred`, or nil.  Predicates belong to exactly one
  calculus, so the first hit is the only hit.

  What a calculus *answers*, which is what a rule antecedent is discharged by
  (`chain/qualitative-antecedent`).  A predicate that merely moves the network is
  `calculus-triggered-by`'s question, and answering it here would have the join try to
  discharge a `temporalDistance` antecedent off the interval algebra."
  [kb pred]
  (first (filter #(contains? (:predicates %) pred) (registered-calculi kb))))

(defn calculus-triggered-by
  "The registered calculus whose network `pred` moves, or nil — every predicate
  `calculus-for` matches, plus the ones a narrowing reads.  The re-check and re-join
  triggers ask this, because what has to be put in front of a settle is a rule joining on
  a relation the network entails, and a metric constraint moves that network without being
  a predicate any such rule mentions.

  The set is folded into the calculus at construction (`calculus`), so this costs the same
  membership test `calculus-for` does — it is asked per asserted sentence."
  [kb pred]
  (first (filter #(contains? (:trigger-predicates %) pred) (registered-calculi kb))))

(defn solve-with-support
  "Entailed solutions for `goal` in `context`, each paired with the handles it rests on —
  a seq of `[bindings #{handle}]`.

  `solve-goal` answers *which* pairs the network entails; `support` answers what stored
  facts each one rests on.  Forward chaining needs both, and needs them together: the
  bindings extend the join, and the handles become the conclusion's antecedents, so
  retracting any fact behind the entailment withdraws whatever was concluded from it.

  A pair whose support is empty is dropped rather than answered with a groundless
  justification.  That is not a hypothetical: the *diagonal* of a reflexive denotation
  (`(partOfRegion ?x ?x)`) is entailed by the algebra's identity alone, with no stored
  fact behind it, and a conclusion drawn from it would rest on the rule and nothing else
  while looking as though it rested on the network.

  `pairs` narrows the enumeration to those pairs (`solve-goal`), which is what a re-join
  over a delta passes.  It adds no work here: a pair with no support was never going to
  be answered, and a pair whose support is what changed is in the delta by construction.

  `goal` is a **positive** literal `(P a b)`, where `solve-goal` takes either polarity.
  That is the boundary's shape rather than a shortcut: what a *refutation* rests on is the
  whole network rather than a support list, so a negated antecedent is not answered by
  entailment at all and `chain/qualitative-antecedent` claims only the positive shape."
  ([calc kb goal context] (solve-with-support calc kb goal context nil))
  ([calc kb goal context pairs]
   (let [[_ a b] goal]
     (for [bnd (solve-goal calc kb goal context pairs)
           :let [x (if (pvar? a) (get bnd a) a)
                 y (if (pvar? b) (get bnd b) b)
                 sup (support calc kb context x y)]
           :when (seq sup)]
       [bnd sup]))))

;; ---- what the passes hold, declared -------------------------------------
;;
;; Both caches hang off the **calculus value**, and a shipped calculus is one `def` — so
;; two KBs registering Allen share one cache and these are process rows, not per-KB ones.
;; That sharing is deliberate (a pass keyed on the network value is one caller's answer
;; and another's), and it is exactly the case a per-KB row would misattribute.  The limit
;; is per calculus; the count is across all of them.

(defn- calculus-cache-total [k]
  (reduce + 0 (map #(count @(get % k)) (vals @built-calculi))))

(defn- clear-calculus-cache [k]
  (let [n (calculus-cache-total k)]
    (doseq [c (vals @built-calculi)] (reset! (get c k) {}))
    n))

(defn- trim-calculus-cache [k target]
  (reduce + 0 (map #(caches/trim-map! (get % k) target) (vals @built-calculi))))

(caches/register-cache
 {:cache    :path-consistency
  :label    "Path-consistency passes"
  :scope    :process
  :unit     "networks"
  :limit    (caches/limit-thunk :path-consistency pc-cache-limit)
  :counters nil
  :note     (str "One tightened network per network value a calculus has been asked "
                 "about. Keyed on the value rather than on the KB or the context, so a "
                 "change to the believed facts is a different key and never a stale "
                 "answer.")
  :read     (fn [_] {:entries (calculus-cache-total :pc-cache)})
  :clear    (fn [_] (clear-calculus-cache :pc-cache))
  :trim     (fn [_ target] (trim-calculus-cache :pc-cache target))})

(caches/register-cache
 {:cache    :network-support
  :label    "Network support passes"
  :scope    :process
  :unit     "networks"
  :limit    (caches/limit-thunk :network-support pc-cache-limit)
  :counters nil
  :note     (str "The same pass carrying the stored facts each entailment rests on — a "
                 "separate cache because support is asked for rarely and every query "
                 "would otherwise pay to propagate what nothing reads.")
  :read     (fn [_] {:entries (calculus-cache-total :support-cache)})
  :clear    (fn [_] (clear-calculus-cache :support-cache))
  :trim     (fn [_ target] (trim-calculus-cache :support-cache target))})
