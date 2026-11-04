;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.qcn-kb
  "The KB half every calculus over `vaelii.impl.qcn` shares: a calculus value
  (`calculus`), the believed facts of one reader context read into a resident network,
  the passes over it, entailment and refutation as prover solutions, the support an
  entailment rests on, and the delta a forward re-join runs over.  See docs/qcn.md."
  (:require [clojure.set :as set]
            [taoensso.trove :as trove]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.except :as exc]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.predicates :as pr]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.qcn :as qcn]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.violations :as violations]))

(def ^:private pc-cache-limit 256)

;; `{name calculus}` for every calculus built in this process, which the cache rows below
;; sum over; keyed by name so a reloaded calculus replaces its entry.
(defonce ^:private built-calculi (atom {}))

(defn- pvar? [x] (sx/variable? x))

(defn- node-term?
  "A term usable as a network node when the narrowing names no `:node?`: a symbol that is
  not a variable."
  [x]
  (and (symbol? x) (not (pvar? x))))

(defn calculus
  "Bundle an algebra and its vocabulary into the value every function here takes.
  `denotation` maps each stored predicate to the set of base relations it denotes, so its
  keys are the predicates the prover claims.

  `narrowing` is the optional second reader — nil for a calculus that has none:

    {:fn         (fn [kb context] → {:net … :support …} | nil)
     :over-nodes (fn [nodes] → {:net … :support …} | nil)
     :node?      which terms are nodes, when not every node is a symbol
     :bindings   the dynamic vars `:fn` reads, whose values key the resident network
     :sources    every predicate whose arrival or departure moves what it answers
     :contexts   the subset that puts a NODE in the network, so names a reader context}

  `:over-nodes` reads only the node set, so `with-goal-nodes` runs it over a goal's nodes
  too.  Either key may be absent.  `:sources` and `:contexts` are folded into
  `:trigger-predicates` and `:context-predicates` here, once.

  `typed` is the predicates whose `arg` declarations are narrower than the network's
  nodes, answered only over arguments those types admit (`solve-goal`).

  The value carries its two pass caches and is registered in `built-calculi`."
  ([nm algebra denotation] (calculus nm algebra denotation nil))
  ([nm algebra denotation narrowing] (calculus nm algebra denotation narrowing #{}))
  ([nm algebra denotation narrowing typed]
   (let [answered (set (keys denotation))
         c {:name       nm
            ;; as written; `qcn` compiles and caches it on first use
            :algebra    algebra
            :denotation denotation
            :predicates answered
            :typed      (set typed)
            :narrowing  narrowing
            :node?      (or (:node? narrowing) node-term?)
            :trigger-predicates (into answered (:sources narrowing))
            :context-predicates (into answered (:contexts narrowing))
            :pc-cache   (atom {})
            ;; apart from `:pc-cache`, so a plain query never propagates support
            :support-cache (atom {})}]
     (swap! built-calculi assoc nm c)
     c)))

;; ---- reading the KB into a network --------------------------------------

(defn asserted-pairs
  "Every `[handles a b]` for which `(pred a b)` is believed and visible from `context`,
  through the matcher's spec fan.  `handles` is the fact, then for a sub-predicate fact
  the `genl` edges of one path up to `pred` that `context` sees (`tax/reach-support`)."
  [kb node? pred context]
  (let [tx     (reasoning/taxonomy kb)
        reader (when-not (pvar? context) context)
        class  #(jtms/defeat-class (reasoning/tms kb) %)]
    (for [m (res/matches-visible kb (list pred '?a '?b) context)
          :let [bnd (second m), a (get bnd '?a), b (get bnd '?b)]
          :when (and (node? a) (node? b))
          :let [s (or (nth m 2 nil) (p/get-sentex (:records kb) (first m)))
                f (nm/functor (sx/sentence-of s))]]
      [(into [(first m)]
             (when (not= f pred)
               (map first (tax/reach-support tx :genl f pred reader class))))
       a b])))

(defn- refuted-pairs
  "Every `[handle a b]` for which `(not (pred a b))` is believed and visible from
  `context`, read off `pred`'s own predicate extent with no spec fan (docs/qcn.md,
  \"Negation\").  A fact about a spelling merge-retired for `context` is dropped, as the
  positive read drops one (`res/retired-for?`)."
  [kb node? pred context]
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
                         (when (and (node? a) (node? c)) [h a c])))))))
         (exc/without-excepted kb context))))

(defn nodes
  "Every term named by a constraint in `net`."
  [net]
  (into #{} (mapcat identity) (keys net)))

(defn- narrow
  "Intersect the `[a b]` constraint of `net` with `rels` and the `[b a]` constraint with
  its converse."
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
  "Fold a narrowing's `{:net … :support …}` into `state`: intersect each pair's
  constraint as given, with no converse mirror, and union its support.  The narrowing's
  `:unsatisfiable-sources` are appended, each `:stand-in` cut to the pairs `state` had not
  already emptied.  `state` unchanged when `narrowed` has no `:net`."
  [state narrowed universe]
  (if-let [net (:net narrowed)]
    (let [support (:support narrowed)
          sources (for [src (:unsatisfiable-sources narrowed)]
                    (update src :stand-in
                            (fn [pairs]
                              (into #{} (filter #(seq (get-in state [:net %] universe)))
                                    pairs))))]
      (cond-> (reduce-kv (fn [st pair rels]
                           (let [hs (get support pair #{})]
                             (-> st
                                 (update-in [:net pair] (fnil set/intersection universe) rels)
                                 (update-in [:support pair] (fnil into #{}) hs)
                                 (update :handles (fnil into #{}) hs))))
                         state net)
        (seq sources) (update :unsatisfiable-sources (fnil into []) sources)))
    state))

(defn- build-network
  "`{:net <network> :support <{[a b] → #{handle}} :handles #{handle}}`, `:handles` the
  union of the support, plus `:unsatisfiable-sources` when a narrowing's source is
  unsatisfiable.  The calculus's predicates, both polarities, then the narrowing."
  [kb {:keys [algebra denotation predicates narrowing node?]} context]
  (let [universe (:universe algebra)
        converse (:converse algebra)
        absorb   (fn [state rels [h a b]]
                   (let [hs (if (coll? h) h [h])]
                     (-> state
                         (update :net narrow universe converse rels a b)
                         (update :support #(reduce (fn [sup h] (support-pair sup h a b)) % hs))
                         (update :handles into hs))))
        stated
        (reduce
         (fn [state pred]
           (let [denot     (denotation pred)
                 ;; what a believed `(not (pred a b))` leaves; converse commutes with it
                 ruled-out (set/difference universe denot)]
             (as-> state $
               (reduce #(absorb %1 denot %2) $ (asserted-pairs kb node? pred context))
               (reduce #(absorb %1 ruled-out %2) $ (refuted-pairs kb node? pred context)))))
         {:net {} :support {} :handles #{}}
         predicates)
        read-kb (if-let [f (:fn narrowing)]
                  (absorb-narrowing stated (f kb context) universe)
                  stated)]
    (if-let [f (:over-nodes narrowing)]
      (absorb-narrowing read-kb (f (nodes (:net read-kb))) universe)
      read-kb)))

(defn- with-goal-nodes
  "`net` with the calculus's `:over-nodes` narrowing run again over its nodes and the
  goal's `extra` ones when `extra` names a node `net` lacks, else `net` itself.  The new
  pairs carry no support."
  [{:keys [narrowing algebra]} net extra]
  (let [f   (:over-nodes narrowing)
        ns  (when f (nodes net))
        new (when f (remove ns extra))]
    (if (seq new)
      (:net (absorb-narrowing {:net net :support {}} (f (into ns new)) (:universe algebra)))
      net)))

(defn- read-network
  "`build-network` of `calc` at `context`, resident on the KB's `:qcn` atom under the
  change clock, keyed on the calculus, the context and the values of the narrowing's
  `:bindings`.  A rebuild equal to the resident value in network, support and
  unsatisfiable sources answers the resident value itself.  See docs/qcn.md, \"The
  network is resident\"."
  [kb calc context]
  (observe/cached (reasoning/qcn kb)
                  (into [(:name calc) context] (map deref) (:bindings (:narrowing calc)))
                  (fn [stale]
                    (let [read (build-network kb calc context)]
                      (if (and stale
                               (= (:net read) (:net stale))
                               (= (:support read) (:support stale))
                               (= (:unsatisfiable-sources read)
                                  (:unsatisfiable-sources stale)))
                        stale
                        read)))))

(defn network
  "The constraint network `{[a b] → #{base relations}}` of every believed relation of
  `calc` visible from `context`, both directions stored: each `(P a b)` intersects the
  pair with P's denotation, each `(not (P a b))` with its complement.  An unrecorded pair
  is the universe.  A variable `context` reads every context's facts into one diagnostic
  network that answers no goal."
  [kb calc context]
  (:net (read-network kb calc context)))

(defn network-support
  "The asserted support of `network`: `{[a b] → #{handle}}`, the sentexes intersected into
  each pair."
  [kb calc context]
  (:support (read-network kb calc context)))

(defn- node-statements
  "`{node → #{#{handle}}}` over the facts of `calc` visible from `context`: per node, the
  handles of each fact naming it (`asserted-pairs`, `refuted-pairs`).  A node only a
  narrowing names has none.  Resident on the KB's `:qcn` atom under the change clock."
  [kb calc context]
  (observe/cached
   (reasoning/qcn kb) [(:name calc) ::statements context]
   (fn [_stale]
     (let [node? (:node? calc)
           rows  (mapcat #(concat (asserted-pairs kb node? % context)
                                  (refuted-pairs kb node? % context))
                         (:predicates calc))]
       (reduce (fn [m [h a b]]
                 (let [hs (set (if (coll? h) h [h]))]
                   (-> m (update a (fnil conj #{}) hs) (update b (fnil conj #{}) hs))))
               {} rows)))))

(defn unsatisfiable-sources
  "The unsatisfiable sources a narrowing of `calc` read in `context`, each
  `{:source kw :pairs [[p q] …] :support #{handle} :stand-in #{[a b]}}`, a `:metric` source
  adding `:cycle [instant …]`, or naming `:dimensions [dimension …]` in place of both when
  its problem is refused.  `:stand-in` is the pairs of this network the narrowing
  emptied for the source and no stored fact emptied.  nil when no source is unsatisfiable."
  [kb calc context]
  (:unsatisfiable-sources (read-network kb calc context)))

(defn reported-sources
  "`unsatisfiable-sources` as a report names them: no `:stand-in`, and `:support` as a
  sorted vector of handles.  nil when no source is unsatisfiable."
  [kb calc context]
  (when-let [srcs (unsatisfiable-sources kb calc context)]
    (mapv #(-> % (dissoc :stand-in) (update :support (comp vec sort))) srcs)))

(defn unsatisfiable-as-written
  "`qcn/unsatisfiable-pairs` of the network of `calc` in `context`, less the stand-in pairs
  of its unsatisfiable sources: the pairs whose stored facts no model satisfies."
  [kb calc context]
  (let [{:keys [net unsatisfiable-sources]} (read-network kb calc context)]
    (reduce #(set/difference %1 (:stand-in %2))
            (qcn/unsatisfiable-pairs net (:algebra calc))
            unsatisfiable-sources)))

;; ---- which readers there are ---------------------------------------------

(defn- held-contexts
  "The contexts storing a fact on one of `preds` or on a sub-predicate of a predicate
  `calc` answers, or a `genl` edge into such a sub-predicate, closed under
  `tax/meet-closure`.  Read from the store, not from belief.  The sub-predicates are the
  global closure, which holds every context's; an edge decides whose facts a scoped fan
  reads.  Resident on the KB's `:qcn` atom under `k` and the change clock."
  [kb calc k preds]
  (observe/cached
   (reasoning/qcn kb) [(:name calc) k]
   (fn [_stale]
     (let [tx   (reasoning/taxonomy kb)
           idx  (:index kb)
           subs (into #{} (mapcat #(tax/specs-global tx %)) (:predicates calc))
           hs   (concat (mapcat #(reads/as-stored-with-functor idx %) (into preds subs))
                        (mapcat #(reads/as-stored-with-args idx 'genl {2 %}) subs))]
       (tax/meet-closure tx (into #{} (keep #(:context (p/get-sentex (:records kb) %))) hs))))))

(defn reader-contexts
  "The reader contexts of `calc`: `held-contexts` over its `:context-predicates`, the
  facts that put a node into a network."
  [kb calc]
  (held-contexts kb calc ::readers (:context-predicates calc)))

;; ---- the path-consistency pass, memoized on the network value -----------

(defn- inconsistency-entry
  "The `:qualitative-inconsistency` entry for the unsatisfiable network `net` of `calc`
  in `context`: the calculus, the context, the nodes, the pairs unsatisfiable as written
  and the unsatisfiable sources a narrowing read."
  [kb calc context net]
  (let [bad  (unsatisfiable-as-written kb calc context)
        srcs (reported-sources kb calc context)]
    {:violation :qualitative-inconsistency
     :calculus  (:name calc)
     :context   context
     :sentence  nil
     :detail    (cond-> {:message (str "the " (name (:name calc))
                                       " network visible from " context
                                       " is unsatisfiable, so no goal naming a"
                                       " node of an unsatisfiable component is"
                                       " answered there")
                         ;; a node may be a NAT and a pair always is a vector,
                         ;; so both are keyed through the guarded printer
                         :nodes (nm/by-print-key (nodes net))}
                  (seq bad)  (assoc :pairs (nm/by-print-key bad))
                  (seq srcs) (assoc :sources srcs))}))

(defn- report-inconsistency!
  "Append an unsatisfiable network to the KB's violations ledger and log it at :warn,
  once per network per KB and context (`observe/newly-seen?`).  See docs/qcn.md,
  \"Reporting an impossible network\"."
  [kb calc context net]
  (when (reasoning/violations kb)
    (let [entry (inconsistency-entry kb calc context net)]
      (trove/log! {:level :warn :id ::qualitative-inconsistency :data entry})
      (violations/report-without-run kb entry))))

(defn- resident-pass
  "`(build stale)`, held on the KB under `k` and the change clock beside `net`, answered
  while `net` is `identical?` to the held one; a different `net` gets `(build nil)`.
  `stale` is the replaced entry, `{:net … :result …}` or nil."
  [kb k net build]
  (let [entry (observe/cached (reasoning/qcn kb) k
                              (fn [stale]
                                (if (identical? net (:net stale))
                                  stale
                                  {:net net :result (build stale)})))]
    (if (identical? net (:net entry)) (:result entry) (build nil))))

(defn- pass
  "`tighten` without the report: path consistency over `net`, memoized on the network
  value with `resident-pass` in front, warm-started (`qcn/path-consistent-from`) when `net`
  narrows the resident network.  `extra` is the goal's nodes beyond `net`'s; only a miss
  reads `net`'s own nodes."
  [kb {:keys [algebra pc-cache] :as calc} context net extra]
  (resident-pass
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
            (qcn/path-consistent net (into (nodes net) extra) algebra))))))))

(defn tighten
  "`pass` over `net`, reporting an unsatisfiable one through `report-inconsistency!`.
  `net` is a network as `network` reads it, never one `with-goal-nodes` extended:
  `newly-seen?` holds one value per KB, calculus and context.  A goal is tightened through
  `tighten-for-goal`."
  [kb calc context net extra]
  (let [result (pass kb calc context net extra)]
    (when (and (= :inconsistent result)
               (observe/newly-seen? (reasoning/qcn kb) [(:name calc) context ::reported] net))
      (report-inconsistency! kb calc context net))
    result))

(defn- component-pass
  "`pass` over `net` with no resident entry in front, memoized in the calculus's
  `:pc-cache` on the network value alone."
  [{:keys [algebra pc-cache]} net]
  (caches/read-through pc-cache (caches/limit-of :path-consistency pc-cache-limit) net
                       #(qcn/path-consistent net (nodes net) algebra)))

(defn- split
  "nil when `net`, a network of `calc` as `network` reads it, is satisfiable.  Else
  `{:bad [#{node} …] :blocked #{node} :net …}`: the connected components whose pass is
  unsatisfiable (`qcn/components`), their nodes, and `net` less them.  When the remainder
  is unsatisfiable as one network, which an algebra whose universe composes to less than
  itself allows, the whole network is one bad component.  Resident on the KB under the
  change clock beside `net` (`resident-pass`).  See docs/qcn.md, \"Unsatisfiability is per
  component\"."
  [kb calc context net]
  (when (= :inconsistent (tighten kb calc context net nil))
    (resident-pass
     kb [(:name calc) context ::split] net
     (fn [_stale]
       (let [bad  (filterv #(= :inconsistent (component-pass calc (qcn/select-nodes net %)))
                           (qcn/components net))
             gone (into #{} cat bad)
             rest (qcn/drop-nodes net gone)]
         (if (and (seq bad) (map? (component-pass calc rest)))
           {:bad bad :blocked gone :net rest}
           {:bad [(nodes net)] :blocked (nodes net) :net {}}))))))

(defn blocked-nodes
  "The nodes of the unsatisfiable components of the network of `calc` visible from
  `context` (`split`): no goal naming one is answered there.  `#{}` when the network is
  satisfiable, and for a variable `context`."
  [calc kb context]
  (if (pvar? context)
    #{}
    (or (:blocked (split kb calc context (network kb calc context))) #{})))

(defn unsatisfiable-components
  "Each unsatisfiable component of the network of `calc` visible from `context`, as
  `{:nodes #{node} :pairs #{[a b]} :culprits #{handle}}`: its nodes, its pairs
  unsatisfiable as written, and the handles a support-carrying pass over it blames
  (`qcn/path-consistent-with-support`).  nil when the network is satisfiable."
  [calc kb context]
  (let [{:keys [net support]} (read-network kb calc context)
        algebra (:algebra calc)]
    (when-let [{:keys [bad]} (split kb calc context net)]
      (mapv (fn [ns]
              (let [sub (qcn/select-nodes net ns)]
                {:nodes    ns
                 :pairs    (qcn/unsatisfiable-pairs sub algebra)
                 :culprits (:culprits (qcn/path-consistent-with-support
                                       sub (qcn/select-nodes support ns) ns algebra))}))
            bad))))

(defn- tighten-for-goal
  "`[net closed extended? blocked]` for a goal naming the nodes `extra` in `context`: the
  network with the goal's nodes (`with-goal-nodes`), its pass, whether the goal's nodes
  added anything, and the nodes of its unsatisfiable components.  The network as read goes
  through `tighten` first; an unsatisfiable one is answered as its satisfiable components
  (`split`), which a goal naming a blocked node does not extend.  The extended one goes
  through `pass`, which does not report.  A goal node cannot make a satisfiable network
  unsatisfiable: a moment is inserted into a consistent calendar chain, and a point is
  constrained only by its own thing's order."
  [kb calc context extra]
  (let [base    (network kb calc context)
        pc      (tighten kb calc context base extra)
        {:keys [blocked] sat :net} (when (= :inconsistent pc) (split kb calc context base))
        read    (or sat base)
        pc      (if sat (pass kb calc context sat extra) pc)
        net     (if (or (= :inconsistent pc) (some #(contains? blocked %) extra))
                  read
                  (with-goal-nodes calc read extra))]
    (if (identical? net read)
      [net pc false blocked]
      [net (pass kb calc context net extra) true blocked])))

(defn constraint
  "The constraint set on `[i j]` in `net`: the identity on the diagonal, the recorded
  set, else the universe (unknown)."
  [calc net i j]
  (qcn/constraint net (:algebra calc) i j))

(defn possible
  "The base relations still possible between `a` and `b` given everything believed in
  `context` — `#{}` when either lies in an unsatisfiable component of the network."
  [calc kb context a b]
  (let [[_ pc _ blocked] (tighten-for-goal kb calc context [a b])]
    (if (or (= pc :inconsistent) (contains? blocked a) (contains? blocked b))
      #{}
      (constraint calc pc a b))))

(defn definite
  "The single base relation between `a` and `b` when path consistency determines it;
  `:inconsistent` when the network contradicts itself, `:unknown` when two or more
  remain possible."
  [calc kb context a b]
  (let [poss (possible calc kb context a b)]
    (case (count poss)
      0 :inconsistent
      1 (first poss)
      :unknown)))

(defn inconsistent?
  "Is the network of `calc` visible from `context` unsatisfiable?"
  [calc kb context]
  (let [net (network kb calc context)]
    (= :inconsistent (tighten kb calc context net nil))))

(defn- governing-contexts
  "`held-contexts` over the `:trigger-predicates` of `calc`, every predicate that moves a
  network, so each context sees the same such sentences as one of these at or above it."
  [kb calc]
  (held-contexts kb calc ::governing (:trigger-predicates calc)))

(defn unsatisfiable-somewhere?
  "Is the network of `calc` unsatisfiable for some context?  Asked of the
  `governing-contexts` alone: a context sees the facts one of them at or above it sees,
  less what a defeat or an `except` withdraws below it, and a network over fewer facts
  is never tighter — so no context is unsatisfiable where all of them are satisfiable
  (docs/exceptions.md, \"Two withdrawals a firing carries\")."
  [calc kb]
  (boolean (some #(inconsistent? calc kb %) (governing-contexts kb calc))))

;; ---- support: which stored sentexes an entailment rests on ---------------

(defn- tighten-with-support
  "`qcn/path-consistent-with-support` over `net` and `support`, memoized in the calculus's
  `:support-cache` on `[net support]` with `resident-pass` in front.  Never warm-started,
  and reports nothing to the ledger (docs/qcn.md, \"Support\")."
  [kb {:keys [algebra support-cache] :as calc} context net support extra]
  (resident-pass
   kb [(:name calc) context ::support-pass] net
   (fn [_stale]
     (caches/read-through
      support-cache (caches/limit-of :network-support pc-cache-limit) [net support]
      #(qcn/path-consistent-with-support net support (into (nodes net) extra) algebra)))))

(defn- resolved
  "The support-carrying pass over the satisfiable components of the network of `calc`
  visible from `context` (`split`), with `extra` folded into the node set."
  [calc kb context extra]
  (let [{:keys [net support]} (read-network kb calc context)
        {:keys [blocked] sat :net} (split kb calc context net)
        net     (or sat net)
        support (qcn/drop-nodes support blocked)]
    (tighten-with-support kb calc context (with-goal-nodes calc net (remove #(contains? blocked %) extra))
                          support extra)))

;; ---- what has moved since a caller last joined over this network ---------
;; docs/qcn.md, "The re-join is semi-naive, over the pairs that moved".

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
  "`{:handles … :net …}`: the handles the network of `calc` in `context` was read out of,
  and the network they close to."
  [kb calc context]
  (let [{:keys [net handles]} (read-network kb calc context)]
    {:handles handles
     :net     (tighten kb calc context net nil)}))

(defn join-delta
  "`{:moved … :baseline …}` for `calc` in `context`: the pairs that may license a firing
  the last re-join did not, and the baseline to hand `note-joined` after this re-join.
  `:moved` is `:all` with no baseline recorded, either side unsatisfiable, or a handle gone
  from the network's input; else the pairs, both directions, whose closed constraint
  differs, `#{}` without a pair read when both baseline values are `identical?` to now's."
  [kb calc context]
  (let [now  (join-baseline kb calc context)
        base (some-> (reasoning/qcn-joined kb) deref (get [(:name calc) context ::joined]))
        same (fn [k] (identical? (get base k) (get now k)))]
    {:baseline now
     :moved    (cond
                 (or (nil? base) (not (map? (:net base))) (not (map? (:net now)))) :all
                 (and (same :handles) (same :net))                                 #{}
                 (or (same :handles) (set/subset? (:handles base) (:handles now)))
                 (differing-pairs (:net base) (:net now))
                 :else                                                             :all)}))

(defn note-joined
  "Record `baseline` as the network every rule mentioning `calc` has now been joined over
  in `context`, in the KB's `:qcn-joined` map.  Only a caller that re-joins all of those
  rules may call this; a single rule's own full join does not."
  [kb calc context baseline]
  (when-let [a (reasoning/qcn-joined kb)]
    (swap! a assoc [(:name calc) context ::joined] baseline))
  nil)

(defn support
  "The handles of the stored sentexes the relation between `a` and `b` rests on: the
  facts intersected into that pair, plus the facts behind every composition that narrowed
  it, for one derivation.  `#{}` when the pair is unconstrained or either node lies in an
  unsatisfiable component."
  [calc kb context a b]
  (let [r (resolved calc kb context [a b])]
    (if (:inconsistent r) #{} (get (:support r) [a b] #{}))))

(defn inconsistency-culprits
  "`{:pair [i j] :support #{handle}}` for an unsatisfiable network, the pair whose
  constraint emptied and the sentexes behind it, or nil when the network is satisfiable.
  Which pair is blamed depends on the driver's order (docs/qcn.md, \"Support\")."
  [calc kb context]
  (let [{:keys [net support]} (read-network kb calc context)
        r (tighten-with-support kb calc context net support nil)]
    (when-let [pair (:inconsistent r)]
      {:pair pair :support (:culprits r)})))

(defn closure-with-support
  "The support-carrying pass over the satisfiable components of the network of `calc`
  visible from `context`, every pair at once: `{:network … :support …}`.  A caller reading
  many pairs reads them here; `support` walks every pair per call."
  [calc kb context]
  (resolved calc kb context nil))

(defn closed-network
  "The pass over the satisfiable components of the network of `calc` visible from
  `context`: `tighten` of the network as read when it is satisfiable, else `pass` of what
  `split` leaves."
  [calc kb context]
  (let [net (network kb calc context)
        pc  (tighten kb calc context net nil)]
    (if-let [sat (:net (split kb calc context net))]
      (pass kb calc context sat nil)
      pc)))

;; ---- the prover ----------------------------------------------------------

(defn- negated-literal
  "The literal a `(not (P a b))` goal negates, or nil for anything else."
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

(defn typed-admits?
  "Do the types `context` sees declared of `pred`'s two positions admit `x` and `y`
  (`res/arg-admits-fn`)?  True for a `pred` that `calc` does not name `:typed`.  The
  admission `solve-goal` asks of a positive goal, for a caller re-deciding one answer."
  [calc kb pred x y context]
  (or (not (contains? (:typed calc) pred))
      (let [admits? (res/arg-admits-fn kb pred context)]
        (and (admits? x 0) (admits? y 1)))))

(defn- solve-goal
  "Solutions for a goal `(P a b)` or `(not (P a b))` in `context`, read off the
  path-consistent network: entailment `possible ⊆ denotation(P)` for the positive,
  refutation `possible ∩ denotation(P) = ∅` for the negative, nothing for a goal naming a
  node of an unsatisfiable component, whose nodes no variable binds (`split`).  A positive goal on a `:typed` predicate also needs each argument
  admitted by its declared types (`res/arg-admits-fn`).  The four goal shapes are
  docs/qcn.md's, \"Reading out\".

  `pairs`, when given, enumerates those pairs in place of the nodes; only a caller that
  has acted on the answers it leaves out (`join-delta`) passes it.  `pairs` is ignored when
  the goal names a node `with-goal-nodes` adds."
  ([calc kb goal context] (solve-goal calc kb goal context nil))
  ([calc kb goal context pairs]
   (let [neg?  (some? (negated-literal goal))
         [pred a b] (claimed-literal calc goal)
         denot ((:denotation calc) pred)
         extra (remove pvar? [a b])
         [net pc extended? blocked] (tighten-for-goal kb calc context extra)
         pairs (when-not extended? pairs)]
     (when-not (or (= pc :inconsistent) (some #(contains? blocked %) extra))
       (let [admits? (when (and (not neg?) (contains? (:typed calc) pred))
                       (res/arg-admits-fn kb pred context))
             holds?  (fn [x y]
                       (let [poss (constraint calc pc x y)]
                         (and (seq poss)
                              (if neg?
                                (empty? (set/intersection poss denot))
                                (set/subset? poss denot))
                              (or (nil? admits?) (and (admits? x 0) (admits? y 1))))))
             answer (fn [x y] (cond-> {} (pvar? a) (assoc a x) (pvar? b) (assoc b y)))]
         (if pairs
           ;; `(P ?x ?x)` reads only a diagonal pair, which `pairs` holds when the caller
           ;; adds it (`solve-with-support`)
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

(defn- lifted-predicates
  "The calculus predicates `goal`'s predicate sits above by `genl`, as `context` sees the
  edges, when `goal` is a positive binary literal on a predicate the calculus does not
  answer; else nil.  `(genl subintervalOf subtimeOf)` and `(genl subtimeOf partOf)` make
  every `subintervalOf` tuple a `subtimeOf` and a `partOf` tuple, so a goal on either
  lifts to `subintervalOf`."
  [calc kb goal context]
  (when (and (sequential? goal) (= 3 (count goal)))
    (let [q (first goal)]
      (when (and (symbol? q) (not (pvar? q)) (not= sx/not-functor q)
                 (not (contains? (:predicates calc) q)))
        ;; most predicates have no spec, so the one closure read answers them
        (let [specs (tax/specs (reasoning/taxonomy kb) q context)]
          (when (< 1 (count specs))
            (seq (sort (filter #(contains? (:predicates calc) %) specs)))))))))

(defn- answered-goals
  "The calculus goals `goal` is answered by: `goal` itself when the calculus claims it,
  else one `(P a b)` per calculus predicate P the goal's predicate lifts to."
  [calc kb goal context]
  (if (claimed-literal calc goal)
    [goal]
    (map #(list % (nth goal 1) (nth goal 2)) (lifted-predicates calc kb goal context))))

(defrecord CalculusProver [calculus]
  prover-types/Prover
  ;; either polarity of a calculus predicate, and a positive goal on a super-predicate
  ;; of one (`lifted-predicates`)
  (applicable? [_ kb goal context]
    (or (some? (claimed-literal calculus goal))
        (some? (lifted-predicates calculus kb goal context))))
  ;; an upper bound from O(1) predicate-extent counts, never a network read
  (est-bindings [_ kb goal _]
    (let [[_ a b] (or (claimed-literal calculus goal) goal)
          n (max 1 (reduce + (map #(reads/stored-count-with-functor (:index kb) %)
                                  (:predicates calculus))))]
      (cond (and (pvar? a) (pvar? b)) (* n n)
            (or (pvar? a) (pvar? b))  n
            :else                     1)))
  (cost [_ _ _ _] :compute)
  ;; 100 for a claimed goal (docs/qcn.md, "Cost, completeness, registration"); a lifted
  ;; goal's super-predicate has stored tuples and other specs the network does not read
  (completeness [_ _ goal _]
    (if (claimed-literal calculus goal) 100 50))
  ;; a variable context fans over the readers (docs/defenses.md, "A variable context goal
  ;; fans over readers rather than reading one unioned network")
  (solve [_ kb goal context]
    (let [goals (answered-goals calculus kb goal context)
          one   (fn [g]
                  (if (pvar? context)
                    (mapcat #(solve-goal calculus kb g %) (reader-contexts kb calculus))
                    (solve-goal calculus kb g context)))]
      (if (and (= 1 (count goals)) (not (pvar? context)))
        (one (first goals))
        (distinct (mapcat one goals)))))
  prover-types/SupportingProver
  ;; empty: a forward join reads a calculus through `qcn-kb/solve-with-support` instead
  (support-functors [_] #{})
  (support-sources  [_] #{})
  (solve-with-support [_ kb goal context]
    (let [tx    (reasoning/taxonomy kb)
          class #(jtms/defeat-class (reasoning/tms kb) %)
          one   (fn [g ctx]
                  (let [[p a b] (claimed-literal calculus g)
                        diag?   (nil? (negated-literal g))
                        lift    (when (not= g goal)
                                  (map first (tax/reach-support tx :genl p (first goal) ctx class)))]
                    (for [bnd (solve-goal calculus kb g ctx)
                          :let [x (if (pvar? a) (get bnd a) a)
                                y (if (pvar? b) (get bnd b) b)
                                s (support calculus kb ctx x y)]]
                      [bnd (into (if (and diag? (= x y) (empty? s))
                                   (res/declared-by kb :reflexive p ctx)
                                   s)
                                 lift)])))]
      (distinct (for [g   (answered-goals calculus kb goal context)
                      ctx (if (pvar? context) (reader-contexts kb calculus) [context])
                      ans (one g ctx)]
                  ans)))))

(defn prover
  "The entailment prover for `calc`, to register with `vaelii.core/add-prover`."
  [calc]
  (->CalculusProver calc))

(defn prover-for?
  "Is `pr` the prover of the calculus named `nm`?"
  [nm pr]
  (and (instance? CalculusProver pr) (= nm (:name (:calculus pr)))))

;; ---- what forward chaining joins on --------------------------------------
;; docs/qcn.md, "Forward chaining too, on a relation nobody stored".

(defonce ^{:private true
           :doc "`registered-calculi`'s last answer as `[registry answer]`, compared by
  `identical?` against the prover vector.  One slot: every KB opens on the same
  `provers/default-provers` vector, and a map keyed on registries would hold every vector
  `add-prover` ever made.  A lost race costs a recomputation."}
  registry-calculi
  (volatile! nil))

(defn registered-calculi
  "The calculi whose prover is registered on `kb`, memoized against the registry's
  identity (`registry-calculi`)."
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
  "The registered calculus whose `:predicates` holds `pred`, or nil; a predicate belongs
  to one calculus.  A predicate that only moves a network is `calculi-triggered-by`'s."
  [kb pred]
  (first (filter #(contains? (:predicates %) pred) (registered-calculi kb))))

(defn converse-entailed?
  "Does `calc`'s network entail `(p a b)` from every believed `(q b a)`: does `calc` own
  `p` and `q`, with the algebra's converse of `q`'s denotation inside `p`'s?  A believed
  `(inverse p q)` the converse table implies is then a source the network already reads
  (`provers/shadowing-channels`)."
  [calc p q]
  (let [den (:denotation calc)]
    (boolean (and (contains? den p) (contains? den q)
                  (set/subset? ((:converse (:algebra calc)) (den q)) (den p))))))

(defn calculi-triggered-by
  "Every registered calculus one of whose `:trigger-predicates` is `pred` or a
  super-predicate of it by the global `genls` closure, or nil.  Every one, not the first:
  one predicate can move two networks.  A caller holding `(genl sub super)` asks it of
  `super`."
  [kb pred]
  (let [cs (registered-calculi kb)]
    (when (seq cs)
      (let [ups (if (symbol? pred) (tax/genls-global (reasoning/taxonomy kb) pred) [pred])]
        (not-empty (filterv (fn [c] (let [tp (:trigger-predicates c)] (some #(contains? tp %) ups)))
                            cs))))))

;; ---- what a write moved --------------------------------------------------
;; docs/qcn.md, "Reporting an impossible network".

(defn calculi-moved-by
  "The registered calculi a believed sentex among `handles` moves, in registration order:
  those its body's functor triggers (`calculi-triggered-by`), those a `genl` edge's
  supertype triggers, and every one for a `genlCx` edge, which puts two contexts' facts in
  one reader.  A rule moves none.  `[]` when no calculus is registered, before any
  handle is read."
  [kb handles]
  (let [cs (registered-calculi kb)]
    (if (empty? cs)
      []
      (let [tms   (reasoning/tms kb)
            moved (into #{}
                        (comp (filter #(jtms/in? tms %))
                              (keep #(p/get-sentex (:records kb) %))
                              (remove :antecedent)
                              (mapcat (fn [s]
                                        (let [b (sx/underlying-body (sx/sentence-of s))
                                              f (when (sequential? b) (first b))]
                                          (cond
                                            (not (symbol? f)) nil
                                            (= 'genlCx f)     cs
                                            (= 'genl f)       (calculi-triggered-by kb (nth b 2 nil))
                                            :else             (calculi-triggered-by kb f))))))
                        handles)]
        (filterv moved cs)))))

(defn- engine-read?
  "Is `f` a functor of core.txt's vocabulary that the engine reads (`pr/entry`), other than
  a type, whose membership names no pair, and an inert term?"
  [f]
  (let [e (pr/entry f)]
    (boolean (and (:shape e) (not (contains? (:facets e) :inert))))))

(defn- region-facts
  "The constraints the settle region `region` adds to the networks of `calc`, as
  `[{:context ctx :rels #{base relation} :a node :b node}]`, or nil when a member may move
  a network in some other way.  A member moves none when it is a rule, a fact on no
  predicate `calc` triggers, or a fact of `calc` naming a term that is no node.  nil for a
  member that is OUT or gone, a sentence on a functor `engine-read?` holds of (a `genl` or
  `genlCx` edge, an `except`, a defeat, an equality edge), a fact on a sub-predicate or a narrowing's
  source, and for every region of a calculus with a narrowing."
  [kb {:keys [algebra denotation predicates narrowing node?] :as calc} region]
  (when-not narrowing
    (let [tms      (reasoning/tms kb)
          universe (:universe algebra)]
      (reduce
       (fn [acc h]
         (let [s (when (jtms/in? tms h) (p/get-sentex (:records kb) h))
               b (when s (sx/underlying-body (sx/sentence-of s)))
               f (when (sequential? b) (first b))]
           (cond
             (nil? s)                            (reduced nil)
             (:antecedent s)                     acc
             (not (symbol? f))                   (reduced nil)
             (contains? predicates f)
             (let [[_ a c] b]
               (if (and (= 3 (count b)) (node? a) (node? c))
                 (conj acc {:context (:context s) :a a :b c
                            :rels    (if (sx/negative? s)
                                       (set/difference universe (denotation f))
                                       (denotation f))})
                 acc))
             (engine-read? f)                    (reduced nil)
             (some #(identical? calc %) (calculi-triggered-by kb f)) (reduced nil)
             :else                               acc)))
       [] region))))

(defn- settled
  "The settle's record of `calc`: `{:calculus :clock :governing #{ctx} :closed {ctx
  pass}}`, `:closed` the pass over each governing context's network, a closed network or
  `:inconsistent`.  nil when none is held for this calculus value."
  [kb calc]
  (let [st (some-> (reasoning/qcn-joined kb) deref (get-in [::settled (:name calc)]))]
    (when (identical? calc (:calculus st)) st)))

(defn- current-settled
  "`settled` while the change clock has not moved since the settle recorded it, else nil."
  [kb calc]
  (let [st (settled kb calc)]
    (when (and st (== (observe/change-clock) (long (:clock st)))) st)))

(defn- read-pass
  "`tighten` of the network of `calc` at `context` as read, which files the ledger entry of
  an unsatisfiable one."
  [kb calc context]
  (tighten kb calc context (network kb calc context) nil))

(defn- settle-whole
  "The settle's record of `calc` read from the KB: every governing context's network,
  read and tightened."
  [kb calc]
  (let [gov (governing-contexts kb calc)]
    {:governing gov
     :closed    (into {} (map (fn [ctx] [ctx (read-pass kb calc ctx)])) gov)}))

(defn- settle-facts
  "The settle's record of `calc` after `facts` (`region-facts`) arrive over the record
  `st`.  A governing context whose network a fact reaches is closed again from its
  recorded pass with the facts' constraints intersected in (`qcn/path-consistent-from`),
  and one a fact adds to the governing contexts is read whole.  A context that closes
  `:inconsistent` is read and tightened, which files its ledger entry and replaces a
  recorded pass a withdrawal the region cannot show left too tight."
  [kb {:keys [algebra] :as calc} st facts]
  (let [tx  (reasoning/taxonomy kb)
        gov (:governing st)
        gov (if (every? #(contains? gov (:context %)) facts)
              gov
              (tax/meet-closure tx (into gov (map :context) facts)))
        universe (:universe algebra)
        converse (:converse algebra)]
    {:governing gov
     :closed
     (into {}
           (map (fn [ctx]
                  (let [prior (get (:closed st) ctx ::absent)
                        up    (tax/context-up tx ctx)
                        delta (reduce (fn [d {:keys [context rels a b]}]
                                        (if (contains? up context)
                                          (narrow d universe converse rels a b)
                                          d))
                                      {} facts)]
                    [ctx (cond
                           (= ::absent prior)       (read-pass kb calc ctx)
                           (empty? delta)           prior
                           (= :inconsistent prior)  (read-pass kb calc ctx)
                           :else
                           (let [r (qcn/path-consistent-from delta prior nil algebra)]
                             (if (map? r) r (read-pass kb calc ctx))))])))
           gov)}))

(defn settles?
  "Does the settle owe `report-moved!` a call: a calculus is registered, or a record of
  one is held?  False on a KB with neither, so its settle reads no region for it."
  [kb]
  (boolean (when-let [a (reasoning/qcn-joined kb)]
             (or (seq (registered-calculi kb)) (contains? @a ::settled)))))

(defn report-moved!
  "Ask every governing context of each calculus the settle region moves whether its
  network is unsatisfiable, so `tighten` files the ledger entry of a newly unsatisfiable
  one, and record each answer for the next settle and for `unsatisfiable-write`.
  `region` is the relabelled handles, `extra` the members no relabel recorded.  A region
  whose every member `region-facts` reads closes the recorded passes again from the
  facts' constraints, with no network read; any other region reads each governing
  context's network whole for a calculus it moves (`calculi-moved-by`), and drops the
  record of one it does not.  The record of a calculus no longer registered is dropped.
  See docs/qcn.md, \"The settle asks every write\".  Returns nil."
  [kb region extra]
  (when (settles? kb)
    (let [moved (set (calculi-moved-by kb (into region extra)))
          now   (fn [calc st] (when st (assoc st :calculus calc :clock (observe/change-clock))))
          recs  (reduce
                 (fn [m calc]
                   (let [st    (settled kb calc)
                         facts (when (and st (empty? extra)) (region-facts kb calc region))
                         st'   (cond
                                 facts                  (if (seq facts) (settle-facts kb calc st facts) st)
                                 (contains? moved calc) (settle-whole kb calc)
                                 :else                  nil)]
                     (if st' (assoc m (:name calc) (now calc st')) m)))
                 {} (registered-calculi kb))]
      (swap! (reasoning/qcn-joined kb) assoc ::settled recs)))
  nil)

(defn forget-settled
  "Drop the settle's record of every calculus, for a settle whose region does not name
  every move (a rebuild's)."
  [kb]
  (some-> (reasoning/qcn-joined kb) (swap! dissoc ::settled))
  nil)

(defn- governing
  "The governing contexts of `calc` the settle recorded, while current, else read."
  [kb calc]
  (or (:governing (current-settled kb calc)) (governing-contexts kb calc)))

(defn- settled-satisfiable?
  "Did the settle record a satisfiable network for `calc` at `context`, with no mutation
  since?"
  [kb calc context]
  (map? (get (:closed (current-settled kb calc)) context)))

(defn fed-inconsistencies
  "The `:qualitative-inconsistency` entries a feed event over the believed `handles`
  carries: one per governing context of each calculus they move whose network is
  unsatisfiable, once per network per KB and context (`observe/newly-seen?` under its own
  key, apart from the ledger's).  In content order of the context."
  [kb handles]
  (vec (for [calc (calculi-moved-by kb handles)
             ctx  (nm/sort-by-content-key identity (governing kb calc))
             :when (not (settled-satisfiable? kb calc ctx))
             :let [net (network kb calc ctx)]
             :when (and (= :inconsistent (tighten kb calc ctx net nil))
                        (observe/newly-seen? (reasoning/qcn kb) [(:name calc) ctx ::fed] net))]
         (inconsistency-entry kb calc ctx net))))

(defn unsatisfiable-write
  "The first unsatisfiable component, at a governing context of a calculus `handles`
  move, whose blamed handles (`unsatisfiable-components`' `:culprits`) include one of
  `handles`: `{:calculus :context :nodes :pairs :culprits}`, or nil.  Calculi in
  registration order, contexts and components in content order.  A component no handle
  of `handles` is blamed for was unsatisfiable without them.  A context the settle
  recorded as satisfiable, with no mutation since, is not read."
  [kb handles]
  (let [hs (set handles)]
    (first (for [calc (calculi-moved-by kb hs)
                 ctx  (nm/sort-by-content-key identity (governing kb calc))
                 :when (and (not (settled-satisfiable? kb calc ctx))
                            (inconsistent? calc kb ctx))
                 comp (nm/sort-by-content-key #(nm/print-key (nm/by-print-key (:nodes %))) compare
                                              (unsatisfiable-components calc kb ctx))
                 :when (some hs (:culprits comp))]
             (assoc comp :calculus (:name calc) :context ctx)))))

(defn solve-with-support
  "Entailed solutions for the positive literal `goal` in `context`, each paired with the
  handles it rests on: a seq of `[bindings #{handle}]`.  The diagonal at a node rests on
  the believed `(reflexive P)` statements `context` sees (`res/declared-by`) and a fact
  naming the node, one solution per such fact (`node-statements`), so placement sees where
  the node is.  A goal on two distinct variables answers the diagonal too, so the
  antecedent that binds first decides no firing.  A solution with empty support is
  dropped.  `pairs` narrows the enumeration as in `solve-goal`, with the diagonal of every
  node it names."
  ([calc kb goal context] (solve-with-support calc kb goal context nil))
  ([calc kb goal context pairs]
   (let [[p a b] goal
         decls  (res/declared-by kb :reflexive p context)
         stated (delay (node-statements kb calc context))
         pairs  (if (and pairs (seq decls)) (into pairs (comp cat (map #(vector % %))) pairs) pairs)
         sols   (cond-> (solve-goal calc kb goal context pairs)
                  (and (seq decls) (nil? pairs) (pvar? a) (pvar? b) (not= a b))
                  (concat (map #(assoc % b (get % a)) (solve-goal calc kb (list p a a) context nil))))]
     (for [bnd sols
           :let [x (if (pvar? a) (get bnd a) a)
                 y (if (pvar? b) (get bnd b) b)
                 s (support calc kb context x y)]
           sup (cond (seq s)                     [s]
                     (and (= x y) (seq decls))   (map #(into decls %) (get @stated x))
                     :else                       nil)]
       [bnd sup]))))

;; ---- what the passes hold, declared -------------------------------------
;; Process rows: both caches hang off the calculus value, which KBs share.  The limit is
;; per calculus; the count is across all of them.

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
                 "answer. Held per calculus, so the limit is per calculus and the count "
                 "here is the total across them.")
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
                 "would otherwise pay to propagate what nothing reads. Held per calculus, "
                 "so the limit is per calculus and the count here is the total across "
                 "them.")
  :read     (fn [_] {:entries (calculus-cache-total :support-cache)})
  :clear    (fn [_] (clear-calculus-cache :support-cache))
  :trim     (fn [_ target] (trim-calculus-cache :support-cache target))})

(caches/register-derived
 {:id :R4 :label "QCN join baselines and settled passes" :kind :cache :keyed-by :context
  :reads [:R3 :M1 :records]
  :holds-content? false
  :retired-by {:cleared :W} :computed :write :imaged? false :at [[:qcn-joined]]
  :note "one re-join baseline per calculus and reader context, compared by identity, and the settle's pass per calculus and governing context (`report-moved!`), dropped by a rebuild's settle; never trimmed"})

(caches/register-derived
 {:id :K4 :label "Path-consistency and support passes" :cache :path-consistency
  :holds-content? false
  :kind :cache :keyed-by :value :reads []
  :retired-by {:caches-cleared :W} :computed :read :imaged? false :var #'built-calculi
  :value (fn [_] (into {} (map (fn [[nm c]] [nm [(some-> (:pc-cache c) deref)
                                                 (some-> (:support-cache c) deref)]]))
                       @built-calculi))
  :note "per calculus, keyed by network value (also registered as `:network-support`); cleared at the bound"})

(caches/register-derived
 {:id :K11 :label "Calculus registry memo" :kind :cache :keyed-by :value :reads []
  :holds-content? false
  :retired-by (caches/on-every :I) :computed :read :imaged? false :var #'registry-calculi
  :value (fn [_] @registry-calculi)
  :note "one slot, compared by identity against the prover registry of the KB read; a read of a KB holding another registry replaces it"})

(caches/register-derived
 {:id :K12 :label "Built calculi" :kind :cache :keyed-by :value :reads []
  :holds-content? false
  :retired-by {} :computed :read :imaged? false :var #'built-calculi
  :value (fn [_] (set (keys @built-calculi)))
  :note "the calculi built in this process by name, each holding the K4 caches; replaced by name"})
