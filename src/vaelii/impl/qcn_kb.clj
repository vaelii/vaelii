;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.qcn-kb
  "The KB half every calculus over `vaelii.impl.qcn` shares: a calculus value
  (`calculus`), the believed facts of one reader context read into a resident network,
  the passes over it, entailment and refutation as prover solutions, the support an
  entailment rests on, and the delta a forward re-join runs over.  See docs/qcn.md."
  (:require [clojure.set :as set]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.except :as exc]
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

;; `{name calculus}` for every calculus built in this process, which the cache rows below
;; sum over; keyed by name so a reloaded calculus replaces its entry.
(defonce ^:private built-calculi (atom {}))

(defn built-calculi-values
  "Every calculus built in this process, one per name."
  []
  (vals @built-calculi))

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
     :pair       (fn [kb context a b support?] → [#{base relations} #{handle}] | nil)
     :node?      which terms are nodes, when not every node is a symbol
     :bindings   the dynamic vars `:fn` reads, whose values key the resident network
     :sources    every predicate whose arrival or departure moves what it answers
     :contexts   the subset that puts a NODE in the network, so names a reader context}

  `with-goal-nodes` runs `:over-nodes` over a goal's nodes too.  Any key may be absent.
  `:sources` and `:contexts` fold into `:trigger-predicates` and `:context-predicates`.
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
  "Every `[handles a b]` for which `(pred a b)` is believed at `context`,
  through the matcher's spec fan.  `handles` is the fact, then for a sub-predicate fact
  the `genl` edges of one path up to `pred` that `context` sees (`tax/reach-support`).
  `[pos node]` keeps the facts holding `node` at argument `pos`, read off its argument
  index."
  ([kb node? pred context] (asserted-pairs kb node? pred context nil))
  ([kb node? pred context [pos node]]
   (let [tx     (reasoning/taxonomy kb)
         reader (when-not (pvar? context) context)
         class  #(jtms/defeat-class (reasoning/tms kb) %)]
     (for [m (res/matches-visible kb (list pred (if (= 1 pos) node '?a) (if (= 2 pos) node '?b))
                                  context)
           :let [bnd (second m)
                 a   (if (= 1 pos) node (get bnd '?a))
                 b   (if (= 2 pos) node (get bnd '?b))]
           :when (and (node? a) (node? b))
           :let [s (or (nth m 2 nil) (p/get-sentex (:records kb) (first m)))
                 f (nm/functor (sx/sentence-of s))]]
       [(into [(first m)]
              (when (not= f pred)
                (map first (tax/reach-support tx :genl f pred reader class))))
        a b]))))

(defn- refuted-pairs
  "Every `[handle a b]` for which `(not (pred a b))` is IN, stored in a context `context`
  sees and not removed there (`exc/without-excepted`), read off `pred`'s own predicate extent with no spec fan (docs/qcn.md,
  \"Negation\").  A fact about a spelling merge-retired for `context` is dropped, as the
  positive read drops one (`res/retired-for?`).  `[pos node]` reads the facts holding
  `node` at argument `pos` instead of the whole extent."
  ([kb node? pred context] (refuted-pairs kb node? pred context nil))
  ([kb node? pred context [pos node]]
   (let [ix       (:index kb)
         up       (when-not (pvar? context) (tax/context-up (reasoning/taxonomy kb) context))
         merged?  (tax/merged-term-pred (reasoning/taxonomy kb))
         visible  (delay (res/visible-supporter-fn kb context))
         retired? (if (and merged? (symbol? context) (not (pvar? context)))
                    #(res/retired-for? kb visible merged? (sx/sentence-of %))
                    (constantly false))]
     (->> (if pos (reads/as-stored-with-args ix pred [[pos node]]) (reads/as-stored-with-functor ix pred))
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
          (exc/without-excepted kb context)))))

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

(defn- stated-rows
  "`[[rels [handles a b]]]`: the believed facts of `calc` visible from `context`, both
  polarities, each with the relations it leaves its pair.  `bound` (`[pos node]`) keeps
  those holding `node` at argument `pos`."
  [kb {:keys [algebra denotation predicates node?]} context bound]
  (let [universe (:universe algebra)]
    (into []
          (mapcat (fn [pred]
                    (let [denot (denotation pred)]
                      (concat (map #(vector denot %) (asserted-pairs kb node? pred context bound))
                              ;; what a believed `(not (pred a b))` leaves; converse commutes with it
                              (map #(vector (set/difference universe denot) %)
                                   (refuted-pairs kb node? pred context bound))))))
          predicates)))

(defn- absorb-rows
  "`{:net :support :handles}` holding `rows` (`stated-rows`), each intersected into its pair."
  [{:keys [algebra]} rows]
  (let [universe (:universe algebra)
        converse (:converse algebra)]
    (reduce (fn [state [rels [h a b]]]
              (let [hs (if (coll? h) h [h])]
                (-> state
                    (update :net narrow universe converse rels a b)
                    (update :support #(reduce (fn [sup h] (support-pair sup h a b)) % hs))
                    (update :handles into hs))))
            {:net {} :support {} :handles #{}}
            rows)))

(defn- build-network
  "`{:net <network> :support <{[a b] → #{handle}} :handles #{handle}}`, `:handles` the
  union of the support, plus `:unsatisfiable-sources` when a narrowing's source is
  unsatisfiable.  The calculus's predicates, both polarities, then the narrowing.  A
  variable `context` reads each fact as its own context believes it (`exc/*unscoped-own*`)."
  [kb {:keys [algebra narrowing] :as calc} context]
  (binding [exc/*unscoped-own* (or exc/*unscoped-own* (pvar? context))]
    (let [universe (:universe algebra)
          stated   (absorb-rows calc (stated-rows kb calc context nil))
          read-kb (if-let [f (:fn narrowing)]
                    (absorb-narrowing stated (f kb context) universe)
                    stated)]
      (if-let [f (:over-nodes narrowing)]
        (absorb-narrowing read-kb (f (nodes (:net read-kb))) universe)
        read-kb))))

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
  (observe/cached (:clock kb) (reasoning/qcn kb)
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
  is the universe.  A variable `context` reads every context's facts, each as its own
  context believes it, into one diagnostic network that answers no goal."
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
   (:clock kb) (reasoning/qcn kb) [(:name calc) ::statements context]
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
   (:clock kb) (reasoning/qcn kb) [(:name calc) k]
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

(defn- resident-pass
  "`(build stale)`, held on the KB under `k` and the change clock beside `net`, answered
  while `net` is `identical?` to the held one; a different `net` gets `(build nil)`.
  `stale` is the replaced entry, `{:net … :result …}` or nil."
  [kb k net build]
  (let [entry (observe/cached (:clock kb) (reasoning/qcn kb) k
                              (fn [stale]
                                (if (identical? net (:net stale))
                                  stale
                                  {:net net :result (build stale)})))]
    (if (identical? net (:net entry)) (:result entry) (build nil))))

(defn tighten
  "Path consistency over `net`, a network as `network` reads it or one `with-goal-nodes`
  extended, memoized on the network value with `resident-pass` in front, warm-started
  (`qcn/path-consistent-from`) when `net` narrows the resident network.  `extra` is the
  goal's nodes beyond `net`'s; only a miss reads `net`'s own nodes.  A read files nothing:
  the settle places an unsatisfiable component (`unsatisfiable-regions`)."
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

(defn- component-pass
  "`tighten` over `net` with no resident entry in front, memoized in the calculus's
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
  through `tighten`; an unsatisfiable one is answered as its satisfiable components
  (`split`), which a goal naming a blocked node does not extend.  A goal node cannot make a satisfiable network
  unsatisfiable: a moment or a calendar term is placed by its fields among the others, and
  a point is constrained only by its own thing's order."
  [kb calc context extra]
  (let [base    (network kb calc context)
        pc      (tighten kb calc context base extra)
        {:keys [blocked] sat :net} (when (= :inconsistent pc) (split kb calc context base))
        read    (or sat base)
        pc      (if sat (tighten kb calc context sat extra) pc)
        net     (if (or (= :inconsistent pc) (some #(contains? blocked %) extra))
                  read
                  (with-goal-nodes calc read extra))]
    (if (identical? net read)
      [net pc false blocked]
      [net (tighten kb calc context net extra) true blocked])))

(defn constraint
  "The constraint set on `[i j]` in `net`: the identity on the diagonal, the recorded
  set, else the universe (unknown)."
  [calc net i j]
  (qcn/constraint net (:algebra calc) i j))

(defn possible-among
  "A fn of two of `nodes` answering the base relations still possible between them given
  everything believed in `context`, read off one pass over the network with `nodes`
  added.  It answers `#{}` for every pair when a node lies in an unsatisfiable component."
  [calc kb context nodes]
  (let [[_ pc _ blocked] (tighten-for-goal kb calc context nodes)]
    (if (or (= pc :inconsistent) (some #(contains? blocked %) nodes))
      (constantly #{})
      (fn [a b] (constraint calc pc a b)))))

(defn- pair-reading
  "The calculus's `:pair` reading of `a` and `b`, `[relations handles]`, or nil."
  [calc kb context a b support?]
  (when-let [f (:pair (:narrowing calc))] (f kb context a b support?)))

(defn- pair-narrowed
  "`poss`, the relations the network leaves between `a` and `b`, intersected with what the
  calculus's `:pair` reading of the two answers, when it has one."
  [calc kb context a b poss]
  (if-let [[r] (pair-reading calc kb context a b false)]
    (set/intersection poss r)
    poss))

(defn possible
  "The base relations still possible between `a` and `b` given everything believed in
  `context`, narrowed by the calculus's `:pair` reading — `#{}` when either lies in an
  unsatisfiable component of the network."
  [calc kb context a b]
  (let [poss ((possible-among calc kb context [a b]) a b)]
    (cond->> poss (seq poss) (pair-narrowed calc kb context a b))))

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
  it, for one derivation.  The `:pair` reading's handles join them where it narrows what
  `possible` answers.  `#{}` when the pair is unconstrained or either node lies in an
  unsatisfiable component."
  [calc kb context a b]
  (let [r (resolved calc kb context [a b])]
    (if (:inconsistent r)
      #{}
      (let [s    (get (:support r) [a b] #{})
            poss (constraint calc (:network r) a b)
            [rels hs] (when (seq poss) (pair-reading calc kb context a b true))]
        (cond-> s (and rels (not (set/subset? poss rels))) (into hs))))))

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
  visible from `context`, every pair at once, with `nodes` added: `{:network … :support
  …}`.  A caller reading many pairs reads them here; `support` walks every pair per call."
  ([calc kb context] (resolved calc kb context nil))
  ([calc kb context nodes] (resolved calc kb context nodes)))

(defn closed-network
  "The pass over the satisfiable components of the network of `calc` visible from
  `context`: `tighten` of the network as read when it is satisfiable, else of what `split`
  leaves."
  [calc kb context]
  (let [net (network kb calc context)
        pc  (tighten kb calc context net nil)]
    (if-let [sat (:net (split kb calc context net))]
      (tighten kb calc context sat nil)
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
  node of an unsatisfiable component, whose nodes no variable binds (`split`).  A positive
  goal on a `:typed` predicate also needs each argument admitted by its declared types
  (`res/arg-admits-fn`).  The four goal shapes are docs/qcn.md's, \"Reading out\".

  `pairs`, when given, enumerates those pairs in place of the nodes; only a caller that
  has acted on the answers it leaves out (`join-delta`) passes it, and it is ignored when
  the goal names a node `with-goal-nodes` adds.  With `pair?`, `pair-narrowed` reads a
  ground goal the network leaves undecided."
  ([calc kb goal context] (solve-goal calc kb goal context nil true))
  ([calc kb goal context pairs pair?]
   (let [neg?  (some? (negated-literal goal))
         [pred a b] (claimed-literal calc goal)
         denot ((:denotation calc) pred)
         extra (remove pvar? [a b])
         [net pc extended? blocked] (tighten-for-goal kb calc context extra)
         pairs (when-not extended? pairs)]
     (when-not (or (= pc :inconsistent) (some #(contains? blocked %) extra))
       (let [admits? (when (and (not neg?) (contains? (:typed calc) pred))
                       (res/arg-admits-fn kb pred context))
             decides? (fn [poss] (if neg?
                                   (empty? (set/intersection poss denot))
                                   (set/subset? poss denot)))
             pair?   (and pair? (not-any? pvar? [a b]))
             holds?  (fn [x y]
                       (let [poss (constraint calc pc x y)
                             poss (cond->> poss
                                    (and pair? (seq poss) (not (decides? poss)))
                                    (pair-narrowed calc kb context x y))]
                         (and (seq poss)
                              (decides? poss)
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

(defrecord CalculusProver [calculus open-est]
  prover-types/Prover
  ;; either polarity of a calculus predicate, and a positive goal on a super-predicate
  ;; of one (`lifted-predicates`)
  (applicable? [_ kb goal context]
    (or (some? (claimed-literal calculus goal))
        (some? (lifted-predicates calculus kb goal context))))
  ;; `open-est` for an open goal, else a bound from O(1) predicate-extent counts (`prover`)
  (est-bindings [_ kb goal _]
    (let [[_ a b] (or (claimed-literal calculus goal) goal)
          open?   (or (pvar? a) (pvar? b))]
      (if (and open? open-est)
        open-est
        (let [n (max 1 (reduce + (map #(reads/stored-count-with-functor (:index kb) %)
                                      (:predicates calculus))))]
          (cond (and (pvar? a) (pvar? b)) (* n n)
                open?                     n
                :else                     1)))))
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
                    (for [bnd (solve-goal calculus kb g ctx nil false)
                          :let [x (if (pvar? a) (get bnd a) a)
                                y (if (pvar? b) (get bnd b) b)
                                s (support calculus kb ctx x y)]
                          sup (if (and diag? (= x y) (empty? s))
                                (res/declaration-supports kb (res/declared-by kb :reflexive p ctx) #{})
                                [s])]
                      [bnd (into sup lift)])))]
      (distinct (for [g   (answered-goals calculus kb goal context)
                      ctx (if (pvar? context) (reader-contexts kb calculus) [context])
                      ans (one g ctx)]
                  ans)))))

(defn prover
  "The entailment prover for `calc`, to register with `vaelii.core/add-prover`.  Its
  `est-bindings` reads no network: a ground goal is 1 and an open one is bounded by the
  stored facts on the calculus's predicates, or is `open-est` when given.  A calculus whose
  open answers the nodes do not list passes `provers/deferred-est` (docs/qcn.md, \"Cost,
  completeness, registration\")."
  ([calc] (prover calc nil))
  ([calc open-est] (->CalculusProver calc open-est)))

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

;; ---- the conflicted regions -------------------------------------------
;; docs/qcn.md, "An impossible network is a stored contradiction".

(defn- component-read
  "`absorb-rows` of the component of `calc`'s network visible from `context` that holds
  `seed`: the facts naming a node reached so far, read off each node's argument index, until
  no fact names a new node.  Its cost is what the component holds.  For a calculus with no
  narrowing, whose network is its facts alone."
  [kb calc context seed]
  (loop [seen #{seed}, todo [seed], rows #{}]
    (if-let [n (peek todo)]
      (let [found (into [] (mapcat #(stated-rows kb calc context [% n])) [1 2])
            new   (into [] (comp (mapcat (fn [[_ [_ a b]]] [a b])) (distinct) (remove seen)) found)]
        (recur (into seen new) (into (pop todo) new) (into rows found)))
      (absorb-rows calc rows))))

(defn- touched-components
  "`[{:nodes :net :support :sources}]`: the components of `calc`'s network visible from
  `context` holding a node of `touched`, or every one when `touched` is nil, `:sources` the
  narrowing's unsatisfiable sources a pair of the component stands in for.  A calculus with
  no narrowing reads each touched component alone (`component-read`); one with a narrowing
  reads the network whole (`read-network`)."
  [kb calc context touched]
  (if (and touched (nil? (:narrowing calc)))
    (loop [ts (seq touched), done #{}, acc []]
      (if-let [[t & more] ts]
        (if (contains? done t)
          (recur more done acc)
          (let [{:keys [net support]} (component-read kb calc context t)
                ns (into #{t} (nodes net))]
            (recur more (into done ns)
                   (cond-> acc (seq net) (conj {:nodes ns :net net :support support})))))
        acc))
    (let [{:keys [net support unsatisfiable-sources]} (read-network kb calc context)]
      (into []
            (keep (fn [ns]
                    (when (or (nil? touched) (some #(contains? ns %) touched))
                      {:nodes   ns
                       :net     (qcn/select-nodes net ns)
                       :support support
                       :sources (filterv (fn [src] (some #(contains? ns (first %)) (:stand-in src)))
                                         unsatisfiable-sources)})))
            (qcn/components net)))))

(defn unsatisfiable-regions
  "The conflicted regions of the network of `calc` visible from `context`: each connected
  component (`touched-components`) holding a node of `touched`, or every one when `touched`
  is nil, whose pass is unsatisfiable, as `{:nodes #{node} :pairs #{[a b]} :sources […]
  :members #{handle}}`.  `:pairs` is the component's pairs unsatisfiable as written, less
  those a narrowing's unsatisfiable source emptied, and `:sources` those sources as
  `reported-sources` names them.  `:members` is the support of its pairs, a source's
  support for a pair it emptied included.  The pass runs over each such component alone,
  memoized on its value (`component-pass`).  `[]` for a variable `context`."
  [calc kb context touched]
  (if (pvar? context)
    []
    (into []
          (keep (fn [{:keys [nodes net support sources]}]
                  (when (= :inconsistent (component-pass calc net))
                    {:nodes   nodes
                     :pairs   (reduce #(set/difference %1 (:stand-in %2))
                                      (qcn/unsatisfiable-pairs net (:algebra calc)) sources)
                     :sources (mapv #(-> % (dissoc :stand-in) (update :support (comp vec sort)))
                                    sources)
                     :members (into #{} (mapcat #(get support %)) (keys net))})))
          (touched-components kb calc context touched))))

(defn solve-with-support
  "Entailed solutions for the positive literal `goal` in `context`, each paired with the
  handles it rests on: a seq of `[bindings #{handle}]`.  The diagonal at a node rests on
  a believed `(reflexive P)` statement `context` sees (`res/declaration-supports`) and a
  fact naming the node, one solution per such pair (`node-statements`), so placement sees
  where the node is.  A goal on two distinct variables answers the diagonal too, so the
  antecedent that binds first decides no firing.  A solution with empty support is
  dropped.  `pairs` narrows the enumeration as in `solve-goal`, with the diagonal of every
  node it names."
  ([calc kb goal context] (solve-with-support calc kb goal context nil))
  ([calc kb goal context pairs]
   (let [[p a b] goal
         decls  (res/declared-by kb :reflexive p context)
         stated (delay (node-statements kb calc context))
         pairs  (if (and pairs (seq decls)) (into pairs (comp cat (map #(vector % %))) pairs) pairs)
         sols   (cond-> (solve-goal calc kb goal context pairs false)
                  (and (seq decls) (nil? pairs) (pvar? a) (pvar? b) (not= a b))
                  (concat (map #(assoc % b (get % a)) (solve-goal calc kb (list p a a) context nil false))))]
     (for [bnd sols
           :let [x (if (pvar? a) (get bnd a) a)
                 y (if (pvar? b) (get bnd b) b)
                 s (support calc kb context x y)]
           sup (cond (seq s)                     [s]
                     (and (= x y) (seq decls))   (mapcat #(res/declaration-supports kb decls %)
                                                         (get @stated x))
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
 {:id :R4 :label "QCN join baselines" :kind :cache :keyed-by :context
  :reads [:R3 :M1 :records]
  :holds-content? false
  :retired-by {:cleared :W} :computed :write :imaged? false :at [[:qcn-joined]]
  :note "one re-join baseline per calculus and reader context, compared by identity; never trimmed"})

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
