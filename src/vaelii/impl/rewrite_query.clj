;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.rewrite-query
  "Positive rewriteOf queries over reader representatives, above raw fact retrieval."
  (:require [vaelii.impl.decide.tuple :as tuple]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.impl.types.reasoning :as reasoning]))

(def consumer-key
  "The syntax-only T2 census: rule ids reading the positive rewrite view, not verdicts."
  :rewrite-view-consumers)

(defn- read-consumer-census
  "Census of rule ids across ALL contexts from two sparse index postings, not verdicts.
  Actual bindings and placement still check the reader; never scan all rule records."
  [kb generation]
  {:gen generation
   :antecedents (set (reads/as-stored-rules-by-antecedent-global (:index kb) 'rewriteOf))
   :watched (set (reads/watched-rules-on (:index kb) 'rewriteOf))})

(defn rebuild-consumers!
  "Rebuild the syntax census after recovery. No belief or rule body is inferred."
  [kb]
  (let [tx (reasoning/taxonomy kb)
        generation (inc (long (get-in @tx [consumer-key :gen] 0)))
        census (read-consumer-census kb generation)]
    (swap! tx assoc consumer-key census)
    census))

(defn note-consumer!
  "Mirror a rule-index change, idempotently, in the existing taxonomy atom.
  Called only in the reasoning/index phase, never by records-only edits. A missing
  older-image census stays cold until a sparse index reconstruction can fill it."
  [kb bucket handle present?]
  (let [tx (reasoning/taxonomy kb)
        before (get @tx consumer-key)]
    ;; Even swap! returning the identical value invokes the taxonomy's change
    ;; watch. Avoid that touch on an ordinary rule with no rewrite consumer.
    (when-not (and before (not (:cold? before))
                   (= present? (contains? (get before bucket #{}) handle)))
      (swap! tx
             (fn [t]
               (let [old (get t consumer-key)
                     next (if (or (nil? old) (:cold? old))
                            {:gen (inc (long (:gen old 0))) :cold? true}
                            (let [members (get old bucket #{})
                                  changed ((if present? conj disj) members handle)]
                              (if (= members changed)
                                old
                                (-> old (assoc bucket changed) (update :gen inc)))))]
                 (if (identical? old next) t (assoc t consumer-key next)))))))
  nil)

(defn possible-consumers?
  "Queue-only observer gate: no index read, including while an older image is cold."
  [kb]
  (let [c (get @(reasoning/taxonomy kb) consumer-key)]
    (boolean (or (nil? c) (:cold? c) (seq (:antecedents c)) (seq (:watched c))))))

(defn- consumer-census
  "Warm census, filling a missing older-image entry from the sparse index only once.
  A rule-index change moves its generation, so a concurrent fill cannot lose it."
  [kb]
  (let [tx (reasoning/taxonomy kb)]
    (loop []
      (let [old (get @tx consumer-key)]
        (if (and old (not (:cold? old)))
          old
          (let [fresh (read-consumer-census kb (long (:gen old 0)))
                result (swap! tx #(if (= old (get % consumer-key))
                                    (assoc % consumer-key fresh) %))]
            (if (= fresh (get result consumer-key)) fresh (recur))))))))

(def normalization-sources
  "Static normalizer sources. Value-predicate sources are discovered through fCP slots."
  '#{rewriteOf sameAs equals natFormula functionCorrespondingPredicate
     functionCorrespondingBinaryPredicate reifiable_function symmetric commutative
     commutativeInArgs associative idempotent meetFunctionOf distinctInArgAndRest
     modal_predicate quotedArg quotedArgAndRest genl genlInverse
     inverse genlCx except defeat})

(defn- normalization-source?
  "Could `source` move a rewrite read? This is discovery, not reader authority.
  Dynamic correspondence predicates are probed through indexed declaration slots
  only after the in-memory consumer gate, not on ordinary no-consumer writes."
  [kb source]
  (or (contains? normalization-sources source)
      (and (symbol? source) (nat-read/any-reifiable-functions? kb)
           (some #(seq (reads/as-stored-with-args (:index kb) res/correspondence-predicate {2 %}))
                 (concat (res/super-predicates kb source '?ctx)
                         (res/swapped-super-predicates kb source '?ctx))))))

(defn affected-consumers
  "The syntax census when a source can change this view, otherwise nil.
  Consumers rejoin in FULL: a rival alias can expose a fallback answer that does not
  rest on the rival's handle, so a supporting-only delta is not sound here."
  [kb source]
  (when (possible-consumers? kb)
    (let [census (consumer-census kb)]
      (when (and (or (seq (:antecedents census)) (seq (:watched census)))
                 (normalization-source? kb source))
        census))))

(defn endpoint
  "A rewriteOf endpoint read as a term by `reader`, never as an equation mention.
  Existing closed applications may resolve, but unknown ones remain written and no
  placeholder is allocated. The second representative walk covers a resolved alias.
  This does not change raw storage or the mention policy of any other equation."
  [kb reader term]
  (let [visible? (res/visible-supporter-fn kb reader)
        term (res/representative-term kb visible? term)]
    (binding [nat-read/*withheld* (nat-read/withheld-at kb reader)]
      (res/representative-term kb visible?
                               (nat-read/reify-existing kb term reader)))))

(defn endpoint-reading
  "The endpoint and the actual resolver readings used to compute it.
  This is evidence input, NOT yet a support certificate: tuple fan/permutation and
  source roles must be retained by the semantic consumer. No alternative resolver
  or allocation is introduced, and ordinary endpoint calls do not record events."
  [kb reader term]
  (let [events (atom [])
        record! #(swap! events conj %)
        visible? (res/visible-supporter-fn kb reader)
        representative (fn [x]
                         (let [value (res/representative-term kb visible? x)]
                           (record! {:operation :representative :term x :value value
                                     :supports (vec (res/representative-supports kb x visible?))})
                           value))
        value (binding [nat-read/*application-read* record!
                        res/*correspondence-read* record!
                        res/*normalization-read* record!]
                (let [term (representative term)]
                  (binding [nat-read/*withheld* (nat-read/withheld-at kb reader)]
                    (representative (nat-read/reify-existing kb term reader)))))]
    [value @events]))

(defn- spellings
  "An index-discovery superset, not a reader's equality authority."
  [kb term]
  (if (and (symbol? term) (not (sx/variable? term)))
    (conj (tax/equiv-class (reasoning/taxonomy kb) term) term)
    #{term}))

(defn- application-heads
  "Possible raw application heads whose value can read as `term`.
  Maps and correspondence value slots are identity witnesses only for discovery.
  Nothing here licenses a match: endpoint and stored visibility are checked later.
  Following heads also covers a raw compound function position reifying to a symbol."
  [kb term]
  (let [idx (:index kb)
        recs (:records kb)
        declarations (delay (res/believed-correspondences kb '?ctx (constantly true)))
        heads (fn heads [x]
                (cond
                  (and (symbol? x) (not (sx/variable? x))) #{x}
                  (seq? x) (heads (first x))
                  :else #{}))]
    (loop [todo [term], seen #{}, found #{}]
      (if (seq todo)
        (let [node (peek todo)]
          (if (contains? seen node)
            (recur (pop todo) seen found)
            (let [names (spellings kb node)
                  maps (for [name names
                             h (reads/as-stored-with-args idx 'natFormula {1 name})
                             :let [[_ _ e] (:sentence (p/get-sentex recs h))]
                             :when (seq? e)]
                         (first e))
                  functions (for [[f pred pos] @declarations
                                  :when (some #(seq (reads/as-stored-with-args idx pred {pos %})) names)]
                              f)
                  next-heads (into (heads node) (mapcat heads) (concat maps functions))]
              (recur (into (pop todo) next-heads) (conj seen node)
                     (into found next-heads)))))
        found))))

(defn- candidate-handles
  "Indexed positive rewrite candidates. A goal with no usable endpoint lead enumerates
  the rewrite extent, not the whole KB.
  The stored lhs is not compound (wff/equality-problems), so a bound canonical lhs leads
  directly from its spellings. A right-bound goal also discovers compound rhs heads
  through existing maps/correspondence value slots, including ambiguous alias cases."
  [kb goal]
  (let [prefix (sx/positional goal)
        [_ left right] prefix
        left? (< 1 (count prefix))
        right? (< 2 (count prefix))
        idx (:index kb)
        grounded? sx/ground-term?]
    (cond
      (sequential? left) #{}

      (and left? (grounded? left))
      (into #{} (mapcat #(reads/as-stored-with-args idx 'rewriteOf {1 %}))
            (spellings kb left))

      (and right? (grounded? right))
      (let [names (spellings kb right)]
        (into (into #{} (mapcat #(concat (reads/as-stored-with-args idx 'rewriteOf {1 %})
                                         (reads/as-stored-with-args idx 'rewriteOf {2 %}))) names)
              (mapcat #(reads/as-stored-with-term idx %))
              (application-heads kb right)))

      (and (seq? right) (grounded? (first right)))
      (into #{} (mapcat #(reads/as-stored-with-term idx %))
            (application-heads kb (first right)))

      :else (reads/as-stored-with-functor idx 'rewriteOf))))

(defn- endpoint-form
  "Read present positional endpoints, retaining any dotted tail for the unifier."
  [kb form reader capture?]
  (let [read-endpoint (if capture? endpoint-reading
                          (fn [kb reader term] [(endpoint kb reader term) nil]))
        prefix (sx/positional form)
        arguments (mapv (fn [position term]
                          (if (< position 2) (read-endpoint kb reader term) [term nil]))
                        (range) (rest prefix))]
    [(apply list (concat [(first prefix)] (map first arguments)
                         (when (sx/dotted? form) ['. (last form)])))
     (into [] (mapcat second) arguments)]))

(defn- read-row
  "Read ONE actual directed row through the same public endpoint computation.
  Keeping the canonical fact separate from goal unification lets a stored firing
  check its old output bindings without normalizing those old values again."
  [kb record reader capture?]
  (let [h (:id record)
        [f :as stored] (:sentence record)]
    (when (and (= 'rewriteOf f) (= 3 (count stored)))
      (for [[visible-h context-bindings] (res/matches-visible kb stored reader)
            :when (= h visible-h)
            :let [[fact events] (endpoint-form kb stored reader capture?)]]
        [fact context-bindings events]))))

(defn row-readings
  "Canonical facts and resolver readings for an actual visible stored rewrite handle.
  These are counter-reading INPUTS for proof-specific maintenance, not a certificate
  or permission to defeat a row globally. Raw storage and directed provenance stay put."
  [kb handle reader]
  (when-let [record (p/get-sentex (:records kb) handle)]
    (read-row kb record reader true)))

(defn- matching-rows
  "One matcher for public bindings and optional resolver-reading capture."
  [kb goal reader capture?]
  (let [[canonical goal-reads] (endpoint-form kb goal reader capture?)
        recs (:records kb)]
    (for [h (candidate-handles kb canonical)
          :let [record (p/get-sentex recs h)]
          ;; Reuse raw retrieval's visibility/exception/retirement contract. Asking
          ;; the exact ground row does not claim the canonical row was stored.
          [fact context-bindings row-reads] (read-row kb record reader capture?)
          :let [bindings (res/match1 kb canonical fact reader)]
          :when bindings]
      (cond-> [h (merge context-bindings bindings) record]
        capture? (conj {:reader reader
                        :events (into goal-reads row-reads)})))))

(defn matches
  "Positive rewrite witnesses as `[handle bindings stored-record]` for `goal`.
  Canonicalize before unifying, including repeated variables and closed endpoints.
  Returned records are the actual as-authored rows, never fabricated self edges.
  This is a read computation only; callers deriving facts must additionally carry the
  normalization supports rather than treating a canonical sentence as stored."
  [kb goal reader]
  (matching-rows kb goal reader false))

(defn matches-with-readings
  "The SAME positive rewrite matcher with a fourth item containing actual resolver
  readings. A consumer must turn those readings into a supported proof with explicit
  source roles and reader maintenance; candidate events alone grant no authority."
  [kb goal reader]
  (matching-rows kb goal reader true))

(defn- evidence
  "One positive source choice. Ordinary class caps always remain in force."
  ([handles] (evidence handles #{} #{}))
  ([handles nonplacing label-only]
   {:supports (set handles)
    :reading (cond-> {}
               (seq nonplacing) (assoc :nonplacing (set nonplacing))
               (seq label-only) (assoc :label-only (set label-only)))}))

(defn- join-evidence
  "Cartesian product of actual source alternatives, preserving stricter repeated uses."
  [left right]
  (for [a left, b right]
    {:supports (into (:supports a) (:supports b))
     :reading (prover-types/merge-source-roles (:supports a) (:reading a)
                                               (:supports b) (:reading b))}))

(defn- contextualize-evidence
  "Retain actual context-route witnesses for sources whose primitive is contextual.
  This does not turn a globally read structural map into a local premise."
  [kb reader {:keys [supports reading] :as choice}]
  (let [tx (reasoning/taxonomy kb)
        nonplacing (:nonplacing reading)
        paths (for [h supports :when (not (contains? nonplacing h))
                    :let [context (:context (p/get-sentex (:records kb) h))]
                    :when (and context (not= context reader))]
                (tax/reach-support tx :genlCx reader context reader))]
    (when (every? some? paths)
      (first (join-evidence [choice] [(evidence (mapcat #(map first %) paths))])))))

(defn- normalization-evidence
  "Alternatives recorded by the same representative and schematic reducer."
  [event]
  (map evidence (:supports event)))

(defn- primitive-mark-evidence
  "Support alternatives for the EXACT global-key primitive observed by store-marks.
  Negative/absent marks have no fabricated premise; reader maintenance must recheck them."
  [kb {:keys [kind arguments present?]}]
  (let [tx (reasoning/taxonomy kb)
        [f n] arguments
        handles (when present?
                  (case kind
                    :symmetric? (tax/prop-supporters tx :symmetric f)
                    :associative? (tax/prop-supporters tx :associative f)
                    :idempotent? (tax/prop-supporters tx :idempotent f)
                    :opaque? (when-not (contains? res/nat-quoting-predicates f)
                               (tax/prop-supporters tx :reifiable f))
                    :groups-of (mapcat #(tax/commuting-supporters tx f %)
                                       (tax/commuting-groups tx f))
                    :mention-at? (map :id (res/mention-declarations kb tx f n))
                    :meet-order (mapcat #(tax/meet-supporters tx f %) (tax/meet-orders tx f))
                    :distinct-from (mapcat #(tax/distinct-supporters tx f %) (tax/distinct-positions tx f))
                    nil))
        live (into #{} (filter #(jtms/in? (reasoning/tms kb) %)) handles)]
    ;; This is a conservative reading of the actual primitive's positive marks,
    ;; never candidate tuple authority. All remain dependencies and class caps.
    [(evidence live live live)]))

(defn- tuple-lineage-evidence
  "Positive fan/permutation witnesses for an already ADMITTED correspondence tuple.
  Never call this on a retrieval-candidate event. Copied-value steps and endpoint
  normalizations are separate obligations of the enclosing certificate builder."
  [kb reader {:keys [operation handle bindings lineage]}]
  (when-not (and (= :tuple operation) (:pattern lineage) (:probe lineage))
    (throw (ex-info "A correspondence proof needs admitted successful-unification lineage"
                    {:type ::missing-tuple-lineage :handle handle})))
  (let [tx (reasoning/taxonomy kb)
        stored (:sentence (p/get-sentex (:records kb) handle))
        [sub super swapped?] (:fan lineage)
        path (if (or (nil? super) (and (= sub super) (not swapped?)))
               []
               (tax/signed-reach-support tx sub super swapped? reader (res/holding-class kb)))
        ground (res/substitute (:probe lineage) bindings)
        permutations (or (inherit/permuted-read-supports kb stored (vec (rest ground)) reader)
                         [[]])]
    (when (some? path)
      (for [marks permutations
            :let [hs (into #{handle} (map first) path)
                  choice (first (join-evidence [(evidence hs)]
                                               [(evidence marks marks #{})]))
                  qualified (contextualize-evidence kb reader choice)]
            :when qualified]
        qualified))))

;; Nested copied readings recurse through both tuple and application evidence.
(declare reading-evidence tuple-evidence)

(defn- correspondence-evidence
  "A declared reading and an actual admitted tuple for the selected sole value.
  Only the write-compatible application branch requires a monotonic-member tuple;
  copied values retain their existing ordinary class semantics."
  [kb reader expression value events monotonic?]
  (let [declarations (into #{}
                           (mapcat (fn [event]
                                     (when (and (= :declarations (:operation event))
                                                (= expression (:expression event)))
                                       (map last (:declarations event)))))
                           events)
        tuples (filter #(and (= :tuple (:operation %)) (= expression (:expression %))
                             (= value (:value %))
                             (or (not monotonic?)
                                 (tuple/monotonic-member? (reasoning/tms kb) (:handle %))))
                       events)]
    (mapcat (fn [h]
              (join-evidence [(evidence #{h} #{} #{h})]
                             (mapcat #(tuple-evidence kb reader %) tuples)))
            declarations)))

(defn- copied-step-evidence
  "Actual selected root maps plus the value reads that licensed a copied spelling."
  [kb reader {:keys [replacements readings]}]
  (reduce
   (fn [choices [target value]]
     (let [sources (filter #(and (= :minted-expression (:operation %))
                                 (= target (:target %)) (:expression %)) readings)
           alternatives
           (mapcat (fn [{:keys [expression handles]}]
                     (join-evidence (map #(evidence #{%} #{%} #{%}) handles)
                                    (correspondence-evidence kb reader expression value readings false)))
                   sources)]
       (join-evidence choices alternatives)))
   [(evidence #{})] replacements))

(defn- tuple-evidence
  "The admitted unification path, its goal/value normalization, and copied bridges."
  [kb reader {:keys [lineage goal-readings value-readings] :as event}]
  (reduce join-evidence
          (tuple-lineage-evidence kb reader event)
          (concat [(reading-evidence kb reader goal-readings)
                   (reading-evidence kb reader value-readings)]
                  (map #(copied-step-evidence kb reader %) (:copied-steps lineage)))))

(defn- failed-branch-evidence
  "Conservative actual ambiguity witnesses, NOT retrieval candidates. A matched row
  may itself be one alias/tuple of an ambiguous branch: omitting its rival would make
  that branch succeed on the purported certificate alone. Keep admitted rows and
  declarations, their actual unification evidence and normalization reads together.
  Empty reads invent no negative premise; the consumer still owes reader maintenance."
  [kb reader events]
  (let [rows (for [{:keys [operation record predicate stated?]} events
                   :when (= :application-row operation)
                   :let [h (:id record)]]
               [(if (= 'natFormula predicate)
                  (evidence #{h} (if stated? #{h} #{}) #{h})
                  (evidence #{h}))])
        declarations (into #{} (mapcat #(when (= :declarations (:operation %))
                                          (map last (:declarations %)))) events)
        tuples (filter #(= :tuple (:operation %)) events)]
    (reduce join-evidence
            [(evidence declarations #{} declarations)]
            (concat rows (map #(tuple-evidence kb reader %) tuples)
                    [(reading-evidence kb reader events)]))))

(defn- application-evidence
  "The selected positive branch plus actual ambiguity witnesses of prior branches.
  A pre-admission candidate never becomes either kind of evidence."
  [kb reader {:keys [source expression value readings attempt-readings]}]
  (let [rows (filter #(= :application-row (:operation %)) readings)
        failed (case source
                 :rewrite []
                 :correspondence [(:rewrite attempt-readings)]
                 :map [(:rewrite attempt-readings) (:correspondence attempt-readings)]
                 :unresolved (vals attempt-readings)
                 [])
        selected
        (case source
          :rewrite (for [{:keys [record predicate]} rows :when (= 'rewriteOf predicate)]
                     (evidence #{(:id record)}))
          :map (for [{:keys [record predicate stated?]} rows
                     :when (and (= 'natFormula predicate)
                                (= value (second (:sentence record))))
                     :let [h (:id record)]]
                 (evidence #{h} (if stated? #{h} #{}) #{h}))
          :correspondence (correspondence-evidence kb reader expression value readings true)
          :unresolved [(evidence #{})]
          (throw (ex-info "Unknown application read branch" {:type ::unknown-branch :source source})))]
    (reduce join-evidence
            (join-evidence selected (reading-evidence kb reader readings))
            (map #(failed-branch-evidence kb reader %) failed))))

(defn reading-evidence
  "Positive source alternatives for actual resolver readings; no candidate row is
  admitted by this function. The raw rewrite witness is a separate strict ingredient.
  Absence/uniqueness still requires the consumer's reader-specific recheck. This helper
  is not a registered prover or a generalized forced-conclusion capability."
  [kb reader events]
  (reduce
   (fn [choices event]
     (let [operation (:operation event)
           alternatives
           (cond
             (:application-attempt event) [(evidence #{})]
             (:source event) (application-evidence kb reader event)
             (contains? #{:representative :normalization} operation)
             (normalization-evidence event)
             (= :store-mark operation) (primitive-mark-evidence kb event)
             (= :reifiable-use operation)
             (for [h (tax/prop-supporters (reasoning/taxonomy kb) :reifiable (:function event))
                   :when (res/supporter-believed? kb h reader)]
               (evidence #{h} #{h} #{}))
             (= :modal-use operation)
             (for [h (tax/prop-supporters (reasoning/taxonomy kb) :modal (:predicate event))
                   :when (jtms/in? (reasoning/tms kb) h)]
               (evidence #{h} #{h} #{h}))
             (= :stored-order operation)
             (map #(evidence % % %)
                  (inherit/permuted-read-supports kb (:expression event)
                                                  (vec (rest (:value event))) '?ctx))
             ;; Declarations/tuples/maps are consumed ONLY by their selected
             ;; branch or copied bridge above. Pre-admission candidates never are.
             :else [(evidence #{})])]
       (join-evidence choices alternatives)))
   [(evidence #{})] events))

(defn match-certificates
  "The same public matches with positive source alternatives and proof-local roles.
  The literal forward join and proof-specific counterguards consume these, without
  adding normalization sources to unrelated prover-registry summaries."
  [kb goal reader]
  (mapcat
   (fn [[h bindings _ {:keys [events]}]]
     (let [choices (keep #(contextualize-evidence kb reader %)
                         (join-evidence [(evidence #{h})] (reading-evidence kb reader events)))]
       (when (empty? choices)
         (throw (ex-info "An admitted rewrite read has no complete positive certificate"
                         {:type ::missing-certificate :handle h :reader reader})))
       (for [{:keys [supports reading]} choices]
         [bindings supports (assoc reading :readers #{reader}
                                   :rewrite-reads #{{:goal goal :handle h
                                                     :outputs (select-keys bindings (sx/free-vars goal))}})])))
   (matches-with-readings kb goal reader)))

(defn head-certificates
  "Supported public matches of a lazy rule's already-ground consequent.
  The raw head is derived by the rule/body proof, NOT a fabricated stored equation.
  Its association retains that raw head so counterguards can re-read it at each reader."
  [kb goal head rule-h reader]
  (when (res/supporter-visible? kb rule-h reader)
    (let [[canonical goal-reads] (endpoint-form kb goal reader true)
          [fact head-reads] (endpoint-form kb head reader true)]
      (when-let [bindings (res/unify canonical fact)]
        (let [choices (keep #(contextualize-evidence kb reader %)
                            (join-evidence [(evidence #{rule-h})]
                                           (reading-evidence kb reader (into goal-reads head-reads))))]
          (when (empty? choices)
            (throw (ex-info "An admitted lazy head has no complete positive certificate"
                            {:type ::missing-head-certificate :handle rule-h :reader reader})))
          (for [{:keys [supports reading]} choices]
            [bindings supports
             (assoc reading :readers #{reader}
                    :rewrite-reads #{{:goal goal :handle rule-h :head head
                                      :outputs (select-keys bindings (sx/free-vars goal))}})]))))))

(defn reader-contexts
  "Candidate readers across ALL source contexts, including dynamically named
  correspondence tuple predicates and their fans. Only rewrite consumers call this;
  ordinary computed antecedents keep the existing census. Computation checks each reader."
  [kb]
  (let [tx (reasoning/taxonomy kb)
        predicates (into normalization-sources
                         (mapcat (fn [[_ predicate]]
                                   (into (res/sub-predicates kb predicate '?ctx)
                                         (res/swapped-sub-predicates kb predicate '?ctx))))
                         (res/correspondence-declarations kb '?ctx))
        held (into #{}
                   (mapcat #(first (reads/as-stored-contexts-with-functor-global (:index kb) %)))
                   predicates)]
    (tax/meet-closure tx held)))

(defn head-reader-contexts
  "Lazy-head readers from normalization sources and the actual rule/body supports.
  Including the latter keeps a source-free raw head readable in its own context.
  This is discovery only; each head certificate and the firing's placement admit it."
  [kb handles]
  (tax/meet-closure
   (reasoning/taxonomy kb)
   (into (set (reader-contexts kb))
         (keep #(:context (p/get-sentex (:records kb) %))) handles)))

(defn counter-certificates
  "Positive counter-readings of one firing association at `reader`.
  Fixed inputs retain public endpoint normalization; ONLY the former newly bound
  outputs are compared as values. Re-normalizing those outputs would hide a change.
  This returns proof-specific guard ingredients, never a global defeat or stored edit."
  [kb {:keys [goal handle outputs head]} reader]
  (let [[canonical goal-reads] (endpoint-form kb goal reader true)
        rows (if head
               (let [[fact events] (endpoint-form kb head reader true)] [[fact {} events]])
               (row-readings kb handle reader))]
    (for [[fact _ row-reads] rows
          :let [b (res/match1 kb canonical fact reader)]
          :when (or (nil? b) (not= outputs (select-keys b (keys outputs))))
          choice (join-evidence [(evidence #{handle})]
                                (reading-evidence kb reader (into goal-reads row-reads)))
          :let [qualified (contextualize-evidence kb reader choice)]
          :when qualified]
      [(:supports qualified) (assoc (:reading qualified) :readers #{reader})])))

(defn applicable?
  "Can this positive binary goal read an actual rewriteOf row, including an open head?"
  [kb goal reader]
  (and (sequential? goal)
       (if (sx/dotted? goal) (<= (count (sx/positional goal)) 3) (= 3 (count goal)))
       (let [f (first goal)]
         (or (= 'rewriteOf f)
             (sx/variable? f)
             (and (symbol? f)
                  (contains? (res/sub-predicates kb f reader) 'rewriteOf))))))

(defn head-reader
  "The public backward-head capability, separate from raw rule storage/unification.
  A raw body-bound head is read only once its inputs are ground. Ordinary heads
  use their original unifier; this capability introduces no stored predicate."
  [kb reader]
  {:defer? (fn [goal consequent]
             (and (sequential? consequent)
                  (or (= 'rewriteOf (first consequent))
                      (sx/variable? (first consequent)))
                  (applicable? kb goal reader)))
   :match (fn [goal consequent bindings]
            (if (and (= 'rewriteOf (first consequent)) (= 3 (count consequent)))
              (let [[goal _] (endpoint-form kb goal reader false)
                    [consequent _] (endpoint-form kb consequent reader false)]
                (res/subsuming-unify kb goal consequent
                                     bindings reader))
              (res/subsuming-unify kb goal consequent bindings reader)))})

(defn fact-matches
  "The public fact leaf reading positive rewrite witnesses through representatives.
  Other stored predicates retain the existing retrieval path, including negation and
  sameAs/equals. Do not union a second raw rewrite channel with canonical bindings."
  [kb goal reader]
  (let [raw (res/matches-visible kb goal reader)]
    (if (applicable? kb goal reader)
      (concat
       (remove (fn [[h _ stored]]
                 (let [sentence (or (:sentence stored)
                                    (:sentence (p/get-sentex (:records kb) h)))]
                   (= 'rewriteOf (first sentence)))) raw)
       (matches kb goal reader))
      raw)))
