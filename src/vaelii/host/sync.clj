;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.host.sync
  "Bring a KB's shipped contexts up to the running engine's.

  A KB stores the starter ontology it was built with, and the engine that opens it later
  ships its own: a strength marked `set/monotonic`, a vocabulary term added to core.txt, a
  disjointness the ontology stopped stating.  `sync!` makes the KB state what this engine
  ships, context by context, and leaves everything else alone.

  **What is shipped** is what `starter/load-into` produces, read off a scratch in-memory KB
  it is loaded into — not the text of the files.  The two differ: `genlCx` edges are stored
  in CxUniverse whichever file states them, and the closing `unary_predicate` batch is
  stated by no file.  Each premise is attributed to the load that stored it: CxUniverse
  for the upper ontology, the middle context for a middle file.

  **Which contexts are synced exactly**: CxUniverse and the `kb/middle/` contexts.  A
  premise there that the engine does not ship is retracted when it is about the engine's
  own vocabulary, a strength that differs is restated, and a missing one is asserted.
  Three kinds of sentex are left as they are: a premise naming a term no shipped premise
  names (`vocabulary`), which states an author's vocabulary rather than the engine's; a
  `genlCx` premise, stored in CxUniverse whichever file or author states it; and a sentex
  that is not a premise (a lifted `decontextualized_predicate` copy, a rule firing).  An
  author's own context, wired below CxUniverse, is not one of them and is not read.

  **Only added to**: any other context a shipped file's content is stored in.

  **Only the layers a KB has.**  A middle file whose context holds nothing in the KB is
  not loaded into it.  The upper ontology is loaded only into a KB whose CxUniverse holds
  a premise the upper load ships, and the `unary_predicate` batch only into one that also
  holds a mark the batch ships.

  Comparison is by the form a KB file writes (`text/premise-entries`): a fact or rule
  under its strength wrapper, an `exceptWhen` as the wrapper it was asserted as.  A
  strength the engine **raised** is only an assertion, since `assert` raises a held
  premise's strength in place; one it **lowered** is the form retracted and the weaker one
  asserted, since nothing lowers a strength in place.

  **One batch.**  The sync is one `v/edit!`: the additions first, then the retractions,
  one settle.  So the belief a retraction would sweep and the addition rebuild keeps its
  witness through the batch, where retracting first tore the TMS down only to build it
  back up.  What cannot go in that order — a retraction of a record an addition lands on —
  goes before it (`sync!`).

  **Or one change at a time.**  On a corpus of millions of sentexes the one batch is one
  settle that reports nothing until it ends, and a refused addition rolls all of it back.
  `sync-each!` makes the plan's changes in the same order as one `edit!` each, reporting
  each change and how many are left; it costs a settle per change and gives up the shared
  witness, and buys a sync whose progress can be read and which stops between changes.
  It runs in two stages.  A rule the engine ships forward lands **backward** in the first,
  beside the rest of the content, so no addition fires a new forward rule over a corpus;
  the second turns each such rule forward, one reported change apiece, and a rule whose
  forward chaining is expensive is then the one change the job stops on.

  **Write-back** is the other direction: `write-back!` edits the shipped files to state
  what a KB's exact contexts gained and lost since a `held` reading, one line per
  premise.  The development browser runs it for the starter (docs/catalog.md)."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.host.seed :as seed]
            [vaelii.host.starter :as starter]
            [vaelii.impl.io.text :as text]
            [vaelii.impl.kb :as kbi]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]))

(defn exact-contexts
  "The contexts `sync!` makes state exactly what the engine ships: CxUniverse and the
  middle layer's contexts, as discovered on the classpath."
  []
  (into [sx/root-context] (seed/layer-contexts "middle")))

(defn- edge?
  "Is `form` (a KB-file form, under its strength wrapper or not) a `genlCx` sentence?"
  [form]
  (let [[sentence _] (text/peel-form form)]
    (and (seq? sentence) (= 'genlCx (first sentence)))))

(defn- terms
  "The symbols `form` names, less its variables."
  [form]
  (into #{} (comp (filter symbol?) (remove #(str/starts-with? (name %) "?")))
        (tree-seq coll? seq form)))

(defn vocabulary
  "Every symbol a premise of `shipped` names: the terms the engine owns.  A held premise
  that names a symbol outside it is about an author's vocabulary, and `plan` does not
  retract it, whichever exact context it is stored in — the content a corpus states in
  CxUniverse included.  The cost is a premise the engine stopped shipping together with
  the last mention of a term it names: that term is no longer the engine's, and the
  premise stays."
  [shipped]
  (into #{} (mapcat (comp terms :form)) shipped))

(defn- premise-records
  [kb ids]
  (let [recs (:records kb)]
    (into [] (keep #(p/get-sentex recs %)) ids)))

(defn premises
  "Every premise the starter stores, as `{:context c :form f :file ctx}`: the form a KB
  file writes it in, the context it is stored in, and the context of the load that stored
  it — CxUniverse for the upper ontology, `:unary-predicates` for the closing batch no
  file states.  In the order the
  load stored them, which is an order they assert in: the load retried what arrived
  before its dependencies.  Built in a scratch in-memory KB that is cleared before this
  returns."
  []
  (let [kb      (v/open-kb {:backend :memory :space [::shipped (random-uuid)] :recover? false})
        recs    (:records kb)
        seen    (volatile! #{})
        file-of (volatile! {})]
    (try
      (starter/load-into kb (fn [file]
                              (let [ids (set (p/premise-ids recs))]
                                (vswap! file-of into (map (fn [h] [h file])) (remove @seen ids))
                                (vreset! seen ids))))
      (let [[entries _] (text/premise-entries kb (premise-records kb (sort (p/premise-ids recs))))]
        (mapv (fn [{:keys [handles] :as e}]
                (-> e (dissoc :handles) (assoc :file (@file-of (first handles)))))
              entries))
      (finally
        (v/clear! kb)
        (v/close! kb)))))

(defn- held-forms
  "`{[context form] entry}` for the premises `kb` stores in `context`, less the `genlCx`
  premises in CxUniverse, which sync leaves as they are.  Given `vocab`, only the premises
  naming nothing outside it: `plan` compares a held form with the shipped ones and
  retracts only one about the engine's vocabulary, so a premise naming an author's term
  is neither, and rendering it as a file form — the whole cost of this read on a corpus
  that keeps its own content in CxUniverse — is skipped by a set test on its terms."
  ([kb context] (held-forms kb context nil))
  ([kb context vocab]
   (let [;; a rule and an exceptWhen are kept whole, since text/premise-entries pairs the
         ;; two records of a qualified rule; there are few of them
         ours?       (if vocab
                       #(let [s (:sentence %)]
                          (or (nil? s) (and (seq? s) (= sx/except-wrapper (first s)))
                              (every? vocab (terms s))))
                       (constantly true))
         [entries _] (text/premise-entries
                      kb (filterv #(and (some? (:strength %)) (ours? %))
                                  (v/sentexes-in-context kb context)))]
     (into {}
           (comp (remove #(and (= sx/root-context context) (edge? (:form %))))
                 (map (fn [e] [[(:context e) (:form e)] e])))
           entries))))

(defn- stored?
  "Does `kb` hold `form` in `context` as a premise at least as strong as the form states?
  Asked by lookup, so a context holding a whole corpus is not read to answer it.  A form
  the lookup cannot take — a rule under its wrapper — reads as absent, and asserting it
  again is a no-op when it is there."
  [kb context form]
  (let [[sentence o] (text/peel-form form)
        h (try (v/handle-of kb sentence context) (catch clojure.lang.ExceptionInfo _ nil))
        have (some->> h (v/sentex kb) :strength)]
    (boolean (and have (or (= have :monotonic) (not= :monotonic (:strength o)))))))

(defn- backward-form
  "`form` with its forward direction wrapper (`set/forwardRule`, `set/forwardOnlyRule`)
  turned `set/backwardRule`, or nil when it runs no rule forward.  The strength, default
  and solve wrappers around it are kept; an `exceptWhen` is left as it is, since its
  records are two."
  [form]
  (let [w (when (seq? form) (first form))]
    (cond
      (#{:forward :forward-only} (sx/rule-direction-wrappers w))
      (list 'set/backwardRule (second form))

      (#{sx/strength-wrapper sx/default-rule-wrapper sx/solve-rule-wrapper} w)
      (some->> (backward-form (second form)) (list w))

      :else nil)))

(defn- undirected
  "`sentence` with its rule direction wrappers taken off, under the default and solve
  wrappers it keeps: the record a rule lands on whichever direction states it, since the
  direction is a field of the record (`sx/rule-direction-wrappers`)."
  [sentence]
  (let [w (when (seq? sentence) (first sentence))]
    (cond
      (sx/rule-direction-wrappers w)                             (undirected (second sentence))
      (#{sx/default-rule-wrapper sx/solve-rule-wrapper} w)       (list w (undirected (second sentence)))
      :else                                                      sentence)))

(defn- backward?
  "Does `sentence`, a stored rule as a file renders it, run backward alone: no direction
  wrapper, or `set/backwardRule`?"
  [sentence]
  (and (seq? sentence)
       (let [w (first sentence)]
         (cond (= 'set/backwardRule w)                               true
               (#{sx/default-rule-wrapper sx/solve-rule-wrapper} w) (backward? (second sentence))
               :else                                                (= 'implies w)))))

(defn- canonical-form
  "`form` as a KB file renders the record it asserts: a `set/backwardRule` wrapper is
  dropped where backward is what an unwrapped rule runs, so a shipped backward rule and
  the stored one compare equal.  A generator, a rule concluding a rule, runs forward
  unwrapped and keeps its wrapper."
  [form]
  (let [[s o] (text/peel-form form)
        rule? #(and (seq? %) (or (= 'implies (first %))
                                 (sx/rule-direction-wrappers (first %))
                                 (= sx/default-rule-wrapper (first %))))
        strip (fn strip [x]
                (let [w (when (seq? x) (first x))]
                  (cond
                    (and (= 'set/backwardRule w) (rule? (second x))
                         (not (rule? (last (second x)))))
                    (second x)

                    (#{sx/default-rule-wrapper sx/solve-rule-wrapper} w) (list w (strip (second x)))
                    :else                                                x)))
        s' (strip s)]
    (cond (= s s')              form
          (:strength o)         (list sx/strength-wrapper s')
          :else                 s')))

(defn plan
  "What `sync!` would change in `kb`, without changing it:

    :add     `{:context :form}` the shipped content `kb` lacks, in the layers it has,
             in `premises`'s order
    :remove  `{:context :form :handles}` premises in an exact context the engine does not
             ship, each naming only terms of its `vocabulary`

  A premise the engine ships at a higher strength is an `:add` alone: asserting it raises
  the held one.  One it ships at a lower strength is a `:remove` and an `:add`.  A rule's
  direction is read the same way: a rule held backward and shipped forward is an `:add`
  alone, which raises the one record to forward in place, and one held forward and
  shipped backward is a `:remove` and an `:add`.

  `shipped` defaults to a fresh `(premises)`."
  ([kb] (plan kb (premises)))
  ([kb shipped]
   (let [shipped (map #(update % :form canonical-form) shipped)
         exact   (set (exact-contexts))
         root    sx/root-context
         ;; each layer belongs to a KB that holds some of it: the upper ontology to one
         ;; whose CxUniverse holds a premise it ships, and the closing batch, which a
         ;; vocabulary KB does not run, to one holding a mark the batch ships
         holds?  (fn [load] (some (fn [{:keys [context form file]}]
                                    (and (= load file) (= root context) (not (edge? form))
                                         (stored? kb context form)))
                                  shipped))
         upper?  (holds? root)
         present (into (cond-> #{}
                         upper?                                (conj root)
                         (and upper? (holds? :unary-predicates)) (conj :unary-predicates))
                       (filter #(and (not= root %) (pos? (v/count-in-context kb %))))
                       (distinct (filter symbol? (keep :file shipped))))
         ours    (into #{} (map (juxt :context :form)) shipped)
         vocab   (vocabulary shipped)
         held    (into {} (mapcat #(held-forms kb % vocab))
                       (filter (every-pred exact present) exact))
         wanted  (filter #(present (:file %)) shipped)
         ;; a default premise of one record, shipped known-true: the `:add` raises it.
         ;; An exceptWhen is two records, and is restated whole.
         forward (into #{} (keep (fn [{:keys [context form]}]
                                   (when (backward-form form)
                                     [context (undirected (first (text/peel-form form)))])))
                       wanted)
         raised? (fn [{:keys [context form handles]}]
                   (let [[s o] (text/peel-form form)]
                     (or (and (= 1 (count handles)) (nil? o)
                              (contains? ours [context (list sx/strength-wrapper form)]))
                         ;; a rule held backward and shipped forward
                         (and (backward? s) (contains? forward [context (undirected s)])))))]
     {:add    (into []
                    (comp (remove (fn [{:keys [context form]}]
                                    (if (and (exact context) (not (edge? form)))
                                      (contains? held [context form])
                                      (stored? kb context form))))
                          (map #(select-keys % [:context :form])))
                    wanted)
      :remove (into [] (comp (remove (fn [[k _]] (ours k)))
                             (map val)
                             (remove raised?)
                             (filter #(every? vocab (terms (:form %)))))
                    held)})))

(defn- add!
  "Assert every `{:context :form}` of `entries` into `kb`, retrying the refused ones while a
  round makes progress — a file's order is its terms', not its dependencies'
  (`text/load-entries!`).  Returns what is still refused, each with the refusal's `:type`
  and message, rather than throwing: a KB whose own content refuses a shipped sentence is
  a finding about that KB, and the rest of the sync still applies."
  [kb entries]
  (let [attempt (fn [round total es]
                  (with-open [r (progress/start ::add
                                                (str "sync: assert the set-aside entries (round "
                                                     round ")")
                                                total)]
                    (reduce (fn [acc {:keys [context form] :as e}]
                              (let [[sentence o] (text/peel-form form)
                                    acc (try (v/assert kb sentence context (or o {})) acc
                                             (catch clojure.lang.ExceptionInfo ex
                                               (conj acc (assoc e :type (:type (ex-data ex))
                                                                :message (ex-message ex)))))]
                                (progress/tick! r)
                                acc))
                            [] es)))]
    (v/with-deferred-settle kb
      (loop [round   1
             pending (attempt 1 (when (counted? entries) (count entries)) entries)]
        (if (empty? pending)
          []
          (let [remaining (attempt (inc round) (count pending)
                                   (map #(select-keys % [:context :form]) pending))]
            (if (< (count remaining) (count pending))
              (recur (inc round) remaining)
              remaining)))))))

(defn- records
  "The records asserting `form` lands on, each spelled without its strength or a rule's
  direction: the sentence, or for an `exceptWhen` the wrapper and the rule it qualifies —
  a rule another form states too."
  [form]
  (let [[s _] (text/peel-form form)]
    (if (and (seq? s) (= sx/except-wrapper (first s)) (= 3 (count s)))
      (let [[_ q rule] s]
        #{(list sx/except-wrapper (first (text/peel-form q)) (undirected rule)) (undirected rule)})
      #{(undirected s)})))

(defn- edit-entry
  "`{:context :form}` as a `v/edit!` `:add` line."
  [{:keys [context form]}]
  (let [[sentence o] (text/peel-form form)]
    (cond-> [sentence context] o (conj o))))

(defn- batch!
  "Assert `entries`, then retract `handles`, as one `v/edit!`: one settle.  The edit is
  all-or-nothing, so an entry it refuses rolls the batch back; that entry is set aside
  with its refusal's `:type` and message and the batch runs again without it.  Returns
  the entries set aside."
  [kb entries handles]
  (with-open [rep (progress/start ::batch "sync: run the batch edit, once per refused entry" nil)]
    (loop [entries (vec entries) aside []]
      (if (and (empty? entries) (empty? handles))
        aside
        (let [refused (try (v/edit! kb {:add (mapv edit-entry entries) :remove handles})
                           nil
                           (catch clojure.lang.ExceptionInfo ex
                             (let [{:keys [rolled-back in index] :as data} (ex-data ex)]
                               ;; a removal's refusal is the KB refusing writes: not an
                               ;; entry to set aside
                               (if (and rolled-back (= :add in))
                                 {:index index :type (:type data) :message (ex-message ex)}
                                 (throw ex)))))]
          (progress/tick! rep)
          (if-let [{:keys [index] :as r} refused]
            (recur (into (subvec entries 0 index) (subvec entries (inc index)))
                   (conj aside (merge (nth entries index) (dissoc r :index))))
            aside))))))

(defn- ordered
  "`plan`'s changes in the order `sync!` makes them: `:before`, the retractions of a
  record an addition lands on; `:adds`; `:after`, the other retractions."
  [{adds :add removes :remove}]
  (let [landing  (into #{} (mapcat (fn [{:keys [context form]}]
                                     (map #(vector context %) (records form))))
                       adds)
        restated (fn [{:keys [context form]}] (some #(landing [context %]) (records form)))]
    {:before (filterv restated removes)
     :adds   adds
     :after  (filterv (complement restated) removes)}))

(defn sync!
  "Make `kb`'s shipped contexts state what this engine ships (see the namespace doc), as
  one `v/edit!`: the additions, then the retractions, one settle.  Returns

    {:added n :removed n :refused [{:context :form :type :message} …]}

  **A retraction goes first** only when an addition lands on a record it retracts: a
  strength the engine lowered, whose weaker form would otherwise be asserted onto the
  premise and then retracted with it, or an `exceptWhen` restated around a rule the KB
  keeps.  Those are their own `edit!` before the batch.

  **An addition the batch refuses is set aside**, the batch rolled back and run without
  it, so the rest lands in one settle.  The ones set aside are asserted after it,
  retrying while a round makes progress (`add!`): the batch's refusal can be an order the
  batch could not fix, or content its own retractions then took away.  What still refuses
  is `:refused`.  Each refusal costs the batch one rollback.

  `kb` must accept writes (`v/write-hazards` empty).  `ships` is `(premises)`, passed by a
  caller that syncs more than one KB or prices the sync apart from the scratch load.
  `sync-each!` makes the same changes one at a time, reporting each."
  ([kb] (sync! kb (premises)))
  ([kb ships]
   (let [{:keys [before adds after]} (ordered (plan kb ships))
         handles (fn [es] (into [] (comp (mapcat :handles) (distinct)) es))]
     (when (seq before)
       (v/edit! kb {:remove (handles before)}))
     (let [aside   (batch! kb adds (handles after))
           refused (if (seq aside)
                     (add! kb (map #(select-keys % [:context :form]) aside))
                     [])]
       {:added   (- (count adds) (count refused))
        :removed (+ (count before) (count after))
        :refused refused}))))

(defn sync-each!
  "`sync!`'s changes made one at a time, each its own `v/edit!`, for a KB on which the
  one batch would run for hours without a word.  The plan comes first and its size is
  reported, then `report` is called before each change as

    {:done i :total n :op {:op :add|:remove|:forward :context :form}}

  and once more with `:done n` at the end, so a reader always knows how far it has got.
  The order is `sync!`'s: the retractions an addition lands on, the additions, the other
  retractions.  An addition `edit!` refuses is set aside and retried after the rest while
  a round makes progress (`add!`), and costs no rollback of anything else.  A `report`
  that throws stops the sync between two changes, each of which has settled, so a rerun's
  plan is what is left.

  **A forward rule is added backward, and turned forward last.**  Each addition that runs
  a rule forward (`backward-form`) is asserted with `set/backwardRule` in its place, so
  the content lands with no new rule firing over it.  Once every other change has
  settled, each is an `:op :forward` change of its own: the shipped form asserted over
  the backward rule, which raises the one record to forward in place.  A sync stopped
  between the two stages leaves the rule held backward, which a rerun's plan reads as an
  `:add` alone (`plan`), so the rerun turns it forward there.

  Returns what `sync!` returns, with `:forwarded n`."
  ([kb report] (sync-each! kb (premises) report))
  ([kb ships report]
   (let [{:keys [before adds after]} (ordered (plan kb ships))
         deferred (filterv #(backward-form (:form %)) adds)
         as-added (fn [{:keys [form] :as o}] (assoc o :form (or (backward-form form) form)))
         ops      (vec (concat (map #(assoc % :op :remove) before)
                               (map #(as-added (assoc % :op :add)) adds)
                               (map #(assoc % :op :remove) after)))
         n        (+ (count ops) (count deferred))
         set-aside (fn [aside o ex]
                     (let [{:keys [rolled-back in] :as data} (ex-data ex)]
                       (if (and rolled-back (= :add in))
                         (conj aside (assoc (select-keys o [:context :form])
                                            :type (:type data) :message (ex-message ex)))
                         (throw ex))))
         aside    (reduce (fn [aside [i {:keys [op handles] :as o}]]
                            (report {:done i :total n :op (select-keys o [:op :context :form])})
                            (if (= :add op)
                              (try (v/edit! kb {:add [(edit-entry o)]})
                                   aside
                                   (catch clojure.lang.ExceptionInfo ex (set-aside aside o ex)))
                              (do (v/edit! kb {:remove (vec (distinct handles))}) aside)))
                          [] (map-indexed vector ops))
         refused  (if (seq aside)
                    (add! kb (map #(select-keys % [:context :form]) aside))
                    [])
         ;; a rule whose backward assert stayed refused has nothing to turn forward
         skip     (set (map (juxt :context :form) refused))
         stage2   (reduce (fn [acc [i {:keys [context form] :as o}]]
                            (report {:done (+ (count ops) i) :total n
                                     :op {:op :forward :context context :form form}})
                            (if (skip [context (backward-form form)])
                              acc
                              (try (v/edit! kb {:add [(edit-entry o)]})
                                   (update acc :forwarded inc)
                                   (catch clojure.lang.ExceptionInfo ex
                                     (update acc :refused set-aside o ex)))))
                          {:forwarded 0 :refused []} (map-indexed vector deferred))]
     (report {:done n :total n})
     {:added     (- (count adds) (count refused))
      :removed   (+ (count before) (count after))
      :forwarded (:forwarded stage2)
      :refused   (into refused (:refused stage2))})))

;; ---- writing back ---------------------------------------------------------

(defn held
  "`{[context form] entry}` for every premise `kb` stores in the exact contexts, less the
  `genlCx` premises in CxUniverse: the reading two `write-back!` changes are diffed from."
  [kb]
  (into {} (mapcat #(held-forms kb %)) (exact-contexts)))

(defn context-files
  "The shipped files `context`'s premises are written in, as `java.io.File`s, the one a
  premise about no defined term is appended to first: core.txt and the other upper files
  for CxUniverse, `kb/middle/<context>.txt` for a middle context.  Nil where the layer is
  not a directory on the classpath."
  [context]
  (let [file (fn [path]
               (when-let [r (io/resource path)]
                 (when (= "file" (.getProtocol r)) (io/file r))))]
    (if (= sx/root-context context)
      (seq (keep #(file (str "kb/upper/" %)) (core-context/upper-files)))
      (some-> (file (str "kb/middle/" context ".txt")) vector))))

(defn- subject-terms
  "The terms a premise's line is placed by, in order: a rule's consequent's, a wrapped
  sentence's own, and a literal's first argument and then its functor."
  [sentence]
  (when (seq? sentence)
    (let [[f a b] sentence]
      (cond
        (#{'implies sx/except-wrapper} f)                         (subject-terms b)
        (= 'not f)                                                (subject-terms a)
        (and (symbol? f) (namespace f) (seq? a) (= 2 (count sentence))) (subject-terms a)
        :else (filter #(and (symbol? %) (not (sx/variable? %))) [a f])))))

(defn- blocks
  "`{term [file line]}`: for each `(comment term …)` in `files`, the last line of the
  forms from that comment to the next one.  The first file defining a term wins."
  [spans-of files]
  (reduce (fn [m [t at]] (if (contains? m t) m (assoc m t at)))
          {}
          (for [f files
                :let [ss     (spans-of f)
                      starts (keep-indexed (fn [i {:keys [form]}]
                                             (when (and (seq? form) (= 'comment (first form))) i))
                                           ss)]
                [i j] (map vector starts (concat (rest starts) [(count ss)]))]
            [(second (:form (nth ss i))) [f (:end (nth ss (dec j)))]])))

(defn- edit-file!
  "Apply `edits` to file `f`: `{:start :end :text}` replaces lines start..end with `text`
  (nil deletes them), `{:after line :text}` inserts `text` after `line` (`:end` after the
  last).  Lines are 1-based, and edits at one place keep their order."
  [^java.io.File f edits]
  (let [lines (str/split (slurp f) #"\n" -1)
        n     (cond-> (count lines) (= "" (peek lines)) dec)
        pos   (fn [{:keys [start after]}]
                (if start start (+ 0.5 (if (= :end after) n after))))
        out   (reduce (fn [v {:keys [start end after text] :as e}]
                        (if start
                          (into (subvec v 0 (dec start)) (concat (when text [text]) (subvec v end)))
                          (let [at (long (- (pos e) 0.5))
                                ls (if (= :end after) ["" text] [text])]
                            (into (subvec v 0 at) (concat ls (subvec v at))))))
                      lines
                      (sort-by (juxt pos :i) #(compare %2 %1)
                               (map-indexed #(assoc %2 :i %1) edits)))]
    (spit f (str/join "\n" out))))

(defn write-back!
  "Edit the shipped files to state `changes`, `{:add [entry …] :remove [entry …]}` of
  `{:context :form}` as `held` spells them, one line edit each:

    - a removal deletes the lines of the file form whose sentence matches, compared as
      `kb` stores it in the context, so variable names and antecedent order do not count;
    - a removal and an addition of one sentence rewrite that form in place: a strength
      change;
    - an addition is one line after the forms of the `(comment T …)` block of the first
      term it is about that a file defines (`subject-terms`), or appended to the
      context's first file when none is.

  Every other line stays, comments and order included.  `files-of` maps a context to its
  files and defaults to `context-files`.  Returns `{:written n :skipped [entry …]}`, a
  skipped entry being a removal no file states or one in a context with no file."
  ([kb changes] (write-back! kb changes context-files))
  ([kb {:keys [add remove]} files-of]
   (let [spans-of (memoize (fn [f] (text/form-spans f)))
         by-cx    (group-by :context (concat (map #(assoc % :op :add) add)
                                             (map #(assoc % :op :remove) remove)))
         plan     (for [[context es] by-cx]
                    (let [files (files-of context)
                          k     (memoize (fn [form]
                                           (let [[s _] (text/peel-form form)]
                                             (try (kbi/canonical-sentence kb s context)
                                                  (catch Exception _ s)))))
                          lines (for [f files, sp (spans-of f)] (assoc sp :file f))
                          line  (fn [form]
                                  (let [[s _] (text/peel-form form)]
                                    (or (first (filter #(= s (first (text/peel-form (:form %)))) lines))
                                        (first (filter #(= (k form) (k (:form %))) lines)))))
                          adds  (filter #(= :add (:op %)) es)
                          pair  (into {} (map (fn [a] [(k (:form a)) a])) adds)
                          rems  (for [r (filter #(= :remove (:op %)) es)]
                                  (assoc r :line (when files (line (:form r)))
                                         :into (pair (k (:form r)))))
                          taken (set (keep #(when (:line %) (:into %)) rems))
                          at    (when files (blocks spans-of files))]
                      {:skipped (if files (filterv (complement :line) rems) es)
                       :edits   (when files
                                  (concat
                                   (for [{:keys [line into]} rems :when line]
                                     {:file (:file line) :start (:start line) :end (:end line)
                                      :text (some-> into :form nm/print-key)})
                                   (for [a adds :when (not (taken a))
                                         :let [[s _] (text/peel-form (:form a))
                                               [f l] (or (some at (subject-terms s))
                                                         [(first files) :end])]]
                                     {:file f :after l :text (nm/print-key (:form a))})))}))
         edits    (mapcat :edits plan)]
     (doseq [[f es] (group-by :file edits)]
       (edit-file! f es))
     {:written (count edits)
      :skipped (into [] (comp (mapcat :skipped) (map #(dissoc % :op :line :into))) plan)})))
