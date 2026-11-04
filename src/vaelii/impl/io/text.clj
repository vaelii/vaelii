;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.io.text
  "The text KB format, read and written: one file per context, one s-expression per
  sentence, the format the shipped ontology is authored in (`resources/kb/`,
  `vaelii.host.seed`). Every form is read with `clojure.edn`; the file name is the context.
  `peel-form` takes the `(set/monotonic S)` and `(set/inert S)` wrappers off a whole form.
  Text holds premises and inert sentexes in the author's spelling, with a handle as the
  `(ist Cx S)` reference it resolves from; the export dump (`io.export`, `io.import`) holds
  every record at its own handle.  See docs/kbs.md, \"Text you exported yourself\"."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [vaelii.impl.assert-entry :as entry]
            [vaelii.impl.io.digest :as digest]
            [vaelii.impl.io.export :as export]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.opts :as opts]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning])
  (:import [clojure.lang LineNumberingPushbackReader]
           [java.io File]))

;; ---- the entry-point wrappers ------------------------------------------

(defn peel-form
  "`[sentence opts]` for one form of a text KB file (`sx/form-peel`): `(set/monotonic S)`
  is `S` with `{:strength :monotonic}`, `(set/inert S)` is `S` with `{:inert true}`, which
  tells the caller to write `S` through `assert-inert`, and anything else is itself with
  nil.  Throws `sx/form-peel`'s `:shape` problem for a malformed wrapper."
  [form]
  (let [[sentence opts problem] (sx/form-peel form)]
    (when problem
      (throw (ex-info (:message problem) (dissoc problem :message))))
    [sentence opts]))

;; ---- reading ------------------------------------------------------------

(defn- skip-to-form!
  "Advance `r` past whitespace, commas and `;` comments, so its line number is the line
  the next form opens on."
  [^LineNumberingPushbackReader r]
  (loop []
    (let [c (.read r)]
      (cond
        (neg? c)                                        nil
        (or (Character/isWhitespace c) (= c (int \,)))  (recur)
        (= c (int \;))                                  (do (.readLine r) (recur))
        :else                                           (.unread r c)))))

(defn- unreadable
  "The refusal for a form of `source` that does not read, opening on `line`.  The EDN
  reader's own message is not carried, since it can quote the file (a token, a tag), and
  `kb-diff` sends a refusal's message over the wire; the failure is named by kind."
  [source line ^Throwable t]
  (let [m    (str (ex-message t))
        kind (cond
               (instance? StackOverflowError t)
               "it nests deeper than the reader's stack"
               (str/starts-with? m "EOF while reading")
               "the file ends before the form closes"
               (str/starts-with? m "No reader function for tag")
               "it holds a #tag the EDN reader has no function for"
               (str/starts-with? m "No dispatch macro for")
               "it holds a # dispatch the EDN reader does not read, #= among them"
               :else
               "it holds a token or delimiter the EDN reader does not read")]
    (ex-info (str "text KB file " source ", line " line ": the form that opens there does not"
                  " read as EDN — " kind)
             {:type :unreadable :file (str source) :line line})))

(defn form-spans
  "Every form in the text KB file `source` (anything `io/reader` takes), in file order, as
  `{:form f :start line :end line}`: the 1-based lines the form opens and closes on.
  `clojure.edn`, so comments and blank lines added no work and no code can run.  A form
  that does not read is refused as `:unreadable`, carrying `:file` and the `:line` it
  opens on and never the file's text."
  [source]
  (with-open [r (LineNumberingPushbackReader. (io/reader source))]
    (let [eof (Object.)]
      (loop [acc []]
        (skip-to-form! r)
        (let [line (.getLineNumber r)
              form (try (edn/read {:eof eof} r)
                        (catch Exception e (throw (unreadable source line e)))
                        (catch StackOverflowError e (throw (unreadable source line e))))]
          (if (identical? form eof)
            acc
            (recur (conj acc {:form form :start line :end (.getLineNumber r)}))))))))

(defn read-forms
  "Every form in the text KB file `source`, in file order (`form-spans`)."
  [source]
  (mapv :form (form-spans source)))

(defn context-of
  "The context a text KB file asserts into: its name without the `.txt`."
  [^File f]
  (let [n (.getName f)]
    (symbol (if (str/ends-with? n ".txt") (subs n 0 (- (count n) 4)) n))))

(defn kb-file?
  "Is `f` a context file of a text KB directory — a regular `Cx….txt`?  The prefix is
  the discriminant so a directory holding a README or a checksum is read for its KB
  files rather than refused for the rest."
  [^File f]
  (let [n (.getName f)]
    (and (.isFile f) (str/starts-with? n "Cx") (str/ends-with? n ".txt"))))

(defn kb-files
  "The context files of the text KB directory `dir`, in name order."
  [^File dir]
  (into [] (sort-by #(.getName ^File %) (filter kb-file? (.listFiles dir)))))

(def manifest-file
  "The file a delta export writes beside its context files: `{file {form-index [digest …]}}`,
  the digest of each reference a form holds, in the order `entry/references` reads them."
  "digests.edn")

(defn entries
  "Every `[form context]` a text KB holds, with the files they came from:
  `{:files [\"CxUniverse.txt\" …] :entries [[form context] …] :path \"…\"}`.  In a
  directory holding a `manifest-file`, each entry is `[form context digests]`.

  `source` is a **directory** of `Cx….txt` files — an `export-text!` destination, or an
  ontology tree an author keeps — or a single such file, the context of a form its file's
  name.  A directory is read whole for one `load-entries!` pass, since one context's
  content can rest on another's."
  [source]
  (let [^File f (io/file source)]
    (when-not (.exists f)
      (throw (ex-info (str "no text KB at " (.getPath f) " — a text KB is a directory of"
                           " Cx….txt context files, or one such file")
                      {:type :missing-resource :path (.getPath f)})))
    (let [files    (if (.isDirectory f) (kb-files f) [f])
          ^File mf (io/file f manifest-file)
          manifest (when (and (.isDirectory f) (.isFile mf)) (edn/read-string (slurp mf)))]
      (when (empty? files)
        (throw (ex-info (str (.getPath f) " holds no Cx….txt context files")
                        {:type :missing-resource :path (.getPath f)})))
      {:path    (.getPath f)
       :files   (mapv #(.getName ^File %) files)
       :entries (into [] (mapcat (fn [^File cf]
                                   (let [context (context-of cf)
                                         ds      (when manifest (get manifest (.getName cf) {}))]
                                     (map-indexed (fn [i form]
                                                    (cond-> [form context] ds (conj (get ds i []))))
                                                  (read-forms cf)))))
                      files)})))

(defn- topology-first
  "`entries` with every `(genlCx …)` moved to the front, then every declaration of a
  reference position (`(target_following_predicate P)`, `(arg P n sentence)`, a `quotedArg`
  or `quotedArgAndRest` typing `sentex_handle_term`), stable otherwise. A firing with no
  placement context is dropped as a `:no-placement` violation, and a sentence at a position
  not yet declared a reference is stored as written; the retry loop sees neither, because
  it retries what threw. A stable partition on the sentence's functor, never on arrival.
  See docs/kbs.md, \"Text you exported yourself\"."
  [entries]
  (let [head       (fn [[form _]] (let [s (first (sx/form-peel form))] (when (sequential? s) s)))
        topology?  #(= 'genlCx (first (head %)))
        reference? #(let [[f & args] (head %)]
                      (or (= 'target_following_predicate f)
                          (and (= 'arg f) (= 'sentence (nth args 2 nil)))
                          (and (contains? sx/arg-projections f) (= 'sentence (second args)))
                          (and (#{'quotedArg 'quotedArgAndRest} f)
                               (= 'sentex_handle_term (nth args 2 nil)))))
        rest?      #(not (or (topology? %) (reference? %)))]
    (-> []
        (into (filter topology?) entries)
        (into (filter #(and (reference? %) (not (topology? %)))) entries)
        (into (filter rest?) entries))))

(defn load-entries!
  "Assert every `[form context]` of `entries` through `assert!` (`(assert! sentence context
  opts)`, or `(assert-inert! sentence context)` for a form `peel-form` reads as inert),
  order-insensitively: an entry refused because content further down the list has not
  arrived is retried. Returns how many entries were read. Both writers are passed in
  because this sits under `vaelii.core`. The context topology and the reference declarations
  go first (`topology-first`). Retry rounds run while each makes progress; the survivors of
  a round that changed nothing are re-asserted without a catch, so an ill-formed entry
  throws, or with `refused!` call `(refused! entry ex-info)` per refusal.  With `check!`,
  an entry carrying digests is passed to `(check! sentence context digests)` first."
  ([assert! assert-inert! entries] (load-entries! assert! assert-inert! entries nil nil))
  ([assert! assert-inert! entries refused! check!]
   (let [entries (topology-first entries)
         apply!  (fn [[form context digests]]
                   (let [[sentence o] (peel-form form)]
                     (when (and check! digests) (check! sentence context digests))
                     (if (:inert o)
                       (assert-inert! sentence context)
                       (assert! sentence context o))))
         attempt (fn [round es]
                   (with-open [r (progress/start ::load-entries
                                                 (str "load: assert the entries (round " round ")")
                                                 (count es))]
                     (reduce (fn [acc e]
                               (let [acc (try (apply! e) acc
                                              (catch clojure.lang.ExceptionInfo _ (conj acc e)))]
                                 (progress/tick! r)
                                 acc))
                             [] es)))]
     (loop [round 1, pending (attempt 1 entries)]
       (when (seq pending)
         (let [remaining (attempt (inc round) pending)]
           (cond
             (< (count remaining) (count pending)) (recur (inc round) remaining)
             refused! (doseq [e remaining]
                        (try (apply! e)
                             (catch clojure.lang.ExceptionInfo x (refused! e x))))
             :else    (run! apply! remaining))))))
   (count entries)))

(defn- mismatch-message
  [sentence why]
  (str "the delta's digests and this KB's reading of " (pr-str sentence) " differ: " why
       " — the two KBs canonicalize the sentence differently"))

(defn digest-check
  "A `check!` for `load-entries!` over `kb`: throws `:canonical-mismatch` when the references
  `entry/references` reads in `sentence` are not as many as `digests`, or when one resolves
  to a sentex whose digest is not the one its writer recorded, naming the reference under
  `:reference`.  An `(ist Cx S)` form is `S` read in `Cx`."
  [kb]
  (fn [sentence context digests]
    (let [[context s] (or (entry/ist-parts sentence) [context sentence])
          refs        (entry/references kb (rules/inner-rule s) context)
          actual      (digest/digests kb (mapv :handle refs) false)]
      (when (not= (count refs) (count digests))
        (throw (ex-info (mismatch-message s (str "the writer recorded " (count digests)
                                                 " references and this KB reads " (count refs)))
                        {:type :canonical-mismatch :sentence s
                         :expected (count digests) :actual (count refs)})))
      (doseq [[r e a] (map vector refs digests actual) :when (not= e a)]
        (throw (ex-info (mismatch-message s (str "the reference " (pr-str (:reference r))
                                                 " resolves to a sentex whose digest is " a
                                                 ", and the writer's is " e))
                        {:type :canonical-mismatch :sentence s :reference (:reference r)
                         :context (:context r) :expected e :actual a}))))))

;; ---- writing -------------------------------------------------------------

(defn- authored
  "A stored sentex as its author wrote it: the canonical variables put back through the
  record's own varmap, and the direction / default / assumption / constraint wrappers
  rewrapped around it (`rules/rewrap-sentex` — they ride the record, not the sentence).  A fact
  carries neither and comes back unchanged."
  [sx]
  (let [s (sx/authored-sentence sx)]
    (if (some? (:antecedent sx)) (rules/rewrap-sentex s sx) s)))

(defn- exception-form
  "The `(exceptWhen <query> <rule>)` wrapper an exceptWhen meta-sentex was written as, under
  whichever strength wrappers reproduce the pair, the query in the rule's own variables. An
  outer `(set/monotonic …)` only when both halves are known-true, else on the query. A rule
  another context stores is written `(ist Cx <rule>)`, and on its own line there."
  [meta-sx rule-sx]
  (let [q      (nth (:sentence meta-sx) 1)
        q      (if-let [vm (:varmap rule-sx)] (sx/originalize q vm) q)
        there? (not= (:context meta-sx) (:context rule-sx))
        exc?   (= :monotonic (:strength meta-sx))
        rule?  (and (not there?) (= :monotonic (:strength rule-sx)))
        query? (and exc? (not rule?))]
    (cond-> (list sx/except-wrapper
                  (cond-> q query? (->> (list sx/strength-wrapper)))
                  (cond->> (authored rule-sx)
                    there? (list sx/ist-functor (:context rule-sx))))
      (and exc? rule?) (->> (list sx/strength-wrapper)))))

(defn- with-strength
  "`form` under its strength wrapper, or bare at `:default` — the entry point's own fallback,
  which is why no shipped file carries one."
  [form strength]
  (cond-> form (= :monotonic strength) (->> (list sx/strength-wrapper))))

(defn- reference-writer
  "A fn from a sentence of `kb` to `[sentence digests]`: the sentence a text KB writes, each
  handle at a reference position (`res/reference-positions`) spelled `(ist Cx S)`, `S` the
  named record's sentence as `authored` writes it with its own handles spelled the same
  way, and the digest of each reference in the order `entry/references` reads them.  A
  function term (`res/reference-term?`) is written the same way at its function's
  positions.  nil when a handle names no stored record, or stands at no reference position."
  [kb]
  (let [dg   (digest/digester kb)
        recs (:records kb)
        ps   (memoize #(res/reference-positions kb %))]
    (fn write [sentence]
      (if-not (sequential? sentence)
        [sentence []]
        (let [refs (ps (first sentence))
              out  (volatile! [])
              bare (= sx/except-functor (first sentence))
              arg  (fn [i a]
                     (cond
                       (and refs (refs i) (or (sx/sentex-handle? a) (and bare (integer? a))))
                       (let [h (if (integer? a) a (sx/handle-id a))
                             t (p/get-sentex recs h)
                             [s ds] (when t (write (authored t)))
                             d (when s (dg h))]
                         (if d
                           (do (vswap! out into ds) (vswap! out conj d)
                               (list sx/ist-functor (:context t) s))
                           ::unwritten))
                       (not (some sx/sentex-handle? (tree-seq sequential? seq a))) a
                       (res/reference-term? a) (if-let [[t ds] (write a)]
                                                 (do (vswap! out into ds) t)
                                                 ::unwritten)
                       :else ::unwritten))
              args (into [] (map-indexed arg) sentence)]
          (when-not (some #{::unwritten} args)
            [(apply list args) @out]))))))

(defn- premise-records
  "Every live premise of `kb`, as records.  A premise **is** a sentex whose `:strength`
  is non-nil, and `p/premise-ids` is the set of them."
  [kb]
  (let [recs (:records kb)
        ids  (p/premise-ids recs)]
    (with-open [r (progress/start ::premise-records "text export: read the premise records"
                                  (count ids))]
      (into [] (keep (fn [h] (progress/tick! r) (p/get-sentex recs h))) ids))))

(defn- inert-records
  "Every inert sentex of `kb` (`assert-inert`), as records: a stored sentex that is no
  premise and that the TMS holds no node for.  A derived sentex has a node, so the two
  read apart only over a built network.  Over an unbuilt one (`kb/write-hazards` names
  `:no-belief` or `:stale-belief`) a record outside the premise set is either, and
  this refuses `:unrecovered-kb` rather than write a derived sentex as inert."
  [kb]
  (let [recs     (:records kb)
        tms      (reasoning/tms kb)
        premises (p/premise-ids recs)
        all      (p/sentex-ids recs)
        ids      (with-open [r (progress/start ::inert-ids "text export: find the inert sentexes"
                                               (count all))]
                   (into [] (remove (fn [h]
                                      (progress/tick! r)
                                      (or (contains? premises h) (jtms/known-datum? tms h))))
                         all))
        hz       (when (seq ids) (kb/write-hazards kb))]
    (when (or (:no-belief hz) (:stale-belief hz))
      (let [msg (str "export-text! over a KB whose belief is not built: " (count ids)
                     " stored sentexes are neither premises nor TMS nodes, and an inert"
                     " sentex and a derived one read alike until the network is built."
                     "  Call (recover kb) and export then.")]
        (throw (ex-info msg {:type :unrecovered-kb :hazards (vec (sort (keys hz)))
                             :operation "export-text!" :repair 'recover :message msg}))))
    (with-open [r (progress/start ::inert-records "text export: read the inert records"
                                  (count ids))]
      (into [] (keep (fn [h] (progress/tick! r) (p/get-sentex recs h))) ids))))

(defn premise-entries
  "`[entries skipped]` for `records` of `kb`, premises and inert sentexes: each as the form a KB
  file writes it, `{:context c :form f :handles [h …] :digests [d …]}`, and the records
  there is no text for. `:handles` are the records the form stands for, so a caller knows
  what to retract; `:digests` are `reference-writer`'s, on a form holding references.
  An ordinary fact or rule is `authored` under its strength wrapper, an inert sentex under
  `(set/inert …)`. An exceptWhen meta-sentex is written as the `(exceptWhen <query> <rule>)`
  wrapper (`exception-form`), and a target rule in its context is not written again unless
  known-true under a default exception. Anything else naming a handle is written through
  `reference-writer` (`sx/names-a-handle?`), and skipped and counted when it has no text."
  [kb records]
  (let [ids      (into #{} (map :id) records)
        meta?    #(sx/exceptWhen-meta? (:sentence %))
        write    (reference-writer kb)
        rule-of  #(p/get-sentex (:records kb) (sx/exceptWhen-rule-handle (:sentence %)))
        by-rule  (into {} (comp (filter meta?)
                                (keep (fn [m] (when-let [r (rule-of m)]
                                                (when (= (:context r) (:context m)) r))))
                                (filter (comp ids :id))
                                (filter #(some? (:strength %)))
                                (map (juxt :id identity)))
                       records)
        elsewhere (fn [m] (when-let [r (rule-of m)]
                            (when (and (some? (:strength r)) (not= (:context r) (:context m)))
                              r)))]
    (with-open [r (progress/start ::premise-entries "text: build the text forms"
                                  (when (counted? records) (count records)))]
      (reduce
       (fn [[written skipped] sx]
         (progress/tick! r)
         (let [keep! (fn [form hs & [ds]]
                       [(conj written (cond-> {:context (:context sx) :form form :handles hs}
                                        (seq ds) (assoc :digests ds)))
                        skipped])
               drop! (fn [] [written (conj skipped sx)])]
           (cond
             (and (meta? sx) (by-rule (sx/exceptWhen-rule-handle (:sentence sx)))
                  (= (:context sx) (:context (by-rule (sx/exceptWhen-rule-handle (:sentence sx))))))
             (let [rule (by-rule (sx/exceptWhen-rule-handle (:sentence sx)))]
               (keep! (exception-form sx rule) [(:id sx) (:id rule)]))

             (and (meta? sx) (elsewhere sx))
             (keep! (exception-form sx (elsewhere sx)) [(:id sx)])

             (sx/names-a-handle? (:sentence sx))
             (if-let [[s ds] (write (authored sx))]
               (keep! (if (nil? (:strength sx))
                        (list sx/inert-wrapper s)
                        (with-strength s (:strength sx)))
                      [(:id sx)] ds)
               (drop!))

             ;; an excepted rule rides its own wrapper, unless the wrapper would state a
             ;; weaker class than the rule stands at
             (and (by-rule (:id sx)) (not= :monotonic (:strength sx))) [written skipped]

             (nil? (:strength sx)) (keep! (list sx/inert-wrapper (authored sx)) [(:id sx)])

             :else (keep! (with-strength (authored sx) (:strength sx)) [(:id sx)]))))
       [[] []]
       records))))

(defn- context-forms
  "`[{context [entry …]} skipped]` for `records` of `kb` — the `premise-entries` of each,
  grouped by the context it holds in, in content order, and the records there is no text
  for."
  [kb records]
  (let [[entries skipped] (premise-entries kb records)
        by-context (group-by :context entries)]
    [(into {} (map (fn [[c es]]
                     (let [ds (into {} (map (juxt :form :digests)) es)]
                       [c (mapv (fn [f] {:form f :digests (ds f)}) (nm/by-print-key (map :form es)))])))
           by-context)
     skipped]))

(def ^:private opt-keys
  "Every key the text writer reads, and `:delta?`, which `vaelii.core/export-text!` reads
  to choose the records."
  #{:context :ancestor-set :delta?})

(defn- selected-contexts
  "The contexts an export covers: every one with something to write, or the one
  `:context` names, or the `genlCx` ancestor set `:ancestor-set` names — `c` and every context it
  **sees**, which is the slice a reload needs for `c`'s own content to mean what it
  meant."
  [kb written {:keys [context ancestor-set]}]
  (cond
    context (filterv #{context} (keys written))
    ancestor-set    (let [up (set (tax/context-up (reasoning/taxonomy kb) ancestor-set))]
                      (filterv up (keys written)))
    :else   (vec (keys written))))

(defn- file-text
  "One context file's whole text: a two-line header naming the context, then `forms`, in
  **content** order, one per line.  Nothing here is a fact about this run — no timestamp,
  no writer — so two exports of the same knowledge are byte-identical."
  [context forms]
  (binding [*print-length* nil *print-level* nil *print-meta* false]
    (str ";; " context " — a vaelii text KB: one sentence per form, and the file name\n"
         ";; is the context.  Read by `lein cli load` and vaelii.core/load-text!.\n\n"
         (str/join "\n" (map pr-str forms))
         "\n")))

(defn write-kb!
  "Write `kb`'s premises and inert sentexes into `dir` as a text KB, one `<Context>.txt` per
  context, and return `{:contexts n :sentences n :skipped n :files [\"CxUniverse.txt\" …]
  :bytes n :elapsed-ms n :dir \"…\"}`. `opts`: `{:context C}` for one context's file,
  `{:ancestor-set C}` for `C` and every context it sees; neither writes every context with
  a premise or an inert sentex. A key this fn does not read is refused (`:unknown-option`).
  `records` replaces the premises and inert sentexes. `dir` must be absent or empty. With
  `:delta?`, the `manifest-file` holds the digests of each form's references."
  ([kb dir] (write-kb! kb dir {}))
  ([kb dir o] (write-kb! kb dir o nil))
  ([kb dir o records]
   (opts/check! o opt-keys "export-text!"
                (str "A narrowing nothing reads writes the whole KB, and the summary"
                     " looks the same either way."))
   (let [t0            (System/nanoTime)
         ^File d       (export/ensure-empty-dir! dir "text export destination" "a text KB")
         [written skipped] (context-forms kb (or records
                                                 (into (premise-records kb) (inert-records kb))))
         contexts      (sort (selected-contexts kb written o))
         files         (with-open [r (progress/start ::write-kb "text export: write the context files"
                                                     (count contexts))]
                         (mapv (fn [context]
                                 (let [f (io/file d (str context ".txt"))]
                                   (with-open [w (io/writer f)]
                                     (.write w ^String (file-text context (map :form (written context)))))
                                   (progress/tick! r)
                                   (.getName f)))
                               contexts))]
     (when (:delta? o)
       (binding [*print-length* nil *print-level* nil *print-meta* false]
         (spit (io/file d manifest-file)
               (pr-str (into (sorted-map)
                             (map (fn [c]
                                    [(str c ".txt")
                                     (into (sorted-map)
                                           (keep-indexed (fn [i e] (when (:digests e) [i (:digests e)])))
                                           (written c))]))
                             contexts)))))
     {:contexts   (count files)
      :sentences  (transduce (map #(count (written %))) + 0 contexts)
      :skipped    (count skipped)
      :files      files
      :bytes      (transduce (map (fn [n] (.length (io/file d ^String n)))) + 0 files)
      :elapsed-ms (long (/ (- (System/nanoTime) t0) 1000000))
      :dir        (.getPath d)})))
