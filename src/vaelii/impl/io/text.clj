;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.io.text
  "The **text KB format** — one file per context, one s-expression per sentence — read
  and written.

  It is the format the shipped ontology is authored in (`resources/kb/`,
  `vaelii.host.seed`), and this is where the writer for it lives, so a KB an author
  edited as text can be got back out of a store as text.  The three formats a KB moves
  in are different questions and stay separate entry points:

  | | what it holds | who reads it |
  |---|---|---|
  | **text** (here) | premises, in the author's own spelling, no handles | `assert` |
  | **export dump** (`io.export` / `io.import`) | every record and justification at its own handle | `import!` |
  | the **store** itself | the live KB | the engine |

  A dump is a KB's *state*; text is a KB's *content*.  Only the second survives a
  re-derivation, a rename or an engine that concludes something new — which is what an
  author editing an ontology wants, and what a dump deliberately is not.

  ## The format

  Every form is one sentence, read with `clojure.edn`, so a KB file is data and can
  never run code.  `;;` comments and blank lines are free — the reader is the EDN
  reader, so it skips them without a line-oriented pass.  **The file name is the
  context**: `CxKinship.txt` asserts into `CxKinship`, and a sentence for another
  context says so with `(ist Cx S)` as it would anywhere else.  A rule carries its
  `set/*Rule` / `set/defaultRule` wrappers and its `exceptWhen` exactly as an author
  writes them, because that is what `assert` reads.

  **One wrapper is not part of the sentence**: `(set/monotonic S)`, the known-true
  class.  A strength is an *option* on the assertion rather than part of the sentence, so
  there is nowhere in an s-expression for it to go, and a text KB that could not say it
  would round-trip a KB's monotonic premises down to defaults.  It is peeled by
  `load-entries!` below into `{:strength :monotonic}` and never reaches the store as a
  functor.  `:default` is the entry point's own fallback and is written as nothing, which is why
  no shipped file carries a wrapper.

  **An `exceptWhen` states a strength per half**, because it asserts two things: the rule,
  and the exception qualifying it.  The outer wrapper is the assertion's own option and
  `assert` gives it to *both*, so it can only state a class the two share; a wrapper on
  the **query** states the exception's own, and `assert` reads that one itself
  (`sentex/peel-exception-strength`), so a hand-written KB spells it the same way.  Four
  pairings, four spellings:

  | rule | exception | written as |
  |---|---|---|
  | default | default | `(exceptWhen Q R)` |
  | default | known-true | `(exceptWhen (set/monotonic Q) R)` |
  | known-true | default | `(exceptWhen Q R)`, and `(set/monotonic R)` on a line of its own |
  | known-true | known-true | `(set/monotonic (exceptWhen Q R))` |

  The third takes two lines because there is no wrapper for *weakening* a half: the rule
  gets a line of its own at the stronger class, and `mark-premise` resolves a premise
  asserted twice to the stronger of the two.

  ## What a text export holds, and what it does not

  **Premises only.**  A derived sentex is what the engine concluded from the premises,
  so writing it out would store as a premise what the KB believes as a conclusion — a
  reload would hold it against retraction of everything it followed from.  Chaining
  puts it back at load, which is the whole point.

  **No handles.**  A text KB is re-asserted rather than restored, so it lands at
  whatever handles the loading KB mints.  A caller who needs handle identity across the
  round trip wants `export!`, not this.

  **Deterministic.**  Files are named for their contexts and their forms are ordered by
  content (`nm/by-print-key`), never by handle — so two KBs holding the same knowledge
  export byte-identical files whatever order they were built in
  (docs/defenses.md, \"Tie-breaks and orderings key on content\")."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.opts :as opts]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning])
  (:import [java.io File PushbackReader]))

;; ---- the strength wrapper ------------------------------------------------

(defn peel-strength
  "`[sentence opts]` for one form of a text KB file: a `(set/monotonic S)` wrapper
  becomes `S` with `{:strength :monotonic}`, and anything else is itself with `nil`.

  The wrapper is refused rather than passed through when it is malformed — a bare
  `(set/monotonic)` or one wrapping two sentences would otherwise reach `assert` as a
  sentence whose functor is a namespace-qualified symbol, and be refused there for the
  wrong reason."
  [form]
  (if (and (sequential? form) (= sx/strength-wrapper (first form)))
    (if (= 2 (count form))
      [(second form) {:strength :monotonic}]
      (throw (ex-info (str "(" sx/strength-wrapper " …) wraps exactly one sentence, got "
                           (dec (count form)) ": " (pr-str form))
                      {:type :shape :form form})))
    [form nil]))

;; ---- reading ------------------------------------------------------------

(defn read-forms
  "Every form in the text KB file `source` (anything `io/reader` takes), in file order.
  `clojure.edn`, so comments and blank lines added no work and no code can run."
  [source]
  (with-open [r (PushbackReader. (io/reader source))]
    (let [eof (Object.)]
      (loop [acc []]
        (let [form (edn/read {:eof eof} r)]
          (if (identical? form eof) acc (recur (conj acc form))))))))

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

(defn entries
  "Every `[form context]` a text KB holds, with the files they came from:
  `{:files [\"CxCore.txt\" …] :entries [[form context] …] :path \"…\"}`.

  `source` is a **directory** of `Cx….txt` files — an `export-text!` destination, or an
  ontology tree an author keeps — or a single such file.  Either way the context of a
  form is its file's name, so a directory is read whole and handed to `load-entries!` in
  one pass rather than a file at a time: the names sort alphabetically, which is not a
  dependency order, and one context's content can rest on another's."
  [source]
  (let [^File f (io/file source)]
    (when-not (.exists f)
      (throw (ex-info (str "no text KB at " (.getPath f) " — a text KB is a directory of"
                           " Cx….txt context files, or one such file")
                      {:type :missing-resource :path (.getPath f)})))
    (let [files (if (.isDirectory f) (kb-files f) [f])]
      (when (empty? files)
        (throw (ex-info (str (.getPath f) " holds no Cx….txt context files")
                        {:type :missing-resource :path (.getPath f)})))
      {:path    (.getPath f)
       :files   (mapv #(.getName ^File %) files)
       :entries (into [] (mapcat (fn [^File cf]
                                   (let [context (context-of cf)]
                                     (map #(vector % context) (read-forms cf)))))
                      files)})))

(defn- topology-first
  "`entries` with every `(genlCx …)` moved to the front, stable otherwise — the one
  ordering the retry loop below cannot supply for itself.

  A completed firing needs a **placement context**: one that sees the rule and every
  antecedent fact.  Where there is none the conclusion is *dropped* — a `:no-placement`
  violation, recorded rather than raised — so an edge arriving after the fact it would
  have placed leaves a conclusion nothing re-derives, and the retry loop never sees it,
  because it retries what **threw**.  The context spindle is what `vaelii.host.starter`
  keeps in code for the same reason (CxCore, then the upper layer, then the middle),
  and a directory of files carries no such order.  So the topology goes in first, and
  everything else is retried against the whole of it.

  Deterministic: a stable partition on the sentence's functor, never on arrival."
  [entries]
  (let [topology? (fn [[form _]] (and (sequential? form) (= 'genlCx (first form))))]
    (into (filterv topology? entries) (remove topology? entries))))

(defn load-entries!
  "Assert every `[form context]` of `entries` through `assert!` —
  `(assert! sentence context opts)` — **order-insensitively**: an entry refused because
  content further down the list has not arrived yet is retried rather than fatal.
  Returns how many entries were read.

  `assert!` is passed in rather than required: this sits under `vaelii.core`, and the
  two callers above it are `vaelii.core/load-text!` and `vaelii.host.seed`.

  A KB file's order is its *terms'*, not its dependencies' — blocks run in natural sort
  order, which is the whole point of grouping term-centrically — so a file cannot also
  be dependency-ordered.  `(transitiveInArg largerThan 1 partOf)` sits under `largerThan`
  and `(transitive partOf)` under `partOf`, and `l` sorts before `p`.  Several checks
  read the store (a preservation's transitivity, an `arg` clash, a disjointness), so
  without this a term-centric file is refused for where its author filed a sentence.
  **A whole directory is one pass**, for the same reason one level up: the file names
  sort alphabetically and a context's content can rest on another's.  The **context
  topology goes first** whatever order it arrived in (`topology-first`), which is the one
  thing retrying cannot fix.

  Retry rounds run while each one makes progress; the entries that survive a round that
  changed nothing are re-asserted **without a catch**, so a genuinely ill-formed one
  still throws — carrying the error it has once everything that could have helped it is
  stored, which is the error worth reporting.  A list that loads clean pays one `try`
  per entry and no second round."
  [assert! entries]
  (let [entries (topology-first entries)
        apply!  (fn [[form context]]
                  (let [[sentence o] (peel-strength form)]
                    (assert! sentence context o)))
        attempt (fn [es]
                  (reduce (fn [acc e]
                            (try (apply! e) acc
                                 (catch clojure.lang.ExceptionInfo _ (conj acc e))))
                          [] es))]
    (loop [pending (attempt entries)]
      (when (seq pending)
        (let [remaining (attempt pending)]
          (if (< (count remaining) (count pending))
            (recur remaining)
            (run! apply! remaining))))))
  (count entries))

;; ---- writing -------------------------------------------------------------

(defn- authored
  "A stored sentex as its author wrote it: the canonical variables put back through the
  record's own varmap, and the direction / default / assumption / constraint wrappers
  rewrapped around it (`rules/rewrap` — they ride the record, not the sentence).  A fact
  carries neither and comes back unchanged."
  [sx]
  (let [s (if-let [vm (:varmap sx)] (sx/originalize (sx/sentence-of sx) vm) (sx/sentence-of sx))]
    (rules/rewrap s (:direction sx) (:defeasible sx) (:assumption sx) (:constraint sx))))

(defn- exception-form
  "The `(exceptWhen <query> <rule>)` wrapper an exceptWhen meta-sentex was written as,
  under whichever strength wrappers reproduce the pair.

  The stored meta is `(exceptWhen <query> (sentexHandle H))` and its query is in the
  **rule's** canonical variables, so the rule's varmap is what restores it — the meta
  has none of its own.

  **Two halves, two classes, and the outer wrapper can only state one.**  `assert` gives
  one `opts` to both, so an outer `(set/monotonic …)` says *both* are known-true and is
  written only when they are; a known-true exception on a default rule carries its
  wrapper on the **query** instead, which is the position `assert` reads it in
  (`sentex/peel-exception-strength`).  The remaining pairing — a known-true rule under a
  default exception — needs no wrapper here at all: `context-forms` writes the rule again
  on a line of its own, and `mark-premise` resolves to the stronger."
  [meta-sx rule-sx]
  (let [q      (nth (:sentence meta-sx) 1)
        q      (if-let [vm (:varmap rule-sx)] (sx/originalize q vm) q)
        exc?   (= :monotonic (:strength meta-sx))
        rule?  (= :monotonic (:strength rule-sx))
        query? (and exc? (not rule?))]
    (cond-> (list sx/except-wrapper
                  (cond-> q query? (->> (list sx/strength-wrapper)))
                  (authored rule-sx))
      (and exc? rule?) (->> (list sx/strength-wrapper)))))

(defn- with-strength
  "`form` under its strength wrapper, or bare at `:default` — the entry point's own fallback,
  which is why no shipped file carries one."
  [form strength]
  (cond-> form (= :monotonic strength) (->> (list sx/strength-wrapper))))

(defn- names-a-handle?
  "Does `sentence` name a stored sentex by handle?  Such a sentence has no text form: a
  handle is this KB's own and means something else, or nothing, in the KB that reads the
  file back.

  Two spellings, and the second is why this is not one `tree-seq`.  A `(sentexHandle N)`
  term anywhere inside — what an exceptWhen meta and a target-following meta carry — is a
  handle **by shape**.  An `(except N)` carries a bare integer, a handle **by position**,
  indistinguishable from the `86400` in `(conversionFactor Day Second 86400)`; so it is
  recognised by its functor instead."
  [sentence]
  (boolean (or (and (sequential? sentence) (= sx/except-functor (first sentence)))
               (some sx/sentex-handle? (tree-seq sequential? seq sentence)))))

(defn- premise-records
  "Every live premise of `kb`, as records.  A premise **is** a sentex whose `:strength`
  is non-nil, and `p/premise-ids` is the roster of them."
  [kb]
  (let [recs (:records kb)]
    (into [] (keep #(p/get-sentex recs %)) (p/premise-ids recs))))

(defn- context-forms
  "`[{context [form …]} skipped]` for `kb` — the text of every premise, grouped by the
  context it holds in, and the premises there is no text for.

  Three kinds of premise, and the second is the one that needs assembling:

  * an ordinary fact or rule is `authored` under its strength wrapper;
  * an **exceptWhen meta-sentex** is not written as stored — `(exceptWhen <query>
    (sentexHandle H))` names a handle the reading KB does not have — but as the
    `(exceptWhen <query> <rule>)` wrapper it was asserted as, under whichever strength
    wrappers reproduce the two halves' classes (`exception-form`).  Its target rule is
    then not written again on its own, exactly as a shipped file writes the wrapper and
    not the bare rule; a rule known-true under a `:default` exception gets its own line
    as well, since the wrapper would state the weaker class and `mark-premise` resolves
    to the stronger of the two.
  * anything else naming a handle — an `(except H)`, a `target_following_predicate` meta,
    an exceptWhen meta on a rule the KB *derived* — is **skipped and counted**
    (`names-a-handle?` for the two ways a sentence spells one).  There
    is no spelling for it: the handle is a fact about this store, and a wrapper around a
    derived rule would assert as a premise something the KB never held as one."
  [kb]
  (let [recs     (:records kb)
        premises (premise-records kb)
        meta?    #(sx/exceptWhen-meta? (:sentence %))
        by-rule  (into {} (comp (filter meta?)
                                (keep #(p/get-sentex recs (sx/exceptWhen-rule-handle (:sentence %))))
                                (filter #(some? (:strength %)))
                                (map (juxt :id identity)))
                       premises)]
    (reduce
     (fn [[written skipped] sx]
       (let [keep! (fn [form] [(update written (:context sx) (fnil conj []) form) skipped])
             drop! (fn [] [written (conj skipped sx)])]
         (cond
           (meta? sx)
           (if-let [rule (by-rule (sx/exceptWhen-rule-handle (:sentence sx)))]
             (keep! (exception-form sx rule))
             (drop!))

           (names-a-handle? (:sentence sx)) (drop!)

           ;; an excepted rule rides its own wrapper, unless the wrapper would state a
           ;; weaker class than the rule stands at
           (and (by-rule (:id sx)) (not= :monotonic (:strength sx))) [written skipped]

           :else (keep! (with-strength (authored sx) (:strength sx))))))
     [{} []]
     premises)))

(def ^:private opt-keys
  "Every key the text writer reads."
  #{:context :ancestor-set})

(defn- ensure-empty-dir!
  "`dir` as an empty directory, created when it does not exist.  A directory that
  already holds anything is **refused**: a second export over a first would leave the
  files the first wrote for contexts the second has nothing to say about, and a text KB
  is read as a whole directory."
  ^File [dir]
  (let [^File d (io/file dir)]
    (when (.isFile d)
      (throw (ex-info (str "text export destination " (.getPath d)
                           " is a file, not a directory")
                      {:type :not-a-directory :dir (.getPath d)})))
    (when-let [kids (seq (.listFiles d))]
      (throw (ex-info (str "text export destination " (.getPath d) " is not empty ("
                           (count kids) " entries) — a text KB is a directory of its own")
                      {:type :not-empty :dir (.getPath d)
                       :entries (mapv #(.getName ^File %) (take 8 kids))})))
    (.mkdirs d)
    d))

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
  "One context file's whole text: a two-line header naming the context, then its forms
  in **content** order, one per line.  Nothing here is a fact about this run — no
  timestamp, no writer — so two exports of the same knowledge are byte-identical."
  [context forms]
  (binding [*print-length* nil *print-level* nil *print-meta* false]
    (str ";; " context " — a vaelii text KB: one sentence per form, and the file name\n"
         ";; is the context.  Read by `lein cli load` and vaelii.core/load-text!.\n\n"
         (str/join "\n" (map pr-str (nm/by-print-key forms)))
         "\n")))

(defn write-kb!
  "Write `kb`'s premises into `dir` as a text KB — one `<Context>.txt` per context —
  and return a summary:

      {:contexts n :sentences n :skipped n :files [\"CxCore.txt\" …]
       :bytes n :elapsed-ms n :dir \"…\"}

  `opts` narrows what is written: `{:context C}` for that one context's file, `{:ancestor-set C}`
  for `C` and every context it sees.  Neither, and every context with a premise in it is
  written.  A key this fn does not read is refused (`:unknown-option`) — a misspelt
  narrowing writes the whole KB under a summary that looks right.

  `dir` must be absent or empty.  See the namespace docstring for what a text KB holds
  and what it deliberately does not."
  ([kb dir] (write-kb! kb dir {}))
  ([kb dir o]
   (opts/check! o opt-keys "export-text!"
                (str "A narrowing nothing reads writes the whole KB, and the summary"
                     " looks the same either way."))
   (let [t0            (System/nanoTime)
         ^File d       (ensure-empty-dir! dir)
         [written skipped] (context-forms kb)
         contexts      (sort (selected-contexts kb written o))
         files         (mapv (fn [context]
                               (let [f (io/file d (str context ".txt"))]
                                 (with-open [w (io/writer f)]
                                   (.write w ^String (file-text context (written context))))
                                 (.getName f)))
                             contexts)]
     {:contexts   (count files)
      :sentences  (transduce (map #(count (written %))) + 0 contexts)
      :skipped    (count skipped)
      :files      files
      :bytes      (transduce (map (fn [n] (.length (io/file d ^String n)))) + 0 files)
      :elapsed-ms (long (/ (- (System/nanoTime) t0) 1000000))
      :dir        (.getPath d)})))
