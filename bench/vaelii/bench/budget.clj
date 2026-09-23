;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.budget
  "What a KB holds **resident**, by structure and by backend, against a stated budget.

  The engine has excellent component measurements and no budget.  `bench-scale`,
  `bench-jtms`, `bench-postings`, `bench-records` and `bench-residency` each answer one
  structure's question on one corpus; none of them answers *\"what does a KB of N facts
  hold in heap, and where does it go?\"*  This adds it up — one row per resident
  structure, one column per backend, at two sizes — and extrapolates to a named target so
  the verdict is in the output rather than in a reader's arithmetic.

  ## What counts as resident

  jol retained heap, as `bench-residency` and `bench-jtms` take it: structural, so
  contention-immune, and the only kind of number worth extrapolating.  A mapped section
  is reported **separately and never as heap** — a `MappedByteBuffer` is an address and a
  length, and its pages live in the OS page cache.  Heap and mapped are told apart by
  `.isDirect` rather than by which section it is, so the split is measured rather than
  assumed; `vaelii.impl.disk.index-snapshot`'s own header lists the roots' key and offset
  columns under *resident*, and `load-roots!` maps all three columns, so the two readings
  disagree and only the buffer can settle it.

  ## The corpus

  Vocabulary-fixed, as `bench-residency`'s is: the same individuals, types and predicates
  at every N, so the only thing that grows is the extent.  **Four sizes**, geometric, so
  the answer is the growth between consecutive pairs, checked twice over instead of once —
  two points can name a shape but cannot test one, and three points test an affine fit at
  exactly one held-back sample.  A row that jumps between the *last* two of three samples
  (`docs/density.md`, the routed map's refusal) cannot be told apart from a genuinely
  linear row three points were too small to show; a fourth sample gives every row's affine
  fit two held-back points to be tested against instead of one.

  The individuals are the knob that decides whether the corpus reaches the size it was
  asked for.  `generate` draws them from a **Zipf** distribution, so at a narrow
  vocabulary the same triple is drawn repeatedly and canonicalization collapses it: over
  400 individuals a request for 240,000 ground facts stored 96,940 of them, 40%.  The
  default is wide enough that the request is mostly honoured (78% at the top size), and
  every block prints what it asked for beside what it stored so the shortfall is never
  silent.

  Plus one knob that harness lacks — **j/n, justifications per node**.  The dense JTMS is
  a two-term model (18 B/node + 166 B/justification, `docs/density.md`), so a
  premises-only corpus reports the flattering half of it.  Justifications are driven by
  forward rules whose conclusions **collapse onto a small head space**
  (`(pk ?x ?y) → (derives<i> ?x ?x)`), so each firing adds a justification while the
  derived nodes stay bounded by the individuals — which is what makes the ratio a knob
  instead of an outcome.  A single-antecedent rule over fresh conclusions caps at 0.5 (a
  justification per new node); collapsing the head is what reaches the ≈1.1 that
  `density.md` calls \"the form a common-sense KB actually takes\".  The **achieved**
  ratio is measured and reported — the argument is a target, never a claim.

  ## The extrapolation

  Stated as a shape, and **gated on every step**: a row is called linear only when each
  of the three growths agrees with its own fact ratio, flat only when all three are flat,
  and affine only when a fit through the outer two samples predicts both middle ones it
  was not fitted through.  A row that fits none of the three is reported unextrapolated,
  naming the growths that disqualified it, rather than multiplied out anyway.  `docs/density.md`
  earned the right to interpolate the JTMS by confirming flatness across a 50× range;
  every row here earns it the same way or does without.

  A row whose ceiling is a **configured constant** is read rather than fitted — see
  `capped-rows`.

  **What the target is not.**  The vocabulary is pinned, so a row that tracks it is
  reported flat and carried to the target unchanged.  A real 100,000,000-fact KB does not
  hold 8,000 individuals, so every flat row is a floor and the total that includes them is
  a floor too.  This bench prices the **extent**; it does not price a KB that large.

  Run: `lein bench-budget [facts] [step] [individuals] [target-facts] [budget-gb]`
       (default 60000 facts stepped ×2 three times — 60k/120k/240k/480k — over 8000
       individuals, to 100,000,000 against 40 GB)."
  (:require [clojure.string :as str]
            [vaelii.bench.postings :as postings]
            [vaelii.core :as v]
            [vaelii.impl.columnar :as col]
            [vaelii.impl.config :as config]
            [vaelii.impl.disk.backend :as disk]
            [vaelii.host.io.generate :as gen]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.types.dense-roots :as dense-roots-types]
            [vaelii.impl.types.snapshot :as snapshot-types])
  (:import [java.nio Buffer ByteBuffer DoubleBuffer FloatBuffer IntBuffer LongBuffer ShortBuffer]))

;; ---- measurement ---------------------------------------------------------

(defn- direct?
  "Is this a mapped (off-heap) buffer?  The question the residency split turns on, asked
  of the object rather than of the section it came from."
  [x]
  (and (instance? Buffer x) (.isDirect ^Buffer x)))

(defn- handle?
  "Is this a **handle** — a way out of the object graph and into the JVM — rather than a
  structure?

  The hazard functions are, in another flavour, and the one that actually took this bench
  down.  Every route below ends the same way: at a `java.lang.ref.Reference` whose
  `ReferenceQueue` holds a JDK **thread** for as long as that thread is parked on it, and
  from a thread the walk reaches a classloader and then the process.  It dies on
  `SecureClassLoader$CodeSourceKey`, a *record* class jol cannot take a field offset on.

  Two roads reach it, and this bench walked both:

  * a **file handle** — `DiskKvBackend`'s `log` under the `:disk-log` index, `Kind`'s
    under the durable records — holds a `FileDescriptor`, which hangs a `FileCleanable`
    on the queue;
  * a **mapped buffer** — every section the columnar image maps — carries a `Cleaner` on
    its `att`, and a `Cleaner` is a `PhantomReference` on the same queue.

  **Nondeterministically** down both, which is what made it a bench that failed on some
  runs and lied on the rest: a queue holds a waiter only while its thread is parked, so
  the same `:disk-log` index measured twice reported 9.4 MB once and threw the next.
  Neither number was the index's — 1.5 MB of the surviving one was JDK internals reached
  through the descriptor.

  Nothing named here is heap this KB holds.  A handle is a descriptor and an offset; a
  mapped buffer's pages are the OS's and are counted from its capacity under *mapped* by
  `split`, which classifies the section objects before this ever sees them; a reference's
  referent is by definition not retained."
  [x]
  (or (instance? java.io.RandomAccessFile x)
      (instance? java.io.FileDescriptor x)
      (instance? java.nio.channels.FileChannel x)
      (direct? x)
      (instance? java.lang.ref.Reference x)
      (instance? java.lang.ref.ReferenceQueue x)
      (instance? Thread x)
      (instance? ClassLoader x)))

(def ^:private store-fields
  "How many entries a map may hold and still be read as a store's **own fields** rather
  than as its contents.  `unhandled` descends through the first looking for a handle to
  drop and never through the second: a `DiskRecordStore`'s three `:kinds` and a
  `DiskKvBackend`'s nine slots are small and are where the handles sit; a term index is
  neither, and scanning one for a file handle would cost more than the measurement it
  protects."
  64)

(def ^:private store-depth
  "How deep that descent goes.  Three levels reach every handle a KB holds — the store,
  its per-kind map, that kind's fields — and the fourth is slack.  A bound rather than a
  visited set because the point is to stay cheap: a KB field that closes a cycle back
  onto the KB would otherwise spin, and a handle four levels down is a store shape this
  bench has not met."
  4)

(defn- cell?
  "Is this a **reference cell** — an atom, a ref, an agent, a volatile — whose `deref`
  hands back the value it is holding?

  `IDeref` is the wrong question and asking it cost this bench its largest row.
  `DenseTms` is `IDeref`, and its `deref` **materializes a snapshot**
  (`dense_jtms/snapshot`): rooted on that, the jtms row measured a reference-shaped copy
  built by the measurement itself — 17.8 MB against the 2.5 MB the dense structure
  occupies, at 15,391 nodes / 18,242 justifications, and 1,214 B/node against
  `docs/density.md`'s 18 B/node + 166 B/justification.  A residency bench reporting bytes
  its own walk allocated is the one reading it cannot be allowed to take."
  [x]
  (or (instance? clojure.lang.IRef x)          ; atom, ref, agent
      (instance? clojure.lang.Volatile x)))

(defn- type-vals
  "The field values of a Clojure `deftype` or `defrecord` instance, read reflectively.

  `map?` is not enough, and the gap between them is where the walk kept escaping.
  `ColumnarIndexStore` is a record and answers `vals`; the `Trie` and `DenseRoots` it
  holds are **deftypes**, which are not maps and answer nothing — so the mapped buffers
  in their `mleaf-off`, `mhandles`, `mkeys` and `moff` sat one field below anything the
  pruner could see, and the walk went through them into the cleaner's queue.  These are
  our own classes in the unnamed module, so reading a declared field needs no
  `--add-opens`."
  [x]
  (let [^Class c (class x)]
    (keep (fn [^java.lang.reflect.Field f]
            (when (and (not (java.lang.reflect.Modifier/isStatic (.getModifiers f)))
                       (not (.isPrimitive (.getType f))))
              (.setAccessible f true)
              (.get f x)))
          (.getDeclaredFields c))))

(defn- store-vals
  "The values `unhandled` descends through: a reference cell's value, the fields of one
  of our own types, and a small map's values — functions dropped, since a function is
  opaque to `vals` anyway and walking one is the hazard `data-roots` names.

  A map is descended only while it is small enough to read as a store's **own fields**
  rather than as its contents (`store-fields`); a type is descended whatever its arity,
  because a `deftype`'s fields are its shape and there are never many."
  [x]
  (cond (cell? x)                                      [(deref x)]
        (or (instance? clojure.lang.IRecord x)
            (instance? clojure.lang.IType x))          (remove fn? (type-vals x))
        (and (map? x) (<= (count x) (long store-fields))) (remove fn? (vals x))
        :else                                          nil))

(defn- reaches-handle?
  "Does a file handle sit within `depth` store levels of `x`?"
  [x ^long depth]
  (or (handle? x)
      (and (pos? depth)
           (boolean (some #(reaches-handle? % (dec depth)) (store-vals x))))))

(defn- unhandled
  "`[x]`, or — when a file handle sits within it — the fields of `x` that are not the
  handle, so jol is handed the structure and never the descriptor.

  Expanding a record into its fields loses that record's own header, tens of bytes
  against the megabytes the walk would otherwise attribute to the JDK.  **Idempotent**:
  what comes back reaches no handle, so `cumulative`'s accumulating root set can be
  pruned again on every row without descending a level further each time."
  ([x] (unhandled x store-depth))
  ([x ^long depth]
   (if-not (reaches-handle? x depth)
     [x]
     (when (pos? depth)
       (mapcat #(unhandled % (dec depth)) (remove handle? (store-vals x)))))))

(defn- retained
  "Retained heap of the graph rooted at `objs`, nils and file handles dropped.  jol dedupes
  shared structure *within* one call, so a split that wants to avoid double-counting
  measures the shared root once and subtracts it, the way `bench-residency` does the
  dictionary."
  ^long [objs]
  (let [objs (into [] (comp (remove nil?) (mapcat unhandled)) objs)]
    (if (seq objs) (postings/retained objs) 0)))

(defn- buffer-bytes
  "A buffer's payload in bytes — its capacity times its element width.  Only meaningful
  for a *mapped* buffer, where the bytes are the file's rather than the heap's; a heap
  buffer's cost is what `retained` already counts."
  ^long [x]
  (let [^Buffer b x
        cap (long (.capacity b))]
    (* cap (cond (instance? LongBuffer b)   8
                 (instance? DoubleBuffer b) 8
                 (instance? IntBuffer b)    4
                 (instance? FloatBuffer b)  4
                 (instance? ShortBuffer b)  2
                 (instance? ByteBuffer b)   1
                 :else                      1))))

(defn- split
  "`{:heap n :mapped n}` for a bag of section objects: a direct buffer is mapped and its
  payload counted from its capacity, everything else is heap and measured by jol in one
  call so shared structure is deduped once."
  [objs]
  (let [objs   (remove nil? objs)
        {mapd true heap false} (group-by direct? objs)]
    {:heap   (retained heap)
     :mapped (reduce + 0 (map buffer-bytes mapd))}))

;; ---- the structures a KB holds ------------------------------------------

(defn- index-sections
  "The index store's resident structures, by section.  Every backend answers the two
  totals; the columnar one additionally answers the sections
  `index_snapshot.clj`'s residency split names, because *which* of them tracks the extent
  is the question the paged-index fork is waiting on.

  The token dictionary is measured once and subtracted from the sections over it: it is
  shared by the trie and the roots, and jol counts shared structure under whichever root
  reaches it first."
  [kb]
  (let [idx (:index kb)]
    (if-not (col/columnar? idx)
      {:whole (split [idx])}
      (let [dict     (retained [(:dict idx)])
            csr      (snapshot-types/snapshot-read (:trie idx) nil)
            skeleton (when csr [(:counts csr) (:offsets csr) (:edge-tok csr) (:edge-tgt csr)])
            leaves   (when csr [(:leaf-off csr) (:handles csr)])
            rsec     (dense-roots-types/sections (:roots idx))
            columns  [(:keys rsec) (:offsets rsec)]
            handles  [(:handles rsec)]
            ;; the routed map is what the roots hold when nothing is mapped; the scope
            ;; table and the fallback are what they hold either way
            routed   [(:routed rsec)]
            argfam   [(:argfam rsec)]
            fallback [(:fallback rsec)]]
        {:whole          (split [idx])
         :dictionary     {:heap dict :mapped 0}
         :csr-skeleton   (split skeleton)
         :csr-leaves     (split leaves)
         :roots-columns  (split columns)
         :roots-handles  (split handles)
         :roots-routed   (update (split routed) :heap #(max 0 (- ^long % dict)))
         :roots-argfam   (split argfam)
         :roots-fallback (split fallback)}))))

(defn- kind-objs [records k]
  (when-let [kinds (:kinds records)]
    (keep #(get % k) (vals kinds))))

(def ^:private other-fields
  "The KB fields that are none of the four big structures — the caches, rosters, memos and
  statistics a KB carries beside its two stores, its network and its taxonomy, on the
  `KB` record and on its `Reasoning` value.  Named exhaustively rather than derived by subtraction: jol dedupes shared
  structure *within* a call, so `retained [kb]` is strictly less than the sum of its
  parts, and a remainder taken against it goes negative the moment two rows legitimately
  share anything.  A row here can still be reached from another root — the attribution is
  to whichever this file measures first — which is what the reconciliation line under the
  table is for.

  **`:provers`, `:solver` and `:feed` are excluded, and they are the interesting
  omission.**  Each holds *functions* — a prover registry, the solver, the change feed's
  listeners — and jol walking a Clojure fn reaches its class, its classloader, and from
  there most of the JVM; the walk fails outright on a JDK record inside
  `SecureClassLoader`.  Nothing is lost by leaving them out: a prover registry is a fixed
  handful of vars and a feed's listeners are the caller's objects, so neither grows with
  the corpus, which is the only property this table is about."
  [:conflicts :program :violations :contradictions :recheck :refused
   :settle-stats :chain-stats :opposed :excepted :negations :clashes :supersessions
   :reports :qcn :qcn-joined :matches :closures :naming :constraints :rule-antecedents
   :rule-contexts :unrecovered])

(defn- data-roots
  "The measurable **data** under `x`: a reference cell's value rather than the cell itself
  (so the watches on it are not walked), with any function dropped.  A cell, never an
  `IDeref` — see `cell?` for what that distinction is worth.

  Functions are the hazard this whole file routes around.  A Clojure fn reaches its
  class, its classloader and from there most of the JVM — the walk dies outright on a JDK
  record inside `SecureClassLoader`, and where it survives it reports the process rather
  than the structure.  Three KB fields hold one: `:provers` and `:solver` by their nature,
  and the **taxonomy**, whose `:supporter-filter-active?` / `:supporter-visible?` are
  `install-supporter-visibility!`'s callbacks and close over the KB itself.  Rooted
  naively, an 845-fact taxonomy measured as the entire KB and every other row fell to
  zero behind it.

  File handles are the same hazard by another road and are dropped the same way, by
  `unhandled` — see `handle?` for which road."
  [x]
  (let [v (if (cell? x) (deref x) x)]
    (cond (nil? v) nil
          (fn? v)  nil
          (map? v) (mapcat unhandled (remove fn? (vals v)))
          :else    (unhandled v))))

(defn- cumulative
  "`ordered` is `[[label roots] …]`; each row is measured as an **increment** — what its
  own roots add that every row before it does not already hold — so the rows sum to the
  KB's retained heap exactly instead of double-counting what two of them share.

  Rooting each structure on its own does not work here and the failure is not subtle: a
  845-fact KB measured that way reported 4.9 MB of index and 5.7 MB of taxonomy against a
  whole KB of 5.7 MB, because both walks reach the shipped core vocabulary and jol counts
  it under whichever root it started from.  A budget whose rows sum to 2.2x the truth is
  not a budget.

  **The order therefore decides who owns anything shared, and the index is measured
  last.**  Its row is then what paging the index would actually release — never the
  shared vocabulary that would still be resident afterwards — which is the conservative
  reading of the one question the paged-index prompts exist to answer.  Measuring it
  first would hand it every byte it merely touches and flatter exactly the conclusion
  this bench is being used to reach."
  [ordered]
  (loop [rows [], seen [], [[label roots] & more] ordered]
    (if-not label
      {:rows rows :whole {:heap (retained seen) :mapped 0}}
      (let [roots  (mapcat data-roots (remove nil? roots))
            {mapd true heap false} (group-by direct? roots)
            before (retained seen)
            seen'  (into seen heap)
            after  (retained seen')]
        (recur (conj rows [label {:heap   (max 0 (- after before))
                                  :mapped (reduce + 0 (map buffer-bytes mapd))}])
               seen' more)))))

(defn- kb-structures
  "Every resident structure of `kb`, as `{row {:heap n :mapped n}}`, plus `:whole` — the
  KB's own retained heap — so the table can say how far the rows and the whole disagree
  rather than leaving a reader to assume they do not."
  [kb]
  (let [records  (:records kb)
        idx      (index-sections kb)
        ;; A field that reaches code rather than data kills the walk (see
        ;; `other-fields`), so a new one is reported as unmeasured instead of taking the
        ;; run down — a bench that dies on the last row has measured nothing.
        ;; the roster object itself — `vaelii.impl.roster`'s `LiveRoster`, whose retained
        ;; size is the bitmap it wraps
        roster-o (kind-objs records :live-ids)
        cache-o  (kind-objs records :cache)
        ;; `premises` is a `DiskRecordStore` field, not a per-`Kind` one — the derived
        ;; set of sentex handles with a non-nil `:strength`, one boxed `Long` per premise
        ;; until it is converted the way `roster-o` already was.
        premises-o [(:premises records)]
        ;; A field that reaches code rather than data kills the walk (see
        ;; `other-fields`), so a new one is reported as unmeasured instead of taking the
        ;; run down — a bench that dies on the last row has measured nothing.
        other-o  (try (doall (map #(get (merge (into {} kb) (into {} (reasoning/of kb))) %)
                                  other-fields))
                      (catch Throwable t
                        (println (format "    (other: not measured — %s)" (.getMessage t)))
                        nil))]
    (merge {:index    (:whole idx)
            :sections (dissoc idx :whole)}
           (cumulative [[:taxonomy       [(reasoning/taxonomy kb)]]
                        [:jtms           [(reasoning/tms kb)]]
                        [:record-rosters roster-o]
                        [:record-cache   cache-o]
                        [:record-premises premises-o]
                        [:record-other   [records]]
                        [:other          other-o]
                        [:index          [(:index kb)]]]))))

;; ---- the corpus ----------------------------------------------------------

(def ^:private predicates
  "The generator's binary-predicate count, fixed so the vocabulary is identical at every
  N."
  30)

(def ^:private layers
  "The generator's predicate stratification.  Named here because it decides the **base
  band** — `generate/bands` puts facts on band 0 alone, `(quot predicates layers)`
  of them — and the rules below have to be stated over the predicates that actually
  carry facts, or they never fire."
  3)

(def ^:private base-band
  "The predicates the generated facts land on: `genRel0` … `genRel<base-1>`
  (`generate/pred-name`, `generate/bands`)."
  (mapv #(symbol (str "genRel" %)) (range (max 1 (quot predicates (max 2 layers))))))

(defn- rule-families
  "The forward rules that drive j/n to `target`.  A **family** is one rule per base
  predicate, all concluding into one collapsed head — so a family adds a justification
  per existing fact and only `individuals` new nodes, and `k` whole families plus a
  fractional one reaches j/n ≈ k + fraction.

  The head is `(derives<i> ?x ?x)` rather than `(derives<i> ?x ?y)` deliberately: a head
  that keeps both variables mints a conclusion per fact, which pins the ratio at 0.5 (one
  justification per new node) however many families are stated.  Collapsing it is what
  makes the ratio a knob.  Returns a seq of `[antecedent consequent]` pairs."
  [target]
  (let [whole (long target)
        frac  (- (double target) whole)
        fam   (fn [i preds]
                (for [pred preds]
                  [(list pred '?x '?y)
                   (list (symbol (str "derives" i)) '?x '?x)]))]
    (concat (mapcat #(fam % base-band) (range whole))
            (when (pos? frac)
              (fam whole (take (long (Math/round (* frac (count base-band)))) base-band))))))

(defn- load!
  "A vocabulary-fixed corpus of `facts` over `individuals`, then the rules that drive the
  justification ratio, chained to a fixpoint.  Returns the KB."
  [kb facts individuals j-n]
  (v/clear! kb)
  (gen/load-into kb {:facts facts :rules 0 :individuals individuals
                     :types 40 :predicates predicates :layers layers :chain? false})
  (when (pos? (double j-n))
    (doseq [[ante conseq] (rule-families j-n)]
      (v/assert-rule kb [ante] conseq 'CxGenerated {:direction :forward}))
    (v/forward-chain kb))
  kb)

(defn- open-kb-for [backend dir recover?]
  (v/open-kb {:backend backend :dir dir :recover? recover?}))

(defn- tmpdir ^String []
  (str (java.nio.file.Files/createTempDirectory
        "vaelii-budget-" (into-array java.nio.file.attribute.FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (java.io.File. dir)))] (.delete ^java.io.File f)))

(defn- measure
  "Load `facts` onto `backend`, close, **reopen**, and size everything the reopened KB
  holds.

  Reopened rather than freshly built, because that is the state a running KB is in and
  the only state in which the columnar image exists at all: the close is what writes it,
  and `:recover? :auto` is what maps it back (`bench-residency` takes the same two
  opens for the same reason).  `:disk-log` reopens its durable index populated, so the
  two backends are compared in the same phase of their own lifecycle.

  Every posting is touched once before measuring, so a mapped index is read warm rather
  than as one nothing has looked at.  `:nodes` and `:justs` come off the TMS, so the
  achieved j/n is a measurement rather than the argument that asked for it."
  [backend facts individuals j-n]
  (let [dir (tmpdir)]
    (try
      (load! (open-kb-for backend dir false) facts individuals j-n)
      (disk/close-dir! dir)
      (let [kb    (open-kb-for backend dir :auto)
            _     (dorun (v/sentexes-matching kb '(?p ?x ?y) 'CxGenerated))
            n     (p/sentex-tally (:records kb))
            nodes (count (jtms/datums (reasoning/tms kb)))
            ;; a count, never a size: the dense network stores no justification object
            ;; and rebuilds one per call, so this allocates O(j) temporaries and
            ;; `bench-jtms`' warning applies to sizing what it returns, not to counting it
            justs (count (jtms/justifications (reasoning/tms kb)))]
        (assoc (kb-structures kb)
               :facts n :requested facts :nodes nodes :justs justs
               :j-n (if (pos? nodes) (/ (double justs) nodes) 0.0)))
      (finally (disk/close-dir! dir) (rm-rf! dir)))))

;; ---- the report ----------------------------------------------------------

(defn- mb ^double [b] (/ (double b) 1048576.0))
(defn- gb ^double [b] (/ (double b) 1073741824.0))

(defn- fmt-bytes
  "Bytes at three scales, because the rows now span nine orders of magnitude: the index
  reads in GB and a compressed roster reads in KB, and a row printed as `0.0 MB` is one a
  reader cannot check the shape verdict against — the verdict is computed on the raw
  bytes either way, so the print floor would hide the growth rather than deny it."
  [b]
  (let [x (double b)]
    (cond
      (>= x 1073741824.0) (format "%.2f GB" (gb x))
      (>= x 1048576.0)    (format "%.1f MB" (mb x))
      :else               (format "%.1f KB" (/ x 1024.0)))))

(def ^:private row-order
  "Printed — and **measured** — in this order; see `cumulative` for why the index is
  last."
  [:taxonomy :jtms :record-rosters :record-cache :record-premises :record-other :other :index])

(def ^:private row-labels
  {:index          "index store (what paging it would release)"
   :jtms           "jtms (dense)"
   :record-rosters "record rosters"
   :record-cache   "record cache (bounded)"
   :record-premises "record premises (boxed set)"
   :record-other   "record store, rest"
   :taxonomy       "taxonomy"
   :other          "other (naming, match, feed, qcn)"})

(def ^:private section-order
  "The image's resident sections, in the order the table reads them.  Named once and used
  by both the per-size table and the per-section verdict, so a section cannot be measured
  and then silently dropped from the report — `:roots-handles` was."
  [:dictionary :csr-skeleton :csr-leaves :roots-columns :roots-handles
   :roots-routed :roots-argfam :roots-fallback])

(def ^:private section-labels
  {:dictionary     "token dictionary"
   :csr-skeleton   "CSR skeleton"
   :csr-leaves     "CSR leaves"
   :roots-columns  "roots key + offset columns"
   :roots-handles  "roots handle column"
   :roots-routed   "roots routed map"
   :roots-argfam   "argument-root scope table"
   :roots-fallback "roots fallback blob  <- term + slot rosters"})

(def ^:private growth-tolerance
  "How far a structure's growth may sit from the fact ratio and still be called linear.
  Wide, deliberately: the question this gates is *\"does this row track the extent?\"*,
  and a row that grows 1.8× where the facts grew 2× is linear enough to extrapolate and
  say so.  A row that grows 1.2× is not tracking the extent at all, which is the answer
  rather than a failure.  Applied to **each** step, so a row buys its shape three times."
  0.25)

(def ^:private capped-rows
  "Rows whose ceiling is a **configured constant**, and which are therefore read rather
  than fitted.

  The hot-record cache is an LRU of `vaelii.disk.cache` records per kind
  (`config/disk-cache-capacity`, default 65,536).  Below that count it fills one-for-one
  with the extent and a fit calls it linear; above it, it does not move.  Sampled across
  the cap it reads as linear anyway, and the row that cannot exceed tens of megabytes was
  multiplied out to **39.15 GB** at 100M — 12% of a total, entirely invented.  A constant
  is not something to infer from samples, so the cap is read from the config it lives in,
  and a run whose sizes never reach it refuses the row instead of guessing past it."
  {:record-cache config/disk-cache-capacity})

(defn- ratio ^double [a b] (/ (double b) (max 1.0 (double a))))

(defn- capped-estimate
  "`[bytes note]` for a row bounded by `cap` records per kind, read off the largest
  sample — but only once that sample has saturated the cache, which takes **both** the
  sentexes and the justifications past it, since each kind holds its own LRU."
  [cap {:keys [facts justs]} bytes]
  (let [cap (long cap)]
    (cond
      (zero? cap)
      [0 "cache disabled (vaelii.disk.cache=0)"]
      (>= (min (long facts) (long justs)) cap)
      [bytes (format "capped at %,d records/kind" cap)]
      :else
      [nil (format "cap %,d records/kind not reached — largest sample holds %,d sentexes, %,d justifications"
                   cap facts justs)])))

(defn- extrapolate
  "`[bytes note]` for one row at `target` facts, from N `[facts bytes]` samples (N ≥ 3,
  ascending), or `[nil why]` when no shape fits.

  More than two points, so the shape is **checked** rather than assumed.  Two samples
  always name a straight line; they cannot say whether the row is on one.  A row is
  linear here only when *every* consecutive step's growth matches that step's own fact
  ratio, flat only when every step is flat, and affine only when a fit through the outer
  two samples predicts *every* sample in between — each point held back from the fit is
  what makes it a test, and N-2 of them is a stronger test than one.

  Affine is the form the old two-point gate had no name for and dropped: a fixed
  baseline plus a per-fact part reads as neither flat nor linear, and `record store, rest`
  sat in that gap at 1.65× against facts at 2.75×."
  [pts target]
  (let [tol     (double growth-tolerance)
        near?   (fn [a b] (<= (Math/abs (- (double a) (double b))) (* tol (double b))))
        steps   (partition 2 1 pts)
        f-rats  (mapv (fn [[[f1 _] [f2 _]]] (ratio f1 f2)) steps)
        y-rats  (mapv (fn [[[_ y1] [_ y2]]] (ratio y1 y2)) steps)
        [f1 y1]   (first pts)
        [flast ylast] (peek pts)]
    (cond
      (zero? (long ylast))
      [0 "empty"]

      (every? true? (map near? y-rats f-rats))
      [(long (* (double ylast) (ratio flast target))) (format "linear, all %d steps" (count steps))]

      (every? #(near? % 1.0) y-rats)
      [(long ylast) "flat in the extent"]

      :else
      (let [b    (/ (- (double ylast) (double y1)) (max 1.0 (- (double flast) (double f1))))
            a    (- (double y1) (* b (double f1)))
            at   (+ a (* b (double target)))
            held (subvec pts 1 (dec (count pts)))]
        (if (and (pos? b) (pos? at) (every? (fn [[f y]] (near? (+ a (* b (double f))) y)) held))
          [(long at) (format "affine, %s + %.0f B/fact" (fmt-bytes (max 0.0 a)) b)]
          [nil (format "growth %s against facts %s"
                       (str/join "x then " (map #(format "%.2f" %) y-rats))
                       (str/join "x then " (map #(format "%.2f" %) f-rats)))])))))

(defn- print-header [{:keys [facts requested nodes justs j-n]} backends]
  ;; requested beside stored, because the Zipf draw behind the corpus dedups and the
  ;; shortfall is otherwise invisible — the fact ratios below are the stored ones
  (println (format "\n  N = %,d facts / %,d nodes / %,d justifications / j-n %.2f   (%,d ground facts asked for)"
                   facts nodes justs j-n requested))
  (println (format "    %-38s %s" "" (str/join "  " (map #(format "%14s" (name %)) backends)))))

(defn- print-rows [by-backend backends]
  (doseq [k row-order]
    (println (format "    %-38s %s" (row-labels k)
                     (str/join "  " (for [b backends]
                                      (format "%14s" (fmt-bytes (:heap (get-in by-backend [b :heap-rows k])))))))))
  (println (format "    %-38s %s" "  ── mapped (not heap)"
                   (str/join "  " (for [b backends]
                                    (format "%14s" (fmt-bytes (get-in by-backend [b :mapped-total])))))))
  ;; The rows are measured from their own roots, so anything two of them share is counted
  ;; twice; the KB's own retained heap counts it once.  The gap between them is that
  ;; sharing, and it is printed rather than reconciled away — a row read as a *share* of
  ;; the total is only as good as this line is small.
  (println (format "    %-38s %s" "  sum of rows"
                   (str/join "  " (for [b backends]
                                    (format "%14s" (fmt-bytes (reduce + 0 (map (comp :heap second)
                                                                               (:rows (get by-backend b))))))))))
  ;; A self-check rather than a reconciliation: the rows ARE increments over one
  ;; accumulating walk, so these agree by construction and a disagreement means a walk
  ;; failed rather than that a structure was missed.
  (println (format "    %-38s %s" "  the accumulated walk (self-check)"
                   (str/join "  " (for [b backends]
                                    (format "%14s" (fmt-bytes (:heap (:whole (get by-backend b))))))))))

(defn- print-sections [by-backend backends]
  (when (some #(seq (get-in by-backend [% :sections])) backends)
    (println "\n    the index store's sections (heap unless marked mapped):")
    (doseq [k section-order]
      (println (format "    %-38s %s" (str "      " (section-labels k))
                       (str/join "  " (for [b backends]
                                        (let [s (get-in by-backend [b :sections k])]
                                          (format "%14s"
                                                  (cond (nil? s) "—"
                                                        (pos? (long (:mapped s))) (str (fmt-bytes (:mapped s)) " map")
                                                        :else (fmt-bytes (:heap s))))))))))))

(defn- heap-rows [m] (into {} (:rows m)))

(defn- run [facts step individuals j-n target budget-gb backends]
  (let [prep    (fn [m] (into {} (for [[b v] m]
                                   [b (assoc v :heap-rows (heap-rows v)
                                             :mapped-total (reduce + 0 (map (comp :mapped second) (:rows v))))])))
        by-size (mapv (fn [n] (prep (into {} (for [b backends] [b (measure b n individuals j-n)]))))
                      [facts (* facts step) (* facts step step) (* facts step step step)])
        any     (first backends)]
    (println (format "\n══ the residency budget, %s ══"
                     (str/join " · " (map name backends))))
    (doseq [size by-size]
      (print-header (get size any) backends)
      (print-rows size backends)
      (print-sections size backends))

    (println (format "\n  ── extrapolated to %,d facts, against %d GB ──" target budget-gb))
    (doseq [b backends]
      (let [per    (mapv #(get % b) by-size)
            newest (peek per)]
        (println (format "\n    %s" (name b)))
        (let [totals
              (for [k row-order]
                (let [pts       (mapv (fn [m] [(:facts m) (long (:heap (get-in m [:heap-rows k])))]) per)
                      [ext why] (if-let [cap (get capped-rows k)]
                                  (capped-estimate (cap) newest (second (peek pts)))
                                  (extrapolate pts target))]
                  (println (format "      %-36s %s  %s"
                                   (row-labels k)
                                   (str/join " -> " (map #(format "%9s" (fmt-bytes (second %))) pts))
                                   (if ext (str (fmt-bytes ext) "  (" why ")")
                                       (str "NOT EXTRAPOLATED — " why))))
                  ext))
              known (reduce + 0 (remove nil? totals))
              gaps  (count (filter nil? totals))]
          (println (format "      %-36s %33s %s"
                           "TOTAL (extrapolated rows only)" "" (fmt-bytes known)))
          (println (format "      %-36s %33s %s"
                           (format "against %d GB" budget-gb) ""
                           (let [x (/ (gb known) (double budget-gb))]
                             (format "%s %.2fx%s"
                                     (if (<= x 1.0) "OK" "OVER") x
                                     (if (pos? gaps)
                                       (format "  (+%d row%s not extrapolated — a floor, not a total)"
                                               gaps (if (= 1 gaps) "" "s"))
                                       ""))))))
        ;; The index row above is one number over an image whose sections do not share a
        ;; shape: the CSR skeleton is path-scaled, the dictionary and the roots' key
        ;; columns are vocabulary-bounded, the scope table is bounded by predicates ×
        ;; arities, and the handle column is where the facts are.  Aggregated, a
        ;; fact-scaled section hides inside a mostly-bounded average — so each one gets
        ;; its own shape, and *that* is the answer to "is the image fact-independent?"
        ;;
        ;; A DECOMPOSITION of the index row, never an addition to it: these bytes are
        ;; already counted above, and summing them into the total would double them.
        (when (seq (:sections newest))
          (println (format "\n      %s" "the image's sections — a decomposition of the index row, not an addition to it"))
          (doseq [k section-order
                  :let [sec (get-in newest [:sections k])]
                  :when sec]
            (let [mapped?   (pos? (long (:mapped sec)))
                  bytes-of  (fn [m] (let [x (get-in m [:sections k])
                                          d (long (:mapped x))]
                                      (if (pos? d) d (long (:heap x)))))
                  pts       (mapv (fn [m] [(:facts m) (bytes-of m)]) per)
                  [ext why] (extrapolate pts target)]
              (println (format "        %-36s %s  %s"
                               (str (section-labels k) (when mapped? "  [mapped]"))
                               (str/join " -> " (map #(format "%9s" (fmt-bytes (second %))) pts))
                               (if ext (str (fmt-bytes ext) "  (" why ")")
                                   (str "NOT EXTRAPOLATED — " why))))))))))
  (println (str "\n  Read the four sizes across, then the shape.  A row that tracks the\n"
                "  vocabulary is flat; one that tracks the extent is linear; one with a fixed\n"
                "  baseline over it is affine; one bounded by config is read off its cap.  Each\n"
                "  shape is confirmed on every step, and a row that fits none is refused rather\n"
                "  than multiplied out.\n\n"
                "  The total is a FLOOR even when no row is refused.  The corpus pins the\n"
                "  vocabulary, so every flat row is carried to the target at the value a small\n"
                "  vocabulary gave it — and a KB of that many facts does not have this one.\n"
                "  What is priced here is the extent, not a KB of the target size.")))

(defn -main [& args]
  (let [facts       (Long/parseLong (or (first args) "60000"))
        ;; the per-step multiple now, applied three times: four sizes, geometric
        step        (Long/parseLong (or (second args) "2"))
        ;; wide enough that the Zipf draw behind the corpus mostly stops colliding —
        ;; 400 individuals stored 40% of a 240,000-fact request, 8,000 stores 78%
        individuals (Long/parseLong (or (nth args 2 nil) "8000"))
        target      (Long/parseLong (or (nth args 3 nil) "100000000"))
        budget-gb   (Long/parseLong (or (nth args 4 nil) "40"))]
    (doseq [j-n [0.5 1.1]]
      (println (format "\n\n════ j/n target %.1f ════" j-n))
      (run facts step individuals j-n target budget-gb [:disk-log :disk-snapshot]))
    (println (str "\n  :pg-disk-log is not measured here: the Postgres records live in the\n"
                  "  com.vaelii/postgres adapter, which the engine does not depend on, so this\n"
                  "  process cannot open one.  Its index and JTMS rows are :disk-log's by\n"
                  "  construction (same stores, different records); its record rows are the\n"
                  "  adapter's and belong in the adapter's own bench."))
    (shutdown-agents)
    (System/exit 0)))
