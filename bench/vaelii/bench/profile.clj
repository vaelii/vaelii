;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.profile
  "What shape of question a KB is asked, and what its index does with each shape —
  `vaelii.impl.profile` read out over a whole corpus.

  Six readings, and they answer different questions:

  * **The corpus shape** is static and needs no workload: arity, where the nesting sits,
    and how the token dictionary scales against the vocabulary.  It says what the index
    *holds*.
  * **The load and chain arms** are the engine's own traffic.  Every antecedent a rule
    matches on is a goal somebody really asked, so a forward-chaining run over a corpus's
    own rules is a workload rather than a guess about one.
  * **The ask arm** proves each rule's own consequent two deep.  A rule's consequent is
    the question the rule exists to answer, so the set is a workload the KB declared for
    itself.
  * **The interactive arm** is the one an engine profile forgets.  Every arm above is
    reasoning, and no reasoning calls `terms`, `find-terms` or `find-sentexes` — so
    without this one the term roster and the term index read zero, which reads as a
    family nobody uses and means a family no *reasoner* uses.
  * **The churn arm** retracts a sample and puts it back, which is the only way
    `unindex-sentex!` runs at all.  It prices the retraction tax, which is not the assert
    tax with a sign on it: how many trie nodes a removal kills depends on what else
    shares the prefix.  Two samples, because a taxonomy edge's churn is a closure
    reconcile and an ontology is a fifth taxonomy edges — the index path is what the
    tallies are of, and the edges are a ms/pair line beside them.
  * **The balanced probe** is a guess on purpose, and is labelled as one.  It asks every
    binding pattern equally often, which no real workload does, because its question is
    not *which shapes arrive* but *what each shape costs when it does*.  Frequency comes
    from the arms above; cost comes from here.

  Run:

      lein bench-profile                        the shipped starter
      lein bench-profile generated [facts] [rules]
      lein bench-profile corpus <dir> [profile] a converted corpus (`:cyc-corpus`)

  A corpus run wants a heap, and `:bench` pins `-Xmx6g`.  An environment `JVM_OPTS` is
  placed before the project's own options and loses to it silently, so edit the vector on
  the way past — `with-profile` first, `update-in` second, as `scripts/run-bench-caches.sh`
  documents:

      lein with-profile +bench,+with-foreign update-in :jvm-opts conj '\"-Xmx32g\"' -- \\
        run -m vaelii.bench.profile corpus <dir>"
  (:require [vaelii.bench.util :as u]
            [vaelii.core :as v]
            [vaelii.impl.foreign :as foreign]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.starter :as starter]))

(defn- ms [t0] (/ (- (System/nanoTime) t0) 1e6))

(defn- banner [s]
  (println)
  (println (str "── " s " " (apply str (repeat (max 0 (- 76 (count s))) "─")))))

(defn- pct ^double [n total] (* 100.0 (/ (double n) (double (max 1 total)))))

;; ---- the corpus shape (static; no workload) ------------------------------

(defn- form-depth
  "Nesting depth of one literal: 1 for a flat `(p a b)`, 2 when an argument is itself a
  compound.  A bare symbol is 0."
  ^long [x]
  (if (sequential? x) (inc (long (reduce max 0 (map form-depth x)))) 0))

(defn- literals-of
  "`[where literal …]` for one record: where the literal sits decides whether the
  structural trie can see inside it at all.  A positive fact's arguments are linearized
  into the trie key; a `:false` body is one whole token, and a rule literal is not in the
  trie."
  [sx]
  (if (some? (:antecedent sx))
    (map (fn [l] [:rule l]) (cons (:consequent sx) (:antecedent sx)))
    (let [b (sx/body sx)]
      [[(if (= :false (:truth sx)) :negative :fact) b]])))

(defn- shape-tally [tally sx]
  (let [rule? (some? (:antecedent sx))
        base  (-> tally
                  (update (if rule? :rules :facts) inc)
                  (cond-> (and (not rule?) (= :false (:truth sx))) (update :negatives inc)))
        base  (if rule?
                base
                (let [b (sx/body sx)]
                  (if (and (sequential? b) (seq b))
                    (-> base
                        (update-in [:arity (dec (count b))] (fnil inc 0))
                        (update :preds conj (first b))
                        (update :args into (filter symbol? (rest b))))
                    base)))]
    (reduce (fn [t [where l]]
              (let [d (dec (form-depth l))]
                (cond-> (update-in t [:nesting where (min d 3)] (fnil inc 0))
                  (pos? d) (update-in [:nested where] (fnil inc 0)))))
            (update base :contexts conj (:context sx))
            (literals-of sx))))

(def ^:private empty-shape
  {:facts 0 :rules 0 :negatives 0 :arity {} :nesting {} :nested {}
   :preds #{} :args #{} :contexts #{}})

(defn- exact-floor-0
  "How many distinct term-index keys `sentex/*min-indexed-depth*` 0 would mint, computed
  by holding the whole key set.  Refused above `cap` records, where the set is the
  measurement's own memory problem; the caller reports the upper bound instead."
  [kb ids ^long cap]
  (when (<= (count ids) cap)
    (binding [sx/*min-indexed-depth* 0]
      (count (into #{} (mapcat (fn [id] (when-let [s (p/get-sentex (:records kb) id)]
                                          (sx/index-terms s))))
                   ids)))))

(defn corpus-shape
  "The static profile: what is stored, how deep it nests and where, and how the token
  dictionary scales.  Returns the tally and prints it."
  [kb]
  (banner "the corpus shape (static — no workload)")
  (let [t0    (System/nanoTime)
        ix    (:index kb)
        ids   (vec (p/sentex-ids (:records kb)))
        t     (reduce (fn [t id]
                        (if-let [s (p/get-sentex (:records kb) id)] (shape-tally t s) t))
                      empty-shape ids)
        {:keys [facts rules negatives arity nesting nested preds args contexts]} t
        total (+ (long facts) (long rules))
        ;; the token dictionary, exactly: every `[:term-index …]` key, against the roster
        ;; of symbols beside it.  One streaming pass over the index; nothing retained.
        term-keys (count (sequence (comp (map first) (filter #(= :term-index (first %))))
                                   (p/index-entries ix)))
        roster    (long (p/term-count ix))
        forms     (reduce + 0 (map long (mapcat vals (vals nesting))))
        floor0    (exact-floor-0 kb ids 200000)]
    (println (format "  %,d sentexes — %,d facts (%,d negative), %,d rules — read in %.0f ms"
                     total facts negatives rules (ms t0)))
    (println (format "  %,d distinct fact predicates | %,d distinct argument symbols | %,d contexts"
                     (count preds) (count args) (count contexts)))

    (println "\n  arity of a fact:")
    (doseq [[a n] (sort arity)]
      (println (format "    %d argument(s) %,10d  (%5.1f%%)" a n (pct n facts))))

    (println "\n  where the nesting is — the structural trie linearizes a positive fact's")
    (println "  arguments and nothing else, so only the first row is reachable by it:")
    (println (format "    %-12s %10s %10s %10s %10s   %s" "literal in" "flat" "1 deep" "2 deep" "3+ deep" "nested"))
    (doseq [where [:fact :negative :rule]
            :let [row (get nesting where {})
                  tot (reduce + 0 (vals row))]
            :when (pos? (long tot))]
      (println (format "    %-12s %,10d %,10d %,10d %,10d   %,d  (%.2f%%)"
                       (name where) (get row 0 0) (get row 1 0) (get row 2 0) (get row 3 0)
                       (get nested where 0) (pct (get nested where 0) tot))))
    (let [reach (get nested :fact 0)
          miss  (+ (long (get nested :negative 0)) (long (get nested :rule 0)))]
      (println (format "    → the structural index reaches %,d of the %,d nested literals (%.1f%%)"
                       reach (+ (long reach) miss) (pct reach (+ (long reach) miss)))))

    (println "\n  the token dictionary — is it bound by the vocabulary or by the corpus?")
    (println (format "    term-index keys                 %,10d" term-keys))
    (println (format "    of them symbols (the roster)    %,10d  (%.1f%%)" roster (pct roster term-keys)))
    (println (format "    so compound keys                %,10d  (%.1f%%)"
                     (- term-keys roster) (pct (- term-keys roster) term-keys)))
    (println (format "    keys per sentex                 %14.2f" (/ (double term-keys) (max 1 total))))
    (if floor0
      (println (format "    at *min-indexed-depth* 0        %,10d  (%.2f× the default, %.2f keys/sentex)"
                       floor0 (/ (double floor0) (max 1 term-keys)) (/ (double floor0) (max 1 total))))
      (println (format "    at *min-indexed-depth* 0        ≤ %,8d  (one more key per content literal at most; %,d literals)"
                       (+ term-keys forms) forms)))

    (println "\n  the leading-variable fan, per predicate: `count-children [pred]` is how many")
    (println "  distinct first arguments a `(pred ?x B)` trie walk would expand at level 1.")
    (println (format "    %-34s %12s %12s %10s" "predicate" "extent" "fan at arg1" "extent/fan"))
    (doseq [pd (take 15 (sort-by #(- (long (p/count-with-functor ix %))) (vec preds)))
            :let [ext (long (p/count-with-functor ix pd))
                  fan (long (p/count-children ix [pd]))]]
      (println (format "    %-34s %,12d %,12d %10.2f" pd ext fan (/ (double ext) (max 1 fan)))))
    t))

;; ---- reading the runtime tallies ----------------------------------------

(defn- stuck-adornment?
  "Does a bound argument sit after an open one?  That is the shape with no selective trie
  prefix, and the whole argument for the secondary argument roots."
  [ad]
  (boolean (when-let [open (first (keep-indexed (fn [i c] (when (#{\f \F} c) i)) ad))]
             (some (fn [^long j] (#{\b \B} (nth ad j))) (range (inc (long open)) (count ad))))))

(defn- deep-after-open?
  "Does an **open compound** sit after an open position?  That is the shape with no
  selective access path *at all*: the trie narrows left to right, so the compound's own
  tokens sit behind a fan, and `[:argument-root pred pos term]` keys a **ground**
  argument whole, so a compound holding a variable is not one of its keys either.

  Deliberately not `stuck-adornment?` with a wider alphabet, and the difference is the
  reason both exist.  That one asks for a *bound* argument after an open one, so it never
  counts an `F` — an open compound is open. Its shape is answered by the argument roots
  today; this one is answered by nothing, and adding the two together would report a
  number meaning neither.

  What it cannot see is where inside the compound the variable sits: the adornment is one
  character per **top-level** argument, so `(mass Obj (QuantityFn ?n Kilogram))` reads
  `bF` and is not counted here, although `Kilogram` sits behind `?n` within the subterm.
  This is the outer case only — the compound behind an open position at the top."
  [ad]
  (boolean (when-let [open (first (keep-indexed (fn [i c] (when (#{\f \F} c) i)) ad))]
             (some (fn [^long j] (= \F (nth ad j))) (range (inc (long open)) (count ad))))))

(defn- open-compound?
  "Is an open compound asked at **any** position?  The reading above says where the `F`
  sits; this one says whether an `F` arrives at all, and the two are only worth
  separating when the first is zero — which is exactly when a design decision hangs on
  it.  A zero here is the stronger finding of the two: a corpus that never asks a
  partially-ground compound has no deep position for any key to name, whatever the
  position rule, so it rules out a family keyed inside a compound rather than merely
  reporting that nothing blocks the ones it asks."
  [ad]
  (boolean (some #{\F} ad)))

(defn- shape-rows
  "The `[functor truth adornment path] count` rows of a goal tally, most-asked first,
  printed as one line each."
  [rows]
  (doseq [[[f tr ad pth] n] rows]
    (println (format "      %-30s %-6s %-10s %-15s %,8d"
                     f (name tr) (if (= "" ad) "-" ad) (name pth) n))))

(defn- goal-report [snap label]
  (let [goals (:goals snap)
        total (reduce + 0 (vals goals))
        by    (fn [f] (sort-by val > (reduce (fn [m [k n]] (update m (f k) (fnil + 0) n)) {} goals)))]
    (println (format "\n  %s — %,d retrieval decisions (candidate-handles + matches-hierarchical)"
                     label total))
    (when (pos? total)
      (println "    by access path:")
      (doseq [[pth n] (by #(nth % 3))]
        (println (format "      %-16s %,10d  (%5.1f%%)" (name pth) n (pct n total))))
      (println "    by binding pattern (b ground atom · B ground compound · n unkeyed literal · f open · F open compound):")
      (doseq [[ad n] (take 12 (by #(nth % 2)))]
        (println (format "      %-16s %,10d  (%5.1f%%)" (if (= "" ad) "<no arguments>" ad) n (pct n total))))
      (let [open  (reduce + 0 (map val (filter (fn [[k _]] (= :open (nth k 0))) goals)))
            stuck (reduce + 0 (map val (filter (fn [[k _]] (stuck-adornment? (nth k 2))) goals)))
            deep  (reduce + 0 (map val (filter (fn [[k _]] (deep-after-open? (nth k 2))) goals)))
            anyc  (reduce + 0 (map val (filter (fn [[k _]] (open-compound? (nth k 2))) goals)))]
        ;; the two shapes the secondary roots exist for, as fractions of the whole
        (println (format "    a bound argument after an open one (what the argument roots are for)  %,d  (%.2f%%)"
                         stuck (pct stuck total)))
        (println (format "    an open functor `(?p …)` (what the argument-slot roster is for)       %,d  (%.2f%%)"
                         open (pct open total)))
        ;; and the shape nothing is for — the one a path-keyed root would be built for
        (println (format "    an open compound after an open one (what nothing is for)              %,d  (%.2f%%)"
                         deep (pct deep total)))
        ;; the same shape with the position rule dropped, which separates "never blocked"
        ;; from "never asked" when the line above is zero
        (println (format "    an open compound at any position (whether the shape arrives at all)   %,d  (%.2f%%)"
                         anyc (pct anyc total)))
        (println (format "    distinct shapes asked                                                 %,d"
                         (count goals))))
      (println "    the ten most-asked shapes:")
      (shape-rows (take 10 (sort-by val > goals)))
      ;; the same cut over the shape with no access path, because "is there a corpus that
      ;; wants a path-keyed root" is answered by which functors ask it, not by a total
      (let [deeps (sort-by val > (filter (fn [[k _]] (deep-after-open? (nth k 2))) goals))
            opens (sort-by val > (filter (fn [[k _]] (open-compound? (nth k 2))) goals))]
        (cond
          (seq deeps)
          (do (println "    the open compounds behind an open position, most-asked first:")
              (shape-rows (take 5 deeps)))

          ;; an open compound arrives but always with a ground prefix in front of it: the
          ;; trie reaches its tokens, so the shape is served and the row above is a zero
          ;; about blocking rather than about the corpus
          (seq opens)
          (do (println "    no open compound sat behind an open position; where they were asked:")
              (shape-rows (take 5 opens)))

          :else
          (println "    no open compound was asked at any position"))))))

(def ^:private families
  "Every family a `KvIndexStore` read can land in, in the order the index docstring
  lists them.  Iterated in full rather than over what the tally holds, because a family
  nothing read is the finding: a zero is the answer to \"does this KB use it\"."
  [:trie-lookup :trie-counts :context-root :functor-root :argument-root :argument-slot
   :rule-index :exception-index :term-index :term-roster])

(defn- read-report [snap label]
  (let [rs    (:reads snap)
        total (reduce + 0 (vals rs))]
    (println (format "\n  %s — %,d index reads, by family" label total))
    (doseq [f families
            :let [n (long (get rs f 0))]]
      (println (format "      %-18s %,10d  %s" (name f) n
                       (if (zero? n) "— never read" (format "(%5.1f%%)" (pct n total))))))))

(defn- fan-report [snap label]
  (let [fan   (:fan snap)
        calls (reduce + 0 (map (comp long :calls val) fan))
        visits (reduce + 0 (map (comp long #(or (:visits %) 0) val) fan))
        decades (apply merge-with + (map (comp :decades val) fan))]
    (println (format "\n  %s — %,d trie walks, %,d node probes (%.2f per walk)"
                     label calls visits (/ (double visits) (max 1 calls))))
    (when (seq decades)
      (println "    probes per walk:")
      (doseq [[d n] (sort decades)]
        (println (format "      %,8d …  %,10d walks  (%5.1f%%)" d n (pct n calls)))))
    (when (seq fan)
      (println "    the walks that cost the most, by total probes:")
      (println (format "      %-30s %10s %12s %10s %10s" "first token" "walks" "probes" "per walk" "widest"))
      (doseq [[tok row] (take 10 (sort-by (comp - long :visits val) fan))]
        (println (format "      %-30s %,10d %,12d %10.1f %,10d"
                         tok (:calls row) (:visits row)
                         (/ (double (:visits row)) (max 1 (long (:calls row))))
                         (:widest row)))))))

(defn- write-report [snap label]
  (let [w   (:writes snap)
        tot (fn [k] (reduce + 0 (map (comp long #(or (get % k) 0) val) w)))
        n   (tot :asserts)]
    (println (format "\n  %s — %,d index writes" label n))
    (when (pos? n)
      (let [levels (tot :levels) terms (tot :terms) roots (tot :roots)
            roster (tot :roster) slots (tot :slots)
            ops    (+ (* 2 levels) terms roots roster slots n)]  ; two ops per trie level, plus the seal
        (println "    keys touched per assert, by family:")
        (println (format "      trie levels        %8.2f   (two ops each: a counter and a child edge)" (/ (double levels) n)))
        (println (format "      term index         %8.2f" (/ (double terms) n)))
        (println (format "      secondary roots    %8.2f   (context + functor + one per indexable argument)" (/ (double roots) n)))
        (println (format "      term roster        %8.2f   (a name's first mention only)" (/ (double roster) n)))
        (println (format "      argument slots     %8.2f   (a predicate's first fact at that slot only)" (/ (double slots) n)))
        (println (format "      → batch ops        %8.2f" (/ (double ops) n))))
      (println "    the predicates that cost the most to write:")
      (println (format "      %-30s %10s %10s %10s %10s" "functor" "asserts" "levels" "terms" "roots"))
      (doseq [[f row] (take 8 (sort-by (fn [[_ r]] (- (long (:asserts r)))) w))]
        (let [a (long (:asserts row))]
          (println (format "      %-30s %,10d %10.2f %10.2f %10.2f"
                           f a (/ (double (:levels row)) a) (/ (double (:terms row)) a)
                           (/ (double (:roots row)) a))))))))

(defn- retract-report [snap label]
  (let [w   (:retracts snap)
        tot (fn [k] (reduce + 0 (map (comp long #(or (get % k) 0) val) w)))
        n   (tot :retracts)]
    (println (format "\n  %s — %,d index retractions" label n))
    (when (pos? n)
      (let [levels (tot :levels) terms (tot :terms) roots (tot :roots)
            roster (tot :roster) slots (tot :slots) dead (tot :dead)
            ;; batch 1 is one leaf removal and one decrement per level; batch 2 is three
            ;; deletes per dead node plus a detach from its parent, then the flat
            ;; families and the seal.  A ceiling rather than an equality: the trie root
            ;; has no parent to detach from, so a retraction that killed it is one under
            ops    (+ 1 levels (* 4 dead) terms roots roster slots n)]
        (println "    ops touched per retraction, by family:")
        (println (format "      trie levels        %8.2f   (a leaf removal, then one decrement each)" (/ (double levels) n)))
        (println (format "      dead trie nodes    %8.2f   (three deletes and a parent detach each)" (/ (double dead) n)))
        (println (format "      term index         %8.2f" (/ (double terms) n)))
        (println (format "      secondary roots    %8.2f" (/ (double roots) n)))
        (println (format "      term roster        %8.2f   (a name's last mention only)" (/ (double roster) n)))
        (println (format "      argument slots     %8.2f   (a predicate's last fact at that slot only)" (/ (double slots) n)))
        (println (format "      → batch ops       ≤%8.2f" (/ (double ops) n)))
        ;; the quantity a corpus moves without changing what it holds, and the reason
        ;; this is not the assert tally with a sign on it
        (println (format "    %.2f of every %.2f trie levels died, so the retraction cost is"
                         (/ (double dead) n) (/ (double levels) n)))
        (println "    a property of how much prefix the corpus shares, not of the sentex"))
      (println "    the predicates that cost the most to retract:")
      (println (format "      %-30s %10s %10s %10s" "functor" "retracts" "levels" "dead"))
      (doseq [[f row] (take 8 (sort-by (fn [[_ r]] (- (long (:retracts r)))) w))]
        (let [a (long (:retracts row))]
          (println (format "      %-30s %,10d %10.2f %10.2f"
                           f a (/ (double (:levels row)) a) (/ (double (:dead row)) a))))))))

;; ---- the balanced probe --------------------------------------------------
;; Every binding pattern asked equally often, which no workload does.  Its question is
;; what a shape COSTS, so the arms above can say what arrives and this one what it is
;; worth serving.

(defn- adornments
  "Every `b`/`f` binding pattern over `n` arguments, most-open first."
  [^long n]
  (sort-by #(count (filter #{\b} %))
           (map (fn [^long i]
                  (apply str (map (fn [^long j] (if (bit-test i j) \b \f)) (range n))))
                (range (bit-shift-left 1 n)))))

(defn- probe-pattern
  "`fact` with every position the adornment calls open replaced by a fresh variable, or
  nil when a position it wants *bound* holds a term the roots do not key (a number, a
  string).  Refusing those keeps the requested pattern and the shape the profiler
  observes the same thing: `(comment ?x \"…\")` is asked as `fb` and arrives as `fn`,
  and a row that mixes the two attributes one shape's fan to another."
  [fact ad]
  (when (every? (fn [^long i] (or (= \f (nth ad i)) (sx/indexable-term? (nth (vec (rest fact)) i))))
                (range (count ad)))
    (cons (first fact)
          (map-indexed (fn [i a] (if (= \b (nth ad i)) a (symbol (str "?p" i))))
                       (rest fact)))))

(defn- sample-facts
  "Up to `k` believed fact sentences on `pred`, read straight from the functor root."
  [kb pred ^long k]
  (into [] (comp (map #(p/get-sentex (:records kb) %))
                 (keep (fn [s] (when (and s (nil? (:antecedent s)) (= :true (:truth s)))
                                 (sx/body s))))
                 (filter #(and (sequential? %) (seq %)))
                 (take k))
        (p/sentexes-with-functor (:index kb) pred)))

(defn- probe-row
  "Run `pats` under the instrument and print one row: what `candidate-handles` chose, and
  what the trie walks cost.  The walk figures count **every** `p/lookup` the ask reached,
  not only the one `candidate-handles` decided on, so a shape that diverts to the roots
  and still pays a fan is visible as one."
  [kb label ^long ar pats]
  (prof/start)
  (doseq [pat pats]
    (try (doall (take 200 (v/sentexes-matching kb pat))) (catch Exception _ nil)))
  (let [snap  (prof/stop)
        goals (:goals snap)
        asks  (reduce + 0 (vals goals))
        paths (sort-by val > (reduce (fn [m [kk n]] (update m (nth kk 3) (fnil + 0) n)) {} goals))
        fan   (:fan snap)
        calls (reduce + 0 (map (comp long :calls val) fan))
        vis   (reduce + 0 (map (comp long #(or (:visits %) 0) val) fan))
        wide  (reduce max 0 (map (comp long #(or (:widest %) 0) val) fan))]
    (println (format "    %-6d %-8s %,8d  %-34s %,9d %11.1f %,9d"
                     ar label asks
                     (->> paths (map (fn [[p n]] (str (name p) " " n))) (interpose ", ") (apply str))
                     calls (/ (double vis) (max 1 asks)) wide))))

(defn balanced-probe
  "For each binding pattern, ask it of `k` sample facts on each of the top `preds`
  predicates and report the path it chose and what the walk cost."
  [kb preds ^long k]
  (banner "the balanced probe — every binding pattern asked equally often (SYNTHETIC)")
  (println "  Not a claim about the workload.  What it measures is the cost of a shape, so")
  (println "  the load, chain and ask arms can be read for which shapes actually arrive.")
  (let [by-arity (group-by #(long (dec (count %)))
                           (mapcat #(sample-facts kb % k) preds))]
    (println (format "    %-6s %-8s %8s  %-34s %9s %11s %9s"
                     "arity" "pattern" "asks" "path" "walks" "probes/ask" "widest"))
    (doseq [[ar facts] (sort by-arity)
            :when (<= 1 ar 3)
            ad (adornments ar)
            :let [pats (keep #(probe-pattern % ad) facts)]
            :when (seq pats)]
      (probe-row kb ad ar pats))
    ;; the open-functor shape, which puts every argument behind the variable
    (doseq [[ar facts] (sort by-arity)
            :when (<= 1 ar 2)]
      (probe-row kb (str "?p" (apply str (repeat ar \b))) ar
                 (map #(cons '?p (rest %)) facts)))))

;; ---- the corpora ---------------------------------------------------------

(defn- load-starter! [kb]
  (banner "loading the shipped starter ontology")
  (let [t0 (System/nanoTime)]
    (starter/load-into kb)
    (println (format "  %,d sentexes in %.0f ms" (v/sentex-count kb) (ms t0)))))

(defn- load-generated!
  "A corpus with the measured shape of a real one — Zipf-skewed predicates and
  individuals, binary facts, chain-join rules — so the profile has an arm whose
  distribution is known rather than discovered.

  **Every rule here is backward**, which makes the chain arm report nothing on this corpus
  and is the right trade: a chain join over Zipf-skewed individuals materializes a large
  multiple of the base, and an arm that exists to hold *shape* fixed must not spend its
  run deriving.  The forward traffic comes from the corpora that have their own rules;
  the backward traffic is the ask arm's, which expands exactly these.

  Predicates are **stratified into layers**, as `vaelii.bench.corpus` stratifies them:
  facts populate band 0, and a rule concluding a band-k predicate draws its antecedents
  only from bands below k.  That makes the rule graph acyclic, so the cascade terminates
  in a bounded number of rounds instead of running a Zipf-hot consequent back into its own
  antecedent forever."
  [kb ^long facts ^long rules]
  (banner (format "generating %,d facts and %,d rules" facts rules))
  (let [rng    (java.util.Random. 11)
        layers 3
        preds  (u/terms "pr" (max 40 (quot rules 4)))
        nbase  (max 10 (quot (count preds) 4))
        band   (fn [^long k]
                 (let [bsz (max 1 (quot (- (count preds) nbase) (dec layers)))]
                   (if (zero? k)
                     (subvec preds 0 nbase)
                     (subvec preds
                             (min (count preds) (+ nbase (* (dec k) bsz)))
                             (min (count preds) (+ nbase (* k bsz)))))))
        per-k  (into {} (for [k (range 1 layers)]
                          (let [cb (band k) lo (vec (mapcat band (range k)))]
                            [k {:cb cb :ccum (u/zipf-cumulative (count cb) 1.3)
                                :lo lo :lcum (u/zipf-cumulative (count lo) 1.1)}])))
        inds   (u/terms "Ind" facts)
        icum   (u/zipf-cumulative (count inds) 1.0)
        bcum   (u/zipf-cumulative nbase 1.1)
        ind    #(nth inds (u/zipf-sample icum rng))
        t0     (System/nanoTime)]
    (v/with-deferred-settle kb
      (dotimes [_ rules]
        (let [a     (inc (.nextInt rng 3))
              k     (inc (.nextInt rng (dec layers)))
              {:keys [cb ccum lo lcum]} (per-k k)
              vars  (mapv #(symbol (str "?v" %)) (range (inc a)))
              antes (mapv (fn [j] (list (nth lo (u/zipf-sample lcum rng))
                                        (nth vars j) (nth vars (inc j))))
                          (range a))
              conseq (list (nth cb (u/zipf-sample ccum rng)) (first vars) (last vars))]
          (try (v/assert-rule kb antes conseq 'CxBench
                              {:direction :backward})
               (catch Exception _ nil))))
      (dotimes [_ facts]
        (try (v/assert kb (list (nth (band 0) (u/zipf-sample bcum rng)) (ind) (ind))
                       'CxBench)
             (catch Exception _ nil))))
    (println (format "  %,d sentexes in %.0f ms" (v/sentex-count kb) (ms t0)))))

(defn- load-corpus! [kb dir profile]
  (banner (str "loading " dir " at :" (name profile)))
  (let [reader (foreign/reader! :cyc-corpus)
        t0     (System/nanoTime)
        r      ((:load-dir! reader) kb dir
                {:profile profile
                 :on-progress (fn [{:keys [done note]}]
                                (when (zero? (mod (long done) 200000))
                                  (println (format "    %,10d sentences … %s" done (or note "")))
                                  (flush)))})]
    (println (format "  asserted %,d, refused %,d over %,d contexts in %.0f s"
                     (:asserted r) (:refused r) (:contexts r) (/ (ms t0) 1000)))
    r))

(defn- rule-goals
  "Up to `limit` rule consequents, as written.  A rule's consequent *is* the question the
  rule exists to answer, so a run over the set is a workload the KB declared for itself
  rather than one this harness invented."
  [kb ^long limit]
  (into [] (comp (map #(p/get-sentex (:records kb) %))
                 (keep (fn [s] (when (some? (:antecedent s)) (:consequent s))))
                 (filter #(and (sequential? %) (seq %) (symbol? (first %))))
                 (take limit))
        (p/sentex-ids (:records kb))))

(defn- ask-arm
  "The backward side: each rule's consequent proved with the rules expanded two deep, so
  the antecedents the search opens are goals too.  Bounded per goal (`prove-within`) and
  over the arm as a whole, because a rule set nobody has read can hold a search that does
  not come back, and a workload profile is not the place to discover that."
  [kb ^long limit]
  (banner "the ask arm — each rule's own consequent, proved two deep (REAL)")
  (let [gs       (rule-goals kb limit)
        t0       (System/nanoTime)
        deadline (+ (System/nanoTime) (long 120e9))
        asked    (atom 0)]
    (prof/start)
    (doseq [g gs :while (< (System/nanoTime) deadline)]
      (swap! asked inc)
      (try (v/prove-within kb g '?ctx {:max-ms 200 :max-results 20 :max-depth 2})
           (catch Exception _ nil)))
    (let [snap (prof/stop)]
      (println (format "  proved %,d of %,d rule consequents in %.0f ms"
                       @asked (count gs) (ms t0)))
      (goal-report snap "ask")
      (read-report snap "ask")
      (fan-report snap "ask")
      snap)))

(defn- chain-arm [kb]
  (banner "the chain arm — the goals a forward-chaining run asks (REAL)")
  (prof/start)
  (let [t0 (System/nanoTime)
        r  (try (v/forward-chain kb {:max-depth 3}) (catch Exception e {:error (.getMessage e)}))
        snap (prof/stop)]
    (println (format "  chained in %.0f ms — %s" (ms t0) (pr-str (dissoc r :conclusions))))
    (goal-report snap "chain")
    (read-report snap "chain")
    (fan-report snap "chain")
    snap))

;; ---- the two arms no reasoning workload runs ------------------------------

(defn- stride
  "`n` items spread evenly through `xs`, or all of them when there are fewer.  Even
  spacing rather than a random sample, because an arm has to reproduce: every quantity
  here is a count, and a count taken over a different sample is a different reading with
  nothing to say so."
  [^long n xs]
  (let [v (vec xs) c (count v)]
    (if (<= c n)
      v
      (mapv #(nth v (quot (* (long %) c) n)) (range n)))))

(defn- interactive-arm
  "The vocabulary and term reads an **application** makes — the arm every other one here
  is missing, and the reason two families tally zero everywhere else.

  `terms`, `term-count`, `find-terms` and `find-sentexes` are what the term roster and the
  term index exist for, and not one of them is called by a load, a forward-chaining run or
  a backward proof.  Without this arm the read tally reports those two families at zero,
  which reads as *nothing uses them* and means *no reasoning uses them* — and a per-KB
  index policy turns on the difference.

  No goal shapes come out of it: these reach the index without passing either matcher, so
  they land in `:reads` and `:fan` and nowhere in `:goals`.  The read table is the point."
  [kb ^long limit]
  (banner "the interactive arm — the vocabulary reads an application makes (REAL)")
  (prof/start)
  (let [t0       (System/nanoTime)
        deadline (+ (System/nanoTime) (long 120e9))
        vocab    (v/terms kb)
        _        (v/term-count kb)
        picks    (stride limit (filterv symbol? vocab))
        pages    (atom 0)
        fetched  (atom 0)]
    ;; a term picker's search box, prefix and substring, both over the roster
    (doseq [q (stride 8 picks) :while (< (System/nanoTime) deadline)]
      (let [s (str q)]
        (try (v/find-terms kb (subs s 0 (min 3 (count s))) {:limit 50})
             (v/find-terms kb s {:match :substring :limit 50})
             (catch Exception _ nil))))
    ;; a term page: every sentex mentioning this name.  Capped at 200 records because the
    ;; *index* read is the measurement and the record fetches are not — the posting is
    ;; read whole before the first record is realized, so the cap costs the tally nothing.
    (doseq [t picks :while (< (System/nanoTime) deadline)]
      (try (swap! fetched + (count (take 200 (v/find-sentexes kb t))))
           (swap! pages inc)
           (catch Exception _ nil)))
    ;; and the intersection, which is a different read of the same family
    (doseq [[a b] (partition 2 (stride 64 picks)) :while (< (System/nanoTime) deadline)]
      (try (count (take 200 (v/find-sentexes-all kb [a b]))) (catch Exception _ nil)))
    (let [snap (prof/stop)]
      (println (format "  %,d vocabulary terms; %,d term pages, %,d sentexes fetched, in %.0f ms"
                       (count vocab) @pages @fetched (ms t0)))
      (goal-report snap "interactive")
      (read-report snap "interactive")
      (fan-report snap "interactive")
      snap)))

(def ^:private taxonomy-functors
  "The two predicates whose churn is not an index measurement.

  A `genl` or `genlCx` sentence **is** a taxonomy edge, so retracting one and putting
  it back retires a cached closure (`docs/taxonomy.md`) rather than only the trie under
  it.  On an ontology corpus the two are a fifth of everything stored — `genl` alone is
  the largest predicate in the shipped OpenCyc conversion — and one such pair costs
  several times an ordinary one.  So a sample drawn blind is a fifth taxonomy edges and
  much more than a fifth of the wall-clock.  Priced apart, not dropped: the churn a
  taxonomy sees is real, and its cost is a reading of its own.

  **The spread within the sample is the reading, not its middle.**  What one edge costs is
  the size of the region its removal moves, and that ranges over orders of magnitude
  within one hierarchy: an edge between two leaf types moves almost nothing, and the edge
  putting the root type under `thing` disconnects every type from the root, so `isa?`
  changes for every individual and the affected region is the graph.  Both are ordinary,
  and a mean over a sample holding one of each is the second divided by the sample size,
  wearing the shape of a typical cost.  So the report is median, p95 and max, and it names
  the pairs at the top."
  '#{genl genlCx})

(defn- churn-functor
  "The functor a stored fact churns under, or nil for a rule.  `sx/body` rather than the
  raw sentence, so a `:false` fact classifies on the predicate it denies."
  [sx]
  (let [b (sx/body sx)]
    (when (and (sequential? b) (seq b)) (first b))))

(defn- within
  "Run `f` on a worker of its own and wait `budget-ms` for its value, or `::over-budget`
  when the wait runs out.

  The **bound has to be on the operation**, not between operations: a `:while` on the loop
  is read once a pair is already over, so one pathological retraction is unbounded however
  short the arm's deadline — and a run that hangs here hangs holding a corpus-sized heap,
  where the harness reports the shell's exit rather than the workload's and nobody learns
  for an hour.

  The worker is **abandoned rather than interrupted** when the budget runs out.  A store
  part-way through a write is not something to unwind for a measurement, and the arm stops
  at that point anyway; it is a daemon thread, so the run can still exit while one is
  wedged."
  [^long budget-ms f]
  (let [^java.util.concurrent.ArrayBlockingQueue box (java.util.concurrent.ArrayBlockingQueue. 1)]
    (doto (Thread. ^Runnable (fn [] (.offer box [(f)])) "vaelii-churn")
      (.setDaemon true)
      (.start))
    (if-let [v (.poll box budget-ms java.util.concurrent.TimeUnit/MILLISECONDS)]
      (first v)
      ::over-budget)))

(defn- churn-pair!
  "Retract `sx` and put it straight back: `:done`, `:refused` (the retraction would not
  go) or `:lost` (it went and the fact would not go back).

  Catches `Throwable`, which `Exception` alone would not: a pair that dies on a
  `StackOverflowError` down a closure walk is a pair the arm has to count, not one it may
  let take the run with it."
  [kb sx]
  (if-not (try (v/retract! kb (:id sx)) true (catch Throwable _ nil))
    :refused
    (if (try (v/assert kb (:sentence sx) (:context sx) {:strength (:strength sx)}) true
             (catch Throwable _ nil))
      :done
      :lost)))

(def ^:private heap-ceiling
  "The fraction of the maximum heap past which a sample stops rather than continues.

  The third bound, and the one a clock cannot stand in for: a corpus-sized KB churned
  against enough taxonomy edges throws away and rebuilds a cached closure per pair, and a
  run that dies of that dies **hard** — no stack trace, leiningen reporting only that the
  inner task failed, and a detached harness reporting the shell's exit rather than the
  workload's.  Stopping a little under the ceiling turns that into a line."
  0.90)

(defn- over-heap?
  "Is the live set past `heap-ceiling` of the maximum heap?

  Read twice with a collection between, because one reading is the collector's backlog
  rather than what is live — and a sample stopped on a backlog is a bound firing on
  nothing.  The collection only runs on the reading that is already over, so the ordinary
  pair pays two field reads."
  []
  (let [rt   (Runtime/getRuntime)
        used (fn [] (double (- (.totalMemory rt) (.freeMemory rt))))
        cap  (* heap-ceiling (.maxMemory rt))]
    (when (> (used) cap)
      (System/gc)
      (> (used) cap))))

(defn- churn-progress
  "Where a sample has got to, flushed.

  The arm is the last one to run and the one that can die inside a single operation, so
  it has to narrate: printing only on the way out is how a run reports its header and
  then nothing at all, leaving no clue what it was doing when it went."
  [label ^long ran ^long total t0]
  (let [rt (Runtime/getRuntime)]
    (println (format "    %-16s %,6d of %,6d pairs … %6.1f s, heap %.1f of %.1f GB"
                     label ran total (/ (ms t0) 1000)
                     (/ (- (.totalMemory rt) (.freeMemory rt)) 1073741824.0)
                     (/ (.maxMemory rt) 1073741824.0)))
    (flush)))

(defn- churn-group!
  "Churn `sxs` under three bounds — `pair-ms` on one retract/re-assert pair, `arm-ms` on
  the group, `heap-ceiling` on what is left of the heap — and return
  `{:done :refused :lost :ran :ms :stopped}`.  `:stopped` is absent when every sampled
  fact was churned, and otherwise says which bound fired and how many facts it dropped.

  `:pairs` is one `[ms sentex]` per **completed** pair, which is what lets the report be a
  distribution and name the pairs at the top of it.  A refusal did not do the work and is
  counted rather than timed, or the middle of the sample would be a reading of nothing.
  Keeping them is the only thing that accumulates here and a few hundred is nothing; not
  keeping them is how a run has to be repeated to answer *which pair was that*.

  The heap this watches is the engine's — a taxonomy pair retires a cached closure and the
  next read rebuilds it."
  [kb label sxs pair-ms arm-ms]
  (let [t0       (System/nanoTime)
        deadline (+ t0 (* 1000000 (long arm-ms)))
        total    (count sxs)
        step     (max 4 (quot total 8))]
    (loop [[sx & more] (seq sxs)
           acc {:done 0 :refused 0 :lost 0 :ran 0 :pairs []}]
      (cond
        (nil? sx)
        (assoc acc :ms (ms t0))

        (>= (System/nanoTime) (long deadline))
        (assoc acc :ms (ms t0) :stopped {:why :arm :left (inc (count more))})

        (over-heap?)
        (assoc acc :ms (ms t0) :stopped {:why :heap :left (inc (count more))})

        :else
        (let [t1 (System/nanoTime)
              r  (within (long pair-ms) #(churn-pair! kb sx))
              el (ms t1)]
          (if (= ::over-budget r)
            (assoc acc :ms (ms t0)
                   :stopped {:why :pair :left (inc (count more)) :sx sx})
            (let [acc (cond-> (-> acc (update :ran inc) (update r inc))
                        (= :done r) (update :pairs conj [el sx]))]
              (when (zero? (mod (long (:ran acc)) step))
                (churn-progress label (:ran acc) total t0))
              (recur more acc))))))))

(defn- spread
  "`{:n :median :p95 :max}` over a sample of pair timings, or nil when it is empty.

  **No mean.**  A mean is the right summary of a sample with one scale in it, and this one
  has three: it reads as what a pair costs while being, on the sample that motivated the
  split, one structurally global edge divided by the sample size.  Nearest-rank p95, so it
  is a reading that was taken rather than an interpolation between two — which on a small
  sample makes it the largest reading, and `churn-line` says so instead of dressing it up."
  [xs]
  (when (seq xs)
    (let [v (vec (sort xs))
          n (count v)]
      {:n n
       :median (nth v (quot n 2))
       :p95 (nth v (min (dec n) (max 0 (dec (long (Math/ceil (* 0.95 n)))))))
       :max (peek v)})))

(defn- brief
  "One line naming a sentex, cut to `n` characters.  A corpus `comment` runs to
  paragraphs, and a line naming the pair wants the predicate and its arguments."
  [sx ^long n]
  (let [s (pr-str (:sentence sx))]
    (str (if (<= (count s) n) s (str (subs s 0 n) " …")) " in " (:context sx))))

(defn- churn-line [label group sampled]
  (let [{:keys [done refused lost ms pairs]} group
        s (spread (map first pairs))]
    (println (format "    %-16s %,6d of %,6d pairs, %8.1f ms%s%s%s"
                     label done sampled (double ms)
                     (if s
                       (format " — median %7.3f  p95 %8.3f  max %9.3f ms"
                               (:median s) (:p95 s) (:max s))
                       "")
                     (if (pos? (long refused)) (format ", %,d would not retract" refused) "")
                     (if (pos? (long lost)) (format ", %,d LOST" lost) "")))
    (when (and s (< (long (:n s)) 20))
      (println (format "    %-16s (n=%d — too few for a p95, so that column is the largest reading)"
                       "" (:n s))))))

(defn- churn-worst
  "The `k` costliest pairs of a group, named.  The column that would have answered *which
  pair was that* without re-running: a summary says a sample held something expensive, and
  this says which sentence it was."
  [label group ^long k]
  (let [worst (take k (sort-by (comp - first) (:pairs group)))]
    (when (seq worst)
      (println (format "    the %s pairs that cost the most:" label))
      (doseq [[el sx] worst]
        (println (format "      %9.3f ms  %s" el (brief sx 78)))))))

(defn- retraction-count
  "How many `unindex-sentex!` calls a snapshot tallied, over every functor."
  [snap]
  (reduce + 0 (map (comp long #(or (:retracts %) 0) val) (:retracts snap))))

(defn- churn-ratio
  "What one pair of group `a` costs against one of group `b`, **at the median of each** —
  0.0 when either ran nothing, since a ratio nobody measured is reported as one rather
  than as a division.

  A ratio of means over these two samples is a ratio between one sample's worst edge and
  the other's typical one, which is a comparison nobody can act on."
  [a b]
  (let [med (fn [g] (or (:median (spread (map first (:pairs g)))) 0.0))
        bm  (med b)]
    (if (pos? bm) (/ (med a) bm) 0.0)))

(defn- churn-stopped
  "Say that a bound fired, what it dropped, and which pair it fired on.  Printed with a
  greppable sentinel because a run that stops early has to be *told*: a bound that
  truncates quietly reads afterwards as an arm that covered everything."
  [label {:keys [why left sx]} pair-ms arm-ms]
  (println (format "  ** SENTINEL churn arm STOPPED — the %s sample %s"
                   label (case why
                           :pair (format "had a pair pass its %,d ms budget" pair-ms)
                           :arm  (format "passed its %,d ms budget" arm-ms)
                           :heap (format "reached %.0f%% of the maximum heap"
                                         (* 100.0 heap-ceiling)))))
  (when sx
    (println (format "  ** the pair was %s in %s" (pr-str (:sentence sx)) (:context sx))))
  (println (format "  ** %,d sampled facts were dropped; the tallies below cover what ran"
                   left))
  (when (= :pair why)
    (println "  ** and the pair is abandoned rather than unwound, so this KB may hold")
    (println "  ** neither the fact nor its handle — it is spent, whatever it reads")))

(def ^:private ix-arm-ms
  "The index sample's share of the arm's 120 s.  Split rather than shared with the
  taxonomy sample, because one budget spent front to back is one the second sample never
  reaches — and the second is the slower per pair, so it is the one a shared budget
  starves."
  90000)

(def ^:private tax-arm-ms
  "The taxonomy sample's share of the same 120 s."
  30000)

(defn- churn-arm
  "Retract a sample of stored premises and put each one back — the only arm that runs
  `unindex-sentex!`, and so the only one that prices the retraction tax.

  **Net-neutral by construction**, and it says so when it is not: each fact is
  re-asserted into the same context at the same strength, and a re-assert that fails
  after its retraction succeeded is counted and reported, because it means the arms
  already run were over a different KB than the one this leaves.  The handles move —
  they are allocated in assertion order, and nothing may tie-break on one.

  **Two samples, priced apart.**  The tallies below are the *index* sample's, because
  `taxonomy-functors` is what a blind stride over an ontology fills up with and a
  taxonomy edge's churn is a closure reconcile wearing a retraction's shape.  The
  taxonomy sample runs after, under its own bound — so the comparison between the two
  lines is a reading rather than a number hidden inside one.

  **Reported as a distribution.**  Median, p95 and max per sample, and the costliest pairs
  named, because these two samples do not have the same shape and a pair of means hides
  exactly that: a taxonomy sample holds edges whose costs differ by orders of magnitude,
  and its mean is its worst edge divided by its size.  A reading off this arm gets cited,
  so it has to be a number somebody can act on.

  **Bounded three ways**, and per *pair* is the one that matters: a budget checked between
  pairs cannot see a pair that never returns.  The other two are the sample's own clock
  and `heap-ceiling`, since a clock does not bound what the engine allocates.  All three
  report through `churn-stopped`, and an abandoned pair ends the arm rather than only its
  own sample — the worker is still in the KB, and a second writer beside it would be
  measuring a race.

  It also **narrates**: the samples are printed before the first pair and progress every
  eighth of one, flushed, so a run that dies inside an operation still says how far it
  got.  Reporting only on the way out is how an arm prints its header and then nothing."
  [kb ^long limit ^long pair-ms]
  (banner "the churn arm — what retracting and re-asserting costs the index (REAL)")
  (let [tms      (:tms kb)
        ;; **premises only.**  A derived conclusion is an ordinary literal sentex with no
        ;; antecedent, so filtering on that alone churns the rule engine's own output —
        ;; and a conclusion a rule drew past an argument constraint does not go back in
        ;; as a premise, which the `lost` counter below reports as a KB no longer the one
        ;; the earlier arms measured.  `retract!` is for what somebody asserted.
        facts    (into [] (comp (map #(p/get-sentex (:records kb) %))
                                (filter some?)
                                (filter #(nil? (:antecedent %)))
                                (filter #(jtms/premise? tms (:id %))))
                       (stride (* 4 limit) (vec (p/sentex-ids (:records kb)))))
        {tax true ix false} (group-by #(contains? taxonomy-functors (churn-functor %)) facts)
        ;; strided a second time, per sample: a `take` off an evenly-spaced sample is the
        ;; front of the id space rather than a spread of it, and the split makes each
        ;; sample's size a property of the corpus's mix until it is re-spread
        ix-sxs   (stride limit ix)
        ;; half the index sample rather than a quarter: this one is read as a
        ;; distribution, and its own spread runs to hundreds of times its median, so a
        ;; dozen readings put a p95 on the largest of them and call it a percentile
        tax-sxs  (stride (max 20 (quot limit 2)) tax)]
    ;; said before the first pair rather than after the last, so a run that dies inside
    ;; one still records what the arm was attempting
    (println (format "  %,d strided handles → %,d index-path premises, %,d taxonomy edges;"
                     (* 4 limit) (count ix-sxs) (count tax-sxs)))
    (println (format "  %,d ms per pair, %,d ms the index sample, %,d ms the taxonomy one"
                     pair-ms ix-arm-ms tax-arm-ms))
    (flush)
    ;; the arm's own 120 s, split rather than shared, so the second sample is never
    ;; starved by the first — with `pair-ms` on top, twice, the arm cannot run past it
    (prof/start)
    (let [ix-r    (churn-group! kb "index path" ix-sxs pair-ms ix-arm-ms)
          snap    (prof/stop)
          ;; an abandoned pair is a worker still inside this KB, and a second writer
          ;; beside it is not serializable (docs/storage.md) — so the taxonomy sample is
          ;; dropped rather than measured against one.  A deadline stop left nothing
          ;; running and is not that case
          wedged? (= :pair (:why (:stopped ix-r)))]
      (prof/start)
      (let [tax-r    (churn-group! kb "taxonomy edges" (if wedged? [] tax-sxs)
                                   pair-ms tax-arm-ms)
            tax-snap (prof/stop)
            lost     (+ (long (:lost ix-r)) (long (:lost tax-r)))]
        (println (format "  churned %,d of %,d premises sampled from %,d strided handles"
                         (+ (long (:done ix-r)) (long (:done tax-r)))
                         (+ (count ix-sxs) (count tax-sxs)) (* 4 limit)))
        (churn-line "index path" ix-r (count ix-sxs))
        (if wedged?
          (println (format "    %-16s %,6d pairs not run — the index sample left a worker in this KB"
                           "taxonomy edges" (count tax-sxs)))
          (do (churn-line "taxonomy edges" tax-r (count tax-sxs))
              (println (format "    → at the median a taxonomy pair cost %.1f× an index-path pair, over"
                               (churn-ratio tax-r ix-r)))
              (println (format "      %,d index retractions and %,d taxonomy ones.  Median rather"
                               (retraction-count snap) (retraction-count tax-snap)))
              (println "      than mean, and the columns beside it rather than nothing: what an")
              (println "      edge costs is the size of the region it moves, and one sample holds")
              (println "      edges that move almost nothing beside edges that move the hierarchy.")
              (println "      The tallies below are the index path's alone (docs/taxonomy.md)")
              (churn-worst "taxonomy" tax-r 3)))
        (churn-worst "index-path" ix-r 3)
        (when-let [s (:stopped ix-r)] (churn-stopped "index path" s pair-ms ix-arm-ms))
        (when-let [s (:stopped tax-r)] (churn-stopped "taxonomy edge" s pair-ms tax-arm-ms))
        (when (pos? lost)
          (println (format "  ** %,d were retracted and would not go back — this KB is no longer"
                           lost))
          (println "  ** the one the arms above measured; treat their readings as suspect"))
        (retract-report snap "churn")
        (write-report snap "churn")
        (read-report snap "churn")
        snap))))

(defn -main [& args]
  (let [mode (or (first args) "starter")
        kb   (v/open-kb {})]
    (println (format "vaelii bench-profile — %s, max heap %.1f GB"
                     mode (/ (.maxMemory (Runtime/getRuntime)) 1073741824.0)))
    ;; the load arm runs under the instrument, so the write tally is the real one: every
    ;; assert the corpus makes, not a re-indexed sample of them
    (prof/start)
    (case mode
      "generated" (load-generated! kb
                                   (or (some-> (second args) Long/parseLong) 30000)
                                   (or (some-> (nth args 2 nil) Long/parseLong) 3000))
      "corpus"    (load-corpus! kb (second args) (keyword (or (nth args 3 nil) "ontology")))
      (load-starter! kb))
    (let [load-snap (prof/stop)]
      (banner "the load arm — what asserting this corpus cost the index (REAL)")
      (write-report load-snap "load")
      (goal-report load-snap "load")
      (read-report load-snap "load")
      (fan-report load-snap "load"))

    (let [shape (corpus-shape kb)
          preds (take 12 (sort-by #(- (long (p/count-with-functor (:index kb) %)))
                                  (vec (:preds shape))))]
      (chain-arm kb)
      (ask-arm kb (if (= "corpus" mode) 400 200))
      (interactive-arm kb (if (= "corpus" mode) 400 100))
      (balanced-probe kb preds (if (= "corpus" mode) 40 20))
      ;; last, because it is the only arm that writes: the handles it moves are handles
      ;; every arm above has already finished with.  The second number is the per-pair
      ;; budget, wider on a corpus because everything there is doing more of everything —
      ;; it is set to catch a pair that has stopped making progress, not to police a slow
      ;; one, and the arm's own budget is what bounds the total
      (churn-arm kb (if (= "corpus" mode) 200 50) (if (= "corpus" mode) 10000 2000)))
    (shutdown-agents)))
