;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.hotreads
  "Two reads recomputed per firing, measured — the class `lein perf` says in its own
  docstring it cannot see.

  `perf` gates **growth between two sizes**, so a cost that is constant per operation
  moves both of its readings by the same amount and leaves every ratio alone.  A read
  rebuilt once per placement is exactly that shape: not an algorithmic regression
  against any documented claim, and one that will never fail the gate.  What it *is* is
  a per-firing constant nobody had a number for, and this harness is that number.

  So this one **reports**, like every `bench-*` beside `perf`.  Each arm gives three
  figures, and they multiply:

    ns/read          what one call costs, measured directly
    reads/derivation how many of them a chaining run makes per fact it derives,
                     counted by redefining the read for a second, untimed run
    µs/derivation    what the whole run costs per derived fact, best of `--reps`

  The first two multiply into the read's share of the third, which is the number a fix
  has to move.  A wall clock alone could not say it: a chaining run's cost per fact
  moves with JIT warmth by more than either read is worth.

  **`excepted-handles`** (`vaelii.impl.resolution`) answers which handles a believed
  `(except (sentexHandle H))` hides from a view context.  It opens on the emptiness of
  the `:excepted` roster, so a KB that hides nothing pays one deref; past that it is a
  `tax/context-up` and a `jtms/in?` per except stated in a visible context, **per call**,
  and the callers are per-placement (`chain/place-conclusion` → `antecedent-hidden?`) and
  per candidate justification (`chain/justification-excepted?`).  The excepted targets
  are **decoys** — facts no rule reads — so E moves the cost of the read without moving
  what the run derives, which is what makes the rows comparable.

  **`est-matches`** (`vaelii.impl.plan`) bounds a literal's fan-out.  For a *unary* type
  literal it sums a `prefix-estimate` over the type's whole subtype closure, and
  `plan/order` estimates every remaining literal on every pick — so a broad antecedent
  over a deep hierarchy pays `|specs(T)|` trie walks per pick, per plan, per firing
  attempt.  `tax/specs` is itself memoized on the taxonomy generation, so what is
  measured is the `reduce` over the closure and not the fetch.

  Run: `lein bench-hotreads [--facts n] [--samples n] [--depth n] [--branching n]
                            [--reps n]`

    --facts      facts each chaining arm loads (default 400)
    --samples    direct-call samples per reading (default 20000)
    --depth      genl depth for the est-matches arm (default 6)
    --branching  genl branching for the same (default 3)
    --reps       chaining runs per row, best taken (default 3)"
  (:require [vaelii.core :as v]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(def ^:private defaults
  {:facts     400
   :samples   20000
   :depth     6
   :branching 3
   :reps      3})

(defmacro ^:private timed [& body]
  `(let [t0# (System/nanoTime) r# (do ~@body)]
     [r# (- (System/nanoTime) t0#)]))

(def ^:private space
  "A counter handing each KB its own memory space, so one arm cannot leave state in
  another's — the discipline `perf`'s own `fresh-kb` keeps, over rows this one builds
  from a loop rather than from a fixed list."
  (atom 60))

(defn- fresh-kb []
  (let [kb (v/open-kb {:backend :memory :space (swap! space inc) :recover? false})]
    (v/clear! kb)
    kb))

(defn- per-call
  "Nanoseconds one call of `f` costs.  The warmup is **fixed** rather than proportional
  to `n`: sizing it by the sample count gives the longer reading a head start, which is
  the mistake `perf`'s `measure` records having made."
  ^double [f ^long n]
  (dotimes [_ 2000] (f))
  (let [[_ ns] (timed (dotimes [_ n] (f)))]
    (/ (double ns) n)))

(defn- best-of
  "`build` run `reps` times over a KB each `setup` builds fresh, answering the **fastest**
  `[ns derived]`.  Best rather than mean, for `perf`'s reason: a GC pause landing in one
  window is not a cost, and the run that avoided one is the one describing the code."
  [^long reps setup load! derived-fn]
  (reduce (fn [best _]
            (let [kb     (setup)
                  [_ ns] (timed (load! kb))
                  d      (long (derived-fn kb))]
              (if (or (nil? best) (< ns (long (first best)))) [ns d] best)))
          nil
          (range (max 1 reps))))

(defn- counting-calls
  "`{:total :costly :spent :elapsed}` for one extra repetition of the workload with each
  var in `vars` redefined to count and time itself: every call, the ones `costly?`
  admits, the nanoseconds spent inside those, and how long the whole repetition took.
  Several vars because one read may be served through more than one entry point, and a
  figure that covered some of them would understate the read rather than measure it.  A
  caller resolving an entry point by name (`ns-resolve`) rather than naming it with `#'`
  can hand this the same list against a revision that does not have it yet, which is what
  makes a before-and-after ratio one harness's rather than two.

  **`:spent` is only ever compared against `:elapsed`**, never against the clean run's
  wall clock.  A redefined var is not directly linked and every call through it pays an
  `apply` and two `swap!`s, so this repetition is slower than the run beside it — enough
  that reading a share off one and a total off the other puts the part above the whole,
  which is how this first read.  The share is a ratio inside one run; the absolute
  µs/derivation is the *other* run's, unobserved.

  The `costly?` split is the second half of the same discipline.  Both reads have a fast
  path that skips the work being measured — `excepted-handles` returns `#{}` for a
  variable view context, which is the one forward chaining's own join asks at, and
  `est-matches` reaches the subtype fan only for a unary type literal — so charging
  every call at the slow rate overstates both."
  ([vars costly? f] (counting-calls vars costly? (fn [r _] r) f))
  ([vars costly? charge f]
   (let [total   (atom 0)
         costly  (atom 0)
         spent   (atom 0)
         elapsed (volatile! 0)
         charge! #(swap! spent + %)
         wrap    (fn [v]
                   (let [orig @v]
                     (fn [& args]
                       (swap! total inc)
                       (if (apply costly? args)
                         (let [t0 (System/nanoTime)
                               r  (apply orig args)]
                           (swap! costly inc)
                           (swap! spent + (- (System/nanoTime) t0))
                           ;; a read that answers with a *closure* has done only part of
                           ;; its work by the time it returns; `charge` hands the rest
                           ;; back to this tally instead of leaving it on whoever calls
                           ;; the closure, where it would read as the caller's own cost
                           (charge r charge!))
                         (apply orig args)))))]
     (with-redefs-fn (into {} (map (juxt identity wrap)) vars)
       (fn [] (let [[_ ns] (timed (f))] (vreset! elapsed ns))))
     {:total @total :costly @costly :spent @spent :elapsed @elapsed})))

;; ---- arm 1: excepted-handles per placement -------------------------------

(def ^:private leaf-ctx 'CxHotLeaf)
(def ^:private mid-ctx  'CxHotMid)
(def ^:private base-ctx 'CxHotBase)

(defn- build-contexts! [kb]
  (doseq [[sub super] [[base-ctx 'CxCore] [mid-ctx base-ctx] [leaf-ctx mid-ctx]]]
    (v/assert kb (list 'genlCx sub super) 'CxCore {:chain? false})))

(defn- build-excepts!
  "`e` believed `(except (sentexHandle H))` facts, each hiding a **decoy** — a fact no
  rule below reads.  Asserted in `base-ctx`, which the leaf sees, so every one survives
  the visibility filter and the read pays for all `e`: the worst case for the walk, and
  the honest one to measure, since a KB that excepts anything at all excepts it from
  somewhere its readers can see."
  [kb ^long e]
  (v/with-deferred-settle kb
    (dotimes [i e]
      (let [h (v/assert kb (list 'hr_decoy (symbol (str "HrDecoy" i))) leaf-ctx
                        {:chain? false :strength :monotonic})]
        (v/assert kb (list 'except (sx/sentex-handle h)) base-ctx
                  {:chain? false :strength :monotonic})))))

(defn- except-kb
  "A KB carrying `e` excepts and a forward 2-join over `hrEdge`, with nothing loaded."
  [^long e]
  (let [kb (fresh-kb)]
    (build-contexts! kb)
    (build-excepts! kb e)
    (v/assert-rule kb ['(hrEdge ?x ?y) '(hrEdge ?y ?z)] '(hrPath ?x ?z) leaf-ctx
                   {:direction :forward})
    kb))

(defn- load-edges!
  "An `n`-by-`n` grid of `hrEdge` facts — every row a chain, so the 2-join derives one
  `hrPath` per interior link and the derivation count is a function of the grid alone."
  [kb ^long side]
  (v/with-deferred-settle kb
    (dotimes [i side]
      (dotimes [j side]
        (v/assert kb (list 'hrEdge
                           (symbol (str "HrA" i "X" j))
                           (symbol (str "HrA" i "X" (inc j))))
                  leaf-ctx)))))

(defn- except-row [^long e ^long facts ^long reps]
  (let [side            (long (Math/sqrt (double facts)))
        [ns drv]        (best-of reps #(except-kb e) #(load-edges! % side)
                                 #(p/count-with-functor (:index %) 'hrPath))
        ;; costly = a **concrete** view context, the only one that walks: the join
        ;; forward chaining runs itself asks at `'?ctx`, where the answer is empty by
        ;; construction and the read is a `variable?` test
        {:keys [total costly spent elapsed]}
        ;; both entry points: the set read, and the per-handle predicate the placement
        ;; path goes through (`chain/antecedent-hidden?`, `res/without-excepted`) — with
        ;; that predicate's own calls charged back here, since half its work happens
        ;; after it has returned
        (counting-calls (into [#'res/excepted-handles]
                              (keep #(ns-resolve 'vaelii.impl.resolution %))
                              '[hidden-fn])
                        (fn [_ view-context] (not (sx/variable? view-context)))
                        (fn [r charge!]
                          (if (fn? r)
                            (fn [h] (let [t0 (System/nanoTime)
                                          v  (r h)]
                                      (charge! (- (System/nanoTime) t0))
                                      v))
                            r))
                        #(load-edges! (except-kb e) side))
        kb              (except-kb e)]
    {:excepts e
     :hidden  (count (res/excepted-handles kb leaf-ctx))
     :derived drv
     :ms      (/ ns 1e6)
     :per-drv (/ (double ns) (max 1 drv) 1000.0)
     :calls   (/ (double total) (max 1 drv))
     :costly  (/ (double costly) (max 1 drv))
     :read-ns (/ (double spent) (max 1 costly))
     :share   (* 100.0 (/ (double spent) (max 1 elapsed)))}))

(defn- except-arm [{:keys [facts reps]}]
  (println "\n── excepted-handles ──────────────────────────────────────────────────────────")
  (println "  one believed (except (sentexHandle H)) per decoy, all visible from the reader;")
  (println "  the fact base and the rule are identical across rows, so only E moves.\n")
  (println (format "  %8s %8s %9s %11s %14s %9s %9s %10s %9s"
                   "excepts" "hidden" "derived" "load ms" "µs/derivation"
                   "reads/d" "walks/d" "ns/walk" "share"))
  (println (str "  " (apply str (repeat 96 \-))))
  ;; a discarded row first, because the first row of an arm is a cold one and the rows
  ;; are meant to be read against each other: without this the E=0 baseline carries the
  ;; JVM's warmup and every row after it reads faster than the one above for that reason
  ;; alone — which is how a run shows 1,000 excepts costing less than none
  (except-row 100 facts 1)
  (let [rows (mapv #(except-row % facts reps) [0 1 10 100 1000])]
    (doseq [{:keys [excepts hidden derived ms per-drv calls costly read-ns share]} rows]
      (println (format "  %8d %8d %9d %11.1f %14.1f %9.2f %9.2f %10.0f %8.1f%%"
                       excepts hidden derived ms per-drv calls costly read-ns share)))
    (println (str "\n  `share` is the read's fraction of the run it was measured in, and the only\n"
                  "  column that may be read against a total; the µs/derivation beside it comes\n"
                  "  from the uninstrumented run and is the absolute figure."))
    rows))

;; ---- arm 2: est-matches over a subtype closure ---------------------------

(def ^:private est-ctx 'CxHotEst)

(defn- type-name
  "A type spelling the naming policy accepts: snake_case, so `hr_t7` and never `hrT7`,
  which is indistinguishable from a predicate."
  [i]
  (symbol (str "hr_t" i)))

(defn- tree-size
  "How many nodes a `depth`-level tree of `branching` children per node holds."
  ^long [^long depth ^long branching]
  (loop [d 0, acc 0, level 1]
    (if (= d depth) acc (recur (inc d) (+ acc level) (* level branching)))))

(defn- build-hierarchy!
  "A `genl` tree of `depth` levels and `branching` children per node, rooted at `hr_t0`
  — so `specs(hr_t0)` is the whole tree and `specs` of a leaf is one node."
  [kb ^long depth ^long branching]
  (v/assert kb (list 'genlCx est-ctx 'CxCore) 'CxCore {:chain? false})
  (v/with-deferred-settle kb
    (doseq [i (range 1 (tree-size depth branching))]
      (v/assert kb (list 'genl (type-name i) (type-name (quot (dec i) branching)))
                est-ctx {:chain? false}))))

(defn- est-kb
  "The hierarchy, plus the rule whose broad unary antecedent fans over it.  `rule?` is
  false for no rule, `:backward` for one a query has to expand, anything else for the
  forward one a load fires."
  [^long depth ^long branching rule?]
  (let [kb (fresh-kb)]
    (build-hierarchy! kb depth branching)
    (when rule?
      (v/assert-rule kb ['(hr_t0 ?x) '(hrRel ?x ?y) '(hr_tag ?y)] '(hrOut ?x ?y)
                     est-ctx {:direction (if (= :backward rule?) :backward :forward)}))
    kb))

(defn- load-instances!
  "`n` instances, each typed at a **leaf** of the hierarchy, linked and tagged so the
  rule's other two antecedents match — the shape whose planning cost the broad first
  antecedent dominates."
  [kb n leaf0 leaves opts]
  (v/with-deferred-settle kb
    (dotimes [i n]
      (v/assert kb (list (type-name (+ leaf0 (mod i (max 1 leaves))))
                         (symbol (str "HrI" i)))
                est-ctx opts)
      (v/assert kb (list 'hrRel (symbol (str "HrI" i)) (symbol (str "HrJ" i)))
                est-ctx opts)
      (v/assert kb (list 'hr_tag (symbol (str "HrJ" i))) est-ctx opts))))

(defn- est-arm [{:keys [depth branching samples facts reps]}]
  (println "\n── est-matches over a unary antecedent ───────────────────────────────────────")
  (println "  one reduce over specs(T) per literal per pick, and `order` picks every")
  (println "  remaining literal on every pick.  tax/specs is memoized on the taxonomy")
  (println "  generation, so the fetch is O(1) and the walk over it is not.\n")
  (println (format "  %6s %8s %9s %14s %14s %11s %13s %10s"
                   "depth" "types" "|specs|" "ns/est-matches" "ns/order"
                   "µs/deriv" "fans/d" "share"))
  (println (str "  " (apply str (repeat 96 \-))))
  (doseq [d (range 2 (inc (long depth)))]
    (let [types  (tree-size d branching)
          leaves (long (Math/pow branching (dec d)))
          leaf0  (- types leaves)
          kb     (est-kb d branching false)
          _      (load-instances! kb facts leaf0 leaves {:chain? false})
          specs  (count (tax/specs (reasoning/taxonomy kb) (type-name 0) est-ctx))
          est-ns (per-call #(plan/est-matches kb '(hr_t0 ?x) #{} {:context est-ctx})
                           samples)
          ord-ns (per-call #(plan/order kb ['(hr_t0 ?x) '(hrRel ?x ?y) '(hr_tag ?y)]
                                        est-ctx {})
                           (max 200 (quot (long samples) 10)))
          [ns drv] (best-of reps #(est-kb d branching true)
                            #(load-instances! % facts leaf0 leaves nil)
                            #(p/count-with-functor (:index %) 'hrOut))
          ;; costly = the broad unary literal, the only goal shape that fans over a
          ;; subtype closure; a binary antecedent walks the trie once and is not this
          {:keys [total costly spent elapsed]}
          (counting-calls [#'plan/est-matches]
                          ;; the variable is renamed by the time a firing's plan asks,
                          ;; so the functor is the test and not the literal
                          (fn [_ goal & _] (and (sequential? goal)
                                                (= 'hr_t0 (first goal))))
                          #(load-instances! (est-kb d branching true)
                                            facts leaf0 leaves nil))
          per-d  (/ (double ns) (max 1 drv) 1000.0)
          per-c  (/ (double costly) (max 1 drv))]
      (println (format "  %6d %8d %9d %14.0f %14.0f %11.1f %6.2f/%-6.2f %9.1f%%"
                       d types specs est-ns ord-ns per-d
                       per-c (/ (double total) (max 1 drv))
                       (* 100.0 (/ (double spent) (max 1 elapsed)))))))
  (println (str "\n  `fans/d` is broad-literal calls per derivation over all est-matches calls.\n"
                "  A plan's own `memoizing` collects the repeats *within* one plan — the first\n"
                "  pick fans and the other two hit its cache — so the share is one fan per plan.\n"
                "  For an open atom argument that fan is `count-at [t']` per subtype and is read\n"
                "  as such; any deeper prefix takes the general walk (`plan.clj`).")))

;; ---- arm 3: which path the fan is worth anything on ----------------------
;;
;; The fan above is a per-plan cost, and the obvious answer to a per-plan cost is to
;; remember it.  Whether that is worth doing turns on **which path asks**, so this arm
;; puts the same rule set under forward chaining and under a backward query and reports
;; what the fan costs each.
;;
;; They come out opposite, and that is the finding.  Chaining pays it — and moves the
;; change clock per placement, so a clock-stamped memo is retired between one plan and
;; the next.  A query never moves the clock, so a memo would be served every time — and
;; there the fan is a rounding error against the search around it.  `plan.clj`'s "Why
;; the subtype fan is not memoized across plans" is these two numbers.

(defn- fan-share
  "`{:costly :spent :elapsed}` for the broad literal's estimates inside one run of
  `work` over a KB `setup` builds."
  [setup work]
  (counting-calls [#'plan/est-matches]
                  (fn [_ goal & _] (and (sequential? goal) (= 'hr_t0 (first goal))))
                  #(work (setup))))

(defn- path-arm [{:keys [depth branching facts]}]
  (println "\n── which path pays for the fan ───────────────────────────────────────────────")
  (println "  the same rule set, chained forward and asked backward.\n")
  (println (format "  %-30s %6s %9s %11s %9s %8s"
                   "path" "depth" "|specs|" "run ms" "fans" "share"))
  (println (str "  " (apply str (repeat 78 \-))))
  (doseq [d [(max 2 (- (long depth) 2)) (long depth)]]
    (let [leaves (long (Math/pow branching (dec d)))
          leaf0  (- (tree-size d branching) leaves)
          specs  (let [kb (est-kb d branching false)]
                   (count (tax/specs (reasoning/taxonomy kb) (type-name 0) est-ctx)))
          rows   [["forward chaining (writes)"
                   (fan-share #(est-kb d branching true)
                              #(load-instances! % facts leaf0 leaves nil))]
                  ["backward query (does not)"
                   (fan-share (fn []
                                (let [kb (est-kb d branching :backward)]
                                  (load-instances! kb facts leaf0 leaves {:chain? false})
                                  kb))
                              (fn [kb] (dotimes [_ 40]
                                         (count (v/prove kb '[(hrOut ?a ?b)] est-ctx)))))]]]
      (doseq [[label {:keys [costly spent elapsed]}] rows]
        (println (format "  %-30s %6d %9d %11.1f %9d %7.1f%%"
                         label d specs (/ (double elapsed) 1e6) costly
                         (* 100.0 (/ (double spent) (max 1 elapsed))))))))
  (println (str "\n  A memo stamped on the change clock is retired by a placement, so it reaches the\n"
                "  first line never and the second where there is nothing to take.  Both readings\n"
                "  are inside one instrumented run, as everywhere else here.")))

;; ---- driver --------------------------------------------------------------

(defn- parse-args [args]
  (reduce (fn [m [k v]] (assoc m (keyword (subs k 2)) (Long/parseLong v)))
          defaults
          (partition 2 args)))

(defn -main [& args]
  (let [opts (parse-args args)]
    (println "vaelii hot reads — two per-firing costs the growth gate cannot see")
    (println (format "opts: %s" (pr-str opts)))
    (except-arm opts)
    (est-arm opts)
    (path-arm opts)
    (println))
  (shutdown-agents)
  (System/exit 0))
