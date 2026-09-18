;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.subgoal
  "Would a **cross-query subgoal table** pay?  The census that answers it, and the replay
  that prices it.

  `res/matches-visible` answers survive a query in a clock-stamped per-KB cache
  (`literal-cache`); `provers/solve-goal` answers do not.  The asymmetry is deliberate and
  its reason is written down — a solve is dependent on the prover set that answered it,
  because `ask-capped` drops provers above a cost tier — so a table would have to carry
  that set in its key.  What no argument settles is whether such a table would ever be
  *hit*, and that is a measurement over a real question sequence rather than a claim.

  **The sequence**, four arms, in the order a reader meets them:

    A  the fables' question set — `vaelii.world`'s cast and the four Aesop stories, asked
       the way `stories_test` asks them (`sentexes-matching`, `ask?`, `isa?`, `why-not`);
    B  the starter KB's worked examples (`browser/examples`), one `examples/run` each, which
       is what a render of the commonsense gallery does;
    C  the rule-expanding half — `query` at a depth, `prove`, `escalate` climbing to
       level 7 — the path whose leaf is the registry and which therefore drives
       `solve-goal` per literal per binding rather than once per ask;
    D  one render of the inference debugger — `search-tree` plus `compare-tacticians`,
       which runs the *same* goal once per tactician.

  **The census** counts every `provers/solve-goal-with` invocation by
  `[canonical goal, context, prover set]` and splits the repeats three ways: repeats
  inside one API call (which nothing serves today — the node engine's claimed-key set
  drops a node before it reaches the leaf, so what is counted here is already
  post-dedup), repeats across API calls, and repeats across API calls **under an unmoved
  change clock**, which is the only kind a clock-stamped table could serve.

  **The replay** prices it: a prototype table — clock-stamped, keyed the same way, storing
  only a completed realization (`literal-cache/storing`, so a bounded run leaves no
  prefix behind) — switched on and off in one JVM with the two arms interleaved, at three
  workloads.  Numbers are comparable **within this harness only**: a hand-rolled `lein
  run` bench does not reach the JIT level a long-lived server does, so the ratio is the
  reading and the millisecond count is not.

  The answers are compared off and on at the end, because a cache that changes an answer
  has not been measured, it has been broken.

  Run: `lein bench-subgoal`            — the census and all three replay workloads
       `lein bench-subgoal census`     — the census alone
       `lein bench-subgoal replay [n]` — the replay alone, `n` interleaved repetitions"
  (:require [clojure.string :as str]
            [clojure.walk :as walk]
            [vaelii.core :as v]
            [vaelii.impl.caches :as caches]
            [vaelii.host.core-context :as core-context]
            [vaelii.browser.examples :as examples]
            [vaelii.impl.literal-cache :as lc]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.provers :as provers]
            [vaelii.browser.sandbox :as sandbox]
            [vaelii.host.starter :as starter]
            [vaelii.koinii.channel :as ch]
            [vaelii.koinii.dispute :as d]
            [vaelii.koinii.identity :as id]
            [vaelii.koinii.speech-acts :as sa]
            [vaelii.world :as world])
  (:import [java.util ArrayList]
           [java.util.concurrent.atomic AtomicLong]))

;; ---- the extension point ------------------------------------------------------------
;; One wrapper around the registry's dispatch, installed once, doing whichever of the two
;; jobs is switched on.  `solve-goal-with` rather than `solve-goal`, because it is the
;; single choke point: `solve-goal` passes the whole registry, `ask-capped` passes a
;; cost-capped subset, and level 5 passes the transitive provers alone.

(def ^:private ^ArrayList census (ArrayList.))   ; [call-ordinal key clock]
(def ^:private counting (volatile! nil))         ; nil = off, else the call ordinal
(def ^:private tabling (volatile! false))

(def ^:private table (atom {}))
(def ^:private ^AtomicLong hits (AtomicLong. 0))
(def ^:private ^AtomicLong misses (AtomicLong. 0))

(def ^:private table-limit
  "The bound the prototype takes, which is `literal-cache`'s — the same wholesale clear,
  so the two would compete for memory on the same terms."
  4096)

(defn- prover-set-key
  "What tells one prover list from another.  Identity against the KB's own registry is
  the common case and costs a pointer compare; a filtered list falls back to its class
  names, which is what a real key would have to carry."
  [kb prs]
  (if (identical? prs (provers/registry kb))
    :all
    (mapv #(.getSimpleName (class %)) prs)))

(defn- storing
  "`xs`, with the realized answer handed to `store!` at the moment the source runs dry —
  and never if the consumer stops first.  `literal-cache/storing`, restated here because
  a prototype that stored a truncated prefix would measure a table nobody would ship."
  [store! xs]
  (let [acc (volatile! [])]
    ((fn step [s]
       (lazy-seq
        (if-let [c (seq s)]
          (do (vswap! acc conj (first c))
              (cons (first c) (step (rest c))))
          (do (store! @acc) nil))))
     xs)))

(defn- tabled
  "`f`'s answer for `goal`, through the prototype table."
  [f kb prs goal context]
  (let [[canon rename] (lc/canonicalize goal)
        k    [canon context (prover-set-key kb prs)]
        now  (observe/change-clock)
        hit  (get @table k)]
    (if (and hit (== now (long (:clock hit))))
      (do (.incrementAndGet hits)
          (map #(lc/rename-bindings rename %) (:value hit)))
      (do (.incrementAndGet misses)
          (->> (f kb prs canon context)
               (storing (fn [vs]
                          (when (== (observe/change-clock) now)
                            (swap! table caches/assoc-bounded table-limit
                                   k {:clock now :value vs}))))
               (map #(lc/rename-bindings rename %)))))))

(defn- install!
  "Wrap the registry's dispatch.  Idempotent by construction — called once from `-main`,
  never at load, so requiring this namespace changes nothing about the engine."
  []
  (alter-var-root
   #'provers/solve-goal-with
   (fn [f]
     (fn [kb prs goal context]
       (when-let [n @counting]
         (.add census [n [(first (lc/canonicalize goal)) context (prover-set-key kb prs)]
                       (observe/change-clock)]))
       (if @tabling
         (tabled f kb prs goal context)
         (f kb prs goal context))))))

;; ---- the KB --------------------------------------------------------------

(defn- build-kb
  "The starter schema, the test-world (the cast and the four fables), and every worked
  example's premises written into one sandbox — the KB a reader of the browser has in
  front of them once they have clicked through the gallery."
  []
  (let [kb  (v/open-kb {:backend :memory :space 42 :recover? false})
        _   (starter/load-into kb)
        _   (world/load-into kb)
        cx  (sandbox/context-for (sandbox/mint-token))]
    (doseq [e examples/examples] (examples/establish! kb e cx))
    [kb cx]))

;; ---- the sequence --------------------------------------------------------

(defn- arm-a
  "The fables' question set, in the order `stories_test` asks it."
  [kb _cx]
  [#(v/sentexes-matching kb '(locatedIn Engine1 Garage1) 'CxNaturalWorld)
   #(v/sentexes-matching kb '(locatedIn Piston1 Garage1) 'CxNaturalWorld)
   #(v/ask? kb '(locatedIn Engine1 House1) 'CxNaturalWorld)
   #(v/ask? kb '(locatedIn Piston1 House1) 'CxNaturalWorld)
   #(v/sentexes-matching kb '(owns Tom Roof1) 'CxSocialWorld)
   #(v/sentexes-matching kb '(owns Tom Chimney1) 'CxSocialWorld)
   #(v/sentexes-matching kb '(owns Tom Engine1) 'CxSocialWorld)
   #(v/sentexes-matching kb '(owns Tom Engine1) 'CxNaturalWorld)
   #(v/sentexes-matching kb '(physical_object Roof1) '?ctx)
   #(v/ask? kb '(physical_object Roof1))
   #(v/isa? kb 'LionA 'mammal)
   #(v/isa? kb 'MouseA 'animal)
   #(v/isa? kb 'TortoiseA 'reptile)
   #(v/isa? kb 'AntA 'insect)
   #(v/isa? kb 'BoyA 'person)
   #(v/isa? kb 'WolfA 'mammal)
   #(v/sentexes-matching kb '(repaidKindness MouseA LionA) 'CxLionMouse)
   #(v/sentexes-matching kb '(repaidKindness LionA MouseA) 'CxLionMouse)
   #(v/sentexes-matching kb '(wins TortoiseA HareA) 'CxTortoiseHare)
   #(v/sentexes-matching kb '(wins HareA TortoiseA) 'CxTortoiseHare)
   #(v/sentexes-matching kb '(survives_winter AntA) 'CxAntGrasshopper)
   #(v/sentexes-matching kb '(suffers_in_winter GrasshopperA) 'CxAntGrasshopper)
   #(v/sentexes-matching kb '(betterPreparedThan AntA GrasshopperA) 'CxAntGrasshopper)
   #(v/sentexes-matching kb '(believed BoyA) 'CxCriedWolf)
   #(v/sentexes-matching kb '(not (believed BoyA)) 'CxCriedWolf)
   #(v/why-not kb '(believed BoyA) 'CxCriedWolf)
   #(v/sentexes-matching kb '(in_danger BoyA) 'CxCriedWolf)
   #(v/sentexes-matching kb '(in_danger WolfA) 'CxCriedWolf)
   #(v/sentexes-matching kb '(mortal LionA) 'CxLionMouse)
   #(v/sentexes-matching kb '(flies WolfA) '?ctx)
   #(v/sentexes-matching kb '(flies HareA) '?ctx)
   #(v/isa? kb 'lion 'unary_predicate)
   #(v/isa? kb 'mouse 'unary_predicate)
   #(v/isa? kb 'hare 'unary_predicate)
   #(v/isa? kb 'wolf 'unary_predicate)
   #(v/isa? kb 'tortoise 'unary_predicate)
   #(v/isa? kb 'ant 'unary_predicate)
   #(v/isa? kb 'grasshopper 'unary_predicate)
   #(v/isa? kb 'spared 'binary_predicate)
   #(v/isa? kb 'repaidKindness 'binary_predicate)
   #(v/isa? kb 'in_danger 'unary_predicate)
   #(v/isa? kb 'cries_wolf 'unary_predicate)
   #(v/sentexes-matching kb '(achievesGoal FoxF HasCheese) 'CxFoxCrow)
   #(v/sentexes-matching kb '(achievesGoal TortoiseA WinRace) 'CxTortoiseHare)
   #(v/sentexes-matching kb '(achievesGoal FoxF HasCheese) 'CxTortoiseHare)
   #(v/sentexes-matching kb '(achievesGoal FoxF HasCheese) 'CxUniverse)
   #(v/ask? kb '(achievesGoal CrowF HasCheese) 'CxFoxCrow)
   #(v/sentexes-matching kb '(responsibleFor FoxF CrowSings) 'CxFoxCrow)
   #(v/ask? kb '(causes Flatter1 FoxGetsCheese))
   #(v/ask? kb '(causes FoxGetsCheese Flatter1))
   #(v/ask? kb '(beforeEvent Flatter1 FoxGetsCheese))
   #(v/ask? kb '(beforeEvent FoxGetsCheese Flatter1))
   #(v/ask? kb '(afterEvent CrowSings Flatter1))
   #(v/ask? kb '(afterEvent FoxGetsCheese Flatter1))
   #(v/sentexes-matching kb '(event CheeseFalls) '?ctx)
   #(v/ask? kb '(event CheeseFalls))
   #(v/isa? kb 'Flatter1 'event)
   #(v/isa? kb 'FoxF 'agent)
   #(v/isa? kb 'causes 'transitive)
   #(v/isa? kb 'achievesGoal 'binary_predicate)
   #(v/isa? kb 'responsibleFor 'binary_predicate)])

(defn- arm-b
  "One `examples/run` per worked example — a render of the commonsense gallery."
  [kb cx]
  (mapv (fn [e] #(examples/run kb e cx)) examples/examples))

(defn- arm-c
  "The rule-expanding half: a depth-bounded `query`, `prove`, and `escalate` climbing
  past the registry into level 7."
  [kb cx]
  [#(v/query kb '(causes Flatter1 ?y) 'CxFoxCrow {:max-depth 3})
   #(v/query kb '(causes ?x ?y) 'CxFoxCrow {:max-depth 3})
   #(v/query kb '(beforeEvent ?x ?y) 'CxFoxCrow {:max-depth 3})
   #(v/query kb '(afterEvent ?x ?y) 'CxFoxCrow {:max-depth 3})
   #(v/query kb '(achievesGoal ?a ?g) 'CxFoxCrow {:max-depth 3})
   #(v/query kb '(in_danger ?x) 'CxCriedWolf {:max-depth 3})
   #(v/query kb '(locatedIn ?p House1) 'CxNaturalWorld {:max-depth 3})
   #(v/query kb '(owns Tom ?x) 'CxSocialWorld {:max-depth 3})
   #(v/query kb '(mortal ?x) 'CxLionMouse {:max-depth 3})
   #(v/query kb '(repaidKindness ?a ?b) 'CxLionMouse {:max-depth 3})
   #(v/query kb '[(causes ?x ?y) (beforeEvent ?x ?y)] 'CxFoxCrow {:max-depth 3})
   #(v/prove kb '(in_danger ?x) 'CxCriedWolf)
   #(v/prove kb '(betterPreparedThan ?a ?b) 'CxAntGrasshopper)
   #(v/escalate kb '(causes Flatter1 FoxGetsCheese) 'CxFoxCrow)
   #(v/escalate kb '(in_danger BoyA) 'CxCriedWolf)
   #(v/escalate kb '(grandparentOf AdaEx CalEx) cx)
   #(v/explain-levels kb '(in_danger BoyA) 'CxCriedWolf)])

(defn- arm-d
  "One render of the inference debugger.  `compare-tacticians` asks one goal once per
  tactician, so this arm is where a single API call repeats a subgoal most."
  [kb _cx]
  [#(v/search-tree kb '(causes ?x ?y) 'CxFoxCrow {:max-depth 3})
   #(v/compare-tacticians kb '(causes ?x ?y) 'CxFoxCrow {:max-depth 3})
   #(v/search-tree kb '(in_danger ?x) 'CxCriedWolf {:max-depth 3})
   #(v/compare-tacticians kb '(in_danger ?x) 'CxCriedWolf {:max-depth 3})])

(defn- arms [kb cx]
  [["A  fables + story questions"   (arm-a kb cx)]
   ["B  commonsense examples"       (arm-b kb cx)]
   ["C  rule-expanding queries"     (arm-c kb cx)]
   ["D  inference-debugger render"  (arm-d kb cx)]])

(defn- sequence-of [kb cx] (into [] (mapcat second) (arms kb cx)))

(defn- run-once!
  "One pass of `qs`, every lazy answer realized so nothing is left unpaid for."
  [qs]
  (let [out (ArrayList.)]
    (doseq [f qs] (.add out (let [r (f)] (if (seq? r) (doall r) r))))
    out))

;; ---- the census ----------------------------------------------------------

(defn- analyse
  "Solve counts over `[call-ordinal key clock]` triples.

  `:within` is the repeats inside one API call; `:cross` the first solve of a key in a
  call that an *earlier* call already solved; `:cross-clock` the subset of those whose
  earlier solve ran under the same change clock — the only ones a clock-stamped table
  could serve."
  [entries]
  (let [by-call (sort-by first (group-by first entries))
        within  (reduce + (map (fn [[_ es]]
                                 (- (count es) (count (into #{} (map second) es))))
                               by-call))]
    (loop [cs by-call, seen {}, cross 0, cross-clock 0]
      (if-let [[_ es] (first cs)]
        (let [firsts (reduce (fn [m e] (if (contains? m (second e))
                                         m
                                         (assoc m (second e) (nth e 2))))
                             {} es)]
          (recur (rest cs) (merge seen firsts)
                 (+ cross (count (filter (fn [[k _]] (contains? seen k)) firsts)))
                 (+ cross-clock (count (filter (fn [[k c]] (= (get seen k ::none) c)) firsts)))))
        {:calls (count by-call)
         :solves (count entries)
         :distinct (count (into #{} (map second) entries))
         :within within
         :cross cross
         :cross-clock cross-clock}))))

(defn- pct ^double [n d] (if (zero? (long d)) 0.0 (* 100.0 (/ (double n) (long d)))))

(defn- census-row [label a]
  (println (format "  %-30s %5d %7d %8d %7d %6.1f%% %7d %6.1f%% %7d %6.1f%%"
                   label (:calls a) (:solves a) (:distinct a)
                   (:within a) (pct (:within a) (:solves a))
                   (:cross a) (pct (:cross a) (:solves a))
                   (:cross-clock a) (pct (:cross-clock a) (:solves a)))))

(defn- run-census!
  "Count the solves the sequence performs, arm by arm — then again over a second,
  identical pass, which is the ceiling a table could reach and not a workload."
  [kb cx]
  (let [as   (arms kb cx)
        seqn (sequence-of kb cx)]
    (run-once! seqn)                                    ; warm: classes, caches, closures
    (.clear census)
    (let [bounds (loop [as as, i 0, out []]
                   (if-let [[label qs] (first as)]
                     (recur (rest as) (+ i (count qs)) (conj out [label i (+ i (count qs))]))
                     out))
          n      (count seqn)]
      (loop [i 0] (when (< i n)
                    (vreset! counting i)
                    (let [r ((nth seqn i))] (when (seq? r) (doall r)))
                    (vreset! counting nil)
                    (recur (inc i))))
      (loop [i 0] (when (< i n)
                    (vreset! counting (+ n i))
                    (let [r ((nth seqn i))] (when (seq? r) (doall r)))
                    (vreset! counting nil)
                    (recur (inc i))))
      (let [all (vec census)
            p1  (filterv #(< (long (first %)) n) all)
            p2  (filterv #(>= (long (first %)) n) all)]
        (println)
        (println "=== census: solve-goal invocations by [canonical goal, context, prover set] ===")
        (println (format "  %-30s %5s %7s %8s %15s %15s %15s"
                         "" "calls" "solves" "distinct" "within" "cross" "cross@clock"))
        (doseq [[label lo hi] bounds]
          (census-row label (analyse (filterv #(and (<= (long lo) (long (first %)))
                                                    (< (long (first %)) (long hi)))
                                              p1))))
        (println (str "  " (apply str (repeat 100 \-))))
        (census-row "the sequence, once" (analyse p1))
        (census-row "the same sequence again" (analyse p2))
        (census-row "both passes together" (analyse all))
        (println)
        (println "  prover sets seen:"
                 (->> all
                      (into #{} (map (fn [e] (nth (second e) 2))))
                      (map (fn [s] (if (= :all s)
                                     "the whole registry"
                                     (str (count s) " provers"))))
                      sort
                      (str/join ", ")))
        (println "  change clock, first solve / last:"
                 (nth (first all) 2) "/" (nth (peek all) 2))
        (println)
        (println "  most-repeated keys, both passes:")
        (doseq [[k c] (take 8 (sort-by (comp - val) (frequencies (map second all))))]
          (println (format "    %5d  %s" c (pr-str k))))))))

;; ---- the koinii conversation ---------------------------------------------

(defn- run-koinii!
  "The fifth arm, reported apart because it has a KB of its own and because its shape is
  the point: a koinii conversation **interleaves writes with reads**.  Every speech act is
  an assert, so the change clock moves between one read and the next, and a clock-stamped
  table meets each read empty however much the reads repeat.  The roommates' emergent
  argument from `koinii_roommates_test`, minus the wire."
  []
  (let [kb       (doto (v/open-kb {:backend :memory :space 43 :recover? false})
                   (core-context/load-into)
                   (sa/load-speech-acts))
        proposal (list 'shouldAdopt 'Apartment 'Dog)
        rules    [(list 'implies (list 'wants_companionship '?p) (list 'wouldEnjoy '?p 'Dog))
                  (list 'implies (list 'and (list 'memberOf '?p 'Apartment)
                                       (list 'wouldEnjoy '?p 'Dog))
                        proposal)
                  (list 'implies (list 'allergicTo '?p 'DogDander) (list 'harmedBy '?p 'Dog))
                  (list 'implies (list 'and (list 'memberOf '?p 'Apartment)
                                       (list 'harmedBy '?p 'Dog))
                        (list 'not proposal))]]
    (binding [id/*policy* :proof-tier]
      (let [ava  (ch/join (ch/local kb) 'CxApartment 'AgentAva)
            ben  (ch/join (ch/local kb) 'CxApartment 'AgentBen)
            steps
            [[:write #(doseq [r rules] (v/assert kb r 'CxApartment))]
             [:write #(ch/assert ava (list 'memberOf 'AgentAva 'Apartment))]
             [:read  #(v/ask? kb proposal 'CxApartment)]
             [:write #(ch/assert ava (list 'wants_companionship 'AgentAva))]
             [:read  #(v/ask? kb proposal 'CxApartment)]
             [:read  #(v/ask? kb (list 'not proposal) 'CxApartment)]
             [:write #(ch/assert ben (list 'memberOf 'AgentBen 'Apartment))]
             [:read  #(v/ask? kb proposal 'CxApartment)]
             [:write #(ch/assert ben (list 'allergicTo 'AgentBen 'DogDander))]
             [:read  #(v/ask? kb proposal 'CxApartment)]
             [:read  #(v/ask? kb (list 'not proposal) 'CxApartment)]
             [:read  #(d/disputes-in kb 'CxApartment)]
             [:read  #(v/sentexes-matching kb (list 'not proposal) 'CxApartment)]
             [:read  #(v/why-not kb proposal 'CxApartment)]
             [:read  #(v/ask? kb proposal 'CxApartment)]]]
        (.clear census)
        (let [clocks (volatile! [])]
          (loop [i 0, ss steps]
            (when-let [[kind f] (first ss)]
              (when (= :read kind) (vreset! counting i))
              (let [r (f)] (when (seq? r) (doall r)))
              (vreset! counting nil)
              (vswap! clocks conj [kind (observe/change-clock)])
              (recur (inc i) (rest ss))))
          (let [all    (vec census)
                reads  (filterv #(= :read (first %)) @clocks)
                moves  (count (distinct (map second reads)))]
            (println)
            (println "=== the koinii arm: a conversation, reported apart ===")
            (println (format "  %-30s %5s %7s %8s %15s %15s %15s"
                             "" "calls" "solves" "distinct" "within" "cross" "cross@clock"))
            (census-row "E  koinii conversation" (analyse all))
            (println (format "  %d reads, over %d distinct change-clock values — a read shares a clock"
                             (count reads) moves))
            (println "  with an earlier read only where no speech act fell between them.")))))))

;; ---- the replay ----------------------------------------------------------

(defn- tick!
  "One assert and its retraction — the mutation a live KB performs between reads, and
  the whole of what a coarse change clock needs to see.  Taken back, so no answer moves."
  [kb n]
  (v/retract! kb (v/assert kb (list 'cries_wolf (symbol (str "ClockTickBench" n))) 'CxCriedWolf)))

(defn- time-runs! ^double [qs n between]
  (let [t0 (System/nanoTime)]
    (dotimes [i n] (run-once! qs) (between i))
    (/ (- (System/nanoTime) t0) 1e6)))

(defn- median [xs] (nth (sort xs) (quot (count xs) 2)))

(defn- ab!
  "One A/B row: `runs` passes of the sequence per timed unit, `between` run in between,
  the two arms interleaved `reps` times.  The table is dropped before each ON unit, so no
  unit inherits the previous one's entries."
  [label qs runs between reps]
  (let [off (volatile! []) on (volatile! [])]
    (dotimes [_ reps]
      (vreset! tabling false)
      (vswap! off conj (time-runs! qs runs between))
      (vreset! tabling true)
      (reset! table {})
      (.set hits 0) (.set misses 0)
      (vswap! on conj (time-runs! qs runs between)))
    (vreset! tabling false)
    (let [o (median @off) t (median @on)
          h (.get hits) m (.get misses)]
      (println (format "  %-32s %8.1f %8.1f   %6.3fx   %6d / %6d  %5.1f%%"
                       label o t (/ (double o) (double t)) h (+ h m) (pct h (+ h m)))))))

(defn- comparable
  "The answers with the debugger's per-row wall clocks dropped — `compare-tacticians`
  reports `:ms` per tactician, which is a timing and not an answer."
  [xs]
  (walk/postwalk (fn [x] (if (map? x) (dissoc x :ms) x)) xs))

(defn- answers-of [qs]
  (comparable (mapv (fn [f] (let [r (f)] (if (seq? r) (vec r) r))) qs)))

(defn- run-replay! [kb cx reps]
  (let [qs (sequence-of kb cx)]
    (vreset! tabling false) (time-runs! qs 2 (fn [_]))     ; warm both arms
    (vreset! tabling true)  (time-runs! qs 2 (fn [_]))
    (vreset! tabling false) (reset! table {})
    (println)
    (println (format "=== replay: prototype table off vs on, %d interleaved repetitions, medians ===" reps))
    (println (format "  %-32s %8s %8s   %7s   %15s %6s"
                     "" "off ms" "on ms" "speedup" "table hits" ""))
    (ab! "one pass, each question once"    qs 1 (fn [_]) reps)
    (ab! "five passes, nothing written"    qs 5 (fn [_]) reps)
    (ab! "five passes, one write between"  qs 5 #(tick! kb %) reps)
    (let [_ (vreset! tabling false)
          a (answers-of qs)
          _ (vreset! tabling true)
          _ (reset! table {})
          b (answers-of qs)
          c (answers-of qs)]
      (vreset! tabling false)
      (println)
      (println "  answers identical, off vs on (cold table):" (= a b))
      (println "  answers identical, off vs on (warm table):" (= a c)))))

;; ---- the run -------------------------------------------------------------

(defn -main [& args]
  (let [mode (or (first args) "all")
        reps (or (some-> (second args) Long/parseLong) 7)]
    (install!)
    (println "vaelii cross-query subgoal tabling — the starter ontology plus the test-world")
    (println "ratios are readable within this harness only (see the namespace docstring)")
    (let [[kb cx] (build-kb)]
      (when (contains? #{"all" "census"} mode) (run-census! kb cx) (run-koinii!))
      (when (contains? #{"all" "replay"} mode) (run-replay! kb cx reps)))
    (shutdown-agents)))
