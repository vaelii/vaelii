;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.supporter-reach-test
  "Whether a stored supporter of a relation rests on a target of the stored `except`s and
  placed `defeat`s (`kb/supporter-reaches?`) is read at every scoped walk whose filter memo
  the change clock retired, so at every write.  The forward walk from the targets is held
  across writes (`kb/held-forward-reach`): a false is kept as the handles the walk read,
  and the next read walks on from the handles the touched sets recorded since, folded in
  at each settle exit (`kb/note-reach-touched!`).  Two things are held here.

  **The held answer is the fresh walk's.**  After every step of a stream of writes, on
  both networks, the reach read through the KB's memo equals the reach read with none.
  The stream gives the held walk every way to go wrong: a fact that completes a rule
  firing off the targets' closure and derives a supporter, under one deferred settle and
  across several settles with no read between them, a defeat placed on a new target, a
  removal of the fact that completed the firing and its return, and writes nowhere near
  the closure.  A defeat placed while the walk is held is walked on from, so a firing
  completed off its chain later is met.

  **It reads the closure once.**  Writes off the targets' closure leave the memo's entry
  standing and answer from it, so a read after a mint does not walk the closure again.
  A walk that met a supporter is held as the path it met it by, and a read after a write
  off that path checks the path rather than walking."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.except :as exc]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(def ^:private M {:strength :monotonic})
(def ^:private C 'CxPerf)

(defn- reach-kb
  "A KB with `k` defeated facts `(rsr_p0 rsr_cI)`, each the head of a forward chain
  `rsr_p0 → rsr_p1 → rsr_p2`, a rule deriving `(genl ?x rsr_top)` from `(rsr_p2 ?x)` and
  `(rsr_on ?x)`, and 4k `genl` supporters, so the reach walks forward from the targets."
  [opts k]
  (let [kb (tu/fresh opts)]
    (v/with-deferred-settle kb
      (v/assert kb '(genl rsr_top thing) C M)
      (dotimes [i (* 4 k)] (v/assert kb (list 'genl (symbol (str "rsr_g" i)) 'rsr_top) C M))
      (v/assert-rule kb '[(rsr_p0 ?x)] '(rsr_p1 ?x) C {:direction :forward})
      (v/assert-rule kb '[(rsr_p1 ?x)] '(rsr_p2 ?x) C {:direction :forward})
      (v/assert-rule kb '[(rsr_p2 ?x) (rsr_on ?x)] '(genl ?x rsr_top) C {:direction :forward})
      (dotimes [i k]
        (let [c (symbol (str "rsr_c" i))]
          (v/assert kb (list 'rsr_p0 c) C {})
          (v/assert kb (list 'not (list 'rsr_p0 c)) C M))))
    kb))

(defn- reach
  "The `genl` reach with the placed defeats counted, read through the KB's memo when
  `held?`, else walked afresh."
  [kb held?]
  (let [t    @(reasoning/taxonomy kb)
        sups (#'tax/supporter-summary t :genl)]
    (kb/supporter-reaches? kb (exc/supporter-entries kb) sups true
                           (when held? (:supporter-reach t)))))

(defn- memo-walks
  "How many times a read through the KB's memo walked from the targets."
  [kb]
  (:misses (caches/tally-map (caches/tally-of (:supporter-reach @(reasoning/taxonomy kb)) :T12))))

(defn- agrees [kb what]
  (let [fresh (reach kb false)]
    (is (= fresh (reach kb true)) what)
    fresh))

(defn- stream
  "The writes, each `[label f]`; `f` takes the KB."
  []
  (let [on  (fn [i] (list 'rsr_on (symbol (str "rsr_c" i))))
        off (fn [i] (list 'rsr_on (symbol (str "rsr_d" i))))]
    [["a fact off the closure" #(v/assert % (off 0) C {})]
     ["a fact completing a firing off a target's chain" #(v/assert % (on 1) C {})]
     ["its removal" #(v/retract! % (v/handle-of % (on 1) C))]
     ["three settles, the second completing a firing, no read between"
      (fn [kb] (v/assert kb (off 1) C {}) (v/assert kb (on 2) C {}) (v/assert kb (off 2) C {}))]
     ["its removal" #(v/retract! % (v/handle-of % (on 2) C))]
     ["a deferred settle completing a firing among facts off the closure"
      (fn [kb] (v/with-deferred-settle kb
                 (v/assert kb (off 3) C {}) (v/assert kb (on 3) C {}) (v/assert kb (off 4) C {})))]
     ["its removal" #(v/retract! % (v/handle-of % (on 3) C))]
     ["a defeat placed on a fresh chain's head"
      (fn [kb] (v/with-deferred-settle kb
                 (v/assert kb '(rsr_p0 rsr_e1) C {})
                 (v/assert kb '(not (rsr_p0 rsr_e1)) C M)))]
     ["a fact completing a firing off the new target's chain" #(v/assert % '(rsr_on rsr_e1) C {})]
     ["its removal" #(v/retract! % (v/handle-of % '(rsr_on rsr_e1) C))]
     ["a fact on a chain no defeat targets yet" (fn [kb]
                                                  (v/assert kb '(rsr_p0 rsr_e0) C {})
                                                  (v/assert kb '(rsr_on rsr_e0) C {}))]
     ["a defeat placed on that chain's head" #(v/assert % '(not (rsr_p0 rsr_e0)) C M)]
     ["the fact completing it removed" #(v/retract! % (v/handle-of % '(rsr_on rsr_e0) C))]
     ["the fact back" #(v/assert % '(rsr_on rsr_e0) C {})]]))

(deftest the-held-reach-answers-what-a-fresh-walk-answers
  (doseq [tms [:dense :reference]]
    (testing (str tms)
      (tu/with-cleared-kb [kb #(reach-kb {:tms tms} 6)]
        (is (false? (agrees kb "before any write")))
        (let [answers (mapv (fn [[label f]] (f kb) (agrees kb label)) (stream))]
          (is (= [false true false true false true false false true false false true false true] answers)
              "the stream reaches a supporter where a firing completes off a target's closure"))))))

(deftest a-write-off-the-closure-reads-the-held-walk
  (tu/with-cleared-kb [kb #(reach-kb {} 6)]
    (is (false? (reach kb true)))
    (let [walks (memo-walks kb)]
      (dotimes [i 8] (v/assert kb (list 'rsr_on (symbol (str "rsr_f" i))) C {}))
      (is (false? (reach kb true)))
      (is (= walks (memo-walks kb))
          "eight settles off the closure, each reading the reach, walk from the targets no more"))
    (let [walks (memo-walks kb)]
      (v/with-deferred-settle kb
        (v/assert kb '(rsr_p0 rsr_c99) C {})
        (v/assert kb '(not (rsr_p0 rsr_c99)) C M))
      (is (= 7 (count @(val (first (exc/supporter-entries kb))))) "a seventh target")
      (is (false? (agrees kb "a new defeat")))
      (is (= walks (memo-walks kb))
          "a stored defeat reads the targets again and walks on from the new one"))))

(def ^:private rules
  "The rules a write may remove and restore, by name: the chain's first link and the rule
  completing a firing at a `genl` supporter."
  {:chain    ['[(rsr_p0 ?x)] '(rsr_p1 ?x)]
   :complete ['[(rsr_p2 ?x) (rsr_on ?x)] '(genl ?x rsr_top)]})

(defn- rule!
  "Assert the rule named `r` (`rules`), and answer its handle."
  [kb r]
  (let [[ante cons] (rules r)] (v/assert-rule kb ante cons C {:direction :forward})))

(defn- random-ops
  "`n` writes drawn with `rng` over terms 0..2, each `[op i]`: a chain head defeated and
  freed, its firing completed and undone, a fact stated past the target (`:direct`, a
  path to the supporter that rests on no target), a defeated supporter that is its own
  target (`:self`), a rule removed and restored, and a fact off the closure."
  [^java.util.Random rng n]
  (let [ops [:defeat :undefeat :on :off :direct :undirect :self :unself :chain :complete :noise]]
    (vec (repeatedly n #(vector (nth ops (.nextInt rng (count ops))) (.nextInt rng 3))))))

(defn- apply-op!
  "Apply `[op i]` to `kb`; `held` is an atom of the handles of the rules (`rules`) stored."
  [kb held [op i]]
  (let [c     (symbol (str "rsr_c" i))
        head  (list 'rsr_p0 c)
        selfs (list 'genl (symbol (str "rsr_s" i)) 'rsr_top)
        drop! (fn [sentence] (some->> (v/handle-of kb sentence C) (v/retract! kb)))]
    (case op
      :defeat   (v/with-deferred-settle kb (v/assert kb head C {}) (v/assert kb (list 'not head) C M))
      :undefeat (drop! (list 'not head))
      :on       (v/assert kb (list 'rsr_on c) C {})
      :off      (drop! (list 'rsr_on c))
      :direct   (v/assert kb (list 'rsr_p2 c) C {})
      :undirect (drop! (list 'rsr_p2 c))
      :self     (v/with-deferred-settle kb (v/assert kb selfs C {}) (v/assert kb (list 'not selfs) C M))
      :unself   (drop! (list 'not selfs))
      (:chain :complete) (if-let [h (@held op)]
                           (do (v/retract! kb h) (swap! held dissoc op))
                           (swap! held assoc op (rule! kb op)))
      :noise    (v/assert kb (list 'rsr_on (symbol (str "rsr_n" i))) C {}))))

(deftest a-held-reach-over-random-writes-answers-what-a-fresh-walk-answers
  (doseq [seed [9 12 13 14 30 43]]
    (tu/with-cleared-kb [kb #(reach-kb {} 2)]
      (let [held  (atom (into {} (map (juxt identity #(rule! kb %))) (keys rules)))
            trace (mapv (fn [op] (apply-op! kb held op) [op (reach kb false) (reach kb true)])
                        (random-ops (java.util.Random. seed) 60))
            moves (set (map (fn [[[_ a] [_ b]]] [a b]) (partition 2 1 trace)))]
        (is (= [] (filterv (fn [[_ fresh held]] (not= fresh held)) trace))
            (str "seed " seed ": the writes after which the held reach differs"))
        (is (every? moves [[false true] [true false] [true true]])
            (str "seed " seed " makes a hit, breaks one and keeps one"))))))

(defn- witness-target
  "The chain term of the target the held path of the `genl` reach starts from."
  [kb]
  (let [memo @(:supporter-reach @(reasoning/taxonomy kb))
        hs   (some (fn [[[rel] e]] (when (= :genl rel) (first (:witness e)))) memo)]
    (second (:sentence (v/sentex kb (first hs))))))

(deftest a-write-off-the-path-reads-the-held-true
  (tu/with-cleared-kb [kb #(reach-kb {} 6)]
    (let [on  #(list 'rsr_on %)
          off (fn [n] (dotimes [i 8] (v/assert kb (list 'rsr_on (symbol (str "rsr_f" n i))) C {})))]
      (v/assert kb (on 'rsr_c1) C {})
      (v/assert kb (on 'rsr_c2) C {})
      (is (true? (reach kb true)))
      (let [walks (memo-walks kb)]
        (off 0)
        (is (true? (reach kb true)))
        (is (= walks (memo-walks kb)) "eight settles off the path, each reading the reach, walk no more"))
      (let [walks (memo-walks kb)]
        (v/retract! kb (v/handle-of kb (on (witness-target kb)) C))
        (is (true? (agrees kb "the path's last firing undone, the other chain's standing")))
        (is (= (inc walks) (memo-walks kb)) "a path that no longer holds walks again")
        (off 1)
        (is (true? (reach kb true)))
        (is (= (inc walks) (memo-walks kb)) "the walk again holds the path it met"))
      (let [walks (memo-walks kb)]
        (v/retract! kb (v/handle-of kb (on (witness-target kb)) C))
        (is (false? (agrees kb "both firings undone")))
        (is (= (inc walks) (memo-walks kb)))))))

(deftest a-held-path-cut-under-a-standing-supporter-reads-false
  (doseq [[label cut!] [["the target freed" #(v/retract! % (v/handle-of % '(not (rsr_p0 rsr_c1)) C))]
                        ["the path's last firing undone" #(v/retract! % (v/handle-of % '(rsr_on rsr_c1) C))]
                        ["the chain's first link removed" #(v/retract! % (rule! % :chain))]]]
    (tu/with-cleared-kb [kb #(reach-kb {} 6)]
      (v/assert kb '(rsr_on rsr_c1) C {})
      (is (true? (reach kb true)) label)
      ;; the supporter stays stored, a premise as well
      (v/assert kb '(genl rsr_c1 rsr_top) C {})
      (cut! kb)
      (is (some? (v/handle-of kb '(genl rsr_c1 rsr_top) C)) label)
      (is (false? (agrees kb label))))))
