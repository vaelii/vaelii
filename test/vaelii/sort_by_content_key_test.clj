;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.sort-by-content-key-test
  "`nm/sort-by-content-key` / `nm/min-by-content-key` / `nm/print-key` — the
  decorate-sort-undecorate the engine's content orders share, and the one guarded
  printer they use when a key is printed at all.  What is pinned here is the contract
  every caller leans on: the key is built **once per element** (not once per
  comparison), the sort short-circuits below two so a one-element listing builds no key
  at all, ties fall to arrival order, and `min-by-content-key` is
  `(first (sort-by-content-key …))` in one pass.

  The last tests are **scans of the sources**, not unit assertions, and they are here
  because this is the class of order-dependence that keeps coming back one site at a
  time.  Three shapes, one rule — an order the engine answers off is keyed on content:

    * a `pr-str` or `str` ordering key with the print vars left ambient.  A REPL binds
      `*print-length*`, two long sentences elide to one prefix, the key collapses, and
      the tie falls back to the enumeration order the content key existed to remove —
      silently, because every value involved is still legal.
    * an ordering keyed on the **handle** (`sort-by :id`, `min-key :id`, `(sort
      handles)`).  A handle is allocated in assertion order, so this is arrival order
      written down as a key: the same knowledge typed the other way round reads
      differently ([docs/defenses.md](../../docs/defenses.md), \"Tie-breaks and
      orderings key on content, not the handle\").
    * a positional take off a **match set** — `(first (sentexes-matching …))`.  The
      retrieval promises the set, never an order, so `first` names whichever member the
      index enumerated: a KB holding two matches answers by the order it was written in.

  A fourth scan is here for a different reason — cost, not correctness.  `sort-by` runs
  its key fn *inside* the comparator, so a key that reads the KB is a taxonomy closure
  re-read ~2·n·log₂n times where `sort-by-content-key` reads it n times.  Same file
  because it is the same fix, and because these sites are found the same way: by reading
  the key a call is handed.

  What every one of them reads is the **form**, not the line.  A key written below its
  call was invisible until it was, which is the whole content of #50."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.impl.naming :as nm])
  (:import [java.io File]))

(defn- counting
  "A key fn that tallies how many times it is called, so a test can prove the key is
  built n times rather than ~2·n·log₂n."
  [f]
  (let [n (atom 0)]
    [n (fn [x] (swap! n inc) (f x))]))

(deftest builds-the-key-once-per-element-not-once-per-comparison
  (let [coll (shuffle (range 64))
        [calls k] (counting identity)
        _ (doall (nm/sort-by-content-key k compare coll))]
    (is (= 64 @calls)
        "the key is decorated once per element; a per-comparison key fn would run ~2·n·log₂n times")))

(deftest short-circuits-below-two-and-builds-no-key
  (testing "zero and one element return the collection's own order, untouched"
    (let [[c0 k0] (counting identity)
          [c1 k1] (counting identity)]
      (is (= [] (nm/sort-by-content-key k0 [])))
      (is (= [:only] (nm/sort-by-content-key k1 [:only])))
      (is (= 0 @c0) "no key is built for an empty collection")
      (is (= 0 @c1) "no key is built for a singleton — the key is what orders, and there is nothing to order")))
  (testing "min over zero is nil, over one is that one, still no key built"
    (let [[c0 k0] (counting identity)
          [c1 k1] (counting identity)]
      (is (nil? (nm/min-by-content-key k0 [])))
      (is (= :only (nm/min-by-content-key k1 [:only])))
      (is (= 0 @c0))
      ;; min over a singleton decorates the one element (harmless) — assert it is at most one
      (is (<= @c1 1)))))

(deftest compare-form-is-the-default-and-orders-structurally
  ;; shorter-first, not lexicographic: (a) before (a b), which pr-str/str would reverse
  (let [forms [(list 'a 'b) (list 'a) (list 'b)]]
    (is (= [(list 'a) (list 'a 'b) (list 'b)]
           (nm/sort-by-content-key identity forms))
        "compare-form default: (a) precedes (a b) precedes (b)")))

(deftest a-pre-built-tuple-key-orders-under-plain-compare
  ;; a [rank …] priority vector is Comparable; pass `compare` to keep that exact order
  (let [xs [{:p 1 :n "z"} {:p 0 :n "m"} {:p 1 :n "a"}]
        key (juxt :p :n)]
    (is (= [{:p 0 :n "m"} {:p 1 :n "a"} {:p 1 :n "z"}]
           (nm/sort-by-content-key key compare xs))
        "sorted by the tuple key under default compare, primary then secondary")))

(deftest ties-keep-arrival-order
  ;; every element shares one key, so the whole order must be the arrival order
  (let [xs (mapv (fn [i] {:id i}) (range 20))]
    (is (= xs (nm/sort-by-content-key (constantly :same) compare xs))
        "equal keys fall back to arrival order, never to a re-shuffle")
    (is (= (first xs) (nm/min-by-content-key (constantly :same) compare xs))
        "min on an all-tie collection is the earliest arrival")))

(deftest min-agrees-with-first-of-sort
  (doseq [cmp [compare nm/compare-form]
          n   [1 2 3 8 64]]
    (let [xs (shuffle (mapv (fn [i] [(mod (* i 7) 5) i]) (range n)))
          key first]
      (is (= (first (nm/sort-by-content-key key cmp xs))
             (nm/min-by-content-key key cmp xs))
          (str "min == first-of-sort for cmp " cmp " at n=" n)))))

;; ---- print-key: the guarded printer, and the scan that keeps it the only one ----

(deftest print-key-is-unmoved-by-an-ambient-print-bound
  (let [a (list 'likes 'Tom 'Jerry 'Spike 'Butch)
        b (list 'likes 'Tom 'Jerry 'Spike 'Nibbles)]
    (testing "a caller's print bounds elide two long sentences to one prefix"
      (binding [*print-length* 3]
        (is (= (pr-str a) (pr-str b))
            "the hazard itself: a bare pr-str key collapses, and the tie falls to arrival")))
    (testing "print-key ignores them, so the key stays total"
      (binding [*print-length* 3 *print-level* 2]
        (is (not= (nm/print-key a) (nm/print-key b)))
        (is (= [a b] (nm/sort-by-content-key nm/print-key compare [b a]))
            "and the order is the content one, under the bound that would have collapsed it")))
    (testing "metadata is no part of what a sentence says"
      (binding [*print-meta* true]
        (is (= (nm/print-key a) (nm/print-key (with-meta a {:tagged true}))))))))

(def ^:private ordering-call
  "The calls whose first argument is an ordering **key**.  `sort` is absent on purpose —
  it takes no key fn, so a printed value cannot reach it.  `group-by` is here because a
  key that collapses collapses two *buckets* into one, which is the same defect wearing a
  different hat."
  #"sort-by|min-by-content-key|max-key|min-key|group-by")

(def ^:private printed-key-allowed
  "The sources where a printed or `str`'d ordering key is not a hazard, each by a
  distinctive substring of its own line, and why.  Every entry keys a **keyword** — an
  option key, a mode name, a belief mode — and `*print-length*` / `*print-level*` elide
  collections, never a keyword, so those keys cannot collapse.  They order a rejection
  message's `:options` list rather than anything a belief or a report is read off.

  One allowlist for both scans below, because they are one rule seen from two sides: a
  key that may not print may not `str` either, and a value safe for one is safe for both."
  #{"(remove opt-keys (keys opts))"
    "(remove edit-batch-keys (keys batch))"
    "(keys belief-modes)"})

(def ^:private bare-str
  "`str` standing alone as a key fn — `(sort-by str …)`, `(comp str :sentence)`, `(str c)`
  inside a tuple key.  The lookarounds are what keep `pr-str`, `str/join` and a symbol that
  merely ends in those three letters out of it."
  #"(?<![\w-])str(?![\w/-])")

(defn- clj-sources []
  (->> (file-seq (io/file "src/vaelii"))
       (filter #(.isFile ^File %))
       (map #(.getPath ^File %))
       (filter #(str/ends-with? % ".clj"))
       sort))

(defn- test-sources
  "The test tree, for the positional-take scan alone: a test reading a match set by
  position is right only while the goal happens to have one answer, which is the same
  arrival-order bet the engine is held to.  This file is left out — its prose names the
  shape it forbids."
  []
  (->> (file-seq (io/file "test/vaelii"))
       (filter #(.isFile ^File %))
       (map #(.getPath ^File %))
       (filter #(str/ends-with? % ".clj"))
       (remove #(str/ends-with? % "sort_by_content_key_test.clj"))
       sort))

(defn- string-end
  "One past the string literal opening at `i`, escapes honoured — so a `\\\"` inside it
  does not end it and a `(` inside it balances nothing."
  [^String s i]
  (let [n (count s)]
    (loop [j (inc i)]
      (cond (>= j n)             n
            (= \\ (.charAt s j)) (recur (+ j 2))
            (= \" (.charAt s j)) (inc j)
            :else                (recur (inc j))))))

(defn- atom-end
  "One past the bare atom starting at `i` — a symbol, keyword or number, which runs to the
  first whitespace or delimiter."
  [^String s i]
  (let [n (count s)]
    (loop [j (inc i)]
      (if (or (>= j n)
              (let [c (.charAt s j)]
                (or (Character/isWhitespace c)
                    (contains? #{\( \) \[ \] \{ \} \" \; \, \'} c))))
        j
        (recur (inc j))))))

(defn- form-end
  "One past the **single form** beginning at or after `i`: the paren-balanced read a line
  cut cannot do.  Strings and line comments are skipped whole, a character literal is one
  atom, and a reader prefix (`#`, `'`, `` ` ``, `~`, `@`, `^`) decorates the form after it
  rather than standing as one."
  [^String s i]
  (let [n (count s)]
    (loop [i i depth 0]
      (if (>= i n)
        n
        (let [c (.charAt s i)]
          (cond
            (= \; c)                     (recur (or (str/index-of s "\n" i) n) depth)
            (= \" c)                     (let [e (string-end s i)]
                                           (if (zero? depth) e (recur e depth)))
            (= \\ c)                     (if (zero? depth)
                                           (atom-end s (inc i))
                                           (recur (+ i 2) depth))
            (contains? #{\( \[ \{} c)    (recur (inc i) (inc depth))
            (contains? #{\) \] \}} c)    (if (<= depth 1) (inc i) (recur (inc i) (dec depth)))
            (pos? depth)                 (recur (inc i) depth)
            (Character/isWhitespace c)   (recur (inc i) depth)
            (contains? #{\# \' \` \~ \@ \^} c) (recur (inc i) depth)
            :else                        (atom-end s i)))))))

(defn- ordering-keys
  "`[line-number line key-form]` for every `call` in `text` — the ordering **key** each one
  is handed, read as a form.

  A key is not \"the rest of the line\".  Written below its call — a `juxt` broken over two
  lines, a `pr-str` on the continuation — it is invisible to a scan that cuts the line
  after the call, and that one-line window is how every site this file has ever missed was
  missed: PR #46's `quality.clj` one, and the four `llm/inventory.clj` ones.  Reading to
  the key's own closing paren sees all of it, however far down the page it runs, **and
  stops there** — so the collection argument, which may legitimately print what the sort
  answered (`(map pr-str (sort-by …))` renders an answer and never keys on it), is no part
  of what is judged."
  [call ^String text]
  (let [lines (vec (str/split-lines text))
        m     (re-matcher call text)]
    (loop [found [] pos 0 line 1]
      (if-not (.find m)
        found
        (let [start (.start m)
              line  (+ line (count (re-seq #"\n" (subs text pos start))))
              key   (subs text (.end m) (form-end text (.end m)))]
          (recur (conj found [line (nth lines (dec line) "") key]) start line))))))

(defn- unguarded-printed-keys
  "Every `[path line-number line]` in `src/vaelii` that hands a bare `pr-str` to an
  ordering call, with the three ways of being guarded taken out: the printer is
  `nm/print-key`; a `*print-length*` binding frame is open within the twelve lines above
  (the shape `solve/content-key` and `settle/content-order` use, one binding around a
  whole sort rather than one per element); or the line is allowlisted above.

  `naming.clj` itself is skipped — it is where the guard is defined and where the hazard
  is described in prose."
  []
  (for [path  (clj-sources)
        :when (not (str/ends-with? path "/naming.clj"))
        :let  [text  (slurp path)
               lines (vec (str/split-lines text))]
        [n line key] (ordering-keys ordering-call text)
        :let  [above (str/join "\n" (subvec lines (max 0 (- n 13)) n))]
        :when (and (str/includes? key "pr-str")
                   (not (str/includes? key "print-key"))
                   (not (str/includes? above "*print-length*"))
                   (not-any? #(str/includes? line %) printed-key-allowed))]
    [path n (str/trim line)]))

(deftest no-ordering-key-prints-without-the-guard
  ;; The recurring bug this closes: `(sort-by pr-str …)` over an answer *set*, or over a
  ;; map's `keys`/`vals`.  Under a REPL's `*print-length*` the key collapses and the
  ;; choice — which hypothesis survives, which ASP atom gets which id, which declaration
  ;; a refusal names — falls back to handle order, which is assertion order.  Nothing
  ;; throws and no test of the answer notices, because both readings are legal.
  (let [bad (unguarded-printed-keys)]
    (is (empty? bad)
        (str "an ordering key is printed with the print vars left ambient — use "
             "`nm/print-key`, or bind `*print-length*`/`*print-level*` around the sort:\n"
             (str/join "\n" (map (fn [[p n l]] (str "  " p ":" n "  " l)) bad))))))

(defn- unguarded-str-keys
  "Every `[path line-number line]` in `src/vaelii` that hands a bare `str` to an ordering
  call.  The guarded answers are `nm/print-key` (a collection-capable value), `nm/name-key`
  (a scalar one) and `nm/compare-form` (no key at all), none of which contains a bare
  `str` — so a converted site simply stops matching, and no second roster has to be kept
  in step with this one.  The allowlist above is the one exception, and `naming.clj` is
  skipped for the reason the printed scan skips it.

  **Why `str` is the same hazard as `pr-str`.**  `str` on a collection is `pr-str` with
  the ambient print vars honoured — `(str '(a b c d))` under `*print-length*` 2 is
  `(a b ...)` — so a sentence, a NAT, a context NAT or a binding map keyed with it
  collapses under a REPL's bounds exactly as a printed key does.  On a symbol, keyword,
  string or number it cannot, which is what `nm/name-key` is for: the same `str`, with the
  scalar written down as a claim and a collection routed to the guarded printer."
  []
  (for [path  (clj-sources)
        :when (not (str/ends-with? path "/naming.clj"))
        :let  [text (slurp path)]
        [n line key] (ordering-keys ordering-call text)
        :when (and (re-find bare-str key)
                   (not-any? #(str/includes? line %) printed-key-allowed))]
    [path n (str/trim line)]))

(deftest no-ordering-key-is-a-bare-str
  ;; The wider half of the same class, and the one that had ~50 live sites: `str` honours
  ;; the print vars exactly as `pr-str` does, so `(sort-by str terms)` over a list that may
  ;; hold a NAT is the printed-key hazard with the printing hidden.  Nothing throws, both
  ;; readings are legal, and the order the page or the report is read in falls back to
  ;; whatever the index enumerated.
  (let [bad (unguarded-str-keys)]
    (is (empty? bad)
        (str "an ordering key is a bare `str` — use `nm/print-key` where the value may be "
             "a collection (a sentence, a NAT, a context NAT, a binding map), `nm/name-key` "
             "where it is a scalar, or `nm/compare-form` where no key is needed at all:\n"
             (str/join "\n" (map (fn [[p n l]] (str "  " p ":" n "  " l)) bad))))))

;; ---- a key that reads the KB, run once per comparison -------------------

(def ^:private plain-sort-by
  "`sort-by` itself, and not the cure.  `sort-by-content-key` and `min-by-content-key`
  both continue past a `-`, which the lookahead refuses, so a converted site simply stops
  matching and no second roster has to be kept in step with this one."
  #"\((?:nm/|naming/)?sort-by(?![\w/-])")

(def ^:private kb-reading-key
  "`kb` named inside an ordering key — the key asks the knowledge base something.  A
  `genls` closure, a match, an `arg` read: whatever it is, it is not a field access, and
  `sort-by` will run it once per *comparison*."
  #"(?<![\w-])kb(?![\w-])")

(defn- kb-reading-sort-keys
  "Every `[path line-number line]` in `src/vaelii` that hands `sort-by` a key that reads
  the KB.  No allowlist, because there is no case for one: the cure is a drop-in with the
  same order and the same tie-break, so a site that wants this key wants
  `nm/sort-by-content-key` (or `nm/min-by-content-key`, where the sort was thrown away
  but for its first element)."
  []
  (for [path (clj-sources)
        :let [text (slurp path)]
        [n line key] (ordering-keys plain-sort-by text)
        :when (re-find kb-reading-key key)]
    [path n (str/trim line)]))

(deftest no-sort-by-key-reads-the-kb
  ;; `sort-by` calls its key fn from inside the comparator, so `(sort-by (partial
  ;; specificity kb) types)` re-reads a taxonomy closure ~2·n·log₂n times to answer a
  ;; question n reads settle.  Nothing goes red — the order is right, and only the cost is
  ;; wrong — which is why this is a scan rather than a test of an answer.
  (let [bad (kb-reading-sort-keys)]
    (is (empty? bad)
        (str "an ordering key reads the KB and `sort-by` runs it per comparison — use "
             "`nm/sort-by-content-key` (or `nm/min-by-content-key` where only the first "
             "element is kept), which builds the key once per element:\n"
             (str/join "\n" (map (fn [[p n l]] (str "  " p ":" n "  " l)) bad))))))

;; ---- what the scans read: the form, not the line -----------------------

(deftest a-key-written-below-its-call-is-read
  ;; The hole every one of these scans had, as a fixture rather than as a source file: cut
  ;; the line after `(sort-by` and there is nothing left to judge, so a key one line down
  ;; passed a green guard.  That is how PR #46's `quality.clj` site and #50's four
  ;; `llm/inventory.clj` ones were all written under a scan that was watching for exactly
  ;; them.
  (let [text (str "(defn- ranked [kb xs]\n"
                  "  (sort-by\n"
                  "   (juxt first (comp (partial specificity kb) second)\n"
                  "         (fn [x] (pr-str x)))\n"
                  "   xs))\n")
        [[n line key] :as found] (ordering-keys ordering-call text)]
    (is (= 1 (count found)) "one ordering call, found once")
    (is (= 2 n) "reported at the line the call is on, not the line the key ends on")
    (is (= "(sort-by" (str/trim line)))
    (is (str/includes? key "specificity kb")
        "the key below the call is read at all — cutting the line saw nothing after `(sort-by`")
    (is (str/includes? key "pr-str")
        "and all of it, however many lines down it runs")
    (is (not (str/includes? key "xs"))
        "and it stops at the key's own closing paren — the collection is no part of the key")
    (testing "so all four scans see it, where a line cut saw none of them"
      (is (re-find #"pr-str" key))
      (is (re-find kb-reading-key key)))))

(deftest the-form-read-is-not-fooled-by-a-string-or-a-comment
  ;; A paren inside a string or after a `;` closes nothing, and a scan that counted them
  ;; would end the key early — which is indistinguishable from a *narrower* guard, the failure mode this
  ;; whole file exists to refuse.
  (let [text (str "(sort-by (juxt :a   ; ) does not close anything\n"
                  "               #(str \"(\" %))\n"
                  "         xs)\n")
        [[_ _ key]] (ordering-keys ordering-call text)]
    (is (str/includes? key "#(str")
        "the comment's paren did not end the key")
    (is (str/ends-with? key "%))")
        "and the string's paren did not either — the key ends where its own paren does")
    (is (not (str/includes? key "xs")))))

;; ---- the handle as a key: arrival order, written down ------------------

(def ^:private handle-ordering-call
  "The calls whose first argument is an ordering **key**, for the handle scan.  `group-by`
  is absent where the printed roster has it: bucketing on a handle groups a unique key and
  orders nothing, so it cannot carry arrival order into an answer."
  #"sort-by|min-by-content-key|max-key|min-key")

(def ^:private handle-key
  "A key fn that reads a stored handle — `:id` or `:handle`, alone or inside a `juxt`."
  #"(?<![\w-]):(?:id|handle)(?![\w-])")

(def ^:private handle-collection-sort
  "`sort` over a collection **of** handles.  No key fn is passed, so neither key scan can
  see it, and the elements are the integers themselves — allocated in assertion order,
  which is the whole hazard."
  #"\(sort (?:\(map :id|\(map :handle|\(:handles|\(:ids|handles|ids|id\))")

(def ^:private handle-key-allowed
  "The sources where an ordering **is** keyed on a handle and that is not a hazard, each by
  a distinctive substring of its own line.  Two kinds, and no third.

  A **display** listing orders rows on a page, or the nodes of a search tree a page draws:
  nothing is read off the order but the eye, and the handle is the one key a reader sees
  printed beside the row it ordered.  A **handle-set identity** sorts a vector of handles
  to name the *set* they form — `dispute-id`'s pair is a key two callers holding it either
  way round must spell the same way, and sorting the integers is what makes one spelling.
  Neither decides a belief, a witness, a placement or a report's sides.

  One allowlist for both scans below, for the reason the printed one is shared: they are
  one rule — an answer's order is a function of content — seen from two sides."
  #{"(sort-by :id sentexes)"
    "(sort-by :id justifications)"
    "(sort-by :id (into [] (take ego-scan) (v/sentexes-matching kb pattern '?ctx)))"
    "(sort-by :id (vals @(:nodes sess)))"
    "(sort-by (juxt (comp print-key :context) :id) sentexes)"
    "(sort (:handles entry))"
    "(vec (sort id))"})

(defn- handle-keyed-orderings
  "Every `[path line-number line]` in `src/vaelii` that orders on a handle — a `:id` /
  `:handle` key fn handed to an ordering call, or a bare `sort` over a collection of
  handles — minus the allowlist above."
  []
  (distinct
   (sort
    (concat
     (for [path (clj-sources)
           :let [text (slurp path)]
           [n line key] (ordering-keys handle-ordering-call text)
           :when (and (re-find handle-key key)
                      (not-any? #(str/includes? line %) handle-key-allowed))]
       [path n (str/trim line)])
     ;; the bare `sort` over a collection *of* handles passes no key fn, so there is no
     ;; form to read and the line is the whole of what there is to see
     (for [path  (clj-sources)
           :let  [lines (vec (str/split-lines (slurp path)))]
           i     (range (count lines))
           :let  [line (nth lines i)]
           :when (and (re-find handle-collection-sort line)
                      (not-any? #(str/includes? line %) handle-key-allowed))]
       [path (inc i) (str/trim line)])))))

(deftest no-ordering-key-is-a-handle
  ;; The half of the rule the printed scan cannot see, and the more direct one: a handle
  ;; is allocated in assertion order, so keying an order on it *is* keying it on arrival.
  ;; The same knowledge loaded the other way round then elects the other side of a
  ;; dilemma, names the other supporter of an edge, or reports the two sides of a clash
  ;; reversed — and nothing throws, because both readings are legal.
  (let [bad (handle-keyed-orderings)]
    (is (empty? bad)
        (str "an ordering keys on the handle — order by the content instead "
             "(`nm/sort-by-content-key` with `nm/print-key` / `nm/compare-form`, or "
             "`solve/content-key` where a total order is needed):\n"
             (str/join "\n" (map (fn [[p n l]] (str "  " p ":" n "  " l)) bad))))))

;; ---- a positional take off a match SET ---------------------------------

(def ^:private match-call
  "The reads that answer with the **set** of matching sentexes.  `res/matches-visible`
  promises that set and nothing about the order it comes back in, and each of these is a
  entry point onto it.

  The three **extent** reads are here on the same argument: `sentexes-in-context`,
  `sentexes-with-functor` and `sentexes-with-arg` each answer everything under one index
  key, in whatever order that key's postings enumerate — which is the order the facts were
  written in.  A lazy seq is a bounded read, never a promise about which member comes
  first."
  #"\((?:v/|kb/|res/|core/|p/)?(?:sentexes-matching|sentexes-matching-as-stored|matches-visible|matches-hierarchical|sentexes-in-context|sentexes-with-functor|sentexes-with-arg)\b")

(def ^:private positional-take
  "A take that names ONE member by position, applied directly to the call."
  #"\((?:first|ffirst|second|last)\s+$")

(def ^:private threaded-take
  "The same take, one thread away: `(some-> (matches …) first :sentence)`."
  #"\(some->>?\s+$")

(def ^:private content-ordered
  "What makes a positional take legal: the set is put in **content** order first, so
  `first` names what the knowledge says rather than what the index enumerated."
  #"sort-by-content(?:-key)?|min-by-content-key|sort-by :context|print-key|compare-form")

(defn- positional-takes-on-a-match-set
  "Every `[path line-number line]` in `src/vaelii` and `test/vaelii` that names one member
  of a match set by position, with the guard taken out: a content ordering within the
  three lines the take spans.  Three lines because the thread that does it — call, sort,
  take — is written down the page, and the guard sits between the two halves of what
  would otherwise be flagged."
  []
  (for [path  (concat (clj-sources) (test-sources))
        :let  [lines (vec (str/split-lines (slurp path)))]
        i     (range (count lines))
        :let  [line   (nth lines i)
               m      (re-find match-call line)
               prefix (when m (subs line 0 (str/index-of line m)))
               window (str/join " " (subvec lines i (min (count lines) (+ i 3))))]
        :when (and m
                   (or (re-find positional-take prefix)
                       (and (re-find threaded-take prefix)
                            (re-find #"(?<![\w-])(?:first|ffirst|second|last)(?![\w-])"
                                     window)))
                   (not (re-find content-ordered window))
                   (not-any? #(str/includes? line %) handle-key-allowed))]
    [path (inc i) (str/trim line)]))

(deftest no-positional-take-off-a-match-set
  ;; `matches-visible` promises the SET of matches, so `(first (sentexes-matching …))` asks
  ;; a question the retrieval does not answer: with two matching sentexes it names
  ;; whichever the index enumerated, which is the order they were written in.  The fix is
  ;; either to order on content before taking one, or to say out loud why there can only be
  ;; one — a functional predicate refuses the second row, and a caller resting on that
  ;; refusal should name it rather than lean on it silently
  ;; (`koinii.identity/sole-registry-match`).  The test tree is held to it too: a test's
  ;; `first` off a match set is right only while its goal has one answer, and the
  ;; single-answer entry point (`v/handle-of`) or a cardinality assertion says so instead.
  (let [bad (positional-takes-on-a-match-set)]
    (is (empty? bad)
        (str "one member of a match set is named by position — order on content first "
             "(`nm/sort-by-content-key`, or `sort-by :context` where the sentence is "
             "shared), or refuse the many-match case explicitly:\n"
             (str/join "\n" (map (fn [[p n l]] (str "  " p ":" n "  " l)) bad))))))

(deftest the-allowlist-still-names-live-code
  ;; An allowlist that has outlived its sites is indistinguishable from a rule with exceptions when it is
  ;; really a rule with none — so each entry must still match a line that would otherwise
  ;; be flagged.
  (let [text (str/join "\n" (map slurp (clj-sources)))]
    (doseq [entry (concat printed-key-allowed handle-key-allowed)]
      (is (str/includes? text entry)
          (str "allowlisted ordering key no longer in the sources: " entry)))))
