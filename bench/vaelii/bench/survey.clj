;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.survey
  "Validate the Phase 1 posting-encoding bake-off (`vaelii.bench.postings`) against a
  **real** corpus instead of the synthetic Zipfian generator.

  Reads sentex records from a real on-disk store's `sentexes.log` **read-only, from the
  start** — the frames at the front were written long ago and are complete, so a bare
  read handle never touches the writer's lock and cannot tear against a concurrent
  append at the tail.  It copies nothing and mutates nothing.  A sample of the sentences
  is re-indexed into a fresh in-memory KB, and `postings/survey-index` runs the identical
  composition + four-encoding density measurement.

  **Caveat, stated honestly:** a sample of N out of the corpus's ~15M facts has *less
  term reuse* than the whole, so its big postings (a hot predicate/context) are smaller
  than at full scale — the survey therefore *under*-represents the large-posting tail and,
  if anything, understates Roaring's tier.  What it faithfully reproduces is the fact
  SHAPE (arity, compound nesting, term skew) and the small-posting dominance, which is
  what the int[]-vs-Roaring call turns on.

  `naming` is a different audit over the same scan: what fraction of the corpus the
  **front door** would refuse, by class and by spelling (`naming-audit`, below).

  Run: `lein bench-survey [sample-n] [/path/to/sentexes.log]` (sample defaults to
  300000).  The store defaults to `VAELII_SURVEY_STORE`, else `~/.vaelii/kbs/store`;
  nothing ships one, so this needs a real on-disk KB to point at."
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [taoensso.nippy :as nippy]
            [vaelii.bench.postings :as postings]
            [vaelii.impl.disk.files :as files]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p])
  (:import [java.io RandomAccessFile]))

(defn- thaw-record
  "One frame, as a **field map**.  A record whose class this build no longer defines —
  a store written before a rename — does not throw and does not come back empty: nippy
  hands back `{:nippy/unthawable {:content {…}}}` with every field value in it, and a
  class name is not a fact about the corpus.  So the content is what this reads, and a
  survey over an older store reports the sentences rather than a log of nils.  Only a
  frame with no readable content at all is nil."
  [^bytes bs]
  (let [r (try (nippy/thaw bs) (catch Exception _ nil))]
    (if-let [u (and (map? r) (:nippy/unthawable r))] (:content u) r)))

(defn- stream-sentences
  "The first `n` `[sentence context]` pairs from a record log, read-only from offset 0."
  [^String path ^long n]
  (with-open [raf ^RandomAccessFile (files/open-log-read path)]
    (let [len (.length raf)]
      (loop [off 0, i 0, acc (transient [])]
        (if (or (>= i n) (>= off len))
          (persistent! acc)
          (do (.seek raf off)
              (let [flen (.readInt raf)
                    bs   (byte-array flen)]
                (.readFully raf bs)
                (let [rec (thaw-record bs)]
                  (recur (+ off 4 (long flen)) (inc i)
                         (cond-> acc
                           (and rec (:sentence rec))
                           (conj! [(:sentence rec) (:context rec)])))))))))))

;; ---- rule audit (are there rules, and what predicates do they introduce?) ----
;; The front-of-log fact sample can miss rules loaded elsewhere, so classify EVERY
;; record: a Rule carries :antecedent (the discriminant), an exceptWhen meta is
;; an atomic sentex (a positive `(exceptWhen …)` application — never negated) whose
;; :sentence starts with `exceptWhen`, everything else is a fact.  Two
;; modes: a uniform sample by handle via the .idx (fast, unbiased across the whole store),
;; and a full sequential scan (definitive).

(defn- functor [x] (when (and (sequential? x) (symbol? (first x))) (first x)))

(defn- classify [rec tally]
  (cond
    (nil? rec) (update tally :bad inc)
    (some? (:antecedent rec))
    (-> tally
        (update :rules inc)
        (update :rule-preds into (keep functor (:antecedent rec)))
        (update :rule-preds (fn [s] (if-let [c (functor (:consequent rec))] (conj s c) s)))
        (update :dirs (fn [d] (update d (:direction rec) (fnil inc 0))))
        ;; backward-chain shape: |antecedents| is the per-goal join/branching cost;
        ;; consequent-predicate frequency is the candidate-set size a goal on that
        ;; predicate reads (`rules-by-consequent`).
        (update :ante-counts (fn [m] (update m (count (:antecedent rec)) (fnil inc 0))))
        (update :conseq (fn [m] (if-let [c (functor (:consequent rec))] (update m c (fnil inc 0)) m)))
        (cond-> (:defeasible rec) (update :defeasible inc)))
    (and (sequential? (:sentence rec)) (= 'exceptWhen (first (:sentence rec))))
    (update tally :metas inc)
    :else
    (-> tally (update :facts inc)
        (update :fact-preds (fn [s] (if-let [f (functor (:sentence rec))] (conj s f) s))))))

(defn- report-audit [tally elapsed]
  (let [{:keys [facts rules metas bad fact-preds rule-preds dirs defeasible ante-counts conseq]} tally
        rule-only (clojure.set/difference rule-preds fact-preds)]
    (println (format "\n══ rule audit ══ (%.1fs)  facts %,d | rules %,d | exceptWhen-metas %,d | unthawable %,d"
                     (/ elapsed 1000.0) facts rules metas bad))
    (println (format "  distinct fact predicates : %,d" (count fact-preds)))
    (println (format "  distinct rule predicates : %,d  (in antecedents/consequents)" (count rule-preds)))
    (println (format "  rule directions          : %s" (pr-str dirs)))
    (println (format "  defeasible rules         : %,d" (or defeasible 0)))
    (println (format "  RULE-ONLY predicates (in rules, never in a fact) : %,d" (count rule-only)))
    (when (seq ante-counts)
      (println "  antecedent-count histogram (backward join/branching cost):")
      (doseq [[k c] (sort ante-counts)]
        (println (format "    %d antecedent(s): %,d rules  (%.0f%%)" k c (* 100.0 (/ c (double (max 1 rules))))))))
    (when (seq conseq)
      (println (format "  consequent-predicate skew: %,d distinct consequents; top (= candidate-set size for a goal on it):"
                       (count conseq)))
      (doseq [[p c] (take 10 (sort-by val > conseq))]
        (println (format "    %-28s %,d rules conclude it" p c))))
    (when (seq rule-only)
      (println (format "  sample of the %,d RULE-ONLY predicates:" (count rule-only)))
      (println "    " (pr-str (vec (sort (take 40 rule-only))))))
    tally))

(defn- read-frame [^RandomAccessFile raf ^long off]
  (.seek raf off)
  (let [flen (.readInt raf) bs (byte-array flen)]
    (.readFully raf bs)
    [(+ off 4 (long flen)) (thaw-record bs)]))

(def ^:private empty-tally
  {:facts 0 :rules 0 :metas 0 :bad 0 :defeasible 0 :fact-preds #{} :rule-preds #{} :dirs {}
   :ante-counts {} :conseq {}})

(defn- full-scan [^String log-path]
  (with-open [raf ^RandomAccessFile (files/open-log-read log-path)]
    (let [len (.length raf) t0 (System/nanoTime)]
      (loop [off 0, n 0, tally empty-tally]
        (when (and (pos? n) (zero? (mod n 1000000)))
          (println (format "  … %,d records (%.0f%%)" n (* 100.0 (/ (double off) len)))))
        (if (>= off len)
          (report-audit tally (/ (- (System/nanoTime) t0) 1e6))
          (do (.seek raf off)
              (let [flen (.readInt raf) bs (byte-array flen)]
                (.readFully raf bs)
                (recur (+ off 4 (long flen)) (inc n)
                       (classify (thaw-record bs) tally)))))))))

(defn uniform-records
  "`want` raw thawed records sampled uniformly by handle across the whole store (read-only) —
  facts AND rules, so a caller can filter `:antecedent` for rules."
  [^String dir ^long want]
  (with-open [idx ^RandomAccessFile (RandomAccessFile. (str dir "/records/sentexes.idx") "r")
              log ^RandomAccessFile (files/open-log-read (str dir "/records/sentexes.log"))]
    (let [total (quot (.length idx) 24)
          step  (max 1 (quot total want))]
      (loop [id 0, acc (transient [])]
        (if (>= id total)
          (persistent! acc)
          (let [slot (files/read-slot idx id)
                rec  (when (and slot (not (:tombstone? slot))) (second (read-frame log (:offset slot))))]
            (recur (+ id step) (cond-> acc rec (conj! rec)))))))))

(defn uniform-pairs
  "`want` `[sentence context]` pairs sampled uniformly by handle across the whole store —
  unbiased, unlike streaming the front of the log (which here is homogeneous extraction
  facts).  Read-only."
  [^String dir ^long want]
  (with-open [idx ^RandomAccessFile (RandomAccessFile. (str dir "/records/sentexes.idx") "r")
              log ^RandomAccessFile (files/open-log-read (str dir "/records/sentexes.log"))]
    (let [total (quot (.length idx) 24)
          step  (max 1 (quot total want))]
      (loop [id 0, acc (transient [])]
        (if (>= id total)
          (persistent! acc)
          (let [slot (files/read-slot idx id)
                rec  (when (and slot (not (:tombstone? slot))) (second (read-frame log (:offset slot))))]
            (recur (+ id step)
                   (cond-> acc (and rec (:sentence rec)) (conj! [(:sentence rec) (:context rec)])))))))))

(defn- uniform-sample [^String dir ^long want]
  (with-open [idx ^RandomAccessFile (RandomAccessFile. (str dir "/records/sentexes.idx") "r")
              log ^RandomAccessFile (files/open-log-read (str dir "/records/sentexes.log"))]
    (let [total (quot (.length idx) 24)
          step  (max 1 (quot total want))
          t0    (System/nanoTime)]
      (println (format "  idx holds %,d slots; sampling every %,dth handle" total step))
      (loop [id 0, tally empty-tally]
        (if (>= id total)
          (report-audit tally (/ (- (System/nanoTime) t0) 1e6))
          (let [slot (files/read-slot idx id)
                rec  (when (and slot (not (:tombstone? slot)))
                       (second (read-frame log (:offset slot))))]
            (recur (+ id step) (if rec (classify rec tally) tally))))))))

;; ---- naming audit (what would the front door refuse?) --------------------
;;
;; The dump path builds records directly and never calls `assert`, so the corpus is in
;; the store holding spellings the naming invariants refuse.  This scans every record and
;; asks `nm/problems*` what `assert` would have said, then groups: by class, by the frame
;; the offending literal sits in, and by the *distinct spelling* — because "10,025
;; rejections" is a count of records and the question is how many **names** are behind it.
;;
;; It also prices the counterfactual.  The widened conventions are written out here rather
;; than read from `naming`, so this measures what a change would buy **before** it is
;; made, and re-running it after is a check on the engine rather than a tautology.

(def ^:private candidates
  "The widenings worth pricing, each a whole set of four conventions.

  Ordered by what they **cost**, not by what they rescue.  Admitting a character to a
  role's alphabet costs nothing structural: the four roles are told apart by their initial
  case, and no separator moves that.  Dropping the `Cx` *prefix* is a different kind
  of change — that prefix is the only thing distinguishing a context from an individual —
  so it is priced last and on its own."
  [{:name "+ hyphen"
    :ctx  #"Cx[A-Z][A-Za-z0-9-]*"  :ind #"[A-Z][A-Za-z0-9-]*"
    :pred #"[a-z][a-zA-Z0-9-]*"    :typ #"[a-z][a-z0-9_-]*"}
   {:name "+ hyphen, apostrophe"
    :ctx  #"Cx[A-Z][A-Za-z0-9'-]*" :ind #"[A-Z][A-Za-z0-9'-]*"
    :pred #"[a-z][a-zA-Z0-9'-]*"   :typ #"[a-z][a-z0-9_'-]*"}
   {:name "+ hyphen, apostrophe; and a context is any CapitalCamel"
    :ctx  #"[A-Z][A-Za-z0-9'-]*"   :ind #"[A-Z][A-Za-z0-9'-]*"
    :pred #"[a-z][a-zA-Z0-9'-]*"   :typ #"[a-z][a-z0-9_'-]*"}])

;; total in `s`: a stored record can carry a context that is nil or not a symbol at all,
;; and an audit exists to find exactly that rather than to die on it.
(defn- w-match? [re s] (and (symbol? s) (some? (re-matches re (clojure.core/name s)))))

(defn- rescued?
  "Would `cand`'s conventions make this problem go away?  A spelling class is rescued when
  one of its widened patterns matches; an arity violation and a dotted rest marker are not
  about spelling at all, so no widening here touches them."
  [{:keys [ctx ind pred typ]} {:keys [class symbol]}]
  (case class
    :functor      (or (w-match? pred symbol) (w-match? typ symbol))
    :argument     (or (w-match? ind symbol) (w-match? ctx symbol)
                      (w-match? pred symbol) (w-match? typ symbol))
    (:context-name :ist-context) (w-match? ctx symbol)
    false))

(def ^:private empty-naming-tally
  {:records 0 :bad 0 :offending 0 :problems 0
   :rescued (into {} (for [c candidates] [(:name c) {:problems 0 :records 0}]))
   :by-class {} :by-class-role {} :records-by-class {} :spellings {}})

(defn- bump [m k] (update m k (fnil inc 0)))

(defn- tally-naming [rec tally]
  (if (nil? rec)
    (update tally :bad inc)
    (let [ps (nm/problems* (:sentence rec) (:context rec))
          t  (update tally :records inc)]
      (if (empty? ps)
        t
        (let [n (count ps)]
          (-> t
              (update :offending inc)
              (update :problems + n)
              (update :rescued
                      #(reduce (fn [m c]
                                 (let [k (count (filter (partial rescued? c) ps))]
                                   (-> m
                                       (update-in [(:name c) :problems] + k)
                                       (cond-> (= k n) (update-in [(:name c) :records] inc)))))
                               % candidates))
              (update :by-class      #(reduce (fn [m p] (bump m (:class p))) % ps))
              (update :by-class-role #(reduce (fn [m p] (bump m [(:class p) (:role p)])) % ps))
              (update :records-by-class
                      #(reduce (fn [m c] (bump m c)) % (into #{} (map :class) ps)))
              (update :spellings
                      #(reduce (fn [m p] (update-in m [(:class p) (:symbol p)] (fnil inc 0)))
                               % ps))))))))

(defn- odd-chars
  "The characters of `s` outside `[A-Za-z0-9_]` — what a convention would have to admit
  to accept this spelling, as a sorted string.  A namespaced symbol's `/` never appears:
  `naming` reads the *name* half, so a namespace is already invisible to it."
  [s]
  (apply str (sort (distinct (remove #(or (Character/isLetterOrDigit ^char %) (= \_ %))
                                     (if (symbol? s) (clojure.core/name s) (pr-str s)))))))

(defn- report-spellings [class syms]
  (let [n     (count syms)
        occ   (reduce + (vals syms))
        chars (->> syms keys (map odd-chars) frequencies (sort-by val >))]
    (println (format "\n  ── %s ── %,d distinct spellings over %,d occurrences"
                     (clojure.core/name class) n occ))
    (println "     characters a convention would have to admit (distinct spellings):")
    (doseq [[cs c] (take 8 chars)]
      (println (format "       %-10s %,7d  (%.1f%%)"
                       (if (str/blank? cs) "<none: shape>" (pr-str cs)) c
                       (* 100.0 (/ c (double (max 1 n)))))))
    (println "     most frequent offending spellings:")
    (doseq [[s c] (take 12 (sort-by val > syms))]
      (println (format "       %-42s %,d" s c)))))

(defn- report-naming [tally elapsed]
  (let [{:keys [records bad offending problems rescued
                by-class by-class-role records-by-class spellings]} tally
        pct #(* 100.0 (/ (double %1) (double (max 1 %2))))]
    (println (format "\n══ naming audit ══ (%.1fs)  records %,d | unthawable %,d"
                     (/ elapsed 1000.0) records bad))
    (println (format "  records the front door would REFUSE : %,d  (%.2f%% of %,d)"
                     offending (pct offending records) records))
    (println (format "  violations in them                 : %,d" problems))
    (println "\n  by class:")
    (println (format "    %-16s %12s %12s %12s" "class" "violations" "records" "spellings"))
    (doseq [[c n] (sort-by val > by-class)]
      (println (format "    %-16s %12s %12s %12s"
                       (clojure.core/name c) (format "%,d" n)
                       (format "%,d" (get records-by-class c 0))
                       (format "%,d" (count (get spellings c))))))
    (println "\n  by class × the frame the literal sits in:")
    (doseq [[[c r] n] (sort-by val > by-class-role)]
      (println (format "    %-16s %-12s %,12d" (clojure.core/name c) (clojure.core/name r) n)))
    (doseq [[c syms] (sort-by (comp - count val) spellings)]
      (report-spellings c syms))
    (println "\n  ── what each widening would buy, cheapest change first ──")
    (println (format "    %-52s %13s %13s %13s" "" "violations" "records" "still refused"))
    (doseq [{cname :name} candidates
            :let [{rp :problems rr :records} (get rescued cname)]]
      (println (format "    %-52s %12.2f%% %12.2f%% %,13d"
                       cname (pct rp problems) (pct rr offending) (- offending rr))))
    tally))

(defn- naming-audit [^String log-path]
  (with-open [raf ^RandomAccessFile (files/open-log-read log-path)]
    (let [len (.length raf) t0 (System/nanoTime)]
      (loop [off 0, n 0, tally empty-naming-tally]
        (when (and (pos? n) (zero? (mod n 1000000)))
          (println (format "  … %,d records (%.0f%%)" n (* 100.0 (/ (double off) len)))))
        (if (>= off len)
          (report-naming tally (/ (- (System/nanoTime) t0) 1e6))
          (do (.seek raf off)
              (let [flen (.readInt raf) bs (byte-array flen)]
                (.readFully raf bs)
                (recur (+ off 4 (long flen)) (inc n)
                       (tally-naming (thaw-record bs) tally)))))))))

;; ---- shape survey -------------------------------------------------------

(defn- depth [x] (if (sequential? x) (inc (reduce max 0 (map depth x))) 0))

(defn- shape [pairs]
  (let [sents  (map first pairs)
        lists  (filter sequential? sents)
        arity  (frequencies (map (comp dec count) lists))
        depths (frequencies (map (fn [s] (dec (depth s))) lists)) ; 0 = flat
        preds  (frequencies (map first lists))
        args   (mapcat rest lists)
        inds   (frequencies (filter symbol? args))
        ctxs   (frequencies (map second pairs))]
    (println (format "\n══ real-corpus shape — %,d sampled facts ══" (count pairs)))
    (println (format "  distinct predicates %,d | distinct individuals(arg syms) %,d | distinct contexts %,d"
                     (count preds) (count inds) (count ctxs)))
    (println "  arity histogram (args per fact):")
    (doseq [[a c] (sort (seq arity))]
      (println (format "    arity %d: %,d  (%.0f%%)" a c (* 100.0 (/ c (double (count lists)))))))
    (println (format "  compound nesting: flat %,d | 1-deep %,d | 2+-deep %,d"
                     (get depths 0 0) (get depths 1 0) (reduce + (vals (filter (fn [[d _]] (>= d 2)) depths)))))
    (println "  top predicates by frequency (the big-posting tail):")
    (doseq [[pr c] (take 8 (sort-by val > preds))]
      (println (format "    %-24s %,d" pr c)))
    (println "  Zipf check — top individual frequencies:")
    (doseq [[in c] (take 5 (sort-by val > inds))]
      (println (format "    %-24s %,d" in c)))))

(def default-dir
  "The store the real-corpus benchmarks read, when the command line names none:
  `VAELII_BENCH_STORE`, else `VAELII_SURVEY_STORE`, else `~/.vaelii/kbs/store` — the
  KB location `vaelii.impl.catalog` already searches.  There is no store here by
  default; supply one, or pass a path as the last argument.

  Public because `records`, `densetrie` and `forward` sample the same corpus and must
  not each invent a path of their own."
  (or (System/getenv "VAELII_BENCH_STORE")
      (System/getenv "VAELII_SURVEY_STORE")
      (str (System/getProperty "user.home") "/.vaelii/kbs/store")))

(defn ensure-store!
  "Refuse `dir` unless it holds a record log to sample.

  A benchmark that samples a missing store gets an empty sequence and reports a
  complete, plausible table of numbers derived from nothing — which is worse than
  failing, because it looks like a result.  `want` is what the caller asked for; a
  store too small to answer it is refused for the same reason."
  ([dir] (ensure-store! dir 1))
  ([dir ^long want]
   (let [idx (java.io.File. (str dir "/records/sentexes.idx"))]
     (when-not (.isFile idx)
       (throw (ex-info (str "no record store at " dir
                            " — set VAELII_BENCH_STORE to an on-disk vaelii KB, or pass"
                            " a path as the last argument. None ships with the repo.")
                       {:type ::no-store :dir dir})))
     (let [total (quot (.length idx) 24)]
       (when (< total want)
         (throw (ex-info (str "store at " dir " holds " total " records; " want
                              " were asked for. A sample this size would not mean anything.")
                         {:type ::store-too-small :dir dir :have total :want want})))
       total))))

(defn- density-survey [args uniform?]
  (let [n    (or (some-> (first args) Long/parseLong) 300000)
        path (str default-dir "/records/sentexes.log")]
    (println (format "vaelii real-corpus %s survey — %,d facts (READ-ONLY)"
                     (if uniform? "UNIFORM" "front-of-log") n))
    (when-not (.exists (java.io.File. ^String path))
      (println "  store not found.") (System/exit 1))
    (let [pairs (if uniform? (uniform-pairs default-dir n) (stream-sentences path n))]
      (println (format "  sampled %,d sentences (%,d usable)" n (count pairs)))
      (shape pairs)
      (let [kb (kb/open-kb {:backend :memory :space 26 :recover? false}
                           (fn [_] nil) (fn [_] nil))]
        (p/clear-records! (:records kb)) (p/clear-index! (:index kb))
        (doseq [[s c] pairs] (try (kb/create-sentex kb s c) (catch Exception _ nil)))
        (println (format "  re-indexed %,d sentexes into a fresh :memory KB" (count (p/sentex-ids (:records kb)))))
        (postings/survey-index kb))
      (shutdown-agents))))

(defn -main [& args]
  ;; dispatch: `audit` = full sequential scan (definitive; run in background); `sample [k]`
  ;; = uniform sample by handle across the whole store (fast, unbiased); else the density
  ;; sampling survey.
  (cond
    (= "audit" (first args))
    (do (println (format "vaelii RULE AUDIT — full scan of %s/records/sentexes.log (READ-ONLY)" default-dir))
        (full-scan (str (or (second args) default-dir) "/records/sentexes.log"))
        (shutdown-agents))

    (= "naming" (first args))
    (do (println (format "vaelii NAMING AUDIT — full scan of %s/records/sentexes.log (READ-ONLY)"
                         (or (second args) default-dir)))
        (naming-audit (str (or (second args) default-dir) "/records/sentexes.log"))
        (shutdown-agents))

    (= "sample" (first args))
    (do (println (format "vaelii RULE AUDIT — uniform handle sample of %s (READ-ONLY)" default-dir))
        (uniform-sample (or (nth args 2 nil) default-dir)
                        (or (some-> (second args) Long/parseLong) 200000))
        (shutdown-agents))

    ;; `usurvey` = the density survey on a UNIFORM sample (unbiased across the whole
    ;; store), correcting the front-of-log `survey`, which reads only the homogeneous
    ;; extraction facts at the head.
    (= "usurvey" (first args)) (density-survey (rest args) true)

    :else (density-survey args false)))
