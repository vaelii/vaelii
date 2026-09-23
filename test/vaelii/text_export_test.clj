;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.text-export-test
  "Writing a KB out as a **text KB** and reading it back — `export-text!` /
  `load-text!`, the format the shipped ontology is authored in.

  The claim is a round trip through *content* rather than through state: a text KB
  carries premises only, at no handles, and a reload re-asserts them.  So what these
  tests compare is not a byte-for-byte store but the three things the claim is about —
  the canonical sentexes, the strengths they stand at, and the beliefs they reach — and
  they compare them across two KBs that minted different handles for the same knowledge.

  The other half of the claim is determinism: two KBs holding the same knowledge write
  byte-identical files whatever order they were built in, because a text KB is ordered by
  **content** and carries nothing about the run that wrote it."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.host.starter :as starter]
            [vaelii.impl.io.text :as text]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]
            [vaelii.world :as world])
  (:import (java.io File)
           (java.nio.file Files)
           (java.nio.file.attribute FileAttribute)))

;;; ── temp directories ──────────────────────────────────────────────────

(defn- temp-dir ^File [nm]
  (.toFile (Files/createTempDirectory (str "vaelii-text-" nm "-")
                                      (into-array FileAttribute []))))

(defn- rm-rf! [^File d]
  (doseq [^File f (reverse (file-seq d))] (.delete f)))

(defn- with-dirs*
  "Run `(f dir…)` on `n` temp directory *paths*, deleting them afterwards.  Each is
  removed before the body runs, since an export destination is normally one that does
  not exist yet and that is the case exercising `mkdirs`."
  [n nm f]
  (let [dirs (mapv #(temp-dir (str nm "-" %)) (range n))]
    (try (run! rm-rf! dirs)
         (apply f dirs)
         (finally (run! rm-rf! dirs)))))

;;; ── comparing two KBs by content ──────────────────────────────────────

(defn- resolve-handles
  "`sentence` with every `(sentexHandle N)` replaced by the sentence the handle names.
  A handle is this store's own number, so two KBs holding the same exceptWhen exception
  name it differently and the raw sentences differ where the knowledge does not."
  [kb form]
  (cond
    (sx/sentex-handle? form) (let [t (v/sentex kb (sx/handle-id form))]
                               (if t (list 'namedSentex (v/sentence-of t) (:context t)) form))
    (sequential? form)       (apply list (map #(resolve-handles kb %) form))
    :else                    form))

(defn- content-key
  "A stored sentex as **content**: its canonical sentence with handles resolved, its
  context, and — for a rule — the four mode fields that ride the record rather than the
  sentence.

  A `forced_decontextualized_predicate` sentence keys on no context at all.  The engine
  stores every one of them in `CxUniverse` by force, so the context is not part of what
  such a sentence says."
  [kb sx]
  (let [s (resolve-handles kb (v/sentence-of sx))
        f (when (sequential? s) (first s))]
    (cond-> [s (if (and (symbol? f) (v/has-prop? kb :forced-decontextualized f))
                 ::anywhere
                 (:context sx))]
      (:antecedent sx) (conj [(:direction sx) (:defeasible sx)
                              (:assumption sx) (:constraint sx)]))))

(defn- content [kb]
  (let [recs (:records kb)
        sxs  (into [] (keep #(p/get-sentex recs %)) (p/sentex-ids recs))]
    {:sentexes  (into #{} (map #(content-key kb %)) sxs)
     :strengths (into #{} (comp (filter #(some? (:strength %)))
                                (map #(vector (content-key kb %) (:strength %))))
                      sxs)
     :believed  (into #{} (comp (filter #(v/in? kb (:id %)))
                                (map #(content-key kb %)))
                      sxs)}))

(defn- round-trip
  "Build a KB with `build!`, export it as text into `dir`, load that into a second KB,
  and answer `[before after export-summary load-summary]` — the two `content` maps and
  the two entry points' reports.  Two KBs *sequentially*: nesting two `tu/fresh` would collide,
  both taking the scratch store pair."
  [dir build!]
  (let [[before export] (tu/with-cleared-kb [kb tu/fresh]
                          (build! kb)
                          [(content kb) (v/export-text! kb dir)])
        [after load]    (tu/with-cleared-kb [kb tu/fresh]
                          (let [r (v/load-text! kb dir)] [(content kb) r]))]
    [before after export load]))

;;; ── the KB under test ─────────────────────────────────────────────────

(defn- fresh-terms
  "One set of gensym'd temporaries, so two KBs can be built from the *same* names."
  []
  (tu/with-terms [bird penguin flies feathered happy nests Tweety Opus Rex Nest1
                  heightOf CxText]
    {:bird bird :penguin penguin :flies flies :feathered feathered :happy happy
     :nests nests :heightOf heightOf
     :Tweety Tweety :Opus Opus :Rex Rex :Nest1 Nest1 :ctx CxText}))

(defn- build!
  "Every shape a text writer can quietly drop: a known-true premise, a negative fact, a
  defeasible rule stating its own `exceptWhen`, a backward-only rule, an inert rule, a
  reified NAT in argument position, and a plain fact."
  [kb {:keys [bird penguin flies feathered happy nests heightOf
              Tweety Opus Rex Nest1 ctx]}]
  (v/assert kb (list 'genlCx ctx 'CxUniverse) 'CxUniverse)
  ;; a known-true premise — the one thing the shipped format has no spelling for
  (v/assert kb (list bird Tweety) ctx {:strength :monotonic})
  ;; a defeasible rule stating its own exception: a rule sentex plus the meta-sentex
  ;; that names it by handle, which is the pair the writer has to reassemble
  (v/assert kb (list 'exceptWhen (list penguin '?b)
                     (list 'set/defaultRule
                           (vr/rule-sentence [(list bird '?b)] (list flies '?b))))
            ctx)
  ;; the direction wrappers
  (v/assert kb (list 'set/backwardRule
                     (vr/rule-sentence [(list feathered '?f)] (list bird '?f)))
            ctx)
  (v/assert kb (list 'set/inertRule
                     (vr/rule-sentence [(list bird '?b)] (list nests '?b)))
            ctx)
  (v/assert kb (list feathered Rex) ctx)
  (v/assert kb (list bird Opus) ctx)
  (v/assert kb (list penguin Opus) ctx)
  ;; a negative fact
  (v/assert kb (list 'not (list happy Rex)) ctx)
  ;; a reified NAT in argument position: the function is declared, so the application
  ;; mints a constant and stores its termOfUnit map — all premises, all text
  (v/assert kb (list 'reifiable_function 'QuantityFn) 'CxUniverse)
  (v/assert kb (list heightOf Nest1 (list 'QuantityFn 5 'Meter)) ctx))

;;; ── the round trip ────────────────────────────────────────────────────

(deftest a-hand-built-kb-round-trips-through-text
  (let [terms (fresh-terms)]
    (with-dirs* 1 "roundtrip"
      (fn [dir]
        (let [[before after export load] (round-trip (.getPath ^File dir)
                                                     #(build! % terms))]
          (testing "the export reports what it wrote, and skipped nothing"
            (is (pos? (:sentences export)))
            (is (zero? (:skipped export)))
            (is (seq (:files export))))
          (testing "the load reads every file back"
            (is (= (set (:files export)) (set (:files load))))
            (is (= (:sentences export) (:sentences load))))
          (testing "the same canonical sentexes, at the same strengths"
            (is (= (:sentexes before) (:sentexes after)))
            (is (= (:strengths before) (:strengths after))))
          (testing "and the same beliefs"
            (is (= (:believed before) (:believed after)))))))))

(deftest a-monotonic-premise-keeps-its-class-and-a-default-carries-no-wrapper
  ;; The one thing the shipped format has no spelling for, and the reason
  ;; `(set/monotonic S)` exists: a text KB that could not say it would round-trip every
  ;; known-true premise down to a default, which is a different KB.
  (tu/with-terms [bird sings Tweety CxText]
    (with-dirs* 1 "strength"
      (fn [dir]
        (let [path (.getPath ^File dir)
              before (tu/with-cleared-kb [kb tu/fresh]
                       (v/assert kb (list 'genlCx CxText 'CxUniverse) 'CxUniverse)
                       (v/assert kb (list bird Tweety) CxText {:strength :monotonic})
                       (v/assert kb (list sings Tweety) CxText)
                       (v/export-text! kb path)
                       (slurp (io/file path (str CxText ".txt"))))]
          (testing "the known-true premise carries the wrapper and the default does not"
            (is (re-find (re-pattern (str "\\(set/monotonic \\(" bird " " Tweety "\\)\\)"))
                         before))
            (is (re-find (re-pattern (str "(?m)^\\(" sings " " Tweety "\\)$")) before)))
          (testing "and the class survives the reload"
            (tu/with-cleared-kb [kb tu/fresh]
              (v/load-text! kb path)
              (is (= :monotonic (v/defeat-class kb (v/handle-of kb (list bird Tweety) CxText))))
              (is (= :default (v/defeat-class kb (v/handle-of kb (list sings Tweety) CxText)))))))))))

(deftest two-exports-of-the-same-knowledge-are-byte-identical
  ;; Content order, never handle order, and nothing about the run in the text — so the
  ;; same knowledge asserted in two different orders writes the same bytes.
  (tu/with-terms [dog cat likes Muffet Whiskers Ann CxText]
    (let [facts [(list dog Muffet) (list cat Whiskers) (list likes Ann Muffet)
                 (list likes Ann Whiskers)]
          load! (fn [kb order]
                  (v/assert kb (list 'genlCx CxText 'CxUniverse) 'CxUniverse)
                  (doseq [f order] (v/assert kb f CxText)))]
      (with-dirs* 2 "determinism"
        (fn [a b]
          (let [pa (.getPath ^File a) pb (.getPath ^File b)]
            (tu/with-cleared-kb [kb tu/fresh]
              (load! kb facts)
              (v/export-text! kb pa))
            (tu/with-cleared-kb [kb tu/fresh]
              (load! kb (reverse facts))
              (v/export-text! kb pb))
            (let [names (fn [^File d] (sort (map #(.getName ^File %) (text/kb-files d))))]
              (is (seq (names a))
                  "the export wrote no context files — the comparison below is vacuous")
              (is (= (names a) (names b)) "the same files"))
            (doseq [n (map #(.getName ^File %) (text/kb-files a))]
              (is (= (slurp (io/file a n)) (slurp (io/file b n)))
                  (str n " is byte-identical between the two orders")))))))))

;;; ── the load side: order-insensitivity ────────────────────────────────

(deftest a-text-load-is-order-insensitive-and-puts-the-topology-first
  ;; `load-entries!` takes its `assert!` as an argument, so the two orderings it promises
  ;; are read off directly rather than inferred from a KB.  Both matter to a text KB a
  ;; person edits: a file's blocks run in natural sort order — term-centric, which is not
  ;; dependency order — and a directory's files sort alphabetically, which is not one
  ;; either.
  (testing "every genlCx is asserted first, whatever order it arrived in"
    ;; the one ordering retrying cannot supply for itself: a firing needs a placement
    ;; context, and where there is none the conclusion is DROPPED rather than refused, so
    ;; an edge arriving late leaves nothing for a retry round to see
    (let [seen    (atom [])
          entries '[[(dog Rex) CxA]
                    [(implies (and (dog ?x)) (mammal ?x)) CxB]
                    [(genlCx CxA CxB) CxA]
                    [(cat Tom) CxA]
                    [(genlCx CxB CxUniverse) CxB]]
          n       (text/load-entries! (fn [sen ctx _] (swap! seen conj [sen ctx])) entries)]
      (is (= 5 n) "every entry was read")
      (is (= '[(genlCx CxA CxB) (genlCx CxB CxUniverse)] (mapv first (take 2 @seen)))
          "both edges go in front, in the order they were written")
      (is (= '[(dog Rex) (implies (and (dog ?x)) (mammal ?x)) (cat Tom)]
             (mapv first (drop 2 @seen)))
          "and the rest keep their own order — the partition is stable, not a sort")))

  (testing "an entry refused because what it needs has not arrived yet is retried"
    ;; the docstring's own case: `(transitiveInArg largerThan 1 partOf)` files under
    ;; `largerThan` and `(transitive partOf)` under `partOf`, and `l` sorts before `p`
    (let [seen    (atom [])
          assert! (fn [sen _ _]
                    (when (and (= 'transitiveInArg (first sen))
                               (not (some #{'(transitive partOf)} @seen)))
                      (throw (ex-info "partOf is not transitive yet" {:type :arg-type})))
                    (swap! seen conj sen))
          entries '[[(transitiveInArg largerThan 1 partOf) CxA]
                    [(transitive partOf) CxA]]]
      (is (= 2 (text/load-entries! assert! entries)) "both entries were read")
      (is (= '[(transitive partOf) (transitiveInArg largerThan 1 partOf)] @seen)
          "the refused one landed on the retry round, after what it needed")))

  (testing "and one nothing can help still throws, carrying its own refusal"
    ;; a round that changes nothing re-asserts what is left WITHOUT the catch, so an
    ;; ill-formed entry reports the error it has once everything that could have helped
    ;; it is stored — rather than a generic "some entries did not load"
    (let [assert! (fn [sen _ _]
                    (if (= 'nope (first sen))
                      (throw (ex-info "no" {:type :naming :sentence sen}))
                      sen))
          e       (is (thrown? clojure.lang.ExceptionInfo
                               (text/load-entries! assert! '[[(nope X) CxA] [(fine Y) CxA]])))]
      (is (= :naming (:type (ex-data e)))
          "the entry's own refusal, not a wrapper the retry loop invented"))))

(deftest an-export-narrows-to-one-context-and-to-a-ancestor-set
  (tu/with-terms [dog cat CxUpper CxLower CxOther]
    (with-dirs* 3 "narrow"
      (fn [whole one ancestor-set]
        (let [build! (fn [kb]
                       (v/assert kb (list 'genlCx CxUpper 'CxUniverse) 'CxUniverse)
                       (v/assert kb (list 'genlCx CxLower CxUpper) 'CxUniverse)
                       (v/assert kb (list 'genlCx CxOther 'CxUniverse) 'CxUniverse)
                       (v/assert kb (list dog 'Muffet) CxUpper)
                       (v/assert kb (list cat 'Whiskers) CxLower)
                       (v/assert kb (list dog 'Rex) CxOther))]
          (tu/with-cleared-kb [kb tu/fresh]
            (build! kb)
            (let [all  (v/export-text! kb (.getPath ^File whole))
                  just (v/export-text! kb (.getPath ^File one) {:context CxLower})
                  up   (v/export-text! kb (.getPath ^File ancestor-set) {:ancestor-set CxLower})]
              (testing ":context writes that one file"
                (is (= [(str CxLower ".txt")] (:files just))))
              (testing ":ancestor set writes it and every context it sees"
                (is (contains? (set (:files up)) (str CxLower ".txt")))
                (is (contains? (set (:files up)) (str CxUpper ".txt")))
                (is (not (contains? (set (:files up)) (str CxOther ".txt")))))
              (testing "and neither writes more than the whole KB does"
                (is (<= (count (:files just)) (count (:files up)) (count (:files all)))))))
          (testing "a narrowing key nothing reads is refused"
            (tu/with-cleared-kb [kb tu/fresh]
              (is (thrown? clojure.lang.ExceptionInfo
                           (v/export-text! kb (.getPath ^File one) {:contexts [CxLower]}))))))))))

(deftest a-premise-naming-a-handle-has-no-text-form-and-is-counted
  ;; An `(except H)` is a premise whose sentence holds this store's own number.  There is
  ;; no spelling for it — the number means something else, or nothing, in the KB that
  ;; reads the file back — so it is skipped and said out loud rather than written.
  (tu/with-terms [dog Muffet CxText]
    (with-dirs* 1 "skipped"
      (fn [dir]
        (tu/with-cleared-kb [kb tu/fresh]
          (v/assert kb (list 'genlCx CxText 'CxUniverse) 'CxUniverse)
          (let [h (v/assert kb (list dog Muffet) CxText)]
            (v/assert kb (list 'except h) CxText)
            (let [r (v/export-text! kb (.getPath ^File dir))]
              (is (= 1 (:skipped r)) "the except is counted, not written")
              (is (not (re-find #"except" (slurp (io/file dir (str CxText ".txt"))))))
              (testing "and what is written still reloads"
                (is (re-find (re-pattern (str "\\(" dog " " Muffet "\\)"))
                             (slurp (io/file dir (str CxText ".txt")))))))))))))

(deftest a-text-export-refuses-a-destination-that-is-not-empty
  (tu/with-neutral-kb [kb tu/fresh]
    (with-dirs* 1 "nonempty"
      (fn [dir]
        (.mkdirs ^File dir)
        (spit (io/file dir "already-here.txt") "x")
        (let [e (is (thrown? clojure.lang.ExceptionInfo
                             (v/export-text! kb (.getPath ^File dir))))]
          (is (= :not-empty (:type (ex-data e)))))))))

(deftest a-text-export-refuses-a-destination-that-is-a-file
  ;; A text KB is read back as a whole directory of context files, so the destination has
  ;; to be one.  Named at a regular file, `mkdirs` answers false and the writer would go on
  ;; to write context files under a path that is not a directory — so the name is refused
  ;; where the caller can still change it.
  (tu/with-neutral-kb [kb tu/fresh]
    (with-dirs* 1 "onto-a-file"
      (fn [^File dir]
        (.mkdirs dir)
        (let [^File f (io/file dir "already-a-file")]
          (spit f "a file where a directory was named")
          (let [e (is (thrown? clojure.lang.ExceptionInfo
                               (v/export-text! kb (.getPath f))))]
            (is (= :not-a-directory (:type (ex-data e))))
            (is (= (.getPath f) (:dir (ex-data e))) "naming the path it was given"))
          (is (.isFile f) "and the file it refused is untouched"))))))

(deftest load-text-refuses-a-path-with-no-context-files
  (tu/with-neutral-kb [kb tu/fresh]
    (with-dirs* 1 "empty"
      (fn [dir]
        (.mkdirs ^File dir)
        (let [e (is (thrown? clojure.lang.ExceptionInfo
                             (v/load-text! kb (.getPath ^File dir))))]
          (is (= :missing-resource (:type (ex-data e)))))
        (let [e (is (thrown? clojure.lang.ExceptionInfo
                             (v/load-text! kb (str (.getPath ^File dir) "/nope"))))]
          (is (= :missing-resource (:type (ex-data e)))))))))

;;; ── the shipped schema and the test-world ─────────────────────────────

(deftest ^:slow the-shipped-schema-round-trips-through-text
  ;; The whole starter ontology — CxCore plus every upper and middle context — written
  ;; out and read back into an empty KB.  ~1300 premises across 15 files.
  (with-dirs* 1 "starter"
    (fn [dir]
      (let [[before after export load] (round-trip (.getPath ^File dir) starter/load-into)]
        (is (zero? (:skipped export)) "every premise of the shipped schema has a text form")
        (is (= (count (:files export)) (:contexts load)))
        (is (pos? (:sentences load)))
        (is (= (:sentexes before) (:sentexes after)))
        (is (= (:strengths before) (:strengths after)))
        (is (= (:believed before) (:believed after)))))))

(deftest ^:slow the-test-world-round-trips-through-text
  ;; The starter plus the whole test-world — the cast, the four fables and the
  ;; story-understanding examples — which is where the `exceptWhen` rules, the
  ;; `set/defaultRule`s and the story contexts live.
  (with-dirs* 1 "world"
    (fn [dir]
      (let [[before after export _] (round-trip (.getPath ^File dir)
                                                #(-> % starter/load-into world/load-into))]
        (is (zero? (:skipped export)))
        (is (= (:sentexes before) (:sentexes after)))
        (is (= (:strengths before) (:strengths after)))
        (is (= (:believed before) (:believed after)))))))
