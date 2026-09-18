;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.round-trip-test
  "Export a KB and import it back: the oracle for the portable dump.

  It compares two **KBs**, not two files, because what a dump promises is not bytes —
  it is that the knowledge comes back.  So every comparison is over *content*: a handle
  is a number this build minted and a round trip never promised the same numbers, which
  is why a sentence embedding one (`(exceptWhen … (sentexHandle H))`) is compared by
  what the handle names rather than by the number.

  Where the two sides disagree, the reading side is right by construction — it
  re-canonicalizes everything through this build's own constructor — so a difference is
  a lossy *writer*.

  Both directions across backends (`:memory` → dump → `:disk-log`, and back), because a
  format that only round-trips within one backend is not a format."
  (:require [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.test :refer [deftest is testing]]
            [clojure.walk :as walk]
            [vaelii.browser.catalog :as catalog]
            [vaelii.core :as v]
            [vaelii.impl.disk.backend :as backend]
            [vaelii.impl.io.export :as export]
            [vaelii.impl.io.frames :as frames]
            [vaelii.impl.io.import :as imp]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu])
  (:import (java.io File)
           (java.nio.file Files)
           (java.nio.file.attribute FileAttribute)))

;;; ── scaffolding ───────────────────────────────────────────────────────

(defn- temp-dir ^File [nm]
  (.toFile (Files/createTempDirectory (str "vaelii-rt-" nm "-") (into-array FileAttribute []))))

(defn- rm-rf! [^File d]
  (doseq [^File f (reverse (file-seq d))] (.delete f)))

(defn- memory-kb
  "A cleared plain `:memory` KB (`tu/plain-memory-space`) whatever the suite's backend
  gate says — this namespace is *about* the two backends, so it names both."
  []
  (doto (v/open-kb tu/plain-memory-space) (tu/clear-kb!)))

(defn- disk-kb [^File dir]
  (v/open-kb {:backend :disk-log :dir (.getPath dir) :recover? false}))

;;; ── the KB under test ─────────────────────────────────────────────────

(defn- terms []
  (tu/with-terms [bird penguin animal flies feathered nests happy
                  parentOf grandparentOf ancestorOf
                  Tweety Opus Rex Ann Bob Cid Preferred Deprecated
                  CxStory CxSubStory]
    {:bird bird :penguin penguin :animal animal :flies flies :feathered feathered
     :nests nests :happy happy
     :parentOf parentOf :grandparentOf grandparentOf :ancestorOf ancestorOf
     :Tweety Tweety :Opus Opus :Rex Rex :Ann Ann :Bob Bob :Cid Cid
     :Preferred Preferred :Deprecated Deprecated
     :ctx CxStory :sub CxSubStory}))

(defn- build!
  "Every shape a round trip has ever dropped, in one KB."
  [kb {:keys [bird penguin animal flies feathered nests happy
              parentOf grandparentOf ancestorOf
              Tweety Opus Rex Ann Bob Cid Preferred Deprecated ctx sub]}]
  (binding [v/*clock*   (constantly 1750000000000)
            v/*creator* "round-trip-test"]
    ;; a taxonomy to recover: a genl edge and a context edge
    (v/assert kb (list 'genl penguin bird) ctx {:strength :monotonic})
    (v/assert kb (list 'genl bird animal) ctx {:strength :monotonic})
    (v/assert kb (list 'genlCx sub ctx) sub)
    ;; a defeasible forward rule that states its own exception, and a second rule
    ;; concluding the same literal — so `(flies Tweety)` rests on two justifications
    (v/assert kb (list 'exceptWhen (list penguin '?b)
                       (list 'set/defaultRule
                             (list 'set/forwardRule (vr/rule-sentence [(list bird '?b)] (list flies '?b)))))
              ctx)
    (v/assert kb (list 'set/forwardRule (vr/rule-sentence [(list feathered '?f)]
                                                          (list flies '?f)))
              ctx)
    ;; a backward-only rule, and a rule with a conjunctive antecedent whose variables
    ;; the canonical form renumbers
    (v/assert kb (list 'set/backwardRule (vr/rule-sentence [(list flies '?a)] (list nests '?a)))
              ctx)
    (v/assert kb (vr/rule-sentence [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                                   (list grandparentOf '?x '?z))
              ctx {:direction :forward})
    ;; ground facts, one known-true, and the join that fires the conjunctive rule
    (v/assert kb (list bird Tweety) ctx {:strength :monotonic})
    (v/assert kb (list feathered Tweety) ctx)
    (v/assert kb (list bird Opus) ctx)
    (v/assert kb (list penguin Opus) ctx)          ; blocks the flight rule for Opus
    (v/assert kb (list parentOf Ann Bob) ctx)
    (v/assert kb (list parentOf Bob Cid) ctx)
    ;; a negative fact, defeated by the known-true positive: stored, not believed
    (v/assert kb (list 'not (list happy Rex)) ctx)
    (v/assert kb (list happy Rex) ctx {:strength :monotonic})
    ;; an equality merge: the retired spelling is superseded, and what mentioned it
    ;; gets a derived twin under the representative
    (v/assert kb (list bird Deprecated) sub)
    (v/assert kb (list 'rewriteOf Preferred Deprecated) ctx)
    ;; provenance an application layered on afterwards
    (v/add-provenance kb (v/handle-of kb (list bird Tweety) ctx) {:source :field-guide})
    ;; a term the ancestor rule mentions nowhere else, so the vocabulary is not
    ;; accidentally the same set twice
    (v/assert kb (list 'set/inertRule (vr/rule-sentence [(list parentOf '?p '?q)]
                                                        (list ancestorOf '?p '?q)))
              ctx)))

;;; ── the oracle ────────────────────────────────────────────────────────

(defn- deref-handles
  "A sentence with every `(sentexHandle H)` replaced by the *content* H names.  A
  meta-sentex points at a rule by number; the round trip promises the same rule, not
  the same number."
  [kb sentence]
  (walk/postwalk (fn [x]
                   (if-let [id (sx/handle-id x)]
                     (list 'sentexHandle (v/sentence-of (v/sentex kb id)))
                     x))
                 sentence))

(defn- content
  "A sentex as content: its whole field map, minus the handle, with embedded handles
  dereferenced.  The *whole* map, because the fields a translation drops silently are
  `:varmap` (every rule then renders as ?var0), `:direction` and `:defeasible`."
  [kb sx]
  (-> (into {} sx)
      (dissoc :id)
      (update :sentence #(deref-handles kb %))))

(defn- content-of [kb h] (some->> (v/sentex kb h) (content kb)))

(defn- same!
  "Assert two collections of content hold the same things, reporting **what differs**
  rather than both sides in full — a KB printed twice is unreadable, and the answer to
  \"what did the round trip lose\" is a handful of records."
  [label source target]
  (let [a (set source) b (set target)]
    ;; a snapshot that came out empty would make every comparison below pass on nothing
    (is (pos? (count source)) (str label ": the fixture holds none — the oracle is vacuous"))
    (is (= (count source) (count a)) (str label ": source content is not unique"))
    (is (empty? (set/difference a b)) (str label " — in the source and not the copy"))
    (is (empty? (set/difference b a)) (str label " — in the copy and not the source"))))

(defn- sentex-contents [kb]
  (map #(content-of kb %) (p/sentex-ids (:records kb))))

(defn- justification-contents
  "Every justification as content: what it rests on, what it concludes, what licensed
  it, and the class it confers."
  [kb]
  (vec
   (for [jid (p/justification-ids (:records kb))
         :let [j (v/justification kb jid)]]
     {:antecedents (set (map #(content-of kb %) (:antecedents j)))
      :consequence (content-of kb (:consequence j))
      :informant   (if (integer? (:informant j)) (content-of kb (:informant j)) (:informant j))
      :bindings    (:bindings j)
      :strength    (:strength j)})))

(defn- beliefs
  "What is believed, keyed by content — and for what is not, the reason `why-not` gives,
  since \"not believed\" is several different situations and a round trip has to land in
  the same one."
  [kb]
  (vec
   (for [h (p/sentex-ids (:records kb))
         :let [in? (v/in? kb h)]]
     [(content-of kb h) (if in? :in (:reason (v/why-not kb h)))])))

(defn- taxonomy [kb]
  {:types    (set (v/types kb))
   :contexts (set (v/contexts kb))
   :genls    (into {} (for [t (v/types kb)] [t (set (v/genls kb t))]))
   :up       (into {} (for [c (v/contexts kb)] [c (set (v/context-up kb c))]))})

(defn- provenance-contents [kb]
  (vec (for [h (p/sentex-ids (:records kb))
             :let [prov (v/provenance kb h)]
             :when prov]
         [(content-of kb h) prov])))

(defn- compare-kbs!
  "Assert `target` holds the same knowledge as `source`."
  [source target]
  (testing "the same stored sentences"
    (same! "sentences" (sentex-contents source) (sentex-contents target)))
  (testing "the same justifications, as what they rest on"
    (same! "justifications" (justification-contents source) (justification-contents target)))
  (testing "the same beliefs, and the same reason for each that is not believed"
    (same! "beliefs" (beliefs source) (beliefs target)))
  (testing "the same taxonomy after recover"
    (is (= (taxonomy source) (taxonomy target))))
  (testing "the same provenance"
    (same! "provenance" (provenance-contents source) (provenance-contents target)))
  (testing "the same vocabulary"
    (is (= (set (v/terms source)) (set (v/terms target))))))

(defn- round-trip!
  "Build a KB with `open-source`, export it, import into a KB from `open-target`, and
  run `(f source target summary)`."
  [open-source open-target f]
  (let [dump (temp-dir "dump")]
    (rm-rf! dump)                                   ; export! makes its own directory
    (let [t      (terms)
          source (open-source)
          target (open-target)]
      (try
        (build! source t)
        (export/export! source dump {:compression :none})
        (let [summary (imp/import-dump target dump)]
          (f source target summary t))
        (finally (rm-rf! dump))))))

;;; ── the round trips ───────────────────────────────────────────────────

(deftest memory-out-disk-in
  (let [store (temp-dir "disk-in")]
    (try
      (tu/with-cleared-kb [_ memory-kb]
        (round-trip!
         (fn [] (memory-kb))                        ; the same cleared scratch KB
         (fn [] (disk-kb store))
         (fn [source target summary _t]
           (testing "the summary says what it read and what it did with the handles"
             (is (= :vaelii (:dialect summary)))
             (is (= :preserved (:handle-policy summary)))
             (is (zero? (:collapsed summary)) "nothing canonicalized onto another handle")
             (is (zero? (:rewritten-handles summary))
                 "nothing to rewrite: the embedded handle is already the right number")
             (is (zero? (:dropped-justifications summary)))
             (is (zero? (:dropped-meta-sentexes summary))))
           (compare-kbs! source target))))
      (finally (backend/close-dir! (.getPath store)) (rm-rf! store)))))

(deftest disk-out-memory-in
  (let [store (temp-dir "disk-out")]
    (try
      (tu/with-cleared-kb [_ memory-kb]
        (round-trip!
         (fn [] (disk-kb store))
         (fn [] (memory-kb))
         (fn [source target _summary _t] (compare-kbs! source target))))
      (finally (backend/close-dir! (.getPath store)) (rm-rf! store)))))

;;; ── handles ───────────────────────────────────────────────────────────

(defn- meta-sentexes
  "The `exceptWhen` meta-sentexes, as `[own-handle embedded-handle]` — the one place a
  handle is stored *inside content*, and so the one place its number has to be right
  rather than merely consistent."
  [kb]
  (set (for [h (p/sentex-ids (:records kb))
             :let [s (v/sentence-of (v/sentex kb h))]
             :when (and (seq? s) (= 'exceptWhen (first s)))]
         [h (first (keep sx/handle-id (tree-seq sequential? seq s)))])))

(deftest handles-are-identity-across-the-round-trip
  ;; The comparisons above are deliberately handle-free, because content is what a dump
  ;; owes.  This is the stronger claim ours makes on top: the numbers come back too.  An
  ;; index entry is a posting of handles, so replaying one is possible only over an
  ;; import that keeps them; and a caller holding a handle across an export/import cycle
  ;; is holding a reference rather than a coincidence.
  (let [store (temp-dir "handles")]
    (try
      (tu/with-cleared-kb [_ memory-kb]
        (round-trip!
         (fn [] (memory-kb))
         (fn [] (disk-kb store))
         (fn [source target _summary t]
           (let [sx-ids (p/sentex-ids (:records source))]
             (testing "the same sentex handles, each holding the same record"
               (is (= sx-ids (p/sentex-ids (:records target))))
               (doseq [h sx-ids]
                 (is (= (content-of source h) (content-of target h))
                     (str "handle " h " holds a different record"))))

             (testing "and the same justification handles"
               (is (= (p/justification-ids (:records source))
                      (p/justification-ids (:records target)))))

             (testing "so the handle a meta-sentex embeds is the same number, not just the same rule"
               (is (seq (meta-sentexes source)) "the fixture has one, or this proves nothing")
               (is (= (meta-sentexes source) (meta-sentexes target))))

             (testing "and the imported KB is still usable: a fresh assert cannot collide"
               ;; the corruption this exists to prevent — a counter left behind the
               ;; imported handles overwrites a record on the very next write.  Last,
               ;; because it adds to the target.
               (let [ceiling (apply max (concat sx-ids (p/justification-ids (:records target))))
                     h       (v/assert target (list (:bird t) (:Rex t)) (:ctx t))]
                 (is (< ceiling h))
                 (doseq [h sx-ids]
                   (is (some? (v/sentex target h))
                       (str "handle " h " was overwritten by the assert")))))))))
      (finally (backend/close-dir! (.getPath store)) (rm-rf! store)))))

(deftest the-public-pair-is-a-round-trip-too
  ;; Every trip above calls `export/export!` and `imp/import-dump` — the implementations,
  ;; reached through this namespace's own `:require`.  `v/import!` is the *public* half
  ;; and it does not require its reader: it goes through `vaelii.impl.wiring`'s delayed
  ;; `requiring-resolve`, which is the call a load-order break lands on and the one a
  ;; direct call to `imp/import-dump` steps over.  So the public pair gets a trip of its
  ;; own, calling nothing else.
  ;;
  ;; It is a round trip and not a smoke test because the claim `import!`'s docstring
  ;; makes is exactly the claim `compare-kbs!` checks: a dump whose two halves are not
  ;; both public is not a round trip.
  (let [dump  (temp-dir "public-dump")
        store (temp-dir "public-store")]
    (rm-rf! dump)                                   ; export! makes its own directory
    (try
      (tu/with-cleared-kb [_ memory-kb]
        (let [t      (terms)
              source (memory-kb)
              target (disk-kb store)]
          (build! source t)
          (let [written (v/export! source dump {:compression :none})
                summary (v/import! target dump)]
            (is (= (v/sentex-count source) (:sentexes written))
                "the writer reports what it wrote")
            (is (= :vaelii (:dialect summary)))
            (is (= :preserved (:handle-policy summary)))
            (compare-kbs! source target))))
      (finally (backend/close-dir! (.getPath store))
               (rm-rf! store) (rm-rf! dump)))))

(deftest records-only-reads-our-dialect-too
  ;; The `{:belief? false}` path exists for a corpus past what the JTMS scales to.  It
  ;; shares one fn with the belief path — `field-map->sentence` — so the dialect
  ;; discrimination has to hold there as well: the corpus lands stored and indexed, with
  ;; no TMS behind it.
  (let [dump (temp-dir "records-only")]
    (rm-rf! dump)
    (try
      (let [t (terms)]
        (tu/with-cleared-kb [source memory-kb]
          (build! source t)
          (export/export! source dump {:compression :none})
          (let [store (temp-dir "records-only-store")]
            (try
              (let [target  (disk-kb store)
                    summary (imp/import-dump target dump {:belief? false})]
                (is (false? (:belief? summary)))
                (is (= (v/sentex-count source) (:sentexes summary) (v/sentex-count target)))
                (is (zero? (:justifications summary)) "no belief, so nothing rests on anything")
                (is (seq (v/find-sentexes target (:Tweety t)))
                    "and the corpus is indexed — findable by any term it mentions"))
              (finally (backend/close-dir! (.getPath store)) (rm-rf! store))))))
      (finally (rm-rf! dump)))))

(deftest records-only-keeps-the-premises-a-later-recover-believes-from
  ;; `recover` is what turns this corpus into a believing KB, and it believes from the
  ;; premise roster and the strengths on the records.  Stored strength-less, the rebuild
  ;; still builds a node per handle — so the KB comes back looking whole and believes
  ;; **nothing**, every handle a derivation with no justification to ground it.  So the
  ;; records-only path stores each record of ours the way the belief path stores it,
  ;; minus the TMS it deliberately does not build.
  (let [dump (temp-dir "records-only-premises")]
    (rm-rf! dump)
    (try
      (let [t (terms)]
        (tu/with-cleared-kb [source memory-kb]
          (build! source t)
          (export/export! source dump {:compression :none})
          (let [store (temp-dir "records-only-premises-store")]
            (try
              (let [target (disk-kb store)]
                (imp/import-dump target dump {:belief? false})
                (testing "the corpus arrives with its premises and their strengths"
                  (is (seq (tu/premise-ids target)))
                  (is (every? #(some? (:strength (v/sentex target %))) (tu/premise-ids target))
                      "a premise the roster names carries the strength the dump held"))
                (testing "and nothing is believed yet — there is no TMS behind it"
                  (is (empty? (v/sentexes-matching target (list (:bird t) (:Tweety t))
                                                   (:ctx t)))))
                (v/recover target)
                (testing "so the recover has something to believe from, and does"
                  (is (seq (v/sentexes-matching target (list (:bird t) (:Tweety t)) (:ctx t))))
                  (is (seq (v/sentexes-matching target (list (:parentOf t) (:Ann t) (:Bob t))
                                                (:ctx t))))
                  (is (v/genl? target (:penguin t) (:bird t))
                      "the taxonomy is rebuilt off believed edges, so it answers too")))
              (finally (backend/close-dir! (.getPath store)) (rm-rf! store))))))
      (finally (rm-rf! dump)))))

(deftest stored-belief-is-the-belief-load-minus-the-settling
  ;; The claim `{:belief? :stored}` makes, stated as the equality that defines it: a dump
  ;; read `:stored` and then `recover`ed is the same KB as one read `{:belief? true}`.
  ;; Everything before the recover is a write to the store, and the recover reads the
  ;; store — so the only thing deferring it can change is *when*.
  (let [dump (temp-dir "stored-belief")]
    (rm-rf! dump)
    (try
      (let [t (terms)]
        (tu/with-cleared-kb [source memory-kb]
          (build! source t)
          (export/export! source dump {:compression :none})
          (let [a (temp-dir "stored-a") b (temp-dir "stored-b")]
            (try
              (let [deferred (disk-kb a)
                    eager    (disk-kb b)
                    s-def    (imp/import-dump deferred dump {:belief? :stored})
                    _        (imp/import-dump eager dump {:belief? true})]
                (testing "the summary says which load ran"
                  (is (= :stored (:belief? s-def)))
                  (is (pos? (:justifications s-def)) "belief is stored, not skipped")
                  (is (pos? (:premises s-def))))
                (testing "and nothing is believed yet — the network was never built"
                  (is (empty? (v/sentexes-matching deferred (list (:bird t) (:Tweety t))
                                                   (:ctx t))))
                  (is (not (v/genl? deferred (:penguin t) (:bird t)))
                      "the taxonomy is built by the same pass and is likewise absent"))
                (testing "the store holds everything the eager load's store holds"
                  (is (= (v/sentex-count eager) (v/sentex-count deferred)))
                  (is (= (count (tu/premise-ids eager)) (count (tu/premise-ids deferred)))))
                (v/recover deferred)
                (testing "so recovering it later lands where loading it eagerly landed"
                  (compare-kbs! eager deferred)))
              (finally (backend/close-dir! (.getPath a)) (rm-rf! a)
                       (backend/close-dir! (.getPath b)) (rm-rf! b))))))
      (finally (rm-rf! dump)))))

;;; ── a frame this build will not construct ─────────────────────────────
;;; No live KB can hold one, because the structural checks run inside the constructor
;;; — which is exactly why a *dump* can: an older build, or another engine, stored a
;;; rule under a narrower check than this one runs.  So the fixture splices a frame
;;; into a real export rather than asserting one.

(def ^:private unclosed-rule
  ;; `?l` occurs in one antecedent and nowhere else, so the deferred `lessThan` reaches
  ;; the join with an input nothing bound.  `check-naf-closed` refuses it; the shape is a
  ;; hand-written rule of the kind a foreign dump carries and this check rejects.
  '(set/backwardRule
    (implies (and (lessThan ?x ?l) (canBeStackedWith ?x ?y)) (movable ?x ?y))))

(defn- splice-refused-frame!
  "Append a frame carrying `sentence` to `dir`'s sentex stream and tell `meta.edn` about
  it, so the dump states a count the stream can still meet.  The frame carries no
  `:antecedent`, so the reader hands the sentence to the constructor as written — which
  is the whole point: the refusal has to happen on the reading side."
  [^File dir sentence context]
  (let [meta*  (read-string (slurp (io/file dir "meta.edn")))
        stream (io/file dir "sentexes.nippy.stream")
        frames (vec (frames/read-chunked-seq stream (:compression meta* :none)))
        added  {:id (inc (long (apply max 0 (keep :id frames))))
                :sentence sentence
                :context context}]
    (frames/write-frames! stream (conj frames added)
                          {:compression (:compression meta* :none) :chunk-size 64})
    (spit (io/file dir "meta.edn")
          (pr-str (update meta* :sentex-count inc)))
    added))

(deftest a-frame-this-build-cannot-construct-is-counted-not-fatal
  ;; The other entry point's policy, applied to the structural one.  A name `assert` would
  ;; refuse is stored and counted; a *sentence* this build will not construct cannot be
  ;; stored at all, so it is skipped and counted — and the load finishes either way.
  ;; One refusal taking down a finished pass over millions of good frames is the
  ;; behaviour this replaces.
  (let [dump (temp-dir "refused-frame")]
    (rm-rf! dump)
    (try
      (let [t (terms)]
        (tu/with-cleared-kb [source memory-kb]
          (build! source t)
          (export/export! source dump {:compression :none})
          (let [good (v/sentex-count source)]
            (splice-refused-frame! dump unclosed-rule (:ctx t))
            (testing "records-only"
              (tu/with-cleared-kb [target memory-kb]
                (let [s (imp/import-dump target dump {:belief? false})]
                  (is (= 1 (get-in s [:refused :skipped])))
                  (is (= {:naf-not-closed 1} (get-in s [:refused :by-type])))
                  (is (= (inc good) (get-in s [:refused :checked]))
                      ":checked is the frame count, so the ratio means something")
                  (is (= good (:sentexes s)) "the refused frame is not stored")
                  (is (= (inc good) (:frames s)) "but the stream did yield it")
                  (is (= good (v/sentex-count target))))))
            (testing "and the belief path, which is the one that had hours to lose"
              (tu/with-cleared-kb [target memory-kb]
                (let [s (imp/import-dump target dump {:belief? true})]
                  (is (= 1 (get-in s [:refused :skipped])))
                  (is (= good (:sentexes s)))
                  (is (pos? (:justifications s))
                      "and the rest of the dump landed, belief included")))))))
      (finally (rm-rf! dump)))))

(deftest a-torn-stream-is-still-torn
  ;; The counterpart, and the reason the truncation check reads the frame count from the
  ;; stream rather than from the store: a skipped frame shortens the store, and if that
  ;; were what the check compared it would read every refusal as a torn file — turning a
  ;; tolerated frame back into a fatal one under a different name.
  (let [dump (temp-dir "torn")]
    (rm-rf! dump)
    (try
      (tu/with-cleared-kb [source memory-kb]
        (build! source (terms))
        (export/export! source dump {:compression :none})
        ;; state more sentexes than the stream holds — a torn tail, exactly
        (let [meta* (read-string (slurp (io/file dump "meta.edn")))]
          (spit (io/file dump "meta.edn")
                (pr-str (update meta* :sentex-count + 5))))
        (tu/with-cleared-kb [target memory-kb]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"torn or truncated"
                                (imp/import-dump target dump {:belief? false})))))
      (finally (rm-rf! dump)))))

(deftest a-torn-justification-stream-is-torn-too
  ;; The sentex stream is not the only one `meta.edn` counts, and it is not the one with
  ;; the most to lose: a truncated `justifications.nippy.stream` is indistinguishable from a clean EOF
  ;; exactly as a truncated sentex stream does, and what it costs is *belief* — every
  ;; conclusion whose justification was in the lost tail comes back unsupported, on a KB
  ;; that reports a clean import.  The count is the only witness either stream leaves.
  (let [dump (temp-dir "torn-just")]
    (rm-rf! dump)
    (try
      (tu/with-cleared-kb [source memory-kb]
        (build! source (terms))
        (export/export! source dump {:compression :none})
        (let [meta* (read-string (slurp (io/file dump "meta.edn")))]
          (is (pos? (long (:justification-count meta*)))
              "the corpus carries justifications for the check to be about")
          (spit (io/file dump "meta.edn")
                (pr-str (update meta* :justification-count + 5))))
        (tu/with-cleared-kb [target memory-kb]
          ;; `:stored` rather than `true`: the justification stream is read on both, and
          ;; this one skips the `recover` the check is not about
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"torn or truncated"
                                (imp/import-dump target dump {:belief? :stored}))
              "the belief path reads it")))
      (finally (rm-rf! dump)))))

(deftest an-unknown-belief-value-is-refused-by-name
  ;; The option has three values, so a mistyped one is the quiet failure the key check
  ;; already guards against: anything truthy would otherwise mean `true` and run the
  ;; recover the caller asked to defer.
  (let [dump (temp-dir "belief-value")]
    (rm-rf! dump)
    (try
      (tu/with-cleared-kb [source memory-kb]
        (build! source (terms))
        (export/export! source dump {:compression :none})
        (tu/with-cleared-kb [target memory-kb]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unknown :belief\? value"
                                (imp/import-dump target dump {:belief? :store})))
          (testing "and the refusal lands before anything is written"
            (is (zero? (v/sentex-count target))))))
      (finally (rm-rf! dump)))))

(deftest a-dump-that-carries-an-out-list-is-refused
  ;; A justification frame is a field map, so a dump can carry an `:out` key — a
  ;; negation-as-failure antecedent set, which a `Justification` has no slot for
  ;; (docs/naf.md).  This entry point is the only place a filled one could reach the
  ;; store.  Imported without it, the justification would support its conclusion where
  ;; the exporting KB's did not, so it is refused here, where the frame is still legible.
  ;;
  ;; And refused **before the import writes anything**, which is the other half of what
  ;; a refusal means: the frames come off a file, so the check reads them in a pre-pass
  ;; and a dump this build will not accept never reaches the store.  Run from inside the
  ;; justification loop instead, it fires after the whole sentex phase has landed and
  ;; after every earlier frame is stored — and an import is not a transaction, so the KB
  ;; keeps every sentex the dump had, an arbitrary prefix of its justifications, no
  ;; premise marks and no `recover`, and `assert-empty-destination!` refuses the retry
  ;; until somebody clears the store by hand.
  (let [dump (temp-dir "naf-out")]
    (rm-rf! dump)
    (try
      (tu/with-cleared-kb [kb memory-kb]
        (build! kb (terms))
        (export/export! kb dump {:compression :none})
        (let [f      (io/file dump "justifications.nippy.stream")
              frames (vec (frames/read-chunked-seq f :none))
              victim (first frames)
              stored (fn [] [(count (p/sentex-ids (:records kb)))
                             (count (p/justification-ids (:records kb)))])]
          (is (seq frames) "the fixture derived something, so there is a frame to fill")
          (is (not (contains? victim :out)) "and the writer writes no :out key")
          (frames/write-frames! f
                                (cons (assoc victim :out #{(:consequence victim)})
                                      (rest frames))
                                {:compression :none :chunk-size 10000})
          (tu/clear-kb! kb)
          (is (= [0 0] (stored)) "the destination starts empty, as the importer demands")
          (let [e (is (thrown? clojure.lang.ExceptionInfo (imp/import-dump kb dump)))]
            (is (= :naf-justification (:type (ex-data e))))
            (is (= [(:consequence victim)] (:out (ex-data e)))
                "and it names the slot it refused, not just the frame"))
          (testing "and the store is untouched — nothing landed on the way to the refusal"
            (is (= [0 0] (stored))
                "no sentex, no justification: the dump was read before it was written")
            (is (empty? (tu/premise-ids kb)))
            (is (empty? (v/terms kb)) "and no term was minted into the index either"))
          (testing "so the retry needs no clear! — the empty-destination gate still passes"
            (frames/write-frames! f frames {:compression :none :chunk-size 10000})
            (let [summary (imp/import-dump kb dump)]
              (is (pos? (:sentexes summary)))
              (is (pos? (:justifications summary))
                  "the repaired dump imports into the same KB the refusal left behind")))))
      (finally (rm-rf! dump)))))

;;; ── a meta-sentex the import drops, and what rested on it ─────────────
;;; A **remapped** import rewrites the `(sentexHandle H)` a meta-sentex stores inside its
;;; own sentence, and drops the meta-sentex when H names no record — an exception on a
;;; rule that is not here.  The drop is a deletion, and every other reference to that
;;; record resolves through the same id map, so the map is where the record has to stop
;;; existing too.  On a real dump the reference that survives a deletion is not rare — a
;;; percent or so of the justifications named one — so this is a common case, not an edge.

(defn- dangling-refs
  "Every `[justification-id handle]` where a stored justification names a sentex handle
  the store does not hold.  The whole-store form of the audit that found this: a
  justification is a claim about records, and one that names a record nobody can read is
  a claim about nothing."
  [kb]
  (let [rec  (:records kb)
        live (set (p/sentex-ids rec))]
    (vec (for [jid (p/justification-ids rec)
               :let [j (v/justification kb jid)]
               h   (concat (:antecedents j) [(:consequence j)] [(:informant j)])
               :when (and (integer? h) (not (live h)))]
           [jid h]))))

(defn- splice-orphaning-dump!
  "Edit `dir` into the structure that drops a meta-sentex with something resting on it, and
  return `{:meta-id … :rests-on-it …}`.

  Three edits, and each one stands for something a foreign dump has.  The
  meta-sentex's embedded handle is pointed at a dump id no frame carries, so the rewrite
  cannot resolve it and the record is dropped.  A justification frame is hung off the
  meta-sentex — which our own writer never produces (an exception blocks a rule, it does
  not support a conclusion) and another engine's deduction stream routinely does.  And
  one sentex frame is duplicated under a fresh id so the import
  **collapses** it and is therefore `:remapped`, which is the only mode that rewrites an
  embedded handle at all."
  [^File dir]
  (let [meta*   (read-string (slurp (io/file dir "meta.edn")))
        comp*   (:compression meta* :none)
        sx-file (io/file dir "sentexes.nippy.stream")
        j-file  (io/file dir "justifications.nippy.stream")
        frames  (vec (frames/read-chunked-seq sx-file comp*))
        jframes (vec (frames/read-chunked-seq j-file comp*))
        embeds? (fn [s] (some sx/sentex-handle? (tree-seq sequential? seq s)))
        meta-fr (first (filter #(embeds? (:sentence %)) frames))
        plain   (first (remove #(embeds? (:sentence %)) frames))
        ghost   (+ 1000 (long (apply max (keep :id frames))))
        frames* (conj (mapv (fn [f]
                              (cond-> f
                                (= (:id f) (:id meta-fr))
                                (update :sentence
                                        #(walk/postwalk
                                          (fn [x] (if (sx/handle-id x)
                                                    (sx/sentex-handle ghost) x))
                                          %))))
                            frames)
                      (assoc plain :id (inc ghost)))   ; a duplicate: collapses on import
        next-j  (inc (long (apply max 0 (keep :id jframes))))
        jframe  {:id next-j
                 :informant   :import
                 :antecedents [(:id meta-fr)]
                 :consequence (:id plain)
                 :bindings    {}
                 :strength    :monotonic}
        ;; the same, plus a sentex this dump never carried: dropped either way, so the
        ;; deletion is not what cost it and the orphan count must not claim it
        doomed  (assoc jframe :id (inc next-j)
                       :antecedents [(:id meta-fr) (+ ghost 500)])]
    (is (some? meta-fr) "the fixture exports a meta-sentex, or this proves nothing")
    (frames/write-frames! sx-file frames* {:compression comp* :chunk-size 64})
    (frames/write-frames! j-file (conj jframes jframe doomed)
                          {:compression comp* :chunk-size 64})
    (spit (io/file dir "meta.edn")
          (pr-str (-> meta*
                      (update :sentex-count inc)
                      (cond-> (:justification-count meta*)
                        (update :justification-count + 2)))))
    {:meta-id (:id meta-fr) :rests-on-it (:id jframe) :doomed (:id doomed)}))

(deftest a-dropped-meta-sentex-takes-the-justifications-that-name-it
  ;; The import deletes the meta-sentex and reports it.  What this pins is the other half:
  ;; the id map forgets the dump id along with the record, so every reference to it fails
  ;; to resolve and is dropped through the path a dangling reference already has — and no
  ;; justification is left naming a handle the store does not hold.
  (let [dump (temp-dir "orphaned-meta")]
    (rm-rf! dump)
    (try
      (tu/with-cleared-kb [source memory-kb]
        (build! source (terms))
        (export/export! source dump {:compression :none})
        (splice-orphaning-dump! dump)
        (tu/with-cleared-kb [target memory-kb]
          (let [s (imp/import-dump target dump {:belief? :stored})]
            (testing "the load is remapped, so the embedded handles are rewritten at all"
              (is (= :remapped (:handle-policy s)))
              (is (= 1 (:collapsed s))))
            (testing "and it says what it dropped, and what that took with it"
              (is (= 1 (:dropped-meta-sentexes s)))
              (is (= 1 (:orphaned-ids s)) "one dump id now names no record")
              (is (= 2 (:dropped-justifications s)))
              (is (= 1 (:dropped-justifications-orphaned s))
                  "one of the two: the other also names a sentex the dump never carried,
                   and a justification the dump had already lost is not this load's doing"))
            (testing "so nothing in the store rests on a record the store does not hold"
              (is (empty? (dangling-refs target))))
            (testing "and the recover the :stored mode defers reads a consistent store"
              (v/recover target)
              (is (empty? (dangling-refs target)))))))
      (finally (rm-rf! dump)))))

(deftest recover-leaves-out-a-justification-that-rests-on-nothing
  ;; What `recover` does when a store holds one anyway.  It can: the records are a durable
  ;; store and `delete-sentex!` is on its protocol, so a caller, another dialect's loader,
  ;; or a repair script can leave a justification naming a handle nobody can read.
  ;;
  ;; `rebuild-tms` is the one path whose justifications come off a store rather than out of
  ;; a firing, and so the only one that can reach `add-justification` with a datum that has
  ;; no node.  That call does not refuse it — the reference representation mints a phantom
  ;; and the dense one is not specified there (`vaelii.impl.dense-jtms` states the
  ;; precondition) — and a justification *concluding* the phantom would make it IN, so the
  ;; KB would come back believing a record it cannot show anyone and believing everything
  ;; drawn from it.  Neither half of that is visible to a reader: the handle reads absent
  ;; and its belief reads true.
  ;;
  ;; So the rebuild leaves such a justification out and counts it, which is the policy
  ;; `io.import` takes at the other end of the same store.  Belief stays a claim about
  ;; records the KB holds.
  (let [t (terms)
        {:keys [bird feathered flies Tweety ctx]} t]
    (tu/with-cleared-kb [kb memory-kb]
      (v/assert kb (list 'set/forwardRule (vr/rule-sentence [(list bird '?b)]
                                                            (list feathered '?b))) ctx)
      (v/assert kb (list 'set/forwardRule (vr/rule-sentence [(list feathered '?f)]
                                                            (list flies '?f))) ctx)
      (v/assert kb (list bird Tweety) ctx)
      (let [mid  (v/handle-of kb (list feathered Tweety) ctx)
            end  (v/handle-of kb (list flies Tweety) ctx)]
        (is (some? mid) "the chain fired, or there is nothing to delete")
        (is (some? end))
        ;; the record goes, the justification that concluded it stays — exactly what a
        ;; deletion inside a load leaves behind
        (p/delete-sentex! (:records kb) mid)
        (let [kb2 (v/open-kb tu/plain-memory-space)]   ; a restart: the TMS starts empty
          (is (seq (dangling-refs kb2)) "the store dangles, which is the premise here")
          (v/recover kb2)
          (testing "the rebuild finishes rather than throwing on the missing record"
            (is (nil? (v/sentex kb2 mid)) "and the record is still not there"))
          (testing "and does not believe it, since no node was minted for it"
            (is (not (v/in? kb2 mid)))
            (is (not (v/in? kb2 end))
                "nor the conclusion, which had nothing left to rest on"))
          (testing "so belief and the record agree: the handle reads absent either way"
            (is (nil? (:sentence (v/why kb2 mid))))
            (is (false? (:stored? (v/why kb2 mid))))))))))

(deftest the-catalog-offers-a-dump-we-wrote-and-says-whose-it-is
  ;; `classify` keys on `meta.edn`, and ours carries both the keys it looks for — but a
  ;; card that only said "a dump" would leave the operator guessing which dialect (and so
  ;; how much re-canonicalization) a load faces.
  (let [root (temp-dir "catalog")
        dump (io/file root "an-export")]
    (try
      (tu/with-cleared-kb [source memory-kb]
        (build! source (terms))
        (export/export! source dump {:compression :none})
        (is (= :dump (catalog/classify dump)))
        (System/setProperty "vaelii.kb.path" (.getPath root))
        (try
          (let [card (first (filter #(= "an-export" (:name %)) (catalog/sources)))]
            (is (some? card) "discovered on the search path")
            (is (= :dump (:kind card)))
            (is (= :vaelii (:dialect card)) "and named as ours")
            (is (re-find #"our own dialect" (:blurb card)))
            (is (re-find #"justifications" (:blurb card))
                "counted in the units this dialect keeps"))
          (finally (System/clearProperty "vaelii.kb.path"))))
      (finally (rm-rf! root)))))

;;; ── the claims content comparison alone would not make ────────────────

(deftest what-the-round-trip-has-to-keep-working
  (let [store (temp-dir "claims")]
    (try
      (tu/with-cleared-kb [_ memory-kb]
        (round-trip!
         (fn [] (memory-kb))
         (fn [] (disk-kb store))
         (fn [source target _summary t]
           (let [{:keys [bird penguin flies nests grandparentOf
                         Tweety Opus Ann Cid Preferred Deprecated ctx]} t]

             (testing "the exception still blocks — the meta-sentex found its rule again"
               (is (seq   (v/sentexes-matching target (list flies Tweety) ctx)) "the unexcepted bird flies")
               (is (empty? (v/sentexes-matching target (list flies Opus) ctx)) "the penguin does not")
               (is (= :excepted (:reason (v/why-not target (list flies Opus) ctx)))))

             (testing "a rule reads back in the author's variable names, not ?var0"
               (let [rule-of (fn [kb]
                               (->> (p/sentex-ids (:records kb))
                                    (map #(v/sentex kb %))
                                    (filter #(= grandparentOf (some-> (:consequent %) first)))
                                    first))]
                 (is (some? (rule-of target)))
                 (is (= (v/readable-sentence (rule-of source))
                        (v/readable-sentence (rule-of target)))
                     "the varmap survived — losing it is silent and cosmetic")))

             (testing "backward chaining works over the imported rules"
               (is (seq (v/query target (list nests Tweety) ctx {:max-depth 3}))))

             (testing "the taxonomy answers, so the closures were rebuilt from the records"
               (is (v/genl? target penguin bird))
               (is (v/isa? target Opus bird)))

             (testing "the merge is still a merge"
               (is (v/deprecated? target Deprecated))
               (is (= Preferred (v/representative target Deprecated))))

             (testing "and the conjunctive rule's derived fact came across believed"
               (is (seq (v/sentexes-matching source (list grandparentOf Ann Cid) ctx)))
               (is (seq (v/sentexes-matching target (list grandparentOf Ann Cid) ctx))))))))
      (finally (backend/close-dir! (.getPath store)) (rm-rf! store)))))

;;; ── a corpus with spelling conventions of its own ─────────────────────

(defn- lenient-kb
  "A cleared `:memory` KB whose public entry point is open — the KB a corpus in someone else's
  dialect is loaded into."
  []
  (doto (v/open-kb (assoc tu/plain-memory-space :naming :off)) (tu/clear-kb!)))

(def ^:private foreign-dialect
  "Sentences shaped like the real imported corpus: a `Context`-suffixed context rather
  than a `Cx`-prefixed one, namespaced predicates, and argument names carrying a hyphen
  or a trailing apostrophe.  Every one is refused under `:strict` — on its *context* if
  nothing else — and not one is a name this build may quietly repair.

  The two kinds of name are refused for different reasons now, and the split is the
  point.  A hyphenated name is a **sense** (`game-theory`, `testicular_cancer-reproductive`)
  and is legal: a word, a dash, and the disambiguator saying which sense is meant.  A
  trailing apostrophe is the legacy spelling of a **lexeme**, which vaelii marks with the
  `lex` namespace instead, so `mining'` matches no convention and is refused as an
  argument.  Three of these four therefore carry an argument violation, not all four."
  '[(ex/disambiguator mining')
    (genl choriocarcinoma' testicular_cancer-reproductive)
    (sense game_theory' game-theory)
    (summary psychological_profiling-profiling "A technique used by law enforcement.")])

(deftest a-corpus-in-its-own-dialect-round-trips-verbatim
  ;; The property the whole naming policy rests on: a corpus the public entry point disagrees
  ;; with is *storable*, *portable* and *findable by the very names that broke the
  ;; convention* — and comes back spelled the way it went in.  A loader that silently
  ;; repaired `game-theory` to `gameTheory` would round-trip its own invention, and the
  ;; corpus it was given would be gone.
  (let [dump (temp-dir "foreign-dialect")]
    (rm-rf! dump)
    (try
      (tu/with-cleared-kb [source lenient-kb]
        (doseq [s foreign-dialect] (v/assert source s 'WellContext))
        (is (= (count foreign-dialect) (v/sentex-count source)))
        (export/export! source dump {:compression :none})
        (let [store (temp-dir "foreign-dialect-store")]
          (try
            (let [target  (disk-kb store)
                  summary (imp/import-dump target dump {:belief? false})]
              (testing "every sentence comes back spelling-identical"
                (is (= (set foreign-dialect)
                       (set (map #(v/sentence-of (v/sentex target %))
                                 (p/sentex-ids (:records target)))))))
              (testing "and each is findable by the name that broke the convention"
                (doseq [t '[mining' game-theory choriocarcinoma'
                            psychological_profiling-profiling]]
                  (is (seq (v/find-sentexes target t)) (str "not findable by " t))))
              (testing "the load reports the disagreement it did not enforce"
                ;; the whole point of counting rather than checking: the operator who
                ;; chose the bulk path learns the number while the records go past
                (let [{:keys [checked refused by-class] :as tally} (:naming summary)]
                  (is (= (count foreign-dialect) checked refused)
                      "every record — they share a context the public entry point refuses")
                  (is (= (count foreign-dialect) (:context-name by-class)))
                  (is (= 3 (:argument by-class))
                      "the three apostrophed names — a hyphenated one is a sense and legal")
                  (is (re-find #"records .* `assert` would refuse" (nm/tally-line tally)))))
              (testing "and a strict KB over the same store still reads all of it"
                ;; the policy travels with the KB, not with the records
                (let [strict (v/open-kb {:backend :disk-log :dir (.getPath store)
                                         :recover? false :naming :strict})]
                  (is (= :strict (:naming strict)))
                  (is (seq (v/find-sentexes strict 'game-theory))))))
            (finally (backend/close-dir! (.getPath store)) (rm-rf! store)))))
      (finally (rm-rf! dump)))))

;;; ── a reader that refuses the file still gives the descriptor back ─────

(defn- open-fds
  "How many file descriptors this JVM holds, or nil where the platform bean cannot say.
  `com.sun.management.UnixOperatingSystemMXBean` ships in `jdk.management` everywhere;
  only the *implementation* is Unix-only, so the `instance?` is the portable gate."
  []
  (let [b (java.lang.management.ManagementFactory/getOperatingSystemMXBean)]
    (when (instance? com.sun.management.UnixOperatingSystemMXBean b)
      (.getOpenFileDescriptorCount ^com.sun.management.UnixOperatingSystemMXBean b))))

(deftest a-reader-that-refuses-the-compression-closes-the-file-it-opened
  ;; The acquisition chain: the reader opens the file and *then* builds the
  ;; decompressor over it.  Both ways that second step refuses are ordinary — a codec
  ;; this build has no dependency for, and a section whose bytes are not what the
  ;; dump's `meta.edn` says they are — and a stream left holding the descriptor with
  ;; nothing referencing it is one nothing will ever close.  A foreign dump is exactly
  ;; where both arrive, and an importer walking sections pays it once per section.
  (let [dump (temp-dir "codec")]
    (try
      (let [f (io/file dump "plain.bin")]
        (spit f "not compressed, and not nippy either")
        (testing "a compression this build cannot read is refused"
          (let [e (is (thrown? clojure.lang.ExceptionInfo
                               (doall (frames/read-window-seq f :brotli))))]
            (is (= :unsupported-compression (:type (ex-data e))))))
        (testing "and so is a section whose bytes are not the codec the dump names"
          (is (thrown? java.io.IOException (doall (frames/read-window-seq f :gzip)))))
        (testing "and neither refusal keeps the descriptor"
          (let [before (open-fds)]
            (dotimes [_ 300]
              (try (doall (frames/read-window-seq f :gzip)) (catch Throwable _ nil))
              (try (doall (frames/read-window-seq f :brotli)) (catch Throwable _ nil)))
            (let [after (open-fds)]
              (is (or (nil? before) (< (- (long after) (long before)) 50))
                  (str "600 refused opens leaked descriptors: " before " -> " after))))))
      (finally (rm-rf! dump)))))

(deftest a-dump-naming-one-handle-twice-is-refused-on-both-record-passes
  ;; A handle is an identity, and both record passes land a dump of ours at the handles it
  ;; gave — which is what makes an id in a dump mean anything.  So a second frame claiming
  ;; a handle already stored would destroy the first record with nothing to show for it,
  ;; and every justification, index posting and embedded `(sentexHandle H)` citing that
  ;; number would afterwards name the wrong sentence.  Equal content never reaches the
  ;; check: the canonical form has already collapsed onto one handle, counted as
  ;; `:collapsed`.  What is left is a dump that is genuinely broken, on either path.
  (let [dump (temp-dir "dup-handle")]
    (rm-rf! dump)                                   ; export! makes its own directory
    (try
      (tu/with-cleared-kb [source memory-kb]
        (tu/with-terms [dog cat Muffet Tom CxDup]
          (v/assert source (list dog Muffet) CxDup {:strength :monotonic})
          (v/assert source (list cat Tom) CxDup {:strength :monotonic}))
        (export/export! source dump {:compression :none}))
      (let [^File f  (io/file dump "sentexes.nippy.stream")
            fs       (vec (frames/read-chunked-seq f :none))
            clashing (:id (first fs))]
        (is (= 2 (count fs)) "two frames, so the second is the one that clashes")
        (frames/write-frames! f [(first fs) (assoc (second fs) :id clashing)]
                              {:compression :none :chunk-size 10000})
        ;; `:belief? false` is the bulk records-only pass and the other two the belief
        ;; pass; each lands the dump's handles itself, so each owes the refusal
        (doseq [mode [true :stored false]]
          (testing (str ":belief? " (pr-str mode))
            (tu/with-cleared-kb [target memory-kb]
              (let [d (try (imp/import-dump target dump {:belief? mode})
                           nil
                           (catch clojure.lang.ExceptionInfo e (ex-data e)))]
                (is (= :duplicate-handle (:type d)))
                (is (= clashing (:handle d)) "naming the handle the dump claimed twice"))))))
      (finally (rm-rf! dump)))))

(deftest a-dump-this-build-cannot-read-is-refused-before-the-first-write
  ;; Four gates read `meta.edn` and refuse on it, and each lands before a record is
  ;; stored — which is what makes a refused import safe to retry with no `clear!` in
  ;; between.  A version, a variant or a framing this build does not read has to be a
  ;; named refusal rather than a half-filled store: a dump read up to the point of failure
  ;; leaves a fraction of a KB nobody chose, and nothing downstream can tell it from a
  ;; corpus that really is that small.
  (let [dump    (temp-dir "gates")
        kb      (memory-kb)
        meta!   (fn [m] (spit (io/file dump "meta.edn") (pr-str m)))
        refusal (fn [] (try (imp/import-dump kb dump)
                            nil
                            (catch clojure.lang.ExceptionInfo e (ex-data e))))]
    (try
      (testing "a directory with no meta.edn is not a dump"
        (is (= :no-dump (:type (refusal)))))
      (testing "a format version past the ones this build reads"
        (meta! {:format :vaelii/export :format-version 999})
        (let [d (refusal)]
          (is (= :unsupported-version (:type d)))
          (is (= 999 (:found d)) "naming the version the dump declared")
          (is (= imp/supported-export-versions (:supported d))
              "and the ones it could have read instead")))
      (testing "a variant that is not a record dump"
        (meta! {:format :vaelii/export :format-version 1 :variant :pg-memory})
        (is (= :unsupported-variant (:type (refusal)))))
      (testing "a framing neither stream reader knows"
        (meta! {:format :vaelii/export :format-version 1 :framing :interpretive-dance})
        (is (= :unknown-framing (:type (refusal)))))
      (testing "and every one of them left the destination exactly as it found it"
        (is (zero? (v/sentex-count kb)))
        (is (empty? (p/sentex-ids (:records kb)))))
      (finally (rm-rf! dump) (tu/clear-kb! kb)))))

;;; ── the on-disk layout has one home ───────────────────────────────────

(deftest the-dump-layout-is-stated-once-and-these-are-its-names
  ;; The writer (`export`) and the reader (`import`) must agree on which streams a dump
  ;; holds and what each is called — a rename on one side alone produces a dump the
  ;; other reports as *missing* rather than misnamed, and the discovery moment is a
  ;; restore.  So the names live once, in `frames` beside the framing they name, and
  ;; this pins them to the literal on-disk spellings: the layout is a **frozen wire
  ;; contract** (existing dumps must stay readable), so a change here is a format
  ;; version, never a refactor.
  (is (= "meta.edn"                     frames/meta-file))
  (is (= "sentexes.nippy.stream"        frames/sentex-file))
  (is (= "justifications.nippy.stream"  frames/justification-file))
  (is (= "provenance.nippy.stream"      frames/provenance-file))
  (is (= "index"                        frames/index-dir))
  (is (= "entries.nippy.stream"         frames/index-entry-file))
  (is (= "index.edn"                    frames/index-meta-file)))
