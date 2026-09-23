;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.context-nat-sweep-test
  "The orphan sweep over **reified-NAT contexts** — docs/context-nat.md, docs/nat.md.

  An object `nat/` constant is collected when no sentence names it.  A `cx/` context is a
  *place* as well as a name, so it takes one more source of liveness: what is stored in it.
  It is collected at the same gate when all three are empty — nothing in its context slot,
  no stored sentence naming it, no stored `genlCx` edge mentioning it — and the structural
  `genlCx` edges the producer computes off its own `termOfUnit` map are none of those,
  since a pair of ordered contexts would otherwise hold each other up forever.

  What the namespace pins, beyond the gate itself: every arrival order of the three
  sources reaches the same end state; a re-mint after a sweep dedups to one constant and
  is indistinguishable from one never swept; a query context and a koinii agent or channel
  context are `Cx…` names the sweep cannot name at all; a fork sweeps its own view and
  leaves the base standing; and a swept context stays swept across a durable reopen."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.impl.disk.backend :as disk-backend]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat :as nat]
            [vaelii.koinii.channel :as ch]
            [vaelii.koinii.identity :as id]
            [vaelii.koinii.speech-acts :as sa]
            [vaelii.test-util :as tu])
  (:import [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(use-fixtures :once (tu/loaded core-context/load-into))
(use-fixtures :each (tu/neutral))

;; ---- scaffolding ---------------------------------------------------------

(def ^:private ctr (atom 0))

(defn- fresh-cxfn
  "A gensym'd `Cx*Fn` context-function name, unique per call so the net-neutral fixture's
  retraction leaves nothing behind and no two tests share a dimension."
  []
  (symbol (str "CxTmpSweep" (swap! ctr inc) "Fn")))

(defn- declare-dimension!
  "Declare a fresh context function ordered by `subintervalOf` on its datetime argument,
  plus `DatetimeFn` as the structural (unreifiable) constructor.  Returns the function."
  [kb]
  (let [cxfn (fresh-cxfn)]
    (v/assert kb (list 'context_denoting_function cxfn) 'CxUniverse)
    (v/assert kb '(unreifiable_function DatetimeFn) 'CxUniverse)
    (v/assert kb (list 'contextArgSubrelation cxfn 2 'subintervalOf) 'CxUniverse)
    cxfn))

(defn- reified?
  "Does the KB still map `k` to an expression — is it still a context it knows?  The
  `termOfUnit` is a context NAT's whole bookkeeping, so this is exactly \"not swept\"."
  [kb k]
  (boolean (seq (v/sentexes-matching kb (list 'termOfUnit k '?e) 'CxUniverse))))

(defn- context-in
  "Mint the reified context for `expr` by storing `sentence` in it, and answer
  `[handle constant]`."
  [kb sentence expr]
  (let [h (v/assert kb sentence expr)]
    [h (:context (v/sentex kb h))]))

;; ---- the gate ------------------------------------------------------------

(tu/deftest-kb the-last-sentex-out-of-the-slot-collects-the-context
  ;; The source a `nat/` constant does not have: nothing names the context, so the term
  ;; index alone would call it orphaned the moment it was minted.  What holds it up is
  ;; its extent, and what collects it is the last fact leaving.
  (let [cxfn   (declare-dimension! kb)
        expr   (list cxfn 'CxMonad (list 'DatetimeFn "2000"))
        [h k]  (context-in kb '(likes Tom Ann) expr)]
    (is (nat/reified-context-symbol? k) "a cx/ constant")
    (is (= 1 (v/count-in-context kb k)))
    (is (reified? kb k))
    (v/retract! kb h)
    (is (not (reified? kb k)) "emptied, so collected")
    (is (zero? (v/count-in-context kb k)))))

(tu/deftest-kb a-context-still-holding-a-fact-is-not-collected
  (let [cxfn  (declare-dimension! kb)
        expr  (list cxfn 'CxMonad (list 'DatetimeFn "2001"))
        [h k] (context-in kb '(likes Tom Ann) expr)
        h2    (v/assert kb '(knows Tom Bob) expr)]
    (is (= 2 (v/count-in-context kb k)))
    (v/retract! kb h)
    (is (reified? kb k) "one fact left, so the context stands")
    (is (= [{'?x 'Bob}] (v/ask kb '(knows Tom ?x) expr)) "and still answers")
    (v/retract! kb h2)
    (is (not (reified? kb k)))))

(tu/deftest-kb a-stored-genlcx-edge-keeps-an-emptied-context
  ;; An edge somebody asserted is content about the context, so it holds it up on its own
  ;; — the extent going empty is not enough.
  (let [cxfn  (declare-dimension! kb)
        expr  (list cxfn 'CxMonad (list 'DatetimeFn "2002"))
        [h k] (context-in kb '(likes Tom Ann) expr)
        edge  (v/assert kb (list 'genlCx 'CxStory k) 'CxUniverse)]
    (v/retract! kb h)
    (is (zero? (v/count-in-context kb k)))
    (is (reified? kb k) "the edge is a stored reference, so the context stands")
    (v/retract! kb edge)
    (is (not (reified? kb k)) "and the edge going is what collects it")))

(tu/deftest-kb a-sentence-naming-the-context-keeps-it
  ;; The `nat/` liveness source, asked of a `cx/` constant: a term-position mention is a
  ;; claim about the context and keeps it exactly as a use keeps an object constant.
  (let [cxfn  (declare-dimension! kb)
        expr  (list cxfn 'CxMonad (list 'DatetimeFn "2003"))
        [h k] (context-in kb '(likes Tom Ann) expr)
        note  (v/assert kb (list 'recordedIn 'Tom k) 'CxUniverse)]
    (v/retract! kb h)
    (is (reified? kb k) "the mention is a stored reference")
    (v/retract! kb note)
    (is (not (reified? kb k)))))

(tu/deftest-kb a-computed-genlcx-edge-does-not-keep-a-context-alive
  ;; The producer derives `(genlCx month year)` from the two `termOfUnit` maps, so the
  ;; edge is a *reading* of the bookkeeping rather than a reference to it.  Counting it
  ;; would make every ordered pair immortal — each end held up by an edge computed from
  ;; the other end — which is the whole reason authorship decides this and shape does not.
  (let [cxfn      (declare-dimension! kb)
        year      (list cxfn 'CxMonad (list 'DatetimeFn "2004"))
        month     (list cxfn 'CxMonad (list 'DatetimeFn "2004-01"))
        [hy ky]   (context-in kb '(holiday NewYear) year)
        [hm km]   (context-in kb '(likes Bob Cid) month)]
    (is (v/sees? kb km ky) "the computed edge stands")
    (testing "emptying the month collects it, edge and all, and leaves the year"
      (v/retract! kb hm)
      (is (not (reified? kb km)))
      (is (reified? kb ky))
      (is (not (v/sees? kb km ky)) "the derived edge went with its premise"))
    (testing "and emptying the year then collects the year"
      (v/retract! kb hy)
      (is (not (reified? kb ky))))))

(tu/deftest-kb an-empty-context-goes-even-while-a-spec-of-it-is-live
  ;; What the definition yields, said out loud.  A year whose only fact is retracted is
  ;; held up by nothing — its extent is empty, no sentence names it, and the edge down to
  ;; its live January is one the producer computed off the two maps — so it goes, and
  ;; January goes on holding what it holds.  Nothing is lost: an empty context answers no
  ;; reader, and asserting into the year again re-mints it and recomputes the edge.
  (let [cxfn    (declare-dimension! kb)
        year    (list cxfn 'CxMonad (list 'DatetimeFn "2005"))
        month   (list cxfn 'CxMonad (list 'DatetimeFn "2005-01"))
        [hy ky] (context-in kb '(holiday NewYear) year)
        [_ km]  (context-in kb '(likes Bob Cid) month)]
    (is (v/sees? kb km ky))
    (v/retract! kb hy)
    (is (= [false true] [(reified? kb ky) (reified? kb km)]) "the year goes, January stays")
    (is (= [{'?x 'Cid}] (v/ask kb '(likes Bob ?x) month)) "and still answers")
    (testing "and stating a fact for the year again re-mints it under the same reading"
      (let [[_ ky2] (context-in kb '(holiday NewYear) year)]
        (is (v/sees? kb km ky2))
        (is (= [{'?x 'NewYear}] (v/ask kb '(holiday ?x) month)))))))

(tu/deftest-kb collecting-a-context-orphans-the-object-nat-in-its-expression
  ;; The region grows with the fixpoint, across both kinds: the context's `termOfUnit` is
  ;; the last sentence naming the object constant standing inside its expression, so the
  ;; round that collects the context makes that constant the next round's candidate.  One
  ;; rule, one teardown, a `cx/` and a `nat/` collected by it.
  (let [cxfn  (declare-dimension! kb)
        dimfn (symbol (str "TmpDim" (swap! ctr inc) "Fn"))]
    (v/assert kb (list 'reifiable_function dimfn) 'CxUniverse)
    (let [expr  (list cxfn (list dimfn 'CxMonad) (list 'DatetimeFn "2030"))
          [h k] (context-in kb '(likes Tom Ann) expr)
          inner (second (nat/nat-expression kb k))]
      (is (nat/reified-object-symbol? inner) "the dimension argument reified to an object")
      (v/retract! kb h)
      (is (not (reified? kb k)))
      (is (empty? (v/sentexes-matching kb (list 'termOfUnit inner '?e) 'CxUniverse))
          "and the object constant inside the expression went with it"))))

(tu/deftest-kb a-computed-edges-authorship-survives-a-rebuild
  ;; What tells the engine's wiring from somebody's edge is the producer's informant on the
  ;; justification, and `recover` rebuilds the network from the durable justification
  ;; records.  Were the rebuild to hand the edge back as a premise — or under another
  ;; informant — an emptied context would be held up by what the producer computed about
  ;; it, and the sweep would stop collecting on any KB that had restarted.
  (let [cxfn    (declare-dimension! kb)
        year    (list cxfn 'CxMonad (list 'DatetimeFn "2040"))
        month   (list cxfn 'CxMonad (list 'DatetimeFn "2040-01"))
        [hy ky] (context-in kb '(holiday NewYear) year)
        [hm km] (context-in kb '(likes Bob Cid) month)]
    (v/recover kb)
    (is (v/sees? kb km ky) "the rebuild has the computed edge")
    (v/retract! kb hm)
    (is (not (reified? kb km)) "and still reads it as the engine's own wiring")
    (is (reified? kb ky) "while the year, still holding a fact, stands")
    (v/retract! kb hy)
    (is (not (reified? kb ky)))))

;; ---- order independence --------------------------------------------------

(tu/deftest-kb every-order-of-the-three-liveness-sources-ends-the-same
  ;; Extent, mention and stored edge, retracted in each of the six orders.  Whichever goes
  ;; last is the one that collects, and the end state does not depend on which that was.
  (let [cxfn (declare-dimension! kb)]
    (doseq [[i order] (map-indexed vector
                                   [[:extent :mention :edge] [:extent :edge :mention]
                                    [:mention :extent :edge] [:mention :edge :extent]
                                    [:edge :extent :mention] [:edge :mention :extent]])]
      (let [expr   (list cxfn 'CxMonad (list 'DatetimeFn (str (+ 2010 i))))
            [h k]  (context-in kb '(likes Tom Ann) expr)
            hs     {:extent  h
                    :mention (v/assert kb (list 'recordedIn 'Tom k) 'CxUniverse)
                    :edge    (v/assert kb (list 'genlCx 'CxStory k) 'CxUniverse)}
            ;; one `is` per order rather than one per step: the step-by-step reading is a
            ;; vector, so the assertion count is a property of the test and not of the loop
            standing (mapv (fn [src] (v/retract! kb (hs src)) (reified? kb k)) order)]
        (is (= [true true false] standing)
            (str "order " (pr-str order) " — alive until the last source goes"))
        (is (zero? (v/count-in-context kb k)))))))

;; ---- re-minting ----------------------------------------------------------

(tu/deftest-kb a-swept-context-re-mints-to-one-constant
  ;; The claim the sweep owes: a constant collected and re-minted rebuilds the same KB.
  ;; The **handle** is not part of that — it is per-KB and belief may never key on it — but
  ;; the `cx/` **symbol** now is: a reified constant is named by the content of its
  ;; expression (`nat/content-name`), so re-minting the same expression yields the *same*
  ;; constant, in this KB or another.  The re-mint below is therefore not merely
  ;; indistinguishable from the original — it is the original symbol, reasserted.
  (let [cxfn    (declare-dimension! kb)
        year    (list cxfn 'CxMonad (list 'DatetimeFn "2006"))
        month   (list cxfn 'CxMonad (list 'DatetimeFn "2006-01"))
        [hy ky] (context-in kb '(holiday NewYear) year)
        [hm km] (context-in kb '(likes Bob Cid) month)]
    (v/retract! kb hm)
    (v/retract! kb hy)
    (is (= [false false] [(reified? kb km) (reified? kb ky)]))
    (testing "re-minting the same two expressions rebuilds the same KB"
      (let [[_ ky2] (context-in kb '(holiday NewYear) year)
            [_ km2] (context-in kb '(likes Bob Cid) month)]
        (is (= ky ky2) "the same content-named constant, as a deterministic re-mint always is")
        (is (= 1 (count (v/sentexes-matching kb (list 'termOfUnit '?k year) 'CxUniverse)))
            "one constant for the expression — the re-mint dedups, it does not double")
        (is (= km2 (:context (v/sentex kb (v/assert kb '(knows Bob Dee) month))))
            "and the write entry point resolves the compound to that one constant")
        (is (v/sees? kb km2 ky2) "the computed edge is back")
        (is (= [{'?x 'NewYear}] (v/ask kb '(holiday ?x) month))
            "and the month reads the year's fact again, as it did before the sweep")))))

;; ---- what the sweep cannot name ------------------------------------------

(tu/deftest-kb a-query-context-is-never-a-sweep-candidate
  ;; `CxEverything` / `CxInference` / `CxNothing` name a *way of reading*, resolved at the
  ;; read entry point and refused at every write entry point (docs/contexts.md), so nothing is ever
  ;; stored in one and nothing mints one.  They are `Cx…` names, not `cx/` constants, and
  ;; the sweep collects `cx/` constants alone — so a query holding one holds a symbol the
  ;; candidate set cannot contain, and there is no teardown to race.
  (let [cxfn  (declare-dimension! kb)
        expr  (list cxfn 'CxMonad (list 'DatetimeFn "2007"))
        [h k] (context-in kb '(likes Tom Ann) expr)]
    (is (= [false false false] (mapv nat/reified-context-symbol? (sort nm/query-contexts))))
    (is (= [0 0 0] (mapv #(v/count-in-context kb %) (sort nm/query-contexts))))
    (is (empty? (mapcat #(v/sentexes-matching kb (list 'termOfUnit % '?e) 'CxUniverse)
                        nm/query-contexts))
        "no query context is mapped, so none can be orphaned")
    (v/assert kb '(likes Bob Cid) 'CxStory)
    (v/retract! kb h)
    (is (not (reified? kb k)) "the teardown swept the reified context")
    (is (= [{'?x 'Cid}] (v/ask kb '(likes Bob ?x) 'CxEverything))
        "and the reading mode reads on, untouched by it")))

(deftest a-koinii-agent-or-channel-context-is-never-swept
  ;; Through koinii's own API, which reaches nothing under `vaelii.impl`.  An agent context
  ;; and a channel are `Cx…` names computed from an id — never minted, never mapped — so
  ;; they are outside the sweep's namespace whatever their extent.  The registry sentences
  ;; and the placement edges name them besides.  The KB's own space is cleared on open, so
  ;; a second run in one JVM does not open over the first run's records unrecovered.
  (let [kb2 (doto (v/open-kb {:backend :memory :space [::koinii 1] :recover? false})
              (tu/clear-kb!)
              (core-context/load-into)
              (sa/load-speech-acts))]
    (let [atlas (ch/join (ch/local kb2) 'CxDeploy 'AgentAtlas)
          actx  (:context atlas)
          h     (ch/assert atlas '(usesDatabase ProdCluster PostgreSQL14))
          cxfn  (declare-dimension! kb2)
          expr  (list cxfn 'CxMonad (list 'DatetimeFn "2008"))
          [hc k] (context-in kb2 '(likes Tom Ann) expr)]
      (is (= 'CxAtlas actx) "the agent's own context is a name, not a mint")
      (is (= [false false] [(nat/reified-context-symbol? actx)
                            (nat/reified-context-symbol? (:channel atlas))]))
      (testing "retracting the agent's only assertion leaves its context and the channel"
        (v/retract! kb2 h)
        (is (v/sees? kb2 'CxDeploy actx) "still lifted under the channel")
        (is (v/sees? kb2 actx 'CxSpeechActs) "still rooted in the reply vocabulary")
        (is (= 'CxAtlas (id/context-for 'AgentAtlas)) "and still the agent's place")
        (is (seq (v/sentexes-in-context kb2 actx))
            "the placement mark keeps the context non-empty in any case"))
      (testing "while the same teardown path does collect a reified context beside it"
        (v/retract! kb2 hc)
        (is (not (reified? kb2 k)))
        (is (v/sees? kb2 'CxDeploy actx) "the agent context is untouched by that sweep")))))

;; ---- the fork ------------------------------------------------------------

(deftest a-fork-sweeps-its-own-view-and-never-the-base
  ;; Base immutability is the overlay's first invariant (docs/overlay.md): a retraction in
  ;; a fork tombstones the inherited record rather than deleting it, and the sweep runs
  ;; through the ordinary `retract!` that does so.  So a context the fork empties is
  ;; collected in the fork's view and stands in the base, which is how an object NAT's
  ;; sweep already behaves there.  A `:memory` base on its own space, cleared on open so a
  ;; second run in one JVM starts empty, so the fork is admissible on every run (a
  ;; `:columnar` index has no `KvBackend` to decorate); the fork takes the default, an
  ;; ephemeral space nothing else uses.
  (let [base (doto (v/open-kb {:backend :memory :space [::sweep-base 1] :recover? false})
               (tu/clear-kb!))]
    (core-context/load-into base)
    (let [cxfn  (declare-dimension! base)
          expr  (list cxfn 'CxMonad (list 'DatetimeFn "2009"))
          [h k] (context-in base '(likes Tom Ann) expr)
          f     (v/fork base)]
      (is (reified? f k) "the fork inherits the mapping")
      (v/retract! f h)
      (is (not (reified? f k)) "and sweeps the context it emptied")
      (is (zero? (v/count-in-context f k)))
      (is (reified? base k) "the base still maps it")
      (is (= 1 (v/count-in-context base k)) "and still holds the fact")
      (is (= [{'?x 'Ann}] (v/ask base '(likes Tom ?x) expr))))))

;; ---- durability ----------------------------------------------------------

(defn- with-tmp-dir
  "Run `(f dir)` in a fresh temp directory, closing the disk stores opened on it and
  deleting it afterwards."
  [f]
  (let [dir (str (Files/createTempDirectory "vaelii-cxsweep-" (into-array FileAttribute [])))]
    (try (f dir)
         (finally (disk-backend/close-dir! dir)
                  (doseq [x (reverse (file-seq (java.io.File. dir)))] (.delete ^java.io.File x))))))

(deftest a-swept-context-stays-swept-across-a-reopen
  ;; The sweep deletes durable records, so a restart has nothing to replay: `recover`
  ;; rebuilds belief and the taxonomy from what the store holds, and the collected
  ;; context is not in it.  Run on `:disk-log` outright rather than on whatever storage
  ;; the run selected, so the claim is made against a durable store on every backend.
  (with-tmp-dir
    (fn [dir]
      (let [k (let [kb1 (v/open-kb {:backend :disk-log :dir dir :recover? false})]
                (v/assert kb1 '(context_denoting_function CxTmpDurableFn) 'CxUniverse)
                (v/assert kb1 '(unreifiable_function DatetimeFn) 'CxUniverse)
                (let [expr  '(CxTmpDurableFn CxMonad (DatetimeFn "2020"))
                      [h k] (context-in kb1 '(likes Tom Ann) expr)]
                  (v/retract! kb1 h)
                  (is (not (reified? kb1 k)) "collected before the close")
                  k))]
        (disk-backend/close-dir! dir)
        (let [kb2 (v/open-kb {:backend :disk-log :dir dir :recover? false})]
          (is (nil? (v/handle-of kb2 (list 'termOfUnit k '(CxTmpDurableFn CxMonad (DatetimeFn "2020")))
                                 'CxUniverse))
              "the durable record is gone, not merely disbelieved")
          (v/recover kb2)
          (is (not (reified? kb2 k)) "and the rebuild has nothing to bring back")
          (is (not (contains? (set (v/contexts kb2)) k))))))))
