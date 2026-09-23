;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.exposure-test
  "Two memberships each admissible where stated, whose types some context can jointly
  see as disjoint, are a real contradiction.  A **vantage** — the maximal common
  descendant of the two memberships' contexts — decides the pair under either constraint
  policy, and the exposure pass reports what no vantage convicted, as a `:disjoint` entry
  in the violations ledger.  Neither route refuses a writer on grounds it cannot see.

  Three routes bring one clash into joint sight — the membership arriving last, the
  separating declaration arriving last, the `genlCx` edge arriving last — and the passes
  run at settle exactly so the answer is route-agnostic.  Each route gets a test; the
  shared lattice is two siblings under CxUniverse, with the joint viewer (when one
  exists) below both.  The membership-last route's acceptance test is
  `disjoint_test/a-general-context-may-be-given-what-a-specific-one-forbids`.

  **What the exposure pass is left to report** is the pair the vantage could not convict:
  the separation is derivable only *below* the maximal common descendant, so the vantage
  reads no separation and a context under it reads the whole clash (`deep-separation!`).
  The budgeted sweeps' own tests use that lattice for the same reason."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]
            [vaelii.violation-roster-test :as roster]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- siblings!
  "Two sibling contexts under CxUniverse, two root types, one term holding one
  type in each sibling — admissible everywhere, since neither sibling sees the
  other."
  [kb {:keys [a b t1 t2 x]}]
  (v/assert kb (list 'genl t1 'thing) 'CxUniverse)
  (v/assert kb (list 'genl t2 'thing) 'CxUniverse)
  (v/assert kb (list 'genlCx a 'CxUniverse) 'CxUniverse)
  (v/assert kb (list 'genlCx b 'CxUniverse) 'CxUniverse)
  (v/assert kb (list t1 x) a)
  (v/assert kb (list t2 x) b))

(defn- deep-separation!
  "`siblings!`'s two memberships, a joint viewer `w` below both, and the separation
  written in `decl` — a context `w` cannot see.

  `w` is the maximal common descendant of the two memberships' contexts, so it is the
  vantage `settle/clash-askers` asks the pair's question from; `w` derives no separation,
  so the settle decides nothing.  A context below both `w` and `decl` sees the whole
  clash, and that is what the exposure pass names."
  [kb {:keys [a b w decl t1 t2] :as spec}]
  (v/assert kb (list 'genlCx decl 'CxUniverse) 'CxUniverse)
  (v/assert kb (list 'disjoint t1 t2) decl)
  (siblings! kb spec)
  (v/assert kb (list 'genlCx w a) 'CxUniverse)
  (v/assert kb (list 'genlCx w b) 'CxUniverse))

(defn- deep-viewer!
  "A context below `w` and `decl`: the one that reads the separation and both
  memberships, and so the one an exposure entry names.  The `decl` edge arrives last, so
  the settle that files the entry is that edge's."
  [kb v w decl]
  (v/assert kb (list 'genlCx v w) 'CxUniverse)
  (v/assert kb (list 'genlCx v decl) 'CxUniverse))

(tu/deftest-kb siblings-with-no-joint-viewer-expose-nothing
  ;; the pin for the ∃-descendant reading: the memberships coexist, the declaration
  ;; is visible to both writers, and still no single context sees the whole clash —
  ;; so there is nothing to report and nobody to report it to.
  (tu/with-terms [CxA CxB left_t right_t Pip]
    (v/assert kb (list 'disjoint left_t right_t) 'CxUniverse)
    (siblings! kb {:a CxA :b CxB :t1 left_t :t2 right_t :x Pip})
    (is (empty? (v/violations kb)))
    (is (seq (v/sentexes-matching kb (list left_t Pip) CxA)))
    (is (seq (v/sentexes-matching kb (list right_t Pip) CxB)))))

(tu/deftest-kb a-genlCx-edge-arriving-last-decides-the-clash
  ;; the visibility route: everything else stands, and wiring a joint viewer below
  ;; both siblings is what makes the clash visible — the edge's own settle weighs it.
  ;; CxW is the vantage, and it sees the separation in CxUniverse, so the pair is
  ;; decided rather than reported.  Both memberships are `:default`, so CxW cannot rank
  ;; them and the answer is a dilemma.
  (tu/with-terms [CxA CxB CxW left_t right_t Pip]
    (v/assert kb (list 'disjoint left_t right_t) 'CxUniverse)
    (siblings! kb {:a CxA :b CxB :t1 left_t :t2 right_t :x Pip})
    (v/assert kb (list 'genlCx CxW CxA) 'CxUniverse)
    (is (empty? (v/contradictions kb)) "seeing one side is not seeing the clash")
    (v/assert kb (list 'genlCx CxW CxB) 'CxUniverse)
    (let [cs (v/contradictions kb)]
      (is (= [:disjoint] (mapv :kind cs)))
      (is (= #{(list left_t Pip) (list right_t Pip)}
             (into #{} (map :sentence) (:sides (first cs))))))
    (is (empty? (v/violations kb))
        "decided is not exposed: the ledger does not also claim the pair")))

(tu/deftest-kb a-rebuild-exposes-nothing-because-nothing-newly-moved
  ;; The pass reports what a *change* newly made jointly visible.  A `recover` changes
  ;; nothing — it restores — and its region is every stored sentex, so leaving the pass
  ;; on turns a bounded incremental check into a full-KB audit nobody asked for: 27% of
  ;; an OpenCyc import.  The clash is still there and still findable; what the skip
  ;; costs nobody is re-filing it on every restart.
  ;;
  ;;   CxUniverse
  ;;     ├─ CxA CxB          one membership each
  ;;     └─ CxDecl           (disjoint left_t right_t)
  ;;   CxW sees CxA and CxB  — the vantage, which reads no separation
  ;;     └─ CxV sees CxW and CxDecl   — where the clash is visible whole
  (tu/with-terms [CxA CxB CxW CxDecl CxV left_t right_t Pip]
    (deep-separation! kb {:a CxA :b CxB :w CxW :decl CxDecl
                          :t1 left_t :t2 right_t :x Pip})
    (deep-viewer! kb CxV CxW CxDecl)
    (is (= [:disjoint] (mapv :violation (v/violations kb)))
        "the change that exposed it reported it")
    (is (empty? (v/contradictions kb)) "and no vantage convicted it")
    (v/clear-violations! kb)
    (v/recover kb)
    (is (empty? (v/violations kb)) "and the rebuild does not report it again")
    (testing "while the KB still holds both sides, and an ordinary settle still reports"
      (is (seq (v/sentexes-matching kb (list left_t Pip) CxA)))
      (is (seq (v/sentexes-matching kb (list right_t Pip) CxB)))
      ;; a real change to the same lattice exposes again, so the gate is about
      ;; rebuilding and not about the clash having been seen once
      (tu/with-terms [CxV2]
        (deep-viewer! kb CxV2 CxW CxDecl)
        (let [vs (v/violations kb)]
          (is (every? #(= :disjoint (:violation %)) vs))
          ;; the new viewer is named among those the clash is visible from — the pass
          ;; is off for a rebuild, not off.  (V's sighting is re-filed alongside it:
          ;; an exposure is an event, and the ancestor set moved again.)
          (is (some #(contains? (get-in % [:detail :visible-from]) CxV2) vs)))))))

(tu/deftest-kb the-standing-question-is-answerable-on-demand
  ;; `settle` reports what a change newly exposed; this reports what the KB holds now.
  ;; It is the same clash and the same entry shape, asked of the whole KB by a caller
  ;; who chose to — and it is what an imported KB has instead of a settle that ran
  ;; while the content was arriving.
  (tu/with-terms [CxA CxB CxW CxDecl CxV left_t right_t Pip]
    (v/assert kb (list 'genlCx CxDecl 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'disjoint left_t right_t) CxDecl)
    (siblings! kb {:a CxA :b CxB :t1 left_t :t2 right_t :x Pip})
    (v/assert kb (list 'genlCx CxW CxA) 'CxUniverse)
    (v/assert kb (list 'genlCx CxW CxB) 'CxUniverse)
    (testing "before a joint viewer of the separation exists there is nothing to see"
      (is (empty? (v/violations kb)))
      (is (empty? (v/exposed-clashes kb))))
    (deep-viewer! kb CxV CxW CxDecl)
    (let [filed (v/violations kb)
          asked (v/exposed-clashes kb)]
      (is (= [:disjoint] (mapv :violation asked)))
      (is (= (map :detail filed) (map :detail asked))
          "the same clash, the same entry — one filed as it arose, one asked for")
      (testing "and asking does not file, store, or move belief"
        (v/clear-violations! kb)
        (let [before (tu/content-count kb)]
          (is (seq (v/exposed-clashes kb)))
          (is (empty? (v/violations kb)))
          (is (= before (tu/content-count kb))))))
    (testing "it survives the rebuild that the settle pass deliberately sits out"
      (v/recover kb)
      (is (empty? (v/violations kb)) "the rebuild filed nothing")
      (is (= [:disjoint] (mapv :violation (v/exposed-clashes kb)))
          "and the clash is still there to be asked about"))
    (testing "and it goes when the clash does"
      (v/retract! kb (v/handle-of kb (list 'disjoint left_t right_t) CxDecl))
      (is (empty? (v/exposed-clashes kb))))))

(tu/deftest-kb a-declaration-arriving-last-decides-a-clash-only-a-descendant-sees
  ;; the separation route: two memberships in sibling contexts, jointly visible only from
  ;; a context below both, and the disjointness arriving is what makes them a clash.
  ;; Neither member's own context sees the pair; CxD does, so CxD is the vantage and
  ;; weighs it, under `:refuse` as under `:arbitrate`.  Two defaults are a dilemma.
  (tu/with-terms [CxA CxB CxD t1 t2 Pip]
    (v/assert kb (list 'genl t1 'thing) 'CxUniverse)
    (v/assert kb (list 'genl t2 'thing) 'CxUniverse)
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
    (v/assert kb (list 'genlCx CxD CxB) 'CxUniverse)
    (v/assert kb (list t1 Pip) CxA)
    (v/assert kb (list t2 Pip) CxB)
    (is (empty? (v/contradictions kb)) "compatible until somebody separates them")
    (v/assert kb (list 'disjoint t1 t2) 'CxUniverse)
    (let [cs (v/contradictions kb)]
      (is (= [:disjoint] (mapv :kind cs)))
      (is (= #{(list t1 Pip) (list t2 Pip)}
             (into #{} (map :sentence) (:sides (first cs))))))
    (is (empty? (v/violations kb)) "decided at CxD, not reported")))

(tu/deftest-kb a-genl-edge-arriving-last-decides-a-clash-only-a-descendant-sees
  ;; the closure route: the held types are not themselves separated — a subtype edge
  ;; arriving puts one of them under a separated type, and the instances below its sub
  ;; side are re-examined.  The two memberships sit in sibling contexts, so CxD is the
  ;; only context that sees the pair and the only one that weighs it.
  (tu/with-terms [CxA CxB CxD dog_t canine_t cat_t Rex]
    (v/assert kb (list 'genl canine_t 'thing) 'CxUniverse)
    (v/assert kb (list 'genl cat_t 'thing) 'CxUniverse)
    (v/assert kb (list 'genl dog_t 'thing) 'CxUniverse)
    (v/assert kb (list 'disjoint canine_t cat_t) 'CxUniverse)
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
    (v/assert kb (list 'genlCx CxD CxB) 'CxUniverse)
    (v/assert kb (list dog_t Rex) CxA)
    (v/assert kb (list cat_t Rex) CxB)
    (is (empty? (v/contradictions kb)) "a dog-cat is odd but nothing separates them yet")
    (v/assert kb (list 'genl dog_t canine_t) 'CxUniverse)
    (let [cs (v/contradictions kb)]
      (is (= [:disjoint] (mapv :kind cs)))
      (is (= #{(list dog_t Rex) (list cat_t Rex)}
             (into #{} (map :sentence) (:sides (first cs))))))
    (is (empty? (v/violations kb)) "decided at CxD, not reported")))

(tu/deftest-kb exposure-is-an-event-append-only-and-refiled-on-revival
  ;; the ledger contract: retracting the ingredient that exposed a clash does not
  ;; withdraw the entry, and the ingredient returning files a new one.  The separation
  ;; sits below the vantage (`deep-separation!`), so the pair is the exposure pass's to
  ;; report rather than a vantage's to decide.
  (tu/with-terms [CxA CxB CxW CxDecl CxV t1 t2 Pip]
    (v/assert kb (list 'genlCx CxDecl 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'disjoint t1 t2) CxDecl)
    (v/assert kb (list 'genl t1 'thing) 'CxUniverse)
    (v/assert kb (list 'genl t2 'thing) 'CxUniverse)
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxW CxA) 'CxUniverse)
    (v/assert kb (list 'genlCx CxW CxB) 'CxUniverse)
    (deep-viewer! kb CxV CxW CxDecl)
    (v/assert kb (list t1 Pip) CxA)
    (let [h (v/assert kb (list t2 Pip) CxB)]
      (is (= 1 (count (v/violations kb))))
      (v/retract! kb h)
      (is (= 1 (count (v/violations kb))) "the entry outlives its ingredient")
      (v/assert kb (list t2 Pip) CxB)
      (is (= 2 (count (v/violations kb))) "each exposure is its own event")
      (testing "and the runs differ, so \"current\" stays decidable"
        (is (apply distinct? (map :run (v/violations kb))))))))

(tu/deftest-kb an-unrelated-settle-does-not-refile-a-standing-clash
  ;; locality: the pass reads the settle's moved region, so a clash whose
  ;; ingredients did not move is not re-examined, let alone re-filed.
  (tu/with-terms [CxA CxB CxW CxDecl CxV t1 t2 other Pip Quo]
    (deep-separation! kb {:a CxA :b CxB :w CxW :decl CxDecl :t1 t1 :t2 t2 :x Pip})
    (deep-viewer! kb CxV CxW CxDecl)
    (is (= 1 (count (v/violations kb))))
    (v/assert kb (list other Quo) CxB)
    (v/assert kb (list other Pip) CxB)
    (is (= 1 (count (v/violations kb)))
        "an unrelated membership — even of the clash's own term — files nothing new:
         the pair it forms with the standing types is not disjoint")))

(tu/deftest-kb a-budgeted-sweep-truncates-out-loud
  ;; the extent-sweeping routes (declaration / metatype / edge arriving last) are
  ;; bounded per settle by *exposure-instance-budget*; a sweep cut short files
  ;; :exposure-truncated naming its trigger rather than silently reading as full
  ;; coverage.  The membership route is exact and unbudgeted.
  (binding [tax/*exposure-instance-budget* 1]
    (tu/with-terms [CxA CxC t1 t2 Pip Quo Rex]
      (v/assert kb (list 'genl t1 'thing) 'CxUniverse)
      (v/assert kb (list 'genl t2 'thing) 'CxUniverse)
      (v/assert kb (list 'genlCx CxC 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxA CxC) 'CxUniverse)
      (v/assert kb (list t1 Pip) CxC)
      (v/assert kb (list t2 Pip) CxA)
      (v/assert kb (list t1 Quo) CxC)
      (v/assert kb (list t2 Quo) CxA)
      (v/assert kb (list t1 Rex) CxC)
      ;; the declaration arrives last: five memberships below its types, budget one
      (v/assert kb (list 'disjoint t1 t2) CxC)
      (let [vs (v/violations kb)
            cut (filter #(= :exposure-truncated (:violation %)) vs)]
        (is (seq cut) "the cut is reported, not silent")
        (is (= 1 (count cut))
            "one entry for the pass — the budget is the pass's, so a per-trigger entry
             would say the same thing once per trigger that arithmetic ran out on")
        (is (= [(list 'disjoint t1 t2)] (get-in (first cut) [:detail :sample]))
            "and names what it did not sweep")
        (is (= 1 (get-in (first cut) [:detail :triggers]))
            "and how many went unswept")
        (is (<= (count (filter #(= :disjoint (:violation %)) vs)) 1)
            "at most the budgeted share of instances was examined")))))

(tu/deftest-kb many-cut-sweeps-file-one-entry-between-them
  ;; The corpus-load shape: a settle whose region holds many extent-sweeping triggers.
  ;; The first spends the budget and every one after it is cut short by arithmetic —
  ;; so the ledger gets one entry with a count, not one per trigger.  Left unfixed this
  ;; was 41,500 entries on an OpenCyc load, against a ledger that keeps 1,000.
  (binding [tax/*exposure-instance-budget* 1]
    (tu/with-terms [CxC t1 t2 Pip Quo]
      (v/assert kb (list 'genl t1 'thing) 'CxUniverse)
      (v/assert kb (list 'genl t2 'thing) 'CxUniverse)
      (v/assert kb (list 'genlCx CxC 'CxUniverse) 'CxUniverse)
      (v/assert kb (list t1 Pip) CxC)
      (v/assert kb (list t2 Quo) CxC)
      (v/assert kb (list 'disjoint t1 t2) CxC)
      (v/clear-violations! kb)
      ;; one settle, several sweeping triggers: two genl edges and a metatype
      (tu/with-terms [t3 t4]
        (v/with-deferred-settle kb
          (v/assert kb (list 'genl t3 t1) 'CxUniverse)
          (v/assert kb (list 'genl t4 t2) 'CxUniverse)
          (v/assert kb (list t3 Pip) CxC)
          (v/assert kb (list t4 Quo) CxC)))
      (let [cut (filter #(= :exposure-truncated (:violation %)) (v/violations kb))]
        (is (>= (count cut) 1) "the bound is still reported")
        (is (= 1 (count cut)) "once per settle, however many triggers it cut short")
        (is (<= (count (get-in (first cut) [:detail :sample])) 3)
            "with a sample rather than the whole list")))))

;;; ── what a declaration implicates ─────────────────────────────────────
;;
;; The budget above bounds the sweep; what the sweep spends it *on* is the candidate
;; rule, and the two together decide whether a bounded pass buys real coverage or
;; merely a bounded quantity of terms that were never going to convict.

(tu/deftest-kb a-separation-implicates-the-terms-below-both-sides-not-below-either
  ;; The extent below one side is not the candidate set: a clash needs a membership
  ;; from *each*, so `(disjoint t1 t2)` implicates the terms below t1 **and** t2.
  ;; Forty terms sit below t1 alone and one below both, against a budget of four —
  ;; so a sweep of everything below either side spends the budget ten times over on
  ;; the fillers and never reaches the clash, while the cheaper side is one term.  The two
  ;; memberships sit in sibling contexts, so only the context below both sees the pair and
  ;; the exposure sweep is the path that finds it.
  (binding [tax/*exposure-instance-budget* 4]
    (tu/with-terms [CxA CxB CxD t1 t2 Pip]
      (v/assert kb (list 'genl t1 'thing) 'CxUniverse)
      (v/assert kb (list 'genl t2 'thing) 'CxUniverse)
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
      (v/assert kb (list 'genlCx CxD CxB) 'CxUniverse)
      (dotimes [_ 40]
        (v/assert kb (list t1 (tu/tmp-ind "Filler")) CxA))
      (v/assert kb (list t1 Pip) CxA)
      (v/assert kb (list t2 Pip) CxB)
      (v/clear-violations! kb)
      (v/assert kb (list 'disjoint t1 t2) 'CxUniverse)
      (let [vs (v/violations kb)]
        (is (= #{(list t1 Pip) (list t2 Pip)}
               (into #{} (mapcat #(map :sentence (:sides %))) (v/contradictions kb)))
            "the one term holding both is found, though t1's extent is ten times the budget")
        (is (empty? (filter #{:exposure-truncated :arbitration-truncated}
                            (map :violation vs)))
            "and nothing was cut short — the cheaper side is one term, not forty")))))

(tu/deftest-kb a-sweep-that-convicts-nobody-still-stops-at-the-bound
  ;; The budget bounds the **enumeration**, never the survivors.  Nothing here holds
  ;; both types, so the candidate rule rejects every term it is shown; budgeting what
  ;; survives instead would walk both extents to the end looking for a keeper and then
  ;; report full coverage, which is the one thing a bounded pass may not do.
  ;;
  ;; **The zero-findings cut**, which is this sweep's entry in `truncation-kind-tests`:
  ;; the pass files nothing else, so an entry hung on a finding would have nowhere to
  ;; ride and the eighteen instances past the bound would read as eighteen that were
  ;; cleared.
  (binding [tax/*exposure-instance-budget* 2]
    (tu/with-terms [CxA CxC t1 t2]
      (v/assert kb (list 'genl t1 'thing) 'CxUniverse)
      (v/assert kb (list 'genl t2 'thing) 'CxUniverse)
      (v/assert kb (list 'genlCx CxC 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxA CxC) 'CxUniverse)
      (dotimes [_ 20] (v/assert kb (list t1 (tu/tmp-ind "Left")) CxC))
      (dotimes [_ 20] (v/assert kb (list t2 (tu/tmp-ind "Right")) CxA))
      (v/clear-violations! kb)
      (v/assert kb (list 'disjoint t1 t2) CxC)
      (let [vs  (v/violations kb)
            cut (filter #(= :exposure-truncated (:violation %)) vs)]
        (is (empty? (filter #(= :disjoint (:violation %)) vs))
            "nobody holds both, so there is no clash to expose")
        (is (= 1 (count cut))
            "and the pass says it stopped early rather than claiming it looked at all 20")
        (is (= 1 (get-in (first cut) [:detail :triggers]))
            "counting triggers, which is what a trigger-bounded sweep leaves unswept")
        (is (= [(list 'disjoint t1 t2)] (get-in (first cut) [:detail :sample]))
            "and naming the one it did not finish")
        (is (= 2 (get-in (first cut) [:detail :budget])))
        (is (re-find #"unreported" (get-in (first cut) [:detail :message]))
            "the reader is told what it costs: clashes nobody will hear about")))))

(tu/deftest-kb a-metatype-declaration-arriving-last-decides-the-clash
  ;; `(disjoint_metatype M)` is a *unary* sentence whose argument is a symbol — the
  ;; same shape as a type membership — so the membership arm claims it unless the
  ;; declarations are matched first, and the metatype gets swept as a term holding a
  ;; type while the clash its arrival creates goes unreached.  The memberships sit in
  ;; sibling contexts, so CxD is the only context that sees the pair and the vantage
  ;; that weighs it.
  (tu/with-terms [CxA CxB CxD animal_species dog_t cat_t Rex]
    (v/assert kb (list 'genl dog_t 'thing) 'CxUniverse)
    (v/assert kb (list 'genl cat_t 'thing) 'CxUniverse)
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
    (v/assert kb (list 'genlCx CxD CxB) 'CxUniverse)
    (v/assert kb (list animal_species dog_t) 'CxUniverse)
    (v/assert kb (list animal_species cat_t) 'CxUniverse)
    (v/assert kb (list dog_t Rex) CxA)
    (v/assert kb (list cat_t Rex) CxB)
    (is (empty? (v/contradictions kb)) "the metatype separates nothing yet")
    (v/assert kb (list 'disjoint_metatype animal_species) 'CxUniverse)
    (let [cs (v/contradictions kb)]
      (is (= [:disjoint] (mapv :kind cs))
          "the members become pairwise disjoint, and the term holding two of them clashes")
      (is (= #{(list dog_t Rex) (list cat_t Rex)}
             (into #{} (map :sentence) (:sides (first cs))))))
    (is (empty? (v/violations kb)) "decided at CxD, not reported")))

(tu/deftest-kb the-narrowed-sweep-finds-what-the-complete-question-finds
  ;; The candidate rule is a *narrowing*, so the claim that matters is that it narrows
  ;; to nothing real.  `exposed-clashes` uses no candidate rule and no budget — a term
  ;; is a candidate iff it holds two believed memberships — so it is the independent
  ;; oracle, and the two must agree clash for clash.
  ;;
  ;; The shape is the one that separates the rules: three separated pairs over terms
  ;; that mostly hold one side only, so a sweep below either side collects fillers while
  ;; the intersection collects the two that convict.  On OpenCyc the same comparison
  ;; over every declaration is 638 against 638, with both differences empty.
  ;; The memberships sit in sibling contexts, so only the context below both sees a pair
  ;; and the settle's exposure sweep, not its deciding sweep, is the path under test.
  (tu/with-terms [CxA CxB CxD a1_t a2_t b1_t b2_t Pip Quo]
    (doseq [t [a1_t a2_t b1_t b2_t]]
      (v/assert kb (list 'genl t 'thing) 'CxUniverse))
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
    (v/assert kb (list 'genlCx CxD CxB) 'CxUniverse)
    (dotimes [_ 12] (v/assert kb (list a1_t (tu/tmp-ind "Filler")) CxA))
    (dotimes [_ 12] (v/assert kb (list b2_t (tu/tmp-ind "Filler")) CxA))
    (v/assert kb (list a1_t Pip) CxA)
    (v/assert kb (list b1_t Pip) CxB)
    (v/assert kb (list a2_t Quo) CxA)
    (v/assert kb (list b2_t Quo) CxB)
    (v/clear-violations! kb)
    (v/assert kb (list 'disjoint a1_t b1_t) 'CxUniverse)
    (v/assert kb (list 'disjoint a2_t b2_t) 'CxUniverse)
    (v/assert kb (list 'disjoint a1_t b2_t) 'CxUniverse)
    (let [decided (into #{} (map (fn [c] (into #{} (map (juxt :sentence :context))
                                               (:sides c))))
                        (v/contradictions kb))
          truth   (into #{} (map (fn [d] (into #{} (map (fn [[ty cx]] [(list ty (:term d)) cx]))
                                               (:held d))))
                        (map :detail (v/exposed-clashes kb)))]
      (is (= #{Pip Quo} (into #{} (map (comp :term :detail)) (v/exposed-clashes kb)))
          "two terms hold a separated pair; the 24 fillers hold one side only")
      (is (= truth decided)
          "and the sweep that narrowed to them decides exactly what the complete question finds")
      (is (empty? (v/violations kb))
          "every pair the oracle names has a vantage, so none is left to report"))))

(tu/deftest-kb a-separation-naming-a-non-symbol-implicates-nobody
  ;; A reified NAT argument — OpenCyc declares thousands of separations against terms like
  ;; `(AbnormalFn chromosome)` — has an empty spec closure, so no membership sits below
  ;; it and no clash sits above it.  The reach is empty outright rather than falling out
  ;; of the sizing arithmetic, and in particular the *symbol* side's extent is not swept
  ;; on the strength of a side that can convict nobody.
  (binding [tax/*exposure-instance-budget* 3]
    (tu/with-terms [CxC real_t Pip]
      (v/assert kb (list 'genl real_t 'thing) 'CxUniverse)
      (v/assert kb (list 'genlCx CxC 'CxUniverse) 'CxUniverse)
      (dotimes [_ 20] (v/assert kb (list real_t (tu/tmp-ind "Filler")) CxC))
      (v/assert kb (list real_t Pip) CxC)
      (v/clear-violations! kb)
      (v/assert kb (list 'disjoint (list 'SomeFn real_t) real_t) 'CxUniverse)
      (let [vs (v/violations kb)]
        (is (empty? (filter #(= :disjoint (:violation %)) vs))
            "a compound can head no stored membership, so it is nobody's clash")
        (is (empty? (filter #(= :exposure-truncated (:violation %)) vs))
            "and the 20 instances below the symbol side are not swept for its sake")))))

(tu/deftest-kb the-nogood-path-narrows-the-same-way-the-exposure-pass-does
  ;; `declaration-implicates` and `declaration-reach` answer one question about one KB.
  ;; If they disagreed, a pair one reached and the other did not would be reported as
  ;; merely *visible* by the ledger or as *decided* by `contradictions` depending on
  ;; which route ran — so the arbitrating path gets the same narrowing, and the same
  ;; budget spent on enumeration rather than on terms that convict nobody.
  (binding [checks/*arbitrate-constraints?* true
            tax/*exposure-instance-budget* 4]
    (tu/with-kb [kb]
      (tu/with-terms [dog_t cat_t Rex]
        (v/assert kb (list 'genl dog_t 'thing) 'CxUniverse)
        (v/assert kb (list 'genl cat_t 'thing) 'CxUniverse)
        (dotimes [_ 40] (v/assert kb (list dog_t (tu/tmp-ind "Pup")) 'CxUniverse))
        (v/assert kb (list dog_t Rex) 'CxUniverse)
        (v/assert kb (list cat_t Rex) 'CxUniverse)
        (is (empty? (v/contradictions kb)) "nothing separates them yet")
        (v/assert kb (list 'disjoint dog_t cat_t) 'CxUniverse)
        (is (= [:disjoint] (mapv :kind (v/contradictions kb)))
            "the one term holding both is arbitrated, though dog_t's extent is ten times
             the budget — the cheaper side is cat_t's single instance")))))

(tu/deftest-kb a-metatype-member-implicates-only-the-holders-of-another-member
  ;; The member route, `(M T)` arriving: T's instances can now clash with instances of
  ;; M's *other* members, so a term below T holding nothing else of M is not a
  ;; candidate.  Twenty such terms sit below dog_t against a budget of three.
  (binding [tax/*exposure-instance-budget* 3]
    (tu/with-terms [CxA CxB CxD animal_species dog_t cat_t Rex]
      (v/assert kb (list 'genl dog_t 'thing) 'CxUniverse)
      (v/assert kb (list 'genl cat_t 'thing) 'CxUniverse)
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
      (v/assert kb (list 'genlCx CxD CxB) 'CxUniverse)
      (v/assert kb (list 'disjoint_metatype animal_species) 'CxUniverse)
      (v/assert kb (list animal_species cat_t) 'CxUniverse)
      (dotimes [_ 20] (v/assert kb (list dog_t (tu/tmp-ind "Pup")) CxA))
      (v/assert kb (list dog_t Rex) CxA)
      (v/assert kb (list cat_t Rex) CxB)
      (v/clear-violations! kb)
      (v/assert kb (list animal_species dog_t) 'CxUniverse)
      (let [vs (v/violations kb)]
        (is (= #{(list dog_t Rex) (list cat_t Rex)}
               (into #{} (mapcat #(map :sentence (:sides %))) (v/contradictions kb)))
            "only the term that also holds a second member is a candidate")
        (is (empty? (filter #{:exposure-truncated :arbitration-truncated}
                            (map :violation vs)))
            "and the cheaper side is walked — cat_t's one instance, not dog_t's 21")))))

(tu/deftest-kb a-budgeted-sweep-decides-the-same-pair-in-either-arrival-order
  ;; **Two** separations in one moved region, because one cannot show this: each `v/assert`
  ;; settles, so a single declaration makes the region one element and `content-order` over
  ;; it is a no-op.  Deferred into one settle with a budget covering one reach and not the
  ;; other, the trigger order decides which pair is arbitrated at all — and reversing the
  ;; write order must not move it.
  ;;
  ;; The budget is exactly one reach, so the second trigger arrives with nothing left: this
  ;; is also what covers the spent-budget branch, which files on the probe rather than on
  ;; the arithmetic.  Asserted on *which* separation was decided rather than on the `:kind`,
  ;; since every disjointness clash has the same kind and a different pair would read
  ;; identically.
  ;;
  ;; **Each arm invents its own terms**, and that is what makes the two comparable.  The
  ;; arms share one KB — `with-kb` binds the fixture's, and a `fresh` mid-test would clear
  ;; the store the net-neutrality check recorded its baseline against — so an arm reusing
  ;; the other's vocabulary would sweep a reach the first arm had already doubled, and read
  ;; as an arrival-order effect when it was a leftover.  Its own terms make the second
  ;; arm's reach the same size as the first's, whatever is still standing beside it.
  (binding [checks/*arbitrate-constraints?* true
            tax/*exposure-instance-budget* 11]
    (let [run (fn [backwards?]
                (tu/with-kb [k]
                  (tu/with-terms [aa_t bb_t cc_t dd_t Pip Quo]
                    (doseq [t [aa_t bb_t cc_t dd_t]]
                      (v/assert k (list 'genl t 'thing) 'CxUniverse))
                    (doseq [t [aa_t bb_t cc_t dd_t]]
                      (dotimes [_ 10] (v/assert k (list t (tu/tmp-ind "Pad")) 'CxUniverse)))
                    (v/assert k (list aa_t Pip) 'CxUniverse)
                    (v/assert k (list bb_t Pip) 'CxUniverse)
                    (v/assert k (list cc_t Quo) 'CxUniverse)
                    (v/assert k (list dd_t Quo) 'CxUniverse)
                    (v/clear-violations! k)
                    (v/with-deferred-settle k
                      (doseq [d (cond-> [(list 'disjoint aa_t bb_t) (list 'disjoint cc_t dd_t)]
                                  backwards? reverse)]
                        (v/assert k d 'CxUniverse)))
                    ;; normalized to *which* separation, since the two arms name different
                    ;; terms and the sentences are therefore never `=`
                    {:decided (into #{}
                                    (keep (fn [s]
                                            (let [ts (set (flatten s))]
                                              (cond (contains? ts aa_t) :head
                                                    (contains? ts cc_t) :tail))))
                                    (map :sentence (v/contradictions k)))
                     :cut     (->> (v/violations k)
                                   (filter #(= :arbitration-truncated (:violation %)))
                                   (mapv #(get-in % [:detail :triggers])))})))
          fwd (run false)
          rev (run true)]
      (testing "the content-first trigger gets the budget, whichever was written first"
        (is (contains? (:decided fwd) :head))
        (is (contains? (:decided rev) :head)
            "written second, and still the one the budget was spent on"))
      (testing "and the trigger it could not reach is reported rather than passed over"
        (is (seq (:cut fwd)))
        (is (seq (:cut rev))))
      ;; And the **tail** agrees too, which is the half a weaker reading misses.  The
      ;; budget is one reach, so exactly one of the two separations can be swept and the
      ;; other is cut — and *which* must be decided by `content-order` over the region
      ;; rather than by which was written first.  A reading that only checked the head
      ;; pair would pass while the tail moved with arrival order, which is the shape this
      ;; whole file is about (docs/nmtms.md).
      (is (= (:decided fwd) (:decided rev))
          "the same pairs decided, not merely the same head pair")
      (is (= (:cut fwd) (:cut rev))
          "and the same triggers reported unswept"))))

(tu/deftest-kb an-enumeration-that-exactly-fills-the-budget-is-not-a-cut
  ;; The whole reason the probe takes one past the budget.  A reach of exactly N terms was
  ;; swept in full, and filing it would inflate the number a reader acts on — which is the
  ;; failure `exposure-candidates` measured at 183,397 against a true 41,500.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-terms [t1 t2 Pip]
      ;; built per run and nowhere else: `tu/fresh` clears the scratch space these share,
      ;; so a second copy in the enclosing KB is a second copy in *this* one
      (let [cut-at (fn [budget]
                     (tu/with-kb [k]
                       (doseq [t [t1 t2]] (v/assert k (list 'genl t 'thing) 'CxUniverse))
                       ;; t1's extent is exactly five and is the cheaper side, so it is
                       ;; what `two-sided-reach` enumerates
                       (dotimes [_ 4] (v/assert k (list t1 (tu/tmp-ind "Pad")) 'CxUniverse))
                       (v/assert k (list t1 Pip) 'CxUniverse)
                       (dotimes [_ 9] (v/assert k (list t2 (tu/tmp-ind "Other")) 'CxUniverse))
                       (v/assert k (list t2 Pip) 'CxUniverse)
                       (v/clear-violations! k)
                       (binding [tax/*exposure-instance-budget* budget]
                         (v/assert k (list 'disjoint t1 t2) 'CxUniverse))
                       {:cut     (seq (filter #(= :arbitration-truncated (:violation %))
                                              (v/violations k)))
                        :decided (seq (v/contradictions k))}))]
        (testing "exactly the extent: swept in full, so nothing is filed"
          (let [{:keys [cut decided]} (cut-at 5)]
            (is (nil? cut) "a reach of exactly the budget is not a cut")
            (is (seq decided) "and the pair inside it is decided")))
        (testing "one short: the same reach is a cut, which is what makes the line a line"
          (is (seq (:cut (cut-at 4)))))))))

;;; ── the deciding pass says when it was cut short too ──────────────────
;;
;; `expose-clashes!` files `:exposure-truncated` when the budget stops it, so bounded
;; work never reads as full coverage.  The arbitration sweep spends the same budget
;; before anything is *decided* rather than before anything is reported, which is the
;; half a reader most needs, so it files its own — and its own kind, because a reader
;; acts differently on "went unreported" than on "went undecided", and because
;; `functional` / `asymmetric` reach back here and nowhere else.

(tu/deftest-kb an-arbitration-sweep-cut-short-says-so
  (binding [checks/*arbitrate-constraints?* true
            tax/*exposure-instance-budget* 2]
    (tu/with-terms [t1 t2 Pip]
      (v/assert kb (list 'genl t1 'thing) 'CxUniverse)
      (v/assert kb (list 'genl t2 'thing) 'CxUniverse)
      (dotimes [_ 20] (v/assert kb (list t1 (tu/tmp-ind "Filler")) 'CxUniverse))
      (dotimes [_ 20] (v/assert kb (list t2 (tu/tmp-ind "Other")) 'CxUniverse))
      (v/assert kb (list t1 Pip) 'CxUniverse)
      (v/assert kb (list t2 Pip) 'CxUniverse)
      (v/clear-violations! kb)
      (v/assert kb (list 'disjoint t1 t2) 'CxUniverse)
      (let [cut (filter #(= :arbitration-truncated (:violation %)) (v/violations kb))]
        ;; One entry, and this settle takes one pass — so what the entry's `:triggers`
        ;; counts is not separated here from what the passes counted.  That is the test
        ;; below, over a settle that iterates.
        (is (= 1 (count cut))
            "one entry for the settle")
        (is (= 2 (get-in (first cut) [:detail :budget])))
        (is (<= (count (get-in (first cut) [:detail :sample])) 3)
            "a sample rather than the whole list")
        (is (re-find #"undecided" (get-in (first cut) [:detail :message]))
            "and it says what was left undone, not merely that a bound was hit")))))

(tu/deftest-kb an-arbitration-sweep-that-decides-nothing-still-says-it-was-cut
  ;; **The zero-findings cut**, this sweep's entry in `truncation-kind-tests`.  The
  ;; separation implicates forty memberships and convicts none of them — nobody holds
  ;; both types — so the settle decides nothing and `contradictions` stays empty.  A
  ;; notice hung on what the sweep found would then have nothing to ride on, and the
  ;; instances past the bound would read as instances this settle weighed and let stand.
  (binding [checks/*arbitrate-constraints?* true
            tax/*exposure-instance-budget* 2]
    (tu/with-terms [t1 t2]
      (v/assert kb (list 'genl t1 'thing) 'CxUniverse)
      (v/assert kb (list 'genl t2 'thing) 'CxUniverse)
      (dotimes [_ 20] (v/assert kb (list t1 (tu/tmp-ind "Left")) 'CxUniverse))
      (dotimes [_ 20] (v/assert kb (list t2 (tu/tmp-ind "Right")) 'CxUniverse))
      (v/clear-violations! kb)
      (v/assert kb (list 'disjoint t1 t2) 'CxUniverse)
      (let [cut (filter #(= :arbitration-truncated (:violation %)) (v/violations kb))]
        (is (empty? (v/contradictions kb))
            "the premise: the sweep convicts nobody, so nothing carries a flag")
        (is (= 1 (count cut)) "and the cut is filed all the same")
        (is (= 1 (get-in (first cut) [:detail :triggers])))
        (is (= [(list 'disjoint t1 t2)] (get-in (first cut) [:detail :sample]))
            "naming the declaration whose reach it did not finish")
        (is (= 2 (get-in (first cut) [:detail :budget])))
        (is (re-find #"undecided" (get-in (first cut) [:detail :message]))
            "and saying what was left undone rather than merely unreported")))))

(tu/deftest-kb a-settle-of-several-passes-files-one-trigger-per-declaration
  ;; What `report-arbitration-cut!`'s `distinct` is for, over a settle that can show it.
  ;;
  ;; The sweep runs once per settle **pass** — `constraint-nogoods` re-derives the
  ;; definitional clashes per pass, over a region that accumulates until `settle-finish`
  ;; clears it — so a declaration the budget cut short is noted again on every pass that
  ;; re-reaches it.  `:triggers` is a count a reader acts on ("how many declarations went
  ;; unswept"), so counting the notes instead of the declarations would report two
  ;; unswept declarations where there is one, and the number would move with a fixpoint
  ;; the reader has no way to see.
  ;;
  ;; A one-pass settle cannot separate the two, which is why the test above does not: it
  ;; files one note and reads one trigger whether or not anything dedups.  The
  ;; `exceptWhen` is what makes this settle iterate, and the **write order inside the
  ;; batch** is what makes the exception block rather than refuse: each assertion still
  ;; forward-chains as it lands, so the rule fires on a bird nothing yet excepts, and the
  ;; membership that excepts it arrives after the conclusion is believed.  The first pass
  ;; then moves the blocked set and a second runs to confirm.  (Both facts written before
  ;; the batch, or the excepting one written first, and the firing is refused at derive
  ;; time instead — nothing is blocked, the queue drains empty, and the settle converges
  ;; in a single pass.)  The whole batch is one `with-deferred-settle`, since the cut
  ;; sweep and the extra pass have to be the same settle.
  (binding [checks/*arbitrate-constraints?* true
            tax/*exposure-instance-budget* 2]
    (tu/with-terms [t1 t2 Pip bird penguin flies Opus]
      ;; the separation, with a reach the budget cannot finish
      (v/assert kb (list 'genl t1 'thing) 'CxUniverse)
      (v/assert kb (list 'genl t2 'thing) 'CxUniverse)
      (dotimes [_ 20] (v/assert kb (list t1 (tu/tmp-ind "Filler")) 'CxUniverse))
      (dotimes [_ 20] (v/assert kb (list t2 (tu/tmp-ind "Other")) 'CxUniverse))
      (v/assert kb (list t1 Pip) 'CxUniverse)
      (v/assert kb (list t2 Pip) 'CxUniverse)
      ;; ...and the excepted rule, over vocabulary the separation does not reach
      (v/assert kb (list 'exceptWhen (list penguin '?x)
                         (list 'set/defaultRule
                               (list 'set/forwardRule (vr/rule-sentence [(list bird '?x)] (list flies '?x)))))
                'CxUniverse)
      (v/clear-violations! kb)
      (v/with-deferred-settle kb
        (v/assert kb (list 'disjoint t1 t2) 'CxUniverse)
        (v/assert kb (list bird Opus) 'CxUniverse)
        (v/assert kb (list penguin Opus) 'CxUniverse))
      (let [cut (filter #(= :arbitration-truncated (:violation %)) (v/violations kb))]
        (is (<= 2 (:passes (v/settle-stats kb)))
            "the premise of the test: a settle of one pass sweeps once and dedups nothing")
        (is (= 1 (count cut)) "one entry for the settle")
        (is (= 1 (get-in (first cut) [:detail :triggers]))
            "one declaration went unswept — not one per pass that swept it short")
        (is (= 1 (count (get-in (first cut) [:detail :sample])))
            "and the sample names it once")
        (testing "the exception that made the settle iterate did its own job"
          (is (empty? (v/sentexes-matching kb (list flies Opus) 'CxUniverse))))))))

(tu/deftest-kb a-functional-declaration-swept-short-is-reported-by-nothing-else
  ;; `functional` implicates stored content on the deciding path and on no other, so a
  ;; reader watching only `:exposure-truncated` would never learn its sweep was cut.
  (binding [checks/*arbitrate-constraints?* true
            tax/*exposure-instance-budget* 2]
    (tu/with-terms [ownerOf]
      (v/assert kb (list 'binary_predicate ownerOf) 'CxUniverse)
      (dotimes [_ 20]
        (v/assert kb (list ownerOf (tu/tmp-ind "Thing") (tu/tmp-ind "Who")) 'CxUniverse))
      (v/clear-violations! kb)
      (v/assert kb (list 'functional ownerOf) 'CxUniverse)
      (let [vs (v/violations kb)]
        (is (seq (filter #(= :arbitration-truncated (:violation %)) vs))
            "the deciding pass reports it")
        (is (empty? (filter #(= :exposure-truncated (:violation %)) vs))
            "and the exposure pass has no arm that would")))))

(tu/deftest-kb a-sweep-that-finished-reports-nothing
  (binding [checks/*arbitrate-constraints?* true
            tax/*exposure-instance-budget* 4096]
    (tu/with-terms [t1 t2 Pip]
      (v/assert kb (list 'genl t1 'thing) 'CxUniverse)
      (v/assert kb (list 'genl t2 'thing) 'CxUniverse)
      (v/assert kb (list t1 Pip) 'CxUniverse)
      (v/assert kb (list t2 Pip) 'CxUniverse)
      (v/clear-violations! kb)
      (v/assert kb (list 'disjoint t1 t2) 'CxUniverse)
      (is (empty? (filter #(= :arbitration-truncated (:violation %)) (v/violations kb)))
          "a bound nothing reached is not a truncation")
      (is (seq (v/contradictions kb)) "and the pair it did reach is decided"))))

(tu/deftest-kb a-rebuild-still-sweeps-but-files-no-cut
  ;; Two claims at two budgets, because one budget cannot show both.  The *report* is off
  ;; on a rebuild, like the exposure pass beside it: that settle's region is the whole KB,
  ;; so every declaration in it is cut the moment the budget is spent, and a notice per
  ;; recover would say nothing about the KB and everything about its size.
  ;;
  ;; The *sweep* is not gated the same way.  `recover` binds the flag around two settles
  ;; and the second one's region is only what re-recording the refusals moved — so a
  ;; declaration there still needs its sweep, and a KB that came up without it would
  ;; disagree with one that never restarted.
  (binding [checks/*arbitrate-constraints?* true]
    (let [build (fn [k t1 t2 Pip]
                  (v/assert k (list 'genl t1 'thing) 'CxUniverse)
                  (v/assert k (list 'genl t2 'thing) 'CxUniverse)
                  (dotimes [_ 20] (v/assert k (list t1 (tu/tmp-ind "Filler")) 'CxUniverse))
                  (dotimes [_ 20] (v/assert k (list t2 (tu/tmp-ind "Other")) 'CxUniverse))
                  (v/assert k (list t1 Pip) 'CxUniverse)
                  (v/assert k (list t2 Pip) 'CxUniverse)
                  (v/clear-violations! k))]
      (testing "a budget too small to finish files no notice, because it is a rebuild"
        (tu/with-terms [t1 t2 Pip]
          (tu/with-kb [k]
            (build k t1 t2 Pip)
            (binding [tax/*exposure-instance-budget* 2
                      settle/*rebuilding?* true]
              (v/assert k (list 'disjoint t1 t2) 'CxUniverse))
            (is (empty? (filter #(= :arbitration-truncated (:violation %)) (v/violations k)))
                "off, as it is for the exposure pass"))))
      (testing "and a budget that can finish still decides the pair, rebuilding or not —
                the sweep itself is not gated on the flag"
        (tu/with-terms [t1 t2 Pip]
          (tu/with-kb [k]
            (build k t1 t2 Pip)
            (binding [tax/*exposure-instance-budget* 4096
                      settle/*rebuilding?* true]
              (v/assert k (list 'disjoint t1 t2) 'CxUniverse))
            (is (= [:disjoint] (mapv :kind (v/contradictions k))))))))))

(deftest a-settle-over-the-whole-store-sweeps-nothing-and-files-no-cut
  ;; A load into an empty KB leaves the settle a region holding every stored sentex, so
  ;; the sweep returns no sentex the candidate set does not already hold, and the budget
  ;; it spends there buys nothing.  A cut filed off that settle says content a declaration
  ;; implicates went undecided, in the one settle that decided all of it.  The region
  ;; decides the pair without the sweep, which is the second claim here.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-terms [t1 t2 Pip]
      (let [build (fn [k]
                    (v/assert k (list 'genl t1 'thing) 'CxUniverse)
                    (v/assert k (list 'genl t2 'thing) 'CxUniverse)
                    (dotimes [_ 20] (v/assert k (list t1 (tu/tmp-ind "Filler")) 'CxUniverse))
                    (dotimes [_ 20] (v/assert k (list t2 (tu/tmp-ind "Other")) 'CxUniverse))
                    (v/assert k (list t1 Pip) 'CxUniverse)
                    (v/assert k (list t2 Pip) 'CxUniverse))]
        (testing "one settle over the whole store files no cut, and decides the pair"
          (tu/with-cleared-kb [k tu/fresh]
            (binding [tax/*exposure-instance-budget* 2]
              (v/with-deferred-settle k
                (build k)
                (v/assert k (list 'disjoint t1 t2) 'CxUniverse)))
            (is (empty? (filter #(= :arbitration-truncated (:violation %)) (v/violations k)))
                "the region holds every sentex the sweep would have returned")
            (is (= [:disjoint] (mapv :kind (v/contradictions k)))
                "and the pair is decided off the region")))
        (testing "a declaration whose settle moves less than the store is swept, and a
                  budget too small to finish that sweep files the cut"
          (tu/with-cleared-kb [k tu/fresh]
            (v/with-deferred-settle k (build k))
            (v/clear-violations! k)
            (binding [tax/*exposure-instance-budget* 2]
              (v/assert k (list 'disjoint t1 t2) 'CxUniverse))
            (is (seq (filter #(= :arbitration-truncated (:violation %)) (v/violations k)))
                "the sweep runs whenever the region is smaller than the store")))))))

;; ---- the other two kinds, across the same edge ---------------------------
;;
;; A `functional` slot filled either side of a `genlCx` edge, and an `asymmetric` claim
;; written across one, are weighed at the vantage exactly as a disjointness clash is —
;; under `:refuse` as under `:arbitrate`, since neither writer could see the far half
;; and so neither is being told no.  Same lattice as the disjointness cases above: two
;; siblings neither of which sees the other, and a joint viewer below both that sees the
;; whole pair and decides it.
;;
;; Every pair below is two `:default` claims, so the vantage cannot rank them and the
;; answer is a dilemma: both claims stand and `contradictions` names the pair.

(defn- decided-pairs
  "The settle's dilemmas as `#{[sentence context] …}` sets — a reading that survives the
  arrival order the handles record."
  [kb]
  (into #{} (map (fn [c] (into #{} (map (juxt :sentence :context)) (:sides c))))
        (v/contradictions kb)))

(defn- split-lattice!
  "The declaration and the two siblings with a joint viewer below both — everything but
  the two clashing claims, so a test can choose the order those arrive in."
  [kb {:keys [a b w decl pred]}]
  (v/assert kb (list decl pred) 'CxUniverse)
  (v/assert kb (list 'genlCx a 'CxUniverse) 'CxUniverse)
  (v/assert kb (list 'genlCx b 'CxUniverse) 'CxUniverse)
  (v/assert kb (list 'genlCx w a) 'CxUniverse)
  (v/assert kb (list 'genlCx w b) 'CxUniverse))

(defn- split-pair!
  "Two claims of one predicate, one in each sibling, with a joint viewer below both —
  admissible to both writers, since neither sibling sees the other."
  [kb {:keys [a b one two] :as spec}]
  (split-lattice! kb spec)
  (v/assert kb one a)
  (v/assert kb two b))

(tu/deftest-kb a-functional-slot-filled-across-an-edge-is-decided-at-the-viewer
  ;; The hole this closes.  Neither writer can see the other's filler, so neither is
  ;; refused; the joint viewer CxW sees both, and CxW is the vantage that weighs them.
  (tu/with-terms [CxA CxB CxW birthYear Tom]
    (let [one (list birthYear Tom 1970)
          two (list birthYear Tom 1980)]
      (split-pair! kb {:a CxA :b CxB :w CxW :decl 'functional
                       :pred birthYear :one one :two two})
      (let [cs (v/contradictions kb)]
        (is (= [:functional] (mapv :kind cs)) "one dilemma for the pair, not one per side")
        (is (= #{#{[one CxA] [two CxB]}} (decided-pairs kb))))
      (testing "two defaults cannot be ranked, so both claims stand"
        (is (seq (v/sentexes-matching kb one CxA)))
        (is (seq (v/sentexes-matching kb two CxB)))
        (is (empty? (filter (comp #{:functional} :violation) (v/violations kb)))
            "decided is not exposed")))))

(tu/deftest-kb an-asymmetric-claim-written-across-an-edge-is-decided-at-the-viewer
  (tu/with-terms [CxA CxB CxW largerThan Rex Pip]
    (let [one (list largerThan Rex Pip)
          two (list largerThan Pip Rex)]
      (split-pair! kb {:a CxA :b CxB :w CxW :decl 'asymmetric
                       :pred largerThan :one one :two two})
      (is (= [:asymmetric] (mapv :kind (v/contradictions kb))))
      (is (= #{#{[one CxA] [two CxB]}} (decided-pairs kb)))
      (testing "two defaults cannot be ranked, so both claims stand"
        (is (seq (v/sentexes-matching kb one CxA)))
        (is (seq (v/sentexes-matching kb two CxB)))
        (is (empty? (filter (comp #{:asymmetric} :violation) (v/violations kb))))))))

(deftest the-decision-is-the-same-in-either-arrival-order
  ;; Both halves can sit in one settle's region and each convicts the other, so a pair
  ;; keyed on the walked side would be weighed twice — or read differently — depending on
  ;; which arrived last.  **The two arms share one term set and run over two cleared
  ;; KBs**, so the dilemmas are comparable as values: an arm-local `with-terms` would
  ;; make them differ for a reason that has nothing to do with order.
  (tu/with-terms [CxA CxB CxW birthYear Tom]
    (let [one (list birthYear Tom 1970)
          two (list birthYear Tom 1980)
          spec {:a CxA :b CxB :w CxW :decl 'functional :pred birthYear}
          run  (fn [first-half second-half]
                 (tu/with-cleared-kb [k tu/fresh]
                   (split-lattice! k spec)
                   (v/assert k first-half (if (= first-half one) CxA CxB))
                   (v/assert k second-half (if (= second-half one) CxA CxB))
                   [(mapv :kind (v/contradictions k)) (decided-pairs k)]))
          a (run one two)
          b (run two one)]
      (is (= [[:functional] #{#{[one CxA] [two CxB]}}] a)
          "one dilemma for the pair, whichever half arrived last")
      (is (= a b) "and the identical reading, contexts included"))))

(tu/deftest-kb every-context-that-sees-the-pair-decides-it-not-just-the-convicting-one
  ;; A pair's vantages are a property of the pair, so a second joint viewer is one too.
  ;; Keeping only the vantage that happened to convict would make belief a function of
  ;; which half the region held — the defeat would reach one viewer and not the other.
  ;; The monotonic half is what makes the verdict observable: two defaults tie.
  (tu/with-terms [CxA CxB CxW CxV birthYear Tom]
    (let [one (list birthYear Tom 1970)
          two (list birthYear Tom 1980)]
      (split-lattice! kb {:a CxA :b CxB :w CxW
                          :decl 'functional :pred birthYear})
      ;; a second, incomparable viewer of both siblings, in place before the facts
      (v/assert kb (list 'genlCx CxV CxA) 'CxUniverse)
      (v/assert kb (list 'genlCx CxV CxB) 'CxUniverse)
      (v/assert kb one CxA {:strength :monotonic})
      (v/assert kb two CxB)
      (testing "the loser is defeated at both joint viewers"
        (is (not (v/ask? kb two CxW)))
        (is (not (v/ask? kb two CxV)))
        (is (v/ask? kb one CxW))
        (is (v/ask? kb one CxV)))
      (testing "and stands in its own context, which sees no pair"
        (is (v/ask? kb two CxB))))))

;; `a-wide-slot-cannot-file-its-way-through-the-ledger` and
;; `the-pairs-under-the-cap-are-filed-whole` stood here and are gone with the pass they
;; pinned.  One slot filled from N contexts a single vantage sees is N−1 pairs, and the
;; cross-context report capped them at eight so one settle could not evict a ledger of a
;; thousand.  Those pairs are nogoods now, which are state rather than ledger entries: a
;; reader takes them off `contradictions`, which is recomputed from belief each settle
;; and has no eviction to be starved by.

(deftest either-policy-weighs-the-pair-and-neither-files-it
  ;; The test that catches a policy gate applied in the wrong place.  The vantages are
  ;; asked under both policies, so the pair is decided rather than reported either way —
  ;; and no pass may add a ledger entry there, or the ledger and `contradictions` both
  ;; claim one clash.
  (doseq [policy [:refuse :arbitrate]]
    (testing (str policy)
      (tu/with-neutral-kb [k #(v/open-kb (assoc tu/scratch-space :constraints policy))]
        (tu/with-terms [CxA CxB CxW birthYear Tom]
          (split-pair! k {:a CxA :b CxB :w CxW :decl 'functional
                          :pred birthYear
                          :one (list birthYear Tom 1970) :two (list birthYear Tom 1980)})
          (is (= [:functional] (mapv :kind (v/contradictions k))) "the vantage decides it")
          (is (empty? (filter (comp #{:functional :asymmetric} :violation) (v/violations k)))
              "and the ledger does not also claim it"))))))

(tu/deftest-kb a-pair-both-writers-could-see-is-refused-not-reported
  ;; The gap is cross-context only.  Written in one context the assert entry point sees the
  ;; whole pair and refuses, which is what `:refuse` means — nothing reaches the ledger.
  (tu/with-terms [birthYear Tom]
    (v/assert kb (list 'functional birthYear) 'CxUniverse)
    (v/assert kb (list birthYear Tom 1970) 'CxUniverse)
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list birthYear Tom 1980) 'CxUniverse)))
    (is (empty? (filter (comp #{:functional} :violation) (v/violations kb))))))

(deftest a-self-tuple-in-two-contexts-is-one-pair-in-either-arrival-order
  ;; The converse of `(P a a)` is itself, so both halves are the same sentence in two
  ;; contexts — the case a keying that stops at the sentence gets wrong, by collapsing
  ;; the two sides or by ordering them as the walk supplied.  Two cleared KBs over one
  ;; term set, so the dilemmas compare as values.
  (tu/with-terms [CxA CxB CxW beats Rex]
    (let [claim (list beats Rex Rex)
          run   (fn [c1 c2]
                  (tu/with-cleared-kb [k tu/fresh]
                    (split-lattice! k {:a CxA :b CxB :w CxW
                                       :decl 'asymmetric :pred beats})
                    (v/assert k claim c1)
                    (v/assert k claim c2)
                    [(mapv :kind (v/contradictions k)) (decided-pairs k)]))]
      (is (= [[:asymmetric] #{#{[claim CxA] [claim CxB]}}] (run CxA CxB))
          "one dilemma naming both contexts, not one side twice")
      (is (= (run CxA CxB) (run CxB CxA))
          "and the identical reading whichever context was written first"))))

;; `a-rebuild-reports-nothing-because-nothing-newly-moved` stood here and is gone.  It
;; pinned the rebuild gate on the cross-context *report*; the deciding pass beside it is
;; deliberately not gated that way, since a nogood is state and a rebuild that skipped it
;; would come up believing the loser (`settle/constraint-nogoods`).

(tu/deftest-kb a-predicate-carrying-both-properties-reads-both-postings
  ;; The vantage search reads the argument-1 posting a partner could be in and no other:
  ;; a functional partner shares argument 1, an asymmetric one holds it in argument 2.
  ;; A predicate declared both needs both reads, and dropping either loses a pair rather
  ;; than costing a scan — which a narrowing done for cost is exactly how to get wrong.
  (tu/with-terms [CxA CxB CxW ranks Tom Pip Vic]
    (split-lattice! kb {:a CxA :b CxB :w CxW
                        :decl 'functional :pred ranks})
    (v/assert kb (list 'asymmetric ranks) 'CxUniverse)
    (testing "the functional partner, which shares argument 1"
      (v/assert kb (list ranks Tom 1) CxA)
      (v/assert kb (list ranks Tom 2) CxB)
      (is (= [:functional] (mapv :kind (v/contradictions kb)))))
    (testing "and the asymmetric partner, whose argument 1 is the other side's argument 2"
      ;; fresh subjects: a converse pair on Tom would also be a second filler of Tom's
      ;; functional slot, and the entry point would refuse it before any of this ran
      (v/assert kb (list ranks Pip Vic) CxA)
      (v/assert kb (list ranks Vic Pip) CxB)
      (is (contains? (set (map :kind (v/contradictions kb))) :asymmetric)))))

(tu/deftest-kb an-edge-arriving-after-both-facts-still-decides-the-pair
  ;; The arrival order the region alone cannot see: visibility itself moves, so a pair
  ;; whose halves are already stored and already believed becomes jointly visible without
  ;; either half being relabelled. Neither is in the moved region, so the `genlCx`
  ;; edge has to reach out to them — the same trigger `exposure-candidates` answers for
  ;; disjointness, over the binary-fact parallel of `members-in-ancestors`.
  (tu/with-terms [CxA CxB CxW birthYear Tom]
    (let [one (list birthYear Tom 1970)
          two (list birthYear Tom 1980)]
      (v/assert kb (list 'functional birthYear) 'CxUniverse)
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
      (v/assert kb one CxA)
      (v/assert kb two CxB)
      (is (empty? (v/contradictions kb)) "nothing sees the pair yet")
      (v/assert kb (list 'genlCx CxW CxA) 'CxUniverse)
      (is (empty? (v/contradictions kb)) "seeing one side is not seeing the clash")
      (v/assert kb (list 'genlCx CxW CxB) 'CxUniverse)
      (is (= [:functional] (mapv :kind (v/contradictions kb)))
          "the edge that completes the view weighs the pair")
      (is (= #{#{[one CxA] [two CxB]}} (decided-pairs kb)))
      (is (empty? (filter (comp #{:functional} :violation) (v/violations kb)))
          "decided is not exposed"))))

(deftest the-edges-may-arrive-in-either-position-and-the-decision-is-the-same
  ;; The whole point of the trigger: facts-then-edges and edges-then-facts are the same
  ;; knowledge, so they are one dilemma either way. Two cleared KBs over one term set, so
  ;; the readings compare as values.
  (tu/with-terms [CxA CxB CxW birthYear Tom]
    (let [one   (list birthYear Tom 1970)
          two   (list birthYear Tom 1980)
          decl! (fn [k]
                  (v/assert k (list 'functional birthYear) 'CxUniverse)
                  (v/assert k (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
                  (v/assert k (list 'genlCx CxB 'CxUniverse) 'CxUniverse))
          edges! (fn [k]
                   (v/assert k (list 'genlCx CxW CxA) 'CxUniverse)
                   (v/assert k (list 'genlCx CxW CxB) 'CxUniverse))
          facts! (fn [k] (v/assert k one CxA) (v/assert k two CxB))
          run   (fn [first! second!]
                  (tu/with-cleared-kb [k tu/fresh]
                    (decl! k) (first! k) (second! k)
                    [(mapv :kind (v/contradictions k)) (decided-pairs k)]))
          edges-last  (run facts! edges!)
          edges-first (run edges! facts!)]
      (is (= [[:functional] #{#{[one CxA] [two CxB]}}] edges-first))
      (is (= edges-first edges-last)
          "the identical reading whichever half of the setup arrived last"))))

;; ---- the edge reveals the MARK, not a second fact -----------------------
;;
;; The cases above split the clashing pair across two siblings and bring the two halves
;; into one sight.  The other shape is a pair already **together** in one context `w` and
;; a `(genlCx w c)` edge that reveals the tuple mark standing in `c`: `w` gains sight of
;; the declaration, not of a second fact, so `constraint-facts-in-ancestors` has to read
;; the facts off the edge's **sub** (`w`, the newly-seeing context), not its super.
;; Without that the clash is found only when the mark or a fact arrives last, and the same
;; KB believes differently by arrival order — the invariant `docs/nmtms.md` forbids.
;; Each of the four `:predicate-marked` marks has a witness of this shape below:
;; `functional` and `asymmetric` at arity 2, `anti_transitive` as a three-member triple,
;; and `functionalInArg` at its final position, which is the one `marked-at-final-arg?`
;; branch the arity-2 marks never take.

(tu/deftest-kb a-genlCx-edge-revealing-a-functional-mark-decides-a-co-located-pair
  (tu/with-terms [CxU CxD birthYear Tom]
    (let [one (list birthYear Tom 1970) two (list birthYear Tom 1980)]
      (v/assert kb (list 'functional birthYear) CxD)      ; the mark, invisible to CxU
      (v/assert kb one CxU)
      (v/assert kb two CxU)
      (is (empty? (filter (comp #{:functional} :violation) (v/violations kb)))
          "CxU cannot see the mark yet, so nothing clashes")
      (v/assert kb (list 'genlCx CxU CxD) 'CxUniverse)    ; the edge, arriving last
      (let [cs (v/contradictions kb)]
        (is (= [:functional] (mapv :kind cs)) "the edge reveals the mark and the co-located pair is weighed")
        (is (= #{one two} (set (map :sentence (:sides (first cs)))))))
      (testing "an equal-strength pair is a dilemma: both stand, and nothing is filed as exposed"
        (is (seq (v/sentexes-matching kb one CxU)))
        (is (seq (v/sentexes-matching kb two CxU)))
        (is (empty? (filter (comp #{:functional} :violation) (v/violations kb))))))))

(tu/deftest-kb a-genlCx-edge-revealing-an-anti-transitive-mark-decides-a-co-located-triple
  ;; the three-member nogood, the candidate shape the pairwise reach would miss
  (tu/with-terms [CxU CxD directParentOf Aa Bb Cc]
    (v/assert kb (list directParentOf Aa Bb) CxU)
    (v/assert kb (list directParentOf Bb Cc) CxU)
    (v/assert kb (list directParentOf Aa Cc) CxU)          ; the closing step, beside the chain
    (v/assert kb (list 'anti_transitive directParentOf) CxD)
    (is (empty? (filter (comp #{:anti-transitive} :violation) (v/violations kb)))
        "CxU cannot see the mark yet")
    (v/assert kb (list 'genlCx CxU CxD) 'CxUniverse)
    (let [cs (v/contradictions kb)]
      (is (= [:anti-transitive] (mapv :kind cs))
          "the edge reveals the mark and the chain-plus-step triple is weighed")
      (is (= 3 (count (:sides (first cs))))))
    (testing "an equal-strength triple is a dilemma: all three stand, nothing filed as exposed"
      (is (seq (v/sentexes-matching kb (list directParentOf Aa Cc) CxU)))
      (is (empty? (filter (comp #{:anti-transitive} :violation) (v/violations kb)))))))

(tu/deftest-kb a-genlCx-edge-revealing-an-asymmetric-mark-decides-a-co-located-pair
  ;; the second arity-2 predicate-marked mark, beside `functional`: the reversed-argument
  ;; clash, both halves together in CxU, the mark in CxD, the edge last
  (tu/with-terms [CxU CxD beats Ann Bob]
    (let [one (list beats Ann Bob) two (list beats Bob Ann)]
      (v/assert kb (list 'asymmetric beats) CxD)          ; the mark, invisible to CxU
      (v/assert kb one CxU)
      (v/assert kb two CxU)
      (is (empty? (filter (comp #{:asymmetric} :violation) (v/violations kb)))
          "CxU cannot see the mark yet, so nothing clashes")
      (v/assert kb (list 'genlCx CxU CxD) 'CxUniverse)    ; the edge, arriving last
      (let [cs (v/contradictions kb)]
        (is (= [:asymmetric] (mapv :kind cs)) "the edge reveals the mark and the co-located pair is weighed")
        (is (= #{one two} (set (map :sentence (:sides (first cs)))))))
      (testing "an equal-strength pair is a dilemma: both stand, and nothing is filed as exposed"
        (is (seq (v/sentexes-matching kb one CxU)))
        (is (seq (v/sentexes-matching kb two CxU)))
        (is (empty? (filter (comp #{:asymmetric} :violation) (v/violations kb))))))))

(tu/deftest-kb a-genlCx-edge-revealing-a-functional-in-arg-mark-decides-a-co-located-composite
  ;; `functionalInArg` at its final position, the `marked-at-final-arg?` branch of
  ;; `constraint-facts-in-ancestors` the two arity-2 marks never take: `(functionalInArg P
  ;; 3)` on a ternary, two rows sharing the (arg1,arg2) determinant with unmergeable
  ;; fillers at the constrained position, together in CxU with the mark in CxD.  An
  ;; unmergeable pair at the determined slot reports a `:functional` clash instead of
  ;; merging, so this reads the same violation `functional` does.
  (tu/with-terms [CxU CxD pScore TeamA Y2020]
    (let [one (list pScore TeamA Y2020 10) two (list pScore TeamA Y2020 20)]
      (v/assert kb (list 'functionalInArg pScore 3) CxD)  ; the mark, invisible to CxU
      (v/assert kb one CxU)
      (v/assert kb two CxU)
      (is (empty? (filter (comp #{:functional} :violation) (v/violations kb)))
          "CxU cannot see the mark yet, so nothing clashes")
      (v/assert kb (list 'genlCx CxU CxD) 'CxUniverse)    ; the edge, arriving last
      (let [cs (v/contradictions kb)]
        (is (= [:functional] (mapv :kind cs))
            "the edge reveals the mark and the co-located composite pair is weighed")
        (is (= #{one two} (set (map :sentence (:sides (first cs)))))))
      (testing "an equal-strength pair is a dilemma: both stand, and nothing is filed as exposed"
        (is (seq (v/sentexes-matching kb one CxU)))
        (is (seq (v/sentexes-matching kb two CxU)))
        (is (empty? (filter (comp #{:functional} :violation) (v/violations kb))))))))

(deftest under-arbitrate-a-revealed-mark-defeats-the-co-located-loser-in-every-order
  ;; The belief witness, and the one the exposure half alone does not give: under
  ;; `:arbitrate` the deciding path weighs the pair, so the revealed mark must defeat the
  ;; :default loser against a :monotonic rival — and the answer may not turn on which of
  ;; {mark, facts, edge} arrived last.  `:arbitrate`, since that is where belief moves.
  ;; `functional` and `asymmetric` both decide the clash by defeat and run here together;
  ;; `functionalInArg` decides by merging the fillers, a different outcome, so it is pinned
  ;; by its own exposure witness above rather than folded into this defeat test.
  (tu/with-terms [CxU CxD birthYear Tom beats Ann Bob]
    (doseq [[mark mono loser]
            [[(list 'functional birthYear) (list birthYear Tom 1970) (list birthYear Tom 1980)]
             [(list 'asymmetric beats)     (list beats Ann Bob)      (list beats Bob Ann)]]]
      (let [mark! #(v/assert % mark CxD)
            edge! #(v/assert % (list 'genlCx CxU CxD) 'CxUniverse)
            m!    #(v/assert % mono CxU {:strength :monotonic})  ; known-true, stands
            l!    #(v/assert % loser CxU {:strength :default})   ; defeasible, must lose
            ;; the loser reaches "not believed" two legitimate ways under :arbitrate —
            ;; stored then defeated (edge/mark last), or refused at the entry point when the
            ;; visible known-true rival is already there (facts last, where admitting it
            ;; would store what can never be believed).  Either is order-independent belief;
            ;; the catch tolerates the entry refusal so the final believed set is compared.
            belief (fn [order]
                     (tu/with-neutral-kb [k #(v/open-kb (assoc tu/scratch-space :constraints :arbitrate))]
                       (doseq [step order]
                         (try (step k) (catch clojure.lang.ExceptionInfo _ nil)))
                       [(boolean (seq (v/sentexes-matching k mono CxU)))
                        (boolean (seq (v/sentexes-matching k loser CxU)))]))]
        (doseq [[label order] [[:edge-last  [mark! m! l! edge!]]
                               [:mark-last  [edge! m! l! mark!]]
                               [:facts-last [mark! edge! m! l!]]]]
          (is (= [true false] (belief order))
              (str mark " / " (name label)
                   ": the monotonic fact stands and the default loser does not")))))))

(tu/deftest-kb an-edge-whose-ancestor-set-is-cut-short-says-so
  ;; The trigger reaches out of the region, so it is budgeted like every other sweep —
  ;; and a bounded sweep that reads as full coverage is the failure all of them guard
  ;; against.  The edge reveals a mark to the facts in the ancestor set it opens, and the
  ;; deciding sweep is what walks them, so the notice is `:arbitration-truncated`:
  ;; content the edge implicates went **undecided**.
  ;; Distinct subjects, so the ancestor set is full of candidates and *none* of them
  ;; pairs — nothing but the cut itself can say four of the six facts were never looked
  ;; at.
  (tu/with-terms [CxSrc CxW birthYear]
    (v/assert kb (list 'functional birthYear) 'CxUniverse)
    (v/assert kb (list 'genlCx CxSrc 'CxUniverse) 'CxUniverse)
    (doseq [i (range 6)]
      (v/assert kb (list birthYear (tu/tmp-ind "Subj") (+ 1900 i)) CxSrc))
    (v/clear-violations! kb)
    (binding [tax/*exposure-instance-budget* 2]
      (v/assert kb (list 'genlCx CxW CxSrc) 'CxUniverse))
    (let [vs  (v/violations kb)
          cut (filter (comp #{:arbitration-truncated} :violation) vs)]
      (is (empty? (v/contradictions kb))
          "no pair is decided — the subjects are distinct")
      (is (= 1 (count cut)) "and the cut is still never silent")
      (is (= 1 (get-in (first cut) [:detail :triggers]))
          "it names how many declarations went unswept")
      (is (= [(list 'genlCx CxW CxSrc)] (get-in (first cut) [:detail :sample]))
          "and which edge that was")
      (is (= 2 (get-in (first cut) [:detail :budget])))
      (is (re-find #"undecided" (get-in (first cut) [:detail :message]))
          "the reader is told what it costs: content nobody weighed"))))

(tu/deftest-kb siblings-with-no-joint-viewer-report-nothing
  ;; The ∃-vantage reading, for these two kinds: the claims coexist and no single
  ;; context sees both, so there is nobody the pair is a clash for.
  (tu/with-terms [CxA CxB birthYear Tom]
    (v/assert kb (list 'functional birthYear) 'CxUniverse)
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list birthYear Tom 1970) CxA)
    (v/assert kb (list birthYear Tom 1980) CxB)
    (is (empty? (filter (comp #{:functional} :violation) (v/violations kb))))))

;; ---- and the edge that carries the mark rather than the view -------------
;;
;; A mark is read up the predicate hierarchy (`tax/props-over`), so a pair of `fatherOf`
;; facts either side of a visibility edge is a `(functional parentOf)` clash — and the
;; region walk finds it by itself, because `declared?` asks the same descending question.
;; What the region cannot supply is the pair whose `(genl fatherOf parentOf)` edge arrives
;; **last**: a predicate edge relabels neither half, so neither half is in the region, and
;; the edge is a binary sentence whose own functor carries no mark, so it is a candidate
;; for nothing.  Only naming it a trigger reaches them.  Same shape as the `genlCx` case
;; above and the same answer — the disjointness pass has the analogous arm, over the
;; memberships an edge newly separates.

(tu/deftest-kb a-genl-edge-arriving-after-both-facts-carries-the-mark-down
  (tu/with-terms [CxA CxB CxW birthYear measureOf Tom]
    (let [one (list birthYear Tom 1970)
          two (list birthYear Tom 1980)]
      (v/assert kb (list 'functional measureOf) 'CxUniverse)
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxW CxA) 'CxUniverse)
      (v/assert kb (list 'genlCx CxW CxB) 'CxUniverse)
      (v/assert kb one CxA)
      (v/assert kb two CxB)
      (is (empty? (v/contradictions kb))
          "nothing marked sits above birthYear yet, so the two are unrelated fillers")
      (v/assert kb (list 'genl birthYear measureOf) 'CxUniverse)
      (is (= [:functional] (mapv :kind (v/contradictions kb)))
          "the edge that carries the mark down brings the pair to its vantage")
      (is (= #{#{[one CxA] [two CxB]}} (decided-pairs kb)))
      (testing "two defaults cannot be ranked, so both claims stand"
        (is (seq (v/sentexes-matching kb one CxA)))
        (is (seq (v/sentexes-matching kb two CxB)))
        (is (empty? (filter (comp #{:functional} :violation) (v/violations kb))))))))

(tu/deftest-kb an-asymmetric-mark-descends-to-a-claim-written-across-an-edge
  (tu/with-terms [CxA CxB CxW muchLargerThan largerThan Rex Pip]
    (let [one (list muchLargerThan Rex Pip)
          two (list muchLargerThan Pip Rex)]
      (v/assert kb (list 'asymmetric largerThan) 'CxUniverse)
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxW CxA) 'CxUniverse)
      (v/assert kb (list 'genlCx CxW CxB) 'CxUniverse)
      (v/assert kb one CxA)
      (v/assert kb two CxB)
      (is (empty? (v/contradictions kb)))
      (v/assert kb (list 'genl muchLargerThan largerThan) 'CxUniverse)
      (is (= [:asymmetric] (mapv :kind (v/contradictions kb))))
      (is (= #{#{[one CxA] [two CxB]}} (decided-pairs kb)))
      (is (empty? (filter (comp #{:asymmetric} :violation) (v/violations kb)))))))

(deftest the-mark-may-descend-before-or-after-the-facts-and-the-decision-is-the-same
  ;; The control beside the case that was silent, and the reason it is worth pinning: with
  ;; the edge already in place the region walk found the pair by itself, since `declared?`
  ;; reads the mark up the hierarchy — so that arm passed throughout and the asymmetry
  ;; between the two was invisible from either side alone.  Two cleared KBs over one term
  ;; set, so the entries compare as values.
  (tu/with-terms [CxA CxB CxW birthYear measureOf Tom]
    (let [one    (list birthYear Tom 1970)
          two    (list birthYear Tom 1980)
          decl!  (fn [k]
                   (v/assert k (list 'functional measureOf) 'CxUniverse)
                   (v/assert k (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
                   (v/assert k (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
                   (v/assert k (list 'genlCx CxW CxA) 'CxUniverse)
                   (v/assert k (list 'genlCx CxW CxB) 'CxUniverse))
          edge!  (fn [k] (v/assert k (list 'genl birthYear measureOf) 'CxUniverse))
          facts! (fn [k] (v/assert k one CxA) (v/assert k two CxB))
          run    (fn [first! second!]
                   (tu/with-cleared-kb [k tu/fresh]
                     (decl! k) (first! k) (second! k)
                     [(mapv :kind (v/contradictions k)) (decided-pairs k)]))
          edge-last  (run facts! edge!)
          edge-first (run edge! facts!)]
      (is (= [[:functional] #{#{[one CxA] [two CxB]}}] edge-first))
      (is (= edge-first edge-last)
          "the identical reading whichever of the mark's descent and the facts came last"))))

(tu/deftest-kb a-genl-edge-under-no-marked-predicate-is-not-a-trigger
  ;; `genl` is the commonest edge in an ontology, so an edge with no mark above it must
  ;; cost the pass a `props-over` read and no sweep at all.  Read off the budget, which is
  ;; the one observable: an edge that swept would spend it on the six facts below it and
  ;; file a cut notice saying so.
  (tu/with-terms [CxSrc birthYear plainOf otherOf]
    (v/assert kb (list 'functional birthYear) 'CxUniverse)   ; so the pass runs at all
    (v/assert kb (list 'genlCx CxSrc 'CxUniverse) 'CxUniverse)
    (doseq [i (range 6)]
      (v/assert kb (list plainOf (tu/tmp-ind "Subj") (+ 1900 i)) CxSrc))
    (v/clear-violations! kb)
    (binding [tax/*exposure-instance-budget* 2]
      (v/assert kb (list 'genl plainOf otherOf) 'CxUniverse))
    (is (empty? (v/violations kb))
        "nothing marked above either end, so nothing was enumerated and nothing was cut")))

(tu/deftest-kb an-edge-whose-subtree-is-cut-short-says-so
  ;; The `genlCx` twin one screen up, for the other edge: the trigger reaches out of the
  ;; region, so it is budgeted like every other sweep, and a bounded sweep that read as
  ;; full coverage is the failure all of them guard against.
  ;; Distinct subjects, so the subtree is full of candidates and *none* of them pairs —
  ;; the entry filed can then only be the sweep's, not the cap's.
  (tu/with-terms [CxSrc CxW birthYear measureOf]
    (v/assert kb (list 'functional measureOf) 'CxUniverse)
    (v/assert kb (list 'genlCx CxSrc 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxW CxSrc) 'CxUniverse)
    (doseq [i (range 6)]
      (v/assert kb (list birthYear (tu/tmp-ind "Subj") (+ 1900 i)) CxSrc))
    (v/clear-violations! kb)
    (binding [tax/*exposure-instance-budget* 2]
      (v/assert kb (list 'genl birthYear measureOf) 'CxUniverse))
    (let [cut (filter (comp #{:arbitration-truncated} :violation) (v/violations kb))]
      (is (empty? (v/contradictions kb))
          "no pair is decided — the subjects are distinct")
      (is (seq cut) "and the cut is still never silent")
      (is (pos? (get-in (first cut) [:detail :triggers]))
          "it names how many declarations went unswept"))))

(defn- orderings
  "Every arrival order of `xs`.  The case below runs over all of them rather than over a
  hand-picked few: which sentence is last is exactly what decides whether this policy
  reports, so a subset would be choosing the answer."
  [xs]
  (if (< (count xs) 2)
    [(vec xs)]
    (for [x xs, tail (orderings (remove #{x} xs))]
      (into [x] tail))))

(deftest every-arrival-order-of-a-cross-context-clash-decides-it-once
  ;; **All three ingredients are triggers, so all six orders decide.**  A pair split
  ;; across a visibility edge needs the mark, the `genl` edge that carries it down to the
  ;; predicate the facts are written under, and the two claims themselves — and whichever
  ;; of the three lands last is what the sweep has to reach back from.  The mark's own
  ;; sentence is a trigger for exactly that reason: the two facts it convicts move nothing
  ;; when it arrives, so a pass reading only the region would weigh this in five orders
  ;; out of six and let the mark decide the sixth.
  ;;
  ;; **Once**, not once per member and not once per route.  Both facts and the edge can
  ;; be reached in one settle, and the nogood is keyed on the handle set to collapse them
  ;; (`settle/clash-nogoods`), so a count above one is a reading that depends on how the
  ;; clash was found rather than on what it is.
  (tu/with-terms [CxA CxB CxW birthYear measureOf Tom]
    (doseq [order (orderings [:declaration :edge :facts])]
      (tu/with-cleared-kb [k tu/fresh]
        (v/assert k (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
        (v/assert k (list 'genlCx CxB 'CxUniverse) 'CxUniverse)
        (v/assert k (list 'genlCx CxW CxA) 'CxUniverse)
        (v/assert k (list 'genlCx CxW CxB) 'CxUniverse)
        (let [step {:declaration #(v/assert k (list 'functional measureOf) 'CxUniverse)
                    :edge        #(v/assert k (list 'genl birthYear measureOf) 'CxUniverse)
                    :facts       #(do (v/assert k (list birthYear Tom 1970) CxA)
                                      (v/assert k (list birthYear Tom 1980) CxB))}]
          (doseq [s order] ((step s)))
          (is (= [:functional] (mapv :kind (v/contradictions k)))
              (str "decided once under " (pr-str order)))
          (is (empty? (filter (comp #{:functional} :violation) (v/violations k)))
              (str "and not also reported under " (pr-str order))))))))

;;; ── every bounded pass owes a test of what fires its notice ───────────
;;
;; A truncation notice is filed off the **bound** and never off what the pass found, and
;; the failure when one is not is silent: a passing suite, an empty ledger, and a KB
;; that reads as clean while a sweep looked at nothing.  So each bounded pass owes a
;; test that arranges the bound firing with *nothing* found and demands the notice
;; anyway — and this roster is what stops a further one arriving without it.

(def ^:private truncation-kind-tests
  "Every truncation kind `vaelii.impl.settle` files, against the test that pins what
  fires it — the bound, and never what the pass happened to find.

  Two classes of bound, and what a test can demand differs between them.  A **budget
  cut** is independent of the findings — a sweep spends the budget convicting nobody,
  and every unit after it is bounded to zero and examined — so its test arranges exactly
  that and is the case a notice riding on a finding gets wrong.  A **ledger cap** counts
  what was found, examined and left unnamed, so it cannot fire with nothing found at
  all; its test is the one holding it apart from a cut, since confusing the two tells a
  reader content went unlooked-at when it was looked at and summarized.
  The kinds are read out of the source rather than listed here: a roster with both
  halves hand-written checks only that somebody typed the same thing twice.  A
  whole-file keyword scan rather than the call sites, because which function files a
  kind — and through which helper — is what a refactor moves, and a roster keyed on the
  call shape would go quiet on the change most likely to drop a notice."
  '{:exposure-truncated
    vaelii.exposure-test/a-sweep-that-convicts-nobody-still-stops-at-the-bound
    :arbitration-truncated
    vaelii.exposure-test/an-arbitration-sweep-that-decides-nothing-still-says-it-was-cut
    :arity-truncated
    vaelii.constraint-descension-test/the-budget-running-out-on-an-innocent-predicate-is-still-said-out-loud
    :arity-report-truncated
    vaelii.constraint-descension-test/a-wide-subtree-cannot-file-its-way-through-the-ledger
    :partner-sweep-truncated
    vaelii.exposure-test/an-unnarrowed-partner-sweep-that-finds-nobody-still-says-it-was-cut})

(deftest every-truncation-kind-has-a-test-of-what-fires-it
  ;; `code-only` and not a bare `slurp`: every one of the five kinds is *named in prose*
  ;; in `settle.clj` — each has between one and three docstring mentions beside its one
  ;; filing site — so a raw scan reads the documentation as a filing and the
  ;; `kinds`-minus-tests direction below stays green with every real filing deleted.
  ;; `violation_roster_test` ships the blanker for exactly this reason and says so.
  (let [src   (roster/code-only (slurp "src/vaelii/impl/settle.clj"))
        kinds (into #{}
                    (map (comp keyword second))
                    (re-seq #":([a-z][a-z-]*-truncated)\b" src))
        ;; The other way in, and the one a further bounded sweep is most likely to take
        ;; now that the helper exists: a kind spelled anything at all, handed to
        ;; `cut-notice`.  The scan above would miss it; this one cannot, and neither
        ;; needs a second hand-written list to stay true.
        filed (into #{} (map (comp keyword second))
                    (re-seq #"\(cut-notice\s+:([\w-]+)" src))]
    (is (<= 5 (count kinds))
        "the scan reads the kinds at all — an empty set would pass every check below")
    (is (empty? (set/difference filed (set (keys truncation-kind-tests))))
        (str "a kind filed through `cut-notice` with no test of what fires it: "
             (set/difference filed (set (keys truncation-kind-tests)))))
    (is (empty? (set/difference kinds (set (keys truncation-kind-tests))))
        (str "a truncation kind with no test that its bound is what files it: "
             (set/difference kinds (set (keys truncation-kind-tests)))))
    (is (empty? (set/difference (set (keys truncation-kind-tests)) kinds))
        (str "a rostered kind settle no longer files: "
             (set/difference (set (keys truncation-kind-tests)) kinds)))
    ;; The var, not its `:test` metadata: a selector **strips** `:test` from every test
    ;; it does not select, so reading it would make this fail under `lein test :only`
    ;; while saying the tests had been deleted.  A renamed or deleted one is what the
    ;; roster is for, and resolving catches both.
    (doseq [[kind sym] truncation-kind-tests]
      (is (some? (requiring-resolve sym))
          (str kind " names a test that does not exist: " sym)))))

(tu/deftest-kb a-negative-exposure-budget-is-a-cut-not-a-crash
  ;; `*exposure-instance-budget*` is a public dynamic var; a negative value means
  ;; "nothing more", which is a cut of everything — not a `(subvec … 0 -1)` thrown out
  ;; of the settle that reads it.
  (tu/with-terms [CxA CxB CxW left_t right_t Pip]
    (v/assert kb (list 'disjoint left_t right_t) 'CxUniverse)
    (siblings! kb {:a CxA :b CxB :t1 left_t :t2 right_t :x Pip})
    (v/assert kb (list 'genlCx CxW CxA) 'CxUniverse)
    (let [h (binding [tax/*exposure-instance-budget* -1]
              (v/assert kb (list 'genlCx CxW CxB) 'CxUniverse))]
      (is (nat-int? h)
          "the settle reading a negative budget completes and the edge gets a handle"))))

;;; ── the partner sweep's own bound ─────────────────────────────────────
;;
;; `partner-contexts` is the one bounded read in `settle` with no settle-wide budget to
;; debit: it runs at the assert entry point as well as inside a settle, so there is no
;; `left` volatile to thread through it.  Its unnarrowed arm — a `functionalInArg` mark
;; whose declared position is the whole tuple, leaving no single argument root to narrow
;; by — is a real extent sweep, and it shipped capped but silent.  A cut there costs a
;; *vantage*, so the pairs it loses appear in `:arbitration-truncated`'s trigger count
;; not at all rather than as content swept short, which is why it is its own kind.

(tu/deftest-kb an-unnarrowed-partner-sweep-that-finds-nobody-still-says-it-was-cut
  ;; **The zero-findings cut**, this read's entry in `truncation-kind-tests`.  Every
  ;; fact sits in its own leaf context and no context is below two of them, so no
  ;; vantage sees a pair and the settle decides no clash at all — an entry riding on a
  ;; finding would have nowhere to go, and the six instances past the bound would read
  ;; as six that were cleared.
  (binding [tax/*exposure-instance-budget* 2]
    (tu/with-terms [p]
      (v/assert kb (list 'unary_predicate p) 'CxUniverse)
      (v/assert kb (list 'functionalInArg p 1) 'CxUniverse)
      (let [ctxs (vec (repeatedly 6 #(tu/tmp-ctx "Leaf")))]
        (doseq [c ctxs]
          (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
        (doseq [[i c] (map-indexed vector (butlast ctxs))]
          (v/assert kb (list p (inc i)) c))
        (v/clear-violations! kb)
        (v/assert kb (list p 99) (last ctxs))
        (let [vs  (v/violations kb)
              cut (filter #(= :partner-sweep-truncated (:violation %)) vs)]
          (is (empty? (filter #(= :functional (:violation %)) vs))
              "no context is below two leaves, so there is no clash to expose")
          (is (= 1 (count cut))
              "and the pass says the partner sweep stopped early rather than claiming it looked")
          (is (= 2 (get-in (first cut) [:detail :budget])))
          (is (= [{:pred p :arity 1 :budget 2}] (get-in (first cut) [:detail :sweeps]))
              "naming the predicate and the arity whose determinant left no root to narrow by")
          (is (re-find #"not asked" (get-in (first cut) [:detail :message]))
              "the reader is told what it costs: a vantage that is never consulted"))))))

(tu/deftest-kb a-partner-sweep-inside-its-bound-files-nothing
  ;; The gate on the notice is the cap, not the mark: an ordinary KB using
  ;; `functionalInArg` at an unnarrowed position must not start carrying one.
  (binding [tax/*exposure-instance-budget* 64]
    (tu/with-terms [p]
      (v/assert kb (list 'unary_predicate p) 'CxUniverse)
      (v/assert kb (list 'functionalInArg p 1) 'CxUniverse)
      (let [ctxs (vec (repeatedly 4 #(tu/tmp-ctx "Leaf")))]
        (doseq [c ctxs]
          (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
        (doseq [[i c] (map-indexed vector (butlast ctxs))]
          (v/assert kb (list p (inc i)) c))
        (v/clear-violations! kb)
        (v/assert kb (list p 99) (last ctxs))
        (is (empty? (filter #(= :partner-sweep-truncated (:violation %)) (v/violations kb)))
            "four instances against a budget of sixty-four is not a cut")))))

;;; ── the mark rosters, which drifted once ──────────────────────────────

;; `every-functional-family-mark-is-in-both-of-settles-rosters` stood here and is gone.
;; It asserted over `settle`'s two rosters what #54 broke: the generalized functional mark
;; enrolled for the clash reach and not for the trigger, or the reverse.  Both rosters are
;; read off `predicates` now, and `predicates/check-families` refuses at namespace load the
;; two ways that declaration can be half-written — a family whose spellings disagree about
;; what they sweep, and a term that sweeps and declares no shape for a trigger to recognize
;; it at.  Driven against a deliberately broken table in `predicates_test`; the lane facets
;; the same family has to agree about are `check-facets`, and the one move neither validator
;; can refuse — a spelling dropped from the family outright — is pinned as a literal by
;; `predicates_test/the-declaration-reconstructs-the-taxonomy-rosters`.  The behavioural
;; half is `functional_in_arg_test`'s three declaration-last rows and stays where it is.
