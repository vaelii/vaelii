;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.edit-test
  "`edit` — a batched add-then-remove that settles once.  The point is efficiency and
  a stable belief state: adds land before removes, so a conclusion the removed premise
  solely-supported but an added one re-derives keeps a witness through the
  dependency-directed sweep — it is never swept and rebuilt, and never flickers OUT and
  back.  The final state equals running the asserts and retracts singly.

  And it is **all-or-nothing**: an engine refusal `check-edit` cannot predict — one that
  only bites because an earlier entry in the same batch landed first — is raised on the
  entry that trips it, and the batch is then taken back at the handles it wrote."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kbi]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(deftest edit-adds-before-removing-so-a-rederivable-conclusion-survives
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [a b c X CxThe]
      ;; two rules concluding the same thing, from different premises
      (v/assert-rule kb [(list a '?x)] (list c '?x) CxThe {:direction :forward})
      (v/assert-rule kb [(list b '?x)] (list c '?x) CxThe {:direction :forward})
      (let [fa (v/assert kb (list a X) CxThe)
            ch (v/handle-of kb (list c X) CxThe)]
        (is (v/in? kb ch) "(c X) is derived from (a X)")
        (let [result (v/edit! kb {:add [[(list b X) CxThe]] :remove [fa]})]
          (testing "the return reports the add and the teardown"
            (is (= 1 (count (:added result))))
            (is (pos? (:removed-sentexes (:removed result)))))
          (testing "the removed premise is gone and the added one is believed"
            (is (nil? (v/handle-of kb (list a X) CxThe)))
            (is (v/in? kb (v/handle-of kb (list b X) CxThe))))
          (testing "(c X) survived on the new support — same handle, still IN"
            (is (v/in? kb ch))
            (is (contains?
                 (->> (v/supporting-justifications kb ch)
                      (mapcat :antecedents) set)
                 (v/handle-of kb (list b X) CxThe))
                "its live support now names the added premise")))))))

(deftest edit-matches-separate-assert-and-retract
  ;; Run the same scenario two ways on two *sequential* fresh KBs (nesting two
  ;; `tu/fresh` would collide — both take the scratch db pair), then compare belief.
  (tu/with-terms [a b c X CxThe]
    (letfn [(scenario [kb via-edit?]
              (v/assert-rule kb [(list a '?x)] (list c '?x) CxThe {:direction :forward})
              (v/assert-rule kb [(list b '?x)] (list c '?x) CxThe {:direction :forward})
              (let [fa (v/assert kb (list a X) CxThe)]
                (if via-edit?
                  (v/edit! kb {:add [[(list b X) CxThe]] :remove [fa]})
                  (do (v/assert kb (list b X) CxThe)   ; add...
                      (v/retract! kb fa))))               ; ...then remove
              (into {} (for [s [(list a X) (list b X) (list c X)]]
                         [s (let [h (v/handle-of kb s CxThe)] (boolean (and h (v/in? kb h))))])))]
      (let [via-edit (tu/with-neutral-kb [kb tu/fresh] (scenario kb true))
            via-sep  (tu/with-neutral-kb [kb tu/fresh] (scenario kb false))]
        (is (= via-edit via-sep)
            "edit reaches the same belief as add-then-retract done singly")
        (is (get via-edit (list c X)) "(c X) is believed either way")))))

(deftest edit-degenerate-only-adds-or-only-removes
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [p q X CxThe]
      (testing "only adds behaves like assert-many"
        (let [r (v/edit! kb {:add [[(list p X) CxThe] [(list q X) CxThe]]})]
          (is (= 2 (count (:added r))))
          (is (= {:removed-sentexes 0 :removed-justifications 0} (:removed r)))
          (is (v/in? kb (v/handle-of kb (list p X) CxThe)))
          (is (v/in? kb (v/handle-of kb (list q X) CxThe)))))
      (testing "only removes behaves like retract"
        (let [ph (v/handle-of kb (list p X) CxThe)
              r  (v/edit! kb {:remove [ph]})]
          (is (empty? (:added r)))
          (is (pos? (:removed-sentexes (:removed r))))
          (is (nil? (v/handle-of kb (list p X) CxThe)))
          (is (v/in? kb (v/handle-of kb (list q X) CxThe)) "the untouched premise stays"))))))

(defn- supports-by-content
  "`sentences`' supporting justifications in `context`, antecedents read as sentences."
  [kb sentences context]
  (into {} (for [s sentences]
             [s (when-let [h (v/handle-of kb s context)]
                  (when (v/in? kb h)
                    (into #{} (map (fn [j] [(set (map #(:sentence (v/sentex kb %)) (:antecedents j)))
                                            (:subsumptions j) (:strength j)]))
                          (v/supporting-justifications kb h))))])))

(deftest a-batch-of-genl-edges-derives-what-asserting-them-singly-derives
  (tu/with-terms [a b leaf mid top marked likes fan X Y Z CxThe]
    (let [edges [(list 'genl a mid) (list 'genl b mid) (list 'genl mid top) (list 'genl a top)]
          concl [(list marked X) (list marked Y) (list marked Z) (list fan Z)]
          run   (fn [kb via-edit?]
                  (v/assert-rule kb [(list top '?x)] (list marked '?x) CxThe {:direction :forward})
                  (v/assert-rule kb [(list top '?x) (list likes '?x '?y)] (list fan '?y) CxThe
                                 {:direction :forward})
                  (doseq [s [(list 'genl leaf a) (list a X) (list b Y) (list leaf Z) (list likes Z Z)]]
                    (v/assert kb s CxThe))
                  (if via-edit?
                    (v/edit! kb {:add (mapv #(vector % CxThe) edges)})
                    (doseq [e edges] (v/assert kb e CxThe)))
                  (supports-by-content kb concl CxThe))
          batch  (tu/with-neutral-kb [kb tu/fresh] (run kb true))
          single (tu/with-neutral-kb [kb tu/fresh] (run kb false))]
      (is (= single batch))
      (is (every? seq (vals batch)) "every conclusion is derived"))))

(deftest an-edit-chains-a-subtree-two-genl-edges-share-once
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [a leaf top1 top2 marked1 marked2 X Z CxThe]
      (v/assert-rule kb [(list top1 '?x)] (list marked1 '?x) CxThe {:direction :forward})
      (v/assert-rule kb [(list top2 '?x)] (list marked2 '?x) CxThe {:direction :forward})
      (v/assert kb (list 'genl leaf a) CxThe)
      (let [fx    (v/assert kb (list a X) CxThe)
            fz    (v/assert kb (list leaf Z) CxThe)
            seeds (atom [])
            chain chain/chain-all]
        (with-redefs [chain/chain-all (fn [k seed opts] (swap! seeds into seed) (chain k seed opts))]
          (v/edit! kb {:add [[(list 'genl a top1) CxThe] [(list 'genl a top2) CxThe]]}))
        (is (= {fx 1 fz 1} (select-keys (frequencies @seeds) [fx fz])))
        (is (every? #(v/in? kb (v/handle-of kb % CxThe))
                    [(list marked1 X) (list marked1 Z) (list marked2 X) (list marked2 Z)]))))))

(defn- context-state
  "The sentences `kb` stores in `context`, and the ones it believes there."
  [kb context]
  [(set (map v/sentence-of (v/sentexes-in-context kb context)))
   (set (map v/sentence-of (v/sentexes-in-context kb context {:believed? true})))])

(deftest replace-facts-leaves-what-a-kb-told-the-second-snapshot-holds
  (tu/with-terms [p q nearTo A B C D E F CxSnap CxOther]
    (let [rule  (list 'set/forwardRule (list 'implies (list p '?x) (list q '?x)))
          snap1 [(list p A) (list p B) (list p C) (list nearTo A B)]
          snap2 [(list p A) (list p B) (list p D) (list nearTo B A) (list p E)]
          base  (fn [kb]
                  (v/assert kb (list 'symmetric nearTo) 'CxUniverse {:strength :monotonic})
                  (v/assert kb rule CxSnap)
                  (v/assert kb (list p F) CxOther))
          after (fn [kb] [(context-state kb CxSnap) (context-state kb CxOther)])
          [counts replaced again]
          (tu/with-neutral-kb [kb tu/fresh]
            (base kb)
            (v/replace-facts! kb CxSnap snap1)
            (let [r (v/replace-facts! kb CxSnap snap2)]
              [(select-keys r [:added :removed]) (after kb) (v/replace-facts! kb CxSnap snap2)]))
          loaded (tu/with-neutral-kb [kb tu/fresh]
                   (base kb)
                   (doseq [s snap2] (v/assert kb s CxSnap))
                   (after kb))]
      (is (= {:added 2 :removed 1} counts) "(p D) and (p E) arrive, (p C) leaves, (nearTo B A) is held")
      (is (= loaded replaced)
          "the rule, the derived (q x), CxOther's premise and the stored and believed sets agree")
      (is (= {:added 0 :removed 0 :edit nil} again) "an equal snapshot writes nothing"))))

(deftest replace-facts-never-withdraws-a-conclusion-both-snapshots-support
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [a b c X CxSnap]
      (v/assert kb (list 'set/forwardRule (list 'implies (list a '?x) (list c '?x))) CxSnap)
      (v/assert kb (list 'set/forwardRule (list 'implies (list b '?x) (list c '?x))) CxSnap)
      (v/replace-facts! kb CxSnap [(list a X)])
      (let [events (atom [])
            moved  #(vec (mapcat (juxt :believed-added :believed-removed) @events))
            hc     (v/handle-of kb (list c X) CxSnap)
            token  (v/watch kb (list c '?x) CxSnap #(swap! events conj %))]
        (try
          (v/replace-facts! kb CxSnap [(list b X)])
          (is (= [[] true hc] [(remove empty? (moved)) (v/in? kb hc) (v/handle-of kb (list c X) CxSnap)])
              "(c X) moves from (a X)'s support to (b X)'s with no event and keeps its handle")
          (v/retract! kb (v/handle-of kb (list b X) CxSnap))
          (v/assert kb (list a X) CxSnap)
          (is (seq (remove empty? (moved))) "a retract deletes (c X) unreported (docs/feed.md) and the assert reports it rederived")
          (finally (v/unwatch kb token)))))))

(deftest replace-facts-refuses-a-rule-among-the-facts
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [p q CxSnap]
      (is (= :shape (try (v/replace-facts! kb CxSnap [(list 'implies (list p '?x) (list q '?x))])
                         nil
                         (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
      (is (zero? (v/count-in-context kb CxSnap))))))

(deftest replace-facts-retracts-no-premise-a-snapshot-cannot-name
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [bird penguin flies Tweety CxSnap]
      (let [rule (list 'set/forwardRule (list 'implies (list bird '?b) (list flies '?b)))
            snap [(list bird Tweety) (list penguin Tweety)]]
        (v/assert kb rule CxSnap)
        (v/assert kb (list 'exceptWhen (list penguin '?b) rule) CxSnap)
        (doseq [s snap] (v/assert kb s CxSnap))
        (is (= {:added 0 :removed 0 :edit nil} (v/replace-facts! kb CxSnap snap))
            "the exceptWhen meta-sentex is not a ground literal, so it is not retracted")
        (is (false? (v/ask? kb (list flies Tweety) CxSnap)))
        (is (= :shape (try (v/replace-facts! kb CxSnap [(list 'comment (sx/sentex-handle 1) "a note")])
                           nil
                           (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))
            "a fact naming a sentex by handle is refused")))))

(deftest replace-facts-raises-a-held-fact-to-a-stronger-requested-strength
  (tu/with-terms [p A CxSnap CxKid]
    (let [run (fn [write!]
                (tu/with-neutral-kb [kb tu/fresh]
                  (v/assert kb (list 'genlCx CxKid CxSnap) 'CxUniverse {:strength :monotonic})
                  (v/assert kb (list 'not (list p A)) CxKid)
                  (let [r (write! kb)]
                    [r (:strength (v/sentex kb (v/handle-of kb (list p A) CxSnap)))
                     (v/ask? kb (list 'not (list p A)) CxKid)])))
          [[r1 r2 r3] & replaced]
          (run (fn [kb]
                 [(v/replace-facts! kb CxSnap [(list p A)])
                  (select-keys (v/replace-facts! kb CxSnap [(list p A)] {:strength :monotonic})
                               [:added :removed])
                  (v/replace-facts! kb CxSnap [(list p A)])]))
          [_ & loaded] (run #(v/assert % (list p A) CxSnap {:strength :monotonic}))]
      (is (= {:added 1 :removed 0} r2) "the held :default fact is re-asserted :monotonic")
      (is (= {:added 0 :removed 0 :edit nil} r3) "a weaker request keeps the stored strength")
      (is (= [:monotonic false] loaded replaced)
          "the strength and the child context's denial agree with a KB told the snapshot")
      (is (= 1 (:added r1))))))

(deftest replace-facts-refuses-a-fact-stored-outside-the-context
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [ownerOf dog Rex Fido CxSnap CxElse]
      (v/assert kb (list 'forced_decontextualized_predicate ownerOf) 'CxUniverse {:strength :monotonic})
      (doseq [s [(list ownerOf Rex Fido) (list 'ist CxElse (list dog Rex))]]
        (is (= :shape (try (v/replace-facts! kb CxSnap [(list dog Fido) s])
                           nil
                           (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))
            (pr-str s)))
      (is (= [0 nil nil] [(v/count-in-context kb CxSnap) (v/handle-of kb (list ownerOf Rex Fido) CxSnap)
                          (v/handle-of kb (list dog Rex) CxElse)])
          "a refused snapshot writes nothing")
      (is (= {:added 1 :removed 0}
             (select-keys (v/replace-facts! kb CxSnap [(list 'ist CxSnap (list dog Rex))]) [:added :removed]))
          "an ist naming the context itself is the context's own fact"))))

(deftest replace-facts-refuses-a-fact-with-a-variable-and-never-retracts-one
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [says likes fatherOf grandfather_of Ann Bob CxSnap]
      (let [quoted    (list says Ann (list 'Quote (list likes '?x Bob)))
            schematic (list 'equals (list fatherOf (list fatherOf '?x)) (list grandfather_of '?x))]
        (doseq [s [quoted schematic]]
          (is (= :shape (try (v/replace-facts! kb CxSnap [s])
                             nil
                             (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))
              (pr-str s)))
        (is (zero? (v/count-in-context kb CxSnap)) "a refused snapshot writes nothing")
        (doseq [s [quoted schematic]] (v/assert kb s CxSnap))
        (is (= [{:added 0 :removed 0 :edit nil} 2]
               [(v/replace-facts! kb CxSnap []) (v/count-in-context kb CxSnap)])
            "a stored fact with a variable is outside the ground premises an empty snapshot replaces")))))

(deftest replace-facts-counts-a-symmetric-fact-s-two-spellings-as-one-added-row
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [nearTo A B CxSnap]
      (v/assert kb (list 'symmetric nearTo) 'CxUniverse {:strength :monotonic})
      (is (= [1 1] [(:added (v/replace-facts! kb CxSnap [(list nearTo A B) (list nearTo B A)]))
                    (v/count-in-context kb CxSnap)])))))

;; ---- the entry point refuses what the dry run reports ---------------------------

(deftest a-malformed-add-entry-is-refused-whole-not-applied-in-part
  ;; One fn (`add-entry-shape-problem`) is read by both entry points, so what `check-edit`
  ;; reports as `:shape` is what `edit` throws — a 4-element entry is never applied
  ;; with the junk silently dropped.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Muffet CxShape]
      (testing "a 4-element entry is :shape at both entry points, and nothing lands"
        (let [batch  {:add [[(list dog Muffet) CxShape {} :junk]]}
              before (v/sentex-count kb)]
          (is (= [:shape] (mapv :type (v/check-edit kb batch))))
          (let [e (is (thrown? clojure.lang.ExceptionInfo (v/edit! kb batch)))]
            (is (= :shape (:type (ex-data e)))))
          (is (= before (v/sentex-count kb)))
          (is (nil? (v/handle-of kb (list dog Muffet) CxShape))
              "the entry was refused whole, not applied minus the junk")))
      (testing "a non-sequential entry is :shape at both entry points, not a bare throw"
        (doseq [bad [42 {:sentence 1}]]
          (let [batch {:add [bad]}]
            (is (= [:shape] (mapv :type (v/check-edit kb batch))))
            (let [e (is (thrown? clojure.lang.ExceptionInfo (v/edit! kb batch)))]
              (is (= :shape (:type (ex-data e)))))))))))

(deftest a-batch-half-that-is-not-a-sequence-is-shape-at-every-entry-point
  ;; `{:add 5}` reaches every entry point's iteration, so unrefused it raises a bare
  ;; "Don't know how to create ISeq" out of `check-edit`, `edit` and `preview` alike —
  ;; over the daemon, a 500 with no `:type` to discriminate on.
  (tu/with-neutral-kb [kb tu/fresh]
    (doseq [batch [{:add 5} {:remove 5} {:add {:a 1}} {:remove #{7}}]]
      (testing (pr-str batch)
        (is (= [:shape] (mapv :type (v/check-edit kb batch))))
        (doseq [[nm entry-point] [["edit" #(v/edit! kb batch)]
                                  ["preview" #(v/preview kb batch)]]]
          (let [e (is (thrown? clojure.lang.ExceptionInfo (entry-point))
                      (str nm " refuses " (pr-str batch)))]
            (is (= :shape (:type (ex-data e))) (str nm " says :shape"))))))))

(deftest an-unknown-remove-handle-refuses-the-batch-before-anything-lands
  ;; `check-edit` flags the handle as `:unknown-handle`; an entry point that then quietly
  ;; folded it into zero counts would apply the adds first and leave a half-applied
  ;; batch behind a refusal the dry run had already named.  `retract!` standalone is
  ;; the deliberate contrast: retracting one absent handle is an ordinary zero-count
  ;; answer, not a batch.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Muffet CxHalf]
      (let [ghost 9999999
            batch {:add [[(list dog Muffet) CxHalf]] :remove [ghost]}]
        (is (nil? (v/sentex kb ghost)) "the handle names nothing stored")
        (testing "check-edit predicts the refusal"
          (is (some #(= :unknown-handle (:type %)) (v/check-edit kb batch))))
        (testing "edit refuses the whole batch with the same :type"
          (let [e (is (thrown? clojure.lang.ExceptionInfo (v/edit! kb batch)))]
            (is (= :unknown-handle (:type (ex-data e))))
            (is (= ghost (:handle (ex-data e))))))
        (testing "and the add half did not land — no half-applied batch"
          (is (nil? (v/handle-of kb (list dog Muffet) CxHalf))))
        (testing "retract! standalone keeps its zero-count answer"
          (is (= {:removed-sentexes 0 :removed-justifications 0}
                 (v/retract! kb ghost))))
        (testing "and a nil :remove entry stays nothing-to-remove"
          (is (= 0 (:removed-sentexes (:removed (v/edit! kb {:remove [nil]}))))))))))

;;; ── all-or-nothing ──────────────────────────────────────────────────────

(deftest a-refusal-check-edit-cannot-see-takes-the-whole-batch-back
  ;; The dry run checks each entry against the KB **as it stands**, so a batch whose
  ;; third entry closes a `genl` cycle with its *second* is admissible to `check-edit`
  ;; and refused by the engine two entries in.  That is the case a rollback exists for.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog cat Muffet Rex CxThe]
      (v/assert kb (list 'genlCx CxThe 'CxUniverse) 'CxUniverse)
      (let [sentences [(list dog Muffet) (list 'genl dog cat)
                       (list 'genl cat dog) (list dog Rex)]
            batch     {:add (mapv #(vector % CxThe) sentences)}
            before    {:count      (v/sentex-count kb)
                       :sentexes   (tu/sentex-ids kb)
                       :premises   (tu/premise-ids kb)
                       :justifs    (tu/justification-ids kb)
                       :contras    (v/contradictions kb)}]
        (testing "the dry run predicts nothing: every entry is fine on its own"
          (is (= [] (v/check-edit kb batch))))
        (let [e (is (thrown? clojure.lang.ExceptionInfo (v/edit! kb batch)))
              d (ex-data e)]
          (testing "the engine's own refusal comes back, saying where and that it was undone"
            (is (= :not-well-formed (:type d)) "the original ex-data is kept")
            (is (true? (:rolled-back d)))
            (is (= :add (:in d)))
            (is (= 2 (:index d)))
            (is (= (nth (:add batch) 2) (:entry d)))
            (is (some? (ex-cause e)) "with the original hung off it as the cause")))
        (testing "and the KB is exactly what it was — count, handle set, belief, dilemmas"
          (is (= (:count before) (v/sentex-count kb)))
          (is (= (:sentexes before) (tu/sentex-ids kb)))
          (is (= (:premises before) (tu/premise-ids kb)))
          (is (= (:justifs before) (tu/justification-ids kb)))
          (is (= (:contras before) (v/contradictions kb)))
          (doseq [sentence sentences]
            (is (nil? (v/handle-of kb sentence CxThe))
                (str "nothing is stored for " (pr-str sentence)))))
        (testing "the same batch without the entry that tripped lands whole"
          (let [ok    (into [] (keep-indexed #(when (not= 2 %1) %2)) (:add batch))
                added (:added (v/edit! kb {:add ok}))]
            (is (= 3 (count added)))
            (doseq [[sentence _] ok]
              (is (v/in? kb (v/handle-of kb sentence CxThe))
                  (str (pr-str sentence) " is believed")))))))))

(deftest a-batch-that-refuses-leaves-a-premise-it-named-for-removal-believed
  ;; Removes run after adds, so a batch refused on an add has not reached its removals —
  ;; and the rollback owes the premise, and everything derived from it, untouched.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog cat barks Muffet CxThe]
      (v/assert kb (list 'genlCx CxThe 'CxUniverse) 'CxUniverse)
      (v/assert-rule kb [(list dog '?x)] (list barks '?x) CxThe {:direction :forward})
      (let [h  (v/assert kb (list dog Muffet) CxThe)
            bh (v/handle-of kb (list barks Muffet) CxThe)]
        (is (v/in? kb bh) "the conclusion the removal would sweep is derived")
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/edit! kb {:add [[(list 'genl dog cat) CxThe]
                                        [(list 'genl cat dog) CxThe]]
                                  :remove [h]})))
        (testing "the removal was never made: the premise stands at its handle"
          (is (= h (v/handle-of kb (list dog Muffet) CxThe)))
          (is (v/in? kb h))
          (is (true? (v/premise? kb h))))
        (testing "and so does what it supported, at its own handle"
          (is (= bh (v/handle-of kb (list barks Muffet) CxThe)))
          (is (v/in? kb bh)))
        (testing "with neither add left behind"
          (is (nil? (v/handle-of kb (list 'genl dog cat) CxThe)))
          (is (nil? (v/handle-of kb (list 'genl cat dog) CxThe))))))))

(deftest a-strength-a-refused-batch-raised-goes-back-down
  ;; The audit's third case: a handle the batch did not create and did not merely
  ;; re-assert, but **re-classed**.  `mark-premise` resolves by content and keeps the
  ;; stronger class, which is right for an assertion and wrong for an undo.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog cat Muffet CxThe]
      (v/assert kb (list 'genlCx CxThe 'CxUniverse) 'CxUniverse)
      (let [h (v/assert kb (list dog Muffet) CxThe)]
        (is (= :default (v/defeat-class kb h)))
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/edit! kb {:add [[(list dog Muffet) CxThe {:strength :monotonic}]
                                        [(list 'genl dog cat) CxThe]
                                        [(list 'genl cat dog) CxThe]]})))
        (testing "the class the batch raised is back where the KB had it"
          (is (= :default (v/defeat-class kb h))))))))

;; ---- edit-records! and settle-record-edits! --------------------------------------

(defn- believed
  "Every believed record of `kb` as `[sentence context]`, handles resolved."
  [kb]
  (into #{}
        (comp (filter #(v/in? kb %))
              (map #(let [s (p/get-sentex (:records kb) %)]
                      (tu/handle-free kb [(sx/sentence-of s) (:context s)]))))
        (tu/sentex-ids kb)))

(defn- edit-both-ways
  "The believed records after `scenario` through `edit!` (each direction change a
  retraction and a re-assertion) and through `edit-records!` on a reopened KB without
  belief followed by `settle-record-edits!` with `settle-opts`, on two sequential fresh
  KBs.  `scenario` is `{:build (fn [kb]) :remove [[s ctx]] :direction [[[s ctx] bare d]]}`;
  its `:keeps` and `:entailing?`, read by the caller, are records `edit!` must leave
  believed and whether the row runs under the entailing argument-type reading."
  [{:keys [build remove direction]} settle-opts]
  (let [handles (fn [kb] (mapv (fn [[s c]] (v/handle-of kb s c)) remove))]
    [(tu/with-cleared-kb [kb tu/fresh]
       (build kb)
       (v/edit! kb {:remove (handles kb)})
       (doseq [[[s c] bare d] direction]
         (v/retract! kb (v/handle-of kb s c))
         (v/assert kb bare c {:direction d}))
       (believed kb))
     (tu/with-cleared-kb [kb tu/fresh]
       (build kb)
       (let [hs  (handles kb)
             ds  (into {} (map (fn [[[s c] _ d]] [(v/handle-of kb s c) d])) direction)
             kb2 (tu/test-kb)
             r   (v/edit-records! kb2 {:remove hs :direction ds})]
         (v/settle-record-edits! kb2 (assoc settle-opts :seeds (:seeds r)))
         (believed kb2)))]))

(deftest edit-records-then-settle-believes-what-edit-believes
  (tu/with-terms [p q r s t u w bird flies travels blocked parentOf animal dog needs wanted relativeOf childOf kinOf knows person A B Tweety Fido Rex Fred Mary CxThe CxWorld CxDogs CxRa CxRb CxRm]
    (let [rule (fn [ante conseq] (list 'implies ante conseq))
          ;; a firing names one route for each reachability it rests on, so removing the
          ;; edge it named deletes the justification while the second route still
          ;; licenses the firing; `route-first?` puts the second route before the firing
          cx-route (fn [route-first?]
                     (fn [kb]
                       (let [route #(do (v/assert kb (list 'genlCx CxRm CxRa) 'CxUniverse)
                                        (v/assert kb (list 'genlCx CxRb CxRm) 'CxUniverse))]
                         (v/assert kb (list 'genlCx CxRa 'CxUniverse) 'CxUniverse)
                         (v/assert kb (list 'genlCx CxRb CxRa) 'CxUniverse)
                         (when route-first? (route))
                         (v/assert-rule kb [(list p '?x)] (list q '?x) CxRa {:direction :forward})
                         (v/assert kb (list p A) CxRb)
                         (when-not route-first? (route)))))
          genl-route (fn [route-first?]
                       (fn [kb]
                         (let [route #(do (v/assert kb (list 'genl childOf kinOf) 'CxUniverse)
                                          (v/assert kb (list 'genl kinOf relativeOf) 'CxUniverse))]
                           (v/assert kb (list 'genlCx CxThe 'CxUniverse) 'CxUniverse)
                           (v/assert-rule kb [(list relativeOf '?x '?y)] (list knows '?x '?y) CxThe
                                          {:direction :forward})
                           (v/assert kb (list 'genl childOf relativeOf) 'CxUniverse)
                           (when route-first? (route))
                           (v/assert kb (list childOf Fido Rex) CxThe)
                           (when-not route-first? (route)))))
          ;; `(animal Fred)` is minted off `(parentOf Fred Mary)` and withheld while
          ;; `(dog Fred)` says it more specifically (docs/argtypes.md)
          withheld (fn [kb]
                     (doseq [c [CxWorld CxDogs]]
                       (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
                     (v/assert kb (list 'genlCx CxWorld CxDogs) 'CxUniverse)
                     (v/assert kb (list 'genl animal 'thing) 'CxUniverse)
                     (v/assert kb (list 'genl dog animal) 'CxUniverse)
                     (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
                     (v/assert kb (list dog Fred) CxDogs)
                     (v/assert kb (list parentOf Fred Mary) CxWorld))
          rows
          {"a removed premise takes its forward chain with it"
           {:build (fn [kb]
                     (v/assert-rule kb [(list p '?x)] (list q '?x) CxThe {:direction :forward})
                     (v/assert-rule kb [(list q '?x)] (list r '?x) CxThe {:direction :forward})
                     (v/assert kb (list p A) CxThe)
                     (v/assert kb (list p B) CxThe))
            :remove [[(list p A) CxThe]]}

           "a removed defeater lets a default and what it fires come back"
           {:build (fn [kb]
                     (v/assert kb (list 'set/defaultRule (rule (list bird '?x) (list flies '?x))) CxThe)
                     (v/assert-rule kb [(list flies '?x)] (list travels '?x) CxThe {:direction :forward})
                     (v/assert kb (list bird Tweety) CxThe)
                     (v/assert kb (list 'not (list flies Tweety)) CxThe {:strength :monotonic}))
            :remove [[(list 'not (list flies Tweety)) CxThe]]}

           "a removed fact a negation-as-failure antecedent read releases the firing"
           {:build (fn [kb]
                     (v/assert-rule kb [(list p '?x) (list 'unknown (list blocked '?x))] (list u '?x)
                                    CxThe {:direction :forward})
                     (v/assert kb (list p A) CxThe)
                     (v/assert kb (list blocked A) CxThe))
            :remove [[(list blocked A) CxThe]]}

           "a removed declaration releases a held fact, and the firing it holds back"
           {:build (fn [kb]
                     (v/assert kb (list 'genl dog 'thing) 'CxUniverse)
                     (v/assert kb (list 'unary_predicate needs) 'CxUniverse)
                     (v/assert-rule kb [(list needs '?x)] (list wanted '?x) CxThe {:direction :forward})
                     (v/assert kb (list needs 5) CxThe)
                     (v/assert kb (list 'arg needs 1 dog) 'CxUniverse))
            :remove [[(list 'arg needs 1 dog) 'CxUniverse]]}

           "a fact defeated on arrival is chained once the removal revives it"
           {:build (fn [kb]
                     (v/assert-rule kb [(list q '?x)] (list w '?x) CxThe {:direction :forward})
                     (v/assert kb (list 'not (list q A)) CxThe {:strength :monotonic})
                     (v/assert kb (list q A) CxThe))
            :remove [[(list 'not (list q A)) CxThe]]}

           "a removed membership releases the general mint it withheld"
           {:build withheld :remove [[(list dog Fred) CxDogs]]}

           "a removed genl edge releases the general mint the membership withheld"
           {:build withheld :remove [[(list 'genl dog animal) 'CxUniverse]]}

           "a removed genl route leaves the mint another route derives"
           {:build (fn [kb]
                     (v/assert kb (list 'arg relativeOf 1 person) 'CxUniverse)
                     (v/assert kb (list 'genl childOf relativeOf) 'CxUniverse)
                     (v/assert kb (list 'genl childOf kinOf) 'CxUniverse)
                     (v/assert kb (list 'genl kinOf relativeOf) 'CxUniverse)
                     (v/assert kb (list childOf Fido Rex) 'CxUniverse))
            :remove [[(list 'genl childOf relativeOf) 'CxUniverse]]
            :keeps  [[(list person Fido) 'CxUniverse]] :entailing? true}

           "a removed genlCx edge leaves the firing a later second route licenses"
           {:build (cx-route false) :remove [[(list 'genlCx CxRb CxRa) 'CxUniverse]]
            :keeps [[(list q A) CxRb]]}

           "a removed genlCx edge leaves the firing an earlier second route licenses"
           {:build (cx-route true) :remove [[(list 'genlCx CxRb CxRa) 'CxUniverse]]
            :keeps [[(list q A) CxRb]]}

           "a removed genl edge leaves the firing a later second route licenses"
           {:build (genl-route false) :remove [[(list 'genl childOf relativeOf) 'CxUniverse]]
            :keeps [[(list knows Fido Rex) CxThe]]}

           "a removed genl edge leaves the firing an earlier second route licenses"
           {:build (genl-route true) :remove [[(list 'genl childOf relativeOf) 'CxUniverse]]
            :keeps [[(list knows Fido Rex) CxThe]]}

           "a removed premise that a firing also concludes stays, derived"
           {:build (fn [kb]
                     (v/assert-rule kb [(list p '?x)] (list q '?x) CxThe {:direction :forward})
                     (v/assert kb (list p A) CxThe)
                     (v/assert kb (list q A) CxThe))
            :remove [[(list q A) CxThe]]}

           "a removed argument declaration takes its type mint with it"
           {:build (fn [kb]
                     (v/assert kb (list 'arg parentOf 1 animal) CxThe)
                     (v/assert kb (list parentOf Fido Rex) CxThe))
            :remove [[(list 'arg parentOf 1 animal) CxThe]]}

           "a rule taken off forward takes its firings with it"
           {:build (fn [kb]
                     (v/assert-rule kb [(list p '?x)] (list s '?x) CxThe {:direction :forward})
                     (v/assert kb (list p A) CxThe))
            :direction [[[(rule (list p '?x) (list s '?x)) CxThe] (rule (list p '?x) (list s '?x)) :backward]]}

           "a rule put on forward fires over the stored facts"
           {:build (fn [kb]
                     (v/assert-rule kb [(list p '?x)] (list t '?x) CxThe {:direction :backward})
                     (v/assert kb (list p A) CxThe))
            :direction [[[(rule (list p '?x) (list t '?x)) CxThe] (rule (list p '?x) (list t '?x)) :forward]]}}]
      (doseq [[label row] rows]
        (testing label
          ;; an `:entailing?` row keeps an argument-type mint, which only the entailing
          ;; reading makes
          (let [[via-edit via-records] (if (:entailing? row)
                                         (tu/with-entailing (edit-both-ways row {}))
                                         (edit-both-ways row {}))]
            (doseq [k (:keeps row)]
              (is (contains? via-edit k) (str "the row exercises " (pr-str k))))
            (is (= via-edit via-records)
                (pr-str {:only-edit (remove via-records via-edit)
                         :only-records (remove via-edit via-records)}))))))))

(deftest edit-records-refuses-before-writing
  (tu/with-terms [p q w A CxThe]
    (let [ex-type (fn [f] (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))]
      (tu/with-cleared-kb [kb tu/fresh]
        (let [fa (v/assert kb (list p A) CxThe)
              fq (v/assert kb (list q A) CxThe)
              ex (v/assert kb (list 'except (list 'sentexHandle fq)) CxThe)
              rb (v/assert kb (list 'implies (list p '?x) (list q '?x)) CxThe)
              rl (v/assert kb (list 'set/lazyForwardRule (list 'implies (list q '?x) (list w '?x))) CxThe)
              _  (v/assert kb (list 'arg p 1 w) CxThe)
              mr (v/handle-of kb (kv/mint-rules 'arg) 'CxUniverse)]
          (testing "a KB with belief"
            (is (= :belief-built (ex-type #(v/edit-records! kb {:remove [fa]})))))
          (let [kb2 (tu/test-kb)]
            (testing "an except removal, and the batch's other removal stays unwritten"
              (is (= :record-edit-unsupported (ex-type #(v/edit-records! kb2 {:remove [fa ex]}))))
              (is (some? (p/get-sentex (:records kb2) fa))))
            (testing "a direction on a fact, a bad direction, an absent handle"
              (is (= :unknown-option (ex-type #(v/edit-records! kb2 {:direction {fa :forward}}))))
              (is (= :unknown-option (ex-type #(v/edit-records! kb2 {:direction {fa :sideways}}))))
              (is (= :unknown-handle (ex-type #(v/edit-records! kb2 {:direction {99999 :forward}})))))
            (testing "a mint rule's removal and direction change"
              (is (= :mint-rule (ex-type #(v/edit-records! kb2 {:remove [mr]}))))
              (is (= :mint-rule (ex-type #(v/edit-records! kb2 {:direction {mr :backward}})))))
            (testing "a direction onto or off lazy-forward"
              (is (= :unknown-option (ex-type #(v/edit-records! kb2 {:direction {rb :lazy-forward}}))))
              (is (= :unknown-option (ex-type #(v/edit-records! kb2 {:direction {rl :backward}})))))
            (testing "the same batch run again completes it and counts what is gone"
              (is (= 1 (:removed (v/edit-records! kb2 {:remove [fa]}))))
              (is (= {:removed 0 :absent 1}
                     (select-keys (v/edit-records! kb2 {:remove [fa]}) [:removed :absent]))))
            (testing "a nil removal, as `handle-of` answers on an index not built, counts as absent"
              (is (= {:removed 0 :absent 1}
                     (select-keys (v/edit-records! kb2 {:remove [nil]}) [:removed :absent]))))))))))

(defn- record-digest
  "Every stored record of `kb` by content, `{[sentence context] [record-strength
  premise-strength believed? justifications]}`, each justification its informant and its
  antecedents by content, so two KBs whose handles differ compare: a firing names its rule
  and a mint its mint rule."
  [kb]
  (let [recs (:records kb)
        tms  (reasoning/tms kb)
        ct   #(let [s (p/get-sentex recs %)] [(sx/sentence-of s) (:context s)])]
    (into {}
          (for [h (p/sentex-ids recs)
                :let [s (p/get-sentex recs h)]]
            [(ct h)
             [(:strength s) (jtms/premise-strength tms h) (v/in? kb h)
              (into #{} (for [j (jtms/supports tms h)
                              :let [j (jtms/justification tms j)]]
                          [(if (integer? (:informant j)) (ct (:informant j)) (:informant j))
                           (into #{} (map ct) (:antecedents j))]))]]))))

(defn- add-both-ways
  "`record-digest` after `batch` through `edit!`, and through `edit-records!` on a
  reopened KB without belief followed by `settle-record-edits!` with `settle-opts`, each
  over a fresh KB `build` wrote.  `batch` is `{:add [[s ctx]] :remove [[s ctx]]}`, its
  removals named by content."
  [build {:keys [add remove]} settle-opts]
  (let [handles (fn [kb] (mapv (fn [[s c]] (v/handle-of kb s c)) remove))]
    [(tu/with-cleared-kb [kb tu/fresh]
       (build kb)
       (v/edit! kb {:add add :remove (handles kb)})
       (record-digest kb))
     (tu/with-cleared-kb [kb tu/fresh]
       (build kb)
       (let [hs  (handles kb)
             kb2 (tu/test-kb)
             r   (v/edit-records! kb2 {:add add :remove hs})]
         (v/settle-record-edits! kb2 (assoc settle-opts :seeds (:seeds r)))
         (record-digest kb2)))]))

(defn- lexicon
  "A KB the additions below land in: a context lattice, a type tree under a disjointness,
  two memberships, an argument declaration on `sense` and one on `animal`, a lifted
  `sense`, forward rules over a membership, over `sense` and over each declared type, and a
  rule that derives a `sense` fact."
  [kb]
  (v/assert kb '(genlCx CxWorld CxUniverse) 'CxUniverse)
  (v/assert kb '(genlCx CxData CxWorld) 'CxUniverse)
  (v/assert kb '(genl animal thing) 'CxWorld)
  (v/assert kb '(genl plant thing) 'CxWorld)
  (v/assert kb '(disjoint animal plant) 'CxWorld)
  (v/assert kb '(dog Rex) 'CxData)
  (v/assert kb '(puppy Bo) 'CxData)
  (v/assert kb '(arg sense 1 lexeme_t) 'CxWorld)
  (v/assert kb '(arg animal 1 organism) 'CxWorld)
  (v/assert kb '(decontextualized_predicate sense) 'CxUniverse)
  (v/assert-rule kb ['(animal ?x)] '(breathes ?x) 'CxWorld {:direction :forward})
  (v/assert-rule kb ['(organism ?x)] '(alive ?x) 'CxWorld {:direction :forward})
  (v/assert-rule kb ['(sense ?l ?m)] '(sensed_t ?l) 'CxWorld {:direction :forward})
  (v/assert-rule kb ['(lexeme_t ?l)] '(word_t ?l) 'CxWorld {:direction :forward})
  (v/assert-rule kb ['(alias ?l ?m)] '(sense ?l ?m) 'CxWorld {:direction :forward})
  (v/assert kb '(alias lex/hound dog) 'CxWorld)
  (v/assert kb '(alias lex/cur dog) 'CxWorld))

(def ^:private lexicon-batch
  "New edges in two contexts, a new and a derived `sense` fact, a `comment`, a stored
  premise, and a removal whose firing concluded a `sense` fact."
  {:add    '[[(genl dog canine) CxWorld]
             [(genl canine animal) CxWorld]
             [(genl puppy dog) CxData]
             [(sense lex/mutt dog) CxWorld]
             [(sense lex/hound dog) CxWorld]
             [(comment canine "A dog-like animal.") CxWorld]
             [(genl animal thing) CxWorld]]
   :remove '[[(alias lex/cur dog) CxWorld]]})

(deftest edit-records-additions-settle-to-what-edit-writes
  (doseq [[reading bind] [["subsumed mints pruned" true] ["mints kept" false]]
          settle-opts    [{} {:arg-types? false}]]
    (testing (str reading ", " (pr-str settle-opts))
      (binding [argument/*assertive-arg-types?* true
                checks/*prune-subsumed-mints?*  bind]
        (let [[via-edit via-records] (add-both-ways lexicon lexicon-batch settle-opts)]
          (doseq [k '[[(breathes Rex) CxData] [(breathes Bo) CxData]
                      [(alive Rex) CxData] [(word_t lex/mutt) CxWorld]
                      [(sensed_t lex/mutt) CxWorld] [(sense lex/mutt dog) CxUniverse]]]
            (is (true? (get-in via-edit [k 2])) (str "the batch derives " (pr-str k))))
          (is (= :default (get-in via-edit ['[(sense lex/hound dog) CxWorld] 0]))
              "the derived sense fact gains the premise mark")
          (is (nil? (get via-edit '[(sensed_t lex/cur) CxWorld])) "the removal takes its chain")
          (is (= via-edit via-records)
              (pr-str (into (sorted-map)
                            (keep (fn [k]
                                    (when (not= (get via-edit k) (get via-records k))
                                      [(pr-str k) {:edit (get via-edit k)
                                                   :records (get via-records k)}])))
                            (into (set (keys via-edit)) (keys via-records))))))))))

(deftest edit-records-additions-refuse-before-writing
  (let [ex-type (fn [f] (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))]
    (tu/with-cleared-kb [kb tu/fresh]
      (lexicon kb)
      (v/assert kb '(symmetric relatedTo) 'CxWorld)
      (v/assert-inert kb '(comment cat "an inert note") 'CxWorld)
      (testing "a KB with belief"
        (is (= :belief-built (ex-type #(v/edit-records! kb '{:add [[(genl dog canine) CxWorld]]})))))
      (let [kb2   (tu/test-kb)
            ids   #(set (p/sentex-ids (:records kb2)))
            n0    (ids)
            good  '[(genl dog canine) CxWorld]
            refused (fn [entry] (ex-type #(v/edit-records! kb2 {:add [good entry]})))]
        (doseq [[want entry] [[:record-edit-unsupported '[(isa Rex dog) CxWorld]]
                              [:record-edit-unsupported '[(comment (NameFn dog) "a dog") CxWorld]]
                              [:record-edit-unsupported '[(genl parentOf relativeOf) CxWorld]]
                              [:record-edit-unsupported '[(genl dog canine) CxNowhere]]
                              [:record-edit-unsupported '[(comment cat "an inert note") CxWorld]]
                              [:not-ground '[(genl ?x animal) CxWorld]]
                              [:naming '[(genl dog canine) World]]
                              [:not-well-formed '[(genl dog dog) CxWorld]]
                              [:not-well-formed '[(genl Rex animal) CxWorld]]
                              [:shape '[(genl dog canine)]]
                              [:shape '["genl dog canine" CxWorld]]
                              [:shape '[(genl dog canine) CxEverything]]]]
          (testing (pr-str entry)
            (is (= want (refused entry)))))
        (testing "a batch half that is not a sequence"
          (is (= :shape (ex-type #(v/edit-records! kb2 {:add {:a 1}})))))
        (testing "nothing the refused batches named was written"
          (is (= n0 (ids))))
        (testing "an index never built"
          (kbi/note-hazards! kb2 {:no-index true})
          (is (= :unrecovered-kb (ex-type #(v/edit-records! kb2 {:add [good]}))))
          (kbi/note-hazards! kb2 {:no-index false}))))
    (testing "a mark the store holds that moves where assert stores the fact"
      (tu/with-cleared-kb [kb tu/fresh]
        (lexicon kb)
        (v/assert kb '(symmetric sense) 'CxUniverse)
        (v/assert kb '(forced_decontextualized_predicate comment) 'CxUniverse)
        (let [kb2 (tu/test-kb)]
          (is (= :record-edit-unsupported
                 (ex-type #(v/edit-records! kb2 '{:add [[(sense lex/mutt dog) CxWorld]]}))))
          (is (= :record-edit-unsupported
                 (ex-type #(v/edit-records! kb2 '{:add [[(comment dog "a dog") CxWorld]]})))))))))

(deftest edit-records-additions-count-what-the-store-holds
  (tu/with-cleared-kb [kb tu/fresh]
    (lexicon kb)
    (let [kb2     (tu/test-kb)
          recs    (:records kb2)
          ids     #(set (p/sentex-ids recs))
          derived (v/handle-of kb2 '(sense lex/hound dog) 'CxWorld)
          premise (v/handle-of kb2 '(genl animal thing) 'CxWorld)
          n0      (ids)]
      (is (nil? (:strength (p/get-sentex recs derived))) "the sense fact is derived")
      (testing "a stored premise is present, and nothing is written for it"
        (is (= {:added 0 :present 1 :seeds []}
               (select-keys (v/edit-records! kb2 '{:add [[(genl animal thing) CxWorld]]})
                            [:added :present :seeds])))
        (is (= n0 (ids)))
        (is (= :default (:strength (p/get-sentex recs premise)))))
      (testing "a derived record gains the premise mark, is present, and is a seed"
        (is (= {:added 0 :present 1 :seeds [derived]}
               (select-keys (v/edit-records! kb2 '{:add [[(sense lex/hound dog) CxWorld]]})
                            [:added :present :seeds])))
        (is (= n0 (ids)))
        (is (= :default (:strength (p/get-sentex recs derived))))
        (is (contains? (p/premise-ids recs) derived)))
      (testing "a sentence twice in one batch is one record"
        (let [r (v/edit-records! kb2 '{:add [[(genl dog canine) CxWorld] [(genl dog canine) CxWorld]]})]
          (is (= [1 1] [(:added r) (:present r)]))
          (is (= 1 (count (:seeds r))))
          (is (= (inc (count n0)) (count (ids))))))
      (testing "the batch run again writes nothing and counts each as present"
        (is (= {:added 0 :present 2}
               (select-keys (v/edit-records! kb2 '{:add [[(genl dog canine) CxWorld]
                                                         [(sense lex/hound dog) CxWorld]]})
                            [:added :present]))))
      (testing "the settle believes them as premises"
        (let [edge (v/handle-of kb2 '(genl dog canine) 'CxWorld)]
          (v/settle-record-edits! kb2 {:seeds [derived edge]})
          (is (every? #(and (v/premise? kb2 %) (v/in? kb2 %)) [derived edge])))))))

(deftest edit-records-additions-write-each-fact-once-and-read-no-belief
  (doseq [n [16 128]]
    (testing (str n " facts are " n " records and premise marks and no justification, read"
                  " with the KB's reasoning state unreadable")
      (tu/with-cleared-kb [kb tu/fresh]
        (lexicon kb)
        (let [kb2   (tu/test-kb)
              recs  (:records kb2)
              count-of (fn [] [(count (p/sentex-ids recs)) (count (p/premise-ids recs))
                               (count (p/justification-ids recs))])
              [s0 p0 j0] (count-of)
              batch {:add (into [] (mapcat (fn [i]
                                             (let [t (symbol (str "breed_" i))]
                                               [[(list 'genl t 'dog) 'CxWorld]
                                                [(list 'sense (symbol "lex" (str "breed_" i)) t) 'CxWorld]])))
                                (range (quot n 2)))}
              blind (assoc kb2 :reasoning (reify clojure.lang.IDeref
                                            (deref [_] (throw (ex-info "belief read" {:type ::belief-read})))))
              r     (v/edit-records! blind batch)]
          (is (= n (:added r) (count (:seeds r))))
          (is (= [(+ s0 n) (+ p0 n) j0] (count-of))))))))
