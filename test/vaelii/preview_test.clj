;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.preview-test
  "`preview`: what a batch would do to the KB, without leaving it done.

  The property everything else rests on is that a preview writes nothing it cannot
  take back **at the same handles**, so almost every test here pairs an assertion
  about the answer with a before/after comparison of `content` — the live sentex and
  justification sets.  That is the same thing the neutral fixture checks at teardown,
  but a preview is supposed to be neutral *immediately*, not after a retraction sweep,
  and a test that only leaned on the fixture would pass on a preview that stored
  everything and let the teardown clean up.

  House rules as everywhere: gensym'd temporaries via `tu/with-terms`, engine
  vocabulary (`genl`, `disjoint`, `exceptWhen`, `set/defaultRule`, contexts) literal."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- content
  "The KB's live records, as the pair a preview must not move."
  [kb]
  [(tu/sentex-ids kb) (tu/justification-ids kb)])

(defn- sentences [entries] (mapv :sentence entries))

(defn- except-rule [exception antes conseq]
  (list 'exceptWhen exception (list 'set/defaultRule (vr/rule-sentence antes conseq))))

;; ---- 1. the property everything rests on ---------------------------------

(tu/deftest-kb a-preview-leaves-the-kb-byte-identical
  (tu/with-terms [dog friendly Rex StoryContext]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list friendly '?x)) StoryContext)
    (let [before (content kb)
          _      (v/preview kb {:add [[(list dog Rex) StoryContext]]})]
      (testing "same live sentexes and justifications, at the same handles"
        (is (= before (content kb))))
      (testing "and nothing the batch would have stored is findable"
        (is (nil? (v/handle-of kb (list dog Rex) StoryContext)))
        (is (nil? (v/handle-of kb (list friendly Rex) StoryContext)))))))

;; ---- 2. what a batch would derive ----------------------------------------

(tu/deftest-kb a-batch-that-derives-reports-what-it-derives
  (tu/with-terms [dog friendly Rex StoryContext]
    (let [rh     (v/assert kb (vr/rule-sentence [(list dog '?x)] (list friendly '?x))
                           StoryContext)
          before (content kb)
          r      (v/preview kb {:add [[(list dog Rex) StoryContext]]})]
      (testing "the premise and its consequence both come back"
        (is (= [(list dog Rex) (list friendly Rex)] (sentences (:believed-added r)))))
      (testing "nothing is reported removed, refused, or dropped"
        (is (empty? (:believed-removed r)))
        (is (empty? (:refused r)))
        (is (empty? (:violations r)))
        (is (false? (:bounded? r))))
      (testing "the derived line carries the justification that made it"
        (let [j (:justification (second (:believed-added r)))]
          (is (= rh (:informant j)))
          (is (= (v/readable-sentence (v/sentex kb rh)) (:rule j)))
          (is (= [(list dog Rex)] (:antecedents j)))))
      (testing "the asserted line is a premise and needs no justification"
        (is (true? (:premise? (first (:believed-added r)))))
        (is (nil? (:justification (first (:believed-added r))))))
      (is (= before (content kb))))))

(tu/deftest-kb content-the-batch-would-create-is-reported-without-a-handle
  (tu/with-terms [dog Rex StoryContext]
    (let [r (v/preview kb {:add [[(list dog Rex) StoryContext]]})]
      (testing "a handle that no longer names anything is worse than none"
        (is (nil? (:handle (first (:believed-added r)))))))))

;; ---- 3. what a batch would take away -------------------------------------

(tu/deftest-kb a-batch-that-defeats-an-existing-belief-reports-the-removal
  (tu/with-terms [flies Tweety StoryContext]
    (let [h      (v/assert kb (list flies Tweety) StoryContext)
          before (content kb)
          r      (v/preview kb {:add [[(list 'not (list flies Tweety)) StoryContext
                                       {:strength :monotonic}]]})]
      (testing "the defeated belief is named, with its handle — it is still stored"
        (is (= [(list flies Tweety)] (sentences (:believed-removed r))))
        (is (= h (:handle (first (:believed-removed r)))))
        (is (= :defeated (:reason (first (:believed-removed r))))))
      (testing "and the negation is what arrived"
        (is (= [(list 'not (list flies Tweety))] (sentences (:believed-added r)))))
      (testing "belief is unchanged afterwards — the defeat was hypothetical"
        (is (true? (v/in? kb h))))
      (is (= before (content kb))))))

(tu/deftest-kb previewing-a-removal-reports-what-loses-its-support
  (tu/with-terms [dog friendly Rex StoryContext]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list friendly '?x)) StoryContext)
    (let [h      (v/assert kb (list dog Rex) StoryContext)
          ch     (v/handle-of kb (list friendly Rex) StoryContext)
          before (content kb)
          r      (v/preview kb {:remove [h]})]
      (testing "the premise and everything solely resting on it"
        (is (= #{(list dog Rex) (list friendly Rex)} (set (sentences (:believed-removed r)))))
        (is (= #{h ch} (set (map :handle (:believed-removed r)))))
        (is (every? #{:unsupported} (map :reason (:believed-removed r)))))
      (testing "both are believed again afterwards, at the same handles"
        (is (true? (v/in? kb h)))
        (is (true? (v/in? kb ch))))
      (testing "a removal is previewed by suspending the premise, never by deleting"
        (is (= before (content kb)))))))

(tu/deftest-kb a-removal-with-another-witness-is-not-reported-removed
  (tu/with-terms [dog canine friendly Rex StoryContext]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list friendly '?x)) StoryContext)
    (v/assert kb (vr/rule-sentence [(list canine '?x)] (list friendly '?x)) StoryContext)
    (v/assert kb (list dog Rex) StoryContext)
    (let [h      (v/assert kb (list canine Rex) StoryContext)
          before (content kb)
          r      (v/preview kb {:remove [h]})]
      (testing "the conclusion keeps its other derivation, so only the premise goes"
        (is (= [(list canine Rex)] (sentences (:believed-removed r)))))
      (is (= before (content kb))))))

;; ---- 4. exceptions, in both directions -----------------------------------
;; The case a naive implementation gets wrong twice over: blocking a conclusion
;; *deletes* it, and reviving one *re-derives* it at a fresh handle.  A preview has
;; to answer both without either happening for real.

(tu/deftest-kb previewing-the-fact-that-triggers-an-exception-reports-the-block
  (tu/with-terms [bird penguin flies Opus StoryContext]
    (v/assert kb (except-rule (list penguin '?b) [(list bird '?b)] (list flies '?b))
              StoryContext)
    (v/assert kb (list bird Opus) StoryContext)
    (let [ch     (v/handle-of kb (list flies Opus) StoryContext)
          before (content kb)
          r      (v/preview kb {:add [[(list penguin Opus) StoryContext]]})]
      (testing "the conclusion the exception would block"
        (is (= [(list flies Opus)] (sentences (:believed-removed r))))
        (is (= ch (:handle (first (:believed-removed r))))))
      (testing "and it is still there, at the same handle, still believed"
        (is (= ch (v/handle-of kb (list flies Opus) StoryContext)))
        (is (true? (v/in? kb ch))))
      (testing "the sweep is suppressed for the preview, so nothing was deleted"
        (is (= before (content kb)))))))

(tu/deftest-kb previewing-a-removal-that-releases-an-exception-reports-the-revival
  (tu/with-terms [bird penguin flies Opus StoryContext]
    (v/assert kb (except-rule (list penguin '?b) [(list bird '?b)] (list flies '?b))
              StoryContext)
    (v/assert kb (list bird Opus) StoryContext)
    (let [ph     (v/assert kb (list penguin Opus) StoryContext)
          _      (is (empty? (v/sentexes-matching kb (list flies Opus) StoryContext))
                     "the exception holds, so there is no conclusion to start from")
          before (content kb)
          r      (v/preview kb {:remove [ph]})]
      (testing "removing the blocker would derive the conclusion again"
        (is (contains? (set (sentences (:believed-added r))) (list flies Opus))))
      (testing "the revived line has no handle — a re-derivation mints a fresh one"
        (is (nil? (:handle (first (filter #(= (list flies Opus) (:sentence %))
                                          (:believed-added r)))))))
      (testing "and the rollback collects it: the exception blocks again"
        (is (empty? (v/sentexes-matching kb (list flies Opus) StoryContext)))
        (is (= before (content kb)))))))

;; ---- 5. the derivation path's own refusals -------------------------------

(tu/deftest-kb a-conclusion-the-derivation-path-would-drop-is-reported-as-a-violation
  ;; an `argIsa` conviction has no opposing sentex to weigh against, so the derivation
  ;; path drops it — and a preview says so before the write happens
  (tu/with-terms [person rock parentOf looksLike Boulder Muffet StoryContext]
    (v/assert kb (list 'genl person 'thing) StoryContext)
    (v/assert kb (list 'genl rock 'thing) StoryContext)
    (v/assert kb (list 'argIsa parentOf 1 person) StoryContext)
    (v/assert kb (list rock Boulder) StoryContext)
    (v/assert kb (vr/rule-sentence [(list looksLike '?x)] (list parentOf '?x Muffet)) StoryContext)
    (let [before (content kb)
          r      (v/preview kb {:add [[(list looksLike Boulder) StoryContext]]})]
      (testing "the drop is reported where a real run would report it"
        (is (= [:arg-type] (mapv :violation (:violations r))))
        (is (= [(list parentOf Boulder Muffet)] (mapv :sentence (:violations r)))))
      (testing "only the admissible half of the batch is believed"
        (is (= [(list looksLike Boulder)] (sentences (:believed-added r)))))
      (testing "the KB's own ledger is left as it was found"
        (is (empty? (v/violations kb))))
      (is (= before (content kb))))))

(tu/deftest-kb a-conclusion-the-derivation-path-would-arbitrate-is-previewed-as-a-contradiction
  ;; the counterpart: a disjointness clash names an opposing sentex, so the firing is
  ;; placed and `settle` arbitrates it — and what a reviewer needs to see before the
  ;; commit is the *dilemma* it would open, not a drop that will not happen
  (tu/with-terms [fish mammal swims Willy StoryContext]
    (v/assert kb (list 'disjoint fish mammal) StoryContext)
    (v/assert kb (vr/rule-sentence [(list swims '?x)] (list fish '?x)) StoryContext)
    (v/assert kb (list mammal Willy) StoryContext)
    (let [before (content kb)
          r      (v/preview kb {:add [[(list swims Willy) StoryContext]]})]
      (testing "nothing is dropped — the conclusion is admissible, it is merely contested"
        (is (empty? (:violations r))))
      (testing "both the trigger and the contested conclusion would be believed"
        (is (= #{(list swims Willy) (list fish Willy)}
               (set (sentences (:believed-added r))))))
      (testing "and the contradiction it would open is what the reviewer is shown"
        (is (= 1 (count (:contradictions r)))))
      (is (= before (content kb))))))

;; ---- 6. refusals -------------------------------------------------------

(tu/deftest-kb a-refused-line-is-reported-and-the-rest-of-the-batch-is-previewed
  (tu/with-terms [dog Rex StoryContext]
    (let [before (content kb)
          r      (v/preview kb {:add [['(lives_in ?x ?y) StoryContext]
                                      [(list dog Rex) StoryContext]]})]
      (testing "the bad line is named by position, in check-edit's shape"
        (is (= [[:add 0 :naming]] (mapv (juxt :in :index :type) (:refused r)))))
      (testing "the good line is still previewed"
        (is (= [(list dog Rex)] (sentences (:believed-added r)))))
      (is (= before (content kb))))))

(tu/deftest-kb an-unknown-handle-in-remove-is-refused-not-ignored
  (let [before (content kb)
        r      (v/preview kb {:remove [999999]})]
    (is (= [[:remove 0 :unknown-handle]] (mapv (juxt :in :index :type) (:refused r))))
    (is (empty? (:believed-removed r)))
    (is (= before (content kb)))))

;; ---- 7. re-asserting what is already there -------------------------------
;; The leak a rollback-by-handle misses: `assert` on a stored sentex finds it and
;; marks it a premise, so a preview that only retracted what it *created* would
;; leave a derived datum standing as an asserted one.

(tu/deftest-kb previewing-a-sentence-the-kb-already-derives-adds-nothing-and-marks-nothing
  (tu/with-terms [dog friendly Rex StoryContext]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list friendly '?x)) StoryContext)
    (v/assert kb (list dog Rex) StoryContext)
    (let [ch     (v/handle-of kb (list friendly Rex) StoryContext)
          before (content kb)
          r      (v/preview kb {:add [[(list friendly Rex) StoryContext]]})]
      (testing "it is already believed, so the diff is empty"
        (is (empty? (:believed-added r)))
        (is (empty? (:believed-removed r))))
      (testing "and it is a derived datum again, not a premise"
        (is (false? (v/premise? kb ch))))
      (is (= before (content kb))))))

(tu/deftest-kb previewing-a-premise-the-kb-already-holds-restores-its-strength
  (tu/with-terms [dog Rex StoryContext]
    (let [h      (v/assert kb (list dog Rex) StoryContext {:strength :monotonic})
          before (content kb)]
      (v/preview kb {:add [[(list dog Rex) StoryContext {:strength :default}]]})
      (testing "the weaker restatement does not survive the preview"
        (is (true? (v/premise? kb h)))
        (is (= :monotonic (v/defeat-class kb h))))
      (is (= before (content kb))))))

;; ---- 8. bounds ---------------------------------------------------------

(tu/deftest-kb max-results-caps-each-half-of-the-diff-and-says-so
  (tu/with-terms [dog friendly Rex StoryContext]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list friendly '?x)) StoryContext)
    (let [before (content kb)
          r      (v/preview kb {:add [[(list dog Rex) StoryContext]]} {:max-results 1})]
      (is (= 1 (count (:believed-added r))))
      (is (true? (:bounded? r)) "a capped answer must not read as a complete one")
      (is (= before (content kb))))))

(tu/deftest-kb an-unbounded-run-says-it-was-unbounded
  (tu/with-terms [dog Rex StoryContext]
    (is (false? (:bounded? (v/preview kb {:add [[(list dog Rex) StoryContext]]}))))))

;; ---- 9. an empty batch --------------------------------------------------

(tu/deftest-kb an-empty-batch-previews-nothing-and-moves-nothing
  (let [before (content kb)
        r      (v/preview kb {})]
    (is (= {:believed-added [] :believed-removed [] :refused [] :violations []
            :contradictions [] :bounded? false}
           r))
    (is (= before (content kb)))))

;; ---- 10. the mixed batch -----------------------------------------------

(tu/deftest-kb adds-land-before-removes-in-a-preview-as-they-do-in-an-edit
  (tu/with-terms [dog canine friendly Rex StoryContext]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list friendly '?x)) StoryContext)
    (v/assert kb (vr/rule-sentence [(list canine '?x)] (list friendly '?x)) StoryContext)
    (let [h      (v/assert kb (list dog Rex) StoryContext)
          ch     (v/handle-of kb (list friendly Rex) StoryContext)
          before (content kb)
          r      (v/preview kb {:add    [[(list canine Rex) StoryContext]]
                                :remove [h]})]
      (testing "the added premise re-derives what the removed one was supporting"
        (is (= #{(list canine Rex)} (set (sentences (:believed-added r)))))
        (is (= [(list dog Rex)] (sentences (:believed-removed r))))
        (is (not (contains? (set (map :handle (:believed-removed r))) ch))
            "the conclusion keeps a witness through the batch and never flickers out"))
      (is (= before (content kb))))))

;; ---- 11. the oracle: does the preview predict the edit? ------------------
;; Every other test here pins one behaviour.  This one asks the only question that
;; matters: run the preview, then really run the batch, and compare the two belief
;; diffs.  Sentences and not handles, because content the batch creates — and content
;; a blocked-then-released conclusion is re-derived as — lands on a fresh handle
;; either way, which is exactly why a preview cannot promise handles for it.

(defn- believed-sentences
  "Every believed datum as `{handle sentence}` — computed the expensive way, which is
  fine on a test KB and is what makes it an oracle rather than a re-implementation."
  [kb]
  (into {} (map (fn [h] [h (v/readable-sentence (v/sentex kb h))]))
        (jtms/in-datums (:tms kb))))

(defn- edit-diff
  "The belief diff a real `edit` of `batch` produces, as `{:added #{S} :removed #{S}}`."
  [kb batch]
  (let [before (believed-sentences kb)]
    (v/edit! kb batch)
    (let [after (believed-sentences kb)]
      {:added   (set (vals (apply dissoc after (keys before))))
       :removed (set (vals (apply dissoc before (keys after))))})))

(defn- preview-diff [r]
  {:added   (set (sentences (:believed-added r)))
   :removed (set (sentences (:believed-removed r)))})

(tu/deftest-kb a-preview-predicts-the-edit-when-the-batch-derives
  (tu/with-terms [dog friendly Rex StoryContext]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list friendly '?x)) StoryContext)
    (let [batch {:add [[(list dog Rex) StoryContext]]}]
      (is (= (preview-diff (v/preview kb batch)) (edit-diff kb batch))))))

(tu/deftest-kb a-preview-predicts-the-edit-when-the-batch-defeats
  (tu/with-terms [flies Tweety StoryContext]
    (v/assert kb (list flies Tweety) StoryContext)
    (let [batch {:add [[(list 'not (list flies Tweety)) StoryContext
                        {:strength :monotonic}]]}]
      (is (= (preview-diff (v/preview kb batch)) (edit-diff kb batch))))))

(tu/deftest-kb a-preview-predicts-the-edit-when-the-batch-blocks-a-conclusion
  (tu/with-terms [bird penguin flies Opus StoryContext]
    (v/assert kb (except-rule (list penguin '?b) [(list bird '?b)] (list flies '?b))
              StoryContext)
    (v/assert kb (list bird Opus) StoryContext)
    (let [batch {:add [[(list penguin Opus) StoryContext]]}]
      (is (= (preview-diff (v/preview kb batch)) (edit-diff kb batch))))))

(tu/deftest-kb a-preview-predicts-the-edit-when-the-batch-removes-a-premise
  (tu/with-terms [dog friendly Rex StoryContext]
    (v/assert kb (vr/rule-sentence [(list dog '?x)] (list friendly '?x)) StoryContext)
    (let [h     (v/assert kb (list dog Rex) StoryContext)
          batch {:remove [h]}]
      (is (= (preview-diff (v/preview kb batch)) (edit-diff kb batch))))))

(tu/deftest-kb a-preview-predicts-the-edit-when-the-batch-releases-an-exception
  (tu/with-terms [bird penguin flies Opus StoryContext]
    (v/assert kb (except-rule (list penguin '?b) [(list bird '?b)] (list flies '?b))
              StoryContext)
    (v/assert kb (list bird Opus) StoryContext)
    (let [ph    (v/assert kb (list penguin Opus) StoryContext)
          batch {:remove [ph]}]
      (is (= (preview-diff (v/preview kb batch)) (edit-diff kb batch))))))

;; ---- 12. the clash that withdraws nothing --------------------------------
;; A default against a default is a **represented dilemma**, not a defeat: both sides
;; stay believed and the pair is reported.  So the two diff halves are silent about it,
;; and a caller reading only those would be told the line simply arrived.

(tu/deftest-kb a-batch-that-opens-a-dilemma-reports-it-rather-than-a-withdrawal
  (tu/with-terms [flies Tweety StoryContext]
    (let [h      (v/assert kb (list flies Tweety) StoryContext)
          before (content kb)
          r      (v/preview kb {:add [[(list 'not (list flies Tweety)) StoryContext]]})]
      (testing "nothing was withdrawn, because nothing was defeated"
        (is (empty? (:believed-removed r)))
        (is (true? (v/in? kb h))))
      (testing "but the clash the batch would open is named, with both sides"
        (is (= 1 (count (:contradictions r))))
        (is (= #{(list flies Tweety) (list 'not (list flies Tweety))}
               (set (map :sentence (:sides (first (:contradictions r))))))))
      (is (= before (content kb))))))

(tu/deftest-kb a-dilemma-the-kb-already-has-is-not-the-batch-s-doing
  (tu/with-terms [flies Tweety dog Rex StoryContext]
    (v/assert kb (list flies Tweety) StoryContext)
    (v/assert kb (list 'not (list flies Tweety)) StoryContext)
    (is (= 1 (count (v/contradictions kb))) "the standing dilemma is the baseline")
    (let [r (v/preview kb {:add [[(list dog Rex) StoryContext]]})]
      (is (empty? (:contradictions r))
          "an unrelated line is not answerable for a clash that was already there"))))

;; ---- 13. equality: the second way a belief stops being one ---------------

(tu/deftest-kb a-merge-reports-the-spelling-it-supersedes
  (tu/with-terms [barks Rex Rexy StoryContext]
    (let [h      (v/assert kb (list barks Rexy) StoryContext)
          before (content kb)
          r      (v/preview kb {:add [[(list 'sameAs Rex Rexy) StoryContext]]})]
      (testing "the retired spelling stops being believed, and says why"
        (let [e (first (filter #(= (list barks Rexy) (:sentence %)) (:believed-removed r)))]
          (is (some? e) "the superseded spelling was not reported")
          (is (= h (:handle e)))
          (is (= :superseded (:reason e)))))
      (testing "and the restatement under the representative arrives"
        (is (contains? (set (sentences (:believed-added r))) (list barks Rex))))
      (testing "the merge is undone: the original spelling is believed again"
        (is (true? (v/in? kb h)))
        (is (false? (v/same-class? kb Rex Rexy))))
      (is (= before (content kb))))))

;; ---- 14. a throw during application ------------------------------------
;; `check` is a fair account of `assert`'s refusals, not a proof of one: a batch
;; whose second line is only inadmissible *because the first landed* passes the
;; pre-flight and throws on the way in.  The preview reports it rather than
;; propagating it, and still rolls back.

(tu/deftest-kb a-line-that-throws-only-once-an-earlier-line-lands-is-reported-not-thrown
  (tu/with-terms [fish mammal Willy StoryContext]
    (v/assert kb (list 'disjoint fish mammal) StoryContext)
    (let [before (content kb)
          r      (v/preview kb {:add [[(list fish Willy) StoryContext]
                                      [(list mammal Willy) StoryContext]]})]
      (testing "the pre-flight passed it — the KB it was checked against had neither"
        (is (= [(list fish Willy)] (sentences (:believed-added r)))))
      (testing "so the refusal comes from the application, at its own index"
        (is (= [[:add 1 :disjoint]] (mapv (juxt :in :index :type) (:refused r)))))
      (is (= before (content kb))))))

;; ---- the opts roster ------------------------------------------------------

(tu/deftest-kb a-consequence-door-option-nothing-reads-is-refused
  ;; Every key `preview` and `edit-with-consequences` read is a bound, so the
  ;; silent-default failure is a cap silently off: `{:max-result 5}` reads as no key at
  ;; all, the diff comes back uncapped, and `:bounded?` says false as though the whole
  ;; answer had been asked for.
  (tu/with-terms [dog Muffet CapContext]
    (let [batch {:add [[(list dog Muffet) CapContext]]}]
      (testing "preview refuses the singular typo, naming its roster"
        (let [e (is (thrown? clojure.lang.ExceptionInfo
                             (v/preview kb batch {:max-result 5})))]
          (is (= :unknown-option (:type (ex-data e))))
          (is (= [:max-result] (:unknown (ex-data e))))
          (is (re-find #":max-results" (ex-message e)))))
      (testing "edit-with-consequences reads only :max-results and says so"
        (let [e (is (thrown? clojure.lang.ExceptionInfo
                             (v/edit-with-consequences! kb batch {:max-depth 3})))]
          (is (= :unknown-option (:type (ex-data e))))
          (is (= [:max-depth] (:unknown (ex-data e))))))
      (testing "a non-map opts is refused at both doors"
        ;; The keyword is the point — the refusal is what this asserts — so the
        ;; type mismatch clj-kondo sees is the test's subject, not a defect.
        #_{:clj-kondo/ignore [:type-mismatch]}
        (doseq [door [#(v/preview kb batch :max-results)
                      #(v/edit-with-consequences! kb batch :max-results)]]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"must be a map" (door)))))
      (testing "the rostered keys still run"
        (is (map? (v/preview kb batch {:max-depth 2 :max-derivations 10
                                       :max-results 1})))
        (let [r (v/edit-with-consequences! kb batch {:max-results 1})]
          (is (contains? r :believed-added))
          ;; put the KB back — the roster test's write is not its subject
          (doseq [h (:added r)] (v/retract! kb h)))))))
