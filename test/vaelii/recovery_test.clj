;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.recovery-test
  "Persistence/recovery: rebuild the in-memory taxonomy and JTMS from the durable
  stores, and atomicity of a rejected assert.

  This file's subject IS the durable store, and it deliberately restarts a second
  KB over the same databases, so teardown is a clear rather than JTMS retraction.
  The fixture still guards net-neutrality: it clears at both ends and asserts the
  store is empty on the way out."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.starter :as starter]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :each
  (fn [f]
    (let [kb (tu/fresh)]                       ; cleared empty
      (binding [tu/*kb* kb]
        (let [before (tu/content-count kb)]    ; {:sentexes 0 :justifications 0}
          (try (f)
               (finally
                 (tu/clear-kb! kb)                ; durable content is under test — clesh to clean
                 (is (= before (tu/content-count kb))
                     "recovery test did not return the store to empty"))))))))

(defn- restart
  "Simulate a process restart: a fresh KB over the same databases, with only the
  durable stores — the in-memory taxonomy and JTMS start empty."
  []
  (tu/test-kb))

(tu/deftest-kb recover-rebuilds-taxonomy-and-beliefs
  (starter/load-into kb)
  (world/load-cast kb)                        ; the cast lives in the tests now
  (let [gp (:id (first (v/sentexes-matching kb '(grandparentOf Tom Ann) 'NaturalWorldContext)))]
    (let [kb2 (restart)]
      (testing "before recover, the in-memory graph is empty"
        (is (not (v/isa? kb2 'Muffet 'animal)))           ; taxonomy not rebuilt yet
        (is (not (v/in? kb2 gp))))                        ; jtms not rebuilt yet
      (v/recover kb2)
      (testing "after recover, the taxonomy answers isa? again"
        (is (v/isa? kb2 'Muffet 'animal))
        (is (v/disjoint? kb2 'dog 'cat)))
      (testing "the JTMS is rebuilt: the derived grandparent is IN with its support"
        (is (v/in? kb2 gp))
        (is (seq (v/supporting-justifications kb2 gp))))
      (testing "querying and retraction work on the recovered KB"
        (is (seq (v/sentexes-matching kb2 '(grandparentOf Tom Ann) 'NaturalWorldContext)))
        (let [bob (:id (first (v/sentexes-matching kb2 '(parentOf Bob Ann) 'NaturalWorldContext)))]
          (v/retract! kb2 bob)
          ;; Tom→Bob→Ann gone, but Tom→Bob→Carol keeps grandparentOf via Carol? no —
          ;; retracting (parentOf Bob Ann) removes only (grandparentOf Tom Ann)
          (is (empty? (v/sentexes-matching kb2 '(grandparentOf Tom Ann) 'NaturalWorldContext))))))))

(tu/deftest-kb recover-rebuilds-every-cache-not-only-the-transitive-ones
  ;; `clear-relations!` must empty all six caches, not `:genl` and `:genlContext`
  ;; alone: a rebuild that merged into whatever `:disjoint` / `:props` / `:inverse`
  ;; already held can only ever *add*, so an entry whose sentex is gone would survive
  ;; the recovery meant to re-derive it.  Here the second KB is given a stale entry by
  ;; hand, standing in for one left over from before the restart.
  (let [dog (tu/tmp-type) cat (tu/tmp-type)
        stale-a (tu/tmp-type) stale-b (tu/tmp-type) ghostPred (tu/tmp-pred)]
    (v/assert kb (list 'disjoint dog cat) 'UniverseContext)
    (let [kb2 (restart)]
      ;; entries with no sentex behind them anywhere in the store
      (tax/add-disjoint (:taxonomy kb2) stale-a stale-b 9999)
      (tax/mark-prop (:taxonomy kb2) :transitive ghostPred 9999)
      (is (v/disjoint? kb2 stale-a stale-b))
      (is (v/has-prop? kb2 :transitive ghostPred))
      (v/recover kb2)
      (testing "recovery drops what the store does not back"
        (is (not (v/disjoint? kb2 stale-a stale-b)))
        (is (not (v/has-prop? kb2 :transitive ghostPred))))
      (testing "and re-derives what it does"
        (is (v/disjoint? kb2 dog cat))))))

(tu/deftest-kb recover-rebuilds-disjoint-metatype-membership
  ;; A metatype's members are cached in memory, not stored: the only durable trace is
  ;; the `(M T)` sentexes themselves.  So recovery has to re-read them *after* the
  ;; metatypes are known, or a restart silently loses every pair the metatype
  ;; separated — with no `(disjoint a b)` sentex left to cover for it, as there used
  ;; to be when the clique was materialized.
  (let [animalSpecies (tu/tmp-pred) dog (tu/tmp-type) cat (tu/tmp-type)]
    (v/assert kb (list 'disjointMetatype animalSpecies) 'UniverseContext)
    (v/assert kb (list animalSpecies dog) 'UniverseContext)
    (v/assert kb (list animalSpecies cat) 'UniverseContext)
    (is (v/disjoint? kb dog cat))
    (let [kb2 (restart)]
      (v/recover kb2)
      (is (v/disjoint? kb2 dog cat)
          "membership must be rebuilt, not just the metatype mark"))))

(tu/deftest-kb recover-agrees-about-a-defeated-declaration
  ;; The four flat caches follow belief now, like genl: a defeated `(disjoint A B)`
  ;; stops constraining (docs/taxonomy.md).  Recovery must reproduce that, not merely
  ;; be self-consistent.  `rebuild-taxonomy` replays the *stored* disjoint (the
  ;; defeated one included) so `:cache-support` records every asserting sentex, and the
  ;; `settle` at the end of `recover` then drops it by belief — the same answer either
  ;; side of a restart.  A belief-filtered rebuild would lose the disbelieved supporter
  ;; and clearing its defeat could never revive the entry.
  (let [dog (tu/tmp-type) cat (tu/tmp-type)]
    (v/assert kb (list 'disjoint dog cat) 'UniverseContext {:strength :default})
    (v/assert kb (list 'not (list 'disjoint dog cat)) 'UniverseContext {:strength :monotonic})
    (let [before (v/disjoint? kb dog cat)
          kb2    (restart)]
      (is (not before) "a defeated disjoint does not constrain in memory")
      (v/recover kb2)
      (is (not (v/disjoint? kb2 dog cat)) "nor after a restart")
      (is (= before (v/disjoint? kb2 dog cat))
          "the answer must not change across a restart"))))

(tu/deftest-kb rejected-assert-leaves-no-trace
  (let [dog (tu/tmp-type) animal (tu/tmp-type) fido (tu/tmp-ind)]
    (v/assert kb (list 'genl dog animal) 'UniverseContext)
    (let [n   (p/count-at (:index kb) [])
          ids (count (p/sentex-ids (:records kb)))]
      (testing "a not-well-formed assert writes nothing (checks precede writes)"
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list 'genl fido animal) 'UniverseContext)))  ; genl on an individual
        (is (= n   (p/count-at (:index kb) [])))
        (is (= ids (count (p/sentex-ids (:records kb))))))
      (testing "a naming violation likewise"
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list dog fido) 'badContext)))               ; badContext is not a valid context
        (is (= n (p/count-at (:index kb) [])))))))

(tu/deftest-kb the-recover-option-selects-rebuild-warn-or-silence
  ;; open-kb over non-empty databases without recovery returns a KB whose empty TMS
  ;; and taxonomy make every query silently answer nothing.  `:recover?` defaults to
  ;; `:auto` — rebuild at construction (the test below pins the default itself);
  ;; `false` opts out silently, and `:warn` opts out with a log, leaving recovery to
  ;; the caller.
  (tu/with-terms [dog animal Muffet]
    (v/assert kb (list 'genl dog animal) 'UniverseContext)
    (v/assert kb (list dog Muffet) 'UniverseContext)
    (testing "{:recover? false} constructs an empty-memory KB (recovery is the caller's)"
      (let [kb2 (restart)]                       ; tu/test-kb pins :recover? false
        (is (empty? (v/sentexes-matching kb2 (list dog Muffet) 'UniverseContext)))))
    (testing "{:recover? :warn} likewise — it logs instead of rebuilding"
      (let [kbw (v/open-kb (assoc tu/scratch-space :recover? :warn))]
        (is (empty? (v/sentexes-matching kbw (list dog Muffet) 'UniverseContext)))
        (is (not (v/isa? kbw Muffet animal)))))
    (testing "{:recover? :auto} answers immediately"
      (let [kb3 (v/open-kb (assoc tu/scratch-space :recover? :auto))]
        (is (seq (v/sentexes-matching kb3 (list dog Muffet) 'UniverseContext)))
        (is (v/isa? kb3 Muffet animal))))))

(tu/deftest-kb recover-defaults-to-auto-when-unstated
  ;; The pin for the default itself.  The suite states `:recover?` on every KB it
  ;; builds (`tu/space-opts` pins false, the tests above spell :warn / :auto out), so
  ;; only this open does what a user's does — a non-empty durable store, no
  ;; `:recover?` at all.  The contract: an unstated policy behaves as `:auto`, so the
  ;; KB answers at construction rather than handing back one whose queries silently
  ;; answer nothing.
  (tu/with-terms [dog animal Muffet]
    (v/assert kb (list 'genl dog animal) 'UniverseContext)
    (v/assert kb (list dog Muffet) 'UniverseContext)
    (let [kb2 (v/open-kb (dissoc tu/scratch-space :recover?))]
      (is (seq (v/sentexes-matching kb2 (list dog Muffet) 'UniverseContext))
          "believed at construction — the unstated default recovered")
      (is (v/isa? kb2 Muffet animal)))))

(tu/deftest-kb recover-re-supersedes-a-schematic-rewrite
  ;; A schematic (equals L R) normalizes stored terms to justified twins and supersedes
  ;; the un-normalized originals.  Supersession is derived from the rewrite rules, not
  ;; stored, so recover must re-establish it (via `recovered-supersessions`) — else both
  ;; the original and its twin would be believed after a restart.  The twin's
  ;; justification IS stored, so it survives; only supersession needs re-deriving.
  (tu/with-terms [pp gpp chainR Nn]
    (v/assert kb (list 'equals (list pp (list pp '?x)) (list gpp '?x)) 'UniverseContext)
    (v/assert kb (list chainR (list pp (list pp Nn))) 'UniverseContext)
    (let [orig (v/handle-of kb (list chainR (list pp (list pp Nn))) 'UniverseContext)
          twin (v/handle-of kb (list chainR (list gpp Nn)) 'UniverseContext)]
      (is (some? twin) "the twin was created")
      (is (v/in? kb twin))
      (is (not (v/in? kb orig)) "the original is superseded before the restart")
      (let [kb2 (restart)]
        (v/recover kb2)
        (testing "after recover the twin is believed and the original stays superseded"
          (is (v/in? kb2 twin))
          (is (not (v/in? kb2 orig)))
          (is (seq (v/sentexes-matching kb2 (list chainR (list gpp Nn)) 'UniverseContext))))))))

(tu/deftest-kb recover-survives-a-predicate-and-type-merge
  ;; Round-two rewriteOf merges a predicate / type by moving its functor uses onto the
  ;; representative — facts, the genl closure, and rules (docs/equality.md).  The twins
  ;; (moved fact, edge, rule, rule conclusion) are stored justifications and the rule index
  ;; lives in the index, so both survive the restart; supersession alone is re-derived by
  ;; `recovered-supersessions`.
  (tu/with-terms [bornIn birthplaceOf knownPlace Ada London
                  dog canine animal Rex]
    (v/assert kb (list 'implies (list birthplaceOf '?x '?c) (list knownPlace '?c)) 'UniverseContext)
    (v/assert kb (list birthplaceOf Ada London) 'UniverseContext)
    (v/assert kb (list 'rewriteOf bornIn birthplaceOf) 'UniverseContext)   ; predicate merge
    (v/assert kb (list 'genl dog animal) 'UniverseContext)
    (v/assert kb (list dog Rex) 'UniverseContext)
    (v/assert kb (list 'rewriteOf canine dog) 'UniverseContext)             ; type merge
    (let [moved (v/handle-of kb (list bornIn Ada London) 'UniverseContext)
          known (v/handle-of kb (list knownPlace London) 'UniverseContext)
          orig  (v/handle-of kb (list birthplaceOf Ada London) 'UniverseContext)]
      (is (v/in? kb moved))
      (is (v/in? kb known) "the migrated rule concluded before the restart")
      (let [kb2 (restart)]
        (v/recover kb2)
        (testing "the predicate merge survives: fact moved, original superseded, rule rebuilt"
          (is (v/in? kb2 moved))
          (is (not (v/in? kb2 orig)))
          (is (v/in? kb2 known)))
        (testing "and the recovered rule index still carries the migrated rule"
          (tu/with-terms [Bob Paris]
            (v/assert kb2 (list bornIn Bob Paris) 'UniverseContext)
            (is (seq (v/sentexes-matching kb2 (list knownPlace Paris) 'UniverseContext)))))
        (testing "the type merge survives: isa? answers under the representative"
          (is (v/isa? kb2 Rex canine 'UniverseContext))
          (is (v/isa? kb2 Rex animal 'UniverseContext))
          (is (contains? (set (v/genls kb2 canine)) animal)))))))

(tu/deftest-kb recover-re-supersedes-a-spelling-only-a-context-retired
  ;; Supersession is the *reader's*: a term can head its whole class globally and still
  ;; be retired inside a context whose visible edges elect somebody else, when the
  ;; `rewriteOf` that made it preferred is one that context cannot see.  Nominating
  ;; recovery's candidates by the global election would drop exactly those and the KB
  ;; would come back believing both spellings (docs/equality.md).
  (tu/with-terms [admires Kim Tango Yankee Zulu Xray VisContext HidContext]
    (v/assert kb (list 'genlContext VisContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'genlContext HidContext 'UniverseContext) 'UniverseContext)
    ;; Vis sees: Tango~Yankee and Yankee over Zulu  -> Vis elects Yankee
    (v/assert kb (list 'sameAs Tango Yankee)   VisContext)
    (v/assert kb (list 'rewriteOf Yankee Zulu) VisContext)
    ;; Hid alone sees Tango over Xray, which is what makes Tango the *global* head
    (v/assert kb (list 'rewriteOf Tango Xray)  HidContext)
    (v/assert kb (list admires Kim Tango) VisContext)
    (is (= Tango (v/representative kb Tango)) "Tango heads the class globally")
    (is (= Yankee (v/representative kb Tango VisContext)) "...and is retired inside Vis")
    (let [orig (v/handle-of kb (list admires Kim Tango) VisContext)
          twin (v/handle-of kb (list admires Kim Yankee) VisContext)]
      (is (some? twin))
      (is (not (v/in? kb orig)) "superseded before the restart")
      (let [kb2 (restart)]
        (v/recover kb2)
        (is (v/in? kb2 twin))
        (is (not (v/in? kb2 orig)) "and still superseded after it")
        (is (= [{'?x Yankee}] (v/query kb2 (list admires Kim '?x) VisContext))
            "so Vis reports the one fact once, in the name Vis elects")))))
