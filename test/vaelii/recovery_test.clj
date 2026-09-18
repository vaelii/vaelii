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
            [vaelii.host.starter :as starter]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :each
  (fn [f]
    (let [kb (tu/fresh)]                       ; cleared empty
      (binding [tu/*kb* kb]
        (let [before (tu/content-count kb)]    ; {:sentexes 0 :justifications 0}
          (try (f)
               (finally
                 (tu/clear-kb! kb)                ; durable content is under test — clear to clean
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
  (let [gp (v/handle-of kb '(grandparentOf Tom Ann) 'CxNaturalWorld)]
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
        (is (seq (v/sentexes-matching kb2 '(grandparentOf Tom Ann) 'CxNaturalWorld)))
        (let [bob (v/handle-of kb2 '(parentOf Bob Ann) 'CxNaturalWorld)]
          (v/retract! kb2 bob)
          ;; Tom→Bob→Ann gone, but Tom→Bob→Carol keeps grandparentOf via Carol? no —
          ;; retracting (parentOf Bob Ann) removes only (grandparentOf Tom Ann)
          (is (empty? (v/sentexes-matching kb2 '(grandparentOf Tom Ann) 'CxNaturalWorld))))))))

(tu/deftest-kb recover-rebuilds-every-cache-not-only-the-transitive-ones
  ;; `clear-relations!` must empty all six caches, not `:genl` and `:genlCx`
  ;; alone: a rebuild that merged into whatever `:disjoint` / `:props` / `:inverse`
  ;; already held can only ever *add*, so an entry whose sentex is gone would survive
  ;; the recovery meant to re-derive it.  Here the second KB is given a stale entry by
  ;; hand, standing in for one left over from before the restart.
  (let [dog (tu/tmp-type) cat (tu/tmp-type)
        stale-a (tu/tmp-type) stale-b (tu/tmp-type) ghostPred (tu/tmp-pred)]
    (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
    (let [kb2 (restart)]
      ;; entries with no sentex behind them anywhere in the store
      (tax/add-disjoint (reasoning/taxonomy kb2) stale-a stale-b 9999)
      (tax/mark-prop (reasoning/taxonomy kb2) :transitive ghostPred 9999)
      (is (v/disjoint? kb2 stale-a stale-b))
      (is (v/has-prop? kb2 :transitive ghostPred))
      (v/recover kb2)
      (testing "recovery drops what the store does not back"
        (is (not (v/disjoint? kb2 stale-a stale-b)))
        (is (not (v/has-prop? kb2 :transitive ghostPred))))
      (testing "and re-derives what it does"
        (is (v/disjoint? kb2 dog cat))))))

(tu/deftest-kb recover-does-not-answer-through-an-unsupported-edge
  ;; The replay reads **stored** declarations, so an edge whose record carries no premise
  ;; mark and no justification is activated exactly as a supported one is — and nothing in
  ;; the rebuild opposes it.  No defeat, no block, no supersession: the closing settle has
  ;; no event to react to, and the region-scoped reconcile it runs when it does have one
  ;; would not name this edge either.  So recovery reconciles against belief itself, before
  ;; the settle.  The defeated twin of the claim is
  ;; `taxonomy_belief_test/recover-does-not-revive-a-defeated-edge`, which the opposition
  ;; alone would carry; a store whose records lost their strength marks is what presents
  ;; the unsupported case, and the record store's own API is what stages it here.
  (tu/with-terms [dog_t mammal_t Rex]
    (v/assert kb (list 'genl dog_t mammal_t) 'CxUniverse)
    (v/assert kb (list dog_t Rex) 'CxUniverse)
    (let [h (v/handle-of kb (list 'genl dog_t mammal_t) 'CxUniverse)]
      (p/unmark-premise! (:records kb) h)     ; the record survives, its support does not
      (let [kb2 (restart)]
        (v/recover kb2)
        (is (not (v/in? kb2 h)) "nothing stored supports the edge")
        (testing "so nothing derived from the closure answers through it"
          (is (not (contains? (set (v/genls kb2 dog_t)) mammal_t)))
          (is (not (contains? (set (v/types kb2)) mammal_t)))
          (is (not (v/isa? kb2 Rex mammal_t))))
        (testing "and the supporter is still stored, so re-marking it brings the edge back"
          (p/mark-premise (:records kb2) h :default)
          (v/recover kb2)
          (is (v/in? kb2 h))
          (is (contains? (set (v/genls kb2 dog_t)) mammal_t))
          (is (v/isa? kb2 Rex mammal_t)))))))

(tu/deftest-kb recover-drops-a-malformed-edge-declaration-rather-than-crashing
  ;; `recover` replays the **stored** genl / genlCx sentexes rather than the checked ones,
  ;; reading each edge positionally (`[_ a b]`).  A store an older or foreign writer left a
  ;; non-edge sentex under the genl / genlCx functor root then reaches the rebuild arm as a
  ;; malformed edge whose super reads nil — a two-element sentence binds the member as the
  ;; sub and nil as the super.  Added, the nil is a node the closure's `strong-components`
  ;; cannot walk (`java.util.ArrayDeque` rejects a null element), and it throws the moment a
  ;; loose or cyclic relation is condensed — the `NullPointerException` recover hits on such
  ;; a store.  The genlCx cycle below makes that walk run during the replay, so this is the
  ;; reported crash; the fix drops the malformed declaration and warns, the way `rebuild-tms`
  ;; drops a justification the store cannot root.
  (let [rec    (:records kb)
        idx    (:index kb)
        store! (fn [sentence]                          ; put a sentex past the assert checks
                 (let [s (sx/sentex sentence 'CxUniverse)
                       h (p/put-sentex rec s)]
                   (p/mark-premise rec h :default)
                   (p/index-sentex idx (assoc s :id h) h)))]
    ;; a genlCx cycle — two contexts that see each other — which forces the condensation
    ;; walk during the replay.  `wff` refuses one at assert (docs/contexts.md), but a
    ;; foreign or older writer's store can hold it and recovery replays the stored edges
    ;; past the checks, so it is stored directly here the way such a writer would.
    (store! '(genlCx CxAaa CxBbb))
    (store! '(genlCx CxBbb CxAaa))
    ;; the malformed declarations: a two-element genl / genlCx sentex a foreign loader or an
    ;; older writer's store presents, which no assert path would let past `wff`
    (store! '(genl foo))
    (store! '(genlCx CxFoo))
    (let [kb2   (restart)
          level (v/log-level)
          out   (try (v/set-log-level :warn)
                     (with-out-str (v/recover kb2))     ; throws here without the fix
                     (finally (v/set-log-level level)))
          tax2  @(reasoning/taxonomy kb2)]
      (testing "recover completes rather than crashing in strong-components"
        (is (not (contains? (get-in tax2 [:genl :nodes]) nil)))
        (is (not (contains? (get-in tax2 [:genlCx :nodes]) nil))))
      (testing "the malformed declaration seeds no edge at all, not merely no null node"
        (is (empty? (get-in tax2 [:genl :fwd])))
        (is (= #{'CxAaa 'CxBbb} (get-in tax2 [:genlCx :nodes]))
            "only the well-formed cycle's contexts are nodes"))
      (testing "and the drop is reported, not silent"
        (is (re-find #"not well-formed edges" out))))))

(tu/deftest-kb recover-drops-over-arity-edge-declarations-rather-than-fabricating
  ;; #82: v0.17's replay guard requires both endpoints to be symbols, but the rebuild arm
  ;; reads the edge positionally (`[_ a b]`) off the stored sentence — so an OVER-ARITY row
  ;; `(genl a b surplus)` an older or foreign writer left under the genl / genlCx functor
  ;; root has symbols in positions 1 and 2, passes the endpoint-only guard, and is replayed
  ;; as `(genl a b)`: an edge fabricated from a sentence that never was one, its surplus
  ;; term silently discarded.  The endpoints are non-nil, so — unlike #80 — there is no
  ;; `strong-components` crash; the bug is a SILENT fabrication.  The complete-shape guard
  ;; (arity three, the expected functor, both endpoints symbols) drops it and counts it,
  ;; the same producer boundary #80 drew, applied to the sentence entire.
  (let [rec      (:records kb)
        idx      (:index kb)
        store!   (fn [sentence]                        ; put a sentex past the assert checks
                   (let [s (sx/sentex sentence 'CxUniverse)
                         h (p/put-sentex rec s)]
                     (p/mark-premise rec h :default)
                     (p/index-sentex idx (assoc s :id h) h)))
        sub-ok   (tu/tmp-type)
        super-ok (tu/tmp-type)]
    ;; well-formed edges that MUST survive the rebuild
    (v/assert kb (list 'genl sub-ok super-ok) 'CxUniverse)
    (v/assert kb (list 'genlCx 'CxSubOk 'CxSuperOk) 'CxUniverse)
    ;; over-arity declarations under the correct functor root, symbols in both endpoints —
    ;; the shape the v0.17 endpoint guard replays and this fix rejects
    (store! '(genl SubOver SuperOver SurplusOver))
    (store! '(genlCx CxSubOver CxSuperOver CxSurplusOver))
    (let [kb2   (restart)
          level (v/log-level)
          out   (try (v/set-log-level :warn)
                     (with-out-str (v/recover kb2))
                     (finally (v/set-log-level level)))
          tax2  @(reasoning/taxonomy kb2)]
      (testing "the well-formed edges survive the rebuild"
        (is (contains? (set (v/genls kb2 sub-ok)) super-ok))
        (is (contains? (get-in tax2 [:genlCx :nodes]) 'CxSubOk)))
      (testing "the over-arity row seeds neither edge nor node"
        (is (not (contains? (set (v/genls kb2 'SubOver)) 'SuperOver)))
        (is (not (contains? (get-in tax2 [:genl :nodes]) 'SubOver)))
        (is (not (contains? (get-in tax2 [:genl :nodes]) 'SurplusOver)))
        (is (not (contains? (get-in tax2 [:genlCx :nodes]) 'CxSubOver))))
      (testing "and the drop is reported, not silent"
        (is (re-find #"not well-formed edges" out))))))

(tu/deftest-kb recover-rebuilds-disjoint-metatype-membership
  ;; A metatype's members are cached in memory, not stored: the only durable trace is
  ;; the `(M T)` sentexes themselves.  So recovery has to re-read them *after* the
  ;; metatypes are known, or a restart silently loses every pair the metatype
  ;; separated — with no `(disjoint a b)` sentex left to cover for it, as there used
  ;; to be when the clique was materialized.
  (let [animal_species (tu/tmp-pred) dog (tu/tmp-type) cat (tu/tmp-type)]
    (v/assert kb (list 'disjoint_metatype animal_species) 'CxUniverse)
    (v/assert kb (list animal_species dog) 'CxUniverse)
    (v/assert kb (list animal_species cat) 'CxUniverse)
    (is (v/disjoint? kb dog cat))
    (let [kb2 (restart)]
      (v/recover kb2)
      (is (v/disjoint? kb2 dog cat)
          "membership must be rebuilt, not just the metatype mark"))))

(tu/deftest-kb recover-rebuilds-sibling-disjoint-marks
  ;; Only the `(sibling_disjoint C)` sentex is durable; the pairs it separates are read
  ;; off the genl closure, not stored.  So recovery has to re-mark the parent *and*
  ;; rebuild the closure it reads through, or a restart silently loses every separation.
  (let [collection (tu/tmp-type) dog (tu/tmp-type) cat (tu/tmp-type)]
    (v/assert kb (list 'genl dog collection) 'CxUniverse)
    (v/assert kb (list 'genl cat collection) 'CxUniverse)
    (v/assert kb (list 'sibling_disjoint collection) 'CxUniverse)
    (is (v/disjoint? kb dog cat))
    (let [kb2 (restart)]
      (v/recover kb2)
      (is (v/disjoint? kb2 dog cat)
          "the mark and the genl closure it reads must both be rebuilt"))))

(tu/deftest-kb recover-rebuilds-a-sibling-disjoint-exception
  ;; The exception is a belief-following sentex keyed like disjoint; only the sentex is
  ;; durable.  Recovery must replay it and re-mark the exemption, or a restart re-separates
  ;; a pair the KB exempts — while a non-exempted sibling stays separated.
  (let [collection (tu/tmp-type) a (tu/tmp-type) b (tu/tmp-type) c (tu/tmp-type)]
    (v/assert kb (list 'genl a collection) 'CxUniverse)
    (v/assert kb (list 'genl b collection) 'CxUniverse)
    (v/assert kb (list 'genl c collection) 'CxUniverse)
    (v/assert kb (list 'sibling_disjoint collection) 'CxUniverse)
    (v/assert kb (list 'siblingDisjointException a b) 'CxUniverse)
    (is (not (v/disjoint? kb a b)))
    (is (v/disjoint? kb a c))
    (let [kb2 (restart)]
      (v/recover kb2)
      (is (not (v/disjoint? kb2 a b))
          "the exemption must be rebuilt, not just the mark")
      (is (v/disjoint? kb2 a c)
          "and the mark it excepts still separates a non-exempted pair"))))

(tu/deftest-kb recover-agrees-about-a-defeated-exception
  ;; The exceptions cache follows belief like the others: a defeated exception does not
  ;; exempt.  rebuild-taxonomy replays the *stored* exception (the defeated one included) so
  ;; :cache-support records every asserting sentex, and the reconcile recover runs drops it
  ;; by belief — the same answer either side of a restart.
  (let [collection (tu/tmp-type) a (tu/tmp-type) b (tu/tmp-type)]
    (v/assert kb (list 'genl a collection) 'CxUniverse)
    (v/assert kb (list 'genl b collection) 'CxUniverse)
    (v/assert kb (list 'sibling_disjoint collection) 'CxUniverse)
    (v/assert kb (list 'siblingDisjointException a b) 'CxUniverse {:strength :default})
    (v/assert kb (list 'not (list 'siblingDisjointException a b)) 'CxUniverse {:strength :monotonic})
    (let [before (v/disjoint? kb a b)
          kb2    (restart)]
      (is before "a defeated exception does not exempt in memory")
      (v/recover kb2)
      (is (v/disjoint? kb2 a b) "nor after a restart")
      (is (= before (v/disjoint? kb2 a b))
          "the answer must not change across a restart"))))

(tu/deftest-kb recover-agrees-about-a-defeated-declaration
  ;; The four flat caches follow belief now, like genl: a defeated `(disjoint A B)`
  ;; stops constraining (docs/taxonomy.md).  Recovery must reproduce that, not merely
  ;; be self-consistent.  `rebuild-taxonomy` replays the *stored* disjoint (the
  ;; defeated one included) so `:cache-support` records every asserting sentex, and the
  ;; reconcile `recover` runs over the replay then drops it by belief — the same answer
  ;; either side of a restart.  A belief-filtered rebuild would lose the disbelieved
  ;; supporter and clearing its defeat could never revive the entry.
  (let [dog (tu/tmp-type) cat (tu/tmp-type)]
    (v/assert kb (list 'disjoint dog cat) 'CxUniverse {:strength :default})
    (v/assert kb (list 'not (list 'disjoint dog cat)) 'CxUniverse {:strength :monotonic})
    (let [before (v/disjoint? kb dog cat)
          kb2    (restart)]
      (is (not before) "a defeated disjoint does not constrain in memory")
      (v/recover kb2)
      (is (not (v/disjoint? kb2 dog cat)) "nor after a restart")
      (is (= before (v/disjoint? kb2 dog cat))
          "the answer must not change across a restart"))))

(tu/deftest-kb recover-skips-the-retroactive-sweep-and-decides-the-same-clash
  ;; `recover`'s first settle holds every stored sentex, so the retroactive sweeps can add
  ;; no candidate to it (`settle/*whole-store-region?*`).  Two claims: recover reaches no
  ;; declaration through `declaration-implicates`, and the clash a late declaration makes
  ;; is decided the same way live and after a restart.
  (let [dog (tu/tmp-type) cat (tu/tmp-type) rex (tu/tmp-ind "Rex")]
    (v/assert kb (list dog rex) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list cat rex) 'CxUniverse {:strength :default})
    (v/assert kb (list 'disjoint dog cat) 'CxUniverse {:strength :monotonic})
    (let [cat-h  (v/handle-of kb (list cat rex) 'CxUniverse)
          before (v/in? kb cat-h)
          kb2    (restart)
          calls  (atom 0)
          real   @#'settle/declaration-implicates]
      (is (not before) "the late declaration defeats the default member live")
      (with-redefs-fn {#'settle/declaration-implicates
                       (fn [& args] (swap! calls inc) (apply real args))}
        #(v/recover kb2))
      (is (zero? @calls) "recover's first settle runs no retroactive sweep")
      (is (= before (v/in? kb2 cat-h)) "and decides the pair as the live KB did"))))

(tu/deftest-kb recover-agrees-about-a-rule-concluded-equality
  ;; The live path reads the write and the rebuild reads the store, so a functor whose
  ;; two arms differ is a KB that disagrees with its own restart about what it entails.
  ;; A rule concluding one of the three equality relations is the case that asks it of
  ;; the closure: the conclusion is stored like any other, `rebuild-taxonomy` replays
  ;; every stored `rewriteOf` / `sameAs` / `equals`, and the derivation path has to have
  ;; put the same edge in the running KB.  All three relations, since the arm is
  ;; dispatched by functor.  The live half of the claim is
  ;; `equality-test/a-rule-concluding-an-equality-merges-like-an-asserted-one`.
  (doseq [rel '[rewriteOf sameAs equals]]
    (testing (str "a rule concluding " rel)
      (let [aliasOf  (tu/tmp-pred "alias")
            caresFor (tu/tmp-pred "caresFor")
            Tom      (tu/tmp-ind "Tom")
            [lo hi]  (sort [(tu/tmp-ind "Ann") (tu/tmp-ind "Ann")])]
        (v/assert-rule kb [(list aliasOf '?x '?y)] (list rel '?x '?y) 'CxUniverse {:direction :forward})
        (v/assert kb (list caresFor hi Tom) 'CxUniverse)
        (v/assert kb (list aliasOf lo hi) 'CxUniverse)
        (let [live-class (set (v/equiv-class kb hi))
              live-rep   (v/representative kb hi)
              live-in?   (v/in? kb (v/handle-of kb (list caresFor hi Tom) 'CxUniverse))
              kb2        (restart)]
          (v/recover kb2)
          (testing "the rebuilt closure holds what the live one holds"
            (is (= live-class (set (v/equiv-class kb2 hi)))
                (str "the running KB and its own rebuild disagree about " hi "'s class: "
                     (pr-str live-class) " live, "
                     (pr-str (set (v/equiv-class kb2 hi))) " rebuilt"))
            (is (= live-rep (v/representative kb2 hi))))
          (testing "and they agree about the displaced spelling"
            (is (= live-in?
                   (v/in? kb2 (v/handle-of kb2 (list caresFor hi Tom) 'CxUniverse)))
                "a restart changed whether the retired spelling is believed")))))))

(tu/deftest-kb recover-agrees-about-a-rule-concluded-disjoint-metatype
  ;; The same claim one functor over: `rebuild-taxonomy` replays every stored
  ;; `disjoint_metatype`, so a mark a rule concluded has to separate the metatype's
  ;; members in the running KB as well, or the restart is what makes two types
  ;; disjoint.  The members here are asserted; a member a rule *concludes* is a
  ;; structural arm rather than a table entry and is where the derivation path stops
  ;; (docs/taxonomy.md, "What a rule may conclude").
  (let [seen (tu/tmp-pred "seen") m (tu/tmp-pred "kind_of")
        a    (tu/tmp-type "aa")   b (tu/tmp-type "bb")]
    (v/assert-rule kb [(list seen '?p)] (list 'disjoint_metatype '?p) 'CxUniverse {:direction :forward})
    (v/assert kb (list m a) 'CxUniverse)
    (v/assert kb (list m b) 'CxUniverse)
    (v/assert kb (list seen m) 'CxUniverse)
    (let [live (v/disjoint? kb a b)
          kb2  (restart)]
      (is live "a metatype a rule concluded does not separate its members")
      (v/recover kb2)
      (is (= live (v/disjoint? kb2 a b))
          "a restart changed whether the metatype separates its members"))))

(tu/deftest-kb rejected-assert-leaves-no-trace
  (let [dog (tu/tmp-type) animal (tu/tmp-type) muffet (tu/tmp-ind)]
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (let [n   (p/count-at (:index kb) [])
          ids (count (p/sentex-ids (:records kb)))]
      (testing "a not-well-formed assert writes nothing (checks precede writes)"
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list 'genl muffet animal) 'CxUniverse)))  ; genl on an individual
        (is (= n   (p/count-at (:index kb) [])))
        (is (= ids (count (p/sentex-ids (:records kb))))))
      (testing "a naming violation likewise"
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list dog muffet) 'badContext)))               ; badContext is not a valid context
        (is (= n (p/count-at (:index kb) [])))))))

(tu/deftest-kb the-recover-option-selects-rebuild-warn-or-silence
  ;; open-kb over non-empty databases without recovery returns a KB whose empty TMS
  ;; and taxonomy make every query silently answer nothing.  `:recover?` defaults to
  ;; `:auto` — rebuild at construction (the test below pins the default itself);
  ;; `false` opts out silently, and `:warn` opts out with a log, leaving recovery to
  ;; the caller.
  (tu/with-terms [dog animal Muffet]
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (testing "{:recover? false} constructs an empty-memory KB (recovery is the caller's)"
      (let [kb2 (restart)]                       ; tu/test-kb pins :recover? false
        (is (empty? (v/sentexes-matching kb2 (list dog Muffet) 'CxUniverse)))))
    (testing "{:recover? :warn} likewise — it logs instead of rebuilding"
      (let [kbw (v/open-kb (assoc tu/scratch-space :recover? :warn))]
        (is (empty? (v/sentexes-matching kbw (list dog Muffet) 'CxUniverse)))
        (is (not (v/isa? kbw Muffet animal)))))
    (testing "{:recover? :auto} answers immediately"
      (let [kb3 (v/open-kb (assoc tu/scratch-space :recover? :auto))]
        (is (seq (v/sentexes-matching kb3 (list dog Muffet) 'CxUniverse)))
        (is (v/isa? kb3 Muffet animal))))))

(tu/deftest-kb recover-defaults-to-auto-when-unstated
  ;; The pin for the default itself.  The suite states `:recover?` on every KB it
  ;; builds (`tu/space-opts` pins false, the tests above spell :warn / :auto out), so
  ;; only this open does what a user's does — a non-empty durable store, no
  ;; `:recover?` at all.  The contract: an unstated policy behaves as `:auto`, so the
  ;; KB answers at construction rather than handing back one whose queries silently
  ;; answer nothing.
  (tu/with-terms [dog animal Muffet]
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (let [kb2 (v/open-kb (dissoc tu/scratch-space :recover?))]
      (is (seq (v/sentexes-matching kb2 (list dog Muffet) 'CxUniverse))
          "believed at construction — the unstated default recovered")
      (is (v/isa? kb2 Muffet animal)))))

(tu/deftest-kb recover-re-supersedes-a-schematic-rewrite
  ;; A schematic (equals L R) normalizes stored terms to justified twins and supersedes
  ;; the un-normalized originals.  Supersession is derived from the rewrite rules, not
  ;; stored, so recover must re-establish it (via `recovered-supersessions`) — else both
  ;; the original and its twin would be believed after a restart.  The twin's
  ;; justification IS stored, so it survives; only supersession needs re-deriving.
  (tu/with-terms [pp gpp chainR Nn]
    (v/assert kb (list 'equals (list pp (list pp '?x)) (list gpp '?x)) 'CxUniverse)
    (v/assert kb (list chainR (list pp (list pp Nn))) 'CxUniverse)
    (let [orig (v/handle-of kb (list chainR (list pp (list pp Nn))) 'CxUniverse)
          twin (v/handle-of kb (list chainR (list gpp Nn)) 'CxUniverse)]
      (is (some? twin) "the twin was created")
      (is (v/in? kb twin))
      (is (not (v/in? kb orig)) "the original is superseded before the restart")
      (let [kb2 (restart)]
        (v/recover kb2)
        (testing "after recover the twin is believed and the original stays superseded"
          (is (v/in? kb2 twin))
          (is (not (v/in? kb2 orig)))
          (is (seq (v/sentexes-matching kb2 (list chainR (list gpp Nn)) 'CxUniverse))))))))

(tu/deftest-kb recover-survives-a-predicate-and-type-merge
  ;; Round-two rewriteOf merges a predicate / type by moving its functor uses onto the
  ;; representative — facts, the genl closure, and rules (docs/equality.md).  The twins
  ;; (moved fact, edge, rule, rule conclusion) are stored justifications and the rule index
  ;; lives in the index, so both survive the restart; supersession alone is re-derived by
  ;; `recovered-supersessions`.
  (tu/with-terms [bornIn birthplaceOf knownPlace Ada London
                  dog canine animal Rex]
    (v/assert kb (list 'implies (list birthplaceOf '?x '?c) (list knownPlace '?c)) 'CxUniverse {:direction :forward})
    (v/assert kb (list birthplaceOf Ada London) 'CxUniverse)
    (v/assert kb (list 'rewriteOf bornIn birthplaceOf) 'CxUniverse)   ; predicate merge
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (v/assert kb (list dog Rex) 'CxUniverse)
    (v/assert kb (list 'rewriteOf canine dog) 'CxUniverse)             ; type merge
    (let [moved (v/handle-of kb (list bornIn Ada London) 'CxUniverse)
          known (v/handle-of kb (list knownPlace London) 'CxUniverse)
          orig  (v/handle-of kb (list birthplaceOf Ada London) 'CxUniverse)]
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
            (v/assert kb2 (list bornIn Bob Paris) 'CxUniverse)
            (is (seq (v/sentexes-matching kb2 (list knownPlace Paris) 'CxUniverse)))))
        (testing "the type merge survives: isa? answers under the representative"
          (is (v/isa? kb2 Rex canine 'CxUniverse))
          (is (v/isa? kb2 Rex animal 'CxUniverse))
          (is (contains? (set (v/genls kb2 canine)) animal)))))))

(tu/deftest-kb recover-re-supersedes-a-spelling-only-a-context-retired
  ;; Supersession is the *reader's*: a term can head its whole class globally and still
  ;; be retired inside a context whose visible edges elect somebody else, when the
  ;; `rewriteOf` that made it preferred is one that context cannot see.  Nominating
  ;; recovery's candidates by the global election would drop exactly those and the KB
  ;; would come back believing both spellings (docs/equality.md).
  (tu/with-terms [admires Kim Tango Yankee Zulu Xray CxVis CxHid]
    (v/assert kb (list 'genlCx CxVis 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxHid 'CxUniverse) 'CxUniverse)
    ;; Vis sees: Tango~Yankee and Yankee over Zulu  -> Vis elects Yankee
    (v/assert kb (list 'sameAs Tango Yankee)   CxVis)
    (v/assert kb (list 'rewriteOf Yankee Zulu) CxVis)
    ;; Hid alone sees Tango over Xray, which is what makes Tango the *global* head
    (v/assert kb (list 'rewriteOf Tango Xray)  CxHid)
    (v/assert kb (list admires Kim Tango) CxVis)
    (is (= Tango (v/representative kb Tango)) "Tango heads the class globally")
    (is (= Yankee (v/representative kb Tango CxVis)) "...and is retired inside Vis")
    (let [orig (v/handle-of kb (list admires Kim Tango) CxVis)
          twin (v/handle-of kb (list admires Kim Yankee) CxVis)]
      (is (some? twin))
      (is (not (v/in? kb orig)) "superseded before the restart")
      (let [kb2 (restart)]
        (v/recover kb2)
        (is (v/in? kb2 twin))
        (is (not (v/in? kb2 orig)) "and still superseded after it")
        (is (= [{'?x Yankee}] (v/query kb2 (list admires Kim '?x) CxVis))
            "so Vis reports the one fact once, in the name Vis elects")))))

(tu/deftest-kb recover-gives-a-rule-back-the-class-its-assertion-stated
  ;; A rule's premise strength is now the caller's to state, so it is a value that has
  ;; to survive a restart like a fact's.  The rebuild reads `premise-strength` per
  ;; stored premise and marks each at what it finds, so nothing here is rule-specific —
  ;; which is the claim, since a rebuild that re-marked rules at a constant would put
  ;; a known-true rule back defeasible and no read of the rule would say so.
  (tu/with-terms [bird flies]
    (let [rule (list 'implies (list bird '?x) (list flies '?x))
          h    (v/assert-rule kb [(list bird '?x)] (list flies '?x) 'CxUniverse
                              {:direction :forward :strength :monotonic})]
      (is (= :monotonic (:strength (v/sentex kb h))))
      (let [kb2 (restart)]
        (v/recover kb2)
        (is (= :monotonic (:strength (v/sentex kb2 h))) "the record came back with it")
        (is (true? (v/premise? kb2 h)) "and as a premise")
        (is (= :monotonic (v/defeat-class kb2 h)) "so the class reads back after the rebuild")
        (is (= h (v/handle-of kb2 rule 'CxUniverse)) "at the same handle")))))

(tu/deftest-kb recover-replays-an-inherited-firing-and-its-reasons
  ;; A firing that joined on an inherited claim rests on justifications like any
  ;; other, so the rebuild replays it — and its recorded reasons still carry
  ;; retraction afterwards, which is what makes the replay a belief and not a copy.
  (tu/with-terms [dog_t cat_t chihuahua_t maine_coon_t largerThan outweighs]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl chihuahua_t dog_t) 'CxUniverse)
      (v/assert kb (list 'genl maine_coon_t cat_t) 'CxUniverse)
      (v/assert kb (list 'transitiveInArg largerThan 1 'genl) 'CxUniverse)
      (v/assert kb (list 'transitiveInArg largerThan 2 'genl) 'CxUniverse)
      (v/assert kb (list largerThan dog_t cat_t) 'CxUniverse))
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y))
              'CxUniverse {:direction :forward})
    (let [goal (list outweighs chihuahua_t maine_coon_t)
          h    (v/handle-of kb goal 'CxUniverse)]
      (is (v/in? kb h))
      (let [kb2 (restart)]
        (v/recover kb2)
        (is (v/in? kb2 h) "the firing is IN again after the rebuild")
        (let [reasons (into #{}
                            (comp (mapcat :because) (map :sentence))
                            (:support (v/why kb2 h)))]
          (is (contains? reasons (list largerThan dog_t cat_t)))
          (is (contains? reasons (list 'genl chihuahua_t dog_t)))
          (is (contains? reasons (list 'transitiveInArg largerThan 1 'genl))))
        (testing "a post-recover retraction of a reason still withdraws it"
          (v/retract! kb2 (v/handle-of kb2 (list 'genl chihuahua_t dog_t) 'CxUniverse))
          (is (not (v/in? kb2 h))))))))

(tu/deftest-kb recover-rebuilds-the-rule-rosters
  ;; The two rosters `special/visibility-seeds` reads are derived from storage and no
  ;; store holds them, so a restart starts with neither.  Nothing above the rebuild puts
  ;; them back: recovery replays justifications and the stored special-predicate sentexes,
  ;; never rule *indexing*, which is where they are bumped.  Without the rebuild a
  ;; recovered KB reports no rules at all and seeds a post-restart `genlCx` edge with
  ;; none — arrival-order dependence in the machinery that exists to remove it.
  (tu/with-terms [bird flies departed alive CxAviary]
    (v/assert kb (list 'genlCx CxAviary 'CxUniverse) 'CxUniverse)
    (v/assert-rule kb [(list bird '?x)] (list flies '?x) CxAviary {:direction :forward})
    (v/assert-rule kb [(list 'not (list departed '?x)) (list bird '?x)]
                   (list alive '?x) CxAviary {:direction :forward})
    (let [live-antes @(reasoning/rule-antecedents kb)
          live-ctxs  @(reasoning/rule-contexts kb)]
      (testing "the live roster counts what arrived, negated antecedents by [:not pred]"
        (is (= 2 (get live-antes bird)))
        (is (= 1 (get live-antes [:not departed])))
        (is (= 2 (get live-ctxs CxAviary))))
      (let [kb2 (restart)]
        (v/recover kb2)
        (testing "a reopened KB's rosters are the live ones, entry for entry"
          (is (= live-antes @(reasoning/rule-antecedents kb2)))
          (is (= live-ctxs @(reasoning/rule-contexts kb2))))
        (testing "so the reads off them answer as they did before the restart"
          (is (= 2 (count (chain/rule-firing-report kb2))))
          (is (= (count (chain/rule-firing-report kb))
                 (count (chain/rule-firing-report kb2)))))))))

(tu/deftest-kb recover-skips-a-justification-that-rests-on-a-record-the-store-lost
  ;; A justification is the one thing a store can hold over a sentex it does not — a
  ;; `delete-sentex!` that left one behind, a foreign loader under no consistency
  ;; obligation — and `rebuild-tms` must leave such a justification out of the network
  ;; rather than believe a conclusion resting on a handle that names nothing.
  ;;
  ;; Storedness is read off the live-handle roster first and the record fetch is the
  ;; fallback, since a store rosters a handle only once the record is there.  That makes
  ;; the roster the fast answer and the fetch the one that settles a handle the roster does
  ;; **not** name — which is exactly this case, so it is the case worth pinning.
  (tu/with-terms [p1 q1 Ind]
    (v/assert-rule kb [(list p1 '?x)] (list q1 '?x) 'CxUniverse {:direction :forward})
    (v/assert kb (list p1 Ind) 'CxUniverse)
    (is (seq (v/sentexes-matching kb (list q1 Ind) 'CxUniverse)) "derived before the restart")
    (let [premise-h (v/handle-of kb (list p1 Ind) 'CxUniverse)]
      ;; the record goes, the justification that rests on it stays
      (p/delete-sentex! (:records kb) premise-h)
      (let [kb2 (restart)]
        (v/recover kb2)
        (testing "the conclusion is not believed — its justification rests on nothing"
          (is (empty? (v/sentexes-matching kb2 (list q1 Ind) 'CxUniverse))))
        (testing "and the premise itself is gone from the store"
          (is (nil? (p/get-sentex (:records kb2) premise-h))))))))

(tu/deftest-kb recover-roots-a-justification-whose-antecedents-are-all-stored
  ;; the mirror of the test above: the ordinary case still lands, so the short-circuit
  ;; above cannot be passing by skipping everything.
  (tu/with-terms [p1 q1 Ind]
    (v/assert-rule kb [(list p1 '?x)] (list q1 '?x) 'CxUniverse {:direction :forward})
    (v/assert kb (list p1 Ind) 'CxUniverse)
    (is (seq (v/sentexes-matching kb (list q1 Ind) 'CxUniverse)) "derived before the restart")
    (let [kb2 (restart)]
      (v/recover kb2)
      (let [h (v/handle-of kb2 (list q1 Ind) 'CxUniverse)]
        (is (v/in? kb2 h) "the conclusion is believed again after the restart")
        (is (seq (v/why kb2 h))
            "and it is supported by the justification the rebuild rooted")))))
