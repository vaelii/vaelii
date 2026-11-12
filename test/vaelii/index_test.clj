;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.index-test
  "Integration tests for the trie index and query path.  They run on the suite's
  scratch stores (db 15 = records, 14 = index) and clear them around each test."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.datetime :as dt]
            [vaelii.impl.kb]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.overlay.mount :as mount]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.types.dense-roots]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/empty-kb))

(tu/deftest-kb count-aware-trie
  (let [bornIn (tu/tmp-pred) tom (tu/tmp-ind) bob (tu/tmp-ind)
        paris (tu/tmp-ind) rome (tu/tmp-ind)]
    (v/assert kb (list bornIn tom paris) 'CxNaturalWorld)
    (v/assert kb (list bornIn bob paris) 'CxNaturalWorld)
    (v/assert kb (list bornIn tom rome)  'CxNaturalWorld)
    (testing "counts accumulate along shared prefixes"
      (is (= 3 (p/count-at (:index kb) [])))
      (is (= 3 (p/count-at (:index kb) [bornIn])))
      (is (= 2 (p/count-at (:index kb) [bornIn tom])))
      (is (= 1 (p/count-at (:index kb) [bornIn tom paris]))))
    (testing "and the width at a level is its own read, agreeing with the child set"
      ;; `reads/stored-count-children` is what the query planner's cost model divides by,
      ;; and it is asked once per literal per plan — so it answers off a cardinality rather than
      ;; by building the children (`perf`'s `plan-scaling` is the perf check on that).  The
      ;; two must not drift: a width that disagreed with the set it counts would make
      ;; the planner divide by a number the matcher never sees.
      (let [ix (:index kb)]
        (doseq [prefix [[] [bornIn] [bornIn tom] [bornIn bob]
                        ;; the key ends with the context, so a whole sentence is still an
                        ;; interior node — its children are the contexts it is stored in
                        [bornIn tom paris]
                        [bornIn tom paris 'CxNaturalWorld]  ; the leaf: no children
                        [bornIn tom paris 'CxUniverse]          ; absent: a real sentence,
                                                                 ; not in that context
                        [bornIn (tu/tmp-ind)]                    ; absent: no node at all
                        [(tu/tmp-pred)]]]
          (is (= (count (p/children ix prefix)) (reads/stored-count-children ix prefix))
              (pr-str prefix)))
        (is (= 2 (reads/stored-count-children ix [bornIn])))             ; tom and bob
        (is (= 2 (reads/stored-count-children ix [bornIn tom])))         ; paris and rome
        (is (= 1 (reads/stored-count-children ix [bornIn tom paris])))   ; the one context it is in
        (is (zero? (reads/stored-count-children ix [bornIn tom paris 'CxNaturalWorld])))
        (is (zero? (reads/stored-count-children ix [bornIn (tu/tmp-ind)])))))))

(tu/deftest-kb query-by-context-and-pattern
  (let [bornIn (tu/tmp-pred) tom (tu/tmp-ind) bob (tu/tmp-ind) paris (tu/tmp-ind)]
    (v/assert kb (list bornIn tom paris) 'CxNaturalWorld)
    (v/assert kb (list bornIn bob paris) 'CxNaturalWorld)
    (v/assert kb (list bornIn tom paris) 'CxUniverse)
    (testing "context wildcard returns every context"
      (is (= 2 (count (v/sentexes-matching kb (list bornIn tom paris))))))
    (testing "explicit context narrows results"
      (is (= 1 (count (v/sentexes-matching kb (list bornIn tom paris) 'CxUniverse)))))
    (testing "sentence variables fan out within a context"
      (is (= #{tom bob}
             (set (map (comp second :sentence) (v/sentexes-matching kb (list bornIn '?who paris) 'CxNaturalWorld))))))))

(tu/deftest-kb nested-terms-are-stable
  (let [nat (tu/tmp-pred) succ (tu/tmp-pred) z (tu/tmp-ind)]
    (v/assert kb (list nat (list succ z)) 'CxUniverse)
    (testing "a nested-term sentence round-trips and dedups"
      (is (= 1 (p/count-at (:index kb) [])))
      (is (= 1 (count (v/sentexes-matching kb (list nat (list succ z)) 'CxUniverse))))
      (v/assert kb (list nat (list succ z)) 'CxUniverse)         ; same fact again
      (is (= 1 (p/count-at (:index kb) []))))))            ; still one, not two

;; ---- secondary roots: context / functor / argument ----------------------

(tu/deftest-kb the-context-root-gives-extent-and-cardinality
  (let [p (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind)
        c1 (tu/tmp-ctx) c2 (tu/tmp-ctx)]
    (v/assert kb (list p a b) c1)
    (v/assert kb (list p b a) c1)
    (v/assert kb (list p a a) c2)
    (testing "a context's size is available without enumerating it"
      (is (= 2 (v/count-in-context kb c1)))
      (is (= 1 (v/count-in-context kb c2)))
      (is (= 0 (v/count-in-context kb (tu/tmp-ctx)))))
    (testing "and its extent is the sentexes actually asserted there"
      (is (= #{c1} (set (map :context (v/sentexes-in-context kb c1)))))
      (is (= 2 (count (v/sentexes-in-context kb c1)))))
    (testing "retracting a member decrements it"
      (v/retract! kb (v/handle-of kb (list p a a) c2))
      (is (= 0 (v/count-in-context kb c2))))))

(tu/deftest-kb the-predicate-extent-spans-arity-and-polarity
  (let [dog (tu/tmp-type) muffet (tu/tmp-ind) rex (tu/tmp-ind)
        rel (tu/tmp-pred)]
    (v/assert kb (list dog muffet) 'CxUniverse)
    (v/assert kb (list 'not (list dog rex)) 'CxUniverse)   ; negative fact
    (v/assert kb (list rel muffet rex) 'CxUniverse)
    (testing "both polarities count under the same functor"
      (is (= 2 (v/count-with-functor kb dog)))
      (is (= 2 (count (v/sentexes-with-functor kb dog)))))
    (testing "a different arity is its own functor entry"
      (is (= 1 (v/count-with-functor kb rel))))
    (testing "an unknown functor is simply empty"
      (is (= 0 (v/count-with-functor kb (tu/tmp-pred)))))
    (testing "the extent ends in the context: a scoped read keeps the facts stated there"
      (let [cx (tu/tmp-ctx)
            h  (v/assert kb (list dog rex) cx)]
        (is (= #{h} (set (p/sentexes-with-args (:index kb) dog [] #{cx}))))
        (is (= 2 (count (p/sentexes-with-args (:index kb) dog [] '#{CxUniverse}))))
        (is (= 3 (v/count-with-functor kb dog)))
        (v/retract! kb h)
        (is (= #{} (set (p/sentexes-with-args (:index kb) dog [] #{cx}))))
        (is (= 2 (v/count-with-functor kb dog)))))
    (testing "a rule is not a fact — it contributes no functor entry"
      (let [ante (tu/tmp-pred) conseq (tu/tmp-pred)]
        (v/assert-rule kb [(list ante '?x)] (list conseq '?x) 'CxUniverse {:direction :forward})
        (is (= 0 (v/count-with-functor kb conseq)))))))

(tu/deftest-kb the-arity-bindings-follow-the-stored-binding-facts
  ;; each spelling of a binding posts its `[kind value]` under its predicate, by context;
  ;; a kind leaves with its last fact and a predicate with its last kind
  (tu/with-terms [fooOf barOf CxA CxB]
    (let [idx   (:index kb)
          M     {:strength :monotonic}
          kinds #(reads/as-stored-arity-binding-kinds idx %)
          bound #(into #{} (filter #{fooOf barOf}) (reads/as-stored-arity-bound idx))
          b1 (v/assert kb (list 'binary_predicate fooOf) CxA M)
          b2 (v/assert kb (list 'arity fooOf 2) CxB M)
          m  (v/assert kb (list 'arityMin barOf 2) CxA M)
          va (v/assert kb (list 'variable_arity barOf) CxA M)]
      (v/assert kb (list 'not (list 'arity barOf 3)) CxA M)
      (is (= #{[:exact 2]} (kinds fooOf)) "two spellings of one length are one kind")
      (is (= #{[:min 2] [:var nil]} (kinds barOf)) "a negation binds nothing")
      (is (= #{fooOf barOf} (bound)))
      (is (= #{[b1 :exact 2 CxA] [b2 :exact 2 CxB]}
             (set (reads/as-stored-arity-bindings-global idx fooOf))))
      (is (= [[b2 :exact 2 CxB]] (reads/as-stored-arity-bindings idx fooOf #{CxB}))
          "a read keeps the contexts it is given")
      (v/retract! kb b1)
      (is (= #{[:exact 2]} (kinds fooOf)) "the kind stays while a fact states it")
      (v/retract! kb b2)
      (is (= #{} (kinds fooOf)))
      (is (= #{barOf} (bound)) "the predicate leaves with its last kind")
      (v/retract! kb va)
      (is (= #{[:min 2]} (kinds barOf)))
      (v/retract! kb m)
      (is (= #{} (bound))))))

(tu/deftest-kb the-kept-terms-by-type-follow-the-unary-predicate-set
  ;; `[:unary-kept t]` lists a term under each predicate of its unary predicate set while the
  ;; set lists two or more, in either polarity; one predicate in two contexts is one
  (tu/with-terms [dog cat pet Rex Tom CxA CxB]
    (let [idx  (:index kb)
          ts   #{dog cat pet}
          kept (fn [] (into {} (keep (fn [t] (let [xs (reads/as-stored-unary-kept-terms idx t)]
                                               (when (seq xs) [t xs]))))
                            ts))
          listed #(into #{} (filter ts) (reads/as-stored-unary-kept-types idx))
          a    (fn [s c] (v/assert kb s c))
          rd   (a (list dog Rex) CxA)
          _    (is (= {} (kept)) "one predicate keeps no term")
          rc   (a (list cat Rex) CxA)
          _    (is (= {dog #{Rex} cat #{Rex}} (kept)))
          rp   (a (list pet Rex) CxB)
          rd2  (a (list dog Rex) CxB)
          _    (is (= {dog #{Rex} cat #{Rex} pet #{Rex}} (kept)))
          tn   (a (list 'not (list cat Tom)) CxA)
          td   (a (list dog Tom) CxA)]
      (is (= {dog #{Rex Tom} cat #{Rex Tom} pet #{Rex}} (kept)) "a denial lists its type")
      (is (= ts (listed)))
      (v/retract! kb rc)
      (is (= {dog #{Rex Tom} cat #{Tom} pet #{Rex}} (kept)) "a third predicate leaving takes one entry")
      (v/retract! kb rp)
      (is (= {dog #{Tom} cat #{Tom}} (kept)) "the second leaving takes the term out under both")
      (is (= #{dog cat} (listed)))
      (doseq [h [rd rd2 tn td]] (v/retract! kb h))
      (is (= {} (kept)))
      (is (= #{} (listed))))))

(tu/deftest-kb the-denied-terms-by-type-follow-the-stored-denials
  ;; `[:unary-denied t]` lists a term while a `(not (t term))` is stored in any context
  (tu/with-terms [dog cat Rex Tom CxA CxB]
    (let [idx    (:index kb)
          ts     #{dog cat}
          denied (fn [] (into {} (keep (fn [t] (let [xs (reads/as-stored-unary-denied-terms idx t)]
                                                 (when (seq xs) [t xs]))))
                              ts))
          listed #(into #{} (filter ts) (reads/as-stored-unary-denied-types idx))
          a      (fn [s c] (v/assert kb s c))
          da     (a (list 'not (list dog Rex)) CxA)
          db     (a (list 'not (list dog Rex)) CxB)
          tc     (a (list 'not (list cat Tom)) CxA)
          td     (a (list dog Tom) CxA)]
      (is (= {dog #{Rex} cat #{Tom}} (denied)) "a membership lists nothing")
      (is (= ts (listed)))
      (v/retract! kb da)
      (is (= {dog #{Rex} cat #{Tom}} (denied)) "a denial in another context keeps the term")
      (v/retract! kb db)
      (is (= {cat #{Tom}} (denied)))
      (is (= #{cat} (listed)))
      (doseq [h [tc td]] (v/retract! kb h))
      (is (= {} (denied)))
      (is (= #{} (listed))))))

(tu/deftest-kb the-opposed-bodies-by-functor-follow-the-opposed-bodies
  ;; `[:opposed-between f]` and `[:opposed-functor f]` split the opposed bodies of `f` by
  ;; `nm/between-predicates?`, and the two reads answer as a scan of every opposed body does
  (tu/with-terms [relatesTo parentOf Ann Bob CxA CxB]
    (let [idx      (:index kb)
          ;; `tu/with-terms` folds a predicate temp to bare lowercase, a type's spelling
          [fatherOf kinOf] (map #(gensym (str "tmp" %)) ["FatherOf" "KinOf"])
          fs       #{relatesTo parentOf}
          filed    (fn [tag] (into {} (keep (fn [f] (let [bs (p/family-leaf idx tag [f])]
                                                      (when (seq bs) [f bs]))))
                                   fs))
          scanned  #(into #{} (filter (comp fs first)) (reads/as-stored-opposed-bodies idx))
          agrees?  #(and (= (scanned) (into #{} cat [(mapcat val (filed :opposed-functor))
                                                     (mapcat val (filed :opposed-between))]))
                         (every? (fn [f] (= (boolean (some (fn [b] (= f (first b))) (scanned)))
                                            (reads/stores-opposed-with-functor? idx f)))
                                 fs))
          between  (list relatesTo fatherOf kinOf)
          mixed    (list relatesTo fatherOf Ann)
          fact     (list parentOf Ann Bob)
          a        (fn [s c] (v/assert kb s c))
          hs       (mapv #(a % CxA) [between mixed fact])
          _        (is (= {} (filed :opposed-functor) (filed :opposed-between)) "one polarity files nothing")
          ns1      (mapv #(a (list 'not %) CxB) [between mixed fact])]
      (is (= {relatesTo #{mixed} parentOf #{fact}} (filed :opposed-functor)))
      (is (= {relatesTo #{between}} (filed :opposed-between)))
      (is (reads/stores-opposed-between? idx relatesTo))
      (is (not (reads/stores-opposed-between? idx parentOf)))
      (is (agrees?))
      (let [ns2 (a (list 'not between) CxA)]
        (v/retract! kb (first ns1))
        (is (= {relatesTo #{between}} (filed :opposed-between)) "a denial in another context keeps the body")
        (v/retract! kb ns2))
      (is (= {} (filed :opposed-between)) "the last denial takes the body out")
      (is (not (reads/stores-opposed-between? idx relatesTo)))
      (v/retract! kb (nth hs 2))
      (is (= {relatesTo #{mixed}} (filed :opposed-functor)) "the last positive takes the body out")
      (is (agrees?))
      (doseq [h (into [(first hs) (second hs)] (rest ns1))] (v/retract! kb h))
      (is (= {} (filed :opposed-functor) (filed :opposed-between)))
      (is (not (reads/stores-opposed-with-functor? idx relatesTo))))))

(tu/deftest-kb the-argument-root-discriminates-by-position
  (let [bornIn (tu/tmp-pred) likes (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind) paris (tu/tmp-ind)]
    (v/assert kb (list bornIn tom paris) 'CxUniverse)
    (v/assert kb (list bornIn bob paris) 'CxUniverse)
    (v/assert kb (list likes paris tom) 'CxUniverse)
    (testing "position 2 and position 1 are distinct entries for the same term"
      (is (= 2 (v/count-with-arg kb 2 paris)))          ; born in Paris, twice
      (is (= 1 (v/count-with-arg kb 1 paris))))         ; Paris likes Tom, once
    (testing "the extent holds exactly the sentexes with that term at that position"
      (is (= 1 (count (v/sentexes-with-arg kb 1 tom))))
      (is (= 1 (count (v/sentexes-with-arg kb 2 tom)))))
    (testing "bob only ever appears in position 1"
      (is (= 1 (v/count-with-arg kb 1 bob)))
      (is (= 0 (v/count-with-arg kb 2 bob))))
    (testing "a position nothing occupies, and an unseen term, are both empty"
      (is (= 0 (v/count-with-arg kb 3 paris)))
      (is (= 0 (v/count-with-arg kb 1 (tu/tmp-ind)))))))

;; ---- rule predicate indexes are complete; direction is filtered at use --

;; ---- the set/*Rule wrappers canonicalize into the record ----------------

(tu/deftest-kb a-rule-wrapper-sets-the-direction-on-the-sentex
  (tu/with-terms [p q]
    (testing "a bare implies is backward by default"
      (let [h (v/assert kb (list 'implies (list p '?x) (list q '?x)) 'CxUniverse)]
        (is (= #{:backward} (:engines (v/sentex kb h))))
        (is (nil? (:defeasible (v/sentex kb h))))))))

(tu/deftest-kb each-wrapper-lands-on-the-record
  (doseq [[wrapper expected] '{set/forwardRule  #{:forward :backward}
                               set/backwardRule #{:backward}
                               set/inertRule    #{}}]
    (tu/with-terms [p q]
      (let [h (v/assert kb (list wrapper (list 'implies (list p '?x) (list q '?x)))
                        'CxUniverse)
            s (v/sentex kb h)]
        (testing (str wrapper " sets :engines " expected)
          (is (= expected (:engines s))))
        (testing "and the wrapper itself is not stored — the sentence is the bare rule"
          (is (= 'implies (first (v/sentence-of s))))
          (is (some? (:antecedent s))))))))

(tu/deftest-kb the-default-wrapper-sets-defeasible-on-the-record
  (tu/with-terms [bird flies Tweety]
    (let [h (v/assert kb (list 'set/defaultRule
                               (list 'set/forwardRule (list 'implies (list bird '?x) (list flies '?x))))
                      'CxUniverse)
          s (v/sentex kb h)]
      (is (true? (:defeasible s)))
      (is (= 'implies (first (v/sentence-of s))))
      (testing "and it still behaves as a default — the conclusion is defeasible"
        (v/assert kb (list bird Tweety) 'CxUniverse)
        (is (seq (v/sentexes-matching kb (list flies Tweety) 'CxUniverse)))
        (v/assert kb (list 'not (list flies Tweety)) 'CxUniverse
                  {:strength :monotonic})
        (is (empty? (v/sentexes-matching kb (list flies Tweety) 'CxUniverse)))))))

(tu/deftest-kb the-direction-opt-is-the-same-thing-as-a-wrapper
  (tu/with-terms [p q r]
    (let [viaOpt  (v/assert-rule kb [(list p '?x)] (list q '?x)
                                 'CxUniverse {:direction :backward})
          viaWrap (v/assert kb (list 'set/backwardRule
                                     (list 'implies (list p '?x) (list r '?x)))
                            'CxUniverse)]
      (is (= #{:backward} (:engines (v/sentex kb viaOpt))))
      (is (= #{:backward} (:engines (v/sentex kb viaWrap)))))))

(tu/deftest-kb direction-lives-only-on-the-record
  (tu/with-terms [p q]
    (let [h (v/assert kb (list 'set/forwardRule
                               (list 'implies (list p '?x) (list q '?x)))
                      'CxUniverse)
          s (v/sentex kb h)]
      (testing "the record answers both directions — set/forwardRule is forward + backward"
        (is (rules/forward-sentex? s))
        (is (rules/backward-sentex? s)))
      (testing "and the rule index carries predicates only — no direction mirror"
        (is (contains? (reads/as-stored-rules-by-antecedent-global (:index kb) p) h))
        (is (contains? (reads/as-stored-rules-by-consequent-global (:index kb) q) h))))))

(tu/deftest-kb a-re-asserted-wrapper-resolves-the-record-slot
  ;; One sentex, because direction is not in the identity key — the second assert
  ;; resolves to the existing record.  Which direction that record then holds is decided
  ;; from the two claims rather than from which arrived first, so the pair commutes.
  (tu/with-terms [p q]
    (let [rule (list 'implies (list p '?x) (list q '?x))
          h1   (v/assert kb (list 'set/forwardRule rule) 'CxUniverse)
          h2   (v/assert kb (list 'set/backwardRule rule) 'CxUniverse)]
      (is (= h1 h2))
      (is (= #{:forward :backward} (:engines (v/sentex kb h1)))))))

(tu/deftest-kb rule-predicate-indexes-are-complete-in-both-directions
  (let [p (tu/tmp-pred) q (tu/tmp-pred)]
    (let [fwd (v/assert-rule kb [(list p '?a)] (list q '?a)
                             'CxUniverse {:direction :forward-only})]
      (testing "a forward-only rule is still findable by what it concludes"
        (is (contains? (reads/as-stored-rules-by-consequent-global (:index kb) q) fwd))
        (is (contains? (reads/as-stored-rules-by-antecedent-global (:index kb) p) fwd)))
      (testing "and its direction is on its own record, not inferred from the index"
        (let [s (v/sentex kb fwd)]
          (is (= #{:forward} (:engines s)))
          (is (rules/forward-sentex? s))
          (is (not (rules/backward-sentex? s))))))))

(tu/deftest-kb a-backward-only-rule-does-not-forward-fire
  ;; the antecedent index is now complete, so forward chaining must filter on the
  ;; recorded direction — otherwise a backward/inert rule would start firing.
  (let [p (tu/tmp-pred) q (tu/tmp-pred) x (tu/tmp-ind)]
    (v/assert-rule kb [(list p '?a)] (list q '?a) 'CxUniverse {:direction :backward})
    (v/assert kb (list p x) 'CxUniverse)
    (v/forward-chain kb)
    (testing "forward chaining does not materialize its conclusion"
      (is (empty? (v/sentexes-matching kb (list q x) 'CxUniverse))))
    (testing "but it is still provable backward"
      (is (v/provable? kb (list q x) 'CxUniverse)))))

(tu/deftest-kb an-inert-rule-fires-in-neither-direction
  (let [p (tu/tmp-pred) q (tu/tmp-pred) x (tu/tmp-ind)]
    (v/assert-rule kb [(list p '?a)] (list q '?a) 'CxUniverse {:direction :inert})
    (v/assert kb (list p x) 'CxUniverse)
    (v/forward-chain kb)
    (is (empty? (v/sentexes-matching kb (list q x) 'CxUniverse)))
    (is (not (v/provable? kb (list q x) 'CxUniverse)))))

;; ---- the exception re-check index ---------------------------------------
;;
;; Rule granularity, and no truth value: it answers "which rules might need
;; re-checking", never "does the exception hold".  The predicates are passed in
;; rather than read off the rule, so these drive the protocol directly with handles
;; standing in for rules — what the index stores is a handle either way.

(tu/deftest-kb an-exception-is-posted-under-every-predicate-it-mentions
  (tu/with-terms [flightless_bird adult]
    (let [idx (:index kb) h 4001]
      (rules/index-exception idx h [flightless_bird adult])
      (testing "the rule is findable from each predicate its exception mentions"
        (is (contains? (reads/watched-rules-on idx flightless_bird) h))
        (is (contains? (reads/watched-rules-on idx adult) h)))
      (testing "and lands in the watched-rule set the taxonomy trigger enumerates"
        (is (contains? (reads/watched-rules idx) h))))))

(tu/deftest-kb the-watched-rule-set-accumulates-across-rules
  (tu/with-terms [penguin ostrich]
    (let [idx (:index kb) h1 4002 h2 4003]
      (rules/index-exception idx h1 [penguin])
      (rules/index-exception idx h2 [ostrich])
      (is (= #{h1 h2} (reads/watched-rules idx)))
      (testing "handles keep their type through nippy — ints, not strings"
        (is (every? integer? (reads/watched-rules idx)))))))

(tu/deftest-kb unindexing-clears-every-predicate-key-and-the-watched-rule-set
  (tu/with-terms [flightless_bird adult]
    (let [idx (:index kb) h 4004]
      (rules/index-exception idx h [flightless_bird adult])
      (rules/unindex-exception! idx h [flightless_bird adult])
      (is (empty? (reads/watched-rules-on idx flightless_bird)))
      (is (empty? (reads/watched-rules-on idx adult)))
      (is (empty? (reads/watched-rules idx))))))

(tu/deftest-kb a-predicate-no-exception-mentions-is-empty
  (tu/with-terms [penguin sickChild]
    (let [idx (:index kb)]
      (testing "an index with nothing registered answers empty, not nil"
        (is (= #{} (reads/watched-rules-on idx penguin)))
        (is (= #{} (reads/watched-rules idx))))
      (rules/index-exception idx 4005 [penguin])
      (testing "and a predicate no exception mentions stays empty"
        (is (= #{} (reads/watched-rules-on idx sickChild)))))))

(tu/deftest-kb two-rules-can-share-an-exception-predicate
  ;; the set-membership case: unindexing one must not DEL the shared key and take
  ;; the other rule's registration with it.
  (tu/with-terms [penguin adult]
    (let [idx (:index kb) h1 4006 h2 4007]
      (rules/index-exception idx h1 [penguin adult])
      (rules/index-exception idx h2 [penguin])
      (testing "both are found under the shared predicate"
        (is (= #{h1 h2} (reads/watched-rules-on idx penguin))))
      (rules/unindex-exception! idx h1 [penguin adult])
      (testing "removing one leaves the other reachable"
        (is (= #{h2} (reads/watched-rules-on idx penguin)))
        (is (= #{h2} (reads/watched-rules idx))))
      (testing "and the predicate only the removed rule mentioned is now empty"
        (is (empty? (reads/watched-rules-on idx adult)))))))

(tu/deftest-kb unindex-cleans-up
  (let [bornIn (tu/tmp-pred) tom (tu/tmp-ind) paris (tu/tmp-ind)
        h (v/assert kb (list bornIn tom paris) 'CxNaturalWorld)
        s (assoc (sx/sentex (list bornIn tom paris) 'CxNaturalWorld) :id h)]
    (is (= 1 (p/count-at (:index kb) [])))
    (p/unindex-sentex! (:index kb) s h)
    (is (= 0 (p/count-at (:index kb) [])))
    (is (empty? (v/sentexes-matching kb (list bornIn tom paris) 'CxNaturalWorld)))))

;; ---- the family registry ------------------------------------------------

(deftest every-key-the-starter-writes-names-a-registry-row-with-a-class
  ;; Its own memory KB, whatever backend the suite runs on: the registry is the key
  ;; shapes `KvIndexStore` writes, and `index-entries` on the memory store is that map.
  (let [kb   (doto (v/open-kb {:backend :memory :space [::families] :recover? false})
               (tu/clear-kb!)
               (tu/load-starter!))
        tags (into #{} (map (comp first key)) (p/index-entries (:index kb)))]
    (is (< 10 (count tags)))
    (is (empty? (remove kv/index-families tags)) "a family the registry lacks")
    (doseq [[tag row] kv/index-families]
      (is (#{:access-path :scan-recoverable :sole-witness} (:class row)) (str tag))
      (is (map? (:class-evidence row)) (str tag))
      (when-let [r (:root row)] (is (contains? kv/index-families r) (str tag " root " r)))
      (doseq [t (get-in row [:class-evidence :oracle])]
        (is (requiring-resolve t) (str tag "'s oracle " t))))
    (is (every? #(seq (get-in kv/index-families [% :class-evidence :oracle]))
                (keep (fn [[tag row]] (when (= :access-path (:class row)) tag)) kv/index-families)))
    (is (empty? (remove kv/index-families (keys @#'vaelii.impl.types.dense-roots/routes)))
        "the columnar roots route a family the registry lacks")
    (tu/clear-kb! kb)))

(defn- named-reading
  "`[rel functor family trie]` per relation and naming functor (`except`, `defeat`): the `:tax-named` entries
  `[ctx handle]` the family holds, and those the naming trie and the installed keys give."
  [kb]
  (let [ix (:index kb)]
    (for [rel [:genl :genlCx :flat] f '[except defeat]]
      [rel f
       (into #{} (mapcat (fn [c] (map #(vector c %) (p/family-leaf ix :tax-named [rel f c]))))
             (p/family-children ix :tax-named [rel f] p/every-context))
       (into #{} (for [h (reads/as-stored-named-global ix f)
                       :when (some #(= rel (kv/key-relation %)) (reads/as-stored-installed-keys ix h))
                       [c hs] (reads/as-stored-naming-by-context ix f h)
                       n hs]
                   [c n]))])))

(tu/deftest-kb the-named-supporter-family-agrees-with-the-naming-trie
  ;; The family is written from both sides: the naming fact's index write reads its
  ;; target's installed keys, and the taxonomy's supporter post and retire read the naming
  ;; facts.  The orphaned except covers the retire side, and `reindex`, which indexes every
  ;; record before it posts the supporters, the post side.
  (tu/with-terms [gn_a gn_b gn_c gn_d GnX]
    (let [ix      (:index kb)
          cx      'CxNaturalWorld
          agrees? (fn [label]
                    (doseq [[rel f fam trie] (named-reading kb)]
                      (is (= trie fam) (str label ", " rel " " f))))
          ex      #(v/assert kb (list 'except (sx/sentex-handle %)) cx)
          edge    (v/assert kb (list 'genl gn_a gn_b) cx)
          member  (v/assert kb (list gn_a GnX) cx)
          x-edge  (ex edge)]
      (ex member)
      (v/assert kb (list 'genl gn_c gn_d) cx)
      (v/assert kb (list 'not (list 'genl gn_c gn_d)) cx {:strength :monotonic})
      (agrees? "asserted")
      (is (contains? (p/family-leaf ix :tax-named [:genl 'except cx]) x-edge))
      (is (pos? (reads/stored-count-named-supporters-global ix :genl 'defeat)))
      (v/retract! kb edge)
      (agrees? "the except's target retracted")
      (is (not (contains? (p/family-leaf ix :tax-named [:genl 'except cx]) x-edge)))
      (v/reindex kb)
      (agrees? "reindexed"))))

(tu/deftest-kb the-mint-rule-family-agrees-with-the-trie
  ;; The family's other path is the trie's exact leaf of each rule of `kv/mint-rules`.  A
  ;; fresh KB stores `arg`'s rule with its first `arg` declaration.
  (tu/with-terms [animal parentOf CxWorld]
    (let [trie    #(into {} (keep (fn [[k r]] (when-let [h (v/handle-of kb r kv/mint-rule-context)] [k h])))
                         kv/mint-rules)
          agrees? (fn [label] (is (= (trie) (into {} (reads/as-stored-mint-rules (:index kb)))) label))]
      (agrees? "a fresh KB")
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
      (is (contains? (trie) 'arg))
      (agrees? "asserted")
      (v/reindex kb)
      (agrees? "reindexed"))))

(tu/deftest-kb the-calendar-family-agrees-with-a-scan-of-the-records
  ;; The family's other path is `datetime/month-buckets` over every stored fact, keyed by
  ;; its functor.  A range enters the month of each end, and a retraction takes a month no
  ;; other fact of the functor names out of the functor's months.
  (tu/with-terms [visited attended Ann CxWorld]
    (let [ix      (:index kb)
          facts   #(for [h (p/sentex-ids (:records kb))
                         :let [sx (p/get-sentex (:records kb) h)]
                         :when (nil? (:antecedent sx))]
                     [h (sx/body sx)])
          scan    #(apply merge-with into
                          (for [[h b] (facts), [frame y m] (dt/month-buckets b)]
                            {[(first b) frame y m] #{h}}))
          family  #(into {} (for [f (distinct (map (comp first second) (facts)))
                                  [frame y m :as b] (reads/as-stored-calendar-buckets ix f)]
                              [[f frame y m] (set (reads/as-stored-calendar-at-global ix f b))]))
          agrees? (fn [label] (is (= (scan) (family)) label))
          range-h (v/assert kb (list visited Ann (list 'DatetimeRangeFn "1999-12" "2000-02")) CxWorld)]
      (v/assert kb (list visited Ann '(InstantFn 2000 1 15 12 0 0)) CxWorld)
      (v/assert kb (list attended Ann '(InstantFn 1999 12 24 12 0 0)) CxWorld)
      (is (= #{[:local 1999 12] [:local 2000 3]}
             (set (filter #(contains? (set (reads/as-stored-calendar-at-global ix visited %)) range-h)
                          (reads/as-stored-calendar-buckets ix visited)))))
      (agrees? "asserted")
      (v/retract! kb range-h)
      (is (= [false true] (map #(contains? (reads/as-stored-calendar-buckets ix %) [:local 1999 12])
                               [visited attended])))
      (agrees? "the range retracted")
      (v/reindex kb)
      (agrees? "reindexed"))))

(tu/deftest-kb the-nat-argument-family-agrees-with-the-term-index
  ;; The family's other path is the term index on each function, filtered by the record to
  ;; that function's positive `natFormula` maps.  A number, a string and a negated map enter
  ;; no node, so the probes of those nodes read nothing on both sides.
  (tu/with-terms [Ann Bob CxMonad CxNamed CxOther CxStory PairFn]
    (let [ix      (:index kb)
          slice   (symbol (str (tu/tmp-ctx "Slice") "Fn"))
          scan    #(apply merge-with into {}
                          (for [f [slice PairFn], h (reads/as-stored-with-term ix f)
                                :let [s (:sentence (p/get-sentex (:records kb) h)) e (nth s 2 nil)]
                                :when (and (seq? s) (= 'natFormula (first s)) (sequential? e) (= f (first e)))
                                [i a] (map-indexed vector (rest e))
                                :when (sx/indexable-term? a)]
                            {[f (inc i) a] #{h}}))
          probes  (atom [[slice 1 Bob] [slice 2 '(DatetimeFn "2002")] [PairFn 2 3] [PairFn 3 "s"]])
          stated  #{'CxUniverse CxStory}
          family  #(into {} (for [[f i a :as node] @probes
                                  :let [n (reads/stored-count-nat-formulas-at ix f i a stated)]
                                  :when (pos? n)]
                              [node [n (set (reads/as-stored-nat-formulas-at ix f i a stated))]]))
          agrees? (fn [label]
                    (let [want (update-vals (scan) #(vector (count %) %))]
                      (swap! probes into (keys want))
                      (is (= want (family)) label)))
          named   (v/assert kb (list 'natFormula CxNamed (list slice CxMonad '(DatetimeFn "2000"))) 'CxUniverse)]
      (v/assert kb (list 'natFormula CxOther (list slice CxMonad '(DatetimeFn "2001"))) CxStory)
      (v/assert kb (list 'natFormula Ann (list PairFn Bob 3 "s")) 'CxUniverse)
      (v/assert kb (list 'not (list 'natFormula Bob (list slice Bob '(DatetimeFn "2002")))) 'CxUniverse)
      (is (= #{named} (set (reads/as-stored-nat-formulas-at ix slice 2 ['DatetimeFn "2000"] stated))))
      (is (zero? (reads/stored-count-nat-formulas-at ix slice 2 '(DatetimeFn "2001") #{'CxUniverse})))
      (agrees? "asserted")
      (v/retract! kb named)
      (is (zero? (reads/stored-count-nat-formulas-at ix slice 2 '(DatetimeFn "2000") stated)))
      (agrees? "a map retracted")
      (v/reindex kb)
      (agrees? "reindexed"))))

;; ---- the family methods ---------------------------------------------------

(defmacro ^:private delegating-index
  "A `reify` of every `IndexStore` method, each forwarding to `target`: an implementer
  that reaches the index through the protocol alone."
  [target]
  (let [t (gensym "target")]
    `(let [~t ~target]
       (reify p/IndexStore
         ~@(for [{:keys [name arglists]} (vals (:sigs p/IndexStore))
                 args arglists
                 :let [params (into ['_] (map #(gensym (str %))) (rest args))]]
             `(~name ~params (~(symbol "vaelii.impl.protocols" (str name)) ~t ~@(rest params))))))))

(defn- family-reading
  "What the starter KB in `kb` answers for the taxonomy, the mints and the supporters."
  [kb]
  (let [ix    (:index kb)
        recs  (:records kb)
        edges (keep #(let [s (:sentence (p/get-sentex recs %))]
                       (when (and (seq? s) (= 3 (count s))) (vec (rest s))))
                    (reads/as-stored-with-functor ix 'genl))]
    {:edges      (count edges)
     :genls      (into {} (map (fn [[a _]] [a (v/genls kb a)])) edges)
     :mint-terms (reads/as-stored-mint-terms ix)
     :supporters (into {} (map (fn [[a b]] [[a b] (set (keys (reads/as-stored-supporters-global ix [:genl a b])))]))
                       edges)}))

(deftest an-index-store-reached-through-the-protocol-answers-the-families
  ;; Two memory KBs of their own, whatever backend the suite runs on: one over the
  ;; `KvIndexStore` the memory arm builds, one over a `reify` delegating every protocol
  ;; method to it, so no code can reach the store past the protocol.
  (let [arms    @#'vaelii.impl.kb/index-arms
        open    (fn [space wrap]
                  (with-redefs-fn {#'vaelii.impl.kb/index-arms
                                   (update arms :memory (fn [arm] (fn [o s] (wrap (arm o s)))))}
                    #(doto (v/open-kb {:backend :memory :space space :recover? false})
                       (tu/clear-kb!))))
        plain   (open [::plain] identity)
        wrapped (open [::wrapped] #(delegating-index %))]
    (try
      ;; The starter dump holds mints only under the entailing reading, so the dump both KBs
      ;; import adds one declared fact asserted under it, and the mint-terms row is
      ;; non-empty in every sweep.  The pair is asserted before the import: an assert into
      ;; `wrapped` runs a taxonomy probe, which refuses its store.
      (let [dump (tu/with-terms [rel big_thing Ann Bob]
                   (#'tu/build-dump "vaelii-index-families-"
                                    (assoc tu/starter-build-space :space [::dump])
                                    (fn [kb]
                                      (tu/load-starter! kb)
                                      (tu/with-entailing
                                        (v/assert kb (list 'arg rel 1 big_thing) 'CxUniverse)
                                        (v/assert kb (list rel Ann Bob) 'CxUniverse)))))]
        (doseq [kb [plain wrapped]] (v/import! kb dump {:belief? true})))
      (let [want (family-reading plain)]
        (is (pos? (:edges want)))
        (is (seq (:mint-terms want)))
        (is (= want (family-reading wrapped)))
        (is (= :unforkable-index
               (try (mount/fork-families (:index wrapped)) nil
                    (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))
            "a taxonomy probe refuses a store keeping no family backend"))
      (finally (tu/clear-kb! plain) (tu/clear-kb! wrapped)))))

(tu/deftest-kb the-family-methods-answer-each-shape-alike-on-every-backend
  ;; Each configuration the matrix selects (the nine backends and the overlay) runs this
  ;; table against the same literal answers, so the configurations agree on it.
  (tu/with-terms [rel Tom Ann CxA CxB]
    (let [ix (:index kb)
          E  p/every-context
          h1 (v/assert kb (list rel Tom Ann) CxA)
          h2 (v/assert kb (list rel Tom Tom) CxB)
          h3 (v/assert kb (list rel Ann Tom) CxA)
          as (fn [x] (if (coll? x) (set x) x))]
      (doseq [[read want]
              [[[:family-count :trie [rel] E] 3]
               [[:family-count :trie [rel Tom] E] 2]
               [[:family-count :trie [rel Tom Ann] #{CxA CxB}] 1]
               [[:family-children :trie [rel] E] #{Tom Ann}]
               [[:family-child-count :trie [rel]] 2]
               [[:family-leaf :trie [rel Tom Ann CxA]] #{h1}]
               [[:family-member? :trie [rel Tom Ann CxA] h1] true]
               [[:family-handles :trie [rel Tom Ann] #{CxA CxB}] #{h1}]
               [[:family-count :predicate-extent [rel] E] 3]
               [[:family-count :predicate-extent [rel] #{CxA}] 2]
               [[:family-children :predicate-extent [rel] E] #{CxA CxB}]
               [[:family-children :predicate-extent [rel] #{CxB}] #{CxB}]
               [[:family-child-count :predicate-extent [rel]] 2]
               [[:family-leaf :predicate-extent [rel CxA]] #{h1 h3}]
               [[:family-member? :predicate-extent [rel CxB] h2] true]
               [[:family-handles :predicate-extent [rel] #{CxA}] #{h1 h3}]
               [[:family-handles :predicate-extent [rel] E] #{h1 h2 h3}]
               [[:family-count :argument-root [rel 1 Tom] E] 2]
               [[:family-handles :argument-root [rel 2 Tom] E] #{h2 h3}]
               [[:family-handles :self-tuple [rel] E] #{h2}]
               [[:family-leaf :argument-slot [1 Tom]] #{rel}]
               [[:family-member? :argument-slot [2 Ann] rel] true]
               [[:family-child-count :argument-slot [1 Tom]] 1]
               [[:family-count :argument-slot [1 Tom] E] 1]
               [[:family-leaf :context-root [CxA]] #{h1 h3}]
               [[:family-handles :context-root [] #{CxA CxB}] #{h1 h2 h3}]
               [[:family-count :context-root [] #{CxA CxB}] 3]
               [[:family-count :shape-tuple [rel 2] E] 3]
               [[:family-handles :shape-tuple [rel 2] #{CxB}] #{h2}]
               [[:family-leaf :shape-lengths [rel]] #{2}]
               [[:family-leaf :term-index [Ann]] #{h1 h3}]
               [[:family-member? :term-names [] Ann] true]]]
        (is (= want (as (apply (ns-resolve 'vaelii.impl.protocols (symbol (name (first read))))
                               ix (rest read))))
            (pr-str read)))
      (doseq [m [#(p/family-count ix :predicate-extent [rel] nil)
                 #(p/family-children ix :trie [rel] nil)
                 #(p/family-handles ix :argument-root [rel 1 Tom] nil)]]
        (is (= :bad-args (try (m) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))
            "nil is never every context"))
      (is (= [true true false false]
             (map #(set? (apply p/family-children ix %))
                  [[:trie [rel] E] [:predicate-extent [rel] E]
                   [:trie [rel] #{CxA}] [:predicate-extent [rel] #{CxA}]]))
          "every context answers a set, a context set a vector")
      (is (= :bad-args
             (try (p/family-apply! ix [[:retire :context-root [p/any-context] h1]]) nil
                  (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))
          "a flat set's retire names its context"))))

(defn- family-state
  "What a `:mint` leaf under `t` in `c` and its node and root set, and the `:tax-installs`
  set of `h`, hold."
  [ix t c h]
  {:leaf     (p/family-leaf ix :mint [t c])
   :count    (p/family-count ix :mint [t] p/every-context)
   :children (set (p/family-children ix :mint [t] p/every-context))
   :root     (p/family-member? ix :mint-terms [] t)
   :installs (into #{} (map #(if (= t %) :t %)) (p/family-leaf ix :tax-installs [h]))})

(tu/deftest-kb a-family-batch-equals-its-ops-applied-one-at-a-time
  ;; Every pair and triple of post, retire and a retire from any context of one handle on
  ;; one count-trie leaf and one flat set, from three starting states, applied as one batch
  ;; to one leaf and one call at a time to another; handles past any record's, removed after.
  (let [ix    (:index kb)
        c     (tu/tmp-ctx)
        h     2000000001
        other 2000000002
        steps [:post :retire :retire-any]
        seqs  (concat (for [a steps b steps] [a b]) (for [a steps b steps d steps] [a b d]))
        ops   (fn [t inst step]
                (case step
                  :post       [[:post :mint [t c] h] [:post :tax-installs [inst] t]]
                  :retire     [[:retire :mint [t c] h] [:retire :tax-installs [inst] t]]
                  :retire-any [[:retire :mint [t p/any-context] h] [:retire :tax-installs [inst] t]]))
        n     (atom 0)]
    (doseq [start [[] [:post] [:other]]
            sq    seqs]
      (let [i      (swap! n + 2)
            [ta tb] [(tu/tmp-ind) (tu/tmp-ind)]
            [ia ib] [(+ 2000000100 i) (+ 2000000101 i)]
            init   (fn [t inst] (case (first start)
                                  :post  (p/family-apply! ix (ops t inst :post))
                                  :other (p/family-apply! ix [[:post :mint [t c] other]])
                                  nil))
            _      (init ta ia)
            _      (init tb ib)
            batch  (p/family-apply! ix (into [] (mapcat #(ops ta ia %)) sq))
            single (into [] (mapcat #(p/family-apply! ix (ops tb ib %))) sq)]
        (is (= single batch) (pr-str start sq))
        (is (= (family-state ix tb c ib) (family-state ix ta c ia)) (pr-str start sq))
        (doseq [[t inst] [[ta ia] [tb ib]]]
          (p/family-apply! ix [[:retire :mint [t c] h] [:retire :mint [t c] other]
                               [:retire :tax-installs [inst] t]])
          (is (= {:leaf #{} :count 0 :children #{} :root false :installs #{}}
                 (family-state ix t c inst))
              "nothing is left filed"))))))
