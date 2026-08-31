;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.public-api-test
  "The public namespaces are `vaelii.core` and the five entry points beside it, so the
  taxonomy read surface, the
  non-creating handle lookup, and the stored-vs-believed split of the extent/count
  fns all have to be reachable from it.  These tests pin the public spelling —
  they deliberately require nothing under `vaelii.impl.*` except the test scaffolding."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- the taxonomy, read from core --------------------------------------

(tu/deftest-kb genl-closure-is-readable-from-core
  (tu/with-terms [dog mammal animal cat Muffet]
    (v/assert kb (list 'genl dog mammal)    'CxUniverse)
    (v/assert kb (list 'genl mammal animal) 'CxUniverse)
    (v/assert kb (list 'genl cat mammal)    'CxUniverse)
    (testing "genls is the reflexive up-closure, specs the reflexive down-closure"
      (is (= #{dog mammal animal} (v/genls kb dog)))
      (is (= #{dog cat mammal}    (v/specs kb mammal)))
      (is (= #{animal} (v/genls kb animal)))                 ; reflexive at the root
      (is (= #{Muffet} (v/genls kb Muffet))))                    ; and for a non-node
    (testing "genl? asks the closure transitively"
      (is (v/genl? kb dog animal))
      (is (v/genl? kb dog dog))
      (is (not (v/genl? kb animal dog)))
      (is (not (v/genl? kb dog cat))))
    (testing "types enumerates the hierarchy's nodes"
      (let [ts (set (v/types kb))]
        (is (every? ts [dog cat mammal animal]))
        (is (not (contains? ts Muffet)))))))            ; an individual is not a type

(tu/deftest-kb genlCx-closure-is-readable-from-core
  (tu/with-terms [CxLeaf CxMid CxTop CxOther]
    (v/assert kb (list 'genlCx CxLeaf CxMid) 'CxUniverse)
    (v/assert kb (list 'genlCx CxMid CxTop)  'CxUniverse)
    (testing "context-up is what a context sees; context-down who sees it"
      (is (= #{CxLeaf CxMid CxTop} (v/context-up kb CxLeaf)))
      (is (= #{CxLeaf CxMid} (v/context-down kb CxMid))))
    (testing "sees? is the up-closure membership test, reflexively"
      (is (v/sees? kb CxLeaf CxTop))
      (is (v/sees? kb CxLeaf CxLeaf))
      (is (not (v/sees? kb CxTop CxLeaf)))
      (is (not (v/sees? kb CxLeaf CxOther))))
    (testing "contexts enumerates the context hierarchy's nodes"
      (let [cs (set (v/contexts kb))]
        (is (every? cs [CxLeaf CxMid CxTop]))))))

(tu/deftest-kb predicate-metadata-is-readable-from-core
  (tu/with-terms [siblingOf ancestorOf parentOf childOf spouseOf]
    (v/assert kb (list 'symmetric siblingOf)   'CxUniverse)
    (v/assert kb (list 'transitive ancestorOf) 'CxUniverse)
    (v/assert kb (list 'inverse parentOf childOf) 'CxUniverse)
    (testing "has-prop? reads the metadata a declaration cached"
      (is (v/has-prop? kb :symmetric siblingOf))
      (is (v/has-prop? kb :transitive ancestorOf))
      (is (not (v/has-prop? kb :symmetric ancestorOf)))
      (is (not (v/has-prop? kb :symmetric spouseOf))))
    (testing "props is the whole set carrying a property"
      (is (contains? (v/props kb :symmetric) siblingOf))
      (is (not (contains? (v/props kb :symmetric) ancestorOf))))
    (testing "inverse-of answers in both directions, nil for an unrelated predicate"
      (is (= childOf  (v/inverse-of kb parentOf)))
      (is (= parentOf (v/inverse-of kb childOf)))
      (is (nil? (v/inverse-of kb spouseOf))))))

;; ---- handle-of: the non-creating counterpart to ist ---------------------

(tu/deftest-kb handle-of-finds-without-creating
  (tu/with-terms [dog Muffet Rex CxStory]
    (let [h (v/assert kb (list dog Muffet) CxStory)]
      (testing "an existing sentence resolves to its handle"
        (is (= h (v/handle-of kb (list dog Muffet) CxStory))))
      (testing "a sentence that is not stored is nil — and stays not stored"
        (let [before (tu/sentex-ids kb)]
          (is (nil? (v/handle-of kb (list dog Rex) CxStory)))
          (is (nil? (v/handle-of kb (list dog Muffet) 'CxUniverse)))   ; wrong context
          (is (= before (tu/sentex-ids kb))
              "handle-of must not create — that is the whole difference from ist")))
      (testing "ist, by contrast, creates on a miss (which is why handle-of exists)"
        (let [created (v/ist kb CxStory (list dog Rex))]
          (is (= created (v/handle-of kb (list dog Rex) CxStory)))
          (v/retract! kb created))))))

(tu/deftest-kb handle-of-probes-a-symmetric-mirror-and-sees-defeated-sentexes
  (tu/with-terms [siblingOf dog Ann Bob Muffet CxStory]
    (v/assert kb (list 'symmetric siblingOf) 'CxUniverse)
    (let [h (v/assert kb (list siblingOf Ann Bob) CxStory)]
      (testing "a ground symmetric literal is found in either argument order"
        (is (= h (v/handle-of kb (list siblingOf Bob Ann) CxStory)))))
    (testing "storage, not belief: a defeated sentex still has a handle"
      (let [d (v/assert kb (list dog Muffet) CxStory)]
        (v/assert kb (list 'not (list dog Muffet)) CxStory {:strength :monotonic})
        (is (false? (v/in? kb d)))
        (is (empty? (v/sentexes-matching kb (list dog Muffet) CxStory)))     ; query filters belief
        (is (= d (v/handle-of kb (list dog Muffet) CxStory)))))))  ; handle-of does not

(tu/deftest-kb believed-answers-in?-for-a-whole-batch-at-once
  (tu/with-terms [flies dog Tweety Muffet CxBatch]
    (let [ok   (v/assert kb (list dog Muffet) CxBatch)
          out  (v/assert kb (list flies Tweety) CxBatch)]
      (v/assert kb (list 'not (list flies Tweety)) CxBatch {:strength :monotonic})
      (is (false? (v/in? kb out)) "the default lost to the monotonic negation")
      (testing "the batch answers exactly the handles in? answers true for"
        (is (= #{ok} (v/believed kb [ok out]))))
      (testing "a handle that is not stored is simply absent, as in? would say"
        (is (= #{ok} (v/believed kb [ok out 999999]))))
      (testing "and it agrees with in? handle by handle, which is the contract"
        (let [hs [ok out 999999]]
          (is (= (set (filter #(v/in? kb %) hs)) (v/believed kb hs)))))
      (is (= #{} (v/believed kb []))))))

;; ---- stored vs believed: the counts and the extents ---------------------

(tu/deftest-kb counts-are-stored-extents-and-say-so
  (tu/with-terms [flies Tweety CxCount]
    (v/assert kb (list flies Tweety) CxCount)                     ; default
    (v/assert kb (list 'not (list flies Tweety)) CxCount {:strength :monotonic})
    (let [h (v/handle-of kb (list flies Tweety) CxCount)]
      (is (false? (v/in? kb h)))
      (testing "the O(1) count includes the defeated sentex — it counts storage"
        ;; the negation roots under its positive body's functor, so both sit here
        (is (= 2 (v/count-with-functor kb flies)))
        (is (= 2 (count (v/sentexes-with-functor kb flies))))
        (testing "while query, which filters belief, sees only the winner"
          (is (empty? (v/sentexes-matching kb (list flies Tweety) CxCount)))
          (is (= 1 (count (v/sentexes-matching kb (list 'not (list flies Tweety)) CxCount))))))
      (testing "the extent fns take {:believed? true} to close the gap, at O(n)"
        (is (= 1 (count (v/sentexes-with-functor kb flies {:believed? true}))))
        (is (= 1 (count (v/sentexes-with-arg kb 1 Tweety {:believed? true}))))
        (is (= 2 (count (v/sentexes-with-arg kb 1 Tweety))))
        (is (< (count (v/sentexes-in-context kb CxCount {:believed? true}))
               (v/count-in-context kb CxCount))))
      (testing "count-in-context counts every stored sentex in the context, rules included"
        (is (= (v/count-in-context kb CxCount)
               (count (v/sentexes-in-context kb CxCount))))))))

;; ---- qualitative constraint reasoning, read from core -------------------
;; The networks are reachable from `vaelii.core` alone, and they answer whether or not
;; the calculus's prover is registered — a network is a property of the stored facts,
;; and `add-prover` only decides whether `ask` consults it.  These tests register none.

(tu/deftest-kb the-shipped-calculi-are-listable-without-registering-a-prover
  (let [cs (v/calculi)
        by (into {} (map (juxt :calculus identity)) cs)]
    (testing "all six ship, each with its base relations and its vocabulary"
      (is (= #{:rcc8 :cardinal :relative :distance :allen :point} (set (keys by))))
      (is (= 8 (count (:base (by :rcc8)))))
      (is (= 13 (count (:base (by :allen)))))
      (is (= 3 (count (:base (by :point)))))
      (is (contains? (:predicates (by :rcc8)) 'partOfRegion)))
    (testing "the identity is one of the base relations, on every calculus"
      (doseq [{:keys [calculus base identity]} cs]
        (is (seq identity) (str calculus " declares an identity"))
        (is (every? base identity) (str calculus "'s identity is a base relation"))))))

(tu/deftest-kb the-network-and-a-scenario-are-readable-from-core
  (tu/with-terms [RegA RegB RegC CxPublicSpace]
    (v/assert kb (list 'genlCx CxPublicSpace 'CxWell) 'CxUniverse
              {:strength :monotonic})
    (doseq [[a b] [[RegA RegB] [RegB RegC]]]
      (v/assert kb (list 'nonTangentialProperPart a b) CxPublicSpace
                {:strength :monotonic}))
    (let [net (v/qualitative-network kb :rcc8 CxPublicSpace)]
      (testing "the network names its nodes and says it is satisfiable"
        (is (true? (:consistent? net)))
        (is (= (set [RegA RegB RegC]) (set (:nodes net))))
        (is (nil? (:unsatisfiable net)) "nothing to blame when nothing clashes"))
      (testing "and carries the transitive relation nobody asserted"
        (is (nil? (v/handle-of kb (list 'nonTangentialProperPart RegA RegC)
                               CxPublicSpace)))
        (is (= #{:ntpp} (get (:constraints net) [RegA RegC])))
        (is (= #{:ntpp} (v/possible-relations kb :rcc8 CxPublicSpace RegA RegC)))))
    (testing "a scenario picks one relation per pair, and is a function of the facts"
      (let [s (v/qualitative-scenario kb :rcc8 CxPublicSpace)]
        (is (= :ntpp (get s [RegA RegC])))
        (is (every? keyword? (vals s)))
        (is (= s (v/qualitative-scenario kb :rcc8 CxPublicSpace))
            "repeatable, so it never depends on arrival order")))
    (testing "the bounded enumeration honours its bound"
      (is (<= (count (v/qualitative-scenarios kb :rcc8 CxPublicSpace 2)) 2)))))

(tu/deftest-kb an-unsatisfiable-network-answers-nothing-and-says-which-pair
  (tu/with-terms [RegA RegB CxPublicClash]
    (v/assert kb (list 'genlCx CxPublicClash 'CxWell) 'CxUniverse
              {:strength :monotonic})
    (v/assert kb (list 'nonTangentialProperPart RegA RegB) CxPublicClash
              {:strength :monotonic})
    (v/assert kb (list 'spatiallyDisconnected RegA RegB) CxPublicClash
              {:strength :monotonic})
    (let [net (v/qualitative-network kb :rcc8 CxPublicClash)]
      (is (false? (:consistent? net)))
      (is (= #{[RegA RegB] [RegB RegA]} (set (:unsatisfiable net)))
          "one pair carries this clash, so it is named")
      (is (empty? (v/possible-relations kb :rcc8 CxPublicClash RegA RegB)))
      (is (nil? (v/qualitative-scenario kb :rcc8 CxPublicClash))
          "no arrangement of a world that cannot exist"))))

(tu/deftest-kb naming-a-calculus-that-does-not-exist-is-a-bad-argument
  (let [e (try (v/qualitative-network kb :nope 'CxUniverse)
               (catch clojure.lang.ExceptionInfo e (ex-data e)))]
    (testing "it reports as a bad option, not as a check problem — a sentence can never
              be checked into this, so it does not belong in the :type vocabulary the
              editor renders"
      (is (= :unknown-option (:type e)))
      (is (= :nope (:calculus e))))
    (testing "and it says what there is instead of only what there is not"
      (is (some #{:rcc8} (:known e))))))

;; ---- turning a shipped reasoner on, from core alone ---------------------
;; Ten reasoners ship unregistered, and the provers are `vaelii.impl.*` values — so
;; without a roster on `core` the only way to opt in is to reach past the boundary this
;; namespace exists to hold.  `add-reasoner` names them instead.  These tests require
;; nothing under impl, which is the whole point of them.

(tu/deftest-kb the-shipped-reasoners-are-nameable-and-registrable-from-core
  (testing "the roster covers the six algebras, the three quantitative reasoners and the
            calendar clock"
    (is (= [:allen :calendar :cardinal :distance :duration :metric-time :point :rcc8
            :relative :sign]
           (v/reasoners)))
    (is (= (set (map :calculus (v/calculi)))
           (into #{} (remove #{:duration :metric-time :sign :calendar}) (v/reasoners)))
        "every calculus is registrable, and the roster adds the quantitative three and
         the calendar, which are not relation algebras"))
  (testing "each name resolves to a prover value"
    (doseq [nm (v/reasoners)]
      (is (some? (v/reasoner nm)) (str nm))))
  (testing "an unknown name is a bad argument, and names the roster"
    (let [d (try (v/reasoner :nope) nil (catch clojure.lang.ExceptionInfo e (ex-data e)))]
      (is (= :unknown-option (:type d)))
      (is (= (v/reasoners) (:known d))))))

(tu/deftest-kb registering-allen-makes-an-entailed-relation-derivable
  ;; The behavioural difference registration buys, from the public surface only: two
  ;; stored `before` facts, and the third relation the algebra entails between them.
  (tu/with-terms [EarlyEvent MidEvent LateEvent]
    (v/assert kb (list 'before EarlyEvent MidEvent) 'CxUniverse)
    (v/assert kb (list 'before MidEvent LateEvent) 'CxUniverse)
    (testing "unregistered, the facts are ordinary facts and nothing composes them"
      (is (not (v/ask? kb (list 'before EarlyEvent LateEvent) 'CxUniverse))))
    (v/add-reasoner kb :allen)
    (testing "registered, the composition is entailed"
      (is (v/ask? kb (list 'before EarlyEvent LateEvent) 'CxUniverse)))))

(tu/deftest-kb add-reasoner-registers-several-and-repeats-none
  ;; Sameness has to be the prover *value*: the six algebras share one record type, so a
  ;; class check would register the first and silently drop the rest.  Asked behaviourally
  ;; — two algebras, one call, and both still answering after a repeat.
  (tu/with-terms [EarlyEvent MidEvent LateEvent RegA RegB RegC]
    (v/assert kb (list 'before EarlyEvent MidEvent) 'CxUniverse)
    (v/assert kb (list 'before MidEvent LateEvent) 'CxUniverse)
    (v/assert kb (list 'partOfRegion RegA RegB) 'CxUniverse)
    (v/assert kb (list 'partOfRegion RegB RegC) 'CxUniverse)
    (v/add-reasoner kb :allen :rcc8)
    (testing "both algebras answer after one call — neither shadowed the other"
      (is (v/ask? kb (list 'before EarlyEvent LateEvent) 'CxUniverse))
      (is (v/ask? kb (list 'partOfRegion RegA RegC) 'CxUniverse)))
    (testing "and registering the same two again changes no answer"
      (v/add-reasoner kb :allen :rcc8)
      (is (v/ask? kb (list 'before EarlyEvent LateEvent) 'CxUniverse))
      (is (v/ask? kb (list 'partOfRegion RegA RegC) 'CxUniverse)))
    (testing "a bad name in the list registers none of it"
      (is (thrown? clojure.lang.ExceptionInfo (v/add-reasoner kb :duration :nope)))
      (is (not (v/ask? kb (list 'totalDuration EarlyEvent '?d) 'CxUniverse))
          "the :duration reasoner named beside the bad one did not register"))))

;; ---- naming the edge solver from core -----------------------------------

(tu/deftest-kb the-edge-solver-is-selectable-by-name
  (testing "both shipped backends are nameable, so neither needs an impl value"
    (is (some? (v/set-solver kb :stub)))
    (is (some? (v/set-solver kb :asp))))
  (testing "an unknown name is refused rather than installed"
    (let [d (try (v/set-solver kb :nope) nil (catch clojure.lang.ExceptionInfo e (ex-data e)))]
      (is (= :unknown-option (:type d)))
      (is (= [:asp :stub] (:known d)))))
  (v/set-solver kb :stub))

;; ---- the boundary itself ------------------------------------------------
;;
;; The claim `vaelii.core` makes about itself is checkable, so check it. Six public
;; namespaces: the engine, and the five entry points a reader is told to run or
;; require. Everything under `vaelii.impl.*` is free to change without notice, which
;; is only true if nothing public is spelled that way.

(deftest the-public-namespaces-are-loadable-and-named
  (testing "each public namespace loads and carries the entry points it advertises"
    (doseq [[ns-sym expected]
            '{vaelii.core    #{open-kb assert retract! sentexes-matching query isa?}
              vaelii.client  #{client call assert query retract! isa? watch poll unwatch watchers}
              vaelii.starter #{load-into}
              vaelii.web     #{handler start -main}
              vaelii.serve   #{app start port -main ops feed-ops op-names}
              vaelii.cli     #{dispatch open-kb-from -main}}]
      (require ns-sym)
      (let [publics (set (keys (ns-publics ns-sym)))]
        (is (every? publics expected)
            (str ns-sym " is missing " (pr-str (remove publics expected))))))))

(deftest no-public-namespace-is-spelled-impl
  (testing "the six public namespaces are the whole public surface"
    ;; `koinii/` is neither engine nor API: it is an application shipped in this tree,
    ;; layered on the six below exactly as an outside consumer would be (docs/koinii.md).
    ;; It is excluded here for the same reason it is excluded from the SPI and refusal
    ;; rosters — pinning it as a public promise would make koinii's own development churn
    ;; the engine's contract. What holds it honest is the other direction:
    ;; `koinii-reaches-into-no-impl` below.
    (is (= #{"vaelii.core" "vaelii.client" "vaelii.starter"
             "vaelii.web" "vaelii.serve" "vaelii.cli"}
           (->> (file-seq (java.io.File. "src/vaelii"))
                (filter #(.isFile ^java.io.File %))
                (filter #(.endsWith (.getName ^java.io.File %) ".clj"))
                (remove #(.contains (.getPath ^java.io.File %) "/impl/"))
                (remove #(.contains (.getPath ^java.io.File %) "/koinii/"))
                (map #(-> (.getPath ^java.io.File %)
                          (subs (count "src/"))
                          (subs 0 (- (count (subs (.getPath ^java.io.File %) (count "src/"))) 4))
                          (.replace "/" ".")
                          (.replace "_" "-")))
                set))
        "a new namespace outside impl/ is a new public promise — add it here on purpose")))

(defn- impl-symbols-in
  "Every `vaelii.impl…` symbol in `file`'s CODE — read, not grepped.

  A regex over the text answers a different question than the one being asked.  It sees
  `vaelii.impl` in a docstring that merely says where an engine mechanism lives (koinii's
  docstrings do, legitimately, eight times), and it misses every spelling that is a
  dependency but not the shape it matched: the plain-symbol libspec
  `(:require vaelii.impl.naming)`, the prefix list `(:require [vaelii.impl [naming :as
  nm]])`, an `(:import (vaelii.impl.sentex LiteralSentex))`, a `requiring-resolve` on a
  quoted symbol, and — the one that needs no require at all — a bare
  `(vaelii.impl.naming/sort-by-content-key …)` call, which resolves at runtime because
  `vaelii.core` has already loaded the namespace.  Reading the file and walking the forms
  catches all six as the symbols they are, and a string stays a string.

  `read-string` per top-level form with `*read-eval*` off; reader metadata and `#\"…\"`
  patterns survive it, and a `::` keyword in a namespace this reader has not loaded would
  not, so anything unreadable is reported rather than skipped."
  [^java.io.File file]
  (let [src (str "[" (slurp file) "]")
        forms (binding [*read-eval* false] (read-string src))
        named (fn [x] (and (or (symbol? x) (keyword? x)) (namespace x)))]
    (->> (tree-seq coll? seq forms)
         (keep (fn [x]
                 (cond (named x)   (when (str/starts-with? (namespace x) "vaelii.impl")
                                     (namespace x))
                       (symbol? x) (when (str/starts-with? (str x) "vaelii.impl")
                                     (str x)))))
         distinct
         sort
         vec)))

(deftest koinii-reaches-into-no-impl
  ;; The claim koinii's exclusion above rests on, checked rather than asserted. koinii is
  ;; the one application shipped in this tree, and it earns its place outside `impl/` by
  ;; consuming the same six namespaces an outside consumer gets: a `vaelii.impl.*` symbol
  ;; appearing here means either koinii went around the API, or the API is missing
  ;; something koinii needs and the answer is to publish it — never to reach past it.
  (let [files (->> (file-seq (java.io.File. "src/vaelii/koinii"))
                   (filter #(.isFile ^java.io.File %))
                   (filter #(.endsWith (.getName ^java.io.File %) ".clj"))
                   sort)]
    ;; An empty or renamed directory would pass the check below vacuously, which is the
    ;; failure mode a roster test is for.
    (is (= 8 (count files))
        "koinii's eight modules live at src/vaelii/koinii — moving them moves this test")
    (let [offenders (into {} (keep (fn [^java.io.File f]
                                     (when-some [hits (seq (impl-symbols-in f))]
                                       [(.getPath f) (vec hits)])))
                          files)]
      (is (= {} offenders)
          "koinii is an app on the public API — publish what it needs from vaelii.core"))))

;; ---- the extent fns refuse an option nothing reads ----------------------

(tu/deftest-kb an-extent-option-nothing-reads-is-refused
  ;; The one option the extent fns take is the belief filter, so the silent-default
  ;; failure is the filter silently off: `{:believed true}` (missing the `?`) reads as
  ;; no key at all and the stored extent comes back whole, defeated defaults included —
  ;; indistinguishable from a believed extent with nothing defeated in it.
  (tu/with-terms [flies Tweety CxExtent]
    (v/assert kb (list flies Tweety) CxExtent)
    (testing "the missing-? typo is refused at all three doors, naming the roster"
      (doseq [call [#(v/sentexes-in-context kb CxExtent {:believed true})
                    #(v/sentexes-with-functor kb flies {:believed true})
                    #(v/sentexes-with-arg kb 1 Tweety {:believed true})]]
        (let [e (is (thrown? clojure.lang.ExceptionInfo (call)))]
          (is (= :unknown-option (:type (ex-data e))))
          (is (= [:believed] (:unknown (ex-data e))))
          (is (re-find #":believed\?" (ex-message e))
              "the right spelling is in the message"))))
    (testing "a non-map opts is refused rather than read as no filter"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"must be a map"
                            (v/sentexes-in-context kb CxExtent :believed?))))
    (testing "the rostered spelling still filters"
      (is (= 1 (count (v/sentexes-with-functor kb flies {:believed? true}))))
      (is (= 1 (count (v/sentexes-in-context kb CxExtent {:believed? true})))))))

;; ---- a disjunctive goal is refused at every door that takes one --------

(tu/deftest-kb a-disjunctive-goal-is-refused-at-every-door-that-takes-one
  ;; `or` is expanded at the write door and nowhere else: a rule antecedent stores one
  ;; rule per alternative, and a goal would have to be a union of queries rather than a
  ;; query.  The read doors say so by shape.  `watch` takes a goal too, and a stored
  ;; sentence never unifies with a disjunction — so a watch that registered one would
  ;; fire never, which is the silent-nothing every other watch refusal exists to prevent.
  (tu/with-terms [dog cat]
    (let [goal (list 'or (list dog '?x) (list cat '?x))]
      (testing "the read doors refuse it by shape"
        (doseq [call [#(v/sentexes-matching kb goal 'CxUniverse)
                      #(v/ask kb goal 'CxUniverse)
                      #(v/prove kb goal 'CxUniverse)
                      #(v/query kb [goal] 'CxUniverse)]]
          (let [e (is (thrown? clojure.lang.ExceptionInfo (call)))]
            (is (= :shape (:type (ex-data e)))))))
      (testing "and a watch refuses it rather than registering one that never fires"
        (let [e (is (thrown? clojure.lang.ExceptionInfo
                             (v/watch kb goal 'CxUniverse (fn [_] nil))))]
          (is (= :not-watchable (:type (ex-data e))))
          (is (string? (:reason (ex-data e)))))
        (is (empty? (v/watchers kb)))))))
