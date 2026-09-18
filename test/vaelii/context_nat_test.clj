;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.context-nat-test
  "Reified-NAT contexts and structural genlCx — docs/context-nat.md.

  A `context_denoting_function` `Cx*Fn` reifies its ground applications to an opaque `cx/`
  context constant, so `(CxTimeFn CxMonad (DatetimeFn \"2000\"))` is a context a sentex can
  be stored in and a `genlCx` node — while its unreifiable argument stays structural in the
  `termOfUnit` map, readable to the producer.  `(contextArgSubrelation F pos R)` then orders
  sibling contexts structurally: `(CxTimeFn CxMonad (DatetimeFn \"2000-01\"))` is a spec of
  `(CxTimeFn CxMonad (DatetimeFn \"2000\"))` because January 2000 is inside 2000, with nobody
  asserting the `genlCx` edge."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.impl.nat :as nat]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded core-context/load-into))
(use-fixtures :each (tu/neutral))

(def ^:private ctr (atom 0))
(defn- fresh-cxfn
  "A gensym'd context-function name — `Cx*Fn`-shaped so `naming/context-function?` reads it,
  unique per call so the net-neutral fixture's retraction leaves nothing behind."
  [base] (symbol (str "CxTmp" base (swap! ctr inc) "Fn")))

(defn- declare-datetime-dimension!
  "Declare a fresh `Cx*Fn` context function ordered by `subintervalOf` on its datetime
  argument, plus `DatetimeFn` as a structural (unreifiable) constructor.  Returns the
  context-function symbol."
  [kb]
  (let [cxfn (fresh-cxfn "Time")]
    (v/assert kb (list 'context_denoting_function cxfn) 'CxUniverse)
    (v/assert kb '(unreifiable_function DatetimeFn) 'CxUniverse)
    cxfn))

;; ---- Layer 1: a Cx*Fn application reifies to a cx/ context ---------------

(tu/deftest-kb a-context-fn-application-reifies-to-a-cx-context
  (let [cxfn (declare-datetime-dimension! kb)
        expr (list cxfn 'CxMonad (list 'DatetimeFn "2000"))
        h    (v/assert kb '(likes Tom Ann) expr)
        k    (:context (v/sentex kb h))]
    (testing "the context slot is a reified cx/ constant that classifies as a context"
      (is (nat/reified-context-symbol? k))
      (is (= :context (v/term-role k))))
    (testing "the unreifiable datetime argument stays structural in the termOfUnit map"
      (is (= [(list 'termOfUnit k expr)]
             (map :sentence (v/sentexes-matching kb (list 'termOfUnit k '?e) 'CxUniverse)))))
    (testing "the fact reads back from the compound context (read-side reify is symmetric)"
      (is (= [{'?x 'Ann}] (v/ask kb '(likes Tom ?x) expr))))
    (testing "the same compound dedups to one context constant"
      (let [h2 (v/assert kb '(knows Tom Bob) expr)]
        (is (= k (:context (v/sentex kb h2))))))))

;; ---- Layer 1: a cx/ constant is a well-formed genlCx node ----------------

(tu/deftest-kb a-cx-context-is-a-well-formed-genlcx-node
  (let [cxfn (declare-datetime-dimension! kb)
        h    (v/assert kb '(likes Tom Ann) (list cxfn 'CxMonad (list 'DatetimeFn "2000")))
        k    (:context (v/sentex kb h))]
    (testing "a hand-asserted genlCx edge over the cx/ constant is accepted and wires it in"
      (v/assert kb (list 'genlCx k 'CxCore) 'CxUniverse)
      (is (contains? (set (v/contexts kb)) k))
      (is (v/sees? kb k 'CxCore)))))

;; ---- object nat/ constants are still refused as contexts -----------------

(tu/deftest-kb an-object-nat-is-still-not-a-context
  (tu/with-terms [FruitFn AppleTree]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (let [h (v/assert kb (list 'color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k (second (:sentence (v/sentex kb h)))]
      (is (nat/reified-nat-symbol? k) "it is a reified constant")
      (is (not (nat/reified-context-symbol? k)) "but an object one, not a context")
      (is (not= :context (v/term-role k)))
      (testing "storing a fact in an object nat/ context is refused by naming"
        (is (= :naming
               (try (v/assert kb '(likes Tom Ann) k) ::stored
                    (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))))))

;; ---- Layer 2: structural genlCx from a declared arg sub-relation ---------

(defn- year-and-month
  "Declare the datetime dimension + the subintervalOf ordering, store one fact in the
  year context and one in the month, and return `{:cxfn :year :month :ky :km}`."
  [kb]
  (let [cxfn  (declare-datetime-dimension! kb)
        _     (v/assert kb (list 'contextArgSubrelation cxfn 2 'subintervalOf) 'CxUniverse)
        year  (list cxfn 'CxMonad (list 'DatetimeFn "2000"))
        month (list cxfn 'CxMonad (list 'DatetimeFn "2000-01"))
        hy    (v/assert kb '(holiday NewYear) year)
        hm    (v/assert kb '(weather Cold) month)]
    {:cxfn cxfn :year year :month month
     :ky (:context (v/sentex kb hy)) :km (:context (v/sentex kb hm))}))

(tu/deftest-kb a-month-context-is-a-computed-spec-of-its-year
  (let [{:keys [year month ky km]} (year-and-month kb)]
    (testing "the producer materialized (genlCx month year) with nobody asserting it"
      (is (v/sees? kb km ky) "the month context sees the year context")
      (is (not (v/sees? kb ky km)) "but the year does not see the month"))
    (testing "the edge is a real justified sentex, and the month is in the hierarchy"
      (is (contains? (set (v/contexts kb)) km))
      (is (= [(list 'genlCx km ky)]
             (map :sentence (v/sentexes-matching kb (list 'genlCx km ky) 'CxUniverse)))))
    (testing "a fact in the year is visible from the month (inheritance up the ancestor set)"
      (is (= [{'?h 'NewYear}] (v/ask kb '(holiday ?h) month))))
    (testing "a fact in the month is NOT visible from the year"
      (is (empty? (v/ask kb '(weather ?w) year))))))

(tu/deftest-kb the-computed-edge-belief-follows-its-reasons
  (let [{:keys [cxfn km ky]} (year-and-month kb)]
    (is (v/sees? kb km ky) "baseline: the edge holds")
    (testing "retracting the subrelation declaration withdraws the computed edge"
      (let [decl (tu/sentex-matching kb (list 'contextArgSubrelation cxfn 2 'subintervalOf)
                                     'CxUniverse)]
        (v/retract! kb (:id decl))
        (is (not (v/sees? kb km ky)) "the month no longer sees the year")))))

(tu/deftest-kb the-order-of-arrival-does-not-decide-the-edge
  ;; declaration last, contexts first — the retroactive sweep must reach them
  (let [cxfn  (declare-datetime-dimension! kb)
        year  (list cxfn 'CxMonad (list 'DatetimeFn "2000"))
        month (list cxfn 'CxMonad (list 'DatetimeFn "2000-01"))]
    (v/assert kb '(holiday NewYear) year)
    (v/assert kb '(weather Cold) month)
    (let [km (:context (tu/sentex-matching kb '(weather Cold) month))
          ky (:context (tu/sentex-matching kb '(holiday NewYear) year))]
      (is (not (v/sees? kb km ky)) "no edge before the declaration")
      (v/assert kb (list 'contextArgSubrelation cxfn 2 'subintervalOf) 'CxUniverse)
      (is (v/sees? kb km ky) "the declaration arriving last sweeps the existing contexts"))))

;; ---- Finding #1: the producer reacts to belief REVIVAL, not only to assert ----

(defn- refusal
  "The `:type` a thrown assert refused with, or ::stored when it did not throw."
  [f]
  (try (f) ::stored
       (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(tu/deftest-kb a-revived-subrelation-declaration-rebuilds-the-computed-edge
  ;; The producer runs only on the assert choke-point, but the belief of a
  ;; `contextArgSubrelation` declaration can flip OUT→IN with NO assert — retracting a
  ;; monotonic defeater above it revives it.  An edge never built while the declaration was
  ;; OUT has no justification to revive, so `retract!` must re-run the producer
  ;; (`reconcile-revivals`) against the settled belief (docs/context-nat.md).
  (let [cxfn  (declare-datetime-dimension! kb)
        year  (list cxfn 'CxMonad (list 'DatetimeFn "2000"))
        month (list cxfn 'CxMonad (list 'DatetimeFn "2000-01"))
        hy    (v/assert kb '(holiday NewYear) year)
        hm    (v/assert kb '(weather Cold) month)
        ky    (:context (v/sentex kb hy))
        km    (:context (v/sentex kb hm))]
    (testing "baseline: no declaration, so the month does not see the year"
      (is (not (v/sees? kb km ky))))
    ;; the declaration is stored-but-defeated (a monotonic negation wins) → not believed →
    ;; the producer builds no edge
    (v/assert kb (list 'not (list 'contextArgSubrelation cxfn 2 'subintervalOf)) 'CxUniverse
              {:strength :monotonic})
    (v/assert kb (list 'contextArgSubrelation cxfn 2 'subintervalOf) 'CxUniverse)
    (testing "a defeated declaration builds no edge"
      (is (not (v/in? kb (:id (tu/sentex-matching
                               kb (list 'contextArgSubrelation cxfn 2 'subintervalOf)
                               'CxUniverse))))
          "the declaration is stored but OUT")
      (is (not (v/sees? kb km ky))))
    ;; retract the monotonic negation — the declaration REVIVES with no further assert
    (let [neg (tu/sentex-matching
               kb (list 'not (list 'contextArgSubrelation cxfn 2 'subintervalOf)) 'CxUniverse)]
      (v/retract! kb (:id neg)))
    (testing "reviving the declaration rebuilds the computed edge, before any further assert"
      (is (v/sees? kb km ky) "the month now sees the year")
      (is (= [{'?h 'NewYear}] (v/ask kb '(holiday ?h) month))
          "and a fact in the year is visible from the month up the ancestor set"))))

;; ---- Finding #2: a Cx*Fn in ARGUMENT position does not alias the context ----

(tu/deftest-kb a-context-fn-in-argument-position-does-not-alias-the-context
  ;; A context-denoting `Cx*Fn` application reifies to a `cx/` constant only in the CONTEXT
  ;; slot; the sentence/argument reify walk must leave it structural, or one `cx/` constant
  ;; would be both a context and an untyped object relatum (docs/context-nat.md).
  (let [cxfn (declare-datetime-dimension! kb)
        expr (list cxfn 'CxMonad (list 'DatetimeFn "2000"))
        hc   (v/assert kb '(likes Tom Ann) expr)              ; context-slot use → cx/ constant
        kctx (:context (v/sentex kb hc))
        ha   (v/assert kb (list 'happenedDuring 'Event1 expr) 'CxUniverse)  ; argument-position use
        arg2 (nth (:sentence (v/sentex kb ha)) 2)]
    (testing "the context slot reified to a cx/ constant"
      (is (nat/reified-context-symbol? kctx)))
    (testing "the same expression in argument position is NOT that cx/ constant"
      (is (not= kctx arg2) "the argument must not alias the context slot")
      (is (not (nat/reified-context-symbol? arg2)) "and is no cx/ context constant at all")
      (is (and (sequential? arg2) (= cxfn (first arg2)))
          "it stays a structural compound, exactly as an unreifiable NAT does"))))

;; ---- Finding #3: the context-slot shape gate does not depend on the naming policy ----

(tu/deftest-kb naming-off-still-refuses-a-non-symbol-context-for-shape
  ;; `check-shape!` runs independent of the naming policy, and the gate re-checks that
  ;; reification would yield a symbol — so an undeclared or non-ground compound context is a
  ;; `:shape` refusal even under `:naming :off`, never a raw list in a sentex's context slot
  ;; (docs/context-nat.md).
  (let [cxfn   (declare-datetime-dimension! kb)
        kb-off (assoc kb :naming :off)]
    (testing "an UNDECLARED context-function compound is a shape error even with naming off"
      (is (= :shape (refusal #(v/assert kb-off '(likes Tom Ann)
                                        (list 'CxBogusFn 'CxMonad (list 'DatetimeFn "2000")))))))
    (testing "a DECLARED but NON-GROUND context is a shape error even with naming off"
      (is (= :shape (refusal #(v/assert kb-off '(likes Tom Ann)
                                        (list cxfn 'CxMonad '?x))))))
    (testing "a declared ground context still reifies to a symbol and stores (control)"
      (let [h (v/assert kb-off '(likes Tom Ann) (list cxfn 'CxMonad (list 'DatetimeFn "2000")))]
        (is (symbol? (:context (v/sentex kb-off h))))))))

;; ---- Finding #4: the stored-fact R oracle picks its supporter content-keyed ----

(tu/deftest-kb the-stored-fact-oracle-chooses-its-supporter-by-content
  ;; `subintervalOf` answers `::pure`, so exercise the stored-fact branch with a
  ;; sub-relation that has no registered comparator.  With two believed `(R a b)` facts —
  ;; the same ground relation in two contexts — the edge's supporter must be chosen by
  ;; content (the lexicographically-smallest context), never by handle/retrieval order
  ;; (docs/context-nat.md, order independence).
  (let [cxfn  (declare-datetime-dimension! kb)
        yterm (list 'DatetimeFn "2000")
        mterm (list 'DatetimeFn "2000-01")
        year  (list cxfn 'CxMonad yterm)
        month (list cxfn 'CxMonad mterm)
        rfact (list 'subFooOf mterm yterm)]
    ;; two R-evidence facts, CxUniverse first (lower handle), CxCore second (higher handle
    ;; but the smaller context by content) — so a handle/retrieval-first pick and a
    ;; content-first pick disagree.
    (v/assert kb rfact 'CxUniverse)
    (v/assert kb rfact 'CxCore)
    (v/assert kb '(holiday NewYear) year)
    (v/assert kb '(weather Cold) month)
    (v/assert kb (list 'contextArgSubrelation cxfn 2 'subFooOf) 'CxUniverse)
    (let [ky (:context (tu/sentex-matching kb '(holiday NewYear) year))
          km (:context (tu/sentex-matching kb '(weather Cold) month))]
      (testing "the stored-fact oracle materialized the edge"
        (is (v/sees? kb km ky)))
      (let [edge (tu/sentex-matching kb (list 'genlCx km ky) 'CxUniverse)
            just (first (filter #(= 'contextArgSubrelation (:informant %))
                                (v/supporting-justifications kb (:id edge))))
            ev   (first (filter #(= rfact (:sentence (v/sentex kb %))) (:antecedents just)))]
        (testing "its R-evidence supporter is the fact in the smallest context, not the first"
          (is (= 'CxCore (:context (v/sentex kb ev)))))))))

;; ---- the context slot reads back through the ranks it was written under ---

(tu/deftest-kb a-context-slot-resolves-the-same-way-reading-and-writing
  ;; `maybe-reify-context` mints on the write path and dedups on the read one, and the
  ;; two have to resolve an application to the same term or a fact stored under one
  ;; spelling is unreachable by the other.  A `(rewriteOf T E)` is the rank that shows it:
  ;; the write path resolves the slot to `T` and mints no `termOfUnit`, so a read that
  ;; consulted the dedup probe alone would answer `no-match` for a context it had just
  ;; stored into.
  (tu/with-terms [CxAlias Slot likes Tom Ann]
    (let [cxfn (fresh-cxfn "Alias")
          app  (list cxfn Slot)]
      (v/assert kb (list 'context_denoting_function cxfn) 'CxUniverse)
      (v/assert kb (list 'genlCx CxAlias 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'rewriteOf CxAlias app) 'CxUniverse)
      (let [h (v/assert kb (list likes Tom Ann) app)]
        (testing "the write path resolves the slot to the rewriteOf target"
          (is (= CxAlias (:context (v/sentex kb h)))))
        (testing "and the read path resolves it the same way"
          (is (= [CxAlias]
                 (mapv :context (v/sentexes-matching kb (list likes Tom Ann) app))))
          (is (v/ask? kb (list likes Tom Ann) app)))))))

;; ---- a declared position the function does not have ----------------------

(tu/deftest-kb a-subrelation-position-past-the-arity-orders-nothing-and-throws-nothing
  ;; Nothing at the assert entry point ties a declaration's `pos` to the arity of the function
  ;; it names, so a wide one is storable.  The producer runs on the assert maintenance
  ;; path, so masking that position blind would throw out of an unrelated assert; a
  ;; position that does not index the expression simply names no sibling group.
  (let [cxfn  (declare-datetime-dimension! kb)
        year  (list cxfn 'CxMonad (list 'DatetimeFn "2000"))
        month (list cxfn 'CxMonad (list 'DatetimeFn "2000-01"))]
    (v/assert kb (list 'contextArgSubrelation cxfn 9 'subintervalOf) 'CxUniverse)
    (testing "storing into the contexts still works, declaration first"
      (is (some? (v/assert kb '(holiday NewYear) year)))
      (is (some? (v/assert kb '(weather Cold) month))))
    (let [ky (:context (tu/sentex-matching kb '(holiday NewYear) year))
          km (:context (tu/sentex-matching kb '(weather Cold) month))]
      (testing "and no edge is invented from a position the expression does not have"
        (is (not (v/sees? kb km ky)))
        (is (not (v/sees? kb ky km)))))
    (testing "a second declaration on a real position still orders them"
      (v/assert kb (list 'contextArgSubrelation cxfn 2 'subintervalOf) 'CxUniverse)
      (let [ky (:context (tu/sentex-matching kb '(holiday NewYear) year))
            km (:context (tu/sentex-matching kb '(weather Cold) month))]
        (is (v/sees? kb km ky))))))

;; ---- the calendar constructors, as a person would ask about them --------

(defn- declare-calendar-dimension!
  "Declare a fresh `Cx*Fn` context function ordered by `subintervalOf` on its calendar
  argument, plus the three calendar constructors as structural (unreifiable) ones.
  Returns the context-function symbol."
  [kb]
  (let [cxfn (fresh-cxfn "Cal")]
    (v/assert kb (list 'context_denoting_function cxfn) 'CxUniverse)
    (doseq [f '[YearFn MonthFn DayFn]]
      (v/assert kb (list 'unreifiable_function f) 'CxUniverse))
    (v/assert kb (list 'contextArgSubrelation cxfn 2 'subintervalOf) 'CxUniverse)
    cxfn))

(tu/deftest-kb a-holiday-declared-for-the-year-holds-in-march
  ;; Nobody says March and the 15th of March are inside 2000.  The calendar constructors
  ;; keep their fields readable, and the declared ordering computes the containment.
  (let [cxfn  (declare-calendar-dimension! kb)
        year  (list cxfn 'CxMonad '(YearFn 2000))
        march (list cxfn 'CxMonad '(MonthFn 2000 3))
        day   (list cxfn 'CxMonad '(DayFn 2000 3 15))]
    (v/assert kb '(holiday NewYear) year)
    (v/assert kb '(weather Rainy) march)
    (v/assert kb '(weather Sunny) day)
    (testing "what holds all year holds in March, and on a day in March"
      (is (= [{'?h 'NewYear}] (v/ask kb '(holiday ?h) march)))
      (is (= [{'?h 'NewYear}] (v/ask kb '(holiday ?h) day))))
    (testing "and March's own weather is not the year's"
      (is (empty? (v/ask kb '(weather ?w) year))))
    (testing "the day sits inside its month as the month sits inside its year"
      (is (= #{'Rainy 'Sunny} (set (map #(get % '?w) (v/ask kb '(weather ?w) day))))))))

(tu/deftest-kb a-rule-about-march-does-not-reach-february
  ;; Sibling months are ordered neither way, so a theory stated for one month is not a
  ;; theory about the next.
  (let [cxfn (declare-calendar-dimension! kb)
        feb  (list cxfn 'CxMonad '(MonthFn 2000 2))
        mar  (list cxfn 'CxMonad '(MonthFn 2000 3))]
    (v/assert kb '(implies (and (blooms ?x)) (spring_has_come ?x)) mar {:direction :forward})
    (v/assert kb '(blooms Snowdrop) feb)
    (v/assert kb '(blooms Crocus) mar)
    (testing "the rule fires for its own month"
      (is (v/ask? kb '(spring_has_come Crocus) mar)))
    (testing "and reaches neither the month beside it nor back up into the year"
      (is (not (v/ask? kb '(spring_has_come Snowdrop) feb)))
      (is (not (v/ask? kb '(spring_has_come Snowdrop) mar)))
      (is (not (v/ask? kb '(spring_has_come Crocus)
                       (list cxfn 'CxMonad '(YearFn 2000))))))))

(tu/deftest-kb the-same-month-written-twice-is-one-context
  (let [cxfn  (declare-calendar-dimension! kb)
        march (list cxfn 'CxMonad '(MonthFn 2000 3))
        h1    (v/assert kb '(weather Rainy) march)
        h2    (v/assert kb '(weather Windy) (list cxfn 'CxMonad '(MonthFn 2000 3)))]
    (testing "the second writing resolves to the constant the first minted"
      (is (= (:context (v/sentex kb h1)) (:context (v/sentex kb h2)))))
    (testing "so both facts are in the one context"
      (is (= #{'Rainy 'Windy} (set (map #(get % '?w) (v/ask kb '(weather ?w) march))))))))

(tu/deftest-kb the-calendar-edge-does-not-depend-on-what-arrived-first
  ;; The facts before the ordering declaration, rather than after it: the declaration
  ;; arriving last must sweep the contexts already stored into.
  (let [cxfn  (fresh-cxfn "Cal")
        year  (list cxfn 'CxMonad '(YearFn 2000))
        march (list cxfn 'CxMonad '(MonthFn 2000 3))]
    (v/assert kb (list 'context_denoting_function cxfn) 'CxUniverse)
    (doseq [f '[YearFn MonthFn]]
      (v/assert kb (list 'unreifiable_function f) 'CxUniverse))
    (v/assert kb '(holiday NewYear) year)
    (v/assert kb '(weather Rainy) march)
    (testing "no ordering declared yet, so the two contexts are unrelated"
      (is (empty? (v/ask kb '(holiday ?h) march))))
    (v/assert kb (list 'contextArgSubrelation cxfn 2 'subintervalOf) 'CxUniverse)
    (testing "the declaration arriving last computes the same edge"
      (is (= [{'?h 'NewYear}] (v/ask kb '(holiday ?h) march)))
      (is (empty? (v/ask kb '(weather ?w) year))))))

(tu/deftest-kb a-calendar-month-and-the-iso-month-are-one-interval
  ;; The comparator reads both spellings to one field vector, so a KB told the year one
  ;; way and the month the other still orders them.
  (let [cxfn (declare-calendar-dimension! kb)]
    (v/assert kb '(unreifiable_function DatetimeFn) 'CxUniverse)
    (let [year  (list cxfn 'CxMonad '(YearFn 2000))
          march (list cxfn 'CxMonad '(DatetimeFn "2000-03"))]
      (v/assert kb '(holiday NewYear) year)
      (v/assert kb '(weather Rainy) march)
      (is (= [{'?h 'NewYear}] (v/ask kb '(holiday ?h) march)))
      (is (empty? (v/ask kb '(weather ?w) year))))))

;; ---- the stored-fact oracle is retroactive ------------------------------

(tu/deftest-kb r-evidence-arriving-after-both-contexts-still-orders-them
  ;; A comparator dimension needs nothing but the contexts.  A dimension resolved by
  ;; stored `(R a b)` facts has its evidence arrive on its own schedule, and the producer
  ;; sweeps on that arrival too — otherwise the edge would wait for the next assert that
  ;; happened to touch one of the two contexts, and what the KB answers would depend on
  ;; the order the three arrived in (docs/context-nat.md).
  (let [cxfn  (fresh-cxfn "Time")
        yterm (list 'DatetimeFn "2000")
        mterm (list 'DatetimeFn "2000-01")
        year  (list cxfn 'CxMonad yterm)
        month (list cxfn 'CxMonad mterm)]
    (v/assert kb (list 'context_denoting_function cxfn) 'CxUniverse)
    (v/assert kb '(unreifiable_function DatetimeFn) 'CxUniverse)
    (v/assert kb (list 'contextArgSubrelation cxfn 2 'subFooOf) 'CxUniverse)
    (v/assert kb '(holiday NewYear) year)
    (v/assert kb '(weather Cold) month)
    (let [ky (:context (tu/sentex-matching kb '(holiday NewYear) year))
          km (:context (tu/sentex-matching kb '(weather Cold) month))]
      (testing "no evidence yet, so no edge"
        (is (not (v/sees? kb km ky))))
      (v/assert kb (list 'subFooOf mterm yterm) 'CxUniverse)
      (testing "the evidence arriving last builds the edge it entails"
        (is (v/sees? kb km ky))
        (is (= [{'?h 'NewYear}] (v/ask kb '(holiday ?h) month))))
      (testing "and retracting it withdraws the edge again"
        (v/retract! kb (:id (tu/sentex-matching kb (list 'subFooOf mterm yterm) 'CxUniverse)))
        (is (not (v/sees? kb km ky)))))))

;; ---- the computed edge's supporters, stated below the context it is stored in ----
;;
;; `materialize-edge` stores the computed `genlCx` in CxUniverse and justifies it by the two
;; `termOfUnit` sentexes, the `contextArgSubrelation` declaration and, for a dimension
;; resolved by stored facts, the `(R a b)` evidence.  Nothing requires the declaration or
;; the evidence to be stated where CxUniverse can see it, so the edge can rest on a
;; supporter in a context below its own.  These two tests pin that shape, and
;; `VAELII_AUDIT_SUPPORT` reports both justifications.

(defn- supporter-contexts
  "The contexts of every sentex a justification of handle `h` names, as a set."
  [kb h]
  (set (for [s (:support (v/why kb h)) b (:because s)] (:context b))))

(tu/deftest-kb a-subrelation-declared-below-cxuniverse-orders-the-contexts
  (tu/with-terms [CxData]
    (v/assert kb (list 'genlCx CxData 'CxUniverse) 'CxUniverse)
    (let [cxfn  (declare-datetime-dimension! kb)
          decl  (v/assert kb (list 'contextArgSubrelation cxfn 2 'subintervalOf) CxData)
          year  (list cxfn 'CxMonad (list 'DatetimeFn "2000"))
          month (list cxfn 'CxMonad (list 'DatetimeFn "2000-01"))
          ky    (:context (v/sentex kb (v/assert kb '(holiday NewYear) year)))
          km    (:context (v/sentex kb (v/assert kb '(weather Cold) month)))
          edge  (v/handle-of kb (list 'genlCx km ky) 'CxUniverse)]
      (testing "the declaration stated in CxData still computes the edge, stored in CxUniverse"
        (is (v/sees? kb km ky))
        (is (some? edge)))
      (testing "the edge rests on the declaration in CxData, which CxUniverse does not see"
        (is (contains? (supporter-contexts kb edge) CxData))
        (is (not (v/sees? kb 'CxUniverse CxData))))
      (testing "retracting the declaration withdraws the edge"
        (v/retract! kb decl)
        (is (not (v/sees? kb km ky)))))))

(tu/deftest-kb subrelation-evidence-stated-below-cxuniverse-orders-the-contexts
  (tu/with-terms [CxData]
    (v/assert kb (list 'genlCx CxData 'CxUniverse) 'CxUniverse)
    (let [cxfn  (fresh-cxfn "Time")
          yterm (list 'DatetimeFn "2000")
          mterm (list 'DatetimeFn "2000-01")
          year  (list cxfn 'CxMonad yterm)
          month (list cxfn 'CxMonad mterm)]
      (v/assert kb (list 'context_denoting_function cxfn) 'CxUniverse)
      (v/assert kb '(unreifiable_function DatetimeFn) 'CxUniverse)
      (v/assert kb (list 'contextArgSubrelation cxfn 2 'subFooOf) 'CxUniverse)
      (let [ky   (:context (v/sentex kb (v/assert kb '(holiday NewYear) year)))
            km   (:context (v/sentex kb (v/assert kb '(weather Cold) month)))
            ev   (v/assert kb (list 'subFooOf mterm yterm) CxData)
            edge (v/handle-of kb (list 'genlCx km ky) 'CxUniverse)]
        (testing "evidence stated in CxData still computes the edge, stored in CxUniverse"
          (is (v/sees? kb km ky))
          (is (some? edge)))
        (testing "the edge rests on the evidence in CxData, which CxUniverse does not see"
          (is (contains? (supporter-contexts kb edge) CxData)))
        (testing "retracting the evidence withdraws the edge"
          (v/retract! kb ev)
          (is (not (v/sees? kb km ky))))))))
