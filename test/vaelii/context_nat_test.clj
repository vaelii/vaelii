;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.context-nat-test
  "Reified-NAT contexts and structural genlCx — docs/context-nat.md.

  A ground application in a sentex's context slot reifies to an opaque `cx/` context
  constant, so `(CxTimeFn CxMonad (DatetimeFn \"2000\"))` is a context a sentex can be stored
  in and a `genlCx` node — while its unreifiable argument stays structural in the
  `natFormula` map, readable to the producer.  A read names the context through the
  application while CxUniverse believes `(result CxTimeFn context)`.  `(contextArgSubrelation F pos R)` then orders
  sibling contexts structurally: `(CxTimeFn CxMonad (DatetimeFn \"2000-01\"))` is a spec of
  `(CxTimeFn CxMonad (DatetimeFn \"2000\"))` because January 2000 is inside 2000, with nobody
  asserting the `genlCx` edge."
  (:require [clojure.set :as set]
            [clojure.test :refer [is testing use-fixtures]]
            [taoensso.trove :as trove]
            [vaelii.core :as v]
            [vaelii.impl.context-nat :as cn]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.profile :as prof]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(def ^:private ctr (atom 0))
(defn- fresh-cxfn
  "A gensym'd context-function name in the `Cx*Fn` spelling, unique per call so the net-neutral fixture's retraction leaves nothing behind."
  [base] (symbol (str "CxTmp" base (swap! ctr inc) "Fn")))

(defn- declare-datetime-dimension!
  "Declare a fresh `Cx*Fn` context function ordered by `subintervalOf` on its datetime
  argument, plus `DatetimeFn` as a structural (unreifiable) constructor.  Returns the
  context-function symbol."
  [kb]
  (let [cxfn (fresh-cxfn "Time")]
    (v/assert kb (list 'result cxfn 'context) 'CxUniverse)
    (v/assert kb '(unreifiable_function DatetimeFn) 'CxUniverse)
    cxfn))

;; ---- Layer 1: a Cx*Fn application reifies to a cx/ context ---------------

(tu/deftest-kb a-context-fn-application-reifies-to-a-cx-context
  (let [cxfn (declare-datetime-dimension! kb)
        expr (list cxfn 'CxMonad (list 'DatetimeFn "2000"))
        h    (v/assert kb '(likes Tom Ann) expr)
        k    (:context (v/sentex kb h))]
    (testing "the context slot is a reified cx/ constant that classifies as a context"
      (is (nat-read/reified-context-symbol? k))
      (is (= :context (v/term-role k))))
    (testing "the unreifiable datetime argument stays structural in the natFormula map"
      (is (= [(list 'natFormula k expr)]
             (map :sentence (v/sentexes-matching kb (list 'natFormula k '?e) 'CxUniverse)))))
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
      (v/assert kb (list 'genlCx k 'CxUniverse) 'CxUniverse)
      (is (contains? (set (v/contexts kb)) k))
      (is (v/sees? kb k 'CxUniverse)))))

;; ---- the stored set and the readings are functions of the offered set ----

;; An `except` of the declaration in CxUniverse hides it from every reader: `assert` stores
;; the fact in the `cx/` context whichever arrives first, and a read naming the slot is
;; refused.  `result` is forced-monotonic, so a monotonic denial of the
;; declaration is never believed and the slot reads, as it does under an `except` in a
;; sub-context.  `recover` rebuilds the same reading in either order.
(defn- hide-mark!
  "Hide the `(result cxfn context)` declaration `mark` the way `where` names."
  [kb where mark cxfn sub]
  (case where
    :universe (v/assert kb (list 'except (v/sentex-handle mark)) 'CxUniverse)
    :sub      (v/assert kb (list 'except (v/sentex-handle mark)) sub)
    :denial   (v/assert kb (list 'not (list 'result cxfn 'context)) 'CxUniverse
                        {:strength :monotonic})))

(defn- slot-reading
  "How `fact`, asserted at `slot`, reads: the contexts storing it, whether each is a `cx/`
  constant, its belief there, and `ask?` at the slot."
  [kb fact slot]
  (let [cs (vec (v/contexts-of kb fact))]
    {:stored (count cs)
     :cx?    (every? nat-read/reified-context-symbol? cs)
     :at-cx  (boolean (some #(v/ask? kb fact %) cs))
     :slot   (try (v/ask? kb fact slot) (catch clojure.lang.ExceptionInfo _ :refused))}))

(tu/deftest-kb a-context-declaration-no-reader-believes-stores-and-reads-alike-in-either-order
  (doseq [[where want] [[:universe {:stored 1 :cx? true :at-cx true :slot :refused}]
                        [:denial {:stored 1 :cx? true :at-cx true :slot true}]
                        [:sub {:stored 1 :cx? true :at-cx true :slot true}]]
          order        [[:hide :fact] [:fact :hide]]]
    (tu/with-terms [Winter NewYear holiday CxSub]
      (let [cxfn (fresh-cxfn "Season")
            _    (v/assert kb (list 'genlCx CxSub 'CxUniverse) 'CxUniverse {:strength :monotonic})
            mark (v/assert kb (list 'result cxfn 'context) 'CxUniverse)
            slot (list cxfn Winter)
            fact (list holiday NewYear)]
        (doseq [step order]
          (case step
            :hide (hide-mark! kb where mark cxfn CxSub)
            :fact (v/assert kb fact slot)))
        (let [before (slot-reading kb fact slot)]
          (v/recover kb)
          (is (= [want want] [before (slot-reading kb fact slot)]) (str where " " order)))))))

(defn- run-order!
  "Run `steps` against a fresh context function: `:declare` asserts `(result cxfn
  context)`, `:retract` retracts it, `:fact` asserts `fact` at `slot`.  A refused fact
  stores nothing, which the stored count reports."
  [kb steps cxfn fact slot]
  (let [decl (list 'result cxfn 'context)]
    (doseq [step steps]
      (case step
        :declare (v/assert kb decl 'CxUniverse)
        :retract (v/retract! kb (v/handle-of kb decl 'CxUniverse))
        :fact    (try (v/assert kb fact slot) (catch clojure.lang.ExceptionInfo _ nil))))))

(tu/deftest-kb the-stored-set-and-the-reading-do-not-depend-on-arrival-order
  ;; Every order of the declaration, the fact and the declaration's retraction, and a
  ;; re-declaration after the retraction: the fact is stored in its `cx/` context in every
  ;; row, and the slot reads exactly when the last step touching the declaration left it
  ;; stated.  `recover` rebuilds the same reading.
  (doseq [steps [[:fact]
                 [:declare :fact] [:fact :declare]
                 [:declare :fact :retract] [:declare :retract :fact] [:fact :declare :retract]
                 [:declare :retract :fact :declare] [:declare :fact :retract :declare]
                 [:fact :declare :retract :declare] [:declare :retract :declare :fact]]]
    (tu/with-terms [Winter NewYear holiday]
      (let [cxfn (fresh-cxfn "Order")
            slot (list cxfn Winter)
            fact (list holiday NewYear)
            want {:stored 1 :cx? true :at-cx true
                  :slot   (if (= :declare (last (filter #{:declare :retract} steps))) true :refused)}]
        (run-order! kb steps cxfn fact slot)
        (let [before (slot-reading kb fact slot)]
          (v/recover kb)
          (is (= [want want] [before (slot-reading kb fact slot)]) (str steps)))))))

(tu/deftest-kb an-undeclared-context-application-is-stored-and-refused-at-the-read
  (tu/with-terms [Q NewYear holiday]
    (let [slot (list 'CxBogusFn Q)
          fact (list holiday NewYear)
          h    (v/assert kb fact slot)
          k    (:context (v/sentex kb h))
          err  (try (v/ask? kb fact slot) nil
                    (catch clojure.lang.ExceptionInfo e
                      {:type (:type (ex-data e)) :message (ex-message e)}))]
      (testing "the write stores the fact in a cx/ context with no declaration read"
        (is (nat-read/reified-context-symbol? k))
        (is (v/ask? kb fact k) "a read naming the constant answers it"))
      (testing "a read naming the application is refused, naming the missing declaration"
        (is (= :shape (:type err)))
        (is (re-find #"\(result CxBogusFn context\)" (str (:message err))))))))

(tu/deftest-kb a-declaration-admits-the-slot-only-where-cxuniverse-sees-it
  ;; The slot resolves through the `natFormula` map in CxUniverse, so the declaration is
  ;; read there: stated in CxUniverse, it admits the slot; stated in a context with no
  ;; edge or in a spec of CxUniverse, it does not.  No context sits above CxUniverse.
  (doseq [where [:universe :unwired :below]]
    (tu/with-terms [Winter NewYear holiday CxBelow CxElse]
      (let [cxfn (fresh-cxfn "Scope")
            _    (v/assert kb (list 'genlCx CxBelow 'CxUniverse) 'CxUniverse {:strength :monotonic})
            _    (v/assert kb (list 'result cxfn 'context)
                           ({:universe 'CxUniverse :unwired CxElse :below CxBelow} where))
            slot (list cxfn Winter)
            fact (list holiday NewYear)]
        (v/assert kb fact slot)
        (is (= (if (= :universe where) true :refused)
               (:slot (slot-reading kb fact slot)))
            (str where)))))
  (tu/with-terms [CxAbove]
    (is (= :not-well-formed
           (tu/refusal-type #(v/assert kb (list 'genlCx 'CxUniverse CxAbove) 'CxUniverse)))
        "an edge above CxUniverse is refused")))

(tu/deftest-kb an-object-nat-is-still-not-a-context
  (tu/with-terms [FruitFn AppleTree]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (let [h (v/assert kb (list 'color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k (second (:sentence (v/sentex kb h)))]
      (is (nat-read/reified-nat-symbol? k) "it is a reified constant")
      (is (not (nat-read/reified-context-symbol? k)) "but an object one, not a context")
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
      (is (empty? (v/ask kb '(weather ?w) year))))
    (testing "describe names the year as what the month is a computed spec of"
      (is (= [ky] (:terms (:computed-spec-of (v/describe kb km 'CxUniverse))))))))

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

(defn- cx-of [kb h] (:context (v/sentex kb h)))

(tu/deftest-kb a-context-arg-genlcx-declaration-places-each-context-under-its-argument-in-either-arrival-order
  (tu/with-terms [CxStory p q r]
    (let [cxfn  (declare-datetime-dimension! kb)
          early (list cxfn CxStory (list 'DatetimeFn "2000"))
          late  (list cxfn CxStory (list 'DatetimeFn "2001"))
          _     (v/assert kb (list p) CxStory)
          ke    (cx-of kb (v/assert kb (list q) early))]
      (is (not (v/sees? kb ke CxStory)) "no edge before the declaration")
      (let [decl (v/assert kb (list 'contextArgGenlCx cxfn 1) 'CxUniverse)
            kl   (cx-of kb (v/assert kb (list r) late))]
        (testing "a context minted before the declaration and one minted after sit under their argument"
          (is (v/sees? kb ke CxStory))
          (is (v/sees? kb kl CxStory))
          (is (true? (v/ask? kb (list p) early))))
        (testing "the argument does not see the context"
          (is (not (v/ask? kb (list q) CxStory))))
        (testing "retracting the declaration withdraws both edges"
          (v/retract! kb decl)
          (is (not (v/sees? kb ke CxStory)))
          (is (not (v/sees? kb kl CxStory))))))))

(tu/deftest-kb a-hand-written-natformula-places-its-context-under-the-argument-until-it-is-retracted
  (doseq [declaration-first? [true false]]
    (tu/with-terms [CxStory CxNamed]
      (let [cxfn (declare-datetime-dimension! kb)
            decl #(v/assert kb (list 'contextArgGenlCx cxfn 1) 'CxUniverse)
            _    (when declaration-first? (decl))
            nf   (v/assert kb (list 'natFormula CxNamed (list cxfn CxStory (list 'DatetimeFn "2000"))) 'CxUniverse)]
        (when-not declaration-first? (decl))
        (testing (str "declaration first: " declaration-first?)
          (is (v/sees? kb CxNamed CxStory))
          (v/retract! kb nf)
          (is (not (v/sees? kb CxNamed CxStory))))))))

(tu/deftest-kb a-read-of-an-unwritten-application-sees-its-argument
  (tu/with-terms [CxStory p]
    (let [cxfn (declare-datetime-dimension! kb)]
      (v/assert kb (list 'contextArgGenlCx cxfn 1) 'CxUniverse)
      (v/assert kb (list p) CxStory)
      (is (true? (v/ask? kb (list p) (list cxfn CxStory (list 'DatetimeFn "2000"))))))))

(tu/deftest-kb a-context-arg-genlcx-declaration-builds-no-edge-to-cxuniverse
  (let [cxfn (declare-datetime-dimension! kb)
        _    (v/assert kb (list 'contextArgGenlCx cxfn 1) 'CxUniverse)
        k    (cx-of kb (v/assert kb '(likes Tom Ann) (list cxfn 'CxUniverse (list 'DatetimeFn "2000"))))]
    (is (empty? (v/sentexes-matching kb (list 'genlCx k 'CxUniverse) 'CxUniverse)))))

(tu/deftest-kb a-context-arg-genlcx-declaration-needs-a-positive-position
  (let [cxfn (declare-datetime-dimension! kb)]
    (is (= :not-well-formed
           (tu/refusal-type #(v/assert kb (list 'contextArgGenlCx cxfn 0) 'CxUniverse))))))

(tu/deftest-kb a-fact-into-an-existing-context-orders-no-sibling-pair
  ;; The producer runs on every assert into a context NAT, so it examines only the pairs
  ;; an assert can create: a mint pairs the new context with each sibling, both ways, and
  ;; a fact into a context already minted pairs nothing.  `lein perf`'s
  ;; `context-nat-existing-context` times the second.
  (let [cxfn  (declare-datetime-dimension! kb)
        _     (v/assert kb (list 'contextArgSubrelation cxfn 2 'subintervalOf) 'CxUniverse)
        day   (fn [d] (list cxfn 'CxMonad (list 'DatetimeFn (format "2000-01-%02d" d))))
        calls (atom 0)
        oracle @#'cn/r-evidence]
    (doseq [d (range 1 9)] (v/assert kb '(weather Cold) (day d)))
    (with-redefs [cn/r-evidence (fn [& args] (swap! calls inc) (apply oracle args))]
      (v/assert kb '(weather Warm) (day 1))
      (is (zero? @calls) "a fact into an existing context")
      (v/assert kb '(weather Cold) (day 9))
      (is (= 16 @calls) "a mint beside eight siblings"))))

;; ---- the producer reacts to belief revival, not only to assert ------------

(def ^:private refusal
  (fn [f] (tu/refusal-type f ::stored)))

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

;; ---- position picks the namespace ----------------------------------------

(tu/deftest-kb a-context-fn-in-argument-position-does-not-alias-the-context
  ;; An application reifies to a `cx/` constant only in the CONTEXT slot.  In argument
  ;; position a function that is no `reifiable_function` stays structural, so no `cx/`
  ;; constant is an object relatum (docs/context-nat.md).
  (let [cxfn (declare-datetime-dimension! kb)
        expr (list cxfn 'CxMonad (list 'DatetimeFn "2000"))
        hc   (v/assert kb '(likes Tom Ann) expr)              ; context-slot use → cx/ constant
        kctx (:context (v/sentex kb hc))
        ha   (v/assert kb (list 'happenedDuring 'Event1 expr) 'CxUniverse)  ; argument-position use
        arg2 (nth (:sentence (v/sentex kb ha)) 2)]
    (testing "the context slot reified to a cx/ constant"
      (is (nat-read/reified-context-symbol? kctx)))
    (testing "the same expression in argument position is NOT that cx/ constant"
      (is (not= kctx arg2) "the argument must not alias the context slot")
      (is (not (nat-read/reified-context-symbol? arg2)) "and is no cx/ context constant at all")
      (is (and (sequential? arg2) (= cxfn (first arg2)))
          "it stays a structural compound, exactly as an unreifiable NAT does"))))

(tu/deftest-kb one-expression-in-both-positions-names-one-constant-per-namespace
  ;; A reifiable function declared to denote contexts: the application in the context slot
  ;; mints `cx/k'`, in argument position `nat/k`, in either order.  Each namespace's map is
  ;; 1:1, so the two are no collision.  The argument constant is typed `context` by the
  ;; `result` declaration like any minted constant, and nothing is refused; the `cx/`
  ;; constant carries the role by its spelling and is typed nothing.
  (doseq [order [[:slot :arg] [:arg :slot]]]
    (tu/with-terms [PlaceFn Paris likes visited Tom Ann]
      (v/assert kb (list 'reifiable_function PlaceFn) 'CxUniverse)
      (v/assert kb (list 'result PlaceFn 'context) 'CxUniverse)
      (let [E    (list PlaceFn Paris)
            run  {:slot #(v/assert kb (list likes Tom Ann) E)
                  :arg  #(v/assert kb (list visited Tom E) 'CxUniverse)}
            hs   (into {} (map (fn [step] [step ((run step))])) order)
            kcx  (:context (v/sentex kb (:slot hs)))
            knat (nth (:sentence (v/sentex kb (:arg hs))) 2)
            maps (set (map #(second (:sentence %))
                           (v/sentexes-matching kb (list 'natFormula '?k E) 'CxUniverse)))]
        (testing (str order " the slot and the argument name two constants")
          (is (nat-read/reified-context-symbol? kcx))
          (is (nat-read/reified-object-symbol? knat))
          (is (= #{kcx knat} maps)))
        (testing (str order " each namespace maps the expression once")
          (is (= kcx (nat-read/dedup-constant kb E nat-read/context-namespace nil)))
          (is (= knat (nat-read/dedup-constant kb E)))
          (is (empty? (nat/colliding-constant-groups kb))))
        (testing (str order " the argument constant is a context by the result declaration")
          (is (v/ask? kb (list 'context knat) 'CxUniverse))
          (is (empty? (v/sentexes-matching kb (list 'context kcx) '?ctx))))
        (testing (str order " both reads answer")
          (is (v/ask? kb (list likes Tom Ann) E))
          (is (v/ask? kb (list visited Tom E) 'CxUniverse)))))))

;; ---- the context-slot shape check does not depend on the naming policy -----

(tu/deftest-kb naming-off-still-refuses-a-non-symbol-context-for-shape
  ;; `check-shape!` runs independent of the naming policy, and it checks that
  ;; reification yields a symbol — so a non-ground compound context is a `:shape` refusal
  ;; even under `:naming :off`, never a raw list in a sentex's context slot
  ;; (docs/context-nat.md).
  (let [cxfn   (declare-datetime-dimension! kb)
        kb-off (assoc kb :naming :off)]
    (testing "an UNDECLARED ground application reifies to a symbol and stores"
      (let [h (v/assert kb-off '(likes Tom Ann) (list 'CxBogusFn 'CxMonad (list 'DatetimeFn "2000")))]
        (is (nat-read/reified-context-symbol? (:context (v/sentex kb-off h))))))
    (testing "a DECLARED but NON-GROUND context is a shape error even with naming off"
      (is (= :shape (refusal #(v/assert kb-off '(likes Tom Ann)
                                        (list cxfn 'CxMonad '?x))))))
    (testing "a declared ground context still reifies to a symbol and stores (control)"
      (let [h (v/assert kb-off '(likes Tom Ann) (list cxfn 'CxMonad (list 'DatetimeFn "2000")))]
        (is (symbol? (:context (v/sentex kb-off h))))))))

;; ---- the stored-fact R oracle picks its supporter content-keyed ----------

(tu/deftest-kb the-stored-fact-oracle-chooses-its-supporter-by-content
  ;; `subintervalOf` has a comparator, so exercise the stored-fact branch with a
  ;; sub-relation that has none.  Two believed `(R a b)` facts, the same ground relation in
  ;; two contexts, are two routes, and the edge's justifications read in content order:
  ;; the first rests on the fact in the lexicographically-smallest context, never on the
  ;; one with the smaller handle (docs/context-nat.md, order independence).
  (let [cxfn  (declare-datetime-dimension! kb)
        yterm (list 'DatetimeFn "2000")
        mterm (list 'DatetimeFn "2000-01")
        year  (list cxfn 'CxMonad yterm)
        month (list cxfn 'CxMonad mterm)
        rfact (list 'subFooOf mterm yterm)
        above (tu/tmp-ctx "Side")]
    ;; two R-evidence facts, CxUniverse first (lower handle), then another context
    ;; (higher handle but the smaller context by content, `CxTmp…`) — so a
    ;; handle/retrieval-first pick and a content-first pick disagree.
    (v/assert kb rfact 'CxUniverse)
    (v/assert kb rfact above)
    (v/assert kb '(holiday NewYear) year)
    (v/assert kb '(weather Cold) month)
    (v/assert kb (list 'contextArgSubrelation cxfn 2 'subFooOf) 'CxUniverse)
    (let [ky (:context (tu/sentex-matching kb '(holiday NewYear) year))
          km (:context (tu/sentex-matching kb '(weather Cold) month))]
      (testing "the stored-fact oracle materialized the edge"
        (is (v/sees? kb km ky)))
      (let [edge  (tu/sentex-matching kb (list 'genlCx km ky) 'CxUniverse)
            justs (filter #(= 'contextArgSubrelation (:informant %))
                          (v/supporting-justifications kb (:id edge)))
            ev-cx (fn [just] (some #(when (= rfact (:sentence (v/sentex kb %))) (:context (v/sentex kb %)))
                                   (:antecedents just)))]
        (testing "its R-evidence supporter is the fact in the smallest context, not the first"
          (is (= above (ev-cx (first justs)))))
        (testing "each fact is a route of its own"
          (is (= [above 'CxUniverse] (map ev-cx justs))))))))

;; ---- the context slot reads back through the ranks it was written under ---

(tu/deftest-kb a-context-slot-resolves-the-same-way-reading-and-writing
  ;; `maybe-reify-context` mints on the write path and dedups on the read one, and the
  ;; two have to resolve an application to the same term or a fact stored under one
  ;; spelling is unreachable by the other.  A `(rewriteOf T E)` is the rank that shows it:
  ;; the write path resolves the slot to `T` and mints no `natFormula`, so a read that
  ;; consulted the dedup probe alone would answer `no-match` for a context it had just
  ;; stored into.
  (tu/with-terms [CxAlias Slot likes Tom Ann]
    (let [cxfn (fresh-cxfn "Alias")
          app  (list cxfn Slot)]
      (v/assert kb (list 'result cxfn 'context) 'CxUniverse)
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
    (v/assert kb (list 'result cxfn 'context) 'CxUniverse)
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
    (v/assert kb (list 'result cxfn 'context) 'CxUniverse)
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
    (v/assert kb (list 'result cxfn 'context) 'CxUniverse)
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

(tu/deftest-kb stated-bounds-arriving-after-both-contexts-order-them
  (let [cxfn (declare-calendar-dimension! kb)]
    (tu/with-terms [Spring Equinox Windy]
      (v/assert kb (list 'time_interval Spring) 'CxUniverse)
      (let [ks (:context (v/sentex kb (v/assert kb (list 'holiday Equinox) (list cxfn 'CxMonad Spring))))
            km (:context (v/sentex kb (v/assert kb (list 'weather Windy) (list cxfn 'CxMonad '(MonthFn 2000 3)))))
            _  (is (not (v/sees? kb km ks)) "no bounds yet")
            _  (v/assert kb (list 'startOf Spring '(InstantFn 2000 3 1 0 0 0)) 'CxUniverse)
            h  (v/assert kb (list 'endOf Spring '(InstantFn 2000 6 1 0 0 0)) 'CxUniverse)]
        (is (= [true false] [(v/sees? kb km ks) (v/sees? kb ks km)])
            "the second bound arriving last orders March below the named interval")
        (v/retract! kb h)
        (is (not (v/sees? kb km ks)) "retracting a bound withdraws the edge")))))

(tu/deftest-kb an-instant-order-arriving-after-both-contexts-and-their-named-bounds-orders-them
  (doseq [order [#(list 'instantBefore %1 %2) #(list 'instantAfter %2 %1)]]
    (let [cxfn (declare-calendar-dimension! kb)]
      (tu/with-terms [Spring April Mar1 Mar15 Apr1 May1 Jun1 Equinox Windy]
        (doseq [m [Mar1 Mar15 Apr1 May1 Jun1]] (v/assert kb (list 'time_point m) 'CxUniverse))
        (doseq [[i s e] [[Spring Mar1 Jun1] [April Apr1 May1]]]
          (v/assert kb (list 'time_interval i) 'CxUniverse)
          (v/assert kb (list 'startOf i s) 'CxUniverse)
          (v/assert kb (list 'endOf i e) 'CxUniverse))
        (v/assert kb (order Mar1 Mar15) 'CxUniverse)
        (v/assert kb (order May1 Jun1) 'CxUniverse)
        (let [ks (:context (v/sentex kb (v/assert kb (list 'holiday Equinox) (list cxfn 'CxMonad Spring))))
              ka (:context (v/sentex kb (v/assert kb (list 'weather Windy) (list cxfn 'CxMonad April))))
              _  (is (not (v/sees? kb ka ks)) "no chain from Spring's start to April's yet")
              h  (v/assert kb (order Mar15 Apr1) 'CxUniverse)]
          (is (= [true false] [(v/sees? kb ka ks) (v/sees? kb ks ka)])
              "the middle link of the chain arriving last orders April below Spring")
          (v/retract! kb h)
          (is (not (v/sees? kb ka ks)) "retracting the link withdraws the edge"))))))

(tu/deftest-kb a-slice-at-a-named-moment-is-ordered-below-a-named-interval-its-chain-places-it-in
  (doseq [chain-last? [false true]]
    (let [cxfn (declare-calendar-dimension! kb)]
      (tu/with-terms [Spring Mar1 Mar15 Jun1 Equinox Windy]
        (v/assert kb (list 'contextArgSubrelation cxfn 2 'subtimeOf) 'CxUniverse)
        (v/assert kb (list 'time_interval Spring) 'CxUniverse)
        (v/assert kb (list 'startOf Spring Mar1) 'CxUniverse)
        (v/assert kb (list 'endOf Spring Jun1) 'CxUniverse)
        (let [chain! #(doseq [[a b] [[Mar1 Mar15] [Mar15 Jun1]]]
                        (v/assert kb (list 'instantBefore a b) 'CxUniverse))
              at     #(list cxfn 'CxMonad %)
              _      (when-not chain-last? (chain!))
              ks     (:context (v/sentex kb (v/assert kb (list 'holiday Equinox) (at Spring))))]
          (when-not chain-last?
            (is (true? (v/ask? kb (list 'holiday Equinox) (at Mar15)))
                "the unwritten slice at the moment sees the interval's fact"))
          (let [km (:context (v/sentex kb (v/assert kb (list 'weather Windy) (at Mar15))))]
            (when chain-last? (chain!))
            (is (= [true false] [(v/sees? kb km ks) (v/sees? kb ks km)]))))))))

(tu/deftest-kb a-slice-at-a-stated-start-is-ordered-below-the-open-time-it-starts
  (doseq [start-last? [false true]]
    (let [cxfn (declare-calendar-dimension! kb)]
      (tu/with-terms [Since Equinox Windy Fog]
        (v/assert kb (list 'contextArgSubrelation cxfn 2 'subtimeOf) 'CxUniverse)
        (v/assert kb (list 'time_interval Since) 'CxUniverse)
        (let [start! #(v/assert kb (list 'startOf Since '(InstantFn 2000 1 1 0 0 0)) 'CxUniverse)
              at     #(list cxfn 'CxMonad %)
              h      (when-not start-last? (start!))
              ks     (:context (v/sentex kb (v/assert kb (list 'holiday Equinox) (at Since))))
              km     (:context (v/sentex kb (v/assert kb (list 'weather Windy)
                                                      (at '(InstantFn 2000 1 1 0 0 0)))))
              kl     (:context (v/sentex kb (v/assert kb (list 'weather Fog)
                                                      (at '(InstantFn 2000 6 1 0 0 0)))))
              h      (or h (start!))]
          (is (= [true false false] [(v/sees? kb km ks) (v/sees? kb ks km) (v/sees? kb kl ks)]))
          (v/retract! kb h)
          (is (not (v/sees? kb km ks))))))))

(tu/deftest-kb a-stated-end-before-the-start-leaves-the-slice-at-the-start-ordered
  (let [cxfn (declare-calendar-dimension! kb)]
    (tu/with-terms [Since Equinox Windy]
      (v/assert kb (list 'contextArgSubrelation cxfn 2 'subtimeOf) 'CxUniverse)
      (v/assert kb (list 'startOf Since '(InstantFn 2000 1 1 0 0 0)) 'CxUniverse)
      (v/assert kb (list 'endOf Since '(InstantFn 1999 1 1 0 0 0)) 'CxUniverse)
      (let [at #(list cxfn 'CxMonad %)
            ks (:context (v/sentex kb (v/assert kb (list 'holiday Equinox) (at Since))))
            km (:context (v/sentex kb (v/assert kb (list 'weather Windy) (at '(InstantFn 2000 1 1 0 0 0)))))]
        (is (v/sees? kb km ks))))))

(tu/deftest-kb allen-facts-order-two-slices-through-the-points-in-either-arrival-order
  (doseq [facts-last? [false true]]
    (let [cxfn (declare-calendar-dimension! kb)]
      (tu/with-terms [H Q R Fog Rain Sun]
        (let [at     #(list cxfn 'CxMonad %)
              facts! #(doseq [s [(list 'finishes Q H) (list 'overlaps H R)]]
                        (v/assert kb s 'CxUniverse))
              _      (when-not facts-last? (facts!))
              kh     (:context (v/sentex kb (v/assert kb (list 'weather Fog) (at H))))
              kq     (:context (v/sentex kb (v/assert kb (list 'weather Rain) (at Q))))
              kr     (:context (v/sentex kb (v/assert kb (list 'weather Sun) (at R))))
              _      (when facts-last? (facts!))]
          (is (= [true false false false] [(v/sees? kb kq kh) (v/sees? kb kh kq)
                                           (v/sees? kb kh kr) (v/sees? kb kr kh)]))
          (v/retract! kb (:id (tu/sentex-matching kb (list 'finishes Q H) 'CxUniverse)))
          (is (not (v/sees? kb kq kh))))))))

(tu/deftest-kb a-chain-of-subintervalof-facts-orders-the-slices-at-its-ends
  (doseq [chain-last? [false true]]
    (let [cxfn (declare-calendar-dimension! kb)]
      (tu/with-terms [Inner Mid Outer Fog Rain]
        (let [at     #(list cxfn 'CxMonad %)
              chain! #(doseq [[a b] [[Inner Mid] [Mid Outer]]]
                        (v/assert kb (list 'subintervalOf a b) 'CxUniverse))
              _      (when-not chain-last? (chain!))
              ko     (:context (v/sentex kb (v/assert kb (list 'weather Fog) (at Outer))))
              ki     (:context (v/sentex kb (v/assert kb (list 'weather Rain) (at Inner))))
              _      (when chain-last? (chain!))]
          (is (= [true false] [(v/sees? kb ki ko) (v/sees? kb ko ki)])))))))

(tu/deftest-kb a-slice-at-an-intersection-is-ordered-under-each-argument-and-what-holds-one
  (doseq [fact-last? [false true]]
    (let [cxfn (declare-calendar-dimension! kb)]
      (tu/with-terms [A B Z Fog Rain Hail]
        (let [at    #(list cxfn 'CxMonad %)
              cx    #(:context (v/sentex kb (v/assert kb (list 'weather %1) (at %2))))
              fact! #(v/assert kb (list 'subintervalOf A Z) 'CxUniverse)
              _     (when-not fact-last? (fact!))
              kz    (cx Fog Z)
              kab   (cx Rain (list 'TimeIntersectionFn B A))
              ka    (cx Hail A)
              _     (when fact-last? (fact!))]
          (is (= kab (cx Rain (list 'TimeIntersectionFn A B))))
          (is (= [true true false] [(v/sees? kb kab ka) (v/sees? kb kab kz) (v/sees? kb ka kab)])))))))

(tu/deftest-kb a-declared-time-position-takes-one-spelling-of-each-calendar-time
  (let [cxfn (declare-calendar-dimension! kb)
        cx   #(:context (v/sentex kb (v/assert kb (list 'weather %2) (list cxfn 'CxMonad %1))))]
    (tu/with-terms [Fog Rain]
      (testing "undeclared, two spellings of one month are two contexts"
        (is (not= (cx '(MonthFn 2000 1) Fog) (cx '(DatetimeFn "2000-01") Rain)))))
    (v/assert kb (list 'contextArgCalendarSpelling cxfn 2) 'CxUniverse)
    (doseq [[a b] '[[(DatetimeRangeFn "2000-01" "2000-06") (DatetimeRangeFn "2000-01-01" "2000-06-30T23")]
                    [(DatetimeFn "2000-01-15T1") (DatetimeFn "2000-01-15T01")]
                    [(EndFn (MonthFn 2000 1)) (InstantFn 2000 2 1 0 0 0)]
                    [(DatetimeRangeFn "2000-01" "2000-12") (YearFn 2000)]]]
      (tu/with-terms [Fog Rain]
        (is (= (cx a Fog) (cx b Rain)) (pr-str [a b]))))
    (tu/with-terms [Fog]
      (testing "the constant's expression holds the one spelling"
        (is (= [{'?e (list cxfn 'CxMonad '(DatetimeRangeFn "2000-01" "2000-06"))}]
               (v/ask kb (list 'natFormula (cx '(DatetimeRangeFn "2000-01-01" "2000-06-30T23") Fog) '?e)
                      'CxUniverse)))))))

(tu/deftest-kb a-link-to-a-calendar-moment-orders-a-slice-under-a-time-the-calendar-places
  (doseq [links-last? [false true]]
    (let [cxfn (declare-calendar-dimension! kb)]
      (tu/with-terms [Year Visit M N Fog Rain]
        (let [at     #(list cxfn 'CxMonad %)
              links! #(doseq [s [(list 'instantBefore '(InstantFn 2000 6 1 0 0 0) M)
                                 (list 'instantBefore N '(InstantFn 2000 9 1 0 0 0))]]
                        (v/assert kb s 'CxUniverse))]
          (doseq [s [(list 'startOf Year '(InstantFn 2000 1 1 0 0 0))
                     (list 'endOf Year '(InstantFn 2001 1 1 0 0 0))
                     (list 'startOf Visit M) (list 'endOf Visit N)]]
            (v/assert kb s 'CxUniverse))
          (when-not links-last? (links!))
          (let [ky (:context (v/sentex kb (v/assert kb (list 'weather Fog) (at Year))))
                kv (:context (v/sentex kb (v/assert kb (list 'weather Rain) (at Visit))))]
            (when links-last? (links!))
            (is (= [true false] [(v/sees? kb kv ky) (v/sees? kb ky kv)]))))))))

(tu/deftest-kb a-link-to-a-calendar-moment-orders-calendar-slices-inside-and-around-a-named-time
  (doseq [links-last? [false true]]
    (let [cxfn (declare-calendar-dimension! kb)]
      (tu/with-terms [Visit M N Fog Rain Sun]
        (let [at     #(list cxfn 'CxMonad %)
              cx     #(:context (v/sentex kb (v/assert kb (list 'weather %2) (at %1))))
              links! #(doseq [s [(list 'instantBefore '(InstantFn 2000 2 1 0 0 0) M)
                                 (list 'instantBefore M '(InstantFn 2000 7 1 0 0 0))
                                 (list 'instantBefore '(InstantFn 2000 8 1 0 0 0) N)
                                 (list 'instantBefore N '(InstantFn 2000 11 1 0 0 0))]]
                        (v/assert kb s 'CxUniverse))]
          (v/assert kb (list 'startOf Visit M) 'CxUniverse)
          (v/assert kb (list 'endOf Visit N) 'CxUniverse)
          (when-not links-last? (links!))
          (let [kv (cx Visit Rain)
                kj (cx '(MonthFn 2000 7) Sun)
                ky (cx '(YearFn 2000) Fog)]
            (when links-last? (links!))
            (is (= [true true false false]
                   [(v/sees? kb kj kv) (v/sees? kb kv ky) (v/sees? kb kv kj) (v/sees? kb ky kv)]))))))))

(tu/deftest-kb a-link-to-the-calendar-reads-no-other-fact-naming-a-time-in-the-month
  (let [cxfn (declare-calendar-dimension! kb)]
    (tu/with-terms [Visit E Ann seenAt Rain Sun CxWorld]
      (let [at     #(list cxfn 'CxMonad %)
            cx     #(:context (v/sentex kb (v/assert kb (list 'weather %2) (at %1))))
            seen   (into #{} (for [d (range 1 6)]
                               (v/assert kb (list seenAt Ann (list 'InstantFn 2000 2 d 12 0 0)) CxWorld)))
            km     (cx '(MonthFn 2000 2) Sun)
            kv     (cx Visit Rain)
            read   (volatile! #{})]
        (v/assert kb (list 'startOf Visit '(InstantFn 2000 2 10 0 0 0)) 'CxUniverse)
        (v/assert kb (list 'endOf Visit E) 'CxUniverse)
        (is (not (v/sees? kb kv km)))
        (binding [prof/*handle-sink* #(vswap! read conj %)]
          (v/assert kb (list 'instantBefore E '(InstantFn 2000 2 20 0 0 0)) 'CxUniverse))
        (is (v/sees? kb kv km))
        (is (empty? (set/intersection seen @read)))))))

(tu/deftest-kb a-genlcx-edge-a-rule-concludes-after-the-contexts-orders-them
  (tu/with-terms [CxLow CxHigh monadBelow]
    (let [cxfn (fresh-cxfn "Monad")]
      (v/assert kb (list 'result cxfn 'context) 'CxUniverse)
      (v/assert kb (list 'contextArgSubrelation cxfn 1 'genlMonad) 'CxUniverse)
      (v/assert kb (list 'forced_monotonic_predicate monadBelow) 'CxUniverse)
      (v/assert kb (list 'set/forwardRule (list 'implies (list monadBelow '?a '?b) (list 'genlCx '?a '?b)))
                'CxUniverse)
      (let [klo (:context (v/sentex kb (v/assert kb '(holiday NewYear) (list cxfn CxLow))))
            khi (:context (v/sentex kb (v/assert kb '(weather Cold) (list cxfn CxHigh))))
            _   (is (not (v/sees? kb klo khi)) "no evidence yet")
            h   (v/assert kb (list monadBelow CxLow CxHigh) 'CxUniverse)]
        (is (= [true true] [(v/sees? kb CxLow CxHigh) (v/sees? kb klo khi)])
            "the concluded edge orders the contexts along its two ends")
        (v/retract! kb h)
        (is (not (v/sees? kb klo khi)) "the edge's premise retracted")))))

(tu/deftest-kb no-monad-is-genlmonad-below-cxuniverse
  (tu/with-terms [CxLow CxHigh]
    (let [cxfn (fresh-cxfn "Monad")]
      (v/assert kb (list 'result cxfn 'context) 'CxUniverse)
      (v/assert kb (list 'contextArgSubrelation cxfn 1 'genlMonad) 'CxUniverse)
      (v/assert kb (list 'genlCx CxLow CxHigh) 'CxUniverse)
      (v/assert kb (list 'genlCx CxHigh 'CxUniverse) 'CxUniverse)
      (let [ctx-of #(:context (v/sentex kb (v/assert kb '(holiday NewYear) (list cxfn %))))
            klo    (ctx-of CxLow)
            khi    (ctx-of CxHigh)
            ktop   (ctx-of 'CxUniverse)]
        (is (v/sees? kb klo khi))
        (is (not (v/sees? kb klo ktop)) "the path ends on the implicit edge, which has no supporter")
        (is (not (v/sees? kb khi ktop)))))))

(tu/deftest-kb a-genlcx-edge-a-rule-concludes-once-a-formula-declaration-releases-it-orders-the-slices
  (doseq [order [:declaration-first :declaration-last]]
    (tu/with-terms [CxLow CxHigh holdsIn tag]
      (let [cxfn  (fresh-cxfn "Monad")
            slice #(:context (v/sentex kb (v/assert kb '(holiday NewYear) (list cxfn %))))
            decl! #(v/assert kb (list 'arg holdsIn 2 'sentence) 'CxUniverse)]
        (v/assert kb (list 'result cxfn 'context) 'CxUniverse)
        (v/assert kb (list 'contextArgSubrelation cxfn 1 'genlMonad) 'CxUniverse)
        (v/assert kb (list 'forced_monotonic_predicate holdsIn) 'CxUniverse)
        (when (= :declaration-first order) (decl!))
        (v/assert kb (list 'set/forwardRule (list 'implies (list holdsIn '?a (list '?p '?b)) (list 'genlCx '?a '?b)))
                  'CxUniverse)
        (v/assert kb (list holdsIn CxLow (list tag CxHigh)) 'CxUniverse)
        (let [k1 (slice CxLow) k2 (slice CxHigh)]
          (when (= :declaration-last order) (decl!))
          (is (= [true true] [(v/sees? kb CxLow CxHigh) (v/sees? kb k1 k2)]) (str order)))))))

(tu/deftest-kb a-genlcx-edge-orders-the-slices-of-the-slices-along-its-ends-in-either-order
  (doseq [ends [:monads :slices] order [:edge-first :edge-last]]
    (tu/with-terms [CxLow CxHigh]
      (let [cxfn  (fresh-cxfn "Monad")
            slice #(:context (v/sentex kb (v/assert kb '(holiday NewYear) (list cxfn %))))
            _     (v/assert kb (list 'result cxfn 'context) 'CxUniverse)
            _     (v/assert kb (list 'contextArgSubrelation cxfn 1 'genlMonad) 'CxUniverse)
            _     (when (= [:monads :edge-first] [ends order])
                    (v/assert kb (list 'genlCx CxLow CxHigh) 'CxUniverse))
            k1    (slice CxLow)
            k2    (slice CxHigh)
            edge! #(v/assert kb (if (= :monads ends) (list 'genlCx CxLow CxHigh) (list 'genlCx k1 k2))
                             'CxUniverse)
            _     (when (= [:slices :edge-first] [ends order]) (edge!))
            l1    (slice k1)
            l2    (slice k2)]
        (when (= :edge-last order) (edge!))
        (is (= [true true] [(v/sees? kb k1 k2) (v/sees? kb l1 l2)]) (str ends " " order))))))

(tu/deftest-kb a-slice-nesting-deeper-than-the-producer-rounds-logs-the-rounds-it-left
  (tu/with-terms [CxLow CxHigh]
    (let [cxfn  (fresh-cxfn "Monad")
          slice #(:context (v/sentex kb (v/assert kb '(holiday NewYear) (list cxfn %))))
          nest  #(reduce (fn [v _] (conj v (slice (peek v)))) [%1] (range %2))
          ids   (atom [])]
      (v/assert kb (list 'result cxfn 'context) 'CxUniverse)
      (v/assert kb (list 'contextArgSubrelation cxfn 1 'genlMonad) 'CxUniverse)
      (let [lows (nest CxLow 10) highs (nest CxHigh 10)]
        (binding [trove/*log-fn* (fn [_ns _coords _level id _payload] (swap! ids conj id))]
          (v/assert kb (list 'genlCx CxLow CxHigh) 'CxUniverse))
        (is (= [true true [:vaelii.impl.nat-maintenance/producer-rounds]]
               [(v/sees? kb (lows 1) (highs 1)) (v/sees? kb (lows 9) (highs 9))
                (filterv #{:vaelii.impl.nat-maintenance/producer-rounds} @ids)]))))))

(tu/deftest-kb a-stated-genlmonad-is-refused-and-the-genlcx-path-justifies-the-slice-edge
  (tu/with-terms [CxLow CxHigh]
    (let [cxfn  (fresh-cxfn "Monad")
          slice #(:context (v/sentex kb (v/assert kb '(holiday NewYear) (list cxfn %))))]
      (v/assert kb (list 'result cxfn 'context) 'CxUniverse)
      (v/assert kb (list 'contextArgSubrelation cxfn 1 'genlMonad) 'CxUniverse)
      (is (= :not-well-formed
             (tu/refusal-type #(v/assert kb (list 'genlMonad CxLow CxHigh) 'CxUniverse))))
      (let [h  (v/assert kb (list 'genlCx CxLow CxHigh) 'CxUniverse)
            k1 (slice CxLow)
            k2 (slice CxHigh)]
        (is (= [true true] [(v/sees? kb k1 k2) (v/ask? kb (list 'genlMonad CxLow CxHigh) 'CxUniverse)]))
        (v/retract! kb h)
        (is (= [false false] [(v/sees? kb k1 k2) (v/ask? kb (list 'genlMonad CxLow CxHigh) 'CxUniverse)]))))))

(tu/deftest-kb an-unwritten-slice-sees-both-its-supers-with-a-one-entry-supporter-cache
  (tu/with-terms [CxSupM CxSubM CxOtherM p q]
    (v/assert kb (list 'genlCx CxSupM 'CxWell) 'CxUniverse)
    (v/assert kb (list 'genlCx CxSubM CxSupM) 'CxUniverse)
    (let [h (v/assert kb (list 'genlCx CxOtherM 'CxWell) 'CxUniverse)]
      (v/assert kb (list 'except (list 'sentexHandle h)) CxOtherM))
    (v/assert kb (list p) (list 'CxTimeFn CxSubM '(YearFn 2000)))
    (v/assert kb (list q) (list 'CxTimeFn CxSupM '(MonthFn 2000 3)))
    (let [unwritten (list 'CxTimeFn CxSubM '(MonthFn 2000 3))]
      (try
        (v/set-cache-limit :taxonomy-supporters 1)
        (testing "an except on a genlCx supporter makes the walk read each edge's supporters"
          (is (= [true true] [(v/ask? kb (list p) unwritten) (v/ask? kb (list q) unwritten)])))
        (finally (v/set-cache-limit :taxonomy-supporters nil))))))

(tu/deftest-kb an-unwritten-slice-reads-its-supers-by-the-terms-containing-its-time
  (tu/with-terms [CxM CxSuperM Spring Q1 p q r]
    (let [cxfn (declare-calendar-dimension! kb)
          at   #(list cxfn %1 %2)
          dt   #(list 'DatetimeFn %)
          day  (dt "2000-03-05")
          e    (at CxM day)]
      (v/assert kb '(unreifiable_function DatetimeFn) 'CxUniverse)
      (v/assert kb '(unreifiable_function DatetimeRangeFn) 'CxUniverse)
      (v/assert kb (list 'contextArgSubrelation cxfn 1 'genlMonad) 'CxUniverse)
      (v/assert kb (list 'genlCx CxM CxSuperM) 'CxUniverse)
      (v/assert kb (list 'time_interval Spring) 'CxUniverse)
      (v/assert kb (list 'startOf Spring '(InstantFn 2000 3 1 0 0 0)) 'CxUniverse)
      (v/assert kb (list 'endOf Spring '(InstantFn 2000 6 1 0 0 0)) 'CxUniverse)
      (doseq [y (range 1960 1990)] (v/assert kb (list p) (at CxM (dt (str y)))))
      (v/assert kb (list p) (at CxM (dt "2000-04")))
      (let [qh (v/assert kb (list 'subintervalOf day Q1) 'CxUniverse)
            ks (set (for [t [(dt "2000") (dt "2000-3") '(DayFn 2000 3 5) '(DatetimeRangeFn "2000-02" "2000-04")
                             Spring Q1]]
                      (:context (v/sentex kb (v/assert kb (list p) (at CxM t))))))
            ks (conj ks (:context (v/sentex kb (v/assert kb (list p) (at CxSuperM day)))))]
        (with-redefs [cn/candidates (fn [& _] (throw (ex-info "read every context along the monad" {})))]
          (is (= ks (set (map first (#'cn/unminted-supers kb e))))))
        (v/assert kb (list r) (at CxM Q1))
        (is (true? (v/ask? kb (list r) e)))
        (v/assert kb (list q) (at CxM (dt "2000-03")))
        (is (true? (v/ask? kb (list q) e)) "a context minted after a read is read by the next")
        (v/retract! kb qh)
        (is (not (v/ask? kb (list r) e)) "a retraction after a read is read by the next")))))

;; ---- the computed edge's supporters, stated below the context it is stored in ----
;;
;; `materialize-edge` stores the computed `genlCx` in CxUniverse and justifies it by the two
;; `natFormula` sentexes, the `contextArgSubrelation` declaration and, for a dimension
;; resolved by stored facts, the `(R a b)` evidence.  Nothing requires the declaration or
;; the evidence to be stated where CxUniverse can see it, so the edge can rest on a
;; supporter in a context below its own.  These two tests assert that shape, and
;; `VAELII_AUDIT_SUPPORT` reports both justifications.

(defn- supporter-contexts
  "The contexts of every sentex a justification of handle `h` names, as a set."
  [kb h]
  (set (for [s (:support (tu/why-root kb h)) b (:because s)] (:context b))))

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
      (v/assert kb (list 'result cxfn 'context) 'CxUniverse)
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

(tu/deftest-kb a-re-derived-declaration-draws-no-membership-over-a-computed-edge
  ;; `(arg genlCx 1 context)` and `(arg genlCx 2 context)` are premises in CxUniverse; a
  ;; temporary rule derives them again, before or after the producer computes the edge.
  ;; The edge's placement draws no entailment, so the declaration's sweep over the stored
  ;; extent draws none from it either, and the emptied contexts are collected.
  (doseq [order [:edge-then-rule :rule-then-edge]]
    (tu/with-terms [trigger Pull]
      (let [cxfn      (declare-datetime-dimension! kb)
            _         (v/assert kb (list 'contextArgSubrelation cxfn 2 'subintervalOf) 'CxUniverse)
            _         (doseq [n [1 2]]
                        (v/assert kb (list 'set/forwardRule
                                           (list 'implies (list trigger '?x) (list 'arg 'genlCx n 'context)))
                                  'CxUniverse))
            rederive! #(v/assert kb (list trigger Pull) 'CxUniverse)
            contexts! #(vector (v/assert kb '(holiday NewYear) (list cxfn 'CxMonad (list 'DatetimeFn "2040")))
                               (v/assert kb '(weather Cold) (list cxfn 'CxMonad (list 'DatetimeFn "2040-01"))))
            [hy hm]   (case order
                        :edge-then-rule (let [hs (contexts!)] (rederive!) hs)
                        ;; the first firing precedes the edge; retracting and re-asserting
                        ;; the rule's premise derives the declarations again beside it
                        :rule-then-edge (let [ht (rederive!) hs (contexts!)]
                                          (v/retract! kb ht)
                                          (rederive!)
                                          hs))
            [ky km]   (map #(:context (v/sentex kb %)) [hy hm])
            reified?  #(boolean (seq (v/sentexes-matching kb (list 'natFormula % '?e) 'CxUniverse)))]
        (is (= [true [] []]
               [(v/sees? kb km ky)
                (v/sentexes-matching kb (list 'context km) '?c)
                (v/sentexes-matching kb (list 'context ky) '?c)])
            (str order ": the edge stands and no membership is drawn over it"))
        (is (= [false false] [(do (v/retract! kb hm) (reified? km)) (do (v/retract! kb hy) (reified? ky))])
            (str order ": each emptied context is collected"))))))
