;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.predall-test
  "The predAll / predExists / predInstance / predSpecified matrix (docs/predall.md,
  resources/kb/CxUniverse.txt).

  The *Instance* relations (predAllInstance / predInstanceAll) are rule generators that do
  REAL inference: every member of the quantified collection is concluded to bear the
  predicate to the fixed filler, and the conclusion retracts and belief-follows like any
  derived fact.

  The *Exists* relations (predAllExists / predExistsAll / predExistsInstance /
  predInstanceExists) are inferentially INERT: each declaration is a stored, queryable
  record beside a sanctioned per-cell full-arg placeholder functor an author may use for
  the unnamed filler.  The engine derives nothing — no skolem witness, no defn, no rule
  (Pace, \"skolems suck\").

  The *Specified* relations (predAllSpecified / predSpecifiedAll) are an integrity AUDIT
  that reports the instances with no *determinate* filler.  Indeterminate = a member of the
  extensible `indeterminate_term` category (skolem is its built-in first member), so an
  author-asserted *Exists* placeholder passes and a skolemised witness does not — the
  exact antagonist of the *Exists* class.  The same category drives the UNA identity
  exemption: the unique-name assumption is suspended for an unmerged indeterminate term.

  The tracer is predAllInstance on Pace's `sign` / `-212` example.  The generator's
  generated rule (defeasible, direction `:both` — `set/defaultRule`'s default) fires on a
  believed membership, and its backward arm closes the keystone: bare-literal membership
  derives (the evaluative defnSufficient provers, #59) and is discharged inside a
  query/prove proof (`pred-all-instance-keystone-proves-from-the-bare-literal`).  `ask`
  answers the same goal false by contract — the registry expands no rule."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.impl.predall :as predall]
            [vaelii.impl.resolution :as res]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (tu/load-core!))))

(defn- believes?
  "Is `sentence` a believed, stored sentex in `ctx`?  Read through `sentexes-matching`,
  which is belief-sensitive, rather than through `ask`."
  [kb sentence ctx]
  (boolean (seq (v/sentexes-matching kb sentence ctx))))

;; ==== the -212 subtlety, isolated ==========================================
;; Pace named -212 the keystone: (sign -212 "negative") should be provable from the BARE
;; literal, with membership DERIVED, not hand-asserted.  Both halves hold: membership
;; derives via the evaluative defnSufficient prover (#59), and the generated defaultRule's
;; backward arm discharges that antecedent inside a query/prove proof — see
;; pred-all-instance-keystone-proves-from-the-bare-literal.  The one instrument caveat:
;; `ask` expands no rule by contract, so the ask-mode answer is false by design, not gap.

(tu/deftest-kb minus-212-membership-is-derived
  ;; #59 closed the membership half of the keystone: bare-literal membership now derives,
  ;; no hand-assert needed.
  (is (v/ask? kb '(negative_integer -212) 'CxUniverse)
      "negative_integer membership of a bare literal derives via defnSufficient (#59)")
  (is (v/ask? kb '(integer -212) 'CxUniverse)
      "and integer membership too — now query-time evaluatable"))

;; ==== Instance class: real inference =======================================

(tu/deftest-kb pred-all-instance-mechanism-fires-on-a-believed-membership
  ;; the generator's generated defaultRule (bidirectional), on Pace's sign/-212 predicates:
  ;; once (negative_integer -212) is believed — here asserted directly, exercising the
  ;; forward arm on its own; the keystone test below covers the backward, query-time
  ;; path — the rule concludes (sign -212 "negative") and binds the fixed position.
  (v/assert kb '(binary_predicate sign) 'CxUniverse)
  (v/assert kb '(predAllInstance sign negative_integer "negative") 'CxUniverse)
  (v/assert kb '(negative_integer -212) 'CxUniverse)
  (is (v/ask? kb '(sign -212 "negative") 'CxUniverse)
      "every negative_integer is signed \"negative\", so -212 is")
  (is (= #{"negative"} (into #{} (map '?x) (v/ask kb '(sign -212 ?x) 'CxUniverse)))
      "and querying the fixed position binds it to the filler"))

(tu/deftest-kb pred-all-instance-keystone-proves-from-the-bare-literal
  ;; THE KEYSTONE, closed: with no hand-asserted membership, the generated rule's backward
  ;; arm discharges (negative_integer -212) through the evaluative defnSufficient prover
  ;; at query time, so the acceptance criterion holds from the bare literal.  Under `ask`
  ;; the same goal answers false BY CONTRACT — level 6 is the registry and expands no
  ;; rule (docs/levels.md) — so the pair below asserts both the capability and the
  ;; instrument distinction that once hid it.
  (v/assert kb '(binary_predicate sign) 'CxUniverse)
  (v/assert kb '(predAllInstance sign negative_integer "negative") 'CxUniverse)
  (is (v/query? kb '(sign -212 "negative") 'CxUniverse {:max-depth 5})
      "provable from the bare literal — membership derives inside the proof")
  (is (= [{'?x "negative"}] (vec (v/query kb '(sign -212 ?x) 'CxUniverse {:max-depth 5})))
      "and querying the fixed position binds it")
  (is (not (v/query? kb '(sign -212 "positive") 'CxUniverse {:max-depth 5}))
      "negative control: the wrong filler is not provable")
  (is (not (v/ask? kb '(sign -212 "negative") 'CxUniverse))
      "ask answers false by contract — the registry expands no rule; use query/prove"))

(tu/deftest-kb pred-all-instance-on-a-kind-without-a-defn
  ;; Pace: also cover a kind whose membership is asserted directly, not derived through a
  ;; defnNecessary/defnSufficient expansion.  A gensym'd type has no defn at all.
  (tu/with-terms [color widget Blueish W1]
    (v/assert kb (list 'binary_predicate color) 'CxUniverse)
    (v/assert kb (list 'unary_predicate widget) 'CxUniverse)
    (v/assert kb (list 'predAllInstance color widget Blueish) 'CxUniverse)
    (is (not (believes? kb (list color W1 Blueish) 'CxUniverse))
        "with no member yet, nothing is concluded")
    (v/assert kb (list widget W1) 'CxUniverse)
    (is (believes? kb (list color W1 Blueish) 'CxUniverse)
        "a directly-asserted member fires the generated rule")))

(tu/deftest-kb pred-all-instance-retracts-and-belief-follows
  (tu/with-terms [color widget Blueish W1]
    (v/assert kb (list 'binary_predicate color) 'CxUniverse)
    (v/assert kb (list 'unary_predicate widget) 'CxUniverse)
    (let [dh (v/assert kb (list 'predAllInstance color widget Blueish) 'CxUniverse)]
      (v/assert kb (list widget W1) 'CxUniverse)
      (is (believes? kb (list color W1 Blueish) 'CxUniverse))
      (v/retract! kb dh)
      (is (not (believes? kb (list color W1 Blueish) 'CxUniverse))
          "retracting the declaration withdraws the generated rule and its conclusion"))))

(tu/deftest-kb a-generator-declaration-reaches-the-members-already-stored
  ;; The arrival order every other test here writes the other way round: the members are
  ;; stored first and the declaration second, so the generated rule arrives over an extent
  ;; that already exists.  Both cells, and both must read as the declaration-first
  ;; ordering does — a generator whose descent depended on which came first would make
  ;; belief a function of the file.
  (testing "predAllInstance"
    (tu/with-terms [color widget Blueish W1]
      (v/assert kb (list 'binary_predicate color) 'CxUniverse)
      (v/assert kb (list 'unary_predicate widget) 'CxUniverse)
      (v/assert kb (list widget W1) 'CxUniverse)
      (v/assert kb (list 'predAllInstance color widget Blueish) 'CxUniverse)
      (is (believes? kb (list color W1 Blueish) 'CxUniverse)
          "the generated rule fires on the member stored before it")))
  (testing "predInstanceAll"
    (tu/with-terms [enjoys Alice hobby Chess]
      (v/assert kb (list 'binary_predicate enjoys) 'CxUniverse)
      (v/assert kb (list 'unary_predicate hobby) 'CxUniverse)
      (v/assert kb (list hobby Chess) 'CxUniverse)
      (v/assert kb (list 'predInstanceAll enjoys Alice hobby) 'CxUniverse)
      (is (believes? kb (list enjoys Alice Chess) 'CxUniverse)
          "the argument-swapped twin reaches back the same way"))))

(tu/deftest-kb a-generator-a-genl-edge-and-a-member-agree-in-every-order
  ;; The third ingredient: the member is of a **sub**collection, so the descent runs
  ;; through a `genl` edge and the declaration, the edge and the fact are three things
  ;; that can arrive in any of six orders.  Each is a different retroactive arm — the
  ;; generated rule reaching stored facts, the edge making stored facts matchable at the
  ;; declared collection, the fact meeting a rule already indexed — and all six must
  ;; conclude the same thing.
  (doseq [order [[:decl :edge :fact] [:decl :fact :edge] [:edge :decl :fact]
                 [:edge :fact :decl] [:fact :decl :edge] [:fact :edge :decl]]]
    (tu/with-terms [color widget subwidget Blueish W1]
      (v/assert kb (list 'binary_predicate color) 'CxUniverse)
      (v/assert kb (list 'unary_predicate widget) 'CxUniverse)
      (v/assert kb (list 'unary_predicate subwidget) 'CxUniverse)
      (doseq [step order]
        (case step
          :decl (v/assert kb (list 'predAllInstance color widget Blueish) 'CxUniverse)
          :edge (v/assert kb (list 'genl subwidget widget) 'CxUniverse)
          :fact (v/assert kb (list subwidget W1) 'CxUniverse)))
      (is (believes? kb (list color W1 Blueish) 'CxUniverse)
          (str "order " (pr-str order) ": the subcollection's member is signed too")))))

(tu/deftest-kb pred-instance-all-is-the-argument-swapped-twin
  ;; the fixed filler bears ?pred to every member of the collection, at position 2
  (tu/with-terms [enjoys Alice hobby Chess Sudoku]
    (v/assert kb (list 'binary_predicate enjoys) 'CxUniverse)
    (v/assert kb (list 'unary_predicate hobby) 'CxUniverse)
    (v/assert kb (list 'predInstanceAll enjoys Alice hobby) 'CxUniverse)
    (v/assert kb (list hobby Chess) 'CxUniverse)
    (v/assert kb (list hobby Sudoku) 'CxUniverse)
    (is (= #{Chess Sudoku} (into #{} (map '?y) (v/ask kb (list enjoys Alice '?y) 'CxUniverse)))
        "Alice enjoys every hobby")))

;; ==== Exists class: pure record, inferentially inert =======================
;; Pace's ruling (2026-09-03): everything with "exist" in the name is inferentially
;; inert — a stored, queryable record plus a sanctioned per-cell placeholder functor
;; for authors, and the engine derives NOTHING.  This supersedes the earlier generator
;; design that materialized (?pred ?x P) over the members; inertness is also what makes
;; the two pure-existential cross-cells expressible (nothing to generate, so no range
;; restriction to fail and no variable-functor rule to pollute the planner with).

(tu/deftest-kb an-exists-declaration-is-a-record-and-derives-nothing
  (tu/with-terms [owns person dog Alice]
    (v/assert kb (list 'binary_predicate owns) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'unary_predicate dog) 'CxUniverse)
    (v/assert kb (list 'predAllExists owns person dog) 'CxUniverse)
    (v/assert kb (list person Alice) 'CxUniverse)
    (is (v/ask? kb (list 'predAllExists owns person dog) 'CxUniverse)
        "the declaration is stored and queryable like any fact")
    (is (empty? (into #{} (map '?y) (v/ask kb (list owns Alice '?y) 'CxUniverse)))
        "and no filler is concluded for any member — inferentially inert")
    (is (empty? (into #{} (map '?y) (v/ask kb (list dog '?y) 'CxUniverse)))
        "no placeholder membership is materialized either")))

(tu/deftest-kb all-four-exists-cells-are-inert-records
  ;; the straight cells and the pure-existential cross-cells are uniform under inertness:
  ;; four declarations stored, zero facts derived
  (tu/with-terms [rel person dog Alice Rome]
    (v/assert kb (list 'binary_predicate rel) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'unary_predicate dog) 'CxUniverse)
    (v/assert kb (list 'predAllExists rel person dog) 'CxUniverse)
    (v/assert kb (list 'predExistsAll rel dog person) 'CxUniverse)
    (v/assert kb (list 'predExistsInstance rel person Rome) 'CxUniverse)
    (v/assert kb (list 'predInstanceExists rel Rome dog) 'CxUniverse)
    (v/assert kb (list person Alice) 'CxUniverse)
    (is (v/ask? kb (list 'predExistsInstance rel person Rome) 'CxUniverse)
        "a pure-existential cross-cell is storable and queryable")
    (is (v/ask? kb (list 'predInstanceExists rel Rome dog) 'CxUniverse)
        "and its argument-swapped twin")
    (is (empty? (into [] (v/ask kb (list rel '?x '?y) 'CxUniverse)))
        "none of the four declarations concludes a single fact of the subject predicate")))

(tu/deftest-kb each-exists-cell-reports-the-subjects-with-no-filler
  (tu/with-terms [owns person dog Alice Bob Rex Fido]
    (v/assert kb (list 'binary_predicate owns) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'unary_predicate dog) 'CxUniverse)
    (doseq [x [Alice Bob]] (v/assert kb (list person x) 'CxUniverse))
    (doseq [x [Rex Fido]] (v/assert kb (list dog x) 'CxUniverse))
    (v/assert kb (list owns Alice Rex) 'CxUniverse)
    (doseq [[declaration violations]
            [[(list 'predAllExists owns person dog)      #{Bob}]
             [(list 'predExistsAll owns person dog)      #{Fido}]
             [(list 'predExistsInstance owns person Rex) #{}]
             [(list 'predExistsInstance owns person Fido) #{Fido}]
             [(list 'predInstanceExists owns Alice dog)  #{}]
             [(list 'predInstanceExists owns Bob dog)    #{Bob}]]]
      (is (= {:status :audited :violations violations}
             (v/exists-violations kb declaration 'CxUniverse))
          (pr-str declaration)))
    (testing "all-specified-violations audits each stored declaration, keyed by its tuple"
      (v/assert kb (list 'predAllExists owns person dog) 'CxUniverse)
      (v/assert kb (list 'predInstanceExists owns Alice dog) 'CxUniverse)
      (is (= {['predAllExists owns person dog] {:status :audited :violations #{Bob}}}
             (v/all-specified-violations kb 'CxUniverse))))
    (is (= :bad-args (try (v/exists-violations kb (list 'predAllSpecified owns person) 'CxUniverse)
                          nil
                          (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))))

(tu/deftest-kb an-exists-audit-counts-a-placeholder-and-an-indeterminate-filler
  ;; existence is the whole requirement, where predAllSpecified asks for a determinate one
  (tu/with-terms [owns person dog vague_kind Alice Bob Fuzzy]
    (v/assert kb (list 'binary_predicate owns) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'unary_predicate dog) 'CxUniverse)
    (v/assert kb (list 'genl vague_kind 'indeterminate_term) 'CxUniverse)
    (doseq [x [Alice Bob]] (v/assert kb (list person x) 'CxUniverse))
    (v/assert kb (list owns Alice (list 'PredAllExistsFn owns person dog Alice)) 'CxUniverse)
    (v/assert kb (list vague_kind Fuzzy) 'CxUniverse)
    (v/assert kb (list dog Fuzzy) 'CxUniverse)
    (v/assert kb (list owns Bob Fuzzy) 'CxUniverse)
    (is (= {:status :audited :violations #{}}
           (v/exists-violations kb (list 'predAllExists owns person dog) 'CxUniverse)))))

(tu/deftest-kb a-placeholder-fact-types-its-subject-and-its-placeholder
  ;; `predAllExistsPlaceholder`'s subject is a member of the second argument and its
  ;; placeholder of the third (`argArg`), so a stated fact types both
  (tu/with-terms [rel person dog Alice Rex]
    (v/assert kb (list 'binary_predicate rel) 'CxUniverse)
    (v/assert kb (list 'genl person 'thing) 'CxUniverse)
    (v/assert kb (list 'genl dog 'thing) 'CxUniverse)
    (tu/with-entailing
      (v/assert kb (list 'predAllExistsPlaceholder rel person dog Alice Rex) 'CxUniverse)
      (is (v/isa? kb Alice person 'CxUniverse) "the subject is a member of the second argument")
      (is (v/isa? kb Rex dog 'CxUniverse) "and the placeholder of the third"))))

(tu/deftest-kb pred-exists-all-is-universal-second-existential-first
  ;; (predExistsAll worksFor person company): every company has some person who works
  ;; for it — the argument-swapped twin of predAllExists, universal over position 2 and
  ;; the witness at position 1.  The filler varies with the company it is required of,
  ;; so PredExistsAllFn takes that company as its subject, exactly as PredAllExistsFn
  ;; takes its member, and the placeholder predicate carries the subject too.
  (testing "the function and its predicate carry the subject"
    (is (v/ask? kb '(arity PredExistsAllFn 4) 'CxUniverse) "PredExistsAllFn takes four arguments")
    (is (v/isa? kb 'PredExistsAllFn 'fixed_arity_function))
    (is (not (v/isa? kb 'PredExistsAllFn 'ternary_function)) "and is not ternary")
    (is (v/ask? kb '(resultArg PredExistsAllFn 2) 'CxUniverse) "its value is a ?dep member")
    (is (v/ask? kb '(argArg PredExistsAllFn 4 3) 'CxUniverse) "its subject is an ?indep member")
    (is (v/ask? kb '(arity predExistsAllPlaceholder 5) 'CxUniverse)
        "the placeholder predicate takes the subject and the placeholder last")
    (is (v/ask? kb '(argArg predExistsAllPlaceholder 4 3) 'CxUniverse))
    (is (v/ask? kb '(argArg predExistsAllPlaceholder 5 2) 'CxUniverse)))
  (tu/with-terms [worksFor person company Acme Pat]
    (v/assert kb (list 'binary_predicate worksFor) 'CxUniverse)
    (v/assert kb (list 'genl person 'thing) 'CxUniverse)
    (v/assert kb (list 'genl company 'thing) 'CxUniverse)
    (v/assert kb (list 'predExistsAll worksFor person company) 'CxUniverse)
    (testing "a placeholder fact over a subject types the subject and the placeholder"
      (tu/with-entailing
        (v/assert kb (list 'predExistsAllPlaceholder worksFor person company Acme Pat)
                  'CxUniverse)
        (is (v/isa? kb Acme company 'CxUniverse) "the subject is a member of ?indep")
        (is (v/isa? kb Pat person 'CxUniverse) "and the placeholder of ?dep")))
    (testing "the subjectless four-place spelling is read OUT"
      (tu/with-terms [Pat2]
        (is (tu/stored-in-clash? kb (list 'predExistsAllPlaceholder worksFor person company Pat2)
                                 'CxUniverse))))))

(tu/deftest-kb a-placeholder-is-sanctioned-vocabulary-the-author-asserts
  ;; the per-cell full-arg functor is the author's term for the unnamed filler: usable in
  ;; hand-asserted sentences, structural (unreifiable), and distinct per cell — the
  ;; predAllExists and predExistsAll placeholders over the same (rel, dog) are two terms,
  ;; not one shared filler (Pace, "eventually it will matter that they're distinct")
  (tu/with-terms [rel person dog Alice]
    (v/assert kb (list 'binary_predicate rel) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'unary_predicate dog) 'CxUniverse)
    (v/assert kb (list 'predAllExists rel person dog) 'CxUniverse)
    (v/assert kb (list 'predExistsAll rel dog person) 'CxUniverse)
    (v/assert kb (list person Alice) 'CxUniverse)
    (let [p1 (list 'PredAllExistsFn rel person dog Alice)
          p2 (list 'PredExistsAllFn rel dog person Alice)]
      (v/assert kb (list dog p1) 'CxUniverse)
      (v/assert kb (list dog p2) 'CxUniverse)
      (v/assert kb (list rel Alice p1) 'CxUniverse)
      (is (v/ask? kb (list rel Alice p1) 'CxUniverse)
          "an author-asserted sentence naming the placeholder is believed like any fact")
      (let [fillers (into #{} (map '?y) (v/ask kb (list rel Alice '?y) 'CxUniverse))]
        (is (= 1 (count fillers)) "and answers as a filler")
        (is (not (v/reified-term? (first fillers)))
            "staying a structural NAT — unreifiable, readable inside the sentence"))
      (is (= 2 (count (into #{} (map '?y) (v/ask kb (list dog '?y) 'CxUniverse))))
          "the two cells' placeholders are two distinct dog members, not one shared term"))))

;; The aspirational existential-inference test (Pace, 2026-08-29 — KEEP, do NOT delete).
;; Under pure-record inert semantics nothing at all is derivable from the declaration,
;; so no existential filler for `(parts Lain ?x)` is provable.  That is the expected
;; outcome and it is asserted here as a standing marker for future existential-inference
;; work rather than as a passing feature.
;;
;; Cyc taught us that skolems suck, so we're not prioritizing this line of inference
(tu/deftest-kb exists-inference-from-a-predAllExists-is-not-yet-supported
  (tu/with-terms [parts construct mind Lain]
    (v/assert kb (list 'binary_predicate parts) 'CxUniverse)
    (v/assert kb (list 'unary_predicate construct) 'CxUniverse)
    (v/assert kb (list 'unary_predicate mind) 'CxUniverse)
    (v/assert kb (list 'predAllExists parts construct mind) 'CxUniverse)
    (is (not (v/ask? kb (list 'thereExists '?x
                              (list 'and (list mind '?x) (list parts Lain '?x)))
                     'CxUniverse))
        "no existential mind part of Lain is derivable from the inert record — pending")))

;; ==== Specified class: an integrity audit ==================================

(tu/deftest-kb pred-all-specified-reports-instances-with-no-determinate-filler
  ;; binary form: the required filler type is DERIVED from hasPet's own slot-2 contract
  ;; ((arg hasPet 2 pet)), never restated in the declaration.
  (tu/with-terms [hasPet person pet Alice Bob Carol Rex]
    (v/assert kb (list 'binary_predicate hasPet) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'unary_predicate pet) 'CxUniverse)
    (v/assert kb (list 'arg hasPet 2 pet) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified hasPet person) 'CxUniverse)
    (v/assert kb (list person Alice) 'CxUniverse)   ; a determinate filler
    (v/assert kb (list person Bob) 'CxUniverse)     ; no filler at all
    (v/assert kb (list person Carol) 'CxUniverse)   ; a filler of unknown type
    (v/assert kb (list hasPet Alice Rex) 'CxUniverse)
    (v/assert kb (list pet Rex) 'CxUniverse)
    (tu/with-terms [NotAPet]
      (v/assert kb (list hasPet Carol NotAPet) 'CxUniverse))
    (let [vs (:violations (predall/specified-violations kb hasPet person 'CxUniverse))]
      (is (not (contains? vs Alice)) "Alice has a determinate pet")
      (is (contains? vs Bob) "Bob has no filler at all")
      ;; Carol PASSES, and the pass is the design: the audit's membership question is
      ;; answered by the KB's own reading, and with (arg hasPet 2 pet) visible,
      ;; argument-type inference types her stored filler off that very declaration.
      ;; An audit stricter than the contract it derives from would be the second type
      ;; system the binary form exists to remove; the conformance bite lives at the
      ;; assert-time checker (which refuses a filler it can convict) and on the
      ;; kind-position arms tested below.
      (is (not (contains? vs Carol))
          "a stored filler is typed by the slot contract itself — no second type system"))))

(tu/deftest-kb a-ternary-pred-all-specified-is-read-out
  ;; the old three-place spellings are gone, not tolerated: both functors are
  ;; binary_predicates, so a ternary form is stored as an inert tuple and every reader
  ;; that sees the binding takes it OUT instead of quietly believing a second type system.
  (tu/with-terms [hasPet person pet managedBy manager report]
    (v/assert kb (list 'binary_predicate hasPet) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'unary_predicate pet) 'CxUniverse)
    (v/assert kb (list 'binary_predicate managedBy) 'CxUniverse)
    (v/assert kb (list 'unary_predicate manager) 'CxUniverse)
    (v/assert kb (list 'unary_predicate report) 'CxUniverse)
    (doseq [[functor a b c] [['predAllSpecified hasPet person pet]
                             ['predSpecifiedAll managedBy manager report]]]
      (is (tu/stored-in-clash? kb (list functor a b c) 'CxUniverse)
          (str "the retired ternary " functor " spelling is read OUT")))))

(tu/deftest-kb argn-spellings-share-args-declaration-checks
  ;; the binary projections run arg's own declaration
  ;; arms at the projected position, so a declaration the ternary spelling refuses is
  ;; refused identically under the binary one instead of storing believed-but-inert.
  (tu/with-terms [owns dog]
    (v/assert kb (list 'binary_predicate owns) 'CxUniverse)
    (v/assert kb (list 'unary_predicate dog) 'CxUniverse)
    (try (v/assert kb (list 'arg3 owns dog) 'CxUniverse)
         (is false "arg3 on a binary predicate must refuse — the ternary spelling does")
         (catch clojure.lang.ExceptionInfo e
           (is (= :arg-position (:type (ex-data e)))
               "same arm, same typed reason as (arg owns 3 dog)")))
    (is (not (v/ask? kb (list 'arg3 owns '?t) 'CxUniverse))
        "and nothing stored a believed-but-inert binary spelling")
    (tu/with-terms [kindOf]
      (v/assert kb (list 'type_relation_predicate kindOf) 'CxUniverse)
      (is (v/assert kb (list 'arg1 kindOf 'unary_predicate) 'CxUniverse)
          "arg on a type_relation_predicate is admitted through arg1, as the ternary is")
      (is (= [] (mapv :type (v/check kb (list 'interArg kindOf 1 dog 2 dog) 'CxUniverse)))
          "and so is an interArg over the same relation"))))

(tu/deftest-kb args-entails-argAndRest-from-the-first-position
  ;; `(args P T)` states what `(argAndRest P 1 T)` states, so asking the tail form of a
  ;; relation declared through the every-position form is answered — proved at query time,
  ;; so the store keeps the one declaration that was written.
  (tu/with-terms [tally animal]
    (v/assert kb (list 'variable_arity_predicate tally) 'CxUniverse)
    (v/assert kb (list 'genl animal 'thing) 'CxUniverse)
    (v/assert kb (list 'args tally animal) 'CxUniverse)
    (is (= [{'?n 1 '?t animal}]
           (v/query kb (list 'argAndRest tally '?n '?t) 'CxUniverse {:max-depth 3}))
        "args entails argAndRest at 1, and only at 1")
    (is (empty? (v/sentexes-matching kb (list 'argAndRest tally '?n '?t) 'CxUniverse))
        "and nothing is stored, so the covering check reads the declaration once")))

(tu/deftest-kb a-declaration-without-slot-typing-is-a-reported-gap
  ;; missing slot typing is an explicit declaration-contract diagnostic, never a silent
  ;; unconstrained audit: an untyped pred's declaration reports {:gap …}, and the sweep
  ;; carries the gap where a clean sweep would omit the declaration.
  (tu/with-terms [likes person Alice Bob]
    (v/assert kb (list 'binary_predicate likes) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified likes person) 'CxUniverse)
    (v/assert kb (list person Alice) 'CxUniverse)
    (v/assert kb (list likes Alice Bob) 'CxUniverse)
    (let [r (predall/specified-violations kb likes person 'CxUniverse)]
      (is (= :gap (:status r)) "the stable discriminant names the variant")
      (is (= :missing-slot-typing (:gap r)) "the gap is named, not absorbed")
      (is (= 2 (:position r)) "and carries the audited position")
      (is (nil? (:violations r)) "no violation set pretends the audit ran"))
    (is (= {:status :gap :gap :missing-slot-typing :pred likes :position 2}
           (get (predall/all-specified-violations kb 'CxUniverse)
                ['predAllSpecified likes person]))
        "the sweep reports the gap — it can never pass as a clean declaration")))

(tu/deftest-kb inherited-slot-typing-reaches-the-audit
  ;; the write-once-at-the-general-predicate pattern: the sub-predicate carries no
  ;; declaration of its own, the super's (arg parentOf 2 person) binds its tuples at
  ;; assert, and the audit reads the same constraining-predicates union — a sub whose
  ;; contract is entirely inherited audits, it does not gap.
  (tu/with-terms [parentOf fatherOf person Alice Bob]
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'binary_predicate parentOf) 'CxUniverse)
    (v/assert kb (list 'binary_predicate fatherOf) 'CxUniverse)
    (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
    (v/assert kb (list 'arg parentOf 2 person) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified fatherOf person) 'CxUniverse)
    (v/assert kb (list person Alice) 'CxUniverse)
    (v/assert kb (list person Bob) 'CxUniverse)
    (v/assert kb (list fatherOf Bob Alice) 'CxUniverse)
    (let [r (predall/specified-violations kb fatherOf person 'CxUniverse)]
      (is (= :audited (:status r))
          "the inherited contract is visible — no spurious gap on a fully-typed sub")
      (is (not (contains? (:violations r) Bob)) "Bob's filler satisfies it")
      (is (contains? (:violations r) Alice) "and Alice, fathering nothing, violates"))))

(tu/deftest-kb tail-slot-typing-reaches-the-audit
  ;; the audit reads the slot's contract through `res/arg-constraints-at`, so a slot an
  ;; `argAndRest` or `args` types is typed, as the assert-time checker reads it
  (tu/with-terms [likes admires person Alice Bob Carol]
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'binary_predicate likes) 'CxUniverse)
    (v/assert kb (list 'argAndRest likes 2 person) 'CxUniverse)
    (v/assert kb (list 'binary_predicate admires) 'CxUniverse)
    (v/assert kb (list 'args admires person) 'CxUniverse)
    (doseq [x [Alice Bob Carol]] (v/assert kb (list person x) 'CxUniverse))
    (v/assert kb (list likes Alice Bob) 'CxUniverse)
    (v/assert kb (list admires Bob Carol) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified likes person) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified admires person) 'CxUniverse)
    (let [r (predall/specified-violations kb likes person 'CxUniverse)]
      (is (= :audited (:status r)) "argAndRest from 2 types the audited slot")
      (is (= #{Bob Carol} (:violations r))))
    (let [r (predall/specified-violations kb admires person 'CxUniverse)]
      (is (= :audited (:status r)) "args types every slot, the audited one included")
      (is (= #{Alice Carol} (:violations r))))))

(tu/deftest-kb a-type-relation-slot-audits-the-type-position-arm
  ;; the type_relation_predicate arm in isolation, content and all: the checker has no
  ;; ground-fact arm for a type-level position, so the audit's constraint is the union
  ;; of the two type readings — a kind under thing passes, a declared-but-unplaced
  ;; unary_predicate passes, and a bare individual with no type evidence violates.
  (tu/with-terms [governsKind meta_kind placed_kind orphan_kind M1 M2 M3 NotAType]
    (v/assert kb (list 'unary_predicate meta_kind) 'CxUniverse)
    (v/assert kb (list 'binary_predicate governsKind) 'CxUniverse)
    (v/assert kb (list 'type_relation_predicate governsKind) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified governsKind meta_kind) 'CxUniverse)
    (v/assert kb (list meta_kind M1) 'CxUniverse)
    (v/assert kb (list meta_kind M2) 'CxUniverse)
    (v/assert kb (list meta_kind M3) 'CxUniverse)
    (v/assert kb (list 'genl placed_kind 'thing) 'CxUniverse)
    (v/assert kb (list 'unary_predicate orphan_kind) 'CxUniverse)
    (v/assert kb (list governsKind M1 placed_kind) 'CxUniverse)  ; genl reading
    (v/assert kb (list governsKind M2 orphan_kind) 'CxUniverse)  ; membership reading
    (v/assert kb (list governsKind M3 NotAType) 'CxUniverse)     ; neither
    (let [r (predall/specified-violations kb governsKind meta_kind 'CxUniverse)]
      (is (= :audited (:status r)) "a trp membership is a real slot contract, not a gap")
      (is (not (contains? (:violations r) M1)) "a kind under thing passes the genl reading")
      (is (not (contains? (:violations r) M2))
          "a declared-but-unplaced unary_predicate passes the membership reading")
      (is (contains? (:violations r) M3)
          "a filler with no type evidence of any kind violates"))))

(tu/deftest-kb constraints-compose-as-a-conjunction-not-a-disjunction
  ;; The composition is `every?`, and it CANNOT be distinguished from `some` on stored
  ;; facts: the assert-time checker refuses exactly the fillers a second enforced
  ;; constraint would catch (a kind reaching the wrong place and an individual are both
  ;; convicted at :arg-genl), and the one audit-only arm — :type-position — is subsumed
  ;; by any subtype constraint it could pair with. So the conjunction is killed at the
  ;; unit level, calling the private reader with a hand-built two-constraint typings and
  ;; a filler that satisfies exactly one: under `every?` it fails, under `some` it passes.
  (tu/with-terms [rel meta_k passes fails F1 Y]
    (v/assert kb (list 'binary_predicate rel) 'CxUniverse)
    (v/assert kb (list 'unary_predicate meta_k) 'CxUniverse)
    (v/assert kb (list 'unary_predicate passes) 'CxUniverse)
    (v/assert kb (list 'unary_predicate fails) 'CxUniverse)
    (v/assert kb (list meta_k F1) 'CxUniverse)
    (v/assert kb (list rel F1 Y) 'CxUniverse)
    (v/assert kb (list passes Y) 'CxUniverse)          ; Y is a `passes`, not a `fails`
    (let [admissible? @#'predall/admissible-filler?
          one         {:check :membership :type passes}
          other       {:check :membership :type fails}]
      (is (true?  (admissible? kb rel F1 #{one} 2 'CxUniverse))
          "Y alone satisfies the one constraint it meets")
      (is (false? (admissible? kb rel F1 #{one other} 2 'CxUniverse))
          "but not both — a filler meeting one of two constraints is not admissible"))))

(tu/deftest-kb membership-self-satisfaction-is-the-documented-design
  ;; the membership arm's vacuity for stored fillers is a documented contract, not an
  ;; accident: argument-type inference answers (zpet2 y) off the very (arg zgoverns2 2
  ;; zpet2) declaration the constraint derives from, so a stored filler cannot fail the
  ;; arm — the conformance bite for instance positions lives at the assert-time checker.
  (tu/with-terms [zgoverns2 zmeta2 zpet2 M1 Anything]
    (v/assert kb (list 'unary_predicate zmeta2) 'CxUniverse)
    (v/assert kb (list 'unary_predicate zpet2) 'CxUniverse)
    (v/assert kb (list 'binary_predicate zgoverns2) 'CxUniverse)
    (v/assert kb (list 'arg zgoverns2 2 zpet2) 'CxUniverse)
    (v/assert kb (list zmeta2 M1) 'CxUniverse)
    (v/assert kb (list zgoverns2 M1 Anything) 'CxUniverse)
    (is (v/ask? kb (list zpet2 Anything) 'CxUniverse)
        "any stored filler is a member by the KB's own reading — the declaration types it")
    (v/assert kb (list 'predAllSpecified zgoverns2 zmeta2) 'CxUniverse)
    (is (= {:status :audited :violations #{}}
           (predall/specified-violations kb zgoverns2 zmeta2 'CxUniverse))
        "so a single arg-typed constraint can only be failed by absence or indeterminacy")))

(tu/deftest-kb a-stale-arg-pos-is-refused-typed
  ;; the retired 5-argument call shape collides with the new arity — an unmigrated
  ;; caller's context symbol lands in arg-pos — and must surface as the typed refusal
  ;; the daemon's 400 contract routes, not an anonymous case miss.
  (tu/with-terms [hasPet person pet]
    (v/assert kb (list 'binary_predicate hasPet) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (try (predall/specified-violations kb hasPet person 'CxUniverse pet)
         (is false "a non-:second/:first arg-pos must refuse")
         (catch clojure.lang.ExceptionInfo e
           (is (= :bad-args (:type (ex-data e))) "typed, so a remote caller gets a 400")
           (is (= pet (:arg-pos (ex-data e))) "and told what arrived in the slot")))))

(tu/deftest-kb a-genlarg-typed-slot-audits-the-subtype-arm
  ;; the derived contract has two arms: (arg p 2 t) asks membership, (genlArg p 2 t)
  ;; asks subtypehood — the same split the assert-time checker runs.  A filler that is
  ;; itself the constraint type passes reflexively (no genl self-edge is stored).
  ;; Forced to the constraint-only reading: on the default (entailing) reading the
  ;; `genlArg`-declared slot mints its filler's `genl thing` edge, so `lone_individual`
  ;; would gain a visible path and M3 would not violate.  The audit's open-world excuse
  ;; is the constraint-only behavior this asserts.
  (tu/without-entailing
   (tu/with-terms [governs meta_kind kind_a lone_individual]
     (v/assert kb (list 'binary_predicate governs) 'CxUniverse)
     (v/assert kb (list 'unary_predicate meta_kind) 'CxUniverse)
     (v/assert kb (list 'unary_predicate kind_a) 'CxUniverse)
     (v/assert kb (list 'genlArg governs 2 'thing) 'CxUniverse)
     (v/assert kb (list 'predAllSpecified governs meta_kind) 'CxUniverse)
     (tu/with-terms [M1 M2 M3]
       (v/assert kb (list meta_kind M1) 'CxUniverse)
       (v/assert kb (list meta_kind M2) 'CxUniverse)
       (v/assert kb (list meta_kind M3) 'CxUniverse)
       (v/assert kb (list 'genl kind_a 'thing) 'CxUniverse)
       (v/assert kb (list governs M1 kind_a) 'CxUniverse)      ; a kind under thing — passes
       (v/assert kb (list governs M2 'thing) 'CxUniverse)      ; the type itself
       (v/assert kb (list governs M3 lone_individual) 'CxUniverse) ; no genl path to thing
       (let [vs (:violations (predall/specified-violations kb governs meta_kind 'CxUniverse))]
         (is (not (contains? vs M1)) "a filler with a genl path to the constraint type passes")
         (is (v/ask? kb '(genl thing thing) 'CxUniverse)
             "the genl closure ask answers is reflexive — the pass below is its, not a floor's")
         (is (not (contains? vs M2)) "so the constraint type itself passes")
         (is (contains? vs M3) "a filler with no visible path into the hierarchy violates"))))))

(tu/deftest-kb multiple-slot-constraints-compose-conjunctively
  ;; two visible slot-2 constraints must BOTH be satisfied.  The division of labour the
  ;; comment in `satisfies-typing?` describes shows up concretely here: a filler with
  ;; visible evidence reaching the WRONG constraint is held inert at assert by the checker
  ;; (composition enforced at the entry point — there is no believed
  ;; passes-one-fails-the-other case), so what the audit's conjunction meets on stored
  ;; facts is the checker's open-world excuse: a filler with NO visible evidence stores
  ;; fine and violates both derived constraints, and one under both passes.
  ;; Forced to the constraint-only reading: on the default (entailing) reading each
  ;; `genlArg governs 2 …` mints the filler's type, so `mystery_kind` would no longer be
  ;; the evidence-free filler the audit's conjunction is meant to catch.
  (tu/without-entailing
   (tu/with-terms [governs meta_kind vehicle_kind insured_kind car_kind mystery_kind M1 M2]
     (v/assert kb (list 'binary_predicate governs) 'CxUniverse)
     (v/assert kb (list 'unary_predicate meta_kind) 'CxUniverse)
     (v/assert kb (list 'unary_predicate vehicle_kind) 'CxUniverse)
     (v/assert kb (list 'unary_predicate insured_kind) 'CxUniverse)
     (v/assert kb (list 'genl vehicle_kind 'thing) 'CxUniverse)
     (v/assert kb (list 'genl insured_kind 'thing) 'CxUniverse)
     (v/assert kb (list 'genlArg governs 2 vehicle_kind) 'CxUniverse)
     (v/assert kb (list 'genlArg governs 2 insured_kind) 'CxUniverse)
     (v/assert kb (list 'predAllSpecified governs meta_kind) 'CxUniverse)
     (v/assert kb (list meta_kind M1) 'CxUniverse)
     (v/assert kb (list meta_kind M2) 'CxUniverse)
     (v/assert kb (list 'genl car_kind vehicle_kind) 'CxUniverse)
     (v/assert kb (list 'genl car_kind insured_kind) 'CxUniverse)  ; under both
     (v/assert kb (list governs M1 car_kind) 'CxUniverse)
     (v/assert kb (list governs M2 mystery_kind) 'CxUniverse)      ; no visible evidence
     ;; the partially-conforming case is held inert, which is itself asserted:
     (tu/with-terms [boat_kind M3]
       (v/assert kb (list meta_kind M3) 'CxUniverse)
       (v/assert kb (list 'genl boat_kind vehicle_kind) 'CxUniverse)
       (v/assert kb (list 'disjoint boat_kind insured_kind) 'CxUniverse)
       (is (= :arg-genl (:type (tu/write-conviction kb (list governs M3 boat_kind) 'CxUniverse)))
           "held by the genlArg conviction specifically, not incidentally"))
     (let [vs (:violations (predall/specified-violations kb governs meta_kind 'CxUniverse))]
       (is (not (contains? vs M1)) "car_kind satisfies both subtype constraints")
       (is (contains? vs M2)
           "an evidence-free filler the checker excused fails the audit's conjunction")))))

(tu/deftest-kb argn-bridges-project-arg-in-both-directions
  ;; all six bridge rules, a 3-position x 2-direction matrix: either spelling concludes
  ;; the other, for each projected position — which is what lets a positional constraint
  ;; stand in a binary declaration's subject position, and what a copy/paste slip in any
  ;; one rule's position number would break.
  (tu/with-terms [rel3 kind_a kind_b kind_c kind_d kind_e kind_f]
    (doseq [k [kind_a kind_b kind_c kind_d kind_e kind_f]]
      (v/assert kb (list 'unary_predicate k) 'CxUniverse))
    (v/assert kb (list 'ternary_predicate rel3) 'CxUniverse)
    (doseq [[binary-f n fwd-type bwd-type]
            [['arg1 1 kind_a kind_b]
             ['arg2 2 kind_c kind_d]
             ['arg3 3 kind_e kind_f]]]
      (v/assert kb (list binary-f rel3 fwd-type) 'CxUniverse)
      (is (v/ask? kb (list 'arg rel3 n fwd-type) 'CxUniverse)
          (str binary-f " concludes the ternary spelling at position " n))
      (v/assert kb (list 'arg rel3 n bwd-type) 'CxUniverse)
      (is (v/ask? kb (list binary-f rel3 bwd-type) 'CxUniverse)
          (str "and the ternary spelling at position " n " concludes " binary-f)))))

(defn- contract-derivations
  "How many times one `specified-violations` call over `instances` members of the audited
  collection reaches for the constraining predicates — the walk `slot-typings` derives the
  filler contract from.  Counted rather than timed: the derivation is hoisted out of the
  per-instance loop, so moving it back in changes the *constant* and leaves the growth
  shape linear either way, which is the one thing a `lein perf` ratio cannot see."
  [instances]
  (let [kb   (tu/isolated-fresh)
        n    (atom 0)
        orig res/constraining-predicates]
    (tu/with-terms [keepP dog_k person_k]
      (v/assert kb (list 'binary_predicate keepP) 'CxUniverse)
      (v/assert kb (list 'unary_predicate dog_k) 'CxUniverse)
      (v/assert kb (list 'unary_predicate person_k) 'CxUniverse)
      (v/assert kb (list 'arg keepP 1 person_k) 'CxUniverse)
      (doseq [i (range instances)]
        (v/assert kb (list dog_k (symbol (str "cd_d" i))) 'CxUniverse))
      (with-redefs [res/constraining-predicates
                    (fn [& args] (swap! n inc) (apply orig args))]
        (predall/specified-violations kb keepP dog_k 'CxUniverse :first))
      @n)))

(tu/deftest-kb the-slot-contract-is-derived-once-per-audit-not-once-per-instance
  ;; `specified-violations` derives the filler contract once and passes it into the
  ;; per-instance loop, so an audit costs the derivation plus one read per member rather
  ;; than the product of the two.  Nothing about the ANSWER changes if the derivation
  ;; moves back inside the loop — the same violations come out — and the growth stays
  ;; linear in the members either way, so neither the suite nor a perf ratio would see
  ;; it.  The count is the instrument that does: one reach per declaration functor the
  ;; chokepoint reads (`res/arg-constraints`, seven), whatever the collection's size.
  (let [small (contract-derivations 10)
        large (contract-derivations 200)]
    (is (= 7 small) "one reach per constraining declaration functor, and no more")
    (is (= small large)
        (str "20x the audited members derives the contract the same number of times — "
             small " against " large))))

(tu/deftest-kb a-late-argn-declaration-reaches-facts-stored-before-it
  ;; arg1/arg2/arg3 carry `:reach` in the declaration, and `the-declaration-names-the-
  ;; terms-that-reach` holds the `:reach` facet to that — so the behaviour the facet claims
  ;; is tested here rather than left to the facet's own comment. The projection has no
  ;; reach mechanism of its own: the bridge rule's `arg` conclusion is what
  ;; `special/entail-existing` reads, so the reach arrives at one remove and has to be
  ;; measured through the twin. The reach runs only when `*assertive-arg-types?*` is true,
  ;; as `arg`'s own does.
  (binding [argument/*assertive-arg-types?* true]
    (tu/with-terms [relA kindA subjA objA relB kindB subjB objB]
      (doseq [[label rel kind subj obj decl]
              [["the projection" relA kindA subjA objA (fn [r k] (list 'arg1 r k))]
               ["the ternary"    relB kindB subjB objB (fn [r k] (list 'arg r 1 k))]]]
        (v/assert kb (list 'binary_predicate rel) 'CxUniverse)
        (v/assert kb (list 'genl kind 'thing) 'CxUniverse) ; placed, as entail-existing needs
        (v/assert kb (list rel subj obj) 'CxUniverse)      ; the FACT arrives first
        (is (not (v/ask? kb (list kind subj) 'CxUniverse))
            (str label ": nothing types the subject before the declaration"))
        (v/assert kb (decl rel kind) 'CxUniverse)          ; the declaration arrives LAST
        (is (v/ask? kb (list kind subj) 'CxUniverse)
            (str label " reaches back over the fact stored before it, and mints the"
                 " membership entail-existing draws"))))))

(tu/deftest-kb retracting-either-argn-spelling-collapses-the-pair
  ;; The cycle the six bridge rules form is the one arity and the predicate-type
  ;; memberships form, and it has to collapse the same way: two rules deriving each
  ;; other leave each spelling justified by the other, so a retraction the JTMS read as
  ;; circular support would strand both believed with the asserted one gone.  Run in
  ;; both directions, the rule carrying the cycle differing by which was asserted, and
  ;; over freshly minted terms so no shipped declaration answers beside the probe's.
  (tu/with-terms [relA kindA relB kindB]
    (doseq [[label rel kind decl-fn other-fn]
            [["the projection" relA kindA
              (fn [r k] (list 'arg1 r k)) (fn [r k] (list 'arg r 1 k))]
             ["the ternary"    relB kindB
              (fn [r k] (list 'arg r 1 k)) (fn [r k] (list 'arg1 r k))]]]
      (let [decl (decl-fn rel kind) other (other-fn rel kind)]
        (v/assert kb (list 'binary_predicate rel) 'CxUniverse)
        (v/assert kb (list 'unary_predicate kind) 'CxUniverse)
        (v/assert kb decl 'CxUniverse)
        (is (and (v/ask? kb decl 'CxUniverse) (v/ask? kb other 'CxUniverse))
            (str label " asserted: both spellings are believed"))
        (v/retract! kb (v/handle-of kb decl 'CxUniverse))
        (is (not (v/ask? kb decl 'CxUniverse))
            (str label " retracted: the asserted spelling goes"))
        (is (not (v/ask? kb other 'CxUniverse))
            (str label " retracted: and the derived twin goes with it, the cycle"
                 " grounding neither"))))))

(tu/deftest-kb a-legacy-ternary-declaration-surfaces-from-the-sweep
  ;; the bulk import path builds records without the assert-time checks, so a
  ;; pre-migration dump's ternary declarations can load intact — modeled here by
  ;; asserting into a coreless KB.  The functor's binary shape holds each one inert,
  ;; so no ask answers it; the sweep reads the stored tuples and names each one,
  ;; beside whatever live results the same sweep carries.
  (let [kb (tu/isolated-fresh)]   ; isolated space — tu/fresh would clear the shared fixture KB
    (tu/with-terms [hasPet person pet likes food]
      (let [h (v/assert kb (list 'predAllSpecified hasPet person pet) 'CxUniverse)]
        (is (= :inert (:reason (v/why-not kb (list 'predAllSpecified hasPet person pet) 'CxUniverse))))
        (is (false? (v/in? kb h))))
      (v/assert kb (list 'predAllSpecified likes food) 'CxUniverse)
      (let [report (predall/all-specified-violations kb 'CxUniverse)]
        (is (= {:status :gap :gap :legacy-ternary-declaration
                :pred hasPet :sentence (list 'predAllSpecified hasPet person pet)}
               (get report ['predAllSpecified hasPet person pet]))
            "the stale sentex is named under its whole tuple, never silently unswept")
        (is (= {:status :gap :gap :missing-slot-typing :pred likes :position 2}
               (get report ['predAllSpecified likes food]))
            "and the same sweep carries the other gap kind beside it")))))

(tu/deftest-kb a-legacy-gap-does-not-displace-the-declaration-it-shares-a-prefix-with
  ;; an unmigrated KB carries both spellings at once, which is the whole period the
  ;; legacy gap serves.  A key off the functor and the first two arguments alone is
  ;; the same key the migrated binary declaration takes, so the stale sentex replaced
  ;; a real violation set; and two stale sentexes over one predicate and one
  ;; collection took each other's.  The key is the whole stale tuple for that reason.
  (let [kb (tu/isolated-fresh)]   ; isolated space — tu/fresh would clear the shared fixture KB
    (tu/with-terms [keeperOf person dog cat Rex]
      (v/assert kb (list 'arg keeperOf 1 person) 'CxUniverse)
      (v/assert kb (list dog Rex) 'CxUniverse)
      (v/assert kb (list 'predSpecifiedAll keeperOf dog) 'CxUniverse)
      (v/assert kb (list 'predSpecifiedAll keeperOf dog person) 'CxUniverse)
      (v/assert kb (list 'predSpecifiedAll keeperOf dog cat) 'CxUniverse)
      (let [report (predall/all-specified-violations kb 'CxUniverse)]
        (is (= {:status :audited :violations #{Rex}}
               (get report ['predSpecifiedAll keeperOf dog]))
            "the migrated declaration keeps its own violation set")
        (is (= {:status :gap :gap :legacy-ternary-declaration
                :pred keeperOf :sentence (list 'predSpecifiedAll keeperOf dog person)}
               (get report ['predSpecifiedAll keeperOf dog person]))
            "the stale sentex sits beside it under its own tuple")
        (is (= {:status :gap :gap :legacy-ternary-declaration
                :pred keeperOf :sentence (list 'predSpecifiedAll keeperOf dog cat)}
               (get report ['predSpecifiedAll keeperOf dog cat]))
            "and a second stale sentex over the same predicate and collection is a third key")
        (is (= 3 (count report))
            "three declarations, three entries — none swallowed by another")))))

(tu/deftest-kb pred-all-specified-treats-a-skolem-filler-as-indeterminate
  ;; the crux: a filler minted by head-existential skolemization is INDETERMINATE, so the
  ;; instance it fills still violates the requirement — Specified is the antagonist of the
  ;; existential
  (tu/with-terms [hasPet person pet Alice]
    (v/assert kb (list 'binary_predicate hasPet) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'unary_predicate pet) 'CxUniverse)
    ;; skolemize a pet witness for every person, so Alice HAS a filler — an indeterminate
    ;; one
    (v/assert kb (list 'implies (list person '?x)
                       (list 'exists '?y (list 'and (list hasPet '?x '?y) (list pet '?y))))
              'CxUniverse {:direction :forward})
    (v/assert kb (list 'arg hasPet 2 pet) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified hasPet person) 'CxUniverse)
    (v/assert kb (list person Alice) 'CxUniverse)
    (let [filler (get (first (v/ask kb (list hasPet Alice '?y) 'CxUniverse)) '?y)]
      (is (some? filler) "Alice does have a skolem filler")
      (is (predall/indeterminate-term? kb filler 'CxUniverse)
          "which is an indeterminate (skolem) term"))
    (is (contains? (:violations (predall/specified-violations kb hasPet person 'CxUniverse))
                   Alice)
        "so Alice still violates predAllSpecified — a skolem filler is not determinate")))

(tu/deftest-kb pred-all-specified-honours-an-extensible-indeterminate-kind
  ;; the category is extensible, not hard-wired to skolems: a filler that is a member of a
  ;; NEW kind declared (genl NewKind indeterminate_term) is indeterminate too, so it does
  ;; not satisfy the requirement — the audit reads the category, not the SkolemFn shape.
  (tu/with-terms [hasPet person pet Alice Fuzzy vague_kind]
    (v/assert kb (list 'binary_predicate hasPet) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'unary_predicate pet) 'CxUniverse)
    (v/assert kb (list 'genl vague_kind 'indeterminate_term) 'CxUniverse)  ; a future indeterminate kind
    (v/assert kb (list 'arg hasPet 2 pet) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified hasPet person) 'CxUniverse)
    (v/assert kb (list person Alice) 'CxUniverse)
    (v/assert kb (list hasPet Alice Fuzzy) 'CxUniverse)
    (v/assert kb (list pet Fuzzy) 'CxUniverse)     ; Fuzzy satisfies the derived slot type
    (v/assert kb (list vague_kind Fuzzy) 'CxUniverse)   ; but it is an indeterminate_term member
    (is (predall/indeterminate-term? kb Fuzzy 'CxUniverse)
        "a member of a (genl _ indeterminate_term) kind is indeterminate")
    (is (contains? (:violations (predall/specified-violations kb hasPet person 'CxUniverse))
                   Alice)
        "so Alice's only filler is indeterminate and she violates the requirement")))

(tu/deftest-kb an-exists-placeholder-satisfies-the-specified-requirement
  ;; the antagonism from the other side: the *Exists* placeholder is DETERMINATE — an
  ;; author who asserts it as a filler passes the predAllSpecified audit, where a skolem
  ;; witness (an indeterminate_term) would not.  Under pure-record semantics the
  ;; assertion is the author's, so the test makes it by hand.
  (tu/with-terms [owns person dog Alice]
    (v/assert kb (list 'binary_predicate owns) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'unary_predicate dog) 'CxUniverse)
    (v/assert kb (list 'predAllExists owns person dog) 'CxUniverse)
    (v/assert kb (list 'arg owns 2 dog) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified owns person) 'CxUniverse)
    (v/assert kb (list person Alice) 'CxUniverse)
    (let [p (list 'PredAllExistsFn owns person dog Alice)]
      (v/assert kb (list dog p) 'CxUniverse)
      (v/assert kb (list owns Alice p) 'CxUniverse))
    (is (= {:status :audited :violations #{}}
           (predall/specified-violations kb owns person 'CxUniverse))
        "the author-asserted placeholder is a determinate filler, so nothing violates")))

(tu/deftest-kb pred-specified-all-audits-the-first-position
  ;; the argument-swapped twin: the filler sits at ?pred's first position
  (tu/with-terms [managedBy report manager Carol Dan Boss]
    (v/assert kb (list 'binary_predicate managedBy) 'CxUniverse)
    (v/assert kb (list 'unary_predicate report) 'CxUniverse)
    (v/assert kb (list 'unary_predicate manager) 'CxUniverse)
    ;; binary twin: (predSpecifiedAll ?pred ?indep) — quantified over ?indep at ?pred's
    ;; second position, filler audited at position 1 under the slot-1 derived contract
    (v/assert kb (list 'arg managedBy 1 manager) 'CxUniverse)
    (v/assert kb (list 'predSpecifiedAll managedBy report) 'CxUniverse)
    (v/assert kb (list report Carol) 'CxUniverse)
    (v/assert kb (list report Dan) 'CxUniverse)
    (v/assert kb (list managedBy Boss Carol) 'CxUniverse)  ; Boss manages Carol
    (v/assert kb (list manager Boss) 'CxUniverse)
    (let [vs (:violations
              (predall/specified-violations kb managedBy report 'CxUniverse :first))]
      (is (not (contains? vs Carol)) "Carol has a determinate manager")
      (is (contains? vs Dan) "Dan has none"))))

(tu/deftest-kb all-specified-violations-sweeps-every-declaration
  (tu/with-terms [hasPet person pet Bob]
    (v/assert kb (list 'binary_predicate hasPet) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'unary_predicate pet) 'CxUniverse)
    (v/assert kb (list 'arg hasPet 2 pet) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified hasPet person) 'CxUniverse)
    (v/assert kb (list person Bob) 'CxUniverse)
    (let [report (predall/all-specified-violations kb 'CxUniverse)]
      (is (contains? report ['predAllSpecified hasPet person])
          "the sweep names the violated declaration")
      (is (contains? (:violations (get report ['predAllSpecified hasPet person])) Bob)
          "and carries its violating instances"))))

;; ==== the acceptance fixture: Pace's KE packet, normalized ================
;; The declarations from the 2026-09-04 predAllSpecified KE packet that survived the
;; thread's rulings, normalized to the binary (pred, collection) form.  Parked lines are
;; deliberately absent: the at_least_* collections (await the arity vocabulary lane), the
;; all-functions fcp audit (known unreifiable noise), and the arityMin family (its own
;; vocabulary-only PR).  This section asserts that each surviving declaration is
;; assertable against the shipped core vocabulary and audits — deriving a real slot
;; contract, not a gap.

(tu/deftest-kb the-ke-packet-declarations-assert-and-audit-over-core
  (doseq [[pred indep] [['arg1    'predicate]        ; every relation types argument 1
                        ['result  'function]         ; every function types its result
                        ['comment 'thing]            ; everything is documented
                        ['genl    'unary_predicate]]] ; every type has a place in the hierarchy
    (v/assert kb (list 'predAllSpecified pred indep) 'CxUniverse)
    (let [r (predall/specified-violations kb pred indep 'CxUniverse)]
      (is (= :audited (:status r))
          (str "(predAllSpecified " pred " " indep ") derives a slot contract — "
               pred "'s filler typing is visible to the audit"))))
  ;; genl's slot 2 carries no arg/genlArg declaration on purpose (the root would fail
  ;; it); its contract arrives through the type_relation_predicate arm, and the audit
  ;; that rides it has CONTENT — a fresh type with no genl parent violates the genl
  ;; declaration, and giving it one clears it, which no gap-suppression stub could fake.
  (is (v/ask? kb '(type_relation_predicate genl) 'CxUniverse)
      "the arm the genl declaration audits through is a believed membership")
  ;; content of the type_relation_predicate arm is asserted in isolation by
  ;; a-type-relation-slot-audits-the-type-position-arm; here the packet declaration
  ;; only has to assert and audit rather than gap.
  (is (= :audited (:status (predall/specified-violations kb 'genl 'unary_predicate
                                                         'CxUniverse)))
      "the genl declaration audits through the trp arm, not a gap"))

;; ==== the IndeterminateTerm identity exemption + the UNA matrix ============
;; The unique-name assumption applies to DETERMINATE terms (distinct names are provably
;; different, a term is never different from itself) but is SUSPENDED for an unmerged
;; indeterminate_term: neither equals nor different is provable of it against a determinate
;; term until a merge identifies it.  Built data-driven over the grid rather than N hand-written
;; cases (Pace, "DRY it").
;;
;; FLAGGED for a future ruling: (1) the design notes also want a non-evaluatable
;; *unreifiable* NAT (MotherFn JFK) treated as indeterminate; that rests on the
;; NAT-determinacy question explicitly PUNTED ("for now only skolem is a
;; member; flag the NAT call"), so the category here is skolem + whatever is declared
;; (genl _ indeterminate_term), and the generic-NAT cell is left to that ruling.  (2)
;; a rewriteOf merge restores UNA for a skolem (below), but for an explicitly-declared
;; indeterminate kind the equality merge MIGRATES the kind membership onto the winner, so
;; the winner inherits the indeterminacy — restoring UNA for that row needs a signal that
;; survives the merge (a Pace design call).

(defn- a-skolem
  "Skolemize a witness through a head-existential rule and return the minted skolem
  constant — the built-in first member of indeterminate_term."
  [kb]
  (tu/with-terms [wk pk hasP T1]
    (v/assert kb (list 'binary_predicate hasP) 'CxUniverse)
    (v/assert kb (list 'unary_predicate wk) 'CxUniverse)
    (v/assert kb (list 'unary_predicate pk) 'CxUniverse)
    (v/assert kb (list 'implies (list wk '?x)
                       (list 'exists '?y (list 'and (list hasP '?x '?y) (list pk '?y))))
              'CxUniverse {:direction :forward})
    (v/assert kb (list wk T1) 'CxUniverse)
    (get (first (v/ask kb (list hasP T1 '?y) 'CxUniverse)) '?y)))

(tu/deftest-kb una-applies-to-distinct-determinate-terms
  ;; every atomic determinate term-type pair is provably different; none is different from
  ;; itself — the UNA baseline the exemption is carved out of.
  (tu/with-terms [Alice Bob]
    (doseq [[a b] [[Alice Bob]     ; symbol × symbol (individuals)
                   [1 2]           ; number × number
                   ["x" "y"]       ; string × string
                   [1 "x"]         ; number × string (cross-kind)
                   [Alice 1]]]     ; symbol × number
      (is (v/ask? kb (list 'different a b) 'CxUniverse)
          (str "UNA: " (pr-str a) " and " (pr-str b) " are provably different"))
      (is (not (v/ask? kb (list 'different a a) 'CxUniverse))
          (str "reflexive: " (pr-str a) " is not different from itself")))))

(tu/deftest-kb una-is-suspended-for-unmerged-indeterminate-terms
  ;; all three ways into the category — the built-in skolem, a declared kind, and a
  ;; DIRECT membership — are exempt.  The direct case is the regression test: the prover's
  ;; presence check once required a declared subkind to exist before it would look, so a
  ;; direct member's exemption appeared and disappeared with an unrelated (genl _
  ;; indeterminate_term) declaration, and the audit and the prover disagreed about the
  ;; same term.  Tested in ITS OWN kb-shape (no subkind declared) below.
  (tu/with-terms [Other Foggy vague_kind]
    (v/assert kb (list 'genl vague_kind 'indeterminate_term) 'CxUniverse)
    (v/assert kb (list vague_kind Foggy) 'CxUniverse)
    (doseq [[label t] [["skolem (built-in member)" (a-skolem kb)]
                       ["declared (genl _ indeterminate_term) kind" Foggy]]]
      (is (predall/indeterminate-term? kb t 'CxUniverse)
          (str label " is an indeterminate term"))
      (is (not (v/ask? kb (list 'different t Other) 'CxUniverse))
          (str label ": UNA suspended — not provably different from a determinate term")))))

(tu/deftest-kb a-direct-indeterminate-member-is-exempt-with-no-subkind-declared
  ;; the regression shape: NO (genl _ indeterminate_term) declaration anywhere, only a
  ;; direct membership.  The audit and the prover must agree.
  (tu/with-terms [Other Hazy]
    (v/assert kb (list 'indeterminate_term Hazy) 'CxUniverse)
    (is (predall/indeterminate-term? kb Hazy 'CxUniverse)
        "the audit sees the direct membership")
    (is (not (v/ask? kb (list 'different Hazy Other) 'CxUniverse))
        "and so does the different prover — no subkind declaration required")))

(tu/deftest-kb a-rewriteOf-identifies-a-skolem-and-restores-una
  ;; a merge that gives the skolem a determinate identity lifts the exemption for it.
  (tu/with-terms [Real Other]
    (let [sk (a-skolem kb)]
      (is (not (v/ask? kb (list 'different sk Other) 'CxUniverse)) "unmerged: exempt")
      (v/assert kb (list 'rewriteOf Real sk) 'CxUniverse)          ; identify sk with Real
      (is (v/ask? kb (list 'different sk Other) 'CxUniverse)
          (str "once identified by rewriteOf, the SKOLEM itself obeys the UNA — its"
               " representative has moved off it, which is the exemption's lifting"
               " condition"))
      (is (v/ask? kb (list 'different Real Other) 'CxUniverse)
          "control: the determinate rewrite target was never exempt"))))

(tu/deftest-kb negative-zero-permutations-are-canonicalized
  ;; Pace's Cyc-canonicalizer check: -0.0 must not be a distinct term from 0.0 (the
  ;; Allegro bug).  Scope note: (= 0.0 -0.0) is true in Clojure, so the -0.0 rows
  ;; are settled by =-level canonicalization before the equality closure is ever
  ;; consulted — this asserts the reader-and-equality layer, not a closure read.  (An
  ;; integer -0 literal reads as 0 and is pure reflexivity, so it is not a row.)
  (doseq [[a b una?] [[0.0 -0.0 false]   ; same magnitude+kind: NOT different (no -0.0 bug)
                      [0   0.0  true]    ; integer 0 vs float 0.0: distinct EDN kinds
                      [0.0  1.0 true]]]  ; ordinary distinct floats
    (is (= una? (v/ask? kb (list 'different a b) 'CxUniverse))
        (str "(different " (pr-str a) " " (pr-str b) ") is " una?)))
  (is (v/ask? kb '(different 0.0 1.0 2.0) 'CxUniverse)
      "variable-arity control: three genuinely distinct floats are pairwise different")
  (is (not (v/ask? kb '(different 0.0 -0.0 1.0) 'CxUniverse))
      (str "-0.0 collapses onto 0.0, so this tuple carries a repeat and is NOT pairwise"
           " different — the canonicalization visible through the variable-arity read")))

(tu/deftest-kb a-rule-concluding-indeterminacy-from-a-different-antecedent-is-refused
  ;; `different` is negation as failure over TWO things now: the equality closure, and the
  ;; `indeterminate_term` category the exemption reads.  A rule that concludes the second
  ;; from a `different` antecedent is a cycle through negation — it withdraws the
  ;; antecedent that derived it — so the stratification check refuses it, exactly as it
  ;; already refuses one concluding an equality.  Stored, the pair settles to a belief that
  ;; contradicts its own support: `(indeterminate_term Aa)` believed off a `(different Aa
  ;; Bb)` that the belief then makes false.
  (tu/with-terms [pRel]
    (v/assert kb (list 'binary_predicate pRel) 'CxUniverse)
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list 'implies (list 'and (list pRel '?x '?y)
                                                   (list 'different '?x '?y))
                                    (list 'indeterminate_term '?x))
                           'CxUniverse {:direction :forward}))
        "concluding indeterminacy from a difference is not stratified")
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list 'implies (list 'and (list pRel '?x '?y)
                                                   (list 'different '?x '?y))
                                    (list 'genl '?x 'indeterminate_term))
                           'CxUniverse {:direction :forward}))
        "and neither is minting a subkind of it — the genl edge withdraws the same way")))

(tu/deftest-kb the-audit-and-the-prover-cannot-disagree-about-a-term
  ;; ONE implementation, called from both sides.  Two copies split on a membership no fact
  ;; states: `(arg pointsAt 2 vague_kind)` makes `(vague_kind Hazy)`
  ;; answerable by argument-type inference, which `ask` runs and a stored-sentex read does
  ;; not.  Either answer is defensible; disagreeing is not, because the audit would call a
  ;; filler indeterminate while `different` treated it as a determinate name.
  ;; Forced to the constraint-only reading: on the default (entailing) reading
  ;; `(arg pointsAt 2 vague_kind)` mints `(vague_kind Hazy)`, so the category becomes one
  ;; the KB HOLDS and the audit flips — which is the very split this test asserts cannot
  ;; happen when the membership is only prover-inferable.
  (tu/without-entailing
   (tu/with-terms [pointsAt Src Hazy Other vague_kind]
     (v/assert kb (list 'genl vague_kind 'indeterminate_term) 'CxUniverse)
     (v/assert kb (list 'binary_predicate pointsAt) 'CxUniverse)
     (v/assert kb (list 'arg pointsAt 2 vague_kind) 'CxUniverse)
     (v/assert kb (list pointsAt Src Hazy) 'CxUniverse)
     (is (v/ask? kb (list vague_kind Hazy) 'CxUniverse)
         "the membership is answerable by argument-type inference")
     (let [audit-says     (predall/indeterminate-term? kb Hazy 'CxUniverse)
           una-suspended? (not (v/ask? kb (list 'different Hazy Other) 'CxUniverse))]
       (is (= audit-says una-suspended?)
           "the audit and the different prover give one answer, whichever it is")
       (is (false? audit-says)
           (str "and the answer is that the category is what the KB HOLDS — a stored"
                " membership or a genl edge into it — not what a prover can infer"
                " on demand at query time"))))))

(tu/deftest-kb the-audit-runs-through-the-public-api
  ;; the declarations in CxUniverse send an author to `vaelii.core`, so the audit answers there
  ;; without a caller requiring anything under `vaelii.impl`.  `predall` sits ABOVE core and
  ;; the delegation runs back down through `wiring`, which is the arrangement under test:
  ;; a broken resolve there fails at call time rather than at load.
  (tu/with-terms [hasPet person pet Alice Bob Rex]
    (v/assert kb (list 'binary_predicate hasPet) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'unary_predicate pet) 'CxUniverse)
    (v/assert kb (list 'arg hasPet 2 pet) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified hasPet person) 'CxUniverse)
    (v/assert kb (list person Alice) 'CxUniverse)
    (v/assert kb (list person Bob) 'CxUniverse)
    (v/assert kb (list pet Rex) 'CxUniverse)
    (v/assert kb (list hasPet Alice Rex) 'CxUniverse)
    (is (= {:status :audited :violations #{Bob}}
           (v/specified-violations kb hasPet person 'CxUniverse))
        "Alice has a determinate pet; Bob has no filler at all")
    (is (= {:status :audited :violations #{Bob}}
           (v/specified-violations kb hasPet person 'CxUniverse :second))
        "and :second is the default argument position, stated or not")
    (let [report (v/all-specified-violations kb 'CxUniverse)]
      (is (= {['predAllSpecified hasPet person] {:status :audited :violations #{Bob}}}
             report)
          "the sweep reports the one declaration that does not hold, keyed by it"))
    (v/assert kb (list hasPet Bob Rex) 'CxUniverse)
    (is (= {} (v/all-specified-violations kb 'CxUniverse))
        "and a requirement that holds is omitted, so a clean sweep is an empty map")))
