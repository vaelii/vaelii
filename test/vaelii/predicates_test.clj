;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.predicates-test
  "That `vaelii.impl.predicates` says what the engine already does.

  The declaration namespace began as a claim about twenty-odd lists it did not feed,
  and these tests were the only defensible proof its population was right before a single
  consumer moved.  Consumers have moved since — `taxonomy`'s three lists,
  `spec/::prop-kind`, `vocabulary/classification` and `settle`'s eight — so the tests come in
  **two kinds**, and which kind a list gets is decided by whether it has moved.  One
  still written by hand is **reconstructed** from the declaration and asserted equal to
  itself, which is what says a consumer switching over later cannot change behaviour.
  One that has moved states its **value** as a literal instead: reconstructing a derived
  var proves the wiring and nothing about what it holds.

  **Six facets are reconstructible and four are claims.**  `:cached`, `:derived`,
  `:migrates`, `:arbitrable`, `:reach` and `:query-only` each have a data structure in
  the tree stating them, and are asserted below against it.  `:answers`, `:retriggers`,
  `:convicts` and `:inert` have none — a prover's `applicable?` is per-prover code over
  goal shape, a re-check posting is a line inside an arm, and being read by nothing is
  the absence of code rather than any of it.  Those four are exactly the ones that go
  wrong quietly, which is why the facet validator exists; here they are checked only for
  being drawn from the closed vocabulary.

  No KB is involved, so no fixture is either."
  (:require [clojure.set :as set]
            [clojure.spec.alpha :as s]
            [clojure.test :refer [deftest is testing]]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.predicates :as pr]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.spec :as vspec]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.vocabulary :as vocab]))

(def ^:private table-functors (into #{} (map first) special/entries))

(defn- live
  "The functors `special/entries` gives arm `k`, as a set."
  [k]
  (into #{} (comp (filter #(get (second %) k)) (map first)) special/entries))

;; ---- the table the whole design is modelled on ---------------------------

(deftest the-declaration-reconstructs-the-special-table
  ;; `special/entries` is a **join** now: the functor list, its order, each `:prop` kind
  ;; and each `:derived?` are read off the declaration, and `special/check-declarations`
  ;; refuses a `:cached` or `:checked` disagreement at namespace load.  So what this
  ;; deftest proves has changed from what the values *are* to that the join is wired to
  ;; them — the same thing `special-table-test/the-live-table-passes-its-own-check`
  ;; proves about `check-entries`, and it fails the same way, on a refactor that stops
  ;; routing the table through the declaration.
  ;;
  ;; What the values are is `special-table-test/frozen-table`, which is a literal
  ;; precisely because nothing here can state it any more.
  (testing "the same functors, and nothing else"
    (is (= table-functors pr/in-special-table)
        "a functor in one and not the other is a hole in the population"))
  (testing "in the same order — rebuild-taxonomy replays the table top to bottom and a
            rebuild arm may read what an earlier one wrote, so the order is content"
    (is (= (mapv first special/entries)
           (filterv table-functors (mapv first pr/entries)))))
  (testing ":cached is the integrate/disintegrate/rebuild triple"
    ;; one arm is enough to test for: `check-entries` refuses a partial triple at
    ;; namespace load, so having the add arm and having all three are the same fact
    (is (= (live :integrate) pr/cached))
    (is (= (live :disintegrate) pr/cached))
    (is (= (live :rebuild) pr/cached)))
  (testing ":derived is the flag that also runs the arm on the derivation path"
    (is (= (live :derived?) pr/derived)))
  (testing ":checked is the structural well-formedness arm"
    (is (= (live :wff) pr/checked)))
  (testing "every :cached term names a storage kind, and no other term does"
    (is (= pr/cached
           (into #{} (comp (remove #(= [:none] (:storage (second %)))) (map first))
                 pr/entries)))))

;; ---- the taxonomy's three lists ------------------------------------------

(deftest the-declaration-reconstructs-the-taxonomy-lists
  (testing "the prop kinds a declaration maintains are the ones the table marks"
    (is (= (into {} (comp (filter #(:prop (second %)))
                          (map (fn [[f spec]] [f (:prop spec)])))
                 special/entries)
           (pr/by-storage :prop))))
  (testing "…and are exactly what ::prop-kind admits — the spec is this field read back,
            generated rather than written, so the two cannot say different things"
    (is (every? #(s/valid? ::vspec/prop-kind %) (pr/prop-kinds)))
    (is (not (s/valid? ::vspec/prop-kind :declares-max-cardinality))))
  ;; The three lists below are *read off* the declaration now, so a test that derives
  ;; them from it and compares proves the wiring and nothing about the values.  Each
  ;; therefore states its value as a literal first — small enough to write out, and the
  ;; only place left that says what it is — and asserts the derivation second, which is what
  ;; fails on a refactor that stops routing the var through `predicates`.
  (testing "the argument constraints' subject props"
    (is (= '{arg :declares-arg-isa, genlArg :declares-arg-genl,
             quotedArg :declares-quoted-arg, interArg :declares-inter-arg-isa,
             argArg :declares-arg-arg, interArgEqual :declares-inter-arg-equal,
             args :declares-args-isa, argsGenl :declares-args-genl,
             argAndRest :declares-arg-and-rest-isa,
             argAndRestGenl :declares-arg-and-rest-genl,
             quotedArgAndRest :declares-quoted-arg-and-rest,
             interArgs :declares-inter-args-isa,
             interArgAndRest :declares-inter-arg-and-rest-isa}
           tax/arg-declaration-props))
    (is (= tax/arg-declaration-props
           (select-keys (pr/by-storage :prop) (pr/family :argument-constraint)))))
  (testing "the functional family, spellings and written shapes both"
    (is (= '{functional :mark, functionalInArg :mark-in-arg} tax/functional-family-marks))
    (is (= tax/functional-family-marks (pr/by-family :functional))))
  (testing "the two cached closures are the only :edge storage"
    (is (= '#{genl genlCx} tax/closure-relations))
    (is (= tax/closure-relations (set (keys (pr/by-storage :edge)))))))

;; ---- the merge and arbitration lists -------------------------------------

(deftest the-declaration-reconstructs-the-belief-lists
  (testing ":migrates is the set of relations whose own assertion is a merge"
    (is (= kb/equality-predicates (pr/by-facet :migrates))))
  (testing ":arbitrable, read as the violation kind each names, is checks/arbitrable-kinds"
    ;; A `:pred-position` declaration is a *generalization* of a mark off its fixed slot,
    ;; so its breach carries the mark's kind rather than one of its own: a
    ;; `functionalInArg` violation is a `:functional` violation, arbitrated identically,
    ;; and holds no keyword of its own. Every other arbitrable term stores under the
    ;; keyword its violation is named by.
    (is (= checks/arbitrable-kinds
           (into #{} (comp (filter #(contains? (:facets (second %)) :arbitrable))
                           (remove #(= :pred-position (first (:storage (second %)))))
                           (map #(second (:storage (second %)))))
                 pr/entries)))
    (is (= '#{functionalInArg}
           (into #{} (comp (filter #(contains? (:facets (second %)) :arbitrable))
                           (filter #(= :pred-position (first (:storage (second %)))))
                           (map first))
                 pr/entries))
        "the one arbitrable spelling that takes its kind from the mark it generalizes")))

(deftest the-declaration-names-the-terms-that-reach
  ;; A term carrying `:reach` convicts or mints over content stored before it, each by
  ;; one of four mechanisms, and none of them a settle sweep.
  ;;
  ;; The separations, the covers and the `genl` and `genlCx` edges reach at the read: a
  ;; reader finds a membership nogood from the term the memberships name
  ;; (`membership/term-nogoods`), through the separations it reads.  `arity`, `arityMin` and
  ;; the exact-arity memberships reach at the read too: a reader decides a tuple whose
  ;; length a late binding breaks from the candidate index (`vaelii.impl.decide`).
  ;; `irreflexive`, `anti_symmetric` and the tuple marks reach at the read: a late mark
  ;; offers the stored tuples to the candidate index and a reader decides what it
  ;; convicts.
  ;;
  ;; The argument constraints reach through `special/entail-existing`, which *mints*
  ;; rather than convicting, being open-world, and runs only when
  ;; `argument/*assertive-arg-types?*` is true.  `arg1` / `arg2` / `arg3` reach through that same
  ;; mechanism at one remove, the bridge rule's `arg` conclusion being what
  ;; entail-existing reads: a late `(arg1 owns person)` mints `(person Ann)` over an
  ;; `(owns Ann Rex)` stored before it, exactly as the ternary spelling does.
  ;;
  ;; The commutativity marks reach through `integrate/commute-existing`: a declaration
  ;; that moves a *spelling* re-spells the records already stored, which neither convicts
  ;; nor mints.  `commutative` reaches at one remove the way `arg1` does, the CxUniverse
  ;; rule's `(commutativeInArgAndRest P 1)` conclusion being what the re-spelling fires on.
  (is (= (into '#{genl genlCx disjoint disjoint_metatype sibling_disjoint
                  covering separating partition
                  arity arityMin arg argArg genlArg interArg interArgEqual arg1 arg2 arg3 arg4 arg5
                  commutative commutativeInArgs commutativeInArgAndRest
                  irreflexive anti_symmetric functional functionalInArg asymmetric
                  anti_transitive negates}
               (keys tax/exact-arity-classes))
         (pr/by-facet :reach))))

(def ^:private live-inputs
  "What `settle`'s call site hands the validator — the cross-layer reads a bottom
  namespace cannot make for itself.

  Read off that call site rather than copied from it.  A copy is two spellings of one
  fact with nothing joining them, which is the defect this whole validator exists to
  refuse: every negative case below would go on passing against a map the engine had
  stopped handing it, and a list added to the live map would be one these tests never
  drive."
  settle/facet-check-inputs)

(deftest a-list-that-reads-a-family-enumerates-exactly-that-family
  ;; The rule with no `:stops-short` escape, and the one that would have refused
  ;; `quotedArg`.  Three lists read the argument constraints as a family — the
  ;; declarations here, the entry point's query table, the prover's shape table — and
  ;; `provers/meta-constraint-shape` held three of the four for as long as nothing
  ;; compared them.  The lane rule caught the missing `:answers` facet and offered a
  ;; record; a record is the wrong answer to two enumerations of one fact disagreeing,
  ;; which is why this one refuses outright.
  (let [refusal (fn [lists]
                  (try (pr/check-facets pr/entries (assoc live-inputs :family-lists lists))
                       nil
                       (catch clojure.lang.ExceptionInfo e (ex-data e))))]
    (is (= pr/entries (pr/check-facets pr/entries live-inputs))
        "the three lists agree today")
    (testing "the bug itself: the prover's table missing the family's fourth spelling"
      (let [data (refusal {:argument-constraint
                           {'provers/meta-constraint-functors
                            (disj provers/meta-constraint-functors 'quotedArg)}})]
        (is (= :bad-table-entry (:type data)))
        (is (= :family-list (:mismatch data)))
        (is (= 'provers/meta-constraint-functors (:list data)))
        (is (= '#{quotedArg arg argArg genlArg interArg interArgEqual args argsGenl argAndRest
                  argAndRestGenl quotedArgAndRest interArgs interArgAndRest}
               (:declared data))
            "and the throw names both sets, so the reader sees which half is missing")))
    (testing "and the other direction — a list naming a spelling nothing declares"
      (is (= :family-list
             (:mismatch (refusal {:argument-constraint
                                  {'checks/constraint-declaration-functors
                                   (conj checks/constraint-declaration-functors 'notAConstraint)}})))))
    (testing "a family no list is named for is not thereby unchecked — it is unread,
              which is a different thing, and the lane rule still holds its facets"
      (is (= pr/entries (pr/check-facets pr/entries (assoc live-inputs :family-lists {})))))))

(deftest the-facet-contract-is-checked-at-settles-load
  ;; Everything above drives the validator directly, which proves it *refuses* and
  ;; nothing about anything calling it.  The call is a layer up — two of its rules ask
  ;; whether an arm exists, which `predicates` cannot see — and a bare call there is a
  ;; line that could be deleted with every test here still green.  `settle/checked-
  ;; entries` is that call's value, so reading it is what goes red when the contract
  ;; stops being checked in the processes that load the engine.
  (is (= pr/entries settle/checked-entries)
      "settle's load runs the facet contract over the live declarations"))

(def ^:private family-list-exemptions
  "Vars that enumerate a mark family and are **not** on `settle/facet-check-inputs`'
  `:family-lists`, each with why the rule would say nothing about it.

  A recorded exception rather than a suppression, as `:stops-short` is: the test below
  refuses an entry that has stopped being true, so one cannot outlive its reason.  Every
  entry has the same reason: a list read off the declarations is the rule
  already satisfied, and comparing a derivation with what it derives from checks the
  `=` operator."
  '{argument/declaration-functors
    "derived: `(predicates/family :argument-constraint)`, the functors the argument family queues on"
    taxonomy/arg-declaration-props
    "derived: `(pr/family :argument-constraint)`, keyed to each spelling's own storage"
    taxonomy/functional-family-marks
    "derived: `(pr/by-family :functional)`, keyed to each spelling's written shape"})

(deftest a-list-that-enumerates-a-family-is-named-here
  ;; What `check-facets`' `:family-list` rule cannot see: its own reach.  The rule
  ;; compares the lists `settle/facet-check-inputs` names and is silent about one
  ;; nobody named — so the rule written because two enumerations of the argument
  ;; constraints disagreed covers exactly the enumerations somebody remembered to list.
  ;;
  ;; A family list is recognizable without being named: a var whose members are a
  ;; non-empty *subset* of a family's spellings is reading that family and nothing else.
  ;; Subset and not equality is the point — `meta-constraint-functors` held three of the
  ;; four, and an equality test would have called the bug not-a-family-list and passed.
  (require 'vaelii.core)                ; the whole engine, so the scan sees every ns
  (let [families  (into {} (map (juxt identity pr/family)) pr/mark-families)
        members   (fn [v] (cond (and (set? v) (every? symbol? v))              v
                                (and (map? v) (every? symbol? (keys v)))       (set (keys v))))
        short-name (fn [n sym]
                     (symbol (str (re-find #"[^.]+$" (str (ns-name n))) "/" sym)))
        flagged   (into (sorted-map)
                        (for [n     (all-ns)
                              :when (and (re-find #"^vaelii\." (str (ns-name n)))
                                         (not (re-find #"-test$" (str (ns-name n)))))
                              [sym v] (ns-publics n)
                              :let  [ms (members (try @v (catch Throwable _ nil)))]
                              :when (seq ms)
                              [fam spellings] families
                              :when (set/subset? ms (set spellings))]
                          [(short-name n sym) fam]))
        named     (into #{} (mapcat keys) (vals (:family-lists settle/facet-check-inputs)))
        exempt    (set (keys family-list-exemptions))]
    (doseq [[var-sym fam] flagged]
      (is (or (named var-sym) (exempt var-sym))
          (str var-sym " enumerates the " fam " family and is on neither"
               " `settle/facet-check-inputs` nor `family-list-exemptions` — so"
               " `check-facets` never compares it with the declarations, and a spelling"
               " it is missing means one thing to whichever lane reads it and another"
               " everywhere else.  Name it there, or record here why the comparison"
               " would say nothing.")))
    (doseq [var-sym (sort exempt)]
      (is (flagged var-sym)
          (str "`family-list-exemptions` names " var-sym ", which enumerates no mark"
               " family — the exemption has outlived what it excused.  Drop the entry.")))
    (doseq [var-sym (sort named)]
      (is (flagged var-sym)
          (str "`settle/facet-check-inputs` names " var-sym " as a family list and the"
               " scan does not see it: a var that has been made private, renamed, or has"
               " stopped enumerating a family is one the rule can no longer reach.")))))

(deftest a-facet-implication-nothing-answers-for-does-not-load
  ;; `the-terms-that-convict-with-no-retroactive-half-are-exactly-three` stood here and is
  ;; gone.  It asserted the set of terms that convict at the entry point and reach nothing behind
  ;; it, because the rule could not be stated while three terms broke it.  `check-facets`
  ;; states it: the three now record the exception in `:stops-short`, and the record is
  ;; held to being *exactly* what is owed, so a fourth term cannot appear and a recorded
  ;; one cannot go stale — which is strictly more than the set assertion said.
  (let [refusal (fn [entries]
                  (try (pr/check-facets entries {}) nil
                       (catch clojure.lang.ExceptionInfo e (ex-data e))))
        ok      (fn [spec] (merge {:shape {:args [:predicate]} :storage [:none]
                                   :checked false :facets #{} :family nil}
                                  spec))]
    (is (= pr/entries (pr/check-facets pr/entries live-inputs))
        "the real declarations pass and come back unchanged")

    (testing "#54's shape as an implication: convicting at the entry point and reaching nothing"
      (let [data (refusal [['brokenPred (ok {:facets #{:convicts}})]])]
        (is (= :bad-table-entry (:type data)))
        (is (= :implication (:mismatch data)))
        (is (= 'brokenPred (:functor data)))
        (is (= :reach (:facet data)))))

    (testing "and the exception is a record, not a suppression — it must name the facet
              that is actually owed, and carry a reason"
      (is (nil? (refusal [['brokenPred (ok {:facets #{:convicts}
                                            :stops-short {:reach "measured; the arrival orders agree"}})]]))
          "the owed facet recorded is what makes it load")
      (is (= :stops-short
             (:mismatch (refusal [['brokenPred (ok {:facets #{:convicts :reach}
                                                    :stops-short {:reach "stale"}})]])))
          "a record for a facet the term now carries has gone stale and says nothing")
      (is (= :stops-short
             (:mismatch (refusal [['brokenPred (ok {:facets #{:convicts}
                                                    :stops-short {:reach ""}})]])))
          "and an exception with no reason is a suppression"))

    (testing "a family joined to a lane in one spelling and not another"
      (let [data (refusal [['markOne (ok {:facets #{:convicts :reach} :family :functional})]
                           ['markTwo (ok {:facets #{} :family :functional})]])]
        (is (= :family-lane (:mismatch data)))
        (is (= 'markTwo (:functor data)))))

    (testing "a declaration answering goals about a predicate and posting no re-check"
      (let [entries [['tellsPred (ok {:facets #{:answers}})]]]
        (is (= :recheck (:mismatch (refusal entries)))
            "neither its own arms nor the shared path posts one")
        (is (= entries (pr/check-facets entries {:recheck-subjects '#{tellsPred}}))
            "and the shared path is the other route, not a second requirement")
        (is (nil? (refusal [['tellsPred (ok {:facets #{:answers :retriggers}})]]))
            "as its own arms are")))

    (testing "a facet outside the closed vocabulary, which is a hand-kept list again"
      (is (= :vocabulary (:mismatch (refusal [['brokenPred (ok {:facets #{:convicst}})]])))))

    (testing "the facet and the storage kind say the same thing and cannot disagree"
      (is (= :storage (:mismatch (refusal [['brokenPred (ok {:facets #{:cached}})]]))))
      (is (= :storage (:mismatch (refusal [['brokenPred (ok {:storage [:prop :nope]})]])))))

    (testing "and an arbitrable term must say what its conviction is read through —
              the one conjunct no data decides, so it is claimed on the entry"
      (is (= :arbitrable
             (:mismatch (refusal [['brokenPred (ok {:facets #{:arbitrable :convicts :reach}})]]))))
      (is (nil? (refusal [['brokenPred (ok {:facets #{:arbitrable :convicts :reach}
                                            :opposing-read "the mark is not a member of the nogood"})]]))))

    (testing "a clash check the layer above does not answer"
      (is (= :clash-check
             (:mismatch (refusal [['brokenPred (ok {:clash-checks {:fact :nope}})]]))))
      (is (= [['brokenPred (ok {:clash-checks {:fact :arity}})]]
             (pr/check-facets [['brokenPred (ok {:clash-checks {:fact :arity}})]]
                              {:clash-checks {:fact #{:arity}}}))))

    (testing "an inert term carrying a second opinion about itself"
      (is (= :inert (:mismatch (refusal [['brokenPred (ok {:facets #{:inert :answers}
                                                           :inert "nothing reads it"})]])))))))

(deftest the-four-arbitrable-marks-say-what-they-are-read-through
  ;; The claim `check-facets` requires, read as content rather than as presence: five
  ;; spellings arbitrate, and `arity` is decided at the reader instead.
  (doseq [t (pr/by-facet :arbitrable)]
    (is (string? (:opposing-read (pr/entry t))) (str t " must claim it")))
  (is (not (contains? (pr/by-facet :arbitrable) 'arity))))

;; ---- the query operators -------------------------------------------------

(deftest the-declaration-reconstructs-the-query-only-set
  (testing "the aggregates are query-only, all five, and take one shape"
    (is (set/subset? (set (keys sx/aggregate-functors)) pr/query-only))
    (is (= 1 (count (set (map pr/shape-of (keys sx/aggregate-functors)))))
        "one prover answers all five because they are one shape"))
  (testing "a query-only term is refused at the entry point and caches nothing"
    (doseq [t pr/query-only]
      (is (contains? pr/checked t) (str t " must carry the refusal arm"))
      (is (not (contains? pr/cached t)) (str t " must cache nothing"))
      (is (= [:none] (:storage (pr/entry t))) (str t " must name no storage")))))

;; ---- the population ------------------------------------------------------

(deftest the-population-is-the-grammar
  ;; The first of these is true by construction now — `vocabulary/classification` is the entries
  ;; carrying `:enforced` or `:inert` prose, so its keys cannot fail to be declared here.
  ;; It stays as the statement that the classification is still that read: a refactor putting the
  ;; prose back in a list of its own fails here rather than passing quietly.  What the
  ;; population actually rests on is `vocabulary_audit_test`, which asks CxUniverse.
  (testing "every term CxUniverse's classification answers for is declared here"
    (is (empty? (remove pr/table (keys vocab/classification)))))
  (testing "every functor the special table interprets is declared here"
    (is (empty? (remove pr/table table-functors))))
  (testing "and nothing else is — the population is the grammar, not the KB"
    (is (empty? (remove (into (set (keys vocab/classification)) table-functors)
                        (keys pr/table)))))
  (testing "no term is declared twice"
    (is (= (count pr/entries) (count pr/table)))))

;; ---- the vocabularies are closed -----------------------------------------

(deftest every-field-is-drawn-from-its-closed-vocabulary
  ;; `check-facets`' `:vocabulary` rule walks all five fields of every entry at `settle`'s
  ;; namespace load, and `facets` is `facet-contract`'s keys, so neither the field reads
  ;; nor the pairing between the two vocabularies is this test's to state.  What is left
  ;; is the contract's own rows: an `:implies` naming something that is not a facet asks
  ;; for a keyword no row governs, and a `:lane?` that is not a boolean is a family
  ;; question with no answer.
  (testing "every implication names a facet, so a row cannot ask for a keyword"
    (doseq [[f {:keys [implies lane?]}] pr/facet-contract]
      (is (set/subset? implies pr/facets) (str f "'s :implies must be facets"))
      (is (boolean? lane?) (str f " must decide whether a family agrees about it")))))

(deftest a-term-that-is-never-a-sentence-functor-has-no-shape
  (testing "a collection's membership shape is not per-term data, so it holds none"
    (doseq [[term spec] pr/entries :when (nil? (:shape spec))]
      (is (= [:none] (:storage spec)) (str term " caches nothing"))
      (is (not (contains? pr/checked term))
          (str term " has no sentence to check the structure of")))))

(deftest the-inert-terms-are-inert-in-every-lane
  ;; That an inert term carries that facet and no other, and names no storage, is
  ;; `check-facets`' `:inert` rule now.  What no validator inside `predicates` can see is
  ;; the *other* namespace's answer, which is what this is left saying.
  (doseq [t (pr/by-facet :inert)]
    (is (:inert (vocab/classification t))
        (str t " is called inert here and must be called inert there too"))))

(deftest the-vocabulary-answer-is-one-answer
  ;; `vocabulary/classification` reads the *class* off `:facets` and the prose off whichever key
  ;; it was written under, so the two must not be able to say different things.  The
  ;; `inert` constructor is what holds them together — it writes the facet with the prose
  ;; — and this is what fails if an entry is ever assembled without it.
  (doseq [[term spec] pr/entries]
    (testing (str term)
      (is (not (and (:enforced spec) (:inert spec)))
          "a term is enforced or inert, never both")
      (is (= (boolean (:inert spec)) (contains? (:facets spec) :inert))
          "the :inert prose and the :inert facet are one decision, not two")))
  (testing "and the classification is exactly the entries carrying prose — the wiring, since what
            the prose says is now only written here"
    (is (= (set (keys vocab/classification))
           (into #{} (comp (filter #(or (:enforced (second %)) (:inert (second %))))
                           (map first))
                 pr/entries)))))

;; ---- what the rest of the tree already knows ------------------------------

(deftest the-declaration-agrees-with-the-provers-and-inherit
  (testing "the closure relations answer their own transitivity"
    (is (= provers/transitive-predicates (set (keys (pr/by-storage :edge))))))
  (testing "the two preservation declarations are read back rather than cached"
    (doseq [t (keys inherit/declarations)]
      (is (= [:none] (:storage (pr/entry t))))
      (is (contains? (:facets (pr/entry t)) :answers))))
  (testing "the evaluable predicates answer and store nothing"
    (doseq [t provers/evaluable-predicates]
      (is (contains? (:facets (pr/entry t)) :answers))
      (is (= [:none] (:storage (pr/entry t)))))))

;; ---- the notes are findings ----------------------------------------------

(deftest a-note-names-a-lane-the-facet-vocabulary-does-not-reach
  ;; A note is the record of a term doing something no facet covers, so it is the
  ;; backlog the facet validator will work through — not prose to accumulate.  Asserting
  ;; the count keeps a note from being added silently as an alternative to a facet.
  (let [noted (into #{} (comp (filter #(:notes (second %))) (map first)) pr/entries)]
    (is (seq noted))
    (testing "every term the vocabulary calls inert carries one, since :inert is a
              decision and a decision has a reason"
      (is (set/subset? (pr/by-facet :inert) noted)))))

(deftest every-clash-check-is-named-by-a-grammar-entry
  ;; `check-facets` holds each entry's `:clash-checks` to a check `checks` answers; this
  ;; is the other direction, a check no grammar entry names
  (doseq [[dir checks] {:fact checks/fact-clash-checks :declaration checks/declaration-clash-checks}]
    (is (= (into #{} (map first) checks)
           (into #{} (keep dir) (vals (pr/clash-checks))))
        (name dir))))

