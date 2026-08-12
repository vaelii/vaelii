;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.profile-test
  "Oracle for the workload instrument (`vaelii.impl.profile`).

  A profile is only worth reading if its **labels are true**: a tally that says a shape
  took the argument roots when it walked the trie is worse than no tally, because it
  reads as a measurement.  So the load-bearing tests here are not that counting works —
  they are that each of the access paths the tally names is the path the engine actually
  took, established by making the engine take it and then reading the label back.

  The other half is the switch.  The instrument sits on `candidate-handles`, on
  `matches-hierarchical`, on every `IndexStore` read and on `index-sentex`; off, all of
  them must count nothing at all, since an instrument that leaks counts into an ordinary
  run is a constant on the hot path."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.columnar]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

;; Every test builds its own KB inline (`tu/with-neutral-kb`), because the shapes here
;; need a vocabulary each one declares.  The only fixture is the instrument's own: it is
;; process-wide, so a test that throws while collecting would hand the next one a running
;; tally.
(use-fixtures :each (fn [t] (try (t) (finally (prof/stop)))))

(defn- collected
  "The snapshot of what `f` did, with the instrument started and stopped around it."
  [f]
  (prof/start)
  (try (f) (finally))
  (prof/stop))

(defn- native-trie?
  "Does this KB's index walk its **own** trie rather than `KvIndexStore`'s?

  `:fan` is the one tally that is not index-independent: the columnar store's walk is
  native and counts no node probes, so it reports no fan at all (docs/profile.md).  That
  is a contract rather than a gap, so the fan test asserts it on this backend instead of
  standing aside — a tally that invented a fan here would be worse than the silence."
  [kb]
  (instance? vaelii.impl.columnar.ColumnarIndexStore (:index kb)))

(defn- paths-of
  "The access paths a snapshot recorded for literals on `pred`."
  [snap pred]
  (into #{} (comp (filter (fn [[k _]] (= pred (nth k 0)))) (map (fn [[k _]] (nth k 3))))
        (:goals snap)))

(defn- shapes-of
  "The `[adornment path]` pairs a snapshot recorded for literals on `pred`."
  [snap pred]
  (into #{} (comp (filter (fn [[k _]] (= pred (nth k 0)))) (map (fn [[k _]] [(nth k 2) (nth k 3)])))
        (:goals snap)))

;; ---- the switch ---------------------------------------------------------

(deftest off-by-default-and-silent
  (testing "nothing is collecting until somebody asks"
    (is (false? (prof/profiling?)))
    (is (nil? (prof/snapshot)))
    (is (nil? (prof/stop)) "stopping a stopped instrument is not an error"))
  (tu/with-neutral-kb [kb tu/fresh]
    (let [p (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind) c (tu/tmp-ctx)]
      (v/assert kb (list 'genlContext c 'UniverseContext) 'UniverseContext)
      (v/assert kb (list 'binaryPredicate p) c)
      (v/assert kb (list p a b) c)
      (testing "a whole assert-and-query round trip while off leaves no tally to read"
        (is (seq (v/sentexes-matching kb (list p a '?y))))
        (is (nil? (prof/snapshot)))
        (is (false? (prof/profiling?)))))))

(deftest start-clears-the-previous-run
  (tu/with-neutral-kb [kb tu/fresh]
    (let [p (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind) c (tu/tmp-ctx)]
      (v/assert kb (list 'genlContext c 'UniverseContext) 'UniverseContext)
      (v/assert kb (list 'binaryPredicate p) c)
      (prof/start)
      (v/assert kb (list p a b) c)
      (is (pos? (count (:writes (prof/snapshot)))))
      (prof/start)
      (is (empty? (:writes (prof/snapshot))) "a fresh start holds nothing from the last one")
      (prof/stop))))

;; ---- the labels ---------------------------------------------------------
;;
;; One test per access path the tally can name.  Each builds the pattern that forces the
;; path and then asserts the label came back — which is the only thing that makes a
;; reading of a real corpus mean anything.

(deftest each-access-path-is-labelled-with-the-path-taken
  (tu/with-neutral-kb [kb tu/fresh]
    (let [p   (tu/tmp-pred) q (tu/tmp-pred)
          a   (tu/tmp-ind)  b (tu/tmp-ind)
          ctx (tu/tmp-ctx)]
      (v/assert kb (list 'genlContext ctx 'UniverseContext) 'UniverseContext)
      (v/assert kb (list 'binaryPredicate p) ctx)
      (v/assert kb (list 'binaryPredicate q) ctx)
      (v/assert kb (list p a b) ctx)
      (v/assert kb (list 'not (list q a b)) ctx)

      (testing "a ground argument after an open one takes the argument roots"
        ;; `raw-match` is the level-2 matcher, which is `candidate-handles`' own caller;
        ;; going through it rather than the public read keeps this about ONE decision
        (let [snap (collected #(doall (res/raw-match kb (list p '?x b) ctx)))]
          (is (contains? (paths-of snap p) :arg-roots))
          (is (contains? (shapes-of snap p) ["fb" :arg-roots])
              "and the adornment names which position was bound")))

      (testing "a left prefix keeps the trie"
        (let [snap (collected #(doall (res/raw-match kb (list p a '?y) ctx)))]
          (is (contains? (paths-of snap p) :trie))
          (is (contains? (shapes-of snap p) ["bf" :trie]))))

      (testing "an open negative with something pinned reads the roots"
        (let [snap (collected #(doall (res/raw-match kb (list 'not (list q '?x b)) ctx)))]
          (is (contains? (paths-of snap q) :negative-roots))))

      (testing "an open negative with nothing pinned fans the :false node"
        (let [snap (collected #(doall (res/raw-match kb (list 'not (list '?p '?x '?y)) ctx)))]
          (is (contains? (paths-of snap :open) :negative-fan))))

      (testing "a dotted rest reads whole functor extents instead of positional indexes"
        (let [snap (collected #(doall (res/raw-match kb (list p a '. '?args) ctx)))]
          (is (contains? (paths-of snap p) :dotted-extent)))
        (let [snap (collected #(doall (res/raw-match kb (list '?pred '. '?args) ctx)))]
          (is (contains? (paths-of snap :open) :dotted-extent))))

      (testing "the argument-root retrieval switch moves the label with the behaviour"
        (let [snap (collected #(binding [res/*arg-root-retrieval* false]
                                 (doall (res/raw-match kb (list p '?x b) ctx))))]
          (is (= #{:trie} (paths-of snap p))
              "with the roots off the same shape takes the trie, and says so"))))))

(deftest a-compound-argument-is-labelled-structural-or-functor-extent
  (tu/with-neutral-kb [kb tu/fresh]
    (let [p   (tu/tmp-pred) f (tu/tmp-pred)
          a   (tu/tmp-ind)  u (tu/tmp-ind)
          ctx (tu/tmp-ctx)]
      (v/assert kb (list 'genlContext ctx 'UniverseContext) 'UniverseContext)
      (v/assert kb (list 'binaryPredicate p) ctx)
      (v/assert kb (list 'binaryPredicate f) ctx)
      (v/assert kb (list p a (list f u u)) ctx)
      (testing "on, the structural trie narrows on the compound's interior"
        (let [snap (collected #(doall (res/raw-match kb (list p '?o (list f '?n u)) ctx)))]
          (is (contains? (paths-of snap p) :structural))
          (is (contains? (shapes-of snap p) ["fF" :structural])
              "F is an open compound, which is what the structural index is for")))
      (testing "off, the same shape falls back to the functor extent"
        (let [snap (collected #(binding [res/*structural-index* false]
                                 (doall (res/raw-match kb (list p '?o (list f '?n u)) ctx))))]
          (is (contains? (paths-of snap p) :functor-extent)))))))

(deftest the-set-algebra-matcher-is-labelled-too
  (testing "the level-4 matcher decides its own candidate source, and it is not candidate-handles"
    (tu/with-neutral-kb [kb tu/fresh]
      (let [p   (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind) ctx (tu/tmp-ctx)]
        (v/assert kb (list 'genlContext ctx 'UniverseContext) 'UniverseContext)
        (v/assert kb (list 'binaryPredicate p) ctx)
        (v/assert kb (list p a b) ctx)
        (let [snap (collected #(doall (res/matches-hierarchical kb (list p a '?y) ctx)))]
          (is (contains? (paths-of snap p) :hier-scoped-roots)))
        (let [snap (collected #(doall (res/matches-hierarchical kb (list p '?x '?y) ctx)))]
          (is (contains? (paths-of snap p) :hier-functor-extent)
              "nothing indexable to lead with, so it reads the sub-predicates' extents"))))))

;; ---- the adornment alphabet ---------------------------------------------

(deftest the-adornment-says-what-the-index-can-key
  (testing "one character per argument, and the classes are the index's rather than a reader's"
    (is (= ['pred :true "bf" :trie] (prof/shape-of '(pred Tom ?y) :true :trie)))
    (is (= ['pred :true "fb" :trie] (prof/shape-of '(pred ?x Tom) :true :trie)))
    (is (= ['pred :true "bn" :trie] (prof/shape-of '(pred Tom 1970) :true :trie))
        "a number is ground and is no key, which is why it does not divert to the roots")
    (is (= ['pred :true "bn" :trie] (prof/shape-of '(pred Tom "a string") :true :trie)))
    (is (= ['pred :true "bB" :trie] (prof/shape-of '(pred Tom (f Kilogram)) :true :trie))
        "a ground compound is keyed whole by the argument roots")
    (is (= ['pred :true "bF" :trie] (prof/shape-of '(pred Tom (f ?n)) :true :trie))
        "an open compound is the shape only the structural trie reaches inside")
    (is (= [:open :true "b" :trie] (prof/shape-of '(?type Muffet) :true :trie))
        "an open functor puts every argument behind it, and is its own class")
    (is (= [:none :false "" :trie] (prof/shape-of 'NotASentence :false :trie))
        "a non-sentence body has no arguments to adorn")))

;; ---- the write tally ----------------------------------------------------

(deftest the-write-tally-counts-the-keys-the-index-wrote
  (tu/with-neutral-kb [kb tu/fresh]
    (let [p   (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind) ctx (tu/tmp-ctx)]
      (v/assert kb (list 'genlContext ctx 'UniverseContext) 'UniverseContext)
      (v/assert kb (list 'binaryPredicate p) ctx)
      (let [snap (collected #(v/assert kb (list p a b) ctx))
            row  (get (:writes snap) p)
            sx   (first (filter #(= p (some-> (sx/body %) first))
                                (map #(p/get-sentex (:records kb) %)
                                     (p/sentexes-with-functor (:index kb) p))))]
        (is (some? row) "the tally is keyed by the functor asserted")
        (is (= 1 (:asserts row)))
        (is (= (inc (count (sx/path sx))) (:levels row))
            "one trie level per path token, plus the root")
        (is (= (count (kv/root-keys sx)) (:roots row))
            "and the secondary roots are exactly the ones the index wrote")
        (is (= (count (kv/sentex-terms sx)) (:terms row)))))))

(deftest the-retraction-tally-is-its-own-tally
  (tu/with-neutral-kb [kb tu/fresh]
    (let [p (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind) ctx (tu/tmp-ctx)]
      (v/assert kb (list 'genlContext ctx 'UniverseContext) 'UniverseContext)
      (v/assert kb (list 'binaryPredicate p) ctx)
      (let [h    (v/assert kb (list p a b) ctx)
            sx   (p/get-sentex (:records kb) h)
            snap (collected #(v/retract! kb h))
            row  (get (:retracts snap) p)]
        (is (some? row) "a retraction is tallied, keyed by the functor it removed")
        (is (= 1 (:retracts row)))
        (is (= (inc (count (sx/path sx))) (:levels row))
            "one decrement per path token, plus the root")
        (is (= (count (kv/root-keys sx)) (:roots row))
            "and the secondary roots are exactly the ones the index removed")
        (is (= (count (kv/sentex-terms sx)) (:terms row)))
        (testing "and it is separate from the assert tally, not that one with a sign on it"
          (is (nil? (get (:writes snap) p))
              "a retraction writes no index keys, so it appears in neither :writes nor a merged total"))))))

(deftest how-many-trie-nodes-die-is-decided-by-what-else-is-stored
  (testing "the one quantity in the retraction tally the sentex does not decide"
    (tu/with-neutral-kb [kb tu/fresh]
      (let [p (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind) c (tu/tmp-ind) ctx (tu/tmp-ctx)]
        (v/assert kb (list 'genlContext ctx 'UniverseContext) 'UniverseContext)
        (v/assert kb (list 'binaryPredicate p) ctx)
        (let [h1     (v/assert kb (list p a b) ctx)
              h2     (v/assert kb (list p a c) ctx)
              ;; `(p a c)` still holds the `[p]` and `[p a]` prefix up, so only the
              ;; branch below it dies
              shared (:dead (get (:retracts (collected #(v/retract! kb h1))) p))
              ;; and now nothing does
              alone  (:dead (get (:retracts (collected #(v/retract! kb h2))) p))]
          (is (pos? (long shared)))
          (is (< (long shared) (long alone))
              (str "the same shape of fact kills more trie nodes when nothing shares its"
                   " prefix — which is why a retraction's cost is not a constant per"
                   " family the way an assert's is")))))))

;; ---- the read tally -----------------------------------------------------

(deftest the-read-tally-names-the-family-that-answered
  (tu/with-neutral-kb [kb tu/fresh]
    (let [p   (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind) ctx (tu/tmp-ctx)]
      (v/assert kb (list 'genlContext ctx 'UniverseContext) 'UniverseContext)
      (v/assert kb (list 'binaryPredicate p) ctx)
      (v/assert kb (list p a b) ctx)
      (let [ix (:index kb)]
        (is (= {:functor-root 1} (:reads (collected #(p/count-with-functor ix p)))))
        (is (= {:context-root 1} (:reads (collected #(p/count-in-context ix ctx)))))
        (is (= {:term-roster 1}  (:reads (collected #(p/term-count ix)))))
        (is (= {:trie-counts 1}  (:reads (collected #(p/count-children ix [p])))))
        (is (= {:rule-index 1}   (:reads (collected #(p/rules-by-consequent ix p)))))
        (is (= {:term-index 1}   (:reads (collected #(p/sentexes-with-term ix a)))))
        (testing "a predicate-agnostic argument read touches two families and says so"
          (is (= {:argument-slot 1 :argument-root 1}
                 (:reads (collected #(p/sentexes-with-arg ix 1 a))))))
        (testing "a whole trie walk is one read of the trie, whatever it cost"
          (let [snap (collected #(p/lookup ix (sx/path (sx/sentex (list p a b) ctx))))]
            (is (= 1 (get-in snap [:reads :trie-lookup])))
            (is (nil? (get-in snap [:reads :trie-counts]))
                "the walk reads the backend directly; the counts family is the planner's")))))))

;; ---- the fan tally ------------------------------------------------------

(deftest the-fan-tally-counts-what-the-walk-touched
  (tu/with-neutral-kb [kb tu/fresh]
    (let [p   (tu/tmp-pred) ctx (tu/tmp-ctx)
          inds (repeatedly 12 tu/tmp-ind)
          shared (tu/tmp-ind)]
      (v/assert kb (list 'genlContext ctx 'UniverseContext) 'UniverseContext)
      (v/assert kb (list 'binaryPredicate p) ctx)
      (doseq [i inds] (v/assert kb (list p i shared) ctx))
      (if (native-trie? kb)
        (testing "the columnar trie walks natively, so it reports no fan rather than a wrong one"
          (let [snap (collected #(p/lookup (:index kb)
                                           (sx/path (sx/sentex (list p '?x shared) ctx))))]
            (is (empty? (:fan snap))
                "docs/profile.md: :fan is KvIndexStore's, and this store must not fake one")
            (is (= 1 (get-in snap [:reads :trie-lookup]))
                "the read tally is index-independent even where the fan tally is not")))
        (do
          (testing "a ground lookup walks one node per level"
            (let [snap (collected #(p/lookup (:index kb)
                                             (sx/path (sx/sentex (list p (first inds) shared) ctx))))
                  row  (get (:fan snap) p)]
              (is (= 1 (:calls row)))
              (is (= 1 (:widest row)) "nothing ever branched")
              (is (= 1 (:handles row)))))
          (testing "a leading-variable lookup expands the whole child set at that level"
            (let [snap (collected #(p/lookup (:index kb)
                                             (sx/path (sx/sentex (list p '?x shared) ctx))))
                  row  (get (:fan snap) p)]
              (is (= 1 (:calls row)))
              (is (= 12 (:widest row))
                  "one frontier node per distinct first argument — the fan the roots exist to avoid")
              (is (> (long (:visits row)) 12)))))))))
