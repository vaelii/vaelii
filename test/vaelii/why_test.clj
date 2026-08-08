;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.why-test
  "`why` / `why-not`: the justification graph read back as a proof tree.

  `supporting-justifications` gives one hop; `why` walks all the way down to premises,
  which is what \"why does the KB believe this?\" actually asks.  `why-not` is the
  complement — for a sentex that is stored but OUT, the reason it is OUT."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- vars-in
  "Every variable symbol appearing anywhere in a form."
  [form]
  (into #{} (filter #(and (symbol? %) (.startsWith (name %) "?")))
        (tree-seq sequential? seq form)))

;; ---- why ----------------------------------------------------------------

(tu/deftest-kb why-walks-a-derivation-down-to-its-premises
  (tu/with-terms [parentOf grandparentOf Tom Bob Ann FamContext]
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                   (list grandparentOf '?x '?z) FamContext)
    (let [h1 (v/assert kb (list parentOf Tom Bob) FamContext)
          h2 (v/assert kb (list parentOf Bob Ann) FamContext)
          gp (v/handle-of kb (list grandparentOf Tom Ann) FamContext)
          w  (v/why kb gp)]
      (testing "the derived conclusion is believed, and is not a premise"
        (is (some? gp))
        (is (true? (:believed? w)))
        (is (false? (:premise? w)))
        (is (= (list grandparentOf Tom Ann) (:sentence w)))
        (is (= FamContext (:context w)))
        (is (some? (:defeat-class w))))
      (testing "one supporting justification, naming the rule and its two antecedents"
        (is (= 1 (count (:support w))))
        (let [[s] (:support w)]
          (is (some? (:justification s)))
          (is (= #{h1 h2} (set (map :handle (:because s)))))
          (testing "and the antecedents are premises, so the tree terminates there"
            (is (every? :premise? (:because s)))
            (is (every? #(nil? (:support %)) (:because s)))
            (is (every? #(= :default (:strength %)) (:because s)))))))))

(tu/deftest-kb why-shows-the-rule-with-the-authors-variable-names
  (tu/with-terms [parentOf grandparentOf Tom Bob Ann FamContext]
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                   (list grandparentOf '?x '?z) FamContext)
    (v/assert kb (list parentOf Tom Bob) FamContext)
    (v/assert kb (list parentOf Bob Ann) FamContext)
    (let [[s] (:support (v/why kb (v/handle-of kb (list grandparentOf Tom Ann) FamContext)))]
      (testing "the informant is the rule handle, and the rule sentence is reported"
        (is (integer? (:informant s)))
        (is (some? (:rule s)))
        (is (= (:informant s) (:id (v/sentex kb (:informant s))))))
      (testing "a rule is stored canonically numbered, but reads back as it was written"
        ;; the stored sentence uses ?var0/?var1/?var2; originalize restores ?x/?y/?z
        (is (= '#{?x ?y ?z} (vars-in (:rule s))))
        (is (empty? (filter #(.startsWith (name %) "?var") (vars-in (:rule s))))))
      (testing "the rule is reported as the rule, not recurred into as a fact"
        ;; it *is* an antecedent of the justification, so without lifting it out it
        ;; would appear among :because as if it were data
        (is (not (contains? (set (map :handle (:because s))) (:informant s))))))))

(tu/deftest-kb why-terminates-on-a-cyclic-justification-graph
  (tu/with-terms [seedOf p q Thing CycContext]
    ;; seed -> p, p -> q, q -> p.  (p Thing) is derived twice: once from the seed and
    ;; once from (q Thing), which is itself derived from (p Thing) — a genuine cycle
    ;; in the justification graph, not a rule-level one.
    (v/assert-rule kb [(list seedOf '?x)] (list p '?x) CycContext)
    (v/assert-rule kb [(list p '?x)] (list q '?x) CycContext)
    (v/assert-rule kb [(list q '?x)] (list p '?x) CycContext)
    (v/assert kb (list seedOf Thing) CycContext)
    (let [ph (v/handle-of kb (list p Thing) CycContext)
          w  (v/why kb ph)]
      (testing "the cyclic derivation is walked without recursing forever"
        (is (some? ph))
        (is (true? (:believed? w)))
        (is (<= 2 (count (:support w)))))                   ; from the seed, and from q
      (testing "the back edge is reported as a cycle rather than expanded again"
        (let [cycles (filter :cycle?
                             (for [s (:support w), b (:because s)
                                   s2 (:support b) b2 (:because s2)]
                               b2))]
          (is (seq cycles))
          (is (= #{ph} (set (map :handle cycles)))))))))

(tu/deftest-kb why-on-a-premise-and-on-an-unknown-handle
  (tu/with-terms [dog Muffet FactContext]
    (let [h (v/assert kb (list dog Muffet) FactContext {:strength :monotonic})
          w (v/why kb h)]
      (testing "a premise terminates immediately, carrying its assumption strength"
        (is (true? (:believed? w)))
        (is (true? (:premise? w)))
        (is (= :monotonic (:strength w)))
        (is (nil? (:support w)))))
    (testing "an unknown handle is reported as not stored"
      (is (false? (:stored? (v/why kb 99999999)))))))

(defn- why-nodes
  "Every node of a `why` tree, root included, depth-first."
  [w]
  (cons w (mapcat why-nodes (mapcat :because (:support w)))))

(tu/deftest-kb why-bounds-its-depth-and-the-bound-is-an-option
  ;; A derivation chain longer than the 256 default: rule + 300 `nextOf` links, so
  ;; `(reached NodeN)` rests on `(reached NodeN-1)` rests on … — no repeated handle,
  ;; so the cycle guard never fires and only the depth cap stands between the walk
  ;; and the stack.
  (tu/with-terms [nextOf reached ChainContext]
    (let [n     300
          nodes (vec (repeatedly (inc n) #(tu/tmp-ind "Node")))]
      (v/assert-rule kb [(list nextOf '?x '?y) (list reached '?x)]
                     (list reached '?y) ChainContext)
      (v/assert kb (list reached (nodes 0)) ChainContext)
      ;; the chainer's own derivation bound (`default-chain-opts` :max-depth 64) would
      ;; stop the chain long before `why`'s cap is reached, so lift it past the chain
      (v/assert-many kb (map #(list nextOf (nodes %) (nodes (inc %))) (range n))
                     ChainContext {:max-depth 400})
      (let [h  (v/handle-of kb (list reached (nodes n)) ChainContext)
            h0 (v/handle-of kb (list reached (nodes 0)) ChainContext)]
        (is (some? h) "the chain forward-derived to its end")
        (testing "the default cap truncates the deep branch and says so"
          (let [w (v/why kb h)]
            (is (true? (:believed? w)))
            (is (some :truncated? (why-nodes w)))
            (is (not-any? #(= h0 (:handle %)) (why-nodes w))
                "the chain's far end sits past the cap, so the default walk never reaches it")))
        (testing "{:max-depth n} moves the cap, and a big enough one returns the whole tree"
          (let [w (v/why kb h {:max-depth 400})]
            (is (not-any? :truncated? (why-nodes w)))
            (is (some #(and (= h0 (:handle %)) (:premise? %)) (why-nodes w))
                "the walk now bottoms out at the premise the chain started from"))
          (is (some :truncated? (why-nodes (v/why kb h {:max-depth 5})))
              "and a small one truncates sooner"))
        (testing "nil, absent and empty opts are all the default"
          (is (= (v/why kb h) (v/why kb h nil) (v/why kb h {}) (v/why kb h {:max-depth nil}))))
        (testing "opts are guarded the way assert's are"
          (doseq [[what opts] {"a non-map"          :oops
                               "an unknown key"     {:max-deth 5}
                               "a non-natural depth" {:max-depth "soon"}}]
            (is (= :unknown-option
                   (:type (try (v/why kb h opts) nil
                               (catch clojure.lang.ExceptionInfo e (ex-data e)))))
                (str what " is refused"))))))))

;; ---- why-not ------------------------------------------------------------

(tu/deftest-kb why-not-reports-a-defeated-default-and-what-contradicts-it
  (tu/with-terms [flies Tweety BirdContext]
    (v/assert kb (list flies Tweety) BirdContext)                              ; default
    (v/assert kb (list 'not (list flies Tweety)) BirdContext {:strength :monotonic})
    (let [h  (v/handle-of kb (list flies Tweety) BirdContext)
          wn (v/why-not kb h)]
      (testing "the default lost, but is still stored (it can be revived)"
        (is (some? h))
        (is (false? (v/in? kb h)))
        (is (false? (:believed? wn)))
        (is (= :defeated (:reason wn))))
      (testing "the believed negation is named as the contradiction"
        (is (= 1 (count (:contradicted-by wn))))
        (let [[c] (:contradicted-by wn)]
          (is (= (list 'not (list flies Tweety)) (:sentence c)))
          (is (= :monotonic (:defeat-class c))))))))

(tu/deftest-kb why-not-reports-a-conclusion-whose-support-went-out
  (tu/with-terms [flies airborne Tweety BirdContext]
    (v/assert kb (list flies Tweety) BirdContext)                              ; default
    (v/assert-rule kb [(list flies '?x)] (list airborne '?x) BirdContext)
    (let [ah (v/handle-of kb (list airborne Tweety) BirdContext)]
      (is (some? ah))
      (is (true? (v/in? kb ah)))
      ;; now defeat the antecedent; the conclusion is not itself defeated, it simply
      ;; loses its only valid justification
      (v/assert kb (list 'not (list flies Tweety)) BirdContext {:strength :monotonic})
      (let [wn (v/why-not kb ah)
            fh (v/handle-of kb (list flies Tweety) BirdContext)]
        (testing "OUT for lack of support, not by defeat"
          (is (false? (v/in? kb ah)))
          (is (false? (:believed? wn)))
          (is (= :unsupported (:reason wn)))
          (is (false? (:premise? wn))))
        (testing "and the antecedent that went missing is named"
          (is (seq (:support wn)))
          (is (contains? (set (mapcat :missing (:support wn))) fh)))))))

(tu/deftest-kb why-not-on-a-believed-and-on-an-unknown-handle
  (tu/with-terms [dog Muffet FactContext]
    (let [h (v/assert kb (list dog Muffet) FactContext)]
      (testing "a believed handle has nothing to explain"
        (is (true? (:believed? (v/why-not kb h))))
        (is (nil? (:reason (v/why-not kb h))))))
    (testing "an unknown handle"
      (is (= :not-stored (:reason (v/why-not kb 99999999)))))))

;; ---- the two are complements -------------------------------------------

(tu/deftest-kb why-and-why-not-agree-on-belief
  (tu/with-terms [bird flies Robin Tweety penguin BirdContext]
    ;; the subtype edge is stated where the theory that reasons over it lives: the
    ;; flight rule fires on a penguin *through* this edge, and a conclusion is placed
    ;; only in a context that can see the edge it subsumed through
    (v/assert kb (list 'genl penguin bird) BirdContext)
    (v/assert kb (list 'set/defaultRule (vr/rule-sentence [(list bird '?x)] (list flies '?x)))
              BirdContext)
    (v/assert-rule kb [(list penguin '?x)] (list 'not (list flies '?x)) BirdContext)
    (v/assert kb (list bird Robin) BirdContext)
    ;; Known-true, so the bare exception rule concludes at :monotonic and *defeats* the
    ;; :default `(flies Tweety)`.  Defeat is what this test needs: a defeated datum is
    ;; still stored, so `why` can report it unbelieved and `why-not` can name the side
    ;; that beat it.  (An `exceptWhen` on the flight rule would block instead, and there
    ;; would be no handle to ask about — that is `why-not`'s sentence arity.)
    (v/assert kb (list penguin Tweety) BirdContext {:strength :monotonic})
    (let [rh (v/handle-of kb (list flies Robin) BirdContext)
          th (v/handle-of kb (list flies Tweety) BirdContext)]
      (testing "the ordinary bird flies by default, and why says on what grounds"
        (is (true? (:believed? (v/why kb rh))))
        (is (= :default (:defeat-class (v/why kb rh))))
        (is (seq (:support (v/why kb rh))))
        (is (true? (:believed? (v/why-not kb rh)))))
      (testing "the penguin does not, and why-not says which side won"
        (is (some? th))
        (is (false? (:believed? (v/why kb th))))
        (is (false? (:believed? (v/why-not kb th))))
        (is (= #{(list 'not (list flies Tweety))}
               (set (map :sentence (:contradicted-by (v/why-not kb th))))))))))
