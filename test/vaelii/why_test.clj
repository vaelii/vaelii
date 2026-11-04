;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.why-test
  "`why` / `why-not`: the justification graph read back down to premises.

  `supporting-justifications` gives one hop; `why` walks all the way down to premises,
  which is what \"why does the KB believe this?\" actually asks.  `why-not` is the
  complement — for a sentex that is stored but OUT, the reason it is OUT."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.provers :as provers]
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
  (tu/with-terms [parentOf grandparentOf Tom Bob Ann CxFam]
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                   (list grandparentOf '?x '?z) CxFam {:direction :forward})
    (let [h1    (v/assert kb (list parentOf Tom Bob) CxFam)
          h2    (v/assert kb (list parentOf Bob Ann) CxFam)
          gp    (v/handle-of kb (list grandparentOf Tom Ann) CxFam)
          {:keys [root nodes]} (v/why kb gp)
          w     (nodes root)]
      (testing "the derived conclusion is the root, believed, and not a premise"
        (is (some? gp))
        (is (= gp root (:handle w)))
        (is (true? (:believed? w)))
        (is (false? (:premise? w)))
        (is (= (list grandparentOf Tom Ann) (:sentence w)))
        (is (= CxFam (:context w)))
        (is (some? (:defeat-class w))))
      (testing "one supporting justification, naming the rule and its two antecedents"
        (is (= 1 (count (:support w))))
        (let [[s] (:support w)]
          (is (some? (:justification s)))
          (is (= #{h1 h2} (set (:because s))))
          (testing "and the antecedents are premises, so the graph ends there"
            (is (= #{gp h1 h2} (set (keys nodes))))
            (is (every? (comp :premise? nodes) (:because s)))
            (is (every? #(nil? (:support (nodes %))) (:because s)))
            (is (every? #(= :default (:strength (nodes %))) (:because s)))))))))

(tu/deftest-kb why-shows-the-rule-with-the-authors-variable-names
  (tu/with-terms [parentOf grandparentOf Tom Bob Ann CxFam]
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                   (list grandparentOf '?x '?z) CxFam {:direction :forward})
    (v/assert kb (list parentOf Tom Bob) CxFam)
    (v/assert kb (list parentOf Bob Ann) CxFam)
    (let [w   (v/why kb (v/handle-of kb (list grandparentOf Tom Ann) CxFam))
          [s] (:support ((:nodes w) (:root w)))]
      (testing "the informant is the rule handle, and the rule sentence is reported"
        (is (integer? (:informant s)))
        (is (some? (:rule s)))
        (is (= (:informant s) (:id (v/sentex kb (:informant s))))))
      (testing "a rule is stored canonically numbered, but reads back as it was written"
        ;; the stored sentence uses ?var0/?var1/?var2; originalize restores ?x/?y/?z
        (is (= '#{?x ?y ?z} (vars-in (:rule s))))
        (is (empty? (filter #(.startsWith (name %) "?var") (vars-in (:rule s))))))
      (testing "the rule is reported as the rule, not walked into as a fact"
        ;; it *is* an antecedent of the justification, so without lifting it out it
        ;; would appear among :because as if it were data
        (is (not (contains? (set (:because s)) (:informant s))))
        (is (not (contains? (:nodes w) (:informant s))))))))

(tu/deftest-kb why-returns-a-cyclic-justification-graph-as-a-cycle
  (tu/with-terms [seedOf p q Thing CxCyc]
    ;; seed -> p, p -> q, q -> p.  (p Thing) is derived twice: once from the seed and
    ;; once from (q Thing), which is itself derived from (p Thing) — a genuine cycle
    ;; in the justification graph, not a rule-level one.
    (v/assert-rule kb [(list seedOf '?x)] (list p '?x) CxCyc {:direction :forward})
    (v/assert-rule kb [(list p '?x)] (list q '?x) CxCyc {:direction :forward})
    (v/assert-rule kb [(list q '?x)] (list p '?x) CxCyc {:direction :forward})
    (let [sh    (v/assert kb (list seedOf Thing) CxCyc)
          ph    (v/handle-of kb (list p Thing) CxCyc)
          qh    (v/handle-of kb (list q Thing) CxCyc)
          {:keys [nodes]} (v/why kb ph)
          cites (fn [h] (set (mapcat :because (:support (nodes h)))))]
      (testing "the cyclic derivation is walked to an end, each handle once"
        (is (some? ph))
        (is (true? (:believed? (nodes ph))))
        (is (<= 2 (count (:support (nodes ph)))))            ; from the seed, and from q
        (is (= #{sh ph qh} (set (keys nodes)))))
      (testing "and the cycle is the two nodes naming each other"
        (is (= #{sh qh} (cites ph)))
        (is (= #{ph} (cites qh)))))))

(tu/deftest-kb why-on-a-premise-and-on-an-unknown-handle
  (tu/with-terms [dog Muffet CxFact]
    (let [h (v/assert kb (list dog Muffet) CxFact {:strength :monotonic})
          w (v/why kb h)]
      (testing "a premise is the whole graph, carrying its assumption strength"
        (is (= [h] (keys (:nodes w))))
        (is (true? (:believed? ((:nodes w) h))))
        (is (true? (:premise? ((:nodes w) h))))
        (is (= :monotonic (:strength ((:nodes w) h))))
        (is (nil? (:support ((:nodes w) h))))))
    (testing "an unknown handle is reported as not stored"
      (let [w (v/why kb 99999999)]
        (is (= 99999999 (:root w)))
        (is (false? (:stored? ((:nodes w) 99999999))))))))

(defn- reach-chain!
  "Assert, for each predicate `link` in `links`, the forward rule `(link ?x ?y) (reached
  ?x) ⇒ (reached ?y)`; then the premise `(reached Node0)`; then `n` facts of each `link`
  from Node_i to Node_i+1.  Returns the handles of `(reached Node0)` and `(reached
  Node_n)`."
  [kb links reached ctx n]
  (let [nodes (vec (repeatedly (inc n) #(tu/tmp-ind "Node")))]
    (doseq [link links]
      (v/assert-rule kb [(list link '?x '?y) (list reached '?x)]
                     (list reached '?y) ctx {:direction :forward}))
    (v/assert kb (list reached (nodes 0)) ctx)
    (v/assert-many kb (for [link links, i (range n)] (list link (nodes i) (nodes (inc i))))
                   ctx)
    [(v/handle-of kb (list reached (nodes 0)) ctx)
     (v/handle-of kb (list reached (nodes n)) ctx)]))

(tu/deftest-kb why-returns-a-chain-longer-than-256-whole
  ;; A derivation chain of 300 links: `(reached Node300)` rests on `(reached Node299)`
  ;; rests on … `(reached Node0)`, so the graph is 301 `reached` nodes and 300 links.
  ;; The walk is iterative, so its depth is not the JVM stack's depth — asserted below on
  ;; a deliberately small stack.
  (tu/with-terms [nextOf reached CxChain]
    (let [n       300
          [h0 h]  (reach-chain! kb [nextOf] reached CxChain n)
          w       (v/why kb h)]
      (is (some? h) "the chain forward-derived to its end")
      (testing "every link comes back, down to the premise the chain started from"
        (is (= (inc (* 2 n)) (count (:nodes w))))
        (is (true? (:premise? ((:nodes w) h0)))))
      (testing "the walk spends no JVM stack: it returns on a small one"
        ;; 256 KB is ample for the iterative walk and far short of what 300 recursive
        ;; frames need
        (let [out (atom nil), err (atom nil)
              t   (Thread. nil
                           ^Runnable (fn []
                                       (try (reset! out (v/why kb h))
                                            (catch Throwable e (reset! err e))))
                           "why-small-stack" (* 256 1024))]
          (.start t) (.join t)
          (is (nil? @err) (str "why overflowed a 256 KB stack: " @err))
          (is (= w @out) "and builds the same graph the main-thread walk does"))))))

(tu/deftest-kb why-of-a-ladder-grows-with-its-length-not-its-paths
  ;; Two rules conclude each rung from the one below, so each `(reached Node_i+1)` has two
  ;; justifications that share the antecedent `(reached Node_i)`.  The paths from the top
  ;; rung down number 2^n; the graph holds n+1 rungs and 2n links.
  (tu/with-terms [nextOf linkOf reached CxLadder]
    (let [n      40
          [h0 h] (reach-chain! kb [nextOf linkOf] reached CxLadder n)
          w      (v/why kb h)]
      (is (= 2 (count (:support ((:nodes w) h)))) "two justifications per rung")
      (is (= (inc (* 3 n)) (count (:nodes w))))
      (is (true? (:premise? ((:nodes w) h0)))))))

;; ---- why-not ------------------------------------------------------------

(tu/deftest-kb why-not-reports-a-defeated-default-and-what-contradicts-it
  (tu/with-terms [flies Tweety CxBird]
    (v/assert kb (list flies Tweety) CxBird)                              ; default
    (v/assert kb (list 'not (list flies Tweety)) CxBird {:strength :monotonic})
    (let [h  (v/handle-of kb (list flies Tweety) CxBird)
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
  (tu/with-terms [flies airborne Tweety CxBird]
    (v/assert kb (list flies Tweety) CxBird)                              ; default
    (v/assert-rule kb [(list flies '?x)] (list airborne '?x) CxBird {:direction :forward})
    (let [ah (v/handle-of kb (list airborne Tweety) CxBird)]
      (is (some? ah))
      (is (true? (v/in? kb ah)))
      ;; now defeat the antecedent; the conclusion is not itself defeated, it rests on a
      ;; handle the placed defeat removes from belief
      (v/assert kb (list 'not (list flies Tweety)) CxBird {:strength :monotonic})
      (let [wn (v/why-not kb ah)
            fh (v/handle-of kb (list flies Tweety) CxBird)]
        (testing "withdrawn by the defeat of what it rests on, not defeated itself"
          (is (false? (v/in? kb ah)))
          (is (false? (:believed? wn)))
          (is (= :withdrawn (:reason wn))))
        (testing "and the defeated antecedent is named"
          (is (= [fh] (mapv :handle (:withdrawn-by wn)))))))))

(tu/deftest-kb why-not-on-a-believed-and-on-an-unknown-handle
  (tu/with-terms [dog Muffet CxFact]
    (let [h (v/assert kb (list dog Muffet) CxFact)]
      (testing "a believed handle has nothing to explain"
        (is (true? (:believed? (v/why-not kb h))))
        (is (nil? (:reason (v/why-not kb h))))))
    (testing "an unknown handle"
      (is (= :not-stored (:reason (v/why-not kb 99999999)))))))

(tu/deftest-kb why-not-of-a-sentence-reads-the-context-the-reader-inherits-it-from
  ;;   CxUniverse
  ;;     └─ CxGen      (dog Muffet), defeated there
  ;;          └─ CxSpec   stores nothing
  ;; `ask?` from CxSpec walks the genlCx edge, so `why-not` asked from CxSpec explains the
  ;; sentex CxGen stores instead of reporting it as unstored.
  (tu/with-terms [dog Muffet CxGen CxSpec]
    (v/assert kb (list 'genl dog 'thing) 'CxUniverse)
    (v/assert kb (list 'genlCx CxGen 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxSpec CxGen) 'CxUniverse)
    (let [h (v/assert kb (list dog Muffet) CxGen)]
      (testing "a believed sentence the reader inherits"
        (is (true? (:believed? (v/why-not kb (list dog Muffet) CxSpec))))
        (is (= h (:handle (v/why-not kb (list dog Muffet) CxSpec)))))
      (testing "reported under the context that stores it"
        (is (= CxGen (:context (v/why-not kb (list dog Muffet) CxSpec))))))
    (testing "a sentence no visible context stores is still :not-stored"
      (is (= :not-stored (:reason (v/why-not kb (list dog 'NoSuchThing) CxSpec)))))))

;; ---- the two are complements -------------------------------------------

(tu/deftest-kb why-and-why-not-agree-on-belief
  (tu/with-terms [bird flies Robin Tweety penguin CxBird]
    ;; the subtype edge is stated where the theory that reasons over it lives: the
    ;; flight rule fires on a penguin *through* this edge, and a conclusion is placed
    ;; only in a context that can see the edge it subsumed through
    (v/assert kb (list 'genl penguin bird) CxBird)
    (v/assert kb (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence [(list bird '?x)] (list flies '?x))))
              CxBird)
    (v/assert-rule kb [(list penguin '?x)] (list 'not (list flies '?x)) CxBird {:direction :forward})
    (v/assert kb (list bird Robin) CxBird)
    ;; Known-true, so the bare exception rule concludes at :monotonic and *defeats* the
    ;; :default `(flies Tweety)`.  Defeat is what this test needs: a defeated datum is
    ;; still stored, so `why` can report it unbelieved and `why-not` can name the side
    ;; that beat it.  (An `exceptWhen` on the flight rule would block instead, and there
    ;; would be no handle to ask about — that is `why-not`'s sentence arity.)
    (v/assert kb (list penguin Tweety) CxBird {:strength :monotonic})
    (let [rh (v/handle-of kb (list flies Robin) CxBird)
          th (v/handle-of kb (list flies Tweety) CxBird)]
      (testing "the ordinary bird flies by default, and why says on what grounds"
        (is (true? (:believed? (tu/why-root kb rh))))
        (is (= :default (:defeat-class (tu/why-root kb rh))))
        (is (seq (:support (tu/why-root kb rh))))
        (is (true? (:believed? (v/why-not kb rh)))))
      (testing "the penguin does not, and why-not says which side won"
        (is (some? th))
        (is (false? (:believed? (tu/why-root kb th))))
        (is (false? (:believed? (v/why-not kb th))))
        (is (= #{(list 'not (list flies Tweety))}
               (set (map :sentence (:contradicted-by (v/why-not kb th))))))))))

;; ---- the candidates the backward entry point reads -----------------------------

(tu/deftest-kb the-backward-entry-points-candidate-rules-are-one-definition
  ;; `why` / `argue` / `prove` / `abduce` all reach the rules that could conclude a goal
  ;; through `provers/candidate-rules` — one filter chain, so the DFS prover, the node
  ;; engine, the tacticians and the abducer cannot answer from four readings of "which
  ;; rules apply here".
  (tu/with-terms [seenA derivedQ Subject CxWhyCand]
    (v/assert-rule kb [(list seenA '?x)] (list derivedQ '?x) CxWhyCand {:direction :forward})
    (testing "a sentence goal finds the rule that concludes it"
      (is (= 1 (count (provers/candidate-rules kb (list derivedQ Subject) CxWhyCand)))))
    (testing "a goal that is not a sentence has no functor, so there is nothing to probe"
      ;; `nm/functor` of a non-sequential form is nil, and a lookup under a nil key is a
      ;; question about the rule index rather than about the goal
      (is (nil? (provers/candidate-rules kb Subject CxWhyCand)))
      (is (nil? (provers/candidate-rules kb nil CxWhyCand))))
    (testing "and the entry point has no second copy of the filter chain"
      ;; Two definitions of "which rules could conclude this" is two things to keep in
      ;; step, and they had already drifted on exactly the case above.
      (is (nil? (re-find #"\(defn-? +candidate-rules" (slurp "src/vaelii/core.clj")))
          "vaelii.core reads its candidates through provers/candidate-rules"))))

(defn- seat-explanations
  "`why`, `why-not` and `argue` in content form, for each `[sentence context]` of `goals`,
  on a seat that writes `noise` and then runs `writes` in order."
  [writes goals noise]
  (tu/with-cleared-kb [kb tu/isolated-fresh]
    (run! #(% kb) (cons noise writes))
    (into {} (for [[s c] goals
                   :let [h (v/handle-of kb s c)]]
               [[s c] {:why     (when h (v/why kb h {:content? true}))
                       :why-not (v/why-not kb s c {:content? true})
                       :argue   (v/argue kb s c {:content? true})}]))))

(deftest why-and-argue-answer-alike-on-two-seats-loaded-in-different-orders
  (tu/with-terms [bird flies penguin parentOf friendOf relatedTo wren hasSkill gliding moving
                  notedBy trusted vetted Opus Tweety Pingu Tom Bob Pip Ann Noise CxBird
                  cat dog pet wild fish cat_src pet_src dog_src meows Rex CxA CxB CxHide CxW]
    (let [in   (fn [s c & [o]] #(v/assert % s c o))
          mono {:strength :monotonic}
          note (fn [f s & [o]] #(v/assert % (f (list notedBy (list 'sentexHandle (v/assert % s CxBird)) Ann))
                                          CxBird o))
          rows {:defeat
                [[(in (tu/default-rule [(list bird '?x)] (list flies '?x)) CxBird)
                  (in (list bird Opus) CxBird)
                  (in (list 'not (list flies Opus)) CxBird {:strength :monotonic})]
                 [[(list flies Opus) CxBird] [(list 'not (list flies Opus)) CxBird]]
                 #(= :false (get-in % [[(list flies Opus) CxBird] :argue :verdict]))]
                :except
                [[(in (tu/except-rule (list penguin '?x) [(list bird '?x)] (list flies '?x)) CxBird)
                  (in (list bird Tweety) CxBird) (in (list bird Pingu) CxBird)
                  (in (list penguin Pingu) CxBird)]
                 [[(list flies Tweety) CxBird] [(list flies Pingu) CxBird]]
                 #(= :excepted (get-in % [[(list flies Pingu) CxBird] :why-not :reason]))]
                :transitive-in-arg
                [[(in (list wren Pip) 'CxUniverse) (in (list hasSkill Pip gliding) 'CxUniverse)
                  (in (list 'genl gliding moving) 'CxUniverse)
                  (in (list 'transitiveInArg hasSkill 2 'genl) 'CxUniverse)]
                 [[(list hasSkill Pip moving) 'CxUniverse]]
                 #(= 3 (count (get-in % [[(list hasSkill Pip moving) 'CxUniverse]
                                         :argue :for-derivation 0 :supports 0])))]
                :two-justifications
                [[(in (tu/fwd [(list parentOf '?x '?y)] (list relatedTo '?x '?y)) CxBird)
                  (in (tu/fwd [(list friendOf '?x '?y)] (list relatedTo '?x '?y)) CxBird)
                  (in (list parentOf Tom Bob) CxBird) (in (list friendOf Tom Bob) CxBird)]
                 [[(list relatedTo Tom Bob) CxBird]]
                 #(let [w (get-in % [[(list relatedTo Tom Bob) CxBird] :why])]
                    (= 2 (count (:support (get (:nodes w) (:root w))))))]
                :withdrawn
                [[(note identity (list bird Tom)) (note identity (list wren Bob))
                  (in (tu/fwd [(list notedBy '?s '?p) (list trusted '?p)] (list vetted '?p)) CxBird)
                  (in (list trusted Ann) CxBird)
                  (note #(list 'not %) (list bird Tom) {:strength :monotonic})
                  (note #(list 'not %) (list wren Bob) {:strength :monotonic})]
                 [[(list vetted Ann) CxBird]]
                 #(= 2 (count (get-in % [[(list vetted Ann) CxBird] :why-not :withdrawn-by])))]
                :withdrawn-by-conflicts
                [(-> [(in (list 'disjoint dog cat) 'CxUniverse) (in (list 'disjoint wild pet) 'CxUniverse)
                      (in (list dog_src Rex) CxB mono)
                      (in (tu/fwd [(list cat '?x) (list pet '?x)] (list meows '?x)) CxW mono)]
                     (into (mapcat (fn [[s t c]] [(in (list 'set/forwardRule (list 'implies (list s '?x) (list t '?x))) c mono)
                                                  (in (list t Rex) c)])
                                   [[cat_src cat CxA] [pet_src pet CxA] [dog_src dog CxB] [dog_src wild CxB]]))
                     (into (for [s [cat_src pet_src]]
                             #(v/assert % (list 'except (list 'sentexHandle (v/assert % (list s Rex) CxA mono))) CxHide mono)))
                     (into (for [t [cat dog pet wild]] (in (list 'genl t 'thing) 'CxUniverse)))
                     (into (for [[c up] [[CxA 'CxUniverse] [CxB 'CxUniverse] [CxHide 'CxUniverse]
                                         [CxW CxA] [CxW CxB] [CxW CxHide]]]
                             (in (list 'genlCx c up) 'CxUniverse))))
                 [[(list meows Rex) CxW]]
                 #(= 2 (count (get-in % [[(list meows Rex) CxW] :why-not :withdrawn-by])))]
                :two-conflicts-against-one-member
                [(-> [(in (list 'disjoint dog cat) 'CxUniverse) (in (list 'disjoint fish cat) 'CxUniverse)
                      (in (list dog_src Rex) CxB mono)
                      (in (tu/fwd [(list cat '?x)] (list meows '?x)) CxW mono)
                      #(v/assert % (list 'except (list 'sentexHandle (v/assert % (list cat_src Rex) CxA mono))) CxHide mono)]
                     (into (mapcat (fn [[s t c]] [(in (list 'set/forwardRule (list 'implies (list s '?x) (list t '?x))) c mono)
                                                  (in (list t Rex) c)])
                                   [[cat_src cat CxA] [dog_src dog CxB] [dog_src fish CxB]]))
                     (into (for [t [cat dog fish]] (in (list 'genl t 'thing) 'CxUniverse)))
                     (into (for [[c up] [[CxA 'CxUniverse] [CxB 'CxUniverse] [CxHide 'CxUniverse]
                                         [CxW CxA] [CxW CxB] [CxW CxHide]]]
                             (in (list 'genlCx c up) 'CxUniverse))))
                 [[(list meows Rex) CxW]]
                 #(= 2 (count (get-in % [[(list meows Rex) CxW] :why-not :withdrawn-by])))]}]
      (doseq [[row [writes goals shaped?]] rows]
        (let [a (seat-explanations writes goals (in (list bird Noise) CxBird))
              b (seat-explanations (reverse writes) goals (in (list wren Noise) 'CxUniverse))]
          (is (and (shaped? a) (= a b)) (str row)))))))

(tu/deftest-kb why-not-s-content-form-orders-support-by-the-missing-antecedents
  (tu/with-terms [seenA derivedQ Ann Bob CxMiss]
    (let [r     (v/assert-rule kb [(list seenA '?x)] (list derivedQ '?x) CxMiss {:direction :forward})
          [a b] (map #(v/assert kb (list seenA %) CxMiss) [Ann Bob])
          reply (fn [ms] {:support (mapv (fn [m] {:informant r :verdict nil :missing [m]}) ms)})]
      (is (= (#'v/content-form kb (reply [a b])) (#'v/content-form kb (reply [b a])))))))
