;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.describe-test
  "`describe` over the shipped schema and the test-world's cast: what can I ask about
  this term?

  The question a reader arriving at a term actually has is answered by a dozen separate
  reads — `genls`, `props`, `inverse-of`, the argument declarations, the extent counts —
  and the risk in assembling them is not that one of them is wrong but that the
  *assembly* is: a predicate described as a type, a declaration reported from a context
  the reader cannot see, a truncated list shown without its size.  So the tests here are about
  the assembly.

  The one that matters most is the **scoping**: an `arg` declaration binds a predicate's
  arguments only for a reader whose context sees the declaration, so `describe` at
  `CxUniverse` and at `CxWell` are two different answers about one predicate and both are
  right.  A `describe` that read the whole KB would answer the second everywhere, and
  every context-scoped vocabulary would look global."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :once (tu/loaded (fn [kb] (-> kb tu/load-starter! world/load-into))))
(use-fixtures :each (tu/neutral))

(def ^:private N 'CxNaturalWorld)
(def ^:private W 'CxWell)

;; ---- one shape per role -------------------------------------------------

(tu/deftest-kb a-predicate-is-described-by-what-binds-its-arguments
  (let [d (v/describe kb 'parentOf W)]
    (testing "it is a predicate, and the KB says how long a parentOf sentence is"
      (is (= :predicate (:role d)))
      (is (= [2 'parentOf] ((juxt :arity :arity-via) d))))
    (testing "both argument positions are declared, and each declaration says where"
      (is (= '[(arg parentOf 1 causal) (arg parentOf 2 causal)]
             (mapv :sentence (:arg-declarations d))))
      (is (every? #(= :arg (:kind %)) (:arg-declarations d)))
      (is (every? #(symbol? (:context %)) (:arg-declarations d))))
    (testing "the inverse the KB declares"
      (is (= 'childOf (:inverse d))))
    (testing "the four grants are answered, and none of them is given here"
      (is (false? (:abducible? d)))
      (is (false? (:modal? d)))
      (is (false? (:closed-extent? d)))
      (is (false? (:decontextualized? d))))
    (testing "and the KB's own comment on it"
      (is (seq (:comment d)))
      (is (every? string? (:comment d))))))

(tu/deftest-kb a-predicates-algebraic-properties-are-the-ones-it-carries
  (testing "an ancestor relation is transitive and says so"
    (is (contains? (:props (v/describe kb 'ancestorOf W)) :transitive)))
  (testing "a sibling relation is symmetric"
    (is (contains? (:props (v/describe kb 'siblingOf W)) :symmetric)))
  (testing "a parent relation is neither"
    (is (empty? (:props (v/describe kb 'parentOf W))))))

(tu/deftest-kb a-relation-that-is-a-genl-node-is-described-by-its-stored-arity
  ;; A `genl` edge between two relations makes each a node of the `genl` hierarchy.  The
  ;; stored arity decides the role, and the snake_case temporaries, bound under `:naming
  ;; :off` since `:strict` refuses a snake_case relation's length, show the spelling
  ;; decides nothing.
  (doseq [r '[orthogonal siblingDisjointException performedBy doneBy]]
    (is (= [:predicate 2] ((juxt :role :arity) (v/describe kb r))) (str r)))
  (is (contains? (:props (v/describe kb 'orthogonal)) :symmetric))
  (tu/with-terms [near_rel close_rel unary_kind]
    (v/assert kb (list 'symmetric near_rel) 'CxUniverse {:strength :monotonic})
    (v/assert (assoc kb :naming :off) (list 'binary_predicate close_rel) 'CxUniverse)
    (v/assert kb (list 'genl near_rel close_rel) 'CxUniverse)
    (v/assert kb (list 'unary_predicate unary_kind) 'CxUniverse)
    (v/assert kb (list 'genl unary_kind 'thing) 'CxUniverse)
    (let [d (v/describe kb near_rel W)]
      (is (= [:predicate 2] ((juxt :role :arity) d)))
      (is (= #{:symmetric} (:props d))))
    (is (= :type (:role (v/describe kb unary_kind W))) "a unary node is a type"))
  (tu/with-terms [relP relQ Xa Xb Xc]
    (v/assert kb (list 'arity relQ 2) 'CxUniverse)
    (v/assert kb (list 'genl relP relQ) 'CxUniverse)
    (v/assert kb (list relP Xa Xb Xc) 'CxUniverse)
    (is (= [:predicate 2 relQ] ((juxt :role :arity :arity-via) (v/describe kb relP W)))
        "a relation bound to no length of its own is described with the length it inherits")))

(tu/deftest-kb a-type-is-described-by-what-it-is-under-and-what-it-rules-out
  (let [d (v/describe kb 'dog W)]
    (testing "the taxonomy overrides the spelling: `dog` is a unary predicate and a type,
             and a reader asking about it means the type"
      (is (= :type (:role d))))
    (testing "its supertypes, up the genl chain, reflexively minus itself"
      (is (contains? (set (:terms (:genls d))) 'animal))
      (is (not (contains? (set (:terms (:genls d))) 'dog))))
    (testing "what it is disjoint from, read past the default page"
      (is (contains? (set (:terms (:disjoint (v/describe kb 'dog W {:limit 500})))) 'cat)))
    (testing "and the maximally-general reading of the same separation"
      (is (contains? (set (:terms (:disjoint-maximal d))) 'cat)))
    (testing "and how many instances are stored"
      (is (pos? (:instance-count d))))))

(tu/deftest-kb a-subsumption-is-answered-twice-as-the-closure-and-as-the-edge
  ;; `:genls` / `:specs` are the closures a membership check is against; `:genls-direct` /
  ;; `:specs-direct` are its single `genl` steps, stated or installed by a cover declaration.  The closure restates one
  ;; fact as many — `thing` reaches 110,128 subtypes on the OpenCyc import — and it is
  ;; reflexive where the edge reading is not.
  (let [d (v/describe tu/*kb* 'dog '?ctx)]
    (testing "the edge is what was declared"
      (is (= #{'mammal} (set (:terms (:genls-direct d)))))
      (is (true? (:exact? (:genls-direct d)))))
    (testing "the closure reaches past it, and holds the term itself"
      (is (contains? (set (:terms (:genls d))) 'animal) "reached, not declared")
      (is (not (contains? (set (:terms (:genls-direct d))) 'animal)))
      (is (not (contains? (set (:terms (:genls-direct d))) 'dog))
          "and the edge reading is not reflexive, where the closure is"))
    (testing "a leaf has no subtype edges at all, rather than a truncated list of none"
      (is (empty? (:terms (:specs-direct d))))
      (is (zero? (:total (:specs-direct d)))))))

(tu/deftest-kb a-separation-is-answered-twice-as-the-closure-and-as-what-was-declared
  ;; Two readings of one separation, because they answer different questions.  `:disjoint`
  ;; is every type the separation reaches, which is what a membership check is against;
  ;; `:disjoint-maximal` is the types it was declared between, which is what a reader
  ;; asking "what is this not" can hold in their head.  One collection in the OpenCyc
  ;; import is disjoint from 79,638 types and separated from 43 of them.
  (tu/with-terms [left_type right_type]
    (v/assert kb (list 'genl left_type 'thing) 'CxUniverse {:chain? false})
    (v/assert kb (list 'genl right_type 'thing) 'CxUniverse {:chain? false})
    (v/assert-many kb (for [i (range 400)]
                        (list 'genl (symbol (str (name right_type) "_kid" i)) right_type))
                   'CxUniverse {:chain? false})
    (v/assert kb (list 'disjoint left_type right_type) 'CxUniverse {:chain? false})
    (let [d (v/describe kb left_type 'CxUniverse)]
      (testing "the closure reaches the partner's 400 subtypes"
        (is (= 401 (:total (:disjoint d))))
        (is (true? (:exact? (:disjoint d)))))
      (testing "the maximal reading is the one type it was declared against"
        (is (= [right_type] (:terms (:disjoint-maximal d))))
        (is (= 1 (:total (:disjoint-maximal d))))
        (is (true? (:exact? (:disjoint-maximal d)))))
      (testing "and the maximal set is a subset of the closure, never a name beside it"
        (is (every? (set (:terms (:disjoint d))) (:terms (:disjoint-maximal d))))))
    (testing "past the sort budget the closure is bounded on a sum and says so, and the
             maximal reading — which walks no closure — is unaffected"
      ;; 43 partners spanning 290,000 subtypes took 1.5 s of union to produce a list
      ;; nobody can read: past `describe-sortable` the union is built no further, and the
      ;; sum of the closure sizes (free, every closure being a cached set) is the bound
      (with-redefs-fn {(ns-resolve 'vaelii.core 'describe-sortable) 100}
        #(let [d (v/describe kb left_type 'CxUniverse)]
           (is (= 50 (count (:terms (:disjoint d)))) "capped")
           (is (false? (:exact? (:disjoint d)))
               "and the total is the bound it is — a sum of closures over-counts an overlap")
           (is (= [right_type] (:terms (:disjoint-maximal d))))
           (is (true? (:exact? (:disjoint-maximal d)))))))
    (testing "past the sort budget a union that fits the limit is still exact and sorted"
      (tu/with-terms [small_type other_type]
        (v/assert kb (list 'genl small_type 'thing) 'CxUniverse {:chain? false})
        (v/assert kb (list 'genl other_type 'thing) 'CxUniverse {:chain? false})
        (v/assert kb (list 'disjoint small_type other_type) 'CxUniverse {:chain? false})
        (with-redefs-fn {(ns-resolve 'vaelii.core 'describe-sortable) 0}
          #(is (= {:terms [other_type] :total 1 :exact? true :sorted? true}
                  (:disjoint (v/describe kb small_type 'CxUniverse))))))))
  (testing "overlapping partners whose closure sizes sum past the sort budget, and whose
             union fits it, are sorted and counted exactly"
    (tu/with-terms [near_type outer_type inner_type]
      (v/assert kb (list 'genl near_type 'thing) 'CxUniverse {:chain? false})
      (v/assert kb (list 'genl outer_type 'thing) 'CxUniverse {:chain? false})
      (v/assert kb (list 'genl inner_type outer_type) 'CxUniverse {:chain? false})
      (v/assert-many kb (for [i (range 60)]
                          (list 'genl (symbol (str (name inner_type) "_kid" i)) inner_type))
                     'CxUniverse {:chain? false})
      (v/assert kb (list 'disjoint near_type outer_type) 'CxUniverse {:chain? false})
      (v/assert kb (list 'disjoint near_type inner_type) 'CxUniverse {:chain? false})
      (with-redefs-fn {(ns-resolve 'vaelii.core 'describe-sortable) 100}
        #(let [d (v/describe kb near_type 'CxUniverse)]
           (is (= 2 (:total (:disjoint-maximal d))))
           (is (= [62 true true] ((juxt :total :exact? :sorted?) (:disjoint d)))))))))

(tu/deftest-kb a-type-names-the-predicates-whose-declarations-admit-it
  ;; The question behind it: I have a `dog`, what may I say about one?  A predicate
  ;; admits it when some `arg` / `genlArg` declaration names a type `dog` is under, so
  ;; the answer is read off the declarations' own argument root rather than by trying
  ;; every predicate in the KB against it.
  ;; `dog` sits under five types between them declaring well over fifty positions, so the
  ;; default limit truncates the list: the limit is raised here to ask about the whole answer
  ;; rather than about the first page of it.
  (let [line (:predicates-for-type (v/describe kb 'dog W {:limit 500}))
        rows (:rows line)
        of   (fn [p] (filter #(= p (:predicate %)) rows))
        up   (set (:terms (:genls (v/describe kb 'dog W))))]
    (testing "a relation declared over animals admits a dog"
      (is (seq (of 'parentOf)))
      (is (= #{1 2} (set (map :position (of 'parentOf))))))
    (testing "each row says which declared type let it in, and that type is one of dog's"
      (is (every? #(contains? up (:type %)) (of 'parentOf))))
    (testing "the list is truncated, with its size beside it"
      (is (contains? line :total))
      (is (true? (:exact? line))))
    (testing "and the default limit truncates the list on this term"
      (let [d (:predicates-for-type (v/describe kb 'dog W))]
        (is (= 50 (count (:rows d))))
        (is (> (:total d) 50))))))

;; ---- the definitional block ---------------------------------------------

(defn- block [d] (into {} (map (juxt :part :value)) (:definitional-block d)))

(defn- separations [b] (into {} (map (juxt :term :separation)) (:rows (:siblings b))))

(tu/deftest-kb a-types-block-names-each-part-and-marks-the-missing-ones
  (tu/with-terms [kin_root kin_a kin_b kin_c kin_d KinBoth]
    (doseq [s [(list 'genl kin_root 'thing) (list 'unary_predicate kin_a)
               (list 'genl kin_a kin_root) (list 'genl kin_b kin_root)
               (list 'genl kin_c kin_root) (list 'genl kin_d kin_root)
               (list 'disjoint kin_a kin_b) (list kin_a KinBoth) (list kin_d KinBoth)
               (list 'comment kin_a "A kind made up for this test.")
               (list 'positiveExampleComment kin_a "one made up")]]
      (v/assert kb s 'CxUniverse))
    (let [d (v/describe kb kin_a 'CxUniverse)
          b (block d)]
      (is (= [:comment :positive-examples :negative-examples :kind :parents :siblings :links]
             (mapv :part (:definitional-block d)))
          "the annotations, then the kinds, then the rest; an arity class is no part")
      (is (= :missing (:kind b)) "the arity class is not a kind")
      (is (= [kin_root] (:terms (:parents b))))
      (is (= {kin_b :disjoint kin_c :missing kin_d :overlaps} (separations b))
          "a sibling nothing decides is the missing part of the separations")
      (is (= {:term kin_d :separation :overlaps :witness :shared-instance :via KinBoth}
             (first (filter #(= kin_d (:term %)) (:rows (:siblings b)))))
          "an overlap names the shared instance, as the open-sibling pass reads it")
      (is (= ["A kind made up for this test."] (:comment b)))
      (is (= ["one made up"] (:positive-examples b)))
      (is (= :missing (:negative-examples b))))))

(tu/deftest-kb a-shipped-types-block-reads-the-separation-each-sibling-has
  (let [b (block (v/describe kb 'arachnid W))]
    (is (= ['invertebrate] (:terms (:parents b))))
    (is (= :disjoint (get (separations b) 'insect))
        "invertebrate_class is a disjoint_metatype, so the one membership separates them")
    (is (= ["an insect, which has six legs"] (:negative-examples b))))
  (is (= :orthogonal (get (separations (block (v/describe kb 'electronic_device W))) 'machine))))

(tu/deftest-kb a-types-parents-are-its-minimal-direct-genls
  (testing "a stored parent another parent is strictly below is left out"
    (is (= ['temporal] (:terms (:parents (block (v/describe kb 'causal W)))))
        "(genl causal thing) comes from the partition, and temporal is below thing"))
  (tu/with-terms [kin_root kin_a kin_b]
    (doseq [s [(list 'genl kin_root 'thing) (list 'genl kin_a kin_root)
               (list 'genl kin_a 'thing) (list 'genl kin_b kin_root)]]
      (v/assert kb s 'CxUniverse))
    (let [b (block (v/describe kb kin_a 'CxUniverse))]
      (is (= [kin_root] (:terms (:parents b))))
      (is (= [kin_b] (mapv :term (:rows (:siblings b))))
          "the siblings are the children of the minimal parents only"))))

(tu/deftest-kb two-parents-that-subsume-each-other-show-as-one
  (tu/with-terms [kin_a kin_b kin_c CxEdgeA CxEdgeB CxBoth]
    (doseq [s [(list 'genlCx CxEdgeA 'CxUniverse) (list 'genlCx CxEdgeB 'CxUniverse)
               (list 'genlCx CxBoth CxEdgeA) (list 'genlCx CxBoth CxEdgeB)
               (list 'genl kin_a 'thing) (list 'genl kin_b 'thing)
               (list 'genl kin_c kin_a) (list 'genl kin_c kin_b)]]
      (v/assert kb s 'CxUniverse))
    (v/assert kb (list 'genl kin_a kin_b) CxEdgeA)
    (v/assert kb (list 'genl kin_b kin_a) CxEdgeB)
    (is (= [(first (sort-by pr-str [kin_a kin_b]))]
           (:terms (:parents (block (v/describe kb kin_c CxBoth)))))
        "two contexts' opposite edges: neither is strictly below the other, so one stands for both")))

(tu/deftest-kb genls-block-comment-says-what-genl-means-and-its-note-how-the-engine-runs-it
  (let [b (block (v/describe kb 'genl W))]
    (is (not-any? #(re-find #"closure|chain" %) (:comment b))
        "the comment states what genl means and leaves the closure cache to a note"))
  (is (some #(re-find #"caches the genl closure" (str (nth (:sentence %) 2)))
            (v/sentexes-matching kb '(implementationNote genl ?note) 'CxUniverse))
      "an implementationNote records that the engine caches the closure"))

(defn- arg-table
  "The block `b`'s argument constraint table as `[position quoted? rest? [[kind type] …]]`
  columns."
  [b]
  (mapv (fn [{:keys [position quoted? rest? cell]}]
          [position quoted? rest? (mapv (juxt :kind :type) cell)])
        (:arg-constraints b)))

(tu/deftest-kb a-predicates-block-holds-its-arity-declarations-and-properties
  (let [d (v/describe kb 'parentOf W)
        b (block d)]
    (is (= [:comment :arity :kind :parents :arg-constraints :props :links]
           (mapv :part (:definitional-block d)))
        "the comment, then the arity and the kinds, then the rest")
    (is (= {:exact 2 :via 'parentOf} (:arity b)))
    (is (not-any? '#{binary_predicate} (:terms (:kind b))) "the arity says what the class would")
    (is (= '[[1 false false [[:instance causal]]] [2 false false [[:instance causal]]]]
           (arg-table b))
        "both declarations are in the table, and no other one is left for its own line")
    (is (= :missing (:props b)) "parentOf states no algebraic property"))
  (is (= '[(symmetric siblingOf)] (mapv :sentence (:props (block (v/describe kb 'siblingOf W)))))
      "a property row is the sentence that states it"))

(defn- block-sentences
  "The sentences the block `b` shows as sentence rows: its well-formedness declarations,
  its properties and its links."
  [b]
  (into #{} (comp (mapcat #(let [v (get b %)] (when (vector? v) v))) (map :sentence))
        [:arg-declarations :props :links]))

(tu/deftest-kb a-predicates-block-reads-the-kbs-classification-of-its-sentences
  (tu/with-terms [relP relQ kindT]
    (doseq [s [(list 'unary_predicate kindT) (list 'binary_predicate relP)
               (list 'binary_predicate relQ) (list 'arg relP 1 kindT) (list 'arg relP 2 kindT)
               (list 'irreflexive relP) (list 'functionalInArg relP 2)
               (list 'argsGenl relP kindT) (list 'seeAlso relP relQ)
               (list 'interArgEqual relP 2 7 1 kindT)
               (list 'implementationNote relP "a note no block part shows")]]
      (v/assert kb s 'CxUniverse))
    (let [d (v/describe kb relP 'CxUniverse)
          b (block d)]
      (is (= #{(list 'irreflexive relP) (list 'functionalInArg relP 2)}
             (set (map :sentence (:props b))))
          "irreflexive and the per-position functionalInArg are algebraic properties")
      (is (= [[1 false false [[:instance kindT] [:type kindT]]]
              [2 false false [[:instance kindT] [:type kindT]]]]
             (arg-table b))
          "argsGenl is an argument constraint, in the table on every position")
      (is (= [(list 'interArgEqual relP 2 7 1 kindT)] (mapv :sentence (:arg-declarations b)))
          "a wff declaration the table does not hold keeps its sentence")
      (is (= [(list 'seeAlso relP relQ)] (mapv :sentence (:links b))))
      (is (not (contains? (block-sentences b)
                          (list 'implementationNote relP "a note no block part shows")))
          "implementationNote is not definitional")
      (is (= (set (:arg-declarations d))
             (into (set (:arg-declarations b))
                   (filter #(not= 'interArgEqual (first (:sentence %))))
                   (:arg-declarations d)))
          "every declaration describe lists is in the table or on the line"))))

(tu/deftest-kb a-predicates-argument-constraints-are-one-column-per-position
  (tu/with-terms [relP kindT kindU]
    (doseq [s [(list 'unary_predicate kindT) (list 'genl kindT 'thing)
               (list 'unary_predicate kindU) (list 'genl kindU kindT)
               (list 'quinary_predicate relP)
               (list 'arg relP 1 kindT) (list 'arg relP 1 kindU)
               (list 'arg relP 2 'positive_integer)
               (list 'quotedArg relP 4 'closed_expression) (list 'genlArg relP 5 kindT)]]
      (v/assert kb s 'CxUniverse))
    (is (= [[1 false false [[:instance kindU]]]
            [2 false false '[[:instance positive_integer]]]
            [3 false false []]
            [4 true false '[[:quoted closed_expression]]]
            [5 false false [[:type kindT]]]]
           (arg-table (block (v/describe kb relP 'CxUniverse))))
        "a type another one in its cell is strictly below drops, an unconstrained position is an
        empty cell, and a quoted one is its own column")))

(tu/deftest-kb a-predicate-with-no-argument-constraint-has-no-table
  (tu/with-terms [relP]
    (v/assert kb (list 'unary_predicate relP) 'CxUniverse)
    (v/assert kb (list 'arity relP 1) 'CxUniverse)
    (is (not-any? #(= :arg-constraints (:part %))
                  (:definitional-block (v/describe kb relP 'CxUniverse))))))

(tu/deftest-kb a-covering-constraint-fills-the-cells-it-covers
  (tu/with-terms [relP relQ kindT kindU]
    (doseq [s [(list 'unary_predicate kindT) (list 'genl kindT 'thing)
               (list 'unary_predicate kindU) (list 'genl kindU kindT)
               (list 'binary_predicate relP) (list 'args relP kindT)
               (list 'binary_predicate relQ) (list 'args relQ kindT) (list 'arg relQ 2 kindU)]]
      (v/assert kb s 'CxUniverse))
    (is (= [[1 false false [[:instance kindT]]] [2 false false [[:instance kindT]]]]
           (arg-table (block (v/describe kb relP 'CxUniverse))))
        "args alone types every position of a fixed-arity predicate")
    (is (= [[1 false false [[:instance kindT]]] [2 false false [[:instance kindU]]]]
           (arg-table (block (v/describe kb relQ 'CxUniverse))))
        "a narrower arg2 stands for the covering type it is below")))

(tu/deftest-kb an-unbounded-arity-predicates-tail-is-one-last-column
  (tu/with-terms [relP relQ kindT kindU]
    (doseq [s [(list 'unary_predicate kindT) (list 'genl kindT 'thing)
               (list 'unary_predicate kindU) (list 'genl kindU 'thing)
               (list 'unbounded_arity_predicate relP)
               (list 'arg relP 1 kindT) (list 'argAndRest relP 2 kindU)
               (list 'unbounded_arity_predicate relQ) (list 'args relQ kindT)]]
      (v/assert kb s 'CxUniverse))
    (is (= [[1 false false [[:instance kindT]]] [2 false true [[:instance kindU]]]]
           (arg-table (block (v/describe kb relP 'CxUniverse))))
        "argAndRest 2 is an arg2… column after the numbered ones")
    (is (= [[1 false true [[:instance kindT]]]]
           (arg-table (block (v/describe kb relQ 'CxUniverse))))
        "args alone is a single arg1… column")))

(tu/deftest-kb a-super-predicates-constraints-are-in-the-table
  (tu/with-terms [relP relQ kindT]
    (doseq [s [(list 'unary_predicate kindT) (list 'genl kindT 'thing)
               (list 'binary_predicate relP) (list 'arg relP 1 kindT)
               (list 'binary_predicate relQ) (list 'genl relQ relP)]]
      (v/assert kb s 'CxUniverse))
    (is (= [[1 false false [[:instance kindT]]] [2 false false []]]
           (arg-table (block (v/describe kb relQ 'CxUniverse)))))))

(tu/deftest-kb the-blocks-rows-follow-the-kbs-display-order
  (tu/with-terms [relP kindT]
    (doseq [s [(list 'unary_predicate kindT) (list 'binary_predicate relP)
               (list 'arg relP 1 kindT) (list 'arg relP 2 kindT)
               (list 'irreflexive relP) (list 'functionalInArg relP 2)]]
      (v/assert kb s 'CxUniverse))
    (let [props #(mapv :sentence (:props (block (v/describe kb relP 'CxUniverse))))]
      (is (= [(list 'functionalInArg relP 2) (list 'irreflexive relP)] (props))
          "unnamed predicates are shown in content order")
      (let [h (v/assert kb '(predicateDisplayOrder irreflexive functionalInArg) 'CxUniverse)]
        (try
          (is (= [(list 'irreflexive relP) (list 'functionalInArg relP 2)] (props))
              "a named predicate is shown in the order named")
          (finally (v/retract! kb h)))))))

(tu/deftest-kb a-predicates-arity-part-is-the-length-that-binds-it
  (tu/with-terms [relP relQ relR relS relU]
    (doseq [s [(list 'ternary_predicate relP)
               (list 'binary_predicate relQ) (list 'genl relR relQ)
               (list 'variable_arity_predicate relS) (list 'unbounded_arity_predicate relS)
               (list 'arityMin relS 2)
               (list 'unbounded_arity_predicate relU)]]
      (v/assert kb s 'CxUniverse))
    (let [arity #(:arity (block (v/describe kb % 'CxUniverse)))]
      (is (= {:exact 3 :via relP} (arity relP)))
      (is (= {:exact 2 :via relQ} (arity relR)) "a length a super-predicate binds")
      (is (= {:min 2 :via relS} (arity relS))
          "an unbounded predicate's least length, declared as core.txt declares contradicts")
      (is (= {:any? true} (arity relU))
          "an unbounded predicate no least length binds takes any number"))))

(tu/deftest-kb a-predicate-no-length-binds-has-its-arity-part-missing
  (tu/with-terms [relP]
    (v/assert kb (list 'variable_arity_predicate relP) 'CxUniverse)
    (is (= :missing (:arity (block (v/describe kb relP 'CxUniverse)))))))

(tu/deftest-kb an-unlisted-definitional-predicate-is-shown-after-every-listed-one
  (tu/with-terms [relP kindT defRel]
    (doseq [s [(list 'unary_predicate kindT) (list 'binary_predicate relP)
               (list 'arg relP 1 kindT) (list 'arg relP 2 kindT)
               (list 'comment relP "a relation") (list 'transitive relP)
               (list 'irreflexive relP) (list 'seeAlso relP 'genl)
               (list 'binary_predicate defRel) (list 'definitional_predicate defRel)
               (list 'arg defRel 1 'predicate) (list 'arg defRel 2 'thing)
               (list defRel relP kindT)]]
      (v/assert kb s 'CxUniverse))
    (let [parts (:definitional-block (v/describe kb relP 'CxUniverse))
          holds (fn [s] (first (keep-indexed
                                (fn [i {v :value}]
                                  (when (and (sequential? v) (some #{s} (map :sentence v))) i))
                                parts)))
          at    (holds (list defRel relP kindT))]
      (is (some? at) "a definitional predicate no predicateDisplayOrder fact names is shown")
      (is (= (dec (count parts)) at) "after every part a listed predicate is shown in")
      (is (= [(list 'transitive relP) (list 'irreflexive relP)]
             (mapv :sentence (:value (first (filter #(= :props (:part %)) parts)))))
          "and inside a part, an unlisted row follows the listed ones"))))

(tu/deftest-kb a-terms-kind-is-every-unary-predicate-it-holds
  (tu/with-terms [kindT]
    (doseq [s [(list 'unary_predicate kindT) (list 'genl kindT 'thing) (list 'type kindT)
               (list 'closed_extent_predicate kindT) (list 'not_assertible kindT)]]
      (v/assert kb s 'CxUniverse))
    (let [kinds (set (:terms (:kind (block (v/describe kb kindT 'CxUniverse)))))]
      (is (contains? kinds 'type) "an order is a kind")
      (is (contains? kinds 'closed_extent_predicate) "so is a grant")
      (is (contains? kinds 'not_assertible) "and a refusal mark")
      (is (not (contains? kinds 'unary_predicate)) "and an arity class is not")))
  (let [kinds (set (:terms (:kind (block (v/describe kb 'made W)))))]
    (is (contains? kinds 'origin_type) "a membership the KB does not classify definitional")
    (is (contains? kinds 'time_invariant_relation))
    (is (not-any? '#{unary_predicate binary_predicate} kinds))))

(tu/deftest-kb a-kind-another-kind-is-strictly-below-is-left-out
  (tu/with-terms [kindT]
    (doseq [s [(list 'unary_predicate kindT) (list 'genl kindT 'thing)
               (list 'eternal_predicate kindT) (list 'time_invariant_relation kindT)]]
      (v/assert kb s 'CxUniverse))
    (is (= ['eternal_predicate] (:terms (:kind (block (v/describe kb kindT 'CxUniverse)))))
        "eternal_predicate is below time_invariant_relation"))
  (let [kinds (set (:terms (:kind (block (v/describe kb 'algebraic_predicate_property W)))))]
    (is (contains? kinds 'eternal_predicate))
    (is (not-any? '#{time_invariant_relation unary_predicate} kinds))))

(tu/deftest-kb a-relation-property-another-one-is-strictly-below-is-left-out
  (tu/with-terms [relP kindT]
    (doseq [s [(list 'unary_predicate kindT) (list 'binary_predicate relP)
               (list 'arg relP 1 kindT) (list 'arg relP 2 kindT)
               (list 'equivalence_relation relP) (list 'functionalInArg relP 2)]]
      (v/assert kb s 'CxUniverse))
    (let [props (set (map :sentence (:props (block (v/describe kb relP 'CxUniverse)))))]
      (is (contains? props (list 'equivalence_relation relP)))
      (is (not-any? props (for [p '[reflexive symmetric transitive]] (list p relP)))
          "an equivalence relation is reflexive, symmetric and transitive by genl")
      (is (contains? props (list 'functionalInArg relP 2))
          "a property with more arguments than the predicate is not pruned"))))

(tu/deftest-kb a-cluster-link-is-in-the-block-of-each-term-it-names
  (tu/with-terms [kindA kindB kindC]
    (doseq [t [kindA kindB kindC]]
      (v/assert kb (list 'unary_predicate t) 'CxUniverse)
      (v/assert kb (list 'genl t 'thing) 'CxUniverse))
    (v/assert kb (list 'termsRelated kindA kindB kindC) 'CxUniverse)
    (doseq [t [kindA kindB kindC]]
      (is (= [(list 'termsRelated kindA kindB kindC)]
             (mapv :sentence (:links (block (v/describe kb t 'CxUniverse)))))
          (str t)))))

(tu/deftest-kb an-individual-is-described-by-its-types-and-where-it-is-mentioned
  (let [d (v/describe kb 'Muffet N)]
    (testing "an individual, by the spelling and by the taxonomy alike"
      (is (= :individual (:role d))))
    (testing "the types asserted of it — not their supertypes"
      (is (contains? (set (:types d)) 'dog))
      (is (not (contains? (set (:types d)) 'animal))))
    (testing "the predicates it appears under, with a count each"
      (let [rows (:rows (:predicates d))
            n    (into {} (map (juxt :predicate :count)) rows)]
        (is (= 1 (n 'dog)))
        (is (pos? (n 'eats)))
        (is (every? pos? (vals n)))))
    (testing "the row list is exact when the scan did not bite"
      (is (true? (:exact? (:predicates d)))))))

(tu/deftest-kb a-context-is-described-by-what-it-sees-and-what-sees-it
  (let [d (v/describe kb 'CxKinship W)]
    (is (= :context (:role d)))
    (testing "its ancestor set holds the contexts it reads, reflexively"
      (is (contains? (set (:terms (:up d))) 'CxKinship))
      (is (contains? (set (:terms (:up d))) 'CxUniverse)))
    (testing "its descendant set holds the contexts that read it"
      (is (contains? (set (:terms (:down d))) 'CxWell)))
    (testing "and how many sentexes hold in it"
      (is (pos? (:sentex-count d))))
    (testing "a context nobody computed carries no computed-spec-of key at all"
      (is (not (contains? d :computed-spec-of))))))

;; ---- the scoping, which is the whole point ------------------------------

(tu/deftest-kb an-argument-declaration-is-reported-only-where-the-reader-can-see-it
  ;; `(arg parentOf 1 organism)` is stated in CxUniverse, which every context sees.  A
  ;; `describe` that read the whole KB would report a declaration to a reader for whom
  ;; it does not bind, and a declaration reported looks like one that applies.
  (testing "a reader below the declaration sees it"
    (is (= 2 (count (:arg-declarations (v/describe kb 'parentOf W))))))
  (testing "a reader with no genlCx edge sees it through CxUniverse"
    (tu/with-terms [CxOutside]
      (is (= 2 (count (:arg-declarations (v/describe kb 'parentOf CxOutside)))))))
  (testing "and the unscoped read sees every context's"
    (is (= 2 (count (:arg-declarations (v/describe kb 'parentOf '?ctx))))))
  (testing "a declaration in a sibling context is reported only to its readers"
    (tu/with-terms [CxSide CxOutside]
      (v/assert kb (list 'arg 'parentOf 1 'animal) CxSide)
      (is (= 3 (count (:arg-declarations (v/describe kb 'parentOf CxSide)))))
      (is (= 2 (count (:arg-declarations (v/describe kb 'parentOf CxOutside))))))))

(tu/deftest-kb a-grant-is-a-policy-of-the-context-that-gives-it
  ;; `modal_predicate` and `abducible_predicate` are grants read up the genlCx ancestor set, so a
  ;; predicate granted in one theory is not granted in a sibling.  Net-neutral: the
  ;; grant is asserted on a temporary in a temporary context and retracted with it.
  (tu/with-terms [thinks CxGrantA CxGrantB]
    (v/assert kb (list 'genlCx CxGrantA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxGrantB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'binary_predicate thinks) 'CxUniverse)
    (v/assert kb (list 'modal_predicate thinks) CxGrantA)
    (is (true?  (:modal? (v/describe kb thinks CxGrantA))))
    (is (false? (:modal? (v/describe kb thinks CxGrantB))))))

;; ---- the envelopes ------------------------------------------------------

(tu/deftest-kb every-list-is-truncated-and-says-how-big-the-answer-is
  (let [d (v/describe kb 'thing W {:limit 3})]
    (testing "the list stops at the limit, and the total is the whole answer"
      (is (<= (count (:terms (:specs d))) 3))
      (is (> (:total (:specs d)) 3)))
    (testing "a truncated answer still says whether the count is exact and sorted"
      (is (true? (:exact? (:specs d))))
      (is (true? (:sorted? (:specs d)))))))

(tu/deftest-kb an-option-nothing-reads-is-refused-rather-than-dropped
  ;; The silent failure a key set exists to stop: `{:limt 3}` would answer the default
  ;; fifty under a map that looks exactly like the one asked for.
  (is (= :unknown-option
         (try (v/describe kb 'dog W {:limt 3})
              (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
  (is (= v/describe-opt-keys #{:limit})))

(tu/deftest-kb a-limit-that-is-not-a-positive-integer-is-refused-rather-than-cast
  ;; `{:limit "5"}` reached `take` and threw a bare ClassCastException — a 500 over the
  ;; daemon, where `find-terms`' `:limit` is a typed refusal — and `{:limit 0}` answered
  ;; every list empty under a `:total` that read like an answer.
  (doseq [bad ["5" 0 -3 1.5]]
    (let [e (is (thrown? clojure.lang.ExceptionInfo (v/describe kb 'dog W {:limit bad}))
                (pr-str bad))]
      (is (= :unknown-option (:type (ex-data e))) (pr-str bad))
      (is (= :bad-value (:mismatch (ex-data e))))))
  (testing "and nil is the default limit"
    (is (= (:genls (v/describe kb 'dog W)) (:genls (v/describe kb 'dog W {:limit nil}))))))

(tu/deftest-kb a-spelling-that-declares-no-role-answers-the-common-shape-and-no-more
  (let [d (v/describe kb '?x W)]
    (is (= :variable (:role d)))
    (is (contains? d :genls))
    (is (not (contains? d :arity)))
    (is (not (contains? d :types)))))

;; ---- what the browser renders is what this answers ----------------------

(tu/deftest-kb the-default-limit-is-the-one-the-term-page-lists-with
  ;; The term page reads `describe`'s truncated lists straight through and applies no cap of its
  ;; own, so the two agreeing is not a coincidence to be preserved by hand: the page
  ;; shows exactly what this answered, `:total` and all.
  (is (= 50 v/default-describe-limit))
  (is (= 50 (count (:terms (:specs (v/describe kb 'thing W)))))))
