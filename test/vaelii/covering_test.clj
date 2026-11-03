;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.covering-test
  "covering and partition — named parts that exhaust a whole.

  The declaration half: what a cover states about the taxonomy, what a partition
  separates, and what each is refused for.  The coverage inference itself — n−1 explicit
  negations proving the nth part — is in `covering_inference_test`."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- outcome
  "`:ok`, or the `:type` of the refusal, so a case is compared as a value rather than as
  the presence or absence of a throw."
  [kb sentence context]
  (try (v/assert kb sentence context) :ok
       (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

;; ---- what a cover states -------------------------------------------------

(tu/deftest-kb a-cover-states-the-specialization-it-rests-on
  (tu/with-terms [animal dog cat Rex]
    (v/assert kb (list 'covering animal dog cat) 'CxUniverse)
    (testing "each part is a subtype of the whole, with no genl edge written by hand"
      (is (v/ask? kb (list 'genl dog animal) 'CxUniverse))
      (is (v/ask? kb (list 'genl cat animal) 'CxUniverse)))
    (testing "so a part's member is the whole's member"
      (v/assert kb (list dog Rex) 'CxUniverse)
      (is (v/ask? kb (list animal Rex) 'CxUniverse)))))

(tu/deftest-kb a-fact-of-another-functor-shaped-as-a-cover-pairs-with-no-disjoint
  (tu/with-terms [liesAmong alpha beta gamma]
    (v/assert kb (list liesAmong alpha beta gamma) 'CxUniverse)
    (v/assert kb (list 'disjoint alpha beta) 'CxUniverse)
    (is (empty? (filter #(= :cover (:kind %)) (v/contradictions kb))))))

(tu/deftest-kb a-cover-asserted-before-its-parts-answers-what-one-asserted-after-them-does
  (tu/with-terms [animal dog cat Rex]
    (v/assert kb (list dog Rex) 'CxUniverse)
    (v/assert kb (list 'covering animal dog cat) 'CxUniverse)
    (is (v/ask? kb (list animal Rex) 'CxUniverse)
        "the membership stored first still reaches the whole")))

(tu/deftest-kb retracting-a-cover-drops-the-edges-it-installed
  (tu/with-terms [animal dog cat]
    (let [h (v/assert kb (list 'covering animal dog cat) 'CxUniverse)]
      (is (v/ask? kb (list 'genl dog animal) 'CxUniverse))
      (v/retract! kb h)
      (testing "the specialization goes with the declaration that stated it"
        (is (not (v/ask? kb (list 'genl dog animal) 'CxUniverse)))
        (is (not (v/ask? kb (list 'genl cat animal) 'CxUniverse)))))))

(tu/deftest-kb a-hand-written-edge-survives-the-cover-that-restated-it
  (tu/with-terms [animal dog cat]
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (let [h (v/assert kb (list 'covering animal dog cat) 'CxUniverse)]
      (v/retract! kb h)
      (testing "two supporters, and dropping one leaves the other"
        (is (v/ask? kb (list 'genl dog animal) 'CxUniverse))
        (is (not (v/ask? kb (list 'genl cat animal) 'CxUniverse)))))))

;; ---- what a partition separates, and what a bare cover does not ----------

(tu/deftest-kb a-recovered-kb-holds-the-declaration-and-the-edges-a-partition-stated
  (tu/with-terms [animal dog cat Rex]
    (v/assert kb (list 'partition animal dog cat) 'CxUniverse)
    (v/assert kb (list dog Rex) 'CxUniverse)
    (v/recover kb)
    (is (v/ask? kb (list animal Rex) 'CxUniverse) "the part edge was replayed")
    (is (v/disjoint? kb dog cat) "and so was the declaration that separates the parts")))

(tu/deftest-kb a-bare-cover-leaves-its-parts-free-to-overlap
  (tu/with-terms [animal dog cat Rex]
    (v/assert kb (list 'covering animal dog cat) 'CxUniverse)
    (is (not (v/disjoint? kb dog cat)) "covering claims no separation")
    (v/assert kb (list dog Rex) 'CxUniverse)
    (is (= :ok (outcome kb (list cat Rex) 'CxUniverse))
        "so a term may hold two parts of one cover")))

(tu/deftest-kb a-partition-separates-its-parts-without-a-disjoint-sentex
  (tu/with-terms [animal dog cat Rex]
    (v/assert kb (list 'partition animal dog cat) 'CxUniverse)
    (testing "every pair of parts is disjoint"
      (is (v/disjoint? kb dog cat))
      (is (v/disjoint? kb cat dog)))
    (testing "and no (disjoint …) sentex was written to say so"
      (is (empty? (v/find-sentexes kb {:pattern (list 'disjoint dog cat)}))))
    (testing "the second membership is stored, and the pair is a dilemma where it is written"
      (v/assert kb (list dog Rex) 'CxUniverse)
      (is (tu/stored-in-clash? kb (list cat Rex) 'CxUniverse)))))

(tu/deftest-kb a-partition-separates-the-subtypes-of-its-parts
  (tu/with-terms [animal dog cat poodle Rex]
    (v/assert kb (list 'partition animal dog cat) 'CxUniverse)
    (v/assert kb (list 'genl poodle dog) 'CxUniverse)
    (is (v/disjoint? kb poodle cat)
        "disjointness is inherited downward through genl, as every other arm's is")
    (is (not (v/disjoint? kb poodle dog))
        "and a part is not separated from its own subtype")))

(tu/deftest-kb dropping-a-partition-releases-every-pair-at-once
  (tu/with-terms [animal dog cat bird]
    (let [h (v/assert kb (list 'partition animal dog cat bird) 'CxUniverse)]
      (is (v/disjoint? kb dog cat))
      (is (v/disjoint? kb cat bird))
      (v/retract! kb h)
      (is (not (v/disjoint? kb dog cat)))
      (is (not (v/disjoint? kb cat bird))))))

(tu/deftest-kb an-exception-exempts-one-pair-of-parts
  ;; A partition's separation half is a mark, so a `siblingDisjointException` over two
  ;; parts exempts that pair; the coverage half stands.
  (tu/with-terms [perception reading touch Braille]
    (v/assert kb (list 'partition perception reading touch) 'CxUniverse)
    (is (v/disjoint? kb reading touch))
    (v/assert kb (list 'siblingDisjointException reading touch) 'CxUniverse)
    (is (not (v/disjoint? kb reading touch)))
    (v/assert kb (list reading Braille) 'CxUniverse)
    (is (= :ok (outcome kb (list touch Braille) 'CxUniverse)))
    (is (empty? (filter #(= :orthogonal (:kind %)) (v/conflicts kb))))))

;; ---- what the declaration is refused for --------------------------------

(tu/deftest-kb a-cover-naming-fewer-than-two-parts-states-nothing
  (tu/with-terms [animal dog]
    (is (= :not-well-formed (outcome kb (list 'covering animal dog) 'CxUniverse)))))

(tu/deftest-kb a-cover-is-refused-for-a-shape-no-edge-could-be-installed-for
  (tu/with-terms [animal dog cat plant Rex]
    (testing "a part named twice"
      (is (= :not-well-formed (outcome kb (list 'covering animal dog dog) 'CxUniverse))))
    (testing "an individual in any position"
      (is (= :not-well-formed (outcome kb (list 'covering animal dog Rex) 'CxUniverse)))
      (is (= :not-well-formed (outcome kb (list 'covering Rex dog cat) 'CxUniverse))))
    (testing "the whole named as one of its own parts"
      (is (= :not-well-formed (outcome kb (list 'covering animal animal dog) 'CxUniverse))))
    (testing "a part the closure already places above the whole"
      (v/assert kb (list 'genl animal plant) 'CxUniverse)
      (is (= :not-well-formed (outcome kb (list 'covering animal plant dog) 'CxUniverse))))))

(tu/deftest-kb a-part-only-a-sibling-context-places-above-the-whole-is-stored
  ;; The cover is refused where the bare `genl` is: in the context that sees the edge
  ;; above the whole, and not in its sibling.
  (tu/with-terms [animal dog plant]
    (let [left (tu/tmp-ctx) right (tu/tmp-ctx)]
      (v/assert kb (list 'genlCx left 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx right 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genl animal plant) right)
      (is (= [:not-well-formed :not-well-formed]
             (mapv #(outcome kb % right) [(list 'genl plant animal) (list 'covering animal plant dog)])))
      (is (= :ok (outcome kb (list 'covering animal plant dog) left)))
      (is (= [true false] (mapv #(v/genl? kb plant animal %) [left right]))))))

(tu/deftest-kb a-part-disjoint-from-the-whole-is-stored
  ;; decision 8 of docs/reference.md: the refusal would read the stored `disjoint`, so
  ;; the cover is stored whichever of the two arrived first
  (tu/with-terms [animal dog plant]
    (v/assert kb (list 'disjoint animal plant) 'CxUniverse)
    (is (= :ok (outcome kb (list 'covering animal plant dog) 'CxUniverse)))))

;; ---- the part list is one key, whatever order it is written in ----------

(tu/deftest-kb a-part-list-written-in-another-order-is-one-declaration
  (tu/with-terms [animal dog cat]
    (let [tx (reasoning/taxonomy kb)]
      (v/assert kb (list 'covering animal dog cat) 'CxUniverse)
      (v/assert kb (list 'covering animal cat dog) 'CxUniverse)
      (is (= 1 (count (tax/covers-of tx animal)))
          "one declaration, whichever order the parts arrived in"))))

;; ---- separating: the separation without the coverage --------------------

(tu/deftest-kb separating-separates-its-parts-and-claims-no-coverage
  (tu/with-terms [animal dog cat Rex]
    (v/assert kb (list 'separating animal dog cat) 'CxUniverse)
    (testing "every pair of parts is disjoint, as a partition's are"
      (is (v/disjoint? kb dog cat))
      (is (empty? (v/find-sentexes kb {:pattern (list 'disjoint dog cat)}))))
    (testing "and each part is a subtype of the whole, as a cover's are"
      (is (v/ask? kb (list 'genl dog animal) 'CxUniverse)))
    (testing "a whole instance belonging to no part violates nothing"
      (v/assert kb (list animal Rex) 'CxUniverse)
      (is (empty? (v/conflicts kb))))))

(tu/deftest-kb a-cover-edge-is-one-genl-step-read-from-the-declaration-s-context
  (tu/with-terms [animal dog cat CxA CxB]
    (doseq [c [CxA CxB]] (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
    (v/assert kb (list 'separating animal dog cat) CxA)
    (testing "the parts are the whole's direct specs, and the whole each part's direct genl"
      (is (= #{dog cat} (v/direct-specs kb animal CxA)))
      (is (= #{animal} (v/direct-genls kb dog CxA))))
    (testing "a context that does not see the declaration reads no step"
      (is (= #{} (v/direct-specs kb animal CxB)))
      (is (= #{} (v/direct-genls kb dog CxB))))
    (testing "the global arity reads every edge"
      (is (= #{dog cat} (v/direct-specs kb animal))))
    (testing "separating-covers lists the part lists disjoint? reads"
      (is (some (fn [[w ps]] (and (= animal w) (= #{dog cat} (set ps))))
                (v/separating-covers kb))))))

(tu/deftest-kb covers-of-answers-every-believed-cover-over-one-whole
  (tu/with-terms [animal dog cat bird fish plant CxA]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'partition animal dog cat) 'CxUniverse)
    (v/assert kb (list 'covering animal bird fish) CxA)
    (let [h (v/assert kb (list 'separating animal fish cat dog) 'CxUniverse)]
      (v/assert kb (list 'partition plant dog cat) 'CxUniverse)
      (testing "each kind, with its parts sorted by printed name, in every context"
        (is (= #{[:partition (vec (sort-by str [dog cat]))]
                 [:covering (vec (sort-by str [bird fish]))]
                 [:separating (vec (sort-by str [fish cat dog]))]}
               (v/covers-of kb animal))))
      (testing "a retracted cover leaves the answer"
        (v/retract! kb h)
        (is (= #{:partition :covering} (set (map first (v/covers-of kb animal)))))))
    (testing "a type no cover has for its whole answers the empty set"
      (is (= #{} (v/covers-of kb dog))))))

(tu/deftest-kb a-cover-edge-counts-in-min-genls-and-max-specs
  ;; `puppy ⊂ dog` is stated, `dog ⊂ animal` is the cover declaration's, and `(genl puppy animal)` is
  ;; stated beside them
  (tu/with-terms [animal dog cat puppy CxA CxB]
    (doseq [c [CxA CxB]] (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
    (v/assert kb (list 'separating animal dog cat) CxA)
    (v/assert kb (list 'genl puppy dog) CxA)
    (v/assert kb (list 'genl puppy animal) CxA)
    (testing "the one-step adjacency holds the stated edge to the whole"
      (is (= #{dog animal} (v/direct-genls kb puppy CxA)))
      (is (= #{dog cat puppy} (v/direct-specs kb animal CxA))))
    (testing "the nearest neighbours leave it out, through the cover's edge"
      (is (= #{dog} (v/min-genls kb puppy CxA) (v/min-genls kb puppy)))
      (is (= #{dog cat} (v/max-specs kb animal CxA) (v/max-specs kb animal))))
    (testing "a context that does not see the edges reads none"
      (is (= #{} (v/min-genls kb puppy CxB)))
      (is (= #{} (v/max-specs kb animal CxB))))))

(tu/deftest-kb max-specs-keeps-a-child-that-is-also-a-subtype-of-an-unrelated-type
  ;; `kid_a` has a second parent, `aside`, that is no neighbour of `hub`
  (tu/with-terms [hub aside kid_a kid_b kid_c kid_d kid_e kid_f]
    (let [kids [kid_a kid_b kid_c kid_d kid_e kid_f]]
      (doseq [k kids] (v/assert kb (list 'genl k hub) 'CxUniverse))
      (v/assert kb (list 'genl kid_a aside) 'CxUniverse)
      (is (= (set kids) (v/direct-specs kb hub)))
      (is (= (set kids) (v/max-specs kb hub) (v/max-specs kb hub 'CxUniverse)))
      (is (= #{kid_a} (v/max-specs kb aside))))))

(tu/deftest-kb separating-licenses-no-coverage-inference
  (tu/with-terms [animal dog cat Rex]
    (v/assert kb (list 'separating animal dog cat) 'CxUniverse)
    (v/assert kb (list animal Rex) 'CxUniverse)
    (v/assert kb (list 'not (list dog Rex)) 'CxUniverse)
    (testing "ruling out one part proves nothing about the other"
      (is (not (v/ask? kb (list cat Rex) 'CxUniverse))))
    (testing "and ruling out both refutes nothing"
      (is (= :ok (outcome kb (list 'not (list cat Rex)) 'CxUniverse))))))

(deftest the-two-claims-are-what-the-three-spellings-are-made-of
  (testing "the kinds are closed, and each spelling is one of them"
    (is (= #{:covering :separating :partition} tax/cover-kinds)))
  (testing "and the two readings a cache arm takes of a kind partition them"
    (is (= #{:covering :partition} (set (filter tax/covering-kind? tax/cover-kinds))))
    (is (= #{:separating :partition} (set (filter tax/separating-kind? tax/cover-kinds))))))

(deftest covers-over-answers-alike-from-either-side
  ;; `covers-over` walks the covered wholes when they are fewer than the closure, and the
  ;; closure when it is smaller: both walks must name the same declarations
  (let [t     (tax/create-taxonomy)
        over  #(set (tax/covers-over t 'poodle nil))
        want  #{['animal ['cat 'dog]] ['dog ['poodle 'terrier]]}]
    (tax/add-genl t 'poodle 'dog 1)
    (tax/add-genl t 'dog 'mammal 2)
    (tax/add-genl t 'mammal 'animal 3)
    (tax/add-cover t 'animal ['dog 'cat] :covering 10)
    (tax/add-cover t 'dog ['poodle 'terrier] :partition 11)
    (testing "fewer covers than supertypes"
      (is (= want (over))))
    (testing "more covers than supertypes, most over wholes it does not reach"
      (doseq [i (range 8)]
        (tax/add-cover t (symbol (str "w" i)) ['a 'b] :covering (+ 20 i)))
      (is (= want (over))))
    (testing "a separating declaration claims no coverage"
      (tax/add-cover t 'mammal ['cat 'dog] :separating 30)
      (is (= want (over))))))

(tu/deftest-kb the-three-spellings-are-three-declarations-over-one-part-list
  (tu/with-terms [animal dog cat]
    (let [c (v/assert kb (list 'covering animal dog cat) 'CxUniverse)]
      (is (not (v/disjoint? kb dog cat)) "covering alone separates nothing")
      (v/assert kb (list 'separating animal dog cat) 'CxUniverse)
      (is (v/disjoint? kb dog cat) "the separating declaration does")
      (v/retract! kb c)
      (is (v/disjoint? kb dog cat)
          "and dropping the coverage claim leaves the separation standing"))))

;; ---- what reads the separation a cover makes -----------------------------

(tu/deftest-kb a-cover-separated-clash-is-weighed-like-any-other
  ;; The separation a `partition` makes is the fourth spelling of disjointness, and a KB
  ;; declaring no other is the case that says whether every reader knows about it.  The
  ;; settle's presence check takes four set-emptiness reads for this reason: a check that
  ;; skipped a cover would leave the pair stored and never weighed, while `disjoint?` goes on answering true.
  (testing "two defeasible memberships are a dilemma, as they are under (disjoint A B)"
    (tu/with-kb [kb]
      (tu/with-terms [animal dog cat Rex]
        (v/assert kb (list 'partition animal dog cat) 'CxUniverse)
        (v/assert kb (list dog Rex) 'CxUniverse)
        (v/assert kb (list cat Rex) 'CxUniverse)
        (is (v/disjoint? kb dog cat))
        (is (= 1 (count (v/contradictions kb))))
        (is (v/ask? kb (list dog Rex) 'CxUniverse))
        (is (v/ask? kb (list cat Rex) 'CxUniverse)))))
  (testing "and the known-true side wins where one of them is known-true"
    (tu/with-kb [kb]
      (tu/with-terms [animal dog cat Rex]
        (v/assert kb (list 'partition animal dog cat) 'CxUniverse)
        (v/assert kb (list dog Rex) 'CxUniverse {:strength :monotonic})
        (v/assert kb (list cat Rex) 'CxUniverse)
        (is (v/ask? kb (list dog Rex) 'CxUniverse))
        (is (not (v/ask? kb (list cat Rex) 'CxUniverse)))))))

(tu/deftest-kb a-cover-arriving-last-exposes-the-clash-its-edges-put-under-a-separation
  ;; the covering's part edge puts a stored member under a whole that a disjointness
  ;; separates from its other type; the dilemma is the one the other order opens
  (doseq [cover-last? [true false]]
    (tu/with-kb [kb]
      (tu/with-terms [animal rock dog cat Rex]
        (let [cover! #(v/assert kb (list 'covering animal dog cat) 'CxUniverse)]
          (v/assert kb (list 'disjoint animal rock) 'CxUniverse)
          (when-not cover-last? (cover!))
          (let [d (v/assert kb (list dog Rex) 'CxUniverse)
                r (v/assert kb (list rock Rex) 'CxUniverse)]
            (when cover-last? (cover!))
            (is (= [#{d r}] (filterv #(contains? % d) (map :nogood (v/contradictions kb))))
                (str "cover last: " cover-last?))
            (is (v/ask? kb (list dog Rex) 'CxUniverse))
            (is (v/ask? kb (list rock Rex) 'CxUniverse))))))))

(tu/deftest-kb a-cover-separated-clash-has-a-witness-and-so-a-standing-reading
  ;; `exposed-clashes` answers about every jointly-visible pair, decided or not, and it
  ;; reads the derivation enumeration to say which contexts see one.  An enumeration with
  ;; no cover arm returns nothing for a cover-separated pair, which a caller reads as *not
  ;; disjoint* — the one answer `disjoint?` is already giving the other way.
  (tu/with-terms [animal dog cat Rex]
    (v/assert kb (list 'partition animal dog cat) 'CxUniverse)
    (is (seq (tax/disjointness-witnesses (reasoning/taxonomy kb) dog cat))
        "the pair has at least one complete derivation")
    (v/assert kb (list dog Rex) 'CxUniverse)
    (v/assert kb (list cat Rex) 'CxUniverse)
    (is (= 1 (count (v/exposed-clashes kb))))))

;; ---- a cover's edges bring stored facts under a rule on the whole ---------

(defn- believed? [kb sentence]
  (let [h (v/handle-of kb sentence 'CxUniverse)]
    (boolean (and h (v/in? kb h)))))

(defn- every-order [n] (tu/orders (range n)))

(defn- cover-at-each-position
  "The orders of `n` writes, the last of them the cover, that keep the others in their
  written order and put the cover at each position."
  [n]
  (let [others (vec (range (dec n)))]
    (for [i (range n)]
      (-> (subvec others 0 i) (conj (dec n)) (into (subvec others i))))))

(defn- misread-orders
  "`[spelling order sentence]` for each cover spelling, each order of the writes `world`
  returns and each sentence of its `:expect` (`{sentence believed?}`) that reads otherwise
  once the writes are asserted in CxUniverse in that order and each of `:retract` is
  retracted.  `world` takes the spelling and returns `{:writes :retract :expect}` over
  fresh terms, so each order runs on terms of its own; `orders` takes the count of writes
  and returns index vectors.  A rule is asserted forward, and a cover or `genl` edge
  monotonic."
  [kb world orders]
  (let [misread (volatile! [])]
    (doseq [spelling '[covering separating partition]
            idxs     (orders (count (:writes (world spelling))))]
      (let [{:keys [writes retract expect]} (world spelling)
            order (mapv writes idxs)]
        (doseq [s order]
          (case (first s)
            implies (v/assert kb (list 'set/forwardRule s) 'CxUniverse)
            (genl covering separating partition)
            (v/assert kb s 'CxUniverse {:strength :monotonic})
            (v/assert kb s 'CxUniverse)))
        (doseq [s retract] (v/retract! kb (v/handle-of kb s 'CxUniverse)))
        (doseq [[s want] expect
                :when (not= want (believed? kb s))]
          (vswap! misread conj [spelling order s]))))
    @misread))

(defn- rule-on-the-whole
  "A rule matching the whole alone and one joining it, over a part's facts, with the
  cover written last."
  [spelling]
  (tu/with-terms [a b c z q rel Kit Rex]
    {:writes [(list 'implies (list a '?x) (list z '?x))
              (list 'implies (list 'and (list a '?x) (list rel '?x '?y)) (list q '?y))
              (list c Kit)
              (list rel Kit Rex)
              (list spelling a b c)]
     :expect {(list z Kit) true (list q Rex) true}}))

(tu/deftest-kb a-rule-on-the-whole-fires-on-a-part-fact-wherever-the-cover-arrives
  (is (empty? (misread-orders kb rule-on-the-whole cover-at-each-position)))
  (testing "and a rule joining over the genl closure the cover adds to"
    (is (empty? (misread-orders
                 kb (fn [spelling]
                      (tu/with-terms [a b c under]
                        {:writes [(list 'implies (list 'genl '?t a) (list under '?t))
                                  (list spelling a b c)]
                         :expect {(list under c) true}}))
                 every-order)))))

(tu/deftest-kb ^:slow a-rule-on-the-whole-fires-on-a-part-fact-in-every-order
  (is (empty? (misread-orders kb rule-on-the-whole every-order))))

(tu/deftest-kb retracting-a-cover-withdraws-a-firing-only-its-edge-licensed-in-every-order
  (testing "the cover's edge was the only route"
    (is (empty? (misread-orders
                 kb (fn [spelling]
                      (tu/with-terms [a b c z Kit]
                        {:writes  [(list 'implies (list a '?x) (list z '?x))
                                   (list c Kit)
                                   (list spelling a b c)]
                         :retract [(list spelling a b c)]
                         :expect  {(list z Kit) false}}))
                 every-order))))
  (testing "a stated edge is a second route, and the firing comes back over it"
    (is (empty? (misread-orders
                 kb (fn [spelling]
                      (tu/with-terms [a b c z Kit]
                        {:writes  [(list 'implies (list a '?x) (list z '?x))
                                   (list c Kit)
                                   (list 'genl c a)
                                   (list spelling a b c)]
                         :retract [(list spelling a b c)]
                         :expect  {(list z Kit) true}}))
                 every-order))))
  (testing "the same for a rule joining over the genl closure"
    (is (empty? (misread-orders
                 kb (fn [spelling]
                      (tu/with-terms [a b c under]
                        {:writes  [(list 'implies (list 'genl '?t a) (list under '?t))
                                   (list 'genl c a)
                                   (list spelling a b c)]
                         :retract [(list spelling a b c)]
                         :expect  {(list under c) true (list under b) false}}))
                 every-order)))))
