;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.term-edit-test
  "The term operations: `rename-terms!`, `merge-terms!`, `copy-terms`, `remove-terms!` and
  `check-term-edit` (docs/api.md, \"Contract notes: term operations\")."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [clojure.walk :as walk]
            [vaelii.core :as v]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.term-edit :as te]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(defn- uses
  "The sentences of the stored premises naming `t`, as a set."
  [kb t]
  (into #{} (comp (filter :strength) (map v/sentence-of)) (v/find-sentexes kb t)))

(defn- refusal [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))

(deftest a-substitution-leaves-a-quotation-and-rewrites-an-unquote-hole
  (is (= '(likes Ann (Quote (likes Bob Ann)) (Quasiquote (knows (Unquote Ann2) Bob)) [Ann2])
         (te/substitute '{Bob Ann2}
                        '(likes Ann (Quote (likes Bob Ann)) (Quasiquote (knows (Unquote Bob) Bob)) [Bob]))))
  (is (= '(says Ann (Quasiquote (knows (Quasiquote (Unquote Bob)))))
         (te/substitute '{Bob Ann2} '(says Ann (Quasiquote (knows (Quasiquote (Unquote Bob)))))))
      "a hole of a nested Quasiquote belongs to the inner mention and stays literal"))

(tu/deftest-kb a-rename-restates-every-premise-and-keeps-its-strength
  (tu/with-terms [likes knows X Y CxStory]
    (let [z  (tu/tmp-ind "Renamed")
          h1 (v/assert kb (list likes Y X) CxStory {:strength :monotonic})
          h2 (v/assert kb (list 'comment X "a person") 'CxUniverse)
          h3 (v/assert kb (list 'implies (list likes '?a X) (list knows '?a X)) CxStory)
          r  (v/rename-term! kb X z)]
      (is (= 3 (:restated r) (:retracted r)))
      (is (every? #(nil? (v/sentex kb %)) [h1 h2 h3]))
      (is (= #{} (uses kb X)))
      (let [n1 (v/handle-of kb (list likes Y z) CxStory)]
        (is (= n1 (get (:handles r) h1)))
        (is (= :monotonic (:strength (v/sentex kb n1)))))
      (is (some? (v/handle-of kb (list 'comment z "a person") 'CxUniverse))
          "a comment's quotedArg position names the term as written, so it follows the rename")
      (let [fired (v/provable? kb (list knows Y z) CxStory)]
        (is fired "the restated rule proves over the restated fact")))))

(tu/deftest-kb a-quotation-keeps-the-old-spelling
  (tu/with-terms [says X Y CxStory]
    (let [z (tu/tmp-ind "Renamed")
          q (list says Y (list 'Quote (list says X Y)))
          h (v/assert kb q CxStory)]
      (v/assert kb (list says X Y) CxStory)
      (v/rename-term! kb X z)
      (is (= h (v/handle-of kb q CxStory)))
      (is (= #{q} (uses kb X))))))

(tu/deftest-kb a-rename-restates-a-nat-through-its-expression
  (tu/with-terms [owns X Y HatFn CxStory]
    (v/assert kb (list 'reifiable_function HatFn) 'CxUniverse)
    (v/assert kb (list 'arity HatFn 1) 'CxUniverse)
    (v/assert kb (list owns Y (list HatFn X)) CxStory)
    (v/assert kb (list owns X (list HatFn (list HatFn X))) CxStory)
    (let [z   (tu/tmp-ind "Renamed")
          old (v/find-sentexes kb X)]
      (v/rename-term! kb X z)
      (is (= #{} (uses kb X)) "no premise and no natFormula names the old term")
      (let [a (v/ask? kb (list owns Y (list HatFn z)) CxStory)
            b (v/ask? kb (list owns z (list HatFn (list HatFn z))) CxStory)]
        (is a)
        (is b))
      (is (every? #(nil? (v/sentex kb (:id %))) old)))))

(defn- rename-reading
  "`[refusal rows]` after asserting each `[context sentence]` of `prems` in order, with
  fresh terms for the roles `pRel rRel A C X Y Z Fn CxA CxB W`, and renaming by `smap`:
  the `:type` the rename throws, or nil, and the stored sentexes naming a term of `prems`
  as `[context sentence premise?]`.  A term reads back as its role, and the constant
  minted for `(Fn a)` as `(Mint (Fn a))`."
  [kb prems smap]
  (tu/with-terms [pRel rRel A C X Y Z Fn CxA CxB]
    (let [terms (zipmap '[pRel rRel A C X Y Z Fn CxA CxB W]
                        [pRel rRel A C X Y Z Fn CxA CxB (symbol "nat" (name (tu/tmp-ind "Wq")))])
          real  #(walk/postwalk-replace terms %)
          back  (into (zipmap (vals terms) (keys terms))
                      (for [a '[X Y Z]]
                        [(nat/constant-for "nat" (real (list 'Fn a))) (list 'Mint (list 'Fn a))]))]
      (doseq [[c s] prems] (v/assert kb (real s) (real c)))
      [(when smap (:type (refusal #(v/rename-terms! kb (real smap)))))
       (into #{} (map #(walk/postwalk-replace back [(:context %) (v/sentence-of %) (some? (:strength %))]))
             (mapcat #(v/find-sentexes kb %) (vals terms)))])))

(def ^:private writer-spelled-rows
  ;; `W` is a writer-spelled constant: a premise maps it to `(Fn Y)`, whose minted name is
  ;; another, and a use names it.  The second scenario states the map in `CxA` and the uses
  ;; in `CxB`, neither of which sees the other, and a rename of `Y` is refused.
  (let [universe '[[CxUniverse (reifiable_function Fn)] [CxUniverse (pRel A (Fn X))]
                   [CxUniverse (natFormula W (Fn Y))] [CxUniverse (rRel C W)]]
        sibling  '[[CxUniverse (reifiable_function Fn)] [CxB (pRel A (Fn X))]
                   [CxA (natFormula W (Fn Y))] [CxB (rRel C W)]]]
    [[universe '{X Z} nil] [universe '{Y Z} nil]
     [sibling '{X Z} nil] [sibling '{Y Z} :nat-map-outside-universe]]))

(defn- renames-read-as-written
  "Each ordering `pick` takes from each row of `writer-spelled-rows`, renamed, reads as
  the KB written with the new name, or, for a refused row, throws that refusal and reads
  as the KB written."
  [kb pick]
  (doseq [[prems smap refused] writer-spelled-rows
          :let [orders (pick (vec (tu/permutations prems)))]]
    (is (= {[refused (second (rename-reading kb (cond->> prems (not refused) (walk/postwalk-replace smap))
                                             nil))]
            (count orders)}
           (frequencies (map #(rename-reading kb % smap) orders)))
        (pr-str smap (first (nth prems 2))))))

(tu/deftest-kb ^:slow a-rename-reads-as-the-kb-written-with-the-new-name-in-every-order
  (renames-read-as-written kb identity))

(tu/deftest-kb a-rename-reads-as-the-kb-written-with-the-new-name-in-sampled-orders
  (renames-read-as-written kb #(vector (first %) (nth % 12) (peek %))))

(tu/deftest-kb each-term-operation-reaching-a-map-outside-cxuniverse-is-refused
  (tu/with-terms [rRel C Y Z Fn CxA CxB]
    (let [w  (symbol "nat" (name (tu/tmp-ind "Wq")))
          _  (v/assert kb (list 'reifiable_function Fn) 'CxUniverse)
          hm (v/assert kb (list 'natFormula w (list Fn Y)) CxA)]
      (v/assert kb (list rRel C w) CxB)
      (v/assert kb (list rRel C Z) CxB)
      (doseq [[op mapping] [[:rename {Y (tu/tmp-ind "Renamed")}] [:merge {Y Z}]
                            [:copy {Y (tu/tmp-ind "Copied")}] [:remove [Y]]]]
        (is (= [:nat-map-outside-universe [hm]]
               ((juxt :type :handles) (refusal #(v/term-edit-plan kb op mapping))))
            (str op)))
      (is (= :nat-map-outside-universe (:type (refusal #(v/remove-term! kb Y)))))
      (is (some? (v/sentex kb hm))))))

(tu/deftest-kb a-meta-naming-a-restated-premise-names-its-restatement
  (tu/with-terms [likes X Y CxStory]
    (let [z (tu/tmp-ind "Renamed")
          h (v/assert kb (list likes Y X) CxStory)]
      (v/assert kb (list 'except (list 'ist CxStory (list likes Y X))) CxStory)
      (let [before (v/ask? kb (list likes Y X) CxStory)
            r      (v/rename-term! kb X z)
            n      (get (:handles r) h)
            after  (v/ask? kb (list likes Y z) CxStory)]
        (is (not before))
        (is (= 1 (count (v/sentexes-naming kb n))) "the except names the new handle")
        (is (not after) "and still hides it")))))

(tu/deftest-kb an-exceptWhen-whose-query-uses-the-term-is-restated-with-its-rule
  (doseq [strength [:default :monotonic]]
    (tu/with-terms [bird flies penguin swims X Y W CxStory]
      (let [z    (tu/tmp-ind "Renamed")
            rule (list 'implies (list bird '?x) (list flies '?x))
            hr   (v/assert kb rule CxStory {:strength strength})]
        (v/assert kb (list 'exceptWhen (list penguin '?x X) rule) CxStory)
        (v/assert kb (list 'exceptWhen (list swims '?x) rule) CxStory)
        (v/assert kb (list bird Y) CxStory)
        (v/assert kb (list bird W) CxStory)
        (v/assert kb (list penguin Y X) CxStory)
        (let [before (mapv #(v/provable? kb (list flies %) CxStory) [Y W])
              r      (v/rename-term! kb X z)
              after  (mapv #(v/provable? kb (list flies %) CxStory) [Y W])]
          (testing (name strength)
            (is (= [false true] before))
            (is (= #{} (uses kb X)))
            (is (= [false true] after) "the restated exception blocks Y, and the rule fires for W")
            (is (= hr (v/handle-of kb rule CxStory)) "the rule names no X, so it keeps its record")
            (is (= 2 (:retracted r)) "the exception and the fact naming X, and not the rule")))))))

(tu/deftest-kb removing-a-term-an-exceptWhen-query-alone-uses-keeps-the-rule
  (tu/with-terms [bird flies penguin X Y CxStory]
    (let [rule (list 'implies (list bird '?x) (list flies '?x))
          hr   (v/assert kb rule CxStory)]
      (v/assert kb (list 'exceptWhen (list penguin '?x X) rule) CxStory)
      (v/assert kb (list bird Y) CxStory)
      (v/assert kb (list penguin Y X) CxStory)
      (let [before (v/provable? kb (list flies Y) CxStory)
            r      (v/remove-term! kb X)
            after  (v/provable? kb (list flies Y) CxStory)]
        (is (not before))
        (is (= 2 (:retracted r)) "the exception and the penguin fact")
        (is (= hr (v/handle-of kb rule CxStory)))
        (is after "with its exception gone, the rule fires")))))

(tu/deftest-kb renaming-a-context-moves-its-extent
  (tu/with-terms [likes X Y CxStory]
    (let [cz (tu/tmp-ctx "Tale")]
      (v/assert kb (list 'genlCx CxStory 'CxUniverse) 'CxUniverse)
      (v/assert kb (list likes X Y) CxStory)
      (v/rename-term! kb CxStory cz)
      (is (empty? (v/find-sentexes kb CxStory)))
      (is (some? (v/handle-of kb (list likes X Y) cz)))
      (is (some? (v/handle-of kb (list 'genlCx cz 'CxUniverse) 'CxUniverse))))))

(tu/deftest-kb a-merge-joins-two-types-and-drops-the-edge-between-them
  (tu/with-terms [a_t b_t X]
    (v/assert kb (list 'genl a_t b_t) 'CxUniverse)
    (v/assert kb (list 'genl b_t 'thing) 'CxUniverse)
    (v/assert kb (list a_t X) 'CxUniverse)
    (let [hb (v/assert kb (list b_t X) 'CxUniverse)
          r  (v/merge-term! kb a_t b_t)]
      (is (= #{} (uses kb a_t)))
      (is (= hb (v/handle-of kb (list b_t X) 'CxUniverse)) "the shared sentence keeps b's record")
      (is (nil? (v/handle-of kb (list 'genl b_t b_t) 'CxUniverse)))
      (is (= [1 2] [(:restated r) (:retracted r)])
          "the genl edge between the two is retracted and not restated"))))

(tu/deftest-kb a-merge-of-two-nats-leaves-one-constant
  (tu/with-terms [owns X Y W HatFn CxStory]
    (v/assert kb (list 'reifiable_function HatFn) 'CxUniverse)
    (v/assert kb (list 'arity HatFn 1) 'CxUniverse)
    (v/assert kb (list owns W (list HatFn X)) CxStory)
    (v/assert kb (list owns W (list HatFn Y)) CxStory)
    (v/merge-term! kb X Y)
    (let [owned (v/ask kb (list owns W '?h) CxStory)]
      (is (= 1 (count owned)))
      (is (= #{} (uses kb X))))))

(tu/deftest-kb a-copy-onto-a-stored-type-drops-the-edge-it-makes-reflexive
  (tu/with-terms [a_t b_t X]
    (v/assert kb (list 'genl a_t b_t) 'CxUniverse)
    (v/assert kb (list a_t X) 'CxUniverse)
    (let [r (v/copy-term kb a_t b_t)]
      (is (= [1 0] [(:restated r) (:retracted r)]))
      (is (nil? (v/handle-of kb (list 'genl b_t b_t) 'CxUniverse)))
      (is (some? (v/handle-of kb (list 'genl a_t b_t) 'CxUniverse)))
      (is (some? (v/handle-of kb (list b_t X) 'CxUniverse))))))

(tu/deftest-kb a-term-operation-that-takes-belief-away-is-refused-and-rolled-back
  (doseq [[op irreflexive? strong] [[:merge true :default] [:merge false :monotonic]
                                    [:copy false :monotonic]]]
    (tu/with-terms [partOf X Y Z CxStory]
      (when irreflexive? (v/assert kb (list 'irreflexive partOf) 'CxUniverse {:strength :monotonic}))
      (let [hx  (v/assert kb (list partOf X (if irreflexive? Y Z)) CxStory {:strength strong})
            hn  (when-not irreflexive? (v/assert kb (list 'not (list partOf Y Z)) CxStory))
            run (if (= :merge op) v/merge-term! v/copy-term)
            r   (refusal #(run kb X Y))]
        (testing (pr-str op irreflexive?)
          (is (= [:lost-belief true] [(:type r) (:rolled-back r)]))
          (is (= (if irreflexive? [hx] [hn]) (:handles r)))
          (is (= (set (remove nil? [hx hn])) (v/believed kb (remove nil? [hx hn]))))
          (is (nil? (v/handle-of kb (list partOf Y (if irreflexive? Y Z)) CxStory))))))))

(tu/deftest-kb copy-restates-without-retracting
  (tu/with-terms [likes X Y CxStory]
    (let [z (tu/tmp-ind "Copied")
          h (v/assert kb (list likes Y X) CxStory)
          r (v/copy-term kb X z)]
      (is (= 0 (:retracted r)))
      (is (some? (v/sentex kb h)))
      (is (= (v/handle-of kb (list likes Y z) CxStory) (get (:handles r) h))))))

(tu/deftest-kb remove-retracts-every-use-and-leaves-a-quotation
  (tu/with-terms [likes says owns X Y HatFn CxStory]
    (v/assert kb (list 'reifiable_function HatFn) 'CxUniverse)
    (v/assert kb (list 'arity HatFn 1) 'CxUniverse)
    (let [h1 (v/assert kb (list likes Y X) CxStory)
          h2 (v/assert kb (list owns Y (list HatFn X)) CxStory)
          hm (v/assert kb (list 'except (list 'ist CxStory (list likes Y X))) CxStory)
          q  (list says Y (list 'Quote (list likes Y X)))
          hq (v/assert kb q CxStory)
          r  (v/remove-term! kb X)]
      (is (= 3 (:retracted r)))
      (is (every? #(nil? (v/sentex kb %)) [h1 h2 hm]))
      (is (= hq (v/handle-of kb q CxStory)))
      (is (= #{q} (uses kb X)) "the natFormula map went with the constant's last use"))))

(tu/deftest-kb check-term-edit-names-each-refusal
  (tu/with-terms [likes says X Y a_t b_t dog]
    (v/assert kb (list likes X Y) 'CxUniverse)
    (v/assert kb (list 'genl a_t 'thing) 'CxUniverse)
    (v/assert kb (list 'genl b_t 'thing) 'CxUniverse)
    (v/assert kb (list 'disjoint a_t b_t) 'CxUniverse)
    (v/assert kb (list dog X) 'CxUniverse)
    (let [z (tu/tmp-ind "Fresh")
          q (tu/tmp-ind "Quoted")]
      (v/assert kb (list says Y (list 'Quote (list likes q Y))) 'CxUniverse)
      (doseq [[op mapping type] [[:explode {X z} :shape]
                                 [:rename {} :shape]
                                 [:rename {X X} :shape]
                                 [:rename {X Y Y z} :shape]
                                 [:rename {X z Y z} :shape]
                                 [:remove {X z} :shape]
                                 [:rename {'?x z} :reserved-term]
                                 [:rename {X 'nat/a0abc} :reserved-term]
                                 [:rename {X 'lowercase} :role-change]
                                 [:rename {'genl 'genlTwo} :shipped-term]
                                 [:remove ['genl] :shipped-term]
                                 [:rename {z (tu/tmp-ind "Other")} :unknown-term]
                                 [:rename {X Y} :term-exists]
                                 [:merge {X z} :unknown-term]
                                 [:merge {X q} :unknown-term]
                                 [:merge {a_t b_t} :incompatible-terms]
                                 [:copy {a_t b_t} :incompatible-terms]
                                 [:copy {X a_t} :role-change]]]
        (testing (pr-str op mapping)
          (is (= type (:type (first (v/check-term-edit kb op mapping)))))))
      (is (= [] (v/check-term-edit kb :copy {'genl 'genlTwo})) "a copy of a shipped term is allowed")
      (is (= [] (v/check-term-edit kb :merge {a_t 'thing})) "a merge into a shipped term is allowed")
      (is (= [] (v/check-term-edit kb :rename {X q})) "a name only a quotation mentions is no term")
      (doseq [to [(symbol (str dog "_kind")) (symbol (str dog "-sense"))]]
        (is (= [] (v/check-term-edit kb :rename {dog to}))
            (str "a bare word's spelling admits a type, so " to " keeps its role")))
      (is (= :term-exists (:type (refusal #(v/rename-term! kb X Y)))))
      (is (some? (v/handle-of kb (list likes X Y) 'CxUniverse)) "a refused operation writes nothing"))))

(tu/deftest-kb the-plan-is-the-batch-the-operation-runs
  (tu/with-terms [likes X Y CxStory]
    (let [z    (tu/tmp-ind "Renamed")
          h    (v/assert kb (list likes Y X) CxStory)
          plan (v/term-edit-plan kb :rename {X z})
          [[s c]] (get-in plan [:batch :add])]
      (is (= [[h]] (:restates plan)))
      (is (= [h] (get-in plan [:batch :remove])))
      (is (= [(list likes Y z) CxStory] [s c]))
      (is (= [] (v/check-edit kb (:batch plan))))
      (is (some? (v/preview kb (:batch plan))) "preview reads the batch as it stands")
      (is (some? (v/sentex kb h)) "the plan writes nothing")
      (is (= :term-exists (:type (refusal #(v/term-edit-plan kb :rename {X Y}))))))))

(tu/deftest-kb an-inert-sentex-using-the-term-refuses-a-rename-and-not-a-remove
  (tu/with-terms [likes X Y CxStory]
    (let [z  (tu/tmp-ind "Renamed")
          h  (v/assert-inert kb (list likes Y X) CxStory)
          ex (refusal #(v/rename-term! kb X z))]
      (is (= :unrestatable-sentex (:type ex)))
      (is (= [h] (:handles ex)))
      (is (some? (v/sentex kb h)))
      (is (= 1 (:retracted (v/remove-term! kb X)))))))

(tu/deftest-kb a-sentence-with-no-text-form-refuses-a-rename-and-not-a-remove
  ;; a handle outside a reference position has no text form: one sentence uses X beside
  ;; such a handle, and the other names a premise using X through one
  (doseq [direct? [true false]]
    (tu/with-terms [likes X Y CxStory]
      (let [z  (tu/tmp-ind "Renamed")
            h0 (v/assert kb (list likes Y (if direct? Y X)) CxStory)
            h  (v/assert kb (list likes (if direct? X Y) (list 'sentexHandle h0)) CxStory)
            ex (refusal #(v/rename-term! kb X z))]
        (testing (if direct? "uses the term" "names a premise using it")
          (is (= :unrestatable-sentex (:type ex)))
          (is (= [h] (:handles ex)))
          (is (every? #(some? (v/sentex kb %)) [h0 h]))
          (is (= (if direct? 1 2) (:retracted (v/remove-term! kb X)))))))))

(tu/deftest-kb a-stopped-rename-leaves-the-kb-as-it-found-it
  (tu/with-terms [likes X Y CxStory]
    (let [z  (tu/tmp-ind "Renamed")
          hs (mapv #(v/assert kb (list likes % X) CxStory) [Y (tu/tmp-ind "Other")])
          ex (refusal #(v/rename-term! kb X z {:stop? (constantly true)}))]
      (is (= :interrupted (:type ex)))
      (is (true? (:rolled-back ex)))
      (is (every? #(some? (v/sentex kb %)) hs))
      (is (empty? (v/find-sentexes kb z))))))

(defn- stored-reading
  "Every stored record of `kb` as `[sentence context strength believed?]`."
  [kb]
  (into #{} (map #(let [sx (v/sentex kb %)] [(v/sentence-of sx) (:context sx) (:strength sx) (v/in? kb %)]))
        (tu/sentex-ids kb)))

(deftest a-disk-log-store-reopens-as-a-stopped-or-completed-rename-left-it
  ;; the k-th stop check stops the rename, for each k until one completes, so every stop
  ;; point's rollback is read back off the reopened store
  (tu/with-terms [likes knows X Y CxStory]
    (let [dir  (tu/tmpdir "vaelii-term-edit-")
          open #(v/open-kb {:backend :disk-log :dir dir})
          z    (tu/tmp-ind "Renamed")]
      (try
        (let [kb (open)]
          (v/assert kb (list likes Y X) CxStory {:strength :monotonic})
          (v/assert kb (list 'implies (list likes '?a X) (list knows '?a X)) CxStory)
          (v/close! kb))
        (let [before (let [kb (open)] (try (stored-reading kb) (finally (v/close! kb))))
              done   (loop [k 1]
                       (let [kb (open)
                             n  (volatile! 0)
                             r  (try (v/rename-term! kb X z {:stop? #(= k (vswap! n inc))})
                                     (catch clojure.lang.ExceptionInfo e (ex-data e))
                                     (finally (v/close! kb)))]
                         (if (= :interrupted (:type r))
                           (do (is (= before (let [kb (open)] (try (stored-reading kb) (finally (v/close! kb)))))
                                   (str "stopped at check " k))
                               (recur (inc k)))
                           k)))]
          (is (< 1 done) "a stop check ran after the first one")
          (let [kb (open)]
            (try
              (is (= #{} (uses kb X)))
              (is (v/in? kb (v/handle-of kb (list likes Y z) CxStory)))
              (is (= (count before) (count (stored-reading kb))))
              (finally (v/close! kb)))))
        (finally (tu/rm-rf! dir))))))

(defn- expanded
  "`form` with each reified constant replaced by its expression and each `(sentexHandle h)`
  by the sentence and context `h` names, recursively."
  [kb form]
  (walk/prewalk (fn [x] (cond
                          (and (symbol? x) (nm/reified-constant? x))
                          (if-let [e (v/term-expression kb x)] (expanded kb e) x)
                          (and (seq? x) (= 'sentexHandle (first x)) (integer? (second x)))
                          (if-let [sx (v/sentex kb (second x))]
                            (list :names (expanded kb (v/sentence-of sx)) (:context sx))
                            x)
                          :else x))
                form))

(defn- world-belief
  "Every believed sentex of `kb` as `[sentence context]`, read through `expanded`."
  [kb]
  (into #{} (map #(let [sx (v/sentex kb %)]
                    [(expanded kb (v/sentence-of sx)) (expanded kb (:context sx))]))
        (v/believed kb (p/sentex-ids (:records kb)))))

(defn- renames-preserve-belief
  "Rename each of `terms` in the test world to a fresh name and back.  The answer holds
  `[term lost gained lost-back gained-back]` for each term where belief after the rename
  is not the substitution of belief before it, or belief after the rename back is not
  belief before both."
  [terms]
  (tu/with-cleared-kb [kb #(-> (tu/isolated-fresh) tu/load-starter! world/load-into)]
    (into [] (keep (fn [t]
                     (let [n   (name t)
                           nu  (symbol (cond (nm/context? t)                       (str "CxRenamed" (subs n 2))
                                             (Character/isUpperCase (.charAt n 0)) (str "Renamed" n)
                                             (nm/predicate? t)                     (str n "renamed")
                                             (nm/type-symbol? t)                   (str n "_renamed")
                                             :else                                 (str n "Renamed")))
                           b0  (world-belief kb)
                           exp (into #{} (map (fn [[s c]] [(te/substitute {t nu} s) (te/substitute {t nu} c)])) b0)
                           _   (v/rename-term! kb t nu)
                           b1  (world-belief kb)
                           _   (v/rename-term! kb nu t)
                           b2  (world-belief kb)
                           row [t (remove b1 exp) (remove exp b1) (remove b2 b0) (remove b0 b2)]]
                       (when (some seq (rest row)) row))))
          terms)))

(deftest ^:slow a-rename-preserves-the-test-worlds-belief-up-to-its-substitution
  (is (= [] (renames-preserve-belief '[CxNaturalWorld Tom Muffet liar wants raced]))))

(tu/deftest-kb a-rename-carries-application-provenance
  (tu/with-terms [likes X Y CxStory]
    (let [z (tu/tmp-ind "Renamed")
          h (binding [v/*creator* "ann"] (v/assert kb (list likes Y X) CxStory))]
      (v/add-provenance kb h {:source "import-7"})
      (let [n (get (:handles (binding [v/*creator* "bob"] (v/rename-term! kb X z))) h)]
        (is (= "import-7" (:source (v/provenance kb n))))
        (is (= "bob" (:creator (v/provenance kb n)))
            "the restatement records who renamed, not who wrote the original")))))

(tu/deftest-kb a-failed-provenance-write-rolls-the-rename-or-merge-back-whole
  ;; the second restatement's provenance write throws; a merge's first restatement is its
  ;; stored target, whose own map the first write merged into
  (doseq [op [:rename :merge]]
    (tu/with-terms [likes X Y W Z CxStory]
      (let [target (when (= :merge op) (v/assert kb (list likes Y Z) CxStory))
            hs     (mapv #(v/assert kb (list likes % X) CxStory) [Y W])
            held   (cond-> hs target (conj target))
            _      (doseq [[i h] (map-indexed vector held)]
                     (v/add-provenance kb h {:source (str "import-" i)}))
            prov   #(into {} (map (juxt identity (partial v/provenance kb))) held)
            before (prov)
            put    v/add-provenance
            calls  (atom 0)
            thrown (with-redefs [v/add-provenance
                                 (fn [kb h m]
                                   (if (= 2 (swap! calls inc))
                                     (throw (ex-info "provenance write failed" {:type :io}))
                                     (put kb h m)))]
                     (try (if target (v/merge-term! kb X Z) (v/rename-term! kb X Z)) nil
                          (catch Exception e e)))]
        (testing (name op)
          (is (= [true 2] [(some? thrown) @calls]))
          (is (= before (prov)))
          (is (every? #(v/in? kb %) hs))
          (is (= (if target #{(list likes Y Z)} #{}) (uses kb Z))))))))
