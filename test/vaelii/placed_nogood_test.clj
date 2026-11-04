;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.placed-nogood-test
  "A nogood places its conclusions as a firing does: `(contradicts …)` and the `defeat` of
  a unique weakest member at the maximal common descendants of its members and grounds,
  justified by them (`chain/place-nogood!`).  A `defeat` is a meta-sentex only the engine
  derives, indexed under the handle it names (docs/glossary.md, `defeat`).

  Every test states its lattice in a comment, since the answer is a function of it."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [clojure.walk]
            [vaelii.core :as v]
            [vaelii.impl.budget :as budget]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.impl.decide.membership :as membership]
            [vaelii.impl.except :as exc]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- refusal-type
  "The `:type` `assert` throws for `sentence` in `context`, or nil when it stores it."
  [kb sentence context]
  (try (v/assert kb sentence context) nil
       (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(tu/deftest-kb assert-refuses-defeat-in-every-literal
  (tu/with-terms [cat dog Rex CxA]
    (let [h (v/assert kb (list cat Rex) CxA)
          d (list 'defeat (list 'sentexHandle h))]
      (testing "a fact, its negation, a rule's consequent and antecedent, an exceptWhen query"
        (is (= [:derived-only :derived-only :derived-only :derived-only :derived-only]
               (mapv #(refusal-type kb % CxA)
                     [d
                      (list 'not d)
                      (list 'implies (list dog '?x) (list 'defeat '?x))
                      (list 'implies (list 'defeat '?x) (list dog '?x))
                      (list 'exceptWhen (list 'defeat '?x)
                            (list 'implies (list cat '?x) (list dog '?x)))]))))
      (testing "check predicts the refusal"
        (is (= :derived-only (:type (first (v/check kb d CxA))))))
      (testing "the index holds no defeat, and a defeat pattern is still matchable"
        (is (not (reads/stores-any? (:index kb) 'defeat)))
        (is (empty? (v/sentexes-matching kb '(defeat ?h) '?ctx)))))))

(defn- resolved
  "`form` with each `(sentexHandle h)` replaced by `[sentence context]` of `h`."
  [kb form]
  (if (and (seq? form) (= 'sentexHandle (first form)))
    (let [s (v/sentex kb (second form))] [(:sentence s) (:context s)])
    (if (seq? form) (map #(resolved kb %) form) form)))

(defn- placed
  "The stored `contradicts` and `defeat` sentexes, as `[resolved-sentence context]`."
  [kb]
  (into #{} (for [f '[contradicts defeat]
                  s (v/sentexes-with-functor kb f)]
              [(resolved kb (:sentence s)) (:context s)])))

(defn- sole
  "The one element of `xs`, which must hold exactly one."
  [xs]
  (is (= 1 (count xs)))
  (first xs))

(defn- place!
  "Place the nogood over `members` and `grounds`, and settle, as a write does."
  [kb members grounds]
  (let [hs (chain/place-nogood! kb members grounds)]
    (settle/settle kb)
    hs))

(defn- lattice!
  "CxA and CxB under CxUniverse, CxD under both."
  [kb CxA CxB CxD]
  (doseq [c [CxA CxB]] (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
  (doseq [c [CxA CxB]] (v/assert kb (list 'genlCx CxD c) 'CxUniverse)))

(tu/deftest-kb a-nogood-is-placed-at-the-common-descendant-of-its-members-and-grounds
  ;;   CxUniverse  (excludesType dog cat), a ground no nogood family reads
  ;;     ├─ CxA    (cat Rex) default
  ;;     └─ CxB    (dog Rex) monotonic
  ;;          CxD under both
  (tu/with-terms [cat dog Rex excludesType CxA CxB CxD]
    (lattice! kb CxA CxB CxD)
    (let [l (v/assert kb (list cat Rex) CxA)
          w (v/assert kb (list dog Rex) CxB {:strength :monotonic})
          g (v/assert kb (list excludesType dog cat) 'CxUniverse)
          L [(list cat Rex) CxA]
          W [(list dog Rex) CxB]]
      (place! kb #{l w} #{g})
      (testing "a contradicts naming the members in content order and the defeat of the loser"
        (is (= #{[(list 'contradicts L W) CxD] [(list 'defeat L) CxD]} (placed kb)))
        (is (every? #(v/in? kb (:id %)) (concat (v/sentexes-with-functor kb 'contradicts)
                                                (v/sentexes-with-functor kb 'defeat)))))
      (testing "a second detection, members in another order, stores nothing new"
        (let [before (v/sentex-count kb)]
          (is (empty? (place! kb [w l] [g])))
          (is (= before (v/sentex-count kb)))
          (is (= 1 (count (v/sentexes-with-functor kb 'contradicts))))
          (is (= 1 (count (:support (tu/why-root kb (:id (sole (v/sentexes-with-functor kb 'contradicts))))))))))
      (testing "why names the members, the ground and the genlCx edges CxD sees them over"
        (let [d     (:id (sole (v/sentexes-with-functor kb 'defeat)))
              antes (into #{} (comp (mapcat :because) (map :handle)) (:support (tu/why-root kb d)))]
          (is (= [chain/nogood-informant] (mapv :informant (:support (tu/why-root kb d)))))
          (is (= #{l w g} (into #{} (remove #(= 'genlCx (first (:sentence (v/sentex kb %))))) antes)))
          (is (every? (into #{} (comp (map #(:sentence (v/sentex kb %))) (filter #(= 'genlCx (first %))))
                            antes)
                      [(list 'genlCx CxD CxA) (list 'genlCx CxD CxB)]))))
      (testing "the defeat is in the index by its target"
        (is (= #{l} (reads/as-stored-named-global (:index kb) 'defeat)))))))

(tu/deftest-kb a-dilemma-and-a-conflict-place-a-contradicts-and-no-defeat
  (tu/with-terms [cat dog Rex Tom excludesType CxA]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
    (let [g  (v/assert kb (list excludesType dog cat) 'CxUniverse)
          l1 (v/assert kb (list cat Rex) CxA)
          l2 (v/assert kb (list dog Rex) CxA)
          m1 (v/assert kb (list cat Tom) CxA {:strength :monotonic})
          m2 (v/assert kb (list dog Tom) CxA {:strength :monotonic})]
      (place! kb #{l1 l2} #{g})
      (place! kb #{m1 m2} #{g})
      (is (= 2 (count (v/sentexes-with-functor kb 'contradicts))))
      (is (empty? (v/sentexes-with-functor kb 'defeat))))))

(defn- retracting-takes-it-out
  "Place the nogood of `a-nogood-is-placed-…`, retract the handle `pick` chooses, and
  answer what stays placed."
  [pick]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [cat dog Rex excludesType CxA CxB CxD]
      (lattice! kb CxA CxB CxD)
      (let [hs {:l (v/assert kb (list cat Rex) CxA)
                :w (v/assert kb (list dog Rex) CxB {:strength :monotonic})
                :g (v/assert kb (list excludesType dog cat) 'CxUniverse)}]
        (place! kb #{(:l hs) (:w hs)} #{(:g hs)})
        (v/retract! kb (pick hs))
        [(placed kb) (reads/as-stored-named-global (:index kb) 'defeat)]))))

(tu/deftest-kb retracting-a-member-or-a-ground-takes-the-placed-sentexes-out
  (doseq [k [:l :w :g]]
    (is (= [#{} #{}] (retracting-takes-it-out k)) (str "retracting " k))))

(defn- placed-after
  "The placed sentexes once `ops` run in order on a fresh KB: each asserts one sentence of
  the nogood of `a-nogood-is-placed-…` over a `disjoint` ground, or the edge `(genlCx CxB
  CxA)`; the nogood is placed once its two members and its ground are stored.  The
  `disjoint` ground makes the nogood the membership family's, whose detection the edge
  reaches (`chain/place-memberships!`)."
  [ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [cat dog Rex CxA CxB CxD]
      (lattice! kb CxA CxB CxD)
      (let [hs (reduce (fn [hs op]
                         (let [hs (assoc hs op
                                         (case op
                                           :l    (v/assert kb (list cat Rex) CxA)
                                           :w    (v/assert kb (list dog Rex) CxB {:strength :monotonic})
                                           :g    (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
                                           :edge (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)))]
                           (when (and (not= :edge op) (every? hs [:l :w :g]))
                             (place! kb #{(:l hs) (:w hs)} #{(:g hs)}))
                           hs))
                       {} ops)]
        (assert (every? hs [:l :w :g :edge]))
        ;; the generated names differ per run, so the placement is read by role
        (let [names {cat 'cat dog 'dog Rex 'Rex CxA 'CxA CxB 'CxB CxD 'CxD}]
          (clojure.walk/postwalk #(get names % %) (placed kb)))))))

(tu/deftest-kb a-context-edge-arriving-after-the-nogood-places-it-as-arriving-first-does
  ;; (genlCx CxB CxA) makes CxB a common descendant of both members, above CxD
  (let [first-edge (placed-after [:edge :l :w :g])
        last-edge  (placed-after [:l :w :g :edge])]
    (is (= #{[(list 'contradicts [(list 'cat 'Rex) 'CxA] [(list 'dog 'Rex) 'CxB]) 'CxB]
             [(list 'defeat [(list 'cat 'Rex) 'CxA]) 'CxB]}
           first-edge))
    (is (= first-edge last-edge))))

(tu/deftest-kb every-arrival-order-of-the-members-the-ground-and-the-edge-places-the-same
  (is (= 1 (count (into #{} (map placed-after) (tu/orders [:l :w :g :edge]))))))

(defn- negation-placed-after
  "The placed sentexes and the counts of placed sentexes and their justifications once
  `ops` run in order on a fresh KB, over a negation pair and this lattice:

  ```
  CxUniverse
   ├─ CxA  (pp Rex)              :p
   └─ CxB  (not (pp Rex))        :n
       ├─ CxM                    :edge (genlCx CxM CxA)
       │   └─ CxL                :l    (genlCx CxL CxA)
       └─ CxS                    :s    (genlCx CxS CxA)
  ```

  With every op run the pair is placed at CxM and CxS: the edge retires the placement at
  CxL below its lower end and leaves the one at CxS, outside it."
  [ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [pp Rex CxA CxB CxM CxL CxS]
      (doseq [[c up] [[CxA 'CxUniverse] [CxB 'CxUniverse] [CxM CxB] [CxL CxM] [CxS CxB]]]
        (v/assert kb (list 'genlCx c up) 'CxUniverse))
      (doseq [op ops]
        (case op
          :p    (v/assert kb (list pp Rex) CxA)
          :n    (v/assert kb (list 'not (list pp Rex)) CxB {:strength :monotonic})
          :l    (v/assert kb (list 'genlCx CxL CxA) 'CxUniverse)
          :s    (v/assert kb (list 'genlCx CxS CxA) 'CxUniverse)
          :edge (v/assert kb (list 'genlCx CxM CxA) 'CxUniverse)))
      (let [names {pp 'pp Rex 'Rex CxA 'CxA CxB 'CxB CxM 'CxM CxL 'CxL CxS 'CxS}
            sxs   (mapcat #(v/sentexes-with-functor kb %) '[contradicts defeat])]
        [(clojure.walk/postwalk #(get names % %) (placed kb))
         (count sxs)
         (count (mapcat #(v/supporting-justifications kb (:id %)) sxs))]))))

(tu/deftest-kb a-context-edge-re-places-a-negation-pair-alike-in-every-arrival-order
  (let [readings (into #{} (map negation-placed-after) (tu/orders [:p :n :l :s :edge]))]
    (is (= #{[#{[(list 'contradicts [(list 'not (list 'pp 'Rex)) 'CxB] [(list 'pp 'Rex) 'CxA]) 'CxM]
                [(list 'defeat [(list 'pp 'Rex) 'CxA]) 'CxM]
                [(list 'contradicts [(list 'not (list 'pp 'Rex)) 'CxB] [(list 'pp 'Rex) 'CxA]) 'CxS]
                [(list 'defeat [(list 'pp 'Rex) 'CxA]) 'CxS]}
              4 4]}
           readings))))

(tu/deftest-kb a-placement-pass-counts-each-placement-it-removes-in-its-progress-total
  (let [passes (atom {})
        writes (atom 0)
        start  progress/start
        tick   progress/tick!
        place  @#'chain/place-justified!]
    (with-redefs [progress/start         (fn [id label total & more]
                                           (let [r (apply start id label total more)]
                                             (when (= ::chain/place-sets id)
                                               (reset! writes 0)
                                               (swap! passes assoc (System/identityHashCode r)
                                                      {:total total :ticked 0 :written 0}))
                                             r))
                  progress/tick!         (fn ([r] (tick r))
                                           ([r n]
                                            (when (= ::chain/place-sets (:id r))
                                              (swap! passes update (System/identityHashCode r)
                                                     #(-> % (update :ticked + n) (update :written + @writes)))
                                              (reset! writes 0))
                                            (tick r n)))
                  chain/place-justified! (fn [& args] (swap! writes inc) (apply place args))]
      (negation-placed-after [:p :n :l :s :edge]))
    (is (seq @passes))
    (is (every? (fn [{:keys [total ticked written]}] (= total ticked written)) (vals @passes))
        (str "the edge arriving last retires the placement at CxL: " (pr-str (vals @passes))))))

;; ---- the read walk -----------------------------------------------------------

(defn- self-hiding!
  "The lattice of design's self-hiding example, the nogood placed in CxD:

  ```
  CxUniverse     (excludesType dog cat)
   └─ CxA        (cat Rex)  :default      L
       └─ CxD    (dog Rex)  :monotonic    W
  ```

  Returns `{:l :w :g :d :c}`, the members, the ground, the defeat and the contradicts."
  [kb {:syms [cat dog Rex excludesType CxA CxD]}]
  (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
  (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
  (let [l (v/assert kb (list cat Rex) CxA)
        w (v/assert kb (list dog Rex) CxD {:strength :monotonic})
        g (v/assert kb (list excludesType dog cat) 'CxUniverse)]
    (place! kb #{l w} #{g})
    {:l l :w w :g g
     :d (:id (sole (filter #(= (list 'defeat (list 'sentexHandle l)) (:sentence %))
                           (v/sentexes-with-functor kb 'defeat))))
     :c (:id (sole (v/sentexes-with-functor kb 'contradicts)))}))

(tu/deftest-kb a-placed-defeat-hides-its-target-below-the-placement-and-not-above
  (tu/with-terms [cat dog Rex excludesType CxA CxD]
    (let [{:keys [l d c]} (self-hiding! kb {'cat cat 'dog dog 'Rex Rex 'excludesType excludesType
                                            'CxA CxA 'CxD CxD})]
      (testing "CxD does not believe the loser, and CxA does"
        (is (not (v/believed? kb l CxD)))
        (is (not (v/ask? kb (list cat Rex) CxD)))
        (is (v/believed? kb l CxA))
        (is (v/ask? kb (list cat Rex) CxA)))
      (testing "the defeat and the contradicts rest on the loser and stay believed at CxD"
        (is (v/believed? kb d CxD))
        (is (v/believed? kb c CxD)))
      (testing "the loser stays IN in the network"
        (is (jtms/in? (reasoning/tms kb) l)))
      (testing "the settle that placed it ran one pass"
        (is (= 1 (:passes @(reasoning/settle-stats kb))))))))

(defn- exemption-row
  "Self-hiding's nogood, with CxR below CxD asserting `(except H)` for the handle `pick`
  chooses: `[L believed at CxR, L believed at CxD, contradicts believed at CxR]`."
  [pick]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [cat dog Rex excludesType CxA CxD CxR]
      (let [hs (self-hiding! kb {'cat cat 'dog dog 'Rex Rex 'excludesType excludesType
                                 'CxA CxA 'CxD CxD})]
        (v/assert kb (list 'genlCx CxR CxD) 'CxUniverse)
        (v/assert kb (list 'except (list 'sentexHandle (pick hs))) CxR {:strength :monotonic})
        [(v/believed? kb (:l hs) CxR) (v/believed? kb (:l hs) CxD) (v/believed? kb (:c hs) CxR)]))))

(tu/deftest-kb the-exemption-table-at-a-context-below-the-placement
  (testing "excepting the winner, the ground or the defeat brings the loser back at CxR alone"
    (is (= [true false false] (exemption-row :w)))
    (is (= [true false false] (exemption-row :g)))
    (is (= [true false true] (exemption-row :d))))
  (testing "excepting the loser hides it and the nogood at CxR"
    (is (= [false false false] (exemption-row :l)))))

(tu/deftest-kb a-defeat-hides-at-read-time-and-sweeps-nothing
  ;; The rule in CxA places M there, the rule in CxD
  ;; places P at CxD, and both stay IN in the network
  (tu/with-terms [cat dog Rex excludesType meows purrs CxA CxD]
    (v/assert kb (list 'set/forwardRule (list 'implies (list cat '?x) (list meows '?x))) CxA)
    (v/assert kb (list 'set/forwardRule (list 'implies (list cat '?x) (list purrs '?x))) CxD)
    (let [{:keys [l w]} (self-hiding! kb {'cat cat 'dog dog 'Rex Rex 'excludesType excludesType
                                          'CxA CxA 'CxD CxD})
          tms (reasoning/tms kb)
          m   (v/handle-of kb (list meows Rex) CxA)
          p   (v/handle-of kb (list purrs Rex) CxD)]
      (testing "P stays IN in the network and is not believed at CxD"
        (is (jtms/in? tms p))
        (is (not (v/ask? kb (list purrs Rex) CxD))))
      (testing "M is believed at CxA and not at CxD"
        (is (v/ask? kb (list meows Rex) CxA))
        (is (not (v/ask? kb (list meows Rex) CxD))))
      (testing "retracting the winner changes no label but the placed sentexes'"
        (let [labels #(mapv (fn [h] (jtms/in? tms h)) [l m p])]
          (is (= [true true true] (labels)))
          (v/retract! kb w)
          (is (= [true true true] (labels)))
          (is (empty? (placed kb)))
          (is (v/ask? kb (list purrs Rex) CxD)))))))

(tu/deftest-kb an-except-reaching-a-member-re-reads-the-class-at-that-reader
  ;; The context shape:
  ;;   CxD   W = (dog Rex) :monotonic through X, :default through Y; L = (cat Rex) :default
  ;;    └─ CxR  (except X)
  (tu/with-terms [cat dog Rex excludesType pX pY purrs CxD CxR]
    (v/assert kb (list 'genlCx CxD 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxR CxD) 'CxUniverse)
    (v/assert kb (list 'set/forwardRule (list 'implies (list pX '?x) (list dog '?x))) CxD
              {:strength :monotonic})
    (v/assert kb (list 'set/forwardRule (list 'implies (list pY '?x) (list dog '?x))) CxD)
    (v/assert kb (list 'set/forwardRule (list 'implies (list cat '?x) (list purrs '?x))) CxD)
    (let [x (v/assert kb (list pX Rex) CxD {:strength :monotonic})
          _ (v/assert kb (list pY Rex) CxD)
          l (v/assert kb (list cat Rex) CxD)
          w (v/handle-of kb (list dog Rex) CxD)
          g (v/assert kb (list excludesType dog cat) 'CxUniverse)
          purring #(into #{} (map (juxt :sentence :context)) (v/sentexes-with-functor kb purrs))]
      (is (= :monotonic (v/defeat-class kb w)))
      (place! kb #{l w} #{g})
      (let [before (purring)]
        (v/assert kb (list 'except (list 'sentexHandle x)) CxR {:strength :monotonic})
        (testing "CxR reads W as :default, the nogood as a dilemma, and believes L"
          (is (v/believed? kb l CxR))
          (is (not (v/believed? kb l CxD))))
        (testing "a firing from L is stored as it was before the except"
          (is (= before (purring)))
          (is (seq before)))))))

(defn- swept-after
  "`[placed fired]` once `ops` run in order on a fresh KB after `(pp Rex)` is stored in CxA:
  the stored `contradicts` and `defeat` sentexes and the stored `(rr Rex)`, by role.

  ```
  CxUniverse
   ├─ CxA   P = (pp Rex) :default
   └─ CxB   (not (pp Rex)) :monotonic          :neg
            rule (pp ?x) ⇒ (rr ?x)             :fire
        CxD under both: (except P)             :except
  ```"
  [ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [pp rr Rex CxA CxB CxD]
      (lattice! kb CxA CxB CxD)
      (let [p (v/assert kb (list pp Rex) CxA)]
        (doseq [op ops]
          (case op
            :neg    (v/assert kb (list 'not (list pp Rex)) CxB {:strength :monotonic})
            :fire   (v/assert kb (list 'set/forwardRule (list 'implies (list pp '?x) (list rr '?x))) CxB)
            :except (v/assert kb (list 'except (list 'sentexHandle p)) CxD {:strength :monotonic})))
        (let [names {pp 'pp rr 'rr Rex 'Rex CxA 'CxA CxB 'CxB CxD 'CxD}]
          (clojure.walk/postwalk #(get names % %)
                                 [(placed kb)
                                  (into #{} (map (juxt :sentence :context)) (v/sentexes-with-functor kb rr))]))))))

(tu/deftest-kb a-premise-except-sweeps-a-nogood-s-placement-as-it-sweeps-a-firing-s
  (testing "with no except, the pair and the firing are placed in CxD"
    (is (= [#{[(list 'contradicts [(list 'not (list 'pp 'Rex)) 'CxB] [(list 'pp 'Rex) 'CxA]) 'CxD]
              [(list 'defeat [(list 'pp 'Rex) 'CxA]) 'CxD]}
            #{[(list 'rr 'Rex) 'CxD]}]
           (swept-after [:neg :fire]))))
  (testing "an except of the member in CxD stores neither, in every arrival order"
    (is (= #{[#{} #{}]} (into #{} (map swept-after) (tu/orders [:neg :fire :except]))))))

(defn- closure-swept-after
  "`[with-except after-retract]` once `ops` run in order on a fresh KB after `P = (pp Rex)`
  is stored in CxA, the except asserted by `:except` and retracted last: each the kinds
  of sentex IN in the network at CxD, among `contradicts`, `defeat` and `(rr Rex)`.

  ```
  CxUniverse
   ├─ CxA   P = (pp Rex)   rule (pp ?x) ⇒ (qq ?x)          :rule
   └─ CxB   (not (qq Rex)) :monotonic                       :neg
            rule (qq ?x) ⇒ (rr ?x)                          :fire
        CxD under both: (except P)                          :except
  ```"
  [ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [pp qq rr Rex CxA CxB CxD]
      (lattice! kb CxA CxB CxD)
      (let [p   (v/assert kb (list pp Rex) CxA)
            e   (volatile! nil)
            tms (reasoning/tms kb)
            at  (fn [] (into #{} (for [f ['contradicts 'defeat rr]
                                       s (v/sentexes-with-functor kb f)
                                       :when (and (= CxD (:context s)) (jtms/in? tms (:id s)))]
                                   (if (= rr f) 'rr f))))]
        (doseq [op ops]
          (case op
            :rule   (v/assert kb (list 'set/forwardRule (list 'implies (list pp '?x) (list qq '?x))) CxA)
            :neg    (v/assert kb (list 'not (list qq Rex)) CxB {:strength :monotonic})
            :fire   (v/assert kb (list 'set/forwardRule (list 'implies (list qq '?x) (list rr '?x))) CxB)
            :except (vreset! e (v/assert kb (list 'except (list 'sentexHandle p)) CxD {:strength :monotonic}))))
        (let [with (at)]
          (v/retract! kb @e)
          [with (at)])))))

(tu/deftest-kb an-except-sweeps-what-rests-on-its-target-and-retracting-it-restores-it
  (is (= #{[#{} #{'contradicts 'defeat 'rr}]}
         (into #{} (map closure-swept-after) (tu/orders [:rule :neg :fire :except])))
      "nothing resting on P stays at CxD in any order, and every placement comes back"))

(defn- grounded-reading
  "Two decided nogoods, one defeating the other's dependency: nogood N1 grounded on G, and
  nogood N2 with G its unique weakest member.
  `ops` asserts the sentences in order, each nogood placed once its sentences are stored.
  Answers `[G believed, (kitten Rex) believed]` at CxA.

  ```
  CxA  G = (subKind kitten cat) :default    H = (fixedKind kitten) :monotonic
       (dog Rex) :monotonic                 (kitten Rex) :default
  N2 = {G, H}, ground (excludesFact subKind fixedKind)
  N1 = {(dog Rex), (kitten Rex)}, grounds G and (excludesType dog cat)
  ```"
  [ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [cat dog kitten Rex subKind fixed_kind excludesType excludesFact CxA]
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (let [g1 (v/assert kb (list excludesType dog cat) 'CxUniverse)
            g2 (v/assert kb (list excludesFact subKind fixed_kind) 'CxUniverse)
            hs (reduce (fn [hs op]
                         (let [hs (assoc hs op
                                         (case op
                                           :G  (v/assert kb (list subKind kitten cat) CxA)
                                           :H  (v/assert kb (list fixed_kind kitten) CxA {:strength :monotonic})
                                           :M1 (v/assert kb (list dog Rex) CxA {:strength :monotonic})
                                           :M2 (v/assert kb (list kitten Rex) CxA)))]
                           (when (and (#{:G :H} op) (every? hs [:G :H]))
                             (place! kb #{(:G hs) (:H hs)} #{g2}))
                           (when (and (#{:G :M1 :M2} op) (every? hs [:G :M1 :M2]))
                             (place! kb #{(:M1 hs) (:M2 hs)} #{(:G hs) g1}))
                           hs))
                       {} ops)]
        [(v/believed? kb (:G hs) CxA) (v/believed? kb (:M2 hs) CxA)]))))

(tu/deftest-kb a-defeat-resting-on-a-defeated-ground-gives-one-reading-in-every-order
  ;; A depth-two shape: N2 defeats N1's ground, N1 does not reach N2, and N1's defeat is
  ;; not in force.  The mutual case, each nogood's loser a dependency of the other through
  ;; a rule-derived ground, is `a-defeat-dependency-cycle-is-broken-in-content-order`.
  (is (= #{[false true]} (into #{} (map grounded-reading) (tu/orders [:G :H :M1 :M2])))))

(tu/deftest-kb why-not-names-the-placed-defeat
  ;;   CxD   (cat Rex) :default and (dog Rex) :monotonic, the nogood placed in CxD
  (tu/with-terms [cat dog Rex excludesType CxD]
    (v/assert kb (list 'genlCx CxD 'CxUniverse) 'CxUniverse)
    (let [l (v/assert kb (list cat Rex) CxD)
          w (v/assert kb (list dog Rex) CxD {:strength :monotonic})
          g (v/assert kb (list excludesType dog cat) 'CxUniverse)]
      (place! kb #{l w} #{g})
      (let [d (:id (sole (v/sentexes-with-functor kb 'defeat)))
            r (v/why-not kb l)]
        (is (= :defeated (:reason r)))
        (is (= [d] (:defeats r)))
        (is (= [w] (mapv :handle (:contradicted-by r))))))))

(tu/deftest-kb a-placed-defeat-requeues-the-guards-watching-its-target
  ;; `(unknown (cat Rex))` holds at CxD once the defeat hides L there
  (tu/with-terms [cat dog Rex excludesType barks CxA CxD]
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list 'and (list dog '?x) (list 'unknown (list cat '?x)))
                             (list barks '?x)))
              CxD)
    (self-hiding! kb {'cat cat 'dog dog 'Rex Rex 'excludesType excludesType 'CxA CxA 'CxD CxD})
    (is (v/ask? kb (list barks Rex) CxD))))

(tu/deftest-kb an-except-moving-a-defeat-s-force-requeues-the-guards-watching-its-target
  ;;   CxA  (cat Rex) default        CxD under CxA  (not (cat Rex)) monotonic
  ;;   CxR under CxD  (pp ?x) & (unknown (cat ?x)) => (rr ?x),  (pp Rex)
  ;; The pair's defeat hides (cat Rex) at CxR, so (rr Rex) is concluded there.  An except
  ;; of the denial in CxR takes the defeat out of force there, which moves the target's
  ;; belief with no relabel of it, and the guard is decided again.
  (tu/with-terms [cat pp rr Rex CxA CxD CxR]
    (doseq [[c up] [[CxA 'CxUniverse] [CxD CxA] [CxR CxD]]]
      (v/assert kb (list 'genlCx c up) 'CxUniverse))
    (let [l (v/assert kb (list cat Rex) CxA)
          w (v/assert kb (list 'not (list cat Rex)) CxD {:strength :monotonic})]
      (v/assert kb (list 'set/forwardRule
                         (list 'implies (list 'and (list pp '?x) (list 'unknown (list cat '?x)))
                               (list rr '?x)))
                CxR)
      (v/assert kb (list pp Rex) CxR)
      (is (v/ask? kb (list rr Rex) CxR) "the defeat hides the target, so the guard holds")
      (let [e (v/assert kb (list 'except (list 'sentexHandle w)) CxR)]
        (is (v/believed? kb l CxR) "the except takes the defeat out of force at CxR")
        (is (not (v/ask? kb (list rr Rex) CxR)) "and the guard is decided again")
        (v/retract! kb e)
        (is (v/ask? kb (list rr Rex) CxR) "retracting the except restores the conclusion")))))

(defn- guarded-rule
  "The rule `pp ⇒ rr` guarded by `(cat ?x)`, as an `(unknown …)` antecedent (`:unknown`)
  or as an `exceptWhen` exception (`:except`)."
  [arm pp cat rr]
  (case arm
    :unknown (list 'set/forwardRule
                   (list 'implies (list 'and (list pp '?x) (list 'unknown (list cat '?x)))
                         (list rr '?x)))
    :except  (list 'exceptWhen (list cat '?x)
                   (list 'set/forwardRule (list 'implies (list pp '?x) (list rr '?x))))))

(defn- guard-through-a-defeated-edge
  "`[rr believed? (cat Rex) believed?]` at CxA after the writes `ops`, in order.

  ```
  CxA  (disjoint dog cat) M   (poodle Rex) M   (pp Rex)
       E = (genl poodle dog) :default          L = (cat Rex) :default     (:edge, :cat)
       (not (genl poodle dog)) M                                         (:neg)
       the guarded rule pp ⇒ rr, guarded by (cat ?x)                     (:rule)
  ```

  The membership nogood {(poodle Rex), L} climbs E and places D_M, the defeat of L, resting
  on E.  The negation pair on E places D_E, the defeat of E.  D_E takes D_M out of force,
  so L is believed and the guard holds."
  [arm ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [cat dog poodle pp rr Rex CxA]
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'disjoint dog cat) CxA {:strength :monotonic})
      (v/assert kb (list poodle Rex) CxA {:strength :monotonic})
      (v/assert kb (list pp Rex) CxA)
      (let [l (reduce (fn [l op]
                        (case op
                          :edge (do (v/assert kb (list 'genl poodle dog) CxA) l)
                          :neg  (do (v/assert kb (list 'not (list 'genl poodle dog)) CxA
                                              {:strength :monotonic})
                                    l)
                          :cat  (v/assert kb (list cat Rex) CxA)
                          :rule (do (v/assert kb (guarded-rule arm pp cat rr) CxA) l)))
                      nil ops)]
        [(v/ask? kb (list rr Rex) CxA) (v/believed? kb l CxA)]))))

(tu/deftest-kb a-defeat-taking-another-defeat-out-of-force-requeues-the-guards-watching-its-target
  (doseq [arm [:unknown :except]]
    (testing (name arm)
      (is (= #{[false true]}
             (into #{} (map #(guard-through-a-defeated-edge arm %))
                   (tu/orders [:edge :neg :cat :rule])))))))

(tu/deftest-kb an-except-lowering-a-nogood-member-s-class-requeues-the-guards-watching-the-loser
  ;;   CxD  (disjoint dog cat) M   X = (xx Rex) M   Y = (yy Rex) :default
  ;;        (xx ?a) => (dog ?a) M   (yy ?a) => (dog ?a) M   L = (cat Rex) :default
  ;;        W = (dog Rex): :monotonic through X, :default through Y; D defeats L, rests on W
  ;;   CxR under CxD   the guarded rule pp => rr,  (pp Rex)
  ;; An except of X in CxR leaves W :default there, so the nogood is a dilemma at CxR and L
  ;; is believed there (design section C).  D rests on X only through W.
  (doseq [arm [:unknown :except]]
    (testing (name arm)
      (tu/with-neutral-kb [kb tu/fresh]
        (tu/with-terms [cat dog xx yy pp rr Rex CxD CxR]
          (v/assert kb (list 'genlCx CxD 'CxUniverse) 'CxUniverse)
          (v/assert kb (list 'genlCx CxR CxD) 'CxUniverse)
          (v/assert kb (list 'disjoint dog cat) CxD {:strength :monotonic})
          (doseq [p [xx yy]]
            (v/assert kb (list 'set/forwardRule (list 'implies (list p '?a) (list dog '?a))) CxD
                      {:strength :monotonic}))
          (let [x (v/assert kb (list xx Rex) CxD {:strength :monotonic})
                _ (v/assert kb (list yy Rex) CxD)
                l (v/assert kb (list cat Rex) CxD)]
            (v/assert kb (guarded-rule arm pp cat rr) CxR)
            (v/assert kb (list pp Rex) CxR)
            (is (= [false true] [(v/believed? kb l CxR) (v/ask? kb (list rr Rex) CxR)])
                "D hides L at CxR, so the guard does not hold")
            (let [e (v/assert kb (list 'except (list 'sentexHandle x)) CxR)]
              (is (= [true false] [(v/believed? kb l CxR) (v/ask? kb (list rr Rex) CxR)])
                  "the except leaves D out of force at CxR, and the guard is decided again")
              (v/retract! kb e)
              (is (= [false true] [(v/believed? kb l CxR) (v/ask? kb (list rr Rex) CxR)])
                  "retracting the except gives the firing back"))))))))

(defn- guard-through-a-lowering-except
  "`[rr at CxD, rr at CxR, rr at CxR once the except is retracted]` after the writes `ops`,
  in order, with the members' side stated in `wctx` (`:a` or `:d`), and the except naming
  X (`target` `:x`) or the disjointness (`:ground`).

  ```
  CxA                (disjoint dog cat) M   Y = (yy Rex) :default
                     (xx ?a) => (dog ?a) M   (yy ?a) => (dog ?a) M
                     X = (xx Rex) M                                         (:x)
                     W = (dog Rex): :monotonic through X, :default through Y
   └─ CxD            L = (cat Rex) :default; D defeats L, resting on W      (:cat)
                     (pp Rex)                                               (:pp)
                     the guarded rule pp => rr, guarded by (cat ?x)        (:g)
       └─ CxR        (except X)                                             (:except)
  ```

  With `wctx` `:d` every CxA line is stated in CxD.  At CxD, D hides L, so the firing
  F = (rr Rex) is placed at CxD.  At CxR the except leaves W :default, the nogood is a
  dilemma there, L is believed, and the guard holds.  An except of the
  disjointness hides D's ground at CxR, with the same reading."
  [arm wctx target ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [cat dog xx yy pp rr Rex CxA CxD CxR]
      (let [w ({:a CxA :d CxD} wctx)]
        (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
        (v/assert kb (list 'genlCx CxD CxA) 'CxUniverse)
        (v/assert kb (list 'genlCx CxR CxD) 'CxUniverse)
        (let [g (v/assert kb (list 'disjoint dog cat) w {:strength :monotonic})
              _ (doseq [p [xx yy]]
                  (v/assert kb (list 'set/forwardRule (list 'implies (list p '?a) (list dog '?a))) w
                            {:strength :monotonic}))
              _ (v/assert kb (list yy Rex) w)
              [_ e] (reduce (fn [[x e] op]
                              (case op
                                :x      [(v/assert kb (list xx Rex) w {:strength :monotonic}) e]
                                :pp     (do (v/assert kb (list pp Rex) CxD) [x e])
                                :g      (do (v/assert kb (guarded-rule arm pp cat rr) CxD
                                                      {:strength :monotonic})
                                            [x e])
                                :cat    (do (v/assert kb (list cat Rex) CxD) [x e])
                                :except [x (v/assert kb (list 'except (list 'sentexHandle ({:x x :ground g} target)))
                                                     CxR)]))
                            [nil nil] ops)
              read  [(v/ask? kb (list rr Rex) CxD) (v/ask? kb (list rr Rex) CxR)]]
          (v/retract! kb e)
          (conj read (v/ask? kb (list rr Rex) CxR)))))))

(def ^:private lowering-except-orders
  ;; every order of the four writes, the except right after X and last
  (into [] (comp (mapcat (fn [ops] (let [[pre post] (split-with #(not= :x %) ops)]
                                     [(concat ops [:except]) (concat pre [:x :except] (rest post))])))
                 (distinct))
        (tu/orders [:x :pp :g :cat])))

(defn- lowering-except-readings [target orders]
  (doseq [arm [:unknown :except], wctx [:a :d]]
    (testing [arm wctx]
      (is (= #{[true false true]}
             (into #{} (map #(guard-through-a-lowering-except arm wctx target %)) orders))))))

(tu/deftest-kb ^:slow a-guard-holding-below-through-a-lowering-except-places-its-defeat-at-the-except
  (lowering-except-readings :x lowering-except-orders))

(tu/deftest-kb sampled-orders-place-a-guard-defeat-at-a-lowering-except
  ;; The sampled twin: every seventh order, the except last and right after X among them.
  (lowering-except-readings :x (take-nth 7 lowering-except-orders)))

(tu/deftest-kb a-guard-holding-below-through-an-except-of-the-ground-places-its-defeat-at-the-except
  (lowering-except-readings :ground (take-nth 7 lowering-except-orders)))

(defn- guard-through-a-ground-defeated-below
  "`[rr at CxD, rr at CxR, rr at CxR once the denial is retracted]` after the writes
  `ops`, in order.

  ```
  CxD          (disjoint dog cat) M   (poodle Rex) M   (pp Rex)
               E = (genl poodle dog) :default                              (:edge)
               L = (cat Rex) :default; D_M defeats L, resting on E         (:cat)
               the guarded rule pp => rr, guarded by (cat ?x)             (:rule)
   └─ CxR      (not (genl poodle dog)) M; D_E defeats E at CxR             (:neg)
  ```

  At CxD, D_M hides L, so the firing F = (rr Rex) is placed at CxD.  At CxR, D_E hides E,
  D_M rests on E and is out of force there, L is believed, and the guard holds."
  [arm ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [cat dog poodle pp rr Rex CxD CxR]
      (v/assert kb (list 'genlCx CxD 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxR CxD) 'CxUniverse)
      (v/assert kb (list 'disjoint dog cat) CxD {:strength :monotonic})
      (v/assert kb (list poodle Rex) CxD {:strength :monotonic})
      (v/assert kb (list pp Rex) CxD)
      (let [n    (reduce (fn [n op]
                           (case op
                             :edge (do (v/assert kb (list 'genl poodle dog) CxD) n)
                             :neg  (v/assert kb (list 'not (list 'genl poodle dog)) CxR
                                             {:strength :monotonic})
                             :cat  (do (v/assert kb (list cat Rex) CxD) n)
                             :rule (do (v/assert kb (guarded-rule arm pp cat rr) CxD) n)))
                         nil ops)
            read [(v/ask? kb (list rr Rex) CxD) (v/ask? kb (list rr Rex) CxR)]]
        (v/retract! kb n)
        (conj read (v/ask? kb (list rr Rex) CxR))))))

(tu/deftest-kb a-guard-holding-below-through-a-defeat-of-the-ground-places-its-defeat-at-that-defeat
  (doseq [arm [:unknown :except]]
    (testing (name arm)
      (is (= #{[true false true]}
             (into #{} (map #(guard-through-a-ground-defeated-below arm %))
                   (tu/orders [:edge :neg :cat :rule])))))))

(defn- breed-cycle
  "The reading of the defeat-dependency cycle after the writes `ops`, in order:
  `[L1 L2 G1 G2]` believed at CxA, each asked alone, then L1 and L2 hidden at CxA in one
  read asking L1 first, and in one read asking L2 first.  When `ops` holds `:ex`, `:r`
  and `:s` are the same three readings at CxR and CxS.

  ```
  CxA  (disjoint dog cat) M   (disjoint bird fish) M   (poodle Rex) M   (sparrow Tweety) M
       (dog_breed poodle) M   (bird_breed sparrow) M
       L1 = (cat Rex) :default                                                  (:l1)
       L2 = (fish Tweety) :default                                              (:l2)
       R1 = (fish ?x) & (dog_breed ?t) => (genl ?t dog)                         (:r1)
       R2 = (cat ?x) & (bird_breed ?t) => (genl ?t bird)                        (:r2)
  CxR under CxA   (except G), G the ground of the defeat whose loser is first,
                  written at its position or once G is stored                   (:ex)
  CxS under CxA, beside CxR
  G1 = (genl poodle dog) from R1 over L2;  G2 = (genl sparrow bird) from R2 over L1
  D1 defeats L1 and rests on G1;  D2 defeats L2 and rests on G2
  ```"
  [ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [cat dog fish bird poodle sparrow dog_breed bird_breed Rex Tweety CxA CxR CxS]
      (doseq [[c up] [[CxA 'CxUniverse] [CxR CxA] [CxS CxA]]]
        (v/assert kb (list 'genlCx c up) 'CxUniverse))
      (doseq [s [(list 'disjoint dog cat) (list 'disjoint bird fish) (list poodle Rex)
                 (list sparrow Tweety) (list dog_breed poodle) (list bird_breed sparrow)]]
        (v/assert kb s CxA {:strength :monotonic}))
      (let [first (if (neg? (nm/compare-form [(list cat Rex) CxA] [(list fish Tweety) CxA])) :l1 :l2)
            rule  (fn [lit breed sup]
                    (list 'set/forwardRule
                          (list 'implies (list 'and (list lit '?x) (list breed '?t)) (list 'genl '?t sup))))
            g1s   (list 'genl poodle dog)
            g2s   (list 'genl sparrow bird)
            write (fn [op]
                    (case op
                      :l1 (v/assert kb (list cat Rex) CxA)
                      :l2 (v/assert kb (list fish Tweety) CxA)
                      :r1 (v/assert kb (rule fish dog_breed dog) CxA {:strength :monotonic})
                      :r2 (v/assert kb (rule cat bird_breed bird) CxA {:strength :monotonic})
                      :ex nil))
            except (fn [hs]
                     (let [g (v/handle-of kb (if (= :l1 first) g1s g2s) CxA)]
                       (if (and g (contains? hs :ex) (nil? (:ex hs)))
                         (assoc hs :ex (v/assert kb (list 'except (list 'sentexHandle g)) CxR))
                         hs)))
            hs    (reduce (fn [hs op] (except (assoc hs op (write op)))) {} ops)
            l1    (:l1 hs) l2 (:l2 hs)
            g1    (v/handle-of kb g1s CxA)
            g2    (v/handle-of kb g2s CxA)
            read  (fn [ctx hs] (let [hid (exc/defeat-hidden-fn kb ctx false)] (mapv #(boolean (hid %)) hs)))
            at    (fn [ctx] {:alone (mapv #(v/believed? kb % ctx) [l1 l2 g1 g2])
                             :l1-l2 (read ctx [l1 l2])
                             :l2-l1 (vec (rseq (read ctx [l2 l1])))})]
        (cond-> (assoc (at CxA) :first first)
          (:ex hs) (assoc :r (at CxR) :s (at CxS)))))))

(tu/deftest-kb a-defeat-dependency-cycle-is-broken-in-content-order
  ;; Each defeat rests, through a rule-derived :default type edge, on the other's loser.
  ;; The defeat whose loser is first in content order is in force:
  ;; its loser and the edge resting on it are hidden, and the other loser is believed.
  (let [readings (into #{} (map breed-cycle) (tu/orders [:l1 :l2 :r1 :r2]))
        {:keys [first]} (clojure.core/first readings)
        hidden   (if (= :l1 first) [true false] [false true])]
    (is (= #{{:first first
              :alone (if (= :l1 first) [false true true false] [true false false true])
              :l1-l2 hidden
              :l2-l1 hidden}}
           readings))))

(defn- excepted-cycle-readings
  "The except at CxR hides the first defeat's ground there, so that defeat is out of force
  at CxR for a reason outside the cycle, while the second defeat's ground and verdict
  stand: CxR reads the second in force.  CxA and CxS see no except and read the
  content-order answer."
  [orders]
  (let [readings (into #{} (map breed-cycle) orders)
        {:keys [first]} (clojure.core/first readings)
        expected (if (= :l1 first)
                   {:alone [false true true false] :l1-l2 [true false] :l2-l1 [true false]}
                   {:alone [true false false true] :l1-l2 [false true] :l2-l1 [false true]})
        excepted (if (= :l1 first)
                   {:alone [true false false true] :l1-l2 [false true] :l2-l1 [false true]}
                   {:alone [false true true false] :l1-l2 [true false] :l2-l1 [true false]})]
    (is (= #{(assoc expected :first first :r excepted :s expected)} readings))))

(tu/deftest-kb ^:slow a-cycle-whose-first-defeat-is-out-of-force-at-a-reader-puts-the-second-in-force-there
  (excepted-cycle-readings (tu/orders [:l1 :l2 :r1 :r2 :ex])))

(tu/deftest-kb sampled-orders-put-the-second-defeat-of-a-cycle-in-force-where-the-first-is-excepted
  ;; The sampled twin: every twelfth of the 120 orders.
  (excepted-cycle-readings (take-nth 12 (tu/orders [:l1 :l2 :r1 :r2 :ex]))))

(defn- ground-cycle
  "`{:first … :read [W G L]}`: which of G and L is first in content order, and W, G and L
  believed at L's context, after the writes `ops`, in order.  The ground G of the
  membership nogood over W and L is derived by a rule guarded by L (`:guard` and `:own`,
  with `arm` `:unknown` or `:except`), or by a rule over L (`:self`).

  ```
  CxA  (disjoint dog cat) M   W = (poodle Rex) M   (dog_breed poodle) M        (:w, :breed)
       :guard  (dog_breed ?t) & (poodle ?x) => (genl ?t dog), guarded by (cat ?x)  (:rule)
       :self   (dog_breed ?t) & (cat ?x) => (genl ?t dog)                          (:rule)
  CxB under CxA   L = (cat Rex) :default, in CxA under :own                        (:l)
  G = (genl poodle dog).  D defeats L at L's context and rests on G; under :guard and
  :own the guard defeat of G at L's context rests on L, and under :self G rests on L.
  ```"
  [shape arm ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [cat dog poodle dog_breed Rex CxA CxB]
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)
      (v/assert kb (list 'disjoint dog cat) CxA {:strength :monotonic})
      (let [conc (list 'genl '?t dog)
            lctx (if (= :own shape) CxA CxB)
            rule (case [(if (= :own shape) :guard shape) arm]
                   [:self nil]       (list 'set/forwardRule
                                           (list 'implies (list 'and (list dog_breed '?t) (list cat '?x)) conc))
                   [:guard :unknown] (list 'set/forwardRule
                                           (list 'implies (list 'and (list dog_breed '?t) (list poodle '?x)
                                                                (list 'unknown (list cat '?x)))
                                                 conc))
                   [:guard :except]  (list 'exceptWhen (list cat '?x)
                                           (list 'set/forwardRule
                                                 (list 'implies (list 'and (list dog_breed '?t) (list poodle '?x))
                                                       conc))))
            hs   (into {} (map (fn [op]
                                 [op (case op
                                       :w     (v/assert kb (list poodle Rex) CxA {:strength :monotonic})
                                       :breed (v/assert kb (list dog_breed poodle) CxA {:strength :monotonic})
                                       :rule  (v/assert kb rule CxA {:strength :monotonic})
                                       :l     (v/assert kb (list cat Rex) lctx))]))
                       ops)
            g    (v/handle-of kb (list 'genl poodle dog) CxA)]
        {:first (if (neg? (nm/compare-form [(list 'genl poodle dog) CxA] [(list cat Rex) lctx])) :g :l)
         :read  (mapv #(boolean (and % (v/believed? kb % lctx))) [(:w hs) g (:l hs)])}))))

(tu/deftest-kb a-guard-defeat-and-a-nogood-defeat-resting-on-each-other-are-broken-in-content-order
  ;; The guard defeat of G rests on its blocker L, and the defeat of L rests on G.  The one
  ;; whose target is first in content order is in force at CxB, and the other is not.
  (doseq [arm [:unknown :except]]
    (testing (name arm)
      (let [readings (into #{} (map #(ground-cycle :guard arm %)) (tu/orders [:w :breed :rule :l]))
            first    (:first (clojure.core/first readings))]
        (is (= #{{:first first :read (if (= :g first) [true false true] [true true false])}}
               readings))))))

(tu/deftest-kb a-guard-at-the-firings-own-placement-and-a-nogood-defeat-resting-on-each-other-are-broken-in-content-order
  ;; L is stated where G is placed, so the guard holds at G's own placement.  L is
  ;; `:default`, so G is stored with a guard defeat at CxA resting on L, and the
  ;; walk breaks the cycle in content order in every arrival order, as it
  ;; does for the two-context shape.
  (doseq [arm [:unknown :except]]
    (testing (name arm)
      (let [readings (into #{} (map #(ground-cycle :own arm %)) (tu/orders [:w :breed :rule :l]))
            first    (:first (clojure.core/first readings))]
        (is (= #{{:first first :read (if (= :g first) [true false true] [true true false])}}
               readings))))))

(defn- loser-under-a-guarded-firing
  "`[A B C]` believed at CxA after the writes `ops`, in order.

  ```
  CxA  N = (not (tyb IndB)) M   C = (tyc IndB)   A = (tya IndB)         (:n :c :a)
       (tyb ?x) & (unknown (tyc ?x)) => (tya ?x) M                     (:guarded)
       (tya ?x) => (tyb ?x)                                            (:rule)
  ```
  The rule derives B = (tyb IndB) from A, and the nogood {N, B} places a defeat of B.
  The guarded rule fires from B to A, and C blocks the firing, so the guard defeat of A
  rests on B.  A sorts before B, so a cycle broken in content order would put the guard
  defeat in force and the defeat of B out of force."
  [ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [tya tyb tyc IndB CxA]
      (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse)
      (let [hs (into {} (map (fn [op]
                               [op (case op
                                     :n       (v/assert kb (list 'not (list tyb IndB)) CxA {:strength :monotonic})
                                     :c       (v/assert kb (list tyc IndB) CxA)
                                     :a       (v/assert kb (list tya IndB) CxA)
                                     :guarded (v/assert kb (list 'set/forwardRule
                                                                 (list 'implies (list 'and (list tyb '?x)
                                                                                      (list 'unknown (list tyc '?x)))
                                                                       (list tya '?x)))
                                                        CxA {:strength :monotonic})
                                     :rule    (v/assert kb (list 'set/forwardRule
                                                                 (list 'implies (list tya '?x) (list tyb '?x)))
                                                        CxA))]))
                     ops)
            b  (v/handle-of kb (list tyb IndB) CxA)]
        (mapv #(boolean (and % (v/believed? kb % CxA))) [(:a hs) b (:c hs)])))))

(tu/deftest-kb a-nogood-loser-a-guarded-firing-rests-on-is-hidden-in-every-order
  ;; The guard defeat's force reads its blocker C and not the firing's antecedent B, so
  ;; the two defeats form no cycle and N wins over B.
  (is (= #{[true false true]}
         (into #{} (map loser-under-a-guarded-firing) (tu/orders [:n :c :a :guarded :rule])))))

(defn- loser-beside-an-unguarded-copy
  "`[(tya IndB) (tyc IndB)]` believed at CxC, on any handle CxC sees, after the writes
  `ops`, in order.

  ```
  CxA  (disjoint tya tyb) M   R = (tyb ?x) => (tya ?x) M                  (:rule)
  CxB ⊂ CxA   (tyb IndB) M                                                (:b)
              (exceptWhen (tyc ?x) R), which stores a guarded copy of R   (:guard)
  CxC ⊂ CxB   (genl tyc tyb)   (tyc IndB)                                (:genl :c)
              (tyd IndZ) and an except of it                             (:except)
  ```
  A = (tya IndB) at CxB rests on R's firing and on its guarded copy's.  The guard defeat
  of the copy's firing at CxC rests on (tyc IndB), and the defeat of (tyc IndB) from the
  nogood over A rests on A, so a read meets both.  R's firing holds A whatever the guard,
  so (tyc IndB) loses at CxC.  The except hides nothing the nogood reads; it makes the
  read walk the supports in full."
  [ops]
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [tya tyb tyc tyd IndB IndZ CxA CxB CxC]
      (let [M    {:strength :monotonic}
            rule (list 'set/forwardRule (list 'implies (list tyb '?x) (list tya '?x)))]
        (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse M)
        (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse M)
        (v/assert kb (list 'genlCx CxC CxB) 'CxUniverse M)
        (v/assert kb (list 'disjoint tya tyb) CxA M)
        (doseq [op ops]
          (case op
            :rule   (v/assert kb rule CxA M)
            :b      (v/assert kb (list tyb IndB) CxB M)
            :guard  (v/assert kb (list 'exceptWhen (list tyc '?x) rule) CxB)
            :genl   (v/assert kb (list 'genl tyc tyb) CxC)
            :c      (v/assert kb (list tyc IndB) CxC)
            :except (let [z (v/assert kb (list tyd IndZ) CxC)]
                      (v/assert kb (list 'except (list 'sentexHandle z)) CxC))))
        (mapv (fn [s] (boolean (some (fn [h] (let [sx (v/sentex kb h)]
                                               (and (= s (v/sentence-of sx)) (v/sees? kb CxC (:context sx))
                                                    (v/believed? kb h CxC))))
                                     (v/handles kb))))
              [(list tya IndB) (list tyc IndB)])))))

(tu/deftest-kb a-defeat-held-by-an-unguarded-firing-is-in-force-beside-a-guard-defeat
  ;; The cycle the read meets has one consistent reading: the defeat of (tyc IndB) in
  ;; force.  Every fifth of the 720 orders.
  (is (= #{[true false]}
         (into #{} (map loser-beside-an-unguarded-copy)
               (take-nth 5 (tu/orders [:rule :b :guard :genl :c :except]))))))

(tu/deftest-kb a-defeat-resting-on-its-own-target-through-a-ground-is-in-force
  ;; G rests on L, so the defeat of L rests on L through G as well as directly.  The cycle
  ;; holds one defeat, which is first in content order, so it is in force at CxB: L is
  ;; hidden there, and G with it.
  (is (= #{{:read [true false false]}}
         (into #{} (map #(dissoc (ground-cycle :self nil %) :first)) (tu/orders [:w :breed :rule :l])))))

;; ---- a cycle closed from every entry ------------------------------------------------

(tu/deftest-kb a-cycle-resting-on-an-outer-open-defeat-is-closed-with-it-from-every-entry
  ;; Three conflict keys over six facts, with stub reads: O = A, A = not B, B = A and not
  ;; O, so that B reads O only once A is held true.  The one consistent reading is O and
  ;; A in force and B out.  The reading is the same entered at any key, and a key read
  ;; first and then each of the others after it.
  (tu/with-terms [w_kind Ia Ib Ic Id Ie If]
    (let [in-force-once @#'exc/in-force-once
          ;; losers in content order: A's (Ib), B's (Id), O's (If)
          [h1 h2 h3 h4 h5 h6] (map #(v/assert kb (list w_kind %) 'CxUniverse) [Ie If Ia Ib Ic Id])
          ck   (fn [c x] [:vaelii.impl.except/conflict c x])
          [o a b :as ks] [(ck h1 h2) (ck h3 h4) (ck h5 h6)]
          reading (fn [entry]
                    (let [st (volatile! {})
                          s  {:memo st :recs (:records kb)}
                          fs (atom {})
                          r  (fn [k] (in-force-once s k (@fs k)))]
                      (reset! fs {o (fn [] (r a))
                                  a (fn [] (not (r b)))
                                  b (fn [] (and (r a) (not (r o))))})
                      (r entry)
                      (mapv r ks)))]
      (is (= {o [true true false] a [true true false] b [true true false]}
             (into {} (for [e ks] [e (reading e)])))))))

(tu/deftest-kb a-cycle-reads-its-first-consistent-assignment-from-every-entry-and-order
  ;; Conflict keys with stub reads, the losers in content order k0 < k1 < k2 < k3.  In the
  ;; first row k0 = not k1 and not k2: a read of k0 that finds k1 in force stops before k2,
  ;; so k2 joins the cycle inside its close.  In the second, k2 and k3 close as a cycle of
  ;; their own when the read opens them below k0 or k1.  Each row has two consistent
  ;; readings, and every order of first reads takes the first in content order, in force
  ;; first.
  (tu/with-terms [w_kind Ia Ib Ic Id Ie If Ig Ih]
    (let [in-force-once @#'exc/in-force-once
          hs      (mapv #(v/assert kb (list w_kind %) 'CxUniverse) [Ia Ib Ic Id Ie If Ig Ih])
          ks      (mapv (fn [i] [:vaelii.impl.except/conflict (hs (* 2 i)) (hs (inc (* 2 i)))]) (range 4))
          reading (fn [forms order]
                    (let [s {:memo (volatile! {}) :recs (:records kb)}
                          r (fn r [i] (in-force-once s (ks i) #((forms i) r)))]
                      (run! r order)
                      (mapv r (range (count forms)))))]
      (doseq [[forms expected]
              [[[#(and (not (% 1)) (not (% 2))) #(not (% 0)) #(not (% 0))]
                [true false false]]
               [[#(not (% 1)) #(and (not (% 3)) (or (not (% 0)) (not (% 2))))
                 #(or (not (% 3)) (not (% 1))) #(and (not (% 2)) (not (% 0)))]
                [true false true false]]]]
        (is (= #{expected}
               (into #{} (map #(reading forms %)) (tu/orders (range (count forms))))))))))

(tu/deftest-kb a-cycle-nested-in-a-members-read-is-closed-once-per-read
  ;; Conflict keys with stub reads: d rings of m members, member i of ring l out of force
  ;; when member i + 1 is in force, and reading ring l + 1 only when members i + 1 and
  ;; i + 2 are both in force, so discovery closes ring l without ring l + 1 and each
  ;; assignment of ring l's close reads ring l + 1 again.  Ring l + 1 rests on no member of
  ;; ring l, so its close is kept: the member reads are at most d rings of 2^m
  ;; assignments of m reads, 2m + 1 passes of m reads when m is odd and no assignment is
  ;; consistent, and m + 1 other reads of each member, where reading ring l + 1 once per
  ;; assignment of every ring above it multiplies them.
  (tu/with-terms [w_kind]
    (doseq [[d m] [[3 4] [2 6] [3 3] [2 5]]]
      (let [in-force-once @#'exc/in-force-once
            hs    (mapv (fn [_] (v/assert kb (list w_kind (tu/tmp-ind "Ring")) 'CxUniverse))
                        (range (* 2 d m)))
            ck    (fn [l i] (let [j (* 2 (+ (* l m) i))] [:vaelii.impl.except/conflict (hs j) (hs (inc j))]))
            reads (atom 0)
            s     {:memo (volatile! {}) :recs (:records kb)}
            r     (fn r [l i]
                    (in-force-once s (ck l i)
                                   (fn []
                                     (swap! reads inc)
                                     (let [nxt (r l (mod (inc i) m))
                                           b   (r l (mod (+ i 2) m))]
                                       (when (and nxt b (< l (dec d))) (r (inc l) 0))
                                       (not nxt)))))]
        (r 0 0)
        (is (<= @reads (* d m (+ (bit-shift-left 1 m) (* 3 m) 2))) (str "d " d ", m " m ": " @reads " member reads"))
        (when (even? m)
          (is (every? (fn [[l i]] (= (r l i) (not (r l (mod (inc i) m)))))
                      (for [l (range d) i (range m)] [l i]))))))))

(tu/deftest-kb a-cycle-s-discovery-reads-each-key-once-however-many-paths-reach-it
  ;; Conflict keys with stub reads: a root reading the two keys of layer 0, each key of
  ;; layer l reading both keys of layer l + 1, and the last layer reading the root, so
  ;; 2^l paths reach a key of layer l and every key's first read meets the root open.
  ;; The cycle's 2d + 1 members exceed `enumerated-members`, so its passes read at most
  ;; (2m + 1) · m; discovery reads each key once, where reading it once a path costs 2^d.
  (tu/with-terms [w_kind]
    (doseq [d [4 12]]
      (let [in-force-once @#'exc/in-force-once
            m     (inc (* 2 d))
            hs    (mapv (fn [_] (v/assert kb (list w_kind (tu/tmp-ind "Layer")) 'CxUniverse))
                        (range (* 2 m)))
            ck    (fn [i] [:vaelii.impl.except/conflict (hs (* 2 i)) (hs (inc (* 2 i)))])
            reads (atom 0)
            s     {:memo (volatile! {}) :recs (:records kb)}
            root  (ck (dec m))
            r     (fn r [l i]
                    (in-force-once s (if (neg? l) root (ck (+ (* 2 l) i)))
                                   (fn []
                                     (swap! reads inc)
                                     (if (= l (dec d))
                                       (not (r -1 0))
                                       (let [a (r (inc l) 0) b (r (inc l) 1)]
                                         (not (or a b)))))))]
        (r -1 0)
        (is (<= @reads (* m (+ (* 2 m) 3))) (str "d " d ": " @reads " member reads"))))))

(tu/deftest-kb a-read-the-unit-budget-stops-leaves-the-memo-answering-as-a-fresh-one
  ;; The rings of the test above, 2 of 4 members, with the unit's budget passing at the
  ;; n-th member read, inside discovery or inside a ring's close.  The read throws the
  ;; unit's signal, and the memo it leaves reads every key as a fresh memo does.
  (tu/with-terms [w_kind]
    (let [in-force-once @#'exc/in-force-once
          d 2, m 4
          hs    (mapv (fn [_] (v/assert kb (list w_kind (tu/tmp-ind "Ring")) 'CxUniverse))
                      (range (* 2 d m)))
          ck    (fn [l i] (let [j (* 2 (+ (* l m) i))] [:vaelii.impl.except/conflict (hs j) (hs (inc j))]))
          clock (atom 0)
          rd    (fn [s]
                  (fn r [l i]
                    (in-force-once s (ck l i)
                                   (fn []
                                     (swap! clock inc)
                                     (let [nxt (r l (mod (inc i) m))
                                           b   (r l (mod (+ i 2) m))]
                                       (when (and nxt b (< l (dec d))) (r (inc l) 0))
                                       (not nxt))))))
          all   (fn [s] (let [r (rd s)] (r 0 0) (mapv (fn [[l i]] (r l i)) (for [l (range d) i (range m)] [l i]))))
          fresh (all {:memo (volatile! {}) :recs (:records kb)})]
      (is (= [] (into []
                      (keep (fn [n]
                              (let [s    {:memo (volatile! {}) :recs (:records kb)}
                                    over (with-redefs [budget/now (fn [] @clock)]
                                           (reset! clock 0)
                                           (binding [budget/*unit-deadline* n]
                                             (try ((rd s) 0 0) nil
                                                  (catch clojure.lang.ExceptionInfo e (budget/unit-over? e)))))]
                                (when-not (and over (= fresh (all s))) n))))
                      (range 1 40)))))))

(tu/deftest-kb an-empty-answer-builds-no-reader-state
  ;; a probe matching nothing has no handle to hide, so the visibility filter reads no
  ;; walk state for it; a non-empty answer reads it
  (let [asked (atom 0), orig @#'exc/hidden-fn]
    (with-redefs-fn {#'exc/hidden-fn (fn [& args] (swap! asked inc) (apply orig args))}
      #(do (is (empty? (exc/without-excepted kb 'CxUniverse ())))
           (is (zero? @asked))
           (is (= 1 (count (exc/without-excepted kb 'CxUniverse [[1 {} nil]]))))
           (is (= 1 @asked))))))

;; `exc/reader-frame` counted, as each `f` in `fs` is run
(defn- frames-built [fs]
  (let [built (atom 0), orig @#'exc/reader-frame]
    (with-redefs-fn {#'exc/reader-frame (fn [& args] (swap! built inc) (apply orig args))}
      #(mapv (fn [f] (let [n @built] (f) (- @built n))) fs))))

(tu/deftest-kb a-pass-keeps-a-context-s-reader-frame-across-a-write-that-moves-nothing-it-reads
  ;; a declaration CxA does not see and a rule stated in CxA reading its predicate, so a
  ;; read at CxA owes the walk (`exc/walk-reads?`)
  (tu/with-terms [pf qf Ann Bob Cy CxA CxB]
    (v/assert kb (list 'forced_monotonic_predicate pf) CxB)
    (v/assert-rule kb [(list pf '?x '?y)] (list qf '?x '?y) CxA)
    (let [h    (v/assert kb (list pf Ann Bob) CxA)
          read #(exc/excepted? kb h CxA)
          was  (read)]
      (is (= [0 1 2]
             (frames-built [#(dotimes [_ 3] (read))
                            ;; a fact moves the clock and nothing the frame reads
                            #(exc/with-reader-states
                               (dotimes [_ 3] (read))
                               (v/assert kb (list pf Cy Bob) CxA)
                               (read))
                            ;; an except is read by storage
                            #(exc/with-reader-states
                               (read)
                               (v/assert kb (list 'except (v/sentex-handle (v/handle-of kb (list pf Cy Bob) CxA)))
                                         CxA)
                               (read))])))
      (is (= was (read))))))

(defn- state-reading
  "What a reader state answers, comparable across two builds: nil, or its fields with the
  forced-monotonic reading applied to each declared predicate and to `preds`."
  [kb st preds]
  (when st
    (let [on? (:on? (:forced st))]
      (assoc (select-keys st [:up :closable? :exempting? :conflicts? :yielding?])
             :excepted? (some? (:excepted? st))
             :void? (:void? (:forced st))
             :on (into (sorted-set) (for [k (into (vec (keys (decide/declared (reasoning/taxonomy kb))))
                                                  (for [p preds] [:forced-monotonic p]))]
                                      (conj k (boolean (on? (first k) (second k))))))))))

(defn- fresh-state-misses
  "Run `f` with every reader state a read takes, off a `*reader-states*` memo or the change
  clock's frame, compared with a fresh build (`state-reading`): `[answer [[ctx held fresh] …]]`."
  [preds f]
  (let [bad   (atom [])
        held  @#'exc/reader-state
        frame @#'exc/reader-frame
        build (fn [kb ctx]
                (when-let [fr (frame kb ctx)]
                  (#'exc/with-read-memo fr (#'exc/yielding-reads? kb (:tax fr)))))]
    (with-redefs-fn {#'exc/reader-state
                     (fn [kb ctx]
                       (let [st (held kb ctx)
                             a  (state-reading kb st preds)
                             b  (state-reading kb (build kb ctx) preds)]
                         (when (not= a b) (swap! bad conj [ctx a b]))
                         st))}
      #(let [r (f)] [r @bad]))))

(tu/deftest-kb every-reader-state-a-pass-reads-is-the-one-a-fresh-read-builds
  ;; CxA and CxB under CxUniverse, CxC under CxA, then CxB.  One pass writes each kind of
  ;; change a reader frame or `yielding-reads?` reads, and a plain fact, with a read of
  ;; every reader after each
  (tu/with-terms [pkind pkindOut pmark p_penguin p_bird p_flies PA PB PC PD PE PF PO CxA CxB CxC]
    (let [readers ['CxUniverse CxA CxB CxC]
          base    (tu/sentex-ids kb)
          rows    #(set (for [h (remove base (tu/sentex-ids kb)), c readers
                              :when (v/believed? kb h c)]
                          [h c]))
          fw      {:direction :forward}
          at      (atom {})
          steps
          [[:context-edges #(doseq [[c u] [[CxA 'CxUniverse] [CxB 'CxUniverse] [CxC CxA]]]
                              (v/assert kb (list 'genlCx c u) 'CxUniverse))]
           [:rules #(do (v/assert kb (list 'implies (list 'and (list pkind '?x '?y)) (list pkindOut '?x '?y)) CxA fw)
                        (v/assert kb (list 'implies (list 'and (list pmark '?p))
                                           (list 'forced_monotonic_predicate '?p))
                                  CxB fw))]
           [:facts #(do (swap! at assoc :fact (v/assert kb (list pkind PA PB) CxA))
                        (v/assert kb (list pkind PC PD) CxC))]
           [:a-guard-defeat
            #(do (v/assert kb (list 'exceptWhen (list p_penguin '?b)
                                    (list 'set/defaultRule
                                          (list 'set/forwardRule (list 'implies (list 'and (list p_bird '?b))
                                                                       (list p_flies '?b)))))
                           CxA)
                 (v/assert kb (list p_bird PO) CxA)
                 (swap! at assoc :blocker (v/assert kb (list p_penguin PO) CxA)))]
           [:a-declaration-the-reader-does-not-see
            #(swap! at assoc :decl (v/assert kb (list 'forced_monotonic_predicate pkind) CxB))]
           [:a-plain-fact #(v/assert kb (list pkind PE PF) CxA)]
           [:a-denial-of-a-declared-fact
            #(swap! at assoc :denial (v/assert kb (list 'not (list pkind PA PB)) CxB))]
           [:a-context-edge-to-the-declaration #(v/assert kb (list 'genlCx CxC CxB) 'CxUniverse)]
           [:a-declaration-a-rule-draws #(swap! at assoc :mark (v/assert kb (list pmark pkindOut) CxB))]
           [:its-ground-leaving #(v/retract! kb (:mark @at))]
           [:an-except-of-the-declaration
            #(swap! at assoc :except (v/assert kb (list 'except (v/sentex-handle (:decl @at))) CxC))]
           [:an-except-of-a-fact #(v/assert kb (list 'except (v/sentex-handle (:fact @at))) CxC)]
           [:the-first-except-leaving #(v/retract! kb (:except @at))]
           [:the-denial-leaving #(v/retract! kb (:denial @at))]
           [:the-declaration-leaving #(v/retract! kb (:decl @at))]
           [:the-blocker-leaving #(v/retract! kb (:blocker @at))]]
          [answers misses]
          (fresh-state-misses
           [pkind pkindOut]
           #(exc/with-reader-states
              (vec (for [[step write] steps]
                     (do (write)
                         [step (= (rows) (binding [exc/*reader-states* nil] (rows)))])))))]
      (is (= [] misses))
      (is (every? second answers) (pr-str (remove second answers))))))

(tu/deftest-kb the-reads-between-two-writes-build-one-frame-per-context
  (tu/with-terms [p_note Ann Bob CxA CxB]
    (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse)
    (let [h     (v/assert kb (list p_note Ann) CxA)
          built (atom [])
          frame @#'exc/reader-frame
          read  #(dotimes [_ 3] (v/believed? kb h CxA) (v/believed? kb h CxB))]
      (v/assert kb (list 'not (list p_note Ann)) CxA {:strength :monotonic})
      (with-redefs-fn {#'exc/reader-frame (fn [k ctx] (swap! built conj ctx) (frame k ctx))}
        (fn []
          (read)
          (is (= {CxA 1 CxB 1} (frequencies @built)))
          (v/assert kb (list p_note Bob) CxA)
          (reset! built [])
          (read)
          (is (= {CxA 1 CxB 1} (frequencies @built))))))))

(tu/deftest-kb a-held-values-scope-reads-the-frame-a-rebuild-reads
  (tu/with-terms [p_note p_clash Ann CxA CxB]
    (let [h     (v/assert kb (list p_note Ann) CxA)
          state #(#'exc/reader-state kb CxA)]
      (v/assert kb (list p_clash Ann) CxB)
      (v/assert kb (list 'not (list p_clash Ann)) CxB {:strength :monotonic})
      (observe/with-held-values
        (is (nil? (:excepted? (state))))
        (v/assert kb (list 'except (v/sentex-handle h)) CxA)
        (is (some? (:excepted? (state))))))))

(tu/deftest-kb the-held-yield-read-answers-as-the-whole-read-after-each-write
  ;; a forced-monotonic fact stored, its denial stored and retracted, and the declaration
  ;; retracted: the read held across these writes and the whole read agree after each
  (tu/with-terms [pkind PA PB PC CxA]
    (let [held  #(@#'exc/yielding-reads? kb (reasoning/taxonomy kb))
          whole #(@#'exc/opposed-forced? kb (reasoning/taxonomy kb))
          at    (atom {})
          steps [[:declared #(swap! at assoc :decl (v/assert kb (list 'forced_monotonic_predicate pkind)))]
                 [:a-fact #(v/assert kb (list pkind PA PB))]
                 [:its-denial #(swap! at assoc :denial (v/assert kb (list 'not (list pkind PA PB)) CxA))]
                 [:another-fact #(v/assert kb (list pkind PA PC))]
                 [:the-denial-leaving #(v/retract! kb (:denial @at))]
                 [:a-denial-again #(v/assert kb (list 'not (list pkind PA PC)) CxA)]
                 [:the-declaration-leaving #(v/retract! kb (:decl @at))]]]
      (v/assert kb (list 'genlCx CxA 'CxUniverse))
      (held)
      (is (= [[:declared false false] [:a-fact false false] [:its-denial true true]
              [:another-fact true true] [:the-denial-leaving false false]
              [:a-denial-again true true] [:the-declaration-leaving false false]]
             (for [[step write] steps]
               (do (write) [step (held) (whole)])))))))

(tu/deftest-kb an-edit-builds-each-reader-frame-once
  (tu/with-terms [q_dog q_cat q_animal q_fed PO CxA CxB]
    (doseq [c [CxA CxB]] (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
    (v/assert kb (list 'disjoint q_dog q_cat) 'CxUniverse)
    (v/assert kb (list q_dog PO) CxB)
    (v/assert kb (list q_cat PO) CxB)
    (let [edge (v/assert kb (list 'genl q_dog q_animal) 'CxUniverse {:strength :monotonic})]
      (v/assert kb (list 'except (v/sentex-handle edge)) CxB))
    (v/assert kb (list 'implies (list 'and (list q_animal '?x)) (list q_fed '?x)) CxA {:direction :forward})
    (let [xs     (map #(symbol (str "Dog" %)) (range 12))
          frames (atom 0)
          frame  @#'exc/reader-frame]
      (with-redefs-fn {#'exc/reader-frame (fn [kb ctx] (swap! frames inc) (frame kb ctx))}
        #(v/edit! kb {:add (vec (for [x xs] [(list q_dog x) CxA]))}))
      (is (= 2 @frames) "an except and a placed defeat: 24 frames when each read builds one")
      (is (every? #(v/ask? kb (list q_fed %) CxA) xs))
      (is (not (v/ask? kb (list q_fed (first xs)) CxB))))))

(deftest a-release-settles-to-the-same-belief-with-its-reader-frames-kept
  ;; CxC under CxA and CxB.  QM, QE and QO each hold a membership that withholds a mint
  ;; about them; removing the three releases the mints, and rules reading the mints
  ;; conclude a forced-monotonic declaration, an except and a guard defeat, which leave
  ;; with the memberships and come back with the mints in the same settle.  The settle
  ;; with each reader frame kept (`exc/*reader-states*`) and the one building every reader
  ;; state afresh store and believe the same
  (tu/with-terms [q_animal q_dog q_poodle q_penguin q_emperor q_pet q_bird q_flies qOwns qSwims
                  qkind qkindOut QM QE QO QT QSea QFa QFb CxA CxB CxC]
    (let [M      {:strength :monotonic}
          fw     {:direction :forward}
          U      'CxUniverse
          moving #{'forced_monotonic_predicate 'except 'defeat}
          rows   (fn [kb]
                   (let [row #(let [sx (v/sentex kb %)]
                                (tu/handle-free kb [(v/sentence-of sx) (:context sx)]))
                         hs  (tu/sentex-ids kb)]
                     {:stored   (set (map row hs))
                      :in       (set (map row (filter #(v/in? kb %) hs)))
                      :believed (set (for [h hs, c [U CxA CxB CxC] :when (v/believed? kb h c)]
                                       (conj (row h) c)))
                      :moving   (set (filter #(moving (first (v/sentence-of (v/sentex kb %)))) hs))}))
          run    (fn [fresh?]
                   (tu/with-cleared-kb [kb tu/isolated-fresh]
                     (doseq [[c u] [[CxA U] [CxB U] [CxC CxA] [CxC CxB]]]
                       (v/assert kb (list 'genlCx c u) U))
                     (doseq [s [(list 'genl q_animal 'thing) (list 'genl q_dog q_animal)
                                (list 'genl q_poodle q_dog) (list 'genl q_penguin q_animal)
                                (list 'genl q_emperor q_penguin) (list 'genl q_pet q_animal)
                                (list 'arg qOwns 1 q_animal) (list 'arg qSwims 1 q_penguin)]]
                       (v/assert kb s U M))
                     (let [fact (v/assert kb (list qkind QFa QFb) CxA)]
                       (v/assert kb (list 'implies (list 'and (list qkind '?x '?y)) (list qkindOut '?x '?y)) CxA fw)
                       (v/assert kb (list 'implies (list 'and (list q_animal QM))
                                          (list 'forced_monotonic_predicate qkind))
                                 CxC fw)
                       (v/assert kb (list 'implies (list 'and (list q_animal QE)) (list 'except (v/sentex-handle fact)))
                                 CxC fw)
                       (v/assert kb (list 'implies (list 'and (list q_animal '?x) (list qOwns '?x QT)) (list q_pet '?x))
                                 CxC fw)
                       (v/assert kb (list 'exceptWhen (list q_penguin '?b)
                                          (list 'set/defaultRule
                                                (list 'set/forwardRule (list 'implies (list 'and (list q_bird '?b))
                                                                             (list q_flies '?b)))))
                                 CxC)
                       (v/assert kb (list q_bird QO) CxC)
                       (doseq [x [QM QE]]
                         (v/assert kb (list q_poodle x) CxC M)
                         (v/assert kb (list qOwns x QT) CxC M))
                       (v/assert kb (list q_emperor QO) CxC M)
                       (v/assert kb (list qSwims QO QSea) CxC M))
                     (let [before (rows kb)
                           edit   #(v/edit! kb {:remove (mapv (fn [s] (v/handle-of kb s CxC))
                                                              [(list q_poodle QM) (list q_poodle QE)
                                                               (list q_emperor QO)])})
                           misses (if fresh?
                                    (with-redefs-fn {#'exc/reader-state @#'exc/build-reader-state} edit)
                                    (second (fresh-state-misses [qkind] edit)))]
                       [before (rows kb) misses])))
          [[before kept misses] [_ fresh]]
          (binding [argument/*assertive-arg-types?* true
                    checks/*prune-subsumed-mints?*  true]
            [(run false) (run true)])]
      (testing "the declaration, the except and the defeat each left and came back"
        (is (= 3 (count (:moving before)) (count (:moving kept))))
        (is (empty? (set/intersection (:moving before) (:moving kept)))))
      (is (= [] misses))
      (is (= (dissoc fresh :moving) (dissoc kept :moving))))))

(tu/deftest-kb a-declaration-every-reader-of-its-rule-sees-owes-no-walk
  ;; the declaration and the rule reading its predicate are stated in one context, so a
  ;; reader seeing the rule sees the declaration, until an except naming it is stored
  (tu/with-terms [pf qf CxA CxB]
    (let [d (v/assert kb (list 'forced_monotonic_predicate pf) CxA)]
      (v/assert-rule kb [(list pf '?x '?y)] (list qf '?x '?y) CxA)
      (is (false? (exc/walk-reads? kb)))
      (v/assert kb (list 'except (v/sentex-handle d)) CxB)
      (is (true? (exc/walk-reads? kb))))))

(defn- fresh-route-placements
  "The placements of the nogood over `members` that `routes` give, read as
  `chain/route-placements` reads them with nothing held across reads: no reading pass is
  bound, each route reads its keys' supporters itself, and every choice of one supporter
  per key is taken before the `:strict-keys` test."
  [kb members routes]
  (let [tax  (reasoning/taxonomy kb)
        tms  (reasoning/tms kb)
        cls  (res/holding-class kb)
        exc? (tax/sib-exceptions? tax)
        ctx  #(:context (v/sentex kb %))]
    (into #{}
          (for [{:keys [keys links excluded-at strict-links strict-keys pairs] :as route} routes
                sups (reduce (fn [acc k]
                               (for [xs acc
                                     h  (sort (filter #(jtms/in? tms %) (tax/visible-supporters tax k nil)))]
                                 (conj xs [h (ctx h)])))
                             [[]] keys)
                :when (every? (fn [[k [h]]] (or (not (contains? strict-keys k)) (= :monotonic (cls h))))
                              (map vector (seq keys) sups))
                :let [[ps m] (@#'chain/placements-over kb links (into (vec members) (map first) sups)
                                                       (into (mapv ctx members) (map second) sups) nil
                                                       (when (seq strict-links) (set strict-links)))]
                pctx ps
                :when (not (and exc? (tax/route-exempted? tax route pctx)))
                :when (not (and exc? (seq pairs)
                                (some #(tax/route-exempted? tax {:pair % :mark? true} pctx) pairs)))
                :when (every? (fn [[sub super]]
                                (= :monotonic (tax/reach-strength tax :genl sub super pctx cls)))
                              strict-links)
                :when (not (and excluded-at (excluded-at pctx)))]
            [pctx (-> (set members) (into (map first) sups) (into (get m pctx)))]))))

(defn- membership-placements
  "`{members placements}` for every membership nogood the candidate index keeps, each
  read by `(read members routes)`, the nogoods taken in content order or reversed."
  [kb read reverse?]
  (let [c   (decide/synced kb)
        w   (decide/unscoped-closures (reasoning/taxonomy kb))
        ngs (sort-by #(vec (sort (:members %)))
                     (mapcat #(membership/nogoods-of c %) (membership/nogoods-terms c)))]
    (into {} (map (fn [ng] [(:members ng) (read (:members ng) (membership/routes w (:records kb) ng))]))
          (cond-> ngs reverse? reverse))))

(defn- pass-placements
  "`membership-placements` read by `chain/route-placements` in one reading pass, as the
  placement pass reads them: one neighbour cache and one witness memo over every nogood."
  [kb reverse?]
  (binding [chain/*witnesses* (volatile! nil)]
    (tax/with-neighbours
      (atom {})
      #(membership-placements kb (fn [ms rs] (@#'chain/route-placements kb ms rs nil)) reverse?))))

(tu/deftest-kb a-reading-pass-places-each-membership-nogood-as-a-fresh-read-does
  ;;   CxUniverse ─ CxA, CxB, CxD;  CxW under the three;  CxL under CxA;  CxM under CxW, CxL;
  ;;                CxE under CxW
  ;;   genl (CxUniverse): a0→a1→a2, ax→a1, b1→b2, s→w, u→t2, f→c, g→c;  CxL: a0→ax, b0→b1
  ;;   CxD:  disjoint a1-b1, a1-b2, a2-b2;  (covering w p q);  (disjoint d p);
  ;;         (disjoint_metatype m);  (m t2);  (m p) default;  (sibling_disjoint c);
  ;;         (siblingDisjointException f g)
  ;;   CxA and CxD: (disjoint a2 b1);  CxA: (m p);  CxB: (disjoint e q)
  ;;   CxE: an except of (a0 X)
  ;;   X: (a0 X) CxA (b0 X) CxB          Y: (s Y) CxA (d Y) CxA (e Y) CxB
  ;;   Z: (s Z) CxA (not (w Z)) CxB      V: (s V) CxA (u V) CxB (not (q V)) CxB
  ;;   G: (f G) CxA (g G) CxB
  (tu/with-terms [a0 a1 a2 ax b0 b1 b2 s w p q d e u t2 m f g c X Y Z V G
                  CxA CxB CxD CxW CxL CxM CxE]
    (let [M {:strength :monotonic}
          U 'CxUniverse]
      (doseq [[k up] [[CxA U] [CxB U] [CxD U] [CxW CxA] [CxW CxB] [CxW CxD] [CxL CxA]
                      [CxM CxW] [CxM CxL] [CxE CxW]]]
        (v/assert kb (list 'genlCx k up) U M))
      (doseq [[x y cx] [[a0 a1 U] [a1 a2 U] [ax a1 U] [b1 b2 U] [s w U] [u t2 U] [f c U] [g c U]
                        [a0 ax CxL] [b0 b1 CxL]]]
        (v/assert kb (list 'genl x y) cx M))
      (doseq [[sen cx o] [[(list 'disjoint a1 b1) CxD M] [(list 'disjoint a1 b2) CxD M]
                          [(list 'disjoint a2 b2) CxD M] [(list 'disjoint a2 b1) CxD M]
                          [(list 'disjoint a2 b1) CxA M] [(list 'covering w p q) CxD M]
                          [(list 'disjoint d p) CxD M] [(list 'disjoint e q) CxB M]
                          [(list 'disjoint_metatype m) CxD M] [(list m t2) CxD M]
                          [(list m p) CxD {}] [(list m p) CxA M] [(list 'sibling_disjoint c) CxD M]
                          [(list 'siblingDisjointException f g) CxD M]]]
        (v/assert kb sen cx o))
      (let [hx (v/assert kb (list a0 X) CxA)]
        (v/assert kb (list 'except (v/sentex-handle hx)) CxE M))
      (doseq [[sen cx] [[(list b0 X) CxB] [(list s Y) CxA] [(list d Y) CxA] [(list e Y) CxB]
                        [(list s Z) CxA] [(list 'not (list w Z)) CxB] [(list s V) CxA]
                        [(list u V) CxB] [(list 'not (list q V)) CxB] [(list f G) CxA] [(list g G) CxB]]]
        (v/assert kb sen cx))
      (let [fresh (membership-placements kb #(fresh-route-placements kb %1 %2) false)
            c     (decide/synced kb)
            w     (decide/unscoped-closures (reasoning/taxonomy kb))
            ngs   (mapcat #(membership/nogoods-of c %) (membership/nogoods-terms c))
            kinds (into #{} (map :kind) ngs)]
        (testing "the fixture reads every kind of membership nogood, and places most of them"
          (is (= #{:disjoint :supertype :cover} kinds))
          (is (some #(seq (:strict-keys %)) (mapcat #(membership/routes w (:records kb) %) ngs))
              "a route with strict keys, whose supporters are filtered before the product")
          (is (<= 5 (count fresh)))
          (is (<= 4 (count (filter seq (vals fresh))))))
        (is (= fresh (pass-placements kb false)))
        (is (= fresh (pass-placements kb true)))))))
