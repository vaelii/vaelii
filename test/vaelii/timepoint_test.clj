;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.timepoint-test
  "The named points of a temporal thing (`vaelii.impl.timepoint`) read by the point
  network, in four worlds: a story on its own timeline, dated clues from reading stitched
  into bounds on when a presidency began and ended, a period two authorities date differently, and a story set inside that period
  with one date.

  Each world is data — contexts, labelled facts, questions with their expected answers,
  and consistency checks — and every world-local name is replaced by a fresh temporary
  before it is asserted, so the worlds read as written and the test stays net-neutral.

    [:before p q]   `argue` over (instantBefore p q): :true, :false or :unknown
    [:at X t]       `argue` over (includesInstant X t)
    [:allen X Y]    the Allen relations still possible between X and Y
    :consistent     the point network visible from the context is satisfiable
    {:fixes #{…}}   it is not, and every fact whose removal alone would restore it is
                    among the culprits the network names"
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [clojure.walk :as walk]
            [vaelii.core :as v]
            [vaelii.impl.datetime :as dt]
            [vaelii.impl.interval :as iv]
            [vaelii.impl.point :as pt]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.stp :as stp]
            [vaelii.impl.timepoint :as tp]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded #(doto % (tu/load-core!)
                                      (v/add-reasoner :point :allen :tightest-start-bound)
                                      (v/add-prover (pt/includes-instant-prover)))))
(use-fixtures :each (tu/neutral))

;; ---- the worlds ---------------------------------------------------------

(def ^:private wolf
  {:contexts '{CxWolf #{} CxWolfRetold #{CxWolf}}
   :facts
   '[;; he watched the sheep; one day he cried "Wolf!"
     [CxWolf :cry1-while-watching (instantBefore (StartFn Watch) (StartFn Cry1))]
     ;; the villagers came running; when they arrived he laughed; they went back, angry
     [CxWolf :run1-after-cry1     (instantBefore (StartFn Cry1) (StartFn Run1))]
     [CxWolf :laugh1-on-arrival   (instantEqual (EndFn Run1) (StartFn Laugh1))]
     [CxWolf :return1-after-laugh (instantBefore (StartFn Laugh1) (StartFn Return1))]
     ;; the first trick is those four
     [CxWolf :trick1-start        (instantEqual (StartFn Trick1) (StartFn Cry1))]
     [CxWolf :trick1-end          (instantEqual (EndFn Trick1) (EndFn Return1))]
     ;; later he did it again
     [CxWolf :later-again         (instantBefore (EndFn Trick1) (StartFn Trick2))]
     [CxWolf :trick2-start        (instantEqual (StartFn Trick2) (StartFn Cry2))]
     [CxWolf :run2-after-cry2     (instantBefore (StartFn Cry2) (StartFn Run2))]
     [CxWolf :laugh2-on-arrival   (instantEqual (EndFn Run2) (StartFn Laugh2))]
     [CxWolf :return2-after-laugh (instantBefore (StartFn Laugh2) (StartFn Return2))]
     [CxWolf :trick2-end          (instantEqual (EndFn Trick2) (EndFn Return2))]
     ;; they resolved not to believe him again, on the way back down
     [CxWolf :distrust-after-laugh2 (instantBefore (StartFn Laugh2) (StartFn Distrust))]
     [CxWolf :distrust-on-return2   (instantBefore (StartFn Distrust) (EndFn Return2))]
     ;; one evening a wolf really came, and he cried out while it was there
     [CxWolf :wolf-after-trick2   (instantBefore (EndFn Trick2) (StartFn Attack))]
     [CxWolf :cry3-at-wolf        (instantBefore (StartFn Attack) (StartFn Cry3))]
     [CxWolf :cry3-during-attack  (instantBefore (StartFn Cry3) (EndFn Attack))]
     ;; no one came: they still did not believe him
     [CxWolf :distrust-outlasts-cry3 (instantBefore (EndFn Cry3) (EndFn Distrust))]
     ;; the wolf scattered the flock, which ended his watching
     [CxWolf :loss-in-attack      (instantBefore (StartFn Attack) (StartFn Loss))]
     [CxWolf :loss-ends-by-attack (instantNotAfter (EndFn Loss) (EndFn Attack))]
     [CxWolf :watch-ends-with-attack (instantEqual (EndFn Watch) (EndFn Attack))]
     [CxWolf :dream-before-watch  (before Dream Watch)]
     [CxWolf :song-with-run1      (sharesTimeWith Song Run1)]
     ;; a retelling: the wolf was already prowling when he first cried
     [CxWolfRetold :prowling-first (instantBefore (StartFn Attack) (StartFn Cry1))]]
   :questions
   '[[CxWolf [:before (StartFn Run1) (StartFn Cry2)] :true]
     ;; did they already distrust him when they ran up the second time?  and the third?
     [CxWolf [:at Distrust (StartFn Run2)] :false]
     [CxWolf [:at Distrust (StartFn Cry3)] :true]
     [CxWolf [:at Watch (StartFn Loss)] :true]
     ;; nothing states when he stopped laughing: the question alone makes it a node
     [CxWolf [:before (EndFn Laugh1) (EndFn Return1)] :unknown]
     [CxWolf [:allen Trick1 Trick2] #{:before}]
     [CxWolf [:allen Distrust Return2] #{:contains :started-by :overlapped-by}]
     [CxWolf [:before (EndFn Dream) (StartFn Cry1)] :true]
     [CxWolf [:before (StartFn Song) (StartFn Laugh1)] :true]]
   :checks
   '[[CxWolf :consistent]
     [CxWolfRetold {:fixes #{:later-again :wolf-after-trick2 :prowling-first}}]]})

(def ^:private obama
  "Clues from reading, each placing one event inside the presidency (or outside it) and
  inside a year; stitched together they bound when the presidency began and ended."
  {:contexts '{CxClues #{} CxCluesLater #{CxClues}}
   :facts
   '[;; "in 2004, before he was president, he gave the convention keynote"
     [CxClues :keynote-2004-lower (instantNotAfter (StartFn (YearFn 2004)) (StartFn Keynote))]
     [CxClues :keynote-2004-upper (instantNotAfter (EndFn Keynote) (EndFn (YearFn 2004)))]
     [CxClues :keynote-before-office (instantBefore (EndFn Keynote) (StartFn Presidency))]
     ;; "while president in 2009, he received the Nobel Peace Prize"
     [CxClues :nobel-2009-lower (instantNotAfter (StartFn (YearFn 2009)) (StartFn Nobel))]
     [CxClues :nobel-2009-upper (instantNotAfter (EndFn Nobel) (EndFn (YearFn 2009)))]
     [CxClues :nobel-in-office-start (instantNotAfter (StartFn Presidency) (StartFn Nobel))]
     [CxClues :nobel-in-office-end   (instantNotAfter (EndFn Nobel) (EndFn Presidency))]
     ;; "while president in 2016, he visited Cuba"
     [CxClues :cuba-2016-lower (instantNotAfter (StartFn (YearFn 2016)) (StartFn CubaVisit))]
     [CxClues :cuba-2016-upper (instantNotAfter (EndFn CubaVisit) (EndFn (YearFn 2016)))]
     [CxClues :cuba-in-office-start (instantNotAfter (StartFn Presidency) (StartFn CubaVisit))]
     [CxClues :cuba-in-office-end   (instantNotAfter (EndFn CubaVisit) (EndFn Presidency))]
     ;; "in 2018, after leaving office, he started a production company"
     [CxClues :company-2018-lower (instantNotAfter (StartFn (YearFn 2018)) (StartFn Company))]
     [CxClues :company-2018-upper (instantNotAfter (EndFn Company) (EndFn (YearFn 2018)))]
     [CxClues :company-after-office (instantBefore (EndFn Presidency) (StartFn Company))]
     ;; a later clue that cannot fit: "while president in 2020, he issued a pardon"
     [CxCluesLater :pardon-2020-lower (instantNotAfter (StartFn (YearFn 2020)) (StartFn Pardon))]
     [CxCluesLater :pardon-2020-upper (instantNotAfter (EndFn Pardon) (EndFn (YearFn 2020)))]
     [CxCluesLater :pardon-in-office-start (instantNotAfter (StartFn Presidency) (StartFn Pardon))]
     [CxCluesLater :pardon-in-office-end   (instantNotAfter (EndFn Pardon) (EndFn Presidency))]]
   :questions
   '[;; between the 2009 and 2016 clues: president throughout
     [CxClues [:at Presidency (InstantFn 2012 7 1 0 0 0)] :true]
     [CxClues [:before (StartFn Presidency) (StartFn (YearFn 2010))] :true]
     ;; between the keynote and the Nobel: the clues do not say
     [CxClues [:at Presidency (InstantFn 2008 7 1 0 0 0)] :unknown]
     [CxClues [:at Presidency (InstantFn 2017 7 1 0 0 0)] :unknown]
     ;; before the keynote and after the company: not president
     [CxClues [:at Presidency (InstantFn 2003 7 1 0 0 0)] :false]
     [CxClues [:at Presidency (InstantFn 2019 7 1 0 0 0)] :false]
     [CxClues [:at Presidency (StartFn Keynote)] :false]
     [CxClues [:allen Keynote Presidency] #{:before}]
     [CxClues [:allen Presidency (YearFn 2009)] #{:contains :started-by :overlapped-by}]
     [CxClues [:allen Keynote (YearFn 2004)] #{:starts :during :finishes :equal}]]
   :checks
   '[[CxClues :consistent]
     [CxCluesLater {:fixes #{:pardon-2020-lower :pardon-in-office-end
                             :company-after-office :company-2018-upper}}]]})

(def ^:private renaissance
  {:contexts '{CxPeriodsA #{} CxPeriodsB #{}}
   :facts
   '[;; authority A: begins in the 14th century, ends between 1527 and 1600
     [CxPeriodsA :a-earliest-start (instantEqual (EarliestStartFn Renaissance) (StartFn (YearFn 1300)))]
     [CxPeriodsA :a-latest-start   (instantEqual (LatestStartFn Renaissance) (EndFn (YearFn 1400)))]
     [CxPeriodsA :a-earliest-end   (instantEqual (EarliestEndFn Renaissance) (StartFn (YearFn 1527)))]
     [CxPeriodsA :a-latest-end     (instantEqual (LatestEndFn Renaissance) (EndFn (YearFn 1600)))]
     ;; authority B: begins 1400–1450, ends 1600–1650
     [CxPeriodsB :b-earliest-start (instantEqual (EarliestStartFn Renaissance) (StartFn (YearFn 1400)))]
     [CxPeriodsB :b-latest-start   (instantEqual (LatestStartFn Renaissance) (EndFn (YearFn 1450)))]
     [CxPeriodsB :b-earliest-end   (instantEqual (EarliestEndFn Renaissance) (StartFn (YearFn 1600)))]
     [CxPeriodsB :b-latest-end     (instantEqual (LatestEndFn Renaissance) (EndFn (YearFn 1650)))]
     ;; B: the Baroque began within the Renaissance's closing period — a claim about two
     ;; bound points
     [CxPeriodsB :baroque-after-earliest-end (instantNotAfter (EarliestEndFn Renaissance) (StartFn Baroque))]
     [CxPeriodsB :baroque-by-latest-end      (instantNotAfter (StartFn Baroque) (LatestEndFn Renaissance))]]
   :questions
   '[[CxPeriodsA [:at Renaissance (InstantFn 1450 7 1 0 0 0)] :true]
     [CxPeriodsB [:at Renaissance (InstantFn 1450 7 1 0 0 0)] :unknown]
     [CxPeriodsA [:at Renaissance (InstantFn 1350 7 1 0 0 0)] :unknown]
     [CxPeriodsB [:at Renaissance (InstantFn 1350 7 1 0 0 0)] :false]
     [CxPeriodsA [:at Renaissance (InstantFn 1620 7 1 0 0 0)] :false]
     [CxPeriodsB [:at Renaissance (InstantFn 1620 7 1 0 0 0)] :unknown]
     [CxPeriodsA [:at Renaissance (InstantFn 1500 7 1 0 0 0)] :true]
     [CxPeriodsB [:at Renaissance (InstantFn 1500 7 1 0 0 0)] :true]
     [CxPeriodsB [:before (LatestStartFn Renaissance) (StartFn Baroque)] :true]
     [CxPeriodsB [:allen Renaissance Baroque] #{:before :meets :overlaps :finished-by :contains}]]
   :checks
   '[[CxPeriodsA :consistent] [CxPeriodsB :consistent]]})

(def ^:private tomaso
  (merge-with into renaissance
              {:contexts '{CxTomaso #{}
                           CxTomasoA #{CxTomaso CxPeriodsA} CxTomasoB #{CxTomaso CxPeriodsB}
                           CxGrandson #{CxTomaso}
                           CxGrandsonA #{CxGrandson CxPeriodsA} CxGrandsonB #{CxGrandson CxPeriodsB}}
               :facts
               '[;; during the Renaissance, Tomaso apprenticed to a painter in Florence
                 [CxTomaso :apprenticed-in-ren-start (instantNotAfter (StartFn Renaissance) (StartFn Apprenticeship))]
                 [CxTomaso :apprenticed-in-ren-end   (instantNotAfter (EndFn Apprenticeship) (EndFn Renaissance))]
                 ;; after seven years he opened his own workshop (only the order is read)
                 [CxTomaso :workshop-after-apprenticeship (instantNotAfter (EndFn Apprenticeship) (StartFn Workshop))]
                 ;; his first commission came to the workshop, dated 1482
                 [CxTomaso :commission-at-workshop (instantBefore (StartFn Workshop) (StartFn Commission))]
                 [CxTomaso :commission-1482-lower  (instantNotAfter (StartFn (YearFn 1482)) (StartFn Commission))]
                 [CxTomaso :commission-1482-upper  (instantNotAfter (EndFn Commission) (EndFn (YearFn 1482)))]
                 ;; his grandson finished a Renaissance altarpiece in 1620
                 [CxGrandson :altarpiece-1620-lower (instantNotAfter (StartFn (YearFn 1620)) (EndFn Altarpiece))]
                 [CxGrandson :altarpiece-1620-upper (instantBefore (EndFn Altarpiece) (EndFn (YearFn 1620)))]
                 [CxGrandson :altarpiece-in-ren     (instantNotAfter (EndFn Altarpiece) (EndFn Renaissance))]]
               :questions
               '[;; still an apprentice at the commission?  the story's own order answers it
                 [CxTomaso  [:at Apprenticeship (StartFn Commission)] :false]
                 ;; was the commission during the Renaissance?  only a dating of the period says
                 [CxTomaso  [:at Renaissance (StartFn Commission)] :unknown]
                 [CxTomasoA [:at Renaissance (StartFn Commission)] :true]
                 [CxTomasoB [:at Renaissance (StartFn Commission)] :true]
                 ;; the period's dating reaches back into the story
                 [CxTomaso  [:before (StartFn (YearFn 1399)) (StartFn Apprenticeship)] :unknown]
                 [CxTomasoB [:before (StartFn (YearFn 1399)) (StartFn Apprenticeship)] :true]]
               :checks
               '[[CxTomasoA :consistent] [CxTomasoB :consistent]
                 ;; the same story conflicts under one dating and not the other
                 [CxGrandsonA {:fixes #{:altarpiece-1620-lower :altarpiece-in-ren :a-latest-end}}]
                 [CxGrandsonB :consistent]]}))

;; ---- running a world ----------------------------------------------------

(defn- world-local?
  "A name the world coins: a context, or an individual — not a function (…Fn) or a
  predicate."
  [x]
  (and (symbol? x) (Character/isUpperCase (.charAt (name x) 0))
       (not (str/ends-with? (name x) "Fn"))))

(defn- realize
  "`world` with every world-local name replaced by a fresh temporary."
  [world]
  (let [names (into #{} (filter world-local?) (tree-seq coll? seq world))
        fresh (into {} (for [n names]
                         [n (if (str/starts-with? (name n) "Cx")
                              (tu/tmp-ctx (subs (name n) 2))
                              (tu/tmp-ind (name n)))]))]
    (walk/postwalk-replace fresh world)))

(defn- load-world! [kb {:keys [contexts facts]}]
  (doseq [[c parents] contexts
          p (if (seq parents) parents ['CxUniverse])]
    (v/assert kb (list 'genlCx c p) 'CxUniverse {:strength :monotonic}))
  (into {} (for [[c label s] facts]
             [(v/assert kb s c {:strength :monotonic}) label])))

(defn- answer [kb ctx [kind a b]]
  (case kind
    :before (:verdict (v/argue kb (list 'instantBefore a b) ctx {}))
    :at     (:verdict (v/argue kb (list 'includesInstant a b) ctx {}))
    :allen  (v/possible-relations kb :allen ctx a b)))

(defn- check [kb labels ctx]
  (if (:consistent? (v/qualitative-network kb :point ctx))
    :consistent
    (let [culprits (set (keep labels (:support (qkb/inconsistency-culprits pt/instants kb ctx))))]
      {:culprits culprits})))

(defn- allen-from-points-pair-by-pair
  "The Allen relations the point network determines in `ctx`, each endpoint comparison and
  its support asked of the point network as a goal of its own: the reference the interval
  network's point narrowing, which reads all of them off one closed network, is held to."
  [kb ctx]
  (let [things (into #{} (comp (keep tp/thing-of)
                               (filter #(or (symbol? %) (dt/extent %) (dt/utc-extent %))))
                     (qkb/nodes (qkb/network kb pt/instants ctx)))]
    (reduce
     (fn [acc [x y]]
       (let [ends (for [ex [:start :end] ey [:start :end]] [ex ey (tp/point ex x) (tp/point ey y)])
             cmp  (into {} (for [[ex ey a b] ends]
                             [[ex ey] (pt/possible-point-relations kb ctx a b)]))
             rels (into #{} (keep (fn [[rel sig]]
                                    (when (every? (fn [[k r]] (contains? (cmp k) r)) sig) rel)))
                        stp/endpoint-signature)]
         (if (= rels stp/allen-relations)
           acc
           (-> acc
               (assoc-in [:net [x y]] rels)
               (assoc-in [:support [x y]]
                         (into #{} (mapcat (fn [[_ _ a b]] (qkb/support pt/instants kb ctx a b)))
                               ends))))))
     {:net {} :support {}}
     (for [x things y things :when (not= x y)] [x y]))))

(defn- run-world [kb world]
  (let [{:keys [questions checks] :as w} (realize world)
        labels (load-world! kb w)]
    (doseq [[ctx q expect] questions]
      (testing (pr-str q)
        (is (= expect (answer kb ctx q)))))
    (doseq [[ctx expect] checks]
      (testing (str "consistency in " ctx)
        (let [got (check kb labels ctx)]
          (if (= :consistent expect)
            (is (= :consistent got))
            (is (set/subset? (:fixes expect) (:culprits got)) (pr-str got))))))
    (doseq [[ctx expect] checks :when (= :consistent expect)]
      (testing (str "the Allen reading of the points in " ctx " agrees with the pair-by-pair one")
        (is (= (allen-from-points-pair-by-pair kb ctx)
               (#'iv/points-narrowing-with-support kb ctx)))))))

(tu/deftest-kb a-story-on-its-own-timeline (run-world kb wolf))
(tu/deftest-kb dated-clues-stitched-together (run-world kb obama))
(tu/deftest-kb a-period-with-uncertain-bounds (run-world kb renaissance))
(tu/deftest-kb a-story-inside-a-dated-period (run-world kb tomaso))

;; ---- the terms alone ----------------------------------------------------

(deftest the-inclusion-reader-is-registered-by-name
  (is (some #{:includes-instant} (v/reasoners))))

(tu/deftest-kb a-calendar-point-orders-against-an-instant-with-nothing-stated
  (is (= #{:before} (v/possible-relations kb :point 'CxUniverse
                                          '(EndFn (YearFn 2008)) '(InstantFn 2009 1 20 12 0 0))))
  (is (= #{:equal} (v/possible-relations kb :point 'CxUniverse
                                         '(EndFn (YearFn 1999)) '(StartFn (YearFn 2000))))))

;; ---- forward chaining through the points --------------------------------

(defn- fire-in-order
  "Assert `facts` and a forward rule `antes` → `(concl ?x)` into a fresh context under
  CxUniverse, the rule at position `rule-at` among the facts, and answer the instances of
  `(concl ?x)` believed there."
  [kb antes concl facts rule-at]
  (let [ctx (tu/tmp-ctx "Story")
        [pre post] (split-at rule-at facts)]
    (v/assert kb (list 'genlCx ctx 'CxUniverse) 'CxUniverse)
    (run! #(v/assert kb % ctx) pre)
    (v/assert-rule kb antes (list concl '?x) ctx {:direction :forward})
    (run! #(v/assert kb % ctx) post)
    (set (map :sentence (v/sentexes-matching kb (list concl '?x) ctx)))))

(tu/deftest-kb an-instant-fact-re-joins-the-rules-of-every-calculus-it-moves
  ;; `instantBefore` is answered by the point calculus and read by the Allen one, and the
  ;; fixture registers `:point` first
  (tu/with-terms [A B prior_one]
    (doseq [rule-at [0 1]]
      (is (= #{(list prior_one A)}
             (fire-in-order kb [(list 'before '?x B)] prior_one
                            [(list 'instantBefore (list 'EndFn A) (list 'StartFn B))]
                            rule-at))
          (str "rule at " rule-at)))))

(tu/deftest-kb a-delta-re-join-reaches-a-node-only-the-rule-names
  ;; the rule's second argument is a point no fact states, which the network orders only
  ;; once a goal names it; `instantBefore` is left out, since its `transitive` declaration
  ;; re-joins in full and would find the firing either way
  (doseq [row [:calendar :bound] rule-at [0 1 2]]
    (tu/with-terms [P Q T early_one]
      (let [[pred target facts]
            (case row
              :calendar ['instantNotEqual '(InstantFn 2000 1 1 0 0 0)
                         [(list 'instantBefore P '(InstantFn 1990 1 1 0 0 0))
                          (list 'instantBefore Q '(InstantFn 1991 1 1 0 0 0))]]
              :bound    ['instantNotAfter (list 'LatestEndFn T)
                         [(list 'instantBefore P (list 'StartFn T))
                          (list 'instantBefore Q (list 'StartFn T))]])]
        (is (= #{(list early_one P) (list early_one Q)}
               (fire-in-order kb [(list pred '?x target)] early_one facts rule-at))
            (str pred " rule at " rule-at))))))

(tu/deftest-kb a-declared-reflexive-point-predicate-fires-a-forward-rule-once-per-node
  (doseq [order [[:decl :rule :ab :bq] [:rule :ab :bq :decl]
                 [:ab :decl :rule :bq] [:bq :rule :decl :ab]]]
    (tu/with-terms [A B Q notLater]
      (let [ctx     (tu/tmp-ctx "Story")
            facts   {:decl '(reflexive instantNotAfter)
                     :ab   (list 'instantBefore A B)
                     :bq   (list 'instantBefore B Q)}
            derived #(set (map (comp vec rest :sentence)
                               (v/sentexes-matching kb (list notLater '?x '?y) ctx)))]
        (v/assert kb (list 'genlCx ctx 'CxUniverse) 'CxUniverse)
        (doseq [k order]
          (if (= k :rule)
            (v/assert-rule kb [(list 'instantNotAfter '?x '?y)] (list notLater '?x '?y) ctx
                           {:direction :forward})
            (v/assert kb (facts k) ctx)))
        (testing (pr-str order)
          (is (= #{[A A] [B B] [Q Q] [A B] [B Q] [A Q]} (derived)))
          (let [d (v/handle-of kb (:decl facts) ctx)]
            (is (contains? (set (keys (:nodes (v/why kb (v/handle-of kb (list notLater A A) ctx)))))
                           d))
            (v/retract! kb d))
          (is (= #{[A B] [B Q] [A Q]} (derived))))))))

(tu/deftest-kb an-allen-fact-moves-both-networks-and-a-point-firing-rests-on-it
  (doseq [allen-first? [false true] rule-at [0 1 2]]
    (let [k (if allen-first?
              (doto (v/open-kb {:backend :memory :space [::allen-first] :recover? false})
                (tu/clear-kb!)
                (tu/load-core!)
                (v/add-reasoner :allen :point))
              kb)]
      (try
        (tu/with-terms [A B C early_one]
          (let [ctx     (tu/tmp-ctx "Story")
                allen   (list 'before A B)
                [pre post] (split-at rule-at [allen (list 'instantBefore (list 'StartFn B) (list 'StartFn C))])
                derived #(set (map (comp second :sentence)
                                   (v/sentexes-matching k (list early_one '?x) ctx)))]
            (v/assert k (list 'genlCx ctx 'CxUniverse) 'CxUniverse)
            (run! #(v/assert k % ctx) pre)
            (v/assert-rule k [(list 'instantBefore '?x (list 'StartFn C))] (list early_one '?x) ctx
                           {:direction :forward})
            (run! #(v/assert k % ctx) post)
            (testing (pr-str {:allen-first? allen-first? :rule-at rule-at})
              (is (= (if allen-first? [:allen :point] [:point :allen])
                     (mapv :name (qkb/calculi-triggered-by k 'before))))
              (is (contains? (derived) (list 'EndFn A)))
              (v/retract! k (v/handle-of k allen ctx))
              (is (not (contains? (derived) (list 'EndFn A))))
              (is (contains? (derived) (list 'StartFn B))))))
        (finally (when allen-first? (tu/drop-space! [::allen-first])))))))

;; ---- an unsatisfiable network -------------------------------------------

(tu/deftest-kb an-unsatisfiable-network-is-reported-once-whatever-the-goal-names
  ;; a goal naming (StartFn Z) extends the network with Z's points, so the queries
  ;; alternate between two network values over one set of believed facts
  (tu/with-terms [P Q Z]
    (let [ctx (tu/tmp-ctx "Story")]
      (v/assert kb (list 'genlCx ctx 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'instantBefore P Q) ctx)
      (v/assert kb (list 'instantBefore Q P) ctx)
      (dotimes [_ 3]
        (v/possible-relations kb :point ctx P Q)
        (v/possible-relations kb :point ctx P (list 'StartFn Z)))
      (dotimes [_ 2]
        (v/ask? kb (list 'instantBefore P Q) ctx)
        (v/ask? kb (list 'instantBefore P (list 'EndFn Z)) ctx))
      (let [es (filter #(and (= :qualitative-inconsistency (:violation %)) (= ctx (:context %)))
                       (v/violations kb))]
        (is (= 1 (count es)) (pr-str (map (comp :nodes :detail) es)))
        (is (= #{P Q} (set (:nodes (:detail (first es))))))))))

(deftest one-thing's-points-are-ordered-with-no-kb-in-sight
  (let [net (:net (tp/constraints-over '#{(EarliestStartFn X) (EndFn X)}))]
    (testing "a mentioned thing brings its start and end in"
      (is (= #{:before} (get net '[(StartFn X) (EndFn X)]))))
    (testing "a bound point is ordered against the point it bounds"
      (is (= #{:before :equal} (get net '[(EarliestStartFn X) (StartFn X)]))))
    (testing "an unmentioned bound is not a node"
      (is (not-any? #(contains? (set %) '(LatestEndFn X)) (keys net))))))

(tu/deftest-kb a-moment-spelled-as-a-term-is-its-own-points
  (let [noon '(InstantFn 2000 1 1 12 0 0)
        rel  #(v/possible-relations kb :point 'CxUniverse %1 %2)]
    (testing "every point of an InstantFn term equals the term"
      (doseq [f '[StartFn EndFn EarliestStartFn LatestStartFn EarliestEndFn LatestEndFn]]
        (is (= #{:equal} (rel (list f noon) noon)) (str f))))
    (testing "a point of a point equals that point"
      (tu/with-terms [Party]
        (is (= #{:equal} (rel (list 'EndFn (list 'StartFn Party)) (list 'StartFn Party))))))
    (testing "a point of an InstantFn term is placed by the calendar"
      (is (= #{:before} (rel (list 'EndFn noon) '(StartFn (YearFn 2001))))))))

(tu/deftest-kb a-moment-named-by-a-symbol-given-points-is-given-extent
  (tu/with-terms [Noon]
    (let [a (v/assert kb (list 'time_point Noon) 'CxUniverse)
          s (v/assert kb (list 'instantEqual (list 'StartFn Noon) Noon) 'CxUniverse)
          e (v/assert kb (list 'instantEqual (list 'EndFn Noon) Noon) 'CxUniverse)
          culprits (:support (qkb/inconsistency-culprits pt/instants kb 'CxUniverse))]
      (is (not (:consistent? (v/qualitative-network kb :point 'CxUniverse))))
      (is (= #{s e} (set culprits)))
      (is (not (contains? (set culprits) a))))))

;; ---- a thing against a moment -------------------------------------------

(tu/deftest-kb inclusion-with-support-answers-what-solve-answers
  (tu/with-terms [Party Noon Dusk]
    (let [c     'CxUniverse
          pr    (pt/includes-instant-prover)
          after (v/assert kb (list 'instantBefore (list 'EndFn Party) Dusk) c)]
      (v/assert kb (list 'instantBefore (list 'StartFn Party) Noon) c)
      (v/assert kb (list 'instantBefore Noon (list 'EndFn Party)) c)
      (doseq [g [(list 'includesInstant Party Noon)
                 (list 'not (list 'includesInstant Party Dusk))]]
        (testing (pr-str g)
          (is (= [{}] (prover-types/solve pr kb g c)))
          (is (= (prover-types/solve pr kb g c)
                 (map first (prover-types/solve-with-support pr kb g c))))))
      (testing "a moment after the end is outside by the fact that put it there"
        (is (contains? (second (first (prover-types/solve-with-support
                                       pr kb (list 'not (list 'includesInstant Party Dusk)) c)))
                       after))))))

(tu/deftest-kb a-stated-start-or-end-decides-an-inclusion-and-a-start-alone-holds-its-own-moment
  (tu/with-terms [Since Span Dawn Noon Dusk]
    (let [c       'CxUniverse
          pr      (pt/includes-instant-prover)
          start   (v/assert kb (list 'startOf Since Noon) c)
          verdict (fn [x t] [(v/ask? kb (list 'includesInstant x t) c)
                             (v/ask? kb (list 'not (list 'includesInstant x t)) c)])]
      (v/assert kb (list 'instantBefore Dawn Noon) c)
      (v/assert kb (list 'instantBefore Noon Dusk) c)
      (is (= [[true false] [false true] [false false]] (map #(verdict Since %) [Noon Dawn Dusk])))
      (is (contains? (second (first (prover-types/solve-with-support
                                     pr kb (list 'includesInstant Since Noon) c)))
                     start))
      (v/assert kb (list 'startOf Span Dawn) c)
      (v/assert kb (list 'endOf Span Dusk) c)
      (is (= [[true false] [false true]] (map #(verdict Span %) [Noon Dusk])))
      (v/retract! kb start)
      (is (= [false false] (verdict Since Noon))))))

(tu/deftest-kb an-open-thing-ranges-over-the-things-a-stated-bound-names
  (tu/with-terms [Since Noon CxElse]
    (let [c   'CxUniverse
          day '(InstantFn 2000 1 1 0 0 0)]
      (v/assert kb (list 'startOf Since day) c)
      (v/assert kb (list 'startOf Since Noon) CxElse)
      (is (= #{{'?x Since} {'?x 'Forever}} (set (v/query kb (list 'includesInstant '?x day) c))))
      (is (empty? (v/query kb (list 'includesInstant '?x Noon) c))))))

(tu/deftest-kb a-stored-inclusion-is-answered-beside-the-network
  (tu/with-terms [Party Noon Dusk]
    (let [c    'CxUniverse
          ask? #(v/ask? kb % c)]
      (v/assert kb (list 'includesInstant Party Noon) c)
      (v/assert kb (list 'not (list 'includesInstant Party Dusk)) c)
      (is (ask? (list 'includesInstant Party Noon)))
      (is (ask? (list 'not (list 'includesInstant Party Dusk)))))))

;; The calendar row names a moment no fact names, so only a join that binds `?t` before it
;; reaches `includesInstant` can find it.
(tu/deftest-kb an-inclusion-antecedent-fires-in-every-arrival-order
  (doseq [calendar? [false true]
          order     [[:rule :at :start :end] [:start :end :at :rule]
                     [:at :start :rule :end] [:end :rule :start :at]]]
    (tu/with-terms [presentAt presentDuring Party Noon]
      (let [c       'CxUniverse
            t       (if calendar? '(InstantFn 2000 6 1 12 0 0) Noon)
            [lo hi] (if calendar? '[(InstantFn 2000 1 1 0 0 0) (InstantFn 2001 1 1 0 0 0)] [t t])
            facts   {:at    (list presentAt Party t)
                     :start (list 'instantBefore (list 'StartFn Party) lo)
                     :end   (list 'instantBefore hi (list 'EndFn Party))}
            body    [(list presentAt '?x '?t) '(includesInstant ?x ?t)]
            derived #(set (map :sentence (v/sentexes-matching kb (list presentDuring '?x '?t) c)))]
        (doseq [k order]
          (if (= k :rule)
            (v/assert-rule kb body (list presentDuring '?x '?t) c {:direction :forward})
            (v/assert kb (facts k) c)))
        (testing (pr-str (if calendar? :calendar :symbol) order)
          (is (= #{(list presentDuring Party t)} (derived)))
          (is (= [{'?x Party '?t t}] (vec (v/query kb body c))))
          (v/retract! kb (v/handle-of kb (:end facts) c))
          (is (empty? (derived))))))))

(tu/deftest-kb an-open-inclusion-ranges-over-what-the-network-names
  (tu/with-terms [Party Noon Dusk]
    (let [c 'CxUniverse]
      (v/assert kb (list 'instantBefore (list 'StartFn Party) Noon) c)
      (v/assert kb (list 'instantBefore Noon (list 'EndFn Party)) c)
      (v/assert kb (list 'instantBefore (list 'EndFn Party) Dusk) c)
      (is (= #{{'?x Party} {'?x 'Forever}} (set (v/query kb (list 'includesInstant '?x Noon) c))))
      (is (= #{Noon (list 'StartFn Party)}
             (set (map '?t (v/query kb (list 'includesInstant Party '?t) c)))))
      (is (= #{Dusk (list 'EndFn Party)}
             (set (map '?t (v/query kb (list 'not (list 'includesInstant Party '?t)) c))))))))

(defn- tightest-start-bounds
  "The set of `tightestStartBoundOf` answers for `x` read from `c`."
  [kb x c]
  (set (map '?t (v/ask kb (list 'tightestStartBoundOf x '?t) c))))

(tu/deftest-kb two-unordered-lower-bounds-give-no-tightest-start-bound-until-a-fact-orders-them
  (tu/with-terms [Now Clock1 Clock2]
    (let [c 'CxUniverse]
      (v/assert kb (list 'instantNotBefore Now Clock1) c)
      (v/assert kb (list 'instantAfter Now Clock2) c)
      (is (= #{} (tightest-start-bounds kb Now c)))
      (v/assert kb (list 'instantBefore Clock1 Clock2) c)
      (is (= #{Clock2} (tightest-start-bounds kb Now c))))))

(tu/deftest-kb two-lower-bounds-stated-equal-are-both-tightest-start-bounds
  (tu/with-terms [Now Clock1 Clock2]
    (let [c 'CxUniverse]
      (v/assert kb (list 'instantNotBefore Now Clock1) c)
      (v/assert kb (list 'instantEqual Clock1 Clock2) c)
      (is (= #{Clock1 Clock2} (tightest-start-bounds kb Now c))))))

(tu/deftest-kb a-tightest-start-bound-reads-the-facts-the-asking-context-sees
  (tu/with-terms [Now Clock1 Clock2 CxLog CxLogSpec]
    (let [c 'CxUniverse]
      (v/assert kb (list 'genlCx CxLogSpec CxLog) c)
      (v/assert kb (list 'instantNotBefore Now Clock1) c)
      (v/assert kb (list 'instantBefore Clock1 Clock2) c)
      (v/assert kb (list 'instantNotBefore Now Clock2) CxLog)
      (is (= [#{Clock1} #{Clock2} #{Clock2}]
             (map #(tightest-start-bounds kb Now %) [c CxLog CxLogSpec]))))))

(tu/deftest-kb a-bound-the-point-terms-alone-fix-is-no-tightest-start-bound
  (tu/with-terms [Party Dawn]
    (let [c 'CxUniverse]
      (is (= #{} (tightest-start-bounds kb Party c)))
      (v/assert kb (list 'instantNotBefore (list 'StartFn Party) Dawn) c)
      (is (= #{Dawn} (tightest-start-bounds kb Party c))))))
