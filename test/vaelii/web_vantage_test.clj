;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.web-vantage-test
  "The /vantage page: what a sentence pattern or a term reads as from a context, from the
  contexts it sees that store a match, and from the contexts that see it.  Each test builds
  one of the five cases docs/web.md names and reads the rows the drawing holds."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.svg :as svg]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defn- GET [kb qs]
  ((web/app kb) (cond-> {:request-method :get :uri "/vantage"} qs (assoc :query-string qs))))

(defn- enc [x] (java.net.URLEncoder/encode (pr-str x) "UTF-8"))

(defn- drawn
  "The /vantage page for `q` at `ctx`, and the scenes `svg/scene` drew answering it."
  [kb ctx q]
  (let [seen (atom [])
        orig svg/scene
        r    (with-redefs [svg/scene (fn [s] (swap! seen conj s) (orig s))]
               (GET kb (str "ctx=" (enc ctx) "&q=" (enc q))))]
    [r @seen]))

(defn- cards
  "Each card of `scene` by context, as `[[text class note] …]` in the order drawn."
  [scene]
  (into {} (for [n (:nodes scene)] [(:term n) (mapv (juxt :text :class :note) (:rows n))])))

(defn- believed-rows-agree-with-ask
  "Whether every card of `scene` draws a sentence believed exactly where `v/ask?` answers
  it true at the card's context."
  [kb scene]
  (every? true?
          (for [n (:nodes scene)
                [form rows] (group-by :form (:rows n))]
            (= (boolean (some #(not= "g-out" (:class %)) rows))
               (boolean (v/ask? kb form (:term n)))))))

(defn- drawn-ok
  "The scene `drawn` answers `q` at `ctx` with, after checking the page answered, the scene
  is the vantage drawing, it has no fault and its believed rows agree with `v/ask?`."
  [kb ctx q]
  (let [[r scenes] (drawn kb ctx q)
        scene      (first scenes)]
    (is (= 200 (:status r)))
    (is (= 1 (count scenes)))
    (is (str/starts-with? (:aria-label scene) "vantage of "))
    (is (= [] (svg/faults scene)))
    (is (believed-rows-agree-with-ask kb scene))
    scene))

(tu/deftest-kb the-page-without-a-context-or-a-pattern-is-the-form-alone
  (let [r (GET kb nil)]
    (is (= 200 (:status r)))
    (is (re-find #"<form[^>]*action=\"/vantage\"" (:body r)))
    (is (not (re-find #"kb-graph-fig" (:body r))))))

(tu/deftest-kb an-except-hides-the-sentence-where-it-is-stated-and-not-above
  (tu/with-terms [dog Rex CxStory CxDream]
    (v/assert kb (list 'genlCx CxStory 'CxWell) 'CxUniverse)
    (v/assert kb (list 'genlCx CxDream CxStory) 'CxUniverse)
    (v/assert kb (list dog Rex) CxStory)
    (v/assert kb (list 'except (list 'ist CxStory (list dog Rex))) CxDream)
    (let [c (cards (drawn-ok kb CxStory (list dog Rex)))
          s (str "(" dog " " Rex ")")]
      (is (= {CxStory [[s "g-stated" "stored here · stated · believed"]]
              CxDream [[s "g-out" (str "from " CxStory " · stated · hidden by the except in " CxDream)]]}
             c)))))

(tu/deftest-kb a-defeat-withdraws-a-conclusion-from-its-own-context-and-not-a-sibling
  (tu/with-terms [Pip CxStory CxScene CxOtherScene]
    (v/assert kb (list 'genlCx CxStory 'CxWell) 'CxUniverse)
    (v/assert kb (list 'genlCx CxScene CxStory) 'CxUniverse)
    (v/assert kb (list 'genlCx CxOtherScene CxStory) 'CxUniverse)
    (v/assert kb (list 'bird Pip) CxStory)
    (v/assert kb (list 'not (list 'able Pip 'flying)) CxScene {:strength :monotonic})
    (let [c (cards (drawn-ok kb CxStory (list 'able Pip 'flying)))
          s (str "(able " Pip " flying)")]
      (is (= [[s "g-derived" "stored here · derived · believed"]] (c CxStory)))
      (is (= [[s "g-derived" (str "from " CxStory " · derived · believed")]] (c CxOtherScene)))
      (is (= [[s "g-out" (str "from " CxStory " · derived · defeated by the defeat in " CxScene)]
              [(str "(not " s ")") "g-stated" "stored here · stated · believed"]]
             (c CxScene))))))

(tu/deftest-kb a-decontextualized-copy-names-the-context-it-was-copied-from
  (tu/with-terms [codeOf Code17 CxShelf CxLedger CxAtlas]
    (v/assert kb (list 'decontextualized_predicate codeOf) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx CxShelf 'CxWell) 'CxUniverse)
    (v/assert kb (list 'genlCx CxLedger CxShelf) 'CxUniverse)
    (v/assert kb (list 'genlCx CxAtlas CxShelf) 'CxUniverse)
    (v/assert kb (list codeOf 'dog Code17) CxLedger)
    (v/assert kb (list 'not (list codeOf 'dog Code17)) CxAtlas)
    (let [c   (cards (drawn-ok kb CxShelf (list codeOf 'dog Code17)))
          s   (str "(" codeOf " dog " Code17 ")")
          lift (fn [from] (str "copied from " from " by decontextualized_predicate · believed"))]
      (is (= #{CxShelf 'CxUniverse CxAtlas CxLedger} (set (keys c))) "the context, its ancestor and its children")
      (is (= [[(str "(not " s ")") "g-derived" (str "stored here · " (lift CxAtlas))]
              [s "g-derived" (str "stored here · " (lift CxLedger))]]
             (c 'CxUniverse)))
      (testing "the context stating the denial reads both polarities, which is a dilemma"
        (is (= [[(str "(not " s ")") "g-derived" (str "from CxUniverse · " (lift CxAtlas))]
                [(str "(not " s ")") "g-stated" "stored here · stated · believed"]
                [s "g-derived" (str "from CxUniverse · " (lift CxLedger))]]
               (c CxAtlas)))))))

(tu/deftest-kb each-time-slice-reads-the-status-stored-in-it
  (tu/with-terms [statusOf reviewerOf Pr1 Ann Draft Open CxTracker]
    (let [year  (list 'CxTimeFn CxTracker '(YearFn 2026))
          sept  (list 'CxTimeFn CxTracker '(MonthFn 2026 9))
          oct   (list 'CxTimeFn CxTracker '(MonthFn 2026 10))]
      (v/assert kb (list 'genlCx CxTracker 'CxWell) 'CxUniverse)
      (v/assert kb (list 'ist sept (list statusOf Pr1 Draft)) 'CxUniverse)
      (v/assert kb (list 'ist oct (list statusOf Pr1 Open)) 'CxUniverse)
      (v/assert kb (list 'ist year (list reviewerOf Pr1 Ann)) 'CxUniverse)
      (let [scene (drawn-ok kb CxTracker Pr1)
            text  (into {} (for [n (:nodes scene)] [(:term n) (mapv :text (:rows n))]))]
        (is (= 4 (count (:nodes scene))) "the tracker and its three slices")
        (is (= [] (text CxTracker)))
        (testing "a month slice reads its own status and the year's reviewer, and not the other month's status"
          (is (= #{[(str "(" reviewerOf " " Pr1 " " Ann ")") (str "(" statusOf " " Pr1 " " Draft ")")]
                   [(str "(" reviewerOf " " Pr1 " " Ann ")") (str "(" statusOf " " Pr1 " " Open ")")]}
                 (set (for [[_ rows] text :when (= 2 (count rows))] rows)))))))))

(deftest a-labeling-holds-its-own-truth-values-and-no-other-labeling-s
  (when (solver/available?)
    ;; the isolated space: clearing the scratch space would take the starter this
    ;; namespace's `:once` fixture holds
    (tu/with-cleared-kb [kb #(tu/load-interface! (tu/isolated-fresh))]
      (tu/with-terms [candidate colorOf Item CxBase CxPlan]
        (v/assert kb (list 'genlCx CxBase 'CxUniverse) 'CxUniverse)
        (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list colorOf '?c 'red)))
                  CxBase)
        (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list colorOf '?c 'blue)))
                  CxBase)
        (v/assert kb (list 'functional colorOf) CxBase)
        (v/assert kb (list candidate Item) CxBase)
        (let [{:keys [labelings]} (v/assert kb (list 'do/label CxBase CxPlan) CxBase)
              c (cards (drawn-ok kb CxBase (list colorOf Item '?c)))]
          (is (= 2 (count labelings)))
          (is (= [] (c CxBase)))
          (testing "each labeling stores one colour and denies the other, and believes neither"
            (doseq [{:keys [context]} labelings]
              (is (= 2 (count (c context))))
              (is (every? #(= ["g-out" "stored here · not believed: unsupported"] (rest %)) (c context)))))
          (is (not= (set (map first (c (:context (first labelings)))))
                    (set (map first (c (:context (second labelings))))))))))))

(tu/deftest-kb the-vantage-drawing-is-the-same-bytes-whatever-the-assertion-order
  (let [fig (fn [ctxs]
              (tu/with-terms [Pip CxStory CxScene CxOtherScene]
                (let [facts [[(list 'genlCx CxStory 'CxWell) 'CxUniverse {}]
                             [(list 'genlCx CxScene CxStory) 'CxUniverse {}]
                             [(list 'genlCx CxOtherScene CxStory) 'CxUniverse {}]
                             [(list 'bird Pip) CxStory {}]
                             [(list 'not (list 'able Pip 'flying)) CxScene {:strength :monotonic}]]]
                  (doseq [[s c o] (ctxs facts)] (v/assert kb s c o))
                  (-> (:body (first (drawn kb CxStory (list 'able Pip 'flying))))
                      (->> (re-find #"(?s)<figure class=\"kb-graph-fig\">.*?</figure>"))
                      (str/replace #"/sentex/\d+" "/sentex/N")
                      (str/replace (str CxOtherScene) "CxO")
                      (str/replace (str CxScene) "CxS")
                      (str/replace (str CxStory) "CxT")
                      (str/replace (str Pip) "Pip")))))]
    (let [forward (fig identity)]
      (is (some? forward))
      (is (= forward (fig reverse))))))

(tu/deftest-kb a-card-draws-eight-rows-and-the-drawing-twelve-contexts
  (tu/with-terms [mark CxHub]
    (let [kids (repeatedly 12 #(tu/tmp-ctx "Kid"))]
      (v/assert kb (list 'genlCx CxHub 'CxWell) 'CxUniverse)
      (doseq [k kids] (v/assert kb (list 'genlCx k CxHub) 'CxUniverse))
      (dotimes [_ 9] (v/assert kb (list mark (tu/tmp-ind "Item")) CxHub))
      (let [[r [scene]] (drawn kb CxHub (list mark '?x))
            hub         (first (filter #(= CxHub (:term %)) (:nodes scene)))]
        (is (= [] (svg/faults scene)))
        (is (= 12 (count (:nodes scene))))
        (is (= 8 (count (:rows hub))))
        (is (= ["1 more not drawn"] (:more-lines hub)))
        (is (re-find #"showing 11 of 12 contexts that see" (:body r)))
        (is (re-find #"1 more not listed" (:body r)))))))

(tu/deftest-kb a-parameter-the-page-cannot-read-is-a-400
  (tu/with-terms [CxStory]
    (doseq [qs [(str "ctx=" CxStory "&q=(dog")
                (str "ctx=" CxStory "&q=5")
                "ctx=%3Fc&q=Rex"
                "ctx=CxEverything&q=Rex"]]
      (is (= 400 (:status (GET kb qs))) qs))))
