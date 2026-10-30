;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.sync-test
  "`sync!` locks CxUniverse's premises about the engine's vocabulary to the shipped files,
  brings the middle contexts to what this engine ships, and touches nothing an author put
  anywhere else, nor a premise naming an author's term.

  Each test builds its KB in a private in-RAM space of this namespace's own, restored from
  the suite's starter or upper dump, so the edits a test makes to the shipped contexts
  never reach a KB another namespace holds.  A test whose subject is the author's writes
  makes them in both arrival orders, each over a KB of its own."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.host.sync :as sync]
            [vaelii.impl.io.text :as text]
            [vaelii.test-util :as tu]))

(def ^:private ships
  "The starter's content, computed once: `sync/premises` loads the starter into a
  scratch KB, which is what a test would otherwise pay for per call."
  (delay (sync/premises)))

(defn- open-kb
  [k load!]
  (doto (v/open-kb (assoc tu/starter-build-space :space [::shipped k]))
    (tu/clear-kb!)
    (load!)))

(defn- in-orders
  "Run `check` once per entry of `orders`, `{name [write …]}` with each write a fn of the
  KB, over a starter KB of its own that the entry's writes are applied to in turn."
  [k orders check]
  (doseq [[order ws] orders]
    (let [kb (open-kb [k order] tu/load-starter!)]
      (try
        (run! #(% kb) ws)
        (testing order (check kb))
        (finally (tu/clear-kb! kb))))))

(defn- in-both-orders
  "`in-orders` over `writes` as given and reversed."
  [k writes check]
  (in-orders k {"forward" writes "reversed" (reverse writes)} check))

(defn- shipped-form
  "The first shipped entry in `context` whose form satisfies `pred`."
  [context pred]
  (first (filter #(and (= context (:context %)) (pred (:form %))) @ships)))

(defn- monotonic? [form] (and (seq? form) (= 'set/monotonic (first form))))

(defn- plain-fact?
  "A default fact under a plain functor: no wrapper, no rule, no namespaced functor."
  [form]
  (and (seq? form) (symbol? (first form)) (nil? (namespace (first form)))
       (not (monotonic? form)) (not ('#{implies exceptWhen genlCx} (first form)))))

(def ^:private in-sync {:add [] :remove []})

(deftest a-kb-built-by-this-engine-is-in-sync
  (testing "the starter"
    (let [kb (open-kb :starter tu/load-starter!)]
      (try
        (is (= in-sync (sync/plan kb @ships)))
        (finally (tu/clear-kb! kb)))))
  (testing "a vocabulary KB gains none of the middle contexts it does not have"
    (let [kb (open-kb :core tu/load-core!)]
      (try
        (is (= in-sync (sync/plan kb @ships)))
        (finally (tu/clear-kb! kb))))))

(def ^:private note
  "An author's premise in CxUniverse that names only shipped terms."
  '(comment mammal "an author's note on a shipped term"))

(deftest an-author-premise-about-shipped-terms-in-cxuniverse-is-retracted
  (let [other '(comment bird "another author's note")]
    (in-both-orders :authored
                    [#(v/assert % note 'CxUniverse)
                     #(v/assert % other 'CxUniverse)]
                    (fn [kb]
                      (is (= #{['CxUniverse note] ['CxUniverse other]}
                             (set (map (juxt :context :form) (:remove (sync/plan kb @ships))))))
                      (is (= {:added 0 :removed 2 :refused []} (sync/sync! kb @ships)))
                      (is (nil? (v/handle-of kb note 'CxUniverse)))
                      (is (= in-sync (sync/plan kb @ships)))))))

(deftest a-sync-one-change-at-a-time-reports-each-and-stops-between-two
  (let [other '(comment bird "another author's note")]
    (in-orders :each
               {"reported" [#(v/assert % note 'CxUniverse) #(v/assert % other 'CxUniverse)]}
               (fn [kb]
                 (let [seen (atom [])]
                   (is (= {:added 0 :removed 2 :forwarded 0 :refused []}
                          (sync/sync-each! kb @ships #(swap! seen conj %))))
                   (is (= [0 1 2] (map :done @seen)) "each change, then the end")
                   (is (every? #(= 2 (:total %)) @seen) "the plan's size, known from the start")
                   (is (= #{note other} (set (keep (comp :form :op) @seen))))
                   (is (every? #(= :remove (:op (:op %))) (butlast @seen)))
                   (is (= in-sync (sync/plan kb @ships))))))
    (in-orders :each-stopped
               {"stopped" [#(v/assert % note 'CxUniverse) #(v/assert % other 'CxUniverse)]}
               (fn [kb]
                 (is (thrown? clojure.lang.ExceptionInfo
                              (sync/sync-each! kb @ships
                                               #(when (= 1 (:done %)) (throw (ex-info "stop" {}))))))
                 (is (= 1 (count (:remove (sync/plan kb @ships))))
                     "the first change settled; the rerun's plan is what is left")
                 (is (= {:added 0 :removed 1 :forwarded 0 :refused []} (sync/sync-each! kb @ships (fn [_]))))
                 (is (= in-sync (sync/plan kb @ships)))))))

(defn- forward-rule? [form] (and (seq? form) (= 'set/forwardRule (first form))))

(defn- retract-held!
  "Retract the premise `kb` holds as `form` in `context`, found by its file form."
  [kb context form]
  (v/edit! kb {:remove (vec (:handles (get (sync/held kb) [context form])))}))

(deftest a-forward-rule-lands-backward-and-is-turned-forward-after-the-content
  (let [{:keys [context form]} (shipped-form 'CxUniverse forward-rule?)
        backward (list 'set/backwardRule (second form))
        ;; backward is the default direction, so a file renders the held rule bare
        held-backward (second form)]
    (in-orders :forwarded
               {"missing" [#(retract-held! % context form)]}
               (fn [kb]
                 (let [seen (atom [])]
                   (is (= {:added 1 :removed 0 :forwarded 1 :refused []}
                          (sync/sync-each! kb @ships #(swap! seen conj %))))
                   (is (= [{:op :add :context context :form backward}
                           {:op :forward :context context :form form}]
                          (keep :op @seen))
                       "the rule lands backward with the content, and turns forward last")
                   (is (= [0 1 2] (map :done @seen)))
                   (is (= in-sync (sync/plan kb @ships)))
                   (is (some? (get (sync/held kb) [context form])))
                   (is (nil? (get (sync/held kb) [context held-backward]))
                       "one record, raised to forward in place"))))
    (in-orders :forwarded-stopped
               {"missing" [#(retract-held! % context form)]}
               (fn [kb]
                 (is (thrown? clojure.lang.ExceptionInfo
                              (sync/sync-each! kb @ships
                                               #(when (= :forward (:op (:op %)))
                                                  (throw (ex-info "stop" {}))))))
                 (is (some? (get (sync/held kb) [context held-backward]))
                     "stopped between the stages, the KB holds the rule backward")
                 (is (= {:added 1 :removed 0 :forwarded 1 :refused []}
                        (sync/sync-each! kb @ships (fn [_])))
                     "the rerun turns the held backward rule forward rather than retracting it")
                 (is (= in-sync (sync/plan kb @ships)))))))

(deftest a-rule-whose-direction-changed-is-one-record-raised-or-restated
  (let [{:keys [context form]} (shipped-form 'CxUniverse forward-rule?)
        rule (second form)]
    (in-orders :raised
               {"held backward" [#(retract-held! % context form) #(v/assert % rule context)]}
               (fn [kb]
                 (is (= {:add [{:context context :form form}] :remove []} (sync/plan kb @ships))
                     "the forward assert raises the held rule; nothing is retracted")
                 (is (= {:added 1 :removed 0 :refused []} (sync/sync! kb @ships)))
                 (is (some? (get (sync/held kb) [context form])))
                 (is (= in-sync (sync/plan kb @ships)))))
    (let [lowered (mapv #(if (and (= context (:context %)) (= form (:form %)))
                           (assoc % :form (list 'set/backwardRule rule))
                           %)
                        @ships)]
      (in-orders :lowered
                 {"held forward" []}
                 (fn [kb]
                   (is (= {:added 1 :removed 1 :refused []} (sync/sync! kb lowered))
                       "nothing lowers a direction in place: retracted, then stated backward")
                   (is (some? (get (sync/held kb) [context rule])))
                   (is (nil? (get (sync/held kb) [context form])))
                   (is (= in-sync (sync/plan kb lowered))))))))

(deftest a-premise-naming-a-term-the-engine-does-not-ship-survives-the-sync
  (let [fact '(unary_predicate shipped_authored_kind)
        rule '(implies (bird ?x) (shipped_flagged ?x))]
    (in-both-orders :foreign
                    [#(v/assert % fact 'CxUniverse)
                     #(v/assert % '(arity shippedAuthoredRelation 2) 'CxUniverse)
                     #(v/assert % rule 'CxBiology)]
                    (fn [kb]
                      (is (= in-sync (sync/plan kb @ships)))
                      (is (= {:added 0 :removed 0 :refused []} (sync/sync! kb @ships)))
                      (is (some? (v/handle-of kb fact 'CxUniverse)))
                      (is (some? (v/handle-of kb rule 'CxBiology)))))))

(deftest a-premise-naming-an-authors-term-is-never-rendered-by-the-plan
  ;; a corpus keeps its own content in CxUniverse; the plan reads past it by its terms
  ;; rather than rendering each premise as a file form and dropping it afterwards
  (let [foreign '(comment shipped_authored_kind "an author's note on an author's term")]
    (in-orders :rendered
               {"authored" [#(v/assert % foreign 'CxUniverse)]}
               (fn [kb]
                 (let [rendered (atom #{})
                       entries  @#'text/premise-entries]
                   (with-redefs [text/premise-entries
                                 (fn [kb sxs] (swap! rendered into (map v/sentence-of sxs))
                                   (entries kb sxs))]
                     (is (= in-sync (sync/plan kb @ships))))
                   (is (seq @rendered) "the premises about the engine's own terms are read")
                   (is (not (contains? @rendered foreign))))))))

(deftest an-author-genlcx-edge-survives-the-sync
  (tu/with-terms [CxAuthorAbove CxAuthorBelow]
    (in-both-orders :edges
                    [#(v/assert % (list 'genlCx 'CxUniverse CxAuthorAbove) 'CxUniverse)
                     #(v/assert % (list 'genlCx CxAuthorBelow 'CxWell) CxAuthorBelow)]
                    (fn [kb]
                      (is (= in-sync (sync/plan kb @ships)))
                      (is (= {:added 0 :removed 0 :refused []} (sync/sync! kb @ships)))
                      (is (some? (v/handle-of kb (list 'genlCx 'CxUniverse CxAuthorAbove) 'CxUniverse)))
                      (is (some? (v/handle-of kb (list 'genlCx CxAuthorBelow 'CxWell) 'CxUniverse)))))))

(deftest a-lifted-copy-of-a-data-context-binding-survives-the-sync
  ;; `(binary_predicate R)` stated in a data context has a copy in CxUniverse, which is no
  ;; premise, so the lock does not reach it.
  (tu/with-terms [CxAuthorData tiedTo]
    (let [binding (list 'binary_predicate tiedTo)]
      (in-both-orders :lifted
                      [#(v/assert % (list 'genlCx CxAuthorData 'CxWell) 'CxUniverse)
                       #(v/assert % binding CxAuthorData)]
                      (fn [kb]
                        (let [copy (v/handle-of kb binding 'CxUniverse)]
                          (is (some? copy))
                          (is (false? (v/premise? kb copy)) "the copy is no premise")
                          (is (= {:added 0 :removed 0 :refused []} (sync/sync! kb @ships)))
                          (is (= copy (v/handle-of kb binding 'CxUniverse)))
                          (is (v/in? kb copy))))))))

(deftest a-sentence-removed-from-a-shipped-file-is-retracted
  (let [gone (shipped-form 'CxUniverse plain-fact?)
        less (into [] (remove #(= gone %)) @ships)]
    ;; the premise as the load stored it, and retracted and stated again after the rest
    (in-orders :removed
               {"loaded"   [#(v/assert % note 'CxUniverse)]
                "restated" [#(v/assert % note 'CxUniverse)
                            #(v/retract! % (v/handle-of % (:form gone) 'CxUniverse))
                            #(v/assert % (:form gone) 'CxUniverse)]}
               (fn [kb]
                 (is (= #{['CxUniverse (:form gone)] ['CxUniverse note]}
                        (set (map (juxt :context :form) (:remove (sync/plan kb less)))))
                     "the plan retracts a premise the files no longer state")
                 (is (= {:added 0 :removed 2 :refused []} (sync/sync! kb less)))
                 (is (nil? (v/handle-of kb (:form gone) 'CxUniverse)))
                 (is (= in-sync (sync/plan kb less)))))))

(deftest a-stale-kb-is-brought-to-what-ships
  (let [;; a shipped fact the KB lost
        missing   (shipped-form 'CxUniverse plain-fact?)
        ;; a known-true one the KB holds at :default, outside the forced-monotonic set
        weakened  (let [kb (open-kb :pick tu/load-core!)]
                    (try
                      (first (filter #(and (= 'CxUniverse (:context %))
                                           (monotonic? (:form %))
                                           (let [s (second (:form %))]
                                             (and (seq? s) (symbol? (first s))
                                                  (not ('#{genlCx implies} (first s)))
                                                  (not (v/has-prop? kb :forced-monotonic (first s))))))
                                     @ships))
                      (finally (tu/clear-kb! kb))))
        wsentence (second (:form weakened))
        ;; an author's own context wired below the middle contexts
        user-fact '(unary_predicate shipped_authored_kind)]
    (tu/with-terms [CxAuthored]
      (in-both-orders :stale
                      [#(v/retract! % (v/handle-of % (:form missing) 'CxUniverse))
                       #(do (v/retract! % (v/handle-of % wsentence 'CxUniverse))
                            (v/assert % wsentence 'CxUniverse))
                       #(v/assert % (list 'genlCx CxAuthored 'CxWell) 'CxUniverse)
                       #(v/assert % user-fact CxAuthored)]
                      (fn [kb]
                        (is (= #{{:context 'CxUniverse :form (:form missing)}
                                 {:context 'CxUniverse :form (:form weakened)}}
                               (set (:add (sync/plan kb @ships)))))
                        (is (= {:added 2 :removed 0 :refused []} (sync/sync! kb @ships)))
                        (is (= :monotonic (:strength (v/sentex kb (v/handle-of kb wsentence 'CxUniverse))))
                            "a raised strength is restated")
                        (is (= in-sync (sync/plan kb @ships)))
                        (is (some? (v/handle-of kb user-fact CxAuthored))
                            "the author's context is left alone"))))))

(deftest a-lowered-strength-is-retracted-and-restated
  (let [lowered  (shipped-form 'CxUniverse plain-fact?)
        sentence (:form lowered)]
    (in-both-orders :lowered
                    [#(v/assert % sentence 'CxUniverse {:strength :monotonic})
                     #(v/assert % note 'CxUniverse)]
                    (fn [kb]
                      (testing "the plan retracts the known-true form and asserts the default one"
                        (is (= {:add    [{:context 'CxUniverse :form sentence}]
                                :remove #{['CxUniverse (list 'set/monotonic sentence)]
                                          ['CxUniverse note]}}
                               (update (sync/plan kb @ships) :remove
                                       #(into #{} (map (juxt :context :form)) %)))))
                      (testing "the sync leaves it held at :default"
                        (is (= {:added 1 :removed 2 :refused []} (sync/sync! kb @ships)))
                        (is (= :default (:strength (v/sentex kb (v/handle-of kb sentence 'CxUniverse)))))
                        (is (= in-sync (sync/plan kb @ships))))))))

(deftest an-addition-the-batch-refuses-is-set-aside-and-lands-after-it
  (let [kb      (open-kb :aside tu/load-starter!)
        ;; a `genl` edge and its reverse close a cycle, which is refused
        lost    '(genl dog mammal)
        clash   '(genl mammal dog)
        edits   (atom 0)
        edit!   v/edit!]
    (try
      (v/retract! kb (v/handle-of kb lost 'CxUniverse))
      ;; an author's edge the lost one would close a cycle with, in the exact context the
      ;; sync retracts it from: the batch asserts before it retracts, so it refuses the
      ;; shipped edge, and the edge lands once the batch has retracted the author's
      (v/assert kb clash 'CxUniverse)
      (with-redefs [v/edit! (fn [& args] (swap! edits inc) (apply edit! args))]
        (is (= {:added 1 :removed 1 :refused []} (sync/sync! kb @ships))))
      (testing "the batch refused the edge, and ran again without it"
        (is (= 2 @edits)))
      (is (some? (v/handle-of kb lost 'CxUniverse)))
      (is (nil? (v/handle-of kb clash 'CxUniverse)))
      (is (= in-sync (sync/plan kb @ships)))
      (finally (tu/clear-kb! kb)))))

(deftest an-exception-the-engine-does-not-ship-goes-with-its-rule
  (let [kb   (open-kb :except tu/load-starter!)
        rule '(implies (bird ?x) (mammal ?x))
        form (list 'exceptWhen '(fish ?x) rule)]
    (try
      (v/assert kb form 'CxBiology)
      (let [[entry] (:remove (sync/plan kb @ships))]
        (testing "the wrapper is one entry naming both records"
          (is (= form (:form entry)))
          (is (= 2 (count (:handles entry))))))
      (is (= {:added 0 :removed 1 :refused []} (sync/sync! kb @ships)))
      (is (nil? (v/handle-of kb rule 'CxBiology)))
      (is (= in-sync (sync/plan kb @ships)))
      (finally (tu/clear-kb! kb)))))

(deftest write-back-edits-one-line-per-premise
  (let [dir   (io/file (System/getProperty "java.io.tmpdir") (str "vaelii-write-back-" (System/nanoTime)))
        core  (io/file dir "core.txt")
        other (io/file dir "other.txt")
        kb    (open-kb :write-back (fn [_]))
        u     'CxUniverse]
    (try
      (.mkdirs dir)
      (spit core (str ";; core\n(comment dog \"A dog.\")\n(genl dog mammal)\n\n"
                      "(comment bird \"A bird.\")\n(genl bird animal)\n"))
      (spit other (str "(comment cat \"A cat.\")\n(genl cat mammal)\n"
                       ";; a cat is a mammal\n(implies (and (cat ?c))\n         (mammal ?c))\n"))
      (let [report (sync/write-back!
                    kb
                    {:add    [{:context u :form '(set/monotonic (genl dog mammal))}
                              {:context u :form '(set/monotonic (folk_species dog))}
                              {:context u :form '(genl zebra mammal)}
                              {:context u :form '(genl cat feline)}]
                     :remove [{:context u :form '(genl dog mammal)}
                              {:context u :form '(implies (and (cat ?x)) (mammal ?x))}
                              {:context u :form '(genl absent mammal)}
                              {:context 'CxNowhere :form '(genl dog mammal)}]}
                    #(when (= u %) [core other]))]
        (is (= {:written 5
                :skipped [{:context 'CxNowhere :form '(genl dog mammal)}
                          {:context u :form '(genl absent mammal)}]}
               (update report :skipped #(sort-by (comp str :context) %))))
        (testing "a strength change is rewritten in place, and an addition joins its term's block"
          (is (= (str ";; core\n(comment dog \"A dog.\")\n(set/monotonic (genl dog mammal))\n"
                      "(set/monotonic (folk_species dog))\n\n"
                      "(comment bird \"A bird.\")\n(genl bird animal)\n\n(genl zebra mammal)\n")
                 (slurp core))))
        (testing "a removal matches the sentence under other variable names, and comments stay"
          (is (= "(comment cat \"A cat.\")\n(genl cat mammal)\n;; a cat is a mammal\n(genl cat feline)\n"
                 (slurp other)))))
      (finally
        (tu/clear-kb! kb)
        (run! io/delete-file (reverse (file-seq dir)))))))

(deftest write-back-writes-a-form-whole-under-a-callers-print-bound
  (let [dir  (io/file (System/getProperty "java.io.tmpdir") (str "vaelii-write-back-" (System/nanoTime)))
        core (io/file dir "core.txt")
        kb   (open-kb :write-back-bound (fn [_]))
        u    'CxUniverse]
    (try
      (.mkdirs dir)
      (spit core "(comment dog \"A dog.\")\n(genl dog mammal)\n")
      (binding [*print-length* 2 *print-level* 1]
        (sync/write-back! kb
                          {:add    [{:context u :form '(set/monotonic (genl dog mammal))}
                                    {:context u :form '(implies (and (dog ?d) (pet ?d)) (mammal ?d))}]
                           :remove [{:context u :form '(genl dog mammal)}]}
                          #(when (= u %) [core])))
      (is (= (str "(comment dog \"A dog.\")\n(set/monotonic (genl dog mammal))\n\n"
                  "(implies (and (dog ?d) (pet ?d)) (mammal ?d))\n")
             (slurp core)))
      (finally
        (tu/clear-kb! kb)
        (run! io/delete-file (reverse (file-seq dir)))))))
