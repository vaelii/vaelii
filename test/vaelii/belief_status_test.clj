;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.belief-status-test
  "Contextual belief introspection: own-context belief, exception force, and inheritance stay
  distinct while the status report agrees with the boolean and matching surfaces."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.except :as exc]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(deftest raw-in-doc-points-to-contextual-diagnostics
  (is (re-find #"belief-status" (:doc (meta #'v/believed?)))
      "the own-context read points a caller at the diagnostic for contextual disagreement"))

(tu/deftest-kb contextual-belief-status-separates-every-condition
  (tu/with-terms [bright gem CxTop CxSibling CxLeaf]
    (v/assert kb (list 'genlCx CxTop 'CxWell) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx CxSibling 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [inherit-h (v/assert kb (list 'genlCx CxLeaf CxTop) 'CxUniverse
                              {:strength :monotonic})
          h (v/assert kb (list bright gem) CxTop {:strength :monotonic})]
      (testing "a context that does not see the assertion context does not believe the fact"
        (let [status (v/belief-status kb h CxSibling)]
          (is (not (v/believed? kb h CxSibling)))
          (is (= false (:believed? status)))
          (is (not (contains? status :visible?)) "the status answers belief once, as :believed?")
          (is (nil? (:inherited-path status)))
          (is (empty? (v/sentexes-matching kb (list bright gem) CxSibling)))))
      (testing "a visible inherited fact carries the exact genlCx support path"
        (let [status (v/belief-status kb h CxLeaf)]
          (is (= [{:handle inherit-h :context 'CxUniverse}]
                 (:inherited-path status)))
          (is (:believed? status))
          (is (= (:believed? status)
                 (v/ask? kb (list bright gem) CxLeaf)))))
      (testing "same-context inheritance is the empty path"
        (is (= [] (:inherited-path (v/belief-status kb h CxTop)))))
      (let [e2 (v/assert kb (list 'except (sx/sentex-handle h)) 'CxWell
                         {:strength :monotonic})
            e1 (v/assert kb (list 'except (sx/sentex-handle h)) CxTop
                         {:strength :monotonic})]
        (testing "an exception at the fact's own context hides it from a read naming no context"
          (let [status (v/belief-status kb h CxLeaf)]
            (is (not (v/believed? kb h)))
            (is (not (v/believed? kb h CxLeaf)))
            (is (= false (:believed? status)))
            (is (true? (:in? status)) "an except leaves the JTMS label IN")
            (is (:excepted? status))
            (is (false? (:withdrawn? status)) "an except is not a withdrawal")
            (is (= (sort-by str [CxTop 'CxWell])
                   (mapv #(-> (v/sentex kb (:handle %)) :context)
                         (:exceptions status))))
            (is (= status (v/belief-status kb h CxLeaf))
                "the branching forest is deterministic")))
        (testing "the cheap boolean makes one contextual exception query, not a global scan"
          (let [calls (atom 0)
                excepted? exc/excepted?]
            (with-redefs [exc/closure-excepted-anywhere?
                          (fn [& _]
                            (throw (ex-info "believed? scanned every exception context" {})))
                          exc/excepted?
                          (fn [& args]
                            (swap! calls inc)
                            (apply excepted? args))]
              (is (false? (v/believed? kb h CxLeaf)))
              (is (= 1 @calls)))))
        (let [m (v/assert kb (list 'except (sx/sentex-handle e1)) CxLeaf
                          {:strength :monotonic})]
          (testing "a meta-except restores one branch but another live branch still hides"
            (let [status (v/belief-status kb h CxLeaf)
                  roots  (into {} (map (juxt :handle identity)) (:exceptions status))]
              (is (= [{:handle m :in? true :in-force? true :excepted-by []}]
                     (:excepted-by (get roots e1))))
              (is (false? (:in-force? (get roots e1))))
              (is (:in-force? (get roots e2)))
              (is (:excepted? status))))
          (v/retract! kb e2)
          (testing "with the other branch gone, the meta-except restores belief"
            (let [status (v/belief-status kb h CxLeaf)]
              (is (v/believed? kb h CxLeaf))
              (is (= true (:believed? status)))
              (is (false? (:excepted? status))))))))))

(tu/deftest-kb status-covers-out-absent-and-malformed-handles
  (tu/with-terms [flies Tweety CxStatus]
    (v/assert kb (list 'genlCx CxStatus 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [h (v/assert kb (list flies Tweety) CxStatus {:strength :default})]
      (v/assert kb (list 'not (list flies Tweety)) CxStatus {:strength :monotonic})
      (testing "a defeated sentex is stored, IN in the network and withdrawn at its reader"
        (let [status (v/belief-status kb h CxStatus)]
          (is (:stored? status))
          (is (true? (:in? status)))
          (is (true? (:withdrawn? status)))
          (is (false? (:believed? status)))
          (is (false? (v/believed? kb h CxStatus)))))
      (testing "nil and an unknown integer without dangling exceptions are all false"
        (doseq [handle [nil 999999999]]
          (let [status (v/belief-status kb handle CxStatus)]
            (is (= handle (:handle status)))
            (is (false? (:stored? status)))
            (is (false? (:in? status)))
            (is (nil? (:assertion-context status)))
            (is (= [] (:exceptions status)))
            (is (false? (:excepted? status)))
            (is (nil? (:inherited-path status)))
            (is (false? (:believed? status)))
            (is (not (contains? status :visible?)))
            (is (false? (v/believed? kb handle CxStatus))))))
      (testing "a dangling exception remains diagnosable without making its target stored"
        ;; `assert` refuses an except over an unstored handle, so the except dangles only
        ;; once its target is retracted
        (let [missing (v/assert kb (list flies (tu/tmp-ind)) CxStatus {:strength :monotonic})
              eh (v/assert kb (list 'except (sx/sentex-handle missing)) CxStatus
                           {:strength :monotonic})
              _ (v/retract! kb missing)
              status (v/belief-status kb missing CxStatus)]
          (is (false? (:stored? status)))
          (is (false? (:in? status)))
          (is (= [eh] (mapv :handle (:exceptions status))))
          (is (:excepted? status))
          (is (false? (:believed? status)))
          (is (false? (v/believed? kb missing CxStatus)))))
      (testing "malformed handles keep the established typed refusal"
        (doseq [f [v/believed? v/belief-status]]
          (let [e (try (f kb [h] CxStatus) nil (catch clojure.lang.ExceptionInfo e e))]
            (is (= :bad-handle (:type (ex-data e))))))))))

(tu/deftest-kb exception-forest-order-follows-content-not-allocation
  (tu/with-terms [glows Alpha Beta CxA CxB CxReader]
    (v/assert kb (list 'genlCx CxReader CxA) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx CxReader CxB) 'CxUniverse {:strength :monotonic})
    (let [h1 (v/assert kb (list glows Alpha) CxReader {:strength :monotonic})
          h2 (v/assert kb (list glows Beta) CxReader {:strength :monotonic})]
      ;; Same semantic branches, opposite assertion order.
      (v/assert kb (list 'except (sx/sentex-handle h1)) CxA {:strength :monotonic})
      (v/assert kb (list 'except (sx/sentex-handle h1)) CxB {:strength :monotonic})
      (v/assert kb (list 'except (sx/sentex-handle h2)) CxB {:strength :monotonic})
      (v/assert kb (list 'except (sx/sentex-handle h2)) CxA {:strength :monotonic})
      (let [contexts (fn [h]
                       (mapv #(-> (v/sentex kb (:handle %)) :context)
                             (:exceptions (v/belief-status kb h CxReader))))]
        (is (= (sort-by str [CxA CxB]) (contexts h1) (contexts h2)))))))

(tu/deftest-kb linear-meta-except-chain-is-evaluated-once-per-node
  (tu/with-terms [rings Bell CxChain]
    (let [target (v/assert kb (list rings Bell) CxChain {:strength :monotonic})
          depth 40]
      (loop [target target, n depth]
        (when (pos? n)
          (recur (v/assert kb (list 'except (sx/sentex-handle target)) CxChain
                           {:strength :monotonic})
                 (dec n))))
      (let [reads (atom 0)
            in? jtms/in?
            status (with-redefs [jtms/in? (fn [& args]
                                            (swap! reads inc)
                                            (apply in? args))]
                     (v/belief-status kb target CxChain))
            node-count (fn node-count [nodes]
                         (+ (count nodes)
                            (reduce + 0 (map #(node-count (:excepted-by %)) nodes))))]
        (is (= depth (node-count (:exceptions status))))
        (is (<= @reads (+ depth 2))
            "one raw target read plus at most one cascade read per exception")))))

;; ---- the definition: a record is believed at C when it is IN, no defeat in force at C
;; removes it, no except C sees hides it, and C sees its context through genlCx; a read
;; that names no context answers at the record's own context (docs/glossary.md, "Belief")

(def ^:private M {:strength :monotonic})

(defn- belief-readers
  "Each entry point that answers belief at a context, as `{name (fn [kb hs c])}`, true when
  `c` believes one of the handles `hs`."
  []
  {:believed?    (fn [kb hs c] (boolean (some #(v/believed? kb % c) hs)))
   :status       (fn [kb hs c] (boolean (some #(:believed? (v/belief-status kb % c)) hs)))
   :believed-at? (fn [kb hs c] (boolean (some #(res/believed-at? kb % c) hs)))})

(defn- believing
  "`{reader #{key …}}`: the keys of `cxs`, `{key context}`, at which each belief reader
  answers one of `hs` believed."
  [kb hs cxs]
  (into {} (for [[r f] (belief-readers)]
             [r (into #{} (keep (fn [[k c]] (when (f kb hs c) k))) cxs)])))

(defn- believed-own
  "`{reader believed?}` for each read of `h` that names no context, and for
  `sentexes-matching` at `h`'s own context, which reads the records stored there."
  [kb h]
  (let [{:keys [sentence context]} (v/sentex kb h)]
    {:believed?     (boolean (v/believed? kb h))
     :batch         (contains? (v/believed kb [h]) h)
     :believed-own? (boolean (exc/believed-own? kb h))
     :matching      (boolean (some #(= h (:id %)) (v/sentexes-matching kb sentence context)))}))

(defn- write!
  "Assert the write `[:fact s c opts]`, or `[:except k c]` naming the handle `hs` holds
  for `k`, and answer its handle; nil for an except whose target `hs` lacks."
  [kb hs [kind x c o]]
  (case kind
    :fact   (v/assert kb x c (or o {}))
    :except (when-let [t (get hs x)] (v/assert kb (list 'except (sx/sentex-handle t)) c M))))

(defn- orders
  "Every order of the keys of `writes` in which an `:except` write follows the write it
  names, in key order."
  [writes]
  (letfn [(after [k] (let [[kind x] (writes k)] (if (= :except kind) #{x} #{})))
          (go [done left]
            (if (empty? left)
              [done]
              (mapcat #(go (conj done %) (disj left %))
                      (filter #(every? (set done) (after %)) (sort left)))))]
    (go [] (set (keys writes)))))

(defn- target-records
  "The handles of `target`: a write key, read as that write's handle, or `[:sentence s]`,
  read as every record of `s` in `cxs` and CxUniverse."
  [kb hs target cxs]
  (if (keyword? target)
    #{(hs target)}
    (into #{} (keep #(v/handle-of kb (second target) %)) (cons 'CxUniverse (vals cxs)))))

(defn- check-row!
  "Assert `writes` in every order (`orders`) and read `target` at each context of `cxs`
  with every belief reader: believed at the keys `want`, at `without` once the write
  `toggle` is retracted, and at `want` once it is restated.  A write-key target is also
  read with no context, believed iff `want` holds `home`.  Retracts every write after
  each order."
  [kb cxs {:keys [label writes target home toggle want without]}]
  (let [expect (fn [ks] (cond-> {:at (zipmap (keys (belief-readers)) (repeat ks))}
                          home (assoc :own (let [b (contains? ks home)] {:believed? b :batch b :believed-own? b :matching b}))))
        read   (fn [hs] (cond-> {:at (believing kb (target-records kb hs target cxs) cxs)}
                          home (assoc :own (believed-own kb (hs target)))))]
    (doseq [order (orders writes)]
      (let [hs  (reduce (fn [hs k] (assoc hs k (write! kb hs (writes k)))) {} order)
            r1  (read hs)
            _   (v/retract! kb (hs toggle))
            r2  (read hs)
            hs  (assoc hs toggle (write! kb hs (writes toggle)))
            r3  (read hs)]
        (is (= [(expect want) (expect without) (expect want)] [r1 r2 r3])
            (str label ", in the order " order))
        (run! #(v/retract! kb %) (distinct (rseq (mapv hs order))))))))

(defn- definition-world
  "Assert CxA, CxB and CxS under it, CxC under CxB and CxO beside CxA, and `person` under
  `thing`; answer the contexts `check-row!` reads at."
  [kb {:keys [person CxA CxB CxC CxS CxO]}]
  (doseq [[sub super] [[CxA 'CxUniverse] [CxB CxA] [CxC CxB] [CxS CxA] [CxO 'CxUniverse]]]
    (v/assert kb (list 'genlCx sub super) 'CxUniverse M))
  (v/assert kb (list 'genl person 'thing) 'CxUniverse M)
  {:u 'CxUniverse :a CxA :b CxB :c CxC :s CxS :o CxO})

(defn- row-maker
  "`(rows label writes target home toggle without wants)`: one `check-row!` row per entry
  of `wants`, `{k contexts}`, with `writes` called on the context `k` names."
  [{:keys [CxA CxB CxC CxS CxO]}]
  (let [at {:u 'CxUniverse :a CxA :b CxB :c CxC :s CxS :o CxO}]
    (fn [label writes target home toggle without wants]
      (for [[k want] wants]
        {:label  (str label ", the except in " (at k)) :writes (writes (at k))
         :target target :home home :toggle toggle :want want :without without}))))

(defn- condition-rows
  "Rows where one condition of the definition alone decides belief.  A fact its argument
  declaration holds OUT is neither defeated nor excepted.  A claim excepted where it is
  stated is hidden at its own context by the except alone.  CxO sees a claim only through
  an excepted `genlCx` edge, or through one a denial loses to (`genlCx` is
  forced-monotonic).  A claim's denial rests on an excepted ground."
  [{:keys [likes Ann Bo pp person CxA CxO] :as t}]
  (let [rows    (row-maker t)
        L       (list likes Ann Bo)
        E       (list 'genlCx CxO CxA)
        all     #{:a :b :c :s}
        held    {:l [:fact (list likes 5 Bo) CxA] :g [:fact (list 'arg likes 1 person) 'CxUniverse M]}
        edge-ex (fn [x] {:g [:fact E 'CxUniverse M] :l [:fact L CxA] :e [:except :g x]})
        edge-df (fn [x] {:g [:fact E 'CxUniverse] :l [:fact L CxA] :d [:fact (list 'not E) x M]})
        grounds (fn [x] {:l [:fact L CxA]
                         :r [:fact (list 'set/forwardRule (list 'implies (list pp '?x) (list 'not (list likes '?x Bo)))) CxA M]
                         :p [:fact (list pp Ann) CxA M] :e [:except :p x]})]
    (concat
     [{:label "a fact its argument declaration holds OUT" :writes held :target :l :home :a
       :toggle :g :want #{} :without all}]
     (rows "a claim excepted where it is stated" (fn [x] {:l [:fact L CxA] :e [:except :l x]})
           :l :a :e all {:a #{}})
     (rows "a claim seen through an excepted edge" edge-ex :l :a :e (conj all :o)
           {:u all :a all :o all})
     (rows "a claim seen through an edge a denial loses to" edge-df :l :a :d (conj all :o)
           {:u (conj all :o) :a (conj all :o) :o (conj all :o)})
     (rows "a claim whose denial rests on an excepted ground" grounds :l :a :e #{}
           {:a all :b #{:b :c} :s #{:s}}))))

(defn- definition-rows
  "The rows `check-row!` reads, over `definition-world`.  Each row's last map gives, per
  context an except is stated in, the contexts that believe the target."
  [{:keys [likes Ann Bo pp qq Rex CxA CxB] :as t}]
  (let [L    (list likes Ann Bo)
        D    (list 'not L)
        R    (list 'set/forwardRule (list 'implies (list pp '?x) (list qq '?x)))
        P    (list pp Rex)
        all  #{:a :b :c :s}
        rows (row-maker t)
        claim       (fn [x] {:l [:fact L CxA] :e [:except :l x]})
        defeated    (fn [x] {:l [:fact L CxA] :d [:fact D CxA M] :e [:except :l x]})
        below       (fn [x] {:l [:fact L CxA] :d [:fact D CxB M] :e [:except :l x]})
        winner      (fn [x] {:l [:fact L CxA] :d [:fact D CxA M] :e [:except :d x]})
        antecedent  (fn [x] {:r [:fact R CxA] :p [:fact P CxA] :e [:except :p x]})
        meta-except (fn [x] {:l [:fact L CxA] :e [:except :l CxA] :m [:except :e x]})]
    (concat
     (rows "an excepted claim" claim :l :a :e all
           {:u #{} :a #{} :b #{:a :s} :c #{:a :b :s} :s #{:a :b :c} :o all})
     (rows "an excepted claim its denial defeats" defeated :l :a :e #{}
           {:a #{} :b #{} :s #{}})
     (rows "the denial of an excepted claim" defeated :d :a :e all
           {:a all :b all :s all})
     (rows "an excepted claim a denial below defeats" below :l :a :e #{:a :s}
           {:a #{} :b #{:a :s} :c #{:a :s} :s #{:a}})
     (rows "a claim whose winning denial is excepted" winner :l :a :e #{}
           {:a all :b #{:b :c} :s #{:s}})
     (rows "an excepted winning denial" winner :d :a :e all
           {:a #{} :b #{:a :s} :s #{:a :b :c}})
     (rows "a conclusion whose antecedent is excepted" antecedent [:sentence (list qq Rex)] nil :e all
           {:a #{} :b #{:a :s} :c #{:a :b :s} :s #{:a :b :c}})
     (rows "an excepted antecedent" antecedent :p :a :e all
           {:a #{} :b #{:a :s} :c #{:a :b :s} :s #{:a :b :c}})
     (rows "a claim an excepted except gives back" meta-except :l :a :m #{}
           {:b #{:b :c} :c #{:c} :s #{:s}})
     (rows "an excepted except" meta-except :e :a :m all
           {:b #{:a :s} :c #{:a :b :s} :s #{:a :b :c}}))))

(tu/deftest-kb each-condition-of-the-definition-decides-belief-alone
  (tu/with-terms [likes Ann Bo pp person CxA CxB CxC CxS CxO]
    (let [t   {:likes likes :Ann Ann :Bo Bo :pp pp :person person
               :CxA CxA :CxB CxB :CxC CxC :CxS CxS :CxO CxO}
          cxs (definition-world kb t)]
      (doseq [row (condition-rows t)]
        (check-row! kb cxs row)))))

(tu/deftest-kb ^:slow belief-at-a-context-is-what-that-context-sees
  (tu/with-terms [likes Ann Bo pp qq Rex person CxA CxB CxC CxS CxO]
    (let [t   {:likes likes :Ann Ann :Bo Bo :pp pp :qq qq :Rex Rex :person person
               :CxA CxA :CxB CxB :CxC CxC :CxS CxS :CxO CxO}
          cxs (definition-world kb t)]
      (doseq [row (concat (definition-rows t) (condition-rows t))]
        (check-row! kb cxs row)))))

(tu/deftest-kb an-except-or-defeat-in-a-context-an-excepted-edge-cuts-off-removes-nothing-below-it
  ;; CxB sees CxA only through the edge `cut`.  An except of `cut` is read over CxB's
  ;; unscoped ancestor set, so one stated in CxA cuts CxA off too.  Every other except and
  ;; defeat is read over the ancestor set those leave.
  (tu/with-terms [likes Ann Bo CxA CxB]
    (v/assert kb (list 'genlCx CxA 'CxUniverse) 'CxUniverse M)
    (let [cut  (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse M)
          L    (list likes Ann Bo)
          h    (v/assert kb L 'CxUniverse)
          cxs  {:a CxA :b CxB}
          cut! (fn [cx] (v/assert kb (list 'except (sx/sentex-handle cut)) cx M))
          at   (fn [ks] (zipmap (keys (belief-readers)) (repeat ks)))]
      (testing "an except in CxA hides the claim at every context that sees CxA"
        (let [e (v/assert kb (list 'except (sx/sentex-handle h)) CxA M)]
          (is (= (at #{}) (believing kb #{h} cxs)))
          (doseq [cx [CxB CxA]]
            (let [c (cut! cx)]
              (testing (str "and an except of CxB's edge to CxA, stated in " cx ", gives it back at CxB")
                (is (not (v/sees? kb CxB CxA)))
                (is (= (at #{:b}) (believing kb #{h} cxs)))
                (is (v/ask? kb L CxB))
                (is (false? (:excepted? (v/belief-status kb h CxB)))))
              (v/retract! kb c)
              (is (= (at #{}) (believing kb #{h} cxs)) "and retracting that except hides it again")))
          (v/retract! kb e)))
      (testing "a denial in CxA defeats the claim at every context that sees CxA"
        (let [d (v/assert kb (list 'not L) CxA M)]
          (is (= (at #{}) (believing kb #{h} cxs)))
          (let [c (cut! CxB)]
            (testing "and an except of CxB's edge to CxA gives it back at CxB"
              (is (= (at #{:b}) (believing kb #{h} cxs)))
              (is (false? (:withdrawn? (v/belief-status kb h CxB)))))
            (v/retract! kb c))
          (v/retract! kb d))))))

;; ---- the definition over random worlds

(def ^:private world-up
  "Each world context key's `genlCx` ancestor set, itself and `:u` included."
  {:u #{:u} :a #{:a :u} :b #{:b :a :u} :c #{:c :b :a :u} :s #{:s :a :u}
   :d #{:d :b :s :a :u} :o #{:o :u}})

(defn- world-writes
  "Write 0 is the rule `(pp ?x) → (qq ?x)` in `:a`.  The next `n`, drawn by `rng`, are
  claims at `:default`, denials at either strength and excepts of an earlier write, each
  `[:fact s key opts]` or `[:except i key]` with `key` a context key other than `:u`.  No
  write repeats another, so each write stores its own record."
  [^java.util.Random rng n {:keys [pp qq likes Ann Bo]}]
  (let [pick   (fn [xs] (nth xs (.nextInt rng (count xs))))
        cks    [:a :b :c :s :d :o]
        claims (vec (concat (for [f [pp qq] x [Ann Bo]] (list f x))
                            (for [x [Ann Bo] y [Ann Bo]] (list likes x y))))
        pool   (into claims (map #(list 'not %)) claims)]
    (first
     (reduce (fn [[ws used] _]
               (let [r    (if (= 1 (count ws)) 0 (.nextInt rng 8))
                     free (vec (remove used pool))
                     fact (fn [neg?] (pick (filterv #(= neg? (= 'not (first %))) free)))]
                 (cond (and (< r 4) (some #(not= 'not (first %)) free))
                       (let [c (fact false)] [(conj ws [:fact c (pick cks) {}]) (conj used c)])
                       (and (< r 6) (some #(= 'not (first %)) free))
                       (let [d (fact true)] [(conj ws [:fact d (pick cks) (pick [{} M])]) (conj used d)])
                       :else
                       (let [e (pick (vec (for [i (range 1 (count ws)) k cks :when (not (used [i k]))] [i k])))]
                         [(conj ws (into [:except] e)) (conj used e)]))))
             [[[:fact (list 'set/forwardRule (list 'implies (list pp '?x) (list qq '?x))) :a {}]] #{}]
             (range n)))))

(defn- replay!
  "Assert `writes` (`world-writes`) into `kb` in `order`, the contexts read off `cxs`, and
  answer `{index handle}`; a refused write answers no handle."
  [kb writes order cxs]
  (reduce (fn [hs i]
            (let [[kind x k o] (writes i)
                  h (try (write! kb hs [kind x (cxs k) o])
                         (catch clojure.lang.ExceptionInfo _ nil))]
              (cond-> hs h (assoc i h))))
          {} order))

(defn- world-table
  "`{[reader item key] believed?}` at each context of `cxs` for each write's handle (`item`
  its index) and for each `(qq X)` (`item` `[:qq n]`), with `[reader index]` keys for the
  reads that name no context."
  [kb hs cxs {:keys [qq Ann Bo]}]
  (let [items (concat (for [[i h] hs :when (pos? i)] [i #{h}])
                      (for [[n x] (map-indexed vector [Ann Bo]) :let [s (list qq x)]]
                        [[:qq n] (into #{} (keep #(v/handle-of kb s %)) (vals cxs))]))]
    (into (into {} (for [[i h] hs :when (pos? i) [r b] (believed-own kb h)] [[r i] b]))
          (for [[item ths] items [r f] (belief-readers) [k c] cxs]
            [[r item k] (f kb ths c)]))))

(defn- dependency-order
  "A random order of `writes`' indexes, drawn by `rng`, in which an except follows the
  write it names."
  [^java.util.Random rng writes]
  (loop [done [] left (set (range (count writes)))]
    (if (empty? left)
      done
      (let [ready (vec (sort (filter #(let [[kind x] (writes %)]
                                        (or (not= :except kind) (some #{x} done)))
                                     left)))
            i     (nth ready (.nextInt rng (count ready)))]
        (recur (conj done i) (disj left i))))))

(defn- in-world
  "`(f writes hs cxs terms)` over fresh terms: the world `seed` draws (`world-writes`, `n`
  writes) asserted in `order` under the contexts `world-up` keys, each `genlCx` edge
  stated.  Retracts every write and edge after."
  [kb seed n order f]
  (tu/with-terms [likes Ann Bo pp qq CxA CxB CxC CxS CxD CxO]
    (let [es    (mapv (fn [[sub super]] (v/assert kb (list 'genlCx sub super) 'CxUniverse M))
                      [[CxA 'CxUniverse] [CxB CxA] [CxC CxB] [CxS CxA] [CxD CxB] [CxD CxS]
                       [CxO 'CxUniverse]])
          cxs   {:u 'CxUniverse :a CxA :b CxB :c CxC :s CxS :d CxD :o CxO}
          terms {:pp pp :qq qq :likes likes :Ann Ann :Bo Bo}
          ws    (world-writes (java.util.Random. seed) n terms)
          hs    (replay! kb ws order cxs)]
      (try (f ws hs cxs terms)
           (finally
             (run! #(v/retract! kb %) (distinct (keep hs (rseq (vec order)))))
             (run! #(v/retract! kb %) (rseq es)))))))

(defn- world-findings
  "The definition's violations in the world `seed` draws.  A finding names two readers that
  disagree, or a context believing a record it does not see, or a read naming no context
  that differs from the record's own context's.  An except stated at X must hide its
  target where X is seen and move nothing where X is not.  Retracting that except and
  replaying the writes in another order must each leave the table as it was."
  [kb seed n]
  (let [shape (world-writes (java.util.Random. seed) n {:pp 'pp :qq 'qq :likes 'likes :Ann 'Ann :Bo 'Bo})
        rng   (java.util.Random. (+ 7919 seed))
        order (dependency-order rng shape)
        x     (nth [:a :b :c :s :d :o] (.nextInt rng 6))
        pick  (.nextInt rng 1000000)
        home  (fn [i] (nth (shape i) 2))
        seen? (fn [k] (contains? (world-up k) x))
        [t0 t1 t2 i]
        (in-world kb seed n (range (count shape))
                  (fn [ws hs cxs terms]
                    (let [t0 (world-table kb hs cxs terms)
                          ts (vec (filter #(and (pos? %) (hs %) (not (some #{[:except % x]} ws)))
                                          (range (count ws))))
                          i  (when (seq ts) (nth ts (mod pick (count ts))))]
                      (if-not i
                        [t0 t0 t0 nil]
                        (let [e  (v/assert kb (list 'except (sx/sentex-handle (hs i))) (cxs x) M)
                              t1 (world-table kb hs cxs terms)]
                          (v/retract! kb e)
                          [t0 t1 (world-table kb hs cxs terms) i])))))
        t3    (in-world kb seed n order (fn [_ hs cxs terms] (world-table kb hs cxs terms)))
        at    (fn [t] (filter #(= 3 (count (key %))) t))]
    (vec (concat
          (for [[[r item k] b] (at t0) :when (not= b (t0 [:believed? item k]))]
            [:readers-disagree r item k])
          (for [[[r item k] b] (at t0) :when (and b (integer? item) (not (contains? (world-up k) (home item))))]
            [:believed-unseen r item k])
          (for [[[r j :as key] b] t0 :when (and (= 2 (count key)) (not= b (t0 [:believed? j (home j)])))]
            [:own-context r j])
          (for [[[r item k] b] (at t1) :when (and b (= item i) (seen? k))]
            [:excepted-but-believed r k])
          (for [key (into (set (keys t0)) (keys t1))
                :when (and (= 3 (count key)) (not (seen? (peek key)))
                           (not= (boolean (t0 key)) (boolean (t1 key))))]
            [:moved-where-unseen key])
          (when (not= t0 t2) [[:retraction-did-not-restore i x]])
          (when (not= t0 t3) [[:order-dependent order]])))))

(defn- worlds-findings
  "`{seed findings}` for each seed of `seeds` whose world (`world-findings`, `n` writes)
  breaks the definition, the first six findings each."
  [kb seeds n]
  (into {} (keep (fn [seed] (let [f (world-findings kb seed n)] (when (seq f) [seed (take 6 f)]))))
        seeds))

(tu/deftest-kb sampled-worlds-follow-the-belief-definition
  (is (= {} (worlds-findings kb (range 6) 8))))

(tu/deftest-kb ^:slow many-worlds-follow-the-belief-definition
  (is (= {} (worlds-findings kb (range 100 250) 12))))
