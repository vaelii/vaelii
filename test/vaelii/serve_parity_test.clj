;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.serve-parity-test
  "The ops the daemon grew to reach parity with `vaelii.core`, driven through
  `serve/app` — pure `request -> response`, so no socket.

  One property runs under all of them and is why they are here rather than trusted:
  **a reply has to survive `pr-str` and `edn/read-string`**, which is the whole of what
  crossing the wire is.  Every failure this file exists to catch is invisible to a
  local call — a `java.util.Set` that is not an `IPersistentSet` prints as
  `#object[…]`, a continuation prints as a function, a record prints as `#vaelii…` —
  and each answers `200 {:ok true}` on the way out.

  `wire-clean?` is therefore the assertion, not `:ok`."
  (:require [clojure.edn :as edn]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.serve :as serve]
            [vaelii.regen-client :as rc]
            [vaelii.test-util :as tu])
  (:import [java.io ByteArrayInputStream]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- post-op
  "Call `handler` with `{:op :args}` and return the parsed EDN reply with `:status`.
  The `content-type` is what `guard/edn-body?` requires of the write route."
  [handler op args]
  (let [body (pr-str {:op op :args (vec args)})
        resp (handler {:request-method :post :uri "/op"
                       :headers {"content-type" "application/edn"}
                       :body (ByteArrayInputStream. (.getBytes ^String body "UTF-8"))})]
    (assoc (edn/read-string (:body resp)) :status (:status resp))))

(defn- open-app
  "A handler with no bearer token — the loopback default.  Named rather than defaulted,
  since the default reads `VAELII_API_TOKEN` and a shell holding one would turn every
  call below into a 401."
  [kb]
  (serve/app kb {:token nil}))

(defn- wire-clean?
  "Does `x` survive the wire — `pr-str` then `edn/read-string` back to an equal value?
  The daemon's reply body is exactly that round trip, so a value that fails it reaches
  a client as text the EDN reader refuses or as a *different* value that reads."
  [x]
  (= x (edn/read-string (pr-str x))))

(defn- ok-result
  "The `:result` of `op`, asserting the call succeeded and that its answer crosses the
  wire.  Every test below goes through this, so the round-trip property is checked once
  per op rather than remembered per test."
  [handler op args]
  (let [r (post-op handler op args)]
    (is (:ok r) (str op " refused: " (:error r)))
    (is (= 200 (:status r)) (str op))
    (is (wire-clean? (:result r)) (str op " answered something EDN cannot carry"))
    (:result r)))

;; ---- the closures a query cannot reconstruct ----------------------------

(tu/deftest-kb ordinary-defining-contexts-cross-the-wire
  (tu/with-terms [Subject tagged CxHome]
    (v/assert kb (list 'genlCx CxHome 'CxUniverse) 'CxUniverse)
    (v/assert kb (list tagged Subject) CxHome)
    (is (= #{CxHome} (ok-result (open-app kb) :defining-contexts [Subject])))))

(tu/deftest-kb the-cached-closures-are-served
  ;; Transitivity and the equality partition are cached and recomputed on edge change
  ;; rather than derived by rules (docs/taxonomy.md), so there is no query a remote
  ;; caller could ask instead of these.
  (tu/with-terms [dog animal Rex Rexx siblingOf parentOf childOf CxClosure]
    (v/assert kb (list 'genlCx CxClosure 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genl dog animal) CxClosure)
    (v/assert kb (list 'symmetric siblingOf) CxClosure)
    (v/assert kb (list 'inverse parentOf childOf) CxClosure)
    (v/assert kb (list 'sameAs Rex Rexx) CxClosure)
    (let [handler (open-app kb)]
      (testing "genl? between two types, scoped and unscoped"
        (is (true? (ok-result handler :genl? [dog animal])))
        (is (true? (ok-result handler :genl? [dog animal CxClosure]))))
      (testing "the genlCx ancestor set, both directions, and the visibility question behind it"
        (is (contains? (set (ok-result handler :context-up [CxClosure])) 'CxUniverse))
        (is (contains? (set (ok-result handler :context-down ['CxUniverse])) CxClosure))
        (is (true? (ok-result handler :sees? [CxClosure 'CxUniverse])))
        (is (false? (ok-result handler :sees? ['CxUniverse CxClosure]))))
      (testing "the nearest genlCx neighbours, both directions"
        (is (= #{'CxUniverse} (set (ok-result handler :min-context-parents [CxClosure]))))
        (is (contains? (set (ok-result handler :max-context-children ['CxUniverse])) CxClosure)))
      (testing "the declared predicate properties, and the inverse pairing"
        (is (true? (ok-result handler :has-prop? [:symmetric siblingOf])))
        (is (contains? (set (ok-result handler :props [:symmetric])) siblingOf))
        (is (= childOf (ok-result handler :inverse-of [parentOf]))))
      (testing "the equality partition, including the deprecation that tells sameAs
                from rewriteOf"
        (is (= (ok-result handler :representative [Rex])
               (ok-result handler :representative [Rexx])))
        (is (true? (ok-result handler :same-class? [Rex Rexx])))
        (is (= #{Rex Rexx} (set (ok-result handler :equiv-class [Rex]))))
        (is (false? (ok-result handler :deprecated? [Rexx]))
            "a sameAs merges without retiring either name")))))

;; ---- the whole-KB enumerations ------------------------------------------

(tu/deftest-kb the-audit-enumerations-are-served
  (tu/with-terms [dog Muffet CxAudit CxAuditToo]
    (v/assert kb (list 'genlCx CxAudit 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxAuditToo 'CxUniverse) 'CxUniverse)
    (v/assert kb (list dog Muffet) CxAudit)
    (v/assert kb (list dog Muffet) CxAuditToo)
    (let [handler (open-app kb)
          h (v/handle-of kb (list dog Muffet) CxAudit)]
      (testing "the live handle set crosses as a sorted vector"
        ;; the store's own answer is a java.util.Set that is deliberately not an
        ;; IPersistentSet at scale (docs/storage.md) and has no EDN print form; sorting
        ;; it is also what makes two daemons over one store answer the same bytes
        (let [hs (ok-result handler :handles [])]
          (is (vector? hs))
          (is (= (sort hs) (seq hs)) "the handle set is sorted, so the bytes are stable")
          (is (contains? (set hs) h))))
      (testing "the contexts one sentence is asserted in"
        (is (= #{CxAudit CxAuditToo}
               (set (ok-result handler :contexts-of [(list dog Muffet)])))))
      (testing "the canonical form of a sentence that was never stored"
        (tu/with-terms [cat Unstored]
          (let [sx (ok-result handler :canonical-sentex [(list cat Unstored) CxAudit])]
            (is (map? sx))
            (is (not (record? sx)) "a record must be projected to a plain map")
            (is (= (list cat Unstored) (:sentence sx)))
            (is (nil? (:id sx)) "nothing was written, so there is no handle")
            (is (nil? (v/handle-of kb (list cat Unstored) CxAudit))))))
      (testing "the census of what the engine does with its own grammar"
        (let [audit (ok-result handler :vocabulary-audit [])]
          (is (map? audit))
          (is (every? #(contains? audit %)
                      [:enforced :inert :unclassified :retired :contradicted]))))
      (testing "the exceptWhen fixpoint's instrumentation"
        (let [stats (ok-result handler :settle-stats [])]
          (is (nat-int? (:passes stats)))
          (is (map? (:histogram stats))))))))

;; ---- the ops that take no KB --------------------------------------------

(tu/deftest-kb the-kb-less-ops-are-served-and-listed
  (tu/with-terms [dog fed CxKbLess]
    (v/assert kb (list 'genlCx CxKbLess 'CxUniverse) 'CxUniverse)
    (let [handler (open-app kb)]
      (testing "the op table is data, because two generators read it"
        ;; a closure cannot be asked whether its first vaelii.core parameter is the KB
        ;; the daemon supplies or an argument the caller sends
        (is (= #{:levels :calculi :readable-sentence :sentence-of :quality-report}
               serve/kbless-ops))
        (is (every? serve/ops serve/kbless-ops)))
      (testing "the retrieval stack and the shipped calculi, as data"
        (is (= 8 (count (ok-result handler :levels []))))
        (is (seq (ok-result handler :calculi []))))
      (testing "a stored rule's sentence with the author's variable names put back"
        ;; the read a client needs to *display* a rule it fetched: a rule is stored
        ;; canonically numbered, which reads as gibberish
        (let [h  (v/assert-rule kb [(list dog '?x)] (list fed '?x) CxKbLess)
              sx (ok-result handler :sentex [h])
              readable (ok-result handler :readable-sentence [sx])]
          (is (some #{'?x} (tree-seq sequential? seq readable))
              "the author's ?x came back, not ?var0")
          (testing "and the canonical form, which the rule map no longer carries"
            (is (not (contains? sx :sentence)) "a rule crosses the wire without :sentence")
            (is (= (list 'implies (list dog '?var0) (list fed '?var0))
                   (ok-result handler :sentence-of [sx]))))))
      (testing "a report renders from the map, and a map that is not one is refused"
        (let [q (ok-result handler :kb-quality [])
              md (ok-result handler :quality-report [q])]
          (is (string? md))
          (is (re-find #"(?m)^#" md) "a Markdown report has a heading"))
        (let [r (post-op handler :quality-report [{:not :a-report}])]
          (is (false? (:ok r)))
          (is (= :not-a-report (:type r)))
          (is (= 400 (:status r))
              "a caller reporting on the wrong map made the caller's mistake")))
      (testing "arity is still checked through the KB-less wrapper"
        (let [r (post-op handler :levels [:one :too :many])]
          (is (false? (:ok r)))
          (is (= :bad-args (:type r)))
          (is (= 400 (:status r))))))))

;; ---- the anytime pair ---------------------------------------------------

(tu/deftest-kb the-anytime-reads-cross-without-their-continuation
  ;; `:resume` is a function over an unrealized lazy tail or a DFS goal stack.  Left in
  ;; the reply it prints as `#object[…]`, which the client's reader refuses — and the
  ;; documented `(when (:resume r) …)` loop would read every partial as complete if the
  ;; key were simply dropped, so what replaces it is a boolean.
  (tu/with-terms [dog Rex Fido Muffet CxAnytime]
    (v/assert kb (list 'genlCx CxAnytime 'CxUniverse) 'CxUniverse)
    (doseq [t [Rex Fido Muffet]] (v/assert kb (list dog t) CxAnytime))
    (let [handler (open-app kb)]
      (doseq [op [:ask-within :prove-within]]
        (testing (str op " runs dry")
          (let [r (ok-result handler op [(list dog '?x) CxAnytime {:max-results 10}])]
            (is (= :complete (:status r)))
            (is (= 3 (:count r)))
            (is (false? (:resumable r)))
            (is (not (contains? r :resume)))))
        (testing (str op " cut short")
          (let [r (ok-result handler op [(list dog '?x) CxAnytime {:max-results 1}])]
            (is (= :capped (:status r)))
            (is (true? (:resumable r)) "the caller is told there was more")
            (is (not (contains? r :resume))
                "a continuation is heap state and does not cross a wire"))))
      (testing "a budget key nothing reads is the caller's mistake, not a 500"
        (let [r (post-op handler :ask-within [(list dog '?x) CxAnytime {:max-resultz 1}])]
          (is (false? (:ok r)))
          (is (= :unknown-option (:type r)))
          (is (= 400 (:status r))))))))

;; ---- abduction, and provenance ------------------------------------------

(tu/deftest-kb abduction-is-served-with-the-writes
  ;; A hypothesis is minted through the whole assert pipeline into a scratch context, so
  ;; the op holds the daemon's single writer for its run — and an abduction whose result
  ;; is ignored leaves the KB as it found it.
  (tu/with-terms [wabGoal wabPremise N CxAbduce]
    (v/assert kb (list 'genlCx CxAbduce 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'abducible_predicate wabPremise) CxAbduce)
    (v/assert kb (list 'implies (list 'and (list wabPremise '?x)) (list wabGoal '?x))
              CxAbduce)
    (let [handler (open-app kb)
          before  (tu/sentex-ids kb)]
      (testing "a discarding abduction answers and leaves nothing behind"
        (let [r (ok-result handler :abduce [(list wabGoal N) CxAbduce])]
          (is (= #{(list wabPremise N)} (set (map :sentence (:hypotheses r)))))
          (is (seq (:solutions r)))
          (is (= before (tu/sentex-ids kb))
              "an abduction over the wire stored something")))
      (testing "a kept one stands until :abduce-discard drops it"
        (let [r (ok-result handler :abduce [(list wabGoal N) CxAbduce {:keep? true}])]
          (is (not= before (tu/sentex-ids kb)))
          (let [dropped (ok-result handler :abduce-discard [r])]
            (is (pos? (:removed-sentexes dropped)))
            (is (= before (tu/sentex-ids kb))
                "the scratch context and everything it licensed are gone")))))))

(tu/deftest-kb provenance-is-read-and-layered-over-the-wire
  (tu/with-terms [dog Muffet CxProv]
    (v/assert kb (list 'genlCx CxProv 'CxUniverse) 'CxUniverse)
    (let [handler (open-app kb)
          h (v/assert kb (list dog Muffet) CxProv)]
      (testing "the creation record reads"
        (let [p (ok-result handler :provenance [h])]
          (is (contains? p :created))))
      (testing "an application field is merged on, and reads back"
        (let [merged (ok-result handler :add-provenance [h {:source "a test"}])]
          (is (= "a test" (:source merged)))
          (is (contains? merged :created) "the creation fields are untouched"))
        (is (= "a test" (:source (ok-result handler :provenance [h])))))
      (testing "a non-handle is the caller's mistake"
        (let [r (post-op handler :add-provenance [:not-a-handle {:source "x"}])]
          (is (false? (:ok r)))
          (is (= :bad-handle (:type r)))
          (is (= 400 (:status r))))))))

;; ---- the four-valued read and the knowledge census ----------------------

(tu/deftest-kb argue-and-kb-quality-are-served
  (tu/with-terms [dog Muffet CxArgue]
    (v/assert kb (list 'genlCx CxArgue 'CxUniverse) 'CxUniverse)
    (v/assert kb (list dog Muffet) CxArgue)
    (let [handler (open-app kb)]
      (testing "a stored, believed side comes back with its JTMS explanation"
        (let [r (ok-result handler :argue [(list dog Muffet) CxArgue])]
          (is (= :true (:verdict r)))
          (is (some? (:for-why r)))))
      (testing "a sentence nothing bears on is :unknown rather than :false"
        (tu/with-terms [cat Unmentioned]
          (is (= :unknown (:verdict (ok-result handler :argue
                                               [(list cat Unmentioned) CxArgue]))))))
      (testing "an option nothing reads is refused rather than silently defaulted"
        (let [r (post-op handler :argue [(list dog Muffet) CxArgue {:max-deptth 3}])]
          (is (false? (:ok r)))
          (is (= :unknown-option (:type r)))
          (is (= 400 (:status r)))))
      (testing "the five readings about the knowledge cross whole"
        (let [q (ok-result handler :kb-quality [])]
          (is (every? #(contains? q %)
                      [:rules :extents :chains :taxonomy :declarations])))))))

;; ---- the lifecycle fns that are deliberately not ops --------------------

(tu/deftest-kb the-lifecycle-fns-are-not-reachable-over-the-wire
  ;; Stated as a test rather than left to the table's absence: a lifecycle operation
  ;; belongs to whoever owns the process, and the daemon's callers do not.  Every one of
  ;; these is a `vaelii.core` fn, so nothing but this list keeps it off the wire.
  (let [handler (open-app kb)]
    (doseq [op [:import :recover :reindex :clear :close]]
      (let [r (post-op handler op [])]
        (is (false? (:ok r)) (str op))
        (is (= :unknown-op (:type r)) (str op))
        (is (= 400 (:status r)) (str op))))
    (testing "and the refusal hands back the op list, so a caller discovers the surface"
      (is (some #{:assert} (:ops (post-op handler :recover [])))))))

;; ---- a KB fn is an op, or docs/operations.md says why it is not ---------

(tu/deftest-kb the-reads-the-rule-admits-cross-the-wire
  ;; Seven reads the rule in docs/operations.md admits: data in and out, the KB and not
  ;; the process, and a cost a request bounds or one that grows with the KB.
  (tu/with-terms [dog cat animal pet Rex Tom CxRule]
    (v/assert kb (list 'genlCx CxRule 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genl dog animal) CxRule)
    (v/assert kb (list 'genl cat animal) CxRule)
    (v/assert kb (list 'disjoint dog cat) CxRule)
    (v/assert kb (list dog Rex) CxRule)
    (v/assert kb (list pet Rex) CxRule)
    (v/assert kb (list pet Tom) CxRule)
    (v/assert-rule kb [(list dog '?x)] (list animal '?x) CxRule)
    (let [handler (open-app kb)]
      (testing "query-status: the answers, and whether the depth bound cut them"
        (let [r (ok-result handler :query-status [(list animal '?x) CxRule {:max-depth 3}])]
          (is (= [{'?x Rex}] (:answers r)))
          (is (contains? #{:complete :truncated} (:status r)))
          (is (= 3 (:depth r))))
        (let [r (ok-result handler :query-status [(list animal '?x) CxRule])]
          (is (= :complete (:status r)) "a facts-only read is never truncated")))
      (testing "and it is held to the depth ceiling :query is held to"
        (let [r (post-op handler :query-status [(list animal '?x) CxRule
                                                {:max-depth 1000000}])]
          (is (= :over-ceiling (:type r)))
          (is (= 400 (:status r)))))
      (testing "find-sentexes-all, beside find-sentexes"
        (is (= #{(list dog Rex)}
               (set (map :sentence (ok-result handler :find-sentexes-all [[dog Rex]])))))
        (is (empty? (ok-result handler :find-sentexes-all [[dog Tom]]))))
      (testing "the subsumption relationship of one pair of types"
        (is (= :genl (ok-result handler :subsumption-status [dog animal CxRule])))
        (is (= :disjoint (ok-result handler :subsumption-status [dog cat CxRule])))
        (is (= :orthogonal (ok-result handler :subsumption-status [dog pet CxRule])))
        (is (= #{:genl} (ok-result handler :subsumption-statuses [dog animal]))))
      (testing "the per-instant functionality audit, the twin of the specified pair"
        (is (= #{} (set (ok-result handler :functional-at-instant-violations
                                   [(tu/tmp-pred "at") CxRule]))))
        (is (= {} (ok-result handler :all-functional-at-instant-violations [CxRule]))))
      (testing "the question the solver was last asked: nil before a tie, a map after"
        (is (nil? (ok-result handler :last-program [])))
        (let [quaker (tu/tmp-pred) pacifist (tu/tmp-pred) republican (tu/tmp-pred)
              nixon  (tu/tmp-ind)
              dflt   (fn [a c] (list 'set/defaultRule (list 'set/forwardRule
                                                            (list 'implies a c))))]
          (v/assert kb (dflt (list quaker '?x) (list pacifist '?x)) 'CxUniverse)
          (v/assert kb (dflt (list republican '?x) (list 'not (list pacifist '?x)))
                    'CxUniverse)
          (v/assert kb (list quaker nixon) 'CxUniverse)
          (v/assert kb (list republican nixon) 'CxUniverse)
          (v/assert kb (list 'do/labeling (tu/tmp-ctx "Labeling")) 'CxUniverse)
          (let [p (ok-result handler :last-program [])]
            (is (map? p) "a Program record crosses as a plain map")
            (is (= 2 (count (:assumptions p))))))))))

(def ^:private operations-md "docs/operations.md")

(defn- not-served-in-docs
  "Every `vaelii.core` fn a row of docs/operations.md's \"Not served\" tables names: the
  backticked names in each row's first cell."
  []
  (->> (str/split-lines (slurp operations-md))
       (map str/trim)
       (reduce (fn [[in? acc] line]
                 (cond
                   (str/starts-with? line "| Not served") [true acc]
                   (and in? (str/starts-with? line "|"))
                   [true (into acc (map (comp symbol second)
                                        (re-seq #"`([^`]+)`"
                                                (second (str/split line #"\|")))))]
                   :else [false acc]))
               [false #{}])
       second))

(defn- kb-fns
  "The public `vaelii.core` fns and macros whose first parameter is the KB."
  []
  (set (for [[nm vr] (ns-publics 'vaelii.core)
             :let [al (:arglists (meta vr))]
             :when (and (seq al) (= 'kb (ffirst al)))]
         nm)))

(deftest every-kb-fn-is-an-op-or-a-named-absence
  ;; An absence with a reason is a decision, and one without is indistinguishable from an
  ;; oversight.  A new `vaelii.core` fn that takes a KB fails here until it is a row of
  ;; `serve/ops` or of the table, and docs/operations.md's rule says which.
  (let [served (set (keep #(some-> (rc/core-var %) meta :name) (keys serve/ops)))
        named  (not-served-in-docs)]
    (is (seq named) "the table is found, so an empty set cannot pass the check below")
    (is (empty? (remove #(or (served %) (named %)) (kb-fns)))
        (str "a vaelii.core fn that takes a KB is neither an op nor a row of "
             operations-md "'s table of fns that are not ops"))
    (testing "and the table names only fns that exist and are not served"
      (is (empty? (filter served named)))
      (is (empty? (remove #(ns-resolve 'vaelii.core %) named))))))
