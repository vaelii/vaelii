;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.fluent
  "The `functional_at_instant` audit: a moment where two fluent values of one subject hold,
  read on demand.  `vaelii.core` delegates to it.  See docs/time.md,
  \"Functionality at an instant\", and docs/namespaces.md, \"The layering\"."
  (:require [vaelii.impl.inference :as inference]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.quasiquote :as quasiquote]))

(def ^:private holds-at-depth
  "The `:max-depth` of one `(holdsAt fluent instant)` read.  The event-calculus tests
  answer at depth 3."
  4)

(defn- holds-at?
  "Is `(holdsAt fluent instant)` provable in `ctx` within `holds-at-depth`?  The node
  engine expands the rule and the registry answers each leaf, as in `vaelii.core/query?`.
  The answer follows belief."
  [kb fluent instant ctx]
  (boolean
   (seq (inference/solutions
         kb
         [(quasiquote/prepare-goal-for-read kb (list 'holdsAt fluent instant) ctx)]
         ctx
         {:max-depth    holds-at-depth
          :max-results  1
          :leaf-solver  provers/solve-goal
          :est-override (provers/registry-est-override kb ctx)}))))

(defn- fluent-fillers
  "Every `[subject value fluent]` a binary fluent function `f` carries in the `initiates`
  and `initially` facts believed in `context`.  A reified fluent's `(f subject value)` is
  read from its `nat-expression`; any other shape is skipped.  `fluent` is the term as
  stored, the form `holdsAt` is asked of."
  [kb f context]
  (let [from (fn [fl] (let [expr (if (nat-read/reified-nat-symbol? fl) (nat/nat-expression kb fl) fl)]
                        (when (and (seq? expr) (= f (first expr)) (= 3 (count expr)))
                          [(second expr) (nth expr 2) fl])))]
    (into #{}
          (comp (map from) (remove nil?))
          (concat (for [b (quasiquote/ask-prepared kb (list 'initiates '?e '?fluent '?t) context)]
                    (get b '?fluent))
                  (for [b (quasiquote/ask-prepared kb (list 'initially '?fluent) context)]
                    (get b '?fluent))))))

(defn functional-at-instant-violations
  "The per-instant clashes of one `(functional_at_instant f)` declaration in `context`, as a
  set of maps `{:function f :subject s :instant t :values #{v …} :kind k}` — one per
  moment `t` at which more than one distinct value of `f` holds for one subject `s`.  `:kind`
  is `:merge` when every clashing value is a symbol (the pair `functional` would merge) and
  `:contradiction` otherwise (two numbers or strings `functional` refuses outright).

  The candidate moments are the `time_point` members, the later moment of each
  `instantBefore` pair and the moment of each `happens` fact `ask` answers in `context`
  (docs/time.md, \"Functionality at an instant\").  `holdsAt` is asked of each filler at
  each.  The read follows belief and is scoped to `context`."
  [kb f context]
  (let [fillers  (fluent-fillers kb f context)
        subjects (into #{} (map first) fillers)
        moments  (into #{}
                       (concat (map #(get % '?t)
                                    (quasiquote/ask-prepared kb '(time_point ?t) context))
                               (map #(get % '?b)
                                    (quasiquote/ask-prepared kb '(instantBefore ?a ?b) context))
                               (map #(get % '?t)
                                    (quasiquote/ask-prepared kb '(happens ?e ?t) context))))]
    (into #{}
          (for [t moments
                s subjects
                :let [vals (into #{}
                                 (comp (filter (fn [[cs _ _]] (= s cs)))
                                       (filter (fn [[_ _ fl]] (holds-at? kb fl t context)))
                                       (map second))
                                 fillers)]
                :when (> (count vals) 1)]
            {:function f :subject s :instant t :values vals
             :kind (if (every? symbol? vals) :merge :contradiction)}))))

(defn all-functional-at-instant-violations
  "Every `(functional_at_instant f)` declaration visible in `context`, audited, as
  `{f #{violation …} …}`; a declaration that clashes nowhere is omitted."
  [kb context]
  (into {}
        (for [b     (quasiquote/ask-prepared kb '(functional_at_instant ?f) context)
              :let  [f  (get b '?f)
                     vs (functional-at-instant-violations kb f context)]
              :when (seq vs)]
          [f vs])))
