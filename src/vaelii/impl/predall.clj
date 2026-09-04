;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.predall
  "The *Specified* half of the predAll / predExists / predInstance / predSpecified matrix
  (docs/generators.md, resources/kb/CxCore.txt).

  Where the *Instance* relations stamp real inference and the *Exists* relations are
  inert records beside a sanctioned placeholder functor, `predAllSpecified` / `predSpecifiedAll` are an **integrity
  audit**: given a declaration that every instance of a collection ought to have a
  *determinate* filler, the reader here returns the instances that do not.  It is not a
  stored rule and concludes nothing — it reads the declaration and the beliefs and hands
  back the violations, the way a solve-time report does.

  **Indeterminate = the `indeterminate_term` category.**  A filler counts as determinate
  unless it is a member of the extensible `indeterminate_term` collection (CxCore.txt).
  Skolem constants are its built-in first member — a reified NAT whose expression is a
  `SkolemFn` application (docs/skolem.md), detected structurally because a skolem's
  membership is never a stored fact — and a further kind is added with
  `(genl NewKind indeterminate_term)`.  Whether a non-skolem NAT is determinate by default
  is punted (Pace): a plain individual, a literal and an *Exists* placeholder alike are
  all treated as determinate here, which is what makes `predAllSpecified` the exact
  antagonist of `predAllExists`."
  (:require [vaelii.core :as v]
            [vaelii.impl.skolem :as skolem]))

(defn- skolem-term?
  "Is `term` a skolem constant — a reified NAT whose `termOfUnit` expression heads with
  `SkolemFn` (docs/skolem.md)?  Skolems are the built-in first member of `indeterminate_term`:
  their membership is never a stored fact (they are minted dynamically), so it is read off
  the minting expression rather than through a collection query."
  [kb term]
  (boolean
   (and (v/reified-term? term)
        (let [e (v/term-expression kb term)]
          (and (sequential? e) (= skolem/skolem-function (first e)))))))

(defn indeterminate-term?
  "Is `term` an **indeterminate** filler — a member of the extensible `indeterminate_term`
  category (CxCore.txt)?  A term is indeterminate when it is either a
  skolem constant (the built-in first member, detected structurally by `skolem-term?`) or a
  believed member of `indeterminate_term` in `ctx` — so a future kind added with
  `(genl NewKind indeterminate_term)` is picked up through ordinary collection membership,
  by this reader and by the `different` prover's UNA identity exemption alike.

  A non-skolem NAT that is not declared an `indeterminate_term`, a bare individual and a
  literal are all determinate; the blanket non-skolem-NAT determinacy question is punted
  (Pace).  The `ctx`-free arity checks only the skolem membership."
  ([kb term] (indeterminate-term? kb term nil))
  ([kb term ctx]
   (or (skolem-term? kb term)
       (boolean (and ctx (v/ask? kb (list 'indeterminate_term term) ctx))))))

(defn- determinate-filler?
  "Does the collection `dep` (or, when `dep` is nil, no collection at all) admit at least
  one determinate filler `y` believed at position `arg-pos` of `(pred … x …)` in `ctx`?
  `arg-pos` is `:second` for a `predAllSpecified` (x at position 1, filler at 2) or
  `:first` for a `predSpecifiedAll` (x at position 2, filler at 1)."
  [kb pred x dep arg-pos ctx]
  (let [goal    (case arg-pos
                  :second (list pred x '?y)
                  :first  (list pred '?y x))
        answers (v/ask kb goal ctx)]
    (boolean
     (some (fn [b]
             (let [y (get b '?y)]
               (and (not (indeterminate-term? kb y ctx))
                    (or (nil? dep) (v/ask? kb (list dep y) ctx)))))
           answers))))

(defn specified-violations
  "The instances of `indep` that violate the `(predAllSpecified pred indep dep)` integrity
  requirement in `ctx`: every member x of `indep` for which no believed `(pred x y)` has a
  *determinate* filler y in `dep`.  Returns a set of such x (empty when the requirement
  holds).

  `arg-pos` selects the twin: `:second` for `predAllSpecified` (the audited filler sits at
  `pred`'s second position), `:first` for `predSpecifiedAll` (the filler sits first and
  the quantified instance second).  Defaults to `:second`.

  A filler is indeterminate exactly when it is an `indeterminate_term` — a skolem (the
  built-in first member) or an extension declared with `(genl NewKind indeterminate_term)`
  — so an *Exists* placeholder passes and a skolemised witness does not, which is what
  makes this the antagonist of the *Exists* class."
  ([kb pred indep dep ctx] (specified-violations kb pred indep dep ctx :second))
  ([kb pred indep dep ctx arg-pos]
   (into #{}
         (comp (map #(get % '?x))
               (remove #(determinate-filler? kb pred % dep arg-pos ctx)))
         (v/ask kb (list indep '?x) ctx))))

(defn- declaration-args
  "Read the stored `(functor pred a b)` declarations in `ctx` as `[pred a b]` tuples."
  [kb functor ctx]
  (for [b (v/ask kb (list functor '?pred '?a '?b) ctx)]
    [(get b '?pred) (get b '?a) (get b '?b)]))

(defn all-specified-violations
  "Audit every `predAllSpecified` and `predSpecifiedAll` declaration visible in `ctx` and
  return a map `{[functor pred indep dep] #{violating-instances…}}`, omitting the
  declarations that hold.  The one call an integrity sweep makes; `specified-violations`
  is the per-declaration reader it is built from."
  [kb ctx]
  (into {}
        (for [[functor arg-pos indep-at] [['predAllSpecified :second :a]
                                          ['predSpecifiedAll :first :b]]
              [pred a b] (declaration-args kb functor ctx)
              :let [indep (if (= indep-at :a) a b)
                    dep   (if (= indep-at :a) b a)
                    vs    (specified-violations kb pred indep dep ctx arg-pos)]
              :when (seq vs)]
          [[functor pred indep dep] vs])))
