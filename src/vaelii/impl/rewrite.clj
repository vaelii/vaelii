;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.rewrite
  "The pure term algebra of schematic equational rewriting: Knuth-Bendix orientation,
  one-way matching, normalization of argument terms, and critical-pair detection.  It
  takes the oriented rules as data and reads no store, taxonomy or belief, and it
  requires only `vaelii.impl.sentex`.  See docs/equational.md."
  (:require [vaelii.impl.sentex :as sx]))

;; ---- term structure ------------------------------------------------------

(defn- rewritable-subterms
  "Every subterm of `term` that `normalize` can rewrite **at**: `term` itself, and the
  same of each of its arguments, never a compound in functor position, since `normalize`
  never descends into the head."
  [term]
  (if (sequential? term)
    (cons term (mapcat rewritable-subterms (rest term)))
    (list term)))

(defn term-size
  "The KBO unit weight of `term`: the count of symbol / variable / number leaves,
  functors included.  `(fatherOf (fatherOf ?x))` is 3, `(grandfather_of ?x)` is 2."
  [term]
  (if (sequential? term) (reduce + 0 (map term-size term)) 1))

(defn- var-counts
  "A map of each pattern variable in `term` to how many times it occurs."
  [term]
  (frequencies (sx/form-vars term)))

(defn- var-dominates?
  "Does every variable occur at least as often in `a` as in `b`?  The KBO variable
  condition `#(x,a) ≥ #(x,b)` for every variable x — necessary for `a ≻ b`, or a
  substitution duplicating a variable `b` has more of could make the rewrite grow."
  [a b]
  (let [ca (var-counts a)]
    (every? (fn [[v n]] (>= (get ca v 0) n)) (var-counts b))))

(defn- root
  "The root of `term`: its functor when compound, the atom itself otherwise — a
  constant is a nullary function symbol under KBO, so an equal-weight pair differing at
  a constant (`(g a ?x)` vs `(g b ?x)`) is decided by the precedence on the constants.

  A functor may itself be compound — `((f ?x) a)` is a legal term — so this returns a
  *term*, not always a symbol, and `prec-compare` is total over whatever it hands back."
  [term]
  (if (sequential? term) (first term) term))

(defn- prec-compare
  "`compare` made total over every term shape.  Two values of one class compare natively
  when that class is `Comparable` and not a collection, values of different classes order
  by class name, and everything else (a compound root, a collection, a mixed vector)
  compares by its printed form.  Content-derived, so `prec>` does not depend on which way
  round the equation was written; total, so `orient` refuses by returning nil rather than
  by throwing."
  [a b]
  (let [ca (if (nil? a) "" (.getName (class a)))
        cb (if (nil? b) "" (.getName (class b)))]
    (cond
      (not= ca cb)                                (compare ca cb)
      (and (instance? Comparable a) (not (coll? a))) (compare a b)
      :else                                       (compare (pr-str a) (pr-str b)))))

(defn- prec>
  "The symbol precedence: a fixed, **content-derived** total order on function symbols
  (their natural `compare`, `prec-compare`), so orientation never depends on which
  equation was asserted first.  Arbitrary but deterministic — it decides the
  *direction* of an equal-weight rewrite, not whether one exists.  `(prec> a b)` is
  `a ≻_F b`."
  [a b]
  (neg? (prec-compare b a)))

;; Genuine in-file cycle: a same-root equal-weight pair is decided by `kbo-lex>` over the
;; arguments, and the first differing position is decided by `kbo>` again.  The recursion
;; is the order's own definition, so no ordering of the two removes it.
(declare kbo>)

(defn- kbo-lex>
  "Lexicographic KBO on two equal-length argument lists (reached only when the roots
  are the same symbol): at the first differing position, the left argument must
  dominate under `kbo>`."
  [ss ts]
  (cond
    (empty? ss)               false
    (= (first ss) (first ts)) (recur (rest ss) (rest ts))
    :else                     (kbo> (first ss) (first ts))))

(defn kbo>
  "The **Knuth-Bendix order** with unit weights: is `s ≻ t`?  The variable condition must
  hold; then the heavier side wins; an equal-weight pair is decided by the precedence on
  the two roots (a constant's root is itself), and same-root compounds by a lexicographic
  comparison of the arguments.  A constant against a same-named nullary compound (`c` vs
  `(c)`) is incomparable."
  [s t]
  (and (var-dominates? s t)
       (let [ws (term-size s) wt (term-size t)]
         (cond
           (> ws wt)      true
           (< ws wt)      false
           (sx/variable? s) false          ; a variable is minimal
           (sx/variable? t) false          ; equal weight + t a variable ⇒ not > (var cond already decided)
           :else (let [f (root s) g (root t)]
                   (cond
                     (prec> f g) true
                     (prec> g f) false
                     (and (sequential? s) (sequential? t))
                     (kbo-lex> (rest s) (rest t))
                     :else       false))))))

(defn orient
  "Orient `(equals l r)` into a terminating rewrite `[big small]` by `kbo>`, or nil when
  the sides are KBO-incomparable: a permutative equation such as `(rel ?x ?y) = (rel ?y
  ?x)`, or one whose variable condition fails both ways."
  [l r]
  (cond
    (kbo> l r) [l r]
    (kbo> r l) [r l]
    :else nil))

;; ---- one-way matching + substitution -------------------------------------

(def ^:private no-match ::no-match)

(defn- match*
  [pattern subject sigma]
  (cond
    (= sigma no-match)  no-match
    (sx/variable? pattern)
    (if (contains? sigma pattern)
      (if (= (get sigma pattern) subject) sigma no-match)
      (assoc sigma pattern subject))
    (and (sequential? pattern) (sequential? subject))
    (if (= (count pattern) (count subject))
      (reduce (fn [sig [p s]] (match* p s sig)) sigma (map vector pattern subject))
      no-match)
    (or (sequential? pattern) (sequential? subject)) no-match
    :else (if (= pattern subject) sigma no-match)))

(defn match
  "One-way match of `pattern` (a rule LHS, whose variables may bind) against
  `subject` (a term, possibly variable-bearing): the substitution σ of the pattern's
  variables with `(subst pattern σ) = subject`, or nil.  Only the pattern's variables
  bind — a variable in the subject is treated as an opaque constant — so a rule never
  captures a query's variables, and since orientation forbids an RHS variable absent
  from the LHS, σ binds every variable the RHS will substitute."
  [pattern subject]
  (let [r (match* pattern subject {})]
    (when (not= r no-match) r)))

(defn- subst
  "`term` with each variable replaced by its binding in `sigma` (an unbound variable
  left as-is), recursively."
  [term sigma]
  (cond
    (sx/variable? term)   (get sigma term term)
    (sequential? term)    (apply list (map #(subst % sigma) term))
    :else                 term))

;; ---- normalization -------------------------------------------------------

(def ^:private normalize-guard
  "A pure safety net.  The reduction order already guarantees termination, so this
  bound is never reached; it exists only so a would-be bug fails safe (return the
  partly-normalized term) rather than hanging.  `match` remains the arbiter of every
  rewrite, so a partly-normalized form can only *miss*, never match wrongly."
  4096)

(defn- reduct
  "The term `rule` rewrites `term` to at its root, or nil when its LHS does not match."
  [{:keys [lhs rhs]} term]
  (when-let [sigma (match lhs term)]
    (subst rhs sigma)))

(defn- rewrite-root
  "Rewrite `term` at its root with the first applicable rule, or nil when none
  applies.  `rules` is a seq of `{:lhs :rhs}` oriented pairs."
  [rules term step]
  (some (fn [rule]
          (when-let [red (reduct rule term)]
            (when step (step rule))
            red)) rules))

(defn normalize
  "The normal form of `term` under the oriented `rules`: rewrite innermost subterms to
  a fixpoint, then the root, repeating until nothing applies.  Terminates by the
  reduction order (each root rewrite strictly decreases size); the guard is a pure
  safety net. The optional internal `step` receives each actually chosen rule,
  including recursive and second-step rewrites; the value algorithm is shared."
  ([rules term] (normalize rules term nil))
  ([rules term step]
   (loop [term term, guard 0]
     ;; `(seq term)` as well as `sequential?`: an empty list has no functor to keep, and
     ;; rebuilding it as `(apply list (first term) …)` would hand back `(nil)` — a term the
     ;; caller never wrote, in a form that then keys and matches as itself.
     (let [term' (if (and (sequential? term) (seq term))
                   (apply list (first term) (map #(normalize rules % step) (rest term)))
                   term)]
       (if-let [red (and (< guard normalize-guard) (rewrite-root rules term' step))]
         (recur red (inc guard))
         term')))))

(defn normalize-with-support
  "`[normal-form rule-handles]`, using the same reducer as `normalize`.
  Only actually chosen rules contribute, not rules merely applicable to the initial
  input or unrelated reader-visible equations. An unhandled pure rule contributes
  no stored handle."
  [rules term]
  (let [handles (volatile! #{})
        form (normalize rules term #(when-let [h (:handle %)] (vswap! handles conj h)))]
    [form @handles]))

(def equality-relations
  "The equality relations, whose argument positions are **mentions**: `(equals A B)`
  relates two names and uses neither as a term.  `normalize-sentence` and
  `rule-applies?` leave those positions as written, at any depth.  Normalizing them
  would restate what the sentence says: under `(equals (fatherOf (fatherOf ?x))
  (grandfather_of ?x))`, the denial `(not (equals (fatherOf (fatherOf Tom))
  (grandfather_of Tom)))` would become `(not (equals (grandfather_of Tom)
  (grandfather_of Tom)))`, a denial of reflexivity.  Ground congruence reads the same
  set (`res/equality-mention-heads` is this var), and `kb/equality-predicates` mirrors
  it."
  '#{rewriteOf sameAs equals})

(defn- holds-equality-relation?
  "Does `term` hold an equality relation at any depth?"
  [term]
  (and (sequential? term)
       (or (contains? equality-relations (first term))
           (boolean (some holds-equality-relation? term)))))

(defn- sentence-argument?
  "Is `sentence` a predication whose arguments `normalize-sentence` reduces — a non-empty
  compound that is not itself an equality relation?"
  [sentence]
  (and (sequential? sentence) (seq sentence)
       (not (contains? equality-relations (first sentence)))))

(defn- map-argument-terms
  "`sentence` with `f` applied to each argument term `normalize-sentence` reduces.  An
  argument holding no equality relation is one such term.  An equality relation is
  left as written.  Any other compound holding one keeps its head, and its arguments
  are taken the same way, so `(not (equals …))` and a rule's `(and (equals …) …)` keep
  their equality literals while every other literal beside them normalizes."
  [f sentence]
  (letfn [(arg [t]
            (cond
              (not (holds-equality-relation? t))      (f t)
              (contains? equality-relations (first t)) t
              :else                                    (apply list (first t) (map arg (rest t)))))]
    (apply list (first sentence) (map arg (rest sentence)))))

(defn- argument-terms
  "The terms `map-argument-terms` applies its function to, in the same walk."
  [sentence]
  (letfn [(arg [t]
            (cond
              (not (holds-equality-relation? t))      [t]
              (contains? equality-relations (first t)) []
              :else                                    (mapcat arg (rest t))))]
    (when (sentence-argument? sentence)
      (mapcat arg (rest sentence)))))

(defn normalize-sentence
  "Normalize a **sentence** `(pred arg…)`: rewrite each argument as a term, leaving the
  predication's functor and shape untouched.  A schematic equation is about denoting
  terms, which live in argument position; a predication is an assertion, not a term.
  An equality relation's arguments are not rewritten, at the top or nested
  (`equality-relations`).  A no-op when `rules` is empty."
  [rules sentence]
  (if (and (seq rules) (sentence-argument? sentence))
    (map-argument-terms #(normalize rules %) sentence)
    sentence))

(defn normalize-sentence-with-support
  "`normalize-sentence` with the handles of the actual term-rewrite steps."
  [rules sentence]
  (let [handles (volatile! #{})
        form (if (and (seq rules) (sentence-argument? sentence))
               (map-argument-terms
                (fn [term]
                  (let [[value hs] (normalize-with-support rules term)]
                    (vswap! handles into hs)
                    value)) sentence)
               sentence)]
    [form @handles]))

;; ---- schematic-equation detection ----------------------------------------

(defn schematic-equation?
  "Is `sentence` a schematic equational rule: an `(equals L R)` with a compound side and a
  variable?  A ground `(equals (F a) (F b))` is not one; it reifies to symbols
  (docs/nat.md).  A compound `sameAs` is refused by `wff`, and a compound `rewriteOf` is a
  NAT declaration."
  [sentence]
  (and (sequential? sentence)
       (= 'equals (first sentence))
       (= 3 (count sentence))
       (some sequential? (rest sentence))
       (not (sx/ground-term? sentence))))

(defn rule-applies?
  "Does the oriented rule `{:lhs …}` rewrite some argument subterm of `sentence`?  Asked
  at exactly the positions `normalize` reduces at (`rewritable-subterms`, outside the
  `equality-relations` arguments), so a rule justifies only the twins it rewrote."
  [rule sentence]
  (boolean (some #(some (fn [st] (reduct rule st)) (rewritable-subterms %))
                 (argument-terms sentence))))

;; ---- confluence surfacing: critical pairs between rules ------------------
;; Detection, not completion (docs/equational.md, "Confluence — surfaced, not
;; completed").  A rule's overlap with itself is not reported: one syntactic term always
;; normalizes one way.

(defn- resolve-var
  "`t` with a bound variable followed to the **end** of its chain.  One binding may name
  another — unifying `?a` with `?b` and then `?b` with `?c` leaves `?a → ?b → ?c` — so a
  single hop can hand back a variable that is itself bound, and reading that as unbound
  both loses a constraint (the next `assoc` overwrites the binding it should have
  extended) and hides an occurrence from the occurs check.  Terminates because the occurs
  check is what forbids a cyclic chain."
  [subst t]
  (if (and (sx/variable? t) (contains? subst t))
    (recur subst (get subst t))
    t))

(defn- occurs? [subst v t]
  (let [t (resolve-var subst t)]
    (cond
      (= v t)         true
      (sequential? t) (some #(occurs? subst v %) t)
      :else           false)))

(defn- unify*
  [s t subst]
  (if (nil? subst)
    nil
    (let [s (resolve-var subst s)
          t (resolve-var subst t)]
      (cond
        (= s t)          subst
        (sx/variable? s) (when-not (occurs? subst s t) (assoc subst s t))
        (sx/variable? t) (when-not (occurs? subst t s) (assoc subst t s))
        (and (sequential? s) (sequential? t) (= (count s) (count t)))
        (reduce (fn [sub [a b]] (unify* a b sub)) subst (map vector s t))
        :else            nil))))

(defn- unify
  "The most general unifier of `s` and `t` as a substitution map, or nil.  Two-way (both
  sides' variables may bind), with an occurs check so a cyclic binding cannot form."
  [s t]
  (unify* s t {}))

(defn- resolve-fully
  "`term` with every variable replaced by its (recursively resolved) binding in
  `subst` — the substitution applied to a fixpoint, safe because `unify`'s occurs check
  forbids a cycle."
  [subst term]
  (cond
    (sx/variable? term)  (if (contains? subst term) (recur subst (get subst term)) term)
    (sequential? term)   (apply list (map #(resolve-fully subst %) term))
    :else                term))

(defn- rename-rule
  "A rule with its variables renamed `prefix0`, `prefix1`, … by first occurrence, so two
  rules being overlapped share no variable names.  RHS variables are a subset of the
  LHS's (orientation guarantees it), so the LHS numbering covers both."
  [rule prefix]
  (let [vars (distinct (sx/form-vars (:lhs rule)))
        m    (into {} (map-indexed (fn [i v] [v (symbol (str prefix i))]) vars))]
    {:lhs (subst (:lhs rule) m) :rhs (subst (:rhs rule) m)}))

(defn- positions
  "Every `[path compound-subterm]` of `term` a rewrite can happen **at**, `path` a vector of
  child indices and `[]` the whole term: argument positions only, as
  `rewritable-subterms` reads them."
  [term]
  (letfn [(go [t path]
            (when (and (sequential? t) (seq t))
              (cons [path t]
                    (apply concat
                           (map-indexed (fn [i c] (go c (conj path (inc i)))) (rest t))))))]
    (go term [])))

(defn- replace-at
  "`term` with the subterm at `path` replaced by `new`."
  [term path new]
  (if (empty? path)
    new
    (let [i (first path)]
      (apply list (map-indexed (fn [j c] (if (= j i) (replace-at c (rest path) new) c)) term)))))

(defn- critical-pairs
  "The critical pairs where a subterm of `r1`'s LHS overlaps `r2`'s LHS: for each such
  overlap, `[rewrite r1 at the root, rewrite that subterm with r2]` under the unifier.
  `r1` and `r2` are renamed to disjoint variables first."
  [r1 r2]
  (let [{l1 :lhs rr1 :rhs} (rename-rule r1 "?a")
        {l2 :lhs rr2 :rhs} (rename-rule r2 "?b")]
    (for [[path sub] (positions l1)
          :let [sigma (unify sub l2)]
          :when sigma]
      [(resolve-fully sigma rr1)
       (resolve-fully sigma (replace-at l1 path rr2))])))

(defn non-joining-pairs
  "The overlaps between `new-rule` and the **other** rules in `all-rules` whose two
  reducts do not normalize to one form, as `{:with <other handle> :form-a t :form-b t}`.
  `all-rules`, `new-rule` included, is the active set the reducts are normalized against."
  [new-rule all-rules]
  (let [others   (remove #(= (:handle %) (:handle new-rule)) all-rules)
        rulemaps (map #(select-keys % [:lhs :rhs]) all-rules)]
    (for [o others
          [a b] (distinct (concat (critical-pairs new-rule o) (critical-pairs o new-rule)))
          :let  [na (sx/canon (normalize rulemaps a))
                 nb (sx/canon (normalize rulemaps b))]
          :when (not= na nb)]
      {:with (:handle o) :form-a na :form-b nb})))
