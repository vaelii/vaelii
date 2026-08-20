;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.spec
  "Opt-in `clojure.spec` contracts for the public `vaelii.core` API.

  The engine already validates the *content* of what it stores — naming invariants,
  well-formedness, disjointness (`vaelii.impl.naming` / `vaelii.impl.wff`).  These
  specs guard the other side: the *shape* of the arguments a caller passes, the
  option and budget maps especially, so a typo like `{:strength :monotone}` or a
  string where a millisecond count belongs is rejected at the door with a spec
  explanation rather than surfacing as a downstream error.

  Nothing here runs unless a caller opts in with
  `(clojure.spec.test.alpha/instrument public-syms)` — instrumentation is a
  dev/test tool, so shipping the specs costs a populated registry and no more.  They
  double as machine-checked documentation and as generators for property tests.

  The `s/fdef`s name their targets by fully-qualified symbol, so loading this
  namespace does not load `vaelii.core` — the specs register against the public var
  names, which are the stable contract, independent of how the implementation is
  split across `vaelii.impl.*`.

  Coverage is the **single-item** shape-carrying surface: every entry point that
  takes a handle, a context, a level or a strength/direction, together with the
  option and budget maps those entry points carry.  The pure taxonomy reads
  (`genls`, `context-up`, …) are specced too, since a wrong-arity call to one of
  them is exactly the kind of mistake instrumentation should surface early.

  **Fourteen publics that take an option map are outside it**, and instrumenting says
  nothing about their arguments: the batch writes (`assert-many`,
  `bulk-assert-facts!`), the fork and the two consequence readers over it (`fork`,
  `preview`, `edit-with-consequences!`), the store transfers (`import!`, `export!`),
  the two search-back reads (`search-tree`, `compare-tacticians`), the four-valued
  epistemic-status read (`argue`), and `check`, `abduce`, `kb-quality`, `clear-caches`.
  A roster test in
  `vaelii.spec-test` holds that list against `vaelii.core`'s own arglists, so the
  gap is a set somebody has to edit rather than a claim that goes stale in silence:
  a public that grows an option map, or arrives with one, fails that test until it
  is either specced here or named there."
  (:require [clojure.spec.alpha :as s]
            [vaelii.impl.strength :as strength]))

;; ---- building blocks ----------------------------------------------------

(s/def ::kb map?)                          ; a KB record satisfies map?
(s/def ::context symbol?)                  ; a Cx-prefixed CapitalCamelCase symbol, or the
                                           ; open '?ctx variable the read paths default to
(s/def ::sentence some?)                   ; a sentence (a list) — never nil
(s/def ::goal (s/or :one seq?              ; a single goal sentence …
                    :conjunction           ; … or a vector of them (a conjunctive query)
                    (s/coll-of seq? :kind vector?)))
(s/def ::handle nat-int?)                  ; the integer id a stored sentex is referenced by
(s/def ::id ::handle)                      ; the sentex record's own handle field

;; Everywhere a caller *passes* a handle, nil is a legal argument with a graceful
;; answer — `handle-of` answers nil for a sentence the KB does not hold, and the
;; handle-taking fns answer that nil rather than refuse it (`in?` false, `why`
;; `{:stored? false}`, `retract!` zero counts; `vaelii.handle-test` pins the
;; contract).  So the arg specs below take `::handle-arg`, while `::handle` /
;; `::id` stay the real thing for returns and record fields.
(s/def ::handle-arg (s/nilable ::handle))
(s/def ::term some?)                       ; any indexable term (symbol, number, compound)
(s/def ::truth #{:true :false})            ; a literal's polarity
(s/def ::prover some?)                     ; a vaelii.impl.provers/Prover
(s/def ::solver some?)                     ; a vaelii.impl.solve/Solver

;; ---- the assert option map ----------------------------------------------
;; The **roster** is `vaelii.core/assert-opt-keys`, which refuses a key `assert` does
;; not read; these specs say what a key it does read may hold.  `s/keys` is open, so an
;; unknown key is the roster's to reject and not restated here — but the two must name
;; the same keys, or an option one of them has never heard of passes both.

(s/def ::strength strength/assertable)
(s/def ::chain? boolean?)
(s/def ::max-depth (s/nilable nat-int?))
(s/def ::max-derivations (s/nilable nat-int?))
(s/def ::on-progress ifn?)
(s/def ::progress-every-ms (s/nilable nat-int?))
(s/def ::creator some?)
(s/def ::provenance map?)
(s/def ::opts (s/keys :opt-un [::strength ::chain? ::max-depth ::max-derivations
                               ::on-progress ::progress-every-ms ::creator ::provenance]))

;; ---- the rule-assertion option map (assert-rule adds :direction) --------

(s/def ::direction #{:forward :backward :inert :both})
(s/def ::rule-opts (s/keys :opt-un [::strength ::chain? ::max-depth ::max-derivations
                                    ::on-progress ::progress-every-ms ::creator
                                    ::provenance ::direction]))

;; ---- the anytime budget map ---------------------------------------------

(s/def ::max-ms (s/nilable nat-int?))
(s/def ::max-results (s/nilable nat-int?))
(s/def ::max-cost (s/nilable #{:lookup :compute :search}))
(s/def ::budget (s/keys :opt-un [::max-ms ::max-results ::max-cost ::max-depth]))

;; ---- the lookup-to-query stack ------------------------------------------

(s/def ::level (s/int-in 0 8))             ; 0 :raw … 7 :proved
(s/def ::floor (s/int-in 0 8))             ; escalate's starting level

;; ---- predicate-metadata property kinds (has-prop? / props) --------------

;; Every kind the special table marks, and `special-table-test` holds the two together:
;; a kind the engine records and this set omits is a legal `has-prop?` call that
;; instrumentation refuses.  `:reifiable` / `:unreifiable` / `:quoting` / `:context-denoting`
;; are a *function*'s kind rather than a predicate's, which `::term` admits either way; the
;; four `:declares-*` say that a predicate is the **subject** of an argument constraint
;; rather than that it carries a property, which is what lets the descension ask whose
;; declarations bind a tuple without an index probe per super-predicate
;; (`taxonomy/arg-declaration-props`).
(s/def ::prop-kind #{:transitive :symmetric :asymmetric :reflexive :functional
                     :irreflexive :anti-symmetric
                     :decontextualized :forced-decontextualized :target-following
                     :abducible :reifiable :unreifiable :quoting :context-denoting :modal
                     :declares-arg-isa :declares-arg-genl :declares-quoted-arg
                     :declares-inter-arg-isa})

;; ---- the sentex-map return contract -------------------------------------
;; `query` / `sentex` / the extent readers return sentex records, which are maps.
;; The *stable* contract is the map shape below — `:id`, `:sentence`, `:context`
;; are always present; a rule adds `:antecedent` / `:consequent` / `:direction`.
;; Treat the result as a map: callers should key into it, never depend on the
;; concrete `vaelii.impl.sentex/AtomicSentex` / `RuleSentex` record class, which is an internal
;; detail free to change.
(s/def ::sentex-map (s/keys :req-un [::id ::sentence ::context]
                            :opt-un [::truth ::strength]))
(s/def ::sentex-seq (s/coll-of ::sentex-map))

;; ---- construction -------------------------------------------------------

(s/fdef vaelii.core/open-kb
  :args (s/cat :opts (s/? map?)))

;; ---- writes -------------------------------------------------------------

;; `opts` is nilable: the lower arities delegate to the full one with `opts nil`
;; (`(assert kb s c)` → `(assert kb s c nil)`), so instrumentation sees the nil.
(s/fdef vaelii.core/assert
  :args (s/cat :kb ::kb :sentence ::sentence
               :context (s/? ::context) :opts (s/? (s/nilable ::opts)))
  :ret  (s/or :one ::handle :many (s/coll-of ::handle)))

(s/fdef vaelii.core/assert-rule
  :args (s/cat :kb ::kb :antecedents (s/coll-of ::sentence) :consequent ::sentence
               :context (s/? ::context) :opts (s/? (s/nilable ::rule-opts)))
  :ret  (s/or :one ::handle :many (s/coll-of ::handle)))

(s/fdef vaelii.core/assert-inert
  :args (s/cat :kb ::kb :sentence ::sentence :context ::context)
  :ret  ::handle)

(s/fdef vaelii.core/ist
  :args (s/cat :kb ::kb :ctx ::context :s ::sentence)
  :ret  ::handle)

(s/fdef vaelii.core/forward-chain
  :args (s/cat :kb ::kb :opts (s/? (s/nilable map?))))

(s/fdef vaelii.core/retract!
  :args (s/cat :kb ::kb :handle ::handle-arg))

(s/fdef vaelii.core/add-provenance
  :args (s/cat :kb ::kb :handle ::handle-arg :m map?))

(s/fdef vaelii.core/add-prover
  :args (s/cat :kb ::kb :prover ::prover))

(s/fdef vaelii.core/set-solver
  :args (s/cat :kb ::kb :solver ::solver))

;; ---- reads: match / query -----------------------------------------------

(s/fdef vaelii.core/sentexes-matching
  :args (s/cat :kb ::kb :sentence ::sentence :context (s/? ::context))
  :ret  ::sentex-seq)

;; No `:ret` — the shape depends on an option.  `query` returns binding maps, or, under
;; `{:proof? true}`, `{:bindings … :proof …}` per answer; a `:ret` naming one would be
;; wrong for the other, and naming their union would assert nothing.
(s/fdef vaelii.core/query
  :args (s/cat :kb ::kb :goal ::goal :context (s/? ::context) :opts (s/? (s/nilable map?))))

(s/fdef vaelii.core/query?
  :args (s/cat :kb ::kb :goal ::goal :context (s/? ::context) :opts (s/? (s/nilable map?)))
  :ret  boolean?)

(s/fdef vaelii.core/prove
  :args (s/cat :kb ::kb :goal ::goal :context (s/? ::context)))

(s/fdef vaelii.core/provable?
  :args (s/cat :kb ::kb :goal ::goal :context (s/? ::context))
  :ret  boolean?)

(s/fdef vaelii.core/ask
  :args (s/cat :kb ::kb :goal ::goal :context (s/? ::context)))

(s/fdef vaelii.core/ask?
  :args (s/cat :kb ::kb :goal ::goal :context (s/? ::context))
  :ret  boolean?)

(s/fdef vaelii.core/query-plan
  :args (s/cat :kb ::kb :goal ::goal :context (s/? ::context)))

(s/fdef vaelii.core/handle-of
  :args (s/cat :kb ::kb :sentence ::sentence :context ::context)
  :ret  (s/nilable ::handle))

(s/fdef vaelii.core/contexts-of
  :args (s/cat :kb ::kb :sentence ::sentence))

(s/fdef vaelii.core/believed?
  :args (s/cat :kb ::kb :handle ::handle-arg :context ::context)
  :ret boolean?)

(s/fdef vaelii.core/belief-status
  :args (s/cat :kb ::kb :handle ::handle-arg :context ::context)
  :ret map?)

;; ---- reads: the lookup-to-query stack -----------------------------------

(s/fdef vaelii.core/lookup
  :args (s/cat :kb ::kb :level ::level :goal ::sentence :context (s/? ::context)))

(s/fdef vaelii.core/escalate
  :args (s/cat :kb ::kb :goal ::sentence :context (s/? ::context) :floor (s/? ::floor)))

(s/fdef vaelii.core/explain-levels
  :args (s/cat :kb ::kb :goal ::sentence :context (s/? ::context)))

;; ---- reads: anytime -----------------------------------------------------

(s/fdef vaelii.core/ask-within
  :args (s/cat :kb ::kb :goal ::goal :context (s/? ::context) :budget ::budget))

(s/fdef vaelii.core/prove-within
  :args (s/cat :kb ::kb :goal ::goal :context (s/? ::context) :budget ::budget))

(s/fdef vaelii.core/resume
  :args (s/cat :partial map? :budget ::budget))

;; ---- reads: type / taxonomy ---------------------------------------------

(s/fdef vaelii.core/isa?
  :args (s/cat :kb ::kb :x ::term :t ::term :context (s/? ::context))
  :ret  boolean?)

(s/fdef vaelii.core/types-of
  :args (s/cat :kb ::kb :x ::term :context (s/? ::context)))

(s/fdef vaelii.core/disjoint?
  :args (s/cat :kb ::kb :a ::term :b ::term :context (s/? ::context))
  :ret  boolean?)

(s/fdef vaelii.core/term-role
  :args (s/cat :term ::term)
  :ret  (s/nilable #{:variable :number :context :individual :predicate :type
                     :lexeme :sense}))

(s/fdef vaelii.core/disjoint-metatypes :args (s/cat :kb ::kb))
(s/fdef vaelii.core/metatype-members   :args (s/cat :kb ::kb :m ::term))

(s/fdef vaelii.core/genls  :args (s/cat :kb ::kb :t ::term :context (s/? ::context)))
(s/fdef vaelii.core/specs  :args (s/cat :kb ::kb :t ::term :context (s/? ::context)))
(s/fdef vaelii.core/genl?
  :args (s/cat :kb ::kb :sub ::term :super ::term :context (s/? ::context))
  :ret boolean?)
(s/fdef vaelii.core/types    :args (s/cat :kb ::kb))
(s/fdef vaelii.core/contexts :args (s/cat :kb ::kb))
(s/fdef vaelii.core/context-up   :args (s/cat :kb ::kb :c ::context))
(s/fdef vaelii.core/context-down :args (s/cat :kb ::kb :c ::context))
(s/fdef vaelii.core/sees?  :args (s/cat :kb ::kb :k ::context :y ::context) :ret boolean?)
(s/fdef vaelii.core/has-prop?
  :args (s/cat :kb ::kb :kind ::prop-kind :pred ::term :context (s/? ::context))
  :ret boolean?)
(s/fdef vaelii.core/props  :args (s/cat :kb ::kb :kind ::prop-kind))
(s/fdef vaelii.core/inverse-of
  :args (s/cat :kb ::kb :pred ::term :context (s/? ::context)))

;; ---- reads: equality closure --------------------------------------------

(s/fdef vaelii.core/representative
  :args (s/cat :kb ::kb :term ::term :context (s/? ::context)))
(s/fdef vaelii.core/same-class?
  :args (s/cat :kb ::kb :a ::term :b ::term :context (s/? ::context))
  :ret boolean?)
(s/fdef vaelii.core/equiv-class
  :args (s/cat :kb ::kb :term ::term :context (s/? ::context)))
(s/fdef vaelii.core/deprecated?
  :args (s/cat :kb ::kb :term ::term :context (s/? ::context))
  :ret boolean?)

;; ---- reads: term index & extents ----------------------------------------

(s/fdef vaelii.core/find-sentexes     :args (s/cat :kb ::kb :term ::term) :ret ::sentex-seq)
(s/fdef vaelii.core/find-sentexes-all :args (s/cat :kb ::kb :terms (s/coll-of ::term)) :ret ::sentex-seq)
(s/fdef vaelii.core/indexable-terms   :args (s/cat :sentex ::sentex-map))
(s/fdef vaelii.core/readable-sentence :args (s/cat :sentex (s/nilable ::sentex-map)))

(s/def ::extent-opts (s/nilable (s/keys :opt-un [::believed?])))
(s/def ::believed? boolean?)

(s/fdef vaelii.core/sentexes-in-context
  :args (s/cat :kb ::kb :context ::context :opts (s/? ::extent-opts)) :ret ::sentex-seq)
(s/fdef vaelii.core/count-in-context
  :args (s/cat :kb ::kb :context ::context) :ret nat-int?)
(s/fdef vaelii.core/sentexes-with-functor
  :args (s/cat :kb ::kb :pred ::term :opts (s/? ::extent-opts)) :ret ::sentex-seq)
(s/fdef vaelii.core/count-with-functor
  :args (s/cat :kb ::kb :pred ::term) :ret nat-int?)
(s/fdef vaelii.core/sentexes-with-arg
  :args (s/cat :kb ::kb :pos pos-int? :term ::term :opts (s/? ::extent-opts)) :ret ::sentex-seq)
(s/fdef vaelii.core/count-with-arg
  :args (s/cat :kb ::kb :pos pos-int? :term ::term) :ret nat-int?)

;; the vocabulary — the terms themselves, not the sentexes holding them
(s/def ::match #{:prefix :substring :regex})
(s/def ::case-sensitive? boolean?)
(s/def ::limit pos-int?)
(s/def ::find-terms-opts (s/nilable (s/keys :opt-un [::match ::case-sensitive? ::limit])))

(s/fdef vaelii.core/terms      :args (s/cat :kb ::kb) :ret vector?)
(s/fdef vaelii.core/term-count :args (s/cat :kb ::kb) :ret nat-int?)
(s/fdef vaelii.core/find-terms
  :args (s/cat :kb ::kb :q some? :opts (s/? ::find-terms-opts)) :ret vector?)

;; ---- introspection ------------------------------------------------------

(s/fdef vaelii.core/in?          :args (s/cat :kb ::kb :handle ::handle-arg) :ret boolean?)
(s/fdef vaelii.core/sentex       :args (s/cat :kb ::kb :handle ::handle-arg) :ret (s/nilable ::sentex-map))
(s/fdef vaelii.core/justification    :args (s/cat :kb ::kb :jid ::handle-arg))
(s/fdef vaelii.core/premise?     :args (s/cat :kb ::kb :handle ::handle-arg))
(s/fdef vaelii.core/defeat-class :args (s/cat :kb ::kb :handle ::handle-arg) :ret (s/nilable ::strength))
(s/fdef vaelii.core/supporting-justifications :args (s/cat :kb ::kb :handle ::handle-arg))
(s/fdef vaelii.core/dependent-justifications  :args (s/cat :kb ::kb :handle ::handle-arg))
(s/fdef vaelii.core/provenance   :args (s/cat :kb ::kb :handle ::handle-arg) :ret (s/nilable map?))

;; `why` reads one option, `:max-depth`.  `s/keys` is open, so an unknown key is the
;; fn's own roster to reject (`:unknown-option`), as with the assert opts above; the
;; spec says what the key it does read may hold.
(s/def ::why-opts (s/keys :opt-un [::max-depth]))

(s/fdef vaelii.core/why
  :args (s/cat :kb ::kb :handle ::handle-arg :opts (s/? (s/nilable ::why-opts)))
  :ret map?)

(s/fdef vaelii.core/why-not
  ;; two shapes: a stored handle, or a proposition (for a blocked/excepted answer
  ;; that no handle carries — see docs/exceptions.md)
  :args (s/alt :by-handle   (s/cat :kb ::kb :handle ::handle-arg)
               :by-sentence (s/cat :kb ::kb :sentence ::sentence :context ::context))
  :ret  map?)

;; ---- persistence / recovery ---------------------------------------------

(s/fdef vaelii.core/recover :args (s/cat :kb ::kb))
(s/fdef vaelii.core/reindex :args (s/cat :kb ::kb))
(s/fdef vaelii.core/clear!  :args (s/cat :kb ::kb))

;; ---- the roster ---------------------------------------------------------

(def public-syms
  "The fully-qualified symbols the `s/fdef`s above cover — pass to
  `clojure.spec.test.alpha/instrument` / `unstrument`.  This is the single-item
  shape-carrying surface: everything that takes a handle, context, level, strength
  or direction, the option and budget maps those carry, plus the taxonomy and
  equality reads.  The fourteen opts-taking publics it does **not** reach are named in
  this namespace's docstring and pinned by `vaelii.spec-test`."
  '[vaelii.core/open-kb
    vaelii.core/assert
    vaelii.core/assert-rule
    vaelii.core/assert-inert
    vaelii.core/ist
    vaelii.core/forward-chain
    vaelii.core/retract!
    vaelii.core/add-provenance
    vaelii.core/add-prover
    vaelii.core/set-solver
    vaelii.core/sentexes-matching
    vaelii.core/query
    vaelii.core/query?
    vaelii.core/prove
    vaelii.core/provable?
    vaelii.core/ask
    vaelii.core/ask?
    vaelii.core/query-plan
    vaelii.core/handle-of
    vaelii.core/contexts-of
    vaelii.core/lookup
    vaelii.core/escalate
    vaelii.core/explain-levels
    vaelii.core/ask-within
    vaelii.core/prove-within
    vaelii.core/resume
    vaelii.core/isa?
    vaelii.core/types-of
    vaelii.core/disjoint?
    vaelii.core/term-role
    vaelii.core/disjoint-metatypes
    vaelii.core/metatype-members
    vaelii.core/indexable-terms
    vaelii.core/readable-sentence
    vaelii.core/clear!
    vaelii.core/genls
    vaelii.core/specs
    vaelii.core/genl?
    vaelii.core/types
    vaelii.core/contexts
    vaelii.core/context-up
    vaelii.core/context-down
    vaelii.core/sees?
    vaelii.core/has-prop?
    vaelii.core/props
    vaelii.core/inverse-of
    vaelii.core/representative
    vaelii.core/same-class?
    vaelii.core/equiv-class
    vaelii.core/deprecated?
    vaelii.core/find-sentexes
    vaelii.core/find-sentexes-all
    vaelii.core/terms
    vaelii.core/term-count
    vaelii.core/find-terms
    vaelii.core/sentexes-in-context
    vaelii.core/count-in-context
    vaelii.core/sentexes-with-functor
    vaelii.core/count-with-functor
    vaelii.core/sentexes-with-arg
    vaelii.core/count-with-arg
    vaelii.core/in?
    vaelii.core/believed?
    vaelii.core/belief-status
    vaelii.core/sentex
    vaelii.core/justification
    vaelii.core/premise?
    vaelii.core/defeat-class
    vaelii.core/supporting-justifications
    vaelii.core/dependent-justifications
    vaelii.core/provenance
    vaelii.core/why
    vaelii.core/why-not
    vaelii.core/recover
    vaelii.core/reindex])
