;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.assert-entry
  "The per-sentence write entry point: what `vaelii.core/assert` does once it has one
  sentence in one context.

  Three things live together here because the assert path runs them as one step and
  `preview` has to undo all three:

  - **The premise mark**, written to the network node and the record slot together
    (`put-premise-mark`), and resolved from content rather than arrival order
    (`mark-premise` says why a bare re-assert may not downgrade a class).
  - **The rule slots**, reconciled when a rule is stated twice
    (`reconcile-rule-slots!`, `join-direction`).
  - **The dispatch** a sentence takes — imperative, `ist`, rule, or plain fact
    (`assert-one`).

  `*premise-audit*` is the one hook `preview` and `edit!` need: bound to an atom, every
  mark records the datum's prior state first, which is the whole of what putting a KB
  back the way it was found requires.

  **`assert-one` takes the re-entry as an argument.**  An `(ist Ctx S)` sentence is not
  stored — it asserts `S` in `Ctx` — so the dispatch re-enters the caller's own entry
  point.  That is `vaelii.core/assert`, and an engine namespace may not require
  `vaelii.core`, so the caller passes it in."
  (:require [clojure.string :as str]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.imperative :as imperative]
            [vaelii.impl.integrate :as integrate]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.special :as special]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.violations :as violations]
            [vaelii.impl.wiring :refer [*defer-settle?*]]))

(def ^:dynamic *premise-audit*
  "When bound to an atom, every premise mark on the assert path first records the
  datum's **prior** premise state here — `{handle {:premise? bool :strength kw}}`,
  first writer wins.  That is the whole of what `preview` needs to put a KB back the
  way it found it: a handle it marked and that did not exist before is retracted, one
  that existed as a non-premise is un-marked, and one that was already a premise gets
  its original strength back.  `edit!` binds it too, for the same undo on a batch that
  refused.  Nil, and free, on every ordinary assert."
  nil)

(defn put-premise-mark
  "Write the premise mark on sentex `h` at exactly `strength` — the network's node and
  the record store's slot, which the assert path always moves together.  One function so
  neither half can be marked without the other: the network is what labelling reads and
  the record is what `recover` rebuilds the network from, so a KB whose two halves
  disagreed would answer one thing until it restarted and another afterwards.

  Callers say `mark-premise` instead.  This is the raw write, and the only caller that
  wants it is the one *restoring* a mark it recorded — `rollback-batch!`, putting back a
  class the KB already held rather than stating one."
  [kb h strength]
  (jtms/add-premise (reasoning/tms kb) h strength)
  (p/mark-premise (:records kb) h strength))

(defn- mark-premise
  "Mark sentex `h` a premise, at the **stronger** of the class it already stands at and
  the `strength` offered.  One function so the audit above has one hook rather than
  three, and so neither half can be marked without the other (`put-premise-mark`).

  **Resolved from content, never from arrival order** — the rule
  `reconcile-rule-slots!` states for a re-asserted rule's slots, at the fact entry point, where
  it decides belief rather than what a caller reads back.  A re-assert carrying no
  `:strength` states nothing about the class: the `:default` it falls back to is the
  entry point's fallback and not the caller's claim, so reading that silence as a *downgrade*
  made the same knowledge in two orders reach two sets of beliefs.  Asserting
  `(flies Tweety)` known-true, re-asserting it bare, then asserting the known-true
  negation left the original **defeated**; the same three sentences without the bare
  re-assert in the middle left it believed and the pair an irreducible clash.
  `strength/max` is commutative and idempotent, so the orders agree and a third
  assertion changes nothing.

  Narrowing a class is `retract!` and re-assert, exactly as it is for a rule's
  `:direction`, `:defeasible` and `:strength` (docs/canonicalization.md).  A handle that
  is not a premise stands at nothing — `jtms/premise-strength` reads nil, which ranks 0
  — so it takes the offered class whole, and a retraction therefore leaves no class
  behind for the next assertion to inherit."
  [kb h strength]
  (when-let [audit *premise-audit*]
    (let [tms (reasoning/tms kb)]
      (swap! audit (fn [m]
                     (if (contains? m h)
                       m
                       (assoc m h {:premise? (jtms/premise? tms h)
                                   :strength (jtms/premise-strength tms h)}))))))
  (put-premise-mark kb h (strength/max (jtms/premise-strength (reasoning/tms kb) h) strength)))

(defn check-rule-sentence
  "Every pre-storage check a rule must pass, as a step that writes nothing —
  `checks/check-rule!`, the list both storage entry points read (the other being a generator
  firing, `chain/place-conclusion`).  A generator's own three are in that list rather
  than beside it, because a *minted* rule can be a generator too (docs/generators.md)
  and a check only this entry point ran would be one the fixpoint could store around."
  [kb sentence context]
  (checks/check-rule! kb sentence context))

(defn- join-direction
  "The direction a rule stated two ways holds in: the **least restrictive** of the two.

  `:inert` is the bottom (it runs in neither engine).  `:backward` (backward only) and
  `:forward-only` (forward only) are partial and incomparable; `:forward` / `:both` are
  the top — both mean forward + backward.  Joining two spellings that each lack what the
  other has therefore adds that capability and comes to `:both`, the canonical forward +
  backward value.  A join rather than a pick, because the two spellings are two claims
  about the same rule and a rule that may run forwards *and* may run backwards may do
  both."
  [a b]
  (cond
    (= a b)      a
    (= :inert a) b
    (= :inert b) a
    :else        :both))

(defn- reconcile-rule-slots!
  "Bring a re-asserted rule's `:direction` / `:defeasible` to the value the two
  assertions jointly state, and re-chain it if that newly lets it run forwards.

  These two slots are not in the sentex identity key — a rule is one rule however its
  direction is spelled — so `find-or-create-sentex` hands back the stored record and the
  second spelling would otherwise be dropped.  Dropping it is **arrival-order
  dependent**: a bare `implies` after a `set/inertRule` would stay inert and never fire,
  and after a `set/defaultRule` stay defeasible and lose to a monotonic rival it should
  tie with — the same two assertions reaching two sets of beliefs, which
  `docs/nmtms.md` does not permit.

  So the slots are resolved from **content** instead: the least restrictive direction
  (`join-direction`), and strict over defeasible — a rule asserted once without
  `set/defaultRule` is a rule somebody stated as holding outright.  Both are commutative
  and idempotent, so the two orders agree and a third assertion changes nothing.

  The record moves, and so does the one derived copy of the defeasibility slot: the
  justifications already fired through this rule carry its contribution as their
  `:strength`, read off the record at fire time (`chain/rule-view-of`), so a
  defeasible→strict resolution must reach them or belief keeps the arrival order this
  fn exists to remove — facts asserted *between* the two spellings would hold
  conclusions at `:default` that the same assertions in the other order hold at
  `:monotonic`.  `jtms/restrength-informant` updates that slot and relabels the
  affected region.  The direction join needs no such reach-back: it only ever *adds*
  capability (`join-direction` is a join, never a meet), backward capability is read
  off the record at query time, and new forward capability is the `chain-all` below.

  The trie key does not carry these slots, and `index-rule-sentex` indexes predicates
  rather than direction, so nothing is re-indexed."
  [kb h stored sentence context opts]
  (let [incoming (res/kb-sentex kb sentence context)
        dir      (join-direction (:direction stored) (:direction incoming))
        def?     (when (and (:defeasible stored) (:defeasible incoming)) true)]
    (when (or (not= dir (:direction stored))
              (not= (boolean def?) (boolean (:defeasible stored))))
      (let [s' (assoc stored :direction dir :defeasible def?)]
        (p/put-sentex (:records kb) s')
        (when (not= (boolean def?) (boolean (:defeasible stored)))
          ;; Both copies of the conferred strength, together — the record store's
          ;; justification records (what `supporting-justifications` shows and what
          ;; `recover` rebuilds the network from) and the network's graph copy (what
          ;; labelling reads), the same both-halves rule `mark-premise` states.
          (let [strength (if def? :default :monotonic)
                tms      (reasoning/tms kb)]
            (doseq [jid (jtms/dependents tms h)
                    :let [j (p/get-justification (:records kb) jid)]
                    :when (and j (= h (:informant j)) (not= strength (:strength j)))]
              (p/put-justification (:records kb) (assoc j :strength strength)))
            (jtms/restrength-informant tms h strength)))
        ;; newly forward-capable: it has never been joined over the facts already stored
        (when (and (:chain? opts true)
                   (rules/forward-sentex? s')
                   (not (rules/forward-sentex? stored)))
          (chain/chain-all kb [h] opts))
        (when-not *defer-settle?* (settle/settle kb))))))

(defn- assert-rule-sentence
  "Assert a rule **as written** — any `set/*Rule` wrapper included, since the sentex
  constructor canonicalizes it into the record's `:direction` / `:defeasible`.  The
  well-formedness checks run on the bare rule inside the wrappers.

  Idempotent: a re-asserted rule resolves to the existing sentex.  Where the two
  spellings disagree about direction or defeasibility, the slots are resolved from
  content rather than from which arrived first — see `reconcile-rule-slots!`.

  **`opts :strength` reaches the record here exactly as it does at the fact entry point**, and
  it is the rule's *own* defeat class — whether a contradicting default can defeat the
  rule itself.  What a firing confers on its conclusion is a different question with a
  different authority: `chain/rule-view-of` reads it off `:defeasible`, so a rule stored
  at `:monotonic` still concludes at its weakest antecedent unless it is bare.  Nothing
  in the engine defeats a rule, so the slot is one that reads back rather than one that
  moves belief — `docs/nmtms.md` states the absence.

  **Re-marking on the existing branch is the mark itself, not only its class.**  A rule
  can be stored and not be a premise — a generator's stamped rule is a *conclusion*,
  resting on the generator's justification — and asserting it is a second and
  independent ground for it, exactly as asserting an already-derived fact is at the
  other entry point.  Left unmarked, `assert` answered with a handle for a rule that the next
  retraction of the generator took away with it.

  All three slots resolve alike, and from **content**: `:direction` and `:defeasible`
  in `reconcile-rule-slots!`, `:strength` below by taking the stronger.  A re-assert
  carrying no `:strength` states nothing about the class — the `:default` it falls back
  to is the entry point's fallback, not the caller's claim — so reading that silence as a
  downgrade would leave `defeat-class` answering differently for the same two assertions
  in the two orders.  No belief moves either way, nothing defeating a rule; this is what
  a caller reads back.  Narrowing any of the three is `retract!` and re-assert."
  [kb sentence context opts]
  (check-rule-sentence kb sentence context)
  (let [strength   (get opts :strength :default)
        [h s new?] (kb/find-or-create-sentex kb sentence context strength)]
    (if new?
      (do
        (mark-premise kb h strength)
        (special/index-rule-sentex kb h s)
        ;; A rule naming a predicate or type the closure has **already** merged is
        ;; restated on arrival, exactly as one stored before the merge is restated by it
        ;; (`assert-one`'s own arm, at the fact entry point): `birthplaceOf ⇒ bornIn` changes a
        ;; functor the rule reasons over, so the original is superseded and the twin
        ;; carries the inference.  Without it the same rule, fact and merge fire under the
        ;; representative in the orders that state the rule first and under a retired
        ;; spelling in the rest (docs/equality.md, "Merging predicates and types").  An
        ;; individual-only merge holds a rule back, which `kb/rewritable-sentex?` decides.
        (let [mig (when (kb/rewritable-sentex? kb s) (special/migrate-sentex kb s))]
          (when (seq (:superseded mig))
            (special/refresh-supersessions kb (:superseded mig)))
          ;; defeasible or not, a forward-capable rule seeds the one agenda: `chain`
          ;; joins it over existing facts (process-datum -> fire-rule) at its own strength
          ;; — and the twin joins beside it, since the spelling this rule was written in
          ;; stops firing the moment the supersession above lands
          (when (and (:chain? opts true) (rules/forward-sentex? s))
            ;; ...and if an antecedent reads a declared-transitive predicate, the partner
            ;; facts go back as triggers too: a rule joined over the store from the
            ;; transitive side sees the stored links only, since its closure is answered
            ;; rather than stored and an open goal on it has no record to lead from
            (chain/chain-all kb (-> (into [h] (:new mig))
                                    (into (special/transitive-rule-seeds kb s)))
                             opts))
          (violations/report kb (:violations mig)))
        (when-not *defer-settle?* (settle/settle kb)))
      (do
        (reconcile-rule-slots! kb h s sentence context opts)
        ;; `find-or-create-sentex` hands back the stored record and drops the strength
        ;; the second assertion carried, the same way it drops the direction the
        ;; reconcile above puts back — and the mark is worth making for a second reason
        ;; than the class: a stored rule need not be a premise at all (a generator's
        ;; stamped rule is a *conclusion*, resting on the generator's justification), and
        ;; asserting one is an independent ground for it, exactly as asserting an
        ;; already-derived fact is at the fact entry point.
        ;;
        ;; **Resolved from content, like the two slots above it.**  `strength/max` takes
        ;; the stronger, so the two orders agree and a third assertion changes nothing —
        ;; the rule `reconcile-rule-slots!` holds for `:direction` and `:defeasible`, and
        ;; it holds here for the same reason: a re-assert carrying no `:strength` states
        ;; nothing about the class, so reading that silence as a downgrade made
        ;; `defeat-class` answer differently for the same two assertions in either order.
        ;; Narrowing one is `retract!` and re-assert, as it is for the other two.  A
        ;; record with no class yet — nil, so not a premise — ranks 0 and takes the
        ;; incoming class.
        (let [resolved (strength/max (:strength s) strength)]
          (when (not= resolved (:strength s))
            (mark-premise kb h resolved)
            ;; the mark relabels, and an entry point that moves a label settles before it
            ;; returns.  A class move alone moves none, nothing in the engine defeating
            ;; a rule — but the *first* mark of a rule that was only ever concluded puts
            ;; it IN, and that revives whatever it licenses.
            (when-not *defer-settle?* (settle/settle kb))))))
    h))

;; A `set/defaultRule` wrapper sets `:defeasible` on the record, so the one rule path
;; below handles every flavour — do not add a second entry point per flavour.

(defn assert-exceptWhen-meta!
  "Store one exceptWhen exception against the rule at `rule-handle` as a
  belief-following `(exceptWhen <aligned-query> (sentexHandle rule-handle))`
  meta-sentex, and return its handle.

  `exc` is the exception's conjunct literals in the *author's* variable names (as
  written beside the rule), and `author-vm` is the canonical→author varmap of the rule
  **as written in this assert** — not the rule's stored varmap, which carries whatever
  names the rule was *first* asserted with, so a re-reference under new variable names
  would misalign.  The query is mapped to the rule's canonical variables through it, so
  a firing's bindings substitute straight in; an exception variable no antecedent binds
  is refused (`:exception-not-closed`), as is one that would close a cycle through
  negation (`check-exceptWhen-stratified`).  Storing it posts the re-check index
  (`index-exceptWhen-meta`) and settles, so any conclusion the new exception now blocks
  is swept before this returns."
  [kb rule-handle exc author-vm context opts]
  (let [rsx (p/get-sentex (:records kb) rule-handle)]
    (when-not (and rsx (rules/rule? rsx))
      (throw (ex-info (str "exceptWhen names handle " rule-handle ", which is not a rule")
                      {:type :not-well-formed :handle rule-handle :exception (vec exc)})))
    (let [author  (into #{} (vals author-vm))                       ; the rule's author variables
          inv     (into {} (map (fn [[cv av]] [av cv])) author-vm)  ; {?x ?var0}
          exc-vars (distinct (mapcat #(filter sx/variable? (tree-seq sequential? seq %)) exc))
          loose   (remove author exc-vars)]
      (when (seq loose)
        (throw (ex-info (str "exception is not closed: " (pr-str (vec loose))
                             " unbound by the rule's antecedents")
                        {:type :exception-not-closed :unbound (vec loose)
                         :exception (vec exc) :rule rule-handle})))
      (let [aligned (sx/sort-conjuncts (map #(sx/canon (res/substitute % inv)) exc))
            meta-s  (sx/exceptWhen-meta aligned rule-handle)]
        ;; Each conjunct is held to the naming invariants, like every other literal a
        ;; rule carries.  `check-rule-sentence` runs `nm/check!` on `rules/inner-rule`,
        ;; which has already peeled the query off, and nothing else reached it — so
        ;; `nm/literals`' `:exception` role and the "exceptWhen exception" wording in
        ;; `literal-roles` existed with nothing on the assert path calling them, and
        ;; `(exceptWhen (lives_in ?x cold_place) …)` stored the snake_case-arity-2
        ;; literal `docs/naming.md` says is refused.  The store holding what the front
        ;; entry point refuses is the structure of corruption these checks exist to stop.
        (run! #(nm/check! (:naming kb) % context) aligned)
        (checks/check-no-imperative meta-s)
        (checks/check-exceptWhen-stratified kb rule-handle (keep nm/functor aligned) context)
        (let [strength   (get opts :strength :default)
              [h s new?] (kb/find-or-create-sentex kb meta-s context strength)]
          (when new?
            (mark-premise kb h strength)
            (integrate/sentex-added kb s h)          ; index-exceptWhen-meta + queue the re-check
            ;; If the rule already migrated before this exception existed, migration never
            ;; saw the exception — re-point it onto the live twin(s) now, or the twin fires
            ;; unguarded (docs/equality.md, the meta-after-merge case).
            (special/migrate-meta-onto-twins kb s)
            (when-not *defer-settle?* (settle/settle kb)))  ; sweep what the new exception now blocks
          h)))))

(defn ist-parts
  "The `[context sentence]` an `(ist Ctx S)` names, or nil when the form is not one — a
  bare `(ist Ctx)` included.

  `assert` and `check` both read the form here, so a malformed `ist` is one refusal on
  both paths.  Reaching into it positionally is how the two would disagree: `check`
  taking a default and reporting `:shape` while `assert` takes none and throws a bare
  `IndexOutOfBoundsException`, which carries no `:type` for a caller to discriminate on
  and names nothing a writer can act on."
  [sentence]
  (when (and (sequential? sentence)
             (= sx/ist-functor (first sentence))
             (= 3 (count sentence)))
    [(second sentence) (nth sentence 2)]))

(defn ist-shape-problem
  "The `:shape` problem a malformed `ist` is refused with — a value for `check`, and the
  `ex-info` `assert` throws."
  [sentence]
  {:type :shape :sentence sentence
   :message (str "an (ist Ctx S) names a context and a sentence, got " (pr-str sentence))})

;; `(ist Ctx S)` handed to `assert` recurses into `assert` with the inner sentence
;; (`assert-one` below), and `assert` is defined after it — a genuine forward
;; reference, and the only one here: query and settle live below this namespace, in
;; impl.kb and impl.settle.
(defn assert-one
  "Assert a single sentence (any conjunctive-consequent rule is split into one rule
  per conjunct by `assert` before reaching here).  Returns the sentex handle.

  `from` carries what only the caller's entry point knows: `:assert-fn`, re-entered for
  an `(ist Ctx S)` sentence and for nothing else, and `:bulk?`, the caller-guaranteed
  bulk-load mode that turns off the per-fact machinery which only validates or dedups.
  `:bulk?` is a value rather than a var read because the public knob is
  `vaelii.core/*bulk-load?*`, and an engine namespace may not read `vaelii.core`."
  [kb sentence context opts {:keys [assert-fn bulk?]}]
  (cond
    ;; A `do/` imperative is an instruction, not a fact: nothing is stored, and what
    ;; comes back is the action's result (docs/labeling.md).  First, so no naming or
    ;; well-formedness check ever sees a form that is not a sentence.
    (sx/do-form? sentence)
    (imperative/run kb sentence context)

    ;; (ist Ctx S) is not stored — it finds or creates S in Ctx (ist semantics)
    (and (sequential? sentence) (= sx/ist-functor (first sentence)))
    (if-let [[ctx s] (ist-parts sentence)]
      (assert-fn kb s ctx opts)
      (let [p (ist-shape-problem sentence)]
        (throw (ex-info (:message p) (dissoc p :message)))))

    ;; Every rule flavour takes one path: a bare `(implies ..)` (a :both rule) and
    ;; any `set/*Rule` wrapping of one.  The wrapper is not stripped here — it is
    ;; canonicalized into the record's :direction / :defeasible by the sentex
    ;; constructor.  Routing through the checked rule path also gets
    ;; range-restriction and rule indexing, rather than storing a plain premise.
    (rules/rule-sentence? (rules/inner-rule sentence))
    (assert-rule-sentence kb sentence context opts)

    :else
    ;; A virtual wrapper (`set/*Rule`, `set/defaultRule`, `exceptWhen`) is meaningful
    ;; only around an implication, but the sentex constructor peels it off whatever it
    ;; wraps — so `(set/defaultRule (dog Felix))` *stores* the bare `(dog Felix)`.
    ;; Peel it here too, so the checks below run on the sentence that will actually be
    ;; stored.  Checking the wrapper instead let a fact walk past every definitional
    ;; check: the functor is `set/defaultRule` and the sole argument is a list, so
    ;; naming, arg, disjointness and functionality all matched nothing and passed
    ;; vacuously, and the stripped fact landed in the store unchecked.
    ;;
    ;; A *forced* universal predicate (e.g. genlCx) has its extent placed in
    ;; CxUniverse by force — no justification, the fact simply lives there.
    (let [sentence (rules/inner-rule sentence)
          pred    (nm/functor sentence)
          ;; the global property read on purpose: this decides where the sentex is
          ;; *stored*, and storage cannot vary by the writer's visibility — scoping
          ;; the lift by what could see the declaration would be circular
          context (if (and pred (tax/has-prop? (reasoning/taxonomy kb) :forced-decontextualized pred))
                    special/universal-context context)]
      ;; Bulk load skips every check below: each only *validates* (none writes), and
      ;; the caller has guaranteed the corpus is well-formed — including the arg
      ;; store query in `constraint-checks`, the dominant per-fact cost (`:bulk?`).
      ;; The checks yield one *value* forward: what the argument constraints entail
      ;; about this sentence's arguments.  It is computed here — where the declarations
      ;; are already being read — and materialized below, because at this point the
      ;; sentex does not exist yet and there is no handle to justify a derived type
      ;; against.  Empty unless assertive argument types are on.
      (let [ents (when-not bulk?
                   (nm/check! (:naming kb) sentence context)
                   (checks/check-ground kb sentence context)
                   (when-let [ps (seq (special/wff-problems (reasoning/taxonomy kb) sentence context))]
                     (throw (ex-info (str "not well-formed: " (str/join "; " ps))
                                     {:type :not-well-formed :sentence sentence})))
                   ;; the rule-set half of well-formedness, for the *other* thing that can
                   ;; close a cycle through negation: a genl / genlCx edge arriving
                   ;; underneath rules already stored (docs/exceptions.md).  Before anything
                   ;; is written and before the taxonomy is touched, so a refusal leaves
                   ;; nothing behind.
                   (checks/check-edge-stratified kb sentence context)
                   ;; ...and the third thing that can: a `closed_extent_predicate` grant
                   ;; arriving underneath rules that read the predicate negatively, which
                   ;; is what turns those reads into negation as failure (docs/naf.md)
                   (checks/check-closed-extent-stratified kb sentence context)
                   (checks/constraint-checks kb sentence context))
            strength (get opts :strength :default)
            ;; Bulk load skips the dedup trie-walk: a distinct corpus never hits an
            ;; existing sentex, so `create-sentex` directly is the same result the
            ;; `find-or-create` miss branch would take.
            ;; the record is born carrying its strength, so `mark-premise` below has
            ;; nothing to re-store — see `kb/create-sentex`.
            ;;
            ;; **A predicate that permutes keeps the probe.**  `create-sentex` canonicalizes
            ;; the arguments (`res/kb-sentex` sorts a `(symmetric P)` literal, and the
            ;; commuting component of a commutative one), so the bulk row is *stored* in
            ;; canonical order — but skipping the probe stored it beside a permutation
            ;; already there, two records for one proposition, which the caller cannot
            ;; pre-dedup: telling `(siblingOf Bob Ann)` from a stored `(siblingOf Ann Bob)`
            ;; needs exactly the `(symmetric P)` read the fast path is avoiding, and
            ;; `(covering W C A B)` from a stored `(covering W A B C)` the commuting-group
            ;; read.  So for such a functor the row takes `find-or-create` (one taxonomy
            ;; read per row for a rare mark), which is what makes the bulk result identical
            ;; to loading one-by-one (`integrate/commute-existing`, vaelii#61).  Both reads
            ;; are inside the `bulk?` `and`, so `and` short-circuits them away on the
            ;; non-bulk path, which never reaches them.
            [h s _]  (if (and bulk?
                              (not (and pred
                                        (let [tax (reasoning/taxonomy kb)]
                                          (or (tax/has-prop? tax :symmetric pred)
                                              (seq (tax/commuting-groups tax pred)))))))
                       (let [[h s] (kb/create-sentex kb sentence context strength)] [h s true])
                       (kb/find-or-create-sentex kb sentence context strength))]
        (mark-premise kb h strength)
        ;; The add-side choke point: the sentex is reflected into every cache
        ;; through the special-predicate table and the exception re-check is queued
        ;; — one call, so no assert path can forget either half.  An equality
        ;; sentex reaches the closure there and migrates what it displaces;
        ;; everything else returns nil.  The three slots it returns are the caller's
        ;; to apply: the twins are chaining seeds, the supersessions are belief, and
        ;; and the violations are reported after `chain-all` so they carry its run id.
        (let [eq (integrate/sentex-added kb s h)
              ;; a fact naming a term the closure has *already* displaced is restated
              ;; on arrival, exactly as a fact asserted before the merge is restated
              ;; by it — otherwise migration would depend on which came first
              own  (when (kb/rewritable-sentex? kb s) (special/migrate-sentex kb s))
              ;; ...and, symmetrically, a handle-naming meta (`except`, a target-following
              ;; reply) whose *target* already migrated: the merge ran before this meta
              ;; existed, so migration never saw it — re-point it onto the live twin(s) now,
              ;; or the twin stays visible / unendorsed (docs/equality.md, the
              ;; meta-after-merge case).  A no-op for a non-meta or an un-migrated target.
              _    (special/migrate-meta-onto-twins kb s)
              ;; ...and the equality a `functional` declaration now infers instead of
              ;; throwing, which merges in its turn
              fnl  (special/derive-functional-equalities kb sentence context h)
              ;; ...and the same inference from the declaration's side, so a
              ;; `(functional P)` arriving after P's facts merges what they already
              ;; licensed rather than only what follows it
              fex  (special/equate-existing kb sentence)
              ;; ...and from the third side: a `genl` edge between predicates brings
              ;; stored sub-predicate facts under a `functional` mark above them
              fdn  (special/equate-under-edge kb sentence)
              ;; ...and the antisymmetric merge, in the same three arrival orders: a fact
              ;; meeting its converse under an `(anti_symmetric P)` mark, the declaration
              ;; meeting the facts, and the `genl` edge bringing them under a mark above
              asym (special/derive-antisymmetric-equalities kb sentence context h)
              axe  (special/antisym-equate-existing kb sentence)
              axd  (special/antisym-equate-under-edge kb sentence)
              ;; ...and the same three ingredients once more, through the *other*
              ;; closure, which takes all three of them in one call.  A `genlCx` edge
              ;; widens which merges a context can see, so it restates the sentexes the
              ;; widened ancestor set newly exposes to one — or the record keeps a spelling every
              ;; read from below has retired (docs/equality.md, "An equality applies where
              ;; it is visible") — and it is the fourth arrival order of the
              ;; functional/antisymmetric merge besides, alongside the declaration meeting
              ;; the facts and the `genl` edge bringing them under a mark above them: two
              ;; already-marked facts can be made jointly visible for the first time by an
              ;; edge, and without this the merge those two arrival orders derive would
              ;; depend on whether the contexts were ever wired together before the facts
              ;; arrived.  One call and not three because a *computed* edge — one the
              ;; structural producer materializes with nobody asserting it — has to make
              ;; the same one, and a list each entry point remembers separately is a list one of
              ;; them forgets (vaelii#56)
              cxe  (special/reconcile-context-edge kb sentence)
              ;; ...and the one mark whose retroactive half is a *storage* migration
              ;; rather than a derivation: `(symmetric P)` sorts a literal's arguments at
              ;; the entry point, so the rows stored before it are spelled the way no row stored
              ;; after it will be — and a mirrored pair is two records for one
              ;; proposition, each retractable without the other (vaelii#61)
              sym  (integrate/commute-existing kb sentence h)
              mig  (merge-with into {:new [] :superseded [] :violations []}
                               eq own fnl fex fdn asym axe axd cxe sym)]
          ;; Only when this assert actually merged something.  The reconcile re-examines
          ;; every entry the closure currently displaces, and an assert that merged
          ;; nothing cannot change one: an entry stops being displaced when its terms
          ;; stop rewriting (the closure shrank) or when its restatement stops being
          ;; stored (a deletion), and an assert does neither.  Ungated it is O(merged)
          ;; per assertion — on OpenCyc, 1,489 merges re-examined 780,000 times.
          (when (seq (:superseded mig))
            (special/refresh-supersessions kb (:superseded mig)))
          ;; the CxUniverse copy, if the predicate is decontextualized — a
          ;; deduction off this sentex and the declaration, so it is a chaining seed
          ;; of its own, and it reports rather than throws when it cannot be admitted
          (let [lift  (special/deduce-lifts kb sentence h context)
                ;; ...and the types the argument constraints entail about this
                ;; sentence's arguments, each a deduction off this sentex and the
                ;; declaration that licensed it.  Both directions, because a
                ;; declaration must reach the facts already stored exactly as it
                ;; reaches the facts that follow: `deduce-arg-types` is this sentence
                ;; meeting the declarations, `entail-existing` is this sentence *being*
                ;; a declaration and meeting the facts.  `ents` are pre-checked: they
                ;; came from `constraint-checks`, so `entailment-check` already ran the
                ;; definitional constraint check over them before the store, and the
                ;; materializer need not run it a second time (special/inadmissible).
                args  (special/deduce-arg-types kb ents h context (not bulk?))
                back  (special/entail-existing kb sentence h)
                ;; ...and the third order of the same three ingredients: a `genl` edge
                ;; between predicates brings stored sub-predicate facts under the
                ;; declarations already written above them
                down  (special/entail-under-edge kb sentence)
                ;; ...and, when this sentence is a `defn*` collection definition, the
                ;; forward rule(s) it expands into — derived rule sentexes justified by
                ;; this fact, so retracting or defeating it withdraws the rule and
                ;; everything it concluded (docs/defns.md).  A non-`defn*` sentence pays
                ;; one functor read and returns the empty result.
                dfn   (special/materialize-defn-rules kb sentence h context)
                mig   (update mig :violations into
                              (concat (:violations lift) (:violations args)
                                      (:violations back) (:violations down)
                                      (:violations dfn)))
                seeds (-> [h]
                          (into (:new mig))
                          (into (:new lift))
                          (into (special/minted-seeds kb (:new down)))
                          ;; the companion rule goes on the agenda so it fires over the
                          ;; facts already stored, the way a minted generator rule does
                          (into (:new dfn))
                          ;; a minted type makes this fact matchable at a type it did
                          ;; not have, so it goes on the agenda for the same reason the
                          ;; genl seeds below do — a rule on `(animal ?x)` must fire off
                          ;; a type the entailment minted, within this same assert,
                          ;; and a minted genl edge seeds what it brings under a rule
                          (into (special/minted-seeds kb (:new args)))
                          (into (special/minted-seeds kb (:new back)))
                          ;; a new genl edge makes stored facts matchable at a
                          ;; supertype they did not have — they go back on the agenda,
                          ;; or the same knowledge would derive different things in
                          ;; different arrival orders
                          (into (special/subsumption-seeds kb sentence))
                          ;; ...and a new genlCx edge makes stored facts visible to
                          ;; a rule that could not see them, which is the same failure
                          ;; through the other closure
                          (into (special/visibility-seeds kb sentence))
                          ;; ...and a new link of a declared-transitive predicate extends
                          ;; a closure that is answered rather than stored, so no pair of
                          ;; it is ever a datum: the partner triggers of the rules joined
                          ;; to it go back, or the same failure again through a third
                          (into (special/transitive-seeds kb sentence)))]
            (when (:chain? opts true) (chain/chain-all kb seeds opts))
            ;; **After** the chain, so the entry carries the run that just ran: a
            ;; violation a merge created — the twin that would have made one individual
            ;; both a dog and a cat — is this assert's to report, and
            ;; `violations/report` stamps each entry with `(:runs @chain-stats)`
            ;; (docs/equality.md, "Interactions — Disjointness").  The ledger itself
            ;; accumulates and is emptied only by `clear-violations!`.
            (violations/report kb (:violations mig))))
        ;; `*defer-settle?*` is bound only while a rule firing mints a skolem NAT
        ;; mid-fixpoint (`skolemize-conclusion`): the nested `(termOfUnit K E)` assert
        ;; is monotonic bookkeeping and the enclosing firing settles once when it
        ;; completes, so settling here per mint is redundant churn (docs/skolem.md).
        (when-not *defer-settle?* (settle/settle kb))
        h))))
