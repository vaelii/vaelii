;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.prover
  "A query-time prover for `(bravely S)` and `(cautiously S)` — brave/cautious reading
  of the dilemmas the KB currently holds, answered as a read and never committed.

  ## What it answers

  `(cautiously S)` holds when `S` is in **every** optimal labeling of the current
  dilemmas; `(bravely S)` when `S` is in **some**.  Over a coexisting `P`/`¬P` dilemma the
  engine declines to arbitrate (docs/exceptions.md), both sides are IN, and an ordinary
  `ask` reports both — so it cannot tell the *forced* belief from the *arbitrary* one.  A
  brave/cautious read can: in a Nixon diamond `(bravely (pacifist N))` holds and
  `(cautiously (pacifist N))` does not, because the other labeling gives it up.

  This is the read-path delivery of the forced/arbitrary signal.  The only prior route to
  it, `do/labeling`, **commits** — it re-asserts the kept side at `:monotonic` and defeats
  the loser everywhere (docs/labeling.md).  This prover commits nothing: it reads
  `label/classify-dilemmas` — `dilemma-program`/`classify-program` with a backend, the
  solve-free `label/classify-local` without one — all pure reads over settled belief, so a
  query answers and leaves belief, `contradictions` and `last-program` exactly as they were.

  ## Opting in

  Registered like the other optional reasoners — `(add-reasoner kb :brave-cautious)` — so
  the ASP stack stays off a KB's load path until a caller asks (docs/asp.md).  With a
  backend it enumerates optima and classifies exactly; **with none it reads the solve-free
  JTMS bracket** (`label/classify-local`), which enumerates the dilemmas' optimal
  resolutions from the dependency graph and classifies each datum by which resolutions keep
  it — `:true` in every, `:supportable` in some, `:false` in none.  Exact for a datum whose
  clusters it enumerates: the one cluster its support touches, or several whose product of
  resolutions stays within `VAELII_CLASSIFY_MAX_JOINT_OPTIMA`.  A datum past that cap, or
  one touching a cluster too large to enumerate, degrades to `:supportable`
  (docs/labeling.md).

  ## Where it stops

  **Ground `S` only.**  `(bravely (pacifist N))` is answered; an open `(bravely (pacifist
  ?x))` is not applicable and no prover answers it, rather than enumerating the contested
  atoms — the same restraint `different` takes.

  **A query, not a fact and not an antecedent.**  `bravely`/`cautiously` are not
  assertible (`wff/brave-cautious-problems`): a stored one would be a computed value with
  no way to keep it current, the reason the aggregates and `unknown` are refused too.  As a
  rule antecedent the answer carries no support (it is not a `SupportingProver`), so the
  forward join drops it and it derives nothing — a read, not something belief rests on.
  Threading its support (the dilemma's contested handles) so a rule could rest on it is the
  open design point, deferred until a use asks for it."
  (:require
   [vaelii.impl.asp.label :as label]
   [vaelii.impl.kb :as kb]
   [vaelii.impl.resolution :as res]
   [vaelii.impl.sentex :as sx]
   [vaelii.impl.types.prover :as prover-types]))

(defn- ground? [form]
  (not (some sx/variable? (tree-seq sequential? seq form))))

(defn- modal-goal? [goal]
  (and (sequential? goal)
       (contains? #{'bravely 'cautiously} (first goal))
       (= 2 (count goal))
       (ground? (second goal))))

(defn- believed?
  "Is the stored sentex for `s` believed as `context` reads it (`res/believed-at?`)?  The
  brave/cautious answer for a datum in no dilemma — every optimum agrees with belief
  there — read at `ask`'s level (what is stored or cached, no rule expansion)."
  [kb s context]
  (boolean (when-let [h (kb/find-sentex-handle kb s context)]
             (res/believed-at? kb h context))))

(defn- holds?
  "Does `(<modal> s)` hold in `context`?  `label/classify-dilemmas` classifies the current
  dilemmas — through the ASP backend when one is reachable, else the solve-free JTMS
  bracket (`label/classify-local`) — into in-every / in-some / in-none, and is nil when
  there is no dilemma, where the answer is ordinary belief."
  [kb modal s context]
  (if-let [cls (label/classify-dilemmas kb)]
    (let [h (kb/find-sentex-handle kb s context)]
      (cond
        (nil? h)                          false                 ; not stored — nothing to read
        (contains? (:true cls) h)         true                  ; every resolution: brave & cautious
        (contains? (:supportable cls) h)  (= modal 'bravely)    ; some only: brave, not cautious
        (contains? (:false cls) h)        false                 ; no resolution
        :else                             (believed? kb s context)))  ; not contested: belief
    (believed? kb s context)))                        ; no dilemma at all: ordinary belief

(defrecord BraveCautiousProver []
  prover-types/Prover
  (applicable?  [_ _ goal _] (modal-goal? goal))
  (est-bindings [_ _ _ _] 1)          ; a ground modal check: it holds or it does not
  (cost         [_ _ _ _] :compute)   ; a backend solve (brave + cautious), or the solve-free bracket
  ;; Authoritative for its shape: `bravely`/`cautiously` are not assertible and no rule
  ;; concludes one, so the superset claim holds against an empty field — as it does for
  ;; `different` — and `sole-prover` guards it like any other claimant regardless.
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context]
    (let [[modal s] goal]
      (if (holds? kb modal s context) [{}] []))))

(defn brave-cautious-prover
  "The `(bravely S)` / `(cautiously S)` prover, for `add-prover` — or, the ordinary way in,
  `(add-reasoner kb :brave-cautious)`."
  []
  (->BraveCautiousProver))
