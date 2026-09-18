;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.abduce
  "What would have to be true.

  Backward chaining answers *is this provable?*  Abduction answers the complementary
  question — *what would have to be true for it to be provable?* — and mints the answer
  as a **hypothesis**: an ordinary premise, in a context of its own, at `:default`
  strength, assumed rather than derived.

  The hard parts of abduction are containment, arbitration and cleanup, and this engine
  already had all three, built for other reasons:

  - **Containment is the context lattice.**  A hypothesis goes into a fresh context
    hung *below* the asking context, so it sees everything the question could see and
    nothing that existed before it can see the hypothesis.  A shipped rule firing over a
    hypothesis places its conclusion **in** that context, because placement is the
    maximal common descendant (docs/contexts.md) — so the consequences land inside the
    thing that gets discarded, with nothing arranging for it.  That is the sandbox's
    shape (`vaelii.browser.sandbox`), for the same reason.
  - **Arbitration is strengths.**  A hypothesis is asserted `:default`, so it is
    defeasible by construction: a `:monotonic` fact that contradicts it wins through the
    ordinary defeat path, with no abduction-specific rule anywhere.
  - **Cleanup is retraction.**  A hypothesis is a premise, so `retract!` and the
    dependency-directed sweep remove it and everything it supported.

  So the new code here is the **search** — finding the dead end and deciding what may be
  assumed — and not the belief plumbing.

  Two things the caller is owed, and they are the contract:

  1. **An ignored `abduce` leaves the KB as it found it.**  The lifecycle tears the
     context down before returning unless `:keep?` says otherwise, and it tears it down
     on the way out of an exception too.
  2. **Every answer names its assumptions.**  Solutions come back beside the hypothesis
     set that licensed them, never as if they had been proved.  An empty `:hypotheses` is
     the claim that nothing was assumed.

  See docs/abduction.md."
  (:require [clojure.string :as str]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(def default-opts
  "The caps, and why each exists.

  `:max-hypotheses` bounds how much may be assumed in one call.  An uncapped abducer over
  a rule-rich KB does not terminate usefully — every dead end offers a hypothesis and
  every hypothesis opens fresh dead ends — so the cap is what makes the loop finite
  rather than merely usually-finite.

  `:max-depth` bounds *where* one may be assumed: a dead end reached through more than
  this many rule expansions is left alone.  A hypothesis minted twelve rules deep
  explains the goal in the sense that anything explains anything.

  Both are reported when they bite (`:status`, `:refused`), never silently applied."
  {:max-hypotheses 8
   :max-depth      8})

;; ---- the operation map: handed down, not reached up for ---------------------------
;; Everything abduction needs from outside itself arrives in one `ops` map, and nothing
;; in this namespace names `vaelii.core`:
;;
;;   :rules-fn  `(fn [kb goal context] -> parsed rules)` — core's own candidate chooser,
;;              so abduction searches with exactly the rules `prove` would
;;   :assert    minting a hypothesis is a real assert — checks, index, chaining, settle
;;   :edit      discarding one is a real edit
;;
;; One map rather than a function per dependency because they travel together to the same
;; places: every stage that writes also searches, so threading them apart put the same two
;; arguments side by side through five signatures.  `run` adds `:rules` — `:rules-fn`
;; bound to this run's scratch context — so the stages below it take the operation map alone.
;;
;; Handing them down works here and would not for `vaelii.impl.nat` or
;; `vaelii.impl.skolem`, and the difference matters: abduction is only ever
;; entered from the public API, so `vaelii.core` is the *sole* caller of the two entry
;; points that write.  There is no recursion to break and so nothing to resolve at
;; runtime — where a NAT mint is reached from inside the chaining fixpoint the assert path
;; itself started, which is why that one goes through `vaelii.impl.wiring`.

;; ---- the abduction context ----------------------------------------------

(defn new-token
  "A fresh context token.  Random rather than content-keyed, and deliberately: two
  abductions of one goal in one process must not share a scratch context.  Nothing about
  belief depends on the name — the caller reads the context out of the result rather than
  predicting it — and it is torn down before it could matter to anything else."
  []
  (str/replace (subs (str (java.util.UUID/randomUUID)) 0 13) "-" ""))

(def ^:dynamic *token*
  "The token the abduction context is named by, or nil for a fresh one.  `vaelii.core`
  binds it to the token an operation-log frame records for an `abduce` call
  (`vaelii.impl.oplog`), so the recorded call names the context the call named."
  nil)

(defn- token [] (or *token* (new-token)))

(defn context-for
  "The abduction context named by `token`.  `CxAbduction<token>` satisfies the
  context naming invariant, so it is an ordinary context in every other respect."
  [token]
  (symbol (str "CxAbduction" token)))

(defn- edge [actx base] (list 'genlCx actx base))

(defn- open
  "Mint a fresh abduction context below `base` and answer it.

  Bare, not `open!`: it adds one `genlCx` edge and nothing else, and `discard!` beside it
  is what takes the context back — the `!` is reserved for the operation that cannot be
  undone.

  `:monotonic`, because the *edge* is not a hypothesis: which context sees which is a
  fact about the scratch space, and a defeasible one would let a contradiction among the
  hypotheses quietly unhook the context holding them."
  [kb base ops]
  (let [actx (context-for (token))]
    ((:assert ops) kb (edge actx base) 'CxUniverse {:strength :monotonic})
    actx))

(defn- edge-handles
  "The handles of the `genlCx` edges that made `actx` a context — usually one, but a
  `{:keep? true}` caller may have hung more on it, and every one is removed or the
  scratch context stays reachable.

  Found through the **argument root** rather than remembered: an edge has `actx` at
  argument 1, so one positional read answers it and the teardown needs no bookkeeping to
  survive being handed nothing but a context name.  Every match is returned rather than
  the first the posting set happens to surface, so the teardown does not depend on hash
  order and does not leave a second edge standing."
  [kb actx]
  (->> (reads/as-stored-with-arg (:index kb) 1 actx)
       (keep #(p/get-sentex (:records kb) %))
       (filter #(= 'genlCx (nm/functor (:sentence %))))
       (mapv :id)))

(defn discard!
  "Discard the abduction context whole: every sentex in it, then the edge that made it a
  context.  Answers `{:removed-sentexes n :removed-justifications n}`.

  One `edit` for the extent, so it is one settle and the dependency-directed sweep does
  the rest — a conclusion derived from a hypothesis goes with the hypothesis, and its
  justification with it.  The edge is fetched separately because it was never *in* the
  extent: `genlCx` is forced-decontextualized, so it is stored in CxUniverse.

  Idempotent: a context already gone has an empty extent and no edge.  Irreversible,
  hence the `!` — that is the whole point of it."
  [kb actx ops]
  (let [drop!   (fn [hs] (if (seq hs)
                           (:removed ((:edit ops) kb {:remove (vec hs)}))
                           {:removed-sentexes 0 :removed-justifications 0}))
        extent  (drop! (reads/as-stored-in-context (:index kb) actx))
        the-edge (drop! (edge-handles kb actx))]
    (merge-with + extent the-edge)))

;; ---- the decision ---------------------------------------------------------
;; Deliberately separate from the search.  An ungated abducer hypothesizes anything and
;; is worth nothing, so what may be assumed is stated once, as a predicate over a
;; sentence, and the search calls it.  It reads nothing but its arguments, so it is a
;; call site away from any other search that wants the same rule.

(defn- contradicted?
  "Is a negation of `sentence` believed and visible from `context`?

  The *now* half of the contradiction gate.  A clash discovered later resolves itself —
  the hypothesis is `:default`, so a `:monotonic` fact defeats it through the ordinary
  path — but a clash visible at mint time is not an arbitration to run, it is a
  hypothesis with no business existing.

  `matches-visible`, so **visibility** does the narrowing that matters: a negation stated
  in a context the asker cannot see does not block, exactly as it would not block an
  assertion.  Its belief filter is vacuous here rather than useful, and pleasingly so —
  defeating `(not S)` means believing `S`, and a believed `S` is not a dead end for the
  search to have reached."
  [kb sentence context]
  (boolean (seq (res/matches-visible kb (list 'not sentence) context))))

(defn abducible?
  "May `sentence` be hypothesized in `context`?  The whole gate, cheapest test first.

  * **A ground positive literal.**  An open hypothesis is a skolemization question
    (docs/skolem.md) and not this one, so an unbound variable refuses rather than
    enumerates.  A negation has functor `not`, which nothing declares abducible, so the
    grant below excludes it with no rule of its own.
  * **Declared abducible**, read scoped from `context` — the one gate that is a grant
    rather than a veto, and the reason a KB with no `abducible_predicate` in it abduces
    nothing at all.
  * **Legally assertible**: the same four checks every minted sentence passes
    (`special/inadmissible`) — naming, the definitional constraints, well-formedness,
    edge stratification.  A sentence `assert` would refuse must not be one the search
    assumes, or abduction becomes a way around the checks.
  * **Not already contradicted** where it would be minted."
  [kb sentence context]
  (boolean
   (and (seq? sentence)
        (let [pred (nm/functor sentence)]
          (and (symbol? pred)
               (sx/ground-term? sentence)
               (tax/has-prop? (reasoning/taxonomy kb) :abducible pred context)
               (nil? (special/inadmissible kb sentence context))
               (not (contradicted? kb sentence context)))))))

(defn maybe-abduce
  "The hypothesis this dead end licenses, or nil.

  `goal` is a subgoal the search exhausted, `depth` the rule expansions taken to reach
  it.  This is the decision function a proof-search hook calls, and everything it needs
  is in its arguments — which is what lets one rule govern the standalone pass here and
  any hook inside the search that calls it."
  [kb goal context {:keys [max-depth]} depth]
  (when (and (or (nil? max-depth) (<= depth max-depth))
             (abducible? kb goal context))
    goal))

;; ---- the search -----------------------------------------------------------

(defn- attempt
  "One proof attempt in `actx`, and the dead ends it hit — `{:solutions :dead-ends}`.

  `res/*dead-end*` is a sink, so this is the identical search `prove` runs; the only
  difference is that somebody is listening.  `prove` is a loop, so the thread binding is
  still in place when the last frame is popped — which is why abduction rides the DFS
  and not the lazy `backward`."
  [kb goals actx ops]
  (let [ends (volatile! [])
        sols (binding [res/*dead-end* (fn [g depth] (vswap! ends conj [g depth]))]
               (res/prove kb (:rules ops) goals actx))]
    {:solutions sols :dead-ends @ends}))

(defn- triage
  "Split `dead-ends` into what may be hypothesized and what may not — both distinct,
  both in **content order**, both with the already-minted removed.

  Content order because the cap decides which candidates survive, and a cap resolved by
  whatever order the DFS happened to reach them would make the answer depend on
  traversal — the same reason belief never tie-breaks on a handle (docs/nmtms.md).

  One pass, because the gate runs the full admissibility triple per candidate and the
  refusals are wanted for reporting: asking twice would double the checking.

  And **deduplicated ahead of the gate**, not only in `clean` behind it.  A search
  reports a dead end per *arrival*, so one subgoal a converging rule graph reaches a
  thousand times is a thousand entries, and the gate — `special/inadmissible` plus a
  `matches-visible` probe — would run once each to produce one candidate.  The gate is a
  function of the `[goal depth]` pair alone, so collapsing equal pairs first changes
  nothing but what it costs."
  [kb actx opts minted dead-ends]
  (let [{yes true no false}
        (group-by (fn [[g depth]] (some? (maybe-abduce kb g actx opts depth)))
                  (distinct dead-ends))
        ;; `nm/print-key`, not a bare `pr-str`: the keys are whole dead-end goal
        ;; sentences, so an ambient `*print-length*` elides two of them to one prefix and
        ;; the cap below falls back to `dead-ends`' own order — DFS arrival, the exact
        ;; dependence the paragraph above rules out
        clean (fn [pairs] (->> pairs (map first) (remove minted) distinct
                               (nm/sort-by-content-key nm/print-key compare)))]
    {:candidates (clean yes) :refused (clean no)}))

(defn- mint
  "Assert one hypothesis in the abduction context and answer its handle.

  Bare, not `mint!`: it is one `assert` of one sentence, retracted by the ordinary
  teardown `minimize!` and `discard!` run.

  `:default` — the arbitration invariant, and the only strength a hypothesis may carry.
  The provenance says what it is: a reader of the record must be able to tell an
  assumption from something a person asserted, and the goal it was assumed *for* is the
  other half of that (`vaelii.core/provenance`)."
  [kb sentence actx goal ops]
  ((:assert ops) kb sentence actx
                 {:strength   :default
                  :creator    ::hypothesis
                  :provenance {:abduced true :abduced-for goal}}))

(defn- minimize!
  "Drop the hypotheses the answer does not need, and answer the set that is left.

  `!`, because every round runs a real `:remove` edit: the retraction and its dependency
  sweep are what decide the question, so this destroys stored knowledge whatever it
  answers.

  Greedy and one at a time: retract a hypothesis, re-prove, and put it back only if the
  goal stopped following.  What that yields is an **irredundant** set — no single member
  can be removed — and not a *minimum* one; a smaller set reachable only by swapping two
  members out for a third is an ATMS question and deliberately not asked here.

  Content order again, so which of two mutually-redundant hypotheses survives is decided
  by the sentences and not by the order they were minted in.  A re-minted hypothesis gets
  a fresh handle, which adds no work: the whole context is scratch."
  [kb goals actx goal minted ops]
  (reduce
   (fn [kept sentence]
     ((:edit ops) kb {:remove [(get kept sentence)]})
     (if (seq (:solutions (attempt kb goals actx ops)))
       (dissoc kept sentence)
       (assoc kept sentence (mint kb sentence actx goal ops))))
   minted
   ;; `(keys minted)` is a map's key seq, so a collapsed key would drop the choice onto
   ;; hash order; `nm/print-key` cannot collapse, and the key is built once per
   ;; hypothesis rather than once per comparison
   (nm/sort-by-content-key nm/print-key compare (keys minted))))

(defn- reported-hypotheses
  "The hypothesis set as the caller sees it: sentence, context, handle.  `handle` is nil
  once the context has been discarded — after the teardown there is no such sentex, and a
  dangling integer would be worse than an honest nil (`vaelii.core/preview` says the same
  thing the same way)."
  [minted actx keep?]
  (mapv (fn [sentence] {:sentence sentence :context actx
                        :handle   (when keep? (get minted sentence))})
        (nm/sort-by-content-key nm/print-key compare (keys minted))))

(defn run
  "Prove `goals` in `context`, hypothesizing what the proof needs and cannot find.

  `ops` is the operation map — `{:rules-fn f :assert f :edit f}`, everything abduction needs from
  the layer above it and does not name (see \"the operation map\" above).  `goals` is the vector
  form the DFS takes.

  Answers

      {:solutions   [binding-map …]     under the hypotheses
       :hypotheses  [{:sentence :context :handle} …]
       :refused     [sentence …]        dead ends the gate would not assume
       :context     CxAbductionX
       :status      :complete | :capped}

  `:hypotheses` empty means the goal was proved outright — nothing was assumed, and the
  solutions are as good as `prove`'s.  Otherwise the solutions hold **given** those
  sentences, which is why the two travel together.

  The loop is: prove, gather dead ends, mint what the gate allows, prove again.  Each
  round mints at least one hypothesis or stops, and the minted set is capped, so there
  are at most `:max-hypotheses` rounds.  Minting is what makes progress possible — a
  hypothesis satisfies the antecedent that dead-ended, and the search reaches one rule
  further, exposing the next thing it lacks.

  `:refused` is reported only when nothing was proved, which is when a caller asks *why
  nothing*: a gate that narrows silently reads as \"there was nothing to find\", when the
  truth may be that a predicate was never granted.  `:status :capped` is the other half —
  candidates remained and there was no room for them.

  `opts` takes `default-opts`' caps plus **`:keep?`**.  Without it the context is torn
  down before returning, so an ignored call leaves the KB as it found it; with it the
  context stands and the caller owns it — inspect the hypotheses, watch one get defeated,
  commit one by asserting it somewhere that outlives the scratch — and discards it with
  `vaelii.core/abduce-discard!`.  Committing is deliberately the caller's: abduction
  proposes."
  [kb goals context opts ops]
  (let [opts  (merge default-opts opts)
        keep? (boolean (:keep? opts))
        cap   (:max-hypotheses opts)
        for-  (if (= 1 (count goals)) (first goals) (vec goals))
        actx  (open kb context ops)
        ;; the candidate chooser bound to this run's scratch context, added to the operation map so
        ;; every stage below takes `ops` alone and nothing threads a function beside it
        ops   (assoc ops :rules (fn [g] ((:rules-fn ops) kb g actx)))]
    (try
      (let [{:keys [minted status solutions refused]}
            ;; `capped?` rides the loop: a round that took only `room` of more candidates
            ;; dropped the rest, so even a later round that *finds* a solution did not
            ;; search exhaustively — the honest status is `:capped`, not `:complete`.
            (loop [minted {} capped? false]
              (let [{:keys [solutions dead-ends]} (attempt kb goals actx ops)]
                (if (seq solutions)
                  {:minted minted :status (if capped? :capped :complete)
                   :solutions solutions :refused []}
                  (let [{:keys [candidates refused]}
                        (triage kb actx opts (set (keys minted)) dead-ends)
                        room  (- cap (count minted))
                        fresh (take room candidates)]
                    (if (empty? fresh)
                      {:minted    minted :solutions [] :refused refused
                       :status    (if (or capped? (seq candidates)) :capped :complete)}
                      (recur (reduce (fn [m s] (assoc m s (mint kb s actx for- ops)))
                                     minted fresh)
                             (or capped? (> (count candidates) room))))))))
            ;; Worth the retract-and-retest only when there is something to drop: a lone
            ;; hypothesis that produced a solution was necessary by construction, since
            ;; the round before it minted found none.
            kept  (if (and (seq solutions) (> (count minted) 1))
                    (minimize! kb goals actx for- minted ops)
                    minted)
            ;; Minimization re-runs the proof, so the solutions handed over must be the
            ;; ones the surviving hypotheses actually license — not the ones a larger set
            ;; did.  Unchanged set, no re-proof.
            sols  (if (= (count kept) (count minted))
                    solutions
                    (:solutions (attempt kb goals actx ops)))
            result {:solutions  (vec sols)
                    :hypotheses (reported-hypotheses kept actx keep?)
                    :refused    refused
                    :context    actx
                    :status     status}]
        (when-not keep? (discard! kb actx ops))
        result)
      (catch Throwable t
        ;; Isolation is the contract, and an exception is when it is easiest to break:
        ;; tear the scratch context down before the throw leaves.
        (discard! kb actx ops)
        (throw t)))))
