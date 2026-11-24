;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.abduce
  "Abduction: the scratch-context lifecycle, the check on what may be assumed, and the
  mint/re-prove loop over the dead ends `res/prove` reports.  See docs/abduction.md.

  Everything this namespace needs from `vaelii.core` arrives in one `ops` map —
  `{:rules-fn (fn [kb goal context]) :assert f :edit f}` — and nothing here names
  `vaelii.core`.  Handing them down works because `vaelii.core` is the sole caller of
  the entry points that write; a NAT mint, reached from inside the chaining fixpoint,
  goes through `vaelii.impl.wiring` instead."
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
  "The caps: `:max-hypotheses` bounds how much one call may assume, `:max-depth` the rule
  expansions past which a dead end is left alone."
  {:max-hypotheses 8
   :max-depth      8})

;; ---- the abduction context ----------------------------------------------

(defn new-token
  "A fresh context token.  Random rather than content-keyed: two abductions of one goal
  in one process must not share a scratch context, and the caller reads the context out
  of the result rather than predicting it."
  []
  (str/replace (subs (str (java.util.UUID/randomUUID)) 0 13) "-" ""))

(def ^:dynamic *token*
  "The token the abduction context is named by, or nil for a fresh one.  `vaelii.core`
  binds it to the token an operation-log frame records for an `abduce` call
  (`vaelii.impl.oplog`), so the recorded call names the context the call named."
  nil)

(defn context-for
  "The abduction context named by `token`: `CxAbduction<token>`, an ordinary context."
  [token]
  (symbol (str "CxAbduction" token)))

(def max-kept
  "How many `{:keep? true}` abduction contexts a KB holds at once.  The next keep is
  refused with `:too-many-kept` instead of discarding one: the caller holds each context
  and discards it, and a context discarded unasked would fail that caller's later read or
  `abduce-discard!` with no reason given."
  64)

(defn- kept-contexts
  "The abduction contexts standing in `kb`, in content order.  Between calls each one is
  a kept context, since a call without `:keep?` discards its own before returning."
  [kb]
  (into [] (filter #(str/starts-with? (name %) "CxAbduction"))
        (sort (tax/contexts (reasoning/taxonomy kb)))))

(defn- check-room!
  "Refuse a `{:keep? true}` call when `max-kept` kept contexts already stand, naming them
  under `:contexts` so the caller can discard one."
  [kb]
  (let [held (kept-contexts kb)]
    (when (>= (count held) max-kept)
      (throw (ex-info (str "this KB holds " (count held) " kept abduction contexts, its most"
                           " — abduce-discard! one of " (str/join ", " held) " first")
                      {:type :too-many-kept :max max-kept :contexts held})))))

(defn- open
  "Mint a fresh abduction context below `base` with one `:monotonic` `genlCx` edge, and
  answer it."
  [kb base ops]
  (let [actx (context-for (or *token* (new-token)))]
    ((:assert ops) kb (list 'genlCx actx base) 'CxUniverse {:strength :monotonic})
    actx))

(defn- edge-handles
  "The handles of every `genlCx` edge with `actx` at argument 1 — one from `open`, plus
  any a `{:keep? true}` caller hung on it.  Read off the argument root, so the teardown
  needs nothing but the context name, and all of them, so none is left standing."
  [kb actx]
  (->> (reads/as-stored-with-arg-global (:index kb) 1 actx)
       (keep #(p/get-sentex (:records kb) %))
       (filter #(= 'genlCx (nm/functor (:sentence %))))
       (mapv :id)))

(defn discard!
  "Discard the abduction context whole: every sentex in it, then the edges that made it a
  context.  Answers `{:removed-sentexes n :removed-justifications n}`; idempotent.

  The extent goes in one `edit`, so one settle and its sweep take the derived content
  with the hypotheses.  The edges are removed separately because they are not in the
  extent: `genlCx` is forced-decontextualized, so it is stored in CxUniverse."
  [kb actx ops]
  (let [drop! (fn [hs] (if (seq hs)
                         (:removed ((:edit ops) kb {:remove (vec hs)}))
                         {:removed-sentexes 0 :removed-justifications 0}))]
    (merge-with + (drop! (reads/as-stored-in-context (:index kb) actx))
                (drop! (edge-handles kb actx)))))

;; ---- the abducibility check -----------------------------------------------

(defn abducible?
  "May `sentence` be hypothesized in `context`?  True when it is a ground literal whose
  predicate `abducible_predicate` grants (read scoped from `context`), that `assert`
  would admit (`special/inadmissible`), and whose negation is not believed at
  `context`.  Cheapest test first; the reasons are docs/abduction.md, \"The abducibility check\"."
  [kb sentence context]
  (boolean
   (and (seq? sentence)
        (let [pred (nm/functor sentence)]
          (and (symbol? pred)
               (sx/ground-term? sentence)
               (tax/has-prop? (reasoning/taxonomy kb) :abducible pred context)
               (nil? (special/inadmissible kb sentence context))
               (empty? (res/matches-visible kb (list 'not sentence) context)))))))

;; ---- the search -----------------------------------------------------------

(defn- in-content-order
  "`sentences` sorted by content.  `nm/print-key`, not `pr-str`: an ambient
  `*print-length*` would elide two long sentences to one prefix and leave their order to
  DFS arrival or hash order."
  [sentences]
  (nm/sort-by-content-key nm/print-key compare sentences))

(defn- attempt
  "One `res/prove` of `goals` in `actx` with `res/*dead-end*` bound —
  `{:solutions :dead-ends}`, the dead ends as `[goal depth]` pairs."
  [kb goals actx ops]
  (let [ends (volatile! [])
        sols (binding [res/*dead-end* (fn [g depth] (vswap! ends conj [g depth]))]
               (res/prove kb (:rules ops) goals actx))]
    {:solutions sols :dead-ends @ends}))

(defn- triage
  "Split `dead-ends` into `:candidates` (within `:max-depth` and `abducible?`) and
  `:refused`, each distinct, in content order, with the already-`minted` removed.

  Equal `[goal depth]` pairs collapse before the abducibility check: a search reports a
  dead end per arrival, so a subgoal a converging rule graph reaches a thousand times
  would otherwise run the check a thousand times."
  [kb actx {:keys [max-depth]} minted dead-ends]
  (let [{yes true no false}
        (group-by (fn [[g depth]] (and (or (nil? max-depth) (<= depth max-depth))
                                       (abducible? kb g actx)))
                  (distinct dead-ends))
        clean (fn [pairs] (->> pairs (map first) (remove minted) distinct in-content-order))]
    {:candidates (clean yes) :refused (clean no)}))

(defn- mint
  "Assert one hypothesis in `actx` at `:default` with its provenance, and answer its
  handle."
  [kb sentence actx goal ops]
  ((:assert ops) kb sentence actx
                 {:strength   :default
                  :creator    ::hypothesis
                  :provenance {:abduced true :abduced-for goal}}))

(defn- minimize!
  "Drop the hypotheses the answer does not need, in content order, and answer the
  `{sentence handle}` map that is left: retract one, re-prove, and re-mint it only if the
  goal stopped following.  Irredundant, not minimum."
  [kb goals actx goal minted ops]
  (reduce
   (fn [kept sentence]
     ((:edit ops) kb {:remove [(get kept sentence)]})
     (if (seq (:solutions (attempt kb goals actx ops)))
       (dissoc kept sentence)
       (assoc kept sentence (mint kb sentence actx goal ops))))
   minted
   (in-content-order (keys minted))))

(defn run
  "The body of `vaelii.core/abduce`, which states the result.  `goals` is the vector the
  DFS takes, `opts` `default-opts`' caps plus `:keep?`, `ops` the map the ns docstring
  names."
  [kb goals context opts ops]
  (let [opts  (merge default-opts opts)
        keep? (boolean (:keep? opts))
        cap   (:max-hypotheses opts)
        for-  (if (= 1 (count goals)) (first goals) (vec goals))
        _     (when keep? (check-room! kb))
        actx  (open kb context ops)
        ops   (assoc ops :rules (fn [g] ((:rules-fn ops) kb g actx)))]
    (try
      (let [{:keys [minted status solutions refused]}
            ;; `capped?` carries across rounds: once a round dropped a candidate for want
            ;; of room, the search was not exhaustive, even if a later round proves the goal
            (loop [minted {} capped? false]
              (let [{:keys [solutions dead-ends]} (attempt kb goals actx ops)]
                (if (seq solutions)
                  {:minted minted :status (if capped? :capped :complete)
                   :solutions solutions :refused []}
                  (let [{:keys [candidates refused]}
                        (triage kb actx opts (set (keys minted)) dead-ends)
                        ;; a nil cap is no bound (`opts/check-values!`)
                        room  (when cap (- cap (count minted)))
                        fresh (if room (take room candidates) candidates)]
                    (if (empty? fresh)
                      {:minted    minted :solutions [] :refused refused
                       :status    (if (or capped? (seq candidates)) :capped :complete)}
                      (recur (reduce (fn [m s] (assoc m s (mint kb s actx for- ops)))
                                     minted fresh)
                             (or capped? (boolean (and room (> (count candidates) room))))))))))
            ;; a lone hypothesis that produced a solution is necessary: the round before
            ;; it proved nothing
            kept  (if (and (seq solutions) (> (count minted) 1))
                    (minimize! kb goals actx for- minted ops)
                    minted)
            ;; re-prove after minimizing, so the solutions are the survivors' own
            sols  (if (= (count kept) (count minted))
                    solutions
                    (:solutions (attempt kb goals actx ops)))
            result {:solutions  (vec sols)
                    :hypotheses (mapv (fn [s] {:sentence s :context actx
                                               :handle   (when keep? (get kept s))})
                                      (in-content-order (keys kept)))
                    :refused    refused
                    :context    actx
                    :status     status}]
        (when-not keep? (discard! kb actx ops))
        result)
      (catch Throwable t
        (discard! kb actx ops)
        (throw t)))))
