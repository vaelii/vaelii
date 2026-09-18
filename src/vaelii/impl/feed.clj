;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.feed
  "The change feed's registry and its accumulator — the leaf boundary a settle files its
  relabelled region into, and the one place a listener list lives.

  An application driving the KB otherwise learns that belief changed only by asking
  again, which misses whatever happened between two asks and costs the most on the KBs
  where the least is moving.  Everything a feed needs is already computed: a settle
  knows the **region** it relabelled and which of that region was believed when it
  first touched it (`jtms/touched` / `jtms/touched-in`), and it throws both away.  This
  namespace catches them.

  **Why here.**  `vaelii.impl.observe` is the precedent and the shape is the same: a
  choke point deep in the stack has to reach a consumer defined above it, so the
  indirection is a leaf both can see.  What differs is the altitude.  `observe`'s
  observers fire on *storage*, which is what an alpha memory mirrors; a feed is about
  **belief**, and belief is decided at settle time — an `assert` can store a sentex whose
  label several later justifications settle.  So nothing here is notified from
  `kb/create-sentex`, and the region is the unit rather than the record.

  **What is split where.**  The registry, the accumulator and the reentrancy guard are
  here, on the KB's `:feed` atom.  Turning a region into the `{:believed-added
  :believed-removed}` entries a listener receives is `vaelii.core`'s job — those are
  `preview`'s entry shapes, built from `why-not` and the supporting justifications, and
  they belong beside the code that already renders them.  `core` installs that renderer
  with `install-dispatch!` when it loads, and `deliver!` calls it.

  **What a KB with no listener pays.**  `note-region!` is one deref and a `seq` on the
  listener vector, and nothing accumulates.  A KB *with* one pays per relabelled region
  — the same region a `preview` diffs — and never per stored sentex; see
  `lein perf`'s `feed-listener-scaling`.  See docs/feed.md."
  (:require [taoensso.trove :as trove]))

(def ^:dynamic *enabled?*
  "Does a settle file its region into the feed at all?

  True everywhere except inside `core/preview`, which stores, settles, reads the diff
  and then takes every write back.  A preview that fed listeners would tell an
  application that belief changed and then that it changed back, which is worse than
  silence: the application learned nothing and has probably already acted.  Bound
  around the rollback too, since the rollback is the half that would send the
  retraction."
  true)

(def ^:dynamic *held?*
  "Is delivery deferred to an enclosing operation?

  Most mutations settle once, so the settle *is* the operation and its region is the
  whole story.  A teardown is the exception: `core/retract!` and `core/edit!` settle,
  re-derive what the removal released, and settle again — and a datum that goes OUT in
  the first pass and revives in the second moved no net belief at all.  Delivering per
  settle would report both halves of that flicker.  So those two hold the feed for
  their duration; the regions union, and one event is delivered with the batch's net
  answer, which is the same answer `core/edit-with-consequences!` gives for the same
  batch.

  Nests: an inner hold is a no-op wrapper (`remove-orphaned-nats!` retracts inside a
  retraction), and the outermost one delivers."
  false)

(def ^:private max-delivery-rounds
  "How many times a delivery loop re-drains before it gives up and says so.

  A listener may assert, and its assert settles and files a region of its own — which
  this loop then delivers, which may prompt another assert.  A listener that writes on
  every event it receives is an infinite loop, and it is the listener's bug; what this
  bound buys is that the loop reports it instead of hanging the writer.  The same shape
  as `settle/max-settle-passes` and the orphan sweep's guard, and the same value as the
  latter."
  64)

(defonce ^{:private true
           :doc "A `(fn [kb region was-in])` that renders the region and calls the listeners, or nil.
  Installed by `vaelii.core` at load; nil means nothing above this layer has claimed
  the registry, and `deliver!` is a single deref."}
  dispatch
  (atom nil))

(defn install-dispatch!
  "Register the renderer `deliver!` hands each region to — `vaelii.core`'s, once, when
  it loads.  Global rather than per-KB for `observe`'s reason: the function dispatches
  on the `kb` it is handed, so every live KB shares one installation and each keeps its
  own listeners."
  [f]
  (reset! dispatch f))

(def ^:private initial-state
  "A KB's feed state at construction: no listeners, nothing accumulated, nobody
  delivering.  `:next` is the token counter — monotone per KB, so a token is never
  reissued and `unwatch` on a stale one is a no-op rather than a mis-hit."
  {:listeners [] :next 0 :region #{} :was-in #{} :delivering? false})

(defn create-feed
  "The atom a KB's `:feed` slot holds."
  []
  (atom initial-state))

;; ---- the registry --------------------------------------------------------

(defn register!
  "Add `entry` — a map carrying at least `:f`, plus `:goal` / `:context` for a standing
  query — and return its token.  Appended, so the vector is registration order, which
  is the order `deliver!` calls in."
  [kb entry]
  (when-let [a (:feed kb)]
    ;; the token is read *inside* the swap, so two registrations cannot be handed the
    ;; same one — which would make one `unregister!` drop both listeners
    (let [[old] (swap-vals! a (fn [s] (-> s
                                          (update :next inc)
                                          (update :listeners conj
                                                  (assoc entry :token (:next s))))))]
      (:next old))))

(defn unregister!
  "Drop the listener `token` names; true if there was one.  Idempotent — a token
  already dropped, or one from another KB, removes nothing and says so."
  [kb token]
  (if-let [a (:feed kb)]
    ;; one `swap-vals!`, for `claim!`'s reason turned the other way round: the answer is
    ;; read off the CAS that did the removal, so exactly one of two concurrent unwatches of
    ;; one token can say it removed something.  Read-then-swap, both would see the listener
    ;; present, both would answer true, and a caller counting on the boolean to tell it
    ;; whether it was the one that closed the subscription would be told wrongly.
    (let [[old new] (swap-vals! a update :listeners
                                #(into [] (remove (fn [l] (= token (:token l)))) %))]
      (not= (count (:listeners old)) (count (:listeners new))))
    false))

(defn listeners
  "The registered listeners, in registration order."
  [kb]
  (if-let [a (:feed kb)] (:listeners @a) []))

(defn watched?
  "Is anything listening?  One deref and a `seq` — what a KB with no listener pays for
  the whole feature."
  [kb]
  (boolean (when-let [a (:feed kb)] (seq (:listeners @a)))))

(defn wants-region?
  "Would a region filed now reach anybody?  The gate `settle-finish` reads **before**
  assembling one, so a KB nobody is listening to never builds the two sets it would have
  had nowhere to put — see `note-region!`.  Whether the feed is on is the feed's own
  question, which is why both halves of it live here rather than at the call site."
  [kb]
  (and *enabled?* (watched? kb)))

;; ---- the accumulator -----------------------------------------------------

(defn note-region!
  "A settle relabelled `region`, of which `was-in` was believed when first touched.
  Union both into the accumulator, for the next delivery.

  Accumulates rather than queues, and that is what makes an event the *net* answer:
  two regions unioned and diffed once against belief-now reports what changed, where
  two separately-diffed regions would report a datum that went OUT and came back as a
  removal followed by an addition.  Union is also why order does not matter — the
  event's content is a function of the state the delivery reads, never of which settle
  filed which handle.

  Called behind `wants-region?`, which is what keeps the caller from *assembling* a region
  for a KB nobody is listening to — the re-check here is so this is safe to call anyway,
  not the gate that makes it free."
  [kb region was-in]
  (when (and (wants-region? kb) (seq region))
    (swap! (:feed kb) (fn [s] (-> s
                                  (update :region into region)
                                  (update :was-in into was-in))))))

(defn- claim!
  "Take what has accumulated and mark this caller as the one delivering it, or nil —
  nothing accumulated, or a frame further up is already delivering.

  The nil-when-delivering case is a listener that asserted: its assert settles, that
  settle's region lands in the accumulator, and its own `deliver!` declines the claim
  so the outer loop picks the region up in a later round.  Listeners therefore never
  nest, which is what makes a throwing or writing listener a bounded problem."
  [kb]
  (when-let [a (:feed kb)]
    ;; `swap-vals!`, not read-then-`swap!`: the test and the clear are one CAS, and the
    ;; old value it hands back is exactly what that CAS took.  Read separately, a
    ;; `note-region!` landing between the deref and the swap is cleared without ever
    ;; being delivered — a change notification lost rather than deferred.
    (let [[old] (swap-vals! a (fn [{:keys [delivering? region] :as s}]
                                (if (and (not delivering?) (seq region))
                                  (assoc s :region #{} :was-in #{} :delivering? true)
                                  s)))]
      (when (and (not (:delivering? old)) (seq (:region old)))
        {:region (:region old) :was-in (:was-in old)}))))

(defn- take-accumulated!
  "Take whatever accumulated since the last take — the delivery loop's later rounds,
  where the claim is already held.  Nil when nothing did, which is what ends the loop."
  [kb]
  ;; one CAS, for `claim!`'s reason
  (let [a (:feed kb)
        [old] (swap-vals! a (fn [s] (cond-> s (seq (:region s))
                                            (assoc :region #{} :was-in #{}))))]
    (when (seq (:region old))
      {:region (:region old) :was-in (:was-in old)})))

(defn- release! [kb] (swap! (:feed kb) assoc :delivering? false) nil)

(defn deliver!
  "Hand every accumulated region to the installed renderer, then let go of the claim.
  Called at the tail of every settle — after the relabel is finished, the caches are
  reconciled and the touched set is cleared, so a listener that writes starts a fresh
  settle rather than relabelling inside one.

  A no-op while `*enabled?*` is false, while `*held?*` (an enclosing teardown owns the
  delivery), when nothing above this layer installed a renderer, and when nothing
  accumulated — in that order, and the first three are var reads.  The fourth is not a
  read: `claim!` takes the accumulator with a `swap-vals!`, so a settle on a KB with a
  renderer installed and nothing to say still pays one CAS.  That is the price of taking
  the region and clearing it in one step, which is what stops a listener's own writes
  from being delivered twice.

  Re-drains until the accumulator is empty, so a listener's own writes are reported
  too, and gives up at `max-delivery-rounds` with a `:warn` rather than spinning."
  [kb]
  (when (and *enabled?* (not *held?*))
    (when-let [f @dispatch]
      (when-let [claimed (claim! kb)]
        (try
          (loop [{:keys [region was-in]} claimed, round 1]
            (f kb region was-in)
            (when-let [more (take-accumulated! kb)]
              (if (< round max-delivery-rounds)
                (recur more (inc round))
                (trove/log! {:level :warn :id ::delivery-fixpoint
                             :msg  (str "change feed did not quiesce in "
                                        max-delivery-rounds
                                        " rounds; a listener is writing on every event")
                             :data {:rounds round :pending (count (:region more))}}))))
          (finally (release! kb)))))))

(defmacro with-one-event
  "Run `body` with delivery deferred, then deliver once — the teardown's shape (see
  `*held?*`).  Returns `body`'s value.

  The delivery runs even when `body` **throws**, so a teardown that raised part-way still
  reports the belief it did move.  For `core/edit!` that is nothing: the entry point is
  all-or-nothing, and its rollback runs with `*enabled?*` off, so no region was ever filed
  and there is nothing left of the batch to report.

  **It is not a `finally`, and the difference is which exception the caller sees.**  A
  delivery that throws on the failure path — anything outside `notify-listener!`'s own
  guard, since a listener is already caught and logged there — would out of a `finally`
  replace the refusal `body` raised, and the refusal is the news: the caller asked to
  write and was told no.  So the failure path rethrows what `body` threw and hangs the
  delivery's failure off it as a suppressed exception, where a reader finds both."
  [kb & body]
  `(let [kb# ~kb]
     (try
       (let [v# (binding [*held?* true] ~@body)]
         (deliver! kb#)
         v#)
       (catch Throwable t#
         (try (deliver! kb#)
              (catch Throwable d# (.addSuppressed t# d#)))
         (throw t#)))))
