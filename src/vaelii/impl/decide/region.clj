;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide.region
  "The network-region family's write hook: a `(contradicts …)` leaving the store queues its
  members, so the settle reads their networks again (`network-regions/place-moved!`).  A
  member's retraction removes the placement with no relabel of the other members.  See
  docs/qcn.md, \"An impossible network is a stored contradiction\"."
  (:require [vaelii.impl.caches :as caches]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.types.reasoning :as reasoning]))

(defn- note-placement-left!
  "Queue the members of the `(contradicts …)` sentex `sx` leaving the store."
  [kb sx]
  (let [s (:sentence sx)]
    (when (and (seq? s) (= 'contradicts (first s)))
      (swap! (reasoning/nogood-candidates kb) update ::left (fnil into #{})
             (keep sx/handle-id (rest s))))))

(defn take-left!
  "The members `note-placement-left!` queued since the last call, and the queue emptied."
  [kb]
  (let [[old _] (swap-vals! (reasoning/nogood-candidates kb) dissoc ::left)]
    (::left old #{})))

(def family
  "The network-region family's entry in `decide/registry`: it keeps no candidate rows, and
  its write hook queues the members of a placement that left (`note-placement-left!`)."
  {:note! (fn [kb _ sx stored?]
            (when-not stored? (note-placement-left! kb sx)))})

;; ---- derived state (docs/caches.md, "The derived-state register") ----------

(caches/register-derived
 {:id :Q12 :label "Region departures" :kind :queue :keyed-by :handle :reads [:records]
  :holds-content? false
  :retired-by {:settle-exit :Q :recover :W :cleared :W}
  :computed :write :imaged? false
  :at [[:nogood-candidates ::left]]
  :note "the members of a region `(contradicts …)` that left the store, which `take-left!` drains at the settle exit"})
