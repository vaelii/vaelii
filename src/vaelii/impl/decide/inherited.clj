;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide.inherited
  "The inherited family's rows of the candidate index: the clashes the settle's detector
  found (`discovery/discover-inherited!`), each with its vantages, where each is placed.
  See docs/nmtms.md, \"The inherited-clash memo\"."
  (:require [vaelii.impl.caches :as caches]
            [vaelii.impl.journal :as journal]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- the inherited clashes --------------------------------------------------
;;
;; A stored claim against a known-true claim argument preservation reaches at its tuple or
;; at its converse's (`inherit/clashing-claim`, `inherit/converse-claim`), or a stored
;; membership against one of a separated type (`inherit/separated-claims`), is found by the
;; settle's detector (`discovery/discover-inherited!`) with the most general contexts that
;; read it whole, and placed there (`chain/place-inherited!`).  `:inherited` keeps what the
;; detector found, `{:by-set {members ngmap} :members #{h}}`, for the reports.

(defn- set-entry
  "The entry of member set `ms` over the nogood maps `es` found for it: its vantages the
  union of every map's, its `:sentence` and `:inherited` the least map's by content."
  [ms es]
  (let [e (if (next es)
            (nm/min-by-content-key (juxt #(nm/print-key (:sentence %))
                                         #(nm/print-key (:inherited %)))
                                   compare es)
            (first es))]
    {:nogood    ms
     :sentence  (:sentence e)
     :inherited (:inherited e)
     :vantages  (into #{} (mapcat :vantages) es)}))

(defn- install!
  "Hold `by-set` and `members` under `:inherited`, journaling the handles of `moved`, the
  members that entered or left."
  [kb by-set members moved]
  (swap! (reasoning/nogood-candidates kb)
         (fn [c]
           (let [c (journal/note c moved)]
             (if (seq by-set)
               (assoc c :inherited {:by-set by-set :members members})
               (dissoc c :inherited))))))

(defn install-inherited!
  "Keep the nogood maps `ngs`, every clash a discovery found, under `:inherited` in place
  of what it held: one entry per member set (`set-entry`).  Journals only the members that
  entered or left, so a clash found again moves no candidate.  Returns the member sets the
  index held before and does not hold now.  Writes nothing when `ngs` is empty and nothing
  is held."
  [kb ngs]
  (let [old (:inherited @(reasoning/nogood-candidates kb))]
    (if (and (empty? ngs) (nil? old))
      []
      (let [was     (:members old #{})
            by-set  (into {} (map (fn [[ms es]] [ms (set-entry ms es)])) (group-by :nogood ngs))
            members (into #{} cat (keys by-set))]
        (install! kb by-set members (-> #{} (into (remove was) members) (into (remove members) was)))
        (into [] (remove #(contains? by-set %)) (keys (:by-set old)))))))

(defn update-inherited!
  "Apply `changes`, `{members [ngmap]}` the clashes a discovery found for each member set
  it read again, to `:inherited`: a set with maps takes the entry `set-entry` builds, a
  set with none leaves.  Every other set is kept as held.  `sets-of` answers, for a
  handle, every member set holding it that a discovery can find, so a member of a set
  that left stays a member while another set holds it.  Journals only the members that
  entered or left.  Returns the member sets the index held before and does not hold now."
  [kb changes sets-of]
  (let [old     (:inherited @(reasoning/nogood-candidates kb))
        held    (:by-set old {})
        was     (:members old #{})
        by-set  (reduce-kv (fn [m ms es] (if (seq es) (assoc m ms (set-entry ms es)) (dissoc m ms)))
                           held changes)
        left    (into [] (filter #(and (contains? held %) (not (contains? by-set %)))) (keys changes))
        gained  (into #{} (comp (filter #(contains? by-set %)) cat (remove was)) (keys changes))
        lost    (into #{} (comp cat (filter was)
                                (remove (fn [h] (some #(contains? by-set %) (sets-of h)))))
                      left)]
    (install! kb by-set (reduce disj (into was gained) lost) (into gained lost))
    left))

(defn inherited-clashes
  "The inherited clashes, `{members {:nogood :sentence :inherited :vantages}}`."
  [kb]
  (:by-set (:inherited @(reasoning/nogood-candidates kb))))

(def family
  "The inherited family's entry in `decide/registry`.  Its rows are installed by the
  settle's detector, not noted at the store.  Each nogood of it is placed as a conclusion
  (`chain/place-inherited!`)."
  {:handles   (fn [_ c] (:members (:inherited c)))
   :holds?    (fn [_ c h] (contains? (:members (:inherited c)) h))})

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(caches/register-derived
 {:id :N7 :label "Inherited clashes" :kind :index :keyed-by :value :reads [:D3]
  :holds-content? false
  :retired-by {:inherited :W :recover :R :image-install :R}
  :computed :settle :imaged? :state :at [[:nogood-candidates :inherited]]
  :note "the inherited clashes and their vantages, installed again by every settle's detector"})
