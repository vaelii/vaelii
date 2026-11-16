;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.call-cap
  "Per-KB counts of named expensive calls, each name with the most calls one KB may take.
  While `count!` counts, `counted` adds one to the KB's count for its name, unless a call
  under that name running on this thread has counted.  `entries` lists the counts.  A KB is
  keyed by object identity and held weakly.  With counting off, `counted` costs one atom
  read.  To guard a call, declare its name once as `(def name (call-cap/capped ::name n))`
  and wrap each call site as `(call-cap/counted name kb #(...))`.")

(defonce ^:private caps
  (atom {}))

(defonce ^:private counts
  (atom nil))

(def ^:private ^:dynamic *inside*
  "Each name a `counted`, `uncounted` or `scope` call is running under on this thread, to a
  volatile holding whether that call has counted."
  {})

(defn capped
  "Declare `name` with `cap`, the most `counted` calls under `name` one KB may take, and
  return `name`."
  [name cap]
  (swap! caps assoc name cap)
  name)

(defn count!
  "Count from zero, `tag` naming a KB's caller at its first counted call under a name, or
  stop counting with no argument."
  ([] (reset! counts nil) nil)
  ([tag] (reset! counts {:tag tag :entries {}}) nil))

(defn- add!
  "Add one to `kb`'s count under `name`."
  [name kb]
  (let [k    [name (System/identityHashCode kb)]
        mine #(identical? kb (.get ^java.lang.ref.WeakReference (:ref %)))]
    (swap! counts
           (fn [{:keys [tag] :as c}]
             (when c
               (update-in c [:entries k]
                          (fn [es]
                            (let [es (vec es)
                                  i  (first (keep-indexed #(when (mine %2) %1) es))]
                              (if i
                                (update-in es [i :count] inc)
                                (conj es {:ref (java.lang.ref.WeakReference. kb)
                                          :tag (tag kb) :count 1}))))))))))

(defn counted
  "Run `(f)` as one call under `name` on `kb`: while counting, add one to `kb`'s count for
  `name`, unless a call under `name` running on this thread has counted."
  [name kb f]
  (if (nil? @counts)
    (f)
    (if-let [done (get *inside* name)]
      (do (when-not @done
            (add! name kb)
            (vreset! done true))
          (f))
      (do (add! name kb)
          (binding [*inside* (assoc *inside* name (volatile! true))] (f))))))

(defn uncounted
  "Run `(f)` with no count under `name`, as part of a call counted where it began."
  [name f]
  (binding [*inside* (assoc *inside* name (volatile! true))] (f)))

(defn scope
  "Run `(f)` as at most one call under `name`: the first `counted` call under `name` that
  `f` runs counts, and the rest count nothing."
  [name f]
  (if (contains? *inside* name)
    (f)
    (binding [*inside* (assoc *inside* name (volatile! false))] (f))))

(defn entries
  "Each count as `{:name n :kb k :tag t :count c :cap m}`: `k` names the KB by its identity
  hash, `t` is the `count!` tag's value at its first call, and `m` is `n`'s cap."
  []
  (let [cs @caps]
    (into []
          (mapcat (fn [[[name h] es]]
                    (map #(-> % (dissoc :ref)
                              (assoc :name name :kb (format "KB@%08x" h) :cap (get cs name)))
                         es)))
          (:entries @counts))))
