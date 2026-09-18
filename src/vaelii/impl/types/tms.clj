;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.types.tms
  "The truth-maintenance types, as a held namespace (`vaelii.impl.types.prover` states what
  that means): the `Justification` record and the dense network's adjacency columns.

  The two `Tms` implementations, `RefTms` (`vaelii.impl.jtms`) and `DenseTms`
  (`vaelii.impl.dense-jtms`), are defined with their methods inline in those namespaces.
  `TmsColumns` is a `definterface`, so `HeapColumns` implements it inline, together with
  the three posting helpers it calls."
  (:require [vaelii.impl.types.postings :as postings])
  (:import [it.unimi.dsi.fastutil.ints Int2IntOpenHashMap Int2ObjectOpenHashMap]))

;; A justification's `strength` is the defeat-class it confers, capping the derived
;; datum's class (:monotonic for a bare rule, :default for a defeasible one).
;;
;; `informant` is a rule handle or a symbol (`:premise`, `rewriteOf`, a special
;; predicate's name).  A rule handle is an **implicit antecedent**: `valid?` needs the
;; rule believed, and the adjacency lists the justification under the rule's node, so
;; retracting or defeating a rule withdraws everything it licensed.  The record names the
;; rule once, in `informant`; `antecedents` never repeats it (`without-informant`), and
;; `rests-on` is the two together.
(defrecord Justification [id informant antecedents consequence bindings strength])

;; `TmsColumns` is every read and write the network makes of its six fact-scaled
;; structures.  Adjacency maps a datum to the justification ids touching it: `supports`
;; lists the ones concluding it, `dependents` the ones citing it as an antecedent or as
;; their rule.  The justification columns map an id to its consequence, its informant
;; when that is a handle, and its antecedents.
;;
;; Every read is total over an id the columns do not hold: no adjacency, depth 0,
;; consequence -1, the `no-informant` marker, and no antecedents.  An adjacency read
;; returns a fresh `int[]`, so a caller may walk it while writing the same posting.  A
;; posting emptied by a removal is dropped, so a torn-down node leaves no entry.
(definterface TmsColumns
  (^ints supportsOf [^int d])
  (^ints dependentsOf [^int d])
  (addSupport [^int d ^int jid])
  (addDependent [^int d ^int jid])
  (removeSupport [^int d ^int jid])
  (removeDependent [^int d ^int jid])
  (^int depthOf [^int d])
  (setDepth [^int d ^int depth])
  (dropNode [^int d])
  (^long consequenceOf [^int jid])
  (^int informantOf [^int jid])
  (^ints antecedentsOf [^int jid])
  (putJustification [^int jid ^int consequence ^int informant ^ints antecedents])
  (dropJustification [^int jid]))

(def ^:private ^ints no-ids (int-array 0))

(defn- posting-ints ^ints [^Int2ObjectOpenHashMap m d]
  (if-let [p (.get m (int d))] (postings/pints p) (int-array 0)))

(defn- posting-add! [^Int2ObjectOpenHashMap m d jid]
  (let [k (int d)
        p (or (.get m k) (let [fresh (postings/int-postings)] (.put m k fresh) fresh))]
    (postings/padd! p jid)
    nil))

(defn- posting-rem! [^Int2ObjectOpenHashMap m d jid]
  (when-let [p (.get m (int d))]
    (postings/prem! p jid)
    (when (zero? (long (postings/pcard p))) (.remove m (int d))))
  nil)

(deftype HeapColumns [^Int2IntOpenHashMap depths
                      ^Int2ObjectOpenHashMap supports
                      ^Int2ObjectOpenHashMap conseqs
                      ^Int2IntOpenHashMap j-conseq
                      ^Int2IntOpenHashMap j-inf
                      ^Int2ObjectOpenHashMap j-antes]
  TmsColumns
  (supportsOf [_ d] (posting-ints supports d))
  (dependentsOf [_ d] (posting-ints conseqs d))
  (addSupport [_ d jid] (posting-add! supports d jid))
  (addDependent [_ d jid] (posting-add! conseqs d jid))
  (removeSupport [_ d jid] (posting-rem! supports d jid))
  (removeDependent [_ d jid] (posting-rem! conseqs d jid))
  (depthOf [_ d] (.get depths d))
  (setDepth [_ d depth] (.put depths d depth) nil)
  (dropNode [_ d] (.remove depths d) (.remove supports d) (.remove conseqs d) nil)
  (consequenceOf [_ jid] (if (.containsKey j-conseq jid) (long (.get j-conseq jid)) -1))
  (informantOf [_ jid] (.get j-inf jid))
  (antecedentsOf [_ jid] (or (.get j-antes jid) no-ids))
  (putJustification [_ jid consequence informant antecedents]
    (.put j-conseq jid consequence)
    (.put j-inf jid informant)
    (.put j-antes jid antecedents)
    nil)
  (dropJustification [_ jid]
    (.remove j-conseq jid) (.remove j-inf jid) (.remove j-antes jid) nil))

;; The reference network: one atom holding the canonical state map.

;; The dense network's columns and bitmaps.  `vaelii.impl.dense-jtms` states what each holds.
