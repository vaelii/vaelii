;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.backend-parity-test
  "Every storage backend must answer the **engine** identically, not merely satisfy the
  storage protocols.

  The existing oracles compare stores: `dense_kv_oracle_test`,
  `columnar_index_oracle_test` and `dense_roots_oracle_test` each drive one index
  implementation and its reference through the same op stream and compare every
  protocol read.  That proves the seam, but not that a *KB* built on one backend
  reasons like a KB built on another — the engine sits on top of matching, placement,
  chaining, belief and retraction, and a backend could satisfy the protocols while
  perturbing any of those.

  So this runs one scripted KB session — schema, facts, a forward rule, a query battery,
  a retraction — against every backend, and asserts the sessions are equal.  Results are
  compared as **sentences and contexts**, never as handles: a handle is an allocation
  order, and comparing them would either be trivially true or fail for a reason that is
  not a defect.

  It is deliberately a *default-suite* test.  Running the whole suite under
  `VAELII_TEST_BACKEND=…` is the thorough gate, but it is a thing someone has to
  remember; this one fails in an ordinary `lein test` the day a backend diverges."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.protocols :as p]
            [vaelii.test-util :as tu]))

;; Own db numbers, outside the suite's block, one pair per backend — so a parity KB
;; never shares a store with another test (or with its own siblings here).  The disk
;; arm names a **private temp directory** rather than letting one be derived from the
;; db numbers: a derived directory is a fixed global path, so a previous run that was
;; killed rather than closed leaves its single-writer lock behind and every later run
;; fails on it.
(defn- disk-dir []
  (str (java.nio.file.Files/createTempDirectory
        "vaelii-parity-" (into-array java.nio.file.attribute.FileAttribute []))))

(defn- backends []
  [{:backend :memory          :space 90}
   {:backend :memory-dense    :space 92}
   {:backend :memory-columnar :space 94}
   {:backend :disk            :dir (disk-dir)}
   ;; the mixed modes: durable records with the index derived in RAM.  Both halves are
   ;; the ones above, so what these arms actually prove is the *composition* — that a
   ;; record store and an index store chosen on separate axes still reason as one KB.
   {:backend :disk-memory     :dir (disk-dir)}
   {:backend :disk-dense      :dir (disk-dir)}
   {:backend :disk-columnar   :dir (disk-dir)}
   ;; the fork decorator over an EMPTY base (docs/overlay.md): every merge rule
   ;; degenerates, so the session must come out identical to the plain one it decorates.
   ;; The thorough gate is the whole suite under `VAELII_TEST_BACKEND=overlay`; this is
   ;; the one that fails in an ordinary `lein test`.
   {:backend :overlay
    :base    {:backend :memory :space 96}
    :overlay {:backend :memory :space 98}}])

(defn- sentences
  "The `[sentence context]` pairs behind a seq of handles — the handle-free view."
  [kb handles]
  (->> handles
       (keep #(p/get-sentex (:records kb) %))
       (map (juxt :sentence :context))
       set))

(defn- bindings-of [solutions]
  (set (map #(dissoc % :handle) (map #(if (map? %) % {}) solutions))))

(defn- session
  "One scripted KB session, returning a handle-free record of everything it observed.
  Every backend must produce an equal map."
  [kb]
  (v/assert kb '(genl dog animal) 'ParityContext {:strength :monotonic})
  (v/assert kb '(genl animal thing) 'ParityContext {:strength :monotonic})
  (v/assert kb '(argIsa ownerOf 2 animal) 'ParityContext {:strength :monotonic})
  (v/assert-rule kb '[(dog ?x)] '(mammal ?x) 'ParityContext)
  (v/assert kb '(dog Rex) 'ParityContext {:strength :monotonic})
  (v/assert kb '(dog Muffet) 'ParityContext {:strength :monotonic})
  (v/assert kb '(cat Tom) 'ParityContext {:strength :monotonic})
  (v/assert kb '(ownerOf Ann Rex) 'ParityContext {:strength :monotonic})
  (v/assert kb '(bornIn Rex 1970) 'ParityContext {:strength :monotonic})
  (v/assert kb '(not (dog Tom)) 'ParityContext {:strength :monotonic})
  (let [derived (v/handle-of kb '(mammal Rex) 'ParityContext)
        ix      (:index kb)
        result
        {;; matching and the type walk
         :query-dog      (set (map :sentence (v/sentexes-matching kb '(dog ?x) 'ParityContext)))
         ;; `query` is a level-2 literal match, so the genl spec walk is NOT its job —
         ;; `ask` and level 4 are where a supertype goal reaches a subtype fact
         :ask-animal     (bindings-of (v/ask kb '(animal ?x) 'ParityContext))
         :level4-animal  (set (map :sentence (v/lookup kb 4 '(animal ?x) 'ParityContext)))
         :query-arg      (set (map :sentence (v/sentexes-matching kb '(ownerOf ?who Rex) 'ParityContext)))
         :query-number   (set (map :sentence (v/sentexes-matching kb '(bornIn ?x 1970) 'ParityContext)))
         ;; ground: a negative pattern holding a variable matches nothing anywhere in
         ;; the stack, so it would compare empty-to-empty and prove nothing
         :query-negative (set (map :sentence (v/sentexes-matching kb '(not (dog Tom)) 'ParityContext)))
         ;; the prover stack
         :ask-mammal     (bindings-of (v/ask kb '(mammal ?x) 'ParityContext))
         :provable       [(v/provable? kb '(mammal Rex) 'ParityContext)
                          (v/provable? kb '(mammal Tom) 'ParityContext)]
         ;; the taxonomy
         :isa            [(v/isa? kb 'Rex 'animal 'ParityContext)
                          (v/isa? kb 'Rex 'thing 'ParityContext)
                          (v/isa? kb 'Tom 'animal 'ParityContext)]
         :genls          (v/genls kb 'dog)
         :specs          (v/specs kb 'animal)
         ;; the index reads the engine leans on
         :by-functor     (sentences kb (p/sentexes-with-functor ix 'dog))
         :count-functor  (p/count-with-functor ix 'dog)
         :by-arg         (sentences kb (p/sentexes-with-arg ix 2 'Rex))
         :by-args        (sentences kb (p/sentexes-with-args ix 'ownerOf [[1 'Ann] [2 'Rex]]))
         :in-context     (count (p/sentexes-in-context ix 'ParityContext))
         :by-term        (sentences kb (p/sentexes-with-term ix 'Rex))
         :find-sentexes  (sentences kb (v/find-sentexes kb 'Muffet))
         ;; the trie itself, through the protocol
         :lookup-0       (sentences kb (v/lookup kb 0 '(dog Rex) 'ParityContext))
         :count-at       (p/count-at ix '[dog])
         :children       (set (p/children ix '[dog]))
         ;; the lookup-to-query stack and belief
         :levels         (into {} (for [n (range 2 8)]
                                    [n (count (v/lookup kb n '(mammal Rex) 'ParityContext))]))
         :derived-believed (v/in? kb derived)
         :derived-why-rule (-> (v/why kb derived) :support first :rule)}]
    ;; retraction: the derived consequence must fall away with its premise, everywhere
    (v/retract! kb (v/handle-of kb '(dog Rex) 'ParityContext))
    (assoc result
           :after-retract-query (set (map :sentence (v/sentexes-matching kb '(dog ?x) 'ParityContext)))
           :after-retract-mammal (v/provable? kb '(mammal Rex) 'ParityContext)
           :after-retract-stored (some? (v/handle-of kb '(mammal Rex) 'ParityContext))
           :after-retract-isa   (v/isa? kb 'Rex 'animal 'ParityContext))))

(defn- run-session [opts]
  (let [kb (v/open-kb (assoc opts :recover? false))]
    (tu/clear-kb! kb)
    ;; The script's expectations are hand-written, and this namespace's question is
    ;; whether eight storage backends answer them alike — not what the engine derives.
    ;; Assertive argument types would change the script itself: `(argIsa ownerOf 2
    ;; animal)` and `(ownerOf Ann Rex)` both sit in ParityContext, so Rex would carry a
    ;; second, independent `animal` membership and retracting `(dog Rex)` would no
    ;; longer take his type with it.  That is the feature working, and it is tested
    ;; where it belongs (`vaelii.argtype-entail-test`); pinned off here so the parity
    ;; script means the same thing however the engine is configured.
    (try (binding [checks/*assertive-arg-types?* false] (session kb))
         (finally
           (tu/clear-kb! kb)
           ;; a disk arm holds a single-writer lock and file handles for the JVM's life
           ;; unless it is closed — so close and delete its directory rather than leaving
           ;; one behind per run
           ;; best-effort: the durability daemon may still hold a handle, in which case a
           ;; few KB survive in the OS temp directory — which is what it is for
           (when-let [dir (:dir opts)]
             ((requiring-resolve 'vaelii.impl.disk.backend/close-dir!) dir)
             (doseq [f (reverse (file-seq (java.io.File. ^String dir)))]
               (.delete ^java.io.File f)))))))

(deftest every-backend-reasons-alike
  (let [bs        (backends)
        reference (run-session (first bs))]
    ;; parity between backends that all did nothing is worthless, so pin the session
    ;; down first: it must have matched, subsumed, derived, believed, and retracted.
    (testing "the session is not vacuous"
      (is (= 2 (count (:query-dog reference))) "matched the stored dogs")
      (is (seq (:ask-animal reference)) "the genl spec walk reached dog from animal")
      (is (seq (:level4-animal reference)) "and level 4 is where it enters the stack")
      (is (seq (:query-negative reference)) "the negative fact is stored and matched")
      (is (seq (:ask-mammal reference)) "the forward rule derived something")
      (is (:derived-believed reference) "and the derived consequence is believed")
      (is (= '(implies (dog ?x) (mammal ?x)) (:derived-why-rule reference))
          "with a justification naming the rule that licensed it")
      (is (= [true false] (:provable reference)))
      (is (= [true true false] (:isa reference)))
      (is (pos? (:count-functor reference)))
      (is (not (:after-retract-mammal reference))
          "retracting the premise took the derived consequence with it")
      (is (not (:after-retract-isa reference))
          "and the type membership it rested on"))
    (doseq [opts (rest bs)]
      (testing (str "backend " (:backend opts))
        (let [got (run-session opts)]
          ;; compare key by key: a whole-map mismatch on 20 keys names none of them
          (doseq [k (sort (keys reference))]
            (is (= (get reference k) (get got k))
                (str (name (:backend opts)) " differs at " k))))))))
