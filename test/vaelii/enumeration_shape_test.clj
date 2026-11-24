;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.enumeration-shape-test
  "What a `RecordStore` may answer its three enumerations with, and what a caller may do
  with the answer.

  The protocol says **a `java.util.Set` of handles**, not an `IPersistentSet` — so a store
  whose handle list is a table's worth of them can answer a compressed one
  (`vaelii.impl.handle-set`) instead of a `PersistentHashSet<Long>` at 48–75 bytes a handle.
  That licence is only worth having if the engine cannot tell, and this is where core
  proves it can't: the same content, the same session, against a store that answers
  handle sets and one that answers Clojure sets, compared at the *KB* level — beliefs,
  answers and the whole recovery path — rather than at the protocol call.

  Beside it, `Tallying`: the count-and-emptiness questions the engine asks an enumeration
  without needing the enumeration.  The helpers must read the same number whether the
  store implements the capability or not, because that equality is what lets `open-kb`
  call them unconditionally."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.handle-set :as hs]
            [vaelii.impl.protocols :as p]))

;; ---- a store that answers handle sets ---------------------------------------

(defn- handle-set-store
  "`inner`, with the three enumerations answering `vaelii.impl.handle-set`'s compressed set.
  A reify rather than a redef, for `prefetch_test`'s reason: a protocol method dispatches
  on the value's type, so only a real implementation is in a compiled caller's path.

  It deliberately does **not** implement `Tallying` — the fallback in the helpers is the
  path an out-of-tree store takes on day one, and it has to be the one under test here."
  [inner]
  (reify
    p/RecordStore
    (put-sentex [_ sx] (p/put-sentex inner sx))
    (get-sentex [_ id] (p/get-sentex inner id))
    (delete-sentex! [_ id] (p/delete-sentex! inner id))
    (put-justification [_ d] (p/put-justification inner d))
    (get-justification [_ id] (p/get-justification inner id))
    (delete-justification! [_ id] (p/delete-justification! inner id))
    (next-id [_] (p/next-id inner))
    (put-provenance [_ id prov] (p/put-provenance inner id prov))
    (get-provenance [_ id] (p/get-provenance inner id))
    (delete-provenance! [_ id] (p/delete-provenance! inner id))
    (sentex-ids [_] (hs/handle-set (p/sentex-ids inner)))
    (justification-ids [_] (hs/handle-set (p/justification-ids inner)))
    (mark-premise [_ id s] (p/mark-premise inner id s))
    (unmark-premise! [_ id] (p/unmark-premise! inner id))
    (premise-ids [_] (hs/handle-set (p/premise-ids inner)))
    (premise-strength [_ id] (p/premise-strength inner id))
    (clear-records! [_] (p/clear-records! inner))))

;; ---- the content, and what is observed of it ----------------------------

(defn- load!
  "Facts, a rule that derives from them, a defeasible pair and a retraction — so the KB
  under comparison holds premises, derivations, justifications and a handle whose record
  is gone, which is every kind of thing the recovery walks meet."
  [kb]
  (v/assert kb '(isa Muffet DomesticCat) 'CxTest {:strength :monotonic})
  (v/assert kb '(isa Tom DomesticCat) 'CxTest {:strength :monotonic})
  (v/assert kb '(genls DomesticCat Cat) 'CxTest {:strength :monotonic})
  (v/assert-rule kb ['(isa ?x DomesticCat)] '(likes ?x Milk) 'CxTest {:direction :forward})
  (v/assert kb '(isa Rex Dog) 'CxTest)
  (let [h (v/assert kb '(isa Spot Dog) 'CxTest)]
    (v/retract! kb h))
  kb)

(defn- observation
  "Everything about this KB a caller could read that the handle-set shape could change."
  [kb]
  (let [hs (v/handles kb)]
    {:count     (count hs)
     :handles   (set hs)
     :sorted    (vec (sort hs))
     :believed  (into (sorted-set) (filter #(v/believed? kb %)) hs)
     :milk      (set (v/ask kb '(likes ?x Milk) 'CxTest))
     :cats      (set (v/ask kb '(isa ?x Cat) 'CxTest))
     :every-in? (every? #(contains? hs %) hs)}))

(defn- fresh [] (v/open-kb {:backend :memory :space (gensym "enumshape")}))

;; ---- the engine cannot tell ---------------------------------------------

(deftest a-handle-set-store-answers-the-same-kb
  (let [plain  (load! (fresh))
        compressed (let [kb (load! (fresh))]
                     (assoc kb :records (handle-set-store (:records kb))))]
    (is (= (observation plain) (observation compressed))
        "same handles, same belief, same answers")
    (is (not (set? (v/handles compressed)))
        "and it really was answering a java.util.Set rather than a Clojure one — a test
         that compared two PersistentHashSets would pass without testing anything")))

(deftest the-recovery-path-reads-a-handle-set
  ;; `reindex` walks `sentex-ids` and `recover` walks all three — the premise loop tests
  ;; membership in the sentex handle set, and the justification loop tests it again per
  ;; antecedent.  This is the walk the shape exists for, so it is the one under test.
  (let [plain    (load! (fresh))
        compressed (let [kb (load! (fresh))]
                     (assoc kb :records (handle-set-store (:records kb))))
        before   (observation compressed)
        counts   (v/reindex compressed)]
    (is (= (observation plain) (observation compressed))
        "a rebuild off a handle set lands the same beliefs the plain store lands")
    (is (= before (observation compressed))
        "and the same ones it already held — a reindex is a repair, not a change")
    (is (pos? (long (:sentexes counts))) "the walk saw the records")))

(deftest an-export-reads-a-handle-set
  ;; `export!` sorts both enumerations, which is the one caller that needs an *ordering*
  ;; off them rather than membership.
  (let [dir (str (java.nio.file.Files/createTempDirectory
                  "vaelii-enumshape-" (into-array java.nio.file.attribute.FileAttribute []))
                 "/dump")
        kb  (let [kb (load! (fresh))]
              (assoc kb :records (handle-set-store (:records kb))))
        out (v/export! kb dir {})]
    (is (= (count (v/handles kb)) (:sentexes out))
        "every record was written, and the sort read the handle set in handle order")
    (doseq [f (reverse (file-seq (java.io.File. dir)))] (.delete ^java.io.File f))))

;; ---- the tallies read the same number either way ------------------------

(deftest the-tally-helpers-agree-with-the-enumeration
  (let [kb       (load! (fresh))
        inner    (:records kb)
        compressed (handle-set-store inner)]
    (testing "the reference backend implements the capability"
      (is (satisfies? p/Tallying inner))
      (is (not (satisfies? p/Tallying compressed))
          "and the wrapper does not, so the fallback is what is measured against it"))
    (testing "same counts"
      (is (= (count (p/sentex-ids inner)) (cap/count-sentexes inner) (cap/count-sentexes compressed)))
      (is (= (count (p/justification-ids inner))
             (cap/count-justifications inner) (cap/count-justifications compressed))))
    (testing "same emptiness"
      (doseq [[label f enum] [["sentex" cap/some-sentex-id p/sentex-ids]
                              ["justification" cap/some-justification-id p/justification-ids]
                              ["premise" cap/some-premise-id p/premise-ids]]]
        (is (contains? (set (enum inner)) (f inner))
            (str "the " label " handle the capability answers is one the store holds"))
        (is (contains? (set (enum inner)) (f compressed))
            (str "and so is the one the fallback answers"))))))

(deftest an-empty-store-tallies-empty
  (let [kb       (fresh)
        inner    (:records kb)
        compressed (handle-set-store inner)]
    (v/clear! kb)
    (is (= 0 (cap/count-sentexes inner) (cap/count-sentexes compressed)))
    (is (= 0 (cap/count-justifications inner) (cap/count-justifications compressed)))
    (doseq [f [cap/some-sentex-id cap/some-justification-id cap/some-premise-id]]
      (is (nil? (f inner)) "the capability answers nil over an empty store")
      (is (nil? (f compressed)) "and so does the fallback"))))
