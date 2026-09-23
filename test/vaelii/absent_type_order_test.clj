;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.absent-type-order-test
  "Order independence where a derivation reads the **absence** of a type.

  An argument constraint convicts a sentence when the argument's types have no path to
  the declared one, and `mintable-type?` declines a mint whose type has no path to
  `thing`.  Both read the taxonomy as it stands, so each needs a way back for the order
  where the missing edge or membership arrives later: a dropped rule conclusion, a
  declined decontextualized copy and an unminted declaration are remembered and re-asked
  by `settle` (docs/exceptions.md, \"A refused firing is remembered as bindings\").  And a
  `forced_decontextualized_predicate` declaration moves the extent stored before it.

  Each test runs the same sentences in both orders on a fresh KB and compares what the
  KB holds, stored and believed.  `starter-in-any-order` is the same claim over the
  whole shipped ontology."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.host.seed :as seed]
            [vaelii.impl.io.text :as text]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.test-util :as tu]))

(defn- held
  "What `kb` stores, as a multiset of printed `[sentence context]` pairs with the rule
  handle an `exceptWhen` meta names blanked — the one place content carries a handle,
  and handles are allocated in arrival order."
  [kb]
  (frequencies
   (for [h (p/sentex-ids (:records kb))
         :let [sx (p/get-sentex (:records kb) h)]]
     [(str/replace (pr-str (:sentence sx)) #"\(sentexHandle \d+\)" "(sentexHandle _)")
      (str (:context sx))
      (v/in? kb h)])))

(defn- in-both-orders
  "Run `steps` (a map of step name to a fn of the KB) in `first-steps` then the rest, and
  in the reverse, each on a fresh KB after `setup`; return `[reading-a reading-b]`, each
  `(observe kb)`."
  [setup steps order-a observe]
  (for [order [order-a (reverse order-a)]]
    (tu/with-neutral-kb [kb tu/fresh]
      (setup kb)
      (doseq [s order] ((steps s) kb))
      (observe kb))))

(defn- a-type [kb t ctx] (v/assert kb (list 'genl t 'thing) ctx {:strength :monotonic}))

(defn- a-context [kb ctx super] (v/assert kb (list 'genlCx ctx super) 'CxUniverse {:strength :monotonic}))

(tu/deftest-kb a-forced-declaration-arriving-last-rehomes-what-was-stored-before-it
  ;; The declaration forces the storage context of every `(P …)` asserted after it; one
  ;; asserted before it stayed where it was written, so which context held the fact —
  ;; and the entailments a fact there draws — was the order.
  (tu/with-terms [linkedTo Alpha Beta CxWorld]
    (let [readings (in-both-orders
                    #(a-context % CxWorld 'CxUniverse)
                    {:decl #(v/assert % (list 'forced_decontextualized_predicate linkedTo) 'CxCore)
                     :fact #(v/assert % (list linkedTo Alpha Beta) CxWorld)}
                    [:decl :fact]
                    (fn [kb] {:universe (some? (v/handle-of kb (list linkedTo Alpha Beta) 'CxUniverse))
                              :world    (some? (v/handle-of kb (list linkedTo Alpha Beta) CxWorld))
                              :held     (held kb)}))]
      (is (apply = readings) "both orders hold the same sentexes")
      (is (:universe (first readings)) "the fact lives in CxUniverse")
      (is (not (:world (first readings))) "and not where it was written"))))

(tu/deftest-kb a-conclusion-convicted-by-a-missing-edge-is-placed-once-the-edge-arrives
  ;; `(arg ownsPet 2 animal)` is written in CxTheory, above the rule's context, so there
  ;; it constrains without entailing.  Rex is a `poodleKind`, and until the edge
  ;; `(genl poodleKind animal)` arrives nothing reaches `animal` from there: the firing
  ;; is dropped.  Arriving first, the same edge lets it through — so a KB that drops it
  ;; for good believes less in one order than the other.
  (tu/with-terms [animal poodleKind petOf ownsPet Rex Ann CxTheory CxWorld]
    (let [readings (in-both-orders
                    (fn [kb]
                      (a-context kb CxTheory 'CxUniverse)
                      (a-context kb CxWorld CxTheory)
                      (a-type kb animal CxTheory)
                      (a-type kb poodleKind CxTheory)
                      (v/assert kb (list 'arg ownsPet 2 animal) CxTheory)
                      (v/assert kb (list 'set/forwardRule
                                         (list 'implies (list petOf '?x '?y) (list ownsPet '?y '?x)))
                                CxWorld))
                    {:edge #(v/assert % (list 'genl poodleKind animal) CxTheory)
                     :fact #(do (v/assert % (list poodleKind Rex) CxWorld)
                                (v/assert % (list petOf Rex Ann) CxWorld))}
                    [:edge :fact]
                    (fn [kb] {:owns (boolean (v/ask? kb (list ownsPet Ann Rex) CxWorld))
                              :held (held kb)}))]
      (is (:owns (first readings)) "the edge first: the conclusion is placed")
      (is (apply = readings) "and the edge last reaches the same KB"))))

(tu/deftest-kb a-declaration-whose-type-becomes-a-type-later-mints-then
  ;; `mintable-type?` asks whether the declared type reaches `thing`.  The declaration and
  ;; the fact arriving before that edge minted nothing, and nothing asked again.  Pinned to
  ;; the entailing reading, since the mint is what it asks about.
  (tu/with-entailing
    (doseq [kind ['arg 'genlArg]]
      (testing (str kind)
        (tu/with-terms [gadgetKind usesTool Ann Widget widgetKind CxWorld]
          (let [arg?     (= 'arg kind)
                ;; `genlArg` types a position that names a kind, so its argument is a type
                used     (if arg? Widget widgetKind)
                decl     (list kind usesTool 2 gadgetKind)
                minted   (if arg? (list gadgetKind Widget) (list 'genl widgetKind gadgetKind))
                readings (in-both-orders
                          #(a-context % CxWorld 'CxUniverse)
                          {:type #(a-type % gadgetKind CxWorld)
                           :rest #(do (v/assert % decl CxWorld)
                                      (v/assert % (list usesTool Ann used) CxWorld))}
                          [:type :rest]
                          (fn [kb] {:minted (some? (v/handle-of kb minted CxWorld))
                                    :held   (held kb)}))]
            (is (:minted (first readings)) "the type first: the declaration mints")
            (is (apply = readings) "and the type last reaches the same KB")))))))

;; ---- the whole shipped ontology -----------------------------------------------

(defn- starter-entries
  "Every sentence the starter loads, as `[sentence context]`, in the shipped loader's
  order: the vocabulary head's bootstrap pair, CxCore, the upper and middle members, the
  collectors."
  []
  (concat [['(forced_decontextualized_predicate genlCx) 'CxCore]
           ['(genlCx CxUniverse CxCore) 'CxCore]]
          (map #(vector % 'CxCore) (seed/read-sentences 'CxCore))
          (for [c (seed/layer-contexts "upper")  s (seed/read-sentences c "upper")]  [s c])
          (for [c (seed/layer-contexts "middle") s (seed/read-sentences c "middle")] [s c])
          (for [c (seed/root-contexts)           s (seed/read-sentences c nil)]      [s c])))

(defn- load-shuffled!
  "The starter's sentences in the order `seed` shuffles them to, through the text
  loader, then the starter's closing `unary_predicate` batch."
  [kb seed]
  (let [l (java.util.ArrayList. ^java.util.Collection (vec (starter-entries)))]
    (java.util.Collections/shuffle l (java.util.Random. (long seed)))
    (v/with-deferred-settle kb
      (text/load-entries! (fn [s c o] (v/assert kb s c (or o {}))) (vec l)))
    (v/with-deferred-settle kb
      (doseq [t (nm/by-print-key (v/specs kb 'thing))]
        (v/assert kb (list 'unary_predicate t) 'CxCore)))
    kb))

(defn- held-after
  "`(held kb)` after `load!` on a cleared KB of its own, cleared again after."
  [load!]
  (let [kb (tu/isolated-fresh)]
    (try (held (load! kb)) (finally (tu/clear-kb! kb)))))

(defn- starter-in-orders
  "Each shuffled order in `seeds` against the shipped one.  The shipped reading is the
  restored starter dump — `starter/load-into`'s KB, which `starter_copy_test` pins — so
  a run pays for the shuffled loads alone."
  [seeds]
  (let [shipped (held-after tu/load-starter!)]
    (doseq [s seeds]
      (let [shuffled (held-after #(load-shuffled! % s))]
        (is (= shipped shuffled)
            (str "seed " s ": held only by the shipped order "
                 (pr-str (take 5 (remove (set (keys shuffled)) (keys shipped))))
                 ", only by the shuffled one "
                 (pr-str (take 5 (remove (set (keys shipped)) (keys shuffled))))))))))

(deftest starter-in-any-order
  ;; one shuffled order at :default; `starter-in-many-orders` runs twenty
  (starter-in-orders [7]))

(deftest ^:slow starter-in-many-orders
  (starter-in-orders (range 100 120)))
