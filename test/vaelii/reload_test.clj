;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.reload-test
  "An engine edit reloaded under a loaded KB leaves the KB answering as it did.

  `vaelii.browser.reload/affected` names the namespaces the development browser reloads
  for an edit.  This test reloads that set for an edit to three engine namespaces in turn:
  `vaelii.impl.sentex`, which nearly every engine namespace requires;
  `vaelii.impl.protocols`, a held namespace, whose set is empty; and
  `vaelii.impl.dense-jtms`, the belief network's implementation, which defines the
  network's type with its methods inline.  After each reload it checks the KBs' stores and
  network are still instances of the classes the reloaded code names, compares belief with
  the belief before the first one, then asserts, queries, explains and retracts against
  KBs opened before the first reload, on `:memory` and `:disk-snapshot`.

  The reloads leave the engine reloaded for every test that runs after this one in the
  same JVM, which is the state the development browser runs in after an edit."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [vaelii.browser.reload :as reload]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.types.reasoning :as reasoning])
  (:import [java.io File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(def ^:private cx 'CxUniverse)

(defn- content!
  "A taxonomy edge, a default forward rule that fires through it, and a monotonic denial
  that defeats one of the rule's conclusions."
  [kb]
  (v/assert kb '(genl penguin bird) cx {:strength :monotonic})
  (v/assert kb '(set/defaultRule (set/forwardRule (implies (bird ?x) (flies ?x)))) cx)
  (v/assert kb '(bird Tweety) cx {:strength :monotonic})
  (v/assert kb '(penguin Pingu) cx {:strength :monotonic})
  (v/assert kb '(not (flies Pingu)) cx {:strength :monotonic}))

(defn- belief
  "Belief as content: `{[sentence context] in?}` over every stored sentex."
  [kb]
  (let [recs (:records kb) tms (reasoning/tms kb)]
    (into {} (keep (fn [id] (when-let [s (p/get-sentex recs id)]
                              [[(v/sentence-of s) (:context s)] (jtms/in? tms id)])))
          (p/sentex-ids recs))))

(defn- fliers [kb]
  (into #{} (map #(get % '?x)) (v/query kb '(flies ?x) cx)))

(defn- exercise!
  "Assert a premise the rule fires on, read the conclusion back through `query` and
  `why`, retract the premise, and check the KB's earlier content reads as it did."
  [kb]
  (let [before (belief kb)]
    (is (= '#{Tweety} (fliers kb)) "the defeated default stays defeated")
    (let [h (v/assert kb '(bird Robin) cx {:strength :monotonic})]
      (is (= '#{Tweety Robin} (fliers kb)) "a new premise fires the rule")
      (is (some? (v/why kb (v/handle-of kb '(flies Robin) cx)))
          "the conclusion has a justification to explain")
      (v/retract! kb h))
    (is (= '#{Tweety} (fliers kb)) "retracting the premise withdraws the conclusion")
    (is (= before (select-keys (belief kb) (keys before)))
        "the earlier content is believed as it was")))

(defn- classes
  "The classes of `kb`'s record store, index store and belief network."
  [kb]
  (mapv class [(:records kb) (:index kb) (reasoning/tms kb)]))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (io/file dir)))] (.delete ^File f)))

(deftest an-engine-reload-leaves-a-loaded-kb-answering
  (let [dir     (str (Files/createTempDirectory "vaelii-reload-" (into-array FileAttribute [])))
        kbs     {:memory        (v/open-kb {:backend :memory :space [::memory] :recover? false})
                 :disk-snapshot (v/open-kb {:backend :disk-snapshot :dir dir})}
        entries (reload/scan ["src"])]
    (try
      (doseq [kb (vals kbs)] (content! kb))
      (let [baseline (update-vals kbs belief)
            loaded   (update-vals kbs classes)]
        (doseq [edited '[vaelii.impl.sentex vaelii.impl.protocols vaelii.impl.dense-jtms]]
          (let [nss (reload/affected entries [edited])]
            (testing (str "an edit to " edited)
              (case edited
                vaelii.impl.protocols (is (empty? nss) "a held namespace reloads nothing")
                vaelii.impl.sentex    (is (< 50 (count (filter find-ns nss)))
                                          "nearly every loaded engine namespace requires sentex")
                (is (some #{edited} nss) "the edited namespace reloads"))
              (let [skipped (reload/reload! nss)]
                (when (= 'vaelii.impl.dense-jtms edited)
                  (is (contains? (get skipped edited) 'DenseTms)
                      "the network's deftype is left as loaded")))
              (doseq [[backend kb] kbs]
                (testing (str "on " backend)
                  (is (= (loaded backend) (classes kb)) "no class the KB holds is redefined")
                  (is (instance? (resolve 'vaelii.impl.dense_jtms.DenseTms) (reasoning/tms kb))
                      "the reloaded namespace still names the network's class")
                  (is (= (baseline backend) (belief kb)) "belief is unchanged by the reload")
                  (exercise! kb)))))))
      (finally
        (doseq [kb (vals kbs)] (v/close! kb))
        (rm-rf! dir)))))
