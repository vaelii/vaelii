;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.handle-cache-test
  "The stored-handle cache (`observe/*handle-cache*`) and the justification-dedup
  comparison it sits beside (`jtms/has-justification?`) — the two costs a
  forward-chaining run pays once per *witness* rather than once per conclusion.

  The cache is a **positive** lookup memo: it answers `kb/find-sentex-handle` from a
  map instead of canonicalizing the sentence and walking the trie.  Everything that
  could make it wrong is a way for a cached handle to stop being the answer, so that
  is what these tests enumerate — an absence that later becomes a presence (never
  cached), a presence that is removed (invalidated at the removal choke point), and a
  spelling that resolves through a `symmetric` mirror rather than to itself (not
  cached, since a mirror is only true while a second declaration is).

  The engine-level gate is that engaging it changes nothing a run concludes: a join
  pyramid derives the same content, supported the same way, as it did when every
  lookup read the index."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- the cache is transparent -------------------------------------------

(tu/deftest-kb handle-cache-answers-what-the-index-answers
  (testing "every lookup a bound cache serves equals the one the index serves"
    (tu/with-terms [holds carries A B CxStory]
      (let [s1     (list holds A B)
            s2     (list carries B A)
            absent (list holds B A)
            probes [s1 s2 absent]]
        (v/assert kb s1 CxStory {:chain? false})
        (v/assert kb s2 CxStory {:chain? false})
        (let [uncached (mapv #(kb/find-sentex-handle kb % CxStory) probes)
              cached   (observe/with-handle-cache
                         ;; twice through, so the second pass reads what the first stored
                         (dorun (map #(kb/find-sentex-handle kb % CxStory) probes))
                         (mapv #(kb/find-sentex-handle kb % CxStory) probes))]
          (is (= uncached cached))
          (is (every? some? (take 2 cached)) "the two stored sentences resolve")
          (is (nil? (nth cached 2)) "and the absent one still resolves to nothing"))))))

(tu/deftest-kb handle-cache-never-caches-an-absence
  (testing "a sentence looked up before it exists is found once it does"
    (tu/with-terms [holds A B CxStory]
      (let [s (list holds A B)]
        (observe/with-handle-cache
          (is (nil? (kb/find-sentex-handle kb s CxStory)) "absent to begin with")
          (v/assert kb s CxStory {:chain? false})
          ;; the whole reason a miss is not cached: a firing stores its conclusion
          ;; microseconds after asking whether it was already there
          (is (some? (kb/find-sentex-handle kb s CxStory))
              "and present the moment it is stored, with the cache still bound"))))))

(tu/deftest-kb the-cache-is-scoped-to-one-kb
  ;; `with-handle-cache` deliberately reuses an outer run's map, and two KBs
  ;; declaring nothing symmetric once stamped the one shared empty set — a nested
  ;; run on a second KB (a chaining callback asserting elsewhere) read the first
  ;; KB's handles and justified against a handle in another store
  (tu/with-terms [holds A CxStory]
    (tu/with-cleared-kb [kb2 #(tu/isolated-fresh)]
      (let [s  (list holds A)
            h1 (v/assert kb s CxStory {:chain? false})]
        (observe/with-handle-cache
          (is (= h1 (kb/find-sentex-handle kb s CxStory)) "filled under the first KB")
          (is (nil? (kb/find-sentex-handle kb2 s CxStory))
              "the second KB, sharing the cache, does not read the first's handle"))))))

(tu/deftest-kb a-spelling-canonicalization-rewrites-is-never-cached
  ;; the removal choke point clears the **canonical** key, so an entry keyed on a
  ;; raw spelling canonicalization rewrites — a symmetric literal's unsorted
  ;; arguments — would outlive its sentex as a stale handle
  (tu/with-terms [touches A B CxStory]
    (v/assert kb (list 'symmetric touches) CxStory {:chain? false})
    (let [h (v/assert kb (list touches B A) CxStory {:chain? false})]
      (observe/with-handle-cache
        (is (= h (kb/find-sentex-handle kb (list touches A B) CxStory)))
        (is (= h (kb/find-sentex-handle kb (list touches B A) CxStory)))
        (v/retract! kb h)
        (is (nil? (kb/find-sentex-handle kb (list touches A B) CxStory))
            "neither spelling survives the retraction")
        (is (nil? (kb/find-sentex-handle kb (list touches B A) CxStory)))))))

(tu/deftest-kb handle-cache-is-invalidated-by-removal
  (testing "a retracted sentence stops resolving, cache bound or not"
    (tu/with-terms [holds A B CxStory]
      (let [s (list holds A B)
            h (v/assert kb s CxStory {:chain? false})]
        (observe/with-handle-cache
          (is (= h (kb/find-sentex-handle kb s CxStory)) "cached on the way in")
          (v/retract! kb h)
          (is (nil? (kb/find-sentex-handle kb s CxStory))
              "the removal choke point cleared the entry"))))))

(tu/deftest-kb a-symmetric-declaration-retires-the-cache
  (testing "a spelling cached before the declaration is not served after it"
    (tu/with-terms [nextTo A B CxStory]
      ;; `(nextTo B A)` canonicalizes to itself while nothing is symmetric, and to
      ;; `(nextTo A B)` once the declaration lands — the same raw sentence reaching a
      ;; different handle, which is exactly what the stamp exists to catch
      (v/assert kb (list nextTo B A) CxStory {:chain? false})
      (let [asked (list nextTo B A)]
        (observe/with-handle-cache
          (let [before (kb/find-sentex-handle kb asked CxStory)]
            (is (some? before) "cached under the pre-declaration canonicalization")
            (is (= before (observe/cached-handle (kb/canon-stamp kb) asked CxStory))
                "and served from the cache while that reading holds")
            (v/assert kb (list 'symmetric nextTo) CxStory)
            (is (nil? (observe/cached-handle (kb/canon-stamp kb) asked CxStory))
                "the new stamp retires every entry filled under the old one")))
        ;; and what the index now says is what a cached run says: the sentence stored
        ;; under the old canonicalization is no longer what this spelling asks for.
        ;; That answer is the engine's, not the cache's — the cache only must not
        ;; contradict it
        (is (= (kb/find-sentex-handle kb asked CxStory)
               (observe/with-handle-cache (kb/find-sentex-handle kb asked CxStory)))
            "cached and uncached agree after the declaration")))))

(deftest handle-cache-nests-without-shadowing
  (testing "an inner scope shares the outer map rather than starting an empty one"
    (let [stamp #{}]
      (observe/with-handle-cache
        (observe/cache-handle! stamp '(holds A B) 'CxStory 42)
        (observe/with-handle-cache
          (is (= 42 (observe/cached-handle stamp '(holds A B) 'CxStory)))
          (observe/cache-handle! stamp '(holds B C) 'CxStory 43))
        (is (= 43 (observe/cached-handle stamp '(holds B C) 'CxStory))
            "and what the inner scope learned outlives it")))))

(deftest handle-cache-empties-on-a-new-stamp
  (testing "a fill under a different stamp drops what the old one keyed"
    (let [s1 #{} s2 #{'nextTo}]
      (observe/with-handle-cache
        (observe/cache-handle! s1 '(holds A B) 'CxStory 42)
        (observe/cache-handle! s2 '(holds B C) 'CxStory 43)
        (is (nil? (observe/cached-handle s2 '(holds A B) 'CxStory))
            "the entry from the old stamp is gone, not merely unreadable")
        (is (nil? (observe/cached-handle s1 '(holds A B) 'CxStory))
            "and asking under the old stamp does not resurrect it")
        (is (= 43 (observe/cached-handle s2 '(holds B C) 'CxStory)))))))

(deftest handle-cache-off-by-default
  (testing "unbound, every operation is a no-op and every lookup a miss"
    (let [stamp #{}]
      (is (nil? (observe/cached-handle stamp '(holds A B) 'CxStory)))
      (is (= 7 (observe/cache-handle! stamp '(holds A B) 'CxStory 7))
          "cache-handle! returns the handle whether or not it stored it")
      (is (nil? (observe/forget-handle! '(holds A B) 'CxStory)))
      (is (nil? (observe/cached-handle stamp '(holds A B) 'CxStory))))))

;; ---- justification dedup ------------------------------------------------

(tu/deftest-kb justification-dedup-is-set-equality
  (testing "same members, whatever the order, repetition, or collection type"
    (let [tms (reasoning/tms kb)]
      (jtms/ensure-node tms 9911 0)
      (jtms/add-justification tms (jtms/->just 99011 'rule [11 22 33] 9911 {}))
      (is (jtms/has-justification? tms 'rule [11 22 33] 9911))
      (is (jtms/has-justification? tms 'rule [33 11 22] 9911) "order is not identity")
      (is (jtms/has-justification? tms 'rule [11 11 22 33] 9911)
          "nor is a repeated antecedent — the question is about the set")
      (is (jtms/has-justification? tms 'rule '(22 33 11) 9911) "a seq asks the same thing")
      (is (not (jtms/has-justification? tms 'rule [11 22] 9911)) "a subset is a different set")
      (is (not (jtms/has-justification? tms 'rule [11 22 33 44] 9911)) "so is a superset")
      (is (not (jtms/has-justification? tms 'rule [11 22 44] 9911)) "and so is a swap")
      (is (not (jtms/has-justification? tms 'other [11 22 33] 9911)) "the informant counts")
      (is (not (jtms/has-justification? tms 'rule [11 22 33] 9912)) "so does the conclusion"))))

;; ---- the engine-level gate ----------------------------------------------

(tu/deftest-kb chaining-a-join-pyramid-keeps-one-justification-per-witness
  (testing "the cache changes neither what is derived nor how it is supported"
    (tu/with-terms [linksTo leadsTo reaches nearBy spans X Y Z W CxStory]
      ;; two paths from X to Z (through Y and through W), so the `reaches` conclusion
      ;; is won by two witnesses and must carry two justifications; `spans` sits above
      ;; it, checking that a derived fact feeds the next rule exactly once per witness
      (doseq [f [(list linksTo X Y) (list leadsTo Y Z)
                 (list linksTo X W) (list leadsTo W Z)
                 (list nearBy Z Z)]]
        (v/assert kb f CxStory {:chain? false}))
      (v/assert-rule kb [(list linksTo '?a '?m) (list leadsTo '?m '?b)]
                     (list reaches '?a '?b) CxStory
                     {:direction :forward :chain? false})
      (v/assert-rule kb [(list reaches '?a '?m) (list nearBy '?m '?b)]
                     (list spans '?a '?b) CxStory
                     {:direction :forward :chain? false})
      (v/forward-chain kb)
      (let [h1 (kb/find-sentex-handle kb (list reaches X Z) CxStory)
            h2 (kb/find-sentex-handle kb (list spans X Z) CxStory)]
        (is (some? h1) "the two-witness conclusion is derived")
        (is (some? h2) "and carries the rule above it")
        (is (= 2 (count (jtms/supports (reasoning/tms kb) h1)))
            "one justification per distinct witness — the dedup rejects neither")
        (is (= 1 (count (jtms/supports (reasoning/tms kb) h2)))
            "and exactly one where there is one witness, however often it re-derives")
        (is (= 1 (count (v/sentexes-with-functor kb reaches)))
            "one sentex, not one per witness")))))
