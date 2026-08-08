;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.handle-test
  "A handle is an identity, and no store may ever issue one twice.

  Ordinarily nothing can: every handle comes from `p/next-id`, which only counts up.
  But `put-sentex` / `put-justification` also honour an `:id` on the record they are
  given — that is how an import lands records at the handles a dump gave them — and a
  handle that arrives *that* way still has to be one the counter will never hand out
  again.  Otherwise the very next `assert` overwrites an imported record: no error, no
  warning, one record gone and another wearing its handle.

  So this is a claim about the **protocol**, not about one implementation, and every
  test here runs against both real backends.  The two must not differ on whether a
  write can lose data.

  Its KBs are private (own db numbers, own temp directory) rather than the suite's
  scratch space, because the subject is a store's id counter — a shared store would
  carry another namespace's handles into the arithmetic."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.disk.backend :as backend]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.test-util :as tu])
  (:import (java.io File)
           (java.nio.file Files)
           (java.nio.file.attribute FileAttribute)))

(defn- temp-dir ^File []
  (.toFile (Files/createTempDirectory "vaelii-handle-" (into-array FileAttribute []))))

(defn- rm-rf! [^File d] (doseq [^File f (reverse (file-seq d))] (.delete f)))

(defn- with-each-backend
  "Run `f` over an empty KB on each backend in turn.  Db numbers outside the suite's
  block, and a private temp directory for `:disk` — a directory derived from a db
  number is a fixed global path, and a run that was killed rather than closed leaves
  its single-writer lock behind on it."
  [f]
  (doseq [opts [{:backend :memory :space 96}
                {:backend :disk}]]
    (testing (str (:backend opts))
      (let [dir (when (= :disk (:backend opts)) (temp-dir))
            kb  (v/open-kb (cond-> (assoc opts :recover? false)
                             dir (assoc :dir (.getPath dir))))]
        (try
          (tu/clear-kb! kb)
          (f kb)
          (finally
            (when dir (backend/close-dir! (.getPath dir)) (rm-rf! dir))))))))

;;; ── the counter ───────────────────────────────────────────────────────

(deftest the-counter-clears-every-handle-the-store-holds
  ;; The narrow claim, at the protocol: whatever handles are in the store and however
  ;; they got there, the next one allocated is not one of them.
  (with-each-backend
    (fn [kb]
      (let [records (:records kb)]
        (doseq [n [1 2 3]]
          (p/put-sentex records (assoc (res/kb-sentex kb (list 'dog (symbol (str "Muffet" n)))
                                                      'HandleContext)
                                       :id n)))
        (p/put-justification records (jtms/->just 9 :import #{1 2} 3 {} :default))
        (is (< 9 (p/next-id records))
            "next-id stayed behind a handle the store already holds")))))

(deftest an-imported-record-survives-the-next-assert
  ;; The same bug as a caller sees it: land records at 1…N the way an import does, then
  ;; use the KB.  A counter that had not moved would mint 1 again and `put-sentex` would
  ;; overwrite the first record silently.
  (with-each-backend
    (fn [kb]
      (let [records (:records kb)
            stored  (doall (for [n [1 2 3]]
                             (let [rec (res/kb-sentex kb (list 'dog (symbol (str "Muffet" n)))
                                                      'HandleContext)]
                               (p/put-sentex records (assoc rec :id n))
                               [n (:sentence rec)])))
            h       (v/assert kb '(cat Tom) 'HandleContext)]
        (is (< 3 h) "the assert was handed a handle that was already taken")
        (doseq [[n sentence] stored]
          (is (= sentence (:sentence (v/sentex kb n)))
              (str "the record at handle " n " is not the one that was stored there")))))))

(deftest a-handle-the-store-never-issued-reads-as-nil
  ;; The other half of "a handle is an identity": asking for one that was never handed
  ;; out is a miss, not an error, and it is the same miss on either backend.  A negative
  ;; id is the sharp case — on disk it is a slot number, and so a file position.
  (with-each-backend
    (fn [kb]
      (let [records (:records kb)]
        (p/put-sentex records (assoc (res/kb-sentex kb '(dog Muffet) 'HandleContext) :id 1))
        (doseq [id [-1 0 999999]]
          (is (nil? (p/get-sentex records id)) (str "sentex " id))
          (is (nil? (p/get-justification records id)) (str "justification " id)))
        (is (nil? (p/get-sentex records :chain)) "an informant keyword is not a handle")))))

(deftest a-justification-handle-is-not-reissued-either
  ;; Sentexes and justifications are numbered from **one** counter, so a justification
  ;; landed at an explicit handle has to move it too — or the next derived justification
  ;; overwrites an imported one, and the belief that rested on it silently changes.
  (with-each-backend
    (fn [kb]
      (let [records (:records kb)]
        (p/put-justification records (jtms/->just 4 :import #{1} 2 {} :monotonic))
        (let [h (p/next-id records)]
          (is (< 4 h))
          (p/put-justification records (jtms/->just h :chain #{5} 6 {} :default))
          (is (= :import (:informant (p/get-justification records 4)))
              "the imported justification was overwritten"))))))

;; ---- what a handle-taking fn accepts -------------------------------------
;;
;; Three cases, and the middle one is the whole reason this exists. `assert` returns a
;; VECTOR of handles for a rule with a conjunctive consequent — one rule per conjunct —
;; so `(retract! kb (assert kb rule ctx))` is a composition of the API's own two calls
;; that hands a vector where one handle is expected. Unrefused it resolves to no record
;; and answers `{:removed-sentexes 0}` / `false` / nil: a silent no-op indistinguishable
;; from "there was nothing to do".
;;
;; `nil` is deliberately NOT that mistake. `handle-of` answers nil for a sentence the KB
;; does not hold, so `(in? kb (handle-of kb s ctx))` is ordinary and its honest answer is
;; `false`. Both halves are pinned because tightening the first without exempting the
;; second is the easy over-correction.

(deftest nil-is-a-question-with-an-answer-not-a-bad-handle
  (let [kb (tu/fresh)]
    (testing "every handle-taking read answers rather than throwing"
      (is (false? (v/in? kb nil)))
      (is (false? (v/premise? kb nil)))
      (is (nil? (v/provenance kb nil)))
      (is (false? (:stored? (v/why kb nil))))
      (is (nil? (v/sentex kb nil)))
      (is (nil? (v/justification kb nil)))
      (is (nil? (v/defeat-class kb nil)))
      (is (empty? (v/supporting-justifications kb nil)))
      (is (empty? (v/dependent-justifications kb nil)))
      (is (= :not-stored (:reason (v/why-not kb nil))))
      (is (= {:removed-sentexes 0 :removed-justifications 0} (v/retract! kb nil))))
    (testing "a nil-keyed write is a no-op, not a stored orphan"
      (is (nil? (v/add-provenance kb nil {:source :test}))
          "there is no record to attach to, so nothing is recorded")
      (is (nil? (v/provenance kb nil))
          "and the read agrees — the nil write left nothing to find"))
    (testing "edit and check-edit both treat a nil :remove as nothing to remove"
      (is (= {:removed-sentexes 0 :removed-justifications 0}
             (:removed (v/edit! kb {:remove [nil]}))))
      (is (= [] (v/check-edit kb {:remove [nil]}))))
    (testing "which is what makes this composition work"
      (tu/with-terms [dog Missing]
        (is (false? (v/in? kb (v/handle-of kb (list dog Missing) 'UniverseContext)))
            "handle-of found nothing, so nothing is believed")))))

(deftest a-vector-of-handles-is-refused-rather-than-silently-ignored
  (let [kb (tu/fresh)]
    (tu/with-terms [pOf aOf rOf]
      (let [hs (v/assert-rule kb [(list pOf '?x '?y)]
                              (list 'and (list aOf '?x '?y) (list rOf '?x '?y))
                              'UniverseContext)]
        (is (sequential? hs) "a conjunctive consequent is stored as one rule per conjunct")
        (is (= 2 (count hs)))
        (testing "each handle-taking fn names what it got"
          (doseq [[nm f] [["retract!"       #(v/retract! kb hs)]
                          ["in?"            #(v/in? kb hs)]
                          ["why"            #(v/why kb hs)]
                          ["why-not"        #(v/why-not kb hs)]
                          ["premise?"       #(v/premise? kb hs)]
                          ["sentex"         #(v/sentex kb hs)]
                          ["justification"  #(v/justification kb hs)]
                          ["defeat-class"   #(v/defeat-class kb hs)]
                          ["supporting-justifications" #(v/supporting-justifications kb hs)]
                          ["dependent-justifications"  #(v/dependent-justifications kb hs)]
                          ["provenance"     #(v/provenance kb hs)]
                          ["add-provenance" #(v/add-provenance kb hs {:source :test})]
                          ["edit :remove"   #(v/edit! kb {:remove [hs]})]]]
            (let [d (try (f) nil (catch clojure.lang.ExceptionInfo e (ex-data e)))]
              (is (= :bad-handle (:type d)) (str nm " refused the vector"))
              (is (= hs (:handle d)) (str nm " carried what it was given")))))
        (testing "check-edit reports the same refusal edit throws, as a problem"
          (let [[p :as ps] (v/check-edit kb {:remove [hs]})]
            (is (= 1 (count ps)))
            (is (= :bad-handle (:type p)))
            (is (= :remove (:in p)))
            (is (= hs (:entry p)))))
        (testing "and mapping over them is what works"
          (is (= [1 1] (mapv #(:removed-sentexes (v/retract! kb %)) hs))))))
    (testing "a value that is neither is refused too"
      (is (= :bad-handle (:type (try (v/in? kb :nonsense) nil
                                     (catch clojure.lang.ExceptionInfo e (ex-data e))))))
      (is (= :bad-handle (:type (first (v/check-edit kb {:remove [:nonsense]}))))
          "check-edit classes garbage the way edit does"))
    (testing "while an unknown integer handle is a different finding: not a bad handle"
      (is (= :unknown-handle (:type (first (v/check-edit kb {:remove [999999]}))))))))
