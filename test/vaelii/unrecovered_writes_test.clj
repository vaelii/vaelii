;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.unrecovered-writes-test
  "Writing into a KB whose derived state was never built.

  \"Unrecovered\" names four different arrangements, and the suite had no test that
  *wrote* to any of them — every `:recover? false` in it was a construction detail.  The
  four are reached differently and are repaired differently:

  | how you got there | records | index | TMS | premise roster |
  |---|---|---|---|---|
  | `:disk-log`, `:recover? false` | full | durable, full | empty | full |
  | a derived index, `:recover? false` | full | **empty** | empty | full |
  | records-only load, our dialect | full | full | empty | full |
  | records-only load, foreign dialect | full | full | empty | **empty** |

  What they share is that a *read* over one answers nothing — an answer that can be
  re-asked — while a *write* lands content the store keeps.  Every definitional check
  reads `jtms/in?`, so with no nodes all ten arms match nothing and the assert lands
  unchecked, and nothing later re-runs them.  So the write entry points refuse, and
  `core/*write-unrecovered?*` is the opt that names what accepting one gives up.

  These tests own their KBs rather than taking the fixture's: the state under test is a
  property of how a KB was opened, which a shared fixture cannot hand out."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.browser.web :as web]
            [vaelii.core :as v]
            [vaelii.impl.disk.backend :as backend]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu])
  (:import [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(defn- with-tmp-dir
  "Run `(f dir)` in a fresh temp directory, closing the disk stores opened on it and
  deleting it afterwards — `vaelii.disk-backend-test`'s shape."
  [f]
  (let [dir (str (Files/createTempDirectory "vaelii-unrec-" (into-array FileAttribute [])))]
    (try (f dir)
         (finally
           (backend/close-dir! dir)
           (doseq [x (reverse (file-seq (java.io.File. dir)))] (.delete ^java.io.File x))))))

(defn- ex-type
  "The `:type` of the `ex-info` `f` throws, or `::none`."
  [f]
  (try (f) ::none (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

;; ---- the shapes, and that each one is recognised -------------------------

(deftest a-durable-store-reopened-without-recovery-refuses-every-write
  ;; Row 1: `:disk` records under the log index.  The index is complete, so dedup
  ;; still works; what is missing is belief, and with it every definitional check.
  (with-tmp-dir
    (fn [dir]
      (let [seed (v/open-kb {:backend :disk-log :dir dir :space 26 :recover? :auto})]
        (v/assert seed '(symmetric siblingOf) 'CxUniverse)
        (v/assert seed '(siblingOf Ann Bob) 'CxUniverse)
        (v/close! seed))
      (let [kb (v/open-kb {:backend :disk-log :dir dir :space 26 :recover? false})]
        (testing "the hazard is named, and it is the belief half alone"
          (is (= {:no-belief true} (kb/write-hazards kb))))
        (testing "every write entry point refuses, and by the same name"
          (is (= :unrecovered-kb (ex-type #(v/assert kb '(dog Rex) 'CxUniverse))))
          (is (= :unrecovered-kb (ex-type #(v/assert-inert kb '(dog Rex) 'CxUniverse))))
          (is (= :unrecovered-kb (ex-type #(v/retract! kb 1))))
          (is (= :unrecovered-kb (ex-type #(v/edit! kb {:add [['(dog Rex) 'CxUniverse]]}))))
          (is (= :unrecovered-kb (ex-type #(v/preview kb {:remove [1]})))))
        (testing "the refusal names the repair rather than only the problem"
          (is (re-find #"\(recover kb\)"
                       (try (v/assert kb '(dog Rex) 'CxUniverse) ""
                            (catch clojure.lang.ExceptionInfo e (ex-message e))))))
        (testing "recover makes it writable"
          (v/recover kb)
          (is (= {} (kb/write-hazards kb)))
          (is (integer? (v/assert kb '(dog Rex) 'CxUniverse))))
        (v/close! kb)))))

(deftest a-derived-index-names-the-longer-repair
  ;; Row 2, the one that turns a wrong answer into a wrong store: the index is derived
  ;; and opens empty, so `assert` dedups through nothing and mints a second handle for a
  ;; sentence already stored.  `recover` does not rebuild an index — it reads one — so it
  ;; clears only half the hazard, and the entry point goes on refusing until `reindex`.
  (with-tmp-dir
    (fn [dir]
      (let [seed (v/open-kb {:backend :disk-columnar :dir dir :space 27 :recover? :auto})]
        (v/assert seed '(dog Muffet) 'CxUniverse)
        ;; A derived index is shared per directory for the life of the JVM, so a reopen
        ;; in *this* process would inherit the populated one.  Clearing it is what the
        ;; next JVM's open finds, which is the state under test.
        (p/clear-index! (:index seed))
        (v/close! seed))
      (let [kb (v/open-kb {:backend :disk-columnar :dir dir :space 27 :recover? false})]
        (is (= {:no-belief true :no-index true} (kb/write-hazards kb)))
        (is (= :unrecovered-kb (ex-type #(v/assert kb '(cat Tom) 'CxUniverse))))
        (testing "the message names reindex, not recover"
          (is (re-find #"\(reindex kb\)"
                       (try (v/assert kb '(cat Tom) 'CxUniverse) ""
                            (catch clojure.lang.ExceptionInfo e (ex-message e))))))
        (testing "recover alone is the wrong repair here, and the entry point still says so"
          (v/recover kb)
          (is (= {:no-index true} (kb/write-hazards kb)))
          (is (= :unrecovered-kb (ex-type #(v/assert kb '(cat Tom) 'CxUniverse)))))
        (testing "reindex is the right one"
          (v/reindex kb)
          (is (= {} (kb/write-hazards kb)))
          (is (integer? (v/assert kb '(cat Tom) 'CxUniverse))))
        (v/close! kb)))))

(deftest a-records-only-load-declares-itself-and-is-refused-on-its-word
  ;; Rows 3 and 4: a load that stores records into a KB opened over an **empty** store
  ;; and skips the recover.  Nothing was wrong at open, so `open-kb` concluded nothing —
  ;; and the state that results cannot be read back off the store afterwards, in either
  ;; direction.  Row 4 (a foreign dialect) rosters no premise and carries no strength, so
  ;; its store is byte-for-byte the store a KB of `assert-inert` sentexes has; row 3's is
  ;; the store two KBs sharing a space have, where the second one's belief is behind by
  ;; construction and the engine supports that.  So the loader says so, and the entry points
  ;; refuse on its word rather than on a reading that would catch the wrong things.
  (doseq [[label premise?] [["our dialect — a premise roster and no network" true]
                            ["a foreign dialect — no roster at all" false]]]
    (testing label
      (let [kb (tu/fresh)]
        (is (= {} (kb/write-hazards kb)) "an empty KB is empty, not unrecovered")
        (let [h (p/put-sentex (:records kb) (sx/sentex '(dog Muffet) 'CxUniverse {}))]
          (when premise? (p/mark-premise (:records kb) h :default))
          (p/index-sentex (:index kb) (p/get-sentex (:records kb) h) h))
        (is (= premise? (boolean (seq (p/premise-ids (:records kb))))))
        (is (= {} (kb/write-hazards kb))
            "a store read cannot tell this from an arrangement the engine supports")
        (kb/note-hazards! kb {:no-belief true})
        (is (= {:no-belief true} (kb/write-hazards kb)))
        (is (= :unrecovered-kb (ex-type #(v/assert kb '(cat Tom) 'CxUniverse))))
        (tu/clear-kb! kb)))))

(deftest a-second-kb-over-one-store-is-guarded-by-what-its-own-open-could-see
  ;; Belief is per-KB, so a KB opened beside another over the same store has an empty
  ;; network over a populated store by construction.  Nothing is *inferred* from that —
  ;; `assert-inert` stores a record and mints no node, so an all-inert KB reads the same
  ;; way and a probe would refuse every write into one.  The hazard is therefore a fact
  ;; about what this KB's own open could see, and both halves of that are pinned here:
  ;; the same pairing is guarded or unguarded depending on which end opened first, which
  ;; is a cost of declaring rather than probing and is stated in `kb`'s docstring comment.
  ;;
  ;; `let` binds in order, so which line comes first *is* the arrangement — writing the
  ;; two in one binding vector tests only the half that cannot fail.
  (testing "opened over a store still empty, then filled by the other end"
    (let [first-kb  (tu/fresh)
          second-kb (v/open-kb (assoc tu/scratch-space :recover? false))]
      (v/assert first-kb '(dog Muffet) 'CxUniverse)
      (is (seq (p/sentex-ids (:records second-kb))) "one store behind two KB values")
      (is (empty? (kb/write-hazards second-kb))
          "its open saw an empty store, so there was no hazard to record")
      (is (integer? (v/assert second-kb '(cat Tom) 'CxUniverse)))
      (tu/clear-kb! first-kb)))
  (testing "opened over the records, which its open can see and does declare"
    (let [first-kb (tu/fresh)]
      (v/assert first-kb '(dog Muffet) 'CxUniverse)
      (let [second-kb (v/open-kb (assoc tu/scratch-space :recover? false))]
        (is (= {:no-belief true} (kb/write-hazards second-kb))
            "the same pairing, guarded, because this end opened after the records")
        (is (= :unrecovered-kb (ex-type #(v/assert second-kb '(cat Tom) 'CxUniverse)))))
      (tu/clear-kb! first-kb))))

(deftest a-hazard-over-an-empty-store-is-discharged-by-the-write-that-refills-it
  ;; The two shapes a read of the atom cannot tell apart — a hazard declared, no records
  ;; yet — and the event that does.  A **loader** declares before its first write so the
  ;; hazard covers a load that throws part-way, and writes at the dump's own handles,
  ;; around the write entry points; anything else that emptied the store and is now asserting is
  ;; building this KB's network as it goes.  Retiring on *read* broke the first; never
  ;; retiring made every wipe-then-write caller carry the rule, which the perf harness,
  ;; the cost gate and the forward bench had each got wrong.
  (testing "a wipe, then an ordinary write: the write discharges it"
    (let [kb (tu/fresh)]
      (v/assert kb '(dog Muffet) 'CxUniverse)
      (kb/note-hazards! kb {:no-belief true})
      (tu/clear-kb! kb)
      (kb/note-hazards! kb {:no-belief true})       ; as if `open-kb` had declared it
      (is (integer? (v/assert kb '(cat Tom) 'CxUniverse))
          "the write into the empty store lands")
      (is (= {} (kb/write-hazards kb))
          "and the hazard is gone rather than firing on the next one")
      (is (integer? (v/assert kb '(cat Jerry) 'CxUniverse)))
      (tu/clear-kb! kb)))
  (testing "a loader's declaration outlives every read taken before its records land"
    (let [kb (tu/fresh)]
      (kb/note-hazards! kb {:no-belief true})       ; `io.import`, before its first write
      (is (= {} (kb/write-hazards kb)) "no records yet, so nothing for it to be true of")
      ;; the load writes around the entry points, at the dump's own handles
      (let [h (p/put-sentex (:records kb) (sx/sentex '(dog Rex) 'CxUniverse {}))]
        (p/index-sentex (:index kb) (p/get-sentex (:records kb) h) h))
      (is (= {:no-belief true} (kb/write-hazards kb))
          "and once they land the declaration is what it was")
      (is (= :unrecovered-kb (ex-type #(v/assert kb '(cat Tom) 'CxUniverse))))
      (tu/clear-kb! kb))))

(deftest the-dry-run-answers-what-the-entry-point-answers
  ;; `check` promises "would `assert` succeed, and if not, why" — the same functions in
  ;; the same order.  `check-writable!` runs first at the entry point, so a report that omits it
  ;; tells a caller validating a batch that every line is fine and is then refused on the
  ;; first one.  `check-edit` says it for the batch, before reading any entry.
  (let [kb (tu/fresh)]
    (v/assert kb '(dog Muffet) 'CxUniverse)
    (kb/note-hazards! kb {:no-belief true})
    (is (= [:unrecovered-kb] (mapv :type (v/check kb '(cat Tom) 'CxUniverse))))
    (is (= [:unrecovered-kb] (mapv :type (v/check-edit kb {:add [['(cat Tom) 'CxUniverse]]}))))
    (is (= :unrecovered-kb (ex-type #(v/assert kb '(cat Tom) 'CxUniverse)))
        "and the entry point agrees with the report")
    (testing "and under the opt both go quiet, because the write lands"
      (binding [v/*write-unrecovered?* true]
        (is (empty? (v/check kb '(cat Tom) 'CxUniverse)))
        (is (empty? (v/check-edit kb {:add [['(cat Tom) 'CxUniverse]]})))))
    (tu/clear-kb! kb)))

(deftest a-derived-record-is-not-an-inert-one-and-tears-down-like-neither
  ;; `retract-storage!` reaches its direct teardown when the handle has no TMS node, and
  ;; over an unbuilt network that is three facts rather than two: inert, a stored premise,
  ;; and a **derived** record — which carries no strength, so `p/premise-ids` does not
  ;; name it and the premise test cannot see it, while the store holds the justifications
  ;; that concluded it and any naming it as an antecedent.  Deleting it leaves those
  ;; dangling, which is the corruption the refusal exists for, seen from the one side the
  ;; strength test does not cover.
  (with-tmp-dir
    (fn [dir]
      (let [seed (v/open-kb {:backend :disk-log :dir dir :space 31 :recover? :auto})]
        (v/assert seed '(binary_predicate zsrc) 'CxUniverse)
        (v/assert seed (list 'set/forwardRule (list 'implies '(zsrc ?x ?y) '(zdst ?x ?y)))
                  'CxUniverse {:strength :monotonic})
        (v/assert seed '(zsrc Aa Bb) 'CxUniverse)
        (is (v/ask? seed '(zdst Aa Bb) 'CxUniverse) "the rule fired")
        (v/close! seed))
      ;; reopened without recovery: the records are all there and the network is empty,
      ;; so every stored handle reaches the no-node branch
      (let [kb (v/open-kb {:backend :disk-log :dir dir :space 31 :recover? false})
            derived (first (for [h (p/sentex-ids (:records kb))
                                 :let [s (:sentence (p/get-sentex (:records kb) h))]
                                 :when (and (seq? s) (= 'zdst (first s)))]
                             h))]
        (is (some? derived) "the conclusion is a stored record")
        (is (nil? (:strength (p/get-sentex (:records kb) derived)))
            "carrying no strength, so the premise test reads it as inert")
        (binding [v/*write-unrecovered?* true]
          (is (= :unrecovered-kb (ex-type #(v/retract! kb derived)))
              "refused even under the opt, the sweep it owes not being computable")
          (let [d (ex-data (try (v/retract! kb derived)
                                (catch clojure.lang.ExceptionInfo e e)))]
            (is (= [:no-belief] (:hazards d))
                "the hazards are the sorted vector of keys writable-problem carries")
            (is (= "retract!" (:operation d)))
            (is (= 'recover (:repair d)) "one :type, one shape at both entry points"))
          (is (some? (p/get-sentex (:records kb) derived))
              "and the record is still there"))
        (testing "and after recover it retracts, taking what rested on it"
          (v/recover kb)
          (is (map? (v/retract! kb derived))))
        (v/close! kb)))))

;; ---- what the refusal is protecting, stated as the defect ----------------

(deftest the-escape-shows-what-the-refusal-was-for
  ;; Each `is` below is one of the four defects the refusal prevents, run through the
  ;; opt that accepts them.  Together they are the argument for refusing by default:
  ;; a wrong answer can be re-asked, and none of these can be taken back.
  (with-tmp-dir
    (fn [dir]
      (let [seed (v/open-kb {:backend :disk-log :dir dir :space 28 :recover? :auto})]
        (v/assert seed '(genlCx CxNaturalWorld CxUniverse) 'CxUniverse)
        (v/assert seed '(symmetric siblingOf) 'CxUniverse)
        (v/assert seed '(disjoint dog cat) 'CxUniverse)
        (v/assert seed '(siblingOf Ann Bob) 'CxUniverse)
        (v/assert seed '(dog Muffet) 'CxNaturalWorld)
        (v/close! seed))
      (let [kb     (v/open-kb {:backend :disk-log :dir dir :space 28 :recover? false})
            before (count (p/sentex-ids (:records kb)))]
        (binding [v/*write-unrecovered?* true]
          (testing "the definitional checks pass vacuously — a disjointness violation lands"
            (is (integer? (v/assert kb '(cat Muffet) 'CxNaturalWorld))))
          (testing "a symmetric predicate is stored unsorted, so the duplicate never merges"
            (v/assert kb '(siblingOf Bob Ann) 'CxUniverse)
            (is (= (+ before 2) (count (p/sentex-ids (:records kb))))
                "two new records where a recovered KB would have written one"))
          (testing "retract! is refused even here — its sweep cannot be computed"
            (let [h (first (sort (p/premise-ids (:records kb))))]
              (is (= :unrecovered-premise (ex-type #(v/retract! kb h)))))))
        (testing "and the same KB, recovered, refuses what it just accepted"
          (v/recover kb)
          (v/assert kb '(dog Fido) 'CxNaturalWorld)
          (is (= :disjoint (ex-type #(v/assert kb '(cat Fido) 'CxNaturalWorld)))
              "with belief built, disjointness is enforced again"))
        (v/close! kb)))))

(deftest an-inert-sentex-is-still-torn-down-directly
  ;; The conflation the per-handle refusal separates.  Both cases answer
  ;; `jtms/known-datum?` false; only one of them means "nothing rests on this".  An
  ;; inert sentex is a record with no premise mark, and its direct teardown is correct
  ;; and must keep working — the refusal is for the record that carries one.
  (let [kb (tu/fresh)
        h  (v/assert-inert kb '(dog Muffet) 'CxUniverse)]
    (is (nil? (:strength (p/get-sentex (:records kb) h))))
    (is (= {:removed-sentexes 1 :removed-justifications 0} (v/retract! kb h)))
    (is (nil? (p/get-sentex (:records kb) h)))
    (tu/clear-kb! kb)))

(deftest an-emptied-store-stops-being-unrecovered
  ;; The latch is a claim about *stored records*, so a store emptied out from under it
  ;; has none to make — and the store can be emptied through the protocol without this
  ;; hearing about it, which is what `core/clear!` and the suite's own fixtures do.
  (with-tmp-dir
    (fn [dir]
      (let [seed (v/open-kb {:backend :disk-log :dir dir :space 29 :recover? :auto})]
        (v/assert seed '(dog Muffet) 'CxUniverse)
        (v/close! seed))
      (let [kb (v/open-kb {:backend :disk-log :dir dir :space 29 :recover? false})]
        (is (= {:no-belief true} (kb/write-hazards kb)))
        (p/clear-records! (:records kb))
        (is (= {} (kb/write-hazards kb)))
        (is (integer? (v/assert kb '(cat Tom) 'CxUniverse)))
        (v/close! kb)))))

(deftest a-plain-kb-is-never-treated-as-one
  ;; The other direction, and the one a false positive would break: an ordinary KB with
  ;; inert sentexes in it holds records the TMS has no node for **by design**, so no
  ;; count comparison can be what decides this.
  (let [kb (tu/fresh)]
    (v/assert kb '(dog Muffet) 'CxUniverse)
    (dotimes [i 3] (v/assert-inert kb (list 'cat (symbol (str "Tom" i))) 'CxUniverse))
    (is (= {} (kb/write-hazards kb)))
    (is (integer? (v/assert kb '(bird Tweety) 'CxUniverse)))
    (is (= 1 (count (:believed-added (v/preview kb {:add [['(fish Nemo) 'CxUniverse]]})))))
    (tu/clear-kb! kb)))

;; ---- and the browser, which is where an operator meets it ---------------

(deftest the-browser-refuses-the-write-as-a-page-not-an-exception
  ;; The refusal is an `ex-info` at the entry point, and a route that let one out would answer
  ;; an error status — which leaves htmx not swapping at all, so the write reads as
  ;; having silently vanished.  `write-refusal` already renders two conditions as pages
  ;; for exactly that reason; this is the third, and it says which repair applies.
  (with-tmp-dir
    (fn [dir]
      (let [seed (v/open-kb {:backend :disk-log :dir dir :space 30 :recover? :auto})]
        (v/assert seed '(dog Muffet) 'CxUniverse)
        (v/close! seed))
      (let [kb   (v/open-kb {:backend :disk-log :dir dir :space 30 :recover? false})
            app  (web/app kb)
            post (fn [uri params]
                   (app {:request-method :post :uri uri :scheme :http :params params
                         :headers {"host" "x" "origin" "http://x"}}))]
        (testing "reads stay open, exactly as they do beside a loader"
          (is (= 200 (:status (app {:request-method :get :uri "/stats"})))))
        (testing "and a write answers a page saying so, with the repair on it"
          (doseq [[uri params] [["/assert"  {"text" "(dog Rex)" "ctx" "CxUniverse"}]
                                ["/retract" {"handles" "1"}]]]
            (let [r (post uri params)]
              (is (= 200 (:status r)) (str uri " answers a page, not an error status"))
              (is (str/includes? (:body r) "Nothing was written") (str uri " says so"))
              (is (str/includes? (:body r) "stored but not built") (str uri " says why"))
              (is (str/includes? (:body r) "(recover kb)") (str uri " says which repair")))))
        (testing "nothing landed"
          (is (= 1 (count (p/sentex-ids (:records kb))))))
        (v/close! kb)))))
