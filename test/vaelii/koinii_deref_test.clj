;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.koinii-deref-test
  "Koinii cross-seat dereference: independent seats, each holding its own KB,
  kept in sync by content-addressed commits.  A locator is a hash over a sentex's
  canonical identity, so two seats holding the same assertion compute the same one; a
  commit id is a hash over a seat's whole locator set, so it is a function of state; and a
  marker is untrusted — a seat resolves it against its OWN KB and rehashes what it finds.

  One deftest per 'How to verify' bullet: two seats resolving one commit's sentence to the
  byte-identical canonical form and the same provenance, byte-stable export, tamper caught
  — plus the locator and commit-id invariants the design rests on.  The seats are separate
  KBs (memory on distinct spaces, and a genuinely disk-backed one for the git case)."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.disk.backend :as backend]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as vr]
            [vaelii.koinii.deref :as d]
            [vaelii.test-util :as tu])
  (:import (java.io File)
           (java.util Arrays)))

;;; ── seats and dumps ───────────────────────────────────────────────────

(defn- fresh-seat
  "An independent in-RAM seat — a cleared `:memory` KB on its own derived space, so it
  shares a store with no other seat (or with `*kb*`).  Clear it in a `finally`."
  [tag]
  (doto (v/open-kb (assoc tu/plain-memory-space :space [::seat (name tag)]))
    (tu/clear-kb!)))

(defn- disk-seat
  "A durable seat: a `:disk-log` KB over `dir`, opened unrecovered so an `import!` lands into
  an empty store (the pulled-commit case).  Close it with `backend/close-dir!`."
  [^File dir]
  (v/open-kb {:backend :disk-log :dir (.getPath dir) :recover? false}))

;; Atlas and Boreas each on their own seat's context, provenance fixed so the export is a
;; byte-stable function of state and every seat computes the same content.
(def ^:private atlas-fact  '(usesDatabase ProdCluster PostgreSQL14))
(def ^:private boreas-fact '(usesDatabase StageCluster RedisCache))

(defn- atlas-writes!
  "Atlas asserts its claim into its own context, recorded as its creator."
  [kb]
  (binding [v/*clock* (constantly 1750000000000)]
    (v/assert kb atlas-fact 'CxAtlas {:creator 'AgentAtlas})))

(defn- boreas-writes! [kb]
  (binding [v/*clock* (constantly 1750000000000)]
    (v/assert kb boreas-fact 'CxBoreas {:creator 'AgentBoreas})))

(defn- stream-bytes [^File dir nm]
  (with-open [in (io/input-stream (io/file dir nm))] (.readAllBytes in)))

(defn- tamper-locator
  "Flip one hex digit of `locator`'s digest body, leaving the `\"sha256:\"` tag intact — so
  the result is still a well-formed locator, just not the one this seat computes.  That is
  what makes it a test of the rehash: mangling the tag would make it no locator at all,
  which the resolvers refuse earlier and differently."
  [locator]
  (let [body (subs locator (count "sha256:"))]
    (str "sha256:" (if (= \0 (first body)) \1 \0) (subs body 1))))

;;; ── the locator: content-addressed, handle-independent ────────────────

(deftest a-locator-is-a-function-of-the-assertion-not-the-handle
  (let [a (fresh-seat :loc-a)
        b (fresh-seat :loc-b)]
    (try
      ;; two seats reach the fact among different other assertions, so the handles differ
      (v/assert a '(colour Sky Blue) 'CxAtlas)
      (let [ha (atlas-writes! a)]
        (boreas-writes! b)
        (v/assert b '(colour Grass Green) 'CxBoreas)
        (let [hb (atlas-writes! b)]
          (testing "same assertion, different seats and different handles, one locator"
            (is (not= ha hb) "the fixture put the fact at different handles")
            (is (= (d/locator-of a ha) (d/locator-of b hb))))
          (testing "and `locate` computes it without the fact being at any particular handle"
            (is (= (d/locator-of a ha) (d/locate a atlas-fact 'CxAtlas)))
            (is (= (d/locator-of b hb) (d/locate b atlas-fact 'CxAtlas))))
          (testing "context, polarity and sentence each change the locator"
            (is (not= (d/locate a atlas-fact 'CxAtlas)
                      (d/locate a atlas-fact 'CxBoreas)) "context is part of identity")
            (is (not= (d/locate a atlas-fact 'CxAtlas)
                      (d/locate a (list 'not atlas-fact) 'CxAtlas)) "polarity is")
            (is (not= (d/locate a atlas-fact 'CxAtlas)
                      (d/locate a boreas-fact 'CxAtlas)) "and the sentence is")))
        (is (re-matches #"sha256:[0-9a-f]{64}" (d/locator-of a ha)) "a self-describing sha256 locator"))
      (finally (tu/clear-kb! a) (tu/clear-kb! b)))))

;;; ── locators fold what the engine folds (the cross-seat guarantee) ────
;;; The whole distributed story rests on two seats computing ONE locator for one
;;; assertion even when they spell it differently — so a locator must fold exactly what
;;; the engine canonicalizes: a symmetric predicate's argument order and a comparison's
;;; direction.  `locate` / `locator-of` route through `res/kb-sentex`, which is why they
;;; do.  (This is the guarantee the adversarial review probed; here it as a committed
;;; regression test, since a locator that stopped folding would silently split one
;;; assertion into two across seats and break dereference without failing anything else.)

(deftest locators-fold-mirror-spellings-so-seats-agree
  (let [a (fresh-seat :canon-a)
        b (fresh-seat :canon-b)]
    (try
      (doseq [seat [a b]] (v/assert seat '(symmetric siblingOf) 'CxKin))
      (let [ha (v/assert a '(siblingOf Ann Bob) 'CxKin)          ; seat A's spelling
            hb (v/assert b '(siblingOf Bob Ann) 'CxKin)]         ; seat B's mirror spelling
        (testing "a symmetric predicate: both argument orders are one locator"
          (is (= (d/locator-of a ha) (d/locator-of b hb))
              "the mirror spelling on another seat computes the same locator")
          (is (= (d/locate a '(siblingOf Ann Bob) 'CxKin)
                 (d/locate a '(siblingOf Bob Ann) 'CxKin))
              "and `locate` folds the order the way storage does"))
        (testing "so a marker minted from one spelling dereferences the mirror-stored sentex"
          (let [r (d/dereference b (d/marker a ha))]             ; A's marker, resolved on B
            (is (:resolved? r) "resolves across the spelling difference")
            (is (= hb (:handle r)) "to B's own record, stored under the mirror")))
        (testing "comparison direction folds too — greaterThan stores as lessThan"
          (is (= (d/locate a '(greaterThan 5 3) 'CxKin)
                 (d/locate a '(lessThan 3 5) 'CxKin)))))
      (finally (tu/clear-kb! a) (tu/clear-kb! b)))))

;;; ── the commit id: a function of state, not of assertion order ─────────

(deftest a-commit-id-is-a-function-of-state
  (let [a (fresh-seat :commit-a)
        b (fresh-seat :commit-b)
        facts [['(a1 X Y) 'CxOne] ['(a2 Y Z) 'CxOne] ['(b1 P Q) 'CxTwo] ['(b2 Q R) 'CxTwo]]]
    (try
      (doseq [[s c] facts] (v/assert a s c))
      (doseq [[s c] (reverse facts)] (v/assert b s c))   ; the same state, reached backwards
      (testing "two seats at the same state agree on the commit id, whatever the order"
        (is (= (d/commit-id a) (d/commit-id b))))
      (testing "and it really depended on the order being irrelevant, not on emptiness"
        (is (re-matches #"sha256:[0-9a-f]{64}" (d/commit-id a)))
        (is (= 4 (count (p/sentex-ids (:records a))))))
      (testing "an extra assertion moves the commit id — it is a fingerprint of content"
        (v/assert b '(a3 Z W) 'CxOne)
        (is (not= (d/commit-id a) (d/commit-id b))))
      (finally (tu/clear-kb! a) (tu/clear-kb! b)))))

;;; ── a reply is located by its target ─────────────────────────────────
;;; Every koinii response act names its target as `(sentexHandle n)`, and `n` is the
;;; number the storing seat minted.  Two seats that build one conversation in different
;;; orders mint different numbers, so the locator digests the target's identity in `n`'s
;;; place, and the marker carries the target's marker so the other seat can find it.

(defn- conversation!
  "Atlas's claim, Boreas's claim, Boreas endorsing Atlas's, and Atlas endorsing that
  endorsement — Atlas's claim first when `atlas-first?`, Boreas's otherwise.  The other
  order also mints and retracts one unrelated fact first, so no handle it mints equals
  the first order's.  Returns the four handles."
  [kb atlas-first?]
  (binding [v/*clock* (constantly 1750000000000)]
    (let [junk    (when-not atlas-first? (v/assert kb '(colour Grass Green) 'CxBoreas))
          [ha hb] (if atlas-first?
                    [(atlas-writes! kb) (boreas-writes! kb)]
                    (let [hb (boreas-writes! kb)] [(atlas-writes! kb) hb]))
          end     (v/assert kb (list 'endorses 'AgentBoreas (v/sentex-handle ha)) 'CxBoreas
                            {:creator 'AgentBoreas})
          end2    (v/assert kb (list 'endorses 'AgentAtlas (v/sentex-handle end)) 'CxAtlas
                            {:creator 'AgentAtlas})]
      (when junk (v/retract! kb junk))
      {:atlas ha :boreas hb :end end :end2 end2})))

(deftest a-reply-is-located-by-its-target
  (let [a (fresh-seat :reply-a)
        b (fresh-seat :reply-b)]
    (try
      (let [ha (conversation! a true)
            hb (conversation! b false)]
        (is (every? #(not= (% ha) (% hb)) [:atlas :end :end2])
            "the two orders put the target and both replies at different handles")
        (testing "each reply has one locator on both seats, and so does a reply to a reply"
          (is (= (d/locator-of a (:end ha)) (d/locator-of b (:end hb))))
          (is (= (d/locator-of a (:end2 ha)) (d/locator-of b (:end2 hb)))))
        (testing "so the two seats agree on the commit id and the state root"
          (is (= (d/commit-id a) (d/commit-id b)))
          (is (= (d/state-root a) (d/state-root b))))
        (testing "`locate` computes a reply's locator from its sentence"
          (is (= (d/locator-of a (:end2 ha))
                 (d/locate a (v/sentence-of (v/sentex a (:end2 ha))) 'CxAtlas))))
        (testing "a reply to a different target is a different locator"
          (let [other (v/assert a (list 'endorses 'AgentBoreas (v/sentex-handle (:boreas ha)))
                                'CxBoreas)]
            (is (not= (d/locator-of a other) (d/locator-of a (:end ha)))))))
      (finally (tu/clear-kb! a) (tu/clear-kb! b)))))

(deftest a-reply-marker-resolves-on-a-seat-that-built-the-conversation
  (let [a (fresh-seat :rmark-a)
        b (fresh-seat :rmark-b)]
    (try
      (let [ha   (conversation! a true)
            hb   (conversation! b false)
            m    (read-string (pr-str (d/marker a (:end2 ha))))]
        (testing "the marker carries its target's marker, and that one its own target's"
          (is (= #{(:end ha)} (set (keys (:targets m)))))
          (is (= #{(:atlas ha)} (set (keys (get-in m [:targets (:end ha) :targets]))))))
        (testing "the other seat resolves each target first, then the reply, to its own handles"
          (let [r (d/dereference b m)]
            (is (:resolved? r))
            (is (= (:end2 hb) (:handle r)))))
        (testing "without `:targets` the numbers are the sender's, and the other seat holds no such reply"
          (is (= :not-received (:reason (d/dereference b (dissoc m :targets))))))
        (testing "a target this seat does not hold fails the reply and names the target"
          (let [r (d/dereference b (assoc-in m [:targets (:end ha) :targets (:atlas ha) :sentence]
                                             '(usesDatabase ProdCluster Oracle)))]
            (is (false? (:resolved? r)))
            (is (= :not-received (:reason r)))
            (is (= (:end ha) (:target r)))))
        (testing "a target swapped for another stored record fails the reply's rehash or lookup"
          (let [r (d/dereference b (assoc-in m [:targets (:end ha) :targets (:atlas ha)]
                                             (d/marker b (:boreas hb))))]
            (is (false? (:resolved? r)))))
        (testing "a `:targets` that is not a map of handle numbers to markers is malformed"
          (doseq [t [[1 2] {"1" {}} {1 "x"}]]
            (is (= [:malformed :targets]
                   ((juxt :reason :problem) (d/dereference b (assoc m :targets t))))
                (pr-str t))))
        (testing "a chain of targets deeper than the bound is malformed and does not recurse"
          (let [deep (reduce (fn [inner _] (assoc m :targets {(:end ha) inner})) m (range 80))]
            (is (= [:malformed :targets] ((juxt :reason :problem) (d/dereference b deep)))))))
      (finally (tu/clear-kb! a) (tu/clear-kb! b)))))

(deftest a-record-naming-itself-or-no-record-digests
  (let [a (fresh-seat :self-a)
        b (fresh-seat :self-b)]
    (try
      (boreas-writes! b)
      (let [self! (fn [kb]
                    ;; the next handle, named in the sentence stored at it
                    (let [n (inc (reduce max 0 (v/handles kb)))
                          h (v/assert kb (list 'endorses 'AgentAtlas (v/sentex-handle n)) 'CxAtlas)]
                      (is (= n h) "the fixture predicted the handle")
                      h))
            sa (self! a)
            sb (self! b)]
        (testing "a record naming itself is one locator on two seats with different handles"
          (is (not= sa sb))
          (is (= (d/locator-of a sa) (d/locator-of b sb)))
          (is (= (d/locator-of a sa) (d/locate a (v/sentence-of (v/sentex a sa)) 'CxAtlas))))
        (testing "its marker is finite and resolves"
          (let [m (d/marker a sa)]
            (is (nil? (:targets m)))
            (is (:resolved? (d/dereference a m))))))
      (testing "a handle naming no record digests its number, so two such references differ"
        (let [h1 (v/assert a (list 'endorses 'AgentAtlas (v/sentex-handle 900001)) 'CxAtlas)
              h2 (v/assert a (list 'endorses 'AgentAtlas (v/sentex-handle 900002)) 'CxAtlas)]
          (is (re-matches #"sha256:[0-9a-f]{64}" (d/locator-of a h1)))
          (is (not= (d/locator-of a h1) (d/locator-of a h2)))
          (is (nil? (:targets (d/marker a h1))))))
      (finally (tu/clear-kb! a) (tu/clear-kb! b)))))

;;; ── byte-stable export: the same state exports to the same bytes ──────

(deftest publishing-the-same-state-twice-yields-byte-identical-record-streams
  (let [a  (fresh-seat :bytes)
        d1 (tu/temp-dir "koinii-deref-" "b1" "-")
        d2 (tu/temp-dir "koinii-deref-" "b2" "-")]
    (tu/rm-rf! d1) (tu/rm-rf! d2)                               ; export! makes its own dir
    (try
      (atlas-writes! a)
      (boreas-writes! a)
      (d/publish! a d1)
      (d/publish! a d2)
      (testing "the record streams are a byte-stable function of the KB state"
        (doseq [nm ["sentexes.nippy.stream" "provenance.nippy.stream"]]
          (is (Arrays/equals ^bytes (stream-bytes d1 nm) ^bytes (stream-bytes d2 nm))
              (str nm " differs between two exports of one state"))))
      (finally (tu/clear-kb! a) (tu/rm-rf! d1) (tu/rm-rf! d2)))))

;;; ── two seats, one commit, the same sentence ─────────────────────────

(deftest two-seats-pull-one-commit-and-resolve-the-same-sentence
  (let [source (fresh-seat :src)
        mem    (fresh-seat :seat-mem)
        dir    (tu/temp-dir "koinii-deref-" "disk-seat" "-")
        dump   (tu/temp-dir "koinii-deref-" "commit" "-")]
    (tu/rm-rf! dump)
    (let [disk (disk-seat dir)]
      (try
        (let [ha (atlas-writes! source)]
          (boreas-writes! source)
          (d/publish! source dump)                       ; seat A commits
          (d/pull! mem dump)                             ; a second in-RAM clone pulls it
          (d/pull! disk dump)                            ; and a genuinely durable seat pulls it
          (let [mk (d/marker source ha)]                 ; a marker for Atlas's claim
            (testing "every seat agrees on the commit id — the same knowledge, three stores"
              (is (= (d/commit-id source) (d/commit-id mem) (d/commit-id disk))))
            (testing "and on the state root — a clone that recovered identical provenance is the same snapshot"
              (is (= (d/state-root source) (d/state-root mem) (d/state-root disk))))
            (doseq [[label seat] [["memory clone" mem] ["disk clone" disk]]]
              (testing (str "the " label " resolves the marker from its OWN KB")
                (let [r (d/dereference seat mk)]
                  (is (:resolved? r) (str label " resolved"))
                  (is (= atlas-fact (:sentence r)) "to the byte-identical canonical sentence")
                  (is (= 'CxAtlas (:context r)))
                  (is (= :positive (:polarity r)))
                  (testing "and the same provenance — who asserted it, recovered after the pull"
                    (is (= 'AgentAtlas (:seat r)))
                    (is (= 'AgentAtlas (:creator (:provenance r)))))
                  (testing "the locator this seat computes is the marker's — resolved from the KB"
                    (is (= (:locator mk) (:locator r)))
                    (is (= (:locator mk) (d/locator-of seat (:handle r))))))))))
        (finally
          (tu/clear-kb! source) (tu/clear-kb! mem)
          (backend/close-dir! (.getPath dir)) (tu/rm-rf! dir) (tu/rm-rf! dump))))))

;;; ── a forked seat keeps its own writes across a newer pull ────────────

(defn- forked-seat
  "A seat whose store is a fork: the shared base in one store and the seat's own writes in
  another, both `:memory` on spaces named after `tag`, or both `:disk-log` under `dir`."
  [tag ^File dir]
  (v/open-kb (if dir
               {:backend :overlay
                :base    {:backend :disk-log :dir (str (io/file dir "base"))}
                :overlay {:backend :disk-log :dir (str (io/file dir "own"))}}
               {:backend :overlay
                :base    {:backend :memory :space [::base tag]}
                :overlay {:backend :memory :space [::own tag]}})))

(def ^:private shared-rule '(implies (usesDatabase ?c ?d) (dependsOn ?c ?d)))
(def ^:private stale-fact  '(usesDatabase OldCluster MySQL5))

(defn- believed-in?
  [kb sentence context]
  (boolean (some-> (v/handle-of kb sentence context) (#(v/believed? kb % context)))))

(deftest two-forked-seats-keep-their-writes-when-they-pull-a-newer-commit
  (let [src1 (fresh-seat :rebase-src1)
        src2 (fresh-seat :rebase-src2)
        c1   (tu/temp-dir "koinii-deref-" "rebase-c1" "-")
        c2   (tu/temp-dir "koinii-deref-" "rebase-c2" "-")
        dir  (tu/temp-dir "koinii-deref-" "rebase-disk" "-")]
    (tu/rm-rf! c1) (tu/rm-rf! c2)
    (let [a (forked-seat :rebase-a nil)
          b (atom (forked-seat nil dir))]
      (try
        ;; commit 1: a forward rule and two facts in the shared context
        (v/assert src1 shared-rule 'CxShared {:direction :forward})
        (v/assert src1 atlas-fact 'CxShared)
        (v/assert src1 stale-fact 'CxShared)
        (d/publish! src1 c1)
        ;; commit 2 holds the same rule and Atlas's fact, asserted in another order so every
        ;; handle moves, drops the stale fact and adds Boreas's
        (v/assert src2 boreas-fact 'CxShared)
        (v/assert src2 atlas-fact 'CxShared)
        (v/assert src2 shared-rule 'CxShared {:direction :forward})
        (d/publish! src2 c2)
        (d/pull! a c1)
        (d/pull! @b c1)
        ;; each seat observes in a context of its own that sees the shared one
        (v/assert a '(genlCx CxSeatA CxShared))
        (v/assert a '(usesDatabase EdgeNode SQLite3) 'CxSeatA {:creator 'AgentA})
        (v/assert @b '(genlCx CxSeatB CxShared))
        (v/assert @b '(usesDatabase EdgeNode DuckDb) 'CxSeatB {:creator 'AgentB})
        ;; seat A retracts a shared fact; seat B hides one from its own context
        (v/retract! a (v/handle-of a atlas-fact 'CxShared))
        (v/assert @b (list 'except (list 'sentexHandle (v/handle-of @b atlas-fact 'CxShared)))
                  'CxSeatB)
        (let [summaries {:a (d/pull! a c2) :b (d/pull! @b c2)}]
          (testing "each pull asserted the seat's writes again and refused none"
            (doseq [[k s] summaries]
              (is (empty? (:refused (:rebase s))) (str k))
              (is (empty? (:unresolved (:rebase s))) (str k))))
          (testing "seat A retracted the shared fact again"
            (is (= 1 (:retracted (:rebase (:a summaries)))))))
        (v/close! @b)
        (reset! b (forked-seat nil dir))
        (doseq [[label s cx own other agent]
                [["memory seat" a 'CxSeatA 'SQLite3 'DuckDb 'AgentA]
                 ["disk seat, reopened" @b 'CxSeatB 'DuckDb 'SQLite3 'AgentB]]]
          (testing (str "the " label " keeps its observation, its creator and what follows")
            (is (believed-in? s (list 'usesDatabase 'EdgeNode own) cx))
            (is (= agent (:creator (v/provenance s (v/handle-of s (list 'usesDatabase 'EdgeNode own)
                                                                cx)))))
            (is (believed-in? s (list 'dependsOn 'EdgeNode own) cx)))
          (testing (str "the " label " holds the newer commit's beliefs")
            (is (believed-in? s boreas-fact 'CxShared))
            (is (believed-in? s '(dependsOn StageCluster RedisCache) 'CxShared))
            (is (not (believed-in? s stale-fact 'CxShared)))
            (is (not (believed-in? s (list 'usesDatabase 'EdgeNode other) cx)))))
        (testing "a shared fact a seat retracted stays retracted, and stays shared on the other seat"
          (is (not (believed-in? a atlas-fact 'CxShared)))
          (is (believed-in? @b atlas-fact 'CxShared)))
        (testing "an except naming a shared fact names the fact's handle in the newer commit"
          (is (not (believed-in? @b atlas-fact 'CxSeatB))))
        (finally
          (tu/clear-kb! src1) (tu/clear-kb! src2)
          (v/close! a)
          (doseq [sp [[::base :rebase-a] [::own :rebase-a]]] (tu/drop-space! sp))
          (v/close! @b)
          (backend/close-dir! (str (io/file dir "base")))
          (tu/rm-rf! dir) (tu/rm-rf! c1) (tu/rm-rf! c2))))))

(defn- defeats
  "The `:defeat` reports `(conflicts kb {:defeats? true})` holds, by content:
  `[loser winners placed-in]` over sentences and contexts."
  [kb]
  (into #{} (comp (filter #(= :defeat (:verdict %)))
                  (map (fn [{:keys [loser winners placed-in]}]
                         [[(:sentence loser) (:context loser)]
                          (mapv (juxt :sentence :context) winners)
                          placed-in])))
        (v/conflicts kb {:defeats? true})))

(def ^:private delta-base
  "The shared base: a pet is a cat by default, and nothing is both a dog and a cat."
  [['(disjoint delta_dog delta_cat) {:strength :monotonic}]
   ['(set/forwardRule (implies (delta_pet ?x) (delta_cat ?x))) nil]
   ['(delta_pet Muffet) nil]
   ['(delta_pet Rex) nil]])

(deftest a-seat-publishes-its-delta-and-a-seat-holding-the-base-at-other-handles-reads-the-same-defeat
  (let [src (fresh-seat :delta-src)
        b   (fresh-seat :delta-b)
        c1  (tu/temp-dir "koinii-deref-" "delta-commit" "-")
        out (tu/temp-dir "koinii-deref-" "delta-out" "-")]
    (tu/rm-rf! c1) (tu/rm-rf! out)
    (let [a (forked-seat :delta-a nil)]
      (try
        (doseq [[s o] delta-base] (v/assert src s 'CxShared o))
        (d/publish! src c1)
        (d/pull! a c1)
        ;; seat B holds the same base at other handles: one throwaway handle, then the
        ;; base in reverse
        (v/retract! b (v/assert b '(delta_pet Omega) 'CxShared))
        (doseq [[s o] (rseq delta-base)] (v/assert b s 'CxShared o))
        ;; seat A observes a dog where the base expects a cat, and hides a shared fact
        (v/assert a '(genlCx CxSeatA CxShared))
        (v/assert a '(delta_dog Muffet) 'CxSeatA {:strength :monotonic})
        (v/assert a (list 'except (v/sentex-handle (v/handle-of a '(delta_pet Rex) 'CxShared)))
                  'CxSeatA)
        (let [summary (v/export-text! a (.getPath out) {:delta? true})]
          (testing "the delta holds the seat's three writes and nothing of the base"
            (is (= [3 0 0] ((juxt :sentences :skipped :retractions) summary)))
            (is (not (re-find #"delta_pet Muffet" (apply str (map slurp (rest (file-seq out)))))))))
        (let [merged (v/load-text! b (.getPath out) {:merge? true})]
          (is (empty? (:refused merged))))
        (testing "seat B reads seat A's defeat"
          (is (seq (defeats a)))
          (is (= (defeats a) (defeats b))))
        (testing "the except names seat B's handle for the shared fact"
          (is (believed-in? b '(delta_pet Rex) 'CxShared))
          (is (not (believed-in? b '(delta_pet Rex) 'CxSeatA))))
        (finally
          (tu/clear-kb! src) (tu/clear-kb! b)
          (v/close! a)
          (doseq [sp [[::base :delta-a] [::own :delta-a]]] (tu/drop-space! sp))
          (tu/rm-rf! c1) (tu/rm-rf! out))))))

(deftest a-delta-reference-the-reading-seat-canonicalizes-otherwise-is-refused-by-its-digest
  (doseq [[row b-only refused]
          [["a symmetric mark seat A lacks sorts the arguments B stores"
            '(symmetric deltaNear) [:canonical-mismatch]]
           ["a sameAs seat A lacks keeps the spelling B stores beside its restatement"
            '(sameAs Dover Calais) []]]]
    (testing row
      (let [src (fresh-seat :mismatch-src)
            b   (fresh-seat :mismatch-b)
            c1  (tu/temp-dir "koinii-deref-" "mismatch-commit" "-")
            out (tu/temp-dir "koinii-deref-" "mismatch-out" "-")
            fact '(deltaNear Dover Calais)]
        (tu/rm-rf! c1) (tu/rm-rf! out)
        (let [a (forked-seat :mismatch-a nil)]
          (try
            (v/assert src fact 'CxShared)
            (d/publish! src c1)
            (d/pull! a c1)
            (v/assert b b-only 'CxShared {:strength :monotonic})
            (v/assert b fact 'CxShared)
            (v/assert a '(genlCx CxSeatA CxShared))
            (v/assert a (list 'except (v/sentex-handle (v/handle-of a fact 'CxShared))) 'CxSeatA)
            (v/export-text! a (.getPath out) {:delta? true})
            (let [merged (v/load-text! b (.getPath out) {:merge? true})]
              (is (= refused (mapv :type (:refused merged)))))
            (finally
              (tu/clear-kb! src) (tu/clear-kb! b)
              (v/close! a)
              (doseq [sp [[::base :mismatch-a] [::own :mismatch-a]]] (tu/drop-space! sp))
              (tu/rm-rf! c1) (tu/rm-rf! out))))))))

(deftest a-pull-into-a-non-empty-seat-that-is-no-fork-is-refused
  (let [src  (fresh-seat :refuse-src)
        seat (fresh-seat :refuse-seat)
        dump (tu/temp-dir "koinii-deref-" "refuse-commit" "-")]
    (tu/rm-rf! dump)
    (try
      (atlas-writes! src)
      (d/publish! src dump)
      (boreas-writes! seat)
      (let [e (try (d/pull! seat dump) nil (catch clojure.lang.ExceptionInfo e e))]
        (is (= :not-empty (:type (ex-data e))))
        (is (re-find #":rebase\? true" (ex-message e)) "the refusal names the fork layout"))
      (let [f (v/fork seat)
            e (try (d/pull! f dump) nil (catch clojure.lang.ExceptionInfo e e))]
        (is (= :frozen-base (:type (ex-data e))) "a fork of a live KB does not own its base")
        (v/close! f))
      (finally (tu/clear-kb! src) (tu/clear-kb! seat) (tu/rm-rf! dump)))))

;;; ── the marker is untrusted: tamper and non-receipt are caught ────────

(deftest a-tampered-or-unreceived-marker-is-rejected-and-the-kb-is-the-authority
  (let [source (fresh-seat :tamper-src)
        seat   (fresh-seat :tamper-seat)
        dump   (tu/temp-dir "koinii-deref-" "tamper-commit" "-")]
    (tu/rm-rf! dump)
    (try
      (let [ha (atlas-writes! source)]
        (boreas-writes! source)
        (d/publish! source dump)
        (d/pull! seat dump)
        (let [mk (d/marker source ha)]
          (testing "the genuine marker resolves"
            (is (:resolved? (d/dereference seat mk))))
          (testing "a tampered locator fails the rehash — the marker's payload is rejected, not the KB"
            ;; one hex digit of the digest body flipped, the "sha256:" tag intact: a
            ;; WELL-FORMED locator that is not this seat's, so the rehash is what rejects
            ;; it.  A locator mangled out of the format never gets that far — it is not a
            ;; locator, and is refused as `:malformed` before the KB is read at all.
            (let [bad (assoc mk :locator (tamper-locator (:locator mk)))
                  r   (d/dereference seat bad)]
              (is (not (:resolved? r)))
              (is (= :locator-mismatch (:reason r)))
              (is (= (:locator mk) (:actual r)) "the KB's own locator is what it compared against")))
          (testing "a payload naming a sentence this seat never received does not fall back to trust"
            (let [r (d/dereference seat (assoc mk :sentence '(usesDatabase ProdCluster Mango9)))]
              (is (not (:resolved? r)))
              (is (= :not-received (:reason r)))))
          (testing "and a marker for Boreas's fact resolves — the seat DID pull that one"
            (let [rb (d/dereference seat (d/marker source (v/handle-of source boreas-fact 'CxBoreas)))]
              (is (:resolved? rb))
              (is (= 'AgentBoreas (:seat rb)))))))
      (finally (tu/clear-kb! source) (tu/clear-kb! seat) (tu/rm-rf! dump)))))

;;; ── a malformed marker is ANSWERED, never thrown out of the resolve path ──
;;; A marker arrives over an untrusted transport, so garbage — or a hostile peer's
;;; deliberately malformed sentence — must earn the module's own refusal rather than an
;;; engine-vocabulary exception out of `handle-of`.  The peer would otherwise crash the
;;; receiving seat's resolve path by sending `{:sentence [1 2]}`.

(deftest a-malformed-marker-is-refused-and-never-throws
  (let [source (fresh-seat :bad-src)
        seat   (fresh-seat :bad-seat)
        dump   (tu/temp-dir "koinii-deref-" "bad-commit" "-")]
    (tu/rm-rf! dump)
    (try
      (let [ha (atlas-writes! source)]
        (d/publish! source dump)
        (d/pull! seat dump)
        (let [mk (d/marker source ha)]
          (testing "the genuine marker still resolves — the malformed-marker check lets a real one through"
            (is (:resolved? (d/dereference seat mk))))

          (testing "a malformed :sentence is answered, not thrown — the bug this closes"
            (let [r (d/dereference seat (assoc mk :sentence [1 2]))]
              (is (false? (:resolved? r)) "no engine :shape exception escapes")
              (is (= :malformed (:reason r)))
              (is (= :shape (:problem r)) "the engine's own refusal type names the part")
              (is (= (:locator mk) (:locator r)) "the payload is echoed as it arrived")))

          (testing "and a context the engine will not be asked about is the same answer"
            (let [r (d/dereference seat (assoc mk :context 'CxInference))]
              (is (false? (:resolved? r)))
              (is (= :malformed (:reason r)))
              (is (= :unsupported-context (:problem r)))))

          ;; `handle-of` refuses these by `:shape` rather than answering nil, so a peer
          ;; sending one reads as sending garbage and not as out of sync
          (testing "a sentence that is not a list, or a context that is not one, is malformed"
            (doseq [[label bad] [[":sentence a number" (assoc mk :sentence 42)]
                                 [":sentence a map"    (assoc mk :sentence {:a 1})]
                                 [":sentence a string" (assoc mk :sentence "x")]
                                 [":context nil"       (assoc mk :context nil)]
                                 [":context a number"  (assoc mk :context 42)]
                                 [":context a variable" (assoc mk :context '?ctx)]]]
              (let [r (d/dereference seat bad)]
                (is (false? (:resolved? r)) label)
                (is (= :malformed (:reason r)) label)
                (is (= :shape (:problem r)) label))))

          (testing "a malformed :locator is refused before the KB is consulted at all"
            (doseq [[label bad] [["not a string" 42]
                                 ["no algorithm tag" (apply str (repeat 64 "a"))]
                                 ["uppercase hex" (str "sha256:" (apply str (repeat 64 "A")))]
                                 ["too short" "sha256:aa"]
                                 ["wrong algorithm" (str "sha1:" (apply str (repeat 64 "a")))]
                                 ;; the tag reversed along with the body: not a locator at
                                 ;; all, so it is refused as one rather than compared as one
                                 ["reversed tag and all" (apply str (reverse (:locator mk)))]]]
              (let [r (d/dereference seat (assoc mk :locator bad))]
                (is (false? (:resolved? r)) label)
                (is (= :malformed (:reason r)) label)
                (is (= :locator (:problem r)) label))))

          (testing "a non-map payload is not a marker, whatever it is"
            (doseq [[label bad] [["a string" "sha256:deadbeef"]
                                 ["a vector" [1 2 3]]
                                 ["nil" nil]
                                 ["a number" 7]]]
              (let [r (d/dereference seat bad)]
                (is (false? (:resolved? r)) label)
                (is (= :malformed (:reason r)) label)
                (is (= :not-a-map (:problem r)) label)
                (is (nil? (:locator r)) label))))

          (testing "a missing lookup key is malformed, not a bare-locator resolve"
            (let [r (d/dereference seat (dissoc mk :sentence))]
              (is (= :malformed (:reason r)))
              (is (= :no-sentence (:problem r))))
            (let [r (d/dereference seat (dissoc mk :context))]
              (is (= :malformed (:reason r)))
              (is (= :no-context (:problem r))))
            (testing "but the CLAIMED seat is not required — dereference never reads it"
              (is (:resolved? (d/dereference seat (dissoc mk :seat))))))

          ;; the malformed-marker check must not swallow the genuine absence it exists to stay
          ;; distinct from
          (testing "a WELL-FORMED marker for a sentence this seat does not hold is still :not-received"
            (let [r (d/dereference seat (assoc mk :sentence '(usesDatabase ProdCluster Mango9)))]
              (is (false? (:resolved? r)))
              (is (= :not-received (:reason r)))
              (is (nil? (:problem r)) "an absence carries no problem — nothing was malformed")))

          (testing "why-marker passes the refusal through rather than proving anything"
            (let [r (d/why-marker seat (assoc mk :sentence [1 2]))]
              (is (= :malformed (:reason r)))
              (is (nil? (:why r)))))))
      (finally (tu/clear-kb! source) (tu/clear-kb! seat) (tu/rm-rf! dump)))))

;;; ── the why handoff: the proof comes from the seat's own KB ───────────

(deftest why-marker-hands-off-to-the-seats-own-proof
  (let [source (fresh-seat :why-src)
        seat   (fresh-seat :why-seat)
        dump   (tu/temp-dir "koinii-deref-" "why-commit" "-")]
    (tu/rm-rf! dump)
    (try
      (let [ha (atlas-writes! source)]
        (d/publish! source dump)
        (d/pull! seat dump)
        (let [r (d/why-marker seat (d/marker source ha))]
          (testing "the marker names WHAT to prove; the proof is the seat's own"
            (is (:resolved? r))
            (is (= (:handle r) (:root (:why r))))
            (is (true? (:believed? (tu/why-root (:why r)))) "resolved and believed on this seat")
            (is (= atlas-fact (:sentence (tu/why-root (:why r)))))
            (is (true? (:premise? (tu/why-root (:why r)))) "an asserted fact rests on nothing below it"))))
      (finally (tu/clear-kb! source) (tu/clear-kb! seat) (tu/rm-rf! dump)))))

;;; ── a NEGATIVE fact round-trips (a `:false` sentex keeps its `not`) ────
;;; Regression: a stored `(not S)` keeps the `not` in its `:sentence`, which is the whole
;;; of its sign (docs/storage.md).  A marker must carry that field UNCHANGED — an earlier `assertable`
;;; re-wrapped it, double-negating the sentence into a positive one that resolved to
;;; nothing, and it failed as `:not-received` — indistinguishable from "not pulled yet".

(deftest a-negative-fact-round-trips-and-dereferences
  (let [source (fresh-seat :neg-src)
        seat   (fresh-seat :neg-seat)
        dump   (tu/temp-dir "koinii-deref-" "neg-commit" "-")]
    (tu/rm-rf! dump)
    (try
      (let [nh (v/assert source '(not (happy Rex)) 'CxAtlas {:creator 'AgentAtlas})]
        (testing "the store keeps the `not` in :sentence"
          (is (= '(not (happy Rex)) (:sentence (v/sentex source nh)))))
        (d/publish! source dump)
        (d/pull! seat dump)
        (let [mk (d/marker source nh)]
          (testing "the marker carries the asserted negative form verbatim"
            (is (= '(not (happy Rex)) (:sentence mk))))
          (testing "and it dereferences on the seat that pulled it — not a false :not-received"
            (let [r (d/dereference seat mk)]
              (is (:resolved? r) "the negative fact resolves across seats")
              (is (= :negative (:polarity r)))
              (is (= '(not (happy Rex)) (:sentence r)))
              (is (= 'AgentAtlas (:seat r)))))))
      (finally (tu/clear-kb! source) (tu/clear-kb! seat) (tu/rm-rf! dump)))))

;;; ── the encoder covers what a sentence can hold: chars, doubles ───────
;;; Regression: a `char` is legal sentence content (naming/form-rank), and commit-id folds
;;; EVERY stored sentex — so a char the encoder could not handle would throw and disable
;;; commit-id / locate / state-root for the whole seat, not just that record.

(deftest the-encoder-handles-chars-and-doubles-without-poisoning-the-commit
  (let [a (fresh-seat :enc-a)
        b (fresh-seat :enc-b)]
    (try
      (doseq [seat [a b]]
        (v/assert seat '(grade Essay \A) 'CxS)                 ; a char argument
        (v/assert seat '(ratioOf Circle 3.14159) 'CxS))        ; a double argument
      (testing "commit-id / locate compute over char- and double-bearing sentences"
        (is (re-matches #"sha256:[0-9a-f]{64}" (d/commit-id a)) "no throw on the char/double records")
        (is (re-matches #"sha256:[0-9a-f]{64}" (d/locate a '(grade Essay \A) 'CxS))))
      (testing "and two seats agree on them — the values are content-addressed stably"
        (is (= (d/commit-id a) (d/commit-id b)))
        (is (= (d/locate a '(grade Essay \A) 'CxS)
               (d/locate b '(grade Essay \A) 'CxS)))
        (is (not= (d/locate a '(grade Essay \A) 'CxS)
                  (d/locate a '(grade Essay \B) 'CxS)) "distinct chars, distinct locators"))
      (finally (tu/clear-kb! a) (tu/clear-kb! b)))))

;;; ── and a value the encoding does not cover is refused, not hashed ────
;;; The encoder is a closed spec, and that is what makes a locator a shared address: two
;;; seats agree because there is one byte sequence per value and no fallback that could
;;; differ between them.  So a value outside the spec has to stop the digest.  Falling
;;; back on `pr-str` or on identity would mint a locator a second seat computes
;;; differently, which is worse than the refusal in exactly the way a silent wrong
;;; address is worse than a loud missing one.

(deftest a-value-the-encoding-does-not-cover-refuses-rather-than-hashing-it
  (let [seat (fresh-seat :uncanonical)]
    (try
      (doseq [[what value] [["a map" {:a 1}] ["a set" #{1 2}] ["a Date" (java.util.Date. 0)]]]
        (testing (str what " is refused where the digest is computed")
          (let [d (try (d/locate seat (list 'grade 'Essay value) 'CxS)
                       nil
                       (catch clojure.lang.ExceptionInfo e (ex-data e)))]
            (is (= :koinii/uncanonical-value (:type d)))
            (is (= (class value) (:class d))
                "naming the class, since the value is what the caller has to change"))))
      (testing "the store refuses one too, so the encoder's guard covers a value that
                reached a sentence some other way rather than a value anyone can assert"
        (let [d (try (v/assert seat '(grade Essay {:a 1}) 'CxS)
                     nil
                     (catch clojure.lang.ExceptionInfo e (ex-data e)))]
          (is (= :not-encodable (:type d)))))
      (testing "and the seat still commits — one refused value is not a poisoned seat"
        (v/assert seat '(grade Essay 3) 'CxS)
        (is (re-matches #"sha256:[0-9a-f]{64}" (d/commit-id seat))))
      (finally (tu/clear-kb! seat)))))

;;; ── commit-id folds derived sentexes; state-root survives nil provenance ──

(deftest commit-id-covers-derived-records-and-state-root-tolerates-nil-provenance
  (let [a (fresh-seat :derive)]
    (try
      (v/assert a (list 'set/forwardRule (vr/rule-sentence [(list 'bird '?x)]
                                                           (list 'flies '?x))) 'CxS)
      (v/assert a '(bird Tweety) 'CxS)
      (let [derived (first (filter #(= '(flies Tweety) (:sentence (v/sentex a %)))
                                   (p/sentex-ids (:records a))))]
        (testing "the forward-derived fact is stored with no provenance"
          (is (some? derived) "the rule fired")
          (is (nil? (v/provenance a derived)) "a derived record carries no creator"))
        (testing "commit-id folds it in and does not throw"
          (is (re-matches #"sha256:[0-9a-f]{64}" (d/commit-id a)))
          (is (some? (d/inclusion-proof a (d/locator-of a derived)))
              "the derived leaf is in the commit tree"))
        (testing "state-root tolerates the nil provenance (leaf is [nil nil identity])"
          (is (re-matches #"sha256:[0-9a-f]{64}" (d/state-root a)))))
      (finally (tu/clear-kb! a)))))

;;; ── the commit identity is BELIEF, not storage ────────────────────────
;;; A defeated default is retained on purpose and is no part of what the seat holds, so it
;;; is no part of what the seat commits to: two seats agreeing on every belief must agree
;;; on the id however differently their stores were built.

(deftest a-defeated-record-is-no-part-of-the-commit
  (let [a (fresh-seat :belief-a)
        b (fresh-seat :belief-b)]
    (try
      ;; both seats know exactly the same two things, with identical provenance so the
      ;; state roots are comparable too
      (binding [v/*clock* (constantly 1750000000000)]
        (doseq [seat [a b]]
          (v/assert seat '(not (chirps Rex)) 'CxS {:strength :monotonic :creator 'AgentAtlas})
          (v/assert seat '(barks Rex) 'CxS {:strength :monotonic :creator 'AgentAtlas})))
      (let [cid0  (d/commit-id a)
            root0 (d/state-root a)
            ;; a default the monotonic negative beats: stored on a, believed by nobody
            defeated (v/assert a '(chirps Rex) 'CxS {:creator 'AgentBoreas})]
        (testing "the fixture really stored a record the seat does not believe"
          (is (some? (v/sentex a defeated)) "it is in the store")
          (is (false? (v/believed? a defeated)) "and defeated by the monotonic negative"))
        (testing "a defeated record moves neither the commit id nor the state root"
          (is (= cid0 (d/commit-id a)))
          (is (= root0 (d/state-root a))))
        (testing "so two seats with the same belief and different stored sets agree"
          (is (< (count (p/sentex-ids (:records b))) (count (p/sentex-ids (:records a))))
              "the fixture gave them genuinely different stored sets")
          (is (= (d/commit-id a) (d/commit-id b)) "the same knowledge is one commit id")
          (is (= (d/state-root a) (d/state-root b)) "and one snapshot"))
        (testing "an unbelieved record has no leaf, so there is no inclusion proof for it"
          (is (nil? (d/inclusion-proof a (d/locator-of a defeated))))
          (is (some? (d/inclusion-proof a (d/locate a '(barks Rex) 'CxS)))
              "a believed record still proves, against the same root")
          (is (true? (d/verify-inclusion (d/locate a '(barks Rex) 'CxS)
                                         (d/inclusion-proof a (d/locate a '(barks Rex) 'CxS))
                                         (d/commit-id a)))))
        (testing "and dereference agrees with the proof, because it reads belief"
          ;; `handle-of` and `handles` are STORAGE reads; the commit family enumerates
          ;; belief.  Left unfiltered, a defeated record resolves here while answering no
          ;; inclusion proof — one seat, two answers about what it holds.
          (let [mk (d/marker a defeated)]
            (is (false? (:resolved? (d/dereference a mk))))
            (is (= :not-believed (:reason (d/dereference a mk)))
                "handed the sentence, dereference names which absence it is")
            (is (some? (v/handle-of a '(chirps Rex) 'CxS))
                "and the record is still stored — this is belief, not a retraction")))
        (testing "and reviving it moves the id — belief is what the id follows"
          (v/retract! a (v/handle-of a '(not (chirps Rex)) 'CxS))
          (is (true? (v/believed? a defeated)) "the default is believed once its defeater is gone")
          (is (not= cid0 (d/commit-id a)))
          (is (some? (d/inclusion-proof a (d/locator-of a defeated))))
          (is (true? (:resolved? (d/dereference a (d/marker a defeated))))
              "and it resolves again, with the leaf it now has")))
      (finally (tu/clear-kb! a) (tu/clear-kb! b)))))

;;; ── publish! requires :compression :none ──────────────────────────────

(deftest publish-refuses-a-compression-that-would-cost-byte-stability
  (let [a   (fresh-seat :fixed-compression)
        dir (tu/temp-dir "koinii-deref-" "fixed-compression" "-")]
    (tu/rm-rf! dir)
    (try
      (atlas-writes! a)
      (testing "the byte-stability claim is not a default a caller can override"
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"requires :compression :none"
                              (d/publish! a dir {:compression :gzip})))
        (is (= :koinii/compression-fixed
               (:type (ex-data (try (d/publish! a dir {:compression :gzip})
                                    (catch clojure.lang.ExceptionInfo e e)))))))
      (testing "asking for what it already is is allowed, and other opts pass through"
        (is (some? (d/publish! a dir {:compression :none})))
        (is (.exists ^File (io/file dir "sentexes.nippy.stream"))))
      (finally (tu/clear-kb! a) (tu/rm-rf! dir)))))

;;; ── verify-inclusion fails closed on a malformed (untrusted) proof ────

(deftest verify-inclusion-rejects-malformed-proofs-without-throwing
  (let [a (fresh-seat :vi)]
    (try
      (v/assert a '(likes Alpha Beta) 'CxS)
      (v/assert a '(likes Beta Gamma) 'CxS)
      (let [loc  (d/locate a '(likes Alpha Beta) 'CxS)
            root (d/commit-id a)
            good (d/inclusion-proof a loc)]
        (testing "the genuine proof verifies"
          (is (true? (d/verify-inclusion loc good root))))
        (testing "a malformed proof returns false, never throws — it is untrusted transport data"
          (is (false? (d/verify-inclusion loc [{:hash "zzzz" :side :right}] root)) "non-hex sibling")
          (is (false? (d/verify-inclusion loc [{:side :right}] root)) "missing :hash")
          (is (false? (d/verify-inclusion loc [{:hash (-> good first :hash) :side :up}] root)) "bad :side")
          (is (false? (d/verify-inclusion loc "not-a-proof" root)) "non-sequential proof")
          (is (false? (d/verify-inclusion loc good "sha256:deadbeef")) "wrong root")))
      (finally (tu/clear-kb! a)))))

;; ── a marker over a handle that names no record ───────────────────────────

(deftest marker-refuses-a-handle-that-names-no-record
  (let [a (fresh-seat :nomark)]
    (try
      (testing "a marker can only be minted for an assertion the seat actually holds"
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"no sentex at handle"
                              (d/marker a 999999))))
      (finally (tu/clear-kb! a)))))

;; ── the leaf sort builds no hex keys ──────────────────────────────────────

(deftest the-leaf-sort-orders-bytes-without-building-hex-keys
  ;; `sort-by` runs its keyfn inside the comparator, so `(sort-by hex leaves)` rebuilds
  ;; the 64-char key — 32 Formatter allocations each — ~2·n·log₂n times on the path
  ;; `commit-id` folds every believed sentex through.  Equal-width digests order the
  ;; same way under unsigned byte comparison as under their hex spelling, so the sort
  ;; needs no hex at all; this asserts both halves: no superlinear hex builds, and the
  ;; order is still exactly hex order.
  (let [locators (mapv #(str "probe:" %) (range 16))
        real-hex @#'d/hex
        calls    (atom 0)]
    (let [leaves (with-redefs-fn {#'d/hex (fn [b] (swap! calls inc) (real-hex b))}
                   #(@#'d/sorted-leaves locators))]
      (is (<= @calls (count locators))
          "the sort builds at most one key per leaf, never one per comparison")
      (is (= (sort (map real-hex leaves)) (map real-hex leaves))
          "and the digests come back in hex order, which is what makes the root a function of the set"))))
