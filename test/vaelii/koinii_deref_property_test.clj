;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.koinii-deref-property-test
  "Generative property tests for koinii cross-seat dereference
  (`vaelii.koinii.deref`): the invariants the example-based
  `koinii_deref_test` asserts on a handful of hand-built scenarios, restated as
  test.check properties over randomly generated assertions.

  Every fact is drawn from three SMALL fixed pools — camelCase predicates,
  CapitalCamelCase individuals, Cx-prefixed contexts — so vaelii's naming check
  never refuses a generated assertion, and so the same predicates/individuals
  recur across facts and structural collisions (same locator from two routes to
  one assertion, distinct locators from distinct assertions) are actually
  exercised rather than assumed away by unique gensyms.

  What each `defspec` asserts:

  - `locator-is-content-addressed-and-handle-independent` — a locator is a
    function of the assertion, agreeing across two independent seats that reached
    it among different noise, and matching `sha256:<64 hex>`.
  - `locators-are-injective-over-the-sample` — distinct assertions get distinct
    locators; context, polarity and sentence each move the locator.
  - `encoder-is-deterministic-and-print-var-independent` — the canonical encoder
    ignores ambient `*print-*` vars (it is not `pr-str`).
  - `commit-id-is-an-order-independent-function-of-state` — a Merkle root over the
    *set*, so order does not move it and a superset does.
  - `a-conversation-with-replies-commits-alike-in-two-orders` — the order-independence
    above over sentences that name other sentexes by `(sentexHandle n)`, the shape every
    koinii response act has: replies (and replies to replies) built on two seats that
    minted different handles digest alike, and each reply's marker resolves on the other
    seat.
  - `rules-and-defaults-locate-alike-on-two-seats-loaded-in-different-orders` — forward
    rules and facts at both strengths, loaded on two seats in two orders: the seats commit
    alike, and each premise's sentence on one seat finds the record on the other
    (`v/handle-of`) whose digest is the same.
  - `commit-id-is-knowledge-and-state-root-is-snapshot` — content vs. provenance:
    same facts under different provenance share a `commit-id` but not a `state-root`.
  - `inclusion-proofs-are-sound-and-complete` — every believed locator's proof
    verifies against the real root and is rejected against a wrong root, a tampered
    sibling, or when the locator is absent.
  - `the-commit-identity-is-belief-not-storage` — a stored-but-defeated record is no
    leaf: a seat holding it and a seat that never heard of it compute one commit id,
    one state root, and no inclusion proof for it.
  - `markers-are-untrusted` — a genuine marker resolves to its asserting creator; a
    tampered locator is `:locator-mismatch`; an unreceived sentence is `:not-received`;
    and every way of corrupting a marker on the wire is ANSWERED `:malformed` with the
    problem naming the part, never thrown out of the resolve path.

  Cleanup is required: memory seats share a process-global store keyed by
  `:space`, so every seat is opened on its OWN space (already cleared by
  `fresh-seat`) and cleared again in a `finally`.  A `:once` teardown wipes every
  space this namespace touched, so nothing leaks into a later namespace."
  (:require [clojure.test :refer [use-fixtures]]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [vaelii.core :as v]
            [vaelii.koinii.deref :as d]
            [vaelii.test-util :as tu]))

;;; ── seats: independent in-RAM KBs, each on its own space ──────────────────

(defn- fresh-seat
  "An independent in-RAM seat — a cleared `:memory` KB on its own derived space, so
  it shares a store with no other seat.  `fresh-seat` clears on open; clear it again
  in a `finally`."
  [tag]
  (doto (v/open-kb (assoc tu/plain-memory-space :space [::seat (name tag)]))
    (tu/clear-kb!)))

(defn- with-seat
  "Open one cleared seat on `tag`'s space, run `(f seat)`, clear it in a `finally`.
  Returns `f`'s value (a property's truthy/falsey result)."
  [tag f]
  (let [seat (fresh-seat tag)]
    (try (f seat)
         (finally (tu/clear-kb! seat)))))

(defn- with-two-seats
  "Open two cleared seats on DISTINCT spaces, run `(f a b)`, clear both in a
  `finally`.  Two seats in one trial must never share a space, or the second's
  content leaks into the first."
  [tag-a tag-b f]
  (let [a (fresh-seat tag-a)
        b (fresh-seat tag-b)]
    (try (f a b)
         (finally (tu/clear-kb! a) (tu/clear-kb! b)))))

;; Every space this namespace opens.  The `:once` teardown wipes each one so a
;; generated assertion left by the last trial cannot leak into a later namespace
;; that happens to open the same derived space.
(def ^:private seat-tags
  [:loc-a :loc-b :inj :enc :cid-a :cid-b :split-a :split-b :split-c :split-d
   :proof :marker :belief-a :belief-b :reply-a :reply-b :rule-a :rule-b])

(use-fixtures :once
  (fn [f]
    (try (f)
         (finally (doseq [t seat-tags] (tu/clear-kb! (fresh-seat t)))))))

;;; ── the pools and the fact generators ────────────────────────────────────

;; Bare lowercase predicates, CapitalCamelCase individuals, Cx-prefixed contexts —
;; each satisfies vaelii's naming invariant for its role, so a generated fact is always
;; assertable.  Bare rather than camelCase because the generator mints unary *and*
;; binary facts from one pool, and a bare lowercase word is the one spelling legal at
;; both arities: snake_case is arity 1 and camelCase arity 2+ (docs/naming.md).
;; Small pools on purpose: facts collide.
(def ^:private predicates '[hosts connects likes serves])
(def ^:private individuals '[Alpha Beta Gamma Delta])
(def ^:private contexts '[CxOne CxTwo CxThree])

(def ^:private gen-fact
  "A ground unary `(pred ind)` or binary `(pred ind ind)` fact over the pools."
  (gen/let [pred (gen/elements predicates)
            args (gen/one-of [(gen/fmap vector (gen/elements individuals))
                              (gen/tuple (gen/elements individuals)
                                         (gen/elements individuals))])]
    (apply list pred args)))

(def ^:private gen-fact+ctx
  "A `[fact context]` pair — the unit an assertion is keyed on."
  (gen/tuple gen-fact (gen/elements contexts)))

(defn- gen-permutation
  "A generator of a uniformly random permutation of `coll` (version-independent —
  it does not lean on a particular test.check `shuffle` combinator)."
  [coll]
  (if (empty? coll)
    (gen/return [])
    (gen/let [i   (gen/choose 0 (dec (count coll)))
              rst (gen-permutation (into (subvec (vec coll) 0 i)
                                         (subvec (vec coll) (inc i))))]
      (into [(nth coll i)] rst))))

(def ^:private gen-distinct-pairs
  "A non-empty vector of DISTINCT `[fact context]` pairs (1–8 of them)."
  (gen/vector-distinct gen-fact+ctx {:min-elements 1 :max-elements 8}))

(def ^:private gen-pairs-and-perm
  "Distinct pairs paired with one reordering of them, for the order-independence
  property."
  (gen/let [pairs gen-distinct-pairs
            perm  (gen-permutation pairs)]
    [pairs perm]))

;;; ── small helpers ─────────────────────────────────────────────────────────

(defn- assert-all!
  "Assert every `[fact context]` in `pairs` into `seat` (default provenance)."
  [seat pairs]
  (doseq [[f c] pairs] (v/assert seat f c)))

(defn- wrong-root
  "A syntactically valid `sha256:` root that differs from `root` — an all-zeros
  root, or all-f if `root` happens to be the all-zeros one."
  [root]
  (let [z (str "sha256:" (apply str (repeat 64 \0)))
        o (str "sha256:" (apply str (repeat 64 \f)))]
    (if (= root z) o z)))

(defn- tamper-locator
  "Flip one hex digit of `locator`'s digest body, leaving the `\"sha256:\"` tag intact — so
  the result is still a WELL-FORMED locator, just not the one the seat computes, and it is
  the rehash that rejects it (`:locator-mismatch`).  Mangling the tag instead would make it
  no locator at all, which the resolvers refuse earlier and differently (`:malformed`)."
  [locator]
  (let [body (subs locator (count "sha256:"))]
    (str "sha256:" (if (= \0 (first body)) \1 \0) (subs body 1))))

(defn- tamper-first-sibling
  "Flip one hex digit of the first sibling hash in a non-empty audit path, so the
  recomputed root no longer matches."
  [proof]
  (let [p (vec proof)
        h (get-in p [0 :hash])]
    (assoc-in p [0 :hash] (str (if (= \0 (first h)) \1 \0) (subs h 1)))))

;;; ── 1. content-addressing / cross-seat agreement ─────────────────────────

(def ^:private locator-re #"sha256:[0-9a-f]{64}")

(defspec locator-is-content-addressed-and-handle-independent 80
  (prop/for-all [target  gen-fact+ctx
                 noise-a (gen/vector gen-fact+ctx 0 6)
                 noise-b (gen/vector gen-fact+ctx 0 6)]
                (with-two-seats :loc-a :loc-b
                  (fn [a b]
                    ;; the target lands among different noise in each seat, so its handles differ
                    (assert-all! a (conj (vec noise-a) target))
                    (assert-all! b (into [target] noise-b))
                    (let [[f c] target
                          ha (v/handle-of a f c)
                          hb (v/handle-of b f c)
                          la (d/locator-of a ha)]
                      (and (= la (d/locator-of b hb))                       ; agrees across seats
                           (= (d/locate a f c) (d/locator-of a (v/handle-of a f c)))
                           (boolean (re-matches locator-re la))))))))

;;; ── 2. injectivity over the sample ───────────────────────────────────────

(defspec locators-are-injective-over-the-sample 80
  (prop/for-all [pairs gen-distinct-pairs]
                (with-seat :inj
                  (fn [seat]
                    (assert-all! seat pairs)
                    (let [locs (map (fn [[f c]] (d/locate seat f c)) pairs)
                          ;; a representative pair, and one-field mutations of it
                          [f c]   (first pairs)
                          other-c (first (filter #(not= % c) contexts))
                          other-f (apply list (first (filter #(not= % (first f)) predicates))
                                         (rest f))
                          base    (d/locate seat f c)]
                      (and
                       ;; distinct assertions ⇒ distinct locators, no collisions in the sample
                       (= (count pairs) (count (distinct locs)))
                       ;; context, polarity and sentence each change the locator
                       (not= base (d/locate seat f other-c))
                       (not= base (d/locate seat (list 'not f) c))
                       (not= base (d/locate seat other-f c))))))))

;;; ── 3. encoder determinism & print-var independence ──────────────────────

(defspec encoder-is-deterministic-and-print-var-independent 80
  (prop/for-all [target gen-fact+ctx
                 noise  (gen/vector gen-fact+ctx 0 6)]
                (with-seat :enc
                  (fn [seat]
                    (let [[f c] target]
                      (assert-all! seat (conj (vec noise) target))
                      (let [h     (v/handle-of seat f c)
                            l1    (d/locate seat f c)
                            l2    (d/locator-of seat h)
                            root1 (d/commit-id seat)
                            ;; hostile print vars: pr-str would truncate/alter, the encoder must not
                            [l3 root3] (binding [*print-length* 1 *print-level* 1 *print-meta* true]
                                         [(d/locate seat f c) (d/commit-id seat)])]
                        (and (= l1 l2 l3) (= root1 root3))))))))

;;; ── 4. commit-id: an order-independent function of state ──────────────────

(defspec commit-id-is-an-order-independent-function-of-state 60
  (prop/for-all [[pairs perm] gen-pairs-and-perm
                 extra        gen-fact+ctx]
                (with-two-seats :cid-a :cid-b
                  (fn [a b]
                    (assert-all! a pairs)
                    (assert-all! b perm)                       ; same set, reached in another order
                    (let [order-independent? (= (d/commit-id a) (d/commit-id b))
                          cid-b              (d/commit-id b)
                          [ef ec]            extra
                          new?               (nil? (v/handle-of b ef ec))]
                      (v/assert b ef ec)                        ; a strict superset (when genuinely new)
                      (and order-independent?
                           (if new?
                             (not= cid-b (d/commit-id b))
                             true)))))))

;;; ── 4b. the same over replies: sentences that name a sentex by handle ─────

(def ^:private gen-replies
  "0–6 replies, each `[individual target-index context]`: a `(respondsTo ind (sentexHandle
  h))` naming the record at `target-index` (mod the records before it — the facts, then
  the earlier replies), so replies to replies occur."
  (gen/vector (gen/tuple (gen/elements individuals) gen/nat (gen/elements contexts)) 0 6))

(defn- reply!
  "Assert `replies` into `seat` after the facts whose handles are `facts`, returning the
  handle of every item in order (facts first).  A reply names the handle its target
  landed at on THIS seat."
  [seat facts replies]
  (reduce (fn [hs [ind idx c]]
            (let [target (nth hs (mod idx (count hs)))]
              (conj hs (v/assert seat (list 'respondsTo ind (v/sentex-handle target)) c))))
          facts replies))

(defspec a-conversation-with-replies-commits-alike-in-two-orders 60
  (prop/for-all [pairs   gen-distinct-pairs
                 replies gen-replies]
                (with-two-seats :reply-a :reply-b
                  (fn [a b]
                    (let [ha   (reply! a (mapv (fn [[f c]] (v/assert a f c)) pairs) replies)
                          ;; seat B mints one throwaway handle first and takes the facts in
                          ;; reverse, so the handles it mints differ from seat A's
                          junk (v/assert b '(hosts Omega Omega) 'CxOne)
                          hb   (reply! b (vec (rseq (mapv (fn [[f c]] (v/assert b f c))
                                                          (reverse pairs))))
                                       replies)]
                      (v/retract! b junk)
                      (and (= (d/commit-id a) (d/commit-id b))
                           (every? true?
                                   (map (fn [x y]
                                          (let [r (d/dereference b (d/marker a x))]
                                            (and (:resolved? r) (= y (:handle r))
                                                 (= (d/locator-of a x) (d/locator-of b y)))))
                                        (drop (count pairs) ha) (drop (count pairs) hb)))))))))

;;; ── 4c. the same over rules and defaults ──────────────────────────────────

(def ^:private gen-item
  "A fact or a forward rule over the unary predicates, at `:default` or `:monotonic`:
  `[sentence context strength]`."
  (gen/let [strength (gen/elements [:default :monotonic])
            c        (gen/elements contexts)
            rule?    gen/boolean
            [p q]    (gen/vector-distinct (gen/elements predicates) {:num-elements 2})
            ind      (gen/elements individuals)]
    [(if rule?
       (list 'set/forwardRule (list 'implies (list p '?x) (list q '?x)))
       (list p ind))
     c strength]))

(def ^:private gen-items-and-perm
  (gen/let [items (gen/vector-distinct gen-item {:min-elements 1 :max-elements 8})
            perm  (gen-permutation items)]
    [items perm]))

(defspec rules-and-defaults-locate-alike-on-two-seats-loaded-in-different-orders 40
  (prop/for-all [[items perm] gen-items-and-perm]
                (with-two-seats :rule-a :rule-b
                  (fn [a b]
                    (doseq [[s c strength] items] (v/assert a s c {:strength strength}))
                    (doseq [[s c strength] perm] (v/assert b s c {:strength strength}))
                    (and (= (d/commit-id a) (d/commit-id b))
                         (every? (fn [h]
                                   (let [sa (v/sentex a h)
                                         hb (v/handle-of b (v/sentence-of sa) (:context sa))]
                                     (and hb
                                          (= (v/digest a h) (v/digest b hb))
                                          (= (v/sentence-of sa) (v/sentence-of (v/sentex b hb))))))
                                 (filter #(v/premise? a %) (v/handles a))))))))

;;; ── 5. the knowledge / snapshot split (commit-id vs state-root) ───────────

(defspec commit-id-is-knowledge-and-state-root-is-snapshot 60
  (prop/for-all [pairs gen-distinct-pairs]
                (let [;; SAME facts+contexts, DIFFERENT provenance (creator and clock)
                      diff-prov
                      (with-two-seats :split-a :split-b
                        (fn [a b]
                          (binding [v/*clock* (constantly 1000)]
                            (doseq [[f c] pairs] (v/assert a f c {:creator 'AgentA})))
                          (binding [v/*clock* (constantly 2000)]
                            (doseq [[f c] pairs] (v/assert b f c {:creator 'AgentB})))
                          (and (= (d/commit-id a) (d/commit-id b))       ; same knowledge
                               (not= (d/state-root a) (d/state-root b))))) ; different snapshot
                      ;; IDENTICAL provenance ⇒ both roots equal
                      same-prov
                      (with-two-seats :split-c :split-d
                        (fn [a b]
                          (binding [v/*clock* (constantly 1000)]
                            (doseq [[f c] pairs] (v/assert a f c {:creator 'AgentA})))
                          (binding [v/*clock* (constantly 1000)]
                            (doseq [[f c] pairs] (v/assert b f c {:creator 'AgentA})))
                          (and (= (d/commit-id a) (d/commit-id b))
                               (= (d/state-root a) (d/state-root b)))))]
                  (and diff-prov same-prov))))

;;; ── 6. inclusion-proof soundness & completeness ──────────────────────────

(defspec inclusion-proofs-are-sound-and-complete 60
  (prop/for-all [pairs  gen-distinct-pairs
                 absent gen-fact+ctx]
                (with-seat :proof
                  (fn [seat]
                    (assert-all! seat pairs)
                    (let [root     (d/commit-id seat)
                          handles  (map (fn [[f c]] (v/handle-of seat f c)) pairs)
                          locators (distinct (map #(d/locator-of seat %) handles))
                          [af ac]  absent
                          absent-loc (d/locate seat af ac)]
                      (and
                       ;; every stored locator: a proof that verifies, and is rejected against a
                       ;; wrong root and against a tampered sibling
                       (every? (fn [loc]
                                 (let [proof (d/inclusion-proof seat loc)]
                                   (and proof
                                        (d/verify-inclusion loc proof root)
                                        (not (d/verify-inclusion loc proof (wrong-root root)))
                                        (or (empty? proof)
                                            (not (d/verify-inclusion loc (tamper-first-sibling proof)
                                                                     root))))))
                               locators)
                       ;; a locator absent from the KB ⇒ no proof, and verify false.  (Guard: the
                       ;; "absent" pair may, from small pools, actually be one we stored.)
                       (if (nil? (v/handle-of seat af ac))
                         (and (nil? (d/inclusion-proof seat absent-loc))
                              (not (d/verify-inclusion absent-loc [] root)))
                         true)))))))

;;; ── 7. tamper / non-receipt in dereference ───────────────────────────────

(def ^:private marker-creator 'AgentZeta)

(def ^:private gen-corruption
  "One way a marker can arrive corrupted over the transport, as a `[corrupt expected]`
  pair: the mutation, and the `:problem` `dereference` must name for it.  Every one of
  these is answered — the property fails by THROWING if any reaches the engine unchecked,
  which is what a peer sending a malformed sentence would otherwise do to the seat."
  (gen/elements
   [[#(assoc % :sentence [1 2])       :shape]                ; a vector the engine will not read
    [#(assoc % :sentence '(or (p A) (q B))) :shape]          ; a disjunctive goal
    [#(assoc % :context 'CxInference) :unsupported-context]  ; names no stored sentex
    [#(assoc % :locator "sha256:aa")  :locator]              ; not 64 hex
    [#(assoc % :locator 42)           :locator]              ; not even a string
    [#(dissoc % :sentence)            :no-sentence]
    [#(dissoc % :context)             :no-context]
    [(constantly "not-a-marker")      :not-a-map]
    [(constantly nil)                 :not-a-map]]))

(defspec markers-are-untrusted 80
  (prop/for-all [pairs      gen-distinct-pairs
                 idx        gen/nat
                 absent     gen-fact+ctx
                 corruption gen-corruption]
                (with-seat :marker
                  (fn [seat]
                    (doseq [[f c] pairs] (v/assert seat f c {:creator marker-creator}))
                    (let [[f c]    (nth pairs (mod idx (count pairs)))
                          h        (v/handle-of seat f c)
                          mk       (d/marker seat h)
                          genuine  (d/dereference seat mk)
                          ;; a well-formed locator with one digit flipped: stored, but the
                          ;; marker's locator no longer matches what the KB recomputes
                          tampered (d/dereference seat (assoc mk :locator (tamper-locator (:locator mk))))
                          [corrupt expected] corruption
                          garbled  (d/dereference seat (corrupt mk))
                          [af ac]  absent]
                      (and (:resolved? genuine)
                           (= marker-creator (:seat genuine))
                           (false? (:resolved? tampered))
                           (= :locator-mismatch (:reason tampered))
                           ;; a corrupted marker is answered, with the part named — and a
                           ;; refusal is never confused with an absence
                           (false? (:resolved? garbled))
                           (= :malformed (:reason garbled))
                           (= expected (:problem garbled))
                           ;; a sentence the seat never received ⇒ :not-received (guard: the
                           ;; "absent" pair may actually be stored)
                           (if (nil? (v/handle-of seat af ac))
                             (let [r (d/dereference seat (assoc mk :sentence af :context ac))]
                               (and (= :not-received (:reason r)) (nil? (:problem r))))
                             true)))))))

;;; ── 8. the commit identity is belief, not storage ────────────────────────
;;; Seat A stores a defeated default for every generated fact; seat B never heard of one.
;;; Same belief, different stores — so the same commit id, the same state root, and no
;;; inclusion proof for a leaf that is not in the tree.

(defspec the-commit-identity-is-belief-not-storage 40
  (prop/for-all [pairs gen-distinct-pairs]
                (with-two-seats :belief-a :belief-b
                  (fn [a b]
                    ;; identical provenance on the believed half, so `state-root` compares
                    (binding [v/*clock* (constantly 1000)]
                      (doseq [seat [a b] [f c] pairs]
                        (v/assert seat (list 'not f) c {:strength :monotonic
                                                        :creator 'AgentA})))
                    (let [cid  (d/commit-id a)
                          root (d/state-root a)
                          ;; each positive is beaten by the monotonic negative beside it
                          defeated (doall (for [[f c] pairs]
                                            (v/assert a f c {:creator 'AgentB})))]
                      (and (every? #(and (some? (v/sentex a %)) (false? (v/believed? a %))) defeated)
                           (= cid (d/commit-id a))                 ; the store grew, belief did not
                           (= root (d/state-root a))
                           (= (d/commit-id a) (d/commit-id b))     ; and the seats still agree
                           (= (d/state-root a) (d/state-root b))
                           (every? #(nil? (d/inclusion-proof a (d/locator-of a %))) defeated)
                           ;; dereference reads the same set the proof does: whatever has
                           ;; no leaf resolves nowhere
                           (every? (fn [h]
                                     (= (some? (d/inclusion-proof a (d/locator-of a h)))
                                        (boolean (:resolved? (d/dereference a (d/marker a h))))))
                                   (concat defeated (filter #(v/believed? a %) (v/handles a))))))))))
