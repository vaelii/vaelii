;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.prefetch-test
  "`resolution/*prefetch-candidates*` — the hint a retrieval path gives its record store
  before walking a chunk of candidates.

  The engine's own stores do not implement `protocols/Prefetching`: a record fetch on the
  RAM and disk backends is a page touch, and there is nothing a batch could save.  So the
  mechanism is tested here against a **wrapper that records what it was hinted**, which is
  what lets core state the two properties that matter without a database in the room:

  - **it cannot change an answer.**  The hint returns nothing and every record still
    arrives through `get-sentex`, so the answer set is identical on and off — asserted on
    both retrieval paths, since a positive literal takes the set-algebra one by default
    and the `match-one` fan-out is the reference behind it;
  - **it is bounded by the chunk.**  A consumer that stops at the first solution has
    hinted one chunk and not the extent, which is the whole of what makes the setting
    cheap to leave on.

  A store with no capability is the third property and the default one: the setting is
  inert, because `prefetcher` answers nil and the walk is the walk it always was."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.special :as special]
            [vaelii.impl.types.reasoning :as reasoning]))

(defn- hinting-store
  "`inner` with `Prefetching` bolted on, recording each hint into `hints` (and each
  justification hint into `j-hints`).  A wrapper
  rather than a redef: a protocol method is dispatched on the value's type, so only a real
  implementation is in the path a compiled caller takes."
  ([inner hints] (hinting-store inner hints (atom [])))
  ([inner hints j-hints]
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
     (sentex-ids [_] (p/sentex-ids inner))
     (justification-ids [_] (p/justification-ids inner))
     (mark-premise [_ id s] (p/mark-premise inner id s))
     (unmark-premise! [_ id] (p/unmark-premise! inner id))
     (premise-ids [_] (p/premise-ids inner))
     (premise-strength [_ id] (p/premise-strength inner id))
     (clear-records! [_] (p/clear-records! inner))
     p/Prefetching
     (prefetch-sentexes! [_ ids] (swap! hints conj (vec ids)) nil)
     (prefetch-justifications! [_ ids] (swap! j-hints conj (vec ids)) nil))))

(defn- populated
  "A KB with `n` facts under each of two predicates, and its hint log."
  [n]
  (let [kb    (v/open-kb {:backend :memory :space (gensym "prefetch")})
        _     (doseq [i (range n)]
                (v/assert kb (list 'rel (symbol (str "Ind" i))) 'CxPrefetch)
                (v/assert kb (list 'other (symbol (str "Ind" i))) 'CxPrefetch))
        hints (atom [])]
    [(assoc kb :records (hinting-store (:records kb) hints)) hints]))

(defn- answer-set [kb sentence]
  (set (map (fn [[h b]] [h b]) (res/matches-visible kb sentence 'CxPrefetch))))

;; ---- it cannot change an answer -----------------------------------------

(deftest the-hint-does-not-move-the-answer-set
  (let [[kb _] (populated 200)]
    (doseq [sentence ['(rel ?x) '(rel Ind7) '(?p Ind7) '(other ?x)]]
      (testing (str sentence)
        (let [off (binding [res/*prefetch-candidates* false] (answer-set kb sentence))
              on  (binding [res/*prefetch-candidates* 16]    (answer-set kb sentence))]
          (is (seq off) "the fixture answers this at all")
          (is (= off on) "identical with the hint on"))))))

(deftest the-hint-does-not-move-the-answer-on-either-retrieval-path
  ;; a positive literal takes the set-algebra path by default and the `match-one` fan-out
  ;; is the reference behind it; the hint wraps the candidates of both, so both are held
  ;; to the same set here rather than only the one a default query happens to take.
  (let [[kb _] (populated 200)]
    (doseq [sentence ['(rel ?x) '(rel Ind3)]]
      (testing (str sentence)
        (let [algebra (binding [res/*hierarchical-retrieval* true
                                res/*prefetch-candidates*    16]
                        (answer-set kb sentence))
              fan-out (binding [res/*hierarchical-retrieval* false
                                res/*prefetch-candidates*    16]
                        (answer-set kb sentence))
              plain   (binding [res/*hierarchical-retrieval* false
                                res/*prefetch-candidates*    false]
                        (answer-set kb sentence))]
          (is (= plain fan-out) "the fan-out answers the same hinted and not")
          (is (= plain algebra) "and the set-algebra path agrees with it"))))))

;; ---- it is bounded by the chunk -----------------------------------------

(defn- hinted-for-one-solution
  "How many handles the store was hinted when the consumer took **one** solution out of an
  extent of `n`."
  [n]
  (let [[kb hints] (populated n)]
    (reset! hints [])
    (binding [res/*prefetch-candidates* 16]
      ;; one element realized and dropped — a consumer that stops early, not a read of
      ;; which match comes first
      (dorun (take 1 (res/matches-visible kb '(rel ?x) 'CxPrefetch))))
    {:hints (count @hints)
     :handles (count (mapcat identity @hints))
     :widest (reduce max 0 (map count @hints))}))

(deftest a-consumer-that-stops-early-hints-a-bounded-prefix
  ;; The property that makes the setting cheap to leave on: what a stopping consumer costs
  ;; is a function of the CHUNK and not of the extent.  So it is asserted as exactly that
  ;; — the same three extents, the same hint count — rather than as a number that happens
  ;; to hold at one size.  (The constant is the lazy seq's own read-ahead, not one chunk:
  ;; `mapcat` over the chunks realizes a few before the first answer escapes.)
  (let [small (hinted-for-one-solution 100)
        mid   (hinted-for-one-solution 500)
        big   (hinted-for-one-solution 2000)]
    (is (pos? (:hints small)) "the store was hinted at all")
    (is (= (:hints small) (:hints mid) (:hints big))
        "the same number of chunks whether the extent is 100, 500 or 2000")
    (is (= (:handles small) (:handles mid) (:handles big))
        "…so the same number of handles, and the extent does not enter into it")
    (is (< (:handles big) 2000)
        "which is emphatically not the extent")
    (is (<= (:widest big) 16) "and no hint is larger than the chunk")))

(deftest a-full-walk-hints-the-whole-extent-in-chunks
  (let [[kb hints] (populated 200)]
    (reset! hints [])
    (binding [res/*prefetch-candidates* 16]
      (is (= 200 (count (res/matches-visible kb '(rel ?x) 'CxPrefetch)))))
    (is (= 200 (count (distinct (mapcat identity @hints))))
        "every candidate was hinted exactly once, across the chunks")
    (is (every? #(<= (count %) 16) @hints)
        "and each hint is one chunk")))

(deftest the-hint-carries-only-believed-handles
  ;; the store is never asked to warm a record the walk would skip, so a retracted
  ;; sentex's handle does not appear in a hint.
  (let [[kb hints] (populated 50)
        h (v/handle-of kb '(rel Ind7) 'CxPrefetch)]
    (v/retract! kb h)
    (reset! hints [])
    (binding [res/*prefetch-candidates* 64]
      (doall (res/matches-visible kb '(rel ?x) 'CxPrefetch)))
    (is (seq @hints) "the walk happened")
    (is (not (contains? (set (mapcat identity @hints)) h))
        "the retracted handle was filtered out before the hint")))

;; ---- a store with no capability ----------------------------------------

(deftest the-setting-is-inert-without-the-capability
  ;; the default state of every backend the engine ships: `prefetcher` answers nil and
  ;; the walk is the one that was always there.
  (let [kb (v/open-kb {:backend :memory :space (gensym "prefetch")})]
    (doseq [i (range 100)] (v/assert kb (list 'rel (symbol (str "Ind" i))) 'CxPrefetch))
    (is (nil? (cap/prefetcher (:records kb)))
        "the RAM record store implements no Prefetching, so there is nobody to hint")
    (let [off (binding [res/*prefetch-candidates* false] (answer-set kb '(rel ?x)))
          on  (binding [res/*prefetch-candidates* 16]    (answer-set kb '(rel ?x)))]
      (is (= 100 (count off)))
      (is (= off on) "and turning the setting on changes nothing"))))

(defprotocol InlineOnly (inline-op [x]))
(defprotocol Extended (extended-op [x]))
(extend-type String Extended (extended-op [_] :string))

(deftest has-answers-as-satisfies-with-and-without-an-extend
  (let [both (reify InlineOnly (inline-op [_] 1) Extended (extended-op [_] 2))
        xs   [both "s" (Object.) nil]]
    (is (= [true false false false]
           (mapv #(cap/has? InlineOnly %) xs)
           (mapv #(satisfies? InlineOnly %) xs)))
    (is (= [true true false false]
           (mapv #(cap/has? Extended %) xs)
           (mapv #(satisfies? Extended %) xs)))))

(deftest off-is-the-default
  (is (false? res/*prefetch-candidates*)
      "a hint is issued only when something asks for it"))

(deftest a-value-that-is-not-a-chunk-is-refused-where-it-is-bound
  ;; `true` is the guess an off-value of `false` invites, and it is truthy — so without a
  ;; refusal it passes every check on the query path and fails in `cap/hinting`'s `(long n)`,
  ;; several frames into a lazy seq, naming neither the var nor what was bound to it.
  (doseq [v [true nil 0 -1 :always "256" 2.5]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"\*prefetch-candidates\*"
                          (binding [res/*prefetch-candidates* v]
                            res/*prefetch-candidates*))
        (str (pr-str v) " is not a chunk size")))
  (testing "and it refuses in the one vocabulary, so a caller discriminates on the type
            rather than on the message"
    ;; `:unknown-option` is what `vaelii.impl.config` throws for a switch bound outside
    ;; its domain, and a setting is a setting whether it came from a var or the shell.
    (doseq [v [true nil 0 -1 :always "256" 2.5]]
      (let [e (try (binding [res/*prefetch-candidates* v] res/*prefetch-candidates*)
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (= :unknown-option (:type (ex-data e))) (pr-str v))
        (is (= v (:value (ex-data e))) "and names the value it was given"))))
  (testing "the binding form is what throws, not the walk"
    (let [ran (atom false)]
      (is (thrown? clojure.lang.ExceptionInfo
                   (binding [res/*prefetch-candidates* true] (reset! ran true))))
      (is (false? @ran) "so the body never ran, and no query was in flight when it failed")
      (is (false? res/*prefetch-candidates*) "and the setting is what it was")))
  (testing "and the two shapes that are a chunk"
    (is (false? (binding [res/*prefetch-candidates* false] res/*prefetch-candidates*)))
    (is (= 256 (binding [res/*prefetch-candidates* 256] res/*prefetch-candidates*)))))

;; ---- the recovery walks hint unconditionally ---------------------------

(deftest the-recovery-walks-hint-without-a-setting
  ;; `reindex` fetches every live record and `recover` every stored justification, and
  ;; both consume every handle they are given — so a hint there can save round trips and
  ;; cannot waste one, and neither is conditional on `*prefetch-candidates*`.  That is the whole
  ;; difference from the query path, and it is asserted with the setting explicitly OFF.
  (let [kb    (v/open-kb {:backend :memory :space (gensym "prefetch")})
        _     (do (v/assert-rule kb '[(rel ?x)] '(derived ?x) 'CxPrefetch {:direction :forward})
                  (doseq [i (range 50)]
                    (v/assert kb (list 'rel (symbol (str "Ind" i))) 'CxPrefetch)))
        hints   (atom [])
        j-hints (atom [])
        kb2   (assoc kb :records (hinting-store (:records kb) hints j-hints))]
    (binding [res/*prefetch-candidates* false]
      (v/reindex kb2))
    (testing "the record walk was hinted"
      (is (seq @hints))
      (is (= (count (p/sentex-ids (:records kb2)))
             (count (distinct (mapcat identity @hints))))
          "every live record handle, exactly once"))
    (testing "the justification walk was hinted"
      (is (seq @j-hints))
      (is (= (count (p/justification-ids (:records kb2)))
             (count (distinct (mapcat identity @j-hints))))
          "every stored justification handle, exactly once"))))

(deftest a-store-without-the-capability-recovers-unhinted
  ;; the same walks over the engine's own stores: `prefetcher` is nil, so the seq the walk
  ;; consumes is the enumeration itself and nothing is chunked.
  (let [kb (v/open-kb {:backend :memory :space (gensym "prefetch")})]
    (v/assert-rule kb '[(rel ?x)] '(derived ?x) 'CxPrefetch {:direction :forward})
    (doseq [i (range 20)] (v/assert kb (list 'rel (symbol (str "Ind" i))) 'CxPrefetch))
    (is (nil? (cap/prefetcher (:records kb))))
    (is (nil? (cap/justification-prefetcher (:records kb))))
    (is (map? (v/reindex kb)) "and the rebuild runs exactly as it did")))

(deftest a-recover-hints-the-records-its-settle-reads-a-handle-at-a-time
  ;; the membership candidates' entries, the argument holds a recover decides again and
  ;; the forced predicates' sentexes are read a record apiece, and each walk reads every
  ;; handle it is given
  (let [kb    (v/open-kb {:backend :memory :space (gensym "prefetch")})
        _     (do (v/assert kb '(genl prefetch_dog prefetch_animal) 'CxPrefetch)
                  (v/assert kb '(arg ownsPrefetchPet 2 prefetch_animal) 'CxPrefetch)
                  (v/assert-rule kb '[(ownsPrefetchPet ?o ?p)] '(prefetch_owner ?o) 'CxPrefetch)
                  (v/assert kb '(forced_monotonic_predicate prefetchForced) 'CxPrefetch)
                  (doseq [i (range 20)]
                    (let [x (symbol (str "Ind" i))]
                      (v/assert kb (list 'prefetch_dog x) 'CxPrefetch)
                      (v/assert kb (list 'prefetch_pet x) 'CxPrefetch)
                      (v/assert kb (list 'ownsPrefetchPet 'Owner x) 'CxPrefetch)
                      (v/assert kb (list 'prefetchForced 'Owner x) 'CxPrefetch))))
        hints (atom [])
        kb2   (assoc kb :records (hinting-store (:records kb) hints))
        recs  (:records kb)
        of    (fn [f] (into #{} (filter #(= f (first (:sentence (p/get-sentex recs %)))))
                            (p/sentex-ids recs)))]
    (v/recover kb2)
    (let [hinted (set (mapcat identity @hints))]
      (testing "every membership candidate's entries"
        (is (= 20 (count (of 'prefetch_pet))))
        (is (every? hinted (concat (of 'prefetch_dog) (of 'prefetch_pet)))))
      (testing "the rule on the declared predicate, whose argument hold is decided again"
        (is (some #(and (hinted %) (some? (:antecedent (p/get-sentex recs %))))
                  (p/sentex-ids recs))))
      (testing "every sentex of a forced predicate"
        (is (= 20 (count (of 'prefetchForced))))
        (is (every? hinted (of 'prefetchForced)))))))

(deftest the-supporter-pass-hints-every-stored-declaration
  ;; `reindex` reads each stored declaration again after its record walk, a record apiece,
  ;; so the declaration pass hints its own extent
  (let [kb    (v/open-kb {:backend :memory :space (gensym "prefetch")})
        _     (doseq [i (range 20)]
                (v/assert kb (list 'genl (symbol (str "prefetch_kind" i)) 'prefetch_top)
                          'CxPrefetch))
        hints (atom [])
        kb2   (assoc kb :records (hinting-store (:records kb) hints))
        recs  (:records kb)
        genls (into #{} (filter #(= '[genl prefetch_top]
                                    (let [[f _ t] (:sentence (p/get-sentex recs %))] [f t])))
                    (p/sentex-ids recs))]
    (special/post-taxonomy-supporters! kb2)
    (is (= 20 (count genls)))
    (is (every? (set (mapcat identity @hints)) genls))))

;; ---- the membership placement pass hints a chunk of terms at a time -------

(defn- standing-nogoods
  "A KB of `n` terms each held in two types a `disjoint` separates, so `n` membership
  nogoods stand, read through `hinting-store`, and its hint log."
  [n]
  (let [kb    (v/open-kb {:backend :memory :space (gensym "prefetch")})
        _     (v/with-deferred-settle kb
                (v/assert kb '(disjoint pfa_kind pfb_kind) 'CxPrefetch {:strength :monotonic})
                (doseq [i (range n) :let [x (symbol (str "Ind" i))]]
                  (v/assert kb (list 'pfa_kind x) 'CxPrefetch)
                  (v/assert kb (list 'pfb_kind x) 'CxPrefetch)))
        hints (atom [])]
    [(assoc kb :records (hinting-store (:records kb) hints)) hints]))

(deftest the-membership-placement-pass-hints-each-nogoods-records-in-chunks
  ;; a `genl` edge above one of the types places every nogood again, reading each
  ;; one's members and its placed `(contradicts …)`
  (let [n          600
        [kb hints] (standing-nogoods n)
        recs       (:records kb)
        of         (fn [f] (into #{} (filter #(= f (first (:sentence (p/get-sentex recs %)))))
                                 (p/sentex-ids recs)))]
    (reset! hints [])
    (v/assert kb '(genl pfa_kind pfc_kind) 'CxPrefetch {:strength :monotonic})
    (let [hinted (set (mapcat identity @hints))]
      (is (= n (count (of 'contradicts))))
      (is (every? hinted (concat (of 'contradicts) (of 'pfa_kind) (of 'pfb_kind)))
          "every member and every placed nogood")
      (is (<= (count @hints) 12)
          "a hint a chunk of terms, in the pass that plans and the pass that places"))))

(defn- belief-content
  "Every live sentex as `[sentence context in?]` and every stored justification, by handle."
  [kb]
  (let [recs (:records kb)
        tms  (reasoning/tms kb)]
    {:sentexes       (into (sorted-map)
                           (map (fn [h] (let [s (p/get-sentex recs h)]
                                          [h [(:sentence s) (:context s) (jtms/in? tms h)]])))
                           (p/sentex-ids recs))
     :justifications (into (sorted-map) (map (fn [j] [j (into {} (p/get-justification recs j))]))
                           (p/justification-ids recs))}))

(defn- random-membership-writes
  "`k` writes drawn by `rnd` over three individuals, six types, two `disjoint`
  declarations, three `genl` edges between the types and three contexts under a world
  context: a membership or a denial stated, a stored one retracted, an edge stated or
  retracted."
  [^java.util.Random rnd k]
  (let [pick  #(nth % (.nextInt rnd (count %)))
        types (mapv #(symbol (str "pfr" % "_kind")) (range 6))
        inds  (mapv #(symbol (str "PfrInd" %)) (range 3))
        ctxs  '[CxPfrA CxPfrB CxPfrD]
        edges '[[pfr4_kind pfr0_kind] [pfr5_kind pfr2_kind] [pfr4_kind pfr3_kind]]]
    (vec (repeatedly k #(case (.nextInt rnd 5)
                          0 [:assert (list (pick types) (pick inds)) (pick ctxs)]
                          1 [:assert (list 'not (list (pick types) (pick inds))) (pick ctxs)]
                          2 [:retract]
                          3 [:assert (apply list 'genl (pick edges)) 'CxPfrW]
                          4 [:retract-edge (apply list 'genl (pick edges))])))))

(defn- apply-write!
  "Apply one `random-membership-writes` write to `kb`; `:retract` takes the stored
  membership or denial at index `i` of the handle order."
  [kb [op s ctx] i]
  (case op
    :assert       (try (v/assert kb s ctx (if (= 'genl (first s)) {:strength :monotonic} {}))
                       (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))
    :retract-edge (some->> (v/handle-of kb s 'CxPfrW) (v/retract! kb))
    :retract      (let [recs (:records kb)
                        hs   (sort (filter #(let [s (:sentence (p/get-sentex recs %))]
                                              (re-find #"^pfr\d_kind$" (str (first (if (= 'not (first s)) (second s) s)))))
                                           (p/premise-ids recs)))]
                    (when (seq hs) (v/retract! kb (nth hs (mod i (count hs))))))))

(defn- membership-world
  "A KB holding `random-membership-writes`' contexts and declarations, through
  `hinting-store` when `hints` is an atom."
  [hints]
  (let [kb (v/open-kb {:backend :memory :space (gensym "prefetch")})
        m  {:strength :monotonic}]
    (doseq [[c up] '[[CxPfrW CxUniverse] [CxPfrA CxPfrW] [CxPfrB CxPfrW] [CxPfrD CxPfrA] [CxPfrD CxPfrB]]]
      (v/assert kb (list 'genlCx c up) 'CxUniverse m))
    (v/assert kb '(disjoint pfr0_kind pfr1_kind) 'CxPfrW m)
    (v/assert kb '(disjoint pfr2_kind pfr3_kind) 'CxPfrW m)
    (cond-> kb hints (assoc :records (hinting-store (:records kb) hints)))))

(deftest a-hinted-membership-placement-pass-places-what-an-unhinted-one-places
  ;; the hint returns nothing, so a store that prefetches and one that does not end every
  ;; write with the same records, justifications and belief
  (doseq [seed (range 6)]
    (testing (str "seed " seed)
      (let [hints    (atom [])
            plain    (membership-world nil)
            hinted   (membership-world hints)
            placed   (atom 0)
            diverged (into [] (keep-indexed
                               (fn [i w]
                                 (apply-write! plain w i)
                                 (apply-write! hinted w i)
                                 (let [a (belief-content plain)]
                                   (swap! placed + (count (filter #(= 'contradicts (ffirst (val %)))
                                                                  (:sentexes a))))
                                   (when (not= a (belief-content hinted)) [i w]))))
                           (random-membership-writes (java.util.Random. seed) 60))]
        (is (empty? diverged))
        (is (pos? @placed) "the writes placed nogoods")
        (is (seq @hints) "and the hinted world's placement pass hinted")))))

;; ---- the subsumed-mint pass hints a chunk of candidates at a time ---------

(defmacro ^:private with-pruning
  "The body with the argument entailment on and subsumed mints pruned, bound so a run
  under either switch's parity setting still reaches the pass."
  [& body]
  `(binding [argument/*assertive-arg-types?* true
             checks/*prune-subsumed-mints?* true]
     ~@body))

(deftest the-subsumed-mint-pass-hints-each-mint-and-its-subsumers-in-chunks
  ;; `(pmh_animal x)` minted in CxPmh for each x, `(pmh_dog x)` stated where CxPmh does
  ;; not see it: the edge `(genl pmh_dog pmh_animal)` asks every mint the whole question
  ;; (`edge-route-candidates`), which reads the mint and the membership below it
  (with-pruning
    (let [n     600
          kb    (v/open-kb {:backend :memory :space (gensym "prefetch")})
          m     {:strength :monotonic}
          _     (v/assert kb '(arg pmhOwns 1 pmh_animal) 'CxPmh m)
          _     (v/with-deferred-settle kb
                  (doseq [i (range n) :let [x (symbol (str "PmhInd" i))]]
                    (v/assert kb (list 'pmhOwns x 'PmhThing) 'CxPmh m)
                    (v/assert kb (list 'pmh_dog x) 'CxPmhSide m)))
          hints (atom [])
          kb    (assoc kb :records (hinting-store (:records kb) hints))
          recs  (:records kb)
          of    (fn [f] (into #{} (filter #(= f (first (:sentence (p/get-sentex recs %)))))
                              (p/sentex-ids recs)))
          mints (of 'pmh_animal)]
      (v/assert kb '(genl pmh_dog pmh_animal) 'CxPmh m)
      (let [hinted (set (mapcat identity @hints))]
        (is (= n (count mints) (count (of 'pmh_animal))) "every mint stands")
        (is (every? hinted (concat mints (of 'pmh_dog))) "every mint and the membership below it")
        (is (<= (count @hints) 6) "two hints a chunk of 256 candidates")))))

(defn- random-mint-writes
  "`k` writes drawn by `rnd` over four individuals, five types, four `genl` edges between
  them, argument declarations on `pmrOwns` and three contexts under a world context: a
  membership or a `pmrOwns` fact stated, one of them retracted, an edge or a declaration
  stated or retracted."
  [^java.util.Random rnd k]
  (let [pick  #(nth % (.nextInt rnd (count %)))
        types (mapv #(symbol (str "pmr" % "_kind")) (range 5))
        inds  (mapv #(symbol (str "PmrInd" %)) (range 4))
        ctxs  '[CxPmrA CxPmrB CxPmrD]
        edges '[[pmr1_kind pmr0_kind] [pmr2_kind pmr1_kind] [pmr3_kind pmr0_kind] [pmr4_kind pmr2_kind]]]
    (vec (repeatedly k #(case (.nextInt rnd 12)
                          (0 1 2) [:assert (list (pick types) (pick inds)) (pick ctxs)]
                          (3 4 5) [:assert (list 'pmrOwns (pick inds) 'PmrThing) (pick ctxs)]
                          6       [:retract]
                          (7 8)   [:assert (apply list 'genl (pick edges)) 'CxPmrW]
                          9       [:retract-in (apply list 'genl (pick edges)) 'CxPmrW]
                          10      [:assert (list 'arg 'pmrOwns 1 (pick types)) 'CxPmrW]
                          11      [:retract-in (list 'arg 'pmrOwns 1 (pick types)) 'CxPmrW])))))

(defn- apply-mint-write!
  "Apply one `random-mint-writes` write to `kb`; `:retract` takes the stored membership
  or `pmrOwns` fact at index `i` of the handle order."
  [kb [op s ctx] i]
  (case op
    :assert     (try (v/assert kb s ctx {:strength :monotonic})
                     (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))
    :retract-in (some->> (v/handle-of kb s ctx) (v/retract! kb))
    :retract    (let [recs (:records kb)
                      hs   (sort (filter #(re-find #"^(pmr\d_kind|pmrOwns)$"
                                                   (str (first (:sentence (p/get-sentex recs %)))))
                                         (p/premise-ids recs)))]
                  (when (seq hs) (v/retract! kb (nth hs (mod i (count hs))))))))

(defn- mint-world
  "A KB holding `random-mint-writes`' contexts and a declaration on `pmrOwns`, through
  `hinting-store` when `hints` is an atom."
  [hints]
  (let [kb (v/open-kb {:backend :memory :space (gensym "prefetch")})]
    (doseq [[c up] '[[CxPmrW CxUniverse] [CxPmrA CxPmrW] [CxPmrB CxPmrW] [CxPmrD CxPmrA]]]
      (v/assert kb (list 'genlCx c up) 'CxUniverse {:strength :monotonic}))
    (v/assert kb '(arg pmrOwns 1 pmr0_kind) 'CxPmrW {:strength :monotonic})
    (cond-> kb hints (assoc :records (hinting-store (:records kb) hints)))))

(deftest a-hinted-subsumed-mint-pass-withdraws-what-an-unhinted-one-withdraws
  ;; the hinter reads and writes nothing the pass does not read, so a store that
  ;; prefetches and one that does not end every write, and a recover, with the same
  ;; records, justifications and belief
  (with-pruning
    (doseq [seed (range 6)]
      (testing (str "seed " seed)
        (let [hints     (atom [])
              plain     (mint-world nil)
              hinted    (mint-world hints)
              withdrawn (atom 0)
              diverged  (into [] (keep-indexed
                                  (fn [i w]
                                    (let [before (reads/stored-mint-count-global (:index plain))]
                                      (apply-mint-write! plain w i)
                                      (apply-mint-write! hinted w i)
                                      (when (and (= :assert (first w))
                                                 (< (reads/stored-mint-count-global (:index plain)) before))
                                        (swap! withdrawn inc))
                                      (when (not= (belief-content plain) (belief-content hinted)) [i w]))))
                              (random-mint-writes (java.util.Random. seed) 80))]
          (v/recover plain)
          (v/recover hinted)
          (is (empty? diverged))
          (is (= (belief-content plain) (belief-content hinted)) "after a recover")
          (is (pos? @withdrawn) "a write withdrew a mint")
          (is (seq @hints) "and the hinted world hinted"))))))
