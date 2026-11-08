;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.index-edge-test
  "Edge cases of the storage layer — the count trie (`vaelii.impl.kv`), the
  type-faithfulness of its keys and set members, and the record store's premise
  strengths.

  What is at stake here is that **the index is not self-describing**.  A trie node is
  a key holding a set, and nothing in that set says what it is: a handle is an
  integer, and so is the token `1970`.  The trie is also *ragged* — paths differ in
  length with arity — so a path prefix of one sentex can be another sentex's whole
  path.  Both facts conspire: a walk that stops in the wrong place, or reads the
  wrong key, returns tokens dressed up as handles and every layer above believes
  them, because `get-sentex` on a small integer is a real and completely unrelated
  sentex.  There is no exception and no empty result to notice — just wrong answers.

  So the tests below are mostly about *type and identity of what comes back out*,
  and about the cleanup arithmetic: a node's counter must reach zero exactly when its
  last sentex leaves, since `plan/prefix-estimate` costs every join off those
  counters and an orphaned one is a phantom that never expires."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/empty-kb))

;; ---- the ragged trie: a walk must land on a leaf, not an interior node ----

(tu/deftest-kb a-pattern-shorter-than-the-stored-path-yields-no-handles
  ;; The trie is ragged by arity, so `lookup` cannot decide "leaf" by exhausting the
  ;; pattern: a two-token pattern against a four-token path terminates on an INTERIOR
  ;; node.  When child tokens and leaf handles shared one set key, that returned the
  ;; node's child tokens as if they were handles — `[bornIn Tom]` answered `#{1970}`,
  ;; and `(v/sentex kb 1970)` is a real, unrelated sentex.  Nothing throws and nothing
  ;; comes back empty; the caller is simply lied to.
  (tu/with-terms [bornIn Tom CxBirth]
    (let [h (v/assert kb (list bornIn Tom 1970) CxBirth)
          idx (:index kb)]
      (testing "the full path answers with the handle it was indexed under"
        (is (= #{h} (p/lookup idx [bornIn Tom 1970 CxBirth]))))
      (testing "every short prefix answers empty rather than with its child tokens"
        (is (= #{} (p/lookup idx [bornIn Tom 1970])) "one token short — no context slot")
        (is (= #{} (p/lookup idx [bornIn Tom]))      "would have yielded the token 1970")
        (is (= #{} (p/lookup idx [bornIn]))          "would have yielded the token Tom")
        (is (= #{} (p/lookup idx []))                "would have yielded the token bornIn"))
      (testing "and the token really was the imposter — it sits in the child set"
        (is (= [1970] (p/children idx [bornIn Tom]))))
      (testing "the bug is reachable publicly: level 0 passes a vector path straight through"
        (is (empty? (v/lookup kb 0 [bornIn Tom] CxBirth)))
        (is (= [h] (map :handle (v/lookup kb 0 [bornIn Tom 1970 CxBirth] CxBirth))))))))

(tu/deftest-kb a-full-path-that-is-also-an-interior-node-yields-only-its-own-handles
  ;; The same collision reached with a *correct* full path, so honouring the "pass a
  ;; full path" contract is not enough to be safe.  Raggedness lets one sentex's whole
  ;; path be a proper prefix of another's:
  ;;
  ;;   (rel A B)              in CxCee -> [rel A B CxCee]
  ;;   (rel A B CxCee X) in CxDee -> [rel A B CxCee X CxDee]
  ;;
  ;; so the node [rel A B CxCee] is a leaf AND an interior node at once.  Sharing
  ;; one set key made it hold a handle and the child token `X` together, and lookup
  ;; returned both — an unfilterable mix, since the token is not distinguishable from
  ;; a handle by type.
  (tu/with-terms [rel A B X CxCee CxDee]
    (let [h1 (v/assert kb (list rel A B) CxCee)
          h2 (v/assert kb (list rel A B CxCee X) CxDee)
          idx (:index kb)]
      (is (not= h1 h2))
      (testing "the shorter sentex's leaf holds its handle alone, not the child token"
        (is (= #{h1} (p/lookup idx [rel A B CxCee]))))
      (testing "the longer sentex is still reachable at its own, deeper leaf"
        (is (= #{h2} (p/lookup idx [rel A B CxCee X CxDee]))))
      (testing "and the child edge is still there — it moved key, it was not dropped"
        (is (= [X] (p/children idx [rel A B CxCee])))))))

(tu/deftest-kb a-wildcard-terminus-is-held-to-the-same-leaf-rule
  ;; A variable does not shorten the contract: `lookup` fans a wildcard out over a
  ;; node's child set, and wherever the fan-out lands is still a terminus that must be
  ;; a leaf.  Against the ragged pair below, the five-token wildcard probe descends
  ;; through the child token X and stops one level ABOVE the deeper sentex's leaf — so
  ;; a terminus that reads the child set answers `#{CxDee}`, handing back a
  ;; context name as a handle.
  (tu/with-terms [rel A B X CxCee CxDee]
    (let [h1 (v/assert kb (list rel A B) CxCee)
          h2 (v/assert kb (list rel A B CxCee X) CxDee)
          idx (:index kb)]
      (testing "a well-formed context wildcard reaches exactly the leaf it should"
        (is (= #{h1} (p/lookup idx [rel A B '?ctx]))))
      (testing "a wildcard landing on an interior node yields nothing, not its children"
        (is (= #{} (p/lookup idx [rel A B CxCee '?tok]))
            "would have yielded the token CxDee"))
      (testing "and the wildcard still resolves when the path is run to its real leaf"
        (is (= #{h2} (p/lookup idx [rel A B CxCee '?tok CxDee])))
        (is (= #{h2} (p/lookup idx [rel A B CxCee X '?ctx]))))
      (testing "a context set keeps the last level to its members"
        (is (= #{h1} (p/lookup idx [rel A B '?ctx] #{CxCee CxDee})))
        (is (= #{} (p/lookup idx [rel A B '?ctx] #{CxDee})))
        (is (= #{h2} (p/lookup idx [rel A B CxCee X '?ctx] #{CxDee})))
        (is (= #{} (p/lookup idx [rel A B CxCee X CxDee] #{CxCee})))))))

;; ---- unindex arithmetic: cleanup must fire on dead nodes and only those --

(tu/deftest-kb unindexing-one-of-two-sentexes-leaves-the-shared-node-intact
  ;; The existing coverage unindexes the only sentex in the KB, where every node dies
  ;; and the `(when (<= c 0) ...)` cleanup fires at every level — so a cleanup that
  ;; fired unconditionally would pass it.  Here two paths share the prefix
  ;; `[bornIn Tom]`; removing one must decrement that node and touch nothing else,
  ;; or the survivor is unreachable while still sitting in the record store.
  (tu/with-terms [bornIn Tom Paris Rome CxBirth]
    (let [h1  (v/assert kb (list bornIn Tom Paris) CxBirth)
          h2  (v/assert kb (list bornIn Tom Rome) CxBirth)
          idx (:index kb)]
      (is (= 2 (p/count-at idx [bornIn Tom])))
      (v/retract! kb h1)
      (testing "the shared node survives, decremented to the survivor's count"
        (is (= 1 (p/count-at idx [bornIn Tom])))
        (is (= 1 (p/count-at idx [bornIn])))
        (is (= 1 (p/count-at idx []))))
      (testing "and the survivor is still reachable through it"
        (is (= #{h2} (p/lookup idx [bornIn Tom Rome CxBirth])))
        (is (= [Rome] (p/children idx [bornIn Tom]))
            "the dead branch's label was sremmed from the shared parent; the live one was not"))
      (testing "the retracted branch's own node is gone, not merely emptied"
        (is (= 0 (p/count-at idx [bornIn Tom Paris])))
        (is (empty? (p/lookup idx [bornIn Tom Paris CxBirth])))))))

(tu/deftest-kb the-last-sentex-out-returns-every-interior-counter-to-zero
  ;; An orphaned `[:trie :count prefix]` is invisible — no query fails because of it — but
  ;; `plan/prefix-estimate` costs joins off exactly these counters, so a phantom count
  ;; skews every plan through that prefix, forever.  Counts must be conserved: what
  ;; went up on assert comes back down on retract, at every level of the path.
  (tu/with-terms [bornIn Tom Paris Rome CxBirth]
    (let [h1  (v/assert kb (list bornIn Tom Paris) CxBirth)
          h2  (v/assert kb (list bornIn Tom Rome) CxBirth)
          idx (:index kb)]
      (v/retract! kb h1)
      (v/retract! kb h2)
      (testing "every node along the shared path is back to zero"
        (is (= 0 (p/count-at idx [bornIn Tom Paris])))
        (is (= 0 (p/count-at idx [bornIn Tom])))
        (is (= 0 (p/count-at idx [bornIn])))
        (is (= 0 (p/count-at idx []))))
      (testing "and the child sets are empty all the way up to the root"
        (is (empty? (p/children idx [bornIn Tom])))
        (is (empty? (p/children idx [bornIn])))
        (is (empty? (p/children idx []))
            "the root no longer lists a predicate with nothing under it")))))

;; ---- child tokens round-trip every token type, not just handles ---------

(tu/deftest-kb child-tokens-keep-their-type
  ;; A `KvBackend` must store set members type-faithfully: the trie's child sets hold
  ;; KEYWORDS (`:rule`, `:false` — the key-frame tokens) and NUMBERS (a numeric
  ;; argument) alongside symbol functors.  A backend that flattened those to "rule" /
  ;; "1970" would still pass every other assertion in this suite: nothing compares a
  ;; child token except `lookup`'s wildcard descent, which would then build a prefix
  ;; of strings and silently match nothing.  So type is the assertion.
  (tu/with-terms [bornIn Tom Rex dog p q CxLabel]
    (v/assert kb (list bornIn Tom 1970) CxLabel)
    (v/assert kb (list 'not (list dog Rex)) CxLabel)
    (v/assert kb (list 'implies (list p '?x) (list q '?x)) CxLabel)
    (let [roots (set (p/children (:index kb) []))]
      (testing "a rule keys under the keyword :rule, and a negative fact under :false"
        (is (contains? roots :rule))
        (is (contains? roots :false))
        (is (every? keyword? (filter #{:rule :false} roots)))
        (is (not-any? string? roots) "a raw-string regression would land here"))
      (testing "a positive fact keys under its functor, still a symbol"
        (is (contains? roots bornIn))
        (is (symbol? (first (filter #{bornIn} roots))))))
    (testing "and a numeric argument stays a number, not \"1970\""
      (let [labels (p/children (:index kb) [bornIn Tom])]
        (is (= [1970] labels))
        (is (number? (first labels)))
        (is (not (string? (first labels))))))))

;; ---- the secondary roots: what belongs in each, and what does not -------

(tu/deftest-kb the-context-root-holds-rules-alongside-facts
  ;; Documented as "every sentex there, rules included" and otherwise unasserted — the
  ;; existing coverage only checks the converse, that a rule contributes no *functor*
  ;; entry.  The two are easy to conflate: `root-keys` excludes a rule from the functor
  ;; and argument roots by guarding on the body's shape, and moving the context key
  ;; inside that same guard would drop rules from `sentexes-in-context` too, leaving
  ;; `count-in-context` under-counting a rule-heavy context.
  (tu/with-terms [p q Muffet dog CxRule]
    (let [fact (v/assert kb (list dog Muffet) CxRule)
          rule (v/assert kb (list 'implies (list p '?x) (list q '?x)) CxRule)]
      (testing "the context's extent and cardinality both count the rule"
        (is (= 2 (v/count-in-context kb CxRule)))
        (is (= #{fact rule} (set (map :id (v/sentexes-in-context kb CxRule))))))
      (testing "while the predicate extent still holds facts only"
        (is (= 0 (v/count-with-functor kb q)))
        (is (= 1 (v/count-with-functor kb dog)))))))

(tu/deftest-kb the-argument-root-drops-numbers-and-strings
  ;; `root-keys` filters arguments through `sx/indexable-term?`, which rejects numbers
  ;; and strings as useless lookup keys.  Nobody searches for "every sentex with 1970
  ;; in slot 2" — but a comment string or a year is exactly the kind of high-cardinality
  ;; junk that would bloat `[:argument-root]` with one key per distinct literal.
  (tu/with-terms [bornIn note Tom CxArg]
    (v/assert kb (list bornIn Tom 1970) CxArg)
    (v/assert kb (list note Tom "a free-text remark") CxArg)
    (testing "a symbol argument is indexed by position"
      (is (= 2 (v/count-with-arg kb 1 Tom))))
    (testing "a number and a string are not indexed at all"
      (is (= 0 (v/count-with-arg kb 2 1970)))
      (is (= 0 (v/count-with-arg kb 2 "a free-text remark")))
      (is (empty? (v/sentexes-with-arg kb 2 1970))))))

(tu/deftest-kb the-argument-root-canonicalizes-a-compound-term
  ;; `arg-key` runs the term through `sx/canon` before freezing.  Every other argument
  ;; root test passes an atomic symbol, where `canon` is the identity — so deleting it
  ;; adds no work there.  A COMPOUND term is where it bites: a LazySeq and a
  ;; PersistentList are `=` but freeze to different nippy bytes, so the lookup key
  ;; would miss the stored one and return the empty set.  No error, no exception —
  ;; the fact is simply invisible from that root.
  (tu/with-terms [holds succ Zero CxNum]
    (v/assert kb (list holds (list succ Zero)) CxNum)
    (testing "found by a compound argument written as a plain list"
      (is (= 1 (v/count-with-arg kb 1 (list succ Zero))))
      (is (= 1 (count (v/sentexes-with-arg kb 1 (list succ Zero))))))
    (testing "and by the same term arriving as a lazy seq — canon is what makes these agree"
      (let [lazy-term (map identity (list succ Zero))]
        (is (not (instance? clojure.lang.PersistentList lazy-term))
            "the probe must really be a different sequential type, or it proves nothing")
        (is (= 1 (v/count-with-arg kb 1 lazy-term)))
        (is (= 1 (count (v/sentexes-with-arg kb 1 lazy-term))))))
    (testing "a compound that was never stored is still empty"
      (is (= 0 (v/count-with-arg kb 1 (list succ (list succ Zero))))))))

;; ---- the inverted term index -------------------------------------------

(tu/deftest-kb intersecting-no-terms-is-empty-rather-than-an-arity-error
  ;; `sentexes-with-terms` guards the empty case: an N-key intersection over zero keys
  ;; has no natural answer at the backend (`kv-intersect` is only defined for one or more
  ;; keys), so without the guard `find-sentexes-all` on no terms could throw from deep
  ;; in the store rather than reporting the caller passed nothing.  An empty
  ;; conjunction of constraints is vacuous; the answer is the empty set.
  (tu/with-terms [dog Muffet CxTerm]
    (v/assert kb (list dog Muffet) CxTerm)
    (testing "the guard lives on the index protocol, and answers with a set"
      (is (= #{} (p/sentexes-with-terms (:index kb) []))))
    (testing "so the public wrapper answers empty instead of throwing"
      (is (empty? (v/find-sentexes-all kb []))))
    (testing "while a real intersection still narrows"
      (is (= 1 (count (v/find-sentexes-all kb [dog Muffet]))))
      (is (= 0 (count (v/find-sentexes-all kb [dog (tu/tmp-ind)])))))))

;; ---- a compound probe, at every floor -----------------------------------
;;
;; `sx/*min-indexed-depth*` decides which ground compounds earn their own term-index
;; key, and its default drops the one a literal is of *itself* — the key that is minted
;; per record and holds one handle.  What must not move is the answer: `find-sentexes`
;; on a compound narrows on the atoms and verifies against the record, so it returns the
;; same sentexes whether or not a key was there to read.  These tests reindex the same
;; records under each floor and compare, which is the property the whole change rests on.

(tu/deftest-kb a-compound-probe-answers-the-same-at-every-floor
  (tu/with-terms [pint believes A B Tom CxTerm]
    (let [c    (list pint A B)
          flip (list pint B A)                    ; the same atoms, a different term
          bare (v/assert kb c CxTerm)                     ; the compound IS the literal
          nest (v/assert kb (list believes Tom c) CxTerm) ; and here it is nested in one
          _    (v/assert kb flip CxTerm)
          ids  #(set (map :id (v/find-sentexes kb %)))
          at   (fn [floor f] (binding [sx/*min-indexed-depth* floor] (v/reindex kb) (f)))]
      (try
        (testing "at the default floor the literal's own key is gone and the nested one stays"
          (is (not (contains? (v/indexable-terms (v/sentex kb bare)) c))
              "the fact's body no longer keys itself")
          (is (contains? (v/indexable-terms (v/sentex kb nest)) c)
              "while the same compound nested inside a literal keeps its key")
          (is (= #{nest} (reads/as-stored-with-term (:index kb) c))
              "so the raw index read holds the nesting alone"))
        (testing "and the public read is exact anyway, at every floor"
          (doseq [floor [0 1 2]]
            (is (= #{bare nest} (at floor #(ids c)))
                (str "find-sentexes on the compound, floor " floor))
            (is (= #{bare nest} (at floor #(set (map :id (v/find-sentexes-all kb [c])))))
                (str "and the N-term form of the same probe, floor " floor))))
        (testing "the verify is what keeps it exact — the atoms alone would over-answer"
          (is (= 3 (count (v/find-sentexes-all kb [pint A B])))
              "all three sentexes mention every atom of the compound")
          (is (= #{bare nest} (ids c)) "but only two hold the compound itself"))
        (testing "a term the atoms are shared with is still told apart"
          (is (= #{flip} (set (map :sentence (v/find-sentexes kb flip))))))
        (testing "and a pattern is not a term — the atoms would answer, the probe must not"
          (is (empty? (v/find-sentexes kb (list pint '?x B))))
          (is (empty? (v/find-sentexes-all kb [(list pint '?x B) A]))))
        (testing "an atom probe is untouched by the floor"
          (doseq [floor [0 1 2]]
            (is (= 3 (at floor #(count (v/find-sentexes kb A)))) (str "floor " floor))))
        (finally (v/reindex kb))))))          ; leave the store at the default for teardown

(tu/deftest-kb the-floor-is-what-makes-the-dictionary-vocabulary-bound
  ;; The count, not just the answer: each ground fact keys itself, so at floor 0 the
  ;; distinct-token count grows with the records over a fixed vocabulary and at floor 1
  ;; it does not.  Measured on the sentexes rather than the backend, since that is where
  ;; the policy lives and every index reads it.
  (tu/with-terms [pint A B C CxTerm]
    (let [facts (doall (for [x [A B C], y [A B C] :when (not= x y)]
                         (v/sentex kb (v/assert kb (list pint x y) CxTerm))))
          keys' (fn [floor]
                  (binding [sx/*min-indexed-depth* floor]
                    (into #{} (mapcat v/indexable-terms) facts)))]
      (is (= 6 (count facts)) "six ordered pairs over three individuals")
      (testing "floor 0 mints a key per record on top of the vocabulary"
        (is (= 10 (count (keys' 0))) "4 names + 6 bodies"))
      (testing "the default keys the vocabulary and nothing else"
        (is (= 4 (count (keys' 1))))
        (is (every? symbol? (keys' 1)) "no compound survives, so nothing is fact-scaled")))))

;; ---- record store: premise strengths survive the round trip -------------

(tu/deftest-kb a-premise-strength-round-trips-through-the-record
  ;; `recover` rebuilds the JTMS by reading each premise's strength back off its
  ;; sentex.  If a `:monotonic` premise reads back as `:default`, every defeat
  ;; decision resting on it flips — known-true content silently becomes defeasible,
  ;; and the KB is *consistent*, just wrong.  So the keyword must survive the store as
  ;; a keyword, and the nil-strength default must be applied on write, not guessed later.
  (tu/with-terms [dog Muffet CxPrem]
    (let [h    (v/assert kb (list dog Muffet) CxPrem {:strength :monotonic})
          recs (:records kb)]
      (testing ":monotonic survives the store as :monotonic"
        (is (= :monotonic (p/premise-strength recs h)))
        (is (= :monotonic (:strength (p/get-sentex recs h))))
        (is (keyword? (p/premise-strength recs h)) "not the string \"monotonic\""))

      (testing "mark-premise with no strength writes :default rather than nil"
        (p/mark-premise recs h nil)
        (is (= :default (:strength (p/get-sentex recs h)))
            "the (or strength :default) is applied on the way IN — the record is not left nil")
        (is (= :default (p/premise-strength recs h)))
        (is (contains? (p/premise-ids recs) h)))

      (testing "marking at the strength already stored re-marks and stores nothing new"
        ;; the ordinary assert: `kb/create-sentex` writes the strength into the record it
        ;; stores, so the mark that follows asks for the one already there.  Both stores
        ;; leave the record alone in that case — a whole frame not appended on the
        ;; durable one, a path through the sentex map not copied on the in-memory one —
        ;; and the premise set still takes the handle, which is what the mark is for.
        (p/mark-premise recs h :monotonic)
        (p/mark-premise recs h :monotonic)
        (is (= :monotonic (p/premise-strength recs h)))
        (is (= :monotonic (:strength (p/get-sentex recs h))))
        (is (contains? (p/premise-ids recs) h))
        (testing "and a mark at a different strength does move the record"
          (p/mark-premise recs h :default)
          (is (= :default (:strength (p/get-sentex recs h))))
          (is (contains? (p/premise-ids recs) h))))

      (testing "unmark-premise! clears the strength off the record and the premise set"
        (p/unmark-premise! recs h)
        (is (nil? (:strength (p/get-sentex recs h)))
            "an unmarked sentex is derived, not a premise at some strength")
        (is (not (contains? (p/premise-ids recs) h)))
        (testing "and premise-strength then falls back to :default"
          (is (= :default (p/premise-strength recs h)))))

      (testing "an id with no sentex at all also falls back rather than returning nil"
        (is (= :default (p/premise-strength recs 999999)))
        (is (nil? (p/get-sentex recs 999999))
            "the fallback is a real fallback — there is genuinely no record there"))

      ;; restore premise-hood so the fixture's teardown can retract what this test added
      (p/mark-premise recs h :monotonic))))
