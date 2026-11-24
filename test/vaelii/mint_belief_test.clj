;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.mint-belief-test
  "A rule a **generator** generates is *derived* content: it is justified by the
  firing that minted it, never marked a premise, so the ordinary relabel un-believes
  it the moment what licensed it goes (`chain/mint-rule`, docs/generators.md).  These
  assert that invariant against **defeat** — the case retraction tests do not reach.  A
  defeat is a reader's verdict: the mark stays IN in the network and its own context
  withdraws it, and with it the mint and everything the mint concludes
  (docs/nmtms.md, \"A defeat is scoped to its vantage\").

  `generator_test`'s `retracting-the-fill-retracts-the-rule` and
  `rejoin_belief_test` cover the *retraction* of a fill (which SWEEPS the mint's node
  outright) and the two *re-join* firing paths.  Neither asserts what happens when the
  mark that licensed the mint is **defeated** rather than retracted.  The claim under
  test is that its belief moves: the mint's sole justification names the mark handle as
  an antecedent, so a reader that withdraws the mark withdraws the mint, and every
  conclusion the mint draws rests on it and is withdrawn there too.

  A NOTE on measuring a mint, because it is the trap this file exists to close.  The
  marker rule — the `set/defaultRule (implies (trig ?p) (mark ?p))` that hands the
  generator its fill — is itself a stored rule with an antecedent whose consequent is a
  *fact*, so `vr/generator-sentex?` is false of it and it is an **asserted premise**,
  correctly IN for the whole scenario (nothing in the engine defeats a rule, only its
  conclusion — docs/nmtms.md).  A `(->> rules (remove generator?) first)` helper picks
  *it* up, not the derived mint, and then reports a believed rule after the defeat, which
  looks like a soundness hole.  `the-marker-default-is-not-the-mint` tells the two apart:
  the marker is a premise, the mint is derived, and only the mint's belief moves."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defn- the-mint
  "The one *derived* generated rule in `ctx` concluding `pred` — a rule with an
  antecedent, not a generator, and **not a premise**.  Found by what it concludes and
  by its being derived, so it can never be confused with the marker default the
  generator fires on (which is an asserted premise concluding a fact)."
  [kb ctx pred]
  (->> (v/sentexes-in-context kb ctx)
       (filter :antecedent)
       (remove vr/generator-sentex?)
       (remove #(v/premise? kb (:id %)))
       (filter #(= pred (some-> (:consequent %) first)))
       first))

(defn- build-mint!
  "Assert a generator, a marker default and one fill so a rule is minted; return the
  derived mint's sentex map.  `(trig pbigger)` fires the marker to conclude
  `(mark pbigger)`, on which the generator fires to generate
  `(implies (pbigger ?x ?y) (seen ?x))`."
  [kb mark seen trig pbigger ctx]
  (v/assert kb (list 'implies (list mark '?rel)
                     (list 'implies (list '?rel '?x '?y) (list seen '?x)))
            ctx {:direction :forward})
  (v/assert kb (list 'set/defaultRule
                     (list 'set/forwardRule (list 'implies (list 'and (list trig '?p)) (list mark '?p))))
            ctx)
  (v/assert kb (list trig pbigger) ctx)
  (the-mint kb ctx seen))

;; ---- the invariant: a defeated mint is un-believed -----------------------

(tu/deftest-kb a-defeated-mint-is-un-believed
  (tu/with-terms [pmark pseen trig pbigger CxMB]
    (let [mint (build-mint! kb pmark pseen trig pbigger CxMB)
          mh   (:id mint)]
      (is (some? mint) "a rule was generated")
      (testing "before the defeat the mint is a derived, believed rule"
        (is (not (v/premise? kb mh)) "the mint is derived, not a premise")
        (is (seq (v/supporting-justifications kb mh))
            "and it rests on the generator's firing")
        (is (v/believed? kb mh))
        (is (v/believed? kb mh CxMB)))
      (testing "defeating the mark that licensed it withdraws the mint"
        (v/assert kb (list 'not (list pmark pbigger)) CxMB {:strength :monotonic})
        (is (empty? (v/sentexes-matching kb (list pmark pbigger) CxMB))
            "the mark is defeated")
        (is (not (v/believed? kb mh))
            "the mint's sole justification names the mark, withdrawn — so the mint is")
        (is (false? (v/believed? kb mh CxMB)) "and its context reads it so")))))

;; ---- soundness: an un-licensed mint fires nothing ------------------------

(tu/deftest-kb a-defeated-mint-concludes-nothing-believed-on-the-trigger-path
  ;; the oracle path: a fact matching the mint's antecedent arrives *after* the defeat,
  ;; so `fire-rules-for` reaches the mint through the antecedent index.  A verdict blocks
  ;; no firing: the conclusion rests on the mint, and the reader that withdraws the mint
  ;; withdraws it.
  (tu/with-terms [pmark pseen trig pbigger dog cat CxMB]
    (let [mint (build-mint! kb pmark pseen trig pbigger CxMB)]
      (is (some? mint) "a rule was generated")
      (v/assert kb (list 'not (list pmark pbigger)) CxMB {:strength :monotonic})
      (is (not (v/believed? kb (:id mint))) "the mint is withdrawn")
      (testing "a tuple the mint would range over arrives, and draws nothing believed"
        (v/assert kb (list pbigger dog cat) CxMB)
        (v/forward-chain kb)
        (is (empty? (v/sentexes-matching kb (list pseen dog) CxMB))
            "the withdrawn mint concluded nothing believed")))))

;; ---- the measurement trap this file closes -------------------------------

(tu/deftest-kb the-marker-default-is-not-the-mint
  ;; The marker `defaultRule (implies (trig ?p) (mark ?p))` is a stored rule concluding
  ;; a fact — not a generator — so a `(remove generator?) first` helper returns *it*,
  ;; and it is an asserted PREMISE, correctly believed for the whole scenario.  Mistaking
  ;; it for the mint is what makes a defeated mint *look* like it stays believed.  Tell the
  ;; two apart: the marker stays IN as a premise, only the derived mint's belief moves.
  (tu/with-terms [pmark pseen trig pbigger CxMB]
    (let [mint (build-mint! kb pmark pseen trig pbigger CxMB)
          ;; the naive helper: first non-generator rule with an antecedent
          naive (->> (v/sentexes-in-context kb CxMB)
                     (filter :antecedent)
                     (remove vr/generator-sentex?)
                     (filter #(v/premise? kb (:id %)))
                     first)]
      (is (some? mint) "the derived mint exists")
      (is (some? naive) "so does a premise rule the naive helper would grab")
      (is (not= (:id mint) (:id naive))
          "they are different handles — the naive pick is not the mint")
      (is (v/premise? kb (:id naive)) "the naive pick is an asserted premise")
      (is (not (v/premise? kb (:id mint))) "the mint is derived")
      (testing "after the defeat the premise marker stays IN; only the mint moves"
        (v/assert kb (list 'not (list pmark pbigger)) CxMB {:strength :monotonic})
        (is (v/believed? kb (:id naive))
            "the marker rule is a premise — nothing defeats a rule, only its conclusion")
        (is (not (v/believed? kb (:id mint)))
            "the mint is withdrawn the moment its licensing mark is defeated")))))
