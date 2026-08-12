;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.retrieval-completeness-test
  "Retrieval against **ground truth**, not against another retrieval path.

  The other two retrieval oracles are *relative*: `arg_root_retrieval_test` pins the
  argument roots against the trie, `matches_hierarchical_test` pins the set-algebra
  path against the nested fan-out.  Each proves two mechanisms agree, which is exactly
  what they are for — and neither can see a shape where *both* are wrong.  An open
  negative literal was such a shape: a negative key holds its whole body as one token,
  so the trie matched only an exactly-ground negative, and the fan-out it was compared
  against inherited the same blindness.  `(not (dog ?x))` answered nothing with two
  such facts stored, through `query` and `ask` alike, and both oracles were green.

  So this one has no index in it at all.  It scans every stored record, filters by
  belief and visibility, and unifies — the definition of what the KB holds, written
  out.  The probe KB declares **no genl edge among the probed predicates and nothing
  symmetric**, which is what makes plain `unify` the whole semantics: subsumption and
  the mirror probe are real behaviour that this ground truth deliberately does not
  model, and they are covered by the relative oracles instead.

  Every retrieval configuration is held to it, since a shape can be lost by any one of
  them independently."
  (:require [clojure.set :as set]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- brute
  "Every stored fact `pat` unifies with, reached without consulting any index — the
  same three filters `matches-visible` applies (believed, visible, matching polarity),
  and then `unify` itself."
  [kb pat ctx]
  (let [recs     (:records kb)
        tms      (:tms kb)
        ;; a variable view-context means *any* context, exactly as `matches-visible`
        ;; reads it — the up-closure of a variable is not a cone
        visible? (if (sx/variable? ctx)
                   (constantly true)
                   (let [up (tax/context-up (:taxonomy kb) ctx)] #(contains? up %)))
        pt       (res/kb-sentex kb pat ctx)]
    (into #{}
          (keep (fn [h]
                  (when-let [s (p/get-sentex recs h)]
                    (when (and (nil? (:antecedent s))                 ; facts only
                               (not (sx/exceptWhen-meta? (:sentence s)))
                               (jtms/in? tms h)
                               (visible? (:context s))
                               (= (:truth pt) (:truth s))
                               (res/unify (:sentence pt) (:sentence s)))
                      h)))
                (p/sentex-ids recs)))))

(defn- got [kb pat ctx] (into #{} (map first) (res/matches-visible kb pat ctx)))

(tu/deftest-kb every-pattern-shape-finds-what-is-stored
  (tu/with-terms [dog cat parentOf rel bornIn note
                  Muffet Rex Tom Sam Ann Bob Cid A B C X CxProbe]
    (let [facts [(list dog Muffet) (list dog Rex) (list cat Tom)
                 (list parentOf Ann Bob) (list parentOf Bob Cid) (list parentOf Ann Cid)
                 (list rel A B C) (list rel A X C)
                 (list bornIn Muffet 1970) (list bornIn Rex 1995)
                 (list note Muffet "a string")
                 (list 'not (list dog Tom)) (list 'not (list dog Sam))
                 (list 'not (list parentOf Cid Ann))]
          shapes [;; concrete functor, the ordinary cases
                  (list dog '?x) (list dog Muffet)
                  (list parentOf Ann '?y) (list parentOf '?x Cid)
                  (list rel A '?y C) (list rel '?x '?y C)
                  ;; arguments the roots do not key
                  (list bornIn '?x 1970) (list note '?x "a string")
                  ;; open functor
                  (list '?p Muffet) (list '?p '?x)
                  (list '?p Ann '?y) (list '?p '?x Cid)
                  ;; dotted rest — concrete/open functors and a fixed prefix
                  (list dog '. '?args)
                  (list parentOf Ann '. '?args)
                  (list '?p '. '?args)
                  ;; negative literals — the shape both relative oracles were blind to
                  (list 'not (list dog Tom))
                  (list 'not (list dog '?x))          ; nothing ground but the functor
                  (list 'not (list parentOf '?x Ann)) ; ground arg AFTER a variable
                  (list 'not (list parentOf Cid '?y)) ; ground arg in a LEFT PREFIX
                  (list 'not (list '?p '?x))          ; nothing pinned at all
                  (list 'not (list '?p Tom))
                  (list 'not (list dog '. '?args))
                  (list 'not (list '?p '. '?args))]]
      (v/assert-many kb facts CxProbe {:strength :monotonic})
      (doseq [[label bindings]
              [["default" {}]
               ["hierarchical off" {#'res/*hierarchical-retrieval* false}]
               ["argument roots off" {#'res/*arg-root-retrieval* false}]]]
        (with-bindings bindings
          (doseq [pat shapes, ctx [CxProbe '?ctx]]
            (let [b (brute kb pat ctx)
                  g (got kb pat ctx)]
              (is (= b g)
                  (str label " lost " (pr-str (set/difference b g))
                       " on " (pr-str pat) " @ " ctx))))))
      (testing "the negative shapes are not vacuously equal — they do match something"
        (is (= 2 (count (got kb (list 'not (list dog '?x)) CxProbe))))
        (is (= 1 (count (got kb (list 'not (list parentOf Cid '?y)) CxProbe))))
        ;; two, not three: this pattern is *unary*, so the stored binary
        ;; `(not (parentOf Cid Ann))` does not unify with it
        (is (= 2 (count (got kb (list 'not (list '?p '?x)) CxProbe)))))
      (testing "and the public query answers them too"
        (is (= 2 (count (v/sentexes-matching kb (list 'not (list dog '?x)) CxProbe))))
        (is (= 1 (count (v/sentexes-matching kb (list 'not (list parentOf Cid '?y)) CxProbe))))
        (is (= 11 (count (v/sentexes-matching kb (list '?p '. '?args) CxProbe))))
        (is (= 3 (count (v/sentexes-matching kb
                                             (list 'not (list '?p '. '?args))
                                             CxProbe))))))))
